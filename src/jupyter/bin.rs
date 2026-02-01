//! SGGSLog Jupyter kernel binary.

use sggslog::jupyter::{
    protocol::{ConnectionInfo, ExecuteRequest, KernelInfoReply, Message},
    Kernel,
};
use std::sync::Arc;
use tokio::sync::Mutex;
use zeromq::{Socket, SocketRecv, SocketSend};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: sggslog-kernel <connection-file>");
        std::process::exit(1);
    }

    let conn_file = &args[1];
    let conn_info = ConnectionInfo::from_file(conn_file)?;
    let key = conn_info.key.as_bytes().to_vec();

    // Create the kernel
    let kernel = Arc::new(Mutex::new(Kernel::new()));

    // Create sockets
    let mut shell_socket = zeromq::RouterSocket::new();
    let mut iopub_socket = zeromq::PubSocket::new();
    let mut stdin_socket = zeromq::RouterSocket::new();
    let mut control_socket = zeromq::RouterSocket::new();
    let mut hb_socket = zeromq::RepSocket::new();

    // Bind sockets
    shell_socket
        .bind(&conn_info.endpoint(conn_info.shell_port))
        .await?;
    iopub_socket
        .bind(&conn_info.endpoint(conn_info.iopub_port))
        .await?;
    stdin_socket
        .bind(&conn_info.endpoint(conn_info.stdin_port))
        .await?;
    control_socket
        .bind(&conn_info.endpoint(conn_info.control_port))
        .await?;
    hb_socket
        .bind(&conn_info.endpoint(conn_info.hb_port))
        .await?;

    eprintln!("SGGSLog kernel started");

    // Wrap sockets in Arc<Mutex> for sharing
    let iopub_socket = Arc::new(Mutex::new(iopub_socket));
    let key = Arc::new(key);

    // Spawn heartbeat handler
    let hb_handle = tokio::spawn(async move {
        loop {
            match hb_socket.recv().await {
                Ok(msg) => {
                    let _ = hb_socket.send(msg).await;
                }
                Err(e) => {
                    eprintln!("Heartbeat error: {}", e);
                    break;
                }
            }
        }
    });

    // Spawn control handler
    let control_key = Arc::clone(&key);
    let control_handle = tokio::spawn(async move {
        loop {
            match control_socket.recv().await {
                Ok(msg) => {
                    let frames: Vec<Vec<u8>> = msg.iter().map(|b| b.to_vec()).collect();
                    if let Ok(message) = Message::from_frames(frames, &control_key) {
                        match message.header.msg_type.as_str() {
                            "shutdown_request" => {
                                let reply = message.reply(
                                    "shutdown_reply",
                                    serde_json::json!({"status": "ok", "restart": false}),
                                );
                                let reply_frames = reply.to_frames(&control_key);
                                let zmq_msg = frames_to_zmq_message(reply_frames);
                                let _ = control_socket.send(zmq_msg).await;
                                std::process::exit(0);
                            }
                            _ => {}
                        }
                    }
                }
                Err(e) => {
                    eprintln!("Control error: {}", e);
                    break;
                }
            }
        }
    });

    // Main shell handler loop
    loop {
        match shell_socket.recv().await {
            Ok(msg) => {
                let frames: Vec<Vec<u8>> = msg.iter().map(|b| b.to_vec()).collect();

                match Message::from_frames(frames, &key) {
                    Ok(message) => {
                        handle_shell_message(
                            message,
                            &mut shell_socket,
                            Arc::clone(&iopub_socket),
                            Arc::clone(&kernel),
                            Arc::clone(&key),
                        )
                        .await;
                    }
                    Err(e) => {
                        eprintln!("Failed to parse message: {}", e);
                    }
                }
            }
            Err(e) => {
                eprintln!("Shell receive error: {}", e);
                break;
            }
        }
    }

    hb_handle.abort();
    control_handle.abort();

    Ok(())
}

async fn handle_shell_message(
    message: Message,
    shell_socket: &mut zeromq::RouterSocket,
    iopub_socket: Arc<Mutex<zeromq::PubSocket>>,
    kernel: Arc<Mutex<Kernel>>,
    key: Arc<Vec<u8>>,
) {
    // Helper to send on iopub
    let send_iopub = |msg: Message| {
        let iopub = Arc::clone(&iopub_socket);
        let key = Arc::clone(&key);
        async move {
            let mut socket = iopub.lock().await;
            send_zmq_message(&mut *socket, msg, &key).await;
        }
    };

    // Send busy status (required by Jupyter protocol)
    send_iopub(message.status("busy")).await;

    match message.header.msg_type.as_str() {
        "kernel_info_request" => {
            let reply = message.reply(
                "kernel_info_reply",
                serde_json::to_value(KernelInfoReply::default()).unwrap(),
            );
            send_zmq_message(shell_socket, reply, &key).await;
        }

        "execute_request" => {
            if let Ok(request) = serde_json::from_value::<ExecuteRequest>(message.content.clone()) {
                let result = {
                    let mut k = kernel.lock().await;
                    k.execute(&request.code)
                };

                // Send execute_input
                send_iopub(message.pub_message(
                    "execute_input",
                    serde_json::json!({
                        "code": request.code,
                        "execution_count": 1
                    }),
                ))
                .await;

                match result {
                    Ok(output) => {
                        if !output.is_empty() && !request.silent {
                            send_iopub(message.pub_message(
                                "execute_result",
                                serde_json::json!({
                                    "execution_count": 1,
                                    "data": {"text/plain": output},
                                    "metadata": {}
                                }),
                            ))
                            .await;
                        }

                        let reply = message.reply(
                            "execute_reply",
                            serde_json::json!({
                                "status": "ok",
                                "execution_count": 1,
                                "user_expressions": {}
                            }),
                        );
                        send_zmq_message(shell_socket, reply, &key).await;
                    }
                    Err(e) => {
                        send_iopub(message.pub_message(
                            "stream",
                            serde_json::json!({
                                "name": "stderr",
                                "text": format!("Error: {}\n", e.message)
                            }),
                        ))
                        .await;

                        let reply = message.reply(
                            "execute_reply",
                            serde_json::json!({
                                "status": "error",
                                "execution_count": 1,
                                "ename": "ExecutionError",
                                "evalue": e.message,
                                "traceback": []
                            }),
                        );
                        send_zmq_message(shell_socket, reply, &key).await;
                    }
                }
            }
        }

        "is_complete_request" => {
            let reply = message.reply(
                "is_complete_reply",
                serde_json::json!({"status": "complete"}),
            );
            send_zmq_message(shell_socket, reply, &key).await;
        }

        "complete_request" => {
            let reply = message.reply(
                "complete_reply",
                serde_json::json!({
                    "status": "ok",
                    "matches": [],
                    "cursor_start": 0,
                    "cursor_end": 0,
                    "metadata": {}
                }),
            );
            send_zmq_message(shell_socket, reply, &key).await;
        }

        _ => {
            eprintln!("Unknown message type: {}", message.header.msg_type);
        }
    }

    // Send idle status (required by Jupyter protocol)
    send_iopub(message.status("idle")).await;
}

async fn send_zmq_message<S: SocketSend>(socket: &mut S, msg: Message, key: &[u8]) {
    let frames = msg.to_frames(key);
    let zmq_msg = frames_to_zmq_message(frames);
    if let Err(e) = socket.send(zmq_msg).await {
        eprintln!("Failed to send message: {}", e);
    }
}

fn frames_to_zmq_message(frames: Vec<Vec<u8>>) -> zeromq::ZmqMessage {
    use bytes::Bytes;
    use std::convert::TryFrom;
    let bytes_frames: Vec<Bytes> = frames.into_iter().map(Bytes::from).collect();
    zeromq::ZmqMessage::try_from(bytes_frames).expect("frames should not be empty")
}
