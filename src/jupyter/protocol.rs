//! Jupyter wire protocol implementation.

use hmac::{Hmac, Mac};
use serde::{Deserialize, Serialize};
use sha2::Sha256;
use std::collections::HashMap;

/// Delimiter between routing info and message parts.
pub const DELIMITER: &[u8] = b"<IDS|MSG>";

/// Jupyter message header.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Header {
    pub msg_id: String,
    pub session: String,
    pub username: String,
    pub date: String,
    pub msg_type: String,
    pub version: String,
}

impl Header {
    pub fn new(msg_type: &str, session: &str) -> Self {
        Header {
            msg_id: uuid::Uuid::new_v4().to_string(),
            session: session.to_string(),
            username: "sggslog".to_string(),
            date: chrono_now(),
            msg_type: msg_type.to_string(),
            version: "5.3".to_string(),
        }
    }
}

fn chrono_now() -> String {
    // Simple ISO 8601 timestamp
    use std::time::{SystemTime, UNIX_EPOCH};
    let duration = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    format!("{}.{}", duration.as_secs(), duration.subsec_millis())
}

/// A complete Jupyter message.
#[derive(Debug, Clone)]
pub struct Message {
    pub identities: Vec<Vec<u8>>,
    pub header: Header,
    pub parent_header: Option<Header>,
    pub metadata: HashMap<String, serde_json::Value>,
    pub content: serde_json::Value,
    pub buffers: Vec<Vec<u8>>,
}

impl Message {
    /// Create a reply to this message.
    pub fn reply(&self, msg_type: &str, content: serde_json::Value) -> Message {
        Message {
            identities: self.identities.clone(),
            header: Header::new(msg_type, &self.header.session),
            parent_header: Some(self.header.clone()),
            metadata: HashMap::new(),
            content,
            buffers: Vec::new(),
        }
    }

    /// Parse a message from ZMQ frames.
    pub fn from_frames(frames: Vec<Vec<u8>>, key: &[u8]) -> Result<Self, String> {
        // Find delimiter
        let delim_pos = frames
            .iter()
            .position(|f| f.as_slice() == DELIMITER)
            .ok_or("No delimiter found")?;

        let identities: Vec<Vec<u8>> = frames[..delim_pos].to_vec();
        let rest = &frames[delim_pos + 1..];

        if rest.len() < 5 {
            return Err("Not enough frames after delimiter".to_string());
        }

        let hmac_sig = &rest[0];
        let header_bytes = &rest[1];
        let parent_header_bytes = &rest[2];
        let metadata_bytes = &rest[3];
        let content_bytes = &rest[4];
        let buffers: Vec<Vec<u8>> = rest[5..].to_vec();

        // Verify HMAC if key is provided
        if !key.is_empty() {
            let mut mac = Hmac::<Sha256>::new_from_slice(key)
                .map_err(|_| "Invalid HMAC key")?;
            mac.update(header_bytes);
            mac.update(parent_header_bytes);
            mac.update(metadata_bytes);
            mac.update(content_bytes);

            let expected_sig = hex::encode(mac.finalize().into_bytes());
            let received_sig = String::from_utf8_lossy(hmac_sig);

            if expected_sig != received_sig {
                return Err("HMAC verification failed".to_string());
            }
        }

        let header: Header = serde_json::from_slice(header_bytes)
            .map_err(|e| format!("Failed to parse header: {}", e))?;

        let parent_header: Option<Header> = if parent_header_bytes == b"{}" {
            None
        } else {
            serde_json::from_slice(parent_header_bytes).ok()
        };

        let metadata: HashMap<String, serde_json::Value> =
            serde_json::from_slice(metadata_bytes).unwrap_or_default();

        let content: serde_json::Value = serde_json::from_slice(content_bytes)
            .map_err(|e| format!("Failed to parse content: {}", e))?;

        Ok(Message {
            identities,
            header,
            parent_header,
            metadata,
            content,
            buffers,
        })
    }

    /// Serialize message to ZMQ frames.
    pub fn to_frames(&self, key: &[u8]) -> Vec<Vec<u8>> {
        let header_bytes = serde_json::to_vec(&self.header).unwrap();
        let parent_header_bytes = match &self.parent_header {
            Some(h) => serde_json::to_vec(h).unwrap(),
            None => b"{}".to_vec(),
        };
        let metadata_bytes = serde_json::to_vec(&self.metadata).unwrap();
        let content_bytes = serde_json::to_vec(&self.content).unwrap();

        // Compute HMAC
        let sig = if key.is_empty() {
            String::new()
        } else {
            let mut mac = Hmac::<Sha256>::new_from_slice(key).unwrap();
            mac.update(&header_bytes);
            mac.update(&parent_header_bytes);
            mac.update(&metadata_bytes);
            mac.update(&content_bytes);
            hex::encode(mac.finalize().into_bytes())
        };

        let mut frames = Vec::new();

        // Identities
        for id in &self.identities {
            frames.push(id.clone());
        }

        // Delimiter
        frames.push(DELIMITER.to_vec());

        // HMAC signature
        frames.push(sig.into_bytes());

        // Message parts
        frames.push(header_bytes);
        frames.push(parent_header_bytes);
        frames.push(metadata_bytes);
        frames.push(content_bytes);

        // Buffers
        for buf in &self.buffers {
            frames.push(buf.clone());
        }

        frames
    }
}

/// Connection file format.
#[derive(Debug, Deserialize)]
pub struct ConnectionInfo {
    pub ip: String,
    pub transport: String,
    pub shell_port: u16,
    pub iopub_port: u16,
    pub stdin_port: u16,
    pub control_port: u16,
    pub hb_port: u16,
    pub key: String,
    pub signature_scheme: String,
}

impl ConnectionInfo {
    pub fn from_file(path: &str) -> Result<Self, String> {
        let content = std::fs::read_to_string(path)
            .map_err(|e| format!("Failed to read connection file: {}", e))?;
        serde_json::from_str(&content)
            .map_err(|e| format!("Failed to parse connection file: {}", e))
    }

    pub fn endpoint(&self, port: u16) -> String {
        format!("{}://{}:{}", self.transport, self.ip, port)
    }
}

/// Execute request content.
#[derive(Debug, Deserialize)]
pub struct ExecuteRequest {
    pub code: String,
    pub silent: bool,
    pub store_history: bool,
    pub user_expressions: HashMap<String, String>,
    pub allow_stdin: bool,
    pub stop_on_error: bool,
}

/// Kernel info reply content.
#[derive(Debug, Serialize)]
pub struct KernelInfoReply {
    pub status: String,
    pub protocol_version: String,
    pub implementation: String,
    pub implementation_version: String,
    pub language_info: LanguageInfo,
    pub banner: String,
    pub help_links: Vec<HelpLink>,
}

#[derive(Debug, Serialize)]
pub struct LanguageInfo {
    pub name: String,
    pub version: String,
    pub mimetype: String,
    pub file_extension: String,
}

#[derive(Debug, Serialize)]
pub struct HelpLink {
    pub text: String,
    pub url: String,
}

impl Default for KernelInfoReply {
    fn default() -> Self {
        KernelInfoReply {
            status: "ok".to_string(),
            protocol_version: "5.3".to_string(),
            implementation: "sggslog".to_string(),
            implementation_version: "0.1.0".to_string(),
            language_info: LanguageInfo {
                name: "sggslog".to_string(),
                version: "0.1.0".to_string(),
                mimetype: "text/x-sggslog".to_string(),
                file_extension: ".sggs".to_string(),
            },
            banner: "SGGSLog - Semantically Guided Goal-Sensitive Logic Programming".to_string(),
            help_links: vec![],
        }
    }
}
