use thiserror::Error;

pub type Result<T> = std::result::Result<T, CasError>;

#[derive(Debug, Error)]
pub enum CasError {
    #[error("parse error: {0}")]
    Parse(String),
    #[error("unsupported operation: {0}")]
    Unsupported(String),
}
