use std::{
    backtrace,
    error::Error,
    fmt::{self, Formatter},
};

/// Result of Type and GDError.
pub type GDResult<T> = Result<T, GDError>;

/// GameDig Error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GDErrorKind {
    /// The received packet was bigger than the buffer size.
    PacketOverflow,
    /// The received packet was shorter than the expected one.
    PacketUnderflow,
    /// The received packet is badly formatted.
    PacketBad,
    /// Couldn't send the packet.
    PacketSend,
    /// Couldn't send the receive.
    PacketReceive,
    /// Couldn't decompress data.
    Decompress,
    /// Couldn't create a socket connection.
    SocketConnect,
    /// Couldn't bind a socket.
    SocketBind,
    /// Invalid input.
    InvalidInput,
    /// The server queried is not the queried game server.
    BadGame,
    /// Couldn't automatically query.
    AutoQuery,
    /// A protocol-defined expected format was not met.
    ProtocolFormat,
    /// Couldn't cast a value to an enum.
    UnknownEnumCast,
    /// Couldn't parse a json string.
    JsonParse,
    /// Couldn't parse a value.
    TypeParse,
}

impl GDErrorKind {
    /// Convert error kind into a full error with a source (and implicit
    /// backtrace)
    ///
    /// ```
    /// use gamedig::{GDErrorKind, GDResult};
    /// let _: GDResult<u32> = "thing".parse().map_err(|e| GDErrorKind::TypeParse.context(e));
    /// ```
    pub fn context<E: Into<Box<dyn std::error::Error + 'static>>>(self, source: E) -> GDError {
        GDError::from_error(self, source)
    }
}

type ErrorSource = Box<dyn std::error::Error + 'static>;

/// Gamedig error type
///
/// Can be created in three ways (all of which will implicitly generate a
/// backtrace):
///
/// Directly from an [error kind](crate::errors::GDErrorKind) (without a source)
///
/// ```
/// use gamedig::{GDError, GDErrorKind};
/// let _: GDError = GDErrorKind::PacketBad.into();
/// ```
///
/// [From an error kind with a source](crate::errors::GDErrorKind::context) (any
/// type that implements `Into<Box<dyn std::error::Error + 'static>>)
///
/// ```
/// use gamedig::{GDError, GDErrorKind};
/// let _: GDError = GDErrorKind::PacketBad.context("Reason the packet was bad");
/// ```
///
/// Using the [new helper](crate::errors::GDError::new)
///
/// ```
/// use gamedig::{GDError, GDErrorKind};
/// let _: GDError = GDError::new(GDErrorKind::PacketBad, Some("Reason the packet was bad".into()));
/// ```
pub struct GDError {
    pub kind: GDErrorKind,
    pub source: Option<ErrorSource>,
    pub backtrace: Option<std::backtrace::Backtrace>,
}

impl From<GDErrorKind> for GDError {
    fn from(value: GDErrorKind) -> Self {
        let backtrace = Some(backtrace::Backtrace::capture());
        Self {
            kind: value,
            source: None,
            backtrace,
        }
    }
}

impl PartialEq for GDError {
    fn eq(&self, other: &Self) -> bool { self.kind == other.kind }
}

impl Error for GDError {
    fn source(&self) -> Option<&(dyn Error + 'static)> { self.source.as_ref().map(Box::as_ref) }
}

impl fmt::Debug for GDError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "GDError{{ kind={:?}", self.kind)?;
        if let Some(source) = &self.source {
            writeln!(f, "  source={:?}", source)?;
        }
        if let Some(backtrace) = &self.backtrace {
            let bt = format!("{:#?}", backtrace);
            writeln!(f, "  backtrace={}", bt.replace('\n', "\n  "))?;
        }
        writeln!(f, "}}")?;
        Ok(())
    }
}

impl fmt::Display for GDError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result { write!(f, "{:?}", self) }
}

impl GDError {
    /// Create a new error (with automatic backtrace)
    pub fn new(kind: GDErrorKind, source: Option<ErrorSource>) -> Self {
        let backtrace = Some(std::backtrace::Backtrace::capture());
        Self {
            kind,
            source,
            backtrace,
        }
    }

    /// Create a new error using any type that can be converted to an error
    pub fn from_error<E: Into<Box<dyn std::error::Error + 'static>>>(kind: GDErrorKind, source: E) -> Self {
        Self::new(kind, Some(source.into()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Testing Ok variant of the GDResult type
    #[test]
    fn test_gdresult_ok() {
        let result: GDResult<u32> = Ok(42);
        assert_eq!(result.unwrap(), 42);
    }

    // Testing Err variant of the GDResult type
    #[test]
    fn test_gdresult_err() {
        let result: GDResult<u32> = Err(GDErrorKind::InvalidInput.into());
        assert!(result.is_err());
    }

    // Testing cloning the GDErrorKind type
    #[test]
    fn test_cloning() {
        let error = GDErrorKind::BadGame;
        let cloned_error = error.clone();
        assert_eq!(error, cloned_error);
    }

    // test display GDError
    #[test]
    fn test_display() {
        let err = GDErrorKind::BadGame.context("Rust is not a game");
        let s = format!("{}", err);
        println!("{}", s);
        assert_eq!(
            s,
            "GDError{ kind=BadGame\n  source=\"Rust is not a game\"\n  backtrace=<disabled>\n}\n"
        );
    }

    // test error trait GDError
    #[test]
    fn test_error_trait() {
        let source: Result<u32, _> = "nan".parse();
        let source_err = source.unwrap_err();

        let error_with_context = GDErrorKind::TypeParse.context(source_err.clone());
        assert!(error_with_context.source().is_some());
        assert_eq!(
            format!("{}", error_with_context.source().unwrap()),
            format!("{}", source_err)
        );

        let error_without_context: GDError = GDErrorKind::TypeParse.into();
        assert!(error_without_context.source().is_none());
    }

    // Test creating GDError with GDError::new
    #[test]
    fn test_create_new() {
        let error_from_new = GDError::new(GDErrorKind::InvalidInput, None);
        assert!(error_from_new.backtrace.is_some());
        assert_eq!(error_from_new.kind, GDErrorKind::InvalidInput);
        assert!(error_from_new.source.is_none());
    }

    // Test creating GDError with GDErrorKind::context
    #[test]
    fn test_create_context() {
        let error_from_context = GDErrorKind::InvalidInput.context("test");
        assert!(error_from_context.backtrace.is_some());
        assert_eq!(error_from_context.kind, GDErrorKind::InvalidInput);
        assert!(error_from_context.source.is_some());
    }

    // Test creating GDError with From<GDErrorKind> for GDError
    #[test]
    fn test_create_into() {
        let error_from_into: GDError = GDErrorKind::InvalidInput.into();
        assert!(error_from_into.backtrace.is_some());
        assert_eq!(error_from_into.kind, GDErrorKind::InvalidInput);
        assert!(error_from_into.source.is_none());
    }
}
