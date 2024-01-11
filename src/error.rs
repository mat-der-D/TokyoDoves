//! Error variants
//!
//! A rough sketch of dependency tree:
//!
//! [`Error`] (root of all errors)
//! - [`BoardError`]
//!     - BoardCreateError: [`BoardCreateErrorKind`]
//!     - ActionPerformError: [`ActionPerformErrorKind`] + [`Action`]
//!     - MaskShiftError
//!     - [`ActionConvertError`]
//!         - EncodingError: [`EncodingErrorKind`]
//!         - DecodingError: [`DecodingErrorKind`]
//! - [`GameError`]
//!     - GameRuleCreateError: [`GameRuleCreateErrorKind`]
//!     - PlayingError: [`PlayingErrorKind`]
//! - [`AnalysisError`]
//!     - ArgsValidationError: [`ArgsValidationErrorKind`]
//!     - BoardValueMismatch: [`std::cmp::Ordering`]
//!
//! Some of contents are available only when feature "game" or "analysis" is indicated.

#[cfg(feature = "analysis")]
use crate::analysis::BoardValue;
#[cfg(feature = "game")]
use crate::game::GameStatus;
#[cfg(feature = "analysis")]
use crate::prelude::Board;
use crate::prelude::{Action, Color, Dove};

/// Root of all errors in this crate
///
/// You can find a rough sketch of dependency tree at the top page of the [`error`](`crate::error`) module.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Errors associated to the [`Board`] struct
    #[error("BoardError::{0}")]
    BoardError(#[from] BoardError),

    /// Errors associated to the [`game`](`crate::game`) module
    #[cfg(feature = "game")]
    #[error("GameError::{0}")]
    GameError(#[from] GameError),

    /// Errors associated to the [`analysis`](`crate::analysis`) module
    #[cfg(feature = "analysis")]
    #[error("AnalysisError::{0}")]
    AnalysisError(#[from] AnalysisError),
}

impl Error {
    /// Returns the value in [`Error::BoardError`].
    ///
    /// It returns [`None`] if `self` does not match `Error::BoardError`.
    pub fn as_board_error(&self) -> Option<&BoardError> {
        match self {
            Error::BoardError(err) => Some(err),
            #[cfg(any(feature = "game", feature = "analysis"))]
            _ => None,
        }
    }

    /// Returns the value in [`Error::GameError`].
    ///
    /// It returns [`None`] if `self` does not match `Error::GameError`.
    #[cfg(feature = "game")]
    pub fn as_game_error(&self) -> Option<&GameError> {
        match self {
            Error::GameError(err) => Some(err),
            _ => None,
        }
    }

    /// Returns the value in [`Error::AnalysisError`].
    ///
    /// It returns [`None`] if `self` does not match `Error::AnalysisError`.
    #[cfg(feature = "analysis")]
    pub fn as_analysis_error(&self) -> Option<&AnalysisError> {
        match self {
            Error::AnalysisError(err) => Some(err),
            _ => None,
        }
    }
}

/// Errors associated to the [`Board`](`super::board::main::Board`) struct
#[derive(Debug, thiserror::Error)]
pub enum BoardError {
    /// Errors on creation of [`Board`]
    #[error("BoardCreateError::{kind}")]
    BoardCreateError { kind: BoardCreateErrorKind },

    /// Errors on performing [`Action`]s
    #[error("ActionPeformError::{kind:?}")]
    ActionPerformError {
        kind: ActionPerformErrorKind,
        action: Action,
    },

    /// Internal errors
    #[error("InternalError")]
    InternalError,

    /// Errors on conversion between [`Action`] and string in SSN
    #[error("ActionConvertError::{0}")]
    ActionConvertError(#[from] ActionConvertError),
}

impl BoardError {
    /// Returns the value in [`BoardError::ActionConvertError`].
    ///
    /// It returns [`None`] if `self` does not match `BoardError::ActionConvertError`.
    pub fn as_action_convert_error(&self) -> Option<&ActionConvertError> {
        match self {
            BoardError::ActionConvertError(err) => Some(err),
            _ => None,
        }
    }
}

/// Error kinds on creating [`Board`](`super::board::main::Board`)
#[derive(Debug)]
pub enum BoardCreateErrorKind {
    BossNotFound(Color),
    DoveDuplicated(Color, Dove),
    PositionDuplicated,
    DoveIsolated,
    PositionOutOfRange,
    BitNeitherSingleNorZero([[u64; 6]; 2], u64),
}

impl std::fmt::Display for BoardCreateErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use BoardCreateErrorKind::*;
        let msg = match self {
            BossNotFound(color) => format!("BossNotFound: {color} boss not found"),
            DoveDuplicated(color, dove) => {
                format!("DoveDuplicated: found duplicated doves ({color}, {dove:?})")
            }
            PositionDuplicated => {
                "PositionDuplicated: position duplicated with another dove".to_string()
            }
            DoveIsolated => "DoveIsolated: some dove is isolated".to_string(),
            PositionOutOfRange => "PositionOutOfRange: some dove is out of 4x4 region".to_string(),
            BitNeitherSingleNorZero(pos, bit) => {
                format!("BitNeitherSingleNorZero: position {bit} in {pos:?} is neither single bit nor zero")
            }
        };
        write!(f, "{msg}")
    }
}

impl From<BoardCreateErrorKind> for Error {
    fn from(value: BoardCreateErrorKind) -> Self {
        BoardError::BoardCreateError { kind: value }.into()
    }
}

/// Error kinds on performing [`Action`](`crate::prelude::Action`)
#[derive(Debug)]
pub enum ActionPerformErrorKind {
    // common
    ToBeIsolated,    // for Move, Remove
    OutOfField,      // for Put, Move
    InvalidShift,    // for Put, Move
    InvalidPosition, // for Put, bwd Remove

    // for Put
    AlreadyOnBoard,

    // for Move
    ObstacleInRoute,
    ThroughOuterField,

    // for Remove
    TriedToRemoveBoss,
    NotOnBoard,
}

impl From<(ActionPerformErrorKind, Action)> for Error {
    fn from((kind, action): (ActionPerformErrorKind, Action)) -> Self {
        BoardError::ActionPerformError { kind, action }.into()
    }
}

/// Errors on conversion between [`Action`] and string in SSN
#[derive(Debug, thiserror::Error)]
pub enum ActionConvertError {
    /// Errors on converting from [`Action`] to SSN
    #[error("EncodingError::{kind:?}")]
    EncodingError { kind: EncodingErrorKind },

    /// Errors on converting from SSN to [`Action`]
    #[error("DecodingError::{kind:?}")]
    DecodingError { kind: DecodingErrorKind },
}

/// Error kinds on conversion of [`Action`] into string in SSN
#[derive(Debug)]
pub enum EncodingErrorKind {
    BossNotFound(Color),
    DoveNotFound(Color, Dove),
}

impl From<EncodingErrorKind> for Error {
    fn from(value: EncodingErrorKind) -> Self {
        let err = ActionConvertError::EncodingError { kind: value };
        Error::from(BoardError::from(err))
    }
}

/// Error kinds on conversion of [`Action`] from string in SSN
#[derive(Debug)]
pub enum DecodingErrorKind {
    NumberNotFollowAfterNEWS,
    UnexpectedCharacter(char),
    ColorNotInferred,
    DoveNotInferred,
    BossNotFound(Color),
    DoveNotOnBoard(Color, Dove),
}

impl From<DecodingErrorKind> for Error {
    fn from(value: DecodingErrorKind) -> Self {
        let err = ActionConvertError::DecodingError { kind: value };
        Error::from(BoardError::from(err))
    }
}

/// Errors associated to [`Game`](`crate::game::Game`)
#[cfg(feature = "game")]
#[derive(Debug, thiserror::Error)]
pub enum GameError {
    /// Errors on creating [`GameRule`](`crate::game::GameRule`)
    #[error("GameRuleCreateError::{kind:?}")]
    GameRuleCreateError { kind: GameRuleCreateErrorKind },

    /// Errors on playing games
    #[error("PlayingError::{kind:?}")]
    PlayingError { kind: PlayingErrorKind },
}

/// Error kinds on creating [`GameRule`](`crate::game::GameRule`)
#[cfg(feature = "game")]
#[derive(Debug)]
pub enum GameRuleCreateErrorKind {
    InitialBoardError,
}

#[cfg(feature = "game")]
impl From<GameRuleCreateErrorKind> for Error {
    fn from(value: GameRuleCreateErrorKind) -> Self {
        GameError::GameRuleCreateError { kind: value }.into()
    }
}

/// Error kinds on playing games
#[cfg(feature = "game")]
#[derive(Debug)]
pub enum PlayingErrorKind {
    PlayerMismatch,
    ProhibitedRemove(Action),
    GameFinished(GameStatus),
}

#[cfg(feature = "game")]
impl From<PlayingErrorKind> for Error {
    fn from(value: PlayingErrorKind) -> Self {
        GameError::PlayingError { kind: value }.into()
    }
}

/// Error variants on analysis for games
#[cfg(feature = "analysis")]
#[derive(Debug, thiserror::Error)]
pub enum AnalysisError {
    /// Errors on validating arguments
    #[error("ArgsValidationError::{kind}")]
    ArgsValidationError { kind: ArgsValidationErrorKind },

    /// Errors for [`create_checkmate_tree_with_value`](`crate::analysis::create_checkmate_tree_with_value`)
    #[error("BoardValueMismatch: value of board is {0:?} than value in argument")]
    BoardValueMismatch(std::cmp::Ordering),
}

/// Error kinds on validation of arguments
#[cfg(feature = "analysis")]
#[derive(Debug)]
pub enum ArgsValidationErrorKind {
    FinishedGameBoard(Board),
    UnsupportedValue(BoardValue),
    DrawJudge,
}

#[cfg(feature = "analysis")]
impl From<ArgsValidationErrorKind> for Error {
    fn from(value: ArgsValidationErrorKind) -> Self {
        AnalysisError::ArgsValidationError { kind: value }.into()
    }
}

#[cfg(feature = "analysis")]
impl std::fmt::Display for ArgsValidationErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use ArgsValidationErrorKind::*;
        let msg = match self {
            FinishedGameBoard(_board) => String::from("FinishedGameBoard: board of finished game"),
            UnsupportedValue(value) => format!("UnsupportedValue: {value} not supported"),
            DrawJudge => String::from("DrawJudge: Judge::Draw not supported"),
        };
        write!(f, "{msg}")
    }
}

// *************************************************************************
//  Internal Error
// *************************************************************************
#[derive(Debug, Clone, Copy, thiserror::Error)]
pub(crate) enum DirectionError {
    #[error("bit out of field: {0}")]
    BitOutOfField(u64),
    #[error("index out of range: {0}")]
    IndexOutOfRange(usize),
}
