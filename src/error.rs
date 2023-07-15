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

use crate::{
    analysis::BoardValue,
    game::GameStatus,
    prelude::{Action, Board, Color, Dove},
};

/// Root of all errors in this crate
///
/// You can find a rough sketch of dependency tree at [`crate::error`] page.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("BoardError::{0}")]
    BoardError(#[from] BoardError),

    #[error("GameError::{0}")]
    GameError(#[from] GameError),

    #[error("AnalysisError::{0}")]
    AnalysisError(#[from] AnalysisError),
}

/// Errors associated to [`Board`](`super::board::main::Board`)
#[derive(Debug, thiserror::Error)]
pub enum BoardError {
    #[error("BoardCreateError: {kind:?}")]
    BoardCreateError { kind: BoardCreateErrorKind },

    #[error("ActionPeformError: {kind:?}")]
    ActionPerformError {
        kind: ActionPerformErrorKind,
        action: Action,
    },

    #[error("MaskShiftError")]
    MaskShiftError,

    #[error("ActionConvertError::{0}")]
    ActionConvertError(#[from] ActionConvertError),
}

/// Error kinds on creating [`Board`](`super::board::main::Board`)
#[derive(Debug)]
pub enum BoardCreateErrorKind {
    BossNotFound,
    DoveDuplicated,
    PositionDuplicated,
    DoveIsolated,
    PositionOutOfRange,
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
    #[error("EncodingError: {kind:?}")]
    EncodingError { kind: EncodingErrorKind },

    #[error("DecodingError: {kind:?}")]
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

/// Errors associated to [`Game`]
#[derive(Debug, thiserror::Error)]
pub enum GameError {
    #[error("GameRuleCreateError: {kind:?}")]
    GameRuleCreateError { kind: GameRuleCreateErrorKind },

    #[error("PlayingError: {kind:?}")]
    PlayingError { kind: PlayingErrorKind },
}

/// Error kinds on creating [`GameRule`]
#[derive(Debug)]
pub enum GameRuleCreateErrorKind {
    InitialBoardError,
}

impl From<GameRuleCreateErrorKind> for Error {
    fn from(value: GameRuleCreateErrorKind) -> Self {
        let err = GameError::GameRuleCreateError { kind: value };
        Error::from(GameError::from(err))
    }
}

/// Error kinds that may occur during game playing
#[derive(Debug)]
pub enum PlayingErrorKind {
    PlayerMismatch,
    ProhibitedRemove(Action),
    GameFinished(GameStatus),
}

impl From<PlayingErrorKind> for Error {
    fn from(value: PlayingErrorKind) -> Self {
        GameError::PlayingError { kind: value }.into()
    }
}

/// Error variants on analysis for games
#[derive(Debug, thiserror::Error)]
pub enum AnalysisError {
    #[error("ArgsValidationError: {kind}")]
    ArgsValidationError { kind: ArgsValidationErrorKind },

    #[error("BoardValueMismatch: value of board is {0:?} than value in argument")]
    BoardValueMismatch(std::cmp::Ordering),
}

/// Error kinds on validation of arguments
#[derive(Debug)]
pub enum ArgsValidationErrorKind {
    FinishedGameBoard(Board),
    UnsupportedValue(BoardValue),
    DrawJudge,
}

impl From<ArgsValidationErrorKind> for Error {
    fn from(value: ArgsValidationErrorKind) -> Self {
        AnalysisError::ArgsValidationError { kind: value }.into()
    }
}

impl std::fmt::Display for ArgsValidationErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use ArgsValidationErrorKind::*;
        let msg = match self {
            FinishedGameBoard(_board) => format!("board of finished game"),
            UnsupportedValue(value) => format!("{} not supported", value),
            DrawJudge => format!("Judge::Draw not supported"),
        };
        write!(f, "{}", msg)
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
