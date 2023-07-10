//! Error variants
//!
//! A rough sketch of dependency tree:
//! - [`ActionConvertError`]
//!     - [`SSNEncodingErrorType`]
//!     - [`SSNDecodingErrorType`]
//! - [`BoardError`]
//!     - [`ActionPerformErrorType`]
//!     - [`BoardCreateErrorType`]

use crate::prelude::{
    actions::Action,
    pieces::{Color, Dove},
};

/// Errors associated to [`GameRule`](`crate::game::GameRule`)
#[derive(Debug, Clone, Copy, thiserror::Error)]
pub enum GameRuleError {
    #[error("[InitialBoardError]")]
    InitialBoardError,
}

/// Errors associated to [`Board`](`super::board::main::Board`)
#[derive(Debug, Clone, Copy, thiserror::Error)]
pub enum BoardError {
    #[error("[BoardCreateError]")]
    BoardCreateError { error_type: BoardCreateErrorType },

    #[error("[ActionPerformError] Type: {:?}, Action: {:?}", .error_type, .action)]
    ActionPerformError {
        error_type: ActionPerformErrorType,
        action: Action,
    },

    #[error("[MaskShiftError]")]
    MaskShiftError,
}

/// Types of errors on creating [`Board`](`super::board::main::Board`)
#[derive(Debug, Clone, Copy)]
pub enum BoardCreateErrorType {
    BossNotFound,
    DoveDuplicated,
    PositionDuplicated,
    DoveIsolated,
    PositionOutOfRange,
}

/// Types of errors on performing [`Action`](`crate::prelude::Action`)
#[derive(Debug, Clone, Copy)]
pub enum ActionPerformErrorType {
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

/// Errors on conversion between [`Action`] and string in SSN
#[derive(Debug, Clone, Copy, thiserror::Error)]
pub enum ActionConvertError {
    #[error("[SSNEncodingError] Type: {:?}", .error_type)]
    SSNEncodingError { error_type: SSNEncodingErrorType },

    #[error("[SSNDecodingError] Type: {:?}", .error_type)]
    SSNDecodingError { error_type: SSNDecodingErrorType },
}

/// Types of errors on conversion of [`Action`] into string in SSN
#[derive(Debug, Clone, Copy)]
pub enum SSNEncodingErrorType {
    BossNotFound(Color),
    DoveNotFound(Color, Dove),
}

/// Types of errors on conversion of [`Action`] from string in SSN
#[derive(Debug, Clone, Copy)]
pub enum SSNDecodingErrorType {
    NumberNotFollowAfterNEWS,
    UnexpectedCharacter(char),
    ColorNotInferred,
    DoveNotInferred,
    BossNotFound,
    DoveNotOnBoard(Color, Dove),
}

#[derive(Debug, Clone, Copy, thiserror::Error)]
pub(crate) enum DirectionError {
    #[error("bit out of field: {0}")]
    BitOutOfField(u64),
    #[error("index out of range: {0}")]
    IndexOutOfRange(usize),
}
