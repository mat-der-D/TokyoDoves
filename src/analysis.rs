//! Convenient tools to analyze the game

pub(crate) mod board_value;

// By-pass export
pub use crate::prelude::board::canonicalizer::PositionMapper;

pub use board_value::*;
