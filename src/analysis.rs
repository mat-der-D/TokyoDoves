//! Convenient tools to analyze the game

pub mod board_set;
pub(crate) mod board_value;
pub(crate) mod io;

// By-pass export
pub use crate::prelude::board::canonicalizer::PositionMapper;

pub use board_set::{BoardSet, Capacity, RawBoardSet};
pub use board_value::*;
pub use io::*;
