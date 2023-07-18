//! Convenient tools to analyze the game

/// A module containing a light [`Board`](`crate::Board`) container
/// [`BoardSet`] and associated items.
pub mod board_set;
pub(crate) mod board_value;
pub(crate) mod io;

// By-pass export
pub use crate::prelude::board::canonicalizer::PositionMapper;

pub use board_set::{BoardSet, Capacity};
pub use board_value::*;
pub use io::*;
