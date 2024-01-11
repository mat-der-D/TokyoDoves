//! Convenient tools to analyze the game ("analysis" feature required)
//!
//! The following functions are main contents:
//! - [`evaluate_board`]<br>
//!     It calculates a possible range of [`BoardValue`] of specified [`Board`](`crate::Board`).
//! - [`compare_board_value`]<br>
//!     It compares the value of specified [`Board`](`crate::Board`) to a given [`BoardValue`].
//! - [`create_checkmate_tree`] and [`create_checkmate_tree_with_value`]<br>
//!     It creates an [`BoardValueTree`] that describes routes to ends of the game.
//! - [`find_best_actions`]<br>
//!     It collects the best [`Action`](`crate::Action`)s by [`BoardValue`].
//!
//! The [`BoardValue`] struct plays important roles in the all above functions.
//! See their documentations for more.

pub(crate) mod board_value;

// By-pass export
pub use crate::prelude::board::canonicalizer::PositionMapper;

pub use board_value::*;
