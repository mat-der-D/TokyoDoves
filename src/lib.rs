//! Tokyodoves is a library of an efficient board of Tokyo Doves
//! and associated toolkits.
//!
//! Tokyo Doves is an abstract strategy board game for two players.
//! See the following pages for its rules.
//! - A rule book in Japanese:<br>
//!     <https://image.gamemarket.jp/2019/11/v160.pdf>
//! - A rule book in English:<br>
//!     <https://www.daiso-syuppan.com/wp-content/uploads/2021/02/TOKYO-DOVES.pdf>
//! - A video explaining the rules on YouTube (Japanese):<br>
//!     <https://www.youtube.com/watch?v=SsyoqnipHWQ>
//!
//! The board is implemented with the bitboard technique,
//! which allows for extremely fast operations
//! including moving, putting and removing pieces.
//!
//! # First of all
//! The following are the most fundamental items of this crate.
//! - [`Color`]: An enum of two colors, red and green, representing two players
//! - [`Dove`]: An enum of six types of doves
//! - [`Shift`]: A struct to describe a difference between two squares
//! - [`Action`]: An enum of actions the players perform in their turns
//! - [`Board`]: A struct of a board of the game
//!
//! # Let's play
//! The board at the beginning can be created by [`Board::new()`].
//! ```rust
//! use tokyodoves::*;
//!
//! let mut board = Board::new();
//! println!("{board}");
//! // +---+---+---+---+
//! // | b |   |   |   |
//! // +---+---+---+---+
//! // | B |   |   |   |
//! // +---+---+---+---+
//! // |   |   |   |   |
//! // +---+---+---+---+
//! // |   |   |   |   |
//! // +---+---+---+---+
//! ```
//! "B" stands for a red boss-hato
//! and "b" stands for a green boss-hato.
//! See the documentation of [`color_dove_to_char`]
//! for other characters to be used.
//!
//! If you, red player, want to put from your hand
//! the aniki-hato on the right side of your boss hato,
//! perform an action `Action::Put(Color::Red, Dove::A, Shift::new(0, 1))`.
//! ```rust
//! # use tokyodoves::*;
//! # let mut board = Board::new();
//! let action = Action::Put(Color::Red, Dove::A, Shift::new(0, 1));
//! let result = board.perform(action);
//! assert!(result.is_ok());
//! println!("{board}");
//! // +---+---+---+---+
//! // | b |   |   |   |
//! // +---+---+---+---+
//! // | B | A |   |   |
//! // +---+---+---+---+
//! // |   |   |   |   |
//! // +---+---+---+---+
//! // |   |   |   |   |
//! // +---+---+---+---+
//! ```
//! If the action is legal, `result` is `Ok(())`, otherwise `Err(_)`.
//! See the documentation of the [`perform`](`Board::perform`) method for more.
//!
//! The [`legal_actions`](`Board::legal_actions`) method returns all available actions.
//! ```rust
//! # use tokyodoves::*;
//! # let mut board = Board::new();
//! # let action = Action::Put(Color::Red, Dove::A, Shift::new(0, 1));
//! # let result = board.perform(action);
//! # println!("{board}");
//! let actions = board.legal_actions(Color::Green, true, true, true);
//! for action in actions {
//!     println!("{action:?}");
//! }
//! // Put(Green, A, Shift { dv: 0, dh: 1 })
//! // Put(Green, Y, Shift { dv: 0, dh: 1 })
//! // Put(Green, M, Shift { dv: 0, dh: 1 })
//! // ...
//! // Move(Green, B, Shift { dv: 1, dh: -1 })
//! ```
//! The type of the returned value is [`ActionsFwd`], which is a read-only
//! container of [`Action`]s. Three boolean arguments of [`legal_actions`](`Board::legal_actions`)
//! control what kinds of actions to be considered.
//! See their documentations for more.
//!
//! Next, suppose green player chose to put yaibato on the top-left square of green boss-hato.
//! ```rust
//! # use tokyodoves::*;
//! # let mut board = Board::new();
//! # let action = Action::Put(Color::Red, Dove::A, Shift::new(0, 1));
//! # let result = board.perform(action);
//! # println!("{board}");
//! # let actions = board.legal_actions(Color::Green, true, true, true);
//! let action = actions[6]; // Put(Green, Y , Shift { dv: -1, dh: -1 })
//! board.perform(action);
//! println!("{board}");
//! // +---+---+---+---+
//! // | y |   |   |   |
//! // +---+---+---+---+
//! // |   | b |   |   |
//! // +---+---+---+---+
//! // |   | B | A |   |
//! // +---+---+---+---+
//! // |   |   |   |   |
//! // +---+---+---+---+
//! ```
//! As shown above, the doves on the board slide automatically
//! even if the target position is out of display,
//! as far as the action is legal.
//! See the documentation of [`Action`]
//! for information about how to create actions.
//!
//! After several turns, the game is coming to the end.
//! ```rust
//! # use std::str::FromStr;
//! # use tokyodoves::*;
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! # let board = BoardBuilder::from_str(" bHh;AB M;m aY; T t")?.build()?;
//! println!("{board}");
//! // +---+---+---+---+
//! // |   | b | H | h |
//! // +---+---+---+---+
//! // | A | B |   | M |
//! // +---+---+---+---+
//! // | m |   | a | Y |
//! // +---+---+---+---+
//! // |   | T |   | t |
//! // +---+---+---+---+
//! # Ok(())
//! # }
//! ```
//! The [`surrounded_status`](`Board::surrounded_status`) on [`Board`]
//! provides a way to check the game is ended.
//! ```rust
//! # use std::str::FromStr;
//! # use tokyodoves::*;
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! # let mut board = BoardBuilder::from_str(" bHh;AB M;m aY; T t")?.build()?;
//! let status = board.surrounded_status();
//! assert!(
//!     matches!(status, SurroundedStatus::None)
//! );
//! board.perform(Action::Move(Color::Red, Dove::A, Shift::new(-1, 0)));
//! println!("{board}");
//! // +---+---+---+---+
//! // | A | b | H | h |
//! // +---+---+---+---+
//! // |   | B |   | M |
//! // +---+---+---+---+
//! // | m |   | a | Y |
//! // +---+---+---+---+
//! // |   | T |   | t |
//! // +---+---+---+---+
//! let status = board.surrounded_status();
//! assert!(
//!     matches!(status, SurroundedStatus::OneSide(Color::Green))
//! );
//! # Ok(())
//! # }
//! ```
//!
//! # Play more
//! Although the codes in the last section are sufficient to play the game,
//! this crate provides a [`game`] module,
//! which lets you to realize this in more short codes.
//! This module is available if you indicate the feature "game".
//! See the examples in the [`Game`](`crate::game::Game`) struct of [`game`] module.
//! This module also provides an [`Arena`](`crate::game::Arena`),
//! where two [`Agent`](crate::game::Agent`)s play against.
//! See the documentation of the [`game`] module for more.
//!
//! # Analyze the game
//! If you are absorbed in Tokyo Doves, you want to analyze the game much more deeply.
//! The [`analysis`] module provides several tools for analyses,
//! including a function finding routes to the game end
//! and a function suggesting the best actions that should be performed next.
//! See the documentation of the module for more.
//!
//! If you want to pool a large number of [`Board`]s during your analyses,
//! the [`BoardSet`](`collections::BoardSet`) struct in the [`collections`] module must be useful.
//! It provides not only methods to pool a lot of [`Board`]s,
//! but also methods to save to/load from a binary file.
//! See its documentation for more.
//!
//! These modules are available if you indicate the feature "analysis".
//!
//! # About feature flags
//! The following three features are available:
//! - no flag: Only basic board and related entities are included
//! - "game": Entities related to game playing are included (those which are described in "Play more" section).
//! - "analysis": Tools for analysis and collections are included (those which are described in "Analyze the game" section).
//! It also includes those for "game" feature, and [`AnalystAgent`](`game::AnalystAgent`) additionally.
//!
//! See "features" page of "The Cargo Book" below for information about how to indicate features:<br>
//! <https://doc.rust-lang.org/cargo/reference/features.html>

pub use array_macro;
pub use strum;
pub use strum_macros;
pub use thiserror;

#[cfg(feature = "analysis")]
pub mod analysis;
#[cfg(feature = "analysis")]
pub mod collections;
pub mod error;

#[cfg(feature = "game")]
pub mod game;

mod prelude;

pub use prelude::*;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn random_play() {
        fn _get_next(n: usize) -> usize {
            (33 * n + 31) % 65536
        }

        use Color::*;
        let mut n = 0;
        let num_games = 10_000;
        for _ in 0..num_games {
            let mut board = Board::new();
            let mut player = Red;
            loop {
                n = _get_next(n);
                let actions = board.legal_actions(player, true, true, true);
                assert!(actions.len() > 0);
                let action = actions[n % actions.len()];
                assert!(board.perform(action).is_ok());

                if !matches!(board.surrounded_status(), SurroundedStatus::None) {
                    break;
                }

                player = !player;
            }
        }
    }

    #[test]
    fn random_play_bwd() {
        fn _get_next(n: usize) -> usize {
            (33 * n + 31) % 65536
        }

        use Color::*;
        let mut n = 0;
        let num_games = 10_000;
        for _ in 0..num_games {
            let mut board = Board::new();
            let mut player = Red;
            loop {
                n = _get_next(n);
                let actions = board.legal_actions_bwd(player, true, true, true);
                assert!(actions.len() > 0);
                let action = actions[n % actions.len()];
                assert!(board.perform_bwd(action).is_ok());

                if !matches!(board.surrounded_status(), SurroundedStatus::None) {
                    break;
                }

                player = !player;
            }
        }
    }
}
