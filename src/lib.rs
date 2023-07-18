//! Crate Description

pub use array_macro;
pub use strum;
pub use strum_macros;
pub use thiserror;

pub mod analysis;
pub mod collections;
pub mod error;
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
