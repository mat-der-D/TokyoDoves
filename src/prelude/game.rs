use super::board::{ActionsFwd, Board};
use super::builder::BoardBuilder;
use super::error;
use crate::prelude::{Action, Color};
use crate::SurroundedStatus;

// ************************************************************
//  Building Blocks
// ************************************************************
/// Some kinds of detailed rules
///
/// # Examples
/// ```ignore
/// use std::str::FromStr;
/// use tokyodoves::{GameRule, Color, Board, WinnerJudgement, BoardBuilder};
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// // Set whether `Remove` is allowed or not
/// let rule = GameRule::new(true);
/// // Auto setting (allow `Remove`)
/// let rule = GameRule::default();
/// // Allow `Remove` and `Color::Green` moves first
/// let rule = GameRule::new(true).with_first_player(Color::Green);
/// // Set board you like as the initial board (requires error handling)
/// let initial_board = BoardBuilder::from_str("B;bh")?.build()?;
/// let rule = GameRule::default().with_initial_board(initial_board)?;
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone, Copy)]
pub struct GameRule {
    /// Allow [`Action::Remove`] as a legal action or not
    allow_remove: bool,
    /// The player who moves first
    first_player: Color,
    /// Winner judgement when both bosses are surrounded simultaneously
    simultaneous_surrounding: WinnerJudgement,
    /// Initial board
    initial_board: Board,
}

impl GameRule {
    /// Constructs [`GameRule`] object
    ///
    /// The values of fields are as below:
    /// - `first_player`: `Color::Red`
    /// - `simultaneous_surrounding`: `WinnerJudgement::NextPlayer`
    /// - `initial_board`: `BoardConverter::new_game().board`
    pub fn new(allow_remove: bool) -> Self {
        let first_player = Color::Red;
        let simultaneous_surrounding = WinnerJudgement::NextPlayer;
        let initial_board = BoardBuilder::new().build_unchecked();
        Self {
            allow_remove,
            first_player,
            simultaneous_surrounding,
            initial_board,
        }
    }

    pub fn allow_remove(&self) -> &bool {
        &self.allow_remove
    }

    pub fn first_player(&self) -> &Color {
        &self.first_player
    }

    pub fn simultaneous_surrounding(&self) -> &WinnerJudgement {
        &self.simultaneous_surrounding
    }

    pub fn initial_board(&self) -> &Board {
        &self.initial_board
    }

    /// Update whether allow `Remove` in the game or not
    pub fn set_allow_remove(self, allow_remove: bool) -> Self {
        Self {
            allow_remove,
            ..self
        }
    }

    /// Update the player moving firstly in the beginning of the game
    pub fn with_first_player(self, first_player: Color) -> Self {
        Self {
            first_player,
            ..self
        }
    }

    /// Update judgement rule when both bosses are surrounded simultaneously
    pub fn with_simultaneous_surrounding(self, simultaneous_surrounding: WinnerJudgement) -> Self {
        Self {
            simultaneous_surrounding,
            ..self
        }
    }

    /// Update initial_board of [`GameRule`]
    ///
    /// # Errors
    /// It returns:
    /// - `Err(error::GameRuleError::InitialBoardError)`
    ///     if `initial_board` is that of finished game
    pub fn with_initial_board(self, initial_board: Board) -> Result<Self, error::GameRuleError> {
        if !matches!(initial_board.surrounded_status(), SurroundedStatus::None) {
            return Err(error::GameRuleError::InitialBoardError);
        }
        let rule = Self {
            initial_board,
            ..self
        };
        Ok(rule)
    }
}

impl Default for GameRule {
    /// Returns the default value.
    ///
    /// The default values of fields are as below:
    /// - `allow_remove`: `true`
    /// - others: follow setting in [`Self::new`]
    fn default() -> Self {
        Self::new(true)
    }
}

/// Judgement of winner on some event
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum WinnerJudgement {
    /// The player just before the event is treated as the winner
    LastPlayer,
    /// The player just after the event is treated as the winner
    NextPlayer,
    /// It is a draw game
    Draw,
}

/// Status of the game
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GameStatus {
    /// The game is ongoing
    Ongoing,
    /// The game has already finished; one player defeated the other
    Win(Color),
    /// The game has already finished; it was a draw game
    Draw,
}

// ************************************************************
//  Main Part
// ************************************************************
/// A struct that provides methods to play Tokyo Doves games following rules.
///
/// # Examples
/// The following is a simple example in which one game is played:
/// ```ignore
/// use tokyodoves::{ActionContainer, Game};
///
/// fn main() -> Result<(), Box<dyn std::error::Error>> {
///     // Create a [`Game`] object allowing `Remove` action
///     let mut game = Game::new(true);
///     // Displays the status of the game
///     println!("{}", game);
///
///     let mut turn = 0;
///     loop {
///         turn += 1;
///         // Collects all possible actions
///         let actions = game.actions();
///         // Selects one of them by methods of ActionContainer trait
///         let action = actions[turn % actions.len()];
///         println!("  --> {}", action.to_ssn(game.board())?);
///
///         game.perform(action)?; // Performs the selected action
///         println!("{}", game);
///
///         if !game.is_ongoing() { // If the game is not ongoing...
///             break; // breaks the loop!
///         }
///     }
///
///     match game.winner() { // Who won the game?
///         Some(player) => println!("*** {:?} win! ***", player), // A player won the game
///         None => println!("*** Draw! ***"), // It was a draw game
///     }
///
///     Ok(())
/// }
/// ```
/// To customize the rule more, you can create [`Game`] from [`GameRule`] object:
/// ```ignore
/// use tokyodoves::{Color, Game, GameRule};
///
/// # fn main() {
/// let mut rule = GameRule::default().set_allow_remove(false).with_first_player(Color::Green);
/// let game = Game::from_rule(rule);
/// println!("{}", game);
/// # }
/// ```
/// For more information about the default value of [`GameRule`],
/// see [the documentation about the implementation of `Default` trait
/// for `GameRule`](`GameRule::default`)
#[derive(Debug, Clone, Copy)]
pub struct Game {
    board: Board,
    player: Color,
    status: GameStatus,
    rule: GameRule,
}

impl Game {
    /// Constructs [`Game`]
    pub fn new(allow_remove: bool) -> Game {
        let mut rule = GameRule::default();
        rule.allow_remove = allow_remove;
        Self::from_rule(rule)
    }

    /// Constructs [`Game`] with a specified `rule`
    pub fn from_rule(rule: GameRule) -> Game {
        let board = rule.initial_board;
        let player = rule.first_player;
        let status = GameStatus::Ongoing;
        Game {
            board,
            player,
            status,
            rule,
        }
    }

    /// Reset [`Game`] to the initial state
    pub fn reset(&mut self) {
        *self = Self::from_rule(self.rule)
    }

    /// Get a reference to game rule
    pub fn rule(&self) -> &GameRule {
        &self.rule
    }

    /// Get a reference to board
    pub fn board(&self) -> &Board {
        &self.board
    }

    /// Get a reference to the next player
    pub fn next_player(&self) -> &Color {
        &self.player
    }

    /// Get a reference to status
    pub fn status(&self) -> &GameStatus {
        &self.status
    }

    /// Returns `true` if the game is ongoing
    pub fn is_ongoing(&self) -> bool {
        matches!(self.status, GameStatus::Ongoing)
    }

    /// Returns winner.
    ///
    /// It returns `Some(Color)` if winner has been determined.
    /// It returns `None` if the game is ongoing or draw.
    pub fn winner(&self) -> Option<Color> {
        use GameStatus::*;
        match self.status {
            Ongoing | Draw => None,
            Win(player) => Some(player),
        }
    }

    /// Returns an [`ActionContainer`](`super::container::ActionContainer`) of legal [`Action`]s.
    pub fn actions(&self) -> ActionsFwd {
        self.board
            .legal_actions(self.player, true, true, self.rule.allow_remove)
    }

    /// Performs `action`.
    ///
    /// # Errors
    /// It returns:
    /// - `Err(error::GameError::GameFinishedError)` if the game has already been finished.
    /// - `Err(error::GameError::PlayerMismatchError)` if the player of `action`
    ///     is different from the next player.
    /// - `Err(error::GameError::BoardError { .. })` if performing `action` is illegal for board.
    ///
    /// In any cases, `Game` object is left unchanged.
    pub fn perform(&mut self, action: Action) -> Result<(), error::GameError> {
        if !self.is_ongoing() {
            return Err(error::GameError::GameFinishedError {
                game_status: self.status,
            });
        }

        if self.player != *action.player() {
            return Err(error::GameError::PlayerMismatchError);
        }

        if !self.rule.allow_remove && matches!(action, Action::Remove(_, _)) {
            return Err(error::GameError::ProhibitedRemoveError { action });
        }

        self.board
            .perform(action)
            .map_err(|e| error::GameError::BoardError { error: e })?;

        use GameStatus::*;
        use SurroundedStatus::*;
        match self.board.surrounded_status() {
            Both => match self.rule.simultaneous_surrounding {
                WinnerJudgement::LastPlayer => self.status = Win(self.player),
                WinnerJudgement::NextPlayer => self.status = Win(!self.player),
                WinnerJudgement::Draw => self.status = Draw,
            },
            OneSide(player) => self.status = Win(!player),
            None => self.player = !self.player,
        }

        Ok(())
    }
}

impl std::fmt::Display for Game {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let board_string = self.board.to_string();
        let next_player_string = if self.is_ongoing() {
            format!("{:?}", self.player)
        } else {
            String::from("None")
        };
        write!(f, "{}\nNext Player: {}", board_string, next_player_string)
    }
}
