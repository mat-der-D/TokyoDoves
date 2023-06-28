mod board;
mod builder;
mod game;
mod macros;

pub mod error;
pub use board::*;
pub use builder::*;
pub use game::*;

use std::str::FromStr;
use strum_macros::{EnumIter, EnumString};

/// Two colors of player, just like black and white in chess.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, EnumIter)]
pub enum Color {
    Red,
    Green,
}

impl std::ops::Not for Color {
    type Output = Color;
    fn not(self) -> Self::Output {
        use Color::*;
        match self {
            Red => Green,
            Green => Red,
        }
    }
}

/// Six types of doves.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, EnumIter, EnumString)]
pub enum Dove {
    /// Represents **B**oss-hato,
    /// which can move to adjacent squares in all eight directions,
    /// just like the King in chess.
    /// A player loses when their boss-hato is completely surrounded.
    /// ```text
    /// +---+---+---+---+---+
    /// |   |   |   |   |   |
    /// +---+---+---+---+---+
    /// |   | * | * | * |   |
    /// +---+---+---+---+---+
    /// |   | * | B | * |   |
    /// +---+---+---+---+---+
    /// |   | * | * | * |   |
    /// +---+---+---+---+---+
    /// |   |   |   |   |   |
    /// +---+---+---+---+---+
    /// ```
    #[strum(ascii_case_insensitive)]
    B,
    /// Represents **A**niki-hato,
    /// which can move to adjacent squares in all eight directions,
    /// just like the King in chess.
    /// ```text
    /// +---+---+---+---+---+
    /// |   |   |   |   |   |
    /// +---+---+---+---+---+
    /// |   | * | * | * |   |
    /// +---+---+---+---+---+
    /// |   | * | A | * |   |
    /// +---+---+---+---+---+
    /// |   | * | * | * |   |
    /// +---+---+---+---+---+
    /// |   |   |   |   |   |
    /// +---+---+---+---+---+
    /// ```
    #[strum(ascii_case_insensitive)]
    A,
    /// Represents **Y**aibato,
    /// which can move to four adjacent squares,
    /// forward, backward or sideways,
    /// just like '+'.
    /// ```text
    /// +---+---+---+---+---+
    /// |   |   |   |   |   |
    /// +---+---+---+---+---+
    /// |   |   | * |   |   |
    /// +---+---+---+---+---+
    /// |   | * | Y | * |   |
    /// +---+---+---+---+---+
    /// |   |   | * |   |   |
    /// +---+---+---+---+---+
    /// |   |   |   |   |   |
    /// +---+---+---+---+---+
    /// ```
    #[strum(ascii_case_insensitive)]
    Y,
    /// Represents **M**amedeppo-bato,
    /// which can move to four diagonally adjacent squares,
    /// just like 'x'.
    /// ```text
    /// +---+---+---+---+---+
    /// |   |   |   |   |   |
    /// +---+---+---+---+---+
    /// |   | * |   | * |   |
    /// +---+---+---+---+---+
    /// |   |   | M |   |   |
    /// +---+---+---+---+---+
    /// |   | * |   | * |   |
    /// +---+---+---+---+---+
    /// |   |   |   |   |   |
    /// +---+---+---+---+---+
    /// ```
    #[strum(ascii_case_insensitive)]
    M,
    /// Represents **T**otsu-hato,
    /// which can move forward, backward or sideways,
    /// through any number of squares,
    /// just like the Rook in chess.
    /// ```text
    /// +---+---+---+---+---+
    /// |   |   | * |   |   |
    /// +---+---+---+---+---+
    /// |   |   | * |   |   |
    /// +---+---+---+---+---+
    /// | * | * | T | * | * |
    /// +---+---+---+---+---+
    /// |   |   | * |   |   |
    /// +---+---+---+---+---+
    /// |   |   | * |   |   |
    /// +---+---+---+---+---+
    /// ```
    #[strum(ascii_case_insensitive)]
    T,
    /// Represents **H**ajike-hato,
    /// which can move (or jump) like the Knight in chess.
    /// ```text
    /// +---+---+---+---+---+
    /// |   | * |   | * |   |
    /// +---+---+---+---+---+
    /// | * |   |   |   | * |
    /// +---+---+---+---+---+
    /// |   |   | H |   |   |
    /// +---+---+---+---+---+
    /// | * |   |   |   | * |
    /// +---+---+---+---+---+
    /// |   | * |   | * |   |
    /// +---+---+---+---+---+
    /// ```
    #[strum(ascii_case_insensitive)]
    H,
}

/// Difference between two squares.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Shift {
    /// Horizontal shift. Positive (or negative) direction is on right (or left).
    pub dh: i8,
    /// Vertical shift. Positive (or negative) direction is on downwards (or upwards).
    pub dv: i8,
}

impl std::ops::Add for Shift {
    type Output = Shift;
    fn add(self, rhs: Self) -> Self::Output {
        Shift {
            dh: self.dh + rhs.dh,
            dv: self.dv + rhs.dv,
        }
    }
}

impl std::ops::Neg for Shift {
    type Output = Shift;
    fn neg(self) -> Self::Output {
        Shift {
            dh: -self.dh,
            dv: -self.dv,
        }
    }
}

impl std::ops::Sub for Shift {
    type Output = Shift;
    fn sub(self, rhs: Self) -> Self::Output {
        Shift {
            dh: self.dh - rhs.dh,
            dv: self.dv - rhs.dv,
        }
    }
}

/// Actions players can perform in their turn.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Action {
    /// Put [`Dove`] from [`Color`]'s hand on the board
    /// at the position shifted from [`Color`]'s boss-hato
    /// by [`Shift`].
    Put(Color, Dove, Shift),
    /// Move [`Color`]'s [`Dove`] on the board
    /// toward [`Shift`] from its current position
    Move(Color, Dove, Shift),
    /// Remove [`Color`]'s [`Dove`] from the board
    /// (which returns to [`Color`]'s hand)
    Remove(Color, Dove),
}

impl Action {
    pub fn player(&self) -> &Color {
        use Action::*;
        match self {
            Put(player, _, _) => player,
            Move(player, _, _) => player,
            Remove(player, _) => player,
        }
    }

    pub fn dove(&self) -> &Dove {
        use Action::*;
        match self {
            Put(_, dove, _) => dove,
            Move(_, dove, _) => dove,
            Remove(_, dove) => dove,
        }
    }

    pub fn shift(&self) -> Option<&Shift> {
        use Action::*;
        match self {
            Put(_, _, shift) => Some(shift),
            Move(_, _, shift) => Some(shift),
            Remove(_, _) => None,
        }
    }

    /// Converts `self` into `String` in Standard Short Notation (SSN)
    pub fn to_ssn(self, board: &Board) -> Result<String, error::ActionConvertError> {
        fn _color_dove_to_string(color: Color, dove: Dove) -> String {
            use Color::*;
            let base = format!("{:?}", dove);
            match color {
                Red => base.to_ascii_uppercase(),
                Green => base.to_ascii_lowercase(),
            }
        }

        fn _shift_to_string(shift: Shift) -> String {
            let (ns, ns_num) = match shift.dv {
                x if x > 0 => ("S", x.to_string()),
                x if x < 0 => ("N", (-x).to_string()),
                _ => ("", "".to_string()),
            };
            let (ew, ew_num) = match shift.dh {
                x if x > 0 => ("E", x.to_string()),
                x if x < 0 => ("W", (-x).to_string()),
                _ => ("", "".to_string()),
            };
            format!("{}{}{}{}", ns, ns_num, ew, ew_num)
        }

        use error::ActionConvertError::SSNEncodingError;
        use error::SSNEncodingErrorType::*;
        use Action::*;
        match self {
            Put(c, d, s) => {
                let Some(pos_boss) = board.position_in_rbcc(c, Dove::B) else {
                    return Err(SSNEncodingError { error_type: BossNotFound(c) });
                };
                let exp = format!(
                    "+{}{}",
                    _color_dove_to_string(c, d),
                    _shift_to_string(s + pos_boss)
                );
                Ok(exp)
            }
            Move(c, d, s) => {
                let Some(pos) = board.position_in_rbcc(c, d) else {
                    return Err(SSNEncodingError { error_type: DoveNotFound(c, d) });
                };
                let exp = format!(
                    "{}{}",
                    _color_dove_to_string(c, d),
                    _shift_to_string(pos + s)
                );
                Ok(exp)
            }
            Remove(c, d) => {
                let exp = format!("-{}", _color_dove_to_string(c, d));
                Ok(exp)
            }
        }
    }

    /// Creates `Action` from `&str` in Standard Short Notation (SSN)
    pub fn from_ssn(ssn: &str, board: &Board) -> Result<Action, error::ActionConvertError> {
        enum ActionType {
            Put,
            Move,
            Remove,
        }

        enum Sign {
            Plus,
            Minus,
            Zero,
        }

        impl std::ops::Mul<i8> for Sign {
            type Output = i8;
            fn mul(self, rhs: i8) -> Self::Output {
                match self {
                    Sign::Plus => rhs,
                    Sign::Minus => -rhs,
                    Sign::Zero => 0,
                }
            }
        }

        enum UpdateHeader {
            DV,
            DH,
            None,
        }

        struct SSNDecoder {
            action_type: ActionType,
            color: Option<Color>,
            dove: Option<Dove>,
            dv_sign: Sign,
            dv_abs: i8,
            dh_sign: Sign,
            dh_abs: i8,
            update_header: UpdateHeader,
        }

        impl Default for SSNDecoder {
            fn default() -> Self {
                Self {
                    action_type: ActionType::Move,
                    color: None,
                    dove: None,
                    dv_sign: Sign::Zero,
                    dv_abs: 0,
                    dh_sign: Sign::Zero,
                    dh_abs: 0,
                    update_header: UpdateHeader::None,
                }
            }
        }

        impl SSNDecoder {
            const COLOR_DOVE_CHAR: [char; 12] =
                ['B', 'b', 'A', 'a', 'Y', 'y', 'M', 'm', 'T', 't', 'H', 'h'];
            const NUMBER_CHAR: [char; 9] = ['1', '2', '3', '4', '5', '6', '7', '8', '9'];

            fn process(&mut self, c: char) -> Result<(), error::ActionConvertError> {
                use error::ActionConvertError::SSNDecodingError;
                use error::SSNDecodingErrorType::*;
                match c {
                    '+' => self.action_type = ActionType::Put,
                    '-' => self.action_type = ActionType::Remove,
                    'N' => self.dv_sign = Sign::Minus,
                    'S' => self.dv_sign = Sign::Plus,
                    'E' => self.dh_sign = Sign::Plus,
                    'W' => self.dh_sign = Sign::Minus,
                    x if Self::COLOR_DOVE_CHAR.contains(&x) => {
                        let dove = Dove::from_str(&x.to_string()).unwrap();
                        let color = if x.is_ascii_uppercase() {
                            Color::Red
                        } else {
                            Color::Green
                        };
                        self.dove = Some(dove);
                        self.color = Some(color);
                    }
                    x if Self::NUMBER_CHAR.contains(&x) => {
                        let n = x.to_string().parse::<i8>().unwrap();
                        use UpdateHeader::*;
                        match self.update_header {
                            None => {
                                return Err(SSNDecodingError {
                                    error_type: NumberNotFollowAfterNEWS,
                                })
                            }
                            DV => self.dv_abs = n,
                            DH => self.dh_abs = n,
                        }
                    }
                    x => {
                        return Err(SSNDecodingError {
                            error_type: UnexpectedCharacter(x),
                        })
                    }
                }

                use UpdateHeader::*;
                match c {
                    'N' | 'S' => self.update_header = DV,
                    'E' | 'W' => self.update_header = DH,
                    _ => self.update_header = None,
                }
                Ok(())
            }

            fn try_into_action(self, board: &Board) -> Result<Action, error::ActionConvertError> {
                use error::ActionConvertError::SSNDecodingError;
                use error::SSNDecodingErrorType::*;
                use ActionType::*;
                let Some(color) = self.color else { return Err(SSNDecodingError { error_type: ColorNotInferred }) };
                let Some(dove) = self.dove else { return Err(SSNDecodingError { error_type: DoveNotInferred }) };

                match self.action_type {
                    Put => {
                        let dh = self.dh_sign * self.dh_abs;
                        let dv = self.dv_sign * self.dv_abs;
                        let shift = Shift { dh, dv };
                        let Some(pos) = board.position_in_rbcc(color, Dove::B) else {
                            return Err(SSNDecodingError { error_type: BossNotFound });
                        };
                        Ok(Action::Put(color, dove, -pos + shift))
                    }
                    Move => {
                        let dh = self.dh_sign * self.dh_abs;
                        let dv = self.dv_sign * self.dv_abs;
                        let shift = Shift { dh, dv };
                        let Some(pos) = board.position_in_rbcc(color, dove) else {
                            return Err(SSNDecodingError { error_type: DoveNotOnBoard(color, dove) });
                        };
                        Ok(Action::Put(color, dove, -pos + shift))
                    }
                    Remove => Ok(Action::Remove(color, dove)),
                }
            }
        }

        let mut decoder = SSNDecoder::default();
        for c in ssn.chars() {
            decoder.process(c)?;
        }
        decoder.try_into_action(board)
    }
}
