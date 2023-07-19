use crate::error;
use crate::prelude::{
    board::main::Board,
    pieces::{color_dove_to_char, try_char_to_color_dove, Color, Dove},
    Shift,
};

/// Actions players can perform in their turn.
///
/// The definition of the Standard Short Notation (SSN) is given below.
///
/// Consider a coordinate system centered at red boss.
/// ```text
///         W3   W2   W1         E1   E2   E3
///       +----+----+----+-----+----+----+----+
///   N3  |    |    |    |     |    |    |    |
///       +----+----+----+-----+----+----+----+
///   N2  |    |    |    |     | ** |    |    |
///       +----+----+----+-----+----+----+----+
///   N1  |    |    |    |     |    |    |    |
///       +----+----+----+-----+----+----+----+
///       |    |    |    |  B  |    |    | @@ |
///       +----+----+----+-----+----+----+----+
///   S1  |    |    |    |     |    |    |    |
///       +----+----+----+-----+----+----+----+
///   S2  |    |    |    |  ?  |    |    |    |
///       +----+----+----+-----+----+----+----+
///   S3  |    |    |    |     |    |    |    |
///       +----+----+----+-----+----+----+----+
/// ```
/// - The coordinate of "**" is written in "N2E1".
/// - The coordinate of "@@" is written in "E3".
/// - The coordinate of "?" is written in "S2".
///
/// Then the target positions of all legal actions are included in the above 7x7 squares,
/// where the "target position" means:
/// - for `Action::Put`, the square on which the dove will be put
/// - for `Action::Move`, the square to which the dove moves
/// - for `Action::Remove`, the target position not defined
///
/// Then the following notation is available:
/// - For `Action::Put` => +{dove char}{target position} (e.g. "+AN2E1")
/// - For `Action::Move` => {dove char}{target position} (e.g. "mE2")
/// - For `Action::Remove` => -{dove char} (e.g. "-t")
///
/// To identify "dove char", see the table in the documentation of [`color_dove_to_char`].
///
/// Now the notation above is named SSN.
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
    /// Returns a reference to the player of the action.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Action, Color, Dove};
    ///
    /// let action = Action::Remove(Color::Red, Dove::H);
    /// assert!(matches!(action.player(), Color::Red));
    /// ```
    pub fn player(&self) -> &Color {
        use Action::*;
        match self {
            Put(player, _, _) => player,
            Move(player, _, _) => player,
            Remove(player, _) => player,
        }
    }

    /// Returns a reference to the dove of the action.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Action, Color, Dove};
    ///
    /// let action = Action::Remove(Color::Red, Dove::H);
    /// assert!(matches!(action.dove(), Dove::H));
    /// ```
    pub fn dove(&self) -> &Dove {
        use Action::*;
        match self {
            Put(_, dove, _) => dove,
            Move(_, dove, _) => dove,
            Remove(_, dove) => dove,
        }
    }

    /// Returns a reference to the shift of the action.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Action, Color, Dove, Shift};
    ///
    /// let action1 = Action::Remove(Color::Red, Dove::H);
    /// assert!(action1.shift().is_none());
    /// let action2 = Action::Move(Color::Red, Dove::B, Shift::new(1, 0));
    /// assert_eq!(Shift::new(1, 0), *action2.shift().unwrap());
    /// ```
    pub fn shift(&self) -> Option<&Shift> {
        use Action::*;
        match self {
            Put(_, _, shift) => Some(shift),
            Move(_, _, shift) => Some(shift),
            Remove(_, _) => None,
        }
    }

    /// Converts `self` into `String` in SSN.
    ///
    /// See the documentation of [`Action`] for the definition of SSN.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Board, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = Board::new();
    /// let action = Action::Put(Color::Red, Dove::A, Shift::new(1, 0));
    /// let ssn = action.try_into_ssn(&board)?;
    /// assert_eq!(ssn, "+AS1");
    /// # Ok(())
    /// # }
    /// ```
    pub fn try_into_ssn(self, board: &Board) -> Result<String, error::Error> {
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
            format!("{ns}{ns_num}{ew}{ew_num}")
        }

        use error::EncodingErrorKind::*;
        use Action::*;
        match self {
            Put(c, d, s) => {
                let Some(pos_boss) = board.position_in_rbcc(c, Dove::B) else {
                    return Err(BossNotFound(c).into());
                };
                let exp = format!(
                    "+{0}{1}",
                    color_dove_to_char(c, d),
                    _shift_to_string(s + pos_boss)
                );
                Ok(exp)
            }
            Move(c, d, s) => {
                let Some(pos) = board.position_in_rbcc(c, d) else {
                    return Err(DoveNotFound(c, d).into());
                };
                let exp = format!(
                    "{0}{1}",
                    color_dove_to_char(c, d),
                    _shift_to_string(pos + s)
                );
                Ok(exp)
            }
            Remove(c, d) => {
                let exp = format!("-{}", color_dove_to_char(c, d));
                Ok(exp)
            }
        }
    }

    /// Creates `Action` from `&str` in Standard Short Notation (SSN)
    ///
    /// See the documentation of [`Action`] for the definition of SSN.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Board, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = Board::new();
    /// let ssn = "+AS1";
    /// let action = Action::try_from_ssn(ssn, &board)?;
    /// assert_eq!(action, Action::Put(Color::Red, Dove::A, Shift::new(1, 0)));
    /// # Ok(())
    /// # }
    /// ```
    pub fn try_from_ssn(ssn: &str, board: &Board) -> Result<Action, error::Error> {
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

            fn process(&mut self, c: char) -> Result<(), error::Error> {
                use error::DecodingErrorKind::*;
                match c {
                    '+' => self.action_type = ActionType::Put,
                    '-' => self.action_type = ActionType::Remove,
                    'N' => self.dv_sign = Sign::Minus,
                    'S' => self.dv_sign = Sign::Plus,
                    'E' => self.dh_sign = Sign::Plus,
                    'W' => self.dh_sign = Sign::Minus,
                    x if Self::COLOR_DOVE_CHAR.contains(&x) => {
                        let Some((color, dove)) = try_char_to_color_dove(x) else {
                            unreachable!();
                        };
                        self.dove = Some(dove);
                        self.color = Some(color);
                    }
                    x if Self::NUMBER_CHAR.contains(&x) => {
                        let n = x.to_string().parse::<i8>().unwrap();
                        use UpdateHeader::*;
                        match self.update_header {
                            None => return Err(NumberNotFollowAfterNEWS.into()),
                            DV => self.dv_abs = n,
                            DH => self.dh_abs = n,
                        }
                    }
                    x => return Err(UnexpectedCharacter(x).into()),
                }

                use UpdateHeader::*;
                match c {
                    'N' | 'S' => self.update_header = DV,
                    'E' | 'W' => self.update_header = DH,
                    _ => self.update_header = None,
                }
                Ok(())
            }

            fn try_into_action(self, board: &Board) -> Result<Action, error::Error> {
                use error::DecodingErrorKind::*;
                use ActionType::*;
                let Some(color) = self.color else { return Err(ColorNotInferred.into()) };
                let Some(dove) = self.dove else { return Err(DoveNotInferred.into()) };

                match self.action_type {
                    Put => {
                        let dh = self.dh_sign * self.dh_abs;
                        let dv = self.dv_sign * self.dv_abs;
                        let shift = Shift { dh, dv };
                        let Some(pos) = board.position_in_rbcc(color, Dove::B) else {
                            return Err(BossNotFound(color).into());
                        };
                        Ok(Action::Put(color, dove, -pos + shift))
                    }
                    Move => {
                        let dh = self.dh_sign * self.dh_abs;
                        let dv = self.dv_sign * self.dv_abs;
                        let shift = Shift { dh, dv };
                        let Some(pos) = board.position_in_rbcc(color, dove) else {
                            return Err(DoveNotOnBoard(color, dove).into());
                        };
                        Ok(Action::Move(color, dove, -pos + shift))
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
