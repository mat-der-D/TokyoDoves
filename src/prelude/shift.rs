/// Difference of coordinates between two squares.
///
/// It has two data `dh`, i.e. the **h**orizonal difference,
/// and `dv`, i.e. the **v**ertical difference.
/// Positive/negative `dh` means the direction is on right/left.
/// Positive/negative `dv` means the direction is on downwards/upwards.
/// These data can be accessed
/// via [`dh`](`Self::dh`), [`dv`](`Self::dv`),
/// [`dh_mut`](`Self::dh_mut`) and [`dv_mut`](`Self::dv_mut`).
///
/// This struct supports addition, subtraction and negation.
/// ```ignore
/// use tokyodoves::Shift;
///
/// assert_eq!(-Shift::new(2, 3), Shift::new(-2, -3));
/// assert_eq!(Shift::new(1, 1) + Shift::new(2, 0), Shift::new(3, 1));
/// assert_eq!(Shift::new(2, -1) - Shift::new(1, -2), Shift::new(1, 1));
/// ```
///
/// Pedantically speaking, this struct behaves like
/// an element in two-dimensional Affine space with integral coordinates
/// without scalar multiplication.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Shift {
    /// Horizontal shift. Positive (or negative) direction is on right (or left).
    pub(crate) dh: i8,
    /// Vertical shift. Positive (or negative) direction is on downwards (or upwards).
    pub(crate) dv: i8,
}

impl Shift {
    /// Constructs [`Shift`].
    pub fn new(dh: i8, dv: i8) -> Self {
        Self { dh, dv }
    }

    /// Returns a reference to vertical difference of coordinates.
    pub fn dh(&self) -> &i8 {
        &self.dh
    }

    /// Returns a reference to horizontal difference of coordinates.
    pub fn dv(&self) -> &i8 {
        &self.dv
    }

    /// Returns a mutable reference to vertical difference of coordinates.
    pub fn dh_mut(&mut self) -> &mut i8 {
        &mut self.dh
    }

    /// Returns a mutable reference to horizontal difference of coordinates.
    pub fn dv_mut(&mut self) -> &mut i8 {
        &mut self.dv
    }
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
