use crate::prelude::macros;

const CONGRUENT_MAPS: [[[usize; 16]; 8]; 16] = {
    // (hsize - 1) + 4 * (vsize - 1)
    let rotate_maps = [
        [0, 4, 8, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], // vsize == 1
        [1, 5, 9, 13, 0, 4, 8, 12, 0, 0, 0, 0, 0, 0, 0, 0], // vsize == 2
        [2, 6, 10, 14, 1, 5, 9, 13, 0, 4, 8, 12, 0, 0, 0, 0], // vsize == 3
        [3, 7, 11, 15, 2, 6, 10, 14, 1, 5, 9, 13, 0, 4, 8, 12], // vsize == 4
    ];

    let reflect_maps = [
        [0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], // vsize == 1
        [4, 5, 6, 7, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0], // vsize == 2
        [8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3, 0, 0, 0, 0], // vsize == 3
        [12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], // vsize == 4
    ];

    let mut cons = [[[0_usize; 16]; 8]; 16];
    macros::for_loop!(let mut vsize = 1; vsize < 5; vsize += 1 => {
        macros::for_loop!(let mut hsize = 1; hsize < 5; hsize += 1 => {
            let idx = (hsize - 1) + 4 * (vsize - 1);
            let mut count = 0;
            let mut base = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];

            macros::for_loop!(let mut i = 0; i < 2; i += 1 => {
                macros::for_loop!(let mut j = 0; j < 2; j += 1 => {
                    macros::for_loop!(let mut k = 0; k < 2; k += 1 => {
                        let hvsize = if k % 2 == 0 { vsize } else { hsize };
                        base = compose(rotate_maps[hvsize - 1], base);
                        cons[idx][count] = base;
                        count += 1;
                    }); // k
                }); // j
                base = compose(reflect_maps[vsize - 1], base);
            }); // i
        }); // hsize
    }); // vsize

    cons
};

const fn compose(a: [usize; 16], b: [usize; 16]) -> [usize; 16] {
    let mut a_after_b = [0_usize; 16];
    macros::for_loop!(let mut i = 0; i < 16; i += 1 => {
        a_after_b[i] = a[b[i]];
    });
    a_after_b
}

#[derive(Debug, Clone, Copy)]
pub struct PositionMapper {
    maps: &'static [[usize; 16]; 8],
}

impl PositionMapper {
    pub fn try_create(vsize: usize, hsize: usize) -> Option<Self> {
        if vsize == 0 || vsize >= 5 || hsize == 0 || hsize >= 5 {
            None
        } else {
            // safety is guaranteed because (hsize - 1) + 4 * (vsize - 1) ranges from 0 to 15
            // under the validation above
            let maps = unsafe { CONGRUENT_MAPS.get_unchecked((hsize - 1) + 4 * (vsize - 1)) };
            Some(Self { maps })
        }
    }

    pub fn map(&self, index: usize, pos: usize) -> usize {
        if index >= 8 || pos >= 16 {
            0
        } else {
            // safety is guaranteed thanks to the validation above
            unsafe { *self.maps.get_unchecked(index).get_unchecked(pos) }
        }
    }
}
