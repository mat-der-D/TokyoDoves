pub const CONGRUENT_MAPS: [[[usize; 16]; 8]; 16] = {
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
    let mut vsize = 1;
    while vsize < 5 {
        let mut hsize = 1;
        while hsize < 5 {
            let idx = (hsize - 1) + 4 * (vsize - 1);
            let mut count = 0;
            let mut base = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];

            let mut i = 0;
            while i < 2 {
                let mut j = 0;
                while j < 2 {
                    let mut k = 0;
                    while k < 2 {
                        let hvsize = if k % 2 == 0 { vsize } else { hsize };
                        base = compose(rotate_maps[hvsize - 1], base);
                        cons[idx][count] = base;
                        count += 1;
                        k += 1;
                    }
                    j += 1;
                }
                base = compose(reflect_maps[vsize - 1], base);
                i += 1;
            }
            hsize += 1;
        }
        vsize += 1;
    }
    cons
};

const fn compose(a: [usize; 16], b: [usize; 16]) -> [usize; 16] {
    let mut a_after_b = [0_usize; 16];
    let mut i = 0;
    while i < 16 {
        a_after_b[i] = a[b[i]];
        i += 1;
    }
    a_after_b
}
