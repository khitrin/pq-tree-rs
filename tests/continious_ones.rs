use std::{iter, panic};

use rand::seq::SliceRandom;
use rand::{thread_rng, Rng, RngCore, SeedableRng};
use rand_pcg::Pcg64;

use ::pq_tree::PQTree;

#[test]
fn consecutive_ones_test() {
    let mut rng = thread_rng();
    for i in 0..1000 {
        let seed = rng.next_u64();
        let r = rng.gen_range(2..=16);
        let c = rng.gen_range(2..=16);

        let result = panic::catch_unwind(|| consecutive_ones_test_iter(r, c, seed));
        if let Err(_) = result {
            dbg!(i, r, c, seed);
            panic!();
        }
    }
}

fn consecutive_ones_test_iter(rows: usize, cols: usize, seed: u64) {
    let mut rng = Pcg64::seed_from_u64(seed);

    let mut data = vec![vec![0; cols]; rows];

    for col in 0..cols {
        let s = rng.gen_range(0..rows);
        let e = rng.gen_range((s + 1)..=rows);
        data[s..e].iter_mut().for_each(|r| r[col] = 1);
    }

    data.shuffle(&mut rng);

    let mut pq = PQTree::new(&(0..rows).collect::<Vec<usize>>());
    for c in 0..cols {
        let s = (0..rows).into_iter().filter(|&r| data[r][c] == 1).collect::<Vec<usize>>();
        assert_ne!(s.len(), 0);
        pq = pq.reduction(&s).unwrap();
    }

    let frontier = pq.frontier();
    for c in 0..cols {
        let changes = frontier
            .iter()
            .map(|&r| data[r][c])
            .chain(iter::once(0))
            .fold((0, 0), |(prev, acc), curr| (curr, if curr == prev { acc } else { acc + 1 }))
            .1;

        assert_eq!(changes, 2);
    }
}
