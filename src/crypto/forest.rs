use zeroize::Zeroize;

const C1: u128 = 19;
const C2: u128 = 9;
const FROBENIUS: u128 = (C1 - 1) * (C2 - 1) - 1;
const MIN_N: u128 = FROBENIUS + 1;

#[derive(Clone, Zeroize)]
#[zeroize(drop)]
pub struct ForestNode {
    pub n: u128,
    pub a0: u128,
    pub b0: u128,
    pub rn: u128,
}

#[derive(Clone)]
pub struct ForestBranch {
    pub k: u128,
    pub a: u128,
    pub b: u128,
}

impl ForestNode {
    pub fn new(n: u128) -> Self {
        let a0_val = dr(n);
        let b0_val = (n - C1 * a0_val) / C2;
        let rn_val = rn(n);
        ForestNode { n, a0: a0_val, b0: b0_val, rn: rn_val }
    }

    pub fn is_representable(&self) -> bool {
        self.rn > 0
    }

    pub fn branch(&self, k: u128) -> Option<ForestBranch> {
        if k >= self.rn { return None; }
        Some(ForestBranch {
            k,
            a: self.a0 + C2 * k,
            b: self.b0 - C1 * k,
        })
    }

    pub fn first(&self) -> Option<ForestBranch> { self.branch(0) }

    pub fn last(&self) -> Option<ForestBranch> {
        if self.rn == 0 { return None; }
        self.branch(self.rn - 1)
    }

    pub fn all(&self, cap: usize) -> Vec<ForestBranch> {
        let limit = self.rn.min(cap as u128) as usize;
        (0..limit as u128).filter_map(|k| self.branch(k)).collect()
    }
}

pub fn dr(n: u128) -> u128 {
    if n == 0 { return 0; }
    1 + ((n - 1) % C2)
}

pub fn rn(n: u128) -> u128 {
    if n < MIN_N { return 0; }
    let q = n / C1;
    let d = dr(n);
    if q < d { 0 } else { (q - d) / C2 + 1 }
}

pub fn is_representable(n: u128) -> bool {
    n >= MIN_N
}

pub const fn frobenius() -> u128 { FROBENIUS }
pub const fn min_representable() -> u128 { MIN_N }
pub const fn c1() -> u128 { C1 }
pub const fn c2() -> u128 { C2 }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frobenius_boundary() {
        assert_eq!(FROBENIUS, 143);
        assert_eq!(MIN_N, 144);
        assert!(!is_representable(143));
        assert!(is_representable(144));
    }

    #[test]
    fn rn_closed_form_matches_bruteforce() {
        for n in MIN_N..10000u128 {
            let brute = (0u128..)
                .map(|k| dr(n) + 9 * k)
                .take_while(|&a| 19 * a <= n)
                .filter(|&a| (n - 19 * a) % 9 == 0)
                .count() as u128;
            assert_eq!(rn(n), brute);
        }
    }

    #[test]
    fn node_first_and_last() {
        let node = ForestNode::new(1991);
        let first = node.first().unwrap();
        let last = node.last().unwrap();
        assert_eq!(first.k, 0);
        assert_eq!(first.a, 2);
        assert_eq!(first.b, 217);
        assert_eq!(last.k, 11);
        assert_eq!(last.a, 2 + 9 * 11);
        assert_eq!(last.b, 217 - 19 * 11);
    }

    #[test]
    fn node_all_branches_satisfy_equation() {
        for n in [144u128, 500, 1991, 10_000, 1_000_000] {
            let node = ForestNode::new(n);
            for branch in node.all(64) {
                assert_eq!(C1 * branch.a + C2 * branch.b, n);
            }
        }
    }

    #[test]
    fn node_branch_out_of_range_returns_none() {
        let node = ForestNode::new(1991);
        assert!(node.branch(node.rn).is_none());
        assert!(node.branch(node.rn + 100).is_none());
    }

    #[test]
    fn dr_cycle_one_to_nine() {
        assert_eq!(dr(1), 1);
        assert_eq!(dr(9), 9);
        assert_eq!(dr(10), 1);
        assert_eq!(dr(18), 9);
        assert_eq!(dr(19), 1);
        assert_eq!(dr(1991), 2);
    }

    #[test]
    fn unrepresentable_below_frobenius() {
        let mut count = 0;
        for n in 0..=FROBENIUS {
            if !is_representable(n) { count += 1; }
        }
        assert_eq!(count, 72);
    }

    #[test]
    fn all_above_frobenius_representable() {
        for n in MIN_N..MIN_N + 1000 {
            assert!(is_representable(n));
        }
    }
}
