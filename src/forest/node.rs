use super::branch::ForestBranch;
use super::primitives::{a0, b0, c1, c2, rn};
use zeroize::Zeroize;

#[derive(Clone, Zeroize)]
#[zeroize(drop)]
pub struct ForestNode {
    pub n: u128,
    pub a0: u128,
    pub b0: u128,
    pub rn: u128,
}

impl ForestNode {
    pub fn new(n: u128) -> Self {
        let a0_val = a0(n);
        let rn_val = rn(n);
        let b0_val = if rn_val == 0 { 0 } else { b0(n) };
        ForestNode {
            n,
            a0: a0_val,
            b0: b0_val,
            rn: rn_val,
        }
    }

    pub fn is_representable(&self) -> bool {
        self.rn > 0
    }

    pub fn branch(&self, k: u128) -> Option<ForestBranch> {
        if k >= self.rn {
            return None;
        }
        Some(ForestBranch {
            k,
            a: self.a0 + c2() * k,
            b: self.b0 - c1() * k,
        })
    }

    pub fn first(&self) -> Option<ForestBranch> {
        self.branch(0)
    }

    pub fn last(&self) -> Option<ForestBranch> {
        if self.rn == 0 {
            return None;
        }
        self.branch(self.rn - 1)
    }

    pub fn all(&self, cap: usize) -> Vec<ForestBranch> {
        let limit = self.rn.min(cap as u128) as usize;
        (0..limit as u128).filter_map(|k| self.branch(k)).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::super::primitives::{c1, c2};
    use super::*;

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
        for n in [9u128, 144, 500, 1991, 10_000, 1_000_000] {
            let node = ForestNode::new(n);
            for branch in node.all(64) {
                assert_eq!(c1() * branch.a + c2() * branch.b, n);
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
    fn node_is_representable() {
        assert!(!ForestNode::new(143).is_representable());
        assert!(ForestNode::new(144).is_representable());
        assert!(ForestNode::new(9).is_representable());
    }

    #[test]
    fn node_edge_cases_previously_missed() {
        for n in [9u128, 18, 144, 153, 162] {
            let node = ForestNode::new(n);
            assert!(node.is_representable(), "n={} should be representable", n);
            let b = node.first().unwrap();
            assert_eq!(c1() * b.a + c2() * b.b, n);
        }
    }
}
