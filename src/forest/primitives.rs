const C1: u128 = 19;
const C2: u128 = 9;
const FROBENIUS: u128 = (C1 - 1) * (C2 - 1) - 1;
const MIN_N: u128 = FROBENIUS + 1;

pub fn dr(n: u128) -> u128 {
    if n == 0 {
        return 0;
    }
    1 + ((n - 1) % C2)
}

pub fn rn(n: u128) -> u128 {
    if n < MIN_N {
        return 0;
    }
    let q = n / C1;
    let d = dr(n);
    if q < d {
        0
    } else {
        (q - d) / C2 + 1
    }
}

pub fn is_representable(n: u128) -> bool {
    n >= MIN_N
}

pub const fn frobenius() -> u128 {
    FROBENIUS
}
pub const fn min_representable() -> u128 {
    MIN_N
}
pub const fn c1() -> u128 {
    C1
}
pub const fn c2() -> u128 {
    C2
}

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
            if !is_representable(n) {
                count += 1;
            }
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
