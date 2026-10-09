use crate::forest::{a0, b0, rn};
use aes_gcm::aead::{Aead, KeyInit};
use aes_gcm::{Aes256Gcm, Key, Nonce};
use pqc_kyber::KYBER_CIPHERTEXTBYTES;
use sha2::{Digest, Sha256};
use zeroize::Zeroize;

const DOMAIN: &[u8] = b"MRS-AUTH-CLOCK-KDF-v1";
const C1: u128 = 19;
const C2: u128 = 9;
const FROBENIUS: u128 = (C1 - 1) * (C2 - 1) - 1;
const MIN_N: u128 = FROBENIUS + 1;

const DAY_MS: u128 = 86_400_000;
const HOUR_MS: u128 = 3_600_000;
const MIN_MS: u128 = 60_000;
const SEC_MS: u128 = 1_000;

#[derive(Clone, Zeroize)]
#[zeroize(drop)]
pub struct ClockKey {
    pub key: [u8; 32],
    pub n: u128,
    pub clock: (u128, u32, u32, u32, u32),
    pub rn: u128,
    pub k: u128,
    pub ab: (u128, u128),
}

#[derive(Zeroize)]
#[zeroize(drop)]
pub struct ClockCiphertextPacket {
    pub kyber_ciphertext: [u8; KYBER_CIPHERTEXTBYTES],
    pub aes_payload: Vec<u8>,
}

#[inline]
fn representation(n: u128, k: u128) -> (u128, u128) {
    (a0(n) + C2 * k, b0(n) - C1 * k)
}

#[inline]
fn decompose(n: u128) -> (u128, u32, u32, u32, u32) {
    let d = n / DAY_MS;
    let rem = n % DAY_MS;
    let h = (rem / HOUR_MS) as u32;
    let m = ((rem % HOUR_MS) / MIN_MS) as u32;
    let s = ((rem % MIN_MS) / SEC_MS) as u32;
    let ms = (n % SEC_MS) as u32;
    (d, h, m, s, ms)
}

pub fn derive_key_from_clock(seed: &[u8]) -> ClockKey {
    let h = Sha256::digest(seed);

    let mut n_buf = [0u8; 16];
    n_buf.copy_from_slice(&h[0..16]);
    let mut n = u128::from_be_bytes(n_buf);
    if n < MIN_N {
        n += MIN_N;
    }

    let clock = decompose(n);
    let rn_val = rn(n).max(1);

    let mut hk = Sha256::new();
    hk.update(DOMAIN);
    hk.update(b"|k|");
    hk.update(seed);
    let hk = hk.finalize();
    let mut k_buf = [0u8; 16];
    k_buf.copy_from_slice(&hk[0..16]);
    let k = u128::from_be_bytes(k_buf) % rn_val;

    let ab = representation(n, k);

    let mut kh = Sha256::new();
    kh.update(DOMAIN);
    kh.update(&n.to_be_bytes());
    kh.update(&clock.0.to_be_bytes());
    kh.update(&clock.1.to_be_bytes());
    kh.update(&clock.2.to_be_bytes());
    kh.update(&clock.3.to_be_bytes());
    kh.update(&clock.4.to_be_bytes());
    kh.update(&rn_val.to_be_bytes());
    kh.update(&k.to_be_bytes());
    kh.update(&ab.0.to_be_bytes());
    kh.update(&ab.1.to_be_bytes());
    kh.update(&h[16..32]);

    let out = kh.finalize();
    let mut key = [0u8; 32];
    key.copy_from_slice(&out);

    ClockKey {
        key,
        n,
        clock,
        rn: rn_val,
        k,
        ab,
    }
}

pub fn encrypt_payload(
    key_bytes: &[u8; 32],
    nonce_bytes: &[u8; 12],
    plaintext: &[u8],
    associated_data: &[u8],
) -> Result<Vec<u8>, &'static str> {
    let key = Key::<Aes256Gcm>::from_slice(key_bytes);
    let cipher = Aes256Gcm::new(key);
    let nonce = Nonce::from_slice(nonce_bytes);
    cipher
        .encrypt(
            nonce,
            aes_gcm::aead::Payload {
                msg: plaintext,
                aad: associated_data,
            },
        )
        .map_err(|_| "AES-GCM encryption failed")
}

pub fn decrypt_payload(
    key_bytes: &[u8; 32],
    nonce_bytes: &[u8; 12],
    ciphertext: &[u8],
    associated_data: &[u8],
) -> Result<Vec<u8>, &'static str> {
    let key = Key::<Aes256Gcm>::from_slice(key_bytes);
    let cipher = Aes256Gcm::new(key);
    let nonce = Nonce::from_slice(nonce_bytes);
    cipher
        .decrypt(
            nonce,
            aes_gcm::aead::Payload {
                msg: ciphertext,
                aad: associated_data,
            },
        )
        .map_err(|_| "AES-GCM decryption failed (integrity check failed)")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn determinism() {
        let seed = b"test-seed-32-bytes-long-for-hkdf";
        let k1 = derive_key_from_clock(seed);
        let k2 = derive_key_from_clock(seed);
        assert_eq!(k1.key, k2.key);
        assert_eq!(k1.n, k2.n);
        assert_eq!(k1.k, k2.k);
        assert_eq!(k1.ab, k2.ab);
    }

    #[test]
    fn different_seeds_differ() {
        let k1 = derive_key_from_clock(b"seed-a");
        let k2 = derive_key_from_clock(b"seed-b");
        assert_ne!(k1.key, k2.key);
        assert_ne!(k1.n, k2.n);
    }

    #[test]
    fn avalanche() {
        let s1 = b"avalanche-test-seed-0123456789";
        let mut s2 = *s1;
        s2[0] ^= 0x01;
        let k1 = derive_key_from_clock(s1);
        let k2 = derive_key_from_clock(&s2);
        let diff: u32 = k1
            .key
            .iter()
            .zip(k2.key.iter())
            .map(|(a, b)| (a ^ b).count_ones())
            .sum();
        assert!(diff > 100);
    }

    #[test]
    fn n_is_representable() {
        for i in 0u32..1000 {
            let ck = derive_key_from_clock(&i.to_be_bytes());
            assert!(ck.n >= MIN_N);
            assert!(ck.rn >= 1);
            assert!(ck.k < ck.rn);
        }
    }

    #[test]
    fn representation_is_valid() {
        for i in 0u32..1000 {
            let ck = derive_key_from_clock(&i.to_be_bytes());
            let (a, b) = ck.ab;
            assert_eq!(C1 * a + C2 * b, ck.n);
        }
    }

    #[test]
    fn clock_decomposition_is_bijective() {
        for i in 0u32..1000 {
            let ck = derive_key_from_clock(&i.to_be_bytes());
            let (d, h, m, s, ms) = ck.clock;
            let recomposed = d * DAY_MS
                + (h as u128) * HOUR_MS
                + (m as u128) * MIN_MS
                + (s as u128) * SEC_MS
                + (ms as u128);
            assert_eq!(recomposed, ck.n);
        }
    }

    #[test]
    fn encrypt_decrypt_roundtrip() {
        let ck = derive_key_from_clock(b"roundtrip-test-seed-00000000");
        let nonce = [0u8; 12];
        let aad = b"associated-data";
        let msg = b"hello, MRS-AUTH";
        let ct = encrypt_payload(&ck.key, &nonce, msg, aad).unwrap();
        let pt = decrypt_payload(&ck.key, &nonce, &ct, aad).unwrap();
        assert_eq!(pt, msg);
    }

    #[test]
    fn aad_is_authenticated() {
        let ck = derive_key_from_clock(b"aad-test-seed-00000000000000");
        let nonce = [0u8; 12];
        let ct = encrypt_payload(&ck.key, &nonce, b"msg", b"aad-1").unwrap();
        assert!(decrypt_payload(&ck.key, &nonce, &ct, b"aad-2").is_err());
    }

    #[test]
    fn tampering_is_detected() {
        let ck = derive_key_from_clock(b"tamper-test-seed-00000000000");
        let nonce = [0u8; 12];
        let mut ct = encrypt_payload(&ck.key, &nonce, b"msg", b"aad").unwrap();
        ct[0] ^= 0x01;
        assert!(decrypt_payload(&ck.key, &nonce, &ct, b"aad").is_err());
    }
}
