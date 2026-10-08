use pqc_kyber::{decapsulate, encapsulate, keypair, KyberError};
use rand::thread_rng;

use crate::crypto::{
    decrypt_payload, derive_key_from_clock, encrypt_payload, ClockCiphertextPacket,
};

pub struct Keypair {
    pub public_key: [u8; pqc_kyber::KYBER_PUBLICKEYBYTES],
    pub secret_key: [u8; pqc_kyber::KYBER_SECRETKEYBYTES],
}

pub struct SecureEnvelope {
    pub packet: ClockCiphertextPacket,
}

#[derive(Debug)]
pub enum FrameworkError {
    Kyber(KyberError),
    Crypto(&'static str),
}

impl From<KyberError> for FrameworkError {
    fn from(e: KyberError) -> Self {
        FrameworkError::Kyber(e)
    }
}

fn combine_seed(shared_secret: &[u8], session_id: &[u8]) -> Vec<u8> {
    let mut seed = Vec::with_capacity(shared_secret.len() + 1 + session_id.len());
    seed.extend_from_slice(shared_secret);
    seed.push(0x00);
    seed.extend_from_slice(session_id);
    seed
}

pub struct MrsAuthFramework;

impl MrsAuthFramework {
    pub fn keygen() -> Result<Keypair, FrameworkError> {
        let mut rng = thread_rng();
        let keys = keypair(&mut rng)?;
        Ok(Keypair {
            public_key: keys.public,
            secret_key: keys.secret,
        })
    }

    pub fn full_encrypt(
        public_key: &[u8; pqc_kyber::KYBER_PUBLICKEYBYTES],
        session_id: &[u8],
        nonce: &[u8; 12],
        associated_data: &[u8],
        plaintext: &[u8],
    ) -> Result<SecureEnvelope, FrameworkError> {
        let mut rng = thread_rng();
        let (kyber_ciphertext, shared_secret) = encapsulate(public_key, &mut rng)?;

        let seed = combine_seed(&shared_secret, session_id);
        let clock_key = derive_key_from_clock(&seed);

        let aes_payload = encrypt_payload(&clock_key.key, nonce, plaintext, associated_data)
            .map_err(FrameworkError::Crypto)?;

        Ok(SecureEnvelope {
            packet: ClockCiphertextPacket {
                kyber_ciphertext,
                aes_payload,
            },
        })
    }

    pub fn full_decrypt(
        secret_key: &[u8; pqc_kyber::KYBER_SECRETKEYBYTES],
        envelope: &SecureEnvelope,
        session_id: &[u8],
        nonce: &[u8; 12],
        associated_data: &[u8],
    ) -> Result<Vec<u8>, FrameworkError> {
        let shared_secret = decapsulate(&envelope.packet.kyber_ciphertext, secret_key)?;

        let seed = combine_seed(&shared_secret, session_id);
        let clock_key = derive_key_from_clock(&seed);

        let plaintext = decrypt_payload(
            &clock_key.key,
            nonce,
            &envelope.packet.aes_payload,
            associated_data,
        )
        .map_err(FrameworkError::Crypto)?;

        Ok(plaintext)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn full_round_trip() {
        let keypair = MrsAuthFramework::keygen().expect("keygen should not fail");
        let session_id = b"session-2026-08-24";
        let nonce = [7u8; 12];
        let aad = b"envelope-header";
        let plaintext = b"a message that survives the round trip";

        let envelope = MrsAuthFramework::full_encrypt(
            &keypair.public_key,
            session_id,
            &nonce,
            aad,
            plaintext,
        )
        .expect("encryption should succeed");

        let recovered = MrsAuthFramework::full_decrypt(
            &keypair.secret_key,
            &envelope,
            session_id,
            &nonce,
            aad,
        )
        .expect("decryption should succeed");

        assert_eq!(plaintext.to_vec(), recovered);
    }

    #[test]
    fn wrong_session_id_fails() {
        let keypair = MrsAuthFramework::keygen().expect("keygen should not fail");
        let nonce = [7u8; 12];
        let aad = b"envelope-header";
        let plaintext = b"secret";

        let envelope = MrsAuthFramework::full_encrypt(
            &keypair.public_key,
            b"session-A",
            &nonce,
            aad,
            plaintext,
        )
        .expect("encryption should succeed");

        let result = MrsAuthFramework::full_decrypt(
            &keypair.secret_key,
            &envelope,
            b"session-B",
            &nonce,
            aad,
        );

        assert!(result.is_err());
    }
}
