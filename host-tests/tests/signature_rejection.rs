//! Signature-rejection tests ported from the on-chain `vector` program's
//! Mollusk suite, run directly against the crate's public API.
//!
//! Already covered elsewhere (not repeated here):
//!
//! * wrong header byte: `adversarial::rejects_every_non_compressed_header`
//! * wrong message: `adversarial::verify_paths_agree_on_wrong_message`,
//!   `fuzz::fuzz_mutated_message_rejects`
//! * random bit flips of the signature, including body bytes:
//!   `fuzz::fuzz_mutated_signature_rejects`
//! * decoder rules (negative zero, magnitude 2048, nonzero tail bytes,
//!   residual bits, unbounded unary) at codec level: `internal-tests/codec.rs`
//!   (`rejects_negative_zero_*`, `rejects_oversized_magnitude_*`,
//!   `rejects_trailing_non_zero_byte_*`, `rejects_residual_bit_in_last_consumed_byte`)
//!
//! Determinism: keys come from `program/tests/fixtures`. PQClean signing is
//! randomised (fresh 40-byte nonce), so cases needing a signature with a
//! given property loop over fresh signatures; the failing signature is
//! printed in hex in every assertion message so failures reproduce. The
//! fixed `sample_sig.bin` (message `MSG_FIXTURE`) is used for the fully
//! deterministic checks.

use pqcrypto_falcon::falcon512;
use pqcrypto_traits::sign::{DetachedSignature, SecretKey};
use solana_falcon512::{
    FALCON_512_PUBKEY_LEN, FALCON_512_SIGNATURE_LEN, Falcon512Pubkey, Falcon512Signature,
};

const SK: &[u8] = include_bytes!("../../program/tests/fixtures/falcon.sk");
const PK: &[u8] = include_bytes!("../../program/tests/fixtures/falcon.pk");
const SAMPLE_SIG: &[u8] = include_bytes!("../../program/tests/fixtures/sample_sig.bin");
const MSG_FIXTURE: &[u8] = b"deterministic falcon-512 verify benchmark";

/// 39 bytes, as the Solana program passes: b"vector:" + 32-byte digest.
fn msg39(fill: u8) -> Vec<u8> {
    let mut m = b"vector:".to_vec();
    m.extend_from_slice(&[fill; 32]);
    assert_eq!(m.len(), 39);
    m
}

/// Messages exercised: 39 bytes (program shape) and another length.
fn messages() -> Vec<Vec<u8>> {
    vec![
        msg39(0x42),
        b"another message, 50 bytes long for the length test".to_vec(),
    ]
}

const BODY_START: usize = 41;
const COEFFICIENTS: usize = 512;

type Sig = [u8; FALCON_512_SIGNATURE_LEN];
type Coefficient = (bool, u16);

fn sk() -> falcon512::SecretKey {
    falcon512::SecretKey::from_bytes(SK).unwrap()
}

fn pk() -> Falcon512Pubkey {
    Falcon512Pubkey::try_from_slice(PK).unwrap().clone()
}

fn sign_with(msg: &[u8], sk: &falcon512::SecretKey) -> Sig {
    let sig = falcon512::detached_sign(msg, sk);
    let mut out = [0u8; FALCON_512_SIGNATURE_LEN];
    out[..sig.as_bytes().len()].copy_from_slice(sig.as_bytes());
    out
}

fn sign(msg: &[u8]) -> Sig {
    sign_with(msg, &sk())
}

fn hex(sig: &Sig) -> String {
    sig.iter().map(|b| format!("{b:02x}")).collect()
}

/// Both public verification paths must agree; returns the common answer.
fn verify(sig: &Sig, msg: &[u8]) -> bool {
    let pk = pk();
    let prepared = pk.prepare_pubkey();
    let s = Falcon512Signature::from(*sig);
    let a = s.verify(msg, &pk);
    let b = s.verify_with_prepared(msg, &prepared);
    assert_eq!(a, b, "verify paths disagree on sig {}", hex(sig));
    a
}

fn assert_rejected(sig: &Sig, msg: &[u8], what: &str) {
    assert!(!verify(sig, msg), "{what} accepted; sig = {}", hex(sig));
}

fn bit(bytes: &[u8], at: usize) -> bool {
    bytes[at / 8] >> (7 - at % 8) & 1 == 1
}

/// Decode the compressed body: (sign, 7 low bits, unary high part) per
/// coefficient. Returns coefficients and the number of bits consumed.
fn decode_body(body: &[u8]) -> (Vec<Coefficient>, usize) {
    let mut at = 0;
    let mut out = Vec::new();
    for _ in 0..COEFFICIENTS {
        let negative = bit(body, at);
        let mut magnitude = 0u16;
        for i in 1..8 {
            magnitude = magnitude << 1 | bit(body, at + i) as u16;
        }
        at += 8;
        while !bit(body, at) {
            magnitude += 128;
            at += 1;
        }
        at += 1;
        out.push((negative, magnitude));
    }
    (out, at)
}

/// Inverse of `decode_body`, zero-padded to `len`. Also encodes what the
/// verifier refuses (negative zero, magnitude >= 2048).
fn encode_body(coefficients: &[Coefficient], len: usize) -> Vec<u8> {
    let mut out = vec![0u8; len];
    let mut at = 0;
    let mut push = |one: bool| {
        out[at / 8] |= (one as u8) << (7 - at % 8);
        at += 1;
    };
    for &(negative, magnitude) in coefficients {
        push(negative);
        for i in (0..7).rev() {
            push(magnitude >> i & 1 == 1);
        }
        for _ in 0..magnitude / 128 {
            push(false);
        }
        push(true);
    }
    out
}

fn with_body(sig: &Sig, coefficients: &[Coefficient]) -> Sig {
    let body = encode_body(coefficients, FALCON_512_SIGNATURE_LEN - BODY_START);
    let mut out = *sig;
    out[BODY_START..].copy_from_slice(&body);
    out
}

/// A fresh real signature over `msg` satisfying `wanted`.
fn sign_where(msg: &[u8], wanted: impl Fn(&[Coefficient], usize) -> bool) -> Sig {
    loop {
        let sig = sign(msg);
        let (c, bits) = decode_body(&sig[BODY_START..]);
        if wanted(&c, bits) {
            return sig;
        }
    }
}

#[test]
fn fixture_key_and_sample_signature_verify() {
    assert_eq!(PK.len(), FALCON_512_PUBKEY_LEN);
    let mut sig = [0u8; FALCON_512_SIGNATURE_LEN];
    sig.copy_from_slice(SAMPLE_SIG);
    assert!(verify(&sig, MSG_FIXTURE));
    // Deterministic negative: same fixed signature, other message.
    assert_rejected(&sig, &msg39(0x42), "fixture sig over a different message");
}

#[test]
fn untouched_signature_verifies_and_codec_helper_round_trips() {
    for msg in messages() {
        let sig = sign(&msg);
        assert!(verify(&sig, &msg), "sig = {}", hex(&sig));
        // The helper codec reproduces the signer's bitstream exactly, so the
        // edits in the tests below change only what they claim to.
        let (c, bits) = decode_body(&sig[BODY_START..]);
        assert_eq!(c.len(), COEFFICIENTS);
        assert_eq!(with_body(&sig, &c), sig);
        assert!(bits <= (FALCON_512_SIGNATURE_LEN - BODY_START) * 8);
    }
}

#[test]
fn signature_over_another_message_fails() {
    for msg in messages() {
        let mut other = msg.clone();
        let last = other.len() - 1;
        other[last] ^= 0xff;
        let sig = sign(&other);
        assert_rejected(&sig, &msg, "signature over another message");
    }
}

#[test]
fn signature_of_another_key_fails() {
    // Random second key: only needs to differ from the fixture key.
    let (_, other) = falcon512::keypair();
    for msg in messages() {
        let sig = sign_with(&msg, &other);
        assert_rejected(&sig, &msg, "signature of another key");
    }
}

#[test]
fn flipped_nonce_byte_fails() {
    for msg in messages() {
        for at in [1usize, 2, 20, 39, 40] {
            for mask in [0x01u8, 0x80] {
                let mut sig = sign(&msg);
                sig[at] ^= mask;
                assert_rejected(&sig, &msg, &format!("nonce byte {at} ^ {mask:#x}"));
            }
        }
    }
}

#[test]
fn nonzero_padding_fails() {
    for msg in messages() {
        // A signature whose body ends before the last byte.
        let sig = sign_where(&msg, |_, bits| {
            BODY_START + bits.div_ceil(8) < FALCON_512_SIGNATURE_LEN
        });
        assert!(verify(&sig, &msg));
        let (_, bits) = decode_body(&sig[BODY_START..]);
        for at in [BODY_START + bits.div_ceil(8), FALCON_512_SIGNATURE_LEN - 1] {
            let mut padded = sig;
            padded[at] = 1;
            assert_rejected(&padded, &msg, &format!("nonzero padding at {at}"));
        }
    }
}

#[test]
fn all_zero_signature_fails() {
    for msg in messages() {
        assert_rejected(&[0; FALCON_512_SIGNATURE_LEN], &msg, "all-zero signature");
        // Correct header, otherwise zero: coefficient 0 has an
        // unterminated unary run, which exhausts the buffer.
        let mut s = [0u8; FALCON_512_SIGNATURE_LEN];
        s[0] = 0x39;
        assert_rejected(&s, &msg, "header-only signature");
    }
}

#[test]
fn truncated_body_fails() {
    for msg in messages() {
        // Drop the last coefficient's unary terminator: the zero padding
        // after it then reads as an unterminated/overlong unary run.
        let mut sig = sign(&msg);
        let (_, bits) = decode_body(&sig[BODY_START..]);
        let last = BODY_START + (bits - 1) / 8;
        sig[last] &= !(1 << (7 - (bits - 1) % 8));
        assert_rejected(&sig, &msg, "missing unary terminator");

        // Body ends inside a byte whose unused low bits are not zero.
        let mut sig = sign_where(&msg, |_, bits| bits % 8 != 0);
        let (_, bits) = decode_body(&sig[BODY_START..]);
        sig[BODY_START + bits / 8] |= 1;
        assert_rejected(&sig, &msg, "nonzero residual bits");

        // Body cut off entirely after N bytes (rest zero).
        let sig = sign(&msg);
        let mut cut = sig;
        for b in &mut cut[BODY_START + 300..] {
            *b = 0;
        }
        assert_rejected(&cut, &msg, "body truncated at 300 bytes");
    }
}

#[test]
fn negative_zero_fails_by_encoding_rule_only() {
    for msg in messages() {
        let sig = sign_where(&msg, |c, _| c.iter().any(|&(_, m)| m == 0));
        let (mut c, _) = decode_body(&sig[BODY_START..]);
        let zero = c.iter().position(|&(_, m)| m == 0).unwrap();

        // Control: identical polynomial (+0 stays +0) re-encoded verifies, so
        // the helper changes nothing numerically.
        assert!(verify(&with_body(&sig, &c), &msg));

        // Flip the sign bit of the zero coefficient. s2 as a polynomial is
        // identical, so the hash relation and L2 norm still pass; the ONLY
        // rule that can reject it is the decoder's canonical-encoding rule
        // (codec-level: `rejects_negative_zero_*` in internal-tests/codec.rs).
        c[zero].0 = true;
        assert_rejected(&with_body(&sig, &c), &msg, "negative zero");
    }
}

#[test]
fn oversized_magnitude_2048_fails() {
    // Magnitude 2048 is out of range. The L2 bound alone would not refuse a
    // lone 2048 (2048^2 << bound); rejection here comes from the decoder
    // range check or from the s1 = c - s2*h relation. The pure decoder rule
    // is pinned in internal-tests/codec.rs::rejects_oversized_magnitude_2048
    // (the codec module is private to the crate, unreachable from here).
    for msg in messages() {
        let sig = sign(&msg);
        let (c0, _) = decode_body(&sig[BODY_START..]);
        for slot in [0usize, 255, 511] {
            for negative in [false, true] {
                let mut c = c0.clone();
                c[slot] = (negative, 2048);
                assert_rejected(
                    &with_body(&sig, &c),
                    &msg,
                    &format!("magnitude 2048 at slot {slot}"),
                );
            }
        }
    }
}
