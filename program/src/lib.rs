#![cfg_attr(any(target_arch = "bpf", target_os = "solana"), no_std)]

use solana_falcon512::{
    FALCON_512_SIGNATURE_LEN, Falcon512PreparedPubkey, Falcon512Pubkey, Falcon512Signature,
};

use solana_program_error::ProgramError;

// Prepared (decoded + NTT-transformed) pubkey, computed at compile time so the
// program skips the per-call pubkey decode + forward NTT.
pub const PREPARED_PUBKEY: Falcon512PreparedPubkey = {
    let pk = Falcon512Pubkey::from_bytes(*include_bytes!("../tests/fixtures/falcon.pk"));
    pk.prepare_pubkey()
};

#[cfg(any(target_arch = "bpf", target_os = "solana"))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

/// Custom program error returned when signature verification fails.
const ERR_VERIFY_FAILED: u64 = 3;

/// Solana SBF entrypoint.
///
/// The runtime calls this with `r1 = input`, where `input` points to the
/// serialized account + instruction region. With zero accounts the layout is:
///
/// ```text
///   [u64 num_accounts = 0]      // bytes 0..8
///   [u64 ix_data_len]           // bytes 8..16
///   [ix_data: ix_data_len bytes]// bytes 16..16+ix_data_len
///   [program_id: 32 bytes]      // trailing
/// ```
///
/// We read the instruction-data slice directly from `input + 16` rather than
/// going through any deserializer.
///
/// **Instruction data layout:** `[mode: 0 = SHAKE, 1 = TurboSHAKE][signature (666 bytes)][message]`.
///
/// # Safety
///
/// The Solana runtime guarantees `input` points to a properly-laid-out
/// serialized region with at least `16 + ix_data_len` bytes readable.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn entrypoint(input: *mut u8) -> u64 {
    let ix_data_len = unsafe { core::ptr::read(input.add(8) as *const u64) } as usize;
    if ix_data_len < 1 + FALCON_512_SIGNATURE_LEN {
        return ProgramError::InvalidInstructionData.into();
    }
    let data = unsafe { core::slice::from_raw_parts(input.add(16), ix_data_len) };

    let (mode, data) = data.split_first().unwrap();
    let Some((sig_bytes, message)) = data.split_first_chunk::<FALCON_512_SIGNATURE_LEN>() else {
        return ProgramError::InvalidInstructionData.into();
    };
    // Borrow the signature in place — `from_ref` is a no-op cast (no copy)
    // since `Falcon512Signature` is `#[repr(transparent)]`. Saves ~200 CU
    // vs `Falcon512Signature::from(*sig_bytes)` which memcpy's 666 bytes.
    let signature = Falcon512Signature::from_ref(sig_bytes);

    const TURBO_PUBKEY: Falcon512PreparedPubkey<true> =
        Falcon512PreparedPubkey::from_bytes(*PREPARED_PUBKEY.as_bytes());
    let valid = match mode {
        0 => signature.verify_with_prepared(message, &PREPARED_PUBKEY),
        1 => signature.verify_with_prepared(message, &TURBO_PUBKEY),
        _ => return ProgramError::InvalidInstructionData.into(),
    };
    if valid { 0 } else { ERR_VERIFY_FAILED }
}
