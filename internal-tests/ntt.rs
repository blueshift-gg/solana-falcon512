//! Unit tests for crate::ntt. Loaded into the lib via
//! `#[cfg(test)] #[path]` in src/ntt.rs; the whole `internal-tests/`
//! directory is kept out of the published tarball by [package.exclude].

use super::*;

fn reference_ntt(input: [u32; N]) -> [u32; N] {
    let q = Q as u64;
    let mut r = input;
    let mut k: usize = 1;
    let mut len = N / 2;

    while len > 0 {
        let mut start = 0;
        while start < N {
            let zeta = ZETAS[k] as u64;
            k += 1;
            for j in start..start + len {
                let u = r[j] as u64 % q;
                let v = r[j + len] as u64 % q;
                let t = v * zeta % q;
                r[j] = ((u + t) % q) as u32;
                r[j + len] = ((u + q - t) % q) as u32;
            }
            start += 2 * len;
        }
        len /= 2;
    }

    r
}

fn reference_inv_ntt(input: [u32; N]) -> [u32; N] {
    let q = Q as u64;
    let mut r = input;
    let mut len = 1;

    while len < N {
        let groups = N / (2 * len);
        for i in 0..groups {
            let zeta = INV_ZETAS[groups + i] as u64;
            let start = 2 * i * len;
            for j in start..start + len {
                let u = r[j] as u64 % q;
                let v = r[j + len] as u64 % q;
                r[j] = ((u + v) % q) as u32;
                r[j + len] = ((u + q - v) * zeta % q) as u32;
            }
        }
        len *= 2;
    }

    let n_inv = N_INV as u64;
    for slot in r.iter_mut() {
        *slot = (*slot as u64 * n_inv % q) as u32;
    }
    r
}

#[test]
fn ntt_and_inv_ntt_match_scalar_reference() {
    fn next(seed: &mut u64) -> u64 {
        let mut x = *seed;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        *seed = x;
        x
    }

    let mut cases = vec![[0u32; N], [Q - 1; N]];

    let mut patterned = [0u32; N];
    for (i, slot) in patterned.iter_mut().enumerate() {
        *slot = ((i * 17 + (i >> 1) * 31 + 3) as u32) % Q;
    }
    cases.push(patterned);

    let mut seed = 0x243F_6A88_85A3_08D3;
    for _ in 0..64 {
        let mut poly = [0u32; N];
        for slot in poly.iter_mut() {
            *slot = (next(&mut seed) % Q as u64) as u32;
        }
        cases.push(poly);
    }

    for (case, input) in cases.into_iter().enumerate() {
        let mut optimized_ntt = input;
        ntt(&mut optimized_ntt);
        let reference_ntt = reference_ntt(input);
        assert_eq!(
            optimized_ntt, reference_ntt,
            "case {case}: optimized NTT diverged from scalar reference"
        );

        let mut optimized_inv = optimized_ntt;
        inv_ntt(&mut optimized_inv);
        let reference_inv = reference_inv_ntt(reference_ntt);
        assert_eq!(
            optimized_inv, reference_inv,
            "case {case}: optimized inverse NTT diverged from scalar reference"
        );
        assert_eq!(
            optimized_inv, input,
            "case {case}: inverse NTT did not recover the input"
        );
    }
}

#[test]
fn signed_ntt_path_matches_canonical_ntt() {
    fn next(seed: &mut u64) -> u64 {
        let mut x = *seed;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        *seed = x;
        x
    }

    let mut seed = 0x1319_8A2E_0370_7344;
    for case in 0..64 {
        let mut signed = [0i16; N];
        let mut canonical = [0u32; N];
        for i in 0..N {
            let v = (next(&mut seed) % 4095) as i16 - 2047;
            signed[i] = v;
            canonical[i] = if v < 0 {
                (Q as i32 + v as i32) as u32
            } else {
                v as u32
            };
        }

        let mut from_signed = [0u32; N];
        ntt_main_levels_from_signed(&mut from_signed, &signed);
        ntt_last_level(&mut from_signed);
        for slot in from_signed.iter_mut() {
            *slot = (*slot as u64 % Q as u64) as u32;
        }

        ntt(&mut canonical);
        assert_eq!(
            from_signed, canonical,
            "case {case}: signed NTT path diverged from canonical NTT"
        );
    }
}

// ========================================================================
// Kernel-correctness proptests.
// The Kani harnesses verify *safety* (no overflow, output ranges). They do
// NOT verify algebraic correctness — `assert_eq!` over u64 mod-arithmetic
// equivalence hangs Z3 on the wider kernels. The proptests below reduce
// that gap by random-sampling each kernel against a non-wrapping spec
// reference: many drifts between the production kernel and the spec would
// be caught with high probability over thousands of iterations.
// ========================================================================

use proptest::prelude::*;

proptest! {
    #[test]
    fn ct_butterfly_step_matches_spec(
        a in 0u64..=(10 * Q as u64),
        b in 0u64..=(10 * Q as u64),
        zeta in 0u64..(Q as u64),
    ) {
        let q = Q as u64;
        let (lo, hi) = ct_butterfly_step(a, b, zeta);
        prop_assert_eq!(lo % q, (a + b * zeta) % q);
        prop_assert_eq!(hi % q, (a + q - (b * zeta) % q) % q);
    }

    #[test]
    fn ct_butterfly_lazy_t_step_matches_spec(
        a in 0u64..=LAZY_T_INPUT_MAX,
        b in 0u64..=LAZY_T_INPUT_MAX,
        zeta in 0u64..(Q as u64),
    ) {
        let q = Q as u64;
        let (lo, hi) = ct_butterfly_lazy_t_step(a, b, zeta);
        prop_assert_eq!(lo % q, (a + b * zeta) % q);
        prop_assert_eq!(hi % q, (a + q - (b * zeta) % q) % q);
    }

    #[test]
    fn gs_butterfly_lazy_step_matches_spec(
        u in 0u64..=(256 * Q as u64),
        v in 0u64..=(256 * Q as u64),
        zeta in 0u64..(Q as u64),
    ) {
        let q = Q as u64;
        let (lo, hi) = gs_butterfly_lazy_step(u, v, zeta);
        prop_assert_eq!(lo % q, (u + v) % q);
        prop_assert_eq!(hi, ((u + q - v % q) * zeta) % q);
    }

    #[test]
    fn fused_step_kernel_matches_spec(
        prev_low in 0u32..=(LAZY_T_OUTPUT_MAX as u32),
        prev_high in 0u32..=(LAZY_T_OUTPUT_MAX as u32),
        h_lo in 0u16..(Q as u16),
        h_hi in 0u16..(Q as u16),
        z in 0u64..(Q as u64),
        z_inv in 0u64..(Q as u64),
    ) {
        let q = Q as u64;
        let (new_low, new_high) =
            fused_step_kernel(prev_low, prev_high, h_lo, h_hi, z, z_inv);

        // Spec: pure mod-q arithmetic, no lazy offsets.
        let pl = prev_low as u64 % q;
        let ph = prev_high as u64 % q;
        let s_low = (pl + ph * z) % q;
        let s_high = (pl + q - (ph * z) % q) % q;
        let p_low = (h_lo as u64 * s_low) % q;
        let p_high = (h_hi as u64 * s_high) % q;
        let spec_low = (p_low + p_high) % q;
        let spec_high = ((p_low + q - p_high) * z_inv) % q;

        prop_assert_eq!(new_low % q, spec_low);
        prop_assert_eq!(new_high, spec_high);
    }

    #[test]
    fn fused_norm_step_matches_spec(
        buf_lo in 0u32..=((256 * Q as u64) as u32),
        buf_hi in 0u32..=((256 * Q as u64) as u32),
        c_lo in 0u16..(Q as u16),
        c_hi in 0u16..(Q as u16),
        s2_lo in -2047i16..=2047i16,
        s2_hi in -2047i16..=2047i16,
        zeta in 0u64..(Q as u64),
    ) {
        let kernel =
            fused_norm_step(buf_lo, buf_hi, c_lo, c_hi, s2_lo, s2_hi, zeta);

        // Non-wrapping spec: reduce mod q first, plain subtract.
        let q = Q as u64;
        let half_q = q / 2;
        let new_lo_red = ((buf_lo as u64) + (buf_hi as u64)) % q;
        let new_hi_red =
            ((buf_lo as u64 + LAZY_OFFSET_GS - buf_hi as u64) * zeta) % q;
        let raw_lo = ((c_lo as u64) + q - new_lo_red) % q;
        let raw_hi = ((c_hi as u64) + q - new_hi_red) % q;
        let s1c_lo = if raw_lo > half_q { q - raw_lo } else { raw_lo };
        let s1c_hi = if raw_hi > half_q { q - raw_hi } else { raw_hi };
        let s2_lo_i = s2_lo as i64;
        let s2_hi_i = s2_hi as i64;
        let spec = s1c_lo * s1c_lo
            + s1c_hi * s1c_hi
            + (s2_lo_i * s2_lo_i + s2_hi_i * s2_hi_i) as u64;

        prop_assert_eq!(kernel, spec);
    }
}

// Random-polynomial differential against schoolbook negacyclic mul. This
// is the only test that catches drift in top-level NTT loop bounds, the
// twiddle index, or final-level handling — the kernel proptests above
// verify each butterfly in isolation, and the scalar reference test
// shares twiddle order with the optimized path. This stresses the full
// pipeline (forward NTT → pointwise → inverse NTT) on random inputs.
// Each case runs a 512×512 = 262144-multiply schoolbook product, so cases
// are kept low; 64 random pairs is enough to flush out structural drift
// without adding seconds to the unit-test pass.
proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn ntt_mul_matches_schoolbook_random(
        a in prop::collection::vec(0u32..Q, N..=N),
        b in prop::collection::vec(0u32..Q, N..=N),
    ) {
        let mut a_arr = [0u32; N];
        let mut b_arr = [0u32; N];
        a_arr.copy_from_slice(&a);
        b_arr.copy_from_slice(&b);

        // Schoolbook negacyclic c = a * b in Z_q[x]/(x^N + 1).
        let mut c_school = [0i64; N];
        #[allow(clippy::needless_range_loop)]
        for i in 0..N {
            for j in 0..N {
                let prod = (a_arr[i] as i64) * (b_arr[j] as i64);
                let k = i + j;
                if k < N {
                    c_school[k] += prod;
                } else {
                    c_school[k - N] -= prod;
                }
            }
        }
        let mut c_school_q = [0u32; N];
        for i in 0..N {
            c_school_q[i] = c_school[i].rem_euclid(Q as i64) as u32;
        }

        // NTT pipeline: forward, pointwise, inverse.
        let mut a_ntt = a_arr;
        let mut b_ntt = b_arr;
        ntt(&mut a_ntt);
        ntt(&mut b_ntt);
        let mut prod = [0u32; N];
        for i in 0..N {
            prod[i] = (a_ntt[i] as u64 * b_ntt[i] as u64 % Q as u64) as u32;
        }
        inv_ntt(&mut prod);

        prop_assert_eq!(prod, c_school_q);
    }
}

// ---------------------------------------------------------------------------
// Regression: lazy-`t` offset must cover the TRUE input bound 8·Q + 2047
// (signed s2 → Q + s2 mapping), not 8·Q. With the old `8·Q²` offset,
// `a + offset - t` underflowed for b·zeta > 8·Q².
// ---------------------------------------------------------------------------

#[test]
fn lazy_t_true_bounds_arithmetic() {
    let q = Q as u64;
    assert_eq!(LAZY_T_INPUT_MAX, 8 * q + 2047);
    let max_t = LAZY_T_INPUT_MAX * (q - 1);
    let old_offset = 8 * q * q;
    assert!(max_t > old_offset, "old 8·Q² offset is insufficient");
    assert!(max_t <= T_OFFSET_LAZY_T, "9·Q² covers the true max t");
    assert!(T_OFFSET_LAZY_T.is_multiple_of(q));
    assert!(max_t <= u32::MAX as u64);
}

#[test]
fn lazy_t_butterfly_at_true_bound_is_exact() {
    let q = Q as u64;
    let old_offset = 8 * q * q;
    let b = LAZY_T_INPUT_MAX;
    let zeta = q - 1;
    for a in [0u64, 1, q, LAZY_T_INPUT_MAX] {
        let t = b * zeta;
        assert!(t > old_offset + a, "case must exceed the old offset");
        let exact_lo = (a + t) % q;
        let exact_hi = (a + q - t % q) % q;

        let (lo, hi) = ct_butterfly_lazy_t_step(a, b, zeta);
        assert_eq!((lo as u32) as u64, lo, "lo fits u32");
        assert_eq!((hi as u32) as u64, hi, "hi fits u32");
        assert_eq!(lo % q, exact_lo);
        assert_eq!(hi % q, exact_hi);

        // The old constant underflows (wraps in u64) and is truncated by
        // `as u32`, producing a wrong residue.
        let old_hi = (a + old_offset).wrapping_sub(t);
        assert!(a + old_offset < t);
        assert_ne!(
            (old_hi as u32) as u64 % q,
            exact_hi,
            "old offset gives a wrong residue (a={a})"
        );
    }
}

#[test]
fn fused_step_at_true_bounds_is_exact() {
    let q = Q as u64;
    // Worst case: prev_high at the lazy-t output maximum, z = Q-1.
    let hi_max = LAZY_T_OUTPUT_MAX as u32;
    for (prev_low, prev_high) in [(hi_max, hi_max), (0, hi_max), (hi_max, 0)] {
        let (h_lo, h_hi) = (Q as u16 - 1, Q as u16 - 1);
        let (z, z_inv) = (q - 1, q - 1);
        let (nl, nh) = fused_step_kernel(prev_low, prev_high, h_lo, h_hi, z, z_inv);
        let pl = prev_low as u64 % q;
        let ph = prev_high as u64 % q;
        let s_low = (pl + ph * z) % q;
        let s_high = (pl + q - (ph * z) % q) % q;
        let p_low = h_lo as u64 * s_low % q;
        let p_high = h_hi as u64 * s_high % q;
        assert_eq!(nl % q, (p_low + p_high) % q);
        assert_eq!(nh, (p_low + q - p_high) * z_inv % q);
    }
}

/// Worst-case end-to-end: drive the strict first-level mapping and 6 more
/// strict levels with extreme values and check that no lazy-t input exceeds
/// LAZY_T_INPUT_MAX while the full NTT still matches the reference.
#[test]
fn forward_ntt_from_signed_extremes_matches_reference() {
    for pattern in 0..4u32 {
        let mut s2 = [0i16; N];
        for (i, c) in s2.iter_mut().enumerate() {
            *c = match pattern {
                0 => 2047,
                1 => -2047,
                2 => {
                    if i % 2 == 0 {
                        2047
                    } else {
                        -2047
                    }
                }
                _ => {
                    if (i / 256) % 2 == 0 {
                        2047
                    } else {
                        -2047
                    }
                }
            };
        }
        let mut buf = [0u32; N];
        ntt_main_levels_from_signed(&mut buf, &s2);
        let mut canon = [0u32; N];
        for i in 0..N {
            canon[i] = (s2[i] as i64).rem_euclid(Q as i64) as u32;
        }
        let mut expect = reference_ntt(canon);
        // main levels + last level == full NTT; finish `buf` the same way.
        ntt_last_level(&mut buf);
        for v in buf.iter_mut() {
            *v %= Q;
        }
        for v in expect.iter_mut() {
            *v %= Q;
        }
        assert_eq!(buf, expect);
    }
}

// ---- the Lean model of the forward NTT's levels matches the code ----
//
// `formal_verification/Falcon512/LazyBound.lean` proves, for ANY twiddles < Q,
// that after the first level and six strict levels every value is
// <= LAZY_T_INPUT_MAX, so the lazy-`t` subtraction cannot underflow. It proves
// that for a functional model of the levels. This test is the link between
// that model and `ntt_main_levels_from_signed`: it implements the model
// exactly as the Lean file defines it (closed-form block/partner indexing, the
// twiddle of block `blk` at half-width `len` being ZETAS[N/(2*len) + blk]) and
// asserts the real code's output equals it bit for bit (u32 values, before the
// final len = 1 level), on random, extreme, sparse and adversarial inputs.

/// The Lean model: `s2` through the first level, the strict levels
/// len = N/4 ..= 4, then the lazy-`t` level (len = 2). Returns the values after
/// the lazy-`t` level and the largest value any lazy-`t` butterfly read.
fn lean_model_forward(s2: &[i16; N]) -> ([u64; N], u64) {
    let q = Q as u64;
    let zeta_of = |len: usize, blk: usize| ZETAS[N / (2 * len) + blk] as u64;

    // First level (len = N/2): input is Q + s2 as a natural number.
    let input: Vec<u64> = s2.iter().map(|&c| (q as i64 + c as i64) as u64).collect();
    let mut r = [0u64; N];
    for (i, out) in r.iter_mut().enumerate() {
        let len = N / 2;
        let (blk, high) = (i / (2 * len), (i / len) % 2 == 1);
        let j = if high { i - len } else { i };
        let t = input[j + len] * zeta_of(len, blk) % q;
        *out = if high { input[j] + q - t } else { input[j] + t };
    }
    // Strict levels, then the lazy-t level.
    let mut worst_input = 0;
    let mut len = N / 4;
    while len >= 2 {
        let prev = r;
        for (i, out) in r.iter_mut().enumerate() {
            let (blk, high) = (i / (2 * len), (i / len) % 2 == 1);
            let j = if high { i - len } else { i };
            let (a, b, z) = (prev[j], prev[j + len], zeta_of(len, blk));
            if len == 2 {
                worst_input = worst_input.max(a).max(b);
                let t = b * z;
                *out = if high { a + T_OFFSET_LAZY_T - t } else { a + t };
            } else {
                let t = b * z % q;
                *out = if high { a + q - t } else { a + t };
            }
        }
        len /= 2;
    }
    (r, worst_input)
}

fn check_model_against_code(s2: &[i16; N]) -> u64 {
    let (model, worst_input) = lean_model_forward(s2);
    let mut code = [0u32; N];
    ntt_main_levels_from_signed(&mut code, s2);
    for i in 0..N {
        assert_eq!(model[i], code[i] as u64, "index {i} for s2 = {s2:?}");
        assert!(model[i] <= LAZY_T_OUTPUT_MAX);
    }
    assert!(worst_input <= LAZY_T_INPUT_MAX);
    worst_input
}

#[test]
fn forward_ntt_levels_match_lean_model() {
    let mut rng = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = move || {
        rng = rng
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (rng >> 33) as usize
    };
    let mut worst = 0;

    // Uniform random, ternary extremes, and sparse inputs.
    for round in 0..4000 {
        let mut s2 = [0i16; N];
        for c in s2.iter_mut() {
            *c = match round % 3 {
                0 => (next() % 4095) as i16 - 2047,
                1 => [-2047i16, 2047, 0][next() % 3],
                _ => {
                    if next() % 16 == 0 {
                        [-2047i16, 2047][next() % 2]
                    } else {
                        0
                    }
                }
            };
        }
        worst = worst.max(check_model_against_code(&s2));
    }
    // Constant, alternating and one-hot at every position, both signs.
    for sign in [-2047i16, 2047] {
        worst = worst.max(check_model_against_code(&[sign; N]));
        let mut alt = [0i16; N];
        for (i, c) in alt.iter_mut().enumerate() {
            *c = if i % 2 == 0 { sign } else { -sign };
        }
        worst = worst.max(check_model_against_code(&alt));
        for pos in 0..N {
            let mut one = [0i16; N];
            one[pos] = sign;
            worst = worst.max(check_model_against_code(&one));
        }
    }
    // Adversarial: hill-climb toward the largest lazy-t input (what the old
    // offset could not hold), then check that input too.
    let mut best = [0i16; N];
    let mut best_score = 0;
    for _ in 0..12 {
        let mut s2 = [0i16; N];
        for c in s2.iter_mut() {
            *c = [-2047i16, 2047, 0][next() % 3];
        }
        let mut score = lean_model_forward(&s2).1;
        for _ in 0..1500 {
            let i = next() % N;
            let old = s2[i];
            s2[i] = [-2047i16, 2047, 0, (next() % 4095) as i16 - 2047][next() % 4];
            let new = lean_model_forward(&s2).1;
            if new >= score {
                score = new;
            } else {
                s2[i] = old;
            }
        }
        if score > best_score {
            (best, best_score) = (s2, score);
        }
    }
    worst = worst.max(check_model_against_code(&best));
    println!("largest lazy-t input seen: {worst} (bound {LAZY_T_INPUT_MAX})");
    assert!(worst <= LAZY_T_INPUT_MAX);
}
