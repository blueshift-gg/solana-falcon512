/-
  Falcon512.NTT — Number Theoretic Transform correctness.

  Proves that the CT and GS butterflies are mutual inverses,
  that the NTT round-trip identity holds at the butterfly level,
  and key algebraic constants (N_INV, PSI).

  Core Lean 4 only (no Mathlib): modular ring reasoning is done over `Int`
  with `%`, i.e. in Z/QZ via congruences.
-/

import Falcon512.Defs

namespace Falcon512.Spec.NTT

open Falcon512.Spec

-- ============================================================================
-- N_INV correctness
-- ============================================================================

def N_INV : Nat := 12265

theorem n_inv_correct : (N_INV * N) % Q = 1 := by decide

-- ============================================================================
-- PSI (primitive 2N-th root of unity)
-- ============================================================================

def PSI : Nat := 49

theorem psi_is_root : powQ PSI N = Q - 1 := by
  simp [powQ, mulQ, PSI, N, Q]

theorem psi_order_divides : powQ PSI (2 * N) = 1 := by
  simp [powQ, mulQ, PSI, N, Q]

-- ============================================================================
-- CT/GS butterfly inverse relationship
-- ============================================================================

/-- A CT butterfly followed by a GS butterfly with the inverse twiddle
    factor recovers the original pair scaled by 2.
    Stated over `Int` with `% Q` (congruence mod Q; equivalent to the
    former `ZMod Q` statement, where `z⁻¹` is any `zi` with
    `z * zi ≡ 1 (mod Q)`). -/
theorem ct_gs_inverse_zmod (a b z zi : Int)
    (hz : (z * zi) % (Q : Int) = 1) :
    let lo := a + b * z
    let hi := a - b * z
    (lo + hi) % (Q : Int) = (2 * a) % (Q : Int) ∧
    ((lo - hi) * zi) % (Q : Int) = (2 * b) % (Q : Int) := by
  intro lo hi
  constructor
  · have : lo + hi = 2 * a := by
      show a + b * z + (a - b * z) = 2 * a
      omega
    rw [this]
  · have h1 : (lo - hi) * zi = 2 * b * (z * zi) := by
      have e : lo - hi = 2 * (b * z) := by
        show a + b * z - (a - b * z) = 2 * (b * z)
        omega
      rw [e, Int.mul_assoc, Int.mul_assoc]
      rw [Int.mul_assoc]
    rw [h1, Int.mul_emod, hz]
    simp

-- ============================================================================
-- Full NTT round-trip scaling factor
-- ============================================================================
--
-- `ct_gs_inverse_zmod` above establishes the per-level round-trip (forward CT
-- followed by inverse GS recovers `(2a, 2b)`). The full NTT applies log₂(N)=9
-- levels, accumulating a factor of `2^9 = 512 = N`, cancelled by `N_INV`
-- (pre-folded into the prepared pubkey). The cancellation `N_INV * N ≡ 1
-- (mod Q)` is proved as `n_inv_correct` above.

-- ============================================================================
-- PSI is a primitive 2N-th root of unity in Z_q
-- ============================================================================

/-- PSI has order exactly 2N in Z_q*: `psi^N = -1 (mod Q)` and
    `psi^(2N) = 1 (mod Q)`. These are the two scalar facts that make
    PSI a primitive 2N-th root of unity, the precondition for the
    NTT-as-ring-isomorphism construction (`Z_q[x]/(x^N+1) ↔ Z_q^N` via
    CRT).

    This lemma proves *only* the order facts; the full ring-isomorphism
    claim (that NTT-pointwise-mul corresponds to polynomial mul mod
    x^N+1) is exhaustively checked by the
    `ntt_multiplication_matches_schoolbook` test in `src/ntt.rs`. -/
theorem psi_has_order_2N :
    powQ PSI N = Q - 1 ∧ powQ PSI (2 * N) = 1 :=
  ⟨psi_is_root, psi_order_divides⟩

end Falcon512.Spec.NTT
