/-
  Falcon512.LazyBound — END-TO-END proof that the forward NTT of a signed
  s2 keeps every value at the lazy-t level (len = 2) below
  `LAZY_T_INPUT_MAX = 8·Q + 2047`, so `T_OFFSET_LAZY_T = 9·Q²` suffices.

  `Bounds.lean` proves `lazy_t_offset_sufficient` only UNDER the hypothesis
  `b ≤ LAZY_T_INPUT_MAX`. This file discharges that hypothesis.

  FUNCTIONAL MODEL (arrays are functions `Nat → Nat`).  For half-width `len`
  and a twiddle function `zeta : Nat → Nat` of the block index, output index
  `i` has block `blk = i / (2*len)`, side `(i / len) % 2` (0 = low half,
  1 = high half) and low-half pair index `j = blk*2*len + i % len`.
    low : r j + (r (j+len) * zeta blk) % Q
    high: r j + Q - (r (j+len) * zeta blk) % Q
  Correspondence with `src/ntt.rs`:
    * `ctLevel`/`strictLevel`  <->  `ct_butterfly_step` (`let t = b * zeta % q;
      (a + t, a + q - t)`) as invoked by `ct_butterfly!` in
      `ntt_levels_after_first` for len = 128, 64, 32, 16, 8, 4.
    * `lazyTLevel`            <->  `ct_butterfly_lazy_t_step` (`let t = b * zeta;
      (a + t, a + T_OFFSET_LAZY_T - t)`), the final len = 2 level.
    * `inNat`                  <->  `(s2[i] as i64 as u64).wrapping_add(q)`,
      i.e. the natural number `Q + s2[i]` (exact since |s2| <= 2047 < Q).
    * `firstLevel`            <->  `sgn_ct_bf!` in `ntt_main_levels_from_signed`
      (`t = r_hi * zeta % q; r[j] = r_lo + t; r[j+N/2] = r_lo + q - t`), len = 256,
      zeta = `ZETAS[1]`.
    * `fwdUpTo`: the twiddle of level `l`, block `blk` is `zs l blk`
      (`zs 0 _ = ZETAS[1]`, `zs l blk = ZETAS[2^l + blk]` for l >= 1, the
      Rust `k` incrementing once per block). Bounds only use `zs l blk < Q`.
  CAVEATS: the model abstracts the unrolled loops / in-place `r` updates into
  pure per-level functions; the exact correspondence (including twiddle
  indexing and loop unrolling) is checked by the Rust differential test
  `forward_ntt_levels_match_lean_model` in `internal-tests/ntt.rs`, not in
  Lean. Nat subtraction is truncated in Lean; the proofs show it is exact.
-/

import Falcon512.Defs
import Falcon512.Bounds

namespace Falcon512.Spec.LazyBound

open Falcon512.Spec
open Falcon512.Spec.Bounds

def pairLo (len i : Nat) : Nat := (i / (2 * len)) * (2 * len) + i % len

/-- Generic CT level: `red` reduces `t`, `c` is the high-half offset. -/
def ctLevel (len : Nat) (zeta : Nat → Nat) (red : Nat → Nat) (c : Nat)
    (r : Nat → Nat) (i : Nat) : Nat :=
  let t := red (r (pairLo len i + len) * zeta (i / (2 * len)))
  if (i / len) % 2 = 0 then r (pairLo len i) + t else r (pairLo len i) + c - t

def strictLevel (len : Nat) (zeta : Nat → Nat) (r : Nat → Nat) : Nat → Nat :=
  ctLevel len zeta (fun t => t % Q) Q r

def lazyTLevel (zeta : Nat → Nat) (r : Nat → Nat) : Nat → Nat :=
  ctLevel 2 zeta (fun t => t) T_OFFSET_LAZY_T r

/-- Natural value `Q + s i` (Rust `wrapping_add`). -/
def inNat (s : Nat → Int) (i : Nat) : Nat := ((Q : Int) + s i).toNat

def firstLevel (s : Nat → Int) (zeta : Nat → Nat) : Nat → Nat :=
  strictLevel 256 zeta (inNat s)

def lenAt (l : Nat) : Nat := 256 / 2 ^ l

/-- Signed input, first level, then `k` strict levels (len 128, 64, ...). -/
def fwdUpTo (s : Nat → Int) (zs : Nat → Nat → Nat) : Nat → (Nat → Nat)
  | 0 => firstLevel s (zs 0)
  | k + 1 => strictLevel (lenAt (k + 1)) (zs (k + 1)) (fwdUpTo s zs k)

theorem pairLo_lt (len i : Nat) (hl : 0 < len) (hN : N % (2 * len) = 0)
    (hi : i < N) : pairLo len i + len < N := by
  unfold pairLo
  have hm : 0 < 2 * len := by omega
  have hdv : N = (2 * len) * (N / (2 * len)) :=
    (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hN)).symm
  have h1 : i / (2 * len) < N / (2 * len) := by
    rw [Nat.div_lt_iff_lt_mul hm]
    calc i < N := hi
      _ = N / (2 * len) * (2 * len) := by rw [Nat.mul_comm]; exact hdv
  have h2 : (i / (2 * len) + 1) * (2 * len) ≤ N / (2 * len) * (2 * len) :=
    Nat.mul_le_mul_right _ h1
  have h3 : (i / (2 * len) + 1) * (2 * len) = (i / (2 * len)) * (2 * len) + 2 * len := by
    rw [Nat.add_mul, Nat.one_mul]
  have h4 : N / (2 * len) * (2 * len) = N := by rw [Nat.mul_comm]; exact hdv.symm
  have h5 : i % len < len := Nat.mod_lt _ hl
  omega

theorem strictLevel_bound (len : Nat) (zeta : Nat → Nat) (r : Nat → Nat) (B : Nat)
    (hl : 0 < len) (hN : N % (2 * len) = 0)
    (_hz : ∀ k, zeta k < Q) (hr : ∀ i, i < N → r i ≤ B) :
    ∀ i, i < N → strictLevel len zeta r i ≤ B + Q := by
  intro i hi
  have hlt := pairLo_lt len i hl hN hi
  have ha : r (pairLo len i) ≤ B := hr _ (by omega)
  have hq : (r (pairLo len i + len) * zeta (i / (2 * len))) % Q < Q := Nat.mod_lt _ q_pos
  unfold strictLevel ctLevel
  simp only []
  split <;> omega

theorem firstLevel_bound (s : Nat → Int) (zeta : Nat → Nat)
    (hs : ∀ i, -2047 ≤ s i ∧ s i ≤ 2047) (hz : ∀ k, zeta k < Q) :
    ∀ i, i < N → firstLevel s zeta i ≤ 2 * Q + 2047 := by
  have hin : ∀ i, i < N → inNat s i ≤ Q + 2047 := by
    intro i _
    have := hs i
    unfold inNat Q
    omega
  have := strictLevel_bound 256 zeta (inNat s) (Q + 2047) (by omega)
    (by unfold N; omega) hz hin
  intro i hi
  have := this i hi
  unfold firstLevel
  omega

theorem lenAt_ok (l : Nat) (hl : 1 ≤ l) (h7 : l ≤ 7) :
    0 < lenAt l ∧ N % (2 * lenAt l) = 0 := by
  have : l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5 ∨ l = 6 ∨ l = 7 := by omega
  rcases this with h | h | h | h | h | h | h <;> subst h <;>
    (unfold lenAt N; decide)

theorem fwdUpTo_bound (s : Nat → Int) (zs : Nat → Nat → Nat)
    (hs : ∀ i, -2047 ≤ s i ∧ s i ≤ 2047) (hz : ∀ l k, zs l k < Q) :
    ∀ k, k ≤ 6 → ∀ i, i < N → fwdUpTo s zs k i ≤ (k + 2) * Q + 2047 := by
  intro k
  induction k with
  | zero =>
    intro _ i hi
    have := firstLevel_bound s (zs 0) hs (hz 0) i hi
    simp only [fwdUpTo]
    omega
  | succ k ih =>
    intro hk i hi
    have ⟨hp, hd⟩ := lenAt_ok (k + 1) (by omega) (by omega)
    have := strictLevel_bound (lenAt (k + 1)) (zs (k + 1)) (fwdUpTo s zs k)
      ((k + 2) * Q + 2047) hp hd (hz (k + 1)) (ih (by omega)) i hi
    have e : (k + 1 + 2) * Q = (k + 2) * Q + Q := by
      rw [show k + 1 + 2 = (k + 2) + 1 from rfl, Nat.succ_mul]
    simp only [fwdUpTo]
    omega

/-- Inputs to the lazy-t level (after first level + 6 strict levels). -/
theorem forward_ntt_input_to_lazy_t_le (s : Nat → Int) (zs : Nat → Nat → Nat)
    (hs : ∀ i, -2047 ≤ s i ∧ s i ≤ 2047) (hz : ∀ l k, zs l k < Q) :
    ∀ i, i < N → fwdUpTo s zs 6 i ≤ LAZY_T_INPUT_MAX := by
  intro i hi
  have := fwdUpTo_bound s zs hs hz 6 (by omega) i hi
  unfold LAZY_T_INPUT_MAX
  omega

theorem lazy_t_no_underflow_end_to_end (s : Nat → Int) (zs : Nat → Nat → Nat)
    (hs : ∀ i, -2047 ≤ s i ∧ s i ≤ 2047) (hz : ∀ l k, zs l k < Q)
    (zl : Nat → Nat) (hzl : ∀ k, zl k < Q) :
    ∀ i, i < N →
      (fwdUpTo s zs 6 (pairLo 2 i + 2) * zl (i / (2 * 2))
          ≤ fwdUpTo s zs 6 (pairLo 2 i) + T_OFFSET_LAZY_T) ∧
      lazyTLevel zl (fwdUpTo s zs 6) i < 2 ^ 32 := by
  intro i hi
  have hlt := pairLo_lt 2 i (by omega) (by unfold N; decide) hi
  have hb := forward_ntt_input_to_lazy_t_le s zs hs hz (pairLo 2 i + 2) (by omega)
  have ha := forward_ntt_input_to_lazy_t_le s zs hs hz (pairLo 2 i) (by omega)
  have hsuf := lazy_t_offset_sufficient (fwdUpTo s zs 6 (pairLo 2 i))
    (fwdUpTo s zs 6 (pairLo 2 i + 2)) (zl (i / (2 * 2))) hb (hzl _)
  have hf := lazy_t_fits_u32 _ _ hb (hzl (i / (2 * 2)))
  have hm : fwdUpTo s zs 6 (pairLo 2 i + 2) * zl (i / (2 * 2))
      ≤ (8 * Q + 2047) * (Q - 1) :=
    Nat.mul_le_mul hb (by have := hzl (i / (2 * 2)); omega)
  have hT : T_OFFSET_LAZY_T = 9 * 12289 * 12289 := rfl
  have hQ : Q = 12289 := rfl
  have hnum : (8 * Q + 2047) * (Q - 1) = 1233211392 := by rw [hQ]
  have hU : LAZY_T_INPUT_MAX = 8 * 12289 + 2047 := rfl
  refine ⟨hsuf, ?_⟩
  unfold lazyTLevel ctLevel
  simp only []
  split <;> omega

/-- The previous offset `8·Q²` was insufficient for the true input max. -/
theorem old_offset_insufficient : (8 * Q + 2047) * (Q - 1) > 8 * Q * Q := by
  unfold Q; omega

end Falcon512.Spec.LazyBound
