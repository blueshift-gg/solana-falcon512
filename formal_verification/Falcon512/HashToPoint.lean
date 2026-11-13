/-
  Falcon512.HashToPoint — Uniformity of the rejection-sampled output.

  Falcon's HashToPoint reads SHAKE-256 output as a stream of 16-bit
  candidates and accepts iff `w < 5*Q`. The accepted residue is then
  used as a coefficient of the challenge polynomial `c`.

  This file proves the rejection bound `5*Q` is the right one: every
  residue r ∈ [0, Q) has exactly 5 preimages in the accept set, so the
  conditional distribution of `w mod Q` given acceptance is uniform —
  zero bias.

  Why this matters: a wrong threshold (e.g. accepting w < 6*Q, which
  exceeds 2^16) would either be incorrect (overflow) or, more subtly,
  give a non-uniform `c`, weakening the security argument. Accepting
  too small a threshold (e.g. w < 4*Q) would still be uniform but
  reject more candidates — wasted SHAKE work, not a soundness issue.

  Core Lean only (no Mathlib): the accept set is `List.range (5*Q)`, fibres
  are `List.filter`s and cardinalities are `List.length`.
-/

import Falcon512.Defs

namespace Falcon512.Spec.HashToPoint

open Falcon512.Spec

/-- The accept set: 16-bit candidates `w` with `w < 5*Q`
    (as the list `[0, 1, ..., 5*Q-1]`; formerly `Finset.range (5*Q)`). -/
def acceptSet : List Nat := List.range (5 * Q)

theorem acceptSet_card : acceptSet.length = 5 * Q := by
  unfold acceptSet
  exact List.length_range _

/-- The accept set fits in the 16-bit candidate range. -/
theorem acceptSet_fits_u16 : 5 * Q ≤ 2^16 := by
  unfold Q; omega

/-- 6Q would NOT fit — confirms 5Q is the *largest* multiple of Q
    below 2^16, hence the correct rejection threshold. -/
theorem six_q_exceeds_u16 : 6 * Q > 2^16 := by
  unfold Q; omega

/-- The accepted candidates `w ∈ [0, 5Q)` whose residue mod Q
    equals `r` (formerly a `Finset.filter`; now a `List.filter`). -/
def residueFiber (r : Nat) : List Nat :=
  acceptSet.filter (fun w => w % Q = r)

/-- For every residue `r < Q`, the fiber inside the accept set is
    exactly `{r, r+Q, r+2Q, r+3Q, r+4Q}` — i.e. the five values
    obtained by adding multiples of Q to `r`, all bounded by 5Q.
    (Stated as membership equivalence with the explicit five-element
    list; this is the `Finset` equality of the earlier statement.) -/
theorem residueFiber_eq_image (r : Nat) (hr : r < Q) :
    ∀ w, w ∈ residueFiber r ↔
      w ∈ (List.range 5).map (fun k => r + k * Q) := by
  intro w
  simp only [residueFiber, acceptSet, List.mem_filter, List.mem_range,
             List.mem_map, decide_eq_true_eq]
  unfold Q at *
  constructor
  · rintro ⟨hwlt, hwmod⟩
    exact ⟨w / 12289, by omega, by omega⟩
  · rintro ⟨k, hk5, rfl⟩
    omega

/-- Counting lemma: among `[0, n)` exactly `n / Q + [r < n % Q]` numbers
    are `≡ r (mod Q)`. -/
theorem filter_range_length (r : Nat) (hr : r < Q) (n : Nat) :
    ((List.range n).filter (fun w => w % Q = r)).length
      = n / Q + (if r < n % Q then 1 else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    unfold Q at *
    by_cases h : n % 12289 = r
    · simp [h]
      (repeat' split) <;> omega
    · simp [h]
      (repeat' split) <;> omega

/-- Every residue's fiber has cardinality exactly 5. -/
theorem residueFiber_card (r : Nat) (hr : r < Q) :
    (residueFiber r).length = 5 := by
  unfold residueFiber acceptSet
  rw [filter_range_length r hr]
  unfold Q at *
  split <;> omega

/-- **Uniformity theorem.** Given a uniform random `w ∈ [0, 5Q)`,
    the residue `w mod Q` is uniformly distributed over `[0, Q)`.

    Stated as a counting claim: every residue has the same number of
    preimages (= 5). The probability statement
    `Pr[w mod Q = r | w < 5Q] = 1/Q` follows by dividing both sides
    of `residueFiber_card` by `acceptSet_card = 5Q`. -/
theorem hash_to_point_uniform (r : Nat) (hr : r < Q) :
    (residueFiber r).length * Q = acceptSet.length := by
  rw [residueFiber_card r hr, acceptSet_card]

end Falcon512.Spec.HashToPoint
