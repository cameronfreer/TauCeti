/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti.ViaKoopman.BlockReduction

/-!
# Displacing the last coordinate of a block

The step that decouples one factor from a block, over an invariant event.

Appending the coordinate `r + m` to the prefix `0, 1, …, r - 1` gives a strictly increasing
selection for *every* `m`, so the block transport makes the set-integral of the resulting product
independent of `m`. Averaging over `m < n` therefore leaves the left-hand side unchanged while
turning the right-hand side into a Birkhoff average of `𝟙_B ∘ (· r)` under the shift — which is
where the mean ergodic theorem enters.

## Main results

* `strictMono_snoc_prefix` — appending `r + m` to the prefix is strictly increasing;
* `ContractableLaw.setLIntegral_prefix_mul_indicator_eq_of_displaced` — the resulting set-integral
  does not depend on the displacement `m`.

This is the engine of the Koopman factorization: the `m`-independence is what allows an average
over `m` to be inserted for free, and that average is what the ergodic theorem consumes.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- **Appending a later coordinate to the prefix is strictly increasing.** The prefix occupies
`0, 1, …, r - 1` and the appended coordinate is `r + m`, so the selection is strictly increasing
whatever the displacement `m`. -/
theorem strictMono_snoc_prefix (r m : ℕ) :
    StrictMono (Fin.snoc (fun i : Fin r => (i : ℕ)) (r + m) : Fin (r + 1) → ℕ) := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  rw [Fin.snoc_castSucc]
  rcases Fin.eq_castSucc_or_eq_last i.succ with ⟨j, hj⟩ | hj
  · rw [hj, Fin.snoc_castSucc]
    have : (i : ℕ) < (j : ℕ) := by
      have := congrArg Fin.val hj
      simp only [Fin.val_succ, Fin.val_castSucc] at this
      omega
    exact_mod_cast this
  · rw [hj, Fin.snoc_last]
    exact lt_of_lt_of_le i.isLt (Nat.le_add_right r m)

/-- **The displaced block has a law independent of the displacement.** Over an invariant event,
pushing the restricted law forward along the prefix-plus-`r + m` selection gives the same measure
for every `m` — namely the pushforward along the plain prefix of length `r + 1`.

This is the `m`-independence the decoupling runs on: because the right-hand side does not mention
`m`, an average over `m < n` may be inserted on the left without changing anything, and that
average is a Birkhoff average of the last coordinate under the shift. -/
theorem ContractableLaw.map_restrict_snoc_prefix_eq_prefixProj
    {ρ : Measure (ℕ → α)} (hρ : ContractableLaw ρ) (r m : ℕ)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A) :
    (ρ.restrict A).map
        (fun x : ℕ → α => fun i : Fin (r + 1) =>
          x ((Fin.snoc (fun j : Fin r => (j : ℕ)) (r + m) : Fin (r + 1) → ℕ) i))
      = (ρ.restrict A).map (prefixProj α (r + 1)) :=
  hρ.map_restrict_block_eq_prefixProj_of_measurableSet_invariants (strictMono_snoc_prefix r m) hA

end Probability

end TauCeti

end
