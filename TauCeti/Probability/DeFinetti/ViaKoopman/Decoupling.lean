/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti.ViaKoopman.BlockReduction
public import Mathlib.Dynamics.BirkhoffSum.Average

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

omit [MeasurableSpace α] in
/-- **The displaced coordinates are a Birkhoff average.** Reading coordinate `r` along the shift
orbit gives exactly the displaced coordinates `r, r + 1, …`, so the average over displacements is
`birkhoffAverage` of the single observable `𝟙_B ∘ (· r)`.

This is where the two halves of the argument meet: the left side is what the invariant transport
controls (each term has the same integral over an invariant event), and the right side is what the
mean ergodic theorem converges. -/
theorem birkhoffAverage_shift_coord_eq {B : Set α} (r n : ℕ) (x : ℕ → α) :
    birkhoffAverage ℝ (shift α) (fun y : ℕ → α => (B.indicator (fun _ => (1 : ℝ)) (y r))) n x
      = (n : ℝ)⁻¹ * ∑ m ∈ Finset.range n, B.indicator (fun _ => (1 : ℝ)) (x (r + m)) := by
  rw [birkhoffAverage, birkhoffSum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [shift_iterate_apply]

/-- **Every coordinate has the same set-integral over an invariant event.** The single-coordinate
instance of the block transport: reading coordinate `r` and reading coordinate `0` give the same
integral of any measurable real observable, over any invariant event. -/
theorem ContractableLaw.setIntegral_comp_coord_eq_zero_of_measurableSet_invariants
    {ρ : Measure (ℕ → α)} (hρ : ContractableLaw ρ) (r : ℕ)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A)
    {f : α → ℝ} (hf : Measurable f) :
    ∫ x in A, f (x r) ∂ρ = ∫ x in A, f (x 0) ∂ρ := by
  classical
  have hmap := hρ.map_restrict_block_eq_prefixProj_of_measurableSet_invariants
    (k := fun _ : Fin 1 => r) (Subsingleton.strictMono _) hA
  have hmap0 := hρ.map_restrict_block_eq_prefixProj_of_measurableSet_invariants
    (k := fun _ : Fin 1 => 0) (Subsingleton.strictMono _) hA
  have hg : Measurable fun y : Fin 1 → α => f (y 0) := hf.comp (measurable_pi_apply 0)
  have hcoord : ∀ (s : ℕ), Measurable fun x : ℕ → α => fun _ : Fin 1 => x s :=
    fun s => measurable_pi_lambda _ fun _ => measurable_pi_apply s
  have key : ∀ s : ℕ, StrictMono (fun _ : Fin 1 => s) → ∫ x in A, f (x s) ∂ρ
      = ∫ y, f (y 0) ∂((ρ.restrict A).map (prefixProj α 1)) := by
    intro s hs
    rw [← hρ.map_restrict_block_eq_prefixProj_of_measurableSet_invariants hs hA,
      integral_map (hcoord s).aemeasurable hg.aestronglyMeasurable]
  rw [key r (Subsingleton.strictMono _), key 0 (Subsingleton.strictMono _)]

end Probability

end TauCeti

end
