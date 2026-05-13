import Mathlib

open scoped Topology

/-
The stated lemma `compact_subset_open_has_thickening` is FALSE as written.

Statement:
  ∀ {K U : Set ℂ}, IsCompact K → IsOpen U → K ⊆ U →
    ∃ ρ > 0, {z : ℂ | Metric.infDist z K < ρ} ⊆ U

Counterexample: K = ∅, U = ∅.

Reason: `Metric.infDist z (∅ : Set ℂ) = 0` (by `Metric.infDist_empty`).
So for any `ρ > 0`, every `z` satisfies `Metric.infDist z ∅ = 0 < ρ`, hence
the set `{z | Metric.infDist z ∅ < ρ}` equals `Set.univ`. But the conclusion
requires this set to be a subset of `U = ∅`, which fails.

The intended Mathlib lemma `IsCompact.exists_thickening_subset_open` works
because `Metric.thickening` is defined via `infEDist`, and `infEDist z ∅ = ∞`,
so `Metric.thickening ρ ∅ = ∅`. The user's restatement using `infDist` lost
this empty-case behaviour because `ENNReal.toReal ∞ = 0`.

Verified counterexample below.
-/

example (z : ℂ) : Metric.infDist z (∅ : Set ℂ) = 0 := Metric.infDist_empty

example : ¬ (∀ {K U : Set ℂ}
    (_ : IsCompact K) (_ : IsOpen U) (_ : K ⊆ U),
    ∃ ρ > 0, {z : ℂ | Metric.infDist z K < ρ} ⊆ U) := by
  intro h
  obtain ⟨ρ, hρ, hsub⟩ := h (K := (∅ : Set ℂ)) (U := (∅ : Set ℂ))
    isCompact_empty isOpen_empty (Set.empty_subset _)
  have h0 : (0 : ℂ) ∈ ({z : ℂ | Metric.infDist z (∅ : Set ℂ) < ρ}) := by
    simp [Metric.infDist_empty, hρ]
  exact (hsub h0).elim

/-
Below: the partial proof of `compact_subset_open_has_thickening`.
Closes in the nonempty case via `IsCompact.exists_thickening_subset_open`
and `Metric.mem_thickening_iff_infDist_lt`. The empty case is genuinely
impossible without strengthening the hypothesis (e.g. requiring `K.Nonempty`,
or equivalently rephrasing the conclusion using `Metric.thickening`).
-/
lemma compact_subset_open_has_thickening {K U : Set ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ρ > 0, {z : ℂ | Metric.infDist z K < ρ} ⊆ U := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  by_cases hKemp : K.Nonempty
  · exact hsub ((Metric.mem_thickening_iff_infDist_lt hKemp).mpr hz)
  · -- K = ∅, so infDist z K = 0 < δ holds vacuously and z is arbitrary.
    -- We would need z ∈ U for every z : ℂ, which fails when U ≠ Set.univ.
    -- Signature mismatch: the statement is false in this corner.
    rw [Set.not_nonempty_iff_eq_empty] at hKemp
    subst hKemp
    sorry
