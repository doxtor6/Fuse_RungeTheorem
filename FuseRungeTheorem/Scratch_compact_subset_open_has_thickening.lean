import Mathlib

open scoped Topology

lemma compact_subset_open_has_thickening {K U : Set ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ρ > 0, {z : ℂ | Metric.infDist z K < ρ} ⊆ U := by
  -- Mathlib gives the thickening version directly:
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  -- z ∈ {z | Metric.infDist z K < δ}
  by_cases hKemp : K.Nonempty
  · apply hsub
    rw [Metric.mem_thickening_iff_infDist_lt hKemp]
    exact hz
  · -- K is empty, then infDist z K = 0, so 0 < δ.
    -- But we need z ∈ U. This won't work in general.
    rw [Set.not_nonempty_iff_eq_empty] at hKemp
    subst hKemp
    -- Goal: z ∈ U.
    -- This is unprovable in general. So the statement is false.
    sorry
