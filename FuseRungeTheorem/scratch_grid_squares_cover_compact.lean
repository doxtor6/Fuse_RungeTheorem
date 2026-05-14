import Mathlib

open scoped Topology

lemma compact_subset_open_has_thickening {K U : Set ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ρ > 0, Metric.thickening ρ K ⊆ U :=
  hK.exists_thickening_subset_open hU hKU

private lemma grid_squares_cover_compact
    {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (n : ℕ) (corner : Fin n → ℂ) (s : ℝ),
      0 < s ∧
      (∀ z ∈ K, ∃ i, z.re ∈ Set.Icc ((corner i).re) ((corner i).re + s) ∧
                     z.im ∈ Set.Icc ((corner i).im) ((corner i).im + s)) ∧
      (∀ i, ∀ w : ℂ, w.re ∈ Set.Icc ((corner i).re) ((corner i).re + s) →
                     w.im ∈ Set.Icc ((corner i).im) ((corner i).im + s) →
                     w ∈ U) := by
  classical
  -- Step 1: positive thickening collar.
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ := compact_subset_open_has_thickening hK hU hKU
  -- Step 2: side length s := ρ/3, so 2s < ρ.
  set s : ℝ := ρ / 3 with hs_def
  have hs_pos : 0 < s := by positivity
  have h2s_lt_ρ : 2 * s < ρ := by rw [hs_def]; linarith
  -- Step 3: K is bounded.
  obtain ⟨M, hM_pos, hM_sub⟩ :=
    hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  -- Step 4: define the predicate "square at (i,j) of side s meets K".
  let P : ℤ × ℤ → Prop := fun p =>
    ∃ z ∈ K,
      (p.1 : ℝ) * s ≤ z.re ∧ z.re ≤ (p.1 : ℝ) * s + s ∧
      (p.2 : ℝ) * s ≤ z.im ∧ z.im ≤ (p.2 : ℝ) * s + s
  -- The set of meeting indices is finite (bounded by K bounded).
  have hPbound : ∀ p : ℤ × ℤ, P p → |(p.1 : ℝ)| ≤ M / s + 1 ∧ |(p.2 : ℝ)| ≤ M / s + 1 := by
    intro p ⟨z, hz, h1, h2, h3, h4⟩
    have hzM : ‖z‖ ≤ M := by
      have := hM_sub hz
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    have hzre_abs : |z.re| ≤ M := (Complex.abs_re_le_norm z).trans hzM
    have hzim_abs : |z.im| ≤ M := (Complex.abs_im_le_norm z).trans hzM
    have hzre_lb : -M ≤ z.re := neg_le_of_abs_le hzre_abs
    have hzre_ub : z.re ≤ M := le_of_abs_le hzre_abs
    have hzim_lb : -M ≤ z.im := neg_le_of_abs_le hzim_abs
    have hzim_ub : z.im ≤ M := le_of_abs_le hzim_abs
    refine ⟨?_, ?_⟩
    · -- (p.1 : ℝ) * s ≤ z.re ≤ M  so p.1 ≤ M/s.
      -- (p.1 : ℝ) * s + s ≥ z.re ≥ -M so p.1 ≥ -M/s - 1.
      have hub : (p.1 : ℝ) * s ≤ M := h1.trans hzre_ub
      have hlb : -M - s ≤ (p.1 : ℝ) * s := by linarith
      have hub' : (p.1 : ℝ) ≤ M / s := by
        have := (le_div_iff₀ hs_pos).mpr hub
        exact this
      have hlb' : -M/s - 1 ≤ (p.1 : ℝ) := by
        have := (div_le_iff₀ hs_pos).mpr (by linarith : (-M / s - 1) * s ≤ (p.1 : ℝ) * s)
        sorry
      sorry
    · sorry
  sorry
