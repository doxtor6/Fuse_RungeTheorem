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
  -- Predicate "square at (i,j) meets K", with classical decidability.
  let P : ℤ × ℤ → Prop := fun p =>
    ∃ z ∈ K,
      (p.1 : ℝ) * s ≤ z.re ∧ z.re ≤ (p.1 : ℝ) * s + s ∧
      (p.2 : ℝ) * s ≤ z.im ∧ z.im ≤ (p.2 : ℝ) * s + s
  -- Bound on integer pairs satisfying P.
  set N : ℤ := ⌈M / s⌉ + 1 with hN_def
  have hN_pos : 0 < N := by
    rw [hN_def]
    have : 0 ≤ ⌈M / s⌉ := Int.ceil_nonneg (by positivity)
    omega
  -- Lattice and filter.
  let lattice : Finset (ℤ × ℤ) :=
    (Finset.Ico (-N) (N + 1)) ×ˢ (Finset.Ico (-N) (N + 1))
  let meet : Finset (ℤ × ℤ) := lattice.filter P
  set n : ℕ := meet.card with hn_def
  -- Enumeration of meet by Fin n.
  let e : meet ≃ Fin n := meet.equivFin
  let toLat : Fin n → ℤ × ℤ := fun i => (e.symm i).val
  have htoLat_mem : ∀ i, toLat i ∈ meet := fun i => (e.symm i).property
  have htoLat_P : ∀ i, P (toLat i) := fun i =>
    (Finset.mem_filter.mp (htoLat_mem i)).2
  let corner : Fin n → ℂ := fun i =>
    ⟨((toLat i).1 : ℝ) * s, ((toLat i).2 : ℝ) * s⟩
  refine ⟨n, corner, s, hs_pos, ?_, ?_⟩
  · -- Cover K.
    intro z hz
    set ii : ℤ := ⌊z.re / s⌋ with hii_def
    set jj : ℤ := ⌊z.im / s⌋ with hjj_def
    -- Square (ii, jj) contains z.
    have hii_floor_le : (ii : ℝ) ≤ z.re / s := Int.floor_le _
    have hii_lt_floor : z.re / s < (ii : ℝ) + 1 := Int.lt_floor_add_one _
    have hjj_floor_le : (jj : ℝ) ≤ z.im / s := Int.floor_le _
    have hjj_lt_floor : z.im / s < (jj : ℝ) + 1 := Int.lt_floor_add_one _
    have hii_le_re : (ii : ℝ) * s ≤ z.re := by
      have := (div_le_iff₀ hs_pos).mp hii_floor_le
      linarith
    have hre_le_ii : z.re ≤ (ii : ℝ) * s + s := by
      have h : z.re / s ≤ (ii : ℝ) + 1 := hii_lt_floor.le
      have := (div_le_iff₀ hs_pos).mp h
      linarith
    have hjj_le_im : (jj : ℝ) * s ≤ z.im := by
      have := (div_le_iff₀ hs_pos).mp hjj_floor_le
      linarith
    have him_le_jj : z.im ≤ (jj : ℝ) * s + s := by
      have h : z.im / s ≤ (jj : ℝ) + 1 := hjj_lt_floor.le
      have := (div_le_iff₀ hs_pos).mp h
      linarith
    -- Bounds: ii, jj ∈ [-N, N+1).
    have hzM : ‖z‖ ≤ M := by
      have := hM_sub hz
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    have hzre_abs : |z.re| ≤ M := (Complex.abs_re_le_norm z).trans hzM
    have hzim_abs : |z.im| ≤ M := (Complex.abs_im_le_norm z).trans hzM
    -- Helper: bound floor of u/s when |u| ≤ M.
    have float_bound : ∀ (u : ℝ), |u| ≤ M → -N ≤ ⌊u / s⌋ ∧ ⌊u / s⌋ < N + 1 := by
      intro u hu
      have hu_lb : -M ≤ u := neg_le_of_abs_le hu
      have hu_ub : u ≤ M := le_of_abs_le hu
      have hus_lb : -M / s ≤ u / s := div_le_div_of_nonneg_right hu_lb hs_pos.le
      have hus_ub : u / s ≤ M / s := div_le_div_of_nonneg_right hu_ub hs_pos.le
      -- ⌊u/s⌋ ≤ u/s ≤ M/s < ⌈M/s⌉ + 1 ≤ N + 1 (since N = ⌈M/s⌉ + 1).
      -- Actually we need ⌊u/s⌋ ≤ N, i.e., ⌊u/s⌋ < N + 1.
      refine ⟨?_, ?_⟩
      · -- -N ≤ ⌊u/s⌋. Use ⌊-M/s⌋ ≤ ⌊u/s⌋.
        have h1 : ⌊(-M : ℝ) / s⌋ ≤ ⌊u / s⌋ := Int.floor_le_floor hus_lb
        have h2 : -N ≤ ⌊(-M : ℝ) / s⌋ := by
          -- Need: -N ≤ ⌊-M/s⌋, i.e., ⌊-M/s⌋ ≥ -⌈M/s⌉ - 1 = -N.
          -- We have ⌊-M/s⌋ ≥ -M/s - 1, but ⌊⌋ ∈ ℤ.
          -- Equivalent: ⌊-M/s⌋ + 1 ≥ -M/s > -⌈M/s⌉ - 1 (since ⌈M/s⌉ ≥ M/s).
          -- So ⌊-M/s⌋ ≥ -⌈M/s⌉ - 1 = -N (since both are integers).
          have hceil : (M / s : ℝ) ≤ (⌈M / s⌉ : ℝ) := Int.le_ceil _
          have : -(⌈M / s⌉ : ℝ) ≤ -M / s := by linarith
          -- We want -N ≤ ⌊-M/s⌋ where N = ⌈M/s⌉ + 1.
          -- -N = -⌈M/s⌉ - 1. So need -⌈M/s⌉ - 1 ≤ ⌊-M/s⌋.
          -- Equivalent: -⌈M/s⌉ ≤ ⌊-M/s⌋ + 1.
          -- Since ⌊-M/s⌋ + 1 > -M/s ≥ -⌈M/s⌉, and both are integers, ⌊-M/s⌋ + 1 ≥ -⌈M/s⌉ + 1.
          -- Actually: ⌊x⌋ ≥ x - 1, so ⌊-M/s⌋ ≥ -M/s - 1 ≥ -⌈M/s⌉ - 1 = -N. Cast back.
          have h3 : (⌊(-M : ℝ) / s⌋ : ℝ) ≥ -M / s - 1 := by
            have := Int.sub_one_lt_floor (-M / s)
            linarith
          have h4 : (⌊(-M : ℝ) / s⌋ : ℝ) ≥ -(⌈M / s⌉ : ℝ) - 1 := by linarith
          have h5 : ((-N : ℤ) : ℝ) ≤ (⌊(-M : ℝ) / s⌋ : ℝ) := by
            rw [hN_def]
            push_cast
            linarith
          exact_mod_cast h5
        linarith
      · -- ⌊u/s⌋ < N + 1, i.e., ⌊u/s⌋ ≤ N.
        have h1 : ⌊u / s⌋ ≤ ⌊M / s⌋ := Int.floor_le_floor hus_ub
        have h2 : ⌊M / s⌋ ≤ N := by
          rw [hN_def]
          have : ⌊M / s⌋ ≤ ⌈M / s⌉ := Int.floor_le_ceil _
          omega
        omega
    obtain ⟨hii_lb, hii_ub⟩ := float_bound z.re hzre_abs
    obtain ⟨hjj_lb, hjj_ub⟩ := float_bound z.im hzim_abs
    -- (ii, jj) is in lattice.
    have hij_lat : (ii, jj) ∈ lattice := by
      simp only [lattice, Finset.mem_product, Finset.mem_Ico]
      exact ⟨⟨hii_lb, hii_ub⟩, ⟨hjj_lb, hjj_ub⟩⟩
    -- (ii, jj) is in meet.
    have hij_meet : (ii, jj) ∈ meet := by
      simp only [meet, Finset.mem_filter]
      refine ⟨hij_lat, ?_⟩
      exact ⟨z, hz, hii_le_re, hre_le_ii, hjj_le_im, him_le_jj⟩
    -- Find Fin n index for (ii, jj).
    let p : meet := ⟨(ii, jj), hij_meet⟩
    refine ⟨e p, ?_, ?_⟩
    · -- z.re ∈ Icc (corner (e p)).re ((corner (e p)).re + s)
      show z.re ∈ Set.Icc _ _
      have hcorner_eq : (toLat (e p)) = (ii, jj) := by
        show (e.symm (e p)).val = (ii, jj)
        simp
      simp only [Set.mem_Icc, corner]
      rw [hcorner_eq]
      exact ⟨hii_le_re, hre_le_ii⟩
    · show z.im ∈ Set.Icc _ _
      have hcorner_eq : (toLat (e p)) = (ii, jj) := by
        show (e.symm (e p)).val = (ii, jj)
        simp
      simp only [Set.mem_Icc, corner]
      rw [hcorner_eq]
      exact ⟨hjj_le_im, him_le_jj⟩
  · -- Each square in U.
    intro i w hw_re hw_im
    -- Square at corner i meets K (by filter), witness z₀ ∈ K.
    obtain ⟨z₀, hz₀, hz_re_lb, hz_re_ub, hz_im_lb, hz_im_ub⟩ := htoLat_P i
    -- w is within distance 2s of z₀.
    have hcorner_re : (corner i).re = ((toLat i).1 : ℝ) * s := rfl
    have hcorner_im : (corner i).im = ((toLat i).2 : ℝ) * s := rfl
    simp only [Set.mem_Icc, hcorner_re, hcorner_im] at hw_re hw_im
    -- |w.re - z₀.re| ≤ s, |w.im - z₀.im| ≤ s.
    have habs_re : |w.re - z₀.re| ≤ s := by
      rcases hw_re with ⟨hw1, hw2⟩
      rcases hz_re_lb, hz_re_ub with ⟨hz1, hz2⟩ | _
      · sorry
      · sorry
    sorry
