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
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ := compact_subset_open_has_thickening hK hU hKU
  set s : ℝ := ρ / 3 with hs_def
  have hs_pos : 0 < s := by positivity
  have h2s_lt_ρ : 2 * s < ρ := by rw [hs_def]; linarith
  obtain ⟨M, hM_pos, hM_sub⟩ :=
    hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  let P : ℤ × ℤ → Prop := fun p =>
    ∃ z ∈ K,
      (p.1 : ℝ) * s ≤ z.re ∧ z.re ≤ (p.1 : ℝ) * s + s ∧
      (p.2 : ℝ) * s ≤ z.im ∧ z.im ≤ (p.2 : ℝ) * s + s
  set N : ℤ := ⌈M / s⌉ + 1 with hN_def
  let lattice : Finset (ℤ × ℤ) :=
    (Finset.Ico (-N) (N + 1)) ×ˢ (Finset.Ico (-N) (N + 1))
  let meet : Finset (ℤ × ℤ) := lattice.filter P
  set n : ℕ := meet.card with hn_def
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
    have hii_floor_le : (ii : ℝ) ≤ z.re / s := Int.floor_le _
    have hii_lt_floor : z.re / s < (ii : ℝ) + 1 := Int.lt_floor_add_one _
    have hjj_floor_le : (jj : ℝ) ≤ z.im / s := Int.floor_le _
    have hjj_lt_floor : z.im / s < (jj : ℝ) + 1 := Int.lt_floor_add_one _
    have hii_le_re : (ii : ℝ) * s ≤ z.re := by
      have := (le_div_iff₀ hs_pos).mp hii_floor_le
      linarith
    have hre_le_ii : z.re ≤ (ii : ℝ) * s + s := by
      have h : z.re / s ≤ (ii : ℝ) + 1 := hii_lt_floor.le
      have := (div_le_iff₀ hs_pos).mp h
      linarith
    have hjj_le_im : (jj : ℝ) * s ≤ z.im := by
      have := (le_div_iff₀ hs_pos).mp hjj_floor_le
      linarith
    have him_le_jj : z.im ≤ (jj : ℝ) * s + s := by
      have h : z.im / s ≤ (jj : ℝ) + 1 := hjj_lt_floor.le
      have := (div_le_iff₀ hs_pos).mp h
      linarith
    have hzM : ‖z‖ ≤ M := by
      have := hM_sub hz
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    have hzre_abs : |z.re| ≤ M := (Complex.abs_re_le_norm z).trans hzM
    have hzim_abs : |z.im| ≤ M := (Complex.abs_im_le_norm z).trans hzM
    have float_bound : ∀ (u : ℝ), |u| ≤ M → -N ≤ ⌊u / s⌋ ∧ ⌊u / s⌋ < N + 1 := by
      intro u hu
      have hu_lb : -M ≤ u := neg_le_of_abs_le hu
      have hu_ub : u ≤ M := le_of_abs_le hu
      have hus_lb : -M / s ≤ u / s := div_le_div_of_nonneg_right hu_lb hs_pos.le
      have hus_ub : u / s ≤ M / s := div_le_div_of_nonneg_right hu_ub hs_pos.le
      refine ⟨?_, ?_⟩
      · have h1 : ⌊(-M : ℝ) / s⌋ ≤ ⌊u / s⌋ := Int.floor_le_floor hus_lb
        have h3 : (⌊(-M : ℝ) / s⌋ : ℝ) > -M / s - 1 := Int.sub_one_lt_floor (-M / s)
        have hceil : (M / s : ℝ) ≤ (⌈M / s⌉ : ℝ) := Int.le_ceil _
        have h5 : ((-N : ℤ) : ℝ) ≤ (⌊(-M : ℝ) / s⌋ : ℝ) := by
          rw [hN_def]; push_cast; linarith
        have h6 : -N ≤ ⌊(-M : ℝ) / s⌋ := by exact_mod_cast h5
        linarith
      · have h1 : ⌊u / s⌋ ≤ ⌊M / s⌋ := Int.floor_le_floor hus_ub
        have h2 : ⌊M / s⌋ ≤ N := by
          rw [hN_def]
          have : ⌊M / s⌋ ≤ ⌈M / s⌉ := Int.floor_le_ceil _
          omega
        omega
    obtain ⟨hii_lb, hii_ub⟩ := float_bound z.re hzre_abs
    obtain ⟨hjj_lb, hjj_ub⟩ := float_bound z.im hzim_abs
    have hij_lat : (ii, jj) ∈ lattice := by
      simp only [lattice, Finset.mem_product, Finset.mem_Ico]
      exact ⟨⟨hii_lb, hii_ub⟩, ⟨hjj_lb, hjj_ub⟩⟩
    have hij_meet : (ii, jj) ∈ meet := by
      simp only [meet, Finset.mem_filter]
      refine ⟨hij_lat, ?_⟩
      exact ⟨z, hz, hii_le_re, hre_le_ii, hjj_le_im, him_le_jj⟩
    let p : meet := ⟨(ii, jj), hij_meet⟩
    refine ⟨e p, ?_, ?_⟩
    · show z.re ∈ Set.Icc _ _
      have hcorner_eq : toLat (e p) = (ii, jj) := by
        show (e.symm (e p)).val = (ii, jj)
        simp [p]
      simp only [Set.mem_Icc, corner]
      rw [hcorner_eq]
      exact ⟨hii_le_re, hre_le_ii⟩
    · show z.im ∈ Set.Icc _ _
      have hcorner_eq : toLat (e p) = (ii, jj) := by
        show (e.symm (e p)).val = (ii, jj)
        simp [p]
      simp only [Set.mem_Icc, corner]
      rw [hcorner_eq]
      exact ⟨hjj_le_im, him_le_jj⟩
  · -- Each square in U.
    intro i w hw_re hw_im
    obtain ⟨z₀, hz₀_K, hzre_lb, hzre_ub, hzim_lb, hzim_ub⟩ := htoLat_P i
    have hcorner_re : (corner i).re = ((toLat i).1 : ℝ) * s := rfl
    have hcorner_im : (corner i).im = ((toLat i).2 : ℝ) * s := rfl
    rw [Set.mem_Icc, hcorner_re] at hw_re
    rw [Set.mem_Icc, hcorner_im] at hw_im
    -- |w.re - z₀.re| ≤ s
    have habs_re : |w.re - z₀.re| ≤ s := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · linarith [hw_re.1, hzre_ub]
      · linarith [hw_re.2, hzre_lb]
    have habs_im : |w.im - z₀.im| ≤ s := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · linarith [hw_im.1, hzim_ub]
      · linarith [hw_im.2, hzim_lb]
    -- dist w z₀ ≤ |w.re - z₀.re| + |w.im - z₀.im| ≤ 2s < ρ.
    have hdist : dist w z₀ < ρ := by
      have h1 : dist w z₀ = ‖w - z₀‖ := Complex.dist_eq w z₀
      have h2 : ‖w - z₀‖ ≤ |(w - z₀).re| + |(w - z₀).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      have h3 : (w - z₀).re = w.re - z₀.re := by simp
      have h4 : (w - z₀).im = w.im - z₀.im := by simp
      rw [h3, h4] at h2
      calc dist w z₀ = ‖w - z₀‖ := h1
        _ ≤ |w.re - z₀.re| + |w.im - z₀.im| := h2
        _ ≤ s + s := by linarith
        _ = 2 * s := by ring
        _ < ρ := h2s_lt_ρ
    -- w is in the thickening, hence in U.
    have hw_thick : w ∈ Metric.thickening ρ K := by
      rw [Metric.mem_thickening_iff]
      exact ⟨z₀, hz₀_K, hdist⟩
    exact hρ_sub hw_thick
