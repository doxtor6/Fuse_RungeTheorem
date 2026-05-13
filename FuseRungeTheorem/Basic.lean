import Mathlib

open scoped Topology

/--
Compact subset of an open set has a positive collar.

If `K` is compact, `U` is open, and `K ⊆ U`, then there exists `ρ > 0` such that
the open `ρ`-thickening of `K` is contained in `U`.
-/
lemma compact_subset_open_has_thickening {K U : Set ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ρ > 0, Metric.thickening ρ K ⊆ U :=
  hK.exists_thickening_subset_open hU hKU

section CauchyIntegralApproximation

/-- Contour integral along the oriented line segment from `a` to `b`,
parametrised linearly by `t ∈ [0, 1]`. -/
private noncomputable def segmentIntegral (a b : ℂ) (g : ℂ → ℂ) : ℂ :=
  ∫ t in (0:ℝ)..1, g (a + (t : ℂ) * (b - a)) * (b - a)

/--
Grid-contour Cauchy representation (sub-lemma 1).

For `K` compact in open `U` with `f` holomorphic on `U`, there is a finite
oriented piecewise-linear contour `Γ ⊆ U \ K` (encoded as a `Fin m`-indexed
family of oriented line segments with starts `A` and ends `B`) such that
Cauchy's integral formula holds for every `z ∈ K`:
`f(z) = (1 / (2πi)) · ∑ᵢ ∫_{Aᵢ → Bᵢ} f(ζ) / (ζ - z) dζ`.

The contour is the algebraic (oriented) boundary of a finite cover of `K`
by closed axis-parallel grid squares whose closures lie in `U`, with
interior edges cancelling.
-/
private lemma cauchy_grid_representation
    {K U : Set ℂ} {f : ℂ → ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : DifferentiableOn ℂ f U) :
    ∃ (m : ℕ) (A B : Fin m → ℂ),
      (∀ i, ∀ t ∈ Set.Icc (0:ℝ) 1, A i + (t : ℂ) * (B i - A i) ∈ U \ K) ∧
      ∀ z ∈ K,
        f z = (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
          ∑ i, segmentIntegral (A i) (B i) (fun ζ => f ζ / (ζ - z)) := by
  sorry

/--
Uniform parametric Riemann-sum approximation of a segment integral (sub-lemma 2).

For an oriented segment whose image is disjoint from a compact set `K` and a
function `g` continuous on that image, the parametric contour-integral functional
`z ↦ (1/(2πi)) · ∫_{a → b} g(ζ)/(ζ - z) dζ` is uniformly approximated on `K` by
finite pole-sums `∑ⱼ cⱼ/(z - aⱼ)` whose poles `aⱼ` lie on the segment image.
-/
private lemma segment_pole_sum_uniform_approx
    {K : Set ℂ} (hK : IsCompact K) {a b : ℂ}
    (h_seg_off_K : ∀ t ∈ Set.Icc (0:ℝ) 1, a + (t : ℂ) * (b - a) ∉ K)
    {g : ℂ → ℂ}
    (h_g_cont : ContinuousOn g
      ((fun t : ℝ => a + (t : ℂ) * (b - a)) '' Set.Icc (0:ℝ) 1)) :
    ∀ ε > 0, ∃ (N : ℕ) (sample : Fin N → ℂ) (coeff : Fin N → ℂ),
      (∀ j, sample j ∉ K) ∧
      ∀ z ∈ K,
        ‖(∑ j, coeff j / (z - sample j))
          - (1 / (2 * (Real.pi : ℂ) * Complex.I))
            * segmentIntegral a b (fun ζ => g ζ / (ζ - z))‖ < ε := by
  sorry

end CauchyIntegralApproximation

/--
Cauchy integral approximation by finite pole sums.

For `f` holomorphic on an open `U` containing a compact `K`, we can uniformly
approximate `f` on `K` by a finite sum of simple poles whose pole locations lie
outside `K`.

Glue proof: obtain a finite oriented contour `Γ` from `cauchy_grid_representation`
on which Cauchy's integral formula holds; per segment, apply
`segment_pole_sum_uniform_approx` with budget `ε / (m + 1)`; flatten the
(segment-index × sample-index) pairs into a single `Fin N` indexing; combine
the per-segment estimates via the triangle inequality.
-/
lemma cauchy_integral_approximated_by_pole_sum
    {K U : Set ℂ} {f : ℂ → ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : DifferentiableOn ℂ f U) :
    ∀ ε > 0, ∃ (N : ℕ) (a : Fin N → ℂ) (c : Fin N → ℂ),
      (∀ j, a j ∉ K) ∧
      ∀ z ∈ K, ‖(∑ j, c j / (z - a j)) - f z‖ < ε := by
  intro ε hε
  obtain ⟨m, A, B, hΓ, hCauchy⟩ :=
    cauchy_grid_representation hK hU hKU hf
  have hf_cont : ContinuousOn f U := hf.continuousOn
  have h_seg_off_K : ∀ i : Fin m, ∀ t ∈ Set.Icc (0:ℝ) 1,
      A i + (t : ℂ) * (B i - A i) ∉ K :=
    fun i t ht => (hΓ i t ht).2
  have h_seg_in_U : ∀ i : Fin m, ∀ t ∈ Set.Icc (0:ℝ) 1,
      A i + (t : ℂ) * (B i - A i) ∈ U :=
    fun i t ht => (hΓ i t ht).1
  have h_f_cont_seg : ∀ i : Fin m, ContinuousOn f
      ((fun t : ℝ => A i + (t : ℂ) * (B i - A i)) '' Set.Icc (0:ℝ) 1) := by
    intro i
    refine hf_cont.mono ?_
    rintro w ⟨t, ht, rfl⟩
    exact h_seg_in_U i t ht
  set δ : ℝ := ε / (m + 1) with hδ_def
  have hδ_pos : 0 < δ := by
    refine div_pos hε ?_
    positivity
  choose N sample coeff hsample_off_K happrox using
    fun i : Fin m =>
      segment_pole_sum_uniform_approx hK (h_seg_off_K i) (h_f_cont_seg i) δ hδ_pos
  classical
  set pairType : Type := Σ i : Fin m, Fin (N i) with hpairType_def
  set totalN : ℕ := Fintype.card pairType with htotalN_def
  set φ : Fin totalN ≃ pairType := (Fintype.equivFin pairType).symm with hφ_def
  refine ⟨totalN,
          fun k => sample (φ k).1 (φ k).2,
          fun k => coeff (φ k).1 (φ k).2,
          ?_, ?_⟩
  · intro k
    exact hsample_off_K (φ k).1 (φ k).2
  · intro z hz
    set c0 : ℂ := 1 / (2 * (Real.pi : ℂ) * Complex.I) with hc0_def
    have h_reindex :
        ∑ k : Fin totalN, coeff (φ k).1 (φ k).2 / (z - sample (φ k).1 (φ k).2)
          = ∑ p : pairType, coeff p.1 p.2 / (z - sample p.1 p.2) := by
      apply Finset.sum_equiv φ
      · intro k; simp
      · intro k _; rfl
    rw [h_reindex]
    rw [show (∑ p : pairType, coeff p.1 p.2 / (z - sample p.1 p.2))
          = ∑ i : Fin m, ∑ j : Fin (N i), coeff i j / (z - sample i j) from
        Finset.sum_sigma (Finset.univ : Finset (Fin m))
          (fun i => (Finset.univ : Finset (Fin (N i))))
          (fun p => coeff p.1 p.2 / (z - sample p.1 p.2))]
    rw [hCauchy z hz, Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc ‖∑ i : Fin m,
            ((∑ j : Fin (N i), coeff i j / (z - sample i j)) -
              c0 * segmentIntegral (A i) (B i) (fun ζ => f ζ / (ζ - z)))‖
        ≤ ∑ i : Fin m,
            ‖(∑ j : Fin (N i), coeff i j / (z - sample i j)) -
              c0 * segmentIntegral (A i) (B i) (fun ζ => f ζ / (ζ - z))‖ := by
          exact norm_sum_le _ _
      _ ≤ ∑ _i : Fin m, δ := by
          refine Finset.sum_le_sum ?_
          intro i _
          exact (happrox i z hz).le
      _ = (m : ℝ) * δ := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul]
      _ < ε := by
          rw [hδ_def]
          have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
          rw [mul_div_assoc', div_lt_iff₀ hm1_pos]
          nlinarith [hε, Nat.cast_nonneg m]

/--
Rational approximation with poles off `K`.

A direct corollary of `cauchy_integral_approximated_by_pole_sum`.
-/
theorem rational_approximation_with_poles_off
    {K U : Set ℂ} {f : ℂ → ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : DifferentiableOn ℂ f U) :
    ∀ ε > 0, ∃ (N : ℕ) (a : Fin N → ℂ) (c : Fin N → ℂ),
      (∀ j, a j ∉ K) ∧
      ∀ z ∈ K, ‖(∑ j, c j / (z - a j)) - f z‖ < ε :=
  cauchy_integral_approximated_by_pole_sum hK hU hKU hf

/--
The complement of a compact subset of `ℂ` is unbounded: for every radius `R`
there exists a point `b ∉ K` with `‖b‖ > R`.
-/
lemma compact_complement_unbounded {K : Set ℂ} (hK : IsCompact K) :
    ∀ R : ℝ, ∃ b : ℂ, b ∉ K ∧ R < ‖b‖ := by
  obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  intro R
  set x : ℝ := max (max R M) 0 + 1 with hx_def
  have hx_nonneg : 0 ≤ x := by
    have : 0 ≤ max (max R M) 0 := le_max_right _ _
    linarith
  have hxR : R < x := by
    have h1 : R ≤ max R M := le_max_left R M
    have h2 : max R M ≤ max (max R M) 0 := le_max_left _ _
    linarith
  have hxM : M < x := by
    have h1 : M ≤ max R M := le_max_right R M
    have h2 : max R M ≤ max (max R M) 0 := le_max_left _ _
    linarith
  refine ⟨((x : ℝ) : ℂ), ?_, ?_⟩
  · intro hmem
    have h := hM hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h
    rw [Complex.norm_of_nonneg hx_nonneg] at h
    linarith
  · rw [Complex.norm_of_nonneg hx_nonneg]
    exact hxR

/--
Connected open subsets of `ℂ` are path-connected.
-/
lemma isConnected_isOpen_pathConnected_complex {V : Set ℂ}
    (hV : IsOpen V) (hC : IsConnected V) : IsPathConnected V :=
  hV.isConnected_iff_isPathConnected.mp hC

/--
Path to infinity in the connected complement.

If `K` is compact with connected complement and `a ∉ K`, then for every `R > 0`
there is `b ∉ K` with `R < ‖b‖` and a path from `a` to `b` lying entirely in
`Kᶜ`.
-/
lemma path_to_infinity_in_connected_complement
    {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected (Kᶜ : Set ℂ))
    {a : ℂ} (ha : a ∉ K) :
    ∀ R : ℝ, ∃ (b : ℂ) (hb : b ∉ K) (γ : Path (⟨a, ha⟩ : (Kᶜ : Set ℂ)) ⟨b, hb⟩),
      R < ‖b‖ := by
  sorry

/--
Local pole-moving lemma.

If `a, b ∉ K` satisfy `|a - b| < dist(b, K)`, then for every `ε > 0` there is
`N : ℕ` such that the geometric partial sum
`∑_{n=0}^{N} (a-b)^n / (z-b)^(n+1)` approximates `1/(z-a)` uniformly on `K`
within `ε`.
-/
lemma local_pole_moving
    {K : Set ℂ} (hK : IsCompact K)
    {a b : ℂ} (_ha : a ∉ K) (hb : b ∉ K)
    (hab : ‖a - b‖ < Metric.infDist b K) :
    ∀ ε > 0, ∃ N : ℕ,
      ∀ z ∈ K,
        ‖1 / (z - a) - ∑ n ∈ Finset.range (N + 1), (a - b) ^ n / (z - b) ^ (n + 1)‖ < ε := by
  intro ε hε
  by_cases hKemp : K = ∅
  · refine ⟨0, ?_⟩
    intro z hz
    rw [hKemp] at hz
    exact absurd hz (Set.notMem_empty z)
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKemp
  set d : ℝ := Metric.infDist b K with hd_def
  set r : ℝ := ‖a - b‖ with hr_def
  have hd_pos : 0 < d := by
    have hKclosed : IsClosed K := hK.isClosed
    exact (hKclosed.notMem_iff_infDist_pos hKne).mp hb
  have hr_nonneg : 0 ≤ r := norm_nonneg _
  have hr_lt_d : r < d := hab
  have hd_minus_r_pos : 0 < d - r := sub_pos.mpr hr_lt_d
  have hzb_ge : ∀ z ∈ K, d ≤ ‖z - b‖ := by
    intro z hz
    have h := Metric.infDist_le_dist_of_mem hz (x := b)
    have heq : dist b z = ‖z - b‖ := by
      rw [Complex.dist_eq, ← norm_neg]
      congr 1
      ring
    rw [heq] at h
    exact h
  have hza_ge : ∀ z ∈ K, d - r ≤ ‖z - a‖ := by
    intro z hz
    have h1 : d ≤ ‖z - b‖ := hzb_ge z hz
    have h2 : ‖z - b‖ ≤ ‖z - a‖ + ‖a - b‖ := by
      have := norm_add_le (z - a) (a - b)
      have heq : (z - a) + (a - b) = z - b := by ring
      rw [heq] at this
      exact this
    linarith
  have hzb_ne : ∀ z ∈ K, z - b ≠ 0 := by
    intro z hz hzbeq
    have : ‖z - b‖ = 0 := by rw [hzbeq]; simp
    have h1 := hzb_ge z hz
    linarith
  have hza_ne : ∀ z ∈ K, z - a ≠ 0 := by
    intro z hz hzaeq
    have : ‖z - a‖ = 0 := by rw [hzaeq]; simp
    have h1 := hza_ge z hz
    linarith
  set q : ℝ := r / d with hq_def
  have hq_nonneg : 0 ≤ q := div_nonneg hr_nonneg hd_pos.le
  have hq_lt_one : q < 1 := by
    rw [hq_def, div_lt_one hd_pos]
    exact hr_lt_d
  have htends : Filter.Tendsto (fun n : ℕ => q ^ (n + 1) / (d - r))
      Filter.atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = 0 / (d - r) := by simp
    rw [h0]
    apply Filter.Tendsto.div_const
    have hbase := tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one
    exact hbase.comp (Filter.tendsto_add_atTop_nat 1)
  have hev : ∀ᶠ n in Filter.atTop, q ^ (n + 1) / (d - r) < ε :=
    htends.eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N, ?_⟩
  intro z hz
  have hzb : z - b ≠ 0 := hzb_ne z hz
  have hza : z - a ≠ 0 := hza_ne z hz
  have h_zb_norm : d ≤ ‖z - b‖ := hzb_ge z hz
  have h_zb_pos : 0 < ‖z - b‖ := lt_of_lt_of_le hd_pos h_zb_norm
  have h_za_norm : d - r ≤ ‖z - a‖ := hza_ge z hz
  have h_za_pos : 0 < ‖z - a‖ := lt_of_lt_of_le hd_minus_r_pos h_za_norm
  set u : ℂ := a - b with hu_def
  set w : ℂ := z - b with hw_def
  have hwu_eq : w - u = z - a := by rw [hw_def, hu_def]; ring
  have hw_ne : w ≠ 0 := by rw [hw_def]; exact hzb
  have hwu_ne : w - u ≠ 0 := by rw [hwu_eq]; exact hza
  have h_sum_eq : ∑ n ∈ Finset.range (N + 1), u ^ n / w ^ (n + 1)
      = (1 / w) * ∑ n ∈ Finset.range (N + 1), (u / w) ^ n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [div_pow]
    field_simp
    ring
  have h_ratio_ne_one : u / w ≠ 1 := by
    intro h
    have : u = w := by field_simp at h; exact h
    have hwu0 : w - u = 0 := by rw [this]; ring
    exact hwu_ne hwu0
  have h_geom : ∑ n ∈ Finset.range (N + 1), (u / w) ^ n
      = ((u / w) ^ (N + 1) - 1) / (u / w - 1) := geom_sum_eq h_ratio_ne_one (N + 1)
  have h_main :
      1 / (z - a) - ∑ n ∈ Finset.range (N + 1), u ^ n / w ^ (n + 1)
        = u ^ (N + 1) / (w ^ (N + 1) * (z - a)) := by
    rw [← hwu_eq]
    rw [h_sum_eq, h_geom]
    have hw_pow_ne : w ^ (N + 1) ≠ 0 := pow_ne_zero _ hw_ne
    have h_uw1 : u / w - 1 = (u - w) / w := by
      field_simp
    rw [h_uw1]
    have h_ratio_pow : (u / w) ^ (N + 1) = u ^ (N + 1) / w ^ (N + 1) := div_pow u w (N + 1)
    rw [h_ratio_pow]
    have huw_ne : u - w ≠ 0 := by
      intro h
      apply hwu_ne
      have : w - u = -(u - w) := by ring
      rw [this, h, neg_zero]
    field_simp
    ring
  rw [hu_def, hw_def] at h_main
  rw [h_main]
  rw [norm_div, norm_mul, norm_pow, norm_pow]
  have h_zb_pow_pos : 0 < ‖z - b‖ ^ (N + 1) := pow_pos h_zb_pos _
  have h_zb_pow_ge : d ^ (N + 1) ≤ ‖z - b‖ ^ (N + 1) :=
    pow_le_pow_left₀ hd_pos.le h_zb_norm _
  have h_d_pow_pos : 0 < d ^ (N + 1) := pow_pos hd_pos _
  have h_d_denom_pos : 0 < d ^ (N + 1) * (d - r) := mul_pos h_d_pow_pos hd_minus_r_pos
  have h_num : ‖a - b‖ ^ (N + 1) = r ^ (N + 1) := by rw [hr_def]
  rw [h_num]
  have h_step1 : r ^ (N + 1) / (‖z - b‖ ^ (N + 1) * ‖z - a‖) ≤
      r ^ (N + 1) / (d ^ (N + 1) * (d - r)) := by
    apply div_le_div_of_nonneg_left
    · exact pow_nonneg hr_nonneg _
    · exact h_d_denom_pos
    · exact mul_le_mul h_zb_pow_ge h_za_norm hd_minus_r_pos.le h_zb_pow_pos.le
  have h_step2 : r ^ (N + 1) / (d ^ (N + 1) * (d - r)) = q ^ (N + 1) / (d - r) := by
    rw [hq_def, div_pow]
    field_simp
  rw [h_step2] at h_step1
  have h_q : q ^ (N + 1) / (d - r) < ε := hN N (le_refl N)
  linarith

/--
Pole sufficiently far away is polynomially approximable.

If `b ∈ ℂ` strictly dominates every `z ∈ K` in norm, then `1/(z-b)` can be
uniformly approximated on `K` by polynomials.
-/
lemma far_pole_polynomial_approx
    {K : Set ℂ} (hK : IsCompact K)
    {b : ℂ} (hb : ∀ z ∈ K, ‖z‖ < ‖b‖) :
    ∀ ε > 0, ∃ p : Polynomial ℂ,
      ∀ z ∈ K, ‖p.eval z - 1 / (z - b)‖ < ε := by
  intro ε hε
  by_cases hKne : K.Nonempty
  · have hcont : ContinuousOn (fun z : ℂ => ‖z‖) K := continuous_norm.continuousOn
    obtain ⟨z₀, hz₀K, hz₀max⟩ := hK.exists_isMaxOn hKne hcont
    set M : ℝ := ‖z₀‖ with hM_def
    have hM_bound : ∀ z ∈ K, ‖z‖ ≤ M := fun z hz => hz₀max hz
    have hMb : M < ‖b‖ := hb z₀ hz₀K
    have hM_nonneg : 0 ≤ M := norm_nonneg _
    have hb_ne : b ≠ 0 := by
      intro hb0
      have hbz : ‖b‖ = 0 := by rw [hb0]; simp
      linarith [hM_nonneg]
    have hb_pos : 0 < ‖b‖ := norm_pos_iff.mpr hb_ne
    set q : ℝ := M / ‖b‖ with hq_def
    have hq_nonneg : 0 ≤ q := div_nonneg hM_nonneg hb_pos.le
    have hq_lt_one : q < 1 := by
      rw [hq_def, div_lt_one hb_pos]; exact hMb
    have hgap_pos : 0 < ‖b‖ - M := by linarith
    have htends : Filter.Tendsto (fun n : ℕ => q ^ n / (‖b‖ - M)) Filter.atTop (𝓝 0) := by
      have h₁ : Filter.Tendsto (fun n : ℕ => q ^ n) Filter.atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one
      have h₂ := h₁.div_const (‖b‖ - M)
      simpa using h₂
    have hev : ∀ᶠ n in Filter.atTop, q ^ n / (‖b‖ - M) < ε := by
      rw [Metric.tendsto_atTop] at htends
      obtain ⟨N, hN⟩ := htends ε hε
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hd := hN n hn
      simp only [Real.dist_eq, sub_zero] at hd
      have hpos : 0 ≤ q ^ n / (‖b‖ - M) :=
        div_nonneg (pow_nonneg hq_nonneg _) hgap_pos.le
      rwa [abs_of_nonneg hpos] at hd
    obtain ⟨N, hN⟩ := hev.exists
    refine ⟨∑ n ∈ Finset.range N,
      Polynomial.C (-(b ^ (n + 1))⁻¹) * Polynomial.X ^ n, ?_⟩
    intro z hzK
    have hzbound : ‖z‖ ≤ M := hM_bound z hzK
    have heval :
        (∑ n ∈ Finset.range N,
            Polynomial.C (-(b ^ (n + 1))⁻¹) * Polynomial.X ^ n).eval z =
          -∑ n ∈ Finset.range N, z ^ n / b ^ (n + 1) := by
      rw [Polynomial.eval_finset_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n _
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_X]
      rw [div_eq_mul_inv]
      ring
    rw [heval]
    have hzlt : ‖z‖ < ‖b‖ := hb z hzK
    have hzne : z - b ≠ 0 := by
      intro h
      have hzeq : z = b := sub_eq_zero.mp h
      rw [hzeq] at hzlt; exact lt_irrefl _ hzlt
    have hb_pow_ne : ∀ n, (b ^ n : ℂ) ≠ 0 := fun n => pow_ne_zero n hb_ne
    have hbN_ne : (b ^ N : ℂ) ≠ 0 := hb_pow_ne N
    have hkey :
        (-∑ n ∈ Finset.range N, z ^ n / b ^ (n + 1)) - 1 / (z - b) =
          -(z ^ N / (b ^ N * (z - b))) := by
      have hzbne : z / b ≠ 1 := by
        intro h
        have hzeq : z = b := by
          have := (div_eq_one_iff_eq hb_ne).mp h
          exact this
        rw [hzeq] at hzlt; exact lt_irrefl _ hzlt
      have hgeom : ∑ n ∈ Finset.range N, (z / b) ^ n = ((z / b) ^ N - 1) / (z / b - 1) :=
        geom_sum_eq hzbne N
      have hrew : ∀ n, z ^ n / b ^ (n + 1) = (z / b) ^ n / b := by
        intro n
        rw [pow_succ, div_pow]
        field_simp
      have hsum_eq :
          ∑ n ∈ Finset.range N, z ^ n / b ^ (n + 1) =
            ((z / b) ^ N - 1) / (z - b) := by
        have : ∑ n ∈ Finset.range N, z ^ n / b ^ (n + 1) =
            (∑ n ∈ Finset.range N, (z / b) ^ n) / b := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro n _; exact hrew n
        rw [this, hgeom]
        have hzb_ne : z / b - 1 ≠ 0 := sub_ne_zero.mpr hzbne
        rw [div_div]
        congr 1
        field_simp
      rw [hsum_eq]
      have hzbpow : (z / b) ^ N = z ^ N / b ^ N := div_pow z b N
      rw [hzbpow]
      field_simp
      ring
    rw [hkey]
    rw [norm_neg]
    rw [norm_div, norm_mul, norm_pow, norm_pow]
    have hzb_norm : ‖b‖ - M ≤ ‖z - b‖ := by
      have h1 : ‖b‖ - ‖z‖ ≤ ‖z - b‖ := by
        rw [norm_sub_rev]
        exact norm_sub_norm_le b z
      linarith [hM_bound z hzK]
    have hzb_norm_pos : 0 < ‖z - b‖ := lt_of_lt_of_le hgap_pos hzb_norm
    have hbN_norm_pos : 0 < ‖b‖ ^ N := pow_pos hb_pos N
    have hineq : ‖z‖ ^ N / (‖b‖ ^ N * ‖z - b‖) ≤ q ^ N / (‖b‖ - M) := by
      have hq_pow_eq : q ^ N = M ^ N / ‖b‖ ^ N := by
        rw [hq_def, div_pow]
      rw [hq_pow_eq]
      have rhs_eq : M ^ N / ‖b‖ ^ N / (‖b‖ - M) =
          M ^ N / (‖b‖ ^ N * (‖b‖ - M)) := by
        rw [div_div]
      rw [rhs_eq]
      have hzN_le : ‖z‖ ^ N ≤ M ^ N := pow_le_pow_left₀ (norm_nonneg z) hzbound N
      have hdenom_le : ‖b‖ ^ N * (‖b‖ - M) ≤ ‖b‖ ^ N * ‖z - b‖ :=
        mul_le_mul_of_nonneg_left hzb_norm hbN_norm_pos.le
      have hdenom_pos : 0 < ‖b‖ ^ N * (‖b‖ - M) := mul_pos hbN_norm_pos hgap_pos
      have hLHS_le_mid : ‖z‖ ^ N / (‖b‖ ^ N * ‖z - b‖) ≤
          ‖z‖ ^ N / (‖b‖ ^ N * (‖b‖ - M)) :=
        div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg z) N) hdenom_pos hdenom_le
      have hmid_le_RHS : ‖z‖ ^ N / (‖b‖ ^ N * (‖b‖ - M)) ≤
          M ^ N / (‖b‖ ^ N * (‖b‖ - M)) :=
        div_le_div_of_nonneg_right hzN_le hdenom_pos.le
      exact hLHS_le_mid.trans hmid_le_RHS
    calc ‖z‖ ^ N / (‖b‖ ^ N * ‖z - b‖)
        ≤ q ^ N / (‖b‖ - M) := hineq
      _ < ε := hN
  · refine ⟨0, ?_⟩
    intro z hz
    exact absurd ⟨z, hz⟩ hKne

section SinglePolePolynomial

/--
Step lemma: moving a polynomial in `1/(z-a)` to a polynomial in `1/(z-b)`.

If `a, b ∉ K` and `‖a-b‖ < infDist b K`, then for any polynomial `P` and `ε > 0`,
there exists a polynomial `Q` such that for all `z ∈ K`,
`‖P.eval (1/(z-a)) - Q.eval (1/(z-b))‖ < ε`.
-/
private lemma pole_move_polynomial_step
    {K : Set ℂ} (hK : IsCompact K)
    {a b : ℂ} (ha : a ∉ K) (hb : b ∉ K)
    (hab : ‖a - b‖ < Metric.infDist b K) (P : Polynomial ℂ) :
    ∀ ε > 0, ∃ Q : Polynomial ℂ,
      ∀ z ∈ K, ‖P.eval (1 / (z - a)) - Q.eval (1 / (z - b))‖ < ε := by
  intro ε hε
  by_cases hKemp : K = ∅
  · refine ⟨0, ?_⟩
    intro z hz; rw [hKemp] at hz; exact absurd hz (Set.notMem_empty z)
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKemp
  set d : ℝ := Metric.infDist b K with hd_def
  set r : ℝ := ‖a - b‖ with hr_def
  have hKclosed : IsClosed K := hK.isClosed
  have hd_pos : 0 < d := (hKclosed.notMem_iff_infDist_pos hKne).mp hb
  have hr_nonneg : 0 ≤ r := norm_nonneg _
  have hr_lt_d : r < d := hab
  have hd_minus_r_pos : 0 < d - r := sub_pos.mpr hr_lt_d
  have hzb_ge : ∀ z ∈ K, d ≤ ‖z - b‖ := by
    intro z hz
    have h := Metric.infDist_le_dist_of_mem hz (x := b)
    have heq : dist b z = ‖z - b‖ := by
      rw [Complex.dist_eq, ← norm_neg]; congr 1; ring
    rw [heq] at h; exact h
  have hza_ge : ∀ z ∈ K, d - r ≤ ‖z - a‖ := by
    intro z hz
    have h1 : d ≤ ‖z - b‖ := hzb_ge z hz
    have h2 : ‖z - b‖ ≤ ‖z - a‖ + ‖a - b‖ := by
      have := norm_add_le (z - a) (a - b)
      have heq : (z - a) + (a - b) = z - b := by ring
      rw [heq] at this; exact this
    linarith
  have hzb_ne : ∀ z ∈ K, z - b ≠ 0 := by
    intro z hz hzbeq
    have : ‖z - b‖ = 0 := by rw [hzbeq]; simp
    have h1 := hzb_ge z hz; linarith
  have hza_ne : ∀ z ∈ K, z - a ≠ 0 := by
    intro z hz hzaeq
    have : ‖z - a‖ = 0 := by rw [hzaeq]; simp
    have h1 := hza_ge z hz; linarith
  set M : ℝ := 1 / (d - r) + 1 with hM_def
  have hM_pos : 0 < M := by
    have h1 : 0 < 1 / (d - r) := by positivity
    linarith
  have hM_nonneg : 0 ≤ M := hM_pos.le
  have hPcont : ContinuousOn (fun w : ℂ => P.eval w) (Metric.closedBall (0 : ℂ) M) :=
    P.continuous.continuousOn
  have hPcomp : IsCompact (Metric.closedBall (0 : ℂ) M) := isCompact_closedBall _ _
  have hPucon : UniformContinuousOn (fun w : ℂ => P.eval w) (Metric.closedBall (0 : ℂ) M) :=
    hPcomp.uniformContinuousOn_of_continuous hPcont
  rw [Metric.uniformContinuousOn_iff] at hPucon
  obtain ⟨η, hη_pos, hη⟩ := hPucon ε hε
  set η' : ℝ := min η 1 with hη'_def
  have hη'_pos : 0 < η' := lt_min hη_pos one_pos
  have hη'_le_η : η' ≤ η := min_le_left _ _
  have hη'_le_one : η' ≤ 1 := min_le_right _ _
  obtain ⟨N, hN⟩ := local_pole_moving hK ha hb hab η' hη'_pos
  set R : Polynomial ℂ := ∑ n ∈ Finset.range (N + 1),
    Polynomial.C ((a - b) ^ n) * Polynomial.X ^ (n + 1) with hR_def
  have hR_eval : ∀ z : ℂ, z ≠ b → R.eval (1 / (z - b)) =
      ∑ n ∈ Finset.range (N + 1), (a - b) ^ n / (z - b) ^ (n + 1) := by
    intro z hzne
    have hzbne : z - b ≠ 0 := sub_ne_zero.mpr hzne
    rw [hR_def, Polynomial.eval_finset_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [one_div, inv_pow, pow_succ]
    field_simp
  refine ⟨P.comp R, ?_⟩
  intro z hz
  have hzbne : z ≠ b := by
    intro hzeq
    have : z - b = 0 := by rw [hzeq]; ring
    exact (hzb_ne z hz) this
  have hane : z - a ≠ 0 := hza_ne z hz
  have hpartial := hN z hz
  have hinvza_norm : ‖(1 / (z - a) : ℂ)‖ ≤ 1 / (d - r) := by
    rw [norm_div, norm_one]
    have h_za := hza_ge z hz
    have h_za_pos : 0 < ‖z - a‖ := lt_of_lt_of_le hd_minus_r_pos h_za
    rw [div_le_div_iff₀ h_za_pos hd_minus_r_pos, one_mul, one_mul]
    exact h_za
  have hinvza_lt_M : ‖(1 / (z - a) : ℂ)‖ < M := by
    have : 1 / (d - r) < M := by rw [hM_def]; linarith
    linarith [hinvza_norm]
  have hinvza_mem : (1 / (z - a) : ℂ) ∈ Metric.closedBall (0 : ℂ) M := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hinvza_norm.trans (by rw [hM_def]; linarith)
  set S : ℂ := ∑ n ∈ Finset.range (N + 1), (a - b) ^ n / (z - b) ^ (n + 1) with hS_def
  have hS_close : ‖1 / (z - a) - S‖ < η' := hpartial
  have hS_norm : ‖S‖ ≤ M := by
    have h1 : ‖S‖ ≤ ‖1 / (z - a)‖ + ‖S - 1 / (z - a)‖ := by
      have := norm_add_le (1 / (z - a) : ℂ) (S - 1 / (z - a))
      have heq : (1 / (z - a) : ℂ) + (S - 1 / (z - a)) = S := by ring
      rw [heq] at this; exact this
    have hsymm : ‖S - 1 / (z - a)‖ = ‖1 / (z - a) - S‖ := by rw [norm_sub_rev]
    rw [hsymm] at h1
    have h2 : ‖1 / (z - a)‖ + ‖1 / (z - a) - S‖ ≤ 1 / (d - r) + 1 := by
      linarith [hinvza_norm, hη'_le_one, hS_close.le]
    rw [hM_def]; linarith
  have hS_mem : S ∈ Metric.closedBall (0 : ℂ) M := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hS_norm
  have hdist : dist (1 / (z - a) : ℂ) S < η := by
    rw [dist_eq_norm]
    linarith [hS_close, hη'_le_η]
  have hP_close : ‖P.eval (1 / (z - a)) - P.eval S‖ < ε := by
    have := hη (1 / (z - a)) hinvza_mem S hS_mem hdist
    rwa [dist_eq_norm] at this
  have hQeval : (P.comp R).eval (1 / (z - b)) = P.eval S := by
    rw [Polynomial.eval_comp]
    congr 1
    exact hR_eval z hzbne
  rw [hQeval]
  exact hP_close

/--
Iterating the pole move along a finite chain.

Given a chain `chain : Fin (m+1) → ℂ` with each point outside `K` and each
consecutive pair satisfying the small-step condition, any polynomial in
`1/(z - chain 0)` can be uniformly approximated on `K` by a polynomial in
`1/(z - chain m)`.
-/
private lemma pole_move_polynomial_chain
    {K : Set ℂ} (hK : IsCompact K) :
    ∀ (m : ℕ) (chain : Fin (m + 1) → ℂ)
      (_hchain : ∀ i, chain i ∉ K)
      (_hstep : ∀ i : Fin m,
        ‖chain i.castSucc - chain i.succ‖ < Metric.infDist (chain i.succ) K)
      (P : Polynomial ℂ) (ε : ℝ) (_hε : 0 < ε),
      ∃ Q : Polynomial ℂ,
        ∀ z ∈ K, ‖P.eval (1 / (z - chain 0)) - Q.eval (1 / (z - chain (Fin.last m)))‖ < ε := by
  intro m
  induction m with
  | zero =>
    intro chain hchain _hstep P ε hε
    refine ⟨P, ?_⟩
    intro z hz
    have h0 : (0 : Fin 1) = Fin.last 0 := rfl
    rw [h0, sub_self, norm_zero]
    exact hε
  | succ m ih =>
    intro chain hchain hstep P ε hε
    have hstep0 : ‖chain (Fin.castSucc (0 : Fin (m + 1))) - chain (Fin.succ (0 : Fin (m + 1)))‖
        < Metric.infDist (chain (Fin.succ (0 : Fin (m + 1)))) K := hstep 0
    let chain' : Fin (m + 1) → ℂ := fun i => chain i.succ
    have hchain' : ∀ i, chain' i ∉ K := fun i => hchain i.succ
    have hstep' : ∀ i : Fin m,
        ‖chain' i.castSucc - chain' i.succ‖ < Metric.infDist (chain' i.succ) K := by
      intro i
      show ‖chain i.castSucc.succ - chain i.succ.succ‖
          < Metric.infDist (chain i.succ.succ) K
      have h := hstep i.succ
      have hcs : (i.succ).castSucc = i.castSucc.succ := by ext; simp
      rw [hcs] at h
      exact h
    set a₀ : ℂ := chain 0 with ha₀_def
    set b₀ : ℂ := chain (Fin.succ (0 : Fin (m + 1))) with hb₀_def
    have ha₀_notin : a₀ ∉ K := hchain 0
    have hb₀_notin : b₀ ∉ K := hchain _
    have hstep0' : ‖a₀ - b₀‖ < Metric.infDist b₀ K := by
      have heq : chain (Fin.castSucc (0 : Fin (m + 1))) = a₀ := by
        rw [ha₀_def]; congr 1
      rw [heq] at hstep0
      exact hstep0
    obtain ⟨P', hP'⟩ := pole_move_polynomial_step hK ha₀_notin hb₀_notin hstep0' P (ε / 2)
      (by linarith)
    obtain ⟨Q, hQ⟩ := ih chain' hchain' hstep' P' (ε / 2) (by linarith)
    refine ⟨Q, ?_⟩
    intro z hz
    have hchain'_0 : chain' 0 = b₀ := rfl
    have hchain'_last : chain' (Fin.last m) = chain (Fin.last (m + 1)) := by
      show chain (Fin.succ (Fin.last m)) = chain (Fin.last (m + 1))
      rfl
    have hQ_z := hQ z hz
    rw [hchain'_0, hchain'_last] at hQ_z
    have hP'_z := hP' z hz
    have htri := norm_add_le
      (P.eval (1 / (z - a₀)) - P'.eval (1 / (z - b₀)))
      (P'.eval (1 / (z - b₀)) - Q.eval (1 / (z - chain (Fin.last (m + 1)))))
    have heq : (P.eval (1 / (z - a₀)) - P'.eval (1 / (z - b₀))) +
        (P'.eval (1 / (z - b₀)) - Q.eval (1 / (z - chain (Fin.last (m + 1))))) =
        P.eval (1 / (z - a₀)) - Q.eval (1 / (z - chain (Fin.last (m + 1)))) := by ring
    rw [heq] at htri
    have hgoal_eq : P.eval (1 / (z - chain 0)) -
        Q.eval (1 / (z - chain (Fin.last (m + 1)))) =
        P.eval (1 / (z - a₀)) - Q.eval (1 / (z - chain (Fin.last (m + 1)))) := by
      rw [ha₀_def]
    rw [hgoal_eq]
    linarith

end SinglePolePolynomial

/--
Single pole is polynomially approximable.

Under the connected-complement hypothesis, the function `1/(z-a)` can be
uniformly approximated on `K` by polynomials for any `a ∉ K`.
-/
theorem single_pole_polynomial_approx
    {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected (Kᶜ : Set ℂ))
    {a : ℂ} (ha : a ∉ K) :
    ∀ ε > 0, ∃ p : Polynomial ℂ,
      ∀ z ∈ K, ‖p.eval z - 1 / (z - a)‖ < ε := by
  intro ε hε
  by_cases hKemp : K = ∅
  · refine ⟨0, ?_⟩
    intro z hz; rw [hKemp] at hz; exact absurd hz (Set.notMem_empty z)
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKemp
  have hcont : ContinuousOn (fun z : ℂ => ‖z‖) K := continuous_norm.continuousOn
  obtain ⟨z₀, _hz₀K, hz₀max⟩ := hK.exists_isMaxOn hKne hcont
  set M : ℝ := ‖z₀‖ with hM_def
  have hM_bound : ∀ z ∈ K, ‖z‖ ≤ M := fun z hz => hz₀max hz
  set R : ℝ := M + 1 with hR_def
  have hR_lt : ∀ z ∈ K, ‖z‖ < R := fun z hz => by
    rw [hR_def]; linarith [hM_bound z hz]
  obtain ⟨b, hb, γ, hRb⟩ := path_to_infinity_in_connected_complement hK hKc ha R
  have hKc_open : IsOpen (Kᶜ : Set ℂ) := hK.isClosed.isOpen_compl
  set γc : C(unitInterval, ℂ) :=
    ⟨fun t => ((γ : C(unitInterval, (Kᶜ : Set ℂ))) t).val,
      Continuous.subtype_val (γ : C(unitInterval, (Kᶜ : Set ℂ))).continuous⟩ with hγc_def
  set image : Set ℂ := Set.range γc with himg_def
  have himg_compact : IsCompact image := isCompact_range γc.continuous
  have himg_subset : image ⊆ (Kᶜ : Set ℂ) := by
    rintro x ⟨t, rfl⟩
    exact (γ t).property
  obtain ⟨ρ, hρ_pos, hρ_subset⟩ :=
    compact_subset_open_has_thickening himg_compact hKc_open himg_subset
  have himg_dist : ∀ t : unitInterval, ρ ≤ Metric.infDist (γc t) K := by
    intro t
    have ht_in : γc t ∈ image := ⟨t, rfl⟩
    by_contra hlt
    push_neg at hlt
    obtain ⟨x, hxK, hxd⟩ : ∃ x ∈ K, dist (γc t) x < ρ :=
      (Metric.infDist_lt_iff hKne).mp hlt
    have hx_thick : x ∈ Metric.thickening ρ image := by
      rw [Metric.mem_thickening_iff_infDist_lt ⟨γc t, ht_in⟩]
      calc Metric.infDist x image ≤ dist x (γc t) :=
            Metric.infDist_le_dist_of_mem ht_in
        _ = dist (γc t) x := dist_comm x (γc t)
        _ < ρ := hxd
    have hx_in_Kc : x ∈ (Kᶜ : Set ℂ) := hρ_subset hx_thick
    exact hx_in_Kc hxK
  have hγc_ucont : UniformContinuous γc :=
    CompactSpace.uniformContinuous_of_continuous γc.continuous
  rw [Metric.uniformContinuous_iff] at hγc_ucont
  obtain ⟨δ, hδ_pos, hδ⟩ := hγc_ucont ρ hρ_pos
  obtain ⟨m, hm_lt⟩ : ∃ m : ℕ, (1 : ℝ) / (m + 1) < δ := by
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ_pos
    exact ⟨m, by exact_mod_cast hm⟩
  have hti_mem : ∀ i : Fin (m + 2), (i : ℝ) / (m + 1) ∈ unitInterval := by
    intro i
    refine unitInterval.div_mem ?_ ?_ ?_
    · exact_mod_cast Nat.zero_le _
    · have : (0 : ℝ) < m + 1 := by positivity
      linarith
    · have h := i.is_le
      have : ((i : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast h
      simpa using this
  set chain : Fin (m + 2) → ℂ := fun i =>
    γc ⟨(i : ℝ) / (m + 1), hti_mem i⟩ with hchain_def
  have hchain_notin : ∀ i, chain i ∉ K := by
    intro i hin
    set ti : unitInterval := ⟨(i : ℝ) / (m + 1), hti_mem i⟩ with hti_def
    have hd : ρ ≤ Metric.infDist (γc ti) K := himg_dist ti
    have hd0 : (0 : ℝ) < Metric.infDist (γc ti) K := lt_of_lt_of_le hρ_pos hd
    have hin' : γc ti ∈ K := hin
    have heq : Metric.infDist (γc ti) K = 0 := Metric.infDist_zero_of_mem hin'
    linarith
  have hchain_step : ∀ i : Fin (m + 1),
      ‖chain i.castSucc - chain i.succ‖ < Metric.infDist (chain i.succ) K := by
    intro i
    set tcs : unitInterval := ⟨(i.castSucc : ℝ) / (m + 1), hti_mem i.castSucc⟩ with htcs_def
    set tsucc : unitInterval := ⟨(i.succ : ℝ) / (m + 1), hti_mem i.succ⟩ with htsucc_def
    have hchain_eq_cs : chain i.castSucc = γc tcs := rfl
    have hchain_eq_succ : chain i.succ = γc tsucc := rfl
    have h1 : dist (chain i.castSucc) (chain i.succ) < ρ := by
      rw [hchain_eq_cs, hchain_eq_succ]
      apply hδ
      rw [Subtype.dist_eq]
      simp only [Real.dist_eq]
      have hcs : ((i.castSucc : Fin (m + 2)) : ℝ) = (i : ℝ) := by
        simp [Fin.castSucc]
      have hsucc : ((i.succ : Fin (m + 2)) : ℝ) = (i : ℝ) + 1 := by
        simp [Fin.succ]
      show |((i.castSucc : Fin (m + 2)) : ℝ) / (m + 1) -
        ((i.succ : Fin (m + 2)) : ℝ) / (m + 1)| < δ
      rw [hcs, hsucc]
      have hmpos : (0 : ℝ) < m + 1 := by positivity
      rw [← sub_div, abs_div, abs_of_pos hmpos]
      have hsimp : |(i : ℝ) - ((i : ℝ) + 1)| = 1 := by
        rw [show (i : ℝ) - ((i : ℝ) + 1) = -1 by ring]; simp
      rw [hsimp]
      exact hm_lt
    have h2 : ρ ≤ Metric.infDist (chain i.succ) K := by
      rw [hchain_eq_succ]; exact himg_dist tsucc
    have h3 : ‖chain i.castSucc - chain i.succ‖ = dist (chain i.castSucc) (chain i.succ) := by
      rw [Complex.dist_eq]
    rw [h3]
    exact lt_of_lt_of_le h1 h2
  have hchain_zero : chain 0 = a := by
    show γc ⟨((0 : Fin (m + 2)) : ℝ) / (m + 1), _⟩ = a
    have h0 : (⟨((0 : Fin (m + 2)) : ℝ) / (m + 1), hti_mem 0⟩ : unitInterval)
        = (0 : unitInterval) := by
      apply Subtype.ext
      show ((0 : Fin (m + 2)) : ℝ) / (m + 1) = 0
      simp
    rw [h0]
    show (γ (0 : unitInterval)).val = a
    rw [γ.source]
  have hchain_last : chain (Fin.last (m + 1)) = b := by
    show γc ⟨((Fin.last (m + 1) : Fin (m + 2)) : ℝ) / (m + 1), _⟩ = b
    have h1 : (⟨((Fin.last (m + 1) : Fin (m + 2)) : ℝ) / (m + 1),
        hti_mem (Fin.last (m + 1))⟩ : unitInterval) = (1 : unitInterval) := by
      apply Subtype.ext
      show ((Fin.last (m + 1) : Fin (m + 2)) : ℝ) / (m + 1) = 1
      have hval : ((Fin.last (m + 1) : Fin (m + 2)) : ℕ) = m + 1 := Fin.val_last (m + 1)
      have hcast : ((Fin.last (m + 1) : Fin (m + 2)) : ℝ) = (m : ℝ) + 1 := by
        show ((((Fin.last (m + 1) : Fin (m + 2)) : ℕ)) : ℝ) = (m : ℝ) + 1
        rw [hval]; push_cast; ring
      rw [hcast]
      have hmpos : ((m : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    rw [h1]
    show (γ (1 : unitInterval)).val = b
    rw [γ.target]
  obtain ⟨Q, hQ⟩ := pole_move_polynomial_chain hK (m + 1) chain hchain_notin hchain_step
    Polynomial.X (ε / 2) (by linarith)
  have hzb_ge_one : ∀ z ∈ K, (1 : ℝ) ≤ ‖z - b‖ := by
    intro z hz
    have h1 : ‖b‖ - ‖z‖ ≤ ‖z - b‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le b z
    have h2 : R < ‖b‖ := hRb
    have h3 : ‖z‖ ≤ M := hM_bound z hz
    have h4 : R - M = 1 := by rw [hR_def]; ring
    linarith
  have hinv_zb_norm : ∀ z ∈ K, ‖(1 / (z - b) : ℂ)‖ ≤ 1 := by
    intro z hz
    rw [norm_div, norm_one]
    have h := hzb_ge_one z hz
    have hzbpos : 0 < ‖z - b‖ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) h
    rw [div_le_iff₀ hzbpos]
    linarith
  have hQcont : ContinuousOn (fun w : ℂ => Q.eval w) (Metric.closedBall (0 : ℂ) 2) :=
    Q.continuous.continuousOn
  have hQcomp : IsCompact (Metric.closedBall (0 : ℂ) 2) := isCompact_closedBall _ _
  have hQucon : UniformContinuousOn (fun w : ℂ => Q.eval w) (Metric.closedBall (0 : ℂ) 2) :=
    hQcomp.uniformContinuousOn_of_continuous hQcont
  rw [Metric.uniformContinuousOn_iff] at hQucon
  obtain ⟨η, hη_pos, hη⟩ := hQucon (ε / 2) (by linarith)
  set η' : ℝ := min η 1 with hη'_def
  have hη'_pos : 0 < η' := lt_min hη_pos one_pos
  have hη'_le_η : η' ≤ η := min_le_left _ _
  have hη'_le_one : η' ≤ 1 := min_le_right _ _
  have hb_dom : ∀ z ∈ K, ‖z‖ < ‖b‖ := fun z hz => by
    have h1 := hR_lt z hz
    have h2 : R < ‖b‖ := hRb
    linarith
  obtain ⟨p₀, hp₀⟩ := far_pole_polynomial_approx hK hb_dom η' hη'_pos
  refine ⟨Q.comp p₀, ?_⟩
  intro z hz
  have hQpz : (Q.comp p₀).eval z = Q.eval (p₀.eval z) := Polynomial.eval_comp
  have hp₀_z := hp₀ z hz
  have hinvzb := hinv_zb_norm z hz
  have hp₀_norm : ‖p₀.eval z‖ ≤ 2 := by
    have h1 : ‖p₀.eval z‖ ≤ ‖1 / (z - b)‖ + ‖p₀.eval z - 1 / (z - b)‖ := by
      have := norm_add_le (1 / (z - b) : ℂ) (p₀.eval z - 1 / (z - b))
      have heq : (1 / (z - b) : ℂ) + (p₀.eval z - 1 / (z - b)) = p₀.eval z := by ring
      rw [heq] at this; exact this
    linarith [hη'_le_one]
  have hp₀_mem : p₀.eval z ∈ Metric.closedBall (0 : ℂ) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hp₀_norm
  have hinv_mem : (1 / (z - b) : ℂ) ∈ Metric.closedBall (0 : ℂ) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right]; linarith [hinvzb]
  have hdist_p₀_inv : dist (p₀.eval z) (1 / (z - b)) < η := by
    rw [dist_eq_norm]
    linarith [hp₀_z, hη'_le_η]
  have hQ_close : ‖Q.eval (p₀.eval z) - Q.eval (1 / (z - b))‖ < ε / 2 := by
    have := hη (p₀.eval z) hp₀_mem (1 / (z - b)) hinv_mem hdist_p₀_inv
    rwa [dist_eq_norm] at this
  have hQ_z := hQ z hz
  rw [hchain_zero, hchain_last] at hQ_z
  have hXeval : (Polynomial.X : Polynomial ℂ).eval (1 / (z - a)) = 1 / (z - a) :=
    Polynomial.eval_X
  rw [hXeval] at hQ_z
  rw [hQpz]
  have htri := norm_add_le
    (Q.eval (p₀.eval z) - Q.eval (1 / (z - b)))
    (Q.eval (1 / (z - b)) - 1 / (z - a))
  have heq : (Q.eval (p₀.eval z) - Q.eval (1 / (z - b))) +
      (Q.eval (1 / (z - b)) - 1 / (z - a)) =
      Q.eval (p₀.eval z) - 1 / (z - a) := by ring
  rw [heq] at htri
  have hfinal : ‖Q.eval (1 / (z - b)) - 1 / (z - a)‖ < ε / 2 := by
    have hh : ‖1 / (z - a) - Q.eval (1 / (z - b))‖ < ε / 2 := hQ_z
    rw [norm_sub_rev] at hh; exact hh
  linarith

/--
Finite pole sums are polynomially approximable.

Combining `single_pole_polynomial_approx` over a finite collection of poles.
-/
theorem finite_pole_sum_polynomial_approx
    {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected (Kᶜ : Set ℂ))
    {N : ℕ} (a : Fin N → ℂ) (c : Fin N → ℂ) (ha : ∀ j, a j ∉ K) :
    ∀ ε > 0, ∃ p : Polynomial ℂ,
      ∀ z ∈ K, ‖p.eval z - ∑ j, c j / (z - a j)‖ < ε := by
  sorry

/--
**Runge's theorem (polynomial form, connected-complement version).**

If `U` is open in `ℂ`, `K` is compact with `K ⊆ U` and `Kᶜ` connected, and
`f : ℂ → ℂ` is holomorphic on `U`, then `f` can be uniformly approximated on
`K` by polynomials.
-/
theorem MainTheorem {U K : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hKc : IsConnected (Kᶜ)) (hf : DifferentiableOn ℂ f U) :
    ∀ ε > 0, ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖p.eval z - f z‖ < ε := by
  sorry
