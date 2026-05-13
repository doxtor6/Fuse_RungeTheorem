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

/--
Cauchy integral approximation by finite pole sums.

For `f` holomorphic on an open `U` containing a compact `K`, we can uniformly
approximate `f` on `K` by a finite sum of simple poles whose pole locations lie
outside `K`.
-/
lemma cauchy_integral_approximated_by_pole_sum
    {K U : Set ℂ} {f : ℂ → ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : DifferentiableOn ℂ f U) :
    ∀ ε > 0, ∃ (N : ℕ) (a : Fin N → ℂ) (c : Fin N → ℂ),
      (∀ j, a j ∉ K) ∧
      ∀ z ∈ K, ‖(∑ j, c j / (z - a j)) - f z‖ < ε := by
  sorry

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
      ∀ z ∈ K, ‖(∑ j, c j / (z - a j)) - f z‖ < ε := by
  sorry

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
  -- Uniform bound for both 1/(z-a) and approximations on K.
  set M : ℝ := 1 / (d - r) + 1 with hM_def
  have hM_pos : 0 < M := by
    have h1 : 0 < 1 / (d - r) := by positivity
    linarith
  have hM_nonneg : 0 ≤ M := hM_pos.le
  -- Use uniform continuity of P.eval on closed ball of radius M.
  have hPcont : ContinuousOn (fun w : ℂ => P.eval w) (Metric.closedBall (0 : ℂ) M) :=
    P.continuous.continuousOn
  have hPcomp : IsCompact (Metric.closedBall (0 : ℂ) M) := isCompact_closedBall _ _
  have hPucon : UniformContinuousOn (fun w : ℂ => P.eval w) (Metric.closedBall (0 : ℂ) M) :=
    hPcomp.uniformContinuousOn_of_continuous hPcont
  rw [Metric.uniformContinuousOn_iff] at hPucon
  obtain ⟨η, hη_pos, hη⟩ := hPucon ε hε
  -- Pick η' = min(η, 1) so that the approximation is within η and stays in ball M.
  set η' : ℝ := min η 1 with hη'_def
  have hη'_pos : 0 < η' := lt_min hη_pos one_pos
  have hη'_le_η : η' ≤ η := min_le_left _ _
  have hη'_le_one : η' ≤ 1 := min_le_right _ _
  -- Apply local_pole_moving with ε = η'.
  obtain ⟨N, hN⟩ := local_pole_moving hK ha hb hab η' hη'_pos
  -- Build the approximating polynomial in 1/(z-b).
  -- The partial sum is ∑_{n=0}^N (a-b)^n / (z-b)^(n+1)
  --                  = (1/(z-b)) * ∑_{n=0}^N (a-b)^n (1/(z-b))^n
  -- So the polynomial R(w) := ∑_{n=0}^N (a-b)^n * w^(n+1) satisfies R.eval(1/(z-b)) = partial sum.
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
    rw [one_div, inv_pow, pow_succ, mul_inv, ← mul_assoc, ← one_div, ← one_div, ← div_eq_mul_inv,
        ← div_eq_mul_inv, mul_comm]
    field_simp
  -- Choose Q := P.comp R, so Q.eval (1/(z-b)) = P.eval (R.eval (1/(z-b))) = P.eval (partial sum).
  refine ⟨P.comp R, ?_⟩
  intro z hz
  have hzbne : z ≠ b := by
    intro hzeq
    have : z - b = 0 := by rw [hzeq]; ring
    exact (hzb_ne z hz) this
  have hane : z - a ≠ 0 := hza_ne z hz
  -- partial sum approximates 1/(z-a) within η'.
  have hpartial := hN z hz
  -- ‖1/(z-a)‖ ≤ 1/(d-r) < M.
  have hinvza_norm : ‖(1 / (z - a) : ℂ)‖ ≤ 1 / (d - r) := by
    rw [norm_div, norm_one]
    rw [div_le_div_iff (by positivity) hd_minus_r_pos]
    have := hza_ge z hz
    have h_za_pos : 0 < ‖z - a‖ := lt_of_lt_of_le hd_minus_r_pos this
    rw [one_mul]
    have := hza_ge z hz; linarith
  have hinvza_lt_M : ‖(1 / (z - a) : ℂ)‖ < M := by
    have : 1 / (d - r) < M := by rw [hM_def]; linarith
    linarith [hinvza_norm]
  have hinvza_mem : (1 / (z - a) : ℂ) ∈ Metric.closedBall (0 : ℂ) M := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hinvza_norm.trans (by rw [hM_def]; linarith)
  -- ‖partial sum‖ ≤ ‖1/(z-a)‖ + η' ≤ 1/(d-r) + 1 = M
  set S : ℂ := ∑ n ∈ Finset.range (N + 1), (a - b) ^ n / (z - b) ^ (n + 1) with hS_def
  have hS_close : ‖1 / (z - a) - S‖ < η' := hpartial
  have hS_norm : ‖S‖ ≤ M := by
    have h1 : ‖S‖ ≤ ‖1 / (z - a)‖ + ‖1 / (z - a) - S‖ := by
      have := norm_sub_norm_le (1 / (z - a)) S
      have h2 : ‖1 / (z - a) - S‖ = ‖S - 1 / (z - a)‖ := by rw [norm_sub_rev]
      linarith [norm_sub_le (1 / (z - a) : ℂ) S, this]
    have h2 : ‖1 / (z - a)‖ + ‖1 / (z - a) - S‖ ≤ 1 / (d - r) + 1 := by
      have := hS_close
      linarith [hinvza_norm, hη'_le_one]
    rw [hM_def]; linarith
  have hS_mem : S ∈ Metric.closedBall (0 : ℂ) M := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hS_norm
  -- Now ‖P(1/(z-a)) - P(S)‖ < ε.
  have hdist : dist (1 / (z - a) : ℂ) S < η := by
    rw [dist_eq_norm]
    have := hS_close
    linarith [hη'_le_η]
  have hP_close : ‖P.eval (1 / (z - a)) - P.eval S‖ < ε := by
    have := hη (1 / (z - a)) hinvza_mem S hS_mem hdist
    rwa [dist_eq_norm] at this
  -- Q.eval(1/(z-b)) = P.eval(R.eval(1/(z-b))) = P.eval(S).
  have hQeval : (P.comp R).eval (1 / (z - b)) = P.eval S := by
    rw [Polynomial.eval_comp]
    congr 1
    exact hR_eval z hzbne
  rw [hQeval]
  exact hP_close

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
  sorry

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
