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
    {a b : ℂ} (ha : a ∉ K) (hb : b ∉ K)
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
    -- dist b z = ‖b - z‖ = ‖z - b‖
    have heq : dist b z = ‖z - b‖ := by
      rw [Complex.dist_eq, ← norm_neg]
      congr 1
      ring
    rw [heq] at h
    exact h
  have hza_ge : ∀ z ∈ K, d - r ≤ ‖z - a‖ := by
    intro z hz
    have h1 : d ≤ ‖z - b‖ := hzb_ge z hz
    -- ‖z - b‖ = ‖(z - a) + (a - b)‖ ≤ ‖z - a‖ + ‖a - b‖
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
  -- Find N such that q^(N+1) / (d - r) < ε
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
  -- Set up shorthand
  have hzb : z - b ≠ 0 := hzb_ne z hz
  have hza : z - a ≠ 0 := hza_ne z hz
  have h_zb_norm : d ≤ ‖z - b‖ := hzb_ge z hz
  have h_zb_pos : 0 < ‖z - b‖ := lt_of_lt_of_le hd_pos h_zb_norm
  have h_za_norm : d - r ≤ ‖z - a‖ := hza_ge z hz
  have h_za_pos : 0 < ‖z - a‖ := lt_of_lt_of_le hd_minus_r_pos h_za_norm
  -- Geometric series identity:
  -- 1/(z-a) - ∑ n, (a-b)^n / (z-b)^(n+1) = (a-b)^(N+1) / ((z-b)^(N+1) * (z-a))
  -- We use: ∑_{n=0}^{N} u^n / w^{n+1} = (1/w) * ∑_{n=0}^{N} (u/w)^n
  --                                    = (1/w) * (1 - (u/w)^(N+1)) / (1 - u/w)
  --                                    = (1 - (u/w)^(N+1)) / (w - u)
  -- So 1/(w-u) - sum = (u/w)^(N+1) / (w-u) = u^(N+1) / (w^(N+1) * (w - u))
  -- where u = a-b, w = z-b, w - u = z - a.
  -- Use the identity: ∑_{n=0}^{N} (u/w)^n = (1 - (u/w)^(N+1)) / (1 - u/w)
  -- Rewriting sum: ∑_{n=0}^{N} u^n / w^{n+1} = (1/w) * ∑_{n=0}^{N} (u/w)^n
  -- Define u = a - b, w = z - b. Then w - u = z - a.
  set u : ℂ := a - b with hu_def
  set w : ℂ := z - b with hw_def
  have hw_eq_zb : w = z - b := hw_def
  have hu_eq_ab : u = a - b := hu_def
  have hwu_eq : w - u = z - a := by rw [hw_def, hu_def]; ring
  have hw_ne : w ≠ 0 := by rw [hw_def]; exact hzb
  have hwu_ne : w - u ≠ 0 := by rw [hwu_eq]; exact hza
  -- We want: sum = (1/w) * ∑ (u/w)^n
  have h_sum_eq : ∑ n ∈ Finset.range (N + 1), u ^ n / w ^ (n + 1)
      = (1 / w) * ∑ n ∈ Finset.range (N + 1), (u / w) ^ n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [div_pow]
    field_simp
    ring
  -- Use geom_sum_eq if u / w ≠ 1
  have h_ratio_ne_one : u / w ≠ 1 := by
    intro h
    have : u = w := by field_simp at h; exact h
    have hwu0 : w - u = 0 := by rw [this]; ring
    exact hwu_ne hwu0
  have h_geom : ∑ n ∈ Finset.range (N + 1), (u / w) ^ n
      = ((u / w) ^ (N + 1) - 1) / (u / w - 1) := geom_sum_eq h_ratio_ne_one (N + 1)
  -- Compute the difference
  have h_main :
      1 / (z - a) - ∑ n ∈ Finset.range (N + 1), u ^ n / w ^ (n + 1)
        = u ^ (N + 1) / (w ^ (N + 1) * (z - a)) := by
    rw [← hwu_eq]
    rw [h_sum_eq, h_geom]
    have hw_pow_ne : w ^ (N + 1) ≠ 0 := pow_ne_zero _ hw_ne
    -- u/w - 1 = (u - w) / w = -(w - u)/w
    have h_uw1 : u / w - 1 = (u - w) / w := by
      field_simp
    rw [h_uw1]
    -- (u/w)^(N+1) = u^(N+1) / w^(N+1)
    have h_ratio_pow : (u / w) ^ (N + 1) = u ^ (N + 1) / w ^ (N + 1) := div_pow u w (N + 1)
    rw [h_ratio_pow]
    have hwu_ne' : w - u ≠ 0 := hwu_ne
    have huw_ne : u - w ≠ 0 := by
      intro h
      apply hwu_ne
      have : w - u = -(u - w) := by ring
      rw [this, h, neg_zero]
    field_simp
    ring
  rw [hu_def, hw_def] at h_main
  rw [h_main]
  -- Now bound ‖(a - b)^(N+1) / ((z - b)^(N+1) * (z - a))‖
  rw [norm_div, norm_mul, norm_pow, norm_pow]
  -- = ‖a-b‖^(N+1) / (‖z-b‖^(N+1) * ‖z-a‖) = r^(N+1) / (‖z-b‖^(N+1) * ‖z-a‖)
  -- ≤ r^(N+1) / (d^(N+1) * (d - r))
  have h_zb_pow_pos : 0 < ‖z - b‖ ^ (N + 1) := pow_pos h_zb_pos _
  have h_zb_pow_ge : d ^ (N + 1) ≤ ‖z - b‖ ^ (N + 1) :=
    pow_le_pow_left₀ hd_pos.le h_zb_norm _
  have h_d_pow_pos : 0 < d ^ (N + 1) := pow_pos hd_pos _
  have h_denom_pos : 0 < ‖z - b‖ ^ (N + 1) * ‖z - a‖ := mul_pos h_zb_pow_pos h_za_pos
  have h_d_denom_pos : 0 < d ^ (N + 1) * (d - r) := mul_pos h_d_pow_pos hd_minus_r_pos
  -- ‖a - b‖^(N+1) / (‖z - b‖^(N+1) * ‖z - a‖) ≤ r^(N+1) / (d^(N+1) * (d - r))
  have h_num : ‖a - b‖ ^ (N + 1) = r ^ (N + 1) := by rw [hr_def]
  rw [h_num]
  have h_step1 : r ^ (N + 1) / (‖z - b‖ ^ (N + 1) * ‖z - a‖) ≤
      r ^ (N + 1) / (d ^ (N + 1) * (d - r)) := by
    apply div_le_div_of_nonneg_left
    · exact pow_nonneg hr_nonneg _
    · exact h_d_denom_pos
    · exact mul_le_mul h_zb_pow_ge h_za_norm hd_minus_r_pos.le h_zb_pow_pos.le
  -- And r^(N+1) / (d^(N+1) * (d - r)) = q^(N+1) / (d - r)
  have h_step2 : r ^ (N + 1) / (d ^ (N + 1) * (d - r)) = q ^ (N + 1) / (d - r) := by
    rw [hq_def, div_pow]
    field_simp
  rw [h_step2] at h_step1
  -- Apply hN
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
  sorry

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
