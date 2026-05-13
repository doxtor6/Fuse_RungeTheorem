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
  sorry

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
  · -- Step 1: Get max norm M on K.
    have hcont : ContinuousOn (fun z : ℂ => ‖z‖) K := continuous_norm.continuousOn
    obtain ⟨z₀, hz₀K, hz₀max⟩ := hK.exists_isMaxOn hKne hcont
    set M : ℝ := ‖z₀‖ with hM_def
    have hM_bound : ∀ z ∈ K, ‖z‖ ≤ M := fun z hz => hz₀max hz
    have hMb : M < ‖b‖ := hb z₀ hz₀K
    have hM_nonneg : 0 ≤ M := norm_nonneg _
    have hb_ne : b ≠ 0 := by
      intro hb0
      have : ‖b‖ = 0 := by rw [hb0]; simp
      linarith [hM_nonneg]
    have hb_pos : 0 < ‖b‖ := norm_pos_iff.mpr hb_ne
    set q : ℝ := M / ‖b‖ with hq_def
    have hq_nonneg : 0 ≤ q := div_nonneg hM_nonneg hb_pos.le
    have hq_lt_one : q < 1 := by
      rw [hq_def, div_lt_one hb_pos]; exact hMb
    have hgap_pos : 0 < ‖b‖ - M := by linarith
    -- Step 2: Choose N so that q^N / (‖b‖ - M) < ε.
    have htends : Filter.Tendsto (fun n : ℕ => q ^ n / (‖b‖ - M)) Filter.atTop (𝓝 0) := by
      have h₁ : Filter.Tendsto (fun n : ℕ => q ^ n) Filter.atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one
      have h₂ := h₁.div_const (‖b‖ - M)
      simpa using h₂
    have hev : ∀ᶠ n in Filter.atTop, q ^ n / (‖b‖ - M) < ε := by
      have := (Metric.tendsto_atTop.mp htends) ε hε
      obtain ⟨N, hN⟩ := this
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have := hN n hn
      simp only [Real.dist_eq, sub_zero] at this
      have hpos : 0 ≤ q ^ n / (‖b‖ - M) :=
        div_nonneg (pow_nonneg hq_nonneg _) hgap_pos.le
      rw [abs_of_nonneg hpos] at this
      exact this
    obtain ⟨N, hN⟩ := hev.exists
    -- Step 3: Build polynomial p(z) = -∑_{n=0}^{N-1} z^n / b^{n+1}.
    refine ⟨∑ n ∈ Finset.range N,
      Polynomial.C (-(1 / b ^ (n + 1))) * Polynomial.X ^ n, ?_⟩
    intro z hzK
    -- Evaluate the polynomial.
    have heval :
        (∑ n ∈ Finset.range N,
            Polynomial.C (-(1 / b ^ (n + 1))) * Polynomial.X ^ n).eval z =
          ∑ n ∈ Finset.range N, -(z ^ n / b ^ (n + 1)) := by
      rw [Polynomial.eval_finset_sum]
      apply Finset.sum_congr rfl
      intro n _
      simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
            Polynomial.eval_X, neg_div, div_eq_mul_inv, mul_comm]
    rw [heval]
    -- z ≠ b since ‖z‖ < ‖b‖
    have hzne : z - b ≠ 0 := by
      intro h
      have : z = b := by linarith [sub_eq_zero.mp h]
      have hzb : ‖z‖ = ‖b‖ := by rw [this]
      have : ‖z‖ < ‖b‖ := hb z hzK
      linarith
    -- Key identity: -S - 1/(z-b) = (z/b)^N / (z-b) but with negative...
    -- Let's compute: S = ∑ z^n/b^{n+1}, partial sum identity:
    -- (z - b) * S = ∑ z^{n+1}/b^{n+1} - ∑ z^n/b^n = (z/b)^N - 1
    -- So S = ((z/b)^N - 1)/(z - b), hence -S - 1/(z-b) = -(z/b)^N/(z-b).
    have hb_pow_ne : ∀ n, (b ^ n : ℂ) ≠ 0 := fun n => pow_ne_zero n hb_ne
    have hkey :
        (∑ n ∈ Finset.range N, -(z ^ n / b ^ (n + 1))) - 1 / (z - b) =
          -(z ^ N / (b ^ N * (z - b))) := by
      have hS :
          (z - b) * (∑ n ∈ Finset.range N, z ^ n / b ^ (n + 1)) =
            (z / b) ^ N - 1 := by
        rw [Finset.mul_sum]
        have :
            ∀ n ∈ Finset.range N,
              (z - b) * (z ^ n / b ^ (n + 1)) =
                (z / b) ^ (n + 1) - (z / b) ^ n := by
          intro n _
          have hbn : (b ^ n : ℂ) ≠ 0 := hb_pow_ne n
          have hbn1 : (b ^ (n + 1) : ℂ) ≠ 0 := hb_pow_ne (n + 1)
          field_simp
          ring
        rw [Finset.sum_congr rfl this]
        rw [Finset.sum_range_succ_comm] <;> try rfl
        -- telescoping
        sorry
      sorry
    sorry
  · -- K is empty: any polynomial works
    refine ⟨0, ?_⟩
    intro z hz
    exact absurd ⟨z, hz⟩ hKne

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
