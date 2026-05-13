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
  -- Handle K empty separately.
  by_cases hKemp : K = ∅
  · refine ⟨0, ?_⟩
    intro z hz
    rw [hKemp] at hz
    exact absurd hz (Set.notMem_empty z)
  -- K nonempty case.
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKemp
  set d : ℝ := Metric.infDist b K with hd_def
  set r : ℝ := ‖a - b‖ with hr_def
  -- Positivity of d.
  have hd_pos : 0 < d := by
    have hKclosed : IsClosed K := hK.isClosed
    exact (hKclosed.notMem_iff_infDist_pos hKne).mp hb
  have hr_nonneg : 0 ≤ r := norm_nonneg _
  have hr_lt_d : r < d := hab
  -- For every z ∈ K, ‖z - b‖ ≥ d > 0.
  have hzb_ge : ∀ z ∈ K, d ≤ ‖z - b‖ := by
    intro z hz
    have := Metric.infDist_le_dist_of_mem hz (x := b)
    -- this : Metric.infDist b K ≤ dist b z
    rw [show dist b z = ‖z - b‖ from by rw [dist_comm]; exact Complex.dist_eq z b] at this
    exact this
  -- d - r > 0, useful for bounding ‖z - a‖ from below.
  have hd_minus_r_pos : 0 < d - r := sub_pos.mpr hr_lt_d
  -- ‖z - a‖ ≥ d - r for z ∈ K.
  have hza_ge : ∀ z ∈ K, d - r ≤ ‖z - a‖ := by
    intro z hz
    have h1 : d ≤ ‖z - b‖ := hzb_ge z hz
    have h2 : ‖z - b‖ ≤ ‖z - a‖ + ‖a - b‖ := by
      have := norm_sub_le (z - a) (b - a)
      have heq1 : (z - a) - (b - a) = z - b := by ring
      have heq2 : ‖b - a‖ = ‖a - b‖ := norm_sub_rev b a
      rw [heq1, heq2] at this
      -- Wait: norm_sub_le gives ‖x + y‖ ≤ ‖x‖ + ‖y‖, not what we need.
      sorry
    linarith
  -- Pick N with q^{N+1} / (d - r) < ε, where q = r / d.
  set q : ℝ := r / d with hq_def
  have hq_nonneg : 0 ≤ q := div_nonneg hr_nonneg hd_pos.le
  have hq_lt_one : q < 1 := by
    rw [hq_def]
    rw [div_lt_one hd_pos]
    exact hr_lt_d
  -- q^n → 0, so q^n * (something) < ε eventually.
  have htends : Filter.Tendsto (fun n : ℕ => q ^ (n + 1) / (d - r))
      Filter.atTop (𝓝 (0 / (d - r))) := by
    apply Filter.Tendsto.div_const
    have hbase := tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one
    exact hbase.comp (Filter.tendsto_add_atTop_nat 1)
  rw [zero_div] at htends
  have hev : ∀ᶠ n in Filter.atTop, q ^ (n + 1) / (d - r) < ε := by
    have := htends.eventually (gt_mem_nhds hε)
    exact this
  obtain ⟨N, hN⟩ := hev.exists
  -- Wait, hev.exists is wrong; need to use Filter.eventually_atTop.
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
