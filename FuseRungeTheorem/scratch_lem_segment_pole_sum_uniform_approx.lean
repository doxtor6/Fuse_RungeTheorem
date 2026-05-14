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
Grid cover of a compact set in an open set (sub-obligation 1 for the grid
Cauchy representation).

For `K` compact contained in open `U` and any `ρ > 0`, there exists a finite
family of axis-parallel closed squares of side `s` with `s * Real.sqrt 2 < ρ`,
indexed by `Fin n`, whose union covers `K` and whose closures all lie in `U`.

The square indexed by `i` is specified by its lower-left corner `corner i` and
side length `s`, i.e. the closed set
`{w | w.re ∈ [corner i .re, corner i .re + s] ∧ w.im ∈ [corner i .im, corner i .im + s]}`.

This is the "grid construction" step in the proof of the grid Cauchy
representation lemma. It is purely a geometric/measure-theoretic fact about
compact sets in `ℂ`; no holomorphy is involved.
-/
private lemma grid_squares_cover_compact
    {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (n : ℕ) (corner : Fin n → ℂ) (s : ℝ),
      0 < s ∧
      (∀ z ∈ K, ∃ i, z.re ∈ Set.Icc ((corner i).re) ((corner i).re + s) ∧
                     z.im ∈ Set.Icc ((corner i).im) ((corner i).im + s)) ∧
      (∀ i, ∀ w : ℂ, w.re ∈ Set.Icc ((corner i).re) ((corner i).re + s) →
                     w.im ∈ Set.Icc ((corner i).im) ((corner i).im + s) →
                     w ∈ U) := by
  sorry

/--
Boundary segments of a grid covering lie in `U \ K` (sub-obligation 2).

Given a finite axis-parallel grid covering of a compact `K` by closed squares
of side `s` with closures in `U` (as produced by `grid_squares_cover_compact`),
the oriented edges that bound exactly one square in the covering — the
algebraic boundary of the union — form a family of segments whose images lie
in `U \ K`.

The conclusion is packaged as an existence statement: there exists a `Fin m`
family of starts `A` and ends `B` so that every parametrised point
`A i + t·(B i - A i)` (for `t ∈ [0,1]`) lies in `U \ K`. The auxiliary
"each segment is a boundary edge of the grid" data is left implicit; what we
expose downstream is exactly the boundary-segment family used by the Cauchy
formula step.
-/
private lemma grid_boundary_segments_off_K
    {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (m : ℕ) (A B : Fin m → ℂ),
      ∀ i, ∀ t ∈ Set.Icc (0:ℝ) 1, A i + (t : ℂ) * (B i - A i) ∈ U \ K := by
  sorry

/--
Goursat step: for a function holomorphic on `U \ {z}` and continuous on `U`
(where `U` contains the closed rectangle and `z` lies in the open interior),
the sum of the four oriented `segmentIntegral`s of `g` around the rectangle
boundary equals zero. This is the off-countable Cauchy-Goursat theorem for a
rectangle, converted to the `segmentIntegral` parametrisation used in this
file.
-/
private lemma rectangle_holomorphic_part_integral_zero
    {U : Set ℂ} {g : ℂ → ℂ} (hU : IsOpen U)
    (x₀ y₀ s : ℝ) (hs : 0 < s)
    (hrect_sub_U : ∀ w : ℂ, w.re ∈ Set.Icc x₀ (x₀ + s) →
                            w.im ∈ Set.Icc y₀ (y₀ + s) → w ∈ U)
    (z : ℂ) (hz_int : z.re ∈ Set.Ioo x₀ (x₀ + s) ∧ z.im ∈ Set.Ioo y₀ (y₀ + s))
    (hg_cont : ContinuousOn g U)
    (hg_diff : DifferentiableOn ℂ g (U \ {z})) :
    segmentIntegral ⟨x₀, y₀⟩ ⟨x₀ + s, y₀⟩ g +
    segmentIntegral ⟨x₀ + s, y₀⟩ ⟨x₀ + s, y₀ + s⟩ g +
    segmentIntegral ⟨x₀ + s, y₀ + s⟩ ⟨x₀, y₀ + s⟩ g +
    segmentIntegral ⟨x₀, y₀ + s⟩ ⟨x₀, y₀⟩ g = 0 := by
  -- Setup: corner abbreviations.
  set A : ℂ := ⟨x₀, y₀⟩ with hA_def
  set B : ℂ := ⟨x₀ + s, y₀⟩ with hB_def
  set C : ℂ := ⟨x₀ + s, y₀ + s⟩ with hC_def
  set D : ℂ := ⟨x₀, y₀ + s⟩ with hD_def
  -- Key complex differences (axis-aligned).
  have hBA : B - A = (s : ℂ) := by
    rw [hA_def, hB_def]; apply Complex.ext <;> simp
  have hCB : C - B = (s : ℂ) * Complex.I := by
    rw [hB_def, hC_def]; apply Complex.ext <;> simp
  have hDC : D - C = -(s : ℂ) := by
    rw [hC_def, hD_def]; apply Complex.ext <;> simp
  have hAD : A - D = -((s : ℂ) * Complex.I) := by
    rw [hA_def, hD_def]; apply Complex.ext <;> simp
  -- Each segmentIntegral expressed as a real-axis interval integral.
  have h_seg_AB : segmentIntegral A B g = ∫ x : ℝ in x₀..x₀ + s, g (x + y₀ * Complex.I) := by
    unfold segmentIntegral
    rw [hBA]
    have hA_eq : A = (x₀ : ℂ) + (y₀ : ℂ) * Complex.I := by
      rw [hA_def]; exact Complex.mk_eq_add_mul_I x₀ y₀
    have hrewrite : ∀ t : ℝ,
        g (A + (t : ℂ) * (s : ℂ)) * (s : ℂ) =
        (s : ℝ) • g (((s * t + x₀ : ℝ) : ℂ) + y₀ * Complex.I) := by
      intro t
      rw [Complex.real_smul]
      rw [mul_comm ((s : ℝ) : ℂ) _]
      congr 2
      rw [hA_eq]
      push_cast
      ring
    simp_rw [hrewrite]
    rw [intervalIntegral.integral_smul]
    have key := intervalIntegral.smul_integral_comp_mul_add
      (f := fun x : ℝ => g ((x : ℂ) + (y₀ : ℂ) * Complex.I))
      (a := 0) (b := 1) (c := s) (d := x₀)
    simp only [mul_zero, zero_add, mul_one] at key
    rw [key]
    congr 1
    ring
  have h_seg_BC : segmentIntegral B C g =
      Complex.I * ∫ y : ℝ in y₀..y₀ + s, g (((x₀ + s : ℝ) : ℂ) + y * Complex.I) := by
    unfold segmentIntegral
    rw [hCB]
    have hB_eq : B = ((x₀ + s : ℝ) : ℂ) + (y₀ : ℂ) * Complex.I := by
      rw [hB_def]; exact Complex.mk_eq_add_mul_I (x₀ + s) y₀
    have hrewrite : ∀ t : ℝ,
        g (B + (t : ℂ) * ((s : ℂ) * Complex.I)) * ((s : ℂ) * Complex.I) =
        (s : ℝ) • (Complex.I * g (((x₀ + s : ℝ) : ℂ) + ((s * t + y₀ : ℝ) : ℂ) * Complex.I)) := by
      intro t
      rw [Complex.real_smul]
      have heq : g (B + (t : ℂ) * ((s : ℂ) * Complex.I)) =
             g (((x₀ + s : ℝ) : ℂ) + ((s * t + y₀ : ℝ) : ℂ) * Complex.I) := by
        congr 1
        rw [hB_eq]
        push_cast
        ring
      rw [heq]
      ring
    simp_rw [hrewrite]
    rw [intervalIntegral.integral_smul]
    have key := intervalIntegral.smul_integral_comp_mul_add
      (f := fun y : ℝ => Complex.I * g (((x₀ + s : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      (a := 0) (b := 1) (c := s) (d := y₀)
    simp only [mul_zero, zero_add, mul_one] at key
    rw [key]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    rw [add_comm s y₀]
  have h_seg_CD : segmentIntegral C D g =
      -(∫ x : ℝ in x₀..x₀ + s, g (x + ((y₀ + s : ℝ) : ℂ) * Complex.I)) := by
    unfold segmentIntegral
    rw [hDC]
    have hC_eq : C = ((x₀ + s : ℝ) : ℂ) + ((y₀ + s : ℝ) : ℂ) * Complex.I := by
      rw [hC_def]; exact Complex.mk_eq_add_mul_I (x₀ + s) (y₀ + s)
    have hrewrite : ∀ t : ℝ,
        g (C + (t : ℂ) * (-(s : ℂ))) * (-(s : ℂ)) =
        (-s : ℝ) • g (((-s * t + (x₀ + s) : ℝ) : ℂ) + ((y₀ + s : ℝ) : ℂ) * Complex.I) := by
      intro t
      rw [Complex.real_smul]
      have heq : g (C + (t : ℂ) * (-(s : ℂ))) =
             g (((-s * t + (x₀ + s) : ℝ) : ℂ) + ((y₀ + s : ℝ) : ℂ) * Complex.I) := by
        congr 1
        rw [hC_eq]
        push_cast
        ring
      rw [heq]
      push_cast
      ring
    simp_rw [hrewrite]
    rw [intervalIntegral.integral_smul]
    have key := intervalIntegral.smul_integral_comp_mul_add
      (f := fun x : ℝ => g ((x : ℂ) + ((y₀ + s : ℝ) : ℂ) * Complex.I))
      (a := 0) (b := 1) (c := -s) (d := x₀ + s)
    simp only [mul_zero, zero_add, mul_one] at key
    rw [key]
    rw [intervalIntegral.integral_symm]
    push_cast
    have hx_swap : x₀ + s = s + x₀ := by ring
    rw [hx_swap]
    have hcoll : -s + (s + x₀) = x₀ := by ring
    rw [hcoll]
  have h_seg_DA : segmentIntegral D A g =
      -(Complex.I * ∫ y : ℝ in y₀..y₀ + s, g ((x₀ : ℂ) + y * Complex.I)) := by
    unfold segmentIntegral
    rw [hAD]
    have hD_eq : D = (x₀ : ℂ) + ((y₀ + s : ℝ) : ℂ) * Complex.I := by
      rw [hD_def]; exact Complex.mk_eq_add_mul_I x₀ (y₀ + s)
    have hrewrite : ∀ t : ℝ,
        g (D + (t : ℂ) * (-((s : ℂ) * Complex.I))) * (-((s : ℂ) * Complex.I)) =
        (-s : ℝ) • (Complex.I * g ((x₀ : ℂ) + ((-s * t + (y₀ + s) : ℝ) : ℂ) * Complex.I)) := by
      intro t
      rw [Complex.real_smul]
      have heq : g (D + (t : ℂ) * (-((s : ℂ) * Complex.I))) =
             g ((x₀ : ℂ) + ((-s * t + (y₀ + s) : ℝ) : ℂ) * Complex.I) := by
        congr 1
        rw [hD_eq]
        push_cast
        ring
      rw [heq]
      push_cast
      ring
    simp_rw [hrewrite]
    rw [intervalIntegral.integral_smul]
    have key := intervalIntegral.smul_integral_comp_mul_add
      (f := fun y : ℝ => Complex.I * g ((x₀ : ℂ) + (y : ℝ) * Complex.I))
      (a := 0) (b := 1) (c := -s) (d := y₀ + s)
    simp only [mul_zero, zero_add, mul_one] at key
    rw [key]
    rw [intervalIntegral.integral_symm]
    rw [intervalIntegral.integral_const_mul]
    push_cast
    ring_nf
  -- Build the closed and open rectangles.
  set R : Set ℂ := Set.Icc x₀ (x₀ + s) ×ℂ Set.Icc y₀ (y₀ + s) with hR_def
  set Rint : Set ℂ := Set.Ioo x₀ (x₀ + s) ×ℂ Set.Ioo y₀ (y₀ + s) with hRint_def
  have hR_sub_U : R ⊆ U := by
    intro w hw
    simp only [hR_def, Complex.reProdIm, Set.mem_inter_iff, Set.mem_preimage] at hw
    exact hrect_sub_U w hw.1 hw.2
  have hRint_sub_R : Rint ⊆ R := by
    intro w hw
    simp only [hRint_def, Complex.reProdIm, Set.mem_inter_iff, Set.mem_preimage] at hw
    simp only [hR_def, Complex.reProdIm, Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨Set.Ioo_subset_Icc_self hw.1, Set.Ioo_subset_Icc_self hw.2⟩
  have hRint_sub_U : Rint ⊆ U := hRint_sub_R.trans hR_sub_U
  -- Continuity on the uIcc rectangle.
  have hx_le : x₀ ≤ x₀ + s := by linarith
  have hy_le : y₀ ≤ y₀ + s := by linarith
  have huIcc_x : Set.uIcc x₀ (x₀ + s) = Set.Icc x₀ (x₀ + s) := Set.uIcc_of_le hx_le
  have huIcc_y : Set.uIcc y₀ (y₀ + s) = Set.Icc y₀ (y₀ + s) := Set.uIcc_of_le hy_le
  have hmin_x : min x₀ (x₀ + s) = x₀ := min_eq_left hx_le
  have hmax_x : max x₀ (x₀ + s) = x₀ + s := max_eq_right hx_le
  have hmin_y : min y₀ (y₀ + s) = y₀ := min_eq_left hy_le
  have hmax_y : max y₀ (y₀ + s) = y₀ + s := max_eq_right hy_le
  have hg_cont_R : ContinuousOn g R := hg_cont.mono hR_sub_U
  have hg_cont_R' :
      ContinuousOn g (Set.uIcc x₀ (x₀ + s) ×ℂ Set.uIcc y₀ (y₀ + s)) := by
    rw [huIcc_x, huIcc_y]; exact hg_cont_R
  have hg_diff_Hd : ∀ x ∈ Set.Ioo (min x₀ (x₀ + s)) (max x₀ (x₀ + s)) ×ℂ
                          Set.Ioo (min y₀ (y₀ + s)) (max y₀ (y₀ + s)) \ ({z} : Set ℂ),
                    DifferentiableAt ℂ g x := by
    intro x hx
    rw [hmin_x, hmax_x, hmin_y, hmax_y] at hx
    have hx_in : x ∈ Rint := hx.1
    have hx_ne : x ≠ z := hx.2
    have hx_in_U_diff : x ∈ U \ {z} := ⟨hRint_sub_U hx_in, hx_ne⟩
    apply (hg_diff x hx_in_U_diff).differentiableAt
    have hU_diff_open : IsOpen (U \ ({z} : Set ℂ)) := hU.sdiff isClosed_singleton
    exact hU_diff_open.mem_nhds hx_in_U_diff
  -- Apply Mathlib's Cauchy-Goursat theorem for a rectangle.
  have hAre : A.re = x₀ := by rw [hA_def]
  have hAim : A.im = y₀ := by rw [hA_def]
  have hCre : C.re = x₀ + s := by rw [hC_def]
  have hCim : C.im = y₀ + s := by rw [hC_def]
  have hgoursat := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    g A C ({z}) (Set.countable_singleton z)
    (by
      rw [hAre, hAim, hCre, hCim]
      exact hg_cont_R')
    (by
      rw [hAre, hAim, hCre, hCim]
      exact hg_diff_Hd)
  rw [hAre, hAim, hCre, hCim] at hgoursat
  rw [h_seg_AB, h_seg_BC, h_seg_CD, h_seg_DA]
  rw [smul_eq_mul, smul_eq_mul] at hgoursat
  linear_combination hgoursat

/-- Auxiliary: segment integral of `1/(ζ - z)` along a segment from `a` to `b`,
when the entire shifted segment `{(a-z) + t(b-a) : t ∈ [0,1]}` lies in
`Complex.slitPlane`, equals `Complex.log(b-z) - Complex.log(a-z)`. -/
private lemma segmentIntegral_inv_of_slitPlane
    (a b z : ℂ)
    (hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, (a - z) + (t : ℂ) * (b - a) ∈ Complex.slitPlane) :
    segmentIntegral a b (fun ζ => 1 / (ζ - z)) =
      Complex.log (b - z) - Complex.log (a - z) := by
  unfold segmentIntegral
  set f : ℝ → ℂ := fun t => Complex.log ((a - z) + (t : ℂ) * (b - a)) with hf_def
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt f (1 / ((a + (t : ℂ) * (b - a)) - z) * (b - a)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := by
      rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have hslit : (a - z) + (t : ℂ) * (b - a) ∈ Complex.slitPlane := hseg t ht'
    have hbase : HasDerivAt (fun t : ℝ => (a - z) + (t : ℂ) * (b - a)) (b - a) t := by
      have h1 : HasDerivAt (fun t : ℝ => (Complex.ofRealCLM t : ℂ))
          (Complex.ofRealCLM 1 : ℂ) t :=
        Complex.ofRealCLM.hasDerivAt
      have h1' : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) (1 : ℂ) t := by
        simpa using h1
      have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * (b - a)) (1 * (b - a)) t :=
        h1'.mul_const (b - a)
      have h3 : HasDerivAt (fun t : ℝ => (a - z) + (t : ℂ) * (b - a)) (0 + 1 * (b - a)) t :=
        (hasDerivAt_const t (a - z)).add h2
      simpa using h3
    have hlog := hbase.clog_real hslit
    convert hlog using 1
    have hne : (a - z) + (t : ℂ) * (b - a) ≠ 0 := Complex.slitPlane_ne_zero hslit
    have heq : (a + (t : ℂ) * (b - a)) - z = (a - z) + (t : ℂ) * (b - a) := by ring
    rw [heq]
    field_simp
  have hfa : f 0 = Complex.log (a - z) := by
    simp [hf_def]
  have hfb : f 1 = Complex.log (b - z) := by
    show Complex.log ((a - z) + ((1:ℝ) : ℂ) * (b - a)) = Complex.log (b - z)
    congr 1; push_cast; ring
  have hcont : ContinuousOn (fun t : ℝ => 1 / ((a + (t : ℂ) * (b - a)) - z) * (b - a))
      (Set.uIcc (0:ℝ) 1) := by
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := by
      rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have hslit := hseg t ht'
    have hne2 : (a - z) + (t : ℂ) * (b - a) ≠ 0 := Complex.slitPlane_ne_zero hslit
    have hne : (a + (t : ℂ) * (b - a)) - z ≠ 0 := by
      intro h; apply hne2; linear_combination h
    have h_inner : ContinuousAt (fun t : ℝ => (a + (t : ℂ) * (b - a)) - z) t :=
      ((continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const).continuousAt
    have h_inv : ContinuousAt (fun t : ℝ => 1 / ((a + (t : ℂ) * (b - a)) - z)) t :=
      (continuousAt_const.div h_inner hne)
    exact (h_inv.mul continuousAt_const).continuousWithinAt
  have hint : IntervalIntegrable
      (fun t : ℝ => 1 / ((a + (t : ℂ) * (b - a)) - z) * (b - a)) MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hFTC, hfb, hfa]

/-- Auxiliary "negated" variant: segment integral of `1/(ζ - z)` along a segment from
`a` to `b`, when the entire negated shifted segment `{-((a-z) + t(b-a)) : t ∈ [0,1]}`
lies in `Complex.slitPlane`, equals `Complex.log(-(b-z)) - Complex.log(-(a-z))`. -/
private lemma segmentIntegral_inv_of_neg_slitPlane
    (a b z : ℂ)
    (hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, -((a - z) + (t : ℂ) * (b - a)) ∈ Complex.slitPlane) :
    segmentIntegral a b (fun ζ => 1 / (ζ - z)) =
      Complex.log (-(b - z)) - Complex.log (-(a - z)) := by
  unfold segmentIntegral
  set f : ℝ → ℂ := fun t => Complex.log (-((a - z) + (t : ℂ) * (b - a))) with hf_def
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt f (1 / ((a + (t : ℂ) * (b - a)) - z) * (b - a)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := by
      rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have hslit : -((a - z) + (t : ℂ) * (b - a)) ∈ Complex.slitPlane := hseg t ht'
    have hbase : HasDerivAt (fun t : ℝ => -((a - z) + (t : ℂ) * (b - a))) (-(b - a)) t := by
      have h1 : HasDerivAt (fun t : ℝ => (Complex.ofRealCLM t : ℂ))
          (Complex.ofRealCLM 1 : ℂ) t :=
        Complex.ofRealCLM.hasDerivAt
      have h1' : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) (1 : ℂ) t := by
        simpa using h1
      have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * (b - a)) (1 * (b - a)) t :=
        h1'.mul_const (b - a)
      have h3 : HasDerivAt (fun t : ℝ => (a - z) + (t : ℂ) * (b - a)) (0 + 1 * (b - a)) t :=
        (hasDerivAt_const t (a - z)).add h2
      have h4 : HasDerivAt (fun t : ℝ => -((a - z) + (t : ℂ) * (b - a))) (-(0 + 1 * (b - a))) t :=
        h3.neg
      simpa using h4
    have hlog := hbase.clog_real hslit
    convert hlog using 1
    have hne : -((a - z) + (t : ℂ) * (b - a)) ≠ 0 := Complex.slitPlane_ne_zero hslit
    have hne' : (a - z) + (t : ℂ) * (b - a) ≠ 0 := by
      intro h; apply hne; rw [h]; ring
    have heq : (a + (t : ℂ) * (b - a)) - z = (a - z) + (t : ℂ) * (b - a) := by ring
    rw [heq]
    field_simp
  have hfa : f 0 = Complex.log (-(a - z)) := by
    simp [hf_def]
  have hfb : f 1 = Complex.log (-(b - z)) := by
    show Complex.log (-((a - z) + ((1:ℝ) : ℂ) * (b - a))) = Complex.log (-(b - z))
    congr 1; push_cast; ring
  have hcont : ContinuousOn (fun t : ℝ => 1 / ((a + (t : ℂ) * (b - a)) - z) * (b - a))
      (Set.uIcc (0:ℝ) 1) := by
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := by
      rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have hslit := hseg t ht'
    have hne : -((a - z) + (t : ℂ) * (b - a)) ≠ 0 := Complex.slitPlane_ne_zero hslit
    have hne' : (a - z) + (t : ℂ) * (b - a) ≠ 0 := by
      intro h; apply hne; rw [h]; ring
    have hne'' : (a + (t : ℂ) * (b - a)) - z ≠ 0 := by
      intro h; apply hne'; linear_combination h
    have h_inner : ContinuousAt (fun t : ℝ => (a + (t : ℂ) * (b - a)) - z) t :=
      ((continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const).continuousAt
    have h_inv : ContinuousAt (fun t : ℝ => 1 / ((a + (t : ℂ) * (b - a)) - z)) t :=
      (continuousAt_const.div h_inner hne'')
    exact (h_inv.mul continuousAt_const).continuousWithinAt
  have hint : IntervalIntegrable
      (fun t : ℝ => 1 / ((a + (t : ℂ) * (b - a)) - z) * (b - a)) MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hFTC, hfb, hfa]

/--
The sum of the four oriented `segmentIntegral`s of `ζ ↦ 1/(ζ - z)` around the
rectangle boundary equals `2πi`, when `z` lies in the open interior of the
closed rectangle `[x₀, x₀+s] × [y₀, y₀+s]`.
-/
private lemma rectangle_integral_inv_eq_two_pi_I
    (x₀ y₀ s : ℝ) (hs : 0 < s)
    (z : ℂ) (hz_int : z.re ∈ Set.Ioo x₀ (x₀ + s) ∧ z.im ∈ Set.Ioo y₀ (y₀ + s)) :
    segmentIntegral ⟨x₀, y₀⟩ ⟨x₀ + s, y₀⟩ (fun ζ => 1 / (ζ - z)) +
    segmentIntegral ⟨x₀ + s, y₀⟩ ⟨x₀ + s, y₀ + s⟩ (fun ζ => 1 / (ζ - z)) +
    segmentIntegral ⟨x₀ + s, y₀ + s⟩ ⟨x₀, y₀ + s⟩ (fun ζ => 1 / (ζ - z)) +
    segmentIntegral ⟨x₀, y₀ + s⟩ ⟨x₀, y₀⟩ (fun ζ => 1 / (ζ - z)) =
    2 * (Real.pi : ℂ) * Complex.I := by
  -- Setup: corner abbreviations.
  set A : ℂ := ⟨x₀, y₀⟩ with hA_def
  set B : ℂ := ⟨x₀ + s, y₀⟩ with hB_def
  set C : ℂ := ⟨x₀ + s, y₀ + s⟩ with hC_def
  set D : ℂ := ⟨x₀, y₀ + s⟩ with hD_def
  -- Decompose hypotheses.
  obtain ⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩⟩ := hz_int
  -- Segment AB: shifted segment = (A-z) + t·(B-A) stays in slitPlane (Im < 0).
  have hAB_slit : ∀ t ∈ Set.Icc (0:ℝ) 1,
      (A - z) + (t : ℂ) * (B - A) ∈ Complex.slitPlane := by
    intro t _
    have him : ((A - z) + (t : ℂ) * (B - A)).im = y₀ - z.im := by
      simp [hA_def, hB_def, Complex.add_im, Complex.mul_im, Complex.sub_im,
            Complex.ofReal_re]
    right
    rw [him]
    linarith
  -- Segment BC: Re = x₀ + s - z.re > 0.
  have hBC_slit : ∀ t ∈ Set.Icc (0:ℝ) 1,
      (B - z) + (t : ℂ) * (C - B) ∈ Complex.slitPlane := by
    intro t _
    have hre : ((B - z) + (t : ℂ) * (C - B)).re = (x₀ + s) - z.re := by
      simp [hB_def, hC_def, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im,
            Complex.ofReal_re, Complex.ofReal_im]
    left
    rw [hre]
    linarith
  -- Segment CD: Im = y₀ + s - z.im > 0.
  have hCD_slit : ∀ t ∈ Set.Icc (0:ℝ) 1,
      (C - z) + (t : ℂ) * (D - C) ∈ Complex.slitPlane := by
    intro t _
    have him : ((C - z) + (t : ℂ) * (D - C)).im = (y₀ + s) - z.im := by
      simp [hC_def, hD_def, Complex.add_im, Complex.mul_im, Complex.sub_im,
            Complex.ofReal_re]
    right
    rw [him]
    linarith
  -- Segment DA: shifted by -1 stays in slitPlane (Re of -(D-z + t(A-D)) > 0).
  have hDA_neg_slit : ∀ t ∈ Set.Icc (0:ℝ) 1,
      -((D - z) + (t : ℂ) * (A - D)) ∈ Complex.slitPlane := by
    intro t _
    have hre : (-((D - z) + (t : ℂ) * (A - D))).re = z.re - x₀ := by
      simp [hA_def, hD_def, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im,
            Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im]
    left
    rw [hre]
    linarith
  -- Apply the auxiliary lemmas.
  rw [segmentIntegral_inv_of_slitPlane A B z hAB_slit]
  rw [segmentIntegral_inv_of_slitPlane B C z hBC_slit]
  rw [segmentIntegral_inv_of_slitPlane C D z hCD_slit]
  rw [segmentIntegral_inv_of_neg_slitPlane D A z hDA_neg_slit]
  -- Compute the differences via arg analysis:
  --   A - z has Im < 0, so arg(-(A-z)) = arg(A-z) + π.
  --   D - z has Im > 0, so arg(-(D-z)) = arg(D-z) - π.
  have hAz_im : (A - z).im = y₀ - z.im := by
    simp [hA_def, Complex.sub_im]
  have hDz_im : (D - z).im = (y₀ + s) - z.im := by
    simp [hD_def, Complex.sub_im]
  have hAz_im_neg : (A - z).im < 0 := by rw [hAz_im]; linarith
  have hDz_im_pos : 0 < (D - z).im := by rw [hDz_im]; linarith
  have hargA : (-(A - z)).arg = (A - z).arg + Real.pi :=
    Complex.arg_neg_eq_arg_add_pi_of_im_neg hAz_im_neg
  have hargD : (-(D - z)).arg = (D - z).arg - Real.pi :=
    Complex.arg_neg_eq_arg_sub_pi_of_im_pos hDz_im_pos
  have hnormA : ‖-(A - z)‖ = ‖A - z‖ := by rw [norm_neg]
  have hnormD : ‖-(D - z)‖ = ‖D - z‖ := by rw [norm_neg]
  have hlogA_diff : Complex.log (-(A - z)) - Complex.log (A - z) = Real.pi * Complex.I := by
    rw [Complex.log, Complex.log]
    rw [hnormA, hargA]
    push_cast
    ring
  have hlogD_diff : Complex.log (D - z) - Complex.log (-(D - z)) = Real.pi * Complex.I := by
    rw [Complex.log, Complex.log]
    rw [hnormD, hargD]
    push_cast
    ring
  linear_combination hlogA_diff + hlogD_diff

/--
Cauchy's integral formula on a single rectangle with one pole inside
(sub-obligation 3 — the Mathlib gap).

For a function `f` holomorphic on an open neighborhood of a closed rectangle
`R = [x₀, x₀+s] × [y₀, y₀+s]` and a point `z` in the open interior of `R`,
the line integral of `f(ζ)/(ζ - z)` along the positively oriented boundary
of `R` equals `2πi · f(z)`.

Glue proof: split `f(ζ)/(ζ - z) = dslope f z ζ + f z · (1/(ζ - z))` on each
segment (which avoids `z` since `z` is interior). The `dslope` part has integral
`0` around the rectangle boundary by Cauchy-Goursat on `U \ {z}`
(`rectangle_holomorphic_part_integral_zero`), and the `1/(ζ - z)` part
contributes `2πi` (`rectangle_integral_inv_eq_two_pi_I`).
-/
private lemma rectangle_cauchy_with_pole
    {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (x₀ y₀ s : ℝ) (hs : 0 < s)
    (hrect_sub_U : ∀ w : ℂ, w.re ∈ Set.Icc x₀ (x₀ + s) →
                            w.im ∈ Set.Icc y₀ (y₀ + s) → w ∈ U)
    (z : ℂ) (hz_int : z.re ∈ Set.Ioo x₀ (x₀ + s) ∧ z.im ∈ Set.Ioo y₀ (y₀ + s)) :
    (segmentIntegral ⟨x₀, y₀⟩ ⟨x₀ + s, y₀⟩ (fun ζ => f ζ / (ζ - z)) +
     segmentIntegral ⟨x₀ + s, y₀⟩ ⟨x₀ + s, y₀ + s⟩ (fun ζ => f ζ / (ζ - z)) +
     segmentIntegral ⟨x₀ + s, y₀ + s⟩ ⟨x₀, y₀ + s⟩ (fun ζ => f ζ / (ζ - z)) +
     segmentIntegral ⟨x₀, y₀ + s⟩ ⟨x₀, y₀⟩ (fun ζ => f ζ / (ζ - z)))
    = 2 * (Real.pi : ℂ) * Complex.I * f z := by
  -- Strategy: split f(ζ)/(ζ-z) = dslope f z ζ + f(z) * (1/(ζ-z)) on each segment.
  -- The dslope part has integral 0 by Goursat; the 1/(ζ-z) part is 2πi.
  set A : ℂ := ⟨x₀, y₀⟩ with hA
  set B : ℂ := ⟨x₀ + s, y₀⟩ with hB
  set C : ℂ := ⟨x₀ + s, y₀ + s⟩ with hC
  set D : ℂ := ⟨x₀, y₀ + s⟩ with hD
  -- z is in U (open interior ⊆ closed rectangle ⊆ U).
  have hzU : z ∈ U :=
    hrect_sub_U z ⟨le_of_lt hz_int.1.1, le_of_lt hz_int.1.2⟩
                  ⟨le_of_lt hz_int.2.1, le_of_lt hz_int.2.2⟩
  have hf_diff_z : DifferentiableAt ℂ f z :=
    hf.differentiableAt (hU.mem_nhds hzU)
  -- Pointwise identity: f(ζ)/(ζ - z) = dslope f z ζ + f z * (1/(ζ - z)).
  have key_pointwise : ∀ ζ : ℂ, ζ ≠ z →
      f ζ / (ζ - z) = dslope f z ζ + f z * (1 / (ζ - z)) := by
    intro ζ hζ
    rw [dslope_of_ne f hζ, slope_def_field]
    have hne : ζ - z ≠ 0 := sub_ne_zero.mpr hζ
    field_simp
    ring
  -- Each segment avoids z.
  have hAB_avoid : ∀ t : ℝ, A + (t : ℂ) * (B - A) ≠ z := by
    intro t hc
    have him : (A + (t : ℂ) * (B - A)).im = y₀ := by
      simp [hA, hB, Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_im]
    have hzy : z.im ≠ y₀ := ne_of_gt hz_int.2.1
    apply hzy
    rw [← hc, him]
  have hBC_avoid : ∀ t : ℝ, B + (t : ℂ) * (C - B) ≠ z := by
    intro t hc
    have hre : (B + (t : ℂ) * (C - B)).re = x₀ + s := by
      simp [hB, hC, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.sub_im]
    have hzx : z.re ≠ x₀ + s := ne_of_lt hz_int.1.2
    apply hzx
    rw [← hc, hre]
  have hCD_avoid : ∀ t : ℝ, C + (t : ℂ) * (D - C) ≠ z := by
    intro t hc
    have him : (C + (t : ℂ) * (D - C)).im = y₀ + s := by
      simp [hC, hD, Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_im]
    have hzy : z.im ≠ y₀ + s := ne_of_lt hz_int.2.2
    apply hzy
    rw [← hc, him]
  have hDA_avoid : ∀ t : ℝ, D + (t : ℂ) * (A - D) ≠ z := by
    intro t hc
    have hre : (D + (t : ℂ) * (A - D)).re = x₀ := by
      simp [hD, hA, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.sub_im]
    have hzx : z.re ≠ x₀ := ne_of_gt hz_int.1.1
    apply hzx
    rw [← hc, hre]
  -- Each segment lies in U (it's in the closed rectangle).
  have hAB_in_U : ∀ t ∈ Set.Icc (0:ℝ) 1, A + (t : ℂ) * (B - A) ∈ U := by
    intro t ht
    apply hrect_sub_U
    · have hre_eq : (A + (t : ℂ) * (B - A)).re = x₀ + t * s := by
        simp [hA, hB, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
              Complex.ofReal_im]
      rw [hre_eq]
      refine ⟨?_, ?_⟩
      · linarith [mul_nonneg ht.1 hs.le]
      · have : t * s ≤ 1 * s := mul_le_mul_of_nonneg_right ht.2 hs.le
        linarith
    · have him_eq : (A + (t : ℂ) * (B - A)).im = y₀ := by
        simp [hA, hB, Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_im]
      rw [him_eq]
      exact ⟨le_refl _, by linarith⟩
  have hBC_in_U : ∀ t ∈ Set.Icc (0:ℝ) 1, B + (t : ℂ) * (C - B) ∈ U := by
    intro t ht
    apply hrect_sub_U
    · have hre_eq : (B + (t : ℂ) * (C - B)).re = x₀ + s := by
        simp [hB, hC, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
              Complex.ofReal_im]
      rw [hre_eq]
      exact ⟨by linarith, le_refl _⟩
    · have him_eq : (B + (t : ℂ) * (C - B)).im = y₀ + t * s := by
        simp [hB, hC, Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_im]
      rw [him_eq]
      refine ⟨?_, ?_⟩
      · linarith [mul_nonneg ht.1 hs.le]
      · have : t * s ≤ 1 * s := mul_le_mul_of_nonneg_right ht.2 hs.le
        linarith
  have hCD_in_U : ∀ t ∈ Set.Icc (0:ℝ) 1, C + (t : ℂ) * (D - C) ∈ U := by
    intro t ht
    apply hrect_sub_U
    · have hre_eq : (C + (t : ℂ) * (D - C)).re = (x₀ + s) - t * s := by
        simp [hC, hD, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
              Complex.ofReal_im]
        ring
      rw [hre_eq]
      refine ⟨?_, ?_⟩
      · have : t * s ≤ 1 * s := mul_le_mul_of_nonneg_right ht.2 hs.le
        linarith
      · linarith [mul_nonneg ht.1 hs.le]
    · have him_eq : (C + (t : ℂ) * (D - C)).im = y₀ + s := by
        simp [hC, hD, Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_im]
      rw [him_eq]
      exact ⟨by linarith, le_refl _⟩
  have hDA_in_U : ∀ t ∈ Set.Icc (0:ℝ) 1, D + (t : ℂ) * (A - D) ∈ U := by
    intro t ht
    apply hrect_sub_U
    · have hre_eq : (D + (t : ℂ) * (A - D)).re = x₀ := by
        simp [hD, hA, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
              Complex.ofReal_im]
      rw [hre_eq]
      exact ⟨le_refl _, by linarith⟩
    · have him_eq : (D + (t : ℂ) * (A - D)).im = (y₀ + s) - t * s := by
        simp [hD, hA, Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_im]
        ring
      rw [him_eq]
      refine ⟨?_, ?_⟩
      · have : t * s ≤ 1 * s := mul_le_mul_of_nonneg_right ht.2 hs.le
        linarith
      · linarith [mul_nonneg ht.1 hs.le]
  -- dslope f z is continuous on U.
  have hdslope_cont : ContinuousOn (dslope f z) U := by
    rw [continuousOn_dslope (hU.mem_nhds hzU)]
    exact ⟨hf.continuousOn, hf_diff_z⟩
  -- dslope f z is differentiable on U \ {z}.
  have hdslope_diff : DifferentiableOn ℂ (dslope f z) (U \ {z}) := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    have hwne : w ≠ z := hw.2
    have hwU : w ∈ U := hw.1
    have hne_nhds : ∀ᶠ ζ in nhds w, ζ ≠ z := eventually_ne_nhds hwne
    have h_evEq : (fun ζ : ℂ => (ζ - z)⁻¹ * (f ζ - f z)) =ᶠ[nhds w] dslope f z := by
      filter_upwards [hne_nhds] with ζ hζ
      rw [dslope_of_ne f hζ, slope_def_field, div_eq_inv_mul]
    have hg_diff_at_w : DifferentiableAt ℂ (fun ζ : ℂ => (ζ - z)⁻¹ * (f ζ - f z)) w := by
      apply DifferentiableAt.mul
      · apply DifferentiableAt.inv
        · exact differentiableAt_id.sub_const z
        · exact sub_ne_zero.mpr hwne
      · exact (hf.differentiableAt (hU.mem_nhds hwU)).sub_const (f z)
    exact h_evEq.differentiableAt_iff.mp hg_diff_at_w
  -- Parametrisation map is continuous as a function ℝ → ℂ.
  have hparam_cont : ∀ (a b : ℂ), Continuous (fun t : ℝ => a + (t : ℂ) * (b - a)) :=
    fun a b =>
      continuous_const.add ((Complex.continuous_ofReal).mul continuous_const)
  -- Continuity of dslope f z composed with each segment parametrisation.
  have hdslope_cont_seg : ∀ (a b : ℂ), (∀ t ∈ Set.Icc (0:ℝ) 1, a + (t : ℂ) * (b - a) ∈ U) →
      ContinuousOn (fun t : ℝ => dslope f z (a + (t : ℂ) * (b - a))) (Set.Icc (0:ℝ) 1) :=
    fun a b h_in_U => hdslope_cont.comp (hparam_cont a b).continuousOn h_in_U
  -- Continuity of 1/(ζ - z) composed with each segment parametrisation.
  have hinv_cont_seg : ∀ (a b : ℂ), (∀ t : ℝ, a + (t : ℂ) * (b - a) ≠ z) →
      ContinuousOn (fun t : ℝ => 1 / ((a + (t : ℂ) * (b - a)) - z)) (Set.Icc (0:ℝ) 1) := by
    intro a b h_avoid
    apply ContinuousOn.div continuousOn_const
    · exact ((hparam_cont a b).sub continuous_const).continuousOn
    · intro t _
      exact sub_ne_zero.mpr (h_avoid t)
  -- Helper: split each segment integral into the dslope part and the f(z)·1/(ζ-z) part.
  have seg_split : ∀ (a b : ℂ),
      (∀ t : ℝ, a + (t : ℂ) * (b - a) ≠ z) →
      (∀ t ∈ Set.Icc (0:ℝ) 1, a + (t : ℂ) * (b - a) ∈ U) →
      segmentIntegral a b (fun ζ => f ζ / (ζ - z)) =
        segmentIntegral a b (dslope f z) +
          f z * segmentIntegral a b (fun ζ => 1 / (ζ - z)) := by
    intro a b h_avoid h_in_U
    unfold segmentIntegral
    have eq_int : ∀ t ∈ Set.uIcc (0:ℝ) 1,
        (fun ζ : ℂ => f ζ / (ζ - z)) (a + (t : ℂ) * (b - a)) * (b - a) =
        (dslope f z) (a + (t : ℂ) * (b - a)) * (b - a) +
          f z * ((fun ζ : ℂ => 1 / (ζ - z)) (a + (t : ℂ) * (b - a)) * (b - a)) := by
      intro t _
      have h := key_pointwise (a + (t : ℂ) * (b - a)) (h_avoid t)
      simp only [h]
      ring
    rw [intervalIntegral.integral_congr eq_int]
    have hi₁ : IntervalIntegrable (fun t : ℝ =>
        (dslope f z) (a + (t : ℂ) * (b - a)) * (b - a))
        MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul
      · rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        exact hdslope_cont_seg a b h_in_U
      · exact continuousOn_const
    have hi₂ : IntervalIntegrable (fun t : ℝ =>
        f z * ((fun ζ : ℂ => 1 / (ζ - z)) (a + (t : ℂ) * (b - a)) * (b - a)))
        MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.mul
      · rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        exact hinv_cont_seg a b h_avoid
      · exact continuousOn_const
    rw [intervalIntegral.integral_add hi₁ hi₂]
    rw [← intervalIntegral.integral_const_mul]
  -- Apply seg_split to each of the four segments.
  have hAB := seg_split A B hAB_avoid hAB_in_U
  have hBC := seg_split B C hBC_avoid hBC_in_U
  have hCD := seg_split C D hCD_avoid hCD_in_U
  have hDA := seg_split D A hDA_avoid hDA_in_U
  rw [hAB, hBC, hCD, hDA]
  -- Now the sum has two pieces. Goursat for dslope; explicit 2πi for the inverse part.
  have h_dslope_zero :
      segmentIntegral A B (dslope f z) + segmentIntegral B C (dslope f z) +
        segmentIntegral C D (dslope f z) + segmentIntegral D A (dslope f z) = 0 := by
    have := rectangle_holomorphic_part_integral_zero hU x₀ y₀ s hs hrect_sub_U z hz_int
      hdslope_cont hdslope_diff
    simpa [hA, hB, hC, hD] using this
  have h_inv :
      segmentIntegral A B (fun ζ => 1 / (ζ - z)) +
        segmentIntegral B C (fun ζ => 1 / (ζ - z)) +
        segmentIntegral C D (fun ζ => 1 / (ζ - z)) +
        segmentIntegral D A (fun ζ => 1 / (ζ - z)) =
        2 * (Real.pi : ℂ) * Complex.I := by
    have := rectangle_integral_inv_eq_two_pi_I x₀ y₀ s hs z hz_int
    simpa [hA, hB, hC, hD] using this
  linear_combination h_dslope_zero + f z * h_inv

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

Glue proof: this is the full conjunction "segments in `U \ K`" + "Cauchy
formula". It is bundled together as a single `sorry`-stubbed obligation
`grid_sum_cancels`, because the segments witnessing the first conjunct and
the Cauchy formula on those same segments must use the *same* grid. The
genuine independent stubs above (`grid_squares_cover_compact`,
`grid_boundary_segments_off_K`, `rectangle_cauchy_with_pole`) are the
mathematical ingredients an eventual prover of `grid_sum_cancels` will use.
-/
private lemma grid_sum_cancels
    {K U : Set ℂ} {f : ℂ → ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : DifferentiableOn ℂ f U) :
    ∃ (m : ℕ) (A B : Fin m → ℂ),
      (∀ i, ∀ t ∈ Set.Icc (0:ℝ) 1, A i + (t : ℂ) * (B i - A i) ∈ U \ K) ∧
      ∀ z ∈ K,
        f z = (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
          ∑ i, segmentIntegral (A i) (B i) (fun ζ => f ζ / (ζ - z)) := by
  sorry

private lemma cauchy_grid_representation
    {K U : Set ℂ} {f : ℂ → ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : DifferentiableOn ℂ f U) :
    ∃ (m : ℕ) (A B : Fin m → ℂ),
      (∀ i, ∀ t ∈ Set.Icc (0:ℝ) 1, A i + (t : ℂ) * (B i - A i) ∈ U \ K) ∧
      ∀ z ∈ K,
        f z = (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
          ∑ i, segmentIntegral (A i) (B i) (fun ζ => f ζ / (ζ - z)) :=
  grid_sum_cancels hK hU hKU hf

/--
Uniform parametric Riemann-sum approximation of a segment integral (sub-lemma 2).

For an oriented segment whose image is disjoint from a compact set `K` and a
function `g` continuous on that image, the parametric contour-integral functional
`z ↦ (1/(2πi)) · ∫_{a → b} g(ζ)/(ζ - z) dζ` is uniformly approximated on `K` by
finite pole-sums `∑ⱼ cⱼ/(z - aⱼ)` whose poles `aⱼ` lie on the segment image.
-/
/-- Generic uniform Riemann-sum approximation: for a continuous function
`F : ℝ × ℂ → ℂ` and a compact `Z ⊆ ℂ`, the left-endpoint Riemann sum
`(1/N) ∑_{j<N} F(j/N, z)` approximates `∫₀¹ F(t, z) dt` uniformly in `z ∈ Z`. -/
private lemma riemann_sum_uniform_approx_continuous_param
    {Z : Set ℂ} (hZ : IsCompact Z)
    (F : ℝ → ℂ → ℂ)
    (hF : ContinuousOn (fun p : ℝ × ℂ => F p.1 p.2) (Set.Icc (0:ℝ) 1 ×ˢ Z)) :
    ∀ ε > 0, ∃ N : ℕ, 0 < N ∧ ∀ z ∈ Z,
      ‖(∑ j : Fin N, F (j / N) z / N) - ∫ t in (0:ℝ)..1, F t z‖ < ε := by
  intro ε hε
  -- The product set is compact.
  have hprod : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ Z) := isCompact_Icc.prod hZ
  -- F is uniformly continuous on the product.
  have hUC : UniformContinuousOn (fun p : ℝ × ℂ => F p.1 p.2)
      (Set.Icc (0:ℝ) 1 ×ˢ Z) :=
    hprod.uniformContinuousOn_of_continuous hF
  -- Get δ from uniform continuity for the target ε' = ε/2.
  have hε2 : (0:ℝ) < ε / 2 := by linarith
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨δ, hδpos, hδ⟩ := hUC (ε / 2) hε2
  -- Pick N large enough that 1/N < δ.
  obtain ⟨N, hN_pos, hN_lt⟩ : ∃ N : ℕ, 0 < N ∧ (1 / (N : ℝ)) < δ := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
    refine ⟨N + 1, Nat.succ_pos N, ?_⟩
    have hN1 : (1:ℝ) / δ < N + 1 := lt_of_lt_of_le hN (by exact_mod_cast Nat.le_succ N)
    have hNpos : (0:ℝ) < (N : ℝ) + 1 := by positivity
    rw [div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hδpos] at hN1
    linarith
  refine ⟨N, hN_pos, ?_⟩
  intro z hz
  -- Define I_j(z) = ∫ from j/N to (j+1)/N of F(t, z) dt.
  -- Then ∑ I_j = ∫₀¹ F.
  set t_node : ℕ → ℝ := fun k => (k : ℝ) / N with ht_node_def
  have ht_node_zero : t_node 0 = 0 := by simp [ht_node_def]
  have ht_node_N : t_node N = 1 := by
    simp [ht_node_def]
    field_simp
  -- For each j, F(·, z) is integrable on [j/N, (j+1)/N].
  have hF_cont_z : ContinuousOn (fun t : ℝ => F t z) (Set.Icc (0:ℝ) 1) := by
    have hz_mem : (fun t : ℝ => (t, z)) '' Set.Icc (0:ℝ) 1 ⊆
        Set.Icc (0:ℝ) 1 ×ˢ Z := by
      rintro p ⟨t, ht, rfl⟩
      exact ⟨ht, hz⟩
    intro t ht
    have hcont_prod : ContinuousOn (fun t : ℝ => ((t, z) : ℝ × ℂ)) (Set.Icc (0:ℝ) 1) :=
      (continuous_id.prodMk continuous_const).continuousOn
    have := (hF.comp hcont_prod hz_mem) t ht
    exact this
  have hF_int01 : IntervalIntegrable (fun t : ℝ => F t z) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact hF_cont_z
  -- Each subinterval is integrable.
  have h_step_le : ∀ k : ℕ, k ≤ N → t_node k ≤ t_node (k + 1) := by
    intro k _
    apply div_le_div_of_nonneg_right _ (by exact_mod_cast hN_pos)
    exact_mod_cast Nat.le_succ k
  have h_step_in_Icc : ∀ k : ℕ, k ≤ N → ∀ t ∈ Set.Icc (t_node k) (t_node (k+1)),
      t ∈ Set.Icc (0:ℝ) 1 := by
    intro k hk t ht
    refine ⟨?_, ?_⟩
    · have h1 : (0:ℝ) ≤ t_node k := by
        apply div_nonneg (by exact_mod_cast Nat.zero_le k) (by exact_mod_cast hN_pos.le)
      linarith [ht.1]
    · have h2 : t_node (k+1) ≤ 1 := by
        have hkN : (k:ℝ) + 1 ≤ N := by exact_mod_cast hk
        rw [ht_node_def]
        push_cast
        rw [div_le_one (by exact_mod_cast hN_pos)]
        linarith
      linarith [ht.2]
  have h_subint : ∀ k < N, IntervalIntegrable (fun t : ℝ => F t z)
      MeasureTheory.volume (t_node k) (t_node (k+1)) := by
    intro k hk
    apply ContinuousOn.intervalIntegrable
    have hsub : Set.uIcc (t_node k) (t_node (k+1)) ⊆ Set.Icc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (h_step_le k hk.le)]
      intro t ht
      exact h_step_in_Icc k hk.le t ht
    exact hF_cont_z.mono hsub
  -- Integral equals the sum of subinterval integrals.
  have h_integral_split :
      ∫ t in (0:ℝ)..1, F t z =
        ∑ k ∈ Finset.range N, ∫ t in t_node k..t_node (k+1), F t z := by
    rw [← ht_node_zero, ← ht_node_N]
    exact (intervalIntegral.sum_integral_adjacent_intervals h_subint).symm
  -- For each j, the constant value F(j/N, z)/N equals the integral of F(j/N, z)/N over [j/N, (j+1)/N].
  have h_const_int : ∀ k < N, F (t_node k) z / N =
      ∫ _ in t_node k..t_node (k+1), F (t_node k) z := by
    intro k hk
    rw [intervalIntegral.integral_const]
    have : t_node (k+1) - t_node k = (1:ℝ) / N := by
      rw [ht_node_def]
      push_cast
      field_simp
    rw [this]
    rw [smul_eq_mul]
    ring
  -- The sum of constants equals the sum of integrals.
  have h_sum_const :
      ∑ j : Fin N, F (j / N) z / N =
        ∑ k ∈ Finset.range N, ∫ _ in t_node k..t_node (k+1), F (t_node k) z := by
    rw [Finset.sum_range fun k => ∫ _ in t_node k..t_node (k+1), F (t_node k) z]
    apply Finset.sum_congr rfl
    intro k _
    have hk : (k : ℕ) < N := k.isLt
    rw [← h_const_int k hk]
    rfl
  -- Compute the difference as a single integral.
  rw [h_sum_const, h_integral_split, ← Finset.sum_sub_distrib]
  -- Now we have sum over k of (∫ ... constant - ∫ ... variable).
  -- Bound by triangle inequality: |sum| ≤ sum |...| ≤ N * (1/N) * (ε/2) = ε/2 < ε.
  have h_diff_bound : ∀ k ∈ Finset.range N,
      ‖(∫ _ in t_node k..t_node (k+1), F (t_node k) z) -
       (∫ t in t_node k..t_node (k+1), F t z)‖ ≤ (ε/2) * (1/N) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [← intervalIntegral.integral_sub (by
        apply ContinuousOn.intervalIntegrable
        apply continuousOn_const) (h_subint k hk)]
    -- bound by uniform continuity
    have hbound : ∀ t ∈ Set.uIcc (t_node k) (t_node (k+1)),
        ‖F (t_node k) z - F t z‖ ≤ ε / 2 := by
      intro t ht
      rw [Set.uIcc_of_le (h_step_le k hk.le)] at ht
      have htInIcc : t ∈ Set.Icc (0:ℝ) 1 := h_step_in_Icc k hk.le t ht
      have hk_in_Icc : t_node k ∈ Set.Icc (0:ℝ) 1 := by
        refine ⟨?_, ?_⟩
        · exact div_nonneg (by exact_mod_cast Nat.zero_le k) (by exact_mod_cast hN_pos.le)
        · rw [ht_node_def]
          rw [div_le_one (by exact_mod_cast hN_pos)]
          exact_mod_cast hk.le
      -- compute distance ≤ 1/N < δ
      have hdist : dist ((t_node k, z) : ℝ × ℂ) ((t, z) : ℝ × ℂ) < δ := by
        rw [Prod.dist_eq]
        simp
        have hdtt : dist (t_node k) t ≤ 1 / N := by
          rw [Real.dist_eq, abs_le]
          constructor
          · have : t - t_node k ≤ t_node (k+1) - t_node k := by linarith [ht.2]
            have h2 : t_node (k+1) - t_node k = 1 / N := by
              rw [ht_node_def]; push_cast; field_simp
            linarith
          · linarith [ht.1]
        linarith
      have hp1 : (t_node k, z) ∈ Set.Icc (0:ℝ) 1 ×ˢ Z := ⟨hk_in_Icc, hz⟩
      have hp2 : (t, z) ∈ Set.Icc (0:ℝ) 1 ×ˢ Z := ⟨htInIcc, hz⟩
      have := hδ (t_node k, z) hp1 (t, z) hp2 hdist
      simp at this
      rw [dist_eq_norm] at this
      linarith [this.le]
    have hlen : |t_node (k+1) - t_node k| = 1 / N := by
      have : t_node (k+1) - t_node k = (1:ℝ) / N := by
        rw [ht_node_def]; push_cast; field_simp
      rw [this]
      rw [abs_of_pos]
      apply div_pos one_pos (by exact_mod_cast hN_pos)
    calc ‖∫ t in t_node k..t_node (k+1), F (t_node k) z - F t z‖
        ≤ (ε / 2) * |t_node (k+1) - t_node k| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbound
      _ = (ε / 2) * (1 / N) := by rw [hlen]
  -- Triangle inequality.
  have hsum_bound :
      ‖∑ k ∈ Finset.range N,
        ((∫ _ in t_node k..t_node (k+1), F (t_node k) z) -
         (∫ t in t_node k..t_node (k+1), F t z))‖ ≤
      ∑ k ∈ Finset.range N, (ε/2) * (1/N) := by
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum h_diff_bound
  have hsum_eq : ∑ _k ∈ Finset.range N, (ε/2) * (1/(N:ℝ)) = ε/2 := by
    rw [Finset.sum_const]
    simp [Finset.card_range]
    field_simp
  rw [hsum_eq] at hsum_bound
  linarith

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
  intro ε hε
  -- The integrand kernel F(t, z) = g(γ(t)) * (b-a) / (γ(t) - z), where γ(t) = a + t(b-a).
  set γ : ℝ → ℂ := fun t => a + (t : ℂ) * (b - a) with hγ_def
  -- F : ℝ → ℂ → ℂ
  set F : ℝ → ℂ → ℂ := fun t z => g (γ t) * (b - a) / (γ t - z) with hF_def
  -- Step 1: γ is continuous.
  have hγ_cont : Continuous γ := by
    refine Continuous.add continuous_const ?_
    exact (Complex.continuous_ofReal.mul continuous_const)
  -- Step 2: The segment image is compact.
  have hΓ_compact : IsCompact (γ '' Set.Icc (0:ℝ) 1) :=
    isCompact_Icc.image hγ_cont
  -- Step 3: The segment image is disjoint from K.
  have hΓK_disj : Disjoint (γ '' Set.Icc (0:ℝ) 1) K := by
    rw [Set.disjoint_iff]
    rintro x ⟨⟨t, ht, rfl⟩, hxK⟩
    exact h_seg_off_K t ht hxK
  -- Step 4: K is closed (compact in Hausdorff space).
  have hK_closed : IsClosed K := hK.isClosed
  -- Step 5: positive distance lower bound.
  obtain ⟨r, hr_pos, hr_lt⟩ := Metric.exists_pos_forall_lt_edist hΓ_compact hK_closed hΓK_disj
  -- Convert to a usable distance form: ∀ p ∈ Γ, ∀ q ∈ K, ‖p - q‖ ≥ r.
  have hdist_lower : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z ∈ K, (r : ℝ) ≤ ‖γ t - z‖ := by
    intro t ht z hz
    have := hr_lt (γ t) ⟨t, ht, rfl⟩ z hz
    have h1 : (edist (γ t) z).toReal = dist (γ t) z := by
      rw [edist_dist]
      rw [ENNReal.toReal_ofReal dist_nonneg]
    have hcoer : ((r : ℝ≥0∞)).toReal = (r : ℝ) := by simp
    have hlt : (r : ℝ≥0∞) < edist (γ t) z := this
    have hedist_lt_top : edist (γ t) z < ⊤ := edist_lt_top _ _
    have := (ENNReal.toReal_lt_toReal (by exact_mod_cast (ne_top_iff_ne_top_of_lt hlt).mpr
      hedist_lt_top.ne) hedist_lt_top.ne).mpr hlt
    rw [hcoer, h1] at this
    rw [dist_eq_norm] at this
    linarith
  -- Step 6: F is continuous on [0,1] × K.
  have hF_cont : ContinuousOn (fun p : ℝ × ℂ => F p.1 p.2) (Set.Icc (0:ℝ) 1 ×ˢ K) := by
    -- numerator g(γ(t)) * (b - a), continuous in (t, z), via g composed with continuous γ ∘ fst.
    -- denominator γ(t) - z, continuous and nonzero.
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    -- continuity of γ ∘ fst at p
    have hγp_cont : ContinuousAt (fun p : ℝ × ℂ => γ p.1) p :=
      (hγ_cont.continuousAt.comp continuous_fst.continuousAt)
    -- continuity of g at γ(p.1): g is continuous on the segment image.
    have hg_at : ContinuousWithinAt (fun p : ℝ × ℂ => g (γ p.1))
        (Set.Icc (0:ℝ) 1 ×ˢ K) p := by
      have h1 : γ p.1 ∈ γ '' Set.Icc (0:ℝ) 1 := ⟨p.1, hp1, rfl⟩
      have hg_at_γp := h_g_cont (γ p.1) h1
      -- ContinuousWithinAt g at γ p.1, restricted to image.
      -- Compose with continuous γ ∘ fst.
      have hcomp_in : ∀ q ∈ Set.Icc (0:ℝ) 1 ×ˢ K, γ q.1 ∈ γ '' Set.Icc (0:ℝ) 1 := by
        rintro q ⟨hq1, _⟩
        exact ⟨q.1, hq1, rfl⟩
      exact hg_at_γp.comp hγp_cont.continuousWithinAt hcomp_in
    -- continuity of denominator γ(t) - z.
    have hden_cont : ContinuousAt (fun p : ℝ × ℂ => γ p.1 - p.2) p := by
      exact hγp_cont.sub continuous_snd.continuousAt
    -- denominator nonzero
    have hden_ne : γ p.1 - p.2 ≠ 0 := by
      intro heq
      have : ‖γ p.1 - p.2‖ = 0 := by rw [heq]; simp
      have := hdist_lower p.1 hp1 p.2 hp2
      have hr_pos_real : (0:ℝ) < r := by exact_mod_cast hr_pos
      linarith
    -- combine.
    have h_num : ContinuousWithinAt (fun p : ℝ × ℂ => g (γ p.1) * (b - a))
        (Set.Icc (0:ℝ) 1 ×ˢ K) p :=
      hg_at.mul continuousWithinAt_const
    have h_quot : ContinuousWithinAt (fun p : ℝ × ℂ => g (γ p.1) * (b - a) / (γ p.1 - p.2))
        (Set.Icc (0:ℝ) 1 ×ˢ K) p :=
      h_num.div hden_cont.continuousWithinAt hden_ne
    exact h_quot
  -- Step 7: Apply the generic Riemann sum approximation lemma.
  -- Target ε' = ε * 2 * π (so that after multiplying by 1/(2π) we get ε).
  have h2pi_pos : (0:ℝ) < 2 * Real.pi := by positivity
  set ε' : ℝ := ε * (2 * Real.pi) with hε'_def
  have hε' : 0 < ε' := by
    rw [hε'_def]
    positivity
  obtain ⟨N, hN_pos, h_riemann⟩ :=
    riemann_sum_uniform_approx_continuous_param hK F hF_cont ε' hε'
  -- Step 8: define samples and coefficients.
  -- sample j = γ(j/N), coeff j = -(1/(2πi)) * g(γ(j/N)) * (b-a) / N.
  refine ⟨N, fun j => γ ((j : ℝ) / N),
    fun j => -(1 / (2 * (Real.pi : ℂ) * Complex.I)) * g (γ ((j : ℝ) / N)) * (b - a) / N, ?_, ?_⟩
  · -- samples are outside K.
    intro j
    have hj_in : ((j : ℝ) / N) ∈ Set.Icc (0:ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · exact div_nonneg (by exact_mod_cast (Nat.zero_le j.val)) (by exact_mod_cast hN_pos.le)
      · rw [div_le_one (by exact_mod_cast hN_pos)]
        exact_mod_cast (Nat.lt_succ_iff.mp (Nat.lt_succ_of_lt j.isLt)).trans_lt (Nat.lt_succ_self N) |>.le
    -- Actually simpler: j.val < N so j/N < 1 ≤ 1.
    have hjle : ((j : ℝ) / N) ∈ Set.Icc (0:ℝ) 1 := hj_in
    exact h_seg_off_K _ hjle
  · -- the bound
    intro z hz
    -- Compute the pole sum.
    have h_pole_eq :
        (∑ j : Fin N, (-(1 / (2 * (Real.pi : ℂ) * Complex.I)) *
              g (γ ((j : ℝ) / N)) * (b - a) / N) / (z - γ ((j : ℝ) / N))) =
        -(1 / (2 * (Real.pi : ℂ) * Complex.I)) *
          ∑ j : Fin N, g (γ ((j : ℝ) / N)) * (b - a) / (N * (z - γ ((j : ℝ) / N))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      field_simp
      ring
    -- Simplify -(.../N) / (z - x) = -(... / (N*(z-x))) = ... / (N*(x-z)) (sign flip).
    -- We want to relate this to (1/(2πi)) * (1/N) * ∑ g(γ(j/N))(b-a)/(γ(j/N) - z).
    -- Note: -1/(z - x) = 1/(x - z).
    have h_pole_eq2 :
        (∑ j : Fin N, (-(1 / (2 * (Real.pi : ℂ) * Complex.I)) *
              g (γ ((j : ℝ) / N)) * (b - a) / N) / (z - γ ((j : ℝ) / N))) =
        (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
          ∑ j : Fin N, F ((j : ℝ) / N) z / N := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hjle : ((j : ℝ) / N) ∈ Set.Icc (0:ℝ) 1 := by
        refine ⟨?_, ?_⟩
        · exact div_nonneg (by exact_mod_cast (Nat.zero_le j.val))
            (by exact_mod_cast hN_pos.le)
        · rw [div_le_one (by exact_mod_cast hN_pos)]
          exact_mod_cast j.isLt.le
      have hγ_ne : γ ((j : ℝ) / N) - z ≠ 0 := by
        intro heq
        have hzero : ‖γ ((j : ℝ) / N) - z‖ = 0 := by rw [heq]; simp
        have hge := hdist_lower _ hjle z hz
        have hrpos : (0:ℝ) < r := by exact_mod_cast hr_pos
        linarith
      have hzn : z - γ ((j : ℝ) / N) ≠ 0 := by
        intro heq
        apply hγ_ne
        linear_combination -heq
      have hN_ne : (N : ℂ) ≠ 0 := by exact_mod_cast hN_pos.ne'
      have h2πi_ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        apply mul_ne_zero
        · apply mul_ne_zero
          · exact two_ne_zero
          · exact_mod_cast Real.pi_ne_zero
        · exact Complex.I_ne_zero
      rw [hF_def]
      simp only
      field_simp
      ring
    -- segmentIntegral = ∫₀¹ g(γ(t)) (b - a) / (γ(t) - z) dt = ∫₀¹ F(t, z) dt.
    have h_segInt :
        segmentIntegral a b (fun ζ => g ζ / (ζ - z)) =
        ∫ t in (0:ℝ)..1, F t z := by
      unfold segmentIntegral
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      simp [hF_def, hγ_def]
      ring
    rw [h_pole_eq2, h_segInt]
    -- Now: |1/(2πi) * (Σ F(j/N, z)/N - ∫ F)| < ε.
    rw [← mul_sub]
    rw [norm_mul]
    have hnorm_inv : ‖(1 / (2 * (Real.pi : ℂ) * Complex.I))‖ = 1 / (2 * Real.pi) := by
      rw [norm_div, norm_one]
      rw [norm_mul, norm_mul]
      simp [Complex.norm_I, abs_of_pos (Real.pi_pos)]
    rw [hnorm_inv]
    have h_riem_z := h_riemann z hz
    have h_2pi_pos : (0:ℝ) < 2 * Real.pi := by positivity
    have h_2pi_ne : 2 * Real.pi ≠ 0 := ne_of_gt h_2pi_pos
    have : (1 / (2 * Real.pi)) *
        ‖(∑ j : Fin N, F ((j : ℝ) / N) z / N) - ∫ t in (0:ℝ)..1, F t z‖ <
        (1 / (2 * Real.pi)) * ε' := by
      apply mul_lt_mul_of_pos_left h_riem_z
      positivity
    have h_ε'_eq : (1 / (2 * Real.pi)) * ε' = ε := by
      rw [hε'_def]
      field_simp
    linarith

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
          have hm_nn : (0 : ℝ) ≤ (m : ℝ) := by positivity
          rw [mul_div_assoc', div_lt_iff₀ hm1_pos]
          nlinarith [hε, hm_nn]

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
