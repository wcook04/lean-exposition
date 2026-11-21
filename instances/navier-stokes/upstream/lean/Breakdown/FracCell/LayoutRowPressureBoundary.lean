import Breakdown.FracCell.LayoutRowValueModes
import Breakdown.FracCell.ModeVelSquare
import Breakdown.FracCell.LayoutRowPressureBoundaryParts

open MeasureTheory Set

noncomputable section

namespace Breakdown.FracInternal.LayoutRowPressureBoundary

open CellCert CellCert.CellFormula CellCert.CellAnalysis CellCert.CellAnalysis.CellScalars SteadyCert
  CellCert.Assembly LayoutRowPressureBoundaryParts

private theorem cyl_sub (r r' θ z z' : ℝ) : cylPoint r θ z - cylPoint r' θ z' = cylPoint (r - r') θ (z - z') := by
  ext i
  fin_cases i <;> simp [cylPoint] <;> ring

private theorem cyl_radius (r θ z : ℝ) (hr : 0 ≤ r) : CellAnalysis.cylRadius (cylPoint r θ z) = r := by
  unfold CellAnalysis.cylRadius
  simp [cylPoint]
  rw [show (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 by nlinarith [Real.sin_sq_add_cos_sq θ]]
  exact Real.sqrt_sq hr

private theorem cyl_height (r θ z : ℝ) : cylHeight (cylPoint r θ z) = z := by
  simp [cylHeight, cylPoint]

private theorem cyl_mem {K : CellBox} (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) (θ : ℝ) :
    cylPoint p.1 θ p.2 ∈ K.solid ∩ {y | 0 ≤ cylHeight y} := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
  have hr0 : 0 ≤ p.1 := le_trans hK.r_order.1 h1
  have hz0 : 0 ≤ p.2 := le_trans hK.z_order.1 h3
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [cyl_radius _ _ _ hr0]; exact h1
  · rw [cyl_radius _ _ _ hr0]; exact h2
  · rw [cyl_height, abs_of_nonneg hz0]; exact h3
  · rw [cyl_height, abs_of_nonneg hz0]; exact h4
  · show 0 ≤ cylHeight (cylPoint p.1 θ p.2)
    rw [cyl_height]; exact hz0

private theorem cyl_dist (r r' θ z z' : ℝ) :
    ‖cylPoint r θ z - cylPoint r' θ z'‖ ≤ 2 * dist (r, z) (r', z') := by
  rw [cyl_sub, ModeVelSquareInternal.cylPoint_norm, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  have ha := le_max_left |r - r'| |z - z'|
  have hb := le_max_right |r - r'| |z - z'|
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_abs (r - r'), sq_abs (z - z'), abs_nonneg (r - r'), abs_nonneg (z - z')]

private theorem cyl_cont (r z : ℝ) : Continuous fun θ : ℝ => cylPoint r θ z := by
  unfold cylPoint
  exact (((ModeVelSquareInternal.single_cont 0).comp (continuous_const.mul Real.continuous_cos)).add
    ((ModeVelSquareInternal.single_cont 1).comp (continuous_const.mul Real.continuous_sin))).add continuous_const

private theorem integrand_cont {v : Space → Space} {s : Set Space} (hv : ContinuousOn v s) {r z : ℝ}
    (hs : ∀ θ, cylPoint r θ z ∈ s) (w : ℝ) (i : Fin 3) :
    Continuous (fun θ : ℝ => Complex.exp (-(w * θ : ℝ) * Complex.I) * (frameVec θ (v (cylPoint r θ z)) i : ℂ)) := by
  have hc1 : Continuous (fun θ : ℝ => v (cylPoint r θ z)) := hv.comp_continuous (cyl_cont r z) hs
  have hc2 : Continuous (fun θ : ℝ => frameVec θ (v (cylPoint r θ z)) i) := by
    simp_rw [ModeVelSquareInternal.frameVec_eq]
    exact hc1.inner (ModeVelSquareInternal.frameUnit_cont i)
  have hc3 : Continuous (fun θ : ℝ => Complex.exp (-(w * θ : ℝ) * Complex.I)) := by fun_prop
  exact hc3.mul (Complex.continuous_ofReal.comp hc2)

private theorem integrand_diff {v : Space → Space} {s : Set Space} {L₀ : NNReal} (hv : LipschitzOnWith L₀ v s)
    {r z r' z' : ℝ} (hs : ∀ θ, cylPoint r θ z ∈ s) (hs' : ∀ θ, cylPoint r' θ z' ∈ s) (w : ℝ) (i : Fin 3) (θ : ℝ) :
    ‖Complex.exp (-(w * θ : ℝ) * Complex.I) * (frameVec θ (v (cylPoint r θ z)) i : ℂ) -
      Complex.exp (-(w * θ : ℝ) * Complex.I) * (frameVec θ (v (cylPoint r' θ z')) i : ℂ)‖ ≤
        (2 * L₀ : ℝ) * dist (r, z) (r', z') := by
  rw [← mul_sub, norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  have hlin : frameVec θ (v (cylPoint r θ z)) i - frameVec θ (v (cylPoint r' θ z')) i =
      frameVec θ (v (cylPoint r θ z) - v (cylPoint r' θ z')) i := by
    simp only [ModeVelSquareInternal.frameVec_eq, inner_sub_left]
  rw [hlin]
  refine (ModeVelSquareInternal.frameVec_abs _ _ _).trans ?_
  rw [← dist_eq_norm]
  refine (hv.dist_le_mul _ (hs θ) _ (hs' θ)).trans ?_
  rw [dist_eq_norm]
  have := cyl_dist r r' θ z z'
  have hL : (0 : ℝ) ≤ L₀ := L₀.2
  calc (L₀ : ℝ) * ‖cylPoint r θ z - cylPoint r' θ z'‖ ≤ L₀ * (2 * dist (r, z) (r', z')) :=
        mul_le_mul_of_nonneg_left this hL
    _ = (2 * L₀ : ℝ) * dist (r, z) (r', z') := by ring

private theorem mode_slope {v : Space → Space} {s : Set Space} {L₀ : NNReal} (hv : LipschitzOnWith L₀ v s)
    {T : Set (ℝ × ℝ)} (hT : ∀ p ∈ T, ∀ θ, cylPoint p.1 θ p.2 ∈ s) (m : ℕ) (n : ℤ) (i : Fin 3) :
    LipschitzOnWith (2 * L₀) (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 i) T := by
  refine LipschitzOnWith.of_dist_le_mul (fun p hp q hq => ?_)
  rw [dist_eq_norm]
  unfold modeVec
  rw [← mul_sub, ← intervalIntegral.integral_sub
    ((integrand_cont hv.continuousOn (hT p hp) (azimuth m n) i).intervalIntegrable _ _)
    ((integrand_cont hv.continuousOn (hT q hq) (azimuth m n) i).intervalIntegrable _ _), norm_mul]
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
    (fun θ _ => integrand_diff hv (hT p hp) (hT q hq) (azimuth m n) i θ)
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2 : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [sub_zero, abs_of_pos (by positivity)] at hI
  rw [h2]
  have hd : dist (p.1, p.2) (q.1, q.2) = dist p q := rfl
  rw [hd] at hI
  calc 1 / (2 * Real.pi) * ‖_‖ ≤ 1 / (2 * Real.pi) * ((2 * L₀ : ℝ) * dist p q * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = ((2 * L₀ : NNReal) : ℝ) * dist p q := by push_cast; field_simp

private theorem row_mode_slope {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {a : Fin N}
    (hD : IsCellData α c K S B Cl R) (hR : IsRowShape c K S R) (ha : a ∈ R.rowSet) (n : ℤ) (i : Fin 3) :
    ∃ C : NNReal, LipschitzOnWith C (fun p => rowModeVec c a n p i) K.rect := by
  obtain ⟨L₀, hL₀⟩ := hR.row_slope a ha
  exact ⟨2 * L₀, mode_slope hL₀ (fun p hp θ => cyl_mem hD.box hp θ) c.order n i⟩

private theorem deriv_int {u : ℝ → ℂ} {C : NNReal} (hu : LipschitzWith C u) (a b : ℝ) :
    IntervalIntegrable (deriv u) volume a b :=
  (intervalIntegrable_const (c := (C : ℝ))).mono_fun' (measurable_deriv u).aestronglyMeasurable
    (ae_of_all _ fun _ => norm_deriv_le_of_lipschitz hu)

private theorem part_ftc (L : ℂ →L[ℝ] ℝ) {u : ℝ → ℂ} {C : NNReal} (hu : LipschitzWith C u) (A o a b : ℝ) :
    L (∫ r in a..b, (((A : ℝ) : ℂ) * u r + (((r - o) * A : ℝ) : ℂ) * deriv u r)) =
      ((b - o) * A) * L (u b) - ((a - o) * A) * L (u a) := by
  have hcont : Continuous u := hu.continuous
  have hF : IntervalIntegrable (fun r => (((A : ℝ) : ℂ) * u r + (((r - o) * A : ℝ) : ℂ) * deriv u r)) volume a b := by
    refine IntervalIntegrable.add ?_ ?_
    · exact (continuous_const.mul hcont).intervalIntegrable _ _
    · exact (deriv_int hu a b).continuousOn_mul (by fun_prop)
  rw [← L.intervalIntegral_comp_comm hF]
  have hw : LipschitzWith ‖A‖₊ (fun r : ℝ => (r - o) * A) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs, ← sub_mul, abs_mul, mul_comm]
    ring_nf
    rfl
  have hLu : LipschitzWith (‖L‖₊ * C) (fun r => L (u r)) := L.lipschitz.comp hu
  have key := AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub
    (hw.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b))
    (hLu.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b))
  rw [← key]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hu.ae_differentiableAt_real] with r hr _
  have h1 : deriv (fun r => L (u r)) r = L (deriv u r) :=
    (L.hasFDerivAt.comp_hasDerivAt r hr.hasDerivAt).deriv
  have h2 : deriv (fun r : ℝ => (r - o) * A) r = A := by
    have : HasDerivAt (fun r : ℝ => (r - o) * A) (1 * A) r :=
      ((hasDerivAt_id' r).sub_const o).mul_const A
    rw [this.deriv]; ring
  rw [h1, h2]
  simp only [map_add]
  rw [show (((A : ℝ) : ℂ) * u r) = A • u r from (Complex.real_smul).symm,
    show ((((r - o) * A : ℝ) : ℂ) * deriv u r) = ((r - o) * A) • deriv u r from (Complex.real_smul).symm,
    map_smul, map_smul, smul_eq_mul, smul_eq_mul]

private theorem slice_ftc {u : ℝ → ℂ} {C : NNReal} (hu : LipschitzWith C u) (A o a b : ℝ) :
    ∫ r in a..b, (((A : ℝ) : ℂ) * u r + (((r - o) * A : ℝ) : ℂ) * deriv u r) =
      ((((b - o) * A : ℝ)) : ℂ) * u b - ((((a - o) * A : ℝ)) : ℂ) * u a := by
  apply Complex.ext
  · have := part_ftc Complex.reCLM hu A o a b
    simp only [Complex.reCLM_apply] at this
    rw [this]; simp
  · have := part_ftc Complex.imCLM hu A o a b
    simp only [Complex.imCLM_apply] at this
    rw [this]; simp

private theorem slice_ftc' {u : ℝ → ℂ} {C : NNReal} (hu : LipschitzWith C u) (c o a b : ℝ) :
    ∫ r in a..b, ((((1 / (c - o) : ℝ)) : ℂ) * u r + (((r - o) / (c - o) : ℝ) : ℂ) * deriv u r) =
      ((((b - o) / (c - o) : ℝ)) : ℂ) * u b - ((((a - o) / (c - o) : ℝ)) : ℂ) * u a := by
  have h : ∀ r : ℝ, (r - o) / (c - o) = (r - o) * (1 / (c - o)) := fun r => by ring
  simp_rw [h]
  exact slice_ftc hu (1 / (c - o)) o a b

private theorem radial_strip_trace {f : ℝ × ℝ → ℂ} {c o lo hi : ℝ} {C : NNReal} (hco : c ≠ o)
    (hf : LipschitzOnWith C f (Icc (min c o) (max c o) ×ˢ Icc lo hi)) {t : ℝ → ℝ} (ht : Continuous t) :
    radialStripMoment c o lo hi f (CellBox.radialDeriv f) t = ∫ z in Icc lo hi, f (c, z) * (t z : ℂ) := by
  unfold radialStripMoment
  rcases lt_or_ge hi lo with hlh | hlh
  · simp [Icc_eq_empty_of_lt hlh]
  set m := min c o with hm
  set M := max c o with hM
  have hmM : m ≤ M := min_le_max
  let P : ℝ × ℝ → ℝ × ℝ := fun p => ((projIcc m M hmM p.1 : ℝ), (projIcc lo hi hlh p.2 : ℝ))
  have hPmem : ∀ p, P p ∈ Icc m M ×ˢ Icc lo hi := fun p => ⟨(projIcc m M hmM p.1).2, (projIcc lo hi hlh p.2).2⟩
  have hPid : ∀ p ∈ Icc m M ×ˢ Icc lo hi, P p = p := fun p hp =>
    Prod.ext (by simp [P, projIcc_of_mem hmM hp.1]) (by simp [P, projIcc_of_mem hlh hp.2])
  have hPd : ∀ p q, dist (P p) (P q) ≤ dist p q := by
    intro p q
    rw [Prod.dist_eq, Prod.dist_eq]
    have h1 := (LipschitzWith.projIcc hmM).dist_le_mul p.1 q.1
    have h2 := (LipschitzWith.projIcc hlh).dist_le_mul p.2 q.2
    simp only [NNReal.coe_one, one_mul, Subtype.dist_eq] at h1 h2
    exact max_le_max h1 h2
  set g : ℝ × ℝ → ℂ := fun p => f (P p) with hgdef
  have hg : LipschitzWith C g := LipschitzWith.of_dist_le_mul fun p q =>
    (hf.dist_le_mul _ (hPmem p) _ (hPmem q)).trans (mul_le_mul_of_nonneg_left (hPd p q) C.2)
  have hfg : ∀ p ∈ Icc m M ×ˢ Icc lo hi, f p = g p := fun p hp => by simp only [hgdef, hPid p hp]
  have hnull : ∀ x : ℝ, (volume : Measure (ℝ × ℝ)) ({x} ×ˢ univ) = 0 := by
    intro x; rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  have hS1 : ∫ p in Icc m M ×ˢ Icc lo hi, (((1 / (c - o) : ℝ) : ℂ) * f p +
        (((p.1 - o) / (c - o) : ℝ) : ℂ) * CellBox.radialDeriv f p) * ((t p.2 : ℝ) : ℂ) =
      ∫ p in Icc m M ×ˢ Icc lo hi, (((1 / (c - o) : ℝ) : ℂ) * g p +
        (((p.1 - o) / (c - o) : ℝ) : ℂ) * CellBox.radialDeriv g p) * ((t p.2 : ℝ) : ℂ) := by
    refine setIntegral_congr_ae (measurableSet_Icc.prod measurableSet_Icc) ?_
    have h1 := compl_mem_ae_iff.mpr (hnull m)
    have h2 := compl_mem_ae_iff.mpr (hnull M)
    filter_upwards [h1, h2] with p hp1 hp2 hp
    have hpm : p.1 ≠ m := fun e => hp1 ⟨e, mem_univ _⟩
    have hpM : p.1 ≠ M := fun e => hp2 ⟨e, mem_univ _⟩
    have hio : p.1 ∈ Ioo m M := ⟨lt_of_le_of_ne hp.1.1 (Ne.symm hpm), lt_of_le_of_ne hp.1.2 hpM⟩
    have hd : CellBox.radialDeriv f p = CellBox.radialDeriv g p := by
      unfold CellBox.radialDeriv
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [Icc_mem_nhds hio.1 hio.2] with r hr
      exact hfg (r, p.2) ⟨hr, hp.2⟩
    rw [hfg p hp, hd]
  rw [hS1]
  have hmeasD : Measurable (fun q : ℝ × ℝ => deriv (fun r => g (r, q.1)) q.2) := by
    refine measurable_deriv_with_param (f := fun z r => g (r, z)) ?_
    change Continuous (fun q : ℝ × ℝ => g (q.2, q.1))
    exact hg.continuous.comp continuous_swap
  obtain ⟨Bg, hBg⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨Bt, hBt⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc lo hi) ht.continuousOn
  have hwc : Continuous (fun r : ℝ => (r - o) / (c - o)) := by fun_prop
  obtain ⟨Bw, hBw⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc m M) hwc.continuousOn
  have hgb : ∀ p, ‖g p‖ ≤ Bg := fun p => hBg _ (hPmem p)
  have hdb : ∀ z r, ‖deriv (fun r => g (r, z)) r‖ ≤ C := fun z r => by
    have hl : LipschitzWith (C * 1) (fun r => g (r, z)) := hg.comp (LipschitzWith.prodMk_right z)
    have := norm_deriv_le_of_lipschitz (x₀ := r) hl
    simpa using this
  have hInt : IntegrableOn (fun q : ℝ × ℝ => (((1 / (c - o) : ℝ) : ℂ) * g q.swap +
        (((q.swap.1 - o) / (c - o) : ℝ) : ℂ) * CellBox.radialDeriv g q.swap) * ((t q.swap.2 : ℝ) : ℂ))
      (Icc lo hi ×ˢ Icc m M) (volume.prod volume) := by
    refine Measure.integrableOn_of_bounded (M := (‖(1 / (c - o) : ℝ)‖ * Bg + Bw * C) * Bt) ?_ ?_ ?_
    · rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top measure_Icc_lt_top.ne measure_Icc_lt_top.ne
    · have hm1 : Measurable fun q : ℝ × ℝ => g q.swap := (hg.continuous.comp continuous_swap).measurable
      have hm2 : Measurable fun q : ℝ × ℝ => CellBox.radialDeriv g q.swap := hmeasD
      have hm3 : Measurable fun q : ℝ × ℝ => (((q.swap.1 - o) / (c - o) : ℝ) : ℂ) := by
        exact Complex.measurable_ofReal.comp (hwc.measurable.comp measurable_snd)
      have hm4 : Measurable fun q : ℝ × ℝ => ((t q.swap.2 : ℝ) : ℂ) :=
        Complex.measurable_ofReal.comp (ht.measurable.comp measurable_fst)
      exact (((measurable_const.mul hm1).add (hm3.mul hm2)).mul hm4).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc) (fun q hq => ?_)
      have hw := hBw q.2 hq.2
      have ht' := hBt q.1 hq.1
      rw [norm_mul]
      refine mul_le_mul ?_ ?_ (norm_nonneg _) ?_
      · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, Complex.norm_real]
          exact mul_le_mul_of_nonneg_left (hgb _) (norm_nonneg _)
        · rw [norm_mul, Complex.norm_real]
          exact mul_le_mul hw (hdb _ _) (norm_nonneg _) ((norm_nonneg _).trans hw)
      · rw [Complex.norm_real]; exact ht'
      · exact add_nonneg (mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (hgb 0)))
          (mul_nonneg ((norm_nonneg _).trans (hBw m ⟨le_rfl, hmM⟩)) C.2)
  rw [Measure.volume_eq_prod, ← setIntegral_prod_swap, setIntegral_prod _ hInt, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc (fun z hz => ?_)
  simp only [Prod.swap_prod_mk]
  rw [integral_mul_const, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hmM]
  have hu : LipschitzWith (C * 1) (fun r => g (r, z)) := hg.comp (LipschitzWith.prodMk_right z)
  have hftc := slice_ftc' hu c o m M
  unfold CellBox.radialDeriv
  simp only
  rw [hftc]
  have hcm : (c, z) ∈ Icc m M ×ˢ Icc lo hi := ⟨⟨min_le_left _ _, le_max_left _ _⟩, hz⟩
  have hne : c - o ≠ 0 := sub_ne_zero.mpr hco
  rcases lt_or_gt_of_ne hco with h | h
  · have e1 : m = c := by rw [hm]; exact min_eq_left h.le
    have e2 : M = o := by rw [hM]; exact max_eq_right h.le
    rw [e1, e2, ← hfg _ hcm]
    simp only [edgeSign, if_neg (not_lt.mpr h.le), sub_self, zero_div, div_self hne]
    push_cast
    ring
  · have e1 : m = o := by rw [hm]; exact min_eq_right h.le
    have e2 : M = c := by rw [hM]; exact max_eq_left h.le
    rw [e1, e2, ← hfg _ hcm]
    simp only [edgeSign, if_pos h, sub_self, zero_div, div_self hne]
    push_cast
    ring

private theorem height_strip_trace {f : ℝ × ℝ → ℂ} {c o lo hi : ℝ} {C : NNReal} (hco : c ≠ o)
    (hf : LipschitzOnWith C f (Icc lo hi ×ˢ Icc (min c o) (max c o))) {t : ℝ → ℝ} (ht : Continuous t) :
    heightStripMoment c o lo hi (fun _ => 1) f (CellBox.heightDeriv f) t = ∫ r in Icc lo hi, f (r, c) * (t r : ℂ) := by
  have hs : ∀ a b : ℝ × ℝ, dist a.swap b.swap = dist a b := fun a b => by
    simp [Prod.dist_eq, max_comm]
  have hf' : LipschitzOnWith C (fun q : ℝ × ℝ => f q.swap) (Icc (min c o) (max c o) ×ˢ Icc lo hi) := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    have := hf.dist_le_mul p.swap ⟨hp.2, hp.1⟩ q.swap ⟨hq.2, hq.1⟩
    rwa [hs] at this
  have key := radial_strip_trace hco hf' ht
  unfold radialStripMoment at key
  unfold heightStripMoment
  rw [Measure.volume_eq_prod, ← setIntegral_prod_swap, ← Measure.volume_eq_prod]
  simp only [one_mul, Prod.fst_swap, Prod.snd_swap]
  exact key

private theorem test_cont (F : FaceSegment) (d : ℕ) : Continuous (F.test d) := by
  unfold FaceSegment.test
  exact continuous_finsetSum _ (fun i _ => by fun_prop)

theorem trace_coef {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (ha : a ∈ R.rowSet)
    (n : ℤ) (s : Fin L.presCount) (g : ℝ → ℂ)
    (hg : ∀ p ∈ K.rect, ((L.presSegment s).radial → p.1 = (L.presSegment s).level → rowModeVec c a n p 0 = g p.2) ∧
        (¬ (L.presSegment s).radial → p.2 = (L.presSegment s).level → rowModeVec c a n p 2 = g p.1))
    (d : ℕ) :
    segmentTrace (L.presSegment s) (fun p => rowModeVec c a n p (if (L.presSegment s).radial then 0 else 2)) d =
      ∫ t in Set.Icc (L.presSegment s).lo (L.presSegment s).hi, g t * (((L.presSegment s).test d t : ℝ) : ℂ) := by
  have hbox := hD.box
  have hr := hbox.r_order
  have hz := hbox.z_order
  have hoth := hL.presSegment_other_in_box s
  unfold segmentTrace FaceSegment.moment
  rcases hL.presSegment_on_side s with ⟨hrad, hlev, hlo, hhi, _⟩ | ⟨hrad, hlev, hlo, hhi⟩
  · have ho := hoth.1 hrad
    simp only [hrad, if_true]
    obtain ⟨C, hC⟩ := row_mode_slope hD hR ha n 0
    have hmm : min (L.presSegment s).level (L.presSegment s).other = K.r₁ ∧
        max (L.presSegment s).level (L.presSegment s).other = K.r₂ := by
      rw [ho]
      rcases hlev with h | h <;> rw [h] <;> constructor <;> simp [min_def, max_def] <;> intros <;> linarith
    have hsub : Icc (min (L.presSegment s).level (L.presSegment s).other)
        (max (L.presSegment s).level (L.presSegment s).other) ×ˢ
        Icc (L.presSegment s).lo (L.presSegment s).hi ⊆ K.rect := by
      rw [hmm.1, hmm.2]
      exact prod_mono subset_rfl (Icc_subset_Icc hlo hhi)
    have hne : (L.presSegment s).level ≠ (L.presSegment s).other := by
      rw [ho]; rcases hlev with h | h <;> rw [h] <;> intro e <;> linarith
    rw [radial_strip_trace hne (hC.mono hsub) (test_cont _ d)]
    refine setIntegral_congr_fun measurableSet_Icc (fun z hz' => ?_)
    have hp : ((L.presSegment s).level, z) ∈ K.rect := by
      refine ⟨?_, Icc_subset_Icc hlo hhi hz'⟩
      rcases hlev with h | h <;> rw [h] <;> constructor <;> linarith
    rw [(hg _ hp).1 hrad rfl]
  · have ho := hoth.2 hrad
    simp only [hrad, if_false, Bool.false_eq_true]
    obtain ⟨C, hC⟩ := row_mode_slope hD hR ha n 2
    have hmm : min (L.presSegment s).level (L.presSegment s).other = K.z₁ ∧
        max (L.presSegment s).level (L.presSegment s).other = K.z₂ := by
      rw [ho]
      rcases hlev with h | h <;> rw [h] <;> constructor <;> simp [min_def, max_def] <;> intros <;> linarith
    have hsub : Icc (L.presSegment s).lo (L.presSegment s).hi ×ˢ
        Icc (min (L.presSegment s).level (L.presSegment s).other)
          (max (L.presSegment s).level (L.presSegment s).other) ⊆ K.rect := by
      rw [hmm.1, hmm.2]
      exact prod_mono (Icc_subset_Icc hlo hhi) subset_rfl
    have hne : (L.presSegment s).level ≠ (L.presSegment s).other := by
      rw [ho]; rcases hlev with h | h <;> rw [h] <;> intro e <;> linarith
    rw [height_strip_trace hne (hC.mono hsub) (test_cont _ d)]
    refine setIntegral_congr_fun measurableSet_Icc (fun r hr' => ?_)
    have hp : (r, (L.presSegment s).level) ∈ K.rect := by
      refine ⟨Icc_subset_Icc hlo hhi hr', ?_⟩
      rcases hlev with h | h <;> rw [h] <;> constructor <;> linarith
    rw [(hg _ hp).2 hrad rfl]

theorem boundary_pairing {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet)
    (n : ℤ) (cf : Fin L.presCount → Fin L.degSide → ℂ)
    (hcf : ∀ s, ∀ p ∈ K.rect,
      ((L.presSegment s).radial → p.1 = (L.presSegment s).level →
          rowModeVec c a n p 0 = ∑ d, cf s d * ((L.presSegment s).test d p.2 : ℂ)) ∧
        (¬ (L.presSegment s).radial → p.2 = (L.presSegment s).level →
          rowModeVec c a n p 2 = ∑ d, cf s d * ((L.presSegment s).test d p.1 : ℂ))) :
    ∫ p in K.rect, (p.1 : ℂ) * pairC (modeVec c.order n x.2.2.2.2 p.1 p.2) (rowModeVec c a n p) =
      ∑ s : Fin L.presCount, ∑ d : Fin L.degSide,
        edgeSign (L.presSegment s).level (L.presSegment s).other *
          (if (L.presSegment s).radial then ((L.presSegment s).level : ℂ) else 1) * (starRingEnd ℂ) (cf s d) *
        (L.presSegment s).moment true (L.pressMode n x) (L.pressureGradMode n x 0) (L.pressureGradMode n x 2) d := by
  obtain ⟨hI1, hE1⟩ := radial_side_pairing hα1 hα2 hc hD hR hL hx ha n cf hcf
  obtain ⟨hI2, hE2⟩ := height_side_pairing hα1 hα2 hc hD hR hL hx ha n cf hcf
  have hord : L.order = c.order := hL.layout.order_eq
  have hang := pressure_angular_mode (L := L) hx n
  have hdiv := row_mode_divergence hα1 hα2 hc hD hR hL hx ha n
  have hr0 : 0 ≤ K.r₁ := hD.box.r_order.1
  have hset : (Ioo K.r₁ K.r₂ ×ˢ Ioo K.z₁ K.z₂ : Set (ℝ × ℝ)) =ᵐ[volume] K.rect := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc
  have hmeas : MeasurableSet (Ioo K.r₁ K.r₂ ×ˢ Ioo K.z₁ K.z₂ : Set (ℝ × ℝ)) := measurableSet_Ioo.prod measurableSet_Ioo
  have key : ∫ p in K.rect, (p.1 : ℂ) * pairC (modeVec c.order n x.2.2.2.2 p.1 p.2) (rowModeVec c a n p) =
      ∫ p in K.rect, (((p.1 : ℂ) * L.pressureGradMode n x 0 p * (starRingEnd ℂ) (rowModeVec c a n p 0) +
        L.pressMode n x p * (starRingEnd ℂ) (CellBox.radialDeriv (fun q => (q.1 : ℂ) * rowModeVec c a n q 0) p)) +
        ((p.1 : ℂ) * L.pressureGradMode n x 2 p * (starRingEnd ℂ) (rowModeVec c a n p 2) +
        L.pressMode n x p * (starRingEnd ℂ) ((p.1 : ℂ) * CellBox.heightDeriv (fun q => rowModeVec c a n q 2) p))) := by
    rw [← setIntegral_congr_set hset, ← setIntegral_congr_set hset]
    refine setIntegral_congr_ae hmeas ?_
    filter_upwards [hang] with p hp hmem
    have hp0 : 0 < p.1 := lt_of_le_of_lt hr0 hmem.1.1
    have h1 := hp hp0
    have h2 := hdiv p hmem hp0
    have hθ : (starRingEnd ℂ) (rowModeVec c a n p 1) * ((azimuth c.order n : ℂ) * Complex.I) =
        (starRingEnd ℂ) (CellBox.radialDeriv (fun q => (q.1 : ℂ) * rowModeVec c a n q 0) p) +
          (starRingEnd ℂ) ((p.1 : ℂ) * CellBox.heightDeriv (fun q => rowModeVec c a n q 2) p) := by
      have h3 : (azimuth c.order n : ℂ) * Complex.I * rowModeVec c a n p 1 =
          -(CellBox.radialDeriv (fun q => (q.1 : ℂ) * rowModeVec c a n q 0) p +
            (p.1 : ℂ) * CellBox.heightDeriv (fun q => rowModeVec c a n q 2) p) := by
        linear_combination h2
      have h4 := congrArg (starRingEnd ℂ) h3
      simp only [map_mul, map_neg, map_add, Complex.conj_ofReal, Complex.conj_I] at h4
      simp only [map_mul, Complex.conj_ofReal]
      linear_combination -h4
    unfold pairC
    rw [Fin.sum_univ_three]
    have e0 : modeVec c.order n x.2.2.2.2 p.1 p.2 0 = L.pressureGradMode n x 0 p := by
      simp [CellLayout.pressureGradMode, hord]
    have e1 : modeVec c.order n x.2.2.2.2 p.1 p.2 1 = L.pressureGradMode n x 1 p := by
      simp [CellLayout.pressureGradMode, hord]
    have e2 : modeVec c.order n x.2.2.2.2 p.1 p.2 2 = L.pressureGradMode n x 2 p := by
      simp [CellLayout.pressureGradMode, hord]
    rw [e0, e1, e2, hord] at *
    have hmid : (p.1 : ℂ) * (L.pressureGradMode n x 1 p * (starRingEnd ℂ) (rowModeVec c a n p 1)) =
        L.pressMode n x p * ((starRingEnd ℂ) (rowModeVec c a n p 1) * ((azimuth c.order n : ℂ) * Complex.I)) := by
      rw [← mul_assoc, h1]; ring
    rw [hθ] at hmid
    linear_combination hmid
  rw [key, integral_add hI1 hI2, hE1, hE2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  split_ifs <;> ring

end Breakdown.FracInternal.LayoutRowPressureBoundary
