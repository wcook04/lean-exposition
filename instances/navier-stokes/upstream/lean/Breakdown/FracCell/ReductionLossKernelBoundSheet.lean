import Breakdown.FracCell.ReductionLossKernelBoundParts

open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

namespace KernelSectors

private theorem uIntegral_le (a c l : ℝ) (ha : 0 < a) (hc : 0 < c) (hl : 0 < l) :
    (∫⁻ u in Ioc (-Real.pi) Real.pi, {u : ℝ | |c * u| ≤ l}.indicator
      (fun u => ENNReal.ofReal (1 / (4 * Real.pi * Real.sqrt (a ^ 2 + (c * u) ^ 2)))) u) ≤
      ENNReal.ofReal (Real.arsinh (l / a) / (2 * Real.pi * c)) := by
  have hpi := Real.pi_pos
  set f : ℝ → ℝ := fun u => 1 / (4 * Real.pi * Real.sqrt (a ^ 2 + (c * u) ^ 2)) with hf
  have hfc : Continuous f := by
    rw [hf]
    refine Continuous.div continuous_const (by fun_prop) fun u => ?_
    have : 0 < Real.sqrt (a ^ 2 + (c * u) ^ 2) := Real.sqrt_pos.2 (by positivity)
    positivity
  have h1 : (∫⁻ u in Ioc (-Real.pi) Real.pi, {u : ℝ | |c * u| ≤ l}.indicator (fun u => ENNReal.ofReal (f u)) u) ≤
      ∫⁻ u, (Icc (-(l / c)) (l / c)).indicator (fun u => ENNReal.ofReal (f u)) u := by
    refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun u => ?_)
    by_cases hu : |c * u| ≤ l
    · have hmem : u ∈ Icc (-(l / c)) (l / c) := by
        rw [abs_le] at hu
        constructor
        · rw [neg_le, le_div_iff₀ hc]; nlinarith
        · rw [le_div_iff₀ hc]; nlinarith
      rw [indicator_of_mem (show u ∈ {u : ℝ | |c * u| ≤ l} from hu), indicator_of_mem hmem]
    · rw [indicator_of_notMem (show u ∉ {u : ℝ | |c * u| ≤ l} from hu)]
      exact bot_le
  refine h1.trans (le_of_eq ?_)
  rw [lintegral_indicator measurableSet_Icc]
  have hint : IntegrableOn f (Icc (-(l / c)) (l / c)) := hfc.continuousOn.integrableOn_compact isCompact_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun u => by
    have : 0 < Real.sqrt (a ^ 2 + (c * u) ^ 2) := Real.sqrt_pos.2 (by positivity)
    show (0:ℝ) ≤ 1 / (4 * Real.pi * Real.sqrt (a ^ 2 + (c * u) ^ 2))
    positivity)]
  congr 1
  have hlc : -(l / c) ≤ l / c := by
    have : 0 < l / c := div_pos hl hc
    linarith
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlc]
  have hderiv : ∀ u ∈ uIcc (-(l / c)) (l / c),
      HasDerivAt (fun u => Real.arsinh (c * u / a) / (4 * Real.pi * c)) (f u) u := by
    intro u _
    have h0 : HasDerivAt (fun u => c * u / a) (c / a) u := by
      simpa using ((hasDerivAt_id u).const_mul c).div_const a
    have h2 := (h0.arsinh).div_const (4 * Real.pi * c)
    refine h2.congr_deriv ?_
    show _ = 1 / (4 * Real.pi * Real.sqrt (a ^ 2 + (c * u) ^ 2))
    rw [smul_eq_mul]
    have hs : Real.sqrt (1 + (c * u / a) ^ 2) = Real.sqrt (a ^ 2 + (c * u) ^ 2) / a := by
      have e : a ^ 2 + (c * u) ^ 2 = a ^ 2 * (1 + (c * u / a) ^ 2) := by field_simp
      rw [e, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
      field_simp
    rw [hs]
    have : 0 < Real.sqrt (a ^ 2 + (c * u) ^ 2) := Real.sqrt_pos.2 (by positivity)
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hfc.intervalIntegrable _ _)]
  have e1 : c * (l / c) / a = l / a := by field_simp
  have e2 : c * -(l / c) / a = -(l / a) := by field_simp
  simp only [e1, e2, Real.arsinh_neg]
  field_simp
  ring


private theorem bathtub_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (n : α → ℝ) (hn : Measurable n)
    (φ : ℝ → ENNReal) (d R : ℝ) (hdR : d ≤ R) (hφ : ∀ s t, d ≤ s → s ≤ t → φ t ≤ φ s)
    (A : Set α) (hA : MeasurableSet A) (hAd : ∀ p ∈ A, d ≤ n p)
    (hvol : μ A ≤ μ {p | d ≤ n p ∧ n p ≤ R}) (hfin : μ A ≠ ⊤) :
    ∫⁻ p in A, φ (n p) ∂μ ≤ ∫⁻ p in {p | d ≤ n p ∧ n p ≤ R}, φ (n p) ∂μ := by
  set B := {p | d ≤ n p ∧ n p ≤ R} with hBdef
  have hB : MeasurableSet B := (measurableSet_le measurable_const hn).inter (measurableSet_le hn measurable_const)
  have e1 := lintegral_inter_add_sdiff (μ := μ) (fun p => φ (n p)) A hB
  have e2 := lintegral_inter_add_sdiff (μ := μ) (fun p => φ (n p)) B hA
  rw [inter_comm] at e2
  have h3 : ∫⁻ p in A \ B, φ (n p) ∂μ ≤ φ R * μ (A \ B) := by
    calc ∫⁻ p in A \ B, φ (n p) ∂μ ≤ ∫⁻ _ in A \ B, φ R ∂μ := by
          refine setLIntegral_mono' (hA.diff hB) fun p hp => ?_
          have h1 := hAd p hp.1
          have h2 : R < n p := by
            by_contra h
            exact hp.2 ⟨h1, not_lt.1 h⟩
          exact hφ R (n p) hdR h2.le
      _ = φ R * μ (A \ B) := setLIntegral_const _ _
  have h4 : φ R * μ (B \ A) ≤ ∫⁻ p in B \ A, φ (n p) ∂μ := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' (hB.diff hA) fun p hp => hφ (n p) R hp.1.1 hp.1.2
  have h5 : μ (A \ B) ≤ μ (B \ A) := by
    have a1 := measure_inter_add_sdiff (μ := μ) A hB
    have a2 := measure_inter_add_sdiff (μ := μ) B hA
    rw [inter_comm] at a2
    have hfin' : μ (A ∩ B) ≠ ⊤ := ((measure_mono inter_subset_left).trans_lt hfin.lt_top).ne
    refine (ENNReal.add_le_add_iff_left hfin').1 ?_
    rw [a1, a2]
    exact hvol
  rw [← e1, ← e2]
  exact add_le_add le_rfl (h3.trans (le_trans (mul_le_mul' le_rfl h5) h4))

private theorem radial_lintegral (g : ℝ → ENNReal) (hg : Measurable g) :
    ∫⁻ p : ℝ × ℝ, g (Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ r in Ioi 0, ENNReal.ofReal r * g r := by
  rw [← lintegral_comp_polarCoord_symm]
  have h : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 • g (Real.sqrt ((polarCoord.symm p).1 ^ 2 +
      (polarCoord.symm p).2 ^ 2)) = ENNReal.ofReal p.1 * g p.1 := by
    intro p hp
    have hp1 : 0 < p.1 := hp.1
    have e : (polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2 = p.1 ^ 2 := by
      simp only [polarCoord_symm_apply]
      have := Real.cos_sq_add_sin_sq p.2
      linear_combination p.1 ^ 2 * this
    rw [e, Real.sqrt_sq hp1.le, smul_eq_mul]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet h, polarCoord_target,
    Measure.volume_eq_prod, setLIntegral_prod (fun x : ℝ × ℝ => ENNReal.ofReal x.1 * g x.1) ((ENNReal.measurable_ofReal.comp measurable_fst).mul
      (hg.comp measurable_fst)).aemeasurable]
  simp only [setLIntegral_const, Real.volume_Ioo]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
  congr 2
  ring


private theorem arsinh_abs_le (x : ℝ) : |Real.arsinh x| ≤ |x| := by
  rcases le_total 0 x with h | h
  · have h1 : Real.arsinh x ≤ x := by
      rw [← Real.sinh_le_sinh, Real.sinh_arsinh]
      exact Real.self_le_sinh_iff.2 h
    rw [abs_of_nonneg (Real.arsinh_nonneg_iff.2 h), abs_of_nonneg h]
    exact h1
  · have h1 : Real.arsinh (-x) ≤ -x := by
      rw [← Real.sinh_le_sinh, Real.sinh_arsinh]
      exact Real.self_le_sinh_iff.2 (by linarith)
    rw [abs_of_nonpos (Real.arsinh_nonpos_iff.2 h), abs_of_nonpos h, ← Real.arsinh_neg]
    exact h1

private def sheetPrim (l s : ℝ) : ℝ := (s ^ 2 * Real.arsinh (l / s) + l * Real.sqrt (s ^ 2 + l ^ 2)) / 2

private theorem sheetPrim_deriv (l r : ℝ) (hr : 0 < r) :
    HasDerivAt (sheetPrim l) (r * Real.arsinh (l / r)) r := by
  have hq : HasDerivAt (fun s : ℝ => l / s) ((0 * r - l * 1) / r ^ 2) r :=
    (hasDerivAt_const r l).div (hasDerivAt_id r) hr.ne'
  have ha := hq.arsinh
  have hp := (hasDerivAt_pow 2 r).mul ha
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2 + l ^ 2) (↑2 * r ^ (2 - 1)) r :=
    (hasDerivAt_pow 2 r).add_const (l ^ 2)
  have hpos : 0 < r ^ 2 + l ^ 2 := by positivity
  have hs := (hsq.sqrt hpos.ne').const_mul l
  have hG := (hp.add hs).div_const 2
  refine hG.congr_deriv ?_
  have hsr : Real.sqrt (1 + (l / r) ^ 2) = Real.sqrt (r ^ 2 + l ^ 2) / r := by
    have e : r ^ 2 + l ^ 2 = r ^ 2 * (1 + (l / r) ^ 2) := by field_simp
    rw [e, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
    field_simp
  have hS : 0 < Real.sqrt (r ^ 2 + l ^ 2) := Real.sqrt_pos.2 hpos
  simp only [smul_eq_mul, hsr]
  field_simp
  ring

private theorem sheetPrim_cont (l R : ℝ) : ContinuousOn (sheetPrim l) (Icc 0 R) := by
  intro s _
  apply ContinuousAt.continuousWithinAt
  have h2 : Continuous (fun t : ℝ => l * Real.sqrt (t ^ 2 + l ^ 2)) := by fun_prop
  rcases eq_or_ne s 0 with rfl | hs0
  · have h1 : Tendsto (fun t : ℝ => t ^ 2 * Real.arsinh (l / t)) (𝓝 0) (𝓝 0) := by
      refine squeeze_zero_norm (a := fun t => |l| * |t|) (fun t => ?_) ?_
      · rw [Real.norm_eq_abs, abs_mul, abs_pow]
        rcases eq_or_ne t 0 with rfl | ht
        · simp
        · calc |t| ^ 2 * |Real.arsinh (l / t)| ≤ |t| ^ 2 * |l / t| :=
                mul_le_mul_of_nonneg_left (arsinh_abs_le _) (by positivity)
            _ = |l| * |t| := by
                rw [abs_div]
                field_simp
      · have : Tendsto (fun t : ℝ => |l| * |t|) (𝓝 0) (𝓝 (|l| * |0|)) :=
          (continuous_const.mul continuous_abs).tendsto 0
        simpa using this
    have h3 := (h1.add (h2.tendsto 0)).div_const 2
    have e : sheetPrim l 0 = (0 + l * Real.sqrt (0 ^ 2 + l ^ 2)) / 2 := by
      simp [sheetPrim]
    rw [ContinuousAt, e]
    exact h3
  · have h1 : ContinuousAt (fun t : ℝ => t ^ 2 * Real.arsinh (l / t)) s :=
      (continuousAt_id.pow 2).mul ((continuousAt_const.div continuousAt_id hs0).arsinh)
    exact (h1.add h2.continuousAt).div_const 2

private theorem radial_arsinh_le (l d R : ℝ) (hl : 0 < l) (hd : 0 ≤ d) (hdR : d ≤ R) :
    (∫⁻ r in Ioi 0, ENNReal.ofReal r * (Icc d R).indicator (fun r => ENNReal.ofReal (Real.arsinh (l / r))) r) ≤
      ENNReal.ofReal (sheetPrim l R - sheetPrim l d) := by
  set k : ℝ → ℝ := fun r => r * Real.arsinh (l / r) with hk
  have hk0 : ∀ r, 0 ≤ r → 0 ≤ k r := fun r hr =>
    mul_nonneg hr (Real.arsinh_nonneg_iff.2 (div_nonneg hl.le hr))
  have h1 : (∫⁻ r in Ioi 0, ENNReal.ofReal r * (Icc d R).indicator (fun r => ENNReal.ofReal (Real.arsinh (l / r))) r) ≤
      ∫⁻ r, (Icc d R).indicator (fun r => ENNReal.ofReal (k r)) r := by
    refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun r => ?_)
    by_cases hr : r ∈ Icc d R
    · rw [indicator_of_mem hr, indicator_of_mem hr, hk, ENNReal.ofReal_mul (hd.trans hr.1)]
    · rw [indicator_of_notMem hr, indicator_of_notMem hr, mul_zero]
  refine h1.trans (le_of_eq ?_)
  rw [lintegral_indicator measurableSet_Icc]
  have hmeas : Measurable k := by
    rw [hk]
    exact measurable_id.mul (Real.continuous_arsinh.measurable.comp (measurable_const.div measurable_id))
  have hint : IntegrableOn k (Icc d R) := by
    refine Integrable.mono' (g := fun _ => l) (integrableOn_const (by simp)) hmeas.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Icc fun r hr => ?_)
    have hr0 : 0 ≤ r := hd.trans hr.1
    rw [Real.norm_eq_abs, abs_of_nonneg (hk0 r hr0)]
    rcases eq_or_lt_of_le hr0 with h | h
    · rw [hk]
      simp only [← h, zero_mul]
      exact hl.le
    · have := arsinh_abs_le (l / r)
      rw [abs_of_nonneg (Real.arsinh_nonneg_iff.2 (div_nonneg hl.le hr0)), abs_of_nonneg (div_nonneg hl.le hr0)] at this
      calc k r = r * Real.arsinh (l / r) := rfl
        _ ≤ r * (l / r) := mul_le_mul_of_nonneg_left this hr0
        _ = l := by field_simp
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Icc fun r hr =>
    hk0 r (hd.trans hr.1))]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hdR]
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hdR
    ((sheetPrim_cont l R).mono (Icc_subset_Icc_left hd)) (fun r hr => ?_) ((intervalIntegrable_iff_integrableOn_Icc_of_le hdR).2 hint)
  exact (sheetPrim_deriv l r (lt_of_le_of_lt hd hr.1)).hasDerivWithinAt

private theorem sheetPrim_le (l d R : ℝ) (hl : 0 < l) (hd : 0 ≤ d) (hdR : d ≤ R) : sheetPrim l d ≤ sheetPrim l R := by
  have hmono : MonotoneOn (sheetPrim l) (Icc 0 R) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 R) (sheetPrim_cont l R) ?_ ?_
    · rw [interior_Icc]
      exact fun r hr => (sheetPrim_deriv l r hr.1).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro r hr
      rw [(sheetPrim_deriv l r hr.1).deriv]
      exact mul_nonneg hr.1.le (Real.arsinh_nonneg_iff.2 (div_nonneg hl.le hr.1.le))
  exact hmono ⟨hd, hdR⟩ ⟨hd.trans hdR, le_rfl⟩ hdR


private theorem toIocMod_measurable : Measurable (toIocMod Real.two_pi_pos (-Real.pi)) := by
  have e : toIocMod Real.two_pi_pos (-Real.pi) =
      fun b => b - ((-⌊(-Real.pi + 2 * Real.pi - b) / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) := by
    funext b
    rw [toIocMod, toIocDiv_eq_neg_floor, zsmul_eq_mul]
  rw [e]
  refine measurable_id.sub (Measurable.mul ?_ measurable_const)
  exact measurable_from_top.comp ((((measurable_const.sub measurable_id).div_const _).floor).neg)

private theorem periodic_lintegral (ψ : ℝ → ENNReal) (t : ℝ) :
    ∫⁻ θ in Ioc (-Real.pi) Real.pi, ψ (toIocMod Real.two_pi_pos (-Real.pi) (θ - t)) =
      ∫⁻ θ in Ioc (-Real.pi) Real.pi, ψ θ := by
  have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  set F : AddCircle (2 * Real.pi) → ENNReal := fun q => ψ ((AddCircle.equivIoc (2 * Real.pi) (-Real.pi) q : ℝ))
  have hF : ∀ θ : ℝ, F (θ : AddCircle (2 * Real.pi)) = ψ (toIocMod Real.two_pi_pos (-Real.pi) θ) := fun θ => rfl
  have e : Ioc (-Real.pi) Real.pi = Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by ring_nf
  have h1 : ∫⁻ θ in Ioc (-Real.pi) Real.pi, ψ (toIocMod Real.two_pi_pos (-Real.pi) (θ - t)) =
      ∫⁻ q : AddCircle (2 * Real.pi), F (q - (t : AddCircle (2 * Real.pi))) := by
    rw [e, ← AddCircle.lintegral_preimage (2 * Real.pi) (-Real.pi) (fun q => F (q - (t : AddCircle (2 * Real.pi))))]
    refine lintegral_congr fun θ => ?_
    show _ = F ((θ : AddCircle (2 * Real.pi)) - (t : AddCircle (2 * Real.pi)))
    rw [← AddCircle.coe_sub, hF]
  have h2 : ∫⁻ θ in Ioc (-Real.pi) Real.pi, ψ θ = ∫⁻ q : AddCircle (2 * Real.pi), F q := by
    rw [e, ← AddCircle.lintegral_preimage (2 * Real.pi) (-Real.pi) F]
    refine setLIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
    rw [hF, (toIocMod_eq_self Real.two_pi_pos).2 hθ]
  rw [h1, h2, lintegral_sub_right_eq_self]


private theorem planar_le (ρx ζ pLo pHi zLo zHi d0 l : ℝ) (hl : 0 < l) (hd0 : 0 ≤ d0) (hp : pLo ≤ pHi)
    (hz : zLo ≤ zHi) (hgap : ∀ r z, pLo ≤ r → r ≤ pHi → zLo ≤ z → z ≤ zHi →
      d0 ^ 2 ≤ (ρx - r) ^ 2 + (ζ - z) ^ 2) :
    (∫⁻ p : ℝ × ℝ, (Icc pLo pHi ×ˢ Icc zLo zHi).indicator
      (fun p => ENNReal.ofReal (Real.arsinh (l / Real.sqrt ((ρx - p.1) ^ 2 + (ζ - p.2) ^ 2)))) p) ≤
      ENNReal.ofReal (2 * Real.pi * (sheetPrim l (Real.sqrt (d0 ^ 2 + (pHi - pLo) * (zHi - zLo) / Real.pi)) -
        sheetPrim l d0)) := by
  have hpi := Real.pi_pos
  set n : ℝ × ℝ → ℝ := fun p => Real.sqrt ((ρx - p.1) ^ 2 + (ζ - p.2) ^ 2) with hn
  have hnm : Measurable n := by rw [hn]; fun_prop
  set D1 := Real.sqrt (d0 ^ 2 + (pHi - pLo) * (zHi - zLo) / Real.pi) with hD1
  have harea : 0 ≤ (pHi - pLo) * (zHi - zLo) := mul_nonneg (by linarith) (by linarith)
  have hD1sq : D1 ^ 2 = d0 ^ 2 + (pHi - pLo) * (zHi - zLo) / Real.pi :=
    Real.sq_sqrt (by positivity)
  have hdD : d0 ≤ D1 := by
    rw [hD1]
    calc d0 = Real.sqrt (d0 ^ 2) := (Real.sqrt_sq hd0).symm
      _ ≤ _ := by
        have : 0 ≤ (pHi - pLo) * (zHi - zLo) / Real.pi := by positivity
        exact Real.sqrt_le_sqrt (by linarith)
  set A := Icc pLo pHi ×ˢ Icc zLo zHi with hA
  have hAm : MeasurableSet A := measurableSet_Icc.prod measurableSet_Icc
  set φ : ℝ → ENNReal := fun s => if 0 < s then ENNReal.ofReal (Real.arsinh (l / s)) else ⊤ with hφ
  have hφm : Measurable φ := by
    rw [hφ]
    refine Measurable.ite measurableSet_Ioi ?_ measurable_const
    exact ENNReal.measurable_ofReal.comp (Real.continuous_arsinh.measurable.comp (measurable_const.div measurable_id))
  have hφa : ∀ s t, d0 ≤ s → s ≤ t → φ t ≤ φ s := by
    intro s t hs hst
    rw [hφ]
    by_cases h0 : 0 < s
    · have ht : 0 < t := lt_of_lt_of_le h0 hst
      simp only [if_pos h0, if_pos ht]
      refine ENNReal.ofReal_le_ofReal (Real.arsinh_le_arsinh.2 ?_)
      exact div_le_div_of_nonneg_left hl.le h0 hst
    · simp only [if_neg h0]
      exact le_top
  set B := {p : ℝ × ℝ | d0 ≤ n p ∧ n p ≤ D1} with hB
  set g : ℝ → ENNReal := (Icc d0 D1).indicator φ with hg
  have hgm : Measurable g := hφm.indicator measurableSet_Icc
  have htrans : ∀ f : ℝ → ENNReal, ∫⁻ p : ℝ × ℝ, f (n p) = ∫⁻ w : ℝ × ℝ, f (Real.sqrt (w.1 ^ 2 + w.2 ^ 2)) := by
    intro f
    rw [← lintegral_sub_right_eq_self (fun w : ℝ × ℝ => f (Real.sqrt (w.1 ^ 2 + w.2 ^ 2))) (ρx, ζ)]
    refine lintegral_congr fun p => ?_
    simp only [hn, Prod.fst_sub, Prod.snd_sub]
    congr 2
    ring
  have hBind : ∀ f : ℝ → ENNReal, ∀ p, B.indicator (fun p => f (n p)) p = (Icc d0 D1).indicator f (n p) := by
    intro f p
    by_cases h : p ∈ B
    · rw [indicator_of_mem h, indicator_of_mem (show n p ∈ Icc d0 D1 from h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (show n p ∉ Icc d0 D1 from h)]
  have hBm : MeasurableSet B := (measurableSet_le measurable_const hnm).inter (measurableSet_le hnm measurable_const)
  have hvolA : volume A = ENNReal.ofReal ((pHi - pLo) * (zHi - zLo)) := by
    rw [hA, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
      ← ENNReal.ofReal_mul (by linarith)]
  have hvolB : ENNReal.ofReal ((pHi - pLo) * (zHi - zLo)) ≤ volume B := by
    rw [← lintegral_indicator_one hBm]
    have e1 : ∫⁻ p, B.indicator 1 p = ∫⁻ p, (Icc d0 D1).indicator (fun _ => (1 : ENNReal)) (n p) :=
      lintegral_congr fun p => hBind (fun _ => 1) p
    rw [e1, htrans, radial_lintegral _ (measurable_const.indicator measurableSet_Icc)]
    have e2 : ∫⁻ r in Ioc d0 D1, ENNReal.ofReal r ≤
        ∫⁻ r in Ioi 0, ENNReal.ofReal r * (Icc d0 D1).indicator (fun _ => (1 : ENNReal)) r := by
      calc ∫⁻ r in Ioc d0 D1, ENNReal.ofReal r
          = ∫⁻ r in Ioc d0 D1, ENNReal.ofReal r * (Icc d0 D1).indicator (fun _ => (1 : ENNReal)) r := by
            refine setLIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
            rw [indicator_of_mem (Ioc_subset_Icc_self hr), mul_one]
        _ ≤ _ := lintegral_mono_set fun r hr => (show (0:ℝ) < r from lt_of_le_of_lt hd0 hr.1)
    have e3 : ∫⁻ r in Ioc d0 D1, ENNReal.ofReal r = ENNReal.ofReal ((D1 ^ 2 - d0 ^ 2) / 2) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (f := fun r : ℝ => r) (continuous_id.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        (ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => (hd0.trans hr.1.le)),
        ← intervalIntegral.integral_of_le hdD, integral_id]
    refine le_trans ?_ (mul_le_mul' le_rfl (e3 ▸ e2))
    rw [← ENNReal.ofReal_mul Real.two_pi_pos.le, hD1sq]
    apply le_of_eq
    congr 1
    field_simp
    ring
  have hAd : ∀ p ∈ A, d0 ≤ n p := by
    intro p hp
    have := hgap p.1 p.2 hp.1.1 hp.1.2 hp.2.1 hp.2.2
    rw [hn, ← Real.sqrt_sq hd0]
    exact Real.sqrt_le_sqrt this
  have hfin : volume A ≠ ⊤ := by rw [hvolA]; exact ENNReal.ofReal_ne_top
  have hbt := bathtub_le volume n hnm φ d0 D1 hdD hφa A hAm hAd (hvolA ▸ hvolB) hfin
  calc (∫⁻ p : ℝ × ℝ, A.indicator (fun p => ENNReal.ofReal (Real.arsinh (l / n p))) p)
      = ∫⁻ p in A, ENNReal.ofReal (Real.arsinh (l / n p)) := lintegral_indicator hAm _
    _ ≤ ∫⁻ p in A, φ (n p) := by
        refine setLIntegral_mono' hAm fun p _ => ?_
        rw [hφ]
        by_cases h0 : 0 < n p
        · simp only [if_pos h0, le_refl]
        · simp only [if_neg h0]
          exact le_top
    _ ≤ ∫⁻ p in B, φ (n p) := hbt
    _ = ∫⁻ w : ℝ × ℝ, g (Real.sqrt (w.1 ^ 2 + w.2 ^ 2)) := by
        rw [← lintegral_indicator hBm, ← htrans]
        exact lintegral_congr fun p => hBind φ p
    _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ r in Ioi 0, ENNReal.ofReal r * g r := radial_lintegral g hgm
    _ ≤ ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (sheetPrim l D1 - sheetPrim l d0) := by
        refine mul_le_mul' le_rfl (le_trans (le_of_eq ?_) (radial_arsinh_le l d0 D1 hl hd0 hdD))
        refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
        by_cases h : r ∈ Icc d0 D1
        · rw [hg, indicator_of_mem h, indicator_of_mem h, hφ]
          simp only [if_pos (show (0:ℝ) < r from hr)]
        · rw [hg, indicator_of_notMem h, indicator_of_notMem h]
    _ = _ := (ENNReal.ofReal_mul Real.two_pi_pos.le).symm


private def cylSp : (ℝ × ℝ) × ℝ ≃ᵐ Space :=
  ((MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow.symm)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm).trans
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))

private theorem cylSp_mp : MeasurePreserving cylSp volume volume :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).symm.comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm.comp
      (((MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ).symm).comp
        Measure.measurePreserving_swap))

private theorem cylSp_apply (a b z : ℝ) : cylSp ((a, b), z) 0 = a ∧ cylSp ((a, b), z) 1 = b ∧ cylSp ((a, b), z) 2 = z := by
  refine ⟨rfl, rfl, rfl⟩

private theorem planeAngle_cyl (r θ z : ℝ) (hr : 0 < r) (hθ : θ ∈ Ioo (-Real.pi) Real.pi) :
    planeAngle (cylSp ((r * Real.cos θ, r * Real.sin θ), z)) = θ ∧
      horizontalNorm (cylSp ((r * Real.cos θ, r * Real.sin θ), z)) = r := by
  obtain ⟨h0, h1, -⟩ := cylSp_apply (r * Real.cos θ) (r * Real.sin θ) z
  refine ⟨?_, ?_⟩
  · unfold planeAngle
    rw [h0, h1]
    have e : (⟨r * Real.cos θ, r * Real.sin θ⟩ : ℂ) = (r : ℂ) * (Complex.cos θ + Complex.sin θ * Complex.I) := by
      apply Complex.ext <;> simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [e, Complex.arg_real_mul _ hr, Complex.arg_cos_add_sin_mul_I ⟨hθ.1, hθ.2.le⟩]
  · unfold horizontalNorm
    rw [h0, h1]
    have e : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
      have := Real.cos_sq_add_sin_sq θ
      linear_combination r ^ 2 * this
    rw [e, Real.sqrt_sq hr.le]

private theorem signedTurn_eq (x y : Space) :
    signedTurn x y = toIocMod Real.two_pi_pos (-Real.pi) (planeAngle y - planeAngle x) := by
  have hpi := Real.pi_pos
  set d := planeAngle y - planeAngle x
  set t := toIcoMod Real.two_pi_pos 0 d with ht
  have htm := toIcoMod_mem_Ico' Real.two_pi_pos d
  rw [← ht] at htm
  have hsub := toIcoMod_sub_self Real.two_pi_pos 0 d
  rw [← ht, zsmul_eq_mul] at hsub
  push_cast at hsub
  unfold signedTurn
  rw [← ht]
  symm
  rw [toIocMod_eq_iff]
  split_ifs with h
  · refine ⟨⟨by linarith [htm.1], by linarith⟩, toIcoDiv Real.two_pi_pos 0 d, ?_⟩
    rw [zsmul_eq_mul]
    linarith
  · refine ⟨⟨by linarith [htm.2], by linarith [htm.2]⟩, toIcoDiv Real.two_pi_pos 0 d + 1, ?_⟩
    rw [zsmul_eq_mul]
    push_cast
    linarith

private theorem signedTurn_small (m : ℕ) (hm : 4 ≤ m) (x : Space) (S : Set Space) (y : Space)
    (hy : y ∈ sectorPart m x S 0 ∪ sectorPart m x S (m - 1)) : |signedTurn x y| ≤ 2 * Real.pi / m := by
  have hmr : (0 : ℝ) < m := by positivity
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hpi := Real.pi_pos
  set t := toIcoMod Real.two_pi_pos 0 (planeAngle y - planeAngle x) with ht
  have htm := toIcoMod_mem_Ico' Real.two_pi_pos (planeAngle y - planeAngle x)
  rw [← ht] at htm
  obtain ⟨t0, t1⟩ := htm
  have hq : 2 * Real.pi / m ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hmr]
    nlinarith
  unfold signedTurn
  rw [← ht]
  rcases hy with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
  · rw [← ht] at h1 h2
    simp only [Nat.cast_zero, mul_zero, zero_div, zero_add, mul_one] at h1 h2
    rw [if_pos (by linarith), abs_of_nonneg t0]
    linarith
  · rw [← ht] at h1 h2
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    rw [hcast] at h1 h2
    have e : 2 * Real.pi * ((m : ℝ) - 1) / m = 2 * Real.pi - 2 * Real.pi / m := by
      field_simp
    rw [e] at h1
    rw [if_neg (by intro h; linarith), abs_le]
    constructor <;> linarith

private theorem chord_le (u a : ℝ) (hu : 0 ≤ u) (hua : u ≤ a) (ha : 0 < a) (hapi : a ≤ Real.pi) :
    u / a * Real.sin a ≤ Real.sin u := by
  have hc := strictConcaveOn_sin_Icc.concaveOn
  have hb : (0 : ℝ) ≤ 1 - u / a := by
    rw [sub_nonneg, div_le_one ha]
    exact hua
  have h := hc.2 (show a ∈ Icc 0 Real.pi from ⟨ha.le, hapi⟩) (show (0 : ℝ) ∈ Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
    (div_nonneg hu ha.le) hb (by ring)
  simp only [smul_eq_mul, Real.sin_zero, mul_zero, add_zero] at h
  have e : u / a * a = u := by field_simp
  rw [e] at h
  exact h

private theorem plane_coords (x : Space) : x 0 = horizontalNorm x * Real.cos (planeAngle x) ∧
    x 1 = horizontalNorm x * Real.sin (planeAngle x) := by
  have hn : ‖(⟨x 0, x 1⟩ : ℂ)‖ = horizontalNorm x := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    rfl
  refine ⟨?_, ?_⟩
  · rw [← hn]
    exact (Complex.norm_mul_cos_arg (⟨x 0, x 1⟩ : ℂ)).symm
  · rw [← hn]
    exact (Complex.norm_mul_sin_arg (⟨x 0, x 1⟩ : ℂ)).symm

private theorem gap_le (aLo : ℝ) (aHi : Option ℝ) (bLo bHi s t : ℝ) (h1 : aLo ≤ s)
    (h2 : ∀ h, aHi = some h → s ≤ h) (h3 : bLo ≤ t) (h4 : t ≤ bHi) :
    gapDist aLo aHi bLo (some bHi) ^ 2 ≤ (s - t) ^ 2 := by
  have h0 : 0 ≤ gapDist aLo aHi bLo (some bHi) := le_max_left _ _
  have hle : gapDist aLo aHi bLo (some bHi) ≤ |s - t| := by
    have hA : aLo - bHi ≤ |s - t| := le_abs.2 (Or.inl (by linarith))
    have hB : ∀ h, aHi = some h → bLo - h ≤ |s - t| := fun h hh => le_abs.2 (Or.inr (by linarith [h2 h hh]))
    unfold gapDist
    refine max_le (abs_nonneg _) (max_le hA ?_)
    cases aHi with
    | none => exact abs_nonneg _
    | some h => exact hB h rfl
  rw [← sq_abs (s - t)]
  exact pow_le_pow_left₀ h0 hle 2


private theorem geom_bound (m : ℕ) (V : Space → ℝ) (D : CellSumData) (hD : IsCellSumData m V D)
    (a : Fin D.boxCount) (b : Fin D.pieceCount) (mirrored : Bool) (x : Space)
    (hρlo : D.boxRhoLo a ≤ horizontalNorm x) (ρH zH : ℝ) (hρH : D.pieceRhoHi b = some ρH)
    (hzH : D.pieceZHi b = some zH) (r θ z : ℝ) (hr : 0 < r)
    (hθ : θ ∈ Ioo (-Real.pi) Real.pi) (hzne : z ≠ (if mirrored then mirror x else x) 2)
    (hy : cylSp ((r * Real.cos θ, r * Real.sin θ), z) ∈
      nearSheet m x (D.pieceSolid b) (D.sectorConst m a b) (D.sectorLength a b mirrored)) :
    (D.pieceRhoLo b ≤ r ∧ r ≤ ρH ∧ D.pieceZLo b ≤ z ∧ z ≤ zH) ∧
      |D.sectorConst m a b * toIocMod Real.two_pi_pos (-Real.pi) (θ - planeAngle x)| ≤ D.sectorLength a b mirrored ∧
      1 / (4 * Real.pi * ‖(if mirrored then mirror x else x) - cylSp ((r * Real.cos θ, r * Real.sin θ), z)‖) ≤
        1 / (4 * Real.pi * Real.sqrt (((horizontalNorm x - r) ^ 2 + ((if mirrored then mirror x else x) 2 - z) ^ 2) +
          (D.sectorConst m a b * toIocMod Real.two_pi_pos (-Real.pi) (θ - planeAngle x)) ^ 2)) := by
  have hm4 := hD.order_even.2
  have hmr : (0 : ℝ) < m := by positivity
  have hm4r : (4 : ℝ) ≤ m := by exact_mod_cast hm4
  have hpi := Real.pi_pos
  set y := cylSp ((r * Real.cos θ, r * Real.sin θ), z) with hydef
  set x' := (if mirrored then mirror x else x) with hx'
  obtain ⟨hang, hhor⟩ := planeAngle_cyl r θ z hr hθ
  rw [← hydef] at hang hhor
  obtain ⟨y0, y1, y2⟩ := cylSp_apply (r * Real.cos θ) (r * Real.sin θ) z
  rw [← hydef] at y0 y1 y2
  have hyS : y ∈ D.pieceSolid b := by
    rcases hy.1 with h | h
    · exact h.1
    · exact h.1
  obtain ⟨p1, p2, p3, p4⟩ := hD.piece_solid b y hyS
  replace p2 := p2 ρH hρH
  replace p4 := p4 zH hzH
  rw [hhor] at p1 p2
  rw [y2] at p3 p4
  obtain ⟨q1, q2, q3, q4⟩ := hD.piece_box b
  obtain ⟨r1, r2⟩ := hD.box_lower a
  have hst := signedTurn_eq x y
  rw [hang] at hst
  set u := toIocMod Real.two_pi_pos (-Real.pi) (θ - planeAngle x) with hu
  set c := D.sectorConst m a b with hcdef
  refine ⟨⟨p1, p2, p3, p4⟩, hst ▸ hy.2, ?_⟩
  have hsmall := signedTurn_small m hm4 x (D.pieceSolid b) y hy.1
  rw [hst] at hsmall
  set ρx := horizontalNorm x
  set θx := planeAngle x
  obtain ⟨hx0, hx1⟩ := plane_coords x
  have hx'0 : x' 0 = x 0 ∧ x' 1 = x 1 := by
    rw [hx']
    cases mirrored <;> simp [mirror]
  have hnorm : ‖x' - y‖ ^ 2 = (x' 0 - y 0) ^ 2 + (x' 1 - y 1) ^ 2 + (x' 2 - y 2) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp [Fin.sum_univ_three]
  have hcosu : Real.cos u = Real.cos (θ - θx) := by
    have h := toIocMod_sub_self Real.two_pi_pos (-Real.pi) (θ - θx)
    rw [zsmul_eq_mul] at h
    have : u = (θ - θx) + ((-toIocDiv Real.two_pi_pos (-Real.pi) (θ - θx) : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hu]
      push_cast at h ⊢
      linarith
    rw [this, Real.cos_add_int_mul_two_pi]
  have hhalf : Real.cos u = 1 - 2 * Real.sin (u / 2) ^ 2 := by
    have := Real.cos_sq_add_sin_sq (u / 2)
    have h2 : Real.cos u = Real.cos (2 * (u / 2)) := by ring_nf
    rw [h2, Real.cos_two_mul]
    linarith
  have hhor2 : (x' 0 - y 0) ^ 2 + (x' 1 - y 1) ^ 2 = (ρx - r) ^ 2 + 4 * ρx * r * Real.sin (u / 2) ^ 2 := by
    rw [hx'0.1, hx'0.2, hx0, hx1, y0, y1]
    rw [Real.cos_sub] at hcosu
    have px := Real.cos_sq_add_sin_sq θx
    have py := Real.cos_sq_add_sin_sq θ
    linear_combination (ρx ^ 2) * px + (r ^ 2) * py + (2 * ρx * r) * hcosu - (2 * ρx * r) * hhalf
  set A := Real.pi / m with hA
  have hA0 : 0 < A := by positivity
  have hApi : A ≤ Real.pi := by
    rw [hA, div_le_iff₀ hmr]
    nlinarith
  have hu2 : |u| / 2 ≤ A := by
    rw [hA]
    have : 2 * Real.pi / m = 2 * (Real.pi / m) := by ring
    linarith
  have hchord := chord_le (|u| / 2) A (by positivity) hu2 hA0 hApi
  have hsinabs : Real.sin (u / 2) ^ 2 = Real.sin (|u| / 2) ^ 2 := by
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, neg_div, Real.sin_neg, neg_sq]
  have hkey1 : (Real.sin A / A) ^ 2 * u ^ 2 ≤ 4 * Real.sin (u / 2) ^ 2 := by
    rw [hsinabs]
    have hsA : 0 ≤ Real.sin A := Real.sin_nonneg_of_nonneg_of_le_pi hA0.le hApi
    have h0 : 0 ≤ |u| / 2 / A * Real.sin A := by positivity
    have h2 := pow_le_pow_left₀ h0 hchord 2
    have e : (Real.sin A / A) ^ 2 * u ^ 2 = 4 * (|u| / 2 / A * Real.sin A) ^ 2 := by
      rw [← sq_abs u]
      field_simp
      ring
    rw [e]
    linarith
  have hρρ : D.boxRhoLo a * D.pieceRhoLo b ≤ ρx * r := mul_le_mul hρlo p1 q1 (le_trans r1 hρlo)
  have hρρ0 : 0 ≤ D.boxRhoLo a * D.pieceRhoLo b := mul_nonneg r1 q1
  have hc2 : c ^ 2 = D.boxRhoLo a * D.pieceRhoLo b * (Real.sin A / A) ^ 2 := by
    rw [hcdef]
    unfold CellSumData.sectorConst
    rw [mul_div_assoc, mul_pow, Real.sq_sqrt hρρ0]
  have hcu : (c * u) ^ 2 ≤ 4 * ρx * r * Real.sin (u / 2) ^ 2 := by
    rw [mul_pow, hc2]
    have hs0 : 0 ≤ Real.sin (u / 2) ^ 2 := sq_nonneg _
    have h1 := mul_le_mul_of_nonneg_left hkey1 hρρ0
    have h2 := mul_le_mul_of_nonneg_right hρρ (by positivity : 0 ≤ 4 * Real.sin (u / 2) ^ 2)
    calc D.boxRhoLo a * D.pieceRhoLo b * (Real.sin A / A) ^ 2 * u ^ 2
        = D.boxRhoLo a * D.pieceRhoLo b * ((Real.sin A / A) ^ 2 * u ^ 2) := by ring
      _ ≤ D.boxRhoLo a * D.pieceRhoLo b * (4 * Real.sin (u / 2) ^ 2) := h1
      _ ≤ ρx * r * (4 * Real.sin (u / 2) ^ 2) := h2
      _ = 4 * ρx * r * Real.sin (u / 2) ^ 2 := by ring
  have hzpos : 0 < (x' 2 - z) ^ 2 := by
    have : x' 2 - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzne)
    positivity
  have hS : 0 < Real.sqrt (((ρx - r) ^ 2 + (x' 2 - z) ^ 2) + (c * u) ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hSle : Real.sqrt (((ρx - r) ^ 2 + (x' 2 - z) ^ 2) + (c * u) ^ 2) ≤ ‖x' - y‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (x' - y)), hnorm]
    apply Real.sqrt_le_sqrt
    rw [y2]
    linarith
  exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hSle (by positivity))


private theorem planeAngle_meas : Measurable planeAngle := by
  have e : (fun y : Space => (⟨y 0, y 1⟩ : ℂ)) = fun y => (y 0 : ℂ) + (y 1 : ℂ) * Complex.I := by
    funext y
    apply Complex.ext <;> simp
  have hc : Measurable (fun y : Space => (⟨y 0, y 1⟩ : ℂ)) := by
    rw [e]
    fun_prop
  exact Complex.measurable_arg.comp hc

theorem nearSheet_kernel (m : ℕ) (V : Space → ℝ) (D : CellSumData) (hD : IsCellSumData m V D)
    (a : Fin D.boxCount) (b : Fin D.pieceCount) (mirrored : Bool) (x : Space) (hz : 0 ≤ x 2)
    (hρlo : D.boxRhoLo a ≤ horizontalNorm x) (hρhi : ∀ h, D.boxRhoHi a = some h → horizontalNorm x ≤ h)
    (hzlo : D.boxZLo a ≤ x 2) (hzhi : ∀ h, D.boxZHi a = some h → x 2 ≤ h) (hrule : D.rule a b mirrored = 2) :
    (∫ y in nearSheet m x (D.pieceSolid b) (D.sectorConst m a b) (D.sectorLength a b mirrored),
        1 / (4 * Real.pi * ‖(if mirrored then mirror x else x) - y‖)) ≤
      (D.pieceRhoHi b).getD 0 * (sheetArea (D.sectorLength a b mirrored)
          (Real.sqrt (D.sectorDist m a b mirrored 0 ^ 2 +
            ((D.pieceRhoHi b).getD 0 - D.pieceRhoLo b) * ((D.pieceZHi b).getD 0 - D.pieceZLo b) / Real.pi)) -
        sheetArea (D.sectorLength a b mirrored) (D.sectorDist m a b mirrored 0)) /
        (2 * Real.pi * D.sectorConst m a b) := by
  obtain ⟨hl, hc, hρs, hzs⟩ := hD.near_valid a b mirrored hrule
  obtain ⟨ρH, hρH⟩ := Option.isSome_iff_exists.1 hρs
  obtain ⟨zH, hzH⟩ := Option.isSome_iff_exists.1 hzs
  rw [hρH, hzH, Option.getD_some, Option.getD_some]
  have hpi := Real.pi_pos
  obtain ⟨q1, q2, q3, q4⟩ := hD.piece_box b
  replace q2 := q2 ρH hρH
  replace q4 := q4 zH hzH
  obtain ⟨r1, r2⟩ := hD.box_lower a
  set x' := (if mirrored then mirror x else x) with hx'
  set c := D.sectorConst m a b with hcdef
  set l := D.sectorLength a b mirrored with hldef
  set N := nearSheet m x (D.pieceSolid b) c l with hN
  set ρx := horizontalNorm x with hρx
  set θx := planeAngle x with hθx
  set ζ := x' 2 with hζ
  set pLo := D.pieceRhoLo b with hpLo
  set pHi := ρH with hpHi
  set zLo := D.pieceZLo b with hzLo
  set zHi := zH with hzHi
  set d0 := D.sectorDist m a b mirrored 0 with hd0def
  set D1 := Real.sqrt (d0 ^ 2 + (pHi - pLo) * (zHi - zLo) / Real.pi) with hD1
  have hd0 : 0 ≤ d0 := Real.sqrt_nonneg _
  have hdD : d0 ≤ D1 := by
    rw [hD1]
    calc d0 = Real.sqrt (d0 ^ 2) := (Real.sqrt_sq hd0).symm
      _ ≤ _ := by
        have : 0 ≤ (pHi - pLo) * (zHi - zLo) / Real.pi :=
          div_nonneg (mul_nonneg (by linarith) (by linarith)) hpi.le
        exact Real.sqrt_le_sqrt (by linarith)
  have hgap : ∀ r z, pLo ≤ r → r ≤ pHi → zLo ≤ z → z ≤ zHi → d0 ^ 2 ≤ (ρx - r) ^ 2 + (ζ - z) ^ 2 := by
    intro r z h1 h2 h3 h4
    have e : d0 ^ 2 = gapDist (D.boxRhoLo a) (D.boxRhoHi a) pLo (some pHi) ^ 2 +
        (if mirrored then D.boxZLo a + zLo else gapDist (D.boxZLo a) (D.boxZHi a) zLo (some zHi)) ^ 2 := by
      rw [hd0def]
      unfold CellSumData.sectorDist
      rw [Real.sq_sqrt (by positivity)]
      simp [hpLo, hpHi, hzLo, hzHi, hρH, hzH]
    have hρg := gap_le (D.boxRhoLo a) (D.boxRhoHi a) pLo pHi ρx r hρlo hρhi h1 h2
    rw [e]
    cases mirrored with
    | false =>
      have hzg := gap_le (D.boxZLo a) (D.boxZHi a) zLo zHi (x 2) z hzlo hzhi h3 h4
      simp only [Bool.false_eq_true, if_false] at hzg ⊢
      rw [hζ, hx']
      simp only [Bool.false_eq_true, if_false]
      linarith
    | true =>
      simp only [if_true]
      have hm2 : x' 2 = -x 2 := by rw [hx']; simp [mirror]
      rw [hζ, hm2]
      have : (D.boxZLo a + zLo) ^ 2 ≤ (-x 2 - z) ^ 2 := by
        have e2 : (-x 2 - z) ^ 2 = (x 2 + z) ^ 2 := by ring
        rw [e2]
        exact pow_le_pow_left₀ (add_nonneg r2 q3) (add_le_add hzlo h3) 2
      linarith
  have hstm : Measurable (signedTurn x) := by
    have e : signedTurn x = fun y => toIocMod Real.two_pi_pos (-Real.pi) (planeAngle y - planeAngle x) := by
      funext y
      exact signedTurn_eq x y
    rw [e]
    exact toIocMod_measurable.comp (planeAngle_meas.sub_const _)
  have hNm : MeasurableSet N := by
    have : N = (sectorPart m x (D.pieceSolid b) 0 ∪ sectorPart m x (D.pieceSolid b) (m - 1)) ∩
        {y | |c * signedTurn x y| ≤ l} := rfl
    rw [this]
    exact ((sectorPart_measurable m x _ (hD.solid_measurable b) 0).union
      (sectorPart_measurable m x _ (hD.solid_measurable b) (m - 1))).inter
      (measurableSet_le (hstm.const_mul c).abs measurable_const)
  have hkr : Measurable (fun y : Space => 1 / (4 * Real.pi * ‖x' - y‖)) := by fun_prop
  set F : Space → ENNReal := N.indicator (fun y => ENNReal.ofReal (1 / (4 * Real.pi * ‖x' - y‖))) with hF
  have hFm : Measurable F := (ENNReal.measurable_ofReal.comp hkr).indicator hNm
  set A := Icc pLo pHi ×ˢ Icc zLo zHi with hA
  set P : ℝ × ℝ → ENNReal := A.indicator
    (fun p => ENNReal.ofReal (Real.arsinh (l / Real.sqrt ((ρx - p.1) ^ 2 + (ζ - p.2) ^ 2)))) with hP
  have hPm : Measurable P := by
    refine Measurable.indicator ?_ (measurableSet_Icc.prod measurableSet_Icc)
    exact ENNReal.measurable_ofReal.comp (Real.continuous_arsinh.measurable.comp (by fun_prop))
  set Φ : ℝ → ℝ → ℝ → ENNReal := fun r z u => {u : ℝ | |c * u| ≤ l}.indicator
    (fun u => ENNReal.ofReal (1 / (4 * Real.pi * Real.sqrt (Real.sqrt ((ρx - r) ^ 2 + (ζ - z) ^ 2) ^ 2 + (c * u) ^ 2)))) u
    with hΦ
  set bx : ℝ → ℝ → ENNReal := fun r z => A.indicator (fun _ => (1 : ENNReal)) (r, z) with hbx
  have hbx1 : ∀ r z, bx r z ≠ ⊤ := by
    intro r z
    rw [hbx]
    by_cases h : (r, z) ∈ A
    · simp [indicator_of_mem h]
    · simp [indicator_of_notMem h]
  have step1 : ∫⁻ y in N, ENNReal.ofReal (1 / (4 * Real.pi * ‖x' - y‖)) =
      ∫⁻ z, ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • F (cylSp (polarCoord.symm p, z)) := by
    calc ∫⁻ y in N, ENNReal.ofReal (1 / (4 * Real.pi * ‖x' - y‖)) = ∫⁻ y, F y := (lintegral_indicator hNm _).symm
      _ = ∫⁻ q, F (cylSp q) := (cylSp_mp.lintegral_comp_emb cylSp.measurableEmbedding F).symm
      _ = ∫⁻ z, ∫⁻ p, F (cylSp (p, z)) := by
          rw [Measure.volume_eq_prod (ℝ × ℝ) ℝ]
          exact lintegral_prod_symm (fun q => F (cylSp q)) (hFm.comp cylSp.measurable).aemeasurable
      _ = _ := lintegral_congr fun z => (lintegral_comp_polarCoord_symm (fun p => F (cylSp (p, z)))).symm
  have step2 : ∀ z, z ≠ ζ → ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • F (cylSp (polarCoord.symm p, z)) ≤
      ENNReal.ofReal (pHi / (2 * Real.pi * c)) * ∫⁻ r, P (r, z) := by
    intro z hzne
    have hpt : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 • F (cylSp (polarCoord.symm p, z)) ≤
        ENNReal.ofReal pHi * bx p.1 z * Φ p.1 z (toIocMod Real.two_pi_pos (-Real.pi) (p.2 - θx)) := by
      intro p hp
      have hsymm : polarCoord.symm p = (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := polarCoord_symm_apply p
      rw [hsymm]
      by_cases hy : cylSp ((p.1 * Real.cos p.2, p.1 * Real.sin p.2), z) ∈ N
      · obtain ⟨hbox, hcu, hk⟩ := geom_bound m V D hD a b mirrored x hρlo pHi zHi hρH hzH p.1 p.2 z hp.1 hp.2 hzne hy
        have hmemA : (p.1, z) ∈ A := ⟨⟨hbox.1, hbox.2.1⟩, ⟨hbox.2.2.1, hbox.2.2.2⟩⟩
        rw [hF, indicator_of_mem hy, hbx]
        simp only [indicator_of_mem hmemA, mul_one, hΦ]
        rw [indicator_of_mem (show toIocMod Real.two_pi_pos (-Real.pi) (p.2 - θx) ∈ {u : ℝ | |c * u| ≤ l} from hcu),
          Real.sq_sqrt (by positivity), smul_eq_mul]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal hbox.2.1) (ENNReal.ofReal_le_ofReal hk)
      · rw [hF, indicator_of_notMem hy, smul_zero]
        exact bot_le
    have hΦm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal pHi * bx p.1 z * Φ p.1 z (toIocMod Real.two_pi_pos (-Real.pi) (p.2 - θx))) := by
      have hT : Measurable (fun p : ℝ × ℝ => toIocMod Real.two_pi_pos (-Real.pi) (p.2 - θx)) :=
        toIocMod_measurable.comp (measurable_snd.sub_const _)
      have hAm : MeasurableSet A := measurableSet_Icc.prod measurableSet_Icc
      refine (measurable_const.mul ?_).mul ?_
      · simp only [hbx]
        exact (measurable_const.indicator hAm).comp (measurable_fst.prodMk measurable_const)
      · simp only [hΦ, Set.indicator_apply, Set.mem_ofPred_eq]
        refine Measurable.ite ?_ ?_ measurable_const
        · exact measurableSet_le ((hT.const_mul c).abs) measurable_const
        · exact ENNReal.measurable_ofReal.comp (by fun_prop)
    have hu : ∀ r, ∫⁻ θ in Ioo (-Real.pi) Real.pi, Φ r z (toIocMod Real.two_pi_pos (-Real.pi) (θ - θx)) ≤
        ENNReal.ofReal (Real.arsinh (l / Real.sqrt ((ρx - r) ^ 2 + (ζ - z) ^ 2)) / (2 * Real.pi * c)) := by
      intro r
      have hs : 0 < Real.sqrt ((ρx - r) ^ 2 + (ζ - z) ^ 2) := by
        have : ζ - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzne)
        exact Real.sqrt_pos.2 (by positivity)
      calc ∫⁻ θ in Ioo (-Real.pi) Real.pi, Φ r z (toIocMod Real.two_pi_pos (-Real.pi) (θ - θx))
          ≤ ∫⁻ θ in Ioc (-Real.pi) Real.pi, Φ r z (toIocMod Real.two_pi_pos (-Real.pi) (θ - θx)) :=
            lintegral_mono_set Ioo_subset_Ioc_self
        _ = ∫⁻ u in Ioc (-Real.pi) Real.pi, Φ r z u := periodic_lintegral (Φ r z) θx
        _ ≤ _ := uIntegral_le _ c l hs hc hl
    calc ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • F (cylSp (polarCoord.symm p, z))
        ≤ ∫⁻ p in polarCoord.target, ENNReal.ofReal pHi * bx p.1 z * Φ p.1 z (toIocMod Real.two_pi_pos (-Real.pi) (p.2 - θx)) :=
          setLIntegral_mono' polarCoord.open_target.measurableSet hpt
      _ = ∫⁻ r in Ioi 0, ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal pHi * bx r z * Φ r z (toIocMod Real.two_pi_pos (-Real.pi) (θ - θx)) := by
          rw [polarCoord_target, Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hΦm.aemeasurable]
      _ ≤ ∫⁻ r in Ioi 0, ENNReal.ofReal pHi * bx r z *
            ENNReal.ofReal (Real.arsinh (l / Real.sqrt ((ρx - r) ^ 2 + (ζ - z) ^ 2)) / (2 * Real.pi * c)) := by
          refine lintegral_mono fun r => ?_
          rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hbx1 r z))]
          exact mul_le_mul' le_rfl (hu r)
      _ ≤ ∫⁻ r, ENNReal.ofReal (pHi / (2 * Real.pi * c)) * P (r, z) := by
          refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun r => ?_)
          rw [hbx, hP]
          by_cases h : (r, z) ∈ A
          · simp only [indicator_of_mem h, mul_one]
            rw [← ENNReal.ofReal_mul (q1.trans q2), ← ENNReal.ofReal_mul (div_nonneg (q1.trans q2) (by positivity))]
            apply le_of_eq
            congr 1
            ring
          · simp only [indicator_of_notMem h, mul_zero, zero_mul, le_refl]
      _ = ENNReal.ofReal (pHi / (2 * Real.pi * c)) * ∫⁻ r, P (r, z) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hae : ∀ᵐ z : ℝ ∂volume, z ≠ ζ := by
    rw [ae_iff]
    simp
  have hbound : ∫⁻ y in N, ENNReal.ofReal (1 / (4 * Real.pi * ‖x' - y‖)) ≤
      ENNReal.ofReal (pHi / (2 * Real.pi * c)) * ENNReal.ofReal (2 * Real.pi * (sheetPrim l D1 - sheetPrim l d0)) := by
    rw [step1]
    calc ∫⁻ z, ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • F (cylSp (polarCoord.symm p, z))
        ≤ ∫⁻ z, ENNReal.ofReal (pHi / (2 * Real.pi * c)) * ∫⁻ r, P (r, z) :=
          lintegral_mono_ae (hae.mono fun z hz => step2 z hz)
      _ = ENNReal.ofReal (pHi / (2 * Real.pi * c)) * ∫⁻ p, P p := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, Measure.volume_eq_prod ℝ ℝ,
            lintegral_prod_symm _ hPm.aemeasurable]
      _ ≤ _ := mul_le_mul' le_rfl (planar_le ρx ζ pLo pHi zLo zHi d0 l hl hd0 q2 q4 hgap)
  have hX : 0 ≤ pHi / (2 * Real.pi * c) * (2 * Real.pi * (sheetPrim l D1 - sheetPrim l d0)) := by
    have h1 := sheetPrim_le l d0 D1 hl hd0 hdD
    have h2 : 0 ≤ pHi / (2 * Real.pi * c) := div_nonneg (q1.trans q2) (by positivity)
    exact mul_nonneg h2 (mul_nonneg (by positivity) (by linarith))
  have hRHS : pHi * (sheetArea l D1 - sheetArea l d0) / (2 * Real.pi * c) =
      pHi / (2 * Real.pi * c) * (2 * Real.pi * (sheetPrim l D1 - sheetPrim l d0)) := by
    unfold sheetArea sheetPrim
    ring
  rw [hRHS, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => by show (0:ℝ) ≤ 1 / (4 * Real.pi * ‖x' - y‖); positivity) hkr.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hX (hbound.trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_mul (div_nonneg (q1.trans q2) (by positivity))]

theorem twoSector_near (m : ℕ) (V : Space → ℝ) (D : CellSumData) (hD : IsCellSumData m V D)
    (a : Fin D.boxCount) (b : Fin D.pieceCount) (mirrored : Bool) (x : Space) (hz : 0 ≤ x 2)
    (hρlo : D.boxRhoLo a ≤ horizontalNorm x) (hρhi : ∀ h, D.boxRhoHi a = some h → horizontalNorm x ≤ h)
    (hzlo : D.boxZLo a ≤ x 2) (hzhi : ∀ h, D.boxZHi a = some h → x 2 ≤ h) (hrule : D.rule a b mirrored = 2) :
    (∫ y in sectorPart m x (D.pieceSolid b) 0 ∪ sectorPart m x (D.pieceSolid b) (m - 1),
      V y / (4 * Real.pi * ‖(if mirrored then mirror x else x) - y‖)) ≤ D.nearTerm m a b mirrored :=
  twoSector_near_of_sheet m V D hD a b mirrored x hz hρlo hρhi hzlo hzhi hrule
    (nearSheet_kernel m V D hD a b mirrored x hz hρlo hρhi hzlo hzhi hrule)

end KernelSectors

end Reduction

end CellCert

end Breakdown
