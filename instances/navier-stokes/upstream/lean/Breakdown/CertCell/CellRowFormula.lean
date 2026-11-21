import Breakdown.CertCell.RowProfileDefs

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

namespace Internal.RowForm

theorem rect_meas (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem rect_cpt (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

theorem fst_nonneg {K : CellBox} (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) : 0 ≤ p.1 :=
  hK.r_order.1.trans hp.1.1

theorem eval_cont (K : CellBox) (P : CellPoly) : Continuous (fun p : ℝ × ℝ => P.eval K p) := by
  unfold CellPoly.eval CellBox.refR CellBox.refZ
  fun_prop

theorem ofReal_contDiff {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 (fun p => (f p : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hf

theorem eval_contDiff (K : CellBox) (P : CellPoly) : ContDiff ℝ 1 (fun p : ℝ × ℝ => P.eval K p) := by
  unfold CellPoly.eval
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  refine (contDiff_const.mul ((ofReal_contDiff ?_).pow _)).mul ((ofReal_contDiff ?_).pow _)
  · unfold CellBox.refR; fun_prop
  · unfold CellBox.refZ; fun_prop

theorem radial_cont {ψ : ℝ × ℝ → ℂ} (hψ : ContDiff ℝ 1 ψ) : Continuous (CellBox.radialDeriv ψ) := by
  have e : CellBox.radialDeriv ψ = fun p => fderiv ℝ ψ p (1, 0) := by
    funext p
    obtain ⟨r, z⟩ := p
    exact (((hψ.differentiable one_ne_zero) (r, z)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id' r).prodMk (hasDerivAt_const r z))).deriv
  rw [e]
  exact (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem height_cont {ψ : ℝ × ℝ → ℂ} (hψ : ContDiff ℝ 1 ψ) : Continuous (CellBox.heightDeriv ψ) := by
  have e : CellBox.heightDeriv ψ = fun p => fderiv ℝ ψ p (0, 1) := by
    funext p
    obtain ⟨r, z⟩ := p
    exact (((hψ.differentiable one_ne_zero) (r, z)).hasFDerivAt.comp_hasDerivAt z
      ((hasDerivAt_const z r).prodMk (hasDerivAt_id' z))).deriv
  rw [e]
  exact (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem weighted_int {K : CellBox} (hK : IsCellBox K) {g t : ℝ × ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict K.rect))
    (hg2 : IntegrableOn (fun p => p.1 * ‖g p‖ ^ 2) K.rect)
    (ht : AEStronglyMeasurable t (volume.restrict K.rect)) {M : ℝ} (hM : ∀ p ∈ K.rect, ‖t p‖ ≤ M) :
    IntegrableOn (fun p => (p.1 : ℂ) * g p * t p) K.rect := by
  have h1 : IntegrableOn (fun p : ℝ × ℝ => p.1) K.rect :=
    continuous_fst.continuousOn.integrableOn_compact (rect_cpt K)
  refine Integrable.mono' ((Integrable.const_mul hg2 |M|).add (Integrable.const_mul h1 |M|))
    (((Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul hg).mul ht) ?_
  filter_upwards [ae_restrict_mem (rect_meas K)] with p hp
  have h0 := fst_nonneg hK hp
  have hn : 0 ≤ ‖g p‖ := norm_nonneg _
  have htM : ‖t p‖ ≤ |M| := (hM p hp).trans (le_abs_self M)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
  have hgle : ‖g p‖ ≤ ‖g p‖ ^ 2 + 1 := by nlinarith [sq_nonneg (‖g p‖ - 1)]
  calc p.1 * ‖g p‖ * ‖t p‖ ≤ p.1 * ‖g p‖ * |M| := mul_le_mul_of_nonneg_left htM (mul_nonneg h0 hn)
    _ ≤ p.1 * (‖g p‖ ^ 2 + 1) * |M| := by gcongr
    _ = |M| * (p.1 * ‖g p‖ ^ 2) + |M| * p.1 := by ring

theorem weighted_int_cont {K : CellBox} (hK : IsCellBox K) {g t : ℝ × ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict K.rect))
    (hg2 : IntegrableOn (fun p => p.1 * ‖g p‖ ^ 2) K.rect) (ht : Continuous t) :
    IntegrableOn (fun p => (p.1 : ℂ) * g p * t p) K.rect := by
  obtain ⟨M, hM⟩ := (rect_cpt K).exists_bound_of_continuousOn ht.continuousOn
  exact weighted_int hK hg hg2 ht.aestronglyMeasurable hM

theorem comp_int {K : CellBox} (hK : IsCellBox K) {F : ℝ × ℝ → ℝ} (hF : IntegrableOn F K.rect)
    {h : ℝ × ℝ → ℂ} (hh : AEStronglyMeasurable h (volume.restrict K.rect))
    (hle : ∀ p ∈ K.rect, p.1 * ‖h p‖ ^ 2 ≤ F p) : IntegrableOn (fun p => p.1 * ‖h p‖ ^ 2) K.rect := by
  refine Integrable.mono' hF (continuous_fst.aestronglyMeasurable.mul (hh.norm.pow 2)) ?_
  filter_upwards [ae_restrict_mem (rect_meas K)] with p hp
  rw [Real.norm_of_nonneg (mul_nonneg (fst_nonneg hK hp) (sq_nonneg _))]
  exact hle p hp

theorem cnormSq_nonneg (x : Fin 3 → ℂ) : 0 ≤ cnormSq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem le_cnormSq (x : Fin 3 → ℂ) (a : Fin 3) : ‖x a‖ ^ 2 ≤ cnormSq x :=
  Finset.single_le_sum (f := fun b => ‖x b‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ a)

theorem vec_int {K : CellBox} (hK : IsCellBox K) (F : ℝ × ℝ → ℝ)
    (hF : IntegrableOn (fun p => p.1 * F p) K.rect) {g : ℝ × ℝ → Fin 3 → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict K.rect)) (hle : ∀ p ∈ K.rect, cnormSq (g p) ≤ F p)
    (a : Fin 3) : IntegrableOn (fun p => p.1 * ‖g p a‖ ^ 2) K.rect :=
  comp_int hK hF ((continuous_apply a).comp_aestronglyMeasurable hg) fun p hp =>
    mul_le_mul_of_nonneg_left ((le_cnormSq _ a).trans (hle p hp)) (fst_nonneg hK hp)

theorem pair_int {K : CellBox} (hK : IsCellBox K) (φ : Fin 3 → CellPoly) {g : ℝ × ℝ → Fin 3 → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict K.rect))
    (hg2 : ∀ a, IntegrableOn (fun p => p.1 * ‖g p a‖ ^ 2) K.rect) :
    IntegrableOn (fun p => (p.1 : ℂ) * cdot3 (g p) (testValue K φ p)) K.rect := by
  have e : (fun p => (p.1 : ℂ) * cdot3 (g p) (testValue K φ p))
      = fun p => ∑ a : Fin 3, (p.1 : ℂ) * g p a * (starRingEnd ℂ) ((φ a).eval K p) := by
    funext p
    simp only [cdot3, testValue, Finset.mul_sum, mul_assoc]
  rw [e]
  refine integrable_finsetSum _ fun a _ => ?_
  exact weighted_int_cont hK ((continuous_apply a).comp_aestronglyMeasurable hg) (hg2 a)
    (Complex.continuous_conj.comp (eval_cont K (φ a)))

theorem turn_cont (k : ℝ) (a : Fin 3) : Continuous (fun x : Fin 3 → ℂ => turnVector k x a) := by
  have h : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
  rcases h with rfl | rfl | rfl <;> simp only [turnVector] <;> simp <;> fun_prop

theorem testValue_cont (K : CellBox) (φ : Fin 3 → CellPoly) : Continuous (testValue K φ) :=
  continuous_pi fun a => eval_cont K (φ a)

theorem testGrad_meas (K : CellBox) (k : ℝ) (φ : Fin 3 → CellPoly) (a b : Fin 3) :
    AEStronglyMeasurable (fun p => (starRingEnd ℂ) (testGrad K k φ p a b)) (volume.restrict K.rect) := by
  refine (Complex.continuous_conj.measurable.comp ?_).aestronglyMeasurable
  have h : b = 0 ∨ b = 1 ∨ b = 2 := by fin_cases b <;> simp
  rcases h with rfl | rfl | rfl
  · simp only [testGrad]
    exact (radial_cont (eval_contDiff K (φ a))).measurable
  · simp only [testGrad, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, if_false]
    exact ((turn_cont k a).comp (testValue_cont K φ)).measurable.div
      (Complex.measurable_ofReal.comp measurable_fst)
  · simp only [testGrad, show (2 : Fin 3) ≠ 0 by decide, if_false]
    exact (height_cont (eval_contDiff K (φ a))).measurable

theorem testGrad_bound {K : CellBox} (hK : IsCellBox K) (k : ℝ) {φ : Fin 3 → CellPoly}
    (hreg : IsAxisRegularTest K k φ) (a b : Fin 3) :
    ∃ M : ℝ, ∀ p ∈ K.rect, ‖(starRingEnd ℂ) (testGrad K k φ p a b)‖ ≤ M := by
  simp only [Complex.norm_conj]
  have h : b = 0 ∨ b = 1 ∨ b = 2 := by fin_cases b <;> simp
  rcases h with rfl | rfl | rfl
  · simp only [testGrad]
    exact (rect_cpt K).exists_bound_of_continuousOn (radial_cont (eval_contDiff K (φ a))).continuousOn
  · obtain ⟨C, hC⟩ := hreg
    refine ⟨|C|, fun p hp => ?_⟩
    simp only [testGrad, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, if_false]
    have h0 := fst_nonneg hK hp
    rcases h0.eq_or_lt with h1 | h1
    · rw [← h1]; simp
    · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg h0, div_le_iff₀ h1]
      exact (hC p hp a).trans (mul_le_mul_of_nonneg_right (le_abs_self C) h0)
  · simp only [testGrad, show (2 : Fin 3) ≠ 0 by decide, if_false]
    exact (rect_cpt K).exists_bound_of_continuousOn (height_cont (eval_contDiff K (φ a))).continuousOn

theorem five_split {μ : Measure (ℝ × ℝ)} {a l c d q : ℝ × ℝ → ℂ} (ha : Integrable a μ)
    (hl : Integrable l μ) (hc : Integrable c μ) (hd : Integrable d μ) (hq : Integrable q μ) :
    ∫ x, a x - l x + c x + d x + q x ∂μ
      = (∫ x, a x ∂μ) - (∫ x, l x ∂μ) + (∫ x, c x ∂μ) + (∫ x, d x ∂μ) + ∫ x, q x ∂μ := by
  have h4 : Integrable (fun x => a x - l x + c x + d x) μ := ((ha.sub hl).add hc).add hd
  have h3 : Integrable (fun x => a x - l x + c x) μ := (ha.sub hl).add hc
  have h2 : Integrable (fun x => a x - l x) μ := ha.sub hl
  rw [integral_add h4 hq, integral_add h3 hd, integral_add h2 hc, integral_sub ha hl]

end Internal.RowForm

open Internal.RowForm in
theorem cellRowFormula_holds : CellRowFormulaStatement := by
  intro K hK k freq R hR couple drive f hc hd hcd hf φ hsol hreg
  obtain ⟨hmv, hmg, hml, hmp⟩ := hR.measurable
  have hF := hR.integrable
  have hsg : ∀ p, 0 ≤ ∑ a : Fin 3, cnormSq (R.grad p a) := fun p => Finset.sum_nonneg fun a _ => cnormSq_nonneg _
  have hvI := vec_int hK _ hF hmv fun p _ => by
    linarith [cnormSq_nonneg (R.lap p), cnormSq_nonneg (R.presGrad p), hsg p]
  have hlI := vec_int hK _ hF hml fun p _ => by
    linarith [cnormSq_nonneg (R.vel p), cnormSq_nonneg (R.presGrad p), hsg p]
  have hpI := vec_int hK _ hF hmp fun p _ => by
    linarith [cnormSq_nonneg (R.lap p), cnormSq_nonneg (R.vel p), hsg p]
  have hgI : ∀ a, ∀ b, IntegrableOn (fun p => p.1 * ‖R.grad p a b‖ ^ 2) K.rect := fun a =>
    vec_int hK _ hF ((continuous_apply a).comp_aestronglyMeasurable hmg) fun p _ => by
      have := Finset.single_le_sum (f := fun a => cnormSq (R.grad p a))
        (fun _ _ => cnormSq_nonneg _) (Finset.mem_univ a)
      linarith [cnormSq_nonneg (R.lap p), cnormSq_nonneg (R.vel p), cnormSq_nonneg (R.presGrad p)]
  have hcI := vec_int hK _ hcd hc fun p _ => by linarith [cnormSq_nonneg (drive p)]
  have hdI := vec_int hK _ hcd hd fun p _ => by linarith [cnormSq_nonneg (couple p)]
  have hmg2 : ∀ a b, AEStronglyMeasurable (fun p => R.grad p a b) (volume.restrict K.rect) := fun a b =>
    (continuous_apply b).comp_aestronglyMeasurable ((continuous_apply a).comp_aestronglyMeasurable hmg)
  have hmv2 : ∀ a, AEStronglyMeasurable (fun p => R.vel p a) (volume.restrict K.rect) := fun a =>
    (continuous_apply a).comp_aestronglyMeasurable hmv
  have IL := pair_int hK φ hml hlI
  have IP := pair_int hK φ hmp hpI
  have IC := pair_int hK φ hc hcI
  have ID := pair_int hK φ hd hdI
  have IS : IntegrableOn (fun p => (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
      R.grad p a b * (starRingEnd ℂ) (testGrad K k φ p a b)) K.rect := by
    have e : (fun p => (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
        R.grad p a b * (starRingEnd ℂ) (testGrad K k φ p a b))
        = fun p => ∑ a : Fin 3, ∑ b : Fin 3,
          (p.1 : ℂ) * R.grad p a b * (starRingEnd ℂ) (testGrad K k φ p a b) := by
      funext p
      simp only [Finset.mul_sum, mul_assoc]
    rw [e]
    refine integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_
    obtain ⟨M, hM⟩ := testGrad_bound hK k hreg a b
    exact weighted_int hK (hmg2 a b) (hgI a b) (testGrad_meas K k φ a b) hM
  have IA : IntegrableOn (fun p => (p.1 : ℂ) * cdot3 (fun a => ((freq : ℂ) * Complex.I + 1 / 2) * R.vel p a
      + (1 / 2 : ℂ) * ((p.1 : ℂ) * R.grad p a 0 + (p.2 : ℂ) * R.grad p a 2)) (testValue K φ p)) K.rect := by
    have e : (fun p => (p.1 : ℂ) * cdot3 (fun a => ((freq : ℂ) * Complex.I + 1 / 2) * R.vel p a
        + (1 / 2 : ℂ) * ((p.1 : ℂ) * R.grad p a 0 + (p.2 : ℂ) * R.grad p a 2)) (testValue K φ p))
        = fun p => ∑ a : Fin 3, ((p.1 : ℂ) * R.vel p a
            * (((freq : ℂ) * Complex.I + 1 / 2) * (starRingEnd ℂ) ((φ a).eval K p))
          + (p.1 : ℂ) * R.grad p a 0 * ((1 / 2 : ℂ) * (p.1 : ℂ) * (starRingEnd ℂ) ((φ a).eval K p))
          + (p.1 : ℂ) * R.grad p a 2 * ((1 / 2 : ℂ) * (p.2 : ℂ) * (starRingEnd ℂ) ((φ a).eval K p))) := by
      funext p
      simp only [cdot3, testValue, Fin.sum_univ_three]
      ring
    rw [e]
    refine integrable_finsetSum _ fun a _ => ?_
    have hcj := Complex.continuous_conj.comp (eval_cont K (φ a))
    refine ((weighted_int_cont hK (hmv2 a) (hvI a) (continuous_const.mul hcj)).add
      (weighted_int_cont hK (hmg2 a 0) (hgI a 0) ?_)).add
      (weighted_int_cont hK (hmg2 a 2) (hgI a 2) ?_)
    · exact (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)).mul hcj
    · exact (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)).mul hcj
  have e1 : rowPairing K f φ = ∫ p in K.rect,
      (((p.1 : ℂ) * cdot3 (fun a => ((freq : ℂ) * Complex.I + 1 / 2) * R.vel p a
          + (1 / 2 : ℂ) * ((p.1 : ℂ) * R.grad p a 0 + (p.2 : ℂ) * R.grad p a 2)) (testValue K φ p)
        - (p.1 : ℂ) * cdot3 (R.lap p) (testValue K φ p)
        + (p.1 : ℂ) * cdot3 (couple p) (testValue K φ p)
        + (p.1 : ℂ) * cdot3 (drive p) (testValue K φ p))
        + (p.1 : ℂ) * cdot3 (R.presGrad p) (testValue K φ p)) := by
    unfold rowPairing
    refine setIntegral_congr_fun (rect_meas K) fun p hp => ?_
    simp only [hf p hp, cdot3, Fin.sum_univ_three]
    ring
  have e2 : rowVolume K k freq R φ = (∫ p in K.rect, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
      R.grad p a b * (starRingEnd ℂ) (testGrad K k φ p a b))
      + ∫ p in K.rect, (p.1 : ℂ) * cdot3 (fun a => ((freq : ℂ) * Complex.I + 1 / 2) * R.vel p a
          + (1 / 2 : ℂ) * ((p.1 : ℂ) * R.grad p a 0 + (p.2 : ℂ) * R.grad p a 2)) (testValue K φ p) := by
    unfold rowVolume
    rw [← integral_add IS IA]
    congr 1
    funext p
    exact mul_add _ _ _
  have hl := hR.laplacian_parts φ hreg
  have hp := hR.pressure_parts φ hsol hreg
  unfold rowPairing at hl hp
  rw [e1, five_split IA IL IC ID IP, e2]
  unfold rowPairing
  linear_combination (-1 : ℂ) * hl + hp

end CellCalculus

end CertCell

end Breakdown
