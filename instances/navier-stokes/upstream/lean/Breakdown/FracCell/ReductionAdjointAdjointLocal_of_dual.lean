import Breakdown.FracCell.ReductionAdjointDefs
import Breakdown.FracCell.AdjointConvectionPairing
import Breakdown.FracCert.HeldStateLimitAApply

open MeasureTheory
open scoped ContDiff ENNReal

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

namespace AdjointLocalInternal

theorem abs_integral_le_sqrt_mul {f u w : Space → ℝ} (hf : AEStronglyMeasurable f volume) (hu : AEStronglyMeasurable u volume)
    (hw : AEStronglyMeasurable w volume) (hu0 : ∀ y, 0 ≤ u y) (hw0 : ∀ y, 0 ≤ w y)
    (hu2 : Integrable (fun y => u y ^ 2)) (hw2 : Integrable (fun y => w y ^ 2))
    (h : ∀ᵐ y ∂volume, |f y| ≤ u y * w y) :
    Integrable f ∧ |∫ y, f y| ≤ Real.sqrt (∫ y, u y ^ 2) * Real.sqrt (∫ y, w y ^ 2) := by
  have hU : MemLp u (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]; exact (memLp_two_iff_integrable_sq hu).2 hu2
  have hW : MemLp w (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]; exact (memLp_two_iff_integrable_sq hw).2 hw2
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hu0) (Filter.Eventually.of_forall hw0) hU hW
  have hint : Integrable (fun y => u y * w y) := by
    refine ((hu2.add hw2).div_const 2).mono' (hu.mul hw) (Filter.Eventually.of_forall fun y => ?_)
    show ‖u y * w y‖ ≤ (u y ^ 2 + w y ^ 2) / 2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hu0 y) (hw0 y))]
    nlinarith [sq_nonneg (u y - w y)]
  refine ⟨hint.mono' hf (h.mono fun y hy => by rw [Real.norm_eq_abs]; exact hy), ?_⟩
  calc |∫ y, f y| ≤ ∫ y, |f y| := abs_integral_le_integral_abs
    _ ≤ ∫ y, u y * w y := integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _) hint h
    _ ≤ _ := by
      refine hH.trans (le_of_eq ?_)
      simp only [Real.rpow_two, Real.sqrt_eq_rpow]

theorem entrySq_nonneg (K : Space →L[ℝ] Space) : 0 ≤ entrySq K :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

theorem entrySq_cont : Continuous (fun K : Space →L[ℝ] Space => entrySq K) := by
  unfold entrySq; fun_prop

theorem trace_cont : Continuous (fun K : Space →L[ℝ] Space →L[ℝ] Space => secondTrace K) := by
  unfold secondTrace; fun_prop

theorem entryInner_le (G K : Space →L[ℝ] Space) :
    |entryInner G K| ≤ Real.sqrt (entrySq G) * Real.sqrt (entrySq K) := by
  unfold entryInner entrySq
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => abs_real_inner_le_norm (G (unitVector i)) (K (unitVector i))).trans ?_
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem trace_sq_le (K : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖secondTrace K‖ ^ 2 ≤ 3 * ∑ i : Fin 3, ∑ j : Fin 3, ‖K (unitVector i) (unitVector j)‖ ^ 2 := by
  unfold secondTrace
  simp only [Fin.sum_univ_three]
  have h0 : ‖K (unitVector 0) (unitVector 0) + K (unitVector 1) (unitVector 1) + K (unitVector 2) (unitVector 2)‖
      ≤ ‖K (unitVector 0) (unitVector 0)‖ + ‖K (unitVector 1) (unitVector 1)‖ + ‖K (unitVector 2) (unitVector 2)‖ :=
    norm_add₃_le
  have h1 := pow_le_pow_left₀ (norm_nonneg _) h0 2
  nlinarith [sq_nonneg (‖K (unitVector 0) (unitVector 0)‖ - ‖K (unitVector 1) (unitVector 1)‖),
    sq_nonneg (‖K (unitVector 1) (unitVector 1)‖ - ‖K (unitVector 2) (unitVector 2)‖),
    sq_nonneg (‖K (unitVector 0) (unitVector 0)‖ - ‖K (unitVector 2) (unitVector 2)‖),
    sq_nonneg ‖K (unitVector 0) (unitVector 1)‖, sq_nonneg ‖K (unitVector 0) (unitVector 2)‖,
    sq_nonneg ‖K (unitVector 1) (unitVector 0)‖, sq_nonneg ‖K (unitVector 1) (unitVector 2)‖,
    sq_nonneg ‖K (unitVector 2) (unitVector 0)‖, sq_nonneg ‖K (unitVector 2) (unitVector 1)‖]

theorem ae_ne_zero : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
  exact measure_singleton 0

theorem pair_entry {G K : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume)
    (hK : AEStronglyMeasurable K volume) (hGi : Integrable (fun y => entrySq (G y)))
    (hKi : Integrable (fun y => entrySq (K y))) :
    |∫ y, entryInner (G y) (K y)| ≤ Real.sqrt (∫ y, entrySq (G y)) * Real.sqrt (∫ y, entrySq (K y)) := by
  have hfm : AEStronglyMeasurable (fun y => entryInner (G y) (K y)) volume := by
    unfold entryInner
    fun_prop
  have h := abs_integral_le_sqrt_mul (u := fun y => Real.sqrt (entrySq (G y))) (w := fun y => Real.sqrt (entrySq (K y))) hfm
    (Real.continuous_sqrt.comp_aestronglyMeasurable (entrySq_cont.comp_aestronglyMeasurable hG))
    (Real.continuous_sqrt.comp_aestronglyMeasurable (entrySq_cont.comp_aestronglyMeasurable hK))
    (fun y => Real.sqrt_nonneg _) (fun y => Real.sqrt_nonneg _)
    (by simpa only [Real.sq_sqrt (entrySq_nonneg _)] using hGi)
    (by simpa only [Real.sq_sqrt (entrySq_nonneg _)] using hKi)
    (Filter.Eventually.of_forall fun y => entryInner_le _ _)
  simpa only [Real.sq_sqrt (entrySq_nonneg _)] using h.2

theorem mul_add_mul_le_sqrt {a b A B w : ℝ} (hw : 0 < w) :
    a * A + b * B ≤ Real.sqrt (A ^ 2 + B ^ 2 / w) * Real.sqrt (a ^ 2 + w * b ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  set X := B / w with hX
  have hB : B = X * w := by rw [hX]; field_simp
  have hB2 : B ^ 2 / w = X ^ 2 * w := by rw [hB]; field_simp
  rw [hB2, hB]
  nlinarith [mul_nonneg hw.le (sq_nonneg (A * b - X * a))]

end AdjointLocalInternal

open AdjointLocalInternal

theorem adjointLocal_of_dual (hR : AdjointRepresentationStatement) (hW : WeightedInverseSquareStatement) (Hc : ℝ)
    (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4) {k N : ℕ} (d : FracCertData k N)
    (hH : InverseSquareConstStatement d.order Hc) (hw : 0 < d.weightMin) (hlow : ∀ y, d.weightMin ≤ d.weight y)
    (hmeas : Measurable d.weight) (hhigh : ∀ y, d.weight y ≤ d.weightMax)
    (hprof : ∀ p ∈ box d.radius, ContDiff ℝ 1 (d.profile p) ∧ (∀ y, divergenceAt (d.profile p) y = 0) ∧
      ∃ K : ℝ, ∀ y, ‖d.profile p y‖ ≤ K * (1 + ‖y‖)⁻¹ ∧ ‖d.gradProfile p y‖ ≤ K * (1 + ‖y‖) ^ (-2 : ℝ))
    (hsol : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, IsSolenoidalL2 (d.adjoint j p))
    (D : Fin k → (Fin k → ℝ) → AdjointDual k)
    (hD : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, IsAdjointDual α d j p (D j p))
    (hbound : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius,
      Real.sqrt ((D j p).dualBound ^ 2 + ((D j p).potentialScale * (D j p).potentialBound + (D j p).fluxBound
        + (D j p).inverseSquareBound
        + ∑ i ∈ Finset.univ \ (D j p).exactSet, |p i| * ((D j p).shiftBound i + Hc * (D j p).shiftGradBound i)) ^ 2
          / d.weightMin) ≤ d.adjointLocal j p) :
    ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, ∀ v G H, IsSecondOrderField d.order v G H →
      ∀ P, IsWeakFractionalPower α v P → MemLp (driftField α (d.rotationRate p) v G) 2 volume →
        |l2Pair (d.localField α p v G H 0) (d.adjoint j p) + l2Pair (negSecondTrace H) (d.adjointSharp j p)
          - ∑ l, d.adjointPin j p l * pinValue (d.smoothPin l) G| ≤ d.adjointLocal j p * Real.sqrt (d.energy G H) := by
  intro j hj p hp v G H hv P _hP hdrift
  obtain ⟨hprofC, hprofdiv, hprofdec⟩ := hprof p hp
  have hDd := hD j hj p hp
  have hb := hbound j hj p hp
  rw [hR α hα₁ hα₂ d j p (D j p) hDd hprofC hprofdiv hprofdec (hsol j hj p hp) v G H hv hdrift]
  generalize D j p = E at hDd hb ⊢
  set ζ := d.adjoint j p with hζ
  have hζm : AEStronglyMeasurable ζ volume := hDd.adjoint_measurable.1
  have hGm := hv.measurable_gradient
  have hGi := hv.gradient_two
  have hvm := hv.measurable_velocity
  set b := Real.sqrt (∫ y, entrySq (G y)) with hbdef
  set a := Real.sqrt (∫ y, ‖secondTrace (H y)‖ ^ 2) with hadef
  obtain ⟨hHc0, hHcv⟩ := hH
  obtain ⟨hinvI, hinvle⟩ := hHcv v G H hv
  set h := Real.sqrt (∫ y, ‖v y‖ ^ 2 / ‖y‖ ^ 2) with hhdef
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hh : h ≤ Hc * b := by
    rw [hhdef, hbdef, ← Real.sqrt_sq hHc0, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt hinvle
  have htrm : AEStronglyMeasurable (fun y => secondTrace (H y)) volume :=
    trace_cont.comp_aestronglyMeasurable hv.measurable_second
  have htri : Integrable (fun y => ‖secondTrace (H y)‖ ^ 2) := by
    refine (hv.second_two.const_mul 3).mono' (htrm.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact trace_sq_le _
  have hvq : Integrable (fun y => (‖v y‖ / ‖y‖) ^ 2) := by
    simpa only [div_pow] using hinvI
  have hvqm : AEStronglyMeasurable (fun y => ‖v y‖ / ‖y‖) volume :=
    (hvm.norm.aemeasurable.div measurable_norm.aemeasurable).aestronglyMeasurable
  have hvq' : (∫ y, (‖v y‖ / ‖y‖) ^ 2) = ∫ y, ‖v y‖ ^ 2 / ‖y‖ ^ 2 := by
    simp only [div_pow]
  have h1 : |l2Pair (negSecondTrace H) E.dualField| ≤ a * E.dualBound := by
    have hmT : MemLp (negSecondTrace H) 2 volume := by
      refine (memLp_two_iff_integrable_sq_norm (f := negSecondTrace H) (by unfold negSecondTrace; exact htrm.neg)).2 ?_
      simpa only [negSecondTrace, norm_neg] using htri
    have hc := ApplyPairingInternal.abs_pair_le hmT hDd.dual_two.1
    have he : (∫ y, ‖negSecondTrace H y‖ ^ 2) = ∫ y, ‖secondTrace (H y)‖ ^ 2 := by
      simp only [negSecondTrace, norm_neg]
    rw [he] at hc
    exact hc.trans (mul_le_mul_of_nonneg_left hDd.dual_bound ha0)
  have h2 : |E.potentialScale * ∫ y, entryInner (G y) (E.potentialGrad y)| ≤
      E.potentialScale * E.potentialBound * b := by
    rw [abs_mul, abs_of_nonneg hDd.potentialScale_nonneg, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hDd.potentialScale_nonneg
    refine (pair_entry hGm hDd.potential_two.2.1 hGi hDd.potential_two.2.2.1).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hDd.potential_bound hb0
  have h3 : |∫ y, entryInner (G y) (E.fluxField y)| ≤ E.fluxBound * b := by
    refine (pair_entry hGm hDd.flux_two.1 hGi hDd.flux_two.2.1).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hDd.flux_bound hb0
  set F := E.inverseSquarePart with hF
  have hFm : AEStronglyMeasurable F volume := hDd.inverseSquare_part.1
  have hFw : MemLp (fun y => ‖y‖ • F y) 2 volume := hDd.inverseSquare_part.2
  have hsumeq : harmonicWeightSq F = harmonicWeightSqOn E.inverseSquareModes F := by
    unfold harmonicWeightSq harmonicWeightSqOn
    refine tsum_eq_sum (fun n hn => ?_)
    have e1 : ∀ ρ z : ℝ, angularMode (horizontalPart F) n ρ z = 0 := fun ρ z => (hDd.inverseSquare_modes n hn ρ z).1
    have e2 : ∀ ρ z : ℝ, angularMode (verticalPart F) n ρ z = 0 := fun ρ z => (hDd.inverseSquare_modes n hn ρ z).2
    simp [e1, e2]
  have hwle : harmonicWeightSq F ≤ ENNReal.ofReal (E.inverseSquareBound ^ 2) := by
    rw [hsumeq]; exact hDd.inverseSquare_weight
  have hne : harmonicWeightSq F ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hwle
  have hsq : Real.sqrt (harmonicWeightSq F).toReal ≤ E.inverseSquareBound := by
    have := ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) hwle
    calc Real.sqrt (harmonicWeightSq F).toReal ≤ Real.sqrt (E.inverseSquareBound ^ 2) := Real.sqrt_le_sqrt this
      _ = E.inverseSquareBound := Real.sqrt_sq hDd.inverseSquareBound_nonneg
  have h4 : |∫ y, inner ℝ (v y) (F y)| ≤ E.inverseSquareBound * b :=
    (hW d.order v G H hv F hFm hFw hne).trans (mul_le_mul_of_nonneg_right hsq hb0)
  have hFwi : Integrable (fun y => (‖y‖ * ‖F y‖) ^ 2) := by
    have := (memLp_two_iff_integrable_sq_norm hFw.1).1 hFw
    simpa only [norm_smul, norm_norm] using this
  have h4i : Integrable (fun y => inner ℝ (v y) (F y)) := by
    refine (abs_integral_le_sqrt_mul (u := fun y => ‖v y‖ / ‖y‖) (w := fun y => ‖y‖ * ‖F y‖)
      (hvm.inner hFm) hvqm (continuous_norm.aestronglyMeasurable.mul hFm.norm)
      (fun y => by positivity) (fun y => by positivity) hvq hFwi ?_).1
    filter_upwards [ae_ne_zero] with y hy
    have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
    refine (abs_real_inner_le_norm _ _).trans (le_of_eq ?_)
    field_simp
  have hshift : ∀ i, Integrable (fun y => inner ℝ (v y)
      (convectionAdjointField (E.shiftField i) (E.shiftGrad i) ζ E.adjointGrad y)) ∧
      |∫ y, inner ℝ (v y) (convectionAdjointField (E.shiftField i) (E.shiftGrad i) ζ E.adjointGrad y)|
        ≤ (E.shiftBound i + Hc * E.shiftGradBound i) * b := by
    intro i
    obtain ⟨hSc, hDS, hdiv, hdec⟩ := hDd.shift_regular i
    obtain ⟨hI, heq⟩ := convectionPairing_eq hDd.adjoint_regular hζm hSc hDS hdiv hdec hv hinvI
    refine ⟨hI, ?_⟩
    rw [heq]
    have hDSc : Continuous (E.shiftGrad i) := by
      rw [show E.shiftGrad i = fun y => fderiv ℝ (E.shiftField i) y from funext hDS]
      exact hSc.continuous_fderiv one_ne_zero
    obtain ⟨hw1, hw2⟩ := hDd.shift_weighted i
    have hk1 : |∫ y, inner ℝ (ζ y) (G y (E.shiftField i y))| ≤ E.shiftBound i * b := by
      have hc := abs_integral_le_sqrt_mul (u := fun y => ‖E.shiftField i y‖ * ‖ζ y‖)
        (w := fun y => Real.sqrt (entrySq (G y)))
        (hζm.inner (ApplyPairingInternal.apply_meas hGm hSc.continuous.aestronglyMeasurable))
        (hSc.continuous.norm.aestronglyMeasurable.mul hζm.norm)
        (Real.continuous_sqrt.comp_aestronglyMeasurable (entrySq_cont.comp_aestronglyMeasurable hGm))
        (fun y => by positivity) (fun y => Real.sqrt_nonneg _)
        (by simpa only [mul_pow] using hw1)
        (by simpa only [Real.sq_sqrt (entrySq_nonneg _)] using hGi)
        (Filter.Eventually.of_forall fun y => ?_)
      · simp only [mul_pow, Real.sq_sqrt (entrySq_nonneg _)] at hc
        exact hc.2.trans (mul_le_mul_of_nonneg_right (hDd.shift_bound i) hb0)
      · refine (abs_real_inner_le_norm _ _).trans ?_
        have := ApplyPairingInternal.apply_norm_le (G y) (E.shiftField i y)
        calc ‖ζ y‖ * ‖G y (E.shiftField i y)‖ ≤ ‖ζ y‖ * (Real.sqrt (entrySq (G y)) * ‖E.shiftField i y‖) :=
              mul_le_mul_of_nonneg_left this (norm_nonneg _)
          _ = _ := by ring
    have hk2 : |∫ y, inner ℝ (ζ y) (E.shiftGrad i y (v y))| ≤ E.shiftGradBound i * h := by
      have hc := abs_integral_le_sqrt_mul (u := fun y => ‖y‖ * ‖E.shiftGrad i y‖ * ‖ζ y‖) (w := fun y => ‖v y‖ / ‖y‖)
        (hζm.inner (ApplyPairingInternal.apply_meas hDSc.aestronglyMeasurable hvm))
        ((continuous_norm.mul hDSc.norm).aestronglyMeasurable.mul hζm.norm) hvqm
        (fun y => by positivity) (fun y => by positivity)
        (by simpa only [mul_pow] using hw2) hvq ?_
      · rw [hvq'] at hc
        simp only [mul_pow] at hc
        exact hc.2.trans (mul_le_mul_of_nonneg_right (hDd.shiftGrad_bound i) (Real.sqrt_nonneg _))
      · filter_upwards [ae_ne_zero] with y hy
        have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
        refine (abs_real_inner_le_norm _ _).trans ?_
        have := (E.shiftGrad i y).le_opNorm (v y)
        calc ‖ζ y‖ * ‖E.shiftGrad i y (v y)‖ ≤ ‖ζ y‖ * (‖E.shiftGrad i y‖ * ‖v y‖) :=
              mul_le_mul_of_nonneg_left this (norm_nonneg _)
          _ = _ := by field_simp
    have hsg0 : 0 ≤ E.shiftGradBound i := (Real.sqrt_nonneg _).trans (hDd.shiftGrad_bound i)
    calc |(∫ y, inner ℝ (ζ y) (G y (E.shiftField i y))) + ∫ y, inner ℝ (ζ y) (E.shiftGrad i y (v y))|
        ≤ E.shiftBound i * b + E.shiftGradBound i * h := (abs_add_le _ _).trans (add_le_add hk1 hk2)
      _ ≤ E.shiftBound i * b + E.shiftGradBound i * (Hc * b) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hh hsg0)
      _ = (E.shiftBound i + Hc * E.shiftGradBound i) * b := by ring
  have hsplit : l2Pair v (E.remainderField α d j p) = (∫ y, inner ℝ (v y) (F y)) +
      ∑ i ∈ Finset.univ \ E.exactSet, p i * ∫ y, inner ℝ (v y) (convectionAdjointField (E.shiftField i) (E.shiftGrad i) ζ E.adjointGrad y) := by
    unfold l2Pair
    rw [integral_congr_ae (g := fun y => inner ℝ (v y) (F y) + ∑ i ∈ Finset.univ \ E.exactSet, p i *
      inner ℝ (v y) (convectionAdjointField (E.shiftField i) (E.shiftGrad i) ζ E.adjointGrad y)) ?_]
    · rw [integral_add h4i (integrable_finsetSum _ fun i _ => (hshift i).1.const_mul (p i)),
        integral_finsetSum _ fun i _ => (hshift i).1.const_mul (p i)]
      simp only [integral_const_mul]
    · filter_upwards [hDd.remainder_split] with y hy
      rw [hy, inner_add_right, inner_sum]
      simp only [real_inner_smul_right]
      rfl
  have h5 : |l2Pair v (E.remainderField α d j p)| ≤
      (E.inverseSquareBound + ∑ i ∈ Finset.univ \ E.exactSet, |p i| * (E.shiftBound i + Hc * E.shiftGradBound i)) * b := by
    rw [hsplit, add_mul, Finset.sum_mul]
    refine (abs_add_le _ _).trans (add_le_add h4 ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hshift i).2 (abs_nonneg _)
  have hen : a ^ 2 + d.weightMin * b ^ 2 ≤ d.energy G H := by
    unfold FracCertData.energy weightedEnergy
    rw [hadef, hbdef, Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _),
      Real.sq_sqrt (integral_nonneg fun y => entrySq_nonneg _), ← integral_const_mul]
    refine add_le_add le_rfl (integral_mono (hGi.const_mul _) ?_ fun y => ?_)
    · refine hGi.bdd_mul (c := d.weightMax) hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (hw.trans_le (hlow y))]
      exact hhigh y
    · exact mul_le_mul_of_nonneg_right (hlow y) (entrySq_nonneg _)
  set A := E.dualBound
  set B := E.potentialScale * E.potentialBound + E.fluxBound + E.inverseSquareBound +
    ∑ i ∈ Finset.univ \ E.exactSet, |p i| * (E.shiftBound i + Hc * E.shiftGradBound i) with hBdef
  have htot : |l2Pair (negSecondTrace H) E.dualField +
      E.potentialScale * (∫ y, entryInner (G y) (E.potentialGrad y)) -
      (∫ y, entryInner (G y) (E.fluxField y)) + l2Pair v (E.remainderField α d j p)| ≤ a * A + b * B := by
    have e1 := abs_add_le (l2Pair (negSecondTrace H) E.dualField +
      E.potentialScale * (∫ y, entryInner (G y) (E.potentialGrad y)) -
      (∫ y, entryInner (G y) (E.fluxField y))) (l2Pair v (E.remainderField α d j p))
    have e2 := abs_sub (l2Pair (negSecondTrace H) E.dualField +
      E.potentialScale * (∫ y, entryInner (G y) (E.potentialGrad y))) (∫ y, entryInner (G y) (E.fluxField y))
    have e3 := abs_add_le (l2Pair (negSecondTrace H) E.dualField)
      (E.potentialScale * (∫ y, entryInner (G y) (E.potentialGrad y)))
    rw [hBdef]
    nlinarith
  refine htot.trans ((mul_add_mul_le_sqrt hw).trans ?_)
  exact mul_le_mul hb (Real.sqrt_le_sqrt hen) (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans hb)

end Reduction

end CellCert

end Breakdown
