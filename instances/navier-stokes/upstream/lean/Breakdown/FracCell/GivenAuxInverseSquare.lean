import Breakdown.FracCell.GivenAuxDefs
import Breakdown.FracCell.GivenAuxAdjoint
import Breakdown.FracCell.GivenAuxPin
import Breakdown.FracCell.GivenProfileBounds
import Breakdown.FracCell.GivenProfileBoundsField
import Breakdown.FracCell.ModelField
import Breakdown.FracCell.ModelFormParts
import Breakdown.FracCert.HeldStateLimitAApply
import Breakdown.FracCert.WeakRegular
import Breakdown.FracCell.GivenAuxInverseSquareOpen

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

private theorem memLp_sq_bound {f : Space → Space} {g : Space → ℝ} (hf : AEStronglyMeasurable f volume)
    (hg : Integrable g volume) (h : ∀ᵐ y ∂volume, ‖f y‖ ^ 2 ≤ g y) : MemLp f 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm hf]
  refine hg.mono' ((hf.norm.aemeasurable.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [h] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hy

private theorem memLp_of_eq {f g : Space → Space} (hf : MemLp f 2 volume) (h : ∀ y, f y = g y) :
    MemLp g 2 volume :=
  hf.ae_eq (Filter.Eventually.of_forall h)

private theorem turn_cont : Continuous axialTurn := by
  let f : Space →ₗ[ℝ] Space :=
    { toFun := axialTurn
      map_add' := by
        intro a b
        ext i
        fin_cases i <;> simp [axialTurn] <;> ring
      map_smul' := by
        intro r a
        ext i
        fin_cases i <;> simp [axialTurn] }
  exact f.continuous_of_finiteDimensional

private theorem aesm_norm : AEStronglyMeasurable (fun y : Space => ‖y‖) volume :=
  continuous_norm.aestronglyMeasurable

private theorem aesm_apply {G : Space → (Space →L[ℝ] Space)} {v : Space → Space}
    (hG : AEStronglyMeasurable G volume) (hv : AEStronglyMeasurable v volume) :
    AEStronglyMeasurable (fun y => G y (v y)) volume :=
  Continuous.comp_aestronglyMeasurable₂ (g := fun (L : Space →L[ℝ] Space) (w : Space) => L w)
    (continuous_fst.clm_apply continuous_snd) hG hv

private theorem apply_weighted {Dζ : Space → (Space →L[ℝ] Space)} {v : Space → Space}
    (hDζ : AEStronglyMeasurable Dζ volume) (hv : AEStronglyMeasurable v volume) (hvle : ∀ y, ‖v y‖ ≤ ‖y‖)
    (h4 : Integrable (fun y => ‖y‖ ^ 4 * entrySq (Dζ y)) volume) :
    MemLp (fun y => ‖y‖ • Dζ y (v y)) 2 volume := by
  refine memLp_sq_bound (aesm_norm.smul (aesm_apply hDζ hv)) h4 (Filter.Eventually.of_forall fun y => ?_)
  have hE : 0 ≤ entrySq (Dζ y) := Finset.sum_nonneg fun i _ => sq_nonneg _
  have ha := ApplyPairingInternal.apply_norm_le (Dζ y) (v y)
  have hle : ‖‖y‖ • Dζ y (v y)‖ ≤ ‖y‖ * (Real.sqrt (entrySq (Dζ y)) * ‖y‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_norm]
    exact mul_le_mul_of_nonneg_left (ha.trans (mul_le_mul_of_nonneg_left (hvle y) (Real.sqrt_nonneg _)))
      (norm_nonneg _)
  calc ‖‖y‖ • Dζ y (v y)‖ ^ 2 ≤ (‖y‖ * (Real.sqrt (entrySq (Dζ y)) * ‖y‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = ‖y‖ ^ 4 * Real.sqrt (entrySq (Dζ y)) ^ 2 := by ring
    _ = ‖y‖ ^ 4 * entrySq (Dζ y) := by rw [Real.sq_sqrt hE]

private theorem drift_weighted (α a : ℝ) (ζ : Space → Space) (Dζ : Space → (Space →L[ℝ] Space))
    (hζ : AEStronglyMeasurable ζ volume) (hDζ : AEStronglyMeasurable Dζ volume)
    (hζw : MemLp (fun y => ‖y‖ • ζ y) 2 volume) (h4 : Integrable (fun y => ‖y‖ ^ 4 * entrySq (Dζ y)) volume) :
    MemLp (fun y => ‖y‖ • Reduction.driftAdjointField α a ζ Dζ y) 2 volume := by
  have h1 := apply_weighted hDζ aestronglyMeasurable_id (fun y => le_rfl) h4
  have h2 := apply_weighted hDζ turn_cont.aestronglyMeasurable
    (fun y => FracCert.WeakRegularInternal.norm_axialTurn_le y) h4
  have h3 : MemLp (fun y => ‖y‖ • axialTurn (ζ y)) 2 volume := by
    refine hζw.of_le (aesm_norm.smul (turn_cont.comp_aestronglyMeasurable hζ))
      (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (FracCert.WeakRegularInternal.norm_axialTurn_le _) (norm_nonneg _)
  refine memLp_of_eq (((hζw.const_smul (1 - 4 * (1 / (2 * α)))).sub (h1.const_smul (1 / (2 * α)))).sub
    ((h2.sub h3).const_smul a)) (fun y => ?_)
  simp only [Pi.sub_apply, Pi.smul_apply, Reduction.driftAdjointField, id]
  module

private theorem conv_weighted (W : Space → Space) (DW : Space → (Space →L[ℝ] Space)) (ζ : Space → Space)
    (Dζ : Space → (Space →L[ℝ] Space)) (hW : AEStronglyMeasurable W volume) (hDW : AEStronglyMeasurable DW volume)
    (hζ : AEStronglyMeasurable ζ volume) (hDζ : AEStronglyMeasurable Dζ volume) (C : ℝ)
    (hb : ∀ y, ‖y‖ * ‖W y‖ ≤ C ∧ ‖DW y‖ ≤ C)
    (hζw : MemLp (fun y => ‖y‖ • ζ y) 2 volume) (hE : Integrable (fun y => entrySq (Dζ y)) volume) :
    MemLp (fun y => ‖y‖ • Reduction.convectionAdjointField W DW ζ Dζ y) 2 volume := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hb 0).2
  have hcurl := ModelFieldInternal.aesm_curl hDζ
  have h1 : MemLp (fun y => ‖y‖ • crossVec (curlOf (Dζ y)) (W y)) 2 volume := by
    refine memLp_sq_bound (g := fun y => C ^ 2 * (2 * entrySq (Dζ y)))
      (aesm_norm.smul (ModelFieldInternal.aesm_cross hcurl hW))
      ((hE.const_mul 2).const_mul _) (Filter.Eventually.of_forall fun y => ?_)
    have hc := ModelFieldInternal.cross_le (curlOf (Dζ y)) (W y)
    have hs := ModelFormInternal.curl_sq_le (Dζ y)
    have hle : ‖‖y‖ • crossVec (curlOf (Dζ y)) (W y)‖ ≤ C * ‖curlOf (Dζ y)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_norm]
      calc ‖y‖ * ‖crossVec (curlOf (Dζ y)) (W y)‖ ≤ ‖y‖ * (‖curlOf (Dζ y)‖ * ‖W y‖) :=
            mul_le_mul_of_nonneg_left hc (norm_nonneg _)
        _ = ‖curlOf (Dζ y)‖ * (‖y‖ * ‖W y‖) := by ring
        _ ≤ ‖curlOf (Dζ y)‖ * C := mul_le_mul_of_nonneg_left (hb y).1 (norm_nonneg _)
        _ = C * ‖curlOf (Dζ y)‖ := by ring
    calc ‖‖y‖ • crossVec (curlOf (Dζ y)) (W y)‖ ^ 2 ≤ (C * ‖curlOf (Dζ y)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = C ^ 2 * ‖curlOf (Dζ y)‖ ^ 2 := by ring
      _ ≤ C ^ 2 * (2 * entrySq (Dζ y)) := mul_le_mul_of_nonneg_left hs (sq_nonneg C)
  have hadjm : AEStronglyMeasurable (fun y => ContinuousLinearMap.adjoint (DW y)) volume :=
    (ContinuousLinearMap.adjoint : (Space →L[ℝ] Space) ≃ₗᵢ⋆[ℝ] (Space →L[ℝ] Space)).continuous.comp_aestronglyMeasurable hDW
  have h2 : MemLp (fun y => ‖y‖ • ContinuousLinearMap.adjoint (DW y) (ζ y)) 2 volume := by
    have hz : MemLp (fun y => C • (‖y‖ • ζ y)) 2 volume := memLp_of_eq (hζw.const_smul C) (fun y => rfl)
    refine hz.of_le (aesm_norm.smul (aesm_apply hadjm hζ))
      (Filter.Eventually.of_forall fun y => ?_)
    have hn : ‖ContinuousLinearMap.adjoint (DW y) (ζ y)‖ ≤ C * ‖ζ y‖ := by
      refine ((ContinuousLinearMap.adjoint (DW y)).le_opNorm (ζ y)).trans ?_
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (hb y).2 (norm_nonneg _)
    rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, abs_norm, Real.norm_eq_abs, abs_of_nonneg hC]
    calc ‖y‖ * ‖ContinuousLinearMap.adjoint (DW y) (ζ y)‖ ≤ ‖y‖ * (C * ‖ζ y‖) :=
          mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ = C * (‖y‖ * ‖ζ y‖) := by ring
  refine memLp_of_eq (h1.neg.add (h2.const_smul (2 : ℝ))) (fun y => ?_)
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, Reduction.convectionAdjointField]
  module

private theorem decay_bound {C w a e : ℝ} (hw : 0 ≤ w) (ha : a ≤ C * (1 + w) ^ (-(1 : ℝ)))
    (he : e ≤ C * (1 + w) ^ (-(2 : ℝ))) (ha0 : 0 ≤ a) : w * a ≤ C ∧ e ≤ C := by
  have h1 : (1 + w) ^ (-(1 : ℝ)) = (1 + w)⁻¹ := Real.rpow_neg_one _
  have hpos : 0 < 1 + w := by linarith
  have hC : 0 ≤ C := by
    by_contra hneg
    push Not at hneg
    have : C * (1 + w) ^ (-(1 : ℝ)) < 0 := mul_neg_of_neg_of_pos hneg (Real.rpow_pos_of_pos hpos _)
    linarith
  have h2 : (1 + w) ^ (-(2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  refine ⟨?_, he.trans (by nlinarith)⟩
  rw [h1] at ha
  have hw1 : w * (1 + w)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hpos]; linarith
  calc w * a ≤ w * (C * (1 + w)⁻¹) := mul_le_mul_of_nonneg_left ha hw
    _ = C * (w * (1 + w)⁻¹) := by ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hw1 hC
    _ = C := mul_one C

private theorem w_add {f g : Space → Space} (hf : MemLp (fun y => ‖y‖ • f y) 2 volume)
    (hg : MemLp (fun y => ‖y‖ • g y) 2 volume) : MemLp (fun y => ‖y‖ • (f y + g y)) 2 volume := by
  exact memLp_of_eq (hf.add hg) (fun y => by simp only [Pi.add_apply, smul_add])

private theorem w_sub {f g : Space → Space} (hf : MemLp (fun y => ‖y‖ • f y) 2 volume)
    (hg : MemLp (fun y => ‖y‖ • g y) 2 volume) : MemLp (fun y => ‖y‖ • (f y - g y)) 2 volume := by
  exact memLp_of_eq (hf.sub hg) (fun y => by simp only [Pi.sub_apply, smul_sub])

private theorem w_smul (c : ℝ) {f : Space → Space} (hf : MemLp (fun y => ‖y‖ • f y) 2 volume) :
    MemLp (fun y => ‖y‖ • (c • f y)) 2 volume := by
  exact memLp_of_eq (hf.const_smul c) (fun y => by simp only [Pi.smul_apply]; rw [smul_comm])

private theorem w_sum {ι : Type*} (s : Finset ι) (f : ι → Space → Space)
    (hf : ∀ i ∈ s, MemLp (fun y => ‖y‖ • f i y) 2 volume) :
    MemLp (fun y => ‖y‖ • ∑ i ∈ s, f i y) 2 volume := by
  exact memLp_of_eq (memLp_finsetSum' s hf) (fun y => by rw [Finset.sum_apply, Finset.smul_sum])

private theorem aesm_of_weighted {F : Space → Space} (h : AEStronglyMeasurable (fun y => ‖y‖ • F y) volume) :
    AEStronglyMeasurable F volume := by
  have hne : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
    exact measure_singleton 0
  have hinv : AEStronglyMeasurable (fun y : Space => ‖y‖⁻¹) volume := (measurable_norm.inv).aestronglyMeasurable
  refine (hinv.smul h).congr ?_
  filter_upwards [hne] with y hy
  show ‖y‖⁻¹ • (‖y‖ • F y) = F y
  rw [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy), one_smul]

private theorem profile_cont {k : ℕ} (D : ProfileData k) (hD : IsProfileData D) (p : Fin k → ℝ) :
    Continuous (D.profile p) := by
  have : D.profile p = fun y => ∑ μ ∈ D.index, ProfileData.monomialOf p μ •
      fieldOf D.chart (D.part μ) (D.phase p) y := rfl
  rw [this]
  refine continuous_finsetSum _ fun μ hμ => ?_
  obtain ⟨C, hC⟩ := FracCellInternal.fieldOf_decay D.chart hD.chart (D.part μ) (hD.parts μ hμ) |D.phase p|
  exact ((hC (D.phase p) le_rfl).1.continuous).const_smul (ProfileData.monomialOf p μ)

theorem pinTrace_weighted_of_support (X L : Space → Space) (hXc : HasCompactSupport X)
    (hL : Reduction.IsWeakNegTraceOf X L) (hLm : AEStronglyMeasurable L volume)
    (hLb : ∃ C : ℝ, ∀ᵐ y ∂volume, ‖L y‖ ≤ C) :
    MemLp (fun y => ‖y‖ • L y) 2 volume := by
  obtain ⟨C, hC⟩ := hLb
  have htop : MemLp L ⊤ volume := memLp_top_of_bound hLm C hC
  have hU : IsOpen (tsupport X)ᶜ := (isClosed_tsupport X).isOpen_compl
  have hzero : ∀ᵐ y ∂volume, y ∈ (tsupport X)ᶜ → L y = 0 := by
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((htop.locallyIntegrable le_top).locallyIntegrableOn _) ?_
    intro g hg hgs hgU
    have hint : Integrable (fun y => g y • L y) volume :=
      (hg.continuous.integrable_of_hasCompactSupport hgs).smul_of_top_left htop
    refine integral_eq_zero_of_forall_integral_inner_eq_zero ℝ _ hint (fun w => ?_)
    have htest : IsTestVectorField (fun y => g y • w) :=
      ⟨hg.smul contDiff_const, by exact hgs.smul_right (f' := fun _ : Space => w)⟩
    have hid := hL _ htest
    have hlhs : ∫ y, inner ℝ (X y) (-sumSecondPartialsAt (fun y => g y • w) y) = 0 := by
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
      by_cases hy : y ∈ tsupport g
      · have hX0 : X y = 0 := image_eq_zero_of_notMem_tsupport (hgU hy)
        simp [hX0]
      · have h2 : iteratedFDeriv ℝ 2 (fun y => g y • w) y = 0 := by
          by_contra hne
          exact hy (tsupport_smul_subset_left g (fun _ => w)
            (support_iteratedFDeriv_subset 2 (Function.mem_support.mpr hne)))
        simp [sumSecondPartialsAt, h2]
    rw [hlhs] at hid
    have heq : (fun y => inner ℝ w (g y • L y)) = fun y => inner ℝ (L y) (g y • w) := by
      funext y
      rw [inner_smul_right, inner_smul_right, real_inner_comm]
    show ∫ y, inner ℝ w (g y • L y) = 0
    rw [heq, ← hid]
  have hK : IsCompact (tsupport X) := hXc
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  have hg : MemLp ((tsupport X).indicator (fun _ => R * C)) 2 volume :=
    memLp_indicator_const 2 hK.isClosed.measurableSet (R * C) (Or.inr hK.measure_lt_top.ne)
  refine hg.of_le ((continuous_norm.aestronglyMeasurable).smul hLm) ?_
  filter_upwards [hC, hzero] with y hy hy0
  by_cases hyK : y ∈ tsupport X
  · rw [Set.indicator_of_mem hyK, norm_smul, Real.norm_eq_abs, abs_norm]
    have hR0 : 0 ≤ R := (norm_nonneg y).trans (hR y hyK)
    exact (mul_le_mul (hR y hyK) hy (norm_nonneg _) hR0).trans ((le_abs_self _).trans (Real.norm_eq_abs _).symm.le)
  · rw [hy0 hyK, smul_zero, norm_zero]
    exact norm_nonneg _


theorem amplitude_regular_of {k : ℕ} (D : ProfileData k) (hD : IsProfileData D) (i : Fin k) (p : Fin k → ℝ)
    (hi : Pi.single i 1 ∈ D.index) :
    ContDiff ℝ 1 (amplitudeFieldAt D i p) ∧ (∀ y, divergenceAt (amplitudeFieldAt D i p) y = 0) ∧
      ∃ C : ℝ, ∀ y, ‖amplitudeFieldAt D i p y‖ ≤ C * (1 + ‖y‖)⁻¹ ∧
        ‖fderiv ℝ (amplitudeFieldAt D i p) y‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ) := by
  have hF := hD.parts _ hi
  obtain ⟨C, hC⟩ := FracCellInternal.fieldOf_decay D.chart hD.chart (D.part (Pi.single i 1)) hF |D.phase p|
  obtain ⟨hc, hb⟩ := hC (D.phase p) le_rfl
  have e : amplitudeFieldAt D i p = fieldOf D.chart (D.part (Pi.single i 1)) (D.phase p) := rfl
  rw [e]
  refine ⟨hc, fun y => FracCellInternal.fieldOf_divergence D.chart hD.chart _ hF _ y, C, fun y => ⟨?_, (hb y).2.1⟩⟩
  rw [← Real.rpow_neg_one]
  exact (hb y).1

private theorem ringRep_convAmp {k : ℕ} (D : ProfileData k) (hD : IsProfileData D) (A : AuxData k)
    (hA : IsAuxData D.chart A) (j : Fin k) (p : Fin k → ℝ) (i : Fin k) (hi : Pi.single i 1 ∈ D.index) :
    HasRingRep (fun y => Reduction.convectionAdjointField (amplitudeFieldAt D i p)
      (fun z => fderiv ℝ (amplitudeFieldAt D i p) z) (A.adjointField D.chart j p)
      (fun z => fderiv ℝ (A.adjointField D.chart j p) z) y) := by
  have hW : ∃ S, IsRingTrigSum S (amplitudeFieldAt D i p) :=
    ringTrig_fieldOf D.chart (D.part (Pi.single i 1)) (D.phase p)
  obtain ⟨S, hS⟩ := RingModesInternal.trig_convection hW ((amplitude_regular_of D hD i p hi).1.differentiable one_ne_zero)
    (ringTrig_adjointField D.chart A j p) (differentiable_adjointField D.chart hD.chart A hA j p)
  exact ⟨S, _, Filter.Eventually.of_forall (fun _ => rfl), hS⟩

private theorem inverseSquare_ring (α : ℝ) {k N : ℕ} (D : ProfileData k) (hD : IsProfileData D)
    (hamp : ∀ i, Pi.single i 1 ∈ D.index)
    (A : AuxData k) (hA : IsAuxData D.chart A) (c : FracCellData k N) (hd : IsProfileInstance D c.toFracCertData)
    (hI : IsAuxInstance D A c) (j : Fin k) (p : Fin k → ℝ) (Dd : Reduction.AdjointDual k)
    (hgrad : Dd.adjointGrad = fun y => fderiv ℝ (A.adjointField D.chart j p) y)
    (hpin : ∀ l, Dd.pinPotential l = A.pinPotentialField D.chart l ∧ Dd.pinScale l = A.pinScale l)
    (hdual : Dd.dualField = A.dualFieldOf D.chart j p) (hpot : Dd.potentialField = A.potentialFieldOf D.chart j p)
    (hflux : Dd.fluxField = A.fluxFieldOf D.chart j p) (hpress : Dd.pressure = A.adjointPressureField D.chart j p)
    (hsharp : Reduction.IsWeakNegTraceOf (fun y => c.splitVisc • c.adjoint j p y + c.adjointSharp j p y) Dd.sharpTrace)
    (hpinT : ∀ l, Reduction.IsWeakNegTraceOf (Dd.pinPotential l) (Dd.pinTrace l))
    (hpressG : Reduction.IsWeakScalarGradientOf Dd.pressure Dd.pressureGrad)
    (hdualT : Reduction.IsWeakNegTraceOf Dd.dualField Dd.dualTrace)
    (hpotT : Reduction.IsWeakNegTraceOf Dd.potentialField Dd.potentialTrace)
    (hfluxD : Reduction.IsWeakMatrixDivergenceOf Dd.fluxField Dd.fluxDiv)
    (hsharpW : MemLp (fun y => ‖y‖ • Dd.sharpTrace y) 2 volume)
    (hpinTB : ∀ l, AEStronglyMeasurable (Dd.pinTrace l) volume ∧ ∃ C : ℝ, ∀ᵐ y ∂volume, ‖Dd.pinTrace l y‖ ≤ C)
    (hpressW : MemLp Dd.pressure 2 volume ∧ MemLp (fun y => ‖y‖ • Dd.pressureGrad y) 2 volume)
    (hdualW : MemLp (fun y => ‖y‖ • Dd.dualTrace y) 2 volume)
    (hpotW : MemLp (fun y => ‖y‖ • Dd.potentialTrace y) 2 volume)
    (hfluxW : AEStronglyMeasurable Dd.fluxField volume ∧ Integrable (fun y => entrySq (Dd.fluxField y)) ∧
      MemLp (fun y => ‖y‖ • Dd.fluxDiv y) 2 volume) :
    HasRingRep (fun y => inverseSquarePartOf α D c.toFracCertData j p Dd y) := by
  have hadj : c.toFracCertData.adjoint j p = A.adjointField D.chart j p := hI.adjoint_eq j p
  have hdrift : HasRingRep (fun y => Reduction.driftAdjointField α (c.toFracCertData.rotationRate p)
      (c.toFracCertData.adjoint j p) Dd.adjointGrad y) := by
    rw [hadj, hgrad]
    exact ringRep_drift D.chart hD.chart A hA j p α _
  have hsh : HasRingRep (fun y => Dd.sharpTrace y) := by
    refine ringRep_sharpTrace D.chart hD.chart A hA j p c.splitVisc Dd.sharpTrace ?_ hsharpW
    have e1 : c.adjoint j p = A.adjointField D.chart j p := hI.adjoint_eq j p
    have e2 : c.adjointSharp j p = A.sharpField D.chart c.splitVisc j p := hI.adjointSharp_eq j p
    rw [e1, e2] at hsharp
    exact hsharp
  have hconvP : HasRingRep (fun y => Reduction.convectionAdjointField (c.toFracCertData.profile p)
      (c.toFracCertData.gradProfile p) (c.toFracCertData.adjoint j p) Dd.adjointGrad y) := by
    unfold FracCertData.gradProfile
    rw [hadj, hgrad, hd.profile_eq]
    exact ringRep_convection D hD A hA j p _ (Or.inl rfl)
  have hconvT : ∀ i ∈ Finset.univ \ Dd.exactSet, HasRingRep (fun y => p i •
      Reduction.convectionAdjointField (amplitudeFieldAt D i p) (fun z => fderiv ℝ (amplitudeFieldAt D i p) z)
        (c.toFracCertData.adjoint j p) Dd.adjointGrad y) := by
    intro i _
    refine HasRingRep.smul (p i) ?_
    rw [hadj, hgrad]
    exact ringRep_convAmp D hD A hA j p i (hamp i)
  have hpinR : ∀ l ∈ (Finset.univ : Finset (Fin k)), HasRingRep (fun y =>
      c.toFracCertData.adjointPin j p l • Dd.pinDual l y) := by
    intro l _
    refine HasRingRep.smul _ ?_
    show HasRingRep (fun y => (1 / Dd.pinScale l) • Dd.pinTrace l y)
    refine HasRingRep.smul _ ?_
    have hT := hpinT l
    rw [(hpin l).1] at hT
    exact ringRep_pinTrace D.chart hD.chart A hA l _ hT (hpinTB l).1 (hpinTB l).2
  have hpr : HasRingRep (fun y => Dd.pressureGrad y) := by
    rw [hpress] at hpressG
    exact ringRep_pressureGrad D.chart hD.chart A hA j p _ hpressG hpressW.2
  have hdu : HasRingRep (fun y => Dd.dualTrace y) := by
    rw [hdual] at hdualT
    exact ringRep_dualTrace D.chart hD.chart A hA j p _ hdualT hdualW
  have hpo : HasRingRep (fun y => Dd.potentialTrace y) := by
    rw [hpot] at hpotT
    exact ringRep_potentialTrace D.chart hD.chart A hA j p _ hpotT hpotW
  have hfl : HasRingRep (fun y => Dd.fluxDiv y) := by
    rw [hflux] at hfluxD
    exact ringRep_fluxDiv D.chart hD.chart A hA j p _ hfluxD hfluxW.2.2
  unfold inverseSquarePartOf Reduction.AdjointDual.remainderField Reduction.AdjointDual.residualField
  exact (((((((hdrift.add hsh).add hconvP).sub (HasRingRep.sum _ _ hpinR)).add hpr).sub hdu).sub
    (hpo.smul _)).sub hfl).sub (HasRingRep.sum _ _ hconvT)

private theorem inverseSquare_weighted (α : ℝ) {k N : ℕ} (D : ProfileData k) (hD : IsProfileData D)
    (hamp : ∀ i, Pi.single i 1 ∈ D.index)
    (A : AuxData k) (hA : IsAuxData D.chart A) (c : FracCellData k N) (hd : IsProfileInstance D c.toFracCertData)
    (hI : IsAuxInstance D A c) (j : Fin k) (p : Fin k → ℝ) (Dd : Reduction.AdjointDual k)
    (hgrad : Dd.adjointGrad = fun y => fderiv ℝ (A.adjointField D.chart j p) y)
    (hpin : ∀ l, Dd.pinPotential l = A.pinPotentialField D.chart l ∧ Dd.pinScale l = A.pinScale l)
    (hpinT : ∀ l, Reduction.IsWeakNegTraceOf (Dd.pinPotential l) (Dd.pinTrace l))
    (hsharpW : MemLp (fun y => ‖y‖ • Dd.sharpTrace y) 2 volume)
    (hpinTB : ∀ l, AEStronglyMeasurable (Dd.pinTrace l) volume ∧ ∃ C : ℝ, ∀ᵐ y ∂volume, ‖Dd.pinTrace l y‖ ≤ C)
    (hpressW : MemLp Dd.pressure 2 volume ∧ MemLp (fun y => ‖y‖ • Dd.pressureGrad y) 2 volume)
    (hdualW : MemLp (fun y => ‖y‖ • Dd.dualTrace y) 2 volume)
    (hpotW : MemLp (fun y => ‖y‖ • Dd.potentialTrace y) 2 volume)
    (hfluxW : AEStronglyMeasurable Dd.fluxField volume ∧ Integrable (fun y => entrySq (Dd.fluxField y)) ∧
      MemLp (fun y => ‖y‖ • Dd.fluxDiv y) 2 volume) :
    MemLp (fun y => ‖y‖ • inverseSquarePartOf α D c.toFracCertData j p Dd y) 2 volume := by
  obtain ⟨hζ2, -, hζw, hDm, -, hE, h4, -⟩ := adjointRegular_of_given D.chart hD.chart A hA j p
  have hζm := hζ2.aestronglyMeasurable
  have hadj : c.toFracCertData.adjoint j p = A.adjointField D.chart j p := hI.adjoint_eq j p
  have hdrift : MemLp (fun y => ‖y‖ • Reduction.driftAdjointField α (c.toFracCertData.rotationRate p)
      (c.toFracCertData.adjoint j p) Dd.adjointGrad y) 2 volume := by
    rw [hadj, hgrad]
    exact drift_weighted _ _ _ _ hζm hDm hζw h4
  have hconvP : MemLp (fun y => ‖y‖ • Reduction.convectionAdjointField (c.toFracCertData.profile p)
      (c.toFracCertData.gradProfile p) (c.toFracCertData.adjoint j p) Dd.adjointGrad y) 2 volume := by
    obtain ⟨C, hC⟩ := FracCellInternal.profile_bounds_everywhere D hD (fun i => |p i|)
    have hp : p ∈ box (fun i => |p i|) := by
      intro i
      exact le_rfl
    unfold FracCertData.gradProfile
    rw [hadj, hgrad, hd.profile_eq]
    refine conv_weighted _ _ _ _ (profile_cont D hD p).aestronglyMeasurable
      (measurable_fderiv ℝ _).aestronglyMeasurable hζm hDm C (fun y => ?_) hζw hE
    obtain ⟨h1, h2, -⟩ := hC p hp y
    exact decay_bound (norm_nonneg y) h1 h2 (norm_nonneg _)
  have hconvT : ∀ i ∈ Finset.univ \ Dd.exactSet, MemLp (fun y => ‖y‖ • (p i •
      Reduction.convectionAdjointField (amplitudeFieldAt D i p) (fun z => fderiv ℝ (amplitudeFieldAt D i p) z)
        (c.toFracCertData.adjoint j p) Dd.adjointGrad y)) 2 volume := by
    intro i _
    refine w_smul (p i) ?_
    obtain ⟨hU, -, C, hb⟩ := amplitude_regular_of D hD i p (hamp i)
    rw [hadj, hgrad]
    refine conv_weighted _ _ _ _ hU.continuous.aestronglyMeasurable
      (measurable_fderiv ℝ _).aestronglyMeasurable hζm hDm C (fun y => ?_) hζw hE
    refine decay_bound (norm_nonneg y) ?_ (hb y).2 (norm_nonneg _)
    rw [Real.rpow_neg_one]
    exact (hb y).1
  have hpinW : ∀ l ∈ (Finset.univ : Finset (Fin k)), MemLp (fun y => ‖y‖ •
      (c.toFracCertData.adjointPin j p l • Dd.pinDual l y)) 2 volume := by
    intro l _
    refine w_smul _ ?_
    show MemLp (fun y => ‖y‖ • ((1 / Dd.pinScale l) • Dd.pinTrace l y)) 2 volume
    refine w_smul _ ?_
    have hsupp : HasCompactSupport (Dd.pinPotential l) := by
      rw [(hpin l).1]
      exact (pinRegular_of_given D.chart hD.chart A hA l).2.1
    exact pinTrace_weighted_of_support _ _ hsupp (hpinT l) (hpinTB l).1 (hpinTB l).2
  unfold inverseSquarePartOf Reduction.AdjointDual.remainderField Reduction.AdjointDual.residualField
  exact w_sub (w_sub (w_sub (w_sub (w_add (w_sub (w_add (w_add hdrift hsharpW) hconvP)
    (w_sum _ _ hpinW)) hpressW.2) hdualW) (w_smul _ hpotW)) hfluxW.2.2) (w_sum _ _ hconvT)

theorem inverseSquare_of_given (α : ℝ) {k N : ℕ} (D : ProfileData k) (hD : IsProfileData D)
    (A : AuxData k) (hA : IsAuxData D.chart A) (c : FracCellData k N) (hd : IsProfileInstance D c.toFracCertData)
    (hI : IsAuxInstance D A c) (hα : α = D.power)
    (hamp : ∀ i, Pi.single i 1 ∈ D.index) (j : Fin k) (p : Fin k → ℝ) (Dd : Reduction.AdjointDual k)
    (hgrad : Dd.adjointGrad = fun y => fderiv ℝ (A.adjointField D.chart j p) y)
    (hpin : ∀ l, Dd.pinPotential l = A.pinPotentialField D.chart l ∧ Dd.pinScale l = A.pinScale l)
    (hdual : Dd.dualField = A.dualFieldOf D.chart j p) (hpot : Dd.potentialField = A.potentialFieldOf D.chart j p)
    (hflux : Dd.fluxField = A.fluxFieldOf D.chart j p) (hpress : Dd.pressure = A.adjointPressureField D.chart j p)
    (hsharp : Reduction.IsWeakNegTraceOf (fun y => c.splitVisc • c.adjoint j p y + c.adjointSharp j p y) Dd.sharpTrace)
    (hpinT : ∀ l, Reduction.IsWeakNegTraceOf (Dd.pinPotential l) (Dd.pinTrace l))
    (hpressG : Reduction.IsWeakScalarGradientOf Dd.pressure Dd.pressureGrad)
    (hdualT : Reduction.IsWeakNegTraceOf Dd.dualField Dd.dualTrace)
    (hpotT : Reduction.IsWeakNegTraceOf Dd.potentialField Dd.potentialTrace)
    (hfluxD : Reduction.IsWeakMatrixDivergenceOf Dd.fluxField Dd.fluxDiv)
    (hsharpW : MemLp (fun y => ‖y‖ • Dd.sharpTrace y) 2 volume)
    (hpinTB : ∀ l, AEStronglyMeasurable (Dd.pinTrace l) volume ∧ ∃ C : ℝ, ∀ᵐ y ∂volume, ‖Dd.pinTrace l y‖ ≤ C)
    (hpressW : MemLp Dd.pressure 2 volume ∧ MemLp (fun y => ‖y‖ • Dd.pressureGrad y) 2 volume)
    (hdualW : MemLp (fun y => ‖y‖ • Dd.dualTrace y) 2 volume)
    (hpotW : MemLp (fun y => ‖y‖ • Dd.potentialTrace y) 2 volume)
    (hfluxW : AEStronglyMeasurable Dd.fluxField volume ∧ Integrable (fun y => entrySq (Dd.fluxField y)) ∧
      MemLp (fun y => ‖y‖ • Dd.fluxDiv y) 2 volume) :
    ∃ part : Space → Space, (∀ᵐ y ∂volume, part y = inverseSquarePartOf α D c.toFracCertData j p Dd y) ∧
      AEStronglyMeasurable part volume ∧ MemLp (fun y => ‖y‖ • part y) 2 volume ∧
      ∃ S : Finset ℤ, ∀ n ∉ S, ∀ ρ z : ℝ,
        Reduction.angularMode (Reduction.horizontalPart part) n ρ z = 0 ∧
          Reduction.angularMode (Reduction.verticalPart part) n ρ z = 0 := by
  obtain ⟨part, hae, S, hS⟩ := (inverseSquare_ring α D hD hamp A hA c hd hI j p Dd hgrad hpin hdual hpot
    hflux hpress hsharp hpinT hpressG hdualT hpotT hfluxD hsharpW hpinTB hpressW hdualW hpotW hfluxW).modes
  have hW := inverseSquare_weighted α D hD hamp A hA c hd hI j p Dd hgrad hpin hpinT hsharpW hpinTB hpressW hdualW
    hpotW hfluxW
  have hWp : MemLp (fun y => ‖y‖ • part y) 2 volume :=
    hW.ae_eq (hae.mono fun y hy => by simp only [hy])
  exact ⟨part, hae, aesm_of_weighted hWp.aestronglyMeasurable, hWp, S, hS⟩

end GivenFields

end CellCert

end Breakdown
