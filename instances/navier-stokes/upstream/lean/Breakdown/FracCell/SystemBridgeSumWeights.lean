import Breakdown.FracCell.CellSystemDefs
import Breakdown.FracCell.GivenAuxAdjointCore
import Breakdown.FracCell.GivenProfileSmoothField
import Breakdown.FracCell.GivenProfileBoundsField
import Breakdown.FracCell.SystemBridgeSumWeightsOpen
import Breakdown.FracCell.GivenModelModel
import Breakdown.FracCell.GivenModelRegion
import Breakdown.FracCell.GivenProfileCentre
import Breakdown.FracCell.GivenToolkit
import Breakdown.FracCell.DensitySlice

open scoped ContDiff ENNReal
open MeasureTheory Matrix Polynomial

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellSystem

open SteadyCert Assembly Reduction GivenFields GivenModel Exterior Spectral CellAnalysis CellCoordinates CellFormula
open _root_.Breakdown.CellCert.Finite

namespace SumWeightsInternal

def turnIso (m : ℕ) : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv ⟨FracInternal.givenTurnLinear m, FracInternal.givenNorm_turn m⟩ rfl

theorem turnIso_apply (m : ℕ) (y : Space) : turnIso m y = turnStep m y := rfl

def mirrorIso : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv ⟨FracInternal.givenMirrorLinear, FracInternal.givenNorm_mirror⟩ rfl

theorem mirrorIso_apply (y : Space) : mirrorIso y = mirror y := rfl

theorem turnBy_eq (m : ℕ) (y : Space) : turnBy (2 * Real.pi / m) y = turnStep m y := rfl

theorem norm_fderiv_equiv (L : Space ≃ₗᵢ[ℝ] Space) {f : Space → Space}
    (h : ∀ y, f (L y) = L (f y)) (y : Space) : ‖fderiv ℝ f (L y)‖ = ‖fderiv ℝ f y‖ := by
  have e : f ∘ L = L ∘ f := funext h
  have h1 : fderiv ℝ (f ∘ L) y = (fderiv ℝ f (L y)).comp (L.toContinuousLinearEquiv : Space →L[ℝ] Space) :=
    L.toContinuousLinearEquiv.comp_right_fderiv
  have h2 : fderiv ℝ (L ∘ f) y = (L.toContinuousLinearEquiv : Space →L[ℝ] Space).comp (fderiv ℝ f y) :=
    L.toContinuousLinearEquiv.comp_fderiv
  rw [e, h2] at h1
  have n1 : ‖(fderiv ℝ f (L y)).comp (L.toContinuousLinearEquiv : Space →L[ℝ] Space)‖ = ‖fderiv ℝ f (L y)‖ :=
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ L
  have n2 : ‖(L.toContinuousLinearEquiv : Space →L[ℝ] Space).comp (fderiv ℝ f y)‖ = ‖fderiv ℝ f y‖ :=
    ContinuousLinearMap.opNorm_linearIsometryEquiv_comp L _
  rw [← n1, ← h1, n2]

theorem everywhere_of_ae (L : Space ≃ₗᵢ[ℝ] Space) {f : Space → Space} (hf : Continuous f)
    (h : ∀ᵐ y ∂volume, f (L y) = L (f y)) : ∀ y, f (L y) = L (f y) := by
  have := (Continuous.ae_eq_iff_eq volume (hf.comp L.continuous) (L.continuous.comp hf)).1 h
  exact fun y => congrFun this y

theorem deriv_equiv (L : Space ≃ₗᵢ[ℝ] Space) {g h : ℝ → Space} (e : ∀ b, g b = L (h b)) (β : ℝ) :
    deriv g β = L (deriv h β) := by
  have : g = L ∘ h := funext e
  rw [this]
  show fderiv ℝ (⇑L ∘ h) β 1 = L (fderiv ℝ h β 1)
  rw [L.comp_fderiv]
  rfl

theorem weight_sq (y : Space) (a : ℝ) :
    ((1 + ‖y‖) ^ (-a)) ^ 2 = (1 + ‖y‖) ^ (-(2 * a)) := by
  have h1 : 0 ≤ 1 + ‖y‖ := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul h1]
  congr 1
  push_cast
  ring

theorem finrank_lt (r : ℝ) (hr : 3 < r) : (Module.finrank ℝ Space : ℝ) < r := by
  rw [finrank_euclideanSpace_fin]
  exact_mod_cast hr

structure GradClass (m : ℕ) (f : Space → Space) : Prop where
  cd : ContDiff ℝ 1 f
  turn : ∀ y, f (turnStep m y) = turnStep m (f y)
  mir : ∀ y, f (mirror y) = mirror (f y)
  bound : ∃ C : ℝ, ∀ y, ‖fderiv ℝ f y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ))

theorem sumWeight_gradSq {m : ℕ} {f : Space → Space} (hf : GradClass m f) : IsSumWeight m (gradSq f) := by
  obtain ⟨C, hC⟩ := hf.bound
  have hcont : Continuous (gradSq f) := by
    unfold gradSq
    exact ((hf.cd.continuous_fderiv one_ne_zero).norm).pow 2
  refine ⟨hcont.measurable, fun y => by unfold gradSq; positivity, fun y => ?_, fun y => ?_, ?_⟩
  · unfold gradSq
    rw [turnBy_eq]
    exact congrArg (· ^ 2) (norm_fderiv_equiv (turnIso m) hf.turn y)
  · unfold gradSq
    exact congrArg (· ^ 2) (norm_fderiv_equiv mirrorIso hf.mir y)
  · have hI : Integrable (fun y : Space => C ^ 2 * (1 + ‖y‖) ^ (-(2 * 2 : ℝ))) :=
      (integrable_one_add_norm (finrank_lt _ (by norm_num))).const_mul _
    refine hI.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    have h0 : 0 ≤ ‖fderiv ℝ f y‖ := norm_nonneg _
    have h1 := hC y
    unfold gradSq
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← weight_sq, ← mul_pow]
    exact pow_le_pow_left₀ h0 h1 2

theorem gradClass_add_smul {m : ℕ} {g h : Space → Space} (hg : GradClass m g) (hh : GradClass m h) (c : ℝ) :
    GradClass m (fun y => g y + c • h y) := by
  obtain ⟨Cg, hCg⟩ := hg.bound
  obtain ⟨Ch, hCh⟩ := hh.bound
  have dg : Differentiable ℝ g := hg.cd.differentiable one_ne_zero
  have dh : Differentiable ℝ h := hh.cd.differentiable one_ne_zero
  refine ⟨hg.cd.add (hh.cd.const_smul c), fun y => ?_, fun y => ?_, ⟨Cg + |c| * Ch, fun y => ?_⟩⟩
  · rw [hg.turn, hh.turn, FracInternal.givenTurn_add, FracInternal.givenTurn_smul]
  · rw [hg.mir, hh.mir, FracInternal.givenMirror_add, FracInternal.givenMirror_smul]
  · have e : fderiv ℝ (fun y => g y + c • h y) y = fderiv ℝ g y + c • fderiv ℝ h y := by
      have dch : DifferentiableAt ℝ (fun z => c • h z) y := (dh y).const_smul c
      rw [fderiv_fun_add (dg y) dch, fderiv_fun_const_smul (dh y)]
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_left (hCh y) (abs_nonneg c)
    nlinarith [hCg y]

theorem fieldOf_turn_all (P : ChartParams) (hm : 0 < P.m) (F : FieldData) (b : ℝ) (y : Space) :
    fieldOf P F b (turnStep P.m y) = turnStep P.m (fieldOf P F b y) :=
  AdjointCoreInternal.field_turn P hm F b y

theorem fieldOf_mirror_all (P : ChartParams) (hP : IsChartParams P) (F : FieldData) (hF : IsFieldData P 1 F)
    (b : ℝ) (y : Space) : fieldOf P F b (mirror y) = mirror (fieldOf P F b y) :=
  everywhere_of_ae mirrorIso (FracInternal.fieldOf_contDiff hP hF b).continuous
    (FracInternal.fieldOf_mirror hP hF b) y

theorem gradClass_fieldOf (P : ChartParams) (hP : IsChartParams P) (F : FieldData) (hF : IsFieldData P 1 F)
    (β : ℝ) : GradClass P.m (fieldOf P F β) := by
  obtain ⟨C, hC⟩ := FracCellInternal.fieldOf_decay P hP F hF |β|
  obtain ⟨hcd, hb⟩ := hC β le_rfl
  exact ⟨hcd, fieldOf_turn_all P hP.m_pos F β, fieldOf_mirror_all P hP F hF β, ⟨C, fun y => (hb y).2.1⟩⟩

theorem phaseDeriv_turn (P : ChartParams) (hm : 0 < P.m) (F : FieldData) (β : ℝ) (y : Space) :
    phaseDerivField P F β (turnStep P.m y) = turnStep P.m (phaseDerivField P F β y) :=
  deriv_equiv (turnIso P.m) (fun b => fieldOf_turn_all P hm F b y) β

theorem phaseDeriv_mirror (P : ChartParams) (hP : IsChartParams P) (F : FieldData) (hF : IsFieldData P 1 F)
    (β : ℝ) (y : Space) : phaseDerivField P F β (mirror y) = mirror (phaseDerivField P F β y) :=
  deriv_equiv mirrorIso (fun b => fieldOf_mirror_all P hP F hF b y) β

theorem gradClass_phaseDeriv (P : ChartParams) (hP : IsChartParams P) (F : FieldData) (hF : IsFieldData P 1 F)
    (β : ℝ) : GradClass P.m (phaseDerivField P F β) := by
  obtain ⟨hcd, -, C, hC⟩ := FracCellInternal.fieldOf_phaseDeriv_regular P hP F hF β
  exact ⟨hcd, phaseDeriv_turn P hP.m_pos F β, phaseDeriv_mirror P hP F hF β, ⟨C, fun y => (hC y).2⟩⟩

theorem phaseCurv_turn (P : ChartParams) (hm : 0 < P.m) (F : FieldData) (β : ℝ) (y : Space) :
    phaseCurvField P F β (turnStep P.m y) = turnStep P.m (phaseCurvField P F β y) :=
  deriv_equiv (turnIso P.m) (fun b => phaseDeriv_turn P hm F b y) β

theorem phaseCurv_mirror (P : ChartParams) (hP : IsChartParams P) (F : FieldData) (hF : IsFieldData P 1 F)
    (β : ℝ) (y : Space) : phaseCurvField P F β (mirror y) = mirror (phaseCurvField P F β y) :=
  deriv_equiv mirrorIso (fun b => phaseDeriv_mirror P hP F hF b y) β

theorem sumWeight_sqDiv {m : ℕ} {f : Space → Space} (hf : Continuous f)
    (ht : ∀ y, f (turnStep m y) = turnStep m (f y)) (hm : ∀ y, f (mirror y) = mirror (f y))
    {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C * (1 + ‖y‖) ^ (-(3 : ℝ))) {w : ℝ} (hw : 0 < w) :
    IsSumWeight m (fun y => ‖f y‖ ^ 2 / w) := by
  have hcont : Continuous (fun y => ‖f y‖ ^ 2 / w) := (hf.norm.pow 2).div_const w
  refine ⟨hcont.measurable, fun y => by positivity, fun y => ?_, fun y => ?_, ?_⟩
  · rw [turnBy_eq, ht, FracInternal.givenNorm_turn]
  · rw [hm, FracInternal.givenNorm_mirror]
  · have hI : Integrable (fun y : Space => C ^ 2 / w * (1 + ‖y‖) ^ (-(2 * 3 : ℝ))) :=
      (integrable_one_add_norm (finrank_lt _ (by norm_num))).const_mul _
    refine hI.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    have h0 : 0 ≤ ‖f y‖ := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← weight_sq, div_mul_eq_mul_div, ← mul_pow]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ h0 (hC y) 2) hw.le

end SumWeightsInternal

namespace SumWeightsCellInternal

theorem centreRegular_of {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) : IsCentreRegular c :=
  ⟨centre_smooth_of D c hS.profile hS.centre_instance,
    by rw [hS.centre_instance.centreSecond_eq]; exact (measurable_fderiv ℝ (fderiv ℝ (D.profile 0))).aestronglyMeasurable,
    centreSecond_symm_of D c hS.profile hS.centre_instance⟩

theorem curlOf_continuous : Continuous (curlOf : (Space →L[ℝ] Space) → Space) := by
  unfold curlOf entry
  fun_prop

theorem cellWeight_nonneg {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) (y : Space) : 0 ≤ c.cellWeight y := by
  rw [hS.rows_instance.cellWeight_eq]
  show 0 ≤ M.piecewise (fun K (_ : Space) => RD.cellWeight K) y
  exact FracInternal.GivenModelModelFrame.piecewise_induct M (fun K (_ : Space) => RD.cellWeight K)
    (fun r : ℝ => 0 ≤ r) le_rfl (fun a b ha hb => add_nonneg ha hb) y (fun K _ => (hS.rows.cellWeight_pos K).le)

theorem cellWeight_measurable {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) : Measurable c.cellWeight := by
  rw [hS.rows_instance.cellWeight_eq]
  exact (FracInternal.GivenModelModelFrame.piecewise_sm M _ fun K => stronglyMeasurable_const).measurable

theorem cellWeight_bound {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) :
    ∃ C : ℝ, ∀ y, c.cellWeight y ≤ C := by
  rw [hS.rows_instance.cellWeight_eq]
  obtain ⟨C, hC⟩ := FracInternal.GivenModelModelFrame.piecewise_bd M (fun K (_ : Space) => RD.cellWeight K)
    (fun K => ⟨|RD.cellWeight K|, fun y _ => le_of_eq (Real.norm_eq_abs _)⟩)
  exact ⟨C, fun y => (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hC y))⟩

theorem cellWeight_congr {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) {y y' : Space}
    (hr : cylRadius y = cylRadius y') (hz : |cylHeight y| = |cylHeight y'|) : c.cellWeight y = c.cellWeight y' := by
  rw [hS.rows_instance.cellWeight_eq]
  unfold cellWeightField CellMesh.piecewise
  refine Finset.sum_congr rfl fun K _ => ?_
  by_cases h : y ∈ M.piece K
  · have h' := (FracInternal.GivenModelModelFrame.mem_piece_congr M K hr hz).1 h
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
  · have h' : y' ∉ M.piece K := fun h' => h ((FracInternal.GivenModelModelFrame.mem_piece_congr M K hr hz).2 h')
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

theorem cellWeight_turn {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) (y : Space) :
    c.cellWeight (turnStep c.order y) = c.cellWeight y :=
  cellWeight_congr c D A M MD RD hS (GivenModelRegionInternal.cylRadius_turnStep _ y)
    (by rw [GivenModelRegionInternal.cylHeight_turnStep])

theorem cellWeight_mirror {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) (y : Space) :
    c.cellWeight (mirror y) = c.cellWeight y :=
  cellWeight_congr c D A M MD RD hS (GivenModelRegionInternal.cylRadius_mirror y)
    (by rw [GivenModelRegionInternal.cylHeight_mirror, abs_neg])

theorem curlError_measurable {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) : Measurable c.curlError := by
  have hC := centreRegular_of c D A M MD RD hS
  have hcc : Continuous c.centreCurl := curlOf_continuous.comp (hC.smooth.continuous_fderiv one_ne_zero)
  have hmc : Measurable c.modelCurl := by
    rw [hS.model_instance.curl_eq]
    exact (FracInternal.GivenModelModelFrame.piecewise_sm M _ fun K =>
      FracInternal.GivenModelModelFrame.pseudoOf_sm _ _).measurable
  have hreg : MeasurableSet c.cellRegion := by
    rw [hS.model_instance.region_eq]
    exact FracInternal.GivenModelModelFrame.region_meas M
  unfold FracCellData.curlError
  exact (hcc.measurable.sub hmc).indicator hreg

theorem curlError_bound {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖c.curlError y‖ ≤ C := by
  have hC := centreRegular_of c D A M MD RD hS
  have hcc : Continuous c.centreCurl := curlOf_continuous.comp (hC.smooth.continuous_fderiv one_ne_zero)
  obtain ⟨-, ⟨Cm, hCm⟩, -, -, -, -⟩ := model_clauses c M MD hS.mesh hS.model hS.model_instance hC
  obtain ⟨-, hb, -⟩ := cellRegion_clauses c M hS.mesh hS.model_instance.region_eq
  obtain ⟨Cc, hCc⟩ := hb.isCompact_closure.exists_bound_of_continuousOn hcc.continuousOn
  refine ⟨|Cc| + |Cm|, by positivity, fun y => ?_⟩
  unfold FracCellData.curlError
  by_cases hy : y ∈ c.cellRegion
  · rw [Set.indicator_of_mem hy]
    refine (norm_sub_le _ _).trans (add_le_add ((hCc y (subset_closure hy)).trans (le_abs_self _)) ?_)
    exact ((hCm y hy).2.1).trans (le_abs_self _)
  · rw [Set.indicator_of_notMem hy, norm_zero]
    positivity

theorem curlError_zero {k N : ℕ} (c : FracCellData k N) {y : Space} (hy : y ∉ c.cellRegion) : c.curlError y = 0 := by
  unfold FracCellData.curlError
  exact Set.indicator_of_notMem hy _

theorem centreSecond_measurable {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) : Measurable c.centreSecond := by
  rw [hS.centre_instance.centreSecond_eq]
  exact measurable_fderiv ℝ (fderiv ℝ (D.profile 0))

theorem curlGradError_measurable {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) :
    Measurable c.curlGradError := by
  have h2 := centreSecond_measurable c D A M MD RD hS
  have hcg : Measurable c.centreCurlGrad := FracInternal.GivenModelModelMain.curlGradMatrix_cont.measurable.comp h2
  have hmg : Measurable c.modelCurlGrad := by
    rw [hS.model_instance.curlGrad_eq]
    have h1 : Measurable (M.piecewise (fun K => pseudoTensorOf c.order (MD.curlGrad K))) :=
      (FracInternal.GivenModelModelFrame.piecewise_sm M _ fun K =>
        FracInternal.GivenModelModelFrame.pseudoTensorOf_sm _ _).measurable
    have h3 : Measurable (Set.indicator M.regionᶜ (fun z => curlGradMatrix (c.centreSecond z))) :=
      hcg.indicator (FracInternal.GivenModelModelFrame.region_meas M).compl
    exact h1.add h3
  exact hcg.sub hmg

theorem curlGradError_bound {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖c.curlGradError y‖ ≤ C := by
  have hC := centreRegular_of c D A M MD RD hS
  obtain ⟨-, ⟨Cm, hCm⟩, -, hout, -, -⟩ := model_clauses c M MD hS.mesh hS.model hS.model_instance hC
  obtain ⟨Cs, hCst⟩ := centre_bounds_of D c hS.profile hS.centre_instance
  obtain ⟨Cg, hCg⟩ := (isCompact_closedBall (0 : Space →L[ℝ] Space →L[ℝ] Space) |Cs|).exists_bound_of_continuousOn
    FracInternal.GivenModelModelMain.curlGradMatrix_cont.continuousOn
  refine ⟨|Cg| + |Cm|, by positivity, fun y => ?_⟩
  by_cases hy : y ∈ c.cellRegion
  · have hs : ‖c.centreSecond y‖ ≤ |Cs| := by
      have h1 := (hCst y).2.2
      have hw : (1 + ‖y‖) ^ (-(3 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)
      have hw0 : 0 ≤ (1 + ‖y‖) ^ (-(3 : ℝ)) := Real.rpow_nonneg (by positivity) _
      calc ‖c.centreSecond y‖ ≤ Cs * (1 + ‖y‖) ^ (-(3 : ℝ)) := h1
        _ ≤ |Cs| * (1 + ‖y‖) ^ (-(3 : ℝ)) := mul_le_mul_of_nonneg_right (le_abs_self _) hw0
        _ ≤ |Cs| * 1 := mul_le_mul_of_nonneg_left hw (abs_nonneg _)
        _ = |Cs| := mul_one _
    have hg : ‖c.centreCurlGrad y‖ ≤ Cg := hCg _ (by rw [Metric.mem_closedBall, dist_zero_right]; exact hs)
    unfold FracCellData.curlGradError
    refine (norm_sub_le _ _).trans (add_le_add (hg.trans (le_abs_self _)) ?_)
    exact ((hCm y hy).2.2.2).trans (le_abs_self _)
  · unfold FracCellData.curlGradError
    rw [(hout y hy).2, sub_self, norm_zero]
    positivity

theorem curlGradError_zero {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) {y : Space}
    (hy : y ∉ c.cellRegion) : c.curlGradError y = 0 := by
  obtain ⟨-, -, -, hout, -, -⟩ := model_clauses c M MD hS.mesh hS.model hS.model_instance
    (centreRegular_of c D A M MD RD hS)
  unfold FracCellData.curlGradError
  rw [(hout y hy).2, sub_self]


end SumWeightsCellInternal

namespace SumWeightsMirrorInternal

open SumWeightsCellInternal

open SumWeightsInternal

theorem fderiv_equiv_apply (L : Space ≃ₗᵢ[ℝ] Space) {f : Space → Space}
    (h : ∀ y, f (L y) = L (f y)) (y u : Space) : fderiv ℝ f (L y) (L u) = L (fderiv ℝ f y u) := by
  have e : f ∘ L = L ∘ f := funext h
  have h1 : fderiv ℝ (f ∘ L) y = (fderiv ℝ f (L y)).comp (L.toContinuousLinearEquiv : Space →L[ℝ] Space) :=
    L.toContinuousLinearEquiv.comp_right_fderiv
  have h2 : fderiv ℝ (L ∘ f) y = (L.toContinuousLinearEquiv : Space →L[ℝ] Space).comp (fderiv ℝ f y) :=
    L.toContinuousLinearEquiv.comp_fderiv
  rw [e, h2] at h1
  have := congrArg (fun T : Space →L[ℝ] Space => T u) h1
  simp only [ContinuousLinearMap.comp_apply] at this
  exact this.symm

def zs (a : Fin 3) : ℝ := if a = 2 then -1 else 1

theorem mirror_apply (v : Space) (l : Fin 3) : (mirror v) l = zs l * v l := by
  fin_cases l <;> simp [SteadyCert.mirror, zs]

theorem mirror_unit (j : Fin 3) : mirror (unitVector j) = zs j • unitVector j := by
  ext l
  fin_cases j <;> fin_cases l <;> simp [SteadyCert.mirror, zs, unitVector]

theorem mirror_mirror (v : Space) : mirror (mirror v) = v := by
  ext l
  fin_cases l <;> simp [SteadyCert.mirror]

theorem entry_mirror {A B : Space →L[ℝ] Space} (h : ∀ u, B u = mirror (A (mirror u))) (l j : Fin 3) :
    entry B l j = zs l * zs j * entry A l j := by
  unfold entry
  rw [h, mirror_unit, map_smul, mirror_apply]
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

theorem curlOf_mirror {A B : Space →L[ℝ] Space} (h : ∀ u, B u = mirror (A (mirror u))) :
    curlOf B = -mirror (curlOf A) := by
  ext i
  simp only [curlOf, entry_mirror h, PiLp.neg_apply, mirror_apply]
  fin_cases i <;> simp [Fin.sum_univ_three, permSign, zs, unitVector] <;> ring

theorem centre_mirror_all {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) (y : Space) :
    c.centre (mirror y) = mirror (c.centre y) :=
  everywhere_of_ae mirrorIso (centreRegular_of c D A M MD RD hS).smooth.continuous
    (centre_class_of D c hS.profile hS.centre_instance).2 y

theorem centreGrad_mirror {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) (y u : Space) :
    c.centreGrad (mirror y) u = mirror (c.centreGrad y (mirror u)) := by
  have h := fderiv_equiv_apply mirrorIso (centre_mirror_all c D A M MD RD hS) y (mirror u)
  simp only [mirrorIso_apply, mirror_mirror] at h
  exact h

theorem curlError_mirror {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) (y : Space) :
    ‖c.curlError (mirror y)‖ = ‖c.curlError y‖ := by
  have hR := hS.model_instance.region_eq
  by_cases hz : cylHeight y = 0
  · have : mirror y = y := by
      ext l
      simp only [cylHeight] at hz
      fin_cases l <;> simp [SteadyCert.mirror, hz]
    rw [this]
  by_cases hy : y ∈ c.cellRegion
  · have hyM : y ∈ M.region := hR ▸ hy
    have hmy : mirror y ∈ c.cellRegion := by
      rw [hR]
      exact (FracInternal.GivenModelModelFrame.mem_region_mirror M y).2 hyM
    obtain ⟨K, hK⟩ := Set.mem_iUnion.1 hyM
    have hsub : (M.box K).solid ⊆ c.cellRegion := by
      rw [hR]
      exact FracInternal.GivenModelModelFrame.solid_sub M K
    have hm := (modelMirror_of c M MD hS.mesh hS.model_instance (M.box K) hsub y hK hz).2.1
    have hc : c.centreCurl (mirror y) = -mirror (c.centreCurl y) :=
      curlOf_mirror (centreGrad_mirror c D A M MD RD hS y)
    unfold FracCellData.curlError
    rw [Set.indicator_of_mem hmy, Set.indicator_of_mem hy, hc, hm]
    have e : -mirror (c.centreCurl y) - -mirror (c.modelCurl y) =
        -(mirrorIso (c.centreCurl y - c.modelCurl y)) := by
      rw [map_sub, mirrorIso_apply, mirrorIso_apply]
      abel
    rw [e, norm_neg, LinearIsometryEquiv.norm_map]
  · have hmy : mirror y ∉ c.cellRegion := by
      rw [hR] at hy ⊢
      exact fun h => hy ((FracInternal.GivenModelModelFrame.mem_region_mirror M y).1 h)
    rw [curlError_zero c hy, curlError_zero c hmy]


theorem mirror_symm (u : Space) : mirrorIso.symm u = mirror u := by
  rw [LinearIsometryEquiv.symm_apply_eq, mirrorIso_apply, mirror_mirror]

def mirrorOp : (Space →L[ℝ] Space) ≃L[ℝ] (Space →L[ℝ] Space) :=
  mirrorIso.toContinuousLinearEquiv.arrowCongr mirrorIso.toContinuousLinearEquiv

theorem mirrorOp_apply (A : Space →L[ℝ] Space) (u : Space) : mirrorOp A u = mirror (A (mirror u)) := by
  simp [mirrorOp, mirror_symm]
  rfl

theorem mirrorConj_norm (A X : Space →L[ℝ] Space) (h : ∀ u, X u = -mirror (A (mirror u))) : ‖X‖ = ‖A‖ := by
  have e : X = -((mirrorIso : Space →L[ℝ] Space).comp (A.comp (mirrorIso : Space →L[ℝ] Space))) := by
    ext1 u
    rw [h]
    rfl
  rw [e, norm_neg, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

theorem centreSecond_eq_fderiv {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) :
    c.centreSecond = fderiv ℝ c.centreGrad := by
  funext y
  rw [hS.centre_instance.centreSecond_eq]
  unfold FracCellData.centreGrad
  rw [hS.centre_instance.centre_eq]
  rfl

theorem centreSecond_mirror {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) (y v u : Space) :
    c.centreSecond (mirror y) v u = mirror (c.centreSecond y (mirror v) (mirror u)) := by
  have hG : ∀ z, c.centreGrad (mirrorIso z) = mirrorOp (c.centreGrad z) := fun z => by
    ext1 u
    rw [mirrorOp_apply]
    exact centreGrad_mirror c D A M MD RD hS z u
  have e : c.centreGrad ∘ mirrorIso = mirrorOp ∘ c.centreGrad := funext hG
  have h1 : fderiv ℝ (c.centreGrad ∘ mirrorIso) y =
      (fderiv ℝ c.centreGrad (mirrorIso y)).comp (mirrorIso.toContinuousLinearEquiv : Space →L[ℝ] Space) :=
    mirrorIso.toContinuousLinearEquiv.comp_right_fderiv
  have h2 : fderiv ℝ (mirrorOp ∘ c.centreGrad) y =
      (mirrorOp : (Space →L[ℝ] Space) →L[ℝ] (Space →L[ℝ] Space)).comp (fderiv ℝ c.centreGrad y) :=
    mirrorOp.comp_fderiv
  rw [e, h2] at h1
  have := congrArg (fun T : Space →L[ℝ] Space →L[ℝ] Space => T (mirror v) u) h1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at this
  rw [mirrorOp_apply] at this
  rw [centreSecond_eq_fderiv c D A M MD RD hS]
  convert this.symm using 3
  all_goals first | exact (mirror_mirror v).symm | rfl

theorem curlGradMatrix_mirror {H B : Space →L[ℝ] Space →L[ℝ] Space}
    (h : ∀ v u, B v u = mirror (H (mirror v) (mirror u))) (u : Space) :
    curlGradMatrix B u = -mirror (curlGradMatrix H (mirror u)) := by
  have hB : ∀ l b q, B (unitVector l) (unitVector b) q =
      zs q * zs l * zs b * H (unitVector l) (unitVector b) q := by
    intro l b q
    rw [h, mirror_unit, mirror_unit, mirror_apply]
    simp only [map_smul, ContinuousLinearMap.smul_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  ext i
  simp only [curlGradMatrix, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hB, PiLp.neg_apply, mirror_apply,
    PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum]
  fin_cases i <;> simp [Fin.sum_univ_three, permSign, zs, unitVector, EuclideanSpace.inner_single_left, mirror_apply] <;> ring

theorem curlGradError_mirror {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) (y : Space) :
    ‖c.curlGradError (mirror y)‖ = ‖c.curlGradError y‖ := by
  have hR := hS.model_instance.region_eq
  by_cases hz : cylHeight y = 0
  · have : mirror y = y := by
      ext l
      simp only [cylHeight] at hz
      fin_cases l <;> simp [SteadyCert.mirror, hz]
    rw [this]
  by_cases hy : y ∈ c.cellRegion
  · have hyM : y ∈ M.region := hR ▸ hy
    obtain ⟨K, hK⟩ := Set.mem_iUnion.1 hyM
    have hsub : (M.box K).solid ⊆ c.cellRegion := by
      rw [hR]
      exact FracInternal.GivenModelModelFrame.solid_sub M K
    have hm := (modelMirror_of c M MD hS.mesh hS.model_instance (M.box K) hsub y hK hz).2.2.2.1
    have hc := curlGradMatrix_mirror (centreSecond_mirror c D A M MD RD hS y)
    refine mirrorConj_norm _ _ fun u => ?_
    unfold FracCellData.curlGradError FracCellData.centreCurlGrad
    have key : ∀ a b : Space, -mirror a - -mirror b = -mirror (a - b) := fun a b => by
      ext l
      simp only [PiLp.sub_apply, PiLp.neg_apply, mirror_apply]
      ring
    simp only [_root_.sub_apply]
    rw [hc u, hm u, key]
  · have hmy : mirror y ∉ c.cellRegion := by
      rw [hR] at hy ⊢
      exact fun h => hy ((FracInternal.GivenModelModelFrame.mem_region_mirror M y).1 h)
    rw [curlGradError_zero c D A M MD RD hS hy, curlGradError_zero c D A M MD RD hS hmy]

end SumWeightsMirrorInternal

namespace SumWeightsTurnInternal

open SumWeightsInternal SumWeightsMirrorInternal

theorem plane_norm (y : Space) : ‖((y 0 : ℂ) + (y 1 : ℂ) * Complex.I)‖ = cylRadius y := by
  rw [Complex.norm_add_mul_I]
  rfl

theorem turn_plane (m : ℕ) (y : Space) :
    (((turnStep m y) 0 : ℂ) + ((turnStep m y) 1 : ℂ) * Complex.I) =
      ((Real.cos (2 * Real.pi / m) * y 0 - Real.sin (2 * Real.pi / m) * y 1 : ℝ) : ℂ) +
        ((Real.sin (2 * Real.pi / m) * y 0 + Real.cos (2 * Real.pi / m) * y 1 : ℝ) : ℂ) * Complex.I := by
  simp [turnStep]

theorem angle_cos_sin (m : ℕ) (y : Space) (hy : cylRadius y ≠ 0) :
    Real.cos (cylAngle (turnStep m y)) = Real.cos (cylAngle y + 2 * Real.pi / m) ∧
      Real.sin (cylAngle (turnStep m y)) = Real.sin (cylAngle y + 2 * Real.pi / m) := by
  have hz : ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) ≠ 0 := by
    intro h
    apply hy
    rw [← plane_norm, h, norm_zero]
  have hz' : (((turnStep m y) 0 : ℂ) + ((turnStep m y) 1 : ℂ) * Complex.I) ≠ 0 := by
    intro h
    apply hy
    rw [← GivenModelRegionInternal.cylRadius_turnStep m y, ← plane_norm, h, norm_zero]
  have hr := plane_norm y
  have hr' : ‖(((turnStep m y) 0 : ℂ) + ((turnStep m y) 1 : ℂ) * Complex.I)‖ = cylRadius y := by
    rw [plane_norm, GivenModelRegionInternal.cylRadius_turnStep]
  unfold cylAngle
  rw [Real.cos_add, Real.sin_add, Complex.cos_arg hz', Complex.sin_arg, Complex.cos_arg hz, Complex.sin_arg, hr, hr']
  rw [turn_plane]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  constructor <;> field_simp <;> ring

theorem exp_turn (m : ℕ) (hm : 0 < m) (β : ℕ) (y : Space) (hy : cylRadius y ≠ 0) :
    Complex.exp (((azimuth m (β : ℤ) * cylAngle (turnStep m y) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((azimuth m (β : ℤ) * cylAngle y : ℝ) : ℂ) * Complex.I) := by
  obtain ⟨hc, hs⟩ := angle_cos_sin m y hy
  have e1 : Complex.exp ((cylAngle (turnStep m y) : ℂ) * Complex.I) =
      Complex.exp (((cylAngle y + 2 * Real.pi / m : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, hc, hs]
  have hn : azimuth m (β : ℤ) = ((β * m : ℕ) : ℝ) := by
    simp [azimuth]
  have key : ∀ t : ℝ, Complex.exp (((((β * m : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((t : ℂ) * Complex.I) ^ (β * m) := fun t => by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hn, key, e1, ← key]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have e2 : ((((β * m : ℕ) : ℝ) * (cylAngle y + 2 * Real.pi / m) : ℝ) : ℂ) * Complex.I =
      ((((β * m : ℕ) : ℝ) * cylAngle y : ℝ) : ℂ) * Complex.I + (β : ℕ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp
    try ring
  rw [e2, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem harmonic_turn (m : ℕ) (hm : 0 < m) {d J : ℕ} (P : Fin (J + 1) → CellPoly d) (y : Space)
    (hy : cylRadius y ≠ 0) : harmonicValue m P (turnStep m y) = harmonicValue m P y := by
  unfold harmonicValue
  simp only [GivenModelRegionInternal.cylRadius_turnStep, GivenModelRegionInternal.cylHeight_turnStep,
    exp_turn m hm _ y hy]

theorem frame_turn_angle (m : ℕ) (y : Space) (hy : cylRadius y ≠ 0) (a : Fin 3) :
    frameUnit (cylAngle (turnStep m y)) a = turnStep m (frameUnit (cylAngle y) a) := by
  rw [FracInternal.DensitySlice.turn_frame]
  obtain ⟨hc, hs⟩ := angle_cos_sin m y hy
  fin_cases a <;> simp [frameUnit, radialUnit, angularUnit, axialUnit, hc, hs]

theorem cart_turn (m : ℕ) (y : Space) (hy : cylRadius y ≠ 0) (w : Fin 3 → ℝ) :
    cartOfFrame (cylAngle (turnStep m y)) w = turnStep m (cartOfFrame (cylAngle y) w) := by
  unfold cartOfFrame
  conv_rhs => rw [← turnIso_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, turnIso_apply, frame_turn_angle m y hy]

theorem axis_fixed (m : ℕ) (y : Space) (hy : cylRadius y = 0) : turnStep m y = y := by
  have h : y 0 ^ 2 + y 1 ^ 2 = 0 := by
    unfold cylRadius at hy
    rwa [Real.sqrt_eq_zero (by positivity)] at hy
  have h0 : y 0 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
  have h1 : y 1 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
  ext i
  fin_cases i <;> simp [turnStep, h0, h1]

theorem pseudoOf_turn (m : ℕ) (hm : 0 < m) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → CellPoly d) (y : Space)
    (hy : cylRadius y ≠ 0) : pseudoOf m P (turnStep m y) = turnStep m (pseudoOf m P y) := by
  have hsgn : ∀ a, pseudoSign (turnStep m y) a = pseudoSign y a := fun a => by
    simp only [pseudoSign, vectorSign, GivenModelRegionInternal.cylHeight_turnStep]
  unfold pseudoOf
  simp only [hsgn, harmonic_turn m hm _ y hy]
  exact cart_turn m y hy _

theorem mem_region_turn (M : CellMesh) (m : ℕ) (y : Space) : turnStep m y ∈ M.region ↔ y ∈ M.region := by
  simp only [CellMesh.region, Set.mem_iUnion, CellBox.solid, Set.mem_ofPred_eq,
    GivenModelRegionInternal.cylRadius_turnStep, GivenModelRegionInternal.cylHeight_turnStep]

theorem modelCurl_turn {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) (y : Space)
    (hy : cylRadius y ≠ 0) : c.modelCurl (turnStep c.order y) = turnStep c.order (c.modelCurl y) := by
  have hm : 0 < c.order := by rw [hS.centre_instance.order_eq]; exact hS.profile.chart.m_pos
  rw [hS.model_instance.curl_eq]
  unfold ModelData.curlField CellMesh.piecewise
  conv_rhs => rw [← turnIso_apply, map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  have hcong := FracInternal.GivenModelModelFrame.mem_piece_congr M K (GivenModelRegionInternal.cylRadius_turnStep c.order y)
    (by rw [GivenModelRegionInternal.cylHeight_turnStep])
  by_cases h : y ∈ M.piece K
  · rw [Set.indicator_of_mem (hcong.2 h), Set.indicator_of_mem h, turnIso_apply]
    exact pseudoOf_turn _ hm _ _ hy
  · rw [Set.indicator_of_notMem (fun h' => h (hcong.1 h')), Set.indicator_of_notMem h, map_zero]

theorem turn_inv (m : ℕ) :
    turnStep m (Real.cos (2 * Real.pi / m) • unitVector 0 - Real.sin (2 * Real.pi / m) • unitVector 1) = unitVector 0 ∧
    turnStep m (Real.sin (2 * Real.pi / m) • unitVector 0 + Real.cos (2 * Real.pi / m) • unitVector 1) = unitVector 1 ∧
    turnStep m (unitVector 2) = unitVector 2 := by
  have hcs := Real.sin_sq_add_cos_sq (2 * Real.pi / m)
  refine ⟨?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;> simp [turnStep, unitVector] <;>
    first | ring1 | linear_combination hcs | linear_combination -hcs

theorem curlOf_turn (m : ℕ) {A B : Space →L[ℝ] Space} (h : ∀ u, B (turnStep m u) = turnStep m (A u)) :
    curlOf B = turnStep m (curlOf A) := by
  obtain ⟨t0, t1, t2⟩ := turn_inv m
  have hB0 := h (Real.cos (2 * Real.pi / m) • unitVector 0 - Real.sin (2 * Real.pi / m) • unitVector 1)
  have hB1 := h (Real.sin (2 * Real.pi / m) • unitVector 0 + Real.cos (2 * Real.pi / m) • unitVector 1)
  have hB2 := h (unitVector 2)
  rw [t0] at hB0
  rw [t1] at hB1
  rw [t2] at hB2
  have hcs := Real.sin_sq_add_cos_sq (2 * Real.pi / m)
  ext i
  simp only [curlOf, entry, Fin.sum_univ_three, hB0, hB1, hB2]
  fin_cases i <;> simp [permSign, turnStep, unitVector, map_sub, map_add, map_smul] <;>
    first | ring1 | linear_combination ((A (EuclideanSpace.single 0 1)) 1 - (A (EuclideanSpace.single 1 1)) 0) * hcs

theorem centre_turn_all {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) (y : Space) :
    c.centre (turnStep c.order y) = turnStep c.order (c.centre y) :=
  everywhere_of_ae (turnIso c.order) (centre_smooth_of D c hS.profile hS.centre_instance).continuous
    (centre_class_of D c hS.profile hS.centre_instance).1 y

theorem curlError_turn {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) (y : Space) :
    ‖c.curlError (turnStep c.order y)‖ = ‖c.curlError y‖ := by
  by_cases hr : cylRadius y = 0
  · rw [axis_fixed _ y hr]
  have hR := hS.model_instance.region_eq
  have hmem : turnStep c.order y ∈ c.cellRegion ↔ y ∈ c.cellRegion := by
    rw [hR]
    exact mem_region_turn M c.order y
  unfold FracCellData.curlError
  by_cases hy : y ∈ c.cellRegion
  · rw [Set.indicator_of_mem (hmem.2 hy), Set.indicator_of_mem hy]
    have hc : c.centreCurl (turnStep c.order y) = turnStep c.order (c.centreCurl y) :=
      curlOf_turn c.order (fun u => fderiv_equiv_apply (turnIso c.order) (centre_turn_all c D A M MD RD hS) y u)
    rw [hc, modelCurl_turn c D A M MD RD hS y hr, ← turnIso_apply, ← turnIso_apply, ← map_sub,
      LinearIsometryEquiv.norm_map]
  · rw [Set.indicator_of_notMem (fun h => hy (hmem.1 h)), Set.indicator_of_notMem hy]

end SumWeightsTurnInternal

namespace SumWeightsSecondInternal

open SumWeightsInternal SumWeightsMirrorInternal SumWeightsTurnInternal SumWeightsCellInternal

theorem curlGradMatrix_apply (H : Space →L[ℝ] Space →L[ℝ] Space) (u : Space) :
    curlGradMatrix H u = curlOf (H u) := by
  have hu : u = u 0 • unitVector 0 + u 1 • unitVector 1 + u 2 • unitVector 2 := by
    ext i
    fin_cases i <;> simp [unitVector]
  ext i
  conv_rhs => rw [hu]
  simp only [curlGradMatrix, curlOf, entry, map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]
  fin_cases i <;> simp [Fin.sum_univ_three, permSign, unitVector, EuclideanSpace.inner_single_left] <;> ring

theorem conj_norm (L : Space ≃ₗᵢ[ℝ] Space) (A X : Space →L[ℝ] Space) (h : ∀ u, X (L u) = L (A u)) : ‖X‖ = ‖A‖ := by
  have e : X = (L : Space →L[ℝ] Space).comp (A.comp (L.symm : Space →L[ℝ] Space)) := by
    ext1 u
    have := h (L.symm u)
    rw [LinearIsometryEquiv.apply_symm_apply] at this
    rw [this]
    rfl
  rw [e, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

theorem cartOp_turn (m : ℕ) (y : Space) (hy : cylRadius y ≠ 0) (M : Fin 3 → Fin 3 → ℝ) (u : Space) :
    cartOpOfFrame (cylAngle (turnStep m y)) M (turnStep m u) = turnStep m (cartOpOfFrame (cylAngle y) M u) := by
  unfold cartOpOfFrame
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, frame_turn_angle m y hy,
    FracInternal.DensitySlice.turn_inner]
  conv_rhs => rw [← turnIso_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, map_smul, turnIso_apply]

theorem pseudoTensorOf_turn (m : ℕ) (hm : 0 < m) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d)
    (y : Space) (hy : cylRadius y ≠ 0) (u : Space) :
    pseudoTensorOf m P (turnStep m y) (turnStep m u) = turnStep m (pseudoTensorOf m P y u) := by
  have hv : ∀ a, vectorSign (turnStep m y) a = vectorSign y a := fun a => by
    simp only [vectorSign, GivenModelRegionInternal.cylHeight_turnStep]
  have hsgn : ∀ a, pseudoSign (turnStep m y) a = pseudoSign y a := fun a => by
    simp only [pseudoSign, vectorSign, GivenModelRegionInternal.cylHeight_turnStep]
  unfold pseudoTensorOf
  simp only [hsgn, hv, harmonic_turn m hm _ y hy]
  exact cartOp_turn m y hy _ u

theorem centreGrad_turn {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) (y u : Space) :
    c.centreGrad (turnStep c.order y) (turnStep c.order u) = turnStep c.order (c.centreGrad y u) :=
  fderiv_equiv_apply (turnIso c.order) (centre_turn_all c D A M MD RD hS) y u

def turnOp (m : ℕ) : (Space →L[ℝ] Space) ≃L[ℝ] (Space →L[ℝ] Space) :=
  (turnIso m).toContinuousLinearEquiv.arrowCongr (turnIso m).toContinuousLinearEquiv

theorem turnOp_apply (m : ℕ) (A : Space →L[ℝ] Space) (u : Space) :
    turnOp m A (turnStep m u) = turnStep m (A u) := by
  simp [turnOp]
  rw [← turnIso_apply m u, LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem centreSecond_turn {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) (y v u : Space) :
    c.centreSecond (turnStep c.order y) (turnStep c.order v) (turnStep c.order u) =
      turnStep c.order (c.centreSecond y v u) := by
  have hG : ∀ z, c.centreGrad (turnIso c.order z) = turnOp c.order (c.centreGrad z) := fun z => by
    ext1 w
    obtain ⟨w', rfl⟩ : ∃ w', w = turnStep c.order w' := ⟨(turnIso c.order).symm w, by
      rw [← turnIso_apply, LinearIsometryEquiv.apply_symm_apply]⟩
    rw [turnOp_apply]
    exact centreGrad_turn c D A M MD RD hS z w'
  have e : c.centreGrad ∘ turnIso c.order = turnOp c.order ∘ c.centreGrad := funext hG
  have h1 : fderiv ℝ (c.centreGrad ∘ turnIso c.order) y =
      (fderiv ℝ c.centreGrad (turnIso c.order y)).comp
        ((turnIso c.order).toContinuousLinearEquiv : Space →L[ℝ] Space) :=
    (turnIso c.order).toContinuousLinearEquiv.comp_right_fderiv
  have h2 : fderiv ℝ (turnOp c.order ∘ c.centreGrad) y =
      (turnOp c.order : (Space →L[ℝ] Space) →L[ℝ] (Space →L[ℝ] Space)).comp (fderiv ℝ c.centreGrad y) :=
    (turnOp c.order).comp_fderiv
  rw [e, h2] at h1
  have := congrArg (fun T : Space →L[ℝ] Space →L[ℝ] Space => T v (turnStep c.order u)) h1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at this
  rw [turnOp_apply] at this
  rw [centreSecond_eq_fderiv c D A M MD RD hS]
  exact this.symm

theorem curlGradError_turn {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) (y : Space) :
    ‖c.curlGradError (turnStep c.order y)‖ = ‖c.curlGradError y‖ := by
  by_cases hr : cylRadius y = 0
  · rw [axis_fixed _ y hr]
  have hm : 0 < c.order := by rw [hS.centre_instance.order_eq]; exact hS.profile.chart.m_pos
  have hR := hS.model_instance.region_eq
  have hmem : turnStep c.order y ∈ c.cellRegion ↔ y ∈ c.cellRegion := by
    rw [hR]
    exact mem_region_turn M c.order y
  by_cases hy : y ∈ c.cellRegion
  · refine conj_norm (turnIso c.order) _ _ fun u => ?_
    have hyM : y ∈ M.region := hR ▸ hy
    have hTM : turnStep c.order y ∈ M.region := hR ▸ hmem.2 hy
    have hmodel : ∀ z ∈ M.region, ∀ w, c.modelCurlGrad z w =
        M.piecewise (fun K => pseudoTensorOf c.order (MD.curlGrad K)) z w := fun z hz w => by
      rw [hS.model_instance.curlGrad_eq]
      show (M.piecewise (fun K => pseudoTensorOf c.order (MD.curlGrad K)) z +
        Set.indicator M.regionᶜ (fun z => curlGradMatrix (c.centreSecond z)) z) w = _
      rw [Set.indicator_of_notMem (Set.notMem_compl_iff.2 hz), add_zero]
    have hpw : M.piecewise (fun K => pseudoTensorOf c.order (MD.curlGrad K)) (turnStep c.order y)
        (turnStep c.order u) = turnStep c.order (M.piecewise (fun K => pseudoTensorOf c.order (MD.curlGrad K)) y u) := by
      unfold CellMesh.piecewise
      rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
      conv_rhs => rw [← turnIso_apply, map_sum]
      refine Finset.sum_congr rfl fun K _ => ?_
      have hcong := FracInternal.GivenModelModelFrame.mem_piece_congr M K
        (GivenModelRegionInternal.cylRadius_turnStep c.order y) (by rw [GivenModelRegionInternal.cylHeight_turnStep])
      by_cases h : y ∈ M.piece K
      · rw [Set.indicator_of_mem (hcong.2 h), Set.indicator_of_mem h, turnIso_apply]
        exact pseudoTensorOf_turn _ hm _ _ hr u
      · rw [Set.indicator_of_notMem (fun h' => h (hcong.1 h')), Set.indicator_of_notMem h,
          ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply, map_zero]
    have hc : curlGradMatrix (c.centreSecond (turnStep c.order y)) (turnStep c.order u) =
        turnStep c.order (curlGradMatrix (c.centreSecond y) u) := by
      rw [curlGradMatrix_apply, curlGradMatrix_apply]
      exact curlOf_turn c.order (fun w => centreSecond_turn c D A M MD RD hS y u w)
    unfold FracCellData.curlGradError FracCellData.centreCurlGrad
    rw [_root_.sub_apply, _root_.sub_apply, hmodel _ hTM, hmodel _ hyM]
    simp only [turnIso_apply]
    rw [hc, hpw]
    exact (map_sub (turnIso c.order) _ _).symm
  · rw [curlGradError_zero c D A M MD RD hS hy, curlGradError_zero c D A M MD RD hS (fun h => hy (hmem.1 h))]

end SumWeightsSecondInternal

namespace SumWeightsCellInternal

theorem integrable_of_region {V : Space → ℝ} (hV : Measurable V) {s : Set Space} (hs : MeasurableSet s)
    (hfin : volume s < ⊤) {B : ℝ} (hB : ∀ y, |V y| ≤ B) (h0 : ∀ y ∉ s, V y = 0) : Integrable V :=
  memLp_one_iff_integrable.1 (FracInternal.GivenModelModelMain.memLp_of_bd s hs hfin V hV.aestronglyMeasurable B
    (fun y => by rw [Real.norm_eq_abs]; exact hB y) h0 1)

theorem region_facts {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) :
    MeasurableSet c.cellRegion ∧ volume c.cellRegion < ⊤ := by
  rw [hS.model_instance.region_eq]
  exact ⟨FracInternal.GivenModelModelFrame.region_meas M, FracInternal.GivenModelModelMain.region_fin M⟩

theorem curlGradError_sumWeight {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) :
    IsSumWeight c.order (fun y => ‖c.curlGradError y‖ ^ 2) := by
  have hm : Measurable (fun y => ‖c.curlGradError y‖ ^ 2) :=
    (curlGradError_measurable c D A M MD RD hS).norm.pow_const 2
  obtain ⟨C, hC0, hC⟩ := curlGradError_bound c D A M MD RD hS
  obtain ⟨hs, hfin⟩ := region_facts c D A M MD RD hS
  refine ⟨hm, fun y => by positivity, fun y => ?_, fun y => ?_, ?_⟩
  · rw [SumWeightsInternal.turnBy_eq, SumWeightsSecondInternal.curlGradError_turn c D A M MD RD hS]
  · rw [SumWeightsMirrorInternal.curlGradError_mirror c D A M MD RD hS]
  · refine integrable_of_region hm hs hfin (B := C ^ 2) (fun y => ?_) (fun y hy => ?_)
    · rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC y) 2
    · rw [curlGradError_zero c D A M MD RD hS hy, norm_zero]
      norm_num

theorem curlError_sumWeight {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) :
    IsSumWeight c.order (fun y => c.cellWeight y * ‖c.curlError y‖ ^ 2) := by
  have hm : Measurable (fun y => c.cellWeight y * ‖c.curlError y‖ ^ 2) :=
    (cellWeight_measurable c D A M MD RD hS).mul ((curlError_measurable c D A M MD RD hS).norm.pow_const 2)
  have hnn := cellWeight_nonneg c D A M MD RD hS
  obtain ⟨C, hC0, hC⟩ := curlError_bound c D A M MD RD hS
  obtain ⟨Cw, hCw⟩ := cellWeight_bound c D A M MD RD hS
  obtain ⟨hs, hfin⟩ := region_facts c D A M MD RD hS
  refine ⟨hm, fun y => mul_nonneg (hnn y) (by positivity), fun y => ?_, fun y => ?_, ?_⟩
  · rw [SumWeightsInternal.turnBy_eq, cellWeight_turn c D A M MD RD hS,
      SumWeightsTurnInternal.curlError_turn c D A M MD RD hS]
  · rw [cellWeight_mirror c D A M MD RD hS, SumWeightsMirrorInternal.curlError_mirror c D A M MD RD hS]
  · refine integrable_of_region hm hs hfin (B := Cw * C ^ 2) (fun y => ?_) (fun y hy => ?_)
    · rw [abs_of_nonneg (mul_nonneg (hnn y) (by positivity))]
      exact mul_le_mul (hCw y) (pow_le_pow_left₀ (norm_nonneg _) (hC y) 2) (by positivity)
        ((hnn y).trans (hCw y))
    · rw [curlError_zero c hy, norm_zero]
      norm_num

end SumWeightsCellInternal

open SumWeightsInternal

theorem sumWeights_of {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) (w : ℝ) (hw : 0 < w)
    (step : Fin k → ℝ) (hamp : ∀ i, Pi.single i 1 ∈ D.index) :
    IsSumWeight c.order (fun y => ‖c.curlGradError y‖ ^ 2) ∧
    IsSumWeight c.order (fun y => c.cellWeight y * ‖c.curlError y‖ ^ 2) ∧
    (∀ i β, IsSumWeight c.order (gradSq (ampField D step i β))) ∧
    (∀ μ ∈ D.index, 2 ≤ ∑ i, μ i → ∀ β, IsSumWeight c.order (gradSq (fieldOf D.chart (D.part μ) β))) ∧
    (∀ β, IsSumWeight c.order (gradSq (phaseCurvField D.chart (D.part 0) β))) ∧
    (∀ j ∈ c.activeSet, ∀ γ ∈ (A.adjointFamily j).indices, ∀ β,
      IsSumWeight c.order (fun y => ‖fieldOf D.chart ((A.adjointFamily j).coef γ) β y‖ ^ 2 / w)) := by
  have hP : IsChartParams D.chart := hS.profile.chart
  have hord : c.order = D.chart.m := hS.centre_instance.order_eq
  refine ⟨SumWeightsCellInternal.curlGradError_sumWeight c D A M MD RD hS,
    SumWeightsCellInternal.curlError_sumWeight c D A M MD RD hS, fun i β => ?_, fun μ hμ _ β => ?_, fun β => ?_,
    fun j _ γ hγ β => ?_⟩
  · rw [hord]
    have e : ampField D step i β = fun y => fieldOf D.chart (D.part (Pi.single i 1)) β y +
        step i • phaseDerivField D.chart (D.part 0) β y := rfl
    rw [e]
    exact sumWeight_gradSq (gradClass_add_smul
      (gradClass_fieldOf D.chart hP _ (hS.profile.parts _ (hamp i)) β)
      (gradClass_phaseDeriv D.chart hP _ (hS.profile.parts _ hS.profile.index_zero) β) (step i))
  · rw [hord]
    exact sumWeight_gradSq (gradClass_fieldOf D.chart hP _ (hS.profile.parts μ hμ) β)
  · rw [hord]
    have hF := hS.profile.parts _ hS.profile.index_zero
    obtain ⟨hcd, hb⟩ := SumWeightsOpen.phaseCurv_regular D.chart hP _ hF β
    exact sumWeight_gradSq ⟨hcd, phaseCurv_turn D.chart hP.m_pos _ β, phaseCurv_mirror D.chart hP _ hF β, hb⟩
  · rw [hord]
    have hF := hS.aux.adjoint_shape j γ hγ
    obtain ⟨C, hC⟩ := AdjointCoreInternal.field_decay D.chart hP _ hF β
    exact sumWeight_sqDiv (AdjointCoreInternal.field_contDiff D.chart hP _ hF β).continuous
      (fun y => (AdjointCoreInternal.field_class D.chart hP _ hF β y).1)
      (fun y => (AdjointCoreInternal.field_class D.chart hP _ hF β y).2) hC hw

end CellSystem

end CellCert

end Breakdown
