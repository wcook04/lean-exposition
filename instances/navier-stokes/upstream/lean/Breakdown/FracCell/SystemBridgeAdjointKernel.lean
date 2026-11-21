import Breakdown.FracCell.CellSystemDefs
import Breakdown.FracCell.SystemBridgesSums
import Breakdown.FracCell.GivenAuxAdjointCore
import Breakdown.FracCell.ReductionLossKernelBound_of_cellSums

open scoped ContDiff ENNReal
open MeasureTheory Matrix Polynomial

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellSystem

open SteadyCert Assembly Reduction GivenFields GivenModel Exterior Spectral CellAnalysis CellCoordinates CellFormula
open _root_.Breakdown.CellCert.Finite

namespace AdjointKernelInternal

private theorem pair_bound (u v : Space → ℝ) (hu : ∀ y, 0 ≤ u y) (hv : ∀ y, 0 ≤ v y)
    (hum : AEStronglyMeasurable u volume) (hvm : AEStronglyMeasurable v volume)
    (hu2 : Integrable (fun y => u y ^ 2)) (hv2 : Integrable (fun y => v y ^ 2)) :
    Integrable (fun y => u y * v y) ∧
      (∫ y, u y * v y) ≤ Real.sqrt (∫ y, u y ^ 2) * Real.sqrt (∫ y, v y ^ 2) := by
  have hint : Integrable (fun y => u y * v y) := by
    refine Integrable.mono' (hu2.add hv2) (hum.mul hvm) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hu y) (hv y)), Pi.add_apply]
    nlinarith [sq_nonneg (u y - v y), hu y, hv y]
  refine ⟨hint, ?_⟩
  have huL : MemLp u (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) by simp]
    exact (memLp_two_iff_integrable_sq hum).2 hu2
  have hvL : MemLp v (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) by simp]
    exact (memLp_two_iff_integrable_sq hvm).2 hv2
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hu) (Filter.Eventually.of_forall hv) huL hvL
  have e1 : ∀ f : Space → ℝ, (∫ y, f y ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = Real.sqrt (∫ y, f y ^ 2) := by
    intro f
    rw [Real.sqrt_eq_rpow]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact Real.rpow_two (f y)
  rw [e1 u, e1 v] at hH
  exact hH

private theorem sum_bound {ι : Type} (I : Finset ι) (a κ : ι → ℝ) (u : ι → Space → ℝ) (g : Space → ℝ)
    (ha : ∀ i ∈ I, 0 ≤ a i) (hκ : ∀ i ∈ I, 0 ≤ κ i) (hu : ∀ i ∈ I, ∀ y, 0 ≤ u i y)
    (hum : ∀ i ∈ I, AEStronglyMeasurable (u i) volume) (hu2 : ∀ i ∈ I, Integrable (fun y => u i y ^ 2))
    (hle : ∀ i ∈ I, (∫ y, u i y ^ 2) ≤ κ i ^ 2)
    (hgm : AEStronglyMeasurable g volume) (hg0 : ∀ y, 0 ≤ g y) (hg : ∀ y, g y ≤ (∑ i ∈ I, a i * u i y) ^ 2) :
    Integrable g ∧ (∫ y, g y) ≤ (∑ i ∈ I, a i * κ i) ^ 2 := by
  have hsq : ∀ y, (∑ i ∈ I, a i * u i y) ^ 2 = ∑ i ∈ I, ∑ l ∈ I, (a i * a l) * (u i y * u l y) := by
    intro y
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hp : ∀ i ∈ I, ∀ l ∈ I, Integrable (fun y => u i y * u l y) ∧
      (∫ y, u i y * u l y) ≤ κ i * κ l := by
    intro i hi l hl
    obtain ⟨h1, h2⟩ := pair_bound (u i) (u l) (hu i hi) (hu l hl) (hum i hi) (hum l hl) (hu2 i hi) (hu2 l hl)
    refine ⟨h1, h2.trans ?_⟩
    have s1 : Real.sqrt (∫ y, u i y ^ 2) ≤ κ i :=
      (Real.sqrt_le_sqrt (hle i hi)).trans_eq (Real.sqrt_sq (hκ i hi))
    have s2 : Real.sqrt (∫ y, u l y ^ 2) ≤ κ l :=
      (Real.sqrt_le_sqrt (hle l hl)).trans_eq (Real.sqrt_sq (hκ l hl))
    exact mul_le_mul s1 s2 (Real.sqrt_nonneg _) (hκ i hi)
  have hG : Integrable (fun y => ∑ i ∈ I, ∑ l ∈ I, (a i * a l) * (u i y * u l y)) :=
    integrable_finsetSum _ fun i hi => integrable_finsetSum _ fun l hl => (hp i hi l hl).1.const_mul _
  have hgi : Integrable g := by
    refine Integrable.mono' hG hgm (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 y), ← hsq y]
    exact hg y
  refine ⟨hgi, ?_⟩
  calc (∫ y, g y) ≤ ∫ y, ∑ i ∈ I, ∑ l ∈ I, (a i * a l) * (u i y * u l y) :=
        integral_mono hgi hG fun y => (hg y).trans_eq (hsq y)
    _ = ∑ i ∈ I, ∑ l ∈ I, (a i * a l) * ∫ y, u i y * u l y := by
        rw [integral_finsetSum _ fun i hi => integrable_finsetSum _ fun l hl => (hp i hi l hl).1.const_mul _]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [integral_finsetSum _ fun l hl => (hp i hi l hl).1.const_mul _]
        refine Finset.sum_congr rfl fun l _ => ?_
        exact integral_const_mul _ _
    _ ≤ ∑ i ∈ I, ∑ l ∈ I, (a i * a l) * (κ i * κ l) := by
        refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun l hl => ?_
        exact mul_le_mul_of_nonneg_left (hp i hi l hl).2 (mul_nonneg (ha i hi) (ha l hl))
    _ = (∑ i ∈ I, a i * κ i) ^ 2 := by
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
        ring


private theorem multiPow_abs_le {k : ℕ} (γ : Fin k → ℕ) (p r : Fin k → ℝ) (hp : ∀ i, |p i| ≤ r i) :
    |multiPow γ p| ≤ multiPow γ r := by
  unfold multiPow
  rw [Finset.abs_prod]
  refine Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => ?_
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hp i) _

private theorem multiPow_nonneg' {k : ℕ} (γ : Fin k → ℕ) (r : Fin k → ℝ) (hr : ∀ i, 0 ≤ r i) :
    0 ≤ multiPow γ r := by
  unfold multiPow
  exact Finset.prod_nonneg fun i _ => pow_nonneg (hr i) _

private theorem phase_near {k : ℕ} (A : AuxData k) (r p : Fin k → ℝ) (hp : ∀ i, |p i| ≤ r i) :
    |A.phase p - A.phase 0| ≤ splitWidth r A.phaseSlope := by
  have e : A.phase p - A.phase 0 = ∑ i, A.phaseSlope i * p i := by
    simp [AuxData.phase]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hp i) (abs_nonneg _)

private theorem hbase {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M)
    (h : CellSystemCondition c D A M MD RD X)
    (hKB : ∀ (m : ℕ) (V : Space → ℝ) (S : CellSumData), IsCellSumData m V S → ∀ Λ : ℝ,
      (∀ a, S.boxBound a ≤ Λ) → KernelBound V Λ)
    (hW : ∀ j ∈ c.activeSet, ∀ γ ∈ (A.adjointFamily j).indices, ∀ β,
      IsSumWeight c.order (fun y => ‖fieldOf D.chart ((A.adjointFamily j).coef γ) β y‖ ^ 2 / X.weightValue)) :
    ∀ j ∈ c.activeSet, ∀ p ∈ box c.radius, KernelBound (adjointWeightOf c X.weightValue j p) (X.adjointKernel j) := by
  intro j hj p hp
  have hw : 0 < X.weightValue := h.inst.weightValue_pos
  have hpr : ∀ i, |p i| ≤ c.radius i := hp
  have hβ : |A.phase p - A.phase 0| ≤ X.splitRange :=
    (phase_near A c.radius p hpr).trans h.losses.adjoint_width
  obtain ⟨F, hFdef⟩ : ∃ F : (Fin k → ℕ) → Space → Space,
      F = fun γ => fieldOf D.chart ((A.adjointFamily j).coef γ) (A.phase p) := ⟨_, rfl⟩
  have hadj : ∀ y, c.adjoint j p y = ∑ γ ∈ (A.adjointFamily j).indices, multiPow γ p • F γ y := by
    intro y
    rw [h.given.aux_instance.adjoint_eq j p, hFdef]
    rfl
  have hK : ∀ γ ∈ (A.adjointFamily j).indices,
      KernelBound (fun y => ‖F γ y‖ ^ 2 / X.weightValue) (X.adjointPartKernel j γ ^ 2) := by
    intro γ hγ
    rw [hFdef]
    exact hKB c.order _ _
      (cellSumData_of c.order _ _ (h.losses.adjoint_values j hj γ hγ)
        (h.losses.adjoint_bounded j hj γ hγ (A.phase p) hβ) (hW j hj γ hγ (A.phase p))) _
      (h.losses.adjoint_boxes j hj γ hγ)
  have hcont : ∀ γ ∈ (A.adjointFamily j).indices, Continuous (F γ) := by
    intro γ hγ
    rw [hFdef]
    exact (GivenFields.AdjointCoreInternal.field_contDiff D.chart h.given.profile.chart _ (h.given.aux.adjoint_shape j γ hγ) (A.phase p)).continuous
  have hScont : Continuous (fun y => ∑ γ ∈ (A.adjointFamily j).indices, multiPow γ p • F γ y) :=
    continuous_finsetSum (f := fun γ y => multiPow γ p • F γ y) _ fun γ hγ => (hcont γ hγ).const_smul (multiPow γ p)
  have hV : ∀ y, adjointWeightOf c X.weightValue j p y =
      ‖∑ γ ∈ (A.adjointFamily j).indices, multiPow γ p • F γ y‖ ^ 2 / X.weightValue := by
    intro y
    unfold adjointWeightOf
    rw [hadj y]
  have hVm : Measurable (adjointWeightOf c X.weightValue j p) := by
    have e : adjointWeightOf c X.weightValue j p =
        fun y => ‖∑ γ ∈ (A.adjointFamily j).indices, multiPow γ p • F γ y‖ ^ 2 / X.weightValue := funext hV
    rw [e]
    exact ((hScont.norm.pow 2).div_const _).measurable
  have hpt : ∀ y, ‖∑ γ ∈ (A.adjointFamily j).indices, multiPow γ p • F γ y‖ ≤
      ∑ γ ∈ (A.adjointFamily j).indices, multiPow γ c.radius * ‖F γ y‖ := by
    intro y
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun γ _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (multiPow_abs_le γ p c.radius hpr) (norm_nonneg _)
  refine ⟨fun y => by rw [hV y]; positivity, hVm, fun x => ?_⟩
  have hdm : Measurable (fun y : Space => 4 * Real.pi * ‖x - y‖) :=
    (continuous_const.mul (continuous_const.sub continuous_id).norm).measurable
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : Space → ℝ, ρ = fun y => Real.sqrt (1 / (X.weightValue * (4 * Real.pi * ‖x - y‖))) :=
    ⟨_, rfl⟩
  have hρ0 : ∀ y, 0 ≤ ρ y := fun y => by rw [hρdef]; exact Real.sqrt_nonneg _
  have hρm : Measurable ρ := by
    rw [hρdef]
    exact Real.continuous_sqrt.measurable.comp (measurable_const.div (measurable_const.mul hdm))
  have hρ2 : ∀ y, ρ y ^ 2 = 1 / (X.weightValue * (4 * Real.pi * ‖x - y‖)) := fun y => by
    rw [hρdef]
    exact Real.sq_sqrt (by positivity)
  have hquot : ∀ (t : ℝ) (y : Space), t / X.weightValue / (4 * Real.pi * ‖x - y‖) = t * ρ y ^ 2 := by
    intro t y
    rw [hρ2 y, mul_one_div, div_div]
  have hu2 : ∀ γ y, (‖F γ y‖ * ρ y) ^ 2 = ‖F γ y‖ ^ 2 / X.weightValue / (4 * Real.pi * ‖x - y‖) := by
    intro γ y
    rw [mul_pow, hquot]
  have key := AdjointKernelInternal.sum_bound (A.adjointFamily j).indices (fun γ => multiPow γ c.radius)
    (fun γ => X.adjointPartKernel j γ) (fun γ y => ‖F γ y‖ * ρ y)
    (fun y => adjointWeightOf c X.weightValue j p y / (4 * Real.pi * ‖x - y‖))
    (fun γ _ => multiPow_nonneg' γ c.radius h.base.radius_nonneg)
    (fun γ _ => h.losses.adjointPartKernel_nonneg j γ)
    (fun γ _ y => mul_nonneg (norm_nonneg _) (hρ0 y))
    (fun γ hγ => ((hcont γ hγ).norm.measurable.mul hρm).aestronglyMeasurable)
    (fun γ hγ => by
      have e : (fun y => (‖F γ y‖ * ρ y) ^ 2) =
          fun y => ‖F γ y‖ ^ 2 / X.weightValue / (4 * Real.pi * ‖x - y‖) := funext (hu2 γ)
      rw [e]
      exact ((hK γ hγ).2.2 x).1)
    (fun γ hγ => by
      have e : (fun y => (‖F γ y‖ * ρ y) ^ 2) =
          fun y => ‖F γ y‖ ^ 2 / X.weightValue / (4 * Real.pi * ‖x - y‖) := funext (hu2 γ)
      rw [e]
      exact ((hK γ hγ).2.2 x).2)
    ((hVm.div hdm).aestronglyMeasurable)
    (fun y => div_nonneg (by rw [hV y]; positivity) (by positivity))
    (fun y => by
      have e : adjointWeightOf c X.weightValue j p y / (4 * Real.pi * ‖x - y‖) =
          (‖∑ γ ∈ (A.adjointFamily j).indices, multiPow γ p • F γ y‖ * ρ y) ^ 2 := by
        rw [hV y, hquot, mul_pow]
      have e2 : ∑ γ ∈ (A.adjointFamily j).indices, multiPow γ c.radius * (‖F γ y‖ * ρ y) =
          (∑ γ ∈ (A.adjointFamily j).indices, multiPow γ c.radius * ‖F γ y‖) * ρ y := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun γ _ => by ring
      rw [e, e2]
      exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (hρ0 y))
        (mul_le_mul_of_nonneg_right (hpt y) (hρ0 y)) 2)
  refine ⟨key.1, key.2.trans ?_⟩
  have hs0 : 0 ≤ ∑ γ ∈ (A.adjointFamily j).indices, multiPow γ c.radius * X.adjointPartKernel j γ :=
    Finset.sum_nonneg fun γ _ => mul_nonneg (multiPow_nonneg' γ c.radius h.base.radius_nonneg)
      (h.losses.adjointPartKernel_nonneg j γ)
  calc (∑ γ ∈ (A.adjointFamily j).indices, multiPow γ c.radius * X.adjointPartKernel j γ) ^ 2
      ≤ Real.sqrt (X.adjointKernel j) ^ 2 := pow_le_pow_left₀ hs0 (h.losses.adjointKernel_ge j hj) 2
    _ = X.adjointKernel j := Real.sq_sqrt (h.losses.adjointKernel_nonneg j)

private theorem part_weight {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) (w : ℝ) (hw : 0 < w)
    (j : Fin k) (γ : Fin k → ℕ) (hγ : γ ∈ (A.adjointFamily j).indices) (β : ℝ) :
    IsSumWeight c.order (fun y => ‖fieldOf D.chart ((A.adjointFamily j).coef γ) β y‖ ^ 2 / w) := by
  have hP : IsChartParams D.chart := hS.profile.chart
  have hF := hS.aux.adjoint_shape j γ hγ
  have hord : c.order = D.chart.m := hS.centre_instance.order_eq
  obtain ⟨C, hC⟩ := GivenFields.AdjointCoreInternal.field_decay D.chart hP _ hF β
  have hcl := GivenFields.AdjointCoreInternal.field_class D.chart hP _ hF β
  have hcont : Continuous (fun y => ‖fieldOf D.chart ((A.adjointFamily j).coef γ) β y‖ ^ 2 / w) :=
    ((GivenFields.AdjointCoreInternal.field_contDiff D.chart hP _ hF β).continuous.norm.pow 2).div_const w
  rw [hord]
  refine ⟨hcont.measurable, fun y => by positivity, fun y => ?_, fun y => ?_, ?_⟩
  · have e : turnBy (2 * Real.pi / D.chart.m) y = turnStep D.chart.m y := rfl
    rw [e, (hcl y).1, FracInternal.givenNorm_turn]
  · rw [(hcl y).2, FracInternal.givenNorm_mirror]
  · have hr : (Module.finrank ℝ Space : ℝ) < 6 := by
      rw [finrank_euclideanSpace_fin]
      norm_num
    have hI : Integrable (fun y : Space => C ^ 2 / w * (1 + ‖y‖) ^ (-(6 : ℝ))) :=
      (integrable_one_add_norm hr).const_mul _
    refine hI.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    have hq : ((1 + ‖y‖) ^ (-(3 : ℝ))) ^ 2 = (1 + ‖y‖) ^ (-(6 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖fieldOf D.chart ((A.adjointFamily j).coef γ) β y‖ ^ 2 / w
        ≤ (C * (1 + ‖y‖) ^ (-(3 : ℝ))) ^ 2 / w :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC y) 2) hw.le
      _ = C ^ 2 / w * (1 + ‖y‖) ^ (-(6 : ℝ)) := by
          rw [mul_pow, hq]
          ring

end AdjointKernelInternal

theorem adjointKernel_of_weights {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M)
    (h : CellSystemCondition c D A M MD RD X)
    (hW : ∀ j ∈ c.activeSet, ∀ γ ∈ (A.adjointFamily j).indices, ∀ β,
      IsSumWeight c.order (fun y => ‖fieldOf D.chart ((A.adjointFamily j).coef γ) β y‖ ^ 2 / X.weightValue)) :
    ∀ j ∈ c.activeSet, ∀ p ∈ box c.radius, KernelBound (adjointWeightOf c X.weightValue j p) (X.adjointKernel j) :=
  AdjointKernelInternal.hbase c D A M MD RD X h (fun m V S hS Λ hΛ => kernelBound_of_cellSums m V S hS Λ hΛ) hW

theorem adjointKernel_of {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M)
    (h : CellSystemCondition c D A M MD RD X) :
    ∀ j ∈ c.activeSet, ∀ p ∈ box c.radius, KernelBound (adjointWeightOf c X.weightValue j p) (X.adjointKernel j) := by
  exact adjointKernel_of_weights c D A M MD RD X h
    (fun j _ γ hγ β => AdjointKernelInternal.part_weight c D A M MD RD h.given X.weightValue h.inst.weightValue_pos j γ hγ β)

end CellSystem

end CellCert

end Breakdown
