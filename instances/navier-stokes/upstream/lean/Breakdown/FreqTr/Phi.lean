import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.Phi

theorem fieldOp_realized_or_zero (A : Space → Space) (F : Space → CSpace →L[ℝ] CSpace) :
    IsRealizedBy (fieldOp A F) A F ∨ fieldOp A F = 0 := by
  unfold fieldOp
  split_ifs with h
  · exact Or.inl h.choose_spec
  · exact Or.inr rfl

theorem scalarOp_ae (h1 : FieldOpRealized) {m : Space → ℝ} (hm : Continuous m) {C : ℝ}
    (hC : ∀ ξ, |m ξ| ≤ C) (f : L2C) :
    (fieldOp id (fun ξ => m ξ • ContinuousLinearMap.id ℝ CSpace) f : Space → CSpace) =ᵐ[volume]
      fun ξ => m ξ • f ξ := by
  have hF : AEStronglyMeasurable (fun ξ => m ξ • ContinuousLinearMap.id ℝ CSpace) volume :=
    (hm.smul continuous_const).aestronglyMeasurable
  have hB : ∀ ξ, ‖m ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ C := by
    intro ξ
    calc ‖m ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ ‖m ξ‖ * ‖ContinuousLinearMap.id ℝ CSpace‖ :=
          norm_smul_le _ _
      _ ≤ |m ξ| * 1 := by
          rw [Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg _)
      _ ≤ C := by rw [mul_one]; exact hC ξ
  have := h1 (ContinuousLinearEquiv.refl ℝ Space) _ C hF hB f
  simpa [ContinuousLinearEquiv.coe_refl'] using this

theorem scalarOp_norm_le (h1 : FieldOpRealized) {m : Space → ℝ} (hm : Continuous m) {C : ℝ}
    (hC : ∀ ξ, |m ξ| ≤ C) (f : L2C) :
    ‖fieldOp id (fun ξ => m ξ • ContinuousLinearMap.id ℝ CSpace) f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [scalarOp_ae h1 hm hC f] with ξ hξ
  rw [hξ, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _)

theorem scalarOp_mem (h1 : FieldOpRealized) {m : Space → ℝ} (hm : Continuous m) {C : ℝ}
    (hC : ∀ ξ, |m ξ| ≤ C) (hneg : ∀ ξ, m (-ξ) = m ξ) {x : L2C} (hx : x ∈ Sig) :
    fieldOp id (fun ξ => m ξ • ContinuousLinearMap.id ℝ CSpace) x ∈ Sig := by
  set y := fieldOp id (fun ξ => m ξ • ContinuousLinearMap.id ℝ CSpace) x with hy
  have hyae := scalarOp_ae h1 hm hC x
  simp only [Sig, Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero] at hx ⊢
  obtain ⟨hx1, hx2⟩ := hx
  constructor
  · rcases fieldOp_realized_or_zero (fun ξ => -ξ) (fun _ => conjVec) with hR | hR
    · have hrefl : reflConj = fieldOp (fun ξ => -ξ) (fun _ => conjVec) := rfl
      rw [hrefl] at hx1 ⊢
      have hneg' : Filter.Tendsto (fun ξ : Space => -ξ) (ae volume) (ae volume) :=
        (Measure.measurePreserving_neg volume).quasiMeasurePreserving.tendsto_ae
      have hyneg := hyae.comp_tendsto hneg'
      have hxa := hR x
      rw [hx1] at hxa
      apply Lp.ext
      filter_upwards [hR y, hyneg, hyae, hxa] with ξ e1 e2 e3 e4
      rw [e1, e3]
      simp only [Function.comp] at e2
      rw [e2, hneg, e4, map_smul]
    · have h0 : reflConj = 0 := hR
      rw [h0] at hx1 ⊢
      have hx0 : x = 0 := by simpa using hx1.symm
      rw [hy, hx0, map_zero]
      simp
  · rcases fieldOp_realized_or_zero id longitudinal with hR | hR
    · apply Lp.ext
      have hxa := hR x
      rw [hx2] at hxa
      filter_upwards [hR y, hyae, hxa, Lp.coeFn_zero CSpace 2 (volume : Measure Space)] with ξ e1 e2 e3 e4
      rw [e1, e4]
      simp only [id] at e3 ⊢
      rw [e2, map_smul]
      rw [← e3]
      simp
    · rw [hR]
      simp

theorem mul_exp_neg_le_one (y : ℝ) : y * Real.exp (-y) ≤ 1 := by
  have h := Real.add_one_le_exp y
  calc y * Real.exp (-y) ≤ Real.exp y * Real.exp (-y) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

theorem sspHeat_eq {τ : ℝ} (hτ : 0 < τ) (ξ : Space) :
    sspFactor ξ * heatFactor τ ξ =
      τ⁻¹ * ((4 * π ^ 2 * τ * ‖ξ‖ ^ 2) * Real.exp (-(4 * π ^ 2 * τ * ‖ξ‖ ^ 2))) := by
  unfold sspFactor heatFactor
  rw [max_eq_left hτ.le]
  field_simp

theorem sspHeat_nonneg (τ : ℝ) (ξ : Space) : 0 ≤ sspFactor ξ * heatFactor τ ξ := by
  unfold sspFactor heatFactor
  positivity

theorem sspHeat_le {τ : ℝ} (hτ : 0 < τ) (ξ : Space) : |sspFactor ξ * heatFactor τ ξ| ≤ τ⁻¹ := by
  rw [abs_of_nonneg (sspHeat_nonneg τ ξ), sspHeat_eq hτ]
  have : (4 * π ^ 2 * τ * ‖ξ‖ ^ 2) * Real.exp (-(4 * π ^ 2 * τ * ‖ξ‖ ^ 2)) ≤ 1 :=
    mul_exp_neg_le_one _
  calc τ⁻¹ * ((4 * π ^ 2 * τ * ‖ξ‖ ^ 2) * Real.exp (-(4 * π ^ 2 * τ * ‖ξ‖ ^ 2))) ≤ τ⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hτ.le)
    _ = τ⁻¹ := mul_one _

theorem phiFactor_nonneg {τ : ℝ} (ξ : Space) : 0 ≤ phiFactor τ ξ := by
  unfold phiFactor
  positivity

theorem phiFactor_sq_le {τ : ℝ} (hτ : 0 < τ) (ξ : Space) : phiFactor τ ξ ^ 2 ≤ τ⁻¹ := by
  have e : phiFactor τ ξ ^ 2 =
      (sspFactor ξ * heatFactor τ ξ) * Real.exp (-(4 * π ^ 2 * τ * ‖ξ‖ ^ 2)) := by
    unfold phiFactor sspFactor heatFactor
    rw [max_eq_left hτ.le]
    ring
  have hle : Real.exp (-(4 * π ^ 2 * τ * ‖ξ‖ ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      have : 0 ≤ 4 * π ^ 2 * τ * ‖ξ‖ ^ 2 := by positivity
      linarith)
  rw [e]
  calc (sspFactor ξ * heatFactor τ ξ) * Real.exp (-(4 * π ^ 2 * τ * ‖ξ‖ ^ 2))
      ≤ (sspFactor ξ * heatFactor τ ξ) * 1 := mul_le_mul_of_nonneg_left hle (sspHeat_nonneg τ ξ)
    _ ≤ τ⁻¹ := by rw [mul_one]; exact le_of_abs_le (sspHeat_le hτ ξ)

theorem phiFactor_le {τ : ℝ} (hτ : 0 < τ) (ξ : Space) : |phiFactor τ ξ| ≤ τ ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg hτ.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_inv, abs_of_nonneg (phiFactor_nonneg ξ),
    ← Real.sqrt_sq (phiFactor_nonneg (τ := τ) ξ)]
  exact Real.sqrt_le_sqrt (phiFactor_sq_le hτ ξ)

theorem heatFactor_le (τ : ℝ) (ξ : Space) : |heatFactor τ ξ| ≤ 1 := by
  unfold heatFactor
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  have : 0 ≤ 4 * π ^ 2 * max τ 0 * ‖ξ‖ ^ 2 := by positivity
  linarith

theorem continuous_phiFactor (τ : ℝ) : Continuous (phiFactor τ) := by
  unfold phiFactor
  fun_prop

theorem continuous_heatFactor (τ : ℝ) : Continuous (heatFactor τ) := by
  unfold heatFactor
  fun_prop

theorem continuous_sspHeat (τ : ℝ) : Continuous (fun ξ => sspFactor ξ * heatFactor τ ξ) := by
  unfold sspFactor heatFactor
  fun_prop

end Internal.Phi

open Internal.Phi in
theorem phiBoundsVelocity (h1 : FieldOpRealized) (h2 : HeatSemigroup) (h3 : VelocityInvertsHalfSsp) :
    PhiBounds ∧ PhiVelocity := by
  have hheat : ∀ τ (ψ : X), ((heatX τ ψ : X) : L2C) =ᵐ[volume]
      fun ξ => heatFactor τ ξ • (ψ : L2C) ξ := by
    intro τ ψ
    rw [h2.2.2.2.2.2 τ ψ]
    exact scalarOp_ae h1 (continuous_heatFactor τ) (heatFactor_le τ) (ψ : L2C)
  have hvel : PhiVelocity := by
    intro τ hτ ψ h hssp
    have hgmem := scalarOp_mem h1 (continuous_phiFactor τ) (phiFactor_le hτ)
      (fun ξ => by simp [phiFactor]) ψ.2
    have hg : IsHalfSspOf ⟨_, hgmem⟩ h := by
      unfold IsHalfSspOf
      filter_upwards [hssp, hheat τ ψ,
        scalarOp_ae h1 (continuous_phiFactor τ) (phiFactor_le hτ) (ψ : L2C)] with ξ e1 e2 e3
      rw [e1, e2, e3, smul_smul, smul_smul]
      congr 1
      unfold sspFactor heatFactor phiFactor
      rw [max_eq_left hτ.le]
      ring
    exact (h3 _ h hg).symm
  refine ⟨⟨‖toPhys‖ + ‖velocity‖ + 1, fun τ hτ ψ => ?_⟩, hvel⟩
  have hmem := scalarOp_mem h1 (continuous_sspHeat τ) (sspHeat_le hτ)
    (fun ξ => by simp [sspFactor, heatFactor]) ψ.2
  have hssp : IsSspOf (heatX τ ψ) ⟨_, hmem⟩ := by
    unfold IsSspOf
    filter_upwards [hheat τ ψ,
      scalarOp_ae h1 (continuous_sspHeat τ) (sspHeat_le hτ) (ψ : L2C)] with ξ e1 e2
    rw [e2, e1, smul_smul]
  have hae := hvel τ hτ ψ _ hssp
  have hXn := scalarOp_norm_le h1 (continuous_sspHeat τ) (sspHeat_le hτ) (ψ : L2C)
  have hPn := scalarOp_norm_le h1 (continuous_phiFactor τ) (phiFactor_le hτ) (ψ : L2C)
  have hψ : 0 ≤ ‖ψ‖ := norm_nonneg _
  have hk : 0 ≤ τ ^ (-(1 / 2 : ℝ)) := by positivity
  have hT : 0 ≤ ‖toPhys‖ := norm_nonneg _
  have hV : 0 ≤ ‖velocity‖ := norm_nonneg _
  refine ⟨(Lp.memLp _).ae_eq hae.symm, ?_, ?_⟩
  · rw [← Lp.norm_def]
    have e : phiX τ ψ = toPhys (fieldOp id (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace)
      (ψ : L2C)) := rfl
    rw [e]
    calc ‖toPhys (fieldOp id (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) (ψ : L2C))‖
        ≤ ‖toPhys‖ * ‖fieldOp id (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace)
          (ψ : L2C)‖ := toPhys.le_opNorm _
      _ ≤ ‖toPhys‖ * (τ ^ (-(1 / 2 : ℝ)) * ‖ψ‖) := mul_le_mul_of_nonneg_left hPn hT
      _ ≤ (‖toPhys‖ + ‖velocity‖ + 1) * τ ^ (-(1 / 2 : ℝ)) * ‖ψ‖ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hk hψ)
  · rw [eLpNorm_congr_ae hae, ← Lp.norm_def, Real.rpow_neg_one]
    have hi : 0 ≤ τ⁻¹ := inv_nonneg.mpr hτ.le
    calc ‖velocity ⟨_, hmem⟩‖ ≤ ‖velocity‖ * ‖(⟨_, hmem⟩ : X)‖ := velocity.le_opNorm _
      _ ≤ ‖velocity‖ * (τ⁻¹ * ‖ψ‖) := mul_le_mul_of_nonneg_left hXn hV
      _ ≤ (‖toPhys‖ + ‖velocity‖ + 1) * τ⁻¹ * ‖ψ‖ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hi hψ)

end Breakdown.Freq
