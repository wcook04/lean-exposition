import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.FieldOp

theorem det_ne_zero (E : Space ≃L[ℝ] Space) : LinearMap.det (E : Space →ₗ[ℝ] Space) ≠ 0 :=
  (LinearEquiv.isUnit_det' E.toLinearEquiv).ne_zero

def detFactor (E : Space ≃L[ℝ] Space) : ℝ≥0∞ := ENNReal.ofReal |(LinearMap.det (E : Space →ₗ[ℝ] Space))⁻¹|

theorem detFactor_ne_top (E : Space ≃L[ℝ] Space) : detFactor E ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top

theorem map_eq (E : Space ≃L[ℝ] Space) : Measure.map E volume = detFactor E • volume :=
  Measure.map_linearMap_addHaar_eq_smul_addHaar volume (det_ne_zero E)

theorem qmp (E : Space ≃L[ℝ] Space) : Measure.QuasiMeasurePreserving E volume volume :=
  Measure.LinearMap.quasiMeasurePreserving volume (E : Space →ₗ[ℝ] Space) (det_ne_zero E)

theorem eLpNorm_comp (E : Space ≃L[ℝ] Space) {f : Space → CSpace} (hf : AEStronglyMeasurable f volume) :
    eLpNorm (f ∘ E) 2 volume = detFactor E ^ (1 / (2 : ℝ≥0∞)).toReal • eLpNorm f 2 volume := by
  rw [← eLpNorm_map_measure (by rw [map_eq]; exact hf.smul_measure _) (qmp E).aemeasurable, map_eq,
    eLpNorm_smul_measure_of_ne_top (by norm_num)]

theorem memLp_comp (E : Space ≃L[ℝ] Space) {f : Space → CSpace} (hf : MemLp f 2 volume) :
    MemLp (f ∘ E) 2 volume := by
  have h : MemLp f 2 (Measure.map E volume) := by rw [map_eq]; exact hf.smul_measure (detFactor_ne_top E)
  exact h.comp_of_map (qmp E).aemeasurable

def applyFun (E : Space ≃L[ℝ] Space) (F : Space → CSpace →L[ℝ] CSpace) (f : L2C) : Space → CSpace :=
  fun ξ => F ξ (f (E ξ))

theorem aesm_apply (E : Space ≃L[ℝ] Space) {F : Space → CSpace →L[ℝ] CSpace}
    (hF : AEStronglyMeasurable F volume) (f : L2C) : AEStronglyMeasurable (applyFun E F f) volume := by
  have hg : AEStronglyMeasurable (fun ξ => (f : Space → CSpace) (E ξ)) volume :=
    (Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving (qmp E)
  exact (isBoundedBilinearMap_apply.continuous).comp_aestronglyMeasurable₂ hF hg

theorem norm_apply_le (E : Space ≃L[ℝ] Space) {F : Space → CSpace →L[ℝ] CSpace} {C : ℝ}
    (hC : ∀ ξ, ‖F ξ‖ ≤ C) (f : L2C) (ξ : Space) :
    ‖applyFun E F f ξ‖ ≤ C * ‖((f : Space → CSpace) ∘ E) ξ‖ :=
  (F ξ).le_of_opNorm_le (hC ξ) _

theorem memLp_apply (E : Space ≃L[ℝ] Space) {F : Space → CSpace →L[ℝ] CSpace} {C : ℝ}
    (hF : AEStronglyMeasurable F volume) (hC : ∀ ξ, ‖F ξ‖ ≤ C) (f : L2C) :
    MemLp (applyFun E F f) 2 volume :=
  (memLp_comp E (Lp.memLp f)).of_le_mul (aesm_apply E hF f) (Filter.Eventually.of_forall (norm_apply_le E hC f))


theorem comp_ae (E : Space ≃L[ℝ] Space) {f g : Space → CSpace} (h : f =ᵐ[volume] g) :
    (fun ξ => f (E ξ)) =ᵐ[volume] fun ξ => g (E ξ) :=
  (qmp E).ae_eq_comp h

def opLin (E : Space ≃L[ℝ] Space) {F : Space → CSpace →L[ℝ] CSpace} {C : ℝ}
    (hF : AEStronglyMeasurable F volume) (hC : ∀ ξ, ‖F ξ‖ ≤ C) : L2C →ₗ[ℝ] L2C where
  toFun f := (memLp_apply E hF hC f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards [comp_ae E (Lp.coeFn_add f g)] with ξ hξ
    simp only [applyFun, Pi.add_apply] at hξ ⊢
    rw [hξ, map_add]
  map_smul' c f := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    filter_upwards [comp_ae E (Lp.coeFn_smul c f)] with ξ hξ
    simp only [applyFun, Pi.smul_apply, RingHom.id_apply] at hξ ⊢
    rw [hξ, map_smul]

theorem norm_opLin_le (E : Space ≃L[ℝ] Space) {F : Space → CSpace →L[ℝ] CSpace} {C : ℝ}
    (hF : AEStronglyMeasurable F volume) (hC : ∀ ξ, ‖F ξ‖ ≤ C) (f : L2C) :
    ‖opLin E hF hC f‖ ≤ (C * (detFactor E ^ (1 / (2 : ℝ≥0∞)).toReal).toReal) * ‖f‖ := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  change ‖(memLp_apply E hF hC f).toLp _‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def]
  have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := volume) (Filter.Eventually.of_forall (norm_apply_le E hC f)) 2
  rw [eLpNorm_comp E (Lp.aestronglyMeasurable f)] at h1
  have hfin : eLpNorm (f : Space → CSpace) 2 volume ≠ ⊤ := Lp.eLpNorm_ne_top f
  have hjfin : detFactor E ^ (1 / (2 : ℝ≥0∞)).toReal ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) (detFactor_ne_top E)
  calc (eLpNorm (applyFun E F f) 2 volume).toReal
      ≤ (ENNReal.ofReal C * (detFactor E ^ (1 / (2 : ℝ≥0∞)).toReal • eLpNorm (f : Space → CSpace) 2 volume)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hjfin hfin)) h1
    _ = _ := by
        simp only [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0]
        ring

def op (E : Space ≃L[ℝ] Space) {F : Space → CSpace →L[ℝ] CSpace} {C : ℝ}
    (hF : AEStronglyMeasurable F volume) (hC : ∀ ξ, ‖F ξ‖ ≤ C) : L2C →L[ℝ] L2C :=
  (opLin E hF hC).mkContinuous _ (norm_opLin_le E hF hC)

theorem op_spec (E : Space ≃L[ℝ] Space) {F : Space → CSpace →L[ℝ] CSpace} {C : ℝ}
    (hF : AEStronglyMeasurable F volume) (hC : ∀ ξ, ‖F ξ‖ ≤ C) : IsRealizedBy (op E hF hC) E F :=
  fun f => (memLp_apply E hF hC f).coeFn_toLp

end Internal.FieldOp

theorem fieldOpRealized : FieldOpRealized := by
  intro E F C hF hC
  have h : ∃ T, IsRealizedBy T E F := ⟨Internal.FieldOp.op E hF hC, Internal.FieldOp.op_spec E hF hC⟩
  rw [fieldOp, dif_pos h]
  exact h.choose_spec

theorem isRealizedBy_unique {S T : L2C →L[ℝ] L2C} {A : Space → Space} {F : Space → CSpace →L[ℝ] CSpace}
    (hS : IsRealizedBy S A F) (hT : IsRealizedBy T A F) : S = T := by
  ext1 f
  exact Lp.ext ((hS f).trans (hT f).symm)

theorem fieldOp_eq_of_isRealizedBy {T : L2C →L[ℝ] L2C} {A : Space → Space}
    {F : Space → CSpace →L[ℝ] CSpace} (hT : IsRealizedBy T A F) : fieldOp A F = T := by
  have h : ∃ T, IsRealizedBy T A F := ⟨T, hT⟩
  rw [fieldOp, dif_pos h]
  exact isRealizedBy_unique h.choose_spec hT

theorem isRealizedBy_fieldOp (E : Space ≃L[ℝ] Space) {A : Space → Space} (hA : ⇑E = A)
    {F : Space → CSpace →L[ℝ] CSpace} {C : ℝ} (hF : AEStronglyMeasurable F volume)
    (hC : ∀ ξ, ‖F ξ‖ ≤ C) : IsRealizedBy (fieldOp A F) A F := by
  subst hA
  exact fieldOpRealized E F C hF hC

theorem fieldOp_ae (E : Space ≃L[ℝ] Space) {A : Space → Space} (hA : ⇑E = A)
    {F : Space → CSpace →L[ℝ] CSpace} {C : ℝ} (hF : AEStronglyMeasurable F volume)
    (hC : ∀ ξ, ‖F ξ‖ ≤ C) (f : L2C) :
    (fieldOp A F f : Space → CSpace) =ᵐ[volume] fun ξ => F ξ (f (A ξ)) :=
  isRealizedBy_fieldOp E hA hF hC f

theorem isRealizedBy_fieldOp_id {F : Space → CSpace →L[ℝ] CSpace} {C : ℝ}
    (hF : AEStronglyMeasurable F volume) (hC : ∀ ξ, ‖F ξ‖ ≤ C) : IsRealizedBy (fieldOp id F) id F :=
  isRealizedBy_fieldOp (ContinuousLinearEquiv.refl ℝ Space) rfl hF hC

namespace Internal.FieldOp

theorem detFactor_rpow_toReal (E : Space ≃L[ℝ] Space) :
    (detFactor E ^ (1 / (2 : ℝ≥0∞)).toReal).toReal = Real.sqrt |(LinearMap.det (E : Space →ₗ[ℝ] Space))⁻¹| := by
  rw [detFactor, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (abs_nonneg _), Real.sqrt_eq_rpow]
  norm_num

end Internal.FieldOp

theorem norm_fieldOp_apply_le (E : Space ≃L[ℝ] Space) {A : Space → Space} (hA : ⇑E = A)
    {F : Space → CSpace →L[ℝ] CSpace} {C : ℝ} (hF : AEStronglyMeasurable F volume)
    (hC : ∀ ξ, ‖F ξ‖ ≤ C) (f : L2C) :
    ‖fieldOp A F f‖ ≤ C * Real.sqrt |(LinearMap.det (E : Space →ₗ[ℝ] Space))⁻¹| * ‖f‖ := by
  subst hA
  rw [fieldOp_eq_of_isRealizedBy (Internal.FieldOp.op_spec E hF hC), ← Internal.FieldOp.detFactor_rpow_toReal]
  exact Internal.FieldOp.norm_opLin_le E hF hC f

theorem norm_fieldOp_le (E : Space ≃L[ℝ] Space) {A : Space → Space} (hA : ⇑E = A)
    {F : Space → CSpace →L[ℝ] CSpace} {C : ℝ} (hF : AEStronglyMeasurable F volume)
    (hC : ∀ ξ, ‖F ξ‖ ≤ C) :
    ‖fieldOp A F‖ ≤ C * Real.sqrt |(LinearMap.det (E : Space →ₗ[ℝ] Space))⁻¹| :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg ((norm_nonneg _).trans (hC 0)) (Real.sqrt_nonneg _))
    (norm_fieldOp_apply_le E hA hF hC)

theorem norm_fieldOp_id_apply_le {F : Space → CSpace →L[ℝ] CSpace} {C : ℝ}
    (hF : AEStronglyMeasurable F volume) (hC : ∀ ξ, ‖F ξ‖ ≤ C) (f : L2C) :
    ‖fieldOp id F f‖ ≤ C * ‖f‖ := by
  have h := norm_fieldOp_apply_le (ContinuousLinearEquiv.refl ℝ Space) rfl hF hC f
  have hd : LinearMap.det ((ContinuousLinearEquiv.refl ℝ Space : Space ≃L[ℝ] Space) : Space →ₗ[ℝ] Space) = 1 :=
    LinearMap.det_id
  rw [hd, inv_one, abs_one, Real.sqrt_one, mul_one] at h
  exact h

theorem norm_fieldOp_id_le {F : Space → CSpace →L[ℝ] CSpace} {C : ℝ}
    (hF : AEStronglyMeasurable F volume) (hC : ∀ ξ, ‖F ξ‖ ≤ C) : ‖fieldOp id F‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans (hC 0))
    (norm_fieldOp_id_apply_le hF hC)

theorem isRealizedBy_comp {S T : L2C →L[ℝ] L2C} {A B : Space → Space}
    {F G : Space → CSpace →L[ℝ] CSpace} (hS : IsRealizedBy S A F) (hT : IsRealizedBy T B G)
    (hA : Measure.QuasiMeasurePreserving A volume volume) :
    IsRealizedBy (S ∘L T) (B ∘ A) (fun ξ => (F ξ).comp (G (A ξ))) := by
  intro f
  have h2 : (fun ξ => (T f : Space → CSpace) (A ξ)) =ᵐ[volume] fun ξ => G (A ξ) (f (B (A ξ))) :=
    hA.ae_eq_comp (hT f)
  filter_upwards [hS (T f), h2] with ξ h1 h2'
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at h1 ⊢
  rw [h1, h2']

theorem quasiMeasurePreserving_continuousLinearEquiv (E : Space ≃L[ℝ] Space) :
    Measure.QuasiMeasurePreserving E volume volume :=
  Internal.FieldOp.qmp E

theorem fieldOp_comp (E E' : Space ≃L[ℝ] Space) {A B : Space → Space} (hA : ⇑E = A) (hB : ⇑E' = B)
    {F G : Space → CSpace →L[ℝ] CSpace} {C C' : ℝ} (hF : AEStronglyMeasurable F volume)
    (hC : ∀ ξ, ‖F ξ‖ ≤ C) (hG : AEStronglyMeasurable G volume) (hC' : ∀ ξ, ‖G ξ‖ ≤ C') :
    fieldOp A F ∘L fieldOp B G = fieldOp (B ∘ A) (fun ξ => (F ξ).comp (G (A ξ))) :=
  (fieldOp_eq_of_isRealizedBy (isRealizedBy_comp (isRealizedBy_fieldOp E hA hF hC)
    (isRealizedBy_fieldOp E' hB hG hC') (hA ▸ Internal.FieldOp.qmp E))).symm

theorem restrictX_coe {T : L2C →L[ℝ] L2C} (hT : ∀ x ∈ Sig, T x ∈ Sig) (x : X) :
    (restrictX T x : L2C) = T x := by
  rw [restrictX, dif_pos hT]
  rfl

end Breakdown.Freq
