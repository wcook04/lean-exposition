import Breakdown.CertCell.BridgeStatements
import Breakdown.Cert.CoerciveModeRotation
import Breakdown.Cert.CoerciveModeL2
import Breakdown.Cert.ProductBound

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.ModeFlip

open Coercive.RotationInternal (axialRot_apply_zero axialRot_apply_one axialRot_apply_two space_ext
  axialRot_map_smul)
open Coercive.Internal.ModeRotation (expFactor modeAverage_eq expFactor_add_period)
open Cert.Internal.ProductBound (weakGradient_unique)
open Cert.Internal.ReadingExists (isWeakGradient_congr)

theorem frameSign_mul_self (a : Fin 3) : frameSign a * frameSign a = 1 := by
  unfold frameSign
  split_ifs <;> norm_num

theorem flipPoint_apply (y : Space) (i : Fin 3) : flipPoint y i = frameSign i * y i := by
  fin_cases i <;> simp [flipPoint, frameSign, unitVector]

theorem flipPoint_flipPoint (y : Space) : flipPoint (flipPoint y) = y := by
  ext i
  rw [flipPoint_apply, flipPoint_apply, ← mul_assoc, frameSign_mul_self, one_mul]

theorem flipPoint_unitVector (j : Fin 3) : flipPoint (unitVector j) = frameSign j • unitVector j := by
  ext i
  rw [flipPoint_apply, PiLp.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [frameSign, unitVector]

theorem flipPoint_smul (c : ℝ) (y : Space) : flipPoint (c • y) = c • flipPoint y := by
  ext i
  simp only [flipPoint_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem axialRot_flipPoint (φ : ℝ) (y : Space) :
    axialRot φ (flipPoint y) = flipPoint (axialRot (-φ) y) := by
  apply space_ext
  · simp only [axialRot_apply_zero, flipPoint_apply, Real.cos_neg, Real.sin_neg]
    simp [frameSign]
  · simp only [axialRot_apply_one, flipPoint_apply, Real.cos_neg, Real.sin_neg]
    simp [frameSign]
    ring
  · simp only [axialRot_apply_two, flipPoint_apply]

theorem axialRot_neg_unit (φ : ℝ) (j : Fin 3) :
    axialRot (-φ) (unitVector j) = frameSign j • flipPoint (axialRot φ (unitVector j)) := by
  have h := axialRot_flipPoint (-φ) (unitVector j)
  rw [neg_neg, flipPoint_unitVector, axialRot_map_smul] at h
  rw [← h, smul_smul, frameSign_mul_self, one_smul]

theorem axialRot_add_two_pi (φ : ℝ) (y : Space) : axialRot (φ + 2 * Real.pi) y = axialRot φ y := by
  simp only [axialRot, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem axialRot_neg_add_two_pi (φ : ℝ) (y : Space) :
    axialRot (-(φ + 2 * Real.pi)) y = axialRot (-φ) y := by
  rw [show -(φ + 2 * Real.pi) = -φ - 2 * Real.pi by ring]
  simp only [axialRot, Real.cos_sub_two_pi, Real.sin_sub_two_pi]

theorem expFactor_flip (ξ : ℤ × ℤ) (τ φ : ℝ) : expFactor (flipLabel ξ) τ (-φ) = expFactor ξ τ φ := by
  unfold expFactor flipLabel
  congr 1
  push_cast
  ring

theorem integral_neg_of_periodic (q : ℝ → ℂ) (hq : Function.Periodic q (2 * Real.pi)) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), q (-φ) = ∫ φ in (0 : ℝ)..(2 * Real.pi), q φ := by
  rw [intervalIntegral.integral_comp_neg, neg_zero]
  have h := hq.intervalIntegral_add_eq (-(2 * Real.pi)) 0
  rwa [neg_add_cancel, zero_add] at h

theorem clm_apply_eq_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : Space →L[ℝ] E)
    (u : Space) : L u = ∑ j : Fin 3, u j • L (unitVector j) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr u]
  simp [map_sum, map_smul, EuclideanSpace.basisFun_apply, unitVector]

theorem locallyIntegrable_comp_isometry {E : Type*} [NormedAddCommGroup E] (F : Space ≃ₗᵢ[ℝ] Space)
    {f : Space → E} (hf : LocallyIntegrable f volume) : LocallyIntegrable (fun y => f (F y)) volume := by
  refine locallyIntegrable_iff.2 fun K hK => ?_
  have h1 : IntegrableOn f (F '' K) volume := hf.integrableOn_isCompact (hK.image F.continuous)
  have h2 := (F.measurePreserving.integrableOn_comp_preimage F.toHomeomorph.measurableEmbedding).2 h1
  exact h2.mono_set (Set.subset_preimage_image F K)

theorem integral_comp_isometry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Space ≃ₗᵢ[ℝ] Space) (h : Space → E) : ∫ y, h (F y) = ∫ y, h y :=
  F.measurePreserving.integral_comp F.toHomeomorph.measurableEmbedding h


theorem integral_isometry_comm (F : Space ≃ₗᵢ[ℝ] Space) {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (h : X → Space) : ∫ x, F (h x) ∂μ = F (∫ x, h x ∂μ) :=
  F.toLinearIsometry.integral_comp_comm h

theorem weakGradient_flip (F : Space ≃ₗᵢ[ℝ] Space) (hF : ∀ y, F y = flipPoint y) {f : Space → Space}
    {g : Space → (Space →L[ℝ] Space)} (hfg : IsWeakGradient f g) (c : ℝ) (hc : c * c = 1) :
    IsWeakGradient (fun y => c • F (f (F y)))
      (fun y => c • ((F.toContinuousLinearEquiv : Space →L[ℝ] Space).comp
        ((g (F y)).comp (F.toContinuousLinearEquiv : Space →L[ℝ] Space)))) := by
  have hLx : ∀ x, (F.toContinuousLinearEquiv : Space →L[ℝ] Space) x = F x := fun x => rfl
  have hFF : ∀ x, F (F x) = x := fun x => by rw [hF, hF, flipPoint_flipPoint]
  have hFe : ∀ j, F (unitVector j) = frameSign j • unitVector j := fun j => by
    rw [hF, flipPoint_unitVector]
  have hc1 : ‖c‖ = 1 := by
    have h : |c| * |c| = 1 := by rw [← abs_mul, hc, abs_one]
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg c]
  refine ⟨?_, ?_, fun φ hφ i => ?_⟩
  · refine (locallyIntegrable_comp_isometry F hfg.1).mono ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact (F.continuous.const_smul c).comp_aestronglyMeasurable
        (hfg.1.aestronglyMeasurable.comp_measurePreserving F.measurePreserving)
    · rw [norm_smul, hc1, one_mul, LinearIsometryEquiv.norm_map]
  · refine (locallyIntegrable_comp_isometry F hfg.2.1).mono ?_ (Filter.Eventually.of_forall fun y => ?_)
    · have hcont : Continuous (fun A : Space →L[ℝ] Space =>
          c • ((F.toContinuousLinearEquiv : Space →L[ℝ] Space).comp
            (A.comp (F.toContinuousLinearEquiv : Space →L[ℝ] Space)))) :=
        (continuous_const.clm_comp (continuous_id.clm_comp continuous_const)).const_smul c
      exact hcont.comp_aestronglyMeasurable
        (hfg.2.1.aestronglyMeasurable.comp_measurePreserving F.measurePreserving)
    · rw [norm_smul, hc1, one_mul]
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hLx, hLx,
        LinearIsometryEquiv.norm_map]
      calc ‖g (F y) (F x)‖ ≤ ‖g (F y)‖ * ‖F x‖ := (g (F y)).le_opNorm _
        _ = ‖g (F y)‖ * ‖x‖ := by rw [LinearIsometryEquiv.norm_map]
  · have hψ : IsTestFunction (fun x => φ (F x)) :=
      ⟨hφ.1.comp (F.toContinuousLinearEquiv : Space →L[ℝ] Space).contDiff,
        hφ.2.comp_homeomorph F.toHomeomorph⟩
    have hw := hfg.2.2 _ hψ i
    have hd : ∀ x, fderiv ℝ (fun x => φ (F x)) x (unitVector i)
        = frameSign i * fderiv ℝ φ (F x) (unitVector i) := by
      intro x
      have e := F.toContinuousLinearEquiv.comp_right_fderiv (f := φ) (x := x)
      change fderiv ℝ (φ ∘ F.toContinuousLinearEquiv) x (unitVector i) = _
      rw [e, ContinuousLinearMap.comp_apply]
      show fderiv ℝ φ (F x) (F (unitVector i)) = _
      rw [hFe, map_smul, smul_eq_mul]
    have e2 : ∫ y, φ y • g (F y) (unitVector i) = ∫ x, φ (F x) • g x (unitVector i) := by
      have h := integral_comp_isometry F (fun x => φ (F x) • g x (unitVector i))
      simp only [hFF] at h
      exact h
    have e3 : ∫ y, fderiv ℝ φ y (unitVector i) • f (F y) = ∫ x, fderiv ℝ φ (F x) (unitVector i) • f x := by
      have h := integral_comp_isometry F (fun x => fderiv ℝ φ (F x) (unitVector i) • f x)
      simp only [hFF] at h
      exact h
    simp only [hd] at hw
    beta_reduce
    calc ∫ y, φ y • (c • ((F.toContinuousLinearEquiv : Space →L[ℝ] Space).comp
            ((g (F y)).comp (F.toContinuousLinearEquiv : Space →L[ℝ] Space)))) (unitVector i)
        = ∫ y, (c * frameSign i) • F (φ y • g (F y) (unitVector i)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply, hLx, hFe, map_smul]
          module
      _ = (c * frameSign i) • F (∫ x, φ (F x) • g x (unitVector i)) := by
          rw [integral_smul, integral_isometry_comm F, e2]
      _ = (c * frameSign i) • F (-∫ x, frameSign i • (fderiv ℝ φ (F x) (unitVector i) • f x)) := by
          rw [hw]
          simp only [mul_smul]
      _ = -(c • F (∫ x, fderiv ℝ φ (F x) (unitVector i) • f x)) := by
          rw [integral_smul, map_neg, map_smul, smul_neg, smul_smul, mul_assoc, frameSign_mul_self,
            mul_one]
      _ = -∫ y, fderiv ℝ φ y (unitVector i) • (c • F (f (F y))) := by
          congr 1
          rw [← e3, ← integral_isometry_comm F, ← integral_smul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only [map_smul]
          module

theorem ae_flip_gradient (F : Space ≃ₗᵢ[ℝ] Space) (hF : ∀ y, F y = flipPoint y) {f : Space → Space}
    {g : Space → (Space →L[ℝ] Space)} (hfg : IsWeakGradient f g) (c : ℝ) (hc : c * c = 1)
    (hf : ∀ᵐ y, f (flipPoint y) = c • flipPoint (f y)) :
    ∀ᵐ y, ∀ j, g (flipPoint y) (unitVector j) = (c * frameSign j) • flipPoint (g y (unitVector j)) := by
  have hLx : ∀ x, (F.toContinuousLinearEquiv : Space →L[ℝ] Space) x = F x := fun x => rfl
  have hFF : ∀ x, F (F x) = x := fun x => by rw [hF, hF, flipPoint_flipPoint]
  have hFe : ∀ j, F (unitVector j) = frameSign j • unitVector j := fun j => by
    rw [hF, flipPoint_unitVector]
  have hQ := F.measurePreserving.quasiMeasurePreserving
  have hf' : (fun y => c • F (f (F y))) =ᵐ[volume] f := by
    filter_upwards [hQ.ae hf] with y hy
    simp only [hF, flipPoint_flipPoint] at hy ⊢
    exact hy.symm
  have hw2 := isWeakGradient_congr (weakGradient_flip F hF hfg c hc) hf' Filter.EventuallyEq.rfl
  have hu := weakGradient_unique hfg hw2
  filter_upwards [hQ.ae hu] with y hy j
  rw [← hF y, hy]
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply, hLx, hFe, map_smul, hF, flipPoint_flipPoint]
  rw [flipPoint_smul, smul_smul]

theorem ae_joint_flip (F : Space ≃ₗᵢ[ℝ] Space) (hF : ∀ y, F y = flipPoint y) (Y : ℝ → Space → Space)
    (hY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume) (c : ℝ)
    (h : ∀ᵐ s, ∀ᵐ x, Y s (flipPoint x) = c • flipPoint (Y s x)) :
    ∀ᵐ z : ℝ × Space, Y z.1 (flipPoint z.2) = c • flipPoint (Y z.1 z.2) := by
  obtain ⟨Y', hYm, hYe⟩ := hY
  have hM : MeasurePreserving (fun z : ℝ × Space => (z.1, F z.2)) volume volume := by
    have e : (fun z : ℝ × Space => (z.1, F z.2)) = Prod.map id F := rfl
    rw [e, Measure.volume_eq_prod]
    exact (MeasurePreserving.id (volume : Measure ℝ)).prod F.measurePreserving
  have hYe2 : ∀ᵐ z : ℝ × Space, Y z.1 (F z.2) = Y' (z.1, F z.2) := hM.quasiMeasurePreserving.ae hYe
  have hS : MeasurableSet {z : ℝ × Space | Y' (z.1, F z.2) = c • F (Y' z)} :=
    StronglyMeasurable.measurableSet_eq_fun (hYm.comp_measurable hM.measurable)
      ((F.continuous.const_smul c).comp_stronglyMeasurable hYm)
  have hjoint : ∀ᵐ z : ℝ × Space, Y' (z.1, F z.2) = c • F (Y' z) := by
    have A : ∀ᵐ s, ∀ᵐ x, Y s x = Y' (s, x) := Measure.ae_ae_of_ae_prod hYe
    have B : ∀ᵐ s, ∀ᵐ x, Y s (F x) = Y' (s, F x) := Measure.ae_ae_of_ae_prod hYe2
    rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hS]
    filter_upwards [A, B, h] with s hA hB hh
    filter_upwards [hA, hB, hh] with x h1 h2 h3
    rw [← h2, ← h1, hF, hF, h3]
  filter_upwards [hjoint, hYe, hYe2] with z h1 h2 h3
  simp only [← hF]
  rw [h3, h1]
  congr 2
  exact h2.symm

theorem ae_orbit {p : ℝ × Space → Prop} (h : ∀ᵐ w : ℝ × Space, p w) :
    ∀ᵐ z : ℝ × Space, ∀ᵐ τ : ℝ, ∀ᵐ φ : ℝ, p (z.1 + τ, axialRot φ z.2) :=
  Measure.ae_ae_of_ae_prod
    (Measure.ae_ae_of_ae_prod (Coercive.ModeL2Internal.quasiMeasurePreserving_shiftRot_nested.ae h))

theorem grad_of_columns (F : Space ≃ₗᵢ[ℝ] Space) (hF : ∀ y, F y = flipPoint y) {A B : Space →L[ℝ] Space}
    (h : ∀ j, A (unitVector j) = frameSign j • flipPoint (B (unitVector j))) (u : Space) :
    A u = flipPoint (B (flipPoint u)) := by
  simp only [← hF] at h ⊢
  rw [clm_apply_eq_sum A u, clm_apply_eq_sum B (F u), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h j, map_smul, hF u, flipPoint_apply, smul_smul, mul_comm]

theorem secondDeriv_of_columns (F : Space ≃ₗᵢ[ℝ] Space) (hF : ∀ y, F y = flipPoint y)
    {A B : Space →L[ℝ] Space →L[ℝ] Space}
    (h : ∀ j l, A (unitVector j) (unitVector l)
      = (frameSign l * frameSign j) • flipPoint (B (unitVector j) (unitVector l))) (u w : Space) :
    A u w = flipPoint (B (flipPoint u) (flipPoint w)) := by
  simp only [← hF] at h ⊢
  have hcol : ∀ j, A (unitVector j) w = frameSign j • F (B (unitVector j) (F w)) := by
    intro j
    rw [clm_apply_eq_sum (A (unitVector j)) w, clm_apply_eq_sum (B (unitVector j)) (F w), map_sum,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [h j l, map_smul, hF w, flipPoint_apply]
    simp only [smul_smul]
    congr 1
    ring
  rw [clm_apply_eq_sum A u, _root_.sum_apply, clm_apply_eq_sum B (F u),
    _root_.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [FunLike.coe_smul, Pi.smul_apply]
  rw [hcol j, map_smul, hF u, flipPoint_apply]
  simp only [smul_smul]
  rw [mul_comm]

theorem modeVel_flip_of {v : ℝ → Space → Space} (ξ : ℤ × ℤ) {σ : ℝ} {y : Space}
    (hv : ∀ᵐ τ : ℝ, ∀ᵐ φ : ℝ,
      v (σ + τ) (flipPoint (axialRot φ y)) = flipPoint (v (σ + τ) (axialRot φ y))) :
    modeVel (flipLabel ξ) v σ (flipPoint y) = fun a => (frameSign a : ℂ) * modeVel ξ v σ y a := by
  funext a
  simp only [modeVel, modeAverage_eq]
  have hper : ∀ τ, Function.Periodic (fun φ => expFactor (flipLabel ξ) τ φ
      * ((axialRot (-φ) (v (σ + τ) (axialRot φ (flipPoint y))) a : ℝ) : ℂ)) (2 * Real.pi) := by
    intro τ φ
    simp only [expFactor_add_period, axialRot_add_two_pi, axialRot_neg_add_two_pi]
  calc (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          expFactor (flipLabel ξ) τ φ * ((axialRot (-φ) (v (σ + τ) (axialRot φ (flipPoint y))) a : ℝ) : ℂ)
      = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          expFactor (flipLabel ξ) τ (-φ)
            * ((axialRot (-(-φ)) (v (σ + τ) (axialRot (-φ) (flipPoint y))) a : ℝ) : ℂ) := by
        congr 1
        refine intervalIntegral.integral_congr fun τ _ => ?_
        exact (integral_neg_of_periodic _ (hper τ)).symm
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          (frameSign a : ℂ) * (expFactor ξ τ φ * ((axialRot (-φ) (v (σ + τ) (axialRot φ y)) a : ℝ) : ℂ)) := by
        congr 1
        refine intervalIntegral.integral_congr_ae (hv.mono fun τ hτ _ => ?_)
        refine intervalIntegral.integral_congr_ae (hτ.mono fun φ hφ _ => ?_)
        rw [expFactor_flip, neg_neg, axialRot_flipPoint, neg_neg, hφ, axialRot_flipPoint, flipPoint_apply]
        push_cast
        ring
    _ = (frameSign a : ℂ) * ((1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          expFactor ξ τ φ * ((axialRot (-φ) (v (σ + τ) (axialRot φ y)) a : ℝ) : ℂ)) := by
        simp only [intervalIntegral.integral_const_mul]
        ring

theorem modeGrad_flip_of {G : ℝ → Space → (Space →L[ℝ] Space)} (ξ : ℤ × ℤ) {σ : ℝ} {y : Space}
    (hG : ∀ᵐ τ : ℝ, ∀ᵐ φ : ℝ, ∀ u, G (σ + τ) (flipPoint (axialRot φ y)) u
      = flipPoint (G (σ + τ) (axialRot φ y) (flipPoint u))) :
    modeGrad (flipLabel ξ) G σ (flipPoint y)
      = fun ab => ((frameSign ab.1 * frameSign ab.2 : ℝ) : ℂ) * modeGrad ξ G σ y ab := by
  funext ab
  obtain ⟨i, j⟩ := ab
  simp only [modeGrad, modeAverage_eq]
  have hper : ∀ τ, Function.Periodic (fun φ => expFactor (flipLabel ξ) τ φ
      * ((axialRot (-φ) (G (σ + τ) (axialRot φ (flipPoint y)) (axialRot φ (unitVector j))) i : ℝ) : ℂ))
      (2 * Real.pi) := by
    intro τ φ
    simp only [expFactor_add_period, axialRot_add_two_pi, axialRot_neg_add_two_pi]
  calc (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          expFactor (flipLabel ξ) τ φ * ((axialRot (-φ) (G (σ + τ) (axialRot φ (flipPoint y))
            (axialRot φ (unitVector j))) i : ℝ) : ℂ)
      = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          expFactor (flipLabel ξ) τ (-φ) * ((axialRot (-(-φ)) (G (σ + τ) (axialRot (-φ) (flipPoint y))
            (axialRot (-φ) (unitVector j))) i : ℝ) : ℂ) := by
        congr 1
        refine intervalIntegral.integral_congr fun τ _ => ?_
        exact (integral_neg_of_periodic _ (hper τ)).symm
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          ((frameSign i * frameSign j : ℝ) : ℂ) * (expFactor ξ τ φ * ((axialRot (-φ) (G (σ + τ) (axialRot φ y)
            (axialRot φ (unitVector j))) i : ℝ) : ℂ)) := by
        congr 1
        refine intervalIntegral.integral_congr_ae (hG.mono fun τ hτ _ => ?_)
        refine intervalIntegral.integral_congr_ae (hτ.mono fun φ hφ _ => ?_)
        rw [expFactor_flip, neg_neg, axialRot_flipPoint, neg_neg, axialRot_neg_unit, map_smul, hφ,
          flipPoint_flipPoint, axialRot_map_smul, axialRot_flipPoint, PiLp.smul_apply, flipPoint_apply,
          smul_eq_mul]
        push_cast
        ring
    _ = ((frameSign i * frameSign j : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1,
          ∫ φ in (0 : ℝ)..(2 * Real.pi), expFactor ξ τ φ * ((axialRot (-φ) (G (σ + τ) (axialRot φ y)
            (axialRot φ (unitVector j))) i : ℝ) : ℂ)) := by
        simp only [intervalIntegral.integral_const_mul]
        ring

theorem modeSecondDeriv_flip_of {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (ξ : ℤ × ℤ) {σ : ℝ}
    {y : Space}
    (hH : ∀ᵐ τ : ℝ, ∀ᵐ φ : ℝ, ∀ u w, H (σ + τ) (flipPoint (axialRot φ y)) u w
      = flipPoint (H (σ + τ) (axialRot φ y) (flipPoint u) (flipPoint w))) :
    modeSecondDeriv (flipLabel ξ) H σ (flipPoint y)
      = fun abc => ((frameSign abc.1 * frameSign abc.2.1 * frameSign abc.2.2 : ℝ) : ℂ)
        * modeSecondDeriv ξ H σ y abc := by
  funext abc
  obtain ⟨i, j, l⟩ := abc
  simp only [modeSecondDeriv, modeAverage_eq]
  have hper : ∀ τ, Function.Periodic (fun φ => expFactor (flipLabel ξ) τ φ
      * ((axialRot (-φ) (H (σ + τ) (axialRot φ (flipPoint y)) (axialRot φ (unitVector j))
        (axialRot φ (unitVector l))) i : ℝ) : ℂ)) (2 * Real.pi) := by
    intro τ φ
    simp only [expFactor_add_period, axialRot_add_two_pi, axialRot_neg_add_two_pi]
  calc (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          expFactor (flipLabel ξ) τ φ * ((axialRot (-φ) (H (σ + τ) (axialRot φ (flipPoint y))
            (axialRot φ (unitVector j)) (axialRot φ (unitVector l))) i : ℝ) : ℂ)
      = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          expFactor (flipLabel ξ) τ (-φ) * ((axialRot (-(-φ)) (H (σ + τ) (axialRot (-φ) (flipPoint y))
            (axialRot (-φ) (unitVector j)) (axialRot (-φ) (unitVector l))) i : ℝ) : ℂ) := by
        congr 1
        refine intervalIntegral.integral_congr fun τ _ => ?_
        exact (integral_neg_of_periodic _ (hper τ)).symm
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          ((frameSign i * frameSign j * frameSign l : ℝ) : ℂ) * (expFactor ξ τ φ * ((axialRot (-φ)
            (H (σ + τ) (axialRot φ y) (axialRot φ (unitVector j)) (axialRot φ (unitVector l))) i : ℝ) : ℂ)) := by
        congr 1
        refine intervalIntegral.integral_congr_ae (hH.mono fun τ hτ _ => ?_)
        refine intervalIntegral.integral_congr_ae (hτ.mono fun φ hφ _ => ?_)
        rw [expFactor_flip, neg_neg, axialRot_flipPoint, neg_neg, axialRot_neg_unit, axialRot_neg_unit,
          map_smul, map_smul, FunLike.coe_smul, Pi.smul_apply, hφ, flipPoint_flipPoint, flipPoint_flipPoint,
          smul_smul, axialRot_map_smul, axialRot_flipPoint, PiLp.smul_apply, flipPoint_apply, smul_eq_mul]
        push_cast
        ring
    _ = ((frameSign i * frameSign j * frameSign l : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℂ)
          * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), expFactor ξ τ φ * ((axialRot (-φ)
            (H (σ + τ) (axialRot φ y) (axialRot φ (unitVector j)) (axialRot φ (unitVector l))) i : ℝ) : ℂ)) := by
        simp only [intervalIntegral.integral_const_mul]
        ring

end Internal.ModeFlip

open Internal.ModeFlip in
theorem modeFlip : ModeFlipHolds := by
  intro Γ P v G H g hp hflip ξ
  obtain ⟨γ, hγ, hγ1, hγ2⟩ := hflip
  have hinv : ∀ᵐ z : ℝ × Space, v z.1 (flipPoint z.2) = flipPoint (v z.1 z.2) := by
    filter_upwards [hp.invariant γ hγ] with z hz
    rw [hγ2, add_zero, hγ1, hγ1] at hz
    exact hz
  have hvs : ∀ᵐ s, ∀ᵐ x, v s (flipPoint x) = flipPoint (v s x) := Measure.ae_ae_of_ae_prod hinv
  have hGs : ∀ᵐ s, ∀ᵐ x, ∀ j, G s (flipPoint x) (unitVector j)
      = frameSign j • flipPoint (G s x (unitVector j)) := by
    filter_upwards [hvs, hp.weak_gradient] with s h1 h2
    filter_upwards [ae_flip_gradient γ.1 hγ1 h2 1 (one_mul 1) (h1.mono fun x hx => by rw [hx, one_smul])]
      with x hx j
    rw [hx j, one_mul]
  have hHs : ∀ᵐ s, ∀ᵐ x, ∀ j l, H s (flipPoint x) (unitVector j) (unitVector l)
      = (frameSign l * frameSign j) • flipPoint (H s x (unitVector j) (unitVector l)) := by
    filter_upwards [hGs, hp.weak_secondDeriv] with s h1 h2
    have hl : ∀ l, ∀ᵐ x, ∀ j, H s (flipPoint x) (unitVector j) (unitVector l)
        = (frameSign l * frameSign j) • flipPoint (H s x (unitVector j) (unitVector l)) := fun l =>
      (ae_flip_gradient γ.1 hγ1 (h2 l) (frameSign l) (frameSign_mul_self l)
        (h1.mono fun x hx => hx l)).mono fun x hx j => hx j
    filter_upwards [ae_all_iff.2 hl] with x hx j l
    exact hx l j
  have hGj : ∀ j, ∀ᵐ z : ℝ × Space, G z.1 (flipPoint z.2) (unitVector j)
      = frameSign j • flipPoint (G z.1 z.2 (unitVector j)) := fun j =>
    ae_joint_flip γ.1 hγ1 (fun s x => G s x (unitVector j))
      ((continuous_id.clm_apply continuous_const).comp_aestronglyMeasurable hp.measurable_gradient)
      (frameSign j) (hGs.mono fun s hs => hs.mono fun x hx => hx j)
  have hHj : ∀ j l, ∀ᵐ z : ℝ × Space, H z.1 (flipPoint z.2) (unitVector j) (unitVector l)
      = (frameSign l * frameSign j) • flipPoint (H z.1 z.2 (unitVector j) (unitVector l)) := fun j l =>
    ae_joint_flip γ.1 hγ1 (fun s x => H s x (unitVector j) (unitVector l))
      (((continuous_id.clm_apply continuous_const).clm_apply continuous_const).comp_aestronglyMeasurable
        hp.measurable_secondDeriv)
      (frameSign l * frameSign j) (hHs.mono fun s hs => hs.mono fun x hx => hx j l)
  have hall : ∀ᵐ w : ℝ × Space, v w.1 (flipPoint w.2) = flipPoint (v w.1 w.2)
      ∧ (∀ u, G w.1 (flipPoint w.2) u = flipPoint (G w.1 w.2 (flipPoint u)))
      ∧ ∀ u u', H w.1 (flipPoint w.2) u u' = flipPoint (H w.1 w.2 (flipPoint u) (flipPoint u')) := by
    filter_upwards [hinv, ae_all_iff.2 hGj, ae_all_iff.2 fun j => ae_all_iff.2 (hHj j)] with w h1 h2 h3
    exact ⟨h1, grad_of_columns γ.1 hγ1 h2, secondDeriv_of_columns γ.1 hγ1 h3⟩
  filter_upwards [ae_orbit hall] with z hz
  exact ⟨modeVel_flip_of ξ (hz.mono fun τ h => h.mono fun φ h => h.1),
    modeGrad_flip_of ξ (hz.mono fun τ h => h.mono fun φ h => h.2.1),
    modeSecondDeriv_flip_of ξ (hz.mono fun τ h => h.mono fun φ h => h.2.2)⟩

end Bridge

end CertCell

end Breakdown
