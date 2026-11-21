import Breakdown.CertCell.TopStatements
import Breakdown.CertCell.TailAngularPlane
import Breakdown.CertCell.HarmonicProfiles
import Breakdown.Cert.CoerciveTorus
import Breakdown.Cert.CoerciveRotation

open scoped ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace CertCell

namespace Internal.NegativeModeSum

def orbitModes {β X : Type*} (Φ : ℝ → X → β → ℝ) (u : ℝ × Space → X) (ξ : ℤ × ℤ) (y : Space) :
    β → ℂ :=
  fun b => modeAverage ξ (fun τ φ b => Φ φ (u (τ, axialRot φ y)) b) b

theorem labelHarmonic_injective_of_pos {m : ℕ} (hm : 1 ≤ m) : Function.Injective (labelHarmonic m) := by
  intro a b h
  simp only [labelHarmonic, labelTime, labelAzimuth, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have e1 : a.1 = b.1 := mul_right_cancel₀ hm' h2
  have e2 : a.2 = b.2 := by omega
  exact Prod.ext e1 e2

theorem lintegral_Icc_eq_Ioo_of_periodic {k : ℝ → ℝ≥0∞} (hk : Function.Periodic k (2 * Real.pi)) :
    ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), k φ = ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi, k φ := by
  have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  have h0 := AddCircle.lintegral_preimage (T := 2 * Real.pi) 0 hk.lift
  have h1 := AddCircle.lintegral_preimage (T := 2 * Real.pi) (-Real.pi) hk.lift
  simp only [Function.Periodic.lift_coe] at h0 h1
  rw [zero_add] at h0
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h1
  rw [setLIntegral_congr Ioc_ae_eq_Icc.symm, setLIntegral_congr Ioo_ae_eq_Ioc, h0, h1]

theorem torus_sum_le (g : ℝ → ℝ → ℝ) (hg : StronglyMeasurable (fun z : ℝ × ℝ => g z.1 z.2)) :
    ∑' ξ : ℤ × ℤ, ENNReal.ofReal (‖modeAverage ξ (fun τ φ (_ : Unit) => g τ φ) ()‖ ^ 2) ≤
      ENNReal.ofReal (1 / (2 * Real.pi)) *
        ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (g τ φ ^ 2) := by
  by_cases hJ : (∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi),
      ENNReal.ofReal (g τ φ ^ 2)) < ⊤
  · exact (Coercive.torusSquareSumHolds_proof g hg.aestronglyMeasurable hJ).le
  · rw [not_lt, top_le_iff] at hJ
    have hc : ENNReal.ofReal (1 / (2 * Real.pi)) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (by positivity)).ne'
    rw [hJ, ENNReal.mul_top hc]
    exact le_top

theorem continuous_orbitPair (y : Space) :
    Continuous (fun z : ℝ × ℝ => ((z.1, axialRot z.2 y) : ℝ × Space)) := by
  unfold axialRot
  fun_prop

theorem point_sum_le {β X : Type*} [Fintype β] [NormedAddCommGroup X] (u : ℝ × Space → X)
    (hu : StronglyMeasurable u) (Φ : ℝ → X → β → ℝ)
    (hΦ : ∀ b, Continuous (fun q : ℝ × X => Φ q.1 q.2 b)) (y : Space) :
    ∑' ξ : ℤ × ℤ, ENNReal.ofReal (cnormSq (orbitModes Φ u ξ y)) ≤
      ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Set.Icc (0 : ℝ) 1,
        ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (∑ b, Φ φ (u (τ, axialRot φ y)) b ^ 2) := by
  have hgm : ∀ b, StronglyMeasurable (fun z : ℝ × ℝ => Φ z.2 (u (z.1, axialRot z.2 y)) b) := by
    intro b
    have h1 : StronglyMeasurable (fun z : ℝ × ℝ => u (z.1, axialRot z.2 y)) :=
      hu.comp_measurable (continuous_orbitPair y).measurable
    exact (hΦ b).comp_stronglyMeasurable (continuous_snd.stronglyMeasurable.prodMk h1)
  have hJ : ∀ b, Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (Φ z.2 (u (z.1, axialRot z.2 y)) b ^ 2)) :=
    fun b => ((hgm b).measurable.pow_const 2).ennreal_ofReal
  calc ∑' ξ : ℤ × ℤ, ENNReal.ofReal (cnormSq (orbitModes Φ u ξ y))
      = ∑' ξ : ℤ × ℤ, ∑ b, ENNReal.ofReal
          (‖modeAverage ξ (fun τ φ (_ : Unit) => Φ φ (u (τ, axialRot φ y)) b) ()‖ ^ 2) := by
        refine tsum_congr fun ξ => ?_
        rw [cnormSq, ENNReal.ofReal_sum_of_nonneg (fun b _ => by positivity)]
        rfl
    _ = ∑ b, ∑' ξ : ℤ × ℤ, ENNReal.ofReal
          (‖modeAverage ξ (fun τ φ (_ : Unit) => Φ φ (u (τ, axialRot φ y)) b) ()‖ ^ 2) :=
        Summable.tsum_finsetSum (fun b _ => ENNReal.summable)
    _ ≤ ∑ b, ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Set.Icc (0 : ℝ) 1,
          ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (Φ φ (u (τ, axialRot φ y)) b ^ 2) :=
        Finset.sum_le_sum fun b _ => torus_sum_le (fun τ φ => Φ φ (u (τ, axialRot φ y)) b) (hgm b)
    _ = ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Set.Icc (0 : ℝ) 1,
          ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (∑ b, Φ φ (u (τ, axialRot φ y)) b ^ 2) := by
        rw [← Finset.mul_sum]
        congr 1
        have hm2 : ∀ b, Measurable (fun τ : ℝ => ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi),
            ENNReal.ofReal (Φ φ (u (τ, axialRot φ y)) b ^ 2)) := fun b => (hJ b).lintegral_prod_right'
        rw [← lintegral_finsetSum _ fun b _ => hm2 b]
        refine lintegral_congr fun τ => ?_
        have hm1 : ∀ b, Measurable (fun φ : ℝ => ENNReal.ofReal (Φ φ (u (τ, axialRot φ y)) b ^ 2)) :=
          fun b => (hJ b).comp measurable_prodMk_left
        rw [← lintegral_finsetSum _ fun b _ => hm1 b]
        refine lintegral_congr fun φ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun b _ => by positivity)]

theorem ae_orbitModes_eq {β X : Type*} (Φ : ℝ → X → β → ℝ) {u u' : ℝ × Space → X}
    (hae : u =ᵐ[volume] u') :
    ∀ᵐ p ∂(volume.restrict halfPlane), ∀ ξ,
      orbitModes Φ u ξ (planePoint p) = orbitModes Φ u' ξ (planePoint p) := by
  have h3 := TailBand.quasiMeasurePreserving_orbitPlane.ae_eq hae
  have h4 := Measure.ae_ae_of_ae_prod (Measure.ae_ae_of_ae_prod h3)
  filter_upwards [h4] with p hp
  intro ξ
  funext b
  simp only [orbitModes, modeAverage]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hp] with τ hτ _
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hτ] with φ hφ _
  simp only [Function.comp_apply] at hφ
  rw [hφ]

theorem aemeasurable_orbitModes {β X : Type*} [Fintype β] [NormedAddCommGroup X]
    (Φ : ℝ → X → β → ℝ) (hΦ : ∀ b, Continuous (fun q : ℝ × X => Φ q.1 q.2 b))
    {u : ℝ × Space → X} (hu : AEStronglyMeasurable u volume) (ξ : ℤ × ℤ) :
    AEMeasurable (fun p : ℝ × ℝ => cnormSq (orbitModes Φ u ξ (planePoint p))) (volume.restrict halfPlane) := by
  have hc : Continuous (fun x : β → ℂ => cnormSq x) := by
    unfold cnormSq
    fun_prop
  refine hc.measurable.comp_aemeasurable (aemeasurable_pi_iff.2 fun b => ?_)
  have h := (TailBand.Internal.AngularPlane.aestronglyMeasurable_orbitAverage hu ξ
    (fun φ x => Φ φ x b) (hΦ b)).const_mul (1 / (2 * Real.pi) : ℂ)
  exact h.aemeasurable

theorem amplitude_sum_le {β X : Type*} [Fintype β] [NormedAddCommGroup X] {m : ℕ} (hm : 1 ≤ m)
    (u : ℝ × Space → X) (hu : AEStronglyMeasurable u volume)
    (Φ : ℝ → X → β → ℝ) (hΦ : ∀ b, Continuous (fun q : ℝ × X => Φ q.1 q.2 b))
    (N : X → ℝ) (hNc : Continuous N) (hN : ∀ φ x, ∑ b, Φ φ x b ^ 2 = N x) :
    (∑' ι : ℤ × ℤ, ∫⁻ p in halfPlane,
      ENNReal.ofReal (cnormSq (orbitModes Φ u (labelHarmonic m ι) (planePoint p)) * p.1)) ≤
      ENNReal.ofReal (1 / (2 * Real.pi)) *
        ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (N (u (σ, y))) := by
  have hu' : StronglyMeasurable (hu.mk u) := hu.stronglyMeasurable_mk
  have hae : u =ᵐ[volume] hu.mk u := hu.ae_eq_mk
  have hW : Measurable (fun z : ℝ × Space => ENNReal.ofReal (N (hu.mk u z))) :=
    (hNc.comp_stronglyMeasurable hu').measurable.ennreal_ofReal
  have hsub : halfPlane ⊆ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) :=
    Set.prod_mono le_rfl (Set.subset_univ _)
  have hper : ∀ (τ : ℝ) (p : ℝ × ℝ),
      ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (N (hu.mk u (τ, axialRot φ (planePoint p)))) =
        ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi, ENNReal.ofReal (N (hu.mk u (τ, axialRot φ (planePoint p)))) := by
    intro τ p
    refine lintegral_Icc_eq_Ioo_of_periodic fun φ => ?_
    simp only [axialRot, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hB : ∀ p : ℝ × ℝ, ∑' ξ : ℤ × ℤ, ENNReal.ofReal (cnormSq (orbitModes Φ (hu.mk u) ξ (planePoint p))) ≤
      ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Set.Icc (0 : ℝ) 1,
        ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi, ENNReal.ofReal (N (hu.mk u (τ, axialRot φ (planePoint p)))) := by
    intro p
    have h := point_sum_le (hu.mk u) hu' Φ hΦ (planePoint p)
    simp only [hN, hper] at h
    exact h
  have hmeas : ∀ ξ, AEMeasurable (fun p : ℝ × ℝ => cnormSq (orbitModes Φ (hu.mk u) ξ (planePoint p)))
      (volume.restrict halfPlane) := aemeasurable_orbitModes Φ hΦ hu'.aestronglyMeasurable
  have hp1 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1) (volume.restrict halfPlane) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).aemeasurable
  have hcyl := CellCalculus.Internal.HarmonicProfiles.lintegral_cyl_time _ hW (Set.Icc (0 : ℝ) 1)
  calc (∑' ι : ℤ × ℤ, ∫⁻ p in halfPlane,
        ENNReal.ofReal (cnormSq (orbitModes Φ u (labelHarmonic m ι) (planePoint p)) * p.1))
      = ∑' ι : ℤ × ℤ, ∫⁻ p in halfPlane, ENNReal.ofReal
          (cnormSq (orbitModes Φ (hu.mk u) (labelHarmonic m ι) (planePoint p))) * ENNReal.ofReal p.1 := by
        refine tsum_congr fun ι => lintegral_congr_ae ?_
        filter_upwards [ae_orbitModes_eq Φ hae] with p hp
        rw [hp, ENNReal.ofReal_mul (by unfold cnormSq; positivity)]
    _ = ∫⁻ p in halfPlane, ∑' ι : ℤ × ℤ, ENNReal.ofReal
          (cnormSq (orbitModes Φ (hu.mk u) (labelHarmonic m ι) (planePoint p))) * ENNReal.ofReal p.1 :=
        (lintegral_tsum fun ι => (hmeas _).ennreal_ofReal.mul hp1).symm
    _ ≤ ∫⁻ p in halfPlane, ENNReal.ofReal p.1 * (ENNReal.ofReal (1 / (2 * Real.pi)) *
          ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal (N (hu.mk u (τ, axialRot φ (planePoint p))))) := by
        refine lintegral_mono fun p => ?_
        rw [ENNReal.tsum_mul_right, mul_comm _ (ENNReal.ofReal p.1)]
        gcongr
        exact (ENNReal.tsum_comp_le_tsum_of_injective (labelHarmonic_injective_of_pos hm) _).trans (hB p)
    _ = ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ p in halfPlane, ENNReal.ofReal p.1 *
          ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal (N (hu.mk u (τ, axialRot φ (planePoint p)))) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun p => ?_
        ring
    _ ≤ ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.univ, ENNReal.ofReal p.1 *
          ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal (N (hu.mk u (τ, axialRot φ (planePoint p)))) := by
        gcongr
    _ = ENNReal.ofReal (1 / (2 * Real.pi)) *
          ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (N (hu.mk u (σ, y))) := by
        rw [hcyl]
    _ = ENNReal.ofReal (1 / (2 * Real.pi)) *
          ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (N (u (σ, y))) := by
        congr 1
        refine lintegral_congr_ae (ae_restrict_of_ae ?_)
        have h2 : ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure Space)), u z = hu.mk u z := by
          rw [← Measure.volume_eq_prod]
          exact hae
        filter_upwards [Measure.ae_ae_of_ae_prod h2] with σ hσ
        refine lintegral_congr_ae ?_
        filter_upwards [hσ] with y hy
        rw [hy]

theorem sum_sq_rotCoord (φ : ℝ) (x : Space) : ∑ i : Fin 3, axialRot (-φ) x i ^ 2 = ‖x‖ ^ 2 := by
  obtain ⟨R, hR⟩ := Coercive.axialRotationHolds_proof.1 (-φ)
  rw [← hR, ← R.norm_map x, EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]

theorem continuous_rotCoord (i : Fin 3) : Continuous (fun q : ℝ × Space => axialRot (-q.1) q.2 i) := by
  unfold axialRot
  fun_prop

theorem sum_sq_apply_basis (A : Space →L[ℝ] Space) (b : OrthonormalBasis (Fin 3) ℝ Space) :
    ∑ j, ‖A (b j)‖ ^ 2 = ∑ i, ‖(ContinuousLinearMap.adjoint A) (unitVector i)‖ ^ 2 := by
  set e := EuclideanSpace.basisFun (Fin 3) ℝ
  have he : ∀ i, e i = unitVector i := fun i => by simp [e, unitVector]
  have h1 : ∀ j, ‖A (b j)‖ ^ 2 = ∑ i, ‖inner ℝ (e i) (A (b j))‖ ^ 2 :=
    fun j => (e.sum_sq_norm_inner_right _).symm
  have h2 : ∀ i, ‖(ContinuousLinearMap.adjoint A) (unitVector i)‖ ^ 2 =
      ∑ j, ‖inner ℝ ((ContinuousLinearMap.adjoint A) (e i)) (b j)‖ ^ 2 := fun i => by
    rw [← he i, b.sum_sq_norm_inner_left]
  simp_rw [h1, h2, ContinuousLinearMap.adjoint_inner_left]
  exact Finset.sum_comm

theorem sum_sq_apply_isometry (A : Space →L[ℝ] Space) (R : Space ≃ₗᵢ[ℝ] Space) :
    ∑ j, ‖A (R (unitVector j))‖ ^ 2 = matSq A := by
  have he : ∀ i, EuclideanSpace.basisFun (Fin 3) ℝ i = unitVector i := fun i => by simp [unitVector]
  have h1 := sum_sq_apply_basis A ((EuclideanSpace.basisFun (Fin 3) ℝ).map R)
  have h2 := sum_sq_apply_basis A (EuclideanSpace.basisFun (Fin 3) ℝ)
  simp only [OrthonormalBasis.map_apply, he] at h1 h2
  unfold matSq
  rw [h1, ← h2]

theorem sum_sq_rotGradCoord (φ : ℝ) (A : Space →L[ℝ] Space) :
    ∑ ij : Fin 3 × Fin 3, axialRot (-φ) (A (axialRot φ (unitVector ij.2))) ij.1 ^ 2 = matSq A := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [sum_sq_rotCoord]
  obtain ⟨R, hR⟩ := Coercive.axialRotationHolds_proof.1 φ
  simp only [← hR]
  exact sum_sq_apply_isometry A R

theorem sum_sq_rotSecondDerivCoord (φ : ℝ) (B : Space →L[ℝ] Space →L[ℝ] Space) :
    ∑ ijl : Fin 3 × Fin 3 × Fin 3,
      axialRot (-φ) (B (axialRot φ (unitVector ijl.2.1)) (axialRot φ (unitVector ijl.2.2))) ijl.1 ^ 2 =
      Coercive.secondDerivSq B := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Fintype.sum_prod_type, sum_sq_rotCoord]
  obtain ⟨R, hR⟩ := Coercive.axialRotationHolds_proof.1 φ
  simp only [← hR]
  have h1 : ∀ j, ∑ l, ‖B (R (unitVector j)) (R (unitVector l))‖ ^ 2 =
      ∑ l, ‖B (R (unitVector j)) (unitVector l)‖ ^ 2 :=
    fun j => sum_sq_apply_isometry (B (R (unitVector j))) R
  have h2 : ∀ l, ∑ j, ‖B (R (unitVector j)) (unitVector l)‖ ^ 2 =
      ∑ j, ‖B (unitVector j) (unitVector l)‖ ^ 2 := fun l => by
    have h := sum_sq_apply_isometry (B.flip (unitVector l)) R
    simpa only [ContinuousLinearMap.flip_apply, matSq] using h
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [h2]
  unfold Coercive.secondDerivSq
  exact Finset.sum_comm


end Internal.NegativeModeSum

open Internal.NegativeModeSum in
theorem labelAmplitude_sum_le (m : ℕ) (hm : 1 ≤ m) (f : ℝ → Space → Space)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume) (hp : IsTimePeriodic f) :
    (∑' ι : ℤ × ℤ, ∫⁻ p in halfPlane,
      ENNReal.ofReal (cnormSq (modeVel (labelHarmonic m ι) f 0 (planePoint p)) * p.1)) ≤
      ENNReal.ofReal (1 / (2 * Real.pi)) * periodLIntegral (fun σ y => ‖f σ y‖ ^ 2) := by
  have h := amplitude_sum_le hm (fun z : ℝ × Space => f z.1 z.2) hf
    (fun φ w i => axialRot (-φ) w i) continuous_rotCoord (fun w => ‖w‖ ^ 2) (continuous_norm.pow 2)
    sum_sq_rotCoord
  have e : ∀ ι p, modeVel (labelHarmonic m ι) f 0 (planePoint p) = orbitModes
      (fun φ w i => axialRot (-φ) w i) (fun z : ℝ × Space => f z.1 z.2) (labelHarmonic m ι) (planePoint p) := by
    intro ι p
    funext i
    simp only [modeVel, orbitModes, zero_add]
  simp only [e]
  exact h

open Internal.NegativeModeSum in
theorem labelGradAmplitude_sum_le (m : ℕ) (hm : 1 ≤ m) (G : ℝ → Space → (Space →L[ℝ] Space))
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (hp : IsTimePeriodic G) :
    (∑' ι : ℤ × ℤ, ∫⁻ p in halfPlane,
      ENNReal.ofReal (cnormSq (modeGrad (labelHarmonic m ι) G 0 (planePoint p)) * p.1)) ≤
      ENNReal.ofReal (1 / (2 * Real.pi)) * periodLIntegral (fun σ y => matSq (G σ y)) := by
  have h := amplitude_sum_le hm (fun z : ℝ × Space => G z.1 z.2) hG
    (fun φ (A : Space →L[ℝ] Space) (ij : Fin 3 × Fin 3) => axialRot (-φ) (A (axialRot φ (unitVector ij.2))) ij.1)
    (fun ij => by beta_reduce; unfold axialRot; fun_prop)
    (fun A => matSq A) (by unfold matSq; fun_prop) sum_sq_rotGradCoord
  have e : ∀ ι p, modeGrad (labelHarmonic m ι) G 0 (planePoint p) = orbitModes
      (fun φ (A : Space →L[ℝ] Space) (ij : Fin 3 × Fin 3) => axialRot (-φ) (A (axialRot φ (unitVector ij.2))) ij.1) (fun z : ℝ × Space => G z.1 z.2)
      (labelHarmonic m ι) (planePoint p) := by
    intro ι p
    funext ij
    simp only [modeGrad, orbitModes, zero_add]
  simp only [e]
  exact h

open Internal.NegativeModeSum in
theorem labelSecondDerivAmplitude_sum_le (m : ℕ) (hm : 1 ≤ m) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) (hp : IsTimePeriodic H) :
    (∑' ι : ℤ × ℤ, ∫⁻ p in halfPlane,
      ENNReal.ofReal (cnormSq (modeSecondDeriv (labelHarmonic m ι) H 0 (planePoint p)) * p.1)) ≤
      ENNReal.ofReal (1 / (2 * Real.pi)) * periodLIntegral (fun σ y => Coercive.secondDerivSq (H σ y)) := by
  have h := amplitude_sum_le hm (fun z : ℝ × Space => H z.1 z.2) hH
    (fun φ (B : Space →L[ℝ] Space →L[ℝ] Space) (ijl : Fin 3 × Fin 3 × Fin 3) => axialRot (-φ) (B (axialRot φ (unitVector ijl.2.1)) (axialRot φ (unitVector ijl.2.2))) ijl.1)
    (fun ijl => by beta_reduce; unfold axialRot; fun_prop)
    (fun B => Coercive.secondDerivSq B) (by unfold Coercive.secondDerivSq; fun_prop) sum_sq_rotSecondDerivCoord
  have e : ∀ ι p, modeSecondDeriv (labelHarmonic m ι) H 0 (planePoint p) = orbitModes
      (fun φ (B : Space →L[ℝ] Space →L[ℝ] Space) (ijl : Fin 3 × Fin 3 × Fin 3) => axialRot (-φ) (B (axialRot φ (unitVector ijl.2.1)) (axialRot φ (unitVector ijl.2.2))) ijl.1)
      (fun z : ℝ × Space => H z.1 z.2) (labelHarmonic m ι) (planePoint p) := by
    intro ι p
    funext ijl
    simp only [modeSecondDeriv, orbitModes, zero_add]
  simp only [e]
  exact h

end CertCell

end Breakdown
