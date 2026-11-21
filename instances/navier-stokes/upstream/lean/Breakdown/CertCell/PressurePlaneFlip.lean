import Breakdown.CertCell.BridgeTraceStatements
import Breakdown.FracCell.CylinderFlux

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace SideTrace

open CellCert.CellFormula CellCert.CellAnalysis Bridge SteadyCert

namespace Internal.PressurePlaneFlip

def flipSign (i : Fin 3) : ℝ := if i = 0 then 1 else -1

theorem flipSign_sq (i : Fin 3) : flipSign i * flipSign i = 1 := by
  unfold flipSign; split_ifs <;> norm_num

theorem flipPoint_apply (y : Space) (i : Fin 3) : flipPoint y i = flipSign i * y i := by
  fin_cases i <;> simp [flipPoint, flipSign, unitVector]

theorem flipPoint_flipPoint (y : Space) : flipPoint (flipPoint y) = y := by
  ext i
  rw [flipPoint_apply, flipPoint_apply, ← mul_assoc, flipSign_sq, one_mul]

def flipLinear : Space →ₗ[ℝ] Space where
  toFun := flipPoint
  map_add' x y := by
    ext i
    simp only [flipPoint_apply, PiLp.add_apply]
    ring
  map_smul' c x := by
    ext i
    simp only [flipPoint_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem norm_flipPoint (y : Space) : ‖flipLinear y‖ = ‖y‖ := by
  change ‖flipPoint y‖ = ‖y‖
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [flipPoint_apply, norm_mul]
  have : ‖flipSign i‖ = 1 := by unfold flipSign; split_ifs <;> norm_num
  rw [this, one_mul]

def flipIsometry : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv ⟨flipLinear, norm_flipPoint⟩ rfl

theorem flipIsometry_apply (y : Space) : flipIsometry y = flipPoint y := rfl

theorem flip_measurePreserving : MeasurePreserving flipPoint volume volume :=
  flipIsometry.measurePreserving

theorem flip_embedding : MeasurableEmbedding flipPoint :=
  flipIsometry.toHomeomorph.measurableEmbedding

theorem integral_flip (g : Space → ℝ) : ∫ y, g (flipPoint y) = ∫ y, g y :=
  flip_measurePreserving.integral_comp flip_embedding g

theorem flip_unitVector (j : Fin 3) : flipPoint (unitVector j) = flipSign j • unitVector j := by
  ext i
  rw [flipPoint_apply, PiLp.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [flipSign, unitVector]

theorem inner_flip_unit (w : Space) (j : Fin 3) :
    inner ℝ (flipPoint w) (unitVector j) = flipSign j * inner ℝ w (unitVector j) := by
  simp only [unitVector, EuclideanSpace.inner_single_right, flipPoint_apply]
  simp

theorem potential_flip {Q : Space → Space} {q : Space → ℝ} (hq : IsPotentialOf Q q)
    (hQ : ∀ᵐ y, Q (flipPoint y) = flipPoint (Q y)) : IsPotentialOf Q (fun y => q (flipPoint y)) := by
  obtain ⟨hm, hsq, hw⟩ := hq
  refine ⟨hm.comp_measurePreserving flip_measurePreserving, ?_, ?_⟩
  · intro K hK
    have hK' : IsCompact (flipPoint ⁻¹' K) := flipIsometry.toHomeomorph.isCompact_preimage.2 hK
    have h1 := hsq _ hK'
    have h2 : IntegrableOn ((fun y => q y ^ 2) ∘ flipPoint) (flipPoint ⁻¹' (flipPoint ⁻¹' K)) :=
      (flip_measurePreserving.integrableOn_comp_preimage flip_embedding).2 h1
    have e : flipPoint ⁻¹' (flipPoint ⁻¹' K) = K := by
      ext y; simp [flipPoint_flipPoint]
    rw [e] at h2
    exact h2
  · intro φ hφ j
    have hψ : IsTestScalar (fun y => φ (flipPoint y)) :=
      ⟨hφ.1.comp flipIsometry.contDiff, hφ.2.comp_homeomorph flipIsometry.toHomeomorph⟩
    have hd : ∀ u, fderiv ℝ (fun y => φ (flipPoint y)) u (unitVector j) =
        flipSign j * fderiv ℝ φ (flipPoint u) (unitVector j) := by
      intro u
      have : (fun y => φ (flipPoint y)) = φ ∘ flipIsometry.toContinuousLinearEquiv := rfl
      rw [this, ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearMap.comp_apply]
      change fderiv ℝ φ (flipPoint u) (flipPoint (unitVector j)) = _
      rw [flip_unitVector, map_smul, smul_eq_mul]
    have hd' : ∀ u, fderiv ℝ φ (flipPoint u) (unitVector j) =
        flipSign j * fderiv ℝ (fun y => φ (flipPoint y)) u (unitVector j) := by
      intro u
      rw [hd, ← mul_assoc, flipSign_sq, one_mul]
    have hL : ∫ y, fderiv ℝ φ y (unitVector j) * q (flipPoint y)
        = flipSign j * -∫ u, φ (flipPoint u) * inner ℝ (Q u) (unitVector j) := by
      rw [← integral_flip (fun y => fderiv ℝ φ y (unitVector j) * q (flipPoint y))]
      simp only [flipPoint_flipPoint, hd', mul_assoc]
      rw [integral_const_mul, hw _ hψ j]
    have hR : ∫ y, φ y * inner ℝ (Q y) (unitVector j)
        = flipSign j * ∫ u, φ (flipPoint u) * inner ℝ (Q u) (unitVector j) := by
      rw [← integral_flip (fun y => φ y * inner ℝ (Q y) (unitVector j)), ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hQ] with u hu
      simp only [hu, inner_flip_unit]
      ring
    rw [hL, hR, mul_neg]

theorem flip_ae_eq (hC : PotentialConstantHolds) {Q : Space → Space} {q : Space → ℝ} (hq : IsPotentialOf Q q)
    (hQ : ∀ᵐ y, Q (flipPoint y) = flipPoint (Q y)) : ∀ᵐ y, q (flipPoint y) = q y := by
  obtain ⟨C, hCq⟩ := hC Q q _ hq (potential_flip hq hQ)
  have h2 : ∀ᵐ y, q (flipPoint (flipPoint y)) = q (flipPoint y) + C :=
    flip_measurePreserving.quasiMeasurePreserving.ae hCq
  have hC0 : C = 0 := by
    obtain ⟨y, hy1, hy2⟩ := (hCq.and h2).exists
    rw [flipPoint_flipPoint, hy1] at hy2
    linarith
  filter_upwards [hCq] with y hy
  rw [hy, hC0, add_zero]

theorem cyl_flip (r θ z : ℝ) : flipPoint (cylPoint r θ z) = cylPoint r (-θ) (-z) := by
  ext i
  rw [flipPoint_apply]
  fin_cases i <;> simp [cylPoint, flipSign, Real.cos_neg, Real.sin_neg]

theorem cyl_periodic (r θ z : ℝ) : cylPoint r (θ + 2 * Real.pi) z = cylPoint r θ z := by
  simp [cylPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem azimuth_phase (m : ℕ) (n : ℤ) :
    Complex.exp (((azimuth m n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1 := by
  have : (((azimuth m n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = ((n * m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    simp only [azimuth]; push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem presMode_flip (m : ℕ) (n : ℤ) (q : Space → ℝ) (r z : ℝ) :
    presMode m (-n) q r (-z) = presMode m n (fun y => q (flipPoint y)) r z := by
  unfold presMode
  congr 1
  have ha : azimuth m (-n) = -azimuth m n := by simp [azimuth]
  set f : ℝ → ℂ := fun θ => Complex.exp (-(azimuth m (-n) * θ : ℝ) * Complex.I) * (q (cylPoint r θ (-z)) : ℂ)
    with hf
  have key : ∀ θ, f (2 * Real.pi - θ) =
      Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (q (flipPoint (cylPoint r θ z)) : ℂ) := by
    intro θ
    have hc : cylPoint r (2 * Real.pi - θ) (-z) = cylPoint r (-θ) (-z) := by
      rw [show 2 * Real.pi - θ = -θ + 2 * Real.pi by ring, cyl_periodic]
    have he : Complex.exp (-(azimuth m (-n) * (2 * Real.pi - θ) : ℝ) * Complex.I)
        = Complex.exp (((azimuth m n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)
          * Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) := by
      rw [← Complex.exp_add, ha]
      congr 1
      push_cast
      ring
    simp only [hf, hc, he, azimuth_phase, one_mul, cyl_flip]
  have h1 := intervalIntegral.integral_comp_sub_left f (a := 0) (b := 2 * Real.pi) (2 * Real.pi)
  simp only [sub_self, sub_zero, key] at h1
  rw [← h1]

theorem interval_shift (f : ℝ → ℂ) (hf : Function.Periodic f (2 * Real.pi)) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), f θ = ∫ θ in (-Real.pi)..Real.pi, f θ := by
  have h := hf.intervalIntegral_add_eq 0 (-Real.pi)
  rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at h
  exact h

theorem mode_integrand_periodic (m : ℕ) (n : ℤ) (P : Space → ℝ) (r z : ℝ) :
    Function.Periodic (fun θ : ℝ => Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (P (cylPoint r θ z) : ℂ))
      (2 * Real.pi) := by
  intro θ
  have he : Complex.exp (-(azimuth m n * (θ + 2 * Real.pi) : ℝ) * Complex.I)
      = Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I)
        * (Complex.exp (((azimuth m n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I))⁻¹ := by
    rw [← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [he, azimuth_phase, inv_one, mul_one, cyl_periodic]

theorem presMode_congr (m : ℕ) (n : ℤ) (P P' : Space → ℝ) (r z : ℝ)
    (h : ∀ᵐ θ ∂(volume.restrict (Ioo (-Real.pi) Real.pi)), P (cylPoint r θ z) = P' (cylPoint r θ z)) :
    presMode m n P r z = presMode m n P' r z := by
  unfold presMode
  congr 1
  rw [interval_shift _ (mode_integrand_periodic m n P r z), interval_shift _ (mode_integrand_periodic m n P' r z)]
  refine intervalIntegral.integral_congr_ae ?_
  rw [Set.uIoc_of_le (by linarith [Real.pi_pos])]
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc, ae_restrict_iff' measurableSet_Ioc] at h
  filter_upwards [h] with θ hθ hmem
  rw [hθ hmem]

end Internal.PressurePlaneFlip

open Internal.PressurePlaneFlip in
theorem pressurePlaneFlip (hC : PotentialConstantHolds) : PressurePlaneFlipHolds := by
  intro m Q q _ hq _ hQ n
  have hs := CellCert.CellFormula.Internal.CylinderFlux.slice_ae (flip_ae_eq hC hq hQ)
  have hmeas : MeasurableSet halfPlane := by
    unfold halfPlane
    exact measurableSet_Ioi.prod measurableSet_Ioi
  rw [ae_restrict_iff' hmeas]
  filter_upwards [hs] with p hp hmem
  rw [presMode_flip]
  have hpos : 0 < p.1 := by
    unfold halfPlane at hmem
    exact hmem.1
  exact presMode_congr m n _ _ p.1 p.2 (hp hpos)

end SideTrace

end CertCell

end Breakdown
