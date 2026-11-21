import Breakdown.CertCell.Defs
import Breakdown.CertCell.CouplingStatements
import Breakdown.FracCell.FormulaDataDefs
import Breakdown.CertCell.StatementDefs

open scoped ContDiff ENNReal ComplexOrder
open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

structure IsFlipCompatible {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds)
    (w : Space → ℝ) : Prop where
  strain_flip : ∀ ξ y, m.convD (m.classOf (flipLabel ξ)) (flipPoint y) = m.convD (m.classOf ξ) y
  vorticity_flip : ∀ ξ y, m.convZ (m.classOf (flipLabel ξ)) (flipPoint y) = m.convZ (m.classOf ξ) y
  weight_flip : ∀ y, w (flipPoint y) = w y
  eps_mirror : ∃ π : Equiv.Perm (Fin nE), ∀ β,
    (m.epsP (π β)).modes = flipLabel '' (m.epsP β).modes ∧ (m.epsP (π β)).frame = -(m.epsP β).frame ∧
    ∀ y, (m.epsP (π β)).wt (flipPoint y) = (m.epsP β).wt y
      ∧ (m.epsP (π β)).speed (flipPoint y) = (m.epsP β).speed y
      ∧ (y 2 ≠ 0 → (m.epsP (π β)).share1 (flipPoint y) = (m.epsP β).share1 y
        ∧ (m.epsP (π β)).share2 (flipPoint y) = (m.epsP β).share2 y
        ∧ (m.epsP (π β)).len (flipPoint y) = (m.epsP β).len y
        ∧ (m.epsP (π β)).t0 (flipPoint y) = (m.epsP β).t0 y
        ∧ (m.epsP (π β)).t1 (flipPoint y) = (m.epsP β).t1 y
        ∧ (m.epsP (π β)).t2 (flipPoint y) = (m.epsP β).t2 y
        ∧ (m.epsP (π β)).t3 (flipPoint y) = (m.epsP β).t3 y
        ∧ (m.epsP (π β)).scale (flipPoint y) = (m.epsP β).scale y)
  mu_mirror : ∃ π : Equiv.Perm (Fin nM), ∀ β,
    (m.muP (π β)).modes = flipLabel '' (m.muP β).modes ∧ (m.muP (π β)).frame = -(m.muP β).frame ∧
    (m.muP (π β)).eta = (m.muP β).eta ∧
    ∀ y, (m.muP (π β)).wt (flipPoint y) = (m.muP β).wt y
      ∧ (m.muP (π β)).speed (flipPoint y) = (m.muP β).speed y
      ∧ (y 2 ≠ 0 → (m.muP (π β)).share (flipPoint y) = (m.muP β).share y
        ∧ (m.muP (π β)).t4 (flipPoint y) = (m.muP β).t4 y)
  harmonics_flip : ∀ β ∈ h.harmonics, flipLabel β ∈ h.harmonics
  amplitudes_flip : ∀ β y, h.ampW (flipLabel β) (flipPoint y) = h.ampW β y
    ∧ h.ampGradW (flipLabel β) (flipPoint y) = h.ampGradW β y
    ∧ h.ampVort (flipLabel β) (flipPoint y) = h.ampVort β y
    ∧ h.ampGradVort (flipLabel β) (flipPoint y) = h.ampGradVort β y
  sups_flip : ∀ y, h.supVort (flipPoint y) = h.supVort y ∧ h.supGradVort (flipPoint y) = h.supGradVort y
  amplitudes_axi : ∀ β φ y, h.ampW β (axialRot φ y) = h.ampW β y
    ∧ h.ampGradW β (axialRot φ y) = h.ampGradW β y
    ∧ h.ampVort β (axialRot φ y) = h.ampVort β y
    ∧ h.ampGradVort β (axialRot φ y) = h.ampGradVort β y
  sups_axi : ∀ φ y, h.supVort (axialRot φ y) = h.supVort y ∧ h.supGradVort (axialRot φ y) = h.supGradVort y
  eps_speed_axi : ∀ β, IsAxisymmetric (m.epsP β).speed
  mu_speed_axi : ∀ β, IsAxisymmetric (m.muP β).speed

structure IsFlipInvariantModel (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : Prop where
  field_flip : ∀ σ y, W σ (flipPoint y) = flipPoint (W σ y)
  hessian_flip : ∀ σ y a b, HW σ (flipPoint y) (flipPoint a) (flipPoint b) = flipPoint (HW σ y a b)

def LabelArithmeticHolds : Prop :=
  ∀ m : ℕ, 1 ≤ m → Function.Injective (labelHarmonic m) ∧
    (∀ ι, labelHarmonic m (labelFlip ι) = flipLabel (labelHarmonic m ι)) ∧
    (∀ ι, labelHarmonic m (-ι) = -labelHarmonic m ι) ∧
    ∀ ξ : ℤ × ℤ, IsLatticeHarmonic m ξ ↔ ((m : ℤ) ∣ ξ.2 ∧ Even (ξ.1 + ξ.2 / m))

def VelocitySixthIntegralHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g →
      ∫⁻ σ in Set.Icc (0 : ℝ) 1, (∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6)) ^ ((1 : ℝ) / 6) < ⊤

def ModeShiftRotateHolds : Prop :=
  ∀ (v : ℝ → Space → Space), IsTimePeriodic v → ∀ (ξ : ℤ × ℤ) (σ s φ : ℝ) (y : Space),
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => v (σ + p.1) (axialRot p.2 y))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) →
    modeVel ξ v (σ + s) (axialRot φ y) = fun i =>
      Complex.exp (((2 * Real.pi * ξ.1 * s + ξ.2 * φ : ℝ) : ℂ) * Complex.I)
        * ∑ j : Fin 3, ((axialRot φ (unitVector j) i : ℝ) : ℂ) * modeVel ξ v σ y j

def ModeShiftRotateTensorHolds : Prop :=
  (∀ (G : ℝ → Space → (Space →L[ℝ] Space)), IsTimePeriodic G → ∀ (ξ : ℤ × ℤ) (σ s φ : ℝ) (y : Space),
    (∀ j : Fin 3, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => G (σ + p.1) (axialRot p.2 y) (axialRot p.2 (unitVector j)))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))) →
    modeGrad ξ G (σ + s) (axialRot φ y) = fun ij =>
      Complex.exp (((2 * Real.pi * ξ.1 * s + ξ.2 * φ : ℝ) : ℂ) * Complex.I)
        * ∑ a : Fin 3, ∑ b : Fin 3, ((axialRot φ (unitVector a) ij.1 * axialRot φ (unitVector b) ij.2 : ℝ) : ℂ)
          * modeGrad ξ G σ y (a, b)) ∧
  (∀ (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsTimePeriodic H → ∀ (ξ : ℤ × ℤ) (σ s φ : ℝ) (y : Space),
    (∀ j l : Fin 3, MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => H (σ + p.1) (axialRot p.2 y) (axialRot p.2 (unitVector j)) (axialRot p.2 (unitVector l)))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))) →
    modeSecondDeriv ξ H (σ + s) (axialRot φ y) = fun ijl =>
      Complex.exp (((2 * Real.pi * ξ.1 * s + ξ.2 * φ : ℝ) : ℂ) * Complex.I)
        * ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ((axialRot φ (unitVector a) ijl.1 * axialRot φ (unitVector b) ijl.2.1
            * axialRot φ (unitVector c) ijl.2.2 : ℝ) : ℂ) * modeSecondDeriv ξ H σ y (a, b, c))

def ModeConjugateHolds : Prop :=
  ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ξ : ℤ × ℤ) (σ : ℝ) (y : Space),
    modeVel (-ξ) v σ y = star (modeVel ξ v σ y) ∧ modeGrad (-ξ) G σ y = star (modeGrad ξ G σ y) ∧
      modeSecondDeriv (-ξ) H σ y = star (modeSecondDeriv ξ H σ y)

def ModeFlipHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → (∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) → ∀ ξ : ℤ × ℤ,
    ∀ᵐ z : ℝ × Space,
      modeVel (flipLabel ξ) v z.1 (flipPoint z.2) = (fun a => (frameSign a : ℂ) * modeVel ξ v z.1 z.2 a) ∧
      modeGrad (flipLabel ξ) G z.1 (flipPoint z.2)
        = (fun ab => ((frameSign ab.1 * frameSign ab.2 : ℝ) : ℂ) * modeGrad ξ G z.1 z.2 ab) ∧
      modeSecondDeriv (flipLabel ξ) H z.1 (flipPoint z.2)
        = (fun abc => ((frameSign abc.1 * frameSign abc.2.1 * frameSign abc.2.2 : ℝ) : ℂ)
            * modeSecondDeriv ξ H z.1 z.2 abc)

def ModeOffLatticeHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → ∀ α s : ℝ,
    (∀ᵐ z : ℝ × Space, v (z.1 + s) (axialRot α z.2) = axialRot α (v z.1 z.2)) → ∀ ξ : ℤ × ℤ,
    Complex.exp (((ξ.2 * α + 2 * Real.pi * ξ.1 * s : ℝ) : ℂ) * Complex.I) ≠ 1 →
    ∀ᵐ z : ℝ × Space, modeVel ξ v z.1 z.2 = 0 ∧ modeGrad ξ G z.1 z.2 = 0 ∧ modeSecondDeriv ξ H z.1 z.2 = 0

def ClassSupportHolds : Prop :=
  ∀ (Γ : Set Symmetry) (m : ℕ) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsModeClass Γ m → IsPerturbation Γ P v G H g → ∀ ξ : ℤ × ℤ, ¬ IsLatticeHarmonic m ξ →
    ∀ᵐ z : ℝ × Space, modeVel ξ v z.1 z.2 = 0 ∧ modeGrad ξ G z.1 z.2 = 0 ∧ modeSecondDeriv ξ H z.1 z.2 = 0

theorem classSupport_of_parts (hO : ModeOffLatticeHolds) (hL : LabelArithmeticHolds) :
    ClassSupportHolds := by
  intro Γ m P v G H g hC hP ξ hξ
  obtain ⟨γ, hγΓ, hγ1, hγ2⟩ := hC.twisted
  have hinv : ∀ᵐ z : ℝ × Space, v (z.1 + 1 / 2) (axialRot (Real.pi / m) z.2)
      = axialRot (Real.pi / m) (v z.1 z.2) := by
    filter_upwards [hP.invariant γ hγΓ] with z hz
    simpa only [hγ1, hγ2] using hz
  have hlat : (IsLatticeHarmonic m ξ ↔ ((m : ℤ) ∣ ξ.2 ∧ Even (ξ.1 + ξ.2 / m))) →
      Complex.exp (((ξ.2 * (Real.pi / m) + 2 * Real.pi * ξ.1 * (1 / 2) : ℝ) : ℂ) * Complex.I) = 1 →
      IsLatticeHarmonic m ξ := by
    intro hLm h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have hmR : (0 : ℝ) < m := by exact_mod_cast hC.order_pos
    have hc : (((ξ.2 * (Real.pi / m) + 2 * Real.pi * ξ.1 * (1 / 2) : ℝ) : ℂ))
        = (((n * (2 * Real.pi)) : ℝ) : ℂ) := by
      apply mul_right_cancel₀ Complex.I_ne_zero
      rw [hn]
      push_cast
      ring
    have hreal : (ξ.2 : ℝ) * (Real.pi / m) + 2 * Real.pi * ξ.1 * (1 / 2) = n * (2 * Real.pi) :=
      Complex.ofReal_injective hc
    have h3 : (ξ.2 : ℝ) / m + ξ.1 = 2 * n := by
      apply mul_left_cancel₀ Real.pi_ne_zero
      linear_combination hreal
    have h4 : (ξ.2 : ℝ) = m * (2 * n - ξ.1) := by
      have hsplit : (ξ.2 : ℝ) = ((ξ.2 : ℝ) / m) * m := (div_mul_cancel₀ _ hmR.ne').symm
      rw [hsplit, show (ξ.2 : ℝ) / m = 2 * n - ξ.1 by linarith]
      ring
    have h5 : ξ.2 = (m : ℤ) * (2 * n - ξ.1) := by exact_mod_cast h4
    have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hmR.ne'
    rw [hLm]
    refine ⟨⟨_, h5⟩, ?_⟩
    rw [h5, Int.mul_ediv_cancel_left _ hm0]
    exact ⟨n, by ring⟩
  refine hO Γ P v G H g hP (Real.pi / m) (1 / 2) hinv ξ ?_
  intro h1
  exact hξ (hlat ((hL m hC.order_pos).2.2.2 ξ) h1)

def HalfPlaneReductionHolds : Prop :=
  ∀ g : ℤ × ℤ → Space → ℝ≥0∞, (∀ ξ, AEMeasurable (g ξ)) →
    ∀ S : Set Space, (∀ φ y, axialRot φ y ∈ S ↔ y ∈ S) → (∀ᵐ y, y ∈ S) →
    (∀ ξ φ, ∀ y ∈ S, g ξ (axialRot φ y) = g ξ y) → (∀ ξ, ∀ᵐ y, g (flipLabel ξ) (flipPoint y) = g ξ y) →
    ∫⁻ y, ∑' ξ, g ξ y = ENNReal.ofReal (4 * Real.pi) * ∑' ξ, ∫⁻ p in halfPlane, g ξ (planePoint p) * ENNReal.ofReal p.1

def RotationAverageHolds : Prop :=
  ∀ f : Space → ℝ≥0∞, AEMeasurable f →
    ∫⁻ y, f y = ∫⁻ y, ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), f (axialRot φ y)

def hessFrobSq (A : Space →L[ℝ] Space →L[ℝ] Space) : ℝ :=
  ∑ j : Fin 3, ∑ l : Fin 3, ‖A (unitVector j) (unitVector l)‖ ^ 2

def HessianEnergyIdentityHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g →
      periodLIntegral (fun σ y => hessFrobSq (H σ y)) = periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2)

def ModeDensityBridgeHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (D₀ : ℝ),
    IsModeClass D.cert.symmetries D.azimuthOrder → IsFlipInvariantModel D.given D.givenHess →
    CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess D₀ →
    (∀ q ∈ D.cert.params, HasMeasurableBoundData (D.pieces q) (D.bounds q)) →
    (∀ q ∈ D.cert.params, IsFlipCompatible (D.pieces q) (D.bounds q) D.cert.weightFn) →
    ∀ q ∈ D.cert.params, (∃ e₁ e₂ e₃ : ℝ, CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q) (D.bounds q)
      D.cert.weightFn D.given D.givenHess D.cert.weight e₁ e₂ e₃) →
    ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, CoerciveWeak.densityPosWith (D.pieces q) (D.cert.period q) (D.bounds q)
          D.cert.weightFn v G H D.given D.givenHess σ y) = ENNReal.ofReal (4 * Real.pi) * D.formPos q v G H ∧
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, CoerciveWeak.densityNegWith (D.pieces q) (D.cert.period q) (D.bounds q)
          D.cert.weightFn v G H D.given D.givenHess σ y) = ENNReal.ofReal (4 * Real.pi) * D.formNeg q v G H

def ModeTermFlipHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ),
    IsFlipCompatible m h w →
    ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ξ : ℤ × ℤ) (σ : ℝ) (y : Space), y 2 ≠ 0 →
      modeVel (flipLabel ξ) v σ (flipPoint y) = (fun a => (frameSign a : ℂ) * modeVel ξ v σ y a) →
      modeGrad (flipLabel ξ) G σ (flipPoint y)
        = (fun ab => ((frameSign ab.1 * frameSign ab.2 : ℝ) : ℂ) * modeGrad ξ G σ y ab) →
      modeSecondDeriv (flipLabel ξ) H σ (flipPoint y)
        = (fun abc => ((frameSign abc.1 * frameSign abc.2.1 * frameSign abc.2.2 : ℝ) : ℂ) * modeSecondDeriv ξ H σ y abc) →
      m.modeTerm P h w v G H (flipLabel ξ) σ (flipPoint y) = m.modeTerm P h w v G H ξ σ y

def StretchFlipHolds : Prop :=
  ∀ (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsFlipInvariantModel W HW → (∀ σ, Differentiable ℝ (W σ)) →
    ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space),
      v σ (flipPoint y) = flipPoint (v σ y) → (∀ a, G σ (flipPoint y) (flipPoint a) = flipPoint (G σ y a)) →
      CoerciveWeak.stretchFormWith W HW v G σ (flipPoint y) = CoerciveWeak.stretchFormWith W HW v G σ y

def stretchBilin (gW : Fin 3 × Fin 3 → ℂ) (hW : Fin 3 × Fin 3 × Fin 3 → ℂ) (a : Fin 3 → ℂ)
    (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) : ℂ :=
  -(∑ i : Fin 3, ∑ j : Fin 3, curlOfGrad g i * ((gW (i, j) + gW (j, i)) / 2) * curlOfGrad g' j)
    + ∑ j : Fin 3, (∑ l : Fin 3, a l * curlGradOfSecondDeriv hW (j, l)) * curlOfGrad g' j
    + (1 / 2 : ℂ) * ∑ i : Fin 3, ∑ l : Fin 3, ∑ n : Fin 3, ∑ j : Fin 3,
        (alternatingSymbol i l n : ℂ) * curlGradOfSecondDeriv hW (j, l) * g (i, j) * a' n

def stretchTriple (gW : Fin 3 × Fin 3 → ℂ) (hW : Fin 3 × Fin 3 × Fin 3 → ℂ) (a : Fin 3 → ℂ)
    (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) : ℂ :=
  (stretchBilin gW hW a g a' g' + stretchBilin gW hW a' g' a g) / 2

def MeanStretchModeSumHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (D₀ : ℝ),
    CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess D₀ →
    IsHarmonicExpansion D.givenLabels D.given D.givenHess →
    ∀ (Γ : Set Symmetry) (P : ℝ) v G H g, IsPerturbation Γ P v G H g →
    ∀ᵐ p ∂(volume.restrict halfPlane),
      (∀ β ∈ D.givenLabels, Summable (fun ξ : ℤ × ℤ =>
        ‖stretchTriple (modeGrad β (gradField D.given) 0 (planePoint p)) (modeSecondDeriv β D.givenHess 0 (planePoint p))
          (modeVel ξ v 0 (planePoint p)) (modeGrad ξ G 0 (planePoint p))
          (star (modeVel (ξ + β) v 0 (planePoint p))) (star (modeGrad (ξ + β) G 0 (planePoint p)))‖)) ∧
      D.meanStretch v G p = ∑ β ∈ D.givenLabels, ∑' ξ : ℤ × ℤ,
        (stretchTriple (modeGrad β (gradField D.given) 0 (planePoint p)) (modeSecondDeriv β D.givenHess 0 (planePoint p))
          (modeVel ξ v 0 (planePoint p)) (modeGrad ξ G 0 (planePoint p))
          (star (modeVel (ξ + β) v 0 (planePoint p))) (star (modeGrad (ξ + β) G 0 (planePoint p)))).re

def StretchMeanIntegralHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (D₀ : ℝ),
    IsModeClass D.cert.symmetries D.azimuthOrder → IsFlipInvariantModel D.given D.givenHess →
    CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess D₀ →
    ∀ (P : ℝ) v G H g, IsPerturbation D.cert.symmetries P v G H g →
      MeasureTheory.Integrable (fun z : ℝ × Space => CoerciveWeak.stretchFormWith D.given D.givenHess v G z.1 z.2)
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) ∧
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => D.meanStretch v G p * p.1) halfPlane ∧
      (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, CoerciveWeak.stretchFormWith D.given D.givenHess v G σ y)
        = 4 * Real.pi * ∫ p in halfPlane, D.meanStretch v G p * p.1

def crossCharge (σc γc ℓ : ℝ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) : ℝ :=
  σc * cnormSq (curlOfGrad g) + 3 / (2 * Real.sqrt 2) * γc * (ℓ * cnormSq g + cnormSq a / ℓ)

def StretchTripleBoundHolds : Prop :=
  ∀ (gW : Fin 3 × Fin 3 → ℂ) (hW : Fin 3 × Fin 3 × Fin 3 → ℂ) (σc γc : ℝ), 0 ≤ σc → 0 ≤ γc →
    (∀ u : Fin 3 → ℂ, cnormSq (fun i => ∑ j : Fin 3, ((gW (i, j) + gW (j, i)) / 2) * u j) ≤ σc ^ 2 * cnormSq u) →
    (∀ u : Fin 3 → ℂ, cnormSq (fun j => ∑ l : Fin 3, curlGradOfSecondDeriv hW (j, l) * u l) ≤ γc ^ 2 * cnormSq u) →
    ∀ a g a' g', ‖stretchTriple gW hW a g a' g'‖ ≤
      σc * Real.sqrt (cnormSq (curlOfGrad g)) * Real.sqrt (cnormSq (curlOfGrad g'))
        + 3 / (2 * Real.sqrt 2) * γc * (Real.sqrt (cnormSq a) * Real.sqrt (cnormSq g')
          + Real.sqrt (cnormSq a') * Real.sqrt (cnormSq g))

def CrossWaveBoundHolds : Prop :=
  ∀ (m : ℕ) (A A' B : Finset ℤ) (x x' : ℤ → (Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ))
    (wg : ℤ → Fin 3 × Fin 3 → ℂ) (wh : ℤ → Fin 3 × Fin 3 × Fin 3 → ℂ) (σc γc ℓ βc : ℝ),
    1 ≤ m → 0 ≤ σc → 0 ≤ γc → 0 < ℓ → 0 < βc →
    (∀ θ (u : Fin 3 → ℂ), cnormSq (fun i => ∑ j : Fin 3,
        (∑ n ∈ B, azimuthPhase m n θ * ((wg n (i, j) + wg n (j, i)) / 2)) * u j) ≤ σc ^ 2 * cnormSq u) →
    (∀ θ (u : Fin 3 → ℂ), cnormSq (fun j => ∑ l : Fin 3,
        (∑ n ∈ B, azimuthPhase m n θ * curlGradOfSecondDeriv (wh n) (j, l)) * u l) ≤ γc ^ 2 * cnormSq u) →
    2 * ‖∑ n ∈ B, ∑ n₁ ∈ A, ∑ n₂ ∈ A', if n + n₁ = n₂ then
        stretchTriple (wg n) (wh n) (x n₁).1 (x n₁).2 (star (x' n₂).1) (star (x' n₂).2) else 0‖
      ≤ βc * ∑ n₁ ∈ A, crossCharge σc γc ℓ (x n₁).1 (x n₁).2
        + βc⁻¹ * ∑ n₂ ∈ A', crossCharge σc γc ℓ (x' n₂).1 (x' n₂).2

def upperTrace (f fz : ℝ → ℂ) (h : ℝ) : ℂ :=
  -∫ z in (0 : ℝ)..h, (fz z * ((1 - z / h : ℝ) : ℂ) - f z / (h : ℂ))

def lowerTrace (f fz : ℝ → ℂ) (h : ℝ) : ℂ :=
  ∫ z in (-h)..0, (fz z * ((1 + z / h : ℝ) : ℂ) + f z / (h : ℂ))

def HasWeakDerivOn (f fz : ℝ → ℂ) (a b : ℝ) : Prop :=
  MeasureTheory.IntegrableOn f (Set.Ioo a b) ∧ MeasureTheory.IntegrableOn fz (Set.Ioo a b) ∧
    ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo a b →
      ∫ z in Set.Ioo a b, f z * Complex.ofReal (deriv ψ z) = -∫ z in Set.Ioo a b, fz z * Complex.ofReal (ψ z)

def TraceFlipHolds : Prop :=
  ∀ (f fz : ℝ → ℂ) (h : ℝ) (s : ℂ),
    upperTrace (fun z => s * f (-z)) (fun z => -(s * fz (-z))) h = s * lowerTrace f fz h

def TraceMatchHolds : Prop :=
  ∀ (f fz : ℝ → ℂ) (h : ℝ), 0 < h → HasWeakDerivOn f fz (-(2 * h)) (2 * h) →
    upperTrace f fz h = lowerTrace f fz h

def TraceHeightHolds : Prop :=
  ∀ (f fz : ℝ → ℂ) (h h' : ℝ), 0 < h → h ≤ h' → HasWeakDerivOn f fz (-(2 * h')) (2 * h') →
    upperTrace f fz h = upperTrace f fz h'

def planeVel (ξ : ℤ × ℤ) (v : ℝ → Space → Space) (a : Fin 3) (r : ℝ) : ℝ → ℂ :=
  fun z => modeVel ξ v 0 (planePoint (r, z)) a

def planeVelHeight (ξ : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (a : Fin 3) (r : ℝ) : ℝ → ℂ :=
  fun z => modeGrad ξ G 0 (planePoint (r, z)) (a, 2)

def planeVelHeight2 (ξ : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a : Fin 3) (r : ℝ) :
    ℝ → ℂ :=
  fun z => modeSecondDeriv ξ H 0 (planePoint (r, z)) (a, 2, 2)

def planeScalar (ξ : ℤ × ℤ) (q : ℝ → Space → ℝ) (r : ℝ) : ℝ → ℂ :=
  fun z => modeAverage ξ (fun τ φ (_ : Unit) => q τ (axialRot φ (planePoint (r, z)))) ()

def planeScalarHeight (ξ : ℤ × ℤ) (dq : ℝ → Space → Space) (r : ℝ) : ℝ → ℂ :=
  fun z => modeAverage ξ (fun τ φ (_ : Unit) => dq τ (axialRot φ (planePoint (r, z))) 2) ()

def StripMomentTraceHolds : Prop :=
  ∀ (h lo hi : ℝ) (wt t : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ), 0 < h → lo < hi →
    MeasureTheory.IntegrableOn F (Set.Icc lo hi ×ˢ Set.Icc 0 h) →
    MeasureTheory.IntegrableOn dF (Set.Icc lo hi ×ˢ Set.Icc 0 h) →
    Continuous wt → Continuous t →
    CellCert.CellFormula.heightStripMoment 0 h lo hi wt F dF t
      = ∫ r in lo..hi, ((wt r * t r : ℝ) : ℂ) * upperTrace (fun z => F (r, z)) (fun z => dF (r, z)) h

def HasWeakPlaneDerivsOn (F Fr Fz Frz : ℝ × ℝ → ℂ) (R : Set (ℝ × ℝ)) : Prop :=
  MeasureTheory.IntegrableOn F R ∧ MeasureTheory.IntegrableOn Fr R ∧ MeasureTheory.IntegrableOn Fz R ∧
    MeasureTheory.IntegrableOn Frz R ∧
    ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ interior R →
      (∫ p in R, F p * Complex.ofReal (fderiv ℝ ψ p (1, 0)) = -∫ p in R, Fr p * Complex.ofReal (ψ p)) ∧
      (∫ p in R, F p * Complex.ofReal (fderiv ℝ ψ p (0, 1)) = -∫ p in R, Fz p * Complex.ofReal (ψ p)) ∧
      (∫ p in R, Fr p * Complex.ofReal (fderiv ℝ ψ p (0, 1)) = -∫ p in R, Frz p * Complex.ofReal (ψ p))

def CornerFlipHolds : Prop :=
  ∀ (F Fr Fz Frz : ℝ × ℝ → ℂ) (cr orr h : ℝ) (s : ℂ),
    CellCert.CellFormula.cornerMoment cr orr 0 h (fun p => s * F (p.1, -p.2)) (fun p => s * Fr (p.1, -p.2))
        (fun p => -(s * Fz (p.1, -p.2))) (fun p => -(s * Frz (p.1, -p.2)))
      = s * CellCert.CellFormula.cornerMoment cr orr 0 (-h) F Fr Fz Frz

def CornerMatchHolds : Prop :=
  ∀ (F Fr Fz Frz : ℝ × ℝ → ℂ) (cr orr h lo hi : ℝ), cr ≠ orr → 0 < h → lo < min cr orr → max cr orr < hi →
    HasWeakPlaneDerivsOn F Fr Fz Frz (Set.Icc lo hi ×ˢ Set.Icc (-(2 * h)) (2 * h)) →
    CellCert.CellFormula.cornerMoment cr orr 0 h F Fr Fz Frz = CellCert.CellFormula.cornerMoment cr orr 0 (-h) F Fr Fz Frz

def CornerTraceHolds : Prop :=
  ∀ (F Fr Fz Frz : ℝ × ℝ → ℂ) (cr orr h : ℝ), cr ≠ orr → 0 < h →
    MeasureTheory.IntegrableOn F (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc 0 h) →
    MeasureTheory.IntegrableOn Fr (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc 0 h) →
    MeasureTheory.IntegrableOn Fz (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc 0 h) →
    MeasureTheory.IntegrableOn Frz (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc 0 h) →
    CellCert.CellFormula.cornerMoment cr orr 0 h F Fr Fz Frz
      = CellCert.CellFormula.edgeSign cr orr * ∫ r in Set.Icc (min cr orr) (max cr orr),
          ((((1 / (cr - orr) : ℝ)) : ℂ) * upperTrace (fun z => F (r, z)) (fun z => Fz (r, z)) h
            + (((r - orr) / (cr - orr) : ℝ) : ℂ) * upperTrace (fun z => Fr (r, z)) (fun z => Frz (r, z)) h)

def ModeHeightDerivHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → ∀ (ξ : ℤ × ℤ) (a : Fin 3),
    ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ h : ℝ, 0 < h →
      HasWeakDerivOn (planeVel ξ v a r) (planeVelHeight ξ G a r) (-h) h ∧
      HasWeakDerivOn (planeVelHeight ξ G a r) (planeVelHeight2 ξ H a r) (-h) h ∧
      HasWeakDerivOn (fun z => modeGrad ξ G 0 (planePoint (r, z)) (a, 0))
        (fun z => modeSecondDeriv ξ H 0 (planePoint (r, z)) (a, 0, 2)) (-h) h

def PlaneDataFlipHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → (∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) →
    ∀ (ξ : ℤ × ℤ) (a : Fin 3), ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ h : ℝ, 0 < h →
      upperTrace (planeVel (flipLabel ξ) v a r) (planeVelHeight (flipLabel ξ) G a r) h
          = (frameSign a : ℂ) * upperTrace (planeVel ξ v a r) (planeVelHeight ξ G a r) h ∧
      upperTrace (planeVelHeight (flipLabel ξ) G a r) (planeVelHeight2 (flipLabel ξ) H a r) h
          = -((frameSign a : ℂ) * upperTrace (planeVelHeight ξ G a r) (planeVelHeight2 ξ H a r) h)

def planeVelRadial (ξ : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (a : Fin 3) : ℝ × ℝ → ℂ :=
  fun p => modeGrad ξ G 0 (planePoint p) (a, 0)

def planeVelMixed (ξ : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a : Fin 3) : ℝ × ℝ → ℂ :=
  fun p => modeSecondDeriv ξ H 0 (planePoint p) (a, 0, 2)

def StripDataFlipHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → (∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) →
    ∀ (ξ : ℤ × ℤ) (a : Fin 3) (lo hi h h' : ℝ) (wt t : ℝ → ℝ),
      0 < lo → lo < hi → 0 < h → 0 < h' → Continuous wt → Continuous t →
      CellCert.CellFormula.heightStripMoment 0 h lo hi wt (fun p => planeVel (flipLabel ξ) v a p.1 p.2)
          (fun p => planeVelHeight (flipLabel ξ) G a p.1 p.2) t
        = (frameSign a : ℂ) * CellCert.CellFormula.heightStripMoment 0 h' lo hi wt
          (fun p => planeVel ξ v a p.1 p.2) (fun p => planeVelHeight ξ G a p.1 p.2) t ∧
      CellCert.CellFormula.heightStripMoment 0 h lo hi wt (fun p => planeVelHeight (flipLabel ξ) G a p.1 p.2)
          (fun p => planeVelHeight2 (flipLabel ξ) H a p.1 p.2) t
        = -((frameSign a : ℂ) * CellCert.CellFormula.heightStripMoment 0 h' lo hi wt
          (fun p => planeVelHeight ξ G a p.1 p.2) (fun p => planeVelHeight2 ξ H a p.1 p.2) t)

def CornerDataFlipHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → (∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) →
    ∀ (ξ : ℤ × ℤ) (a : Fin 3) (cr orr h h' : ℝ), 0 < cr → 0 < orr → cr ≠ orr → 0 < h → 0 < h' →
      CellCert.CellFormula.cornerMoment cr orr 0 h (fun p => planeVel (flipLabel ξ) v a p.1 p.2)
          (planeVelRadial (flipLabel ξ) G a) (fun p => planeVelHeight (flipLabel ξ) G a p.1 p.2)
          (planeVelMixed (flipLabel ξ) H a)
        = (frameSign a : ℂ) * CellCert.CellFormula.cornerMoment cr orr 0 h' (fun p => planeVel ξ v a p.1 p.2)
          (planeVelRadial ξ G a) (fun p => planeVelHeight ξ G a p.1 p.2) (planeVelMixed ξ H a)

def ScalarPlaneFlipHolds : Prop :=
  ∀ (q : ℝ → Space → ℝ) (dq : ℝ → Space → Space),
    AEStronglyMeasurable (fun z : ℝ × Space => q z.1 z.2) volume →
    AEStronglyMeasurable (fun z : ℝ × Space => dq z.1 z.2) volume → IsTimePeriodic q → IsTimePeriodic dq →
    (∀ᵐ σ, IsWeakGradient (fun y => q σ y • unitVector 0) (fun y => (innerSL ℝ (dq σ y)).smulRight (unitVector 0))) →
    (∀ R : ℝ, periodLIntegral (fun σ y => if ‖y‖ ≤ R then q σ y ^ 2 + ‖dq σ y‖ ^ 2 else 0) < ⊤) →
    (∀ᵐ z : ℝ × Space, q z.1 (flipPoint z.2) = q z.1 z.2) →
    ∀ ξ : ℤ × ℤ, ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ h : ℝ, 0 < h →
      upperTrace (planeScalar (flipLabel ξ) q r) (planeScalarHeight (flipLabel ξ) dq r) h
        = upperTrace (planeScalar ξ q r) (planeScalarHeight ξ dq r) h

def ScalarHeightDerivHolds : Prop :=
  ∀ (q : ℝ → Space → ℝ) (dq : ℝ → Space → Space),
    AEStronglyMeasurable (fun z : ℝ × Space => q z.1 z.2) volume →
    AEStronglyMeasurable (fun z : ℝ × Space => dq z.1 z.2) volume → IsTimePeriodic q → IsTimePeriodic dq →
    (∀ᵐ σ, IsWeakGradient (fun y => q σ y • unitVector 0) (fun y => (innerSL ℝ (dq σ y)).smulRight (unitVector 0))) →
    (∀ R : ℝ, periodLIntegral (fun σ y => if ‖y‖ ≤ R then q σ y ^ 2 + ‖dq σ y‖ ^ 2 else 0) < ⊤) →
    (∀ᵐ z : ℝ × Space, q z.1 (flipPoint z.2) = q z.1 z.2) →
    ∀ ξ : ℤ × ℤ, ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ h : ℝ, 0 < h →
      HasWeakDerivOn (planeScalar ξ q r) (planeScalarHeight ξ dq r) (-h) h

def StripScalarFlipHolds : Prop :=
  ∀ (q : ℝ → Space → ℝ) (dq : ℝ → Space → Space),
    AEStronglyMeasurable (fun z : ℝ × Space => q z.1 z.2) volume →
    AEStronglyMeasurable (fun z : ℝ × Space => dq z.1 z.2) volume → IsTimePeriodic q → IsTimePeriodic dq →
    (∀ᵐ σ, IsWeakGradient (fun y => q σ y • unitVector 0) (fun y => (innerSL ℝ (dq σ y)).smulRight (unitVector 0))) →
    (∀ R : ℝ, periodLIntegral (fun σ y => if ‖y‖ ≤ R then q σ y ^ 2 + ‖dq σ y‖ ^ 2 else 0) < ⊤) →
    (∀ᵐ z : ℝ × Space, q z.1 (flipPoint z.2) = q z.1 z.2) →
    ∀ (ξ : ℤ × ℤ) (lo hi h h' : ℝ) (wt t : ℝ → ℝ),
      0 < lo → lo < hi → 0 < h → 0 < h' → Continuous wt → Continuous t →
      CellCert.CellFormula.heightStripMoment 0 h lo hi wt (fun p => planeScalar (flipLabel ξ) q p.1 p.2)
          (fun p => planeScalarHeight (flipLabel ξ) dq p.1 p.2) t
        = CellCert.CellFormula.heightStripMoment 0 h' lo hi wt (fun p => planeScalar ξ q p.1 p.2)
          (fun p => planeScalarHeight ξ dq p.1 p.2) t

def PlaneDataRealityHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → (∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) →
    ∀ (ξ : ℤ × ℤ) (a : Fin 3), ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ h : ℝ, 0 < h →
      (ξ.1 = 0 → (starRingEnd ℂ) (upperTrace (planeVel ξ v a r) (planeVelHeight ξ G a r) h)
          = (frameSign a : ℂ) * upperTrace (planeVel ξ v a r) (planeVelHeight ξ G a r) h) ∧
      (ξ.2 = 0 → a ≠ 0 → upperTrace (planeVel ξ v a r) (planeVelHeight ξ G a r) h = 0) ∧
      (ξ.2 = 0 → a = 0 → upperTrace (planeVelHeight ξ G a r) (planeVelHeight2 ξ H a r) h = 0)

theorem planeDataReality_of_parts (hP : PlaneDataFlipHolds) (hC : ModeConjugateHolds) (hF : TraceFlipHolds) :
    PlaneDataRealityHolds := by
  have hconj : ∀ (f fz : ℝ → ℂ) (t : ℝ),
      upperTrace (fun z => starRingEnd ℂ (f z)) (fun z => starRingEnd ℂ (fz z)) t
        = starRingEnd ℂ (upperTrace f fz t) := by
    intro f fz t
    unfold upperTrace
    rw [map_neg, ← intervalIntegral.intervalIntegral_conj]
    congr 1
    refine intervalIntegral.integral_congr fun z _ => ?_
    simp only [map_sub, map_mul, map_div₀, Complex.conj_ofReal]
  intro Γ P v G H g hpert hflip ξ a
  filter_upwards [hP Γ P v G H g hpert hflip ξ a] with r hr h hh
  obtain ⟨h1, h2⟩ := hr h hh
  refine ⟨fun h0 => ?_, fun h0 ha => ?_, fun h0 ha => ?_⟩
  · have hl : flipLabel ξ = -ξ := by
      ext <;> simp [flipLabel, h0]
    have hv : planeVel (-ξ) v a r = fun z => starRingEnd ℂ (planeVel ξ v a r z) := by
      funext z
      simp only [planeVel, (hC v G H ξ 0 (planePoint (r, z))).1, Pi.star_apply]
      rfl
    have hw : planeVelHeight (-ξ) G a r = fun z => starRingEnd ℂ (planeVelHeight ξ G a r z) := by
      funext z
      simp only [planeVelHeight, (hC v G H ξ 0 (planePoint (r, z))).2.1, Pi.star_apply]
      rfl
    rw [hl, hv, hw, hconj] at h1
    exact h1
  · have hl : flipLabel ξ = ξ := by
      ext <;> simp [flipLabel, h0]
    have hs : (frameSign a : ℂ) = -1 := by
      simp [frameSign, ha]
    rw [hl, hs] at h1
    linear_combination h1 / 2
  · have hl : flipLabel ξ = ξ := by
      ext <;> simp [flipLabel, h0]
    have hs : (frameSign a : ℂ) = 1 := by
      simp [frameSign, ha]
    rw [hl, hs] at h2
    linear_combination h2 / 2

def patchTrace (ξ : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (ρ₁ ρ₂ h : ℝ) (φ : ℝ × ℝ → ℂ) : ℂ :=
  ∫ r in ρ₁..ρ₂, upperTrace (planeVel ξ v 2 r) (planeVelHeight ξ G 2 r) h * φ (r, 0) * (r : ℂ)

def PatchTraceBoundHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → (∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) →
    ∀ (ξ : ℤ × ℤ) (ρ₁ ρ₂ h : ℝ) (b : ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (K : NNReal),
      0 < ρ₁ → ρ₁ < ρ₂ → 0 < h → Measurable b → (∃ b₀ > 0, ∀ p, b₀ ≤ b p) → (∃ b₁, ∀ p, b p ≤ b₁) →
      LipschitzWith K φ → (∀ z, φ (ρ₁, z) = 0 ∧ φ (ρ₂, z) = 0) → (∀ r, φ (r, h) = 0) →
      ‖patchTrace ξ v G ρ₁ ρ₂ h φ‖ ^ 2 ≤
        (∫ p in patch ρ₁ ρ₂ h, b p * cnormSq (modeVel (flipLabel ξ) v 0 (planePoint p)) * p.1)
          * ∫ p in patch ρ₁ ρ₂ h, patchGradSq ξ.2 φ p / b p * p.1

def PatchCreditHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → (∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) →
    ∀ (ξ : ℤ × ℤ) (ρ₁ ρ₂ h : ℝ) (b : ℝ × ℝ → ℝ) {N : ℕ} (φ : Fin N → ℝ × ℝ → ℝ) (K : NNReal)
      (Gp : Matrix (Fin N) (Fin N) ℝ),
      0 < ρ₁ → ρ₁ < ρ₂ → 0 < h → Measurable b → (∃ b₀ > 0, ∀ p, b₀ ≤ b p) → (∃ b₁, ∀ p, b p ≤ b₁) →
      (∀ i, LipschitzWith K (φ i)) → (∀ i z, φ i (ρ₁, z) = 0 ∧ φ i (ρ₂, z) = 0) → (∀ i r, φ i (r, h) = 0) →
      Gp.PosDef →
      (∀ c : Fin N → ℂ, ∫ p in patch ρ₁ ρ₂ h,
          patchGradSq ξ.2 (fun p => ∑ i, (starRingEnd ℂ) (c i) * (φ i p : ℂ)) p / b p * p.1
        ≤ Coupling.realQuadForm Gp c) →
      Coupling.realQuadForm Gp⁻¹ (fun i => patchTrace ξ v G ρ₁ ρ₂ h (fun p => (φ i p : ℂ)))
        ≤ ∫ p in patch ρ₁ ρ₂ h, b p * cnormSq (modeVel (flipLabel ξ) v 0 (planePoint p)) * p.1

def PairingModeIdentityHolds : Prop :=
  ∀ (A B : ℝ → Space → (Space →L[ℝ] Space)),
    AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) volume →
    AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2) volume →
    IsTimePeriodic A → IsTimePeriodic B →
    periodLIntegral (fun σ y => matSq (A σ y)) < ⊤ → periodLIntegral (fun σ y => matSq (B σ y)) < ⊤ →
    Summable (fun ξ : ℤ × ℤ => ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (cdotMat (modeGrad ξ A σ y) (modeGrad ξ B σ y)).re) ∧
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, matInner (A σ y) (B σ y)
      = ∑' ξ : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (cdotMat (modeGrad ξ A σ y) (modeGrad ξ B σ y)).re

def PinHalfPlaneHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM),
    IsModeClass D.cert.symmetries D.azimuthOrder →
    (∀ i, ∀ γ ∈ D.cert.symmetries, ∀ σ y a, D.cert.pin i (σ + γ.2) (γ.1 y) (γ.1 a) = γ.1 (D.cert.pin i σ y a)) →
    (∀ i, AEStronglyMeasurable (fun z : ℝ × Space => D.cert.pin i z.1 z.2) volume) →
    (∀ i, IsTimePeriodic (D.cert.pin i)) →
    (∀ i, periodLIntegral (fun σ y => matSq (D.cert.pin i σ y)) < ⊤) →
    ∀ (P : ℝ) v G H g, IsPerturbation D.cert.symmetries P v G H g → ∀ i,
      pinValue (D.cert.pin i) G = 4 * Real.pi * ∑' ι : ℤ × ℤ, ∫ p in halfPlane,
        (cdotMat (labelGrad D.azimuthOrder ι G p) (labelGrad D.azimuthOrder ι (D.cert.pin i) p)).re * p.1

def PlaneSegment.velocityData (S : PlaneSegment) (ξ : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (a : Fin 3) (j : Fin S.testCount) : ℂ :=
  CellCert.CellFormula.heightStripMoment 0 S.height S.lower S.upper (fun _ => 1)
    (fun p => planeVel ξ v a p.1 p.2) (fun p => planeVelHeight ξ G a p.1 p.2) (S.test j)

structure PatchEntry where
  label : ℤ × ℤ
  inner : ℝ
  outer : ℝ
  height : ℝ
  charge : ℝ × ℝ → ℝ
  chargeLower : ℝ
  chargeUpper : ℝ
  testCount : ℕ
  test : Fin testCount → ℝ × ℝ → ℝ
  testSlope : NNReal
  testForm : Matrix (Fin testCount) (Fin testCount) ℝ
  segmentCount : ℕ
  segment : Fin segmentCount → PlaneSegment
  dataCount : ℕ
  dataOf : Fin dataCount → (Σ s : Fin segmentCount, Fin (segment s).testCount)
  traceMap : Matrix (Fin testCount) (Fin dataCount) ℝ
  factorRows : ℕ
  factor : Matrix (Fin factorRows) (Fin testCount) ℝ
  factorSlack : ℝ
  credit : Matrix (Fin dataCount) (Fin dataCount) ℂ

namespace PatchEntry

variable (R : PatchEntry)

def data (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) : Fin R.dataCount → ℂ :=
  fun d => (R.segment (R.dataOf d).1).velocityData R.label v G 2 (R.dataOf d).2

def testCombination (c : Fin R.testCount → ℂ) : ℝ × ℝ → ℂ :=
  fun p => ∑ i, (starRingEnd ℂ) (c i) * (R.test i p : ℂ)

end PatchEntry

structure IsPatchEntry (R : PatchEntry) : Prop where
  inner_pos : 0 < R.inner
  inner_lt_outer : R.inner < R.outer
  height_pos : 0 < R.height
  charge_measurable : Measurable R.charge
  charge_lower_pos : 0 < R.chargeLower
  charge_between : ∀ p, R.chargeLower ≤ R.charge p ∧ R.charge p ≤ R.chargeUpper
  test_slope_bound : ∀ i, LipschitzWith R.testSlope (R.test i)
  test_sides : ∀ i z, R.test i (R.inner, z) = 0 ∧ R.test i (R.outer, z) = 0
  test_top : ∀ i r, R.test i (r, R.height) = 0
  segments : ∀ s, IsPlaneSegment (R.segment s)
  segments_cover : ∀ r, R.inner ≤ r → r ≤ R.outer →
    ∃ s, (R.segment s).lower ≤ r ∧ r ≤ (R.segment s).upper
  segments_disjoint : ∀ s s', s ≠ s' → (R.segment s).upper ≤ (R.segment s').lower ∨
    (R.segment s').upper ≤ (R.segment s).lower
  segments_inside : ∀ s, R.inner ≤ (R.segment s).lower ∧ (R.segment s).upper ≤ R.outer
  trace_expansion : ∀ i s r, (R.segment s).lower ≤ r → r ≤ (R.segment s).upper →
    r * R.test i (r, 0) = ∑ d, (if (R.dataOf d).1 = s then R.traceMap i d * (R.segment (R.dataOf d).1).test (R.dataOf d).2 r else 0)
  form_posDef : R.testForm.PosDef
  form_bound : ∀ c : Fin R.testCount → ℂ,
    ∫ p in patch R.inner R.outer R.height, patchGradSq R.label.2 (R.testCombination c) p / R.charge p * p.1
      ≤ Coupling.realQuadForm R.testForm c
  slack_nonneg : 0 ≤ R.factorSlack
  factor_bound : ((1 + R.factorSlack) • (1 : Matrix (Fin R.factorRows) (Fin R.factorRows) ℝ)
    - R.factor * R.testForm * R.factorᵀ).PosSemidef
  credit_le : ∀ g : Fin R.dataCount → ℂ, Coupling.quadForm R.credit g
    ≤ Coupling.realQuadForm ((R.factor * R.traceMap)ᵀ * (R.factor * R.traceMap)) g / (1 + R.factorSlack)

def PatchEntryCreditHolds : Prop :=
  ∀ (R : PatchEntry), IsPatchEntry R →
    ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
      IsPerturbation Γ P v G H g → (∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) →
      Coupling.quadForm R.credit (R.data v G)
        ≤ ∫ p in patch R.inner R.outer R.height, R.charge p * cnormSq (modeVel (flipLabel R.label) v 0 (planePoint p)) * p.1

structure SourceEntry where
  groupCount : ℕ
  share : Fin groupCount → ℝ
  portDim : ℕ
  sourceDim : ℕ
  port : Fin groupCount → Matrix (Fin sourceDim) (Fin portDim) ℂ

structure IsSourceEntry (S : SourceEntry) : Prop where
  share_pos : ∀ j, 0 < S.share j
  share_sum_le : ∑ j, S.share j ≤ 1
  port_sum : ∑ j, S.port j = 0

structure ClosedPlaneEntry where
  pairCount : ℕ
  partner : Fin pairCount → Fin pairCount
  dataDim : ℕ
  sign : Fin dataDim → ℝ
  weight : Fin pairCount → Matrix (Fin dataDim) (Fin dataDim) ℂ

structure IsClosedPlaneEntry (Q : ClosedPlaneEntry) : Prop where
  partner_involutive : ∀ i, Q.partner (Q.partner i) = i
  sign_sq : ∀ a, Q.sign a ^ 2 = 1
  weight_partner : ∀ i, Q.weight (Q.partner i) = -(Coupling.signDiag Q.sign * Q.weight i * Coupling.signDiag Q.sign)

structure CouplingEntry where
  patchCount : ℕ
  patches : Fin patchCount → PatchEntry
  sourceCount : ℕ
  sources : Fin sourceCount → SourceEntry
  crossCount : ℕ
  crosses : Fin crossCount → CrossWaveEntry
  closedPlanes : ClosedPlaneEntry
  pinWeight : ℝ

structure IsCouplingEntry {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CouplingEntry) : Prop where
  mode_class : IsModeClass D.cert.symmetries D.azimuthOrder
  model_flip : IsFlipInvariantModel D.given D.givenHess
  pieces_flip : ∀ q ∈ D.cert.params, IsFlipCompatible (D.pieces q) (D.bounds q) D.cert.weightFn
  model_harmonics : IsHarmonicExpansion D.givenLabels D.given D.givenHess
  model_state : ∃ D₀ : ℝ, CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess D₀
  bounds_measurable : ∀ q ∈ D.cert.params, HasMeasurableBoundData (D.pieces q) (D.bounds q)
  patches : ∀ i, IsPatchEntry (R.patches i)
  sources : ∀ i, IsSourceEntry (R.sources i)
  crosses : ∀ i, IsCrossWaveEntry (R.crosses i) ∧ (R.crosses i).azimuthOrder = D.azimuthOrder
  closed_planes : IsClosedPlaneEntry R.closedPlanes
  pinWeight_pos : 0 < R.pinWeight

def CouplingEntryHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CouplingEntry),
    IsCouplingEntry D R →
    (∀ q ∈ D.cert.params, (∃ e₁ e₂ e₃ : ℝ, CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q) (D.bounds q)
        D.cert.weightFn D.given D.givenHess D.cert.weight e₁ e₂ e₃) →
      ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
        (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, CoerciveWeak.densityPosWith (D.pieces q) (D.cert.period q) (D.bounds q)
            D.cert.weightFn v G H D.given D.givenHess σ y) = ENNReal.ofReal (4 * Real.pi) * D.formPos q v G H ∧
        (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, CoerciveWeak.densityNegWith (D.pieces q) (D.cert.period q) (D.bounds q)
            D.cert.weightFn v G H D.given D.givenHess σ y) = ENNReal.ofReal (4 * Real.pi) * D.formNeg q v G H ∧
        ∀ i, Coupling.quadForm (R.patches i).credit ((R.patches i).data v G)
          ≤ ∫ p in patch (R.patches i).inner (R.patches i).outer (R.patches i).height,
              (R.patches i).charge p * cnormSq (modeVel (flipLabel (R.patches i).label) v 0 (planePoint p)) * p.1) ∧
    ∀ i, ∀ p ∈ (R.crosses i).region, ∀ (A A' : Finset ℤ) (x x' : ℤ → (Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ)),
      2 * ‖∑ n ∈ (R.crosses i).waveModes, ∑ n₁ ∈ A, ∑ n₂ ∈ A', if n + n₁ = n₂ then
          stretchTriple ((R.crosses i).strainMode n p) ((R.crosses i).vorticityGradMode n p) (x n₁).1 (x n₁).2
            (star (x' n₂).1) (star (x' n₂).2) else 0‖
        ≤ (R.crosses i).balance * ∑ n₁ ∈ A, crossCharge (R.crosses i).strainBound (R.crosses i).vorticityGradBound
            (R.crosses i).length (x n₁).1 (x n₁).2
          + (R.crosses i).balance⁻¹ * ∑ n₂ ∈ A', crossCharge (R.crosses i).strainBound (R.crosses i).vorticityGradBound
            (R.crosses i).length (x' n₂).1 (x' n₂).2

theorem couplingEntry_of_parts (hB : ModeDensityBridgeHolds) (hP : PatchEntryCreditHolds)
    (hX : CrossWaveBoundHolds) : CouplingEntryHolds := by
  intro k C nE nM D R hR
  refine ⟨?_, ?_⟩
  · intro q hq hadm v G H g hpert
    obtain ⟨D₀, hD₀⟩ := hR.model_state
    obtain ⟨hpos, hneg⟩ := hB D D₀ hR.mode_class hR.model_flip hD₀ hR.bounds_measurable hR.pieces_flip q hq hadm
      v G H g hpert
    refine ⟨hpos, hneg, ?_⟩
    intro i
    exact hP (R.patches i) (hR.patches i) D.cert.symmetries (D.cert.period q) v G H g hpert
      hR.mode_class.flip
  · intro i p hp A A' x x'
    obtain ⟨hX', -⟩ := hR.crosses i
    exact hX (R.crosses i).azimuthOrder A A' (R.crosses i).waveModes x x'
      (fun n => (R.crosses i).strainMode n p) (fun n => (R.crosses i).vorticityGradMode n p)
      (R.crosses i).strainBound (R.crosses i).vorticityGradBound (R.crosses i).length (R.crosses i).balance
      hX'.order_pos hX'.strainBound_nonneg hX'.vorticityGradBound_nonneg hX'.length_pos hX'.balance_pos
      (hX'.strain_majorant p hp) (hX'.vorticityGrad_majorant p hp)

end Bridge

end CertCell

end Breakdown
