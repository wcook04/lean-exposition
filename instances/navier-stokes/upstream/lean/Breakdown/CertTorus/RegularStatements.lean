import Breakdown.CertTorus.Defs
import Breakdown.Uniqueness.RegCurve

open MeasureTheory Set Real Filter
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Breakdown.FarField

open Freq SmoothFlow

def symX (x : X) : Space → CSpace := ((x : L2C) : Space → CSpace)

def homSob (k : ℕ) (x : X) : ℝ≥0∞ := homNormSq k (symX x)

def IsSmoothX (x : X) : Prop := ∀ k, homSob k x < ⊤

def IsHomSobolevCurve (k : ℕ) (u : ℝ → X) (S : Set ℝ) : Prop :=
  (∀ t ∈ S, homSob k (u t) < ⊤) ∧
    ∀ t₀ ∈ S, Tendsto (fun t => homSob k (u t - u t₀)) (𝓝[S] t₀) (𝓝 0)

def velSymbol (x : X) (ξ : Space) : CSpace :=
  ((2 * π * ‖ξ‖)⁻¹ : ℝ) • divFreeC ξ ((1 / 2 : ℝ) • (symX x ξ + conjVec (symX x (-ξ))))

def monoSymbol {n : ℕ} (α : Fin n → Fin 3) (ξ : Space) : ℂ :=
  ∏ i, (((2 * π * ξ (α i) : ℝ) : ℂ) * Complex.I)

def IsDerivX {n : ℕ} (α : Fin n → Fin 3) (x y : X) : Prop :=
  ∀ᵐ ξ ∂volume, symX y ξ = monoSymbol α ξ • symX x ξ

def shiftX (h : Space) : X →L[ℝ] X :=
  restrictX (fieldOp id (fun ξ => cmul (Complex.exp (-(((2 * π * inner ℝ h ξ : ℝ)) : ℂ) * Complex.I))))

def fixedPointIter (x : X) (a : ℝ) : ℕ → ℝ → X
  | 0, t => heatX (t - a) x
  | n + 1, t => heatX (t - a) x + ∫ s in a..t, bilinX (t - s) (fixedPointIter x a n s) (fixedPointIter x a n s)

def orbitField (w : ℝ → X) (s : ℝ) (y : Space) : Space := physField (velSymbol (w s)) y

def orbitPressure (w : ℝ → X) (s : ℝ) (y : Space) : ℝ :=
  physScalar (pressureSymbol (velSymbol (w s))) y

def HomWiener : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, ∀ x : X,
    ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖velSymbol x ξ‖ₑ ≤
      ENNReal.ofReal C * (homSob 0 x + homSob (k + 1) x) ^ (1 / 2 : ℝ)

def VelocityOfSymbol : Prop :=
  ∀ x : X, IsSmoothX x → (velocity x : Space → Space) =ᵐ[volume] physField (velSymbol x)

def VelocityOfSymbolOfWiener : Prop := HomWiener → VelocityOfSymbol

def BilinSymbol : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ u : X, IsSmoothX u →
    ∀ᵐ ξ ∂volume, symX (bilinX τ u u) ξ =
      ((2 * π * ‖ξ‖ * heatSymbol τ ξ : ℝ) : ℂ) • nonlinSymbol (velSymbol u) ξ

def BilinSymbolOfVelocity : Prop := HomWiener → VelocityOfSymbol → BilinSymbol

def DerivSobolev : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, ∀ x : X,
    (homSob n x < ⊤ → ∀ α : Fin n → Fin 3, ∃ y, IsDerivX α x y) ∧
    ∀ B : ℝ, (∀ α : Fin n → Fin 3, ∃ y, IsDerivX α x y ∧ ‖y‖ ≤ B) →
      homSob n x ≤ ENNReal.ofReal (C * B ^ 2)

def DerivAlgebra : Prop :=
  (∀ (n : ℕ) (α : Fin n → Fin 3) (x y y' : X), IsDerivX α x y → IsDerivX α x y' → y = y') ∧
  (∀ (α : Fin 0 → Fin 3) (x : X), IsDerivX α x x) ∧
  (∀ (n : ℕ) (α : Fin n → Fin 3) (x y x' y' : X) (c : ℝ), IsDerivX α x y → IsDerivX α x' y' →
      IsDerivX α (x + c • x') (y + c • y')) ∧
  (∀ (n : ℕ) (α : Fin n → Fin 3) (σ : Equiv.Perm (Fin n)) (x y : X),
      IsDerivX α x y → IsDerivX (α ∘ σ) x y) ∧
  ∀ (m n : ℕ) (α : Fin m → Fin 3) (β : Fin n → Fin 3) (x y z : X),
    IsDerivX α x y → IsDerivX β y z → IsDerivX (Fin.append α β) x z

def DerivHeat : Prop :=
  (∀ (n : ℕ) (α : Fin n → Fin 3) (t : ℝ) (x y : X), IsDerivX α x y →
      IsDerivX α (heatX t x) (heatX t y)) ∧
  ∀ n : ℕ, ∃ C : ℝ, ∀ (α : Fin n → Fin 3) (t : ℝ), 0 < t → ∀ x : X,
    ∃ y, IsDerivX α (heatX t x) y ∧ ‖y‖ ≤ C * t ^ (-((n : ℝ) / 2)) * ‖x‖

def DerivIntegral : Prop :=
  ∀ (n : ℕ) (α : Fin n → Fin 3) (F G : ℝ → X) (a b : ℝ), a ≤ b →
    IntervalIntegrable F volume a b → IntervalIntegrable G volume a b →
    (∀ s ∈ Ioo a b, IsDerivX α (F s) (G s)) →
    IsDerivX α (∫ s in a..b, F s) (∫ s in a..b, G s)

def DerivClosed : Prop :=
  ∀ (n : ℕ) (α : Fin n → Fin 3) (x : X) (xs ys : ℕ → X) (B : ℝ),
    Tendsto xs atTop (𝓝 x) → (∀ m, IsDerivX α (xs m) (ys m)) → (∀ m, ‖ys m‖ ≤ B) →
    ∃ y, IsDerivX α x y ∧ ‖y‖ ≤ B

def ShiftCovariance : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ (h : Space) (u v : X),
    bilinX τ (shiftX h u) (shiftX h v) = shiftX h (bilinX τ u v)

def DiffQuotient : Prop :=
  ∀ (j : Fin 3) (x y : X), IsDerivX ![j] x y ↔
    Tendsto (fun t : ℝ => t⁻¹ • (shiftX (-(t • unitVector j)) x - x)) (𝓝[≠] 0) (𝓝 y)

def BilinLeibniz : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ (j : Fin 3) (u u' v v' : X), IsDerivX ![j] u u' → IsDerivX ![j] v v' →
    IsDerivX ![j] (bilinX τ u v) (bilinX τ u' v + bilinX τ u v')

def BilinLeibnizOfShift : Prop := ShiftCovariance → DiffQuotient → BilinLeibniz

def PicardConverges : Prop :=
  ∀ M : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ (u : ℝ → X) (a b : ℝ), a < b → IsMildX u a b →
    (∀ t ∈ Icc a b, ‖u t‖ ≤ M) →
    ∀ t ∈ Icc a (min b (a + δ)), Tendsto (fun n => fixedPointIter (u a) a n t) atTop (𝓝 (u t))

def PicardDerivBound : Prop :=
  ∀ (k : ℕ) (M : ℝ), ∃ δ B : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (x : X) (a : ℝ),
    (∀ m ≤ k, ∀ α : Fin m → Fin 3, ∃ y, IsDerivX α x y ∧ ‖y‖ ≤ M) →
    ∀ n : ℕ, ∀ t ∈ Ioc a (a + δ),
      (∀ m ≤ k, ∀ α : Fin m → Fin 3, ∃ y, IsDerivX α (fixedPointIter x a n t) y ∧ ‖y‖ ≤ B) ∧
      ∀ α : Fin (k + 1) → Fin 3,
        ∃ y, IsDerivX α (fixedPointIter x a n t) y ∧ ‖y‖ ≤ B * (t - a) ^ (-(1 / 2 : ℝ))

def PicardDerivBoundOfCalculus : Prop :=
  DerivAlgebra → DerivHeat → DerivIntegral → DiffQuotient → BilinLeibniz → PicardDerivBound

def LocalGain : Prop :=
  ∀ (k : ℕ) (M : ℝ), ∃ δ B : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (u : ℝ → X) (a b : ℝ), a < b → IsMildX u a b →
    (∀ t ∈ Icc a b, ‖u t‖ ≤ M) →
    (∀ m ≤ k, ∀ α : Fin m → Fin 3, ∃ y, IsDerivX α (u a) y ∧ ‖y‖ ≤ M) →
    ∀ t ∈ Ioc a (min b (a + δ)),
      (∀ m ≤ k, ∀ α : Fin m → Fin 3, ∃ y, IsDerivX α (u t) y ∧ ‖y‖ ≤ B) ∧
      ∀ α : Fin (k + 1) → Fin 3, ∃ y, IsDerivX α (u t) y ∧ ‖y‖ ≤ B * (t - a) ^ (-(1 / 2 : ℝ))

def LocalGainOfPicard : Prop := PicardConverges → PicardDerivBound → DerivClosed → LocalGain

def MildRestrict : Prop :=
  ∀ (u : ℝ → X) (a a' b : ℝ), IsMildX u a b → a ≤ a' → a' ≤ b → IsMildX u a' b

def MildSmoothing : Prop :=
  ∀ (u : ℝ → X) (a b : ℝ), a < b → IsMildX u a b →
    ∀ a' ∈ Ioo a b, ∀ k : ℕ, IsHomSobolevCurve k u (Icc a' b)

def MildSmoothingOfLocalGain : Prop := LocalGain → MildRestrict → DerivSobolev → MildSmoothing

def DuhamelSymbolAe : Prop :=
  ∀ (u : ℝ → X) (a b : ℝ), a < b → IsMildX u a b → (∀ k, IsHomSobolevCurve k u (Icc a b)) →
    ∀ t ∈ Icc a b, ∀ᵐ ξ ∂volume, velSymbol (u t) ξ =
      ((heatSymbol (t - a) ξ : ℝ) : ℂ) • velSymbol (u a) ξ +
        ∫ s in a..t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (velSymbol (u s)) ξ

def DuhamelSymbolOfBilinSymbol : Prop := BilinSymbol → HomWiener → DuhamelSymbolAe

def SymbolCurve : Prop :=
  ∀ (u : ℝ → X) (a b : ℝ), a < b → IsMildX u a b → (∀ k, IsHomSobolevCurve k u (Icc a b)) →
    ∀ k : ℕ, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun τ => toWeightL1 k (velSymbol (u τ)))
        (toWeightL1 k (timeDerivSymbol (velSymbol (u t)))) (Icc a b) t

def SymbolCurveOfDuhamel : Prop := DuhamelSymbolAe → HomWiener → SymbolCurve

def WienerSolution : Prop :=
  ∀ (F : ℝ → Space → CSpace) (a b : ℝ), a < b →
    (∀ t ∈ Icc a b, IsSolenoidalSymbol (F t) ∧ ∀ k, MemLp (F t) 1 (weightL1Measure k)) →
    (∀ k, ∀ t ∈ Icc a b, HasDerivWithinAt (fun τ => toWeightL1 k (F τ))
      (toWeightL1 k (timeDerivSymbol (F t))) (Icc a b) t) →
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => physField (F z.1) z.2) (Icc a b ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => physScalar (pressureSymbol (F z.1)) z.2) (Icc a b ×ˢ univ) ∧
    (∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun τ => physField (F τ) x)
      (sumSecondPartialsAt (physField (F t)) x - advectionAt (physField (F t)) x -
        gradientAt (physScalar (pressureSymbol (F t))) x) t) ∧
    ∀ t ∈ Icc a b, ∀ x, divergenceAt (physField (F t)) x = 0

def DilateSymbol : Prop :=
  ∀ μ : ℝ, 0 < μ → ∀ x : X,
    (∀ k, homSob k (dilX μ x) = ENNReal.ofReal (μ ^ ((k : ℝ) + 1 / 2)) * homSob k x) ∧
    (∀ k, Tendsto (fun ν => homSob k (dilX ν x - dilX μ x)) (𝓝 μ) (𝓝 0) ∨ homSob k x = ⊤) ∧
    (IsSmoothX x → ∀ y, physField (velSymbol (dilX μ x)) y =
      Real.sqrt μ • physField (velSymbol x) (Real.sqrt μ • y)) ∧
    (IsSmoothX x → ∀ y, physScalar (pressureSymbol (velSymbol (dilX μ x))) y =
      μ * physScalar (pressureSymbol (velSymbol x)) (Real.sqrt μ • y))

def RotateSymbol : Prop :=
  ∀ (R : Space ≃ₗᵢ[ℝ] Space) (x : X),
    (∀ k, homSob k (rotX R x) = homSob k x) ∧
    (∀ k, ‖toWeightL1 k (velSymbol (rotX R x))‖ = ‖toWeightL1 k (velSymbol x)‖) ∧
    ∀ y, physField (velSymbol (rotX R x)) y = R (physField (velSymbol x) (R.symm y))

def WindowResidual : Prop :=
  ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (s₀ a b : ℝ), 0 ≤ a → a < b → b < 1 →
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => physicalField W s₀ z.1 z.2) (Icc a b ×ˢ univ) →
    ContDiffOn ℝ ∞ (fun z : ℝ × Space =>
      (1 - z.1)⁻¹ * q (s₀ - Real.log (1 - z.1)) ((Real.sqrt (1 - z.1))⁻¹ • z.2)) (Icc a b ×ˢ univ) →
    (∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun τ => physicalField W s₀ τ x)
      (sumSecondPartialsAt (physicalField W s₀ t) x - advectionAt (physicalField W s₀ t) x -
        gradientAt (fun x' => (1 - t)⁻¹ * q (s₀ - Real.log (1 - t)) ((Real.sqrt (1 - t))⁻¹ • x')) x) t) →
    (∀ t ∈ Icc a b, ∀ x, divergenceAt (physicalField W s₀ t) x = 0) →
    ∀ s ∈ Ioo (s₀ - Real.log (1 - a)) (s₀ - Real.log (1 - b)), ∀ y,
      ContDiffAt ℝ ∞ (fun z : ℝ × Space => W z.1 z.2) (s, y) ∧
      ContDiffAt ℝ ∞ (fun z : ℝ × Space => q z.1 z.2) (s, y) ∧
      SimilarityResidual W q s y = 0 ∧ divergenceAt (W s) y = 0

def OrbitWindows : Prop :=
  ∀ (w : ℝ → X) (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space), realization.F.IsOrbit (realization.rot R) w P →
    ∀ s₀ T : ℝ, 0 < T → T < 1 → IsMildX (fun t => dilX (1 - t)⁻¹ (w (s₀ - Real.log (1 - t)))) 0 T

def PhysFieldDerivBound : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, ∀ f : Space → CSpace, MemLp f 1 (weightL1Measure j) → ∀ y,
    ‖iteratedFDeriv ℝ j (physField f) y‖ ≤ C * ‖toWeightL1 j f‖

def PressureGradL2 : Prop :=
  ∀ x : X, IsSmoothX x →
    MemLp (fun y => fderiv ℝ (physScalar (pressureSymbol (velSymbol x))) y) 2 volume

def PressureGradL2OfWiener : Prop := HomWiener → PressureGradL2

def OrbitSmooth : Prop :=
  ∀ (w : ℝ → X) (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space), realization.F.IsOrbit (realization.rot R) w P →
    (∀ s, IsSmoothX (w s)) ∧
    ContDiff ℝ ∞ (fun z : ℝ × Space => orbitField w z.1 z.2) ∧
    ContDiff ℝ ∞ (fun z : ℝ × Space => orbitPressure w z.1 z.2) ∧
    (∀ s y, SimilarityResidual (orbitField w) (orbitPressure w) s y = 0) ∧
    ∀ s y, divergenceAt (orbitField w s) y = 0

def OrbitSmoothOfWindows : Prop :=
  OrbitWindows → MildRestrict → MildSmoothing → SymbolCurve → WienerSolution → DilateSymbol →
    WindowResidual → HomWiener → OrbitSmooth

def OrbitHomSobolev : Prop :=
  ∀ (w : ℝ → X) (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space), realization.F.IsOrbit (realization.rot R) w P →
    ∀ k, IsHomSobolevCurve k w univ

def OrbitHomSobolevOfWindows : Prop := OrbitWindows → MildSmoothing → DilateSymbol → OrbitHomSobolev

def OrbitDerivBound : Prop :=
  ∀ (w : ℝ → X) (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space), realization.F.IsOrbit (realization.rot R) w P →
    ∃ C, UniformDerivBound (orbitField w) 3 C

def OrbitDerivBoundOfSymbolCurve : Prop :=
  OrbitHomSobolev → HomWiener → RotateSymbol → PhysFieldDerivBound → OrbitDerivBound

def OrbitTail : Prop :=
  ∀ (w : ℝ → X) (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space), realization.F.IsOrbit (realization.rot R) w P →
    TailVanishes (orbitField w)

def OrbitTailOfSymbolCurve : Prop := OrbitHomSobolev → HomWiener → RotateSymbol → OrbitTail

theorem realization_rot_eq (R : Space ≃ₗᵢ[ℝ] Space) : realization.rot R = rotX R := rfl

theorem smoothFieldOfOrbit_of_regularity (hO : OrbitSmooth) (hD : OrbitDerivBound)
    (hT : OrbitTail) (hV : VelocityOfSymbol) (hR : RotateSymbol) (hQ : PressureGradL2) :
    SmoothFieldOfOrbit := by
  intro w P R hw
  obtain ⟨hs, hW, hq, hres, hdiv⟩ := hO w P R hw
  have hvel : IsVelocityOf w (orbitField w) := fun s => hV (w s) (hs s)
  refine ⟨orbitField w, orbitPressure w, ⟨hw.pos, hW, hq, hres, hdiv, ?_, ?_, hD w P R hw, hT w P R hw,
    fun s => hQ (w s) (hs s)⟩, hvel⟩
  · intro s y
    have hp := hw.periodic s
    rw [realization_rot_eq] at hp
    show physField (velSymbol (w (s + P))) y = R (physField (velSymbol (w s)) (R.symm y))
    rw [hp]
    exact (hR R (w s)).2.2 y
  · obtain ⟨s, hs0⟩ := hw.nonzero
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    apply hs0
    apply velocityInjective_holds
    filter_upwards [hvel s] with y hy
    rw [hy]
    exact hcon s y

theorem smoothFieldOfOrbit_of_symbolCalculus
    (hWi : HomWiener) (hVsW : VelocityOfSymbolOfWiener) (hBsV : BilinSymbolOfVelocity)
    (hDs : DerivSobolev) (hDa : DerivAlgebra) (hDh : DerivHeat) (hDi : DerivIntegral)
    (hDc : DerivClosed) (hSc : ShiftCovariance) (hDq : DiffQuotient) (hLs : BilinLeibnizOfShift)
    (hPc : PicardConverges) (hPs : PicardDerivBoundOfCalculus) (hLg : LocalGainOfPicard)
    (hMr : MildRestrict) (hMs : MildSmoothingOfLocalGain) (hDsS : DuhamelSymbolOfBilinSymbol)
    (hScS : SymbolCurveOfDuhamel) (hWs : WienerSolution) (hDl : DilateSymbol) (hRo : RotateSymbol)
    (hWr : WindowResidual) (hOw : OrbitWindows) (hPd : PhysFieldDerivBound)
    (hPgW : PressureGradL2OfWiener) (hOs : OrbitSmoothOfWindows) (hOh : OrbitHomSobolevOfWindows)
    (hOd : OrbitDerivBoundOfSymbolCurve) (hOt : OrbitTailOfSymbolCurve) : SmoothFieldOfOrbit := by
  have hVs : VelocityOfSymbol := hVsW hWi
  have hBs : BilinSymbol := hBsV hWi hVs
  have hL : BilinLeibniz := hLs hSc hDq
  have hPdb : PicardDerivBound := hPs hDa hDh hDi hDq hL
  have hLG : LocalGain := hLg hPc hPdb hDc
  have hMS : MildSmoothing := hMs hLG hMr hDs
  have hDA : DuhamelSymbolAe := hDsS hBs hWi
  have hSC : SymbolCurve := hScS hDA hWi
  have hOS : OrbitSmooth := hOs hOw hMr hMS hSC hWs hDl hWr hWi
  have hOH : OrbitHomSobolev := hOh hOw hMS hDl
  exact smoothFieldOfOrbit_of_regularity hOS (hOd hOH hWi hRo hPd) (hOt hOH hWi hRo) hVs hRo (hPgW hWi)

end Breakdown.FarField
