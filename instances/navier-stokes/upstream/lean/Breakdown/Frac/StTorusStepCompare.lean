import Breakdown.Frac.StTorusInverse
import Breakdown.Torus.CompareStatements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

def fracR3Step {κ : ℝ} (F : ScaledMildFramework Freq.X κ) (P : ℝ) (k : ℕ) (θ : ℝ) :
    ℕ → Piece Freq.X (MildFramework.stepLength P k) →L[ℝ] Piece Freq.X (MildFramework.stepLength P k) :=
  fun _ => θ⁻¹ • (F.stepFree P k).comp (F.stepEnd P k)

def fracTorusStep (α : ℝ) (hα : 1 < α) (T lam θ : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam)
    (hl1 : lam ≤ 1) : ℕ → Piece V (1 - lam) →L[ℝ] Piece V (1 - lam) :=
  fun n => (lam ^ dilExponent α / θ) •
    ((fracStepFrame α hα (stepScale T lam (n + 1)) (stepScale_pos hT hl (n + 1))
      (stepScale_le_one hT1 hl hl1 (n + 1))).pieceFree (1 - lam)).comp (pieceEnd (1 - lam))

def fracR3Entry (α : ℝ) {κ : ℝ} (F : ScaledMildFramework Freq.X κ) (P : ℝ) (k : ℕ) (θ b : ℝ)
    (A : Approximant (MildFramework.stepLength P k) b) (ζ : ShellSeq (MildFramework.stepLength P k))
    (m n : ℕ) (s : Icc (0 : ℝ) (MildFramework.stepLength P k)) : ShellData :=
  restrictR3 b (shiftChain (fracR3Step F P k θ) m n (fracR3Lambda α A ζ m) s)

def fracTorusEntry (α : ℝ) (hα : 1 < α) (T lam θ : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam)
    (hl1 : lam ≤ 1) (b : ℝ) (A : Approximant (1 - lam) b) (ζ : ShellSeq (1 - lam)) (m n : ℕ)
    (s : Icc (0 : ℝ) (1 - lam)) : ShellData :=
  restrictTorus (simScale α (stepScale T lam n)) b
    (shiftChain (fracTorusStep α hα T lam θ hT hT1 hl hl1) m n (fracTorusLambda α A T lam ζ m) s)

def FracR3ChainFormula (α : ℝ) : Prop :=
  ∀ (F : ScaledMildFramework Freq.X (dilExponent α)), F.G = Freq.fracHeatX α → F.D = Freq.fracDilX α →
    ∀ (P : ℝ) (k : ℕ) (θ : ℝ), 0 < P → 0 < k → ∀ (y : Piece Freq.X (MildFramework.stepLength P k)) (m j : ℕ)
    (s : Icc (0 : ℝ) (MildFramework.stepLength P k)),
      shiftChain (fracR3Step F P k θ) m (m + j + 1) y s =
        (θ⁻¹) ^ (j + 1) • Freq.fracDilX α (Real.exp (-(P / k)) ^ (j + 1))
          (Freq.fracHeatX α (Real.exp (-(P / k)) ^ (j + 1) * s + Real.exp (-(P / k)) - Real.exp (-(P / k)) ^ (j + 1))
            (pieceEnd (MildFramework.stepLength P k) y))

def FracTorusChainFormula (α : ℝ) (hα : 1 < α) : Prop :=
  ∀ (T lam θ : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1),
    lam < 1 → ∀ (y : Piece V (1 - lam)) (m j : ℕ) (s : Icc (0 : ℝ) (1 - lam)),
      shiftChain (fracTorusStep α hα T lam θ hT hT1 hl hl1) m (m + j + 1) y s =
        (lam ^ dilExponent α / θ) ^ (j + 1) •
          fracTorusHeat α (stepScale T lam m * (lam ^ (j + 1) * s + lam - lam ^ (j + 1))) (pieceEnd (1 - lam) y)

def FracHeatSolenoidalShift (α : ℝ) : Prop :=
  ∀ t τ : ℝ, 0 ≤ t → 0 < τ → ∀ A : Freq.L2R,
    Freq.fracHeatX α t (Freq.fracHeatSolenoidal α τ A) = Freq.fracHeatSolenoidal α (t + τ) A

def FracR3LambdaFormula (α : ℝ) : Prop :=
  ∀ (L b : ℝ) (A : Approximant L b), 0 < L → L ≤ 1 → ∀ (ζ : ShellSeq L) (m : ℕ) (s : Icc (0 : ℝ) L),
    fracR3Lambda α A ζ m s = ∑ l, ∫ σ in (0 : ℝ)..s, extendPiece (A.weight m l) σ •
      fracLambdaR3 α (A.field m l) (A.isTest m l) b (s - σ) (extendPiece (ζ m) σ)

def FracTorusLambdaFormula (α : ℝ) : Prop :=
  ∀ (L b T lam : ℝ) (A : Approximant L b), 0 < L → L ≤ 1 → 0 < T → T ≤ 1 → 0 < lam → lam ≤ 1 →
    0 < b → Real.sqrt (simScale α T) * b ≤ 1 / 8 → ∀ (ζ : ShellSeq L) (m : ℕ) (s : Icc (0 : ℝ) L),
      fracTorusLambda α A T lam ζ m s = ∑ l, ∫ σ in (0 : ℝ)..s, extendPiece (A.weight m l) σ •
        fracLambdaTorus α (A.field m l) (A.isTest m l) b (stepScale T lam m) (s - σ) (extendPiece (ζ m) σ)

def FracR3EntryFormula (α : ℝ) : Prop :=
  ∀ (F : ScaledMildFramework Freq.X (dilExponent α)), F.K = Freq.fracBilinX α → F.G = Freq.fracHeatX α →
    F.D = Freq.fracDilX α →
    ∀ (P : ℝ) (k : ℕ) (θ b : ℝ) (A : Approximant (MildFramework.stepLength P k) b),
    0 < P → 0 < k → MildFramework.stepLength P k ≤ 1 / 2 → 0 < θ → 0 < b →
    ∀ (ζ : ShellSeq (MildFramework.stepLength P k)) (m j : ℕ) (s : Icc (0 : ℝ) (MildFramework.stepLength P k)),
      fracR3Entry α F P k θ b A ζ m (m + j) s = (θ⁻¹) ^ j • ∑ l,
        ∫ σ in (0 : ℝ)..(if j = 0 then (s : ℝ) else MildFramework.stepLength P k),
          extendPiece (A.weight m l) σ • restrictR3 b (Freq.fracDilX α (Real.exp (-(P / k)) ^ j)
            (-(Freq.fracHeatSolenoidal α (1 - σ - Real.exp (-(P / k)) ^ j * (1 - s))
              (advectShell (A.field m l) (A.isTest m l) b (extendPiece (ζ m) σ)))))

def FracTorusEntryFormula (α : ℝ) (hα : 1 < α) : Prop :=
  ∀ (T lam θ : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1)
    (b : ℝ) (A : Approximant (1 - lam) b), lam < 1 → 1 / 2 ≤ lam → 0 < θ → 0 < b →
    Real.sqrt (simScale α T) * b ≤ 1 / 8 → ∀ (ζ : ShellSeq (1 - lam)) (m j : ℕ) (s : Icc (0 : ℝ) (1 - lam)),
      fracTorusEntry α hα T lam θ hT hT1 hl hl1 b A ζ m (m + j) s = (θ⁻¹) ^ j • ∑ l,
        ∫ σ in (0 : ℝ)..(if j = 0 then (s : ℝ) else 1 - lam),
          extendPiece (A.weight m l) σ • restrictTorus (simScale α (stepScale T lam (m + j))) b
            ((lam ^ j) ^ dilExponent α • (-((stepScale T lam m) ^ (-(1 / (4 * α))) •
              fracSourceOp α (stepScale T lam m) (1 - σ - lam ^ j * (1 - s))
                (advectShell (A.field m l) (A.isTest m l) b (extendPiece (ζ m) σ)))))

def FracFrameChange (α : ℝ) : Prop :=
  ∀ (μ c b : ℝ), 0 < c → c ≤ 1 → IsShellScale μ (Real.sqrt (simScale α c) * b) → ∀ (Z : V) (Y : Freq.X),
    ‖restrictTorus (μ * simScale α c) b (c ^ dilExponent α • Z) - restrictR3 b (Freq.fracDilX α c Y)‖ ≤
      c ^ dilExponent α *
        ‖restrictTorus μ (Real.sqrt (simScale α c) * b) Z - restrictR3 (Real.sqrt (simScale α c) * b) Y‖

def FracWindowBound (α : ℝ) (hα : 1 < α) : Prop :=
  ∀ (F : ScaledMildFramework Freq.X (dilExponent α)), F.K = Freq.fracBilinX α → F.G = Freq.fracHeatX α →
    F.D = Freq.fracDilX α → ∀ (P : ℝ) (k : ℕ) (θ b : ℝ) (A : Approximant (MildFramework.stepLength P k) b)
    (hl : 0 < Real.exp (-(P / k))) (hl1 : Real.exp (-(P / k)) ≤ 1),
    0 < P → 0 < k → MildFramework.stepLength P k ≤ 1 / 2 → Real.exp (-(P / k)) ^ dilExponent α < θ →
    θ < 1 → 0 < b → ∀ (j₀ : ℕ) (η : ℝ), 0 < η → ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1), T < T₀ →
      ∀ (ζ : ShellSeq (MildFramework.stepLength P k)) (m j : ℕ), j ≤ j₀ →
      ∀ s : Icc (0 : ℝ) (MildFramework.stepLength P k),
        ‖fracTorusEntry α hα T (Real.exp (-(P / k))) θ hT hT1 hl hl1 b A ζ m (m + j) s -
          fracR3Entry α F P k θ b A ζ m (m + j) s‖ ≤ η * ‖ζ‖

def FracTailBound (α : ℝ) (hα : 1 < α) : Prop :=
  ∀ (F : ScaledMildFramework Freq.X (dilExponent α)), F.K = Freq.fracBilinX α → F.G = Freq.fracHeatX α →
    F.D = Freq.fracDilX α → ∀ (P : ℝ) (k : ℕ) (θ b : ℝ) (A : Approximant (MildFramework.stepLength P k) b)
    (hl : 0 < Real.exp (-(P / k))) (hl1 : Real.exp (-(P / k)) ≤ 1),
    0 < P → 0 < k → MildFramework.stepLength P k ≤ 1 / 2 → Real.exp (-(P / k)) ^ dilExponent α < θ →
    θ < 1 → 0 < b → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1), Real.sqrt (simScale α T) * b ≤ 1 / 8 →
      ∀ (ζ : ShellSeq (MildFramework.stepLength P k)) (m j : ℕ) (s : Icc (0 : ℝ) (MildFramework.stepLength P k)),
        ‖fracTorusEntry α hα T (Real.exp (-(P / k))) θ hT hT1 hl hl1 b A ζ m (m + j) s‖ ≤
          K * (Real.exp (-(P / k)) ^ dilExponent α / θ) ^ j * ‖ζ‖ ∧
        ‖fracR3Entry α F P k θ b A ζ m (m + j) s‖ ≤ K * (Real.exp (-(P / k)) ^ dilExponent α / θ) ^ j * ‖ζ‖

def FracR3SeedEntry (α : ℝ) : Prop :=
  ∀ (F : ScaledMildFramework Freq.X (dilExponent α)), F.G = Freq.fracHeatX α → F.D = Freq.fracDilX α →
    ∀ (P : ℝ) (k : ℕ) (θ : ℝ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (J : E →L[ℝ] Freq.X),
    0 < P → 0 < k → Real.exp (-(P / k)) ^ dilExponent α < θ → θ < 1 →
    ∀ (e : E) (n : ℕ) (s : Icc (0 : ℝ) (MildFramework.stepLength P k)),
      (Ring.inverse (1 - fracR3Shift F P k θ) (fracR3Seed F P k J e)) n s =
        (θ⁻¹) ^ n • Freq.fracHeatX α (s + (Real.exp (-(P / k)) ^ n)⁻¹ - 1)
          (Freq.fracDilX α (Real.exp (-(P / k)) ^ n) (J e))

def FracTorusSeedEntry (α : ℝ) (hα : 1 < α) : Prop :=
  ∀ (T lam θ : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Jt : E →L[ℝ] V),
    lam < 1 → lam ^ dilExponent α < θ → θ < 1 → ∀ (e : E) (n : ℕ) (s : Icc (0 : ℝ) (1 - lam)),
      (Ring.inverse (1 - fracTorusShift α hα T lam θ hT hT1 hl hl1)
          (fracTorusSeed α hα T lam hT hT1 hl hl1 Jt e)) n s =
        (lam ^ dilExponent α / θ) ^ n • fracTorusHeat α (T * (lam ^ n * s + 1 - lam ^ n)) (Jt e)

def FracLambdaComparison (α : ℝ) (hα : 1 < α) : Prop :=
  ∀ (F : ScaledMildFramework Freq.X (dilExponent α)), F.K = Freq.fracBilinX α → F.G = Freq.fracHeatX α →
    F.D = Freq.fracDilX α → ∀ (P : ℝ) (k : ℕ) (θ b : ℝ)
    (A : Approximant (MildFramework.stepLength P k) b) (hl : 0 < Real.exp (-(P / k)))
    (hl1 : Real.exp (-(P / k)) ≤ 1),
    0 < P → 0 < k → MildFramework.stepLength P k ≤ 1 / 2 → Real.exp (-(P / k)) ^ dilExponent α < θ →
    θ < 1 → 0 < b → ∀ δ : ℝ, 0 < δ → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1), T < T₀ →
      ‖(fracTorusRestrict α _ b T (Real.exp (-(P / k)))).comp
          ((Ring.inverse (1 - fracTorusShift α hα T (Real.exp (-(P / k))) θ hT hT1 hl hl1)).comp
            (fracTorusLambda α A T (Real.exp (-(P / k))))) -
        (r3Restrict _ b).comp ((Ring.inverse (1 - fracR3Shift F P k θ)).comp (fracR3Lambda α A))‖ ≤ δ

def FracSeedComparison (α : ℝ) (hα : 1 < α) : Prop :=
  ∀ (F : ScaledMildFramework Freq.X (dilExponent α)), F.K = Freq.fracBilinX α → F.G = Freq.fracHeatX α →
    F.D = Freq.fracDilX α → ∀ (P : ℝ) (k : ℕ) (θ b : ℝ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E →L[ℝ] Freq.X) (ψ : TestLift E J b) (hl : 0 < Real.exp (-(P / k)))
    (hl1 : Real.exp (-(P / k)) ≤ 1),
    0 < P → 0 < k → MildFramework.stepLength P k ≤ 1 / 2 → Real.exp (-(P / k)) ^ dilExponent α < θ →
    θ < 1 → 0 < b → ∀ δ : ℝ, 0 < δ → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1), T < T₀ →
      ∀ Jt : E →L[ℝ] V,
        (∀ e, Jt e = (simScale α T ^ (1 / 4 : ℝ)) • toV (transplantField (simScale α T) (ψ.field e))) →
      ‖(fracTorusRestrict α _ b T (Real.exp (-(P / k)))).comp
          ((Ring.inverse (1 - fracTorusShift α hα T (Real.exp (-(P / k))) θ hT hT1 hl hl1)).comp
            (fracTorusSeed α hα T (Real.exp (-(P / k))) hT hT1 hl hl1 Jt)) -
        (r3Restrict _ b).comp ((Ring.inverse (1 - fracR3Shift F P k θ)).comp (fracR3Seed F P k J))‖ ≤ δ

end Breakdown.Periodic
