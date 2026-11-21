import Breakdown.Torus.StatementsInverse

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

def shiftChain {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (B : ℕ → X →L[ℝ] X) (m : ℕ) :
    ℕ → X →L[ℝ] X
  | 0 => if m = 0 then ContinuousLinearMap.id ℝ X else 0
  | n + 1 => if m = n + 1 then ContinuousLinearMap.id ℝ X else (B n).comp (shiftChain B m n)

def r3Step (F : MildFramework Freq.X) (P : ℝ) (k : ℕ) (θ : ℝ) :
    ℕ → Piece Freq.X (MildFramework.stepLength P k) →L[ℝ] Piece Freq.X (MildFramework.stepLength P k) :=
  fun _ => θ⁻¹ • (F.stepFree P k).comp (F.stepEnd P k)

def torusStep (hK : KernelSharpBound) (T lam θ : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam)
    (hl1 : lam ≤ 1) : ℕ → Piece V (1 - lam) →L[ℝ] Piece V (1 - lam) :=
  fun n => (lam ^ (1 / 4 : ℝ) / θ) •
    ((stepFrame hK (stepScale T lam (n + 1)) (stepScale_pos hT hl (n + 1))
      (stepScale_le_one hT1 hl hl1 (n + 1))).pieceFree (1 - lam)).comp (pieceEnd (1 - lam))

def r3Entry (F : MildFramework Freq.X) (P : ℝ) (k : ℕ) (θ b : ℝ)
    (A : Approximant (MildFramework.stepLength P k) b) (ζ : ShellSeq (MildFramework.stepLength P k))
    (m n : ℕ) (s : Icc (0 : ℝ) (MildFramework.stepLength P k)) : ShellData :=
  restrictR3 b (shiftChain (r3Step F P k θ) m n (r3Lambda A ζ m) s)

def torusEntry (hK : KernelSharpBound) (T lam θ : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam)
    (hl1 : lam ≤ 1) (b : ℝ) (A : Approximant (1 - lam) b) (ζ : ShellSeq (1 - lam)) (m n : ℕ)
    (s : Icc (0 : ℝ) (1 - lam)) : ShellData :=
  restrictTorus (stepScale T lam n) b
    (shiftChain (torusStep hK T lam θ hT hT1 hl hl1) m n (torusLambda A T lam ζ m) s)

def InvSeriesEntry : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (B : ℕ → X →L[ℝ] X),
    ‖seqShift B‖ < 1 → (∀ g n, seqShift B g n = if n = 0 then 0 else B (n - 1) (g (n - 1))) →
    ∀ g n, (Ring.inverse (1 - seqShift B) g) n = ∑ m ∈ Finset.range (n + 1), shiftChain B m n (g m)

def ShiftChainNorm : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] (B : ℕ → X →L[ℝ] X) (C : ℝ), 0 ≤ C →
    (∀ n, ‖B n‖ ≤ C) → ∀ m n, m ≤ n → ‖shiftChain B m n‖ ≤ C ^ (n - m)

def R3ChainFormula : Prop :=
  ∀ (F : MildFramework Freq.X), F.G = Freq.heatX → F.D = Freq.dilX → ∀ (P : ℝ) (k : ℕ) (θ : ℝ),
    0 < P → 0 < k → ∀ (y : Piece Freq.X (MildFramework.stepLength P k)) (m j : ℕ)
    (s : Icc (0 : ℝ) (MildFramework.stepLength P k)),
      shiftChain (r3Step F P k θ) m (m + j + 1) y s =
        (θ⁻¹) ^ (j + 1) • Freq.dilX (Real.exp (-(P / k)) ^ (j + 1))
          (Freq.heatX (Real.exp (-(P / k)) ^ (j + 1) * s + Real.exp (-(P / k)) - Real.exp (-(P / k)) ^ (j + 1))
            (pieceEnd (MildFramework.stepLength P k) y))

def TorusChainFormula : Prop :=
  ∀ (hK : KernelSharpBound) (T lam θ : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1),
    lam < 1 → ∀ (y : Piece V (1 - lam)) (m j : ℕ) (s : Icc (0 : ℝ) (1 - lam)),
      shiftChain (torusStep hK T lam θ hT hT1 hl hl1) m (m + j + 1) y s =
        (lam ^ (1 / 4 : ℝ) / θ) ^ (j + 1) •
          heat (stepScale T lam m * (lam ^ (j + 1) * s + lam - lam ^ (j + 1))) (pieceEnd (1 - lam) y)

def HeatDivFreeShift : Prop :=
  ∀ t τ : ℝ, 0 ≤ t → 0 < τ → ∀ A : Freq.L2R,
    Freq.heatX t (Freq.heatDivFree τ A) = Freq.heatDivFree (t + τ) A

def HeatDivFreeContinuous : Prop :=
  ∀ A : Freq.L2R, ContinuousOn (fun τ => Freq.heatDivFree τ A) (Ioi 0)

def R3LambdaFormula : Prop :=
  ∀ (L b : ℝ) (A : Approximant L b), 0 < L → L ≤ 1 → ∀ (ζ : ShellSeq L) (m : ℕ) (s : Icc (0 : ℝ) L),
    r3Lambda A ζ m s = ∑ l, ∫ σ in (0 : ℝ)..s, extendPiece (A.weight m l) σ •
      lambdaR3 (A.field m l) (A.isTest m l) b (s - σ) (extendPiece (ζ m) σ)

def TorusLambdaFormula : Prop :=
  ∀ (L b T lam : ℝ) (A : Approximant L b), 0 < L → L ≤ 1 → 0 < T → T ≤ 1 → 0 < lam → lam ≤ 1 →
    0 < b → Real.sqrt T * b ≤ 1 / 8 → ∀ (ζ : ShellSeq L) (m : ℕ) (s : Icc (0 : ℝ) L),
      torusLambda A T lam ζ m s = ∑ l, ∫ σ in (0 : ℝ)..s, extendPiece (A.weight m l) σ •
        lambdaTorus (A.field m l) (A.isTest m l) b (stepScale T lam m) (s - σ) (extendPiece (ζ m) σ)

def R3EntryFormula : Prop :=
  ∀ (F : MildFramework Freq.X), F.K = Freq.bilinX → F.G = Freq.heatX → F.D = Freq.dilX →
    ∀ (P : ℝ) (k : ℕ) (θ b : ℝ) (A : Approximant (MildFramework.stepLength P k) b),
    0 < P → 0 < k → MildFramework.stepLength P k ≤ 1 / 2 → 0 < θ → 0 < b →
    ∀ (ζ : ShellSeq (MildFramework.stepLength P k)) (m j : ℕ) (s : Icc (0 : ℝ) (MildFramework.stepLength P k)),
      r3Entry F P k θ b A ζ m (m + j) s = (θ⁻¹) ^ j • ∑ l,
        ∫ σ in (0 : ℝ)..(if j = 0 then (s : ℝ) else MildFramework.stepLength P k),
          extendPiece (A.weight m l) σ • restrictR3 b (Freq.dilX (Real.exp (-(P / k)) ^ j)
            (-(Freq.heatDivFree (1 - σ - Real.exp (-(P / k)) ^ j * (1 - s))
              (advectShell (A.field m l) (A.isTest m l) b (extendPiece (ζ m) σ)))))

def TorusEntryFormula : Prop :=
  ∀ (hK : KernelSharpBound) (T lam θ : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1)
    (b : ℝ) (A : Approximant (1 - lam) b), lam < 1 → 1 / 2 ≤ lam → 0 < θ → 0 < b →
    Real.sqrt T * b ≤ 1 / 8 → ∀ (ζ : ShellSeq (1 - lam)) (m j : ℕ) (s : Icc (0 : ℝ) (1 - lam)),
      torusEntry hK T lam θ hT hT1 hl hl1 b A ζ m (m + j) s = (θ⁻¹) ^ j • ∑ l,
        ∫ σ in (0 : ℝ)..(if j = 0 then (s : ℝ) else 1 - lam),
          extendPiece (A.weight m l) σ • restrictTorus (stepScale T lam (m + j)) b
            ((lam ^ j) ^ (1 / 4 : ℝ) • (-((stepScale T lam m) ^ (-(1 / 4 : ℝ)) •
              sourceOp (stepScale T lam m) (1 - σ - lam ^ j * (1 - s))
                (advectShell (A.field m l) (A.isTest m l) b (extendPiece (ζ m) σ)))))

def FrameChange : Prop :=
  ∀ (μ c b : ℝ), 0 < c → c ≤ 1 → IsShellScale μ (Real.sqrt c * b) → ∀ (Z : V) (Y : Freq.X),
    ‖restrictTorus (μ * c) b (c ^ (1 / 4 : ℝ) • Z) - restrictR3 b (Freq.dilX c Y)‖ ≤
      c ^ (1 / 4 : ℝ) * ‖restrictTorus μ (Real.sqrt c * b) Z - restrictR3 (Real.sqrt c * b) Y‖

def SplitIntegralBound : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (u ε a c : ℝ),
    0 ≤ u → 0 < ε → 0 ≤ a → 0 ≤ c →
    (∀ σ ∈ Ioo 0 u, ‖f σ‖ ≤ a ∨ (u - σ < ε ∧ ‖f σ‖ ≤ c * (u - σ) ^ (-(3 / 4 : ℝ)))) →
    ‖∫ σ in (0 : ℝ)..u, f σ‖ ≤ a * u + 4 * c * ε ^ (1 / 4 : ℝ)

def WindowBound : Prop :=
  ∀ (hK : KernelSharpBound) (F : MildFramework Freq.X), F.K = Freq.bilinX → F.G = Freq.heatX →
    F.D = Freq.dilX → ∀ (P : ℝ) (k : ℕ) (θ b : ℝ) (A : Approximant (MildFramework.stepLength P k) b)
    (hl : 0 < Real.exp (-(P / k))) (hl1 : Real.exp (-(P / k)) ≤ 1),
    0 < P → 0 < k → MildFramework.stepLength P k ≤ 1 / 2 → Real.exp (-(P / k)) ^ (1 / 4 : ℝ) < θ →
    θ < 1 → 0 < b → ∀ (j₀ : ℕ) (η : ℝ), 0 < η → ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1), T < T₀ →
      ∀ (ζ : ShellSeq (MildFramework.stepLength P k)) (m j : ℕ), j ≤ j₀ →
      ∀ s : Icc (0 : ℝ) (MildFramework.stepLength P k),
        ‖torusEntry hK T (Real.exp (-(P / k))) θ hT hT1 hl hl1 b A ζ m (m + j) s -
          r3Entry F P k θ b A ζ m (m + j) s‖ ≤ η * ‖ζ‖

def TailBound : Prop :=
  ∀ (hK : KernelSharpBound) (F : MildFramework Freq.X), F.K = Freq.bilinX → F.G = Freq.heatX →
    F.D = Freq.dilX → ∀ (P : ℝ) (k : ℕ) (θ b : ℝ) (A : Approximant (MildFramework.stepLength P k) b)
    (hl : 0 < Real.exp (-(P / k))) (hl1 : Real.exp (-(P / k)) ≤ 1),
    0 < P → 0 < k → MildFramework.stepLength P k ≤ 1 / 2 → Real.exp (-(P / k)) ^ (1 / 4 : ℝ) < θ →
    θ < 1 → 0 < b → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1), Real.sqrt T * b ≤ 1 / 8 →
      ∀ (ζ : ShellSeq (MildFramework.stepLength P k)) (m j : ℕ) (s : Icc (0 : ℝ) (MildFramework.stepLength P k)),
        ‖torusEntry hK T (Real.exp (-(P / k))) θ hT hT1 hl hl1 b A ζ m (m + j) s‖ ≤
          K * (Real.exp (-(P / k)) ^ (1 / 4 : ℝ) / θ) ^ j * ‖ζ‖ ∧
        ‖r3Entry F P k θ b A ζ m (m + j) s‖ ≤ K * (Real.exp (-(P / k)) ^ (1 / 4 : ℝ) / θ) ^ j * ‖ζ‖

def R3SeedEntry : Prop :=
  ∀ (F : MildFramework Freq.X), F.G = Freq.heatX → F.D = Freq.dilX → ∀ (P : ℝ) (k : ℕ) (θ : ℝ)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (J : E →L[ℝ] Freq.X),
    0 < P → 0 < k → Real.exp (-(P / k)) ^ (1 / 4 : ℝ) < θ → θ < 1 →
    ∀ (e : E) (n : ℕ) (s : Icc (0 : ℝ) (MildFramework.stepLength P k)),
      (Ring.inverse (1 - r3Shift F P k θ) (r3Seed F P k J e)) n s =
        (θ⁻¹) ^ n • Freq.heatX (s + (Real.exp (-(P / k)) ^ n)⁻¹ - 1)
          (Freq.dilX (Real.exp (-(P / k)) ^ n) (J e))

def TorusSeedEntry : Prop :=
  ∀ (hK : KernelSharpBound) (T lam θ : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Jt : E →L[ℝ] V),
    lam < 1 → lam ^ (1 / 4 : ℝ) < θ → θ < 1 → ∀ (e : E) (n : ℕ) (s : Icc (0 : ℝ) (1 - lam)),
      (Ring.inverse (1 - torusShift hK T lam θ hT hT1 hl hl1) (torusSeed hK T lam hT hT1 hl hl1 Jt e)) n s =
        (lam ^ (1 / 4 : ℝ) / θ) ^ n • heat (T * (lam ^ n * s + 1 - lam ^ n)) (Jt e)

def TransplantDilate : Prop :=
  ∀ (μ c : ℝ) (f : Space → Space), 0 < μ → 0 < c → transplantField μ f = transplantField (μ * c) (dilateField c f)

def DilateTest : Prop :=
  ∀ (c : ℝ) (f : Space → Space), 0 < c → IsTestField f → IsTestField (dilateField c f)

def LambdaComparison : Prop :=
  ∀ (hK : KernelSharpBound) (F : MildFramework Freq.X), F.K = Freq.bilinX → F.G = Freq.heatX →
    F.D = Freq.dilX → ∀ (P : ℝ) (k : ℕ) (θ b : ℝ)
    (A : Approximant (MildFramework.stepLength P k) b) (hl : 0 < Real.exp (-(P / k)))
    (hl1 : Real.exp (-(P / k)) ≤ 1),
    0 < P → 0 < k → MildFramework.stepLength P k ≤ 1 / 2 → Real.exp (-(P / k)) ^ (1 / 4 : ℝ) < θ →
    θ < 1 → 0 < b → ∀ δ : ℝ, 0 < δ → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1), T < T₀ →
      ‖(torusRestrict _ b T (Real.exp (-(P / k)))).comp
          ((Ring.inverse (1 - torusShift hK T (Real.exp (-(P / k))) θ hT hT1 hl hl1)).comp
            (torusLambda A T (Real.exp (-(P / k))))) -
        (r3Restrict _ b).comp ((Ring.inverse (1 - r3Shift F P k θ)).comp (r3Lambda A))‖ ≤ δ

def SeedComparison : Prop :=
  ∀ (hK : KernelSharpBound) (F : MildFramework Freq.X), F.K = Freq.bilinX → F.G = Freq.heatX →
    F.D = Freq.dilX → ∀ (P : ℝ) (k : ℕ) (θ b : ℝ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E →L[ℝ] Freq.X) (ψ : TestLift E J b) (hl : 0 < Real.exp (-(P / k)))
    (hl1 : Real.exp (-(P / k)) ≤ 1),
    0 < P → 0 < k → MildFramework.stepLength P k ≤ 1 / 2 → Real.exp (-(P / k)) ^ (1 / 4 : ℝ) < θ →
    θ < 1 → 0 < b → ∀ δ : ℝ, 0 < δ → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1), T < T₀ →
      ∀ Jt : E →L[ℝ] V, (∀ e, Jt e = (T ^ (1 / 4 : ℝ)) • toV (transplantField T (ψ.field e))) →
      ‖(torusRestrict _ b T (Real.exp (-(P / k)))).comp
          ((Ring.inverse (1 - torusShift hK T (Real.exp (-(P / k))) θ hT hT1 hl hl1)).comp
            (torusSeed hK T (Real.exp (-(P / k))) hT hT1 hl hl1 Jt)) -
        (r3Restrict _ b).comp ((Ring.inverse (1 - r3Shift F P k θ)).comp (r3Seed F P k J))‖ ≤ δ

def AdvectShellBounds : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) (ζ : ShellData),
    (eLpNorm (advectShell φ hφ b ζ : Space → Space) (3 / 2) volume).toReal ≤ C * ‖Freq.embedX φ‖ * ‖ζ‖) ∧
  ∀ (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) (ζ : ShellData),
    ∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b → (advectShell φ hφ b ζ : Space → Space) y = 0

end Breakdown.Periodic
