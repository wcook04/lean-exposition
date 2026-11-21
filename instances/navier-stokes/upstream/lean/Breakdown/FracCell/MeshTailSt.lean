import Breakdown.FracCell.MeshDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

def TailFamily.angleField {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O) (m : ℕ) (B : CellBases)
    (w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ) (o : O) (p : ℝ × ℝ) (θ : ℝ) : ℂ :=
  ∑ i, ∑ c : Fin (T.dim i), T.mult i o c p θ * T.inputFn m B w i c p θ

def TailFiniteStatement : Prop :=
  ∀ (K : CellBox) (B : CellBases), IsCellBox K → IsCellBases K B → ∀ (m : ℕ), 1 ≤ m → ∀ (D : ℕ)
    {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O), IsTailRegular K T → IsTailBounds K B D T →
      ∀ w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ, ∀ F : Finset (ℕ × ℕ),
        (∑ o, T.outWeight o * ∑ n ∈ T.outModes o, ∑ jl ∈ F,
            (if D < max jl.1 jl.2 then ‖B.coef K (T.outputMode m B w o n) jl.1 jl.2‖ ^ 2 else 0))
          ≤ T.majorant w

def CoefModeStatement : Prop :=
  ∀ (K : CellBox) (B : CellBases), IsCellBox K → ∀ (m : ℕ) {I O : Type} [Fintype I] [Fintype O]
    (T : TailFamily I O), IsTailRegular K T → ∀ (w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ) (o : O) (n : ℤ) (j l : ℕ),
      B.coef K (T.outputMode m B w o n) j l
          = (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
              Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * B.coef K (fun p => T.angleField m B w o p θ) j l
        ∧ MemLp (fun θ => B.coef K (fun p => T.angleField m B w o p θ) j l) 2
            (volume.restrict (Set.Ioc 0 (2 * Real.pi)))

def AngleTailStatement : Prop :=
  ∀ (K : CellBox) (B : CellBases), IsCellBox K → IsCellBases K B → ∀ (m : ℕ), 1 ≤ m → ∀ (D : ℕ)
    {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O), IsTailRegular K T → IsTailBounds K B D T →
      ∀ w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ, ∀ F : Finset (ℕ × ℕ),
        (∑ o, T.outWeight o * ((1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), ∑ jl ∈ F,
            (if D < max jl.1 jl.2 then ‖B.coef K (fun p => T.angleField m B w o p θ) jl.1 jl.2‖ ^ 2 else 0)))
          ≤ T.majorant w

def TailFamily.radialInput {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O) (m : ℕ) (B : CellBases)
    (w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ) (i : I) (j : ℕ) (c : Fin (T.dim i)) (z θ : ℝ) : ℂ :=
  ∑ n' ∈ T.inModes, ∑ l ∈ Finset.range (T.inputDeg i + 1),
    w i n' j l c * (B.heightPoly l z : ℂ) * Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I)

def TailFamily.heightInput {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O) (m : ℕ) (B : CellBases)
    (w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ) (i : I) (l : ℕ) (c : Fin (T.dim i)) (r θ : ℝ) : ℂ :=
  ∑ n' ∈ T.inModes, ∑ j ∈ Finset.range (T.inputDeg i + 1),
    w i n' j l c * (B.radialPoly j r : ℂ) * Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I)

def AngleSliceStatement : Prop :=
  ∀ (K : CellBox) (B : CellBases), IsCellBox K → IsCellBases K B → ∀ (m : ℕ) (D : ℕ)
    {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O), IsTailRegular K T → IsTailBounds K B D T →
      ∀ (w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ) (F : Finset (ℕ × ℕ)) (θ : ℝ),
        (∀ i o c, AEStronglyMeasurable (fun p => T.mult i o c p θ) (volume.restrict K.rect)) →
        (∑ o, T.outWeight o * ∑ jl ∈ F,
            (if D < max jl.1 jl.2 then ‖B.coef K (fun p => T.angleField m B w o p θ) jl.1 jl.2‖ ^ 2 else 0))
          ≤ (∑ i, ∑ j ∈ Finset.range (T.inputDeg i + 1), T.radialTotal * T.radialBound i j *
                ∫ z in Set.Icc K.z₁ K.z₂, ∑ c, ‖T.radialInput m B w i j c z θ‖ ^ 2)
            + ∑ i, ∑ l ∈ Finset.range (T.inputDeg i + 1), T.heightTotal * T.heightBound i l *
                ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ∑ c, ‖T.heightInput m B w i l c r θ‖ ^ 2

def InputEnergyStatement : Prop :=
  ∀ (K : CellBox) (B : CellBases), IsCellBox K → IsCellBases K B → ∀ (m : ℕ), 1 ≤ m →
    ∀ {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O)
      (w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ) (i : I) (k : ℕ),
      (IntervalIntegrable (fun θ => ∫ z in Set.Icc K.z₁ K.z₂, ∑ c, ‖T.radialInput m B w i k c z θ‖ ^ 2)
          volume 0 (2 * Real.pi) ∧
        (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
            (∫ z in Set.Icc K.z₁ K.z₂, ∑ c, ‖T.radialInput m B w i k c z θ‖ ^ 2)
          = ∑ n' ∈ T.inModes, ∑ l ∈ Finset.range (T.inputDeg i + 1), ∑ c, ‖w i n' k l c‖ ^ 2) ∧
      (IntervalIntegrable (fun θ => ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ∑ c, ‖T.heightInput m B w i k c r θ‖ ^ 2)
          volume 0 (2 * Real.pi) ∧
        (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
            (∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ∑ c, ‖T.heightInput m B w i k c r θ‖ ^ 2)
          = ∑ n' ∈ T.inModes, ∑ j ∈ Finset.range (T.inputDeg i + 1), ∑ c, ‖w i n' j k c‖ ^ 2)

def RadialBranchStatement : Prop :=
  ∀ (K : CellBox) (B : CellBases), IsCellBox K → IsCellBases K B → ∀ (m : ℕ) (D : ℕ)
    {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O), IsTailRegular K T → IsTailBounds K B D T →
      ∀ (w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ) (F1 F2 : Finset ℕ) (θ : ℝ),
        (∀ i o c, AEStronglyMeasurable (fun p => T.mult i o c p θ) (volume.restrict K.rect)) →
        (∑ o, T.outWeight o * ∑ j' ∈ F1, ∑ l' ∈ F2,
            (if D < j' then ‖B.coef K (fun p => T.angleField m B w o p θ) j' l'‖ ^ 2 else 0))
          ≤ ∑ i, ∑ j ∈ Finset.range (T.inputDeg i + 1), T.radialTotal * T.radialBound i j *
                ∫ z in Set.Icc K.z₁ K.z₂, ∑ c, ‖T.radialInput m B w i j c z θ‖ ^ 2

def HeightBranchStatement : Prop :=
  ∀ (K : CellBox) (B : CellBases), IsCellBox K → IsCellBases K B → ∀ (m : ℕ) (D : ℕ)
    {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O), IsTailRegular K T → IsTailBounds K B D T →
      ∀ (w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ) (F1 F2 : Finset ℕ) (θ : ℝ),
        (∀ i o c, AEStronglyMeasurable (fun p => T.mult i o c p θ) (volume.restrict K.rect)) →
        (∑ o, T.outWeight o * ∑ j' ∈ F1, ∑ l' ∈ F2,
            (if D < l' then ‖B.coef K (fun p => T.angleField m B w o p θ) j' l'‖ ^ 2 else 0))
          ≤ ∑ i, ∑ l ∈ Finset.range (T.inputDeg i + 1), T.heightTotal * T.heightBound i l *
                ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ∑ c, ‖T.heightInput m B w i l c r θ‖ ^ 2

end CellAnalysis

end CellCert

end Breakdown
