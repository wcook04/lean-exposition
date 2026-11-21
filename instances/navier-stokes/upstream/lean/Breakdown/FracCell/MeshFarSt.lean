import Breakdown.FracCell.MeshDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace CellScalars

variable {k : ℕ}

def strainInput (u : (ℤ × Fin 3 × Fin 4 × ℕ × ℕ) ⊕ (Fin k ⊕ Fin k) → ℂ) :
    Fin 2 → ℤ → ℕ → ℕ → Fin 3 → ℂ :=
  fun i n j l c' => if i = 0 then curlComp (lowStrainCoef u n j l) c' else lowVelocityCoef u n j l c'

def velocityInput (u : (ℤ × Fin 3 × Fin 4 × ℕ × ℕ) ⊕ (Fin k ⊕ Fin k) → ℂ) :
    Unit → ℤ → ℕ → ℕ → Fin 9 → ℂ :=
  fun _ n j l e => lowStrainCoef u n j l ⟨e.val / 3, by omega⟩ ⟨e.val % 3, Nat.mod_lt _ (by norm_num)⟩

end CellScalars

def FarCoefStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) {slots : ℕ} (R : CellRows N slots k) (F : FarMajorantData),
      IsCellBox K → K.solid ⊆ c.cellRegion → IsCellScalars α c K S → IsCellBases K B → S.resolved ∪ S.band ⊆ R.yModes →
      IsFarMajorant c K S B R F →
      ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ, ∀ n ∈ R.yModes, ∀ j l : ℕ, S.degNear < max j l →
        (∀ a b : Fin 3,
          B.coef K (fun p => CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b) j l =
            (if n ∈ S.resolved ∪ S.band then
              B.coef K ((CellScalars.strainGroupFamily c K S F).outputMode c.order B
                (CellScalars.strainInput (CellScalars.farVector c K S B x ζ)) (a, b) n) j l else 0)
            + (if n ∈ S.band ∧ b = 1 then
              turnAdjInv (azimuth c.order n) (fun a' => B.coef K ((CellScalars.bandGroupFamily c K S F).outputMode c.order B
                (CellScalars.velocityInput (CellScalars.farVector c K S B x ζ)) a' n) j l) a else 0)) ∧
        (n ∈ S.resolved → ∀ a : Fin 3,
          B.coef K (fun p => CellScalars.yVelocity c K S x.1 x.2.1 n p a) j l =
            B.coef K ((CellScalars.velocityGroupFamily c K S F).outputMode c.order B
              (CellScalars.velocityInput (CellScalars.farVector c K S B x ζ)) a n) j l)

def FarRegularStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (F : FarMajorantData),
      IsCellBox K → K.solid ⊆ c.cellRegion → IsCellScalars α c K S →
      IsTailRegular K (CellScalars.strainGroupFamily c K S F) ∧ IsTailRegular K (CellScalars.velocityGroupFamily c K S F) ∧
        IsTailRegular K (CellScalars.bandGroupFamily c K S F)

def FarSummableStatement : Prop :=
  ∀ (K : CellBox) (B : CellBases), IsCellBox K → IsCellBases K B → ∀ (m : ℕ) (D : ℕ)
    {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O), IsTailRegular K T →
      ∀ (w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ) (o : O) (n : ℤ),
        Summable (fun jl : ℕ × ℕ => if D < max jl.1 jl.2 then ‖B.coef K (T.outputMode m B w o n) jl.1 jl.2‖ ^ 2 else 0)

end CellAnalysis

end CellCert

end Breakdown
