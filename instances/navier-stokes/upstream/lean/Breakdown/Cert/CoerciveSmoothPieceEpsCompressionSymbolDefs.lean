import Breakdown.Cert.CoerciveSmoothPieceEpsCompressionAssembly

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceEpsCompression

open Internal.SmoothPieceEpsCore

def applyMat {q : Type} [Fintype q] (A : Fin 3 → q → ℂ) (u : q → ℂ) : Fin 3 → ℂ := fun i => ∑ j, A i j * u j

def torusPhase (β : ℤ × ℤ) (τ φ : ℝ) : ℂ := Complex.exp (((2 * Real.pi * β.1 * τ + β.2 * φ : ℝ) : ℂ) * Complex.I)

def symbolMat {q : Type} [Fintype q] (H : Finset (ℤ × ℤ)) (A : ℤ × ℤ → Fin 3 → q → ℂ) (τ φ : ℝ) :
    Fin 3 → q → ℂ :=
  fun i j => ∑ β ∈ H, torusPhase β τ φ * A β i j

open Classical in
def halfPart {q : Type} [Fintype q] (H : Finset (ℤ × ℤ)) (T : Set (ℤ × ℤ)) (A : ℤ × ℤ → Fin 3 → q → ℂ)
    (g : ℤ × ℤ → q → ℂ) (ι : ℤ × ℤ) : Fin 3 → ℂ :=
  ∑ β ∈ H, if ι - β ∈ T then applyMat (A β) (g (ι - β)) else 0

open Classical in
def halfSq {p : Type} [Fintype p] (T : Set (ℤ × ℤ)) (x : ℤ × ℤ → p → ℂ) (ι : ℤ × ℤ) : ℝ :=
  if ι ∈ T then cnormSq (x ι) else 0

open Classical in
def halfPairing {q : Type} [Fintype q] (H : Finset (ℤ × ℤ)) (T : Set (ℤ × ℤ)) (A : ℤ × ℤ → Fin 3 → q → ℂ)
    (x : ℤ × ℤ → Fin 3 → ℂ) (g : ℤ × ℤ → q → ℂ) (ι : ℤ × ℤ) : ℂ :=
  if ι ∈ T then cdot (x ι) (halfPart H T A g ι) else 0

end Internal.SmoothPieceEpsCompression

end Coercive

end Breakdown
