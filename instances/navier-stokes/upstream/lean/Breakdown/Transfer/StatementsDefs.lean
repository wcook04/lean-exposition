import Breakdown.Base.Framework

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

structure HeatBilinear (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  G : ℝ → X →L[ℝ] X
  G_zero : G 0 = ContinuousLinearMap.id ℝ X
  G_add : ∀ s t, 0 ≤ s → 0 ≤ t → G (s + t) = (G s).comp (G t)
  G_norm : ∀ t, 0 ≤ t → ‖G t‖ ≤ 1
  G_cont : ∀ x, ContinuousOn (fun t => G t x) (Ici 0)
  K : ℝ → X →L[ℝ] X →L[ℝ] X
  K_symm : ∀ τ u v, K τ u v = K τ v u
  CK : ℝ
  K_bound : ∀ τ, 0 < τ → τ ≤ 1 → ‖K τ‖ ≤ CK * τ ^ (-(3 / 4 : ℝ))
  K_cont : ∀ u v, ContinuousOn (fun τ => K τ u v) (Ioi 0)
  K_shift : ∀ s τ, 0 ≤ s → 0 < τ → ∀ u v, G s (K τ u v) = K (s + τ) u v

def MildFramework.toHeatBilinear {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (F : MildFramework X) : HeatBilinear X where
  G := F.G
  G_zero := F.G_zero
  G_add := F.G_add
  G_norm := F.G_norm
  G_cont := F.G_cont
  K := F.K
  K_symm := F.K_symm
  CK := F.CK
  K_bound := F.K_bound
  K_cont := F.K_cont
  K_shift := F.K_shift

abbrev Piece (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (T : ℝ) :=
  C(Icc (0 : ℝ) T, X)

namespace HeatBilinear

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable (H : HeatBilinear X)

def VarConst (u : ℝ → X) (a t : ℝ) : Prop :=
  IntervalIntegrable (fun s => H.K (t - s) (u s) (u s)) volume a t ∧
    u t = H.G (t - a) (u a) + ∫ s in a..t, H.K (t - s) (u s) (u s)

def IsMildOn (u : ℝ → X) (a b : ℝ) : Prop :=
  ContinuousOn u (Ico a b) ∧
    ∀ t ∈ Ico a b, IntervalIntegrable (fun s => H.K (t - s) (u s) (u s)) volume a t ∧
      u t = H.G (t - a) (u a) + ∫ s in a..t, H.K (t - s) (u s) (u s)

def IsMildOnIcc (u : ℝ → X) (a b : ℝ) : Prop :=
  ContinuousOn u (Icc a b) ∧
    ∀ t ∈ Icc a b, IntervalIntegrable (fun s => H.K (t - s) (u s) (u s)) volume a t ∧
      u t = H.G (t - a) (u a) + ∫ s in a..t, H.K (t - s) (u s) (u s)

def HasCompactKernel : Prop :=
  ∃ S : Set X, Dense S ∧ ∀ f ∈ S, ∀ τ, 0 < τ → IsCompactOperator (H.K τ f)

end HeatBilinear

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def extendPiece {T : ℝ} (f : Piece X T) (t : ℝ) : X :=
  if h : 0 ≤ T then Set.IccExtend h f t else 0

open Classical in
def toPiece (T : ℝ) (f : ℝ → X) : Piece X T :=
  if h : Continuous (fun t : Icc (0 : ℝ) T => f t) then ⟨fun t => f t, h⟩ else 0

def pieceEnd (T : ℝ) : Piece X T →L[ℝ] X :=
  if h : 0 ≤ T then ContinuousMap.evalCLM ℝ (⟨T, h, le_rfl⟩ : Icc (0 : ℝ) T) else 0

namespace HeatBilinear

variable [CompleteSpace X] (H : HeatBilinear X)

open Classical in
def pieceBil (T : ℝ) : Piece X T →L[ℝ] Piece X T →L[ℝ] Piece X T :=
  if h : ∃ B : Piece X T →L[ℝ] Piece X T →L[ℝ] Piece X T, ∀ f g (t : Icc (0 : ℝ) T),
      B f g t = ∫ s in (0 : ℝ)..t, H.K (t - s) (extendPiece f s) (extendPiece g s)
  then h.choose else 0

open Classical in
def pieceFree (T : ℝ) : X →L[ℝ] Piece X T :=
  if h : ∃ L : X →L[ℝ] Piece X T, ∀ x (t : Icc (0 : ℝ) T), L x t = H.G t x
  then h.choose else 0

end HeatBilinear

def iterProd {E : Type*} [Monoid E] (M : ℕ → E) : ℕ → E
  | 0 => 1
  | n + 1 => M n * iterProd M n

def stepMap {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (A : ℕ → Y →L[ℝ] Y) (Γ : E →L[ℝ] Y) (Ev : Y →L[ℝ] E) (n : ℕ) : E →L[ℝ] E :=
  Ev.comp ((Ring.inverse (1 - A n)).comp Γ)

def orbitSeq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (M : E →L[ℝ] E) (θ : ℝ)
    (c : ℕ → E) (x₀ : E) : ℕ → E
  | 0 => x₀
  | n + 1 => θ⁻¹ • (M (orbitSeq M θ c x₀ n) + c n)

namespace MildFramework

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable (F : MildFramework X)

abbrev stepLength (P : ℝ) (k : ℕ) : ℝ := 1 - Real.exp (-(P / k))

def selfSimilar (w : ℝ → X) (s₀ t : ℝ) : X := F.D (1 - t)⁻¹ (w (s₀ - Real.log (1 - t)))

def profilePiece (w : ℝ → X) (P : ℝ) (k n : ℕ) : Piece X (stepLength P k) :=
  toPiece (stepLength P k) (F.selfSimilar w (n * (P / k)))

def stepOp (w : ℝ → X) (P : ℝ) (k n : ℕ) : Piece X (stepLength P k) →L[ℝ] Piece X (stepLength P k) :=
  (2 : ℝ) • F.toHeatBilinear.pieceBil (stepLength P k) (F.profilePiece w P k n)

def stepFree (P : ℝ) (k : ℕ) : X →L[ℝ] Piece X (stepLength P k) :=
  F.toHeatBilinear.pieceFree (stepLength P k)

def stepEnd (P : ℝ) (k : ℕ) : Piece X (stepLength P k) →L[ℝ] X :=
  (F.D (Real.exp (-(P / k)))).comp (pieceEnd (stepLength P k))

theorem isMildOn_iff (u : ℝ → X) (a b : ℝ) :
    F.IsMildOn u a b ↔ F.toHeatBilinear.IsMildOn u a b := Iff.rfl

theorem isMildOnIcc_iff (u : ℝ → X) (a b : ℝ) :
    F.IsMildOnIcc u a b ↔ F.toHeatBilinear.IsMildOnIcc u a b := Iff.rfl

theorem hasCompactKernel : F.toHeatBilinear.HasCompactKernel := F.compact

def stepIndex (μ t : ℝ) : ℕ := ⌊Real.log (1 - t) / Real.log μ⌋₊

def gluePieces (μ : ℝ) (u : ℕ → Piece X (1 - μ)) (t : ℝ) : X :=
  F.D (μ ^ stepIndex μ t)⁻¹
    (extendPiece (u (stepIndex μ t)) ((t - (1 - μ ^ stepIndex μ t)) / μ ^ stepIndex μ t))

end MildFramework

end Breakdown
