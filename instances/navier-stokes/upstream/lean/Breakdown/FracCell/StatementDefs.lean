import Breakdown.FracCert.Defs

noncomputable section

namespace Breakdown

end Breakdown

end

section

open scoped ContDiff ENNReal

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

open SteadyCert

def permSign (i j l : Fin 3) : ℝ :=
  if (i.val, j.val, l.val) = (0, 1, 2) ∨ (i.val, j.val, l.val) = (1, 2, 0) ∨ (i.val, j.val, l.val) = (2, 0, 1) then 1
  else if (i.val, j.val, l.val) = (0, 2, 1) ∨ (i.val, j.val, l.val) = (2, 1, 0) ∨ (i.val, j.val, l.val) = (1, 0, 2) then -1
  else 0

def entry (M : Space →L[ℝ] Space) (a b : Fin 3) : ℝ := M (unitVector b) a

def curlOf (M : Space →L[ℝ] Space) : Space :=
  ∑ i : Fin 3, (∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * entry M l j) • unitVector i

def crossVec (a b : Space) : Space :=
  EuclideanSpace.single 0 (a 1 * b 2 - a 2 * b 1) + EuclideanSpace.single 1 (a 2 * b 0 - a 0 * b 2) +
    EuclideanSpace.single 2 (a 0 * b 1 - a 1 * b 0)

def symPart (M : Space →L[ℝ] Space) : Space →L[ℝ] Space := (1 / 2 : ℝ) • (M + ContinuousLinearMap.adjoint M)

def curlGradMatrix (H : Space →L[ℝ] Space →L[ℝ] Space) : Space →L[ℝ] Space :=
  ∑ j : Fin 3, ∑ l : Fin 3,
    (∑ b : Fin 3, ∑ q : Fin 3, permSign j b q * H (unitVector l) (unitVector b) q)
      • ((innerSL ℝ (unitVector l)).smulRight (unitVector j))

def ratioFn (lam x : ℝ) : ℝ := x / (lam + x)

structure FracCellData (k N : ℕ) extends FracCertData k N where
  innerWeight : ℝ
  curlWeight : ℝ
  cellRegion : Set Space
  cellWeight : Space → ℝ
  centre : Space → Space
  centreSecond : Space → (Space →L[ℝ] Space →L[ℝ] Space)
  modelVelocity : Space → Space
  modelCurl : Space → Space
  modelStrain : Space → (Space →L[ℝ] Space)
  modelCurlGrad : Space → (Space →L[ℝ] Space)
  modelRate : ℝ
  modelActuator : Fin k → Space → Space
  modelActuatorGrad : Fin k → Space → (Space →L[ℝ] Space)
  modelPinField : Fin k → Space → (Space →L[ℝ] Space)
  actuatorGrad : Fin k → Space → (Space →L[ℝ] Space)
  centreLoss : ℝ
  rateLoss : ℝ
  strainLoss : ℝ
  curlGradLoss : ℝ
  velocityLoss : ℝ
  curlLoss : ℝ
  actuatorGradLoss : ℝ
  actuatorLoss : ℝ
  pinFieldLoss : ℝ
  blockIndex : Fin N → ℕ
  spectralBound : ℕ → ℝ → ℝ
  baseCoef : ℝ
  levelCount : ℕ
  levelCoef : Fin levelCount → ℝ
  levelRate : Fin levelCount → ℝ
  cutoff : ℝ
  tailConst : ℝ

namespace FracCellData

variable {k N : ℕ} (c : FracCellData k N)

def centreGrad : Space → (Space →L[ℝ] Space) := fun y => fderiv ℝ c.centre y

def centreCurl (y : Space) : Space := curlOf (c.centreGrad y)

def centreStrain (y : Space) : Space →L[ℝ] Space := symPart (c.centreGrad y)

def centreCurlGrad (y : Space) : Space →L[ℝ] Space := curlGradMatrix (c.centreSecond y)

def strainError (y : Space) : Space →L[ℝ] Space := c.centreStrain y - c.modelStrain y

def curlGradError (y : Space) : Space →L[ℝ] Space := c.centreCurlGrad y - c.modelCurlGrad y

def velocityError (y : Space) : Space := Set.indicator c.cellRegion (fun z => c.centre z - c.modelVelocity z) y

def curlError (y : Space) : Space := Set.indicator c.cellRegion (fun z => c.centreCurl z - c.modelCurl z) y

def gapSymbol (α x : ℝ) : ℝ := x ^ (α - 1) - c.splitVisc

def fullSymbol (α x : ℝ) : ℝ := c.gapSymbol α x + c.reducedCoercivity * (1 + c.weightMin / x)

def ratioSymbol (α x : ℝ) : ℝ := c.gapSymbol α x ^ 2 / c.fullSymbol α x

def levelSum (x : ℝ) : ℝ := c.baseCoef + ∑ i, c.levelCoef i * ratioFn (c.levelRate i) x

end FracCellData

end CellCert

end Breakdown

end
end

section

open Matrix

noncomputable section

namespace Breakdown.CellCert.Finite

def quadValue {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := x ⬝ᵥ (M *ᵥ x)

def IsPositiveOn {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (P : Submodule ℝ (ι → ℝ)) : Prop :=
  ∀ y ∈ P, y ≠ 0 → 0 < quadValue M y

structure TreeCertificate (a b : ℕ) where
  Cell : Type
  cellFintype : Fintype Cell
  Node : Type
  nodeFintype : Fintype Node
  cellForm : Cell → Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ
  cellNode : Cell → Node
  parent : Node → Option Node
  rank : Node → ℕ
  eliminated : Node → Finset (Fin a)
  front : Node → Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ
  root : Node
  globalForm : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ

namespace TreeCertificate

variable {a b : ℕ} (T : TreeCertificate a b)

open Classical in
def nodeInput (ν : T.Node) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ :=
  haveI := T.cellFintype; haveI := T.nodeFintype
  (∑ c ∈ Finset.univ.filter (fun c => T.cellNode c = ν), T.cellForm c)
    + ∑ μ ∈ Finset.univ.filter (fun μ => T.parent μ = some ν), T.front μ

def IsEliminatedSomewhere (i : Fin a) : Prop := ∃ ν, i ∈ T.eliminated ν

def rootSpace : Submodule ℝ (Fin a ⊕ Fin b → ℝ) where
  carrier := {x | ∀ i, T.IsEliminatedSomewhere i → x (Sum.inl i) = 0}
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro c x hx i hi
    simp [hx i hi]

end TreeCertificate

structure IsTreeCertificate {a b : ℕ} (T : TreeCertificate a b) : Prop where
  cell_symm : ∀ c, (T.cellForm c)ᵀ = T.cellForm c
  front_symm : ∀ ν, (T.front ν)ᵀ = T.front ν
  parent_rank : ∀ ν μ, T.parent ν = some μ → T.rank ν < T.rank μ
  root_parent : T.parent T.root = none
  only_root : ∀ ν, T.parent ν = none → ν = T.root
  eliminated_disjoint : ∀ ν μ, ν ≠ μ → Disjoint (T.eliminated ν) (T.eliminated μ)
  front_support : ∀ ν (x y : Fin a ⊕ Fin b → ℝ),
    (∀ i, i ∉ T.eliminated ν → x (Sum.inl i) = y (Sum.inl i)) → (∀ j, x (Sum.inr j) = y (Sum.inr j)) →
    quadValue (T.front ν) x = quadValue (T.front ν) y
  node_bound : ∀ ν (x : Fin a ⊕ Fin b → ℝ), quadValue (T.front ν) x ≤ quadValue (T.nodeInput ν) x
  root_independent : ∀ (x y : Fin a ⊕ Fin b → ℝ),
    (∀ i, ¬ T.IsEliminatedSomewhere i → x (Sum.inl i) = y (Sum.inl i)) → (∀ j, x (Sum.inr j) = y (Sum.inr j)) →
    quadValue (T.front T.root + T.globalForm) x = quadValue (T.front T.root + T.globalForm) y
  root_positive : ∃ P : Submodule ℝ (Fin a ⊕ Fin b → ℝ), P ≤ T.rootSpace ∧
    Nat.card {i : Fin a // ¬ T.IsEliminatedSomewhere i} ≤ Module.finrank ℝ P ∧
    IsPositiveOn (T.front T.root + T.globalForm) P

end Breakdown.CellCert.Finite

end
end

section

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace Assembly

open SteadyCert _root_.Breakdown.CellCert.Finite

abbrev FieldTuple (k : ℕ) :=
  (Space → Space) × (Space → (Space →L[ℝ] Space)) × (Space → (Space →L[ℝ] Space →L[ℝ] Space)) ×
    (Fin k → ℝ) × (Space → Space)

structure CellSplit (k N : ℕ) where
  cellCount : ℕ
  cell : Fin cellCount → Set Space
  rowCell : Fin N → Fin cellCount
  slots : ℕ
  moment : FieldTuple k → Fin slots → ℝ
  freeMap : Matrix (Fin slots) (Fin k) ℝ
  kappaSlot : Fin k → Fin slots
  cellMatrix : Fin cellCount → Matrix (Fin slots ⊕ Fin k) (Fin slots ⊕ Fin k) ℝ
  delayCount : ℕ
  delayForm : Fin delayCount → Matrix (Fin slots ⊕ Fin k) (Fin slots ⊕ Fin k) ℝ

namespace CellSplit

variable {k N : ℕ} (c : FracCellData k N) (S : CellSplit k N)

def globalMatrix : Matrix (Fin S.slots ⊕ Fin k) (Fin S.slots ⊕ Fin k) ℝ :=
  Matrix.diagonal (Sum.elim
    (fun j => if ∃ i, S.kappaSlot i = j then -(c.coercivity * c.multiplierScale ^ 2) else 0)
    (fun _ => -(1 / c.pinWeight)))

end CellSplit

end Assembly

end CellCert

end Breakdown

end
end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Exterior

open SteadyCert Assembly

def traceFreeConst : ℝ := Real.sqrt (7 / 2)

structure ExteriorData where
  radius : Space → ℝ
  radiusMin : ℝ
  radiusMax : ℝ
  strainBound : Space → ℝ
  meanCurlGradBound : Space → ℝ
  waveCurlGradBound : Space → ℝ
  splitLength : Space → ℝ
  coefLower : ℝ
  weightedWave : ℝ
  weightedMean : ℝ

namespace ExteriorData

variable {k N : ℕ} (c : FracCellData k N) (e : ExteriorData)

def gradientCoef (α : ℝ) (y : Space) : ℝ :=
  c.curlWeight - c.coercivity * c.weight y - (traceFreeConst / 2) * e.waveCurlGradBound y * e.splitLength y
    + 2 * min (1 - 3 / (4 * α) - c.curlWeight - e.strainBound y) 0

end ExteriorData

end Exterior

end CellCert

end Breakdown

end
end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

def cylRadius (y : Space) : ℝ := Real.sqrt (y 0 ^ 2 + y 1 ^ 2)

def cylHeight (y : Space) : ℝ := y 2

def cylPoint (r θ z : ℝ) : Space :=
  EuclideanSpace.single 0 (r * Real.cos θ) + EuclideanSpace.single 1 (r * Real.sin θ) + EuclideanSpace.single 2 z

def radialUnit (θ : ℝ) : Space := EuclideanSpace.single 0 (Real.cos θ) + EuclideanSpace.single 1 (Real.sin θ)

def angularUnit (θ : ℝ) : Space := EuclideanSpace.single 0 (-Real.sin θ) + EuclideanSpace.single 1 (Real.cos θ)

def axialUnit : Space := EuclideanSpace.single 2 1

def frameVec (θ : ℝ) (u : Space) : Fin 3 → ℝ :=
  ![inner ℝ u (radialUnit θ), inner ℝ u (angularUnit θ), inner ℝ u axialUnit]

def frameMat (θ : ℝ) (M : Space →L[ℝ] Space) : Fin 3 → Fin 3 → ℝ :=
  fun a b => inner ℝ (M (![radialUnit θ, angularUnit θ, axialUnit] b)) (![radialUnit θ, angularUnit θ, axialUnit] a)

def azimuth (m : ℕ) (n : ℤ) : ℝ := (n : ℝ) * m

def modeVec (m : ℕ) (n : ℤ) (v : Space → Space) (r z : ℝ) : Fin 3 → ℂ :=
  fun a => (1 / (2 * Real.pi) : ℂ) *
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (frameVec θ (v (cylPoint r θ z)) a : ℂ)

def modeMat (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (r z : ℝ) : Fin 3 → Fin 3 → ℂ :=
  fun a b => (1 / (2 * Real.pi) : ℂ) *
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (frameMat θ (G (cylPoint r θ z)) a b : ℂ)

structure CellBox where
  r₁ : ℝ
  r₂ : ℝ
  z₁ : ℝ
  z₂ : ℝ

namespace CellBox

variable (K : CellBox)

def IsAxis : Prop := K.r₁ = 0

def rect : Set (ℝ × ℝ) := Set.Icc K.r₁ K.r₂ ×ˢ Set.Icc K.z₁ K.z₂

def solid : Set Space :=
  {y | K.r₁ ≤ cylRadius y ∧ cylRadius y ≤ K.r₂ ∧ K.z₁ ≤ |cylHeight y| ∧ |cylHeight y| ≤ K.z₂}

open Classical in
def lineWeight (r : ℝ) : ℝ := if K.r₁ = 0 then r else 1

def refR (r : ℝ) : ℝ := (2 * r - K.r₁ - K.r₂) / (K.r₂ - K.r₁)

def refZ (z : ℝ) : ℝ := (2 * z - K.z₁ - K.z₂) / (K.z₂ - K.z₁)

end CellBox

structure IsCellBox (K : CellBox) : Prop where
  r_order : 0 ≤ K.r₁ ∧ K.r₁ < K.r₂
  z_order : 0 ≤ K.z₁ ∧ K.z₁ < K.z₂

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

namespace CellBox

variable (K : CellBox)

open Classical in
def innerRadius : ℝ := if K.r₁ = 0 then 1 else K.r₁

def radialDeriv (P : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := deriv (fun r : ℝ => P (r, p.2)) p.1

def heightDeriv (P : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := deriv (fun z : ℝ => P (p.1, z)) p.2

end CellBox

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

def frameUnit (θ : ℝ) : Fin 3 → Space := ![radialUnit θ, angularUnit θ, axialUnit]

def frameThird (θ : ℝ) (H : Space →L[ℝ] Space →L[ℝ] Space) (a b c : Fin 3) : ℝ :=
  inner ℝ (H (frameUnit θ c) (frameUnit θ b)) (frameUnit θ a)

def modeThird (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b c : Fin 3) (p : ℝ × ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
      (frameThird θ (H (cylPoint p.1 θ p.2)) a b c : ℂ)

def gradMode (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (a b : Fin 3) (p : ℝ × ℝ) : ℂ :=
  modeMat m n G p.1 p.2 a b

def curlComp (s : Fin 3 → Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  ∑ j : Fin 3, ∑ l : Fin 3, (CellCert.permSign i j l : ℂ) * s l j

namespace CellBox

variable (K : CellBox)

end CellBox

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

namespace CellBox

variable (K : CellBox)

open Classical in
def angularWeight (n : ℤ) : ℝ :=
  if K.r₁ = 0 then (if n = 0 then 0 else K.r₂⁻¹ ^ 2) else K.r₂⁻¹

end CellBox

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

structure CellBases where
  radialCoef : ℕ → ℕ → ℝ
  heightCoef : ℕ → ℕ → ℝ

namespace CellBases

variable (B : CellBases)

def radialPoly (j : ℕ) (r : ℝ) : ℝ := ∑ i ∈ Finset.range (j + 1), B.radialCoef j i * r ^ i

def heightPoly (l : ℕ) (z : ℝ) : ℝ := ∑ i ∈ Finset.range (l + 1), B.heightCoef l i * z ^ i

def coef (K : CellBox) (F : ℝ × ℝ → ℂ) (j l : ℕ) : ℂ :=
  ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)

end CellBases

structure IsCellBases (K : CellBox) (B : CellBases) : Prop where
  radial_leading : ∀ j, 0 < B.radialCoef j j
  height_leading : ∀ l, 0 < B.heightCoef l l
  radial_orthonormal : ∀ j j', ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * B.radialPoly j r * B.radialPoly j' r =
    if j = j' then 1 else 0
  height_orthonormal : ∀ l l', ∫ z in Set.Icc K.z₁ K.z₂, B.heightPoly l z * B.heightPoly l' z =
    if l = l' then 1 else 0

def radialEigen (K : CellBox) (j : ℕ) : ℝ :=
  if K.r₁ = 0 then (j : ℝ) * (j + 2) * (2 / (K.r₂ - K.r₁)) ^ 2 else (j : ℝ) * (j + 1) * (2 / (K.r₂ - K.r₁)) ^ 2

def heightEigen (K : CellBox) (l : ℕ) : ℝ := (l : ℝ) * (l + 1) * (2 / (K.z₂ - K.z₁)) ^ 2

def sumSq (s : Fin 3 → Fin 3 → ℂ) : ℝ := ∑ a : Fin 3, ∑ b : Fin 3, ‖s a b‖ ^ 2

def vecSq (v : Fin 3 → ℂ) : ℝ := ∑ a : Fin 3, ‖v a‖ ^ 2

def curlSq (s : Fin 3 → Fin 3 → ℂ) : ℝ := ∑ i : Fin 3, ‖curlComp s i‖ ^ 2

def pairVec (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) : Fin 12 → ℂ :=
  fun i => if h : i.val < 9 then s ⟨i.val / 3, by omega⟩ ⟨i.val % 3, Nat.mod_lt _ (by norm_num)⟩
    else v ⟨i.val - 9, by omega⟩

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

structure CellScalars where
  degLow : ℕ
  degHigh : ℕ
  degNear : ℕ
  resolved : Finset ℤ
  band : Finset ℤ
  strainBound : ℝ × ℝ → ℝ
  meanGradBound : ℝ × ℝ → ℝ
  waveGradBound : ℝ × ℝ → ℝ
  splitLength : ℝ
  energyWeight : ℤ → ℝ
  vorticityWeight : ℤ → ℝ
  localMatrix : ℤ → ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ
  curlAbsorb : ℤ → ℝ
  strainAbsorb : ℤ → ℝ
  velocityAbsorb : ℤ → ℝ
  tailShift : ℤ → ℝ
  penaltyStrain : ℝ
  penaltyCurl : ℝ
  penaltyVelocity : ℝ
  weightFloor : ℝ
  symWeight : ℤ → ℕ → ℕ → ℝ
  antiWeight : ℤ → ℕ → ℕ → ℝ
  velWeight : ℤ → ℕ → ℕ → ℝ

namespace CellScalars

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)

def sampleWeight (p : ℝ × ℝ) : ℝ := c.weight (cylPoint p.1 0 p.2)

def rHat (p : ℝ × ℝ) : ℝ := p.1 / K.lineWeight p.1

def tailLam (j l : ℕ) : ℝ := CellBox.innerRadius K * (radialEigen K j + heightEigen K l)

end CellScalars

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

def modeNumber (m : ℕ) (n : ℤ) : ℝ := |azimuth m n|

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

def bracketMat (u : Fin 3 → ℂ) : Fin 3 → Fin 3 → ℂ :=
  fun i l => ∑ j : Fin 3, (CellCert.permSign i l j : ℂ) * u j

def couplingMap (Gm : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) : Fin 3 → Fin 3 → ℂ :=
  fun i l => -bracketMat (fun a => ∑ b : Fin 3, Gm a b * v b) i l
    + (1 / 2 : ℂ) * ∑ q : Fin 3, bracketMat v i q * Gm l q

def entryPairing (s t : Fin 3 → Fin 3 → ℂ) : ℂ := ∑ a : Fin 3, ∑ b : Fin 3, s a b * (starRingEnd ℂ) (t a b)

def waveForm (Sβ Gβ Gmβ : Fin 3 → Fin 3 → ℂ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ)
    (s' : Fin 3 → Fin 3 → ℂ) (v' : Fin 3 → ℂ) : ℂ :=
  -(∑ a : Fin 3, (starRingEnd ℂ) (curlComp s a) * ∑ b : Fin 3, Sβ a b * curlComp s' b)
    + (1 / 2 : ℂ) * entryPairing (couplingMap Gβ v') s + (1 / 2 : ℂ) * entryPairing s' (couplingMap Gmβ v)

structure CellClasses where
  count : ℕ
  modes : Fin count → Finset ℤ
  strainDev : Fin count → ℝ × ℝ → ℝ
  gradDev : Fin count → ℝ × ℝ → ℝ
  velocityDev : Fin count → ℝ × ℝ → ℝ
  curlDev : Fin count → ℝ × ℝ → ℝ
  shareWeight : Fin count → ℝ
  rowWeight : Fin count → ℝ
  resolvedPart : Fin count → Finset ℤ

namespace CellClasses

variable (Cl : CellClasses)

end CellClasses

namespace CellBox

variable (K : CellBox)

end CellBox

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

namespace CellBox

variable (K : CellBox)

end CellBox

namespace CellScalars

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (Cl : CellClasses)

def strainMode (β : ℤ) (p : ℝ × ℝ) : Fin 3 → Fin 3 → ℂ := modeMat c.order β c.modelStrain p.1 p.2

def curlGradMode (β : ℤ) (p : ℝ × ℝ) : Fin 3 → Fin 3 → ℂ := modeMat c.order β c.modelCurlGrad p.1 p.2

end CellScalars

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

def curlAdj (u : Fin 3 → ℂ) : Fin 3 → Fin 3 → ℂ :=
  fun l j => ∑ i : Fin 3, (CellCert.permSign i j l : ℂ) * u i

def couplingAdj (Gm : Fin 3 → Fin 3 → ℂ) (s : Fin 3 → Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun b => ∑ i : Fin 3, ∑ l : Fin 3,
    (-(∑ j : Fin 3, (CellCert.permSign i l j : ℂ) * (starRingEnd ℂ) (Gm j b))
      + (1 / 2 : ℂ) * ∑ q : Fin 3, (CellCert.permSign i q b : ℂ) * (starRingEnd ℂ) (Gm l q)) * s i l

def matVec (S : Fin 3 → Fin 3 → ℂ) (u : Fin 3 → ℂ) : Fin 3 → ℂ := fun a => ∑ b : Fin 3, S a b * u b

def waveActionStrain (Sβ Gβ : Fin 3 → Fin 3 → ℂ) (s' : Fin 3 → Fin 3 → ℂ) (v' : Fin 3 → ℂ) :
    Fin 3 → Fin 3 → ℂ :=
  fun a b => -curlAdj (matVec Sβ (curlComp s')) a b + (1 / 2 : ℂ) * couplingMap Gβ v' a b

def waveActionVelocity (Gmβ : Fin 3 → Fin 3 → ℂ) (s' : Fin 3 → Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun b => (1 / 2 : ℂ) * couplingAdj Gmβ s' b

def splitStrain (U : Fin 12 → ℂ) : Fin 3 → Fin 3 → ℂ := fun a b => U ⟨3 * a.val + b.val, by omega⟩

def splitVelocity (U : Fin 12 → ℂ) : Fin 3 → ℂ := fun a => U ⟨9 + a.val, by omega⟩

def matAct (A : Matrix (Fin 12) (Fin 12) ℂ) (U : Fin 12 → ℂ) : Fin 12 → ℂ := fun i => ∑ j, A i j * U j

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

def turnAdjInv (k : ℝ) (w : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![(1 / (1 - (k : ℂ) ^ 2)) * (-(k : ℂ) * Complex.I * w 0 - w 1),
    (1 / (1 - (k : ℂ) ^ 2)) * (w 0 - (k : ℂ) * Complex.I * w 1),
    w 2 / (-(k : ℂ) * Complex.I)]

def foldVelocity (k r : ℝ) (Ys : Fin 3 → Fin 3 → ℂ) (Yv : Fin 3 → ℂ) : Fin 3 → Fin 3 → ℂ :=
  fun a b => Ys a b + (if b = 1 then (r : ℂ) * turnAdjInv k Yv a else 0)

structure CellRows (N slots k : ℕ) where
  yModes : Finset ℤ
  rowModes : Finset ℤ
  rowSet : Finset (Fin N)
  farShare : ℝ
  multiplierMatrix : Matrix (Fin N) (Fin N) ℝ
  reducerCount : ℕ
  reducer : Matrix (Fin reducerCount) (Fin N) ℝ
  farSupport : Finset (ℤ × Fin 3 × Fin 4 × ℕ × ℕ)
  farKernel : (ℤ × Fin 3 × Fin 4 × ℕ × ℕ) ⊕ (Fin k ⊕ Fin k) → (ℤ × Fin 3 × Fin 4 × ℕ × ℕ) ⊕ (Fin k ⊕ Fin k) → ℂ
  classRowWeight : Fin N → ℝ
  rowModeOf : Fin N → ℤ

namespace CellScalars

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)

end CellScalars

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

def crossC (a b : Fin 3 → ℂ) : Fin 3 → ℂ := ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

def conjVec3 (a : Fin 3 → ℂ) : Fin 3 → ℂ := fun i => (starRingEnd ℂ) (a i)

def cartOfFrame (θ : ℝ) (w : Fin 3 → ℝ) : Space := ∑ a : Fin 3, w a • frameUnit θ a

def cartOpOfFrame (θ : ℝ) (M : Fin 3 → Fin 3 → ℝ) : Space →L[ℝ] Space :=
  ∑ a : Fin 3, ∑ b : Fin 3, M a b • (innerSL ℝ (frameUnit θ b)).smulRight (frameUnit θ a)

def cylAngle (y : Space) : ℝ := Complex.arg ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I)

namespace CellScalars

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)

variable {slots : ℕ} (R : CellRows N slots k)

def rowMode (a : Fin N) (n : ℤ) (p : ℝ × ℝ) : Fin 3 → ℂ := modeVec c.order n (c.row a) p.1 p.2

def rowCouplingStrain (a : Fin N) (n' : ℤ) (p : ℝ × ℝ) : Fin 3 → Fin 3 → ℂ := fun i l =>
  ((rHat K p : ℝ) : ℂ) * ∑ n ∈ R.rowModes,
    curlAdj (crossC (conjVec3 (modeVec c.order (n - n') c.modelVelocity p.1 p.2)) (rowMode c a n p)) i l

def rowCouplingVelocity (a : Fin N) (n' : ℤ) (p : ℝ × ℝ) : Fin 3 → ℂ := fun i =>
  ((rHat K p : ℝ) : ℂ) * ∑ n ∈ R.rowModes,
    crossC (rowMode c a n p) (conjVec3 (modeVec c.order (n - n') c.modelCurl p.1 p.2)) i

def rowCouplingFolded (a : Fin N) (n' : ℤ) (p : ℝ × ℝ) : Fin 3 → Fin 3 → ℂ :=
  if n' ∈ S.resolved then rowCouplingStrain c K R a n' p
  else foldVelocity (azimuth c.order n') p.1 (rowCouplingStrain c K R a n' p) (rowCouplingVelocity c K R a n' p)

def sigmaWeightedPair (X Y : Fin 3 → Fin 3 → ℂ) (hs ha : ℝ) : ℂ :=
  entryPairing (fun a b => (Y a b + Y b a) / 2) (fun a b => (X a b + X b a) / 2) / hs
    + entryPairing (fun a b => (Y a b - Y b a) / 2) (fun a b => (X a b - X b a) / 2) / ha

def rowSquare (B : CellBases) (μ : Fin N → ℝ) (sel : ℕ → ℕ → Prop) [DecidableRel sel] : ℝ :=
  (∑ n' ∈ S.resolved ∪ S.band, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
    if sel j l ∧ (n' ∉ S.resolved ∨ S.degHigh < max j l) then
      (sigmaWeightedPair
        (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => rowCouplingFolded c K S R a n' p i q) j l)
        (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => rowCouplingFolded c K S R a n' p i q) j l)
        (S.symWeight n' j l) (S.antiWeight n' j l)).re
    else 0)
  + ∑ n' ∈ S.resolved, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
    if sel j l ∧ S.degHigh ≤ max j l then
      vecSq (fun i => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => rowCouplingVelocity c K R a n' p i) j l)
        / S.velWeight n' j l
    else 0

end CellScalars

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

def classField (m : ℕ) (modes : Finset ℤ) (F : Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) (θ : ℝ) : Fin 3 → Fin 3 → ℂ :=
  fun a b => ∑ β ∈ modes, modeMat m β F p.1 p.2 a b * Complex.exp ((azimuth m β * θ : ℝ) * Complex.I)

def classVec (m : ℕ) (modes : Finset ℤ) (F : Space → Space) (p : ℝ × ℝ) (θ : ℝ) : Fin 3 → ℂ :=
  fun a => ∑ β ∈ modes, modeVec m β F p.1 p.2 a * Complex.exp ((azimuth m β * θ : ℝ) * Complex.I)

def OpBound (M : Fin 3 → Fin 3 → ℂ) (δ : ℝ) : Prop := ∀ u : Fin 3 → ℂ, vecSq (matVec M u) ≤ δ ^ 2 * vecSq u

end CellAnalysis

end CellCert

end Breakdown

end
end

section

open Matrix

noncomputable section

namespace Breakdown.CellCert.CellFormula

structure ParamData (D : Type) [Fintype D] [DecidableEq D] where
  relCount : ℕ
  relation : Matrix (Fin relCount) D ℂ
  solved : Fin relCount → D
  skeleton : Finset D

namespace ParamData

variable {D : Type} [Fintype D] [DecidableEq D] (P : ParamData D)

def solvedSet : Finset D := Finset.univ.image P.solved

def freeSet : Finset D := Finset.univ.filter (fun d => d ∉ P.solvedSet)

def interiorSet : Finset D := P.freeSet.filter (fun d => d ∉ P.skeleton)

def solvedBlock : Matrix (Fin P.relCount) (Fin P.relCount) ℂ := fun i j => P.relation i (P.solved j)

def freePart (u : D → ℂ) : D → ℂ := fun d => if d ∈ P.solvedSet then 0 else u d

def param (w : D → ℂ) : D → ℂ :=
  P.freePart w - ∑ j : Fin P.relCount, Pi.single (P.solved j)
    ((P.solvedBlock⁻¹ *ᵥ (P.relation *ᵥ P.freePart w)) j)

end ParamData

structure IsParamData {D : Type} [Fintype D] [DecidableEq D] (P : ParamData D) : Prop where
  solved_injective : Function.Injective P.solved
  solved_not_skeleton : ∀ j, P.solved j ∉ P.skeleton
  solvedBlock_invertible : IsUnit P.solvedBlock.det

def quadFormValue {D : Type} [Fintype D] (Φ : Matrix D D ℂ) (u : D → ℂ) : ℝ :=
  (star u ⬝ᵥ (Φ *ᵥ u)).re

end Breakdown.CellCert.CellFormula

end
end

section

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis

def edgeSign (c o : ℝ) : ℂ := if o < c then 1 else -1

def radialStripMoment (c o lo hi : ℝ) (F dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ) : ℂ :=
  edgeSign c o * ∫ p in Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi,
    ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((t p.2 : ℝ) : ℂ)

def heightStripMoment (c o lo hi : ℝ) (wt : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ) : ℂ :=
  edgeSign c o * ∫ p in Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o),
    ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((wt p.1 * t p.1 : ℝ) : ℂ)

def cornerMoment (cr orr cz oz : ℝ) (F Fr Fz Frz : ℝ × ℝ → ℂ) : ℂ :=
  edgeSign cr orr * edgeSign cz oz *
    ∫ p in Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min cz oz) (max cz oz),
      ((((1 / (cr - orr) : ℝ)) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * F p
        + (((1 / (cr - orr) : ℝ)) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Fz p
        + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * Fr p
        + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Frz p)

structure FaceSegment where
  radial : Bool
  level : ℝ
  other : ℝ
  lo : ℝ
  hi : ℝ
  testCoef : ℕ → ℕ → ℝ

namespace FaceSegment

variable (S : FaceSegment)

def test (d : ℕ) (s : ℝ) : ℝ := ∑ i ∈ Finset.range (d + 1), S.testCoef d i * s ^ i

def moment (weighted : Bool) (F dFr dFz : ℝ × ℝ → ℂ) (d : ℕ) : ℂ :=
  if S.radial then radialStripMoment S.level S.other S.lo S.hi F dFr (S.test d)
  else heightStripMoment S.level S.other S.lo S.hi (fun r => if weighted then r else 1) F dFz (S.test d)

end FaceSegment

structure IsFaceSegment (S : FaceSegment) : Prop where
  other_ne : S.other ≠ S.level
  lo_lt_hi : S.lo < S.hi
  test_leading : ∀ d, S.testCoef d d ≠ 0

def presMode (m : ℕ) (n : ℤ) (P : Space → ℝ) (r z : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (P (cylPoint r θ z) : ℂ)

open Classical in
def IsPotentialOf (Q : Space → Space) (q : Space → ℝ) : Prop :=
  AEStronglyMeasurable q volume ∧ IsLocalSquareIntegrable (fun y => q y ^ 2) ∧
    ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * q y = -∫ y, φ y * inner ℝ (Q y) (unitVector j)

open Classical in
def potentialOf (Q : Space → Space) : Space → ℝ :=
  if h : ∃ q, IsPotentialOf Q q then h.choose else fun _ => 0

structure CellLayout where
  order : ℕ
  box : CellBox
  bases : CellBases
  modes : Finset ℤ
  degCoef : ℕ
  degSide : ℕ
  segCount : ℕ
  segment : Fin segCount → FaceSegment
  presCount : ℕ
  presSegment : Fin presCount → FaceSegment
  cornerCount : ℕ
  corner : Fin cornerCount → ℝ × ℝ
  cornerOther : Fin cornerCount → ℝ × ℝ
  segEnd : Fin segCount → Fin 2 → Option (Fin cornerCount)
  cellCorner : Fin 2 → Fin 2 → Option (Fin cornerCount)
  sideSegments : Fin 4 → Finset (Fin segCount)
  gauge : FaceSegment
  gaugeDeleted : Finset (Fin presCount × Fin degSide)

abbrev CellDatum (modes : Finset ℤ) (Q q segs psegs corners : ℕ) :=
  (modes × Fin 3 × Fin 3 × Fin (Q + 1) × Fin (Q + 1)) ⊕ (modes × Fin 3 × Fin Q × Fin Q) ⊕
    (modes × Fin segs × Fin 3 × Fin (q + 2)) ⊕ (modes × Fin segs × Fin 3 × Fin (q + 1)) ⊕
      (modes × Fin psegs × Fin q) ⊕ (modes × Fin corners × Fin 3) ⊕ Fin corners ⊕
        (modes × Fin 4 × Fin 3 × Fin (Q + 1))

namespace CellDatum

variable {modes : Finset ℤ} {Q q segs psegs corners : ℕ}

def lowStrain (n : modes) (a b : Fin 3) (j l : Fin (Q + 1)) : CellDatum modes Q q segs psegs corners :=
  Sum.inl (n, a, b, j, l)

def lowVelocity (n : modes) (a : Fin 3) (j l : Fin Q) : CellDatum modes Q q segs psegs corners :=
  Sum.inr (Sum.inl (n, a, j, l))

def sideVelocity (n : modes) (s : Fin segs) (a : Fin 3) (d : Fin (q + 2)) :
    CellDatum modes Q q segs psegs corners :=
  Sum.inr (Sum.inr (Sum.inl (n, s, a, d)))

def sideGradient (n : modes) (s : Fin segs) (a : Fin 3) (d : Fin (q + 1)) :
    CellDatum modes Q q segs psegs corners :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl (n, s, a, d))))

def sidePressure (n : modes) (s : Fin psegs) (d : Fin q) : CellDatum modes Q q segs psegs corners :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (n, s, d)))))

def cornerVelocity (n : modes) (c : Fin corners) (a : Fin 3) : CellDatum modes Q q segs psegs corners :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (n, c, a))))))

def cornerStream (c : Fin corners) : CellDatum modes Q q segs psegs corners :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c))))))

def extraVelocity (n : modes) (e : Fin 4) (a : Fin 3) (d : Fin (Q + 1)) :
    CellDatum modes Q q segs psegs corners :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (n, e, a, d)))))))

end CellDatum

namespace CellLayout

variable (L : CellLayout)

abbrev Datum := CellDatum L.modes L.degCoef L.degSide L.segCount L.presCount L.cornerCount

instance instDecEqDatum : DecidableEq L.Datum := Classical.decEq _

instance instFintypeDatum : Fintype L.Datum := by
  unfold Datum CellDatum; infer_instance

def velMode {k : ℕ} (n : ℤ) (x : FieldTuple k) (a : Fin 3) : ℝ × ℝ → ℂ :=
  fun p => modeVec L.order n x.1 p.1 p.2 a

def gradModeOf {k : ℕ} (n : ℤ) (x : FieldTuple k) (a b : Fin 3) : ℝ × ℝ → ℂ :=
  gradMode L.order n x.2.1 a b

def secondModeOf {k : ℕ} (n : ℤ) (x : FieldTuple k) (a b c : Fin 3) : ℝ × ℝ → ℂ :=
  modeThird L.order n x.2.2.1 a b c

def pressureGradMode {k : ℕ} (n : ℤ) (x : FieldTuple k) (a : Fin 3) : ℝ × ℝ → ℂ :=
  fun p => modeVec L.order n x.2.2.2.2 p.1 p.2 a

def gaugeValue {k : ℕ} (x : FieldTuple k) : ℂ :=
  L.gauge.moment true (fun p => presMode L.order 0 (potentialOf x.2.2.2.2) p.1 p.2)
    (L.pressureGradMode 0 x 0) (L.pressureGradMode 0 x 2) 0

def gaugeUnit : ℂ := L.gauge.moment true (fun _ => 1) (fun _ => 0) (fun _ => 0) 0

def pressureOf {k : ℕ} (x : FieldTuple k) : Space → ℝ :=
  fun y => potentialOf x.2.2.2.2 y - (L.gaugeValue x / L.gaugeUnit).re

def pressMode {k : ℕ} (n : ℤ) (x : FieldTuple k) : ℝ × ℝ → ℂ :=
  fun p => presMode L.order n (L.pressureOf x) p.1 p.2

def sideTest (e : Fin 4) (d : ℕ) : ℝ → ℝ :=
  if e.val < 2 then L.bases.heightPoly d
  else fun r => (if L.box.r₁ = 0 then r else 1) * L.bases.radialPoly d r

def extraValue {k : ℕ} (n : ℤ) (x : FieldTuple k) (e : Fin 4) (a : Fin 3) (d : ℕ) : ℂ :=
  if e.val = 0 then radialStripMoment L.box.r₁ L.box.r₂ L.box.z₁ L.box.z₂ (L.velMode n x a) (L.gradModeOf n x a 0) (L.sideTest e d)
  else if e.val = 1 then radialStripMoment L.box.r₂ L.box.r₁ L.box.z₁ L.box.z₂ (L.velMode n x a) (L.gradModeOf n x a 0) (L.sideTest e d)
  else if e.val = 2 then heightStripMoment L.box.z₁ L.box.z₂ L.box.r₁ L.box.r₂ (fun _ => 1) (L.velMode n x a) (L.gradModeOf n x a 2) (L.sideTest e d)
  else heightStripMoment L.box.z₂ L.box.z₁ L.box.r₁ L.box.r₂ (fun _ => 1) (L.velMode n x a) (L.gradModeOf n x a 2) (L.sideTest e d)

def trueData {k : ℕ} (x : FieldTuple k) : L.Datum → ℂ :=
  Sum.elim (fun i => L.bases.coef L.box (L.gradModeOf i.1 x i.2.1 i.2.2.1) i.2.2.2.1 i.2.2.2.2)
  (Sum.elim (fun i => L.bases.coef L.box (L.velMode i.1 x i.2.1) i.2.2.1 i.2.2.2)
  (Sum.elim (fun i => (L.segment i.2.1).moment false (L.velMode i.1 x i.2.2.1)
      (L.gradModeOf i.1 x i.2.2.1 0) (L.gradModeOf i.1 x i.2.2.1 2) i.2.2.2)
  (Sum.elim (fun i => if (L.segment i.2.1).radial then
        (L.segment i.2.1).moment true (L.gradModeOf i.1 x i.2.2.1 0)
          (L.secondModeOf i.1 x i.2.2.1 0 0) (L.secondModeOf i.1 x i.2.2.1 0 2) i.2.2.2
      else (L.segment i.2.1).moment true (L.gradModeOf i.1 x i.2.2.1 2)
          (L.secondModeOf i.1 x i.2.2.1 2 0) (L.secondModeOf i.1 x i.2.2.1 2 2) i.2.2.2)
  (Sum.elim (fun i => (L.presSegment i.2.1).moment true (L.pressMode i.1 x)
      (L.pressureGradMode i.1 x 0) (L.pressureGradMode i.1 x 2) i.2.2)
  (Sum.elim (fun i => cornerMoment (L.corner i.2.1).1 (L.cornerOther i.2.1).1 (L.corner i.2.1).2
      (L.cornerOther i.2.1).2 (L.velMode i.1 x i.2.2) (L.gradModeOf i.1 x i.2.2 0)
      (L.gradModeOf i.1 x i.2.2 2) (L.secondModeOf i.1 x i.2.2 0 2))
  (Sum.elim (fun c => heightStripMoment (L.corner c).2 (L.cornerOther c).2 0 (L.corner c).1 (fun r => r)
      (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) (fun _ => 1))
    (fun i => L.extraValue i.1 x i.2.1 i.2.2.1 i.2.2.2)))))))

end CellLayout

namespace CellLayout

variable (L : CellLayout)

abbrev RelIndex :=
  (L.modes × Fin 3 × Fin L.degCoef × Fin L.degCoef) ⊕ (L.modes × Fin 3 × Fin L.degCoef × Fin L.degCoef) ⊕
    (L.modes × Fin 3 × Fin L.degCoef × Fin L.degCoef) ⊕ (L.modes × Fin (L.degCoef + 1) × Fin (L.degCoef + 1)) ⊕
      (Fin (L.degCoef + 1) × Fin (L.degCoef + 1)) ⊕ (L.modes × Fin 3 × Fin L.degCoef × Fin (L.degCoef + 1)) ⊕
        (L.modes × Fin 3 × Fin L.degCoef × Fin (L.degCoef + 1)) ⊕ (Fin 2 × Fin (L.degCoef + 1) × Fin (L.degCoef + 1)) ⊕
          Fin L.segCount ⊕ (L.modes × Fin 4 × Fin 3 × Fin (L.degCoef + 1))

def segmentTestPair (s : Fin L.segCount) (t : ℝ → ℝ) (d : ℕ) : ℝ :=
  ∫ u in Set.Icc (L.segment s).lo (L.segment s).hi, t u * (L.segment s).test d u

def radialInt (f : ℝ → ℝ) : ℝ := ∫ r in Set.Icc L.box.r₁ L.box.r₂, f r

def heightInt (f : ℝ → ℝ) : ℝ := ∫ z in Set.Icc L.box.z₁ L.box.z₂, f z

def radialStiff (j i : ℕ) : ℝ :=
  L.radialInt (fun r => L.box.lineWeight r * (1 - L.box.refR r ^ 2) * deriv (L.bases.radialPoly j) r * L.bases.radialPoly i r)

def heightStiff (l i : ℕ) : ℝ :=
  L.heightInt (fun z => (1 - L.box.refZ z ^ 2) * deriv (L.bases.heightPoly l) z * L.bases.heightPoly i z)

def radialShift (i j : ℕ) : ℝ :=
  L.radialInt (fun r => L.box.lineWeight r * r * L.bases.radialPoly i r * L.bases.radialPoly j r)

def unitAt (d : L.Datum) : L.Datum → ℂ := Pi.single d 1

def strainAt (n : L.modes) (a b : Fin 3) (j l : ℕ) : L.Datum → ℂ :=
  if h : j < L.degCoef + 1 ∧ l < L.degCoef + 1 then
    L.unitAt (CellDatum.lowStrain n a b ⟨j, h.1⟩ ⟨l, h.2⟩) else 0

def velocityAt (n : L.modes) (a : Fin 3) (j l : ℕ) : L.Datum → ℂ :=
  if h : j < L.degCoef ∧ l < L.degCoef then L.unitAt (CellDatum.lowVelocity n a ⟨j, h.1⟩ ⟨l, h.2⟩) else 0

def turnRow (n : L.modes) (a : Fin 3) (j l : ℕ) : L.Datum → ℂ :=
  let k : ℂ := (azimuth L.order n : ℂ)
  if a = 0 then (k * Complex.I) • L.velocityAt n 0 j l - L.velocityAt n 1 j l
  else if a = 1 then (k * Complex.I) • L.velocityAt n 1 j l + L.velocityAt n 0 j l
  else (k * Complex.I) • L.velocityAt n 2 j l

def extraAt (n : L.modes) (e : Fin 4) (a : Fin 3) (d : ℕ) : L.Datum → ℂ :=
  if h : d < L.degCoef + 1 then L.unitAt (CellDatum.extraVelocity n e a ⟨d, h⟩) else 0

def streamAt (c : Option (Fin L.cornerCount)) : L.Datum → ℂ :=
  match c with
  | none => 0
  | some c => L.unitAt (CellDatum.cornerStream c)

open Classical in
def zeroMode : Option L.modes := if h : (0 : ℤ) ∈ L.modes then some ⟨0, h⟩ else none

def radialBeta (i : ℕ) (r : ℝ) : ℝ := if L.box.r₁ = 0 then r ^ (i + 2) else r ^ i

def relationRow : L.RelIndex → L.Datum → ℂ :=
  Sum.elim (fun ρ => if ρ.2.2.1.val = 0 then 0 else
      L.velocityAt ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2 -
        ∑ i ∈ Finset.range (L.degCoef + 1),
          (((L.radialStiff ρ.2.2.1 i / radialEigen L.box ρ.2.2.1 : ℝ)) : ℂ) • L.strainAt ρ.1 ρ.2.1 0 i ρ.2.2.2)
  (Sum.elim (fun ρ => if ρ.2.2.2.val = 0 then 0 else
      L.velocityAt ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2 -
        ∑ i ∈ Finset.range (L.degCoef + 1),
          (((L.heightStiff ρ.2.2.2 i / heightEigen L.box ρ.2.2.2 : ℝ)) : ℂ) • L.strainAt ρ.1 ρ.2.1 2 ρ.2.2.1 i)
  (Sum.elim (fun ρ =>
      ∑ i ∈ Finset.range (L.degCoef + 1), ((L.radialShift i ρ.2.2.1 : ℝ) : ℂ) • L.strainAt ρ.1 ρ.2.1 1 i ρ.2.2.2
        - L.turnRow ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2)
  (Sum.elim (fun ρ => ∑ a : Fin 3, L.strainAt ρ.1 a a ρ.2.1 ρ.2.2)
  (Sum.elim (fun ρ => match L.zeroMode with
      | none => 0
      | some n0 => L.strainAt n0 2 1 ρ.1 ρ.2)
  (Sum.elim (fun ρ => if L.box.r₁ = 0 ∧ ρ.2.2.2.val = L.degCoef then 0 else
      ((L.radialBeta ρ.2.2.2 L.box.r₂ : ℝ) : ℂ) • L.extraAt ρ.1 1 ρ.2.1 ρ.2.2.1
        - ((L.radialBeta ρ.2.2.2 L.box.r₁ : ℝ) : ℂ) • L.extraAt ρ.1 0 ρ.2.1 ρ.2.2.1
        - ∑ j ∈ Finset.range L.degCoef,
            ((L.radialInt (fun r => deriv (L.radialBeta ρ.2.2.2) r * L.bases.radialPoly j r) : ℝ) : ℂ) •
              L.velocityAt ρ.1 ρ.2.1 j ρ.2.2.1
        - ∑ j ∈ Finset.range (L.degCoef + 1),
            ((L.radialInt (fun r => L.radialBeta ρ.2.2.2 r * L.bases.radialPoly j r) : ℝ) : ℂ) •
              L.strainAt ρ.1 ρ.2.1 0 j ρ.2.2.1)
  (Sum.elim (fun ρ =>
      ((L.box.z₂ ^ (ρ.2.2.2 : ℕ) : ℝ) : ℂ) • L.extraAt ρ.1 3 ρ.2.1 ρ.2.2.1
        - ((L.box.z₁ ^ (ρ.2.2.2 : ℕ) : ℝ) : ℂ) • L.extraAt ρ.1 2 ρ.2.1 ρ.2.2.1
        - ∑ l ∈ Finset.range L.degCoef,
            ((L.heightInt (fun z => deriv (fun z => z ^ (ρ.2.2.2 : ℕ)) z * L.bases.heightPoly l z) : ℝ) : ℂ) •
              L.velocityAt ρ.1 ρ.2.1 ρ.2.2.1 l
        - ∑ l ∈ Finset.range (L.degCoef + 1),
            ((L.heightInt (fun z => z ^ (ρ.2.2.2 : ℕ) * L.bases.heightPoly l z) : ℝ) : ℂ) •
              L.strainAt ρ.1 ρ.2.1 2 ρ.2.2.1 l)
  (Sum.elim (fun ρ => match L.zeroMode with
      | none => 0
      | some n0 => if L.box.r₁ ≠ 0 then 0 else
          ((L.box.r₂ * L.box.r₂ ^ (ρ.2.2 : ℕ) : ℝ) : ℂ) • L.extraAt n0 1 (if ρ.1 = 0 then 0 else 1) ρ.2.1
            - ∑ j ∈ Finset.range (L.degCoef + 1),
                ((L.radialInt (fun r => r * deriv (fun r => r * r ^ (ρ.2.2 : ℕ)) r * L.bases.radialPoly j r) : ℝ) : ℂ) •
                  (if ρ.1 = 0 then L.strainAt n0 1 1 j ρ.2.1 else -L.strainAt n0 0 1 j ρ.2.1)
            - ∑ j ∈ Finset.range (L.degCoef + 1),
                ((L.radialInt (fun r => r * r ^ (ρ.2.2 : ℕ) * L.bases.radialPoly j r) : ℝ) : ℂ) •
                  L.strainAt n0 (if ρ.1 = 0 then 0 else 1) 0 j ρ.2.1)
  (Sum.elim (fun s => match L.zeroMode with
      | none => 0
      | some n0 =>
        if (L.segment s).radial then
          (((L.segment s).level / (L.segment s).testCoef 0 0 : ℝ) : ℂ) •
              (if h : 0 < L.degSide + 2 then L.unitAt (CellDatum.sideVelocity n0 s 0 ⟨0, h⟩) else 0)
            + L.streamAt (L.segEnd s 1) - L.streamAt (L.segEnd s 0)
        else
          ((1 / (L.segment s).testCoef 1 1 : ℝ) : ℂ) •
              (L.unitAt (CellDatum.sideVelocity n0 s 2 ⟨1, by omega⟩)
                - (((L.segment s).testCoef 1 0 / (L.segment s).testCoef 0 0 : ℝ) : ℂ) •
                    L.unitAt (CellDatum.sideVelocity n0 s 2 ⟨0, by omega⟩))
            - L.streamAt (L.segEnd s 1) + L.streamAt (L.segEnd s 0))
  (fun ρ => if ¬ (ρ.2.1.val = 0 ∧ L.box.r₁ = 0) ∧ (if ρ.2.1.val < 2 then ρ.2.2.2.val ≤ L.degSide
        else if L.box.r₁ = 0 then ρ.2.2.2.val ≤ L.degSide else ρ.2.2.2.val ≤ L.degSide + 1) then
      L.extraAt ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2 -
        ∑ s ∈ L.sideSegments ρ.2.1, ∑ d' : Fin (L.degSide + 2),
          ((L.segmentTestPair s (L.sideTest ρ.2.1 ρ.2.2.2) d' : ℝ) : ℂ) •
            L.unitAt (CellDatum.sideVelocity ρ.1 s ρ.2.2.1 d')
    else 0)))))))))

end CellLayout

namespace CellLayout

variable (L : CellLayout)

def IsSkeletonDatum (d : L.Datum) : Prop :=
  Sum.elim (fun _ => False) (Sum.elim (fun _ => False) (Sum.elim (fun _ => True) (Sum.elim (fun _ => True)
    (Sum.elim (fun _ => True) (Sum.elim (fun _ => True) (Sum.elim (fun _ => True) (fun _ => False))))))) d

open Classical in
def lowEntry (i : ℤ × Fin 3 × Fin 4 × ℕ × ℕ) : Option L.Datum :=
  if hn : i.1 ∈ L.modes then
    if hb : i.2.2.1.val < 3 then
      (if h : i.2.2.2.1 < L.degCoef + 1 ∧ i.2.2.2.2 < L.degCoef + 1 then
        some (CellDatum.lowStrain ⟨i.1, hn⟩ i.2.1 ⟨i.2.2.1.val, hb⟩ ⟨i.2.2.2.1, h.1⟩ ⟨i.2.2.2.2, h.2⟩) else none)
    else
      (if h : i.2.2.2.1 < L.degCoef ∧ i.2.2.2.2 < L.degCoef then
        some (CellDatum.lowVelocity ⟨i.1, hn⟩ i.2.1 ⟨i.2.2.2.1, h.1⟩ ⟨i.2.2.2.2, h.2⟩) else none)
  else none

def realCoord (w : L.Datum × Fin 2 → ℝ) : L.Datum → ℂ := fun d => (w (d, 0) : ℂ) + (w (d, 1) : ℂ) * Complex.I

def realPart (u : L.Datum → ℂ) : L.Datum × Fin 2 → ℝ := fun p => if p.2 = 0 then (u p.1).re else (u p.1).im

end CellLayout

structure IsCellLayout {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)
    (L : CellLayout) : Prop where
  order_eq : L.order = c.order
  box_eq : L.box = K
  bases_eq : L.bases = B
  modes_eq : L.modes = S.resolved
  degCoef_eq : L.degCoef = S.degHigh
  degSide_eq : L.degSide = S.degLow
  box_valid : IsCellBox K
  bases_valid : IsCellBases K B
  segment_valid : ∀ s, IsFaceSegment (L.segment s)
  presSegment_valid : ∀ s, IsFaceSegment (L.presSegment s)
  gauge_valid : IsFaceSegment L.gauge ∧ L.gauge.testCoef 0 0 ≠ 0 ∧ 0 ≤ L.gauge.lo
  segment_on_side : ∀ s, ((L.segment s).radial ∧ ((L.segment s).level = K.r₁ ∨ (L.segment s).level = K.r₂) ∧
      K.z₁ ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ K.z₂ ∧ (L.segment s).level ≠ 0) ∨
    (¬ (L.segment s).radial ∧ ((L.segment s).level = K.z₁ ∨ (L.segment s).level = K.z₂) ∧
      K.r₁ ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ K.r₂)
  segment_other_in_box : ∀ s, ((L.segment s).radial → (L.segment s).other = K.r₁ + K.r₂ - (L.segment s).level) ∧
    (¬ (L.segment s).radial → (L.segment s).other = K.z₁ + K.z₂ - (L.segment s).level)
  corner_is_corner : ∀ c, ((L.corner c).1 = K.r₁ ∨ (L.corner c).1 = K.r₂) ∧ ((L.corner c).2 = K.z₁ ∨ (L.corner c).2 = K.z₂)
    ∧ (L.corner c).1 ≠ 0
  corner_other : ∀ c, (L.cornerOther c).1 = K.r₁ + K.r₂ - (L.corner c).1 ∧ (L.cornerOther c).2 = K.z₁ + K.z₂ - (L.corner c).2
  segEnd_spec : ∀ s e c, L.segEnd s e = some c →
    L.corner c = (if (L.segment s).radial then ((L.segment s).level, if e = 0 then (L.segment s).lo else (L.segment s).hi)
      else (if e = 0 then (L.segment s).lo else (L.segment s).hi, (L.segment s).level))
  segEnd_axis : ∀ s e, L.segEnd s e = none → ¬ (L.segment s).radial ∧ e = 0 ∧ (L.segment s).lo = 0
  radial_test_const : ∀ s, (L.segment s).radial → (L.segment s).testCoef 0 0 ≠ 0
  height_test_affine : ∀ s, ¬ (L.segment s).radial → (L.segment s).testCoef 0 0 ≠ 0 ∧ (L.segment s).testCoef 1 1 ≠ 0
  degSide_pos : 1 ≤ L.degSide
  degSide_le : L.degSide + 1 ≤ L.degCoef
  cellCorner_spec : ∀ i j c, L.cellCorner i j = some c →
    L.corner c = (if i = 0 then K.r₁ else K.r₂, if j = 0 then K.z₁ else K.z₂)
  cellCorner_axis : ∀ i j, L.cellCorner i j = none → i = 0 ∧ K.r₁ = 0
  sideSegments_spec : ∀ e s, s ∈ L.sideSegments e →
    ((L.segment s).radial ↔ e.val < 2) ∧
      (L.segment s).level = (if e.val = 0 then K.r₁ else if e.val = 1 then K.r₂ else if e.val = 2 then K.z₁ else K.z₂)
  sideSegments_cover : ∀ e, (e.val = 0 → K.r₁ ≠ 0) → ∀ u, (if e.val < 2 then K.z₁ ≤ u ∧ u ≤ K.z₂ else K.r₁ ≤ u ∧ u ≤ K.r₂) →
    ∃ s ∈ L.sideSegments e, (L.segment s).lo ≤ u ∧ u ≤ (L.segment s).hi
  sideSegments_disjoint : ∀ e, ∀ s ∈ L.sideSegments e, ∀ s' ∈ L.sideSegments e, s ≠ s' →
    (L.segment s).hi ≤ (L.segment s').lo ∨ (L.segment s').hi ≤ (L.segment s).lo
  segments_on_sides : ∀ s, ∃ e, s ∈ L.sideSegments e
  segment_orthonormal : ∀ s d d', d ≤ L.degSide + 1 → d' ≤ L.degSide + 1 →
    ∫ u in Set.Icc (L.segment s).lo (L.segment s).hi, (L.segment s).test d u * (L.segment s).test d' u =
      if d = d' then 1 else 0

structure IsCellParam (L : CellLayout) (P : ParamData L.Datum) (sel : Fin P.relCount → L.RelIndex) : Prop where
  param : IsParamData P
  rows : ∀ i, P.relation i = L.relationRow (sel i)
  skeleton_spec : ∀ d ∈ P.skeleton, L.IsSkeletonDatum d

namespace CellLayout

variable (L : CellLayout)

def cornerAt (n : L.modes) (i j : Fin 2) (a : Fin 3) : L.Datum → ℂ :=
  match L.cellCorner i j with
  | none => 0
  | some c => L.unitAt (CellDatum.cornerVelocity n c a)

def sideGradientRow (n : L.modes) (e : Fin 4) (a : Fin 3) (t : ℝ → ℝ) : L.Datum → ℂ :=
  ∑ s ∈ L.sideSegments e, ∑ d : Fin (L.degSide + 1),
    ((L.segmentTestPair s t d : ℝ) : ℂ) • L.unitAt (CellDatum.sideGradient n s a d)

def sideRadius (e : Fin 4) : ℝ := if e.val = 0 then L.box.r₁ else L.box.r₂

def sideHeightIndex (e : Fin 4) : Fin 2 := if e.val = 2 then 0 else 1

def sideRadialIndex (e : Fin 4) : Fin 2 := if e.val = 0 then 0 else 1

def sideVelocityRow (n : L.modes) (e : Fin 4) (a : Fin 3) (f : ℝ → ℝ) : L.Datum → ℂ :=
  ∑ s ∈ L.sideSegments e, ∑ d : Fin (L.degSide + 2),
    ((L.segmentTestPair s f d : ℝ) : ℂ) • L.unitAt (CellDatum.sideVelocity n s a d)

def turnSideRow (n : L.modes) (e : Fin 4) (a : Fin 3) (f : ℝ → ℝ) : L.Datum → ℂ :=
  let k : ℂ := (azimuth L.order n : ℂ)
  if a = 0 then (k * Complex.I) • L.sideVelocityRow n e 0 f - L.sideVelocityRow n e 1 f
  else if a = 1 then (k * Complex.I) • L.sideVelocityRow n e 1 f + L.sideVelocityRow n e 0 f
  else (k * Complex.I) • L.sideVelocityRow n e 2 f

def faceBaseRow (n : L.modes) (e : Fin 4) (a b : Fin 3) (l : ℕ) : L.Datum → ℂ :=
  if e.val < 2 then
    (if b = 2 then
      ((L.bases.heightPoly l L.box.z₂ : ℝ) : ℂ) • L.cornerAt n (sideRadialIndex e) 1 a
        - ((L.bases.heightPoly l L.box.z₁ : ℝ) : ℂ) • L.cornerAt n (sideRadialIndex e) 0 a
        - L.sideVelocityRow n e a (deriv (L.bases.heightPoly l))
    else if b = 1 then
      ((1 / L.sideRadius e : ℝ) : ℂ) • L.turnSideRow n e a (L.bases.heightPoly l)
    else L.sideGradientRow n e a (L.bases.heightPoly l))
  else
    (if b = 0 then
      ((L.box.r₂ * L.bases.radialPoly l L.box.r₂ : ℝ) : ℂ) • L.cornerAt n 1 (sideHeightIndex e) a
        - ((L.box.r₁ * L.bases.radialPoly l L.box.r₁ : ℝ) : ℂ) • L.cornerAt n 0 (sideHeightIndex e) a
        - L.sideVelocityRow n e a (deriv (fun r => r * L.bases.radialPoly l r))
    else if b = 1 then
      L.turnSideRow n e a (L.bases.radialPoly l)
    else L.sideGradientRow n e a (L.bases.radialPoly l))

def strainFaceRow (n : L.modes) (e : Fin 4) (a b : Fin 3) (l : ℕ) : L.Datum → ℂ :=
  if e.val < 2 ∧ a = 0 ∧ b = 0 then -(L.faceBaseRow n e 1 1 l + L.faceBaseRow n e 2 2 l)
  else if 2 ≤ e.val ∧ a = 2 ∧ b = 2 then -(L.faceBaseRow n e 0 0 l + L.faceBaseRow n e 1 1 l)
  else L.faceBaseRow n e a b l

end CellLayout

namespace CellLayout

variable (L : CellLayout)

def negMode (n : L.modes) : L.modes := if h : -n.1 ∈ L.modes then ⟨-n.1, h⟩ else n

def conjDatum : L.Datum → L.Datum :=
  Sum.map (fun i => (L.negMode i.1, i.2)) (Sum.map (fun i => (L.negMode i.1, i.2))
    (Sum.map (fun i => (L.negMode i.1, i.2)) (Sum.map (fun i => (L.negMode i.1, i.2))
      (Sum.map (fun i => (L.negMode i.1, i.2)) (Sum.map (fun i => (L.negMode i.1, i.2))
        (Sum.map id (fun i => (L.negMode i.1, i.2))))))))

def modeOf : L.Datum → ℤ :=
  Sum.elim (fun i => i.1.1) (Sum.elim (fun i => i.1.1) (Sum.elim (fun i => i.1.1) (Sum.elim (fun i => i.1.1)
    (Sum.elim (fun i => i.1.1) (Sum.elim (fun i => i.1.1) (Sum.elim (fun _ => 0) (fun i => i.1.1)))))))

def IsPlaneDeleted (d : L.Datum) : Prop :=
  Sum.elim (fun _ => False) (Sum.elim (fun _ => False)
    (Sum.elim (fun i => ¬ (L.segment i.2.1).radial ∧ (L.segment i.2.1).level = 0 ∧ i.2.2.1 = 2)
    (Sum.elim (fun i => ¬ (L.segment i.2.1).radial ∧ (L.segment i.2.1).level = 0 ∧ i.2.2.1 ≠ 2)
    (Sum.elim (fun _ => False)
    (Sum.elim (fun i => (L.corner i.2.1).2 = 0 ∧ i.2.2 = 2)
    (Sum.elim (fun c => (L.corner c).2 = 0) (fun _ => False))))))) d

def IsGaugeDeleted (d : L.Datum) : Prop :=
  Sum.elim (fun _ => False) (Sum.elim (fun _ => False) (Sum.elim (fun _ => False) (Sum.elim (fun _ => False)
    (Sum.elim (fun i => (i.1 : ℤ) = 0 ∧ (i.2.1, i.2.2) ∈ L.gaugeDeleted) (fun _ => False))))) d

def IsSystemCoord (p : L.Datum × Fin 2) : Prop :=
  (0 < L.modeOf p.1 ∨ (L.modeOf p.1 = 0 ∧ p.2 = 0)) ∧ ¬ L.IsPlaneDeleted p.1 ∧ ¬ L.IsGaugeDeleted p.1

def partSign (i : Fin 2) : ℝ := if i = 0 then 1 else -1

open Classical in
def expandSystem (ρ : L.Datum × Fin 2 → ℝ) : L.Datum × Fin 2 → ℝ := fun p =>
  if L.IsSystemCoord p then ρ p
  else if L.modeOf p.1 < 0 ∧ L.IsSystemCoord (L.conjDatum p.1, p.2) then partSign p.2 * ρ (L.conjDatum p.1, p.2)
  else 0

end CellLayout

structure IsPressureLayout {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)
    (L : CellLayout) : Prop where
  layout : IsCellLayout c K S B L
  modes_symm : ∀ n ∈ L.modes, -n ∈ L.modes
  presSegment_on_side : ∀ s, ((L.presSegment s).radial ∧ ((L.presSegment s).level = K.r₁ ∨ (L.presSegment s).level = K.r₂) ∧
      K.z₁ ≤ (L.presSegment s).lo ∧ (L.presSegment s).hi ≤ K.z₂ ∧ (L.presSegment s).level ≠ 0) ∨
    (¬ (L.presSegment s).radial ∧ ((L.presSegment s).level = K.z₁ ∨ (L.presSegment s).level = K.z₂) ∧
      K.r₁ ≤ (L.presSegment s).lo ∧ (L.presSegment s).hi ≤ K.r₂)
  presSegment_other_in_box : ∀ s, ((L.presSegment s).radial → (L.presSegment s).other = K.r₁ + K.r₂ - (L.presSegment s).level) ∧
    (¬ (L.presSegment s).radial → (L.presSegment s).other = K.z₁ + K.z₂ - (L.presSegment s).level)
  presSides_cover : ∀ (e : Fin 4), (e.val = 0 → K.r₁ ≠ 0) → ∀ u,
    (if e.val < 2 then K.z₁ ≤ u ∧ u ≤ K.z₂ else K.r₁ ≤ u ∧ u ≤ K.r₂) →
    ∃ s, ((L.presSegment s).radial ↔ e.val < 2) ∧
      (L.presSegment s).level = (if e.val = 0 then K.r₁ else if e.val = 1 then K.r₂ else if e.val = 2 then K.z₁ else K.z₂) ∧
      (L.presSegment s).lo ≤ u ∧ u ≤ (L.presSegment s).hi
  presSides_disjoint : ∀ s s', s ≠ s' → (L.presSegment s).radial = (L.presSegment s').radial →
    (L.presSegment s).level = (L.presSegment s').level →
    (L.presSegment s).hi ≤ (L.presSegment s').lo ∨ (L.presSegment s').hi ≤ (L.presSegment s).lo
  presSegment_orthonormal : ∀ s d d', d < L.degSide → d' < L.degSide →
    ∫ u in Set.Icc (L.presSegment s).lo (L.presSegment s).hi,
      (L.presSegment s).test d u * (L.presSegment s).test d' u = if d = d' then 1 else 0

structure GaugeShift (k : ℕ) where
  left : FieldTuple k → ℝ
  right : FieldTuple k → ℝ
  point : FieldTuple k → ℝ → ℝ

def radialWeightIntegral (t : ℝ → ℝ) (r : ℝ) : ℝ := ∫ ρ in (0 : ℝ)..r, ρ * t ρ

namespace CellLayout

variable (L : CellLayout)

def pressureShift {k : ℕ} (g : GaugeShift k) (x : FieldTuple k) : L.Datum → ℂ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0)
    (Sum.elim (fun i => if (i.1 : ℤ) = 0 then
        (if (L.presSegment i.2.1).radial then
          (((if (L.presSegment i.2.1).level = L.box.r₁ then g.left x else g.right x) *
              ∫ z in (L.presSegment i.2.1).lo..(L.presSegment i.2.1).hi, (L.presSegment i.2.1).test i.2.2 z : ℝ) : ℂ)
        else ((g.point x (L.presSegment i.2.1).hi *
                radialWeightIntegral ((L.presSegment i.2.1).test i.2.2) (L.presSegment i.2.1).hi
              - g.point x (L.presSegment i.2.1).lo *
                radialWeightIntegral ((L.presSegment i.2.1).test i.2.2) (L.presSegment i.2.1).lo : ℝ) : ℂ))
      else 0)
    (fun _ => 0)))))

def shiftedData {k : ℕ} (g : GaugeShift k) (x : FieldTuple k) : L.Datum → ℂ :=
  fun d => L.trueData x d + L.pressureShift g x d

end CellLayout

structure GaugeSpec (L : CellLayout) where
  edge : Option (Fin L.presCount × Fin L.degSide)
  roots : Finset (Fin L.presCount × Fin L.degSide)

namespace CellLayout

variable (L : CellLayout)

def shiftCoefLeft (i : Fin L.presCount × Fin L.degSide) : ℝ :=
  if (L.presSegment i.1).radial then
    (if (L.presSegment i.1).level = L.box.r₁ then
      ∫ z in (L.presSegment i.1).lo..(L.presSegment i.1).hi, (L.presSegment i.1).test i.2 z else 0)
  else
    (if (L.presSegment i.1).hi = L.box.r₂ then 0 else
        radialWeightIntegral ((L.presSegment i.1).test i.2) (L.presSegment i.1).hi)
      - (if (L.presSegment i.1).lo = L.box.r₂ then 0 else
        radialWeightIntegral ((L.presSegment i.1).test i.2) (L.presSegment i.1).lo)

def shiftCoefRight (i : Fin L.presCount × Fin L.degSide) : ℝ :=
  if (L.presSegment i.1).radial then
    (if (L.presSegment i.1).level = L.box.r₁ then 0 else
      ∫ z in (L.presSegment i.1).lo..(L.presSegment i.1).hi, (L.presSegment i.1).test i.2 z)
  else
    (if (L.presSegment i.1).hi = L.box.r₂ then
        radialWeightIntegral ((L.presSegment i.1).test i.2) (L.presSegment i.1).hi else 0)
      - (if (L.presSegment i.1).lo = L.box.r₂ then
        radialWeightIntegral ((L.presSegment i.1).test i.2) (L.presSegment i.1).lo else 0)

def pressureDatumValue {k : ℕ} (x : FieldTuple k) (i : Fin L.presCount × Fin L.degSide) : ℝ :=
  match L.zeroMode with
  | none => 0
  | some n0 => (L.trueData x (CellDatum.sidePressure n0 i.1 i.2)).re

def gaugeJump {k : ℕ} (sp : GaugeSpec L) (x : FieldTuple k) : ℝ :=
  match sp.edge with
  | none => 0
  | some e => -(L.pressureDatumValue x e) / L.shiftCoefRight e

def gaugeShiftOf {k : ℕ} (left right : FieldTuple k → ℝ) : GaugeShift k where
  left := left
  right := right
  point := fun x r => if r = L.box.r₂ then right x else left x

end CellLayout

structure IsGaugeSpec (L : CellLayout) (sp : GaugeSpec L) : Prop where
  deleted_eq : ∀ i, i ∈ L.gaugeDeleted ↔ (sp.edge = some i ∨ i ∈ sp.roots)
  edge_not_root : ∀ e, sp.edge = some e → e ∉ sp.roots
  zero_mode : (0 : ℤ) ∈ L.modes
  box_ne : L.box.r₁ ≠ L.box.r₂
  edge_right_ne : ∀ e, sp.edge = some e → L.shiftCoefRight e ≠ 0
  edge_balanced : ∀ e, sp.edge = some e → L.shiftCoefLeft e + L.shiftCoefRight e = 0
  whole_sides : ∀ s, ((L.presSegment s).radial → (L.presSegment s).lo = L.box.z₁ ∧ (L.presSegment s).hi = L.box.z₂) ∧
    (¬ (L.presSegment s).radial → (L.presSegment s).lo = L.box.r₁ ∧ (L.presSegment s).hi = L.box.r₂)

end CellFormula

end CellCert

end Breakdown

end
end

section

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellEnergy

open CellAnalysis CellFormula

section Rows

variable {D : Type} [Fintype D] [DecidableEq D]

def formOfRows {ι : Type} [Fintype ι] (rows : ι → D → ℂ) (G : Matrix ι ι ℂ) : Matrix D D ℂ :=
  fun d d' => ∑ i, ∑ i', (starRingEnd ℂ) (rows i d) * G i i' * rows i' d'

def testSupForm {ι : Type} [Fintype ι] [DecidableEq ι] (rows : ι → D → ℂ) (G : Matrix ι ι ℂ) : Matrix D D ℂ :=
  formOfRows rows G⁻¹

end Rows

structure LowIndex (D : Type) (modes : Finset ℤ) (Q q : ℕ) where
  strainSlot : modes → Fin 3 → Fin 3 → Fin (Q + 1) → Fin (Q + 1) → D
  velocitySlot : modes → Fin 3 → Fin Q → Fin Q → D
  radialFaceRow : modes → Fin 2 → Fin 3 → Fin 3 → Fin (q + 1) → D → ℂ
  heightFaceRow : modes → Fin 2 → Fin 3 → Fin 3 → Fin (q + 1) → D → ℂ

def basisFn (B : CellBases) (j l : ℕ) (p : ℝ × ℝ) : ℝ := B.radialPoly j p.1 * B.heightPoly l p.2

def monomial (j l : ℕ) (p : ℝ × ℝ) : ℝ := p.1 ^ j * p.2 ^ l

def radialSlope (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := deriv (fun r : ℝ => f (r, p.2)) p.1

def heightSlope (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := deriv (fun z : ℝ => f (p.1, z)) p.2

def rectIntegral (K : CellBox) (f : ℝ × ℝ → ℝ) : ℝ := ∫ p in K.rect, f p

def testInnerMatrix (K : CellBox) {ι : Type} (m : ℝ × ℝ → ℝ) (P : ι → ℝ × ℝ → ℝ) : Matrix ι ι ℂ :=
  fun i i' => ((rectIntegral K (fun p => m p * P i p * P i' p) : ℝ) : ℂ)

def frameTurn (c b : Fin 3) : ℝ :=
  if c = 1 ∧ b = 0 then 1 else if c = 0 ∧ b = 1 then -1 else 0

def angularComb (k : ℝ) (a b : Fin 3) : Fin 3 → Fin 3 → ℂ := fun a' b' =>
  (if a' = a ∧ b' = b then Complex.I * (k : ℂ) else 0)
    - (if a' = a then (frameTurn b' b : ℂ) else 0) - (if b' = b then (frameTurn a' a : ℂ) else 0)

def angularArray (k : ℝ) (C : Fin 3 → Fin 3 → ℂ) : Fin 3 → Fin 3 → ℂ :=
  fun a' b' => ∑ a : Fin 3, ∑ b : Fin 3, C a b * angularComb k a b a' b'

def unitArray (a b : Fin 3) : Fin 3 → Fin 3 → ℂ := fun a' b' => if a' = a ∧ b' = b then 1 else 0

def curlArray (i : Fin 3) : Fin 3 → Fin 3 → ℂ := fun a b => (CellCert.permSign i b a : ℂ)

section Cell

variable {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}
  (K : CellBox) (B : CellBases) (I : LowIndex D modes Q q)

def lowRow (n : modes) (C : Fin 3 → Fin 3 → ℂ) (j l : Fin (Q + 1)) : D → ℂ :=
  fun d => ∑ a : Fin 3, ∑ b : Fin 3, C a b * (if d = I.strainSlot n a b j l then 1 else 0)

def radialFaceComp (n : modes) (C : Fin 3 → Fin 3 → ℂ) (e : Fin 2) (l : Fin (q + 1)) : D → ℂ :=
  fun d => ∑ a : Fin 3, ∑ b : Fin 3, C a b * I.radialFaceRow n e a b l d

def heightFaceComp (n : modes) (C : Fin 3 → Fin 3 → ℂ) (e : Fin 2) (j : Fin (q + 1)) : D → ℂ :=
  fun d => ∑ a : Fin 3, ∑ b : Fin 3, C a b * I.heightFaceRow n e a b j d

def lowPairRow (n : modes) (C : Fin 3 → Fin 3 → ℂ) (φ : ℝ × ℝ → ℝ) : D → ℂ :=
  fun d => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
    ((rectIntegral K (fun p => basisFn B j l p * φ p) : ℝ) : ℂ) * lowRow I n C j l d

def heightMoment (l l' : ℕ) : ℝ := ∫ z in Set.Icc K.z₁ K.z₂, z ^ l * B.heightPoly l' z

def radialMoment (j j' : ℕ) : ℝ := ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * r ^ j * B.radialPoly j' r

def radialProjForm (n : modes) (C : Fin 3 → Fin 3 → ℂ) : Matrix D D ℂ :=
  formOfRows (fun jl : Fin (Q + 1) × Fin (Q + 1) => lowRow I n C jl.1 jl.2)
    (fun jl jl' => ((K.innerRadius * rectIntegral K (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2)
      * radialSlope (basisFn B jl.1 jl.2) p * radialSlope (basisFn B jl'.1 jl'.2) p) : ℝ) : ℂ))

def heightProjForm (n : modes) (C : Fin 3 → Fin 3 → ℂ) : Matrix D D ℂ :=
  formOfRows (fun jl : Fin (Q + 1) × Fin (Q + 1) => lowRow I n C jl.1 jl.2)
    (fun jl jl' => ((K.innerRadius * rectIntegral K (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2)
      * heightSlope (basisFn B jl.1 jl.2) p * heightSlope (basisFn B jl'.1 jl'.2) p) : ℝ) : ℂ))

def radialInnerWeight (p : ℝ × ℝ) : ℝ := (p.1 - K.r₁) * (1 - K.refR p.1 ^ 2)

def heightInnerWeight (p : ℝ × ℝ) : ℝ := (p.1 - K.r₁) * (1 - K.refZ p.2 ^ 2)

def radialInnerForm (n : modes) (C : Fin 3 → Fin 3 → ℂ) : Matrix D D ℂ :=
  testSupForm (fun jl : Fin (Q - 1) × Fin (Q + 1) =>
      lowPairRow K B I n C (fun p => -radialSlope (fun p' => radialInnerWeight K p' * monomial jl.1 jl.2 p') p))
    (testInnerMatrix K (radialInnerWeight K) (fun jl : Fin (Q - 1) × Fin (Q + 1) => monomial jl.1 jl.2))

def heightInnerForm (n : modes) (C : Fin 3 → Fin 3 → ℂ) : Matrix D D ℂ :=
  testSupForm (fun jl : Fin Q × Fin Q =>
      lowPairRow K B I n C (fun p => -heightSlope (fun p' => heightInnerWeight K p' * monomial jl.1 jl.2 p') p))
    (testInnerMatrix K (heightInnerWeight K) (fun jl : Fin Q × Fin Q => monomial jl.1 jl.2))

def radialOuterTest (j l : ℕ) (p : ℝ × ℝ) : ℝ := K.lineWeight p.1 * monomial j l p

def radialOuterRow (n : modes) (C : Fin 3 → Fin 3 → ℂ) (j : Fin Q) (l : Fin (q + 1)) : D → ℂ :=
  fun d => (∑ l' : Fin (q + 1), ((heightMoment K B l l' : ℝ) : ℂ) *
      (((K.r₂ * K.lineWeight K.r₂ * K.r₂ ^ (j : ℕ) : ℝ) : ℂ) * radialFaceComp I n C 1 l' d
        + ((K.r₁ * K.lineWeight K.r₁ * K.r₁ ^ (j : ℕ) : ℝ) : ℂ) * radialFaceComp I n C 0 l' d))
    + lowPairRow K B I n C (fun p => -radialSlope (fun p' => p'.1 * K.refR p'.1 * radialOuterTest K j l p') p) d

def radialOuterForm (n : modes) (C : Fin 3 → Fin 3 → ℂ) : Matrix D D ℂ :=
  testSupForm (fun jl : Fin Q × Fin (q + 1) => radialOuterRow K B I n C jl.1 jl.2)
    (testInnerMatrix K (fun p => p.1) (fun jl : Fin Q × Fin (q + 1) => radialOuterTest K jl.1 jl.2))

def heightOuterRow (n : modes) (C : Fin 3 → Fin 3 → ℂ) (j : Fin (q + 1)) (l : Fin (Q + 1)) : D → ℂ :=
  fun d => (∑ j' : Fin (q + 1), ((radialMoment K B j j' : ℝ) : ℂ) *
      (((K.z₂ ^ (l : ℕ) : ℝ) : ℂ) * heightFaceComp I n C 1 j' d
        + ((K.z₁ ^ (l : ℕ) : ℝ) : ℂ) * heightFaceComp I n C 0 j' d))
    + lowPairRow K B I n C (fun p => -heightSlope (fun p' => p'.1 * K.refZ p'.2 * monomial j l p') p) d

def heightOuterForm (n : modes) (C : Fin 3 → Fin 3 → ℂ) : Matrix D D ℂ :=
  testSupForm (fun jl : Fin (q + 1) × Fin (Q + 1) => heightOuterRow K B I n C jl.1 jl.2)
    (testInnerMatrix K (fun p => p.1) (fun jl : Fin (q + 1) × Fin (Q + 1) => monomial jl.1 jl.2))

def angularTest (j l : ℕ) (p : ℝ × ℝ) : ℝ := p.1 * monomial j l p

def angularAxisForm (n : modes) (C : Fin 3 → Fin 3 → ℂ) : Matrix D D ℂ :=
  testSupForm (fun jl : Fin (Q + 1) × Fin (Q + 1) => lowPairRow K B I n C (fun p => angularTest jl.1 jl.2 p))
    (testInnerMatrix K (fun p => p.1) (fun jl : Fin (Q + 1) × Fin (Q + 1) => angularTest jl.1 jl.2))

def angularOffWeight (p : ℝ × ℝ) : ℝ := (K.r₂ - p.1) / (p.1 * K.r₂)

def angularOffForm (n : modes) (C : Fin 3 → Fin 3 → ℂ) : Matrix D D ℂ :=
  formOfRows (fun jl : Fin (Q + 1) × Fin (Q + 1) => lowRow I n C jl.1 jl.2)
      (fun jl jl' => if jl = jl' then ((K.r₂⁻¹ : ℝ) : ℂ) else 0)
    + testSupForm (fun jl : Fin Q × Fin (Q + 1) =>
        lowPairRow K B I n C (fun p => angularOffWeight K p * angularTest jl.1 jl.2 p))
      (testInnerMatrix K (angularOffWeight K) (fun jl : Fin Q × Fin (Q + 1) => angularTest jl.1 jl.2))

open Classical in
def componentForm (m : ℕ) (n : modes) (C : Fin 3 → Fin 3 → ℂ) : Matrix D D ℂ :=
  radialProjForm K B I n C + (if K.r₁ = 0 then 0 else radialInnerForm K B I n C) + radialOuterForm K B I n C
    + heightProjForm K B I n C + (if K.r₁ = 0 then 0 else heightInnerForm K B I n C) + heightOuterForm K B I n C
    + (if K.r₁ = 0 then angularAxisForm K B I n (angularArray (azimuth m n) C)
        else angularOffForm K B I n (angularArray (azimuth m n) C))

def topForm (n : modes) : Matrix D D ℂ :=
  ∑ a : Fin 3,
    (formOfRows (fun jl : Fin (Q + 1) × Fin (Q + 1) => lowRow I n (unitArray a 0) jl.1 jl.2)
        (fun jl jl' => if jl = jl' ∧ Q - 1 ≤ (jl.1 : ℕ) then 1 else 0)
      + formOfRows (fun jl : Fin (Q + 1) × Fin (Q + 1) => lowRow I n (unitArray a 2) jl.1 jl.2)
        (fun jl jl' => if jl = jl' ∧ (jl.1 : ℕ) ≤ Q - 1 ∧ Q - 1 ≤ (jl.2 : ℕ) then 1 else 0))

def energyForm (m : ℕ) (energyWeight vorticityWeight tailShift : ℤ → ℝ) : Matrix D D ℂ :=
  ∑ n : modes,
    (((energyWeight n : ℝ) : ℂ) • ∑ a : Fin 3, ∑ b : Fin 3, componentForm K B I m n (unitArray a b)
      + ((vorticityWeight n : ℝ) : ℂ) • ∑ i : Fin 3, componentForm K B I m n (curlArray i)
      - ((tailShift n : ℝ) : ℂ) • topForm I n)

end Cell

inductive LowSlot (Q : ℕ) where
  | strain (a b : Fin 3) (j l : Fin (Q + 1))
  | velocity (a : Fin 3) (j l : Fin Q)
  deriving DecidableEq, Fintype

def slotValue (B : CellBases) {Q : ℕ} : LowSlot Q → ℝ × ℝ → (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)
  | .strain a b j l, p => (fun a' b' => if a' = a ∧ b' = b then ((basisFn B j l p : ℝ) : ℂ) else 0, fun _ => 0)
  | .velocity a j l, p => (fun _ _ => 0, fun a' => if a' = a then ((basisFn B j l p : ℝ) : ℂ) else 0)

section Low

variable {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q)

def slotIndex : modes → LowSlot Q → D
  | n, .strain a b j l => I.strainSlot n a b j l
  | n, .velocity a j l => I.velocitySlot n a j l

def slotRow (σ : modes × LowSlot Q) : D → ℂ := fun d => if d = slotIndex I σ.1 σ.2 then 1 else 0

end Low

def sumSesq (s s' : Fin 3 → Fin 3 → ℂ) : ℂ := ∑ a : Fin 3, ∑ b : Fin 3, (starRingEnd ℂ) (s a b) * s' a b

def vecSesq (v v' : Fin 3 → ℂ) : ℂ := ∑ a : Fin 3, (starRingEnd ℂ) (v a) * v' a

def curlSesq (s s' : Fin 3 → Fin 3 → ℂ) : ℂ := ∑ i : Fin 3, (starRingEnd ℂ) (curlComp s i) * curlComp s' i

def matrixSesq (A : Matrix (Fin 12) (Fin 12) ℂ) (U U' : Fin 12 → ℂ) : ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ) (U i) * A i j * U' j

section Forms

open SteadyCert Assembly

variable {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ} (c : FracCellData k N) (K : CellBox) (B : CellBases)
  (S : CellScalars) (Cl : CellClasses) {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q)

def pairSesq (n n' : ℤ) (p : ℝ × ℝ) (U U' : (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) : ℂ :=
  waveForm (CellScalars.strainMode c (n - n') p) (CellScalars.curlGradMode c (n - n') p)
      (CellScalars.curlGradMode c (n' - n) p) U.1 U.2 U'.1 U'.2
    + (if n = n' then matrixSesq (S.localMatrix n p) (pairVec U.1 U.2) (pairVec U'.1 U'.2) else 0)

def pairForm : Matrix D D ℂ :=
  formOfRows (slotRow I)
    (fun σ σ' => ∫ p in K.rect, ((K.lineWeight p.1 * CellScalars.rHat K p : ℝ) : ℂ) *
      pairSesq c S σ.1 σ'.1 p (slotValue B σ.2 p) (slotValue B σ'.2 p))

open Classical in
def classForm : Matrix D D ℂ :=
  formOfRows (slotRow I)
    (fun σ σ' => if σ.1 = σ'.1 then
      ∑ i : Fin Cl.count, (if (σ.1 : ℤ) ∈ Cl.resolvedPart i then ((Cl.shareWeight i : ℝ) : ℂ) *
        ∫ p in K.rect, ((p.1 : ℝ) : ℂ) *
          (((Cl.strainDev i p : ℝ) : ℂ) * curlSesq (slotValue B σ.2 p).1 (slotValue B σ'.2 p).1
            + (((1 / 2) * Exterior.traceFreeConst * Cl.gradDev i p : ℝ) : ℂ) *
              (((S.splitLength : ℝ) : ℂ) * sumSesq (slotValue B σ.2 p).1 (slotValue B σ'.2 p).1
                + vecSesq (slotValue B σ.2 p).2 (slotValue B σ'.2 p).2 / ((S.splitLength : ℝ) : ℂ)))
        else 0)
      else 0)

def actuatorRow (i : Fin k) : D → ℂ :=
  fun d => ∑ σ : modes × LowSlot Q, slotRow I σ d *
    ∫ p in K.rect, ((K.lineWeight p.1 * CellScalars.rHat K p : ℝ) : ℂ) * (1 / 2 : ℂ) *
      entryPairing (slotValue B σ.2 p).1 (fun a b => modeMat c.order σ.1 (c.modelActuatorGrad i) p.1 p.2 a b)

def pinRow (i : Fin k) : D → ℂ :=
  fun d => ∑ σ : modes × LowSlot Q, slotRow I σ d *
    ∫ p in K.rect, ((K.lineWeight p.1 * CellScalars.rHat K p : ℝ) : ℂ) *
      entryPairing (slotValue B σ.2 p).1 (fun a b => modeMat c.order σ.1 (c.modelPinField i) p.1 p.2 a b)

def crossRow : Fin k ⊕ Fin k → D → ℂ
  | .inl i => actuatorRow c K B I i
  | .inr i => pinRow c K B I i

def localForm : Matrix (D ⊕ (Fin k ⊕ Fin k)) (D ⊕ (Fin k ⊕ Fin k)) ℂ :=
  Matrix.fromBlocks
    (energyForm K B I c.order S.energyWeight S.vorticityWeight S.tailShift - classForm K B S Cl I + pairForm c K B S I)
    (fun d x => (starRingEnd ℂ) (crossRow c K B I x d))
    (fun x d => crossRow c K B I x d)
    0

end Forms

def layoutIndex (L : CellLayout) : LowIndex L.Datum L.modes L.degCoef L.degSide where
  strainSlot := CellDatum.lowStrain
  velocitySlot := CellDatum.lowVelocity
  radialFaceRow := fun n e a b l => L.strainFaceRow n ⟨e.val, by omega⟩ a b l
  heightFaceRow := fun n e a b l => L.strainFaceRow n ⟨e.val + 2, by omega⟩ a b l

end CellEnergy

end CellCert

end Breakdown

end
end

section

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars

abbrev LowIndex := ℤ × Fin 3 × Fin 4 × ℕ × ℕ

def lowSupport (S : CellScalars) : Finset LowIndex :=
  S.resolved ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ (Finset.range (S.degHigh + 1) ×ˢ Finset.range (S.degHigh + 1))))

abbrev LowSupp (S : CellScalars) := {i : LowIndex // i ∈ lowSupport S}

abbrev Aug (S : CellScalars) (k : ℕ) := LowSupp S ⊕ (Fin k ⊕ Fin k)

def rankOne {ι : Type} (s : ι → ℂ) : Matrix ι ι ℂ := fun e e' => (starRingEnd ℂ) (s e) * s e'

def linForm {ι : Type} [Fintype ι] (t U : ι → ℂ) : ℂ := ∑ e, t e * U e

section Synthesis

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)

def unitStrain (i : LowIndex) (n : ℤ) (p : ℝ × ℝ) : Fin 3 → Fin 3 → ℂ := fun a b =>
  if i.1 = n ∧ i.2.1 = a ∧ i.2.2.1.val = b.val then
    ((B.radialPoly i.2.2.2.1 p.1 * B.heightPoly i.2.2.2.2 p.2 : ℝ) : ℂ) else 0

def unitVelocity (i : LowIndex) (n : ℤ) (p : ℝ × ℝ) : Fin 3 → ℂ := fun a =>
  if i.1 = n ∧ i.2.1 = a ∧ i.2.2.1.val = 3 then
    ((B.radialPoly i.2.2.2.1 p.1 * B.heightPoly i.2.2.2.2 p.2 : ℝ) : ℂ) else 0

def synthStrain (U : Aug S k → ℂ) (n : ℤ) (p : ℝ × ℝ) : Fin 3 → Fin 3 → ℂ := fun a b =>
  ∑ i : LowSupp S, U (Sum.inl i) * unitStrain B i.1 n p a b

def synthVelocity (U : Aug S k → ℂ) (n : ℤ) (p : ℝ × ℝ) : Fin 3 → ℂ := fun a =>
  ∑ i : LowSupp S, U (Sum.inl i) * unitVelocity B i.1 n p a

def kappaPart (U : Aug S k → ℂ) (i : Fin k) : ℂ := U (Sum.inr (Sum.inl i))

def pinPart (U : Aug S k → ℂ) (i : Fin k) : ℂ := U (Sum.inr (Sum.inr i))

def yStrainOf (sAt : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ) (vAt : ℤ → ℝ × ℝ → Fin 3 → ℂ) (κ ζ : Fin k → ℂ)
    (n : ℤ) (p : ℝ × ℝ) : Fin 3 → Fin 3 → ℂ := fun a b =>
  ((rHat K p : ℝ) : ℂ) *
    ((if n ∈ S.resolved ∪ S.band then ∑ n' ∈ S.resolved,
        waveActionStrain (strainMode c (n - n') p) (curlGradMode c (n - n') p) (sAt n' p) (vAt n' p) a b else 0)
      + (if n ∈ S.resolved then splitStrain (matAct (S.localMatrix n p) (pairVec (sAt n p) (vAt n p))) a b else 0)
      + ∑ i : Fin k, ((κ i / 2) * modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b
          + ζ i * modeMat c.order n (c.modelPinField i) p.1 p.2 a b))

def yVelocityOf (sAt : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ) (vAt : ℤ → ℝ × ℝ → Fin 3 → ℂ) (n : ℤ) (p : ℝ × ℝ) :
    Fin 3 → ℂ := fun b =>
  ((rHat K p : ℝ) : ℂ) *
    ((if n ∈ S.resolved ∪ S.band then ∑ n' ∈ S.resolved,
        waveActionVelocity (curlGradMode c (n' - n) p) (sAt n' p) b else 0)
      + (if n ∈ S.resolved then splitVelocity (matAct (S.localMatrix n p) (pairVec (sAt n p) (vAt n p))) b else 0))

def yFoldedOf (sAt : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ) (vAt : ℤ → ℝ × ℝ → Fin 3 → ℂ) (κ ζ : Fin k → ℂ)
    (n : ℤ) (p : ℝ × ℝ) : Fin 3 → Fin 3 → ℂ :=
  if n ∈ S.resolved then yStrainOf c K S sAt vAt κ ζ n p
  else foldVelocity (azimuth c.order n) p.1 (yStrainOf c K S sAt vAt κ ζ n p) (yVelocityOf c K S sAt vAt n p)

def yCoef (U : Aug S k → ℂ) (n : ℤ) (j l : ℕ) (a b : Fin 3) : ℂ :=
  B.coef K (fun p => yFoldedOf c K S (synthStrain S B U) (synthVelocity S B U) (kappaPart S U) (pinPart S U) n p a b) j l

def yVelCoef (U : Aug S k → ℂ) (n : ℤ) (j l : ℕ) (a : Fin 3) : ℂ :=
  B.coef K (fun p => yVelocityOf c K S (synthStrain S B U) (synthVelocity S B U) n p a) j l

open Classical in
def yVec (n : ℤ) (j l : ℕ) (a b : Fin 3) : Aug S k → ℂ := fun e => yCoef c K S B (Pi.single e 1) n j l a b

def symVec (n : ℤ) (j l : ℕ) (a b : Fin 3) : Aug S k → ℂ := fun e =>
  (yVec c K S B n j l a b e + yVec c K S B n j l b a e) / 2

def antiVec (n : ℤ) (j l : ℕ) (a b : Fin 3) : Aug S k → ℂ := fun e =>
  (yVec c K S B n j l a b e - yVec c K S B n j l b a e) / 2

open Classical in
def velVec (n : ℤ) (j l : ℕ) (a : Fin 3) : Aug S k → ℂ := fun e => yVelCoef c K S B (Pi.single e 1) n j l a

end Synthesis

section Pieces

variable {k N slots : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)
  (R : CellRows N slots k)

def nearMatrix : Matrix (Aug S k) (Aug S k) ℂ :=
  (∑ n ∈ R.yModes, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
    if n ∉ S.resolved ∨ S.degHigh < max j l then
      ∑ a : Fin 3, ∑ b : Fin 3,
        (((1 / S.symWeight n j l : ℝ) : ℂ) • rankOne (symVec c K S B n j l a b)
          + ((1 / S.antiWeight n j l : ℝ) : ℂ) • rankOne (antiVec c K S B n j l a b))
    else 0)
  + ∑ n ∈ S.resolved, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
    if S.degHigh ≤ max j l then
      ∑ a : Fin 3, ((1 / S.velWeight n j l : ℝ) : ℂ) • rankOne (velVec c K S B n j l a)
    else 0

def rowCouplingCoef (a : Fin N) (n' : ℤ) (j l : ℕ) (i q : Fin 3) : ℂ :=
  B.coef K (fun p => rowCouplingFolded c K S R a n' p i q) j l

def rowCouplingVelCoef (a : Fin N) (n' : ℤ) (j l : ℕ) (i : Fin 3) : ℂ :=
  B.coef K (fun p => rowCouplingVelocity c K R a n' p i) j l

def rowYVec (a : Fin N) : Aug S k → ℂ := fun e =>
  (∑ n' ∈ S.resolved ∪ S.band, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
    if n' ∉ S.resolved ∨ S.degHigh < max j l then
      ∑ i : Fin 3, ∑ q : Fin 3,
        (symVec c K S B n' j l i q e *
            (starRingEnd ℂ) ((rowCouplingCoef c K S B R a n' j l i q + rowCouplingCoef c K S B R a n' j l q i) / 2)
              / (S.symWeight n' j l : ℂ)
          + antiVec c K S B n' j l i q e *
            (starRingEnd ℂ) ((rowCouplingCoef c K S B R a n' j l i q - rowCouplingCoef c K S B R a n' j l q i) / 2)
              / (S.antiWeight n' j l : ℂ))
    else 0)
  + ∑ n' ∈ S.resolved, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
    if S.degHigh ≤ max j l then
      ∑ i : Fin 3, velVec c K S B n' j l i e * (starRingEnd ℂ) (rowCouplingVelCoef c K B R a n' j l i)
        / (S.velWeight n' j l : ℂ)
    else 0

open Classical in
def augToFar : Aug S k → LowIndex ⊕ (Fin k ⊕ Fin k) := Sum.elim (fun i => Sum.inl i.1) Sum.inr

open Classical in
def farMatrix : Matrix (Aug S k) (Aug S k) ℂ := fun e e' =>
  if (∀ i, e = Sum.inl i → i.1 ∈ R.farSupport) ∧ (∀ i, e' = Sum.inl i → i.1 ∈ R.farSupport) then
    R.farKernel (augToFar S e) (augToFar S e') else 0

end Pieces

section RowFunctional

variable {k N slots : ℕ} (c : FracCellData k N) (α : ℝ)

def rowModeVec (a : Fin N) (n : ℤ) (p : ℝ × ℝ) : Fin 3 → ℂ := modeVec c.order n (c.row a) p.1 p.2

def rowModeGrad (a : Fin N) (n : ℤ) (p : ℝ × ℝ) : Fin 3 → Fin 3 → ℂ :=
  modeMat c.order n (fun y => fderiv ℝ (c.row a) y) p.1 p.2

def pairC (x y : Fin 3 → ℂ) : ℂ := ∑ i : Fin 3, x i * (starRingEnd ℂ) (y i)

def frameY (p : ℝ × ℝ) : Fin 3 → ℂ := ![(p.1 : ℂ), 0, (p.2 : ℂ)]

def frameTurnY (p : ℝ × ℝ) : Fin 3 → ℂ := ![0, (p.1 : ℂ), 0]

def turnC (v : Fin 3 → ℂ) : Fin 3 → ℂ := ![-v 1, v 0, 0]

def basisVal (B : CellBases) (j l : ℕ) (p : ℝ × ℝ) : ℂ := ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)

def strainRowCoef (K : CellBox) (B : CellBases) (R : CellRows N slots k) (a : Fin N) (n : ℤ) (a' b' : Fin 3)
    (j l : ℕ) : ℂ :=
  ∑ m ∈ R.rowModes, ∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p *
    ((if m = n then
        ((1 / (2 * α) : ℝ) : ℂ) * frameY p b' * (starRingEnd ℂ) (rowModeVec c a m p a')
          + (c.modelRate : ℂ) * frameTurnY p b' * (starRingEnd ℂ) (rowModeVec c a m p a')
          + (c.splitVisc : ℂ) * (starRingEnd ℂ) (rowModeGrad c a m p a' b')
      else 0)
      + pairC (crossC (fun i => (CellCert.permSign i b' a' : ℂ)) (modeVec c.order (m - n) c.modelVelocity p.1 p.2))
          (rowModeVec c a m p))

def velocityRowCoef (K : CellBox) (B : CellBases) (R : CellRows N slots k) (a : Fin N) (n : ℤ) (a' : Fin 3)
    (j l : ℕ) : ℂ :=
  ∑ m ∈ R.rowModes, ∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p *
    ((if m = n then
        ((1 - 1 / (2 * α) : ℝ) : ℂ) * (starRingEnd ℂ) (rowModeVec c a m p a')
          - (c.modelRate : ℂ) * pairC (turnC (Pi.single a' 1)) (rowModeVec c a m p)
      else 0)
      + pairC (crossC (modeVec c.order (m - n) c.modelCurl p.1 p.2) (Pi.single a' 1)) (rowModeVec c a m p))

def segmentTrace (S : FaceSegment) (f : ℝ × ℝ → ℂ) (d : ℕ) : ℂ :=
  S.moment false f (CellBox.radialDeriv f) (CellBox.heightDeriv f) d

def gradSideRowCoef (L : CellLayout) (a : Fin N) (n : ℤ) (s : Fin L.segCount) (a' : Fin 3) (d : ℕ) : ℂ :=
  -(c.splitVisc : ℂ) * edgeSign (L.segment s).level (L.segment s).other *
    (if (L.segment s).radial then ((L.segment s).level : ℂ) else 1) *
    (starRingEnd ℂ) (segmentTrace (L.segment s) (fun p => rowModeVec c a n p a') d)

def presSideRowCoef (L : CellLayout) (a : Fin N) (n : ℤ) (s : Fin L.presCount) (d : ℕ) : ℂ :=
  edgeSign (L.presSegment s).level (L.presSegment s).other *
    (if (L.presSegment s).radial then ((L.presSegment s).level : ℂ) else 1) *
    (starRingEnd ℂ) (segmentTrace (L.presSegment s)
      (fun p => rowModeVec c a n p (if (L.presSegment s).radial then 0 else 2)) d)

def segmentNormal (L : CellLayout) (s : Fin L.segCount) : Fin 3 := if (L.segment s).radial then 0 else 2

def sideNormal (e : Fin 4) : Fin 3 := if e.val < 2 then 0 else 2

def faceLevel (L : CellLayout) (e : Fin 4) : ℝ :=
  if e.val = 0 then L.box.r₁ else if e.val = 1 then L.box.r₂ else if e.val = 2 then L.box.z₁ else L.box.z₂

def faceOther (L : CellLayout) (e : Fin 4) : ℝ :=
  if e.val < 2 then L.box.r₁ + L.box.r₂ - faceLevel L e else L.box.z₁ + L.box.z₂ - faceLevel L e

def faceRowCoef (L : CellLayout) (a : Fin N) (n : ℤ) (e : Fin 4) (l : ℕ) : ℂ :=
  if e.val < 2 then
    ∫ z in Set.Icc L.box.z₁ L.box.z₂, rowModeVec c a n (faceLevel L e, z) 0 * ((L.bases.heightPoly l z : ℝ) : ℂ)
  else
    ∫ r in Set.Icc L.box.r₁ L.box.r₂, ((L.box.lineWeight r * L.bases.radialPoly l r : ℝ) : ℂ) *
      rowModeVec c a n (r, faceLevel L e) 2

def normalFaceRowData (L : CellLayout) (a : Fin N) : L.Datum → ℂ := fun d =>
  ∑ n : L.modes, ∑ e : Fin 4, ∑ l : Fin (L.degSide + 1),
    if e.val = 0 ∧ L.box.r₁ = 0 then 0 else
      -(c.splitVisc : ℂ) * edgeSign (faceLevel L e) (faceOther L e) *
        (if e.val < 2 then (faceLevel L e : ℂ) else 1) * (starRingEnd ℂ) (faceRowCoef c L a n e l) *
          L.strainFaceRow n e (sideNormal e) (sideNormal e) l d

def layoutRowData (L : CellLayout) (R : CellRows N slots k) (a : Fin N) : L.Datum → ℂ := fun d =>
  Sum.elim (fun i => strainRowCoef c α L.box L.bases R a i.1.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2)
  (Sum.elim (fun i => velocityRowCoef c α L.box L.bases R a i.1.1 i.2.1 i.2.2.1 i.2.2.2)
  (Sum.elim (fun _ => 0)
  (Sum.elim (fun i => if i.2.2.1 = segmentNormal L i.2.1 then 0 else gradSideRowCoef c L a i.1.1 i.2.1 i.2.2.1 i.2.2.2)
  (Sum.elim (fun i => presSideRowCoef c L a i.1.1 i.2.1 i.2.2)
  (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 0))))))) d
    + normalFaceRowData c L a d

def layoutRowKappa (a : Fin N) (i : Fin k) : ℝ :=
  (∫ y, inner ℝ (c.modelActuator i y) (c.row a y)) / (4 * Real.pi)

end RowFunctional

structure CellFormulaInputs (k N : ℕ) (S : CellScalars) where
  D : Type
  dataFintype : Fintype D
  dataDecEq : DecidableEq D
  skeletonCount : ℕ
  interiorCount : ℕ
  coordToData : (Fin skeletonCount ⊕ Fin interiorCount → ℝ) → (D → ℂ)
  trueData : FieldTuple k → D → ℂ
  skeleton : FieldTuple k → Fin skeletonCount → ℝ
  interior : FieldTuple k → Fin interiorCount → ℝ
  lowEntry : LowSupp S → Option D
  rowData : Fin N → D → ℂ
  rowKappa : Fin N → Fin k → ℝ
  localForm : Matrix (D ⊕ (Fin k ⊕ Fin k)) (D ⊕ (Fin k ⊕ Fin k)) ℂ

namespace CellFormulaInputs

variable {k N slots : ℕ} {S : CellScalars} (F : CellFormulaInputs k N S) (c : FracCellData k N) (K : CellBox)
  (B : CellBases) (R : CellRows N slots k)

abbrev Coord := Fin F.skeletonCount ⊕ Fin F.interiorCount ⊕ Fin k ⊕ Fin k

def dataVec (u : F.D → ℂ) (κ ζ : Fin k → ℝ) : F.D ⊕ (Fin k ⊕ Fin k) → ℂ :=
  Sum.elim u (Sum.elim (fun i => ((κ i : ℝ) : ℂ)) (fun i => ((ζ i : ℝ) : ℂ)))

def augOfData (u : F.D → ℂ) (κ ζ : Fin k → ℝ) : Aug S k → ℂ :=
  Sum.elim (fun i => (F.lowEntry i).elim 0 u) (Sum.elim (fun i => ((κ i : ℝ) : ℂ)) (fun i => ((ζ i : ℝ) : ℂ)))

def rowValue (a : Fin N) (u : F.D → ℂ) (κ : Fin k → ℝ) : ℝ :=
  (letI := F.dataFintype; ∑ d : F.D, F.rowData a d * u d).re + ∑ i : Fin k, κ i * F.rowKappa a i

def residualValue (a : Fin N) (u : F.D → ℂ) (κ ζ : Fin k → ℝ) : ℝ :=
  F.rowValue a u κ - (letI := F.dataFintype; letI := F.dataDecEq;
    (linForm (rowYVec c K S B R a) (F.augOfData u κ ζ)).re)

def formulaValue (w : F.Coord → ℝ) : ℝ :=
  letI := F.dataFintype; letI := F.dataDecEq;
  let u := F.coordToData (fun e => w (Sum.elim (fun s => Sum.inl s) (fun t => Sum.inr (Sum.inl t)) e))
  let κ : Fin k → ℝ := fun i => c.splitVisc * w (Sum.inr (Sum.inr (Sum.inl i)))
  let ζ : Fin k → ℝ := fun i => c.splitVisc * w (Sum.inr (Sum.inr (Sum.inr i)))
  (quadFormValue F.localForm (F.dataVec u κ ζ)
      - quadFormValue (nearMatrix c K S B R) (F.augOfData u κ ζ)
      - quadFormValue (farMatrix S R) (F.augOfData u κ ζ) / R.farShare
      + ∑ b : Fin R.reducerCount, (∑ a ∈ R.rowSet, R.reducer b a * F.residualValue c K B R a u κ ζ) ^ 2)
    / c.splitVisc

def exactFormula : Matrix F.Coord F.Coord ℝ := fun e e' =>
  (F.formulaValue c K B R (Pi.single e 1 + Pi.single e' 1)
    - F.formulaValue c K B R (Pi.single e 1) - F.formulaValue c K B R (Pi.single e' 1)) / 2

end CellFormulaInputs

section Canonical

variable {k N slots : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
  (R : CellRows N slots k) (L : CellLayout) (P : ParamData L.Datum) (α : ℝ) (g : GaugeShift k)

def skeletonCoords : Finset (L.Datum × Fin 2) := Finset.univ.filter (fun p => p.1 ∈ P.skeleton)

def interiorCoords : Finset (L.Datum × Fin 2) := Finset.univ.filter (fun p => p.1 ∈ P.interiorSet)

def embedCoords (w : Fin (skeletonCoords L P).card ⊕ Fin (interiorCoords L P).card → ℝ) : L.Datum × Fin 2 → ℝ :=
  fun p => if h : p ∈ skeletonCoords L P then w (Sum.inl ((skeletonCoords L P).equivFin ⟨p, h⟩))
    else if h' : p ∈ interiorCoords L P then w (Sum.inr ((interiorCoords L P).equivFin ⟨p, h'⟩)) else 0

def canonicalInputs : CellFormulaInputs k N S where
  D := L.Datum
  dataFintype := inferInstance
  dataDecEq := inferInstance
  skeletonCount := (skeletonCoords L P).card
  interiorCount := (interiorCoords L P).card
  coordToData := fun w => P.param (L.realCoord (embedCoords L P w))
  trueData := fun x => L.shiftedData g x
  skeleton := fun x i => L.realPart (L.shiftedData g x) ((skeletonCoords L P).equivFin.symm i).1
  interior := fun x i => L.realPart (L.shiftedData g x) ((interiorCoords L P).equivFin.symm i).1
  lowEntry := fun i => L.lowEntry i.1
  rowData := layoutRowData c α L R
  rowKappa := layoutRowKappa c
  localForm := CellEnergy.localForm c K B S Cl (CellEnergy.layoutIndex L)

end Canonical

end CellFormula

end CellCert

end Breakdown

end
end

section

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula _root_.Breakdown.CellCert.Finite

open Classical in
def systemSkeletonCoords (L : CellLayout) (P : ParamData L.Datum) : Finset (L.Datum × Fin 2) :=
  (skeletonCoords L P).filter L.IsSystemCoord

open Classical in
def systemInteriorCoords (L : CellLayout) (P : ParamData L.Datum) : Finset (L.Datum × Fin 2) :=
  (interiorCoords L P).filter L.IsSystemCoord

def systemVector (L : CellLayout) (P : ParamData L.Datum) (s : Fin (systemSkeletonCoords L P).card → ℝ)
    (ξ : Fin (systemInteriorCoords L P).card → ℝ) : L.Datum × Fin 2 → ℝ := fun p =>
  if h : p ∈ systemSkeletonCoords L P then s ((systemSkeletonCoords L P).equivFin ⟨p, h⟩)
  else if h' : p ∈ systemInteriorCoords L P then ξ ((systemInteriorCoords L P).equivFin ⟨p, h'⟩) else 0

def IsPressureDatum (L : CellLayout) (d : L.Datum) : Prop :=
  Sum.elim (fun _ => False) (Sum.elim (fun _ => False) (Sum.elim (fun _ => False) (Sum.elim (fun _ => False)
    (Sum.elim (fun _ => True) (fun _ => False))))) d

open Classical in
def presetScale (L : CellLayout) (visc : ℝ) (d : L.Datum) : ℝ := if IsPressureDatum L d then visc else 1

def expandedCoords (L : CellLayout) (P : ParamData L.Datum) (visc : ℝ) (s : Fin (systemSkeletonCoords L P).card → ℝ)
    (ξ : Fin (systemInteriorCoords L P).card → ℝ) :
    Fin (skeletonCoords L P).card ⊕ Fin (interiorCoords L P).card → ℝ :=
  Sum.elim
    (fun i => presetScale L visc ((skeletonCoords L P).equivFin.symm i).1.1 *
      L.expandSystem (systemVector L P s ξ) ((skeletonCoords L P).equivFin.symm i).1)
    (fun j => presetScale L visc ((interiorCoords L P).equivFin.symm j).1.1 *
      L.expandSystem (systemVector L P s ξ) ((interiorCoords L P).equivFin.symm j).1)

structure CellCoords (k slots : ℕ) where
  layout : CellLayout
  param : ParamData layout.Datum
  selection : Fin param.relCount → layout.RelIndex
  Tmap : Matrix (Fin (systemSkeletonCoords layout param).card) (Fin slots) ℝ
  gaugeSpec : GaugeSpec layout
  gaugeLeft : FieldTuple k → ℝ
  gaugeRight : FieldTuple k → ℝ
  given : Matrix (Fin (systemSkeletonCoords layout param).card ⊕ Fin k ⊕ Fin k)
    (Fin (systemSkeletonCoords layout param).card ⊕ Fin k ⊕ Fin k) ℝ

namespace CellCoords

variable {k slots : ℕ} (C : CellCoords k slots)

def restrictState (visc : ℝ) (kappaSlot : Fin k → Fin slots) (w : Fin slots ⊕ Fin k → ℝ) :
    Fin (systemSkeletonCoords C.layout C.param).card ⊕ Fin k ⊕ Fin k → ℝ :=
  Sum.elim (fun j => ∑ i, C.Tmap j i * w (Sum.inl i))
    (Sum.elim (fun i => w (Sum.inl (kappaSlot i)) / visc) (fun i => w (Sum.inr i) / visc))

def formula {N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N slots k) (α : ℝ) : CellFormulaInputs k N S :=
  canonicalInputs c K S B Cl R C.layout C.param α (C.layout.gaugeShiftOf C.gaugeLeft C.gaugeRight)

end CellCoords

end CellCoordinates

end CellCert

end Breakdown

end
end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace CellBox

variable (K : CellBox)

def radialTail (B : CellBases) (D : ℕ) (g : ℝ → ℂ) : ℝ :=
  (∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ‖g r‖ ^ 2)
    - ∑ j' ∈ Finset.range (D + 1),
        ‖∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * g r * (B.radialPoly j' r : ℂ)‖ ^ 2

def heightTail (B : CellBases) (D : ℕ) (g : ℝ → ℂ) : ℝ :=
  (∫ z in Set.Icc K.z₁ K.z₂, ‖g z‖ ^ 2)
    - ∑ l' ∈ Finset.range (D + 1), ‖∫ z in Set.Icc K.z₁ K.z₂, g z * (B.heightPoly l' z : ℂ)‖ ^ 2

end CellBox

structure TailFamily (I O : Type) [Fintype I] [Fintype O] where
  dim : I → ℕ
  mult : (i : I) → O → Fin (dim i) → ℝ × ℝ → ℝ → ℂ
  inModes : Finset ℤ
  outModes : O → Finset ℤ
  outWeight : O → ℝ
  inputDeg : I → ℕ
  radialBound : I → ℕ → ℝ
  heightBound : I → ℕ → ℝ

namespace TailFamily

variable {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O)

def radialTotal : ℝ := ∑ i, ∑ j ∈ Finset.range (T.inputDeg i + 1), T.radialBound i j

def heightTotal : ℝ := ∑ i, ∑ l ∈ Finset.range (T.inputDeg i + 1), T.heightBound i l

end TailFamily

structure FarGroupBounds (I : Type) where
  radialBound : I → ℕ → ℝ
  heightBound : I → ℕ → ℝ

structure FarMajorantData where
  strainGroup : FarGroupBounds (Fin 2)
  velocityGroup : FarGroupBounds Unit
  bandGroup : FarGroupBounds Unit
  strainWeight : ℝ
  resolvedVelocityWeight : ℝ
  bandVelocityWeight : ℝ
  share : ℝ
  turnBound : ℝ
  strainFloor : ℝ
  velocityFloor : ℝ

namespace CellScalars

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)

def strainAt (p : ℝ × ℝ) (θ : ℝ) : Fin 3 → Fin 3 → ℂ :=
  fun a b => (frameMat θ (c.modelStrain (cylPoint p.1 θ p.2)) a b : ℂ)

def curlGradAt (p : ℝ × ℝ) (θ : ℝ) : Fin 3 → Fin 3 → ℂ :=
  fun a b => (frameMat θ (c.modelCurlGrad (cylPoint p.1 θ p.2)) a b : ℂ)

def unitVec3 (c' : Fin 3) : Fin 3 → ℂ := fun a => if a = c' then 1 else 0

def unitMat (e : Fin 9) : Fin 3 → Fin 3 → ℂ := fun a b => if 3 * a.val + b.val = e.val then 1 else 0

def strainGroupFamily (F : FarMajorantData) : TailFamily (Fin 2) (Fin 3 × Fin 3) where
  dim := fun _ => 3
  mult := fun i o c' p θ => ((rHat K p : ℝ) : ℂ) *
    (if i = 0 then -curlAdj (matVec (strainAt c p θ) (unitVec3 c')) o.1 o.2
      else (1 / 2 : ℂ) * couplingMap (curlGradAt c p θ) (unitVec3 c') o.1 o.2)
  inModes := S.resolved
  outModes := fun _ => S.resolved ∪ S.band
  outWeight := fun _ => F.strainWeight
  inputDeg := fun i => if i = 0 then S.degHigh else S.degHigh - 1
  radialBound := F.strainGroup.radialBound
  heightBound := F.strainGroup.heightBound

def velocityGroupFamily (F : FarMajorantData) : TailFamily Unit (Fin 3) where
  dim := fun _ => 9
  mult := fun _ o e p θ => ((rHat K p : ℝ) : ℂ) * waveActionVelocity (curlGradAt c p θ) (unitMat e) o
  inModes := S.resolved
  outModes := fun _ => S.resolved
  outWeight := fun _ => F.resolvedVelocityWeight
  inputDeg := fun _ => S.degHigh
  radialBound := F.velocityGroup.radialBound
  heightBound := F.velocityGroup.heightBound

def bandGroupFamily (F : FarMajorantData) : TailFamily Unit (Fin 3) where
  dim := fun _ => 9
  mult := fun _ o e p θ => ((p.1 * rHat K p : ℝ) : ℂ) * waveActionVelocity (curlGradAt c p θ) (unitMat e) o
  inModes := S.resolved
  outModes := fun _ => S.band
  outWeight := fun _ => F.bandVelocityWeight
  inputDeg := fun _ => S.degHigh
  radialBound := F.bandGroup.radialBound
  heightBound := F.bandGroup.heightBound

def lowStrainCoef (u : (ℤ × Fin 3 × Fin 4 × ℕ × ℕ) ⊕ (Fin k ⊕ Fin k) → ℂ) (n : ℤ) (j l : ℕ) :
    Fin 3 → Fin 3 → ℂ := fun a b => u (Sum.inl (n, a, ⟨b.val, by omega⟩, j, l))

def lowVelocityCoef (u : (ℤ × Fin 3 × Fin 4 × ℕ × ℕ) ⊕ (Fin k ⊕ Fin k) → ℂ) (n : ℤ) (j l : ℕ) : Fin 3 → ℂ :=
  fun a => u (Sum.inl (n, a, 3, j, l))

def groupWeight {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O) (i : I) (j l : ℕ) : ℝ :=
  if j ≤ T.inputDeg i ∧ l ≤ T.inputDeg i then T.radialTotal * T.radialBound i j + T.heightTotal * T.heightBound i l
  else 0

def farMajorantForm (F : FarMajorantData) (u : (ℤ × Fin 3 × Fin 4 × ℕ × ℕ) ⊕ (Fin k ⊕ Fin k) → ℂ) : ℝ :=
  ∑ n ∈ S.resolved, ∑ j ∈ Finset.range (S.degHigh + 1), ∑ l ∈ Finset.range (S.degHigh + 1),
    ((groupWeight (velocityGroupFamily c K S F) () j l
        + (if S.band = ∅ then 0 else groupWeight (bandGroupFamily c K S F) () j l))
        * sumSq (lowStrainCoef u n j l)
      + groupWeight (strainGroupFamily c K S F) 0 j l * curlSq (lowStrainCoef u n j l)
      + groupWeight (strainGroupFamily c K S F) 1 j l * vecSq (lowVelocityCoef u n j l))

end CellScalars

namespace CellScalars

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)

def rowSquareUpTo (B : CellBases) {slots : ℕ} (R : CellRows N slots k) (E : ℕ) (μ : Fin N → ℝ) : ℝ :=
  (∑ n' ∈ S.resolved ∪ S.band, ∑ j ∈ Finset.range (E + 1), ∑ l ∈ Finset.range (E + 1),
    if S.degNear < max j l then
      (sigmaWeightedPair
        (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => rowCouplingFolded c K S R a n' p i q) j l)
        (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => rowCouplingFolded c K S R a n' p i q) j l)
        (S.symWeight n' j l) (S.antiWeight n' j l)).re
    else 0)
  + ∑ n' ∈ S.resolved, ∑ j ∈ Finset.range (E + 1), ∑ l ∈ Finset.range (E + 1),
    if S.degNear < max j l then
      vecSq (fun i => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => rowCouplingVelocity c K R a n' p i) j l)
        / S.velWeight n' j l
    else 0

end CellScalars

end CellAnalysis

namespace CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

inductive SkeletonKey where
  | velocity (n : ℤ) (radial : Bool) (level lo hi : ℝ) (test : ℕ → ℕ → ℝ) (a : Fin 3) (d : ℕ)
  | gradient (n : ℤ) (radial : Bool) (level lo hi : ℝ) (test : ℕ → ℕ → ℝ) (a : Fin 3) (d : ℕ)
  | pressure (n : ℤ) (radial : Bool) (level lo hi : ℝ) (test : ℕ → ℕ → ℝ) (d : ℕ)
  | corner (n : ℤ) (point : ℝ × ℝ) (a : Fin 3)
  | stream (point : ℝ × ℝ)
  | private_

def keyOf (L : CellLayout) : L.Datum → SkeletonKey :=
  Sum.elim (fun _ => SkeletonKey.private_) (Sum.elim (fun _ => SkeletonKey.private_)
    (Sum.elim (fun q => SkeletonKey.velocity (q.1 : ℤ) (L.segment q.2.1).radial (L.segment q.2.1).level
        (L.segment q.2.1).lo (L.segment q.2.1).hi (L.segment q.2.1).testCoef q.2.2.1 q.2.2.2)
      (Sum.elim (fun q => SkeletonKey.gradient (q.1 : ℤ) (L.segment q.2.1).radial (L.segment q.2.1).level
          (L.segment q.2.1).lo (L.segment q.2.1).hi (L.segment q.2.1).testCoef q.2.2.1 q.2.2.2)
        (Sum.elim (fun q => SkeletonKey.pressure (q.1 : ℤ) (L.presSegment q.2.1).radial (L.presSegment q.2.1).level
            (L.presSegment q.2.1).lo (L.presSegment q.2.1).hi (L.presSegment q.2.1).testCoef q.2.2)
          (Sum.elim (fun q => SkeletonKey.corner (q.1 : ℤ) (L.corner q.2.1) q.2.2)
            (Sum.elim (fun c => SkeletonKey.stream (L.corner c)) (fun _ => SkeletonKey.private_)))))))

def pressurePositions (L : CellLayout) : L.Datum → List (ℝ × Bool) :=
  Sum.elim (fun _ => []) (Sum.elim (fun _ => []) (Sum.elim (fun _ => []) (Sum.elim (fun _ => [])
    (Sum.elim (fun q => if (L.presSegment q.2.1).radial then
        [((L.presSegment q.2.1).level, decide ((L.presSegment q.2.1).level ≠ L.box.r₁))]
      else [((L.presSegment q.2.1).lo, decide ((L.presSegment q.2.1).lo = L.box.r₂)),
        ((L.presSegment q.2.1).hi, decide ((L.presSegment q.2.1).hi = L.box.r₂))])
      (fun _ => [])))))

def rowEntries {slots : ℕ} (parts : List (Fin slots × ℝ)) (i' : Fin slots) : ℝ :=
  (parts.map (fun p => if p.1 = i' then p.2 else 0)).sum

def SegmentSplit : SkeletonKey → List (SkeletonKey × ℝ) → Prop
  | SkeletonKey.velocity n rad lev lo hi t a d, parts => ∃ mid, lo < mid ∧ mid < hi ∧
      (∀ p ∈ parts, ∃ lo' hi' t' d', p.1 = SkeletonKey.velocity n rad lev lo' hi' t' a d' ∧
        ((lo' = lo ∧ hi' = mid) ∨ (lo' = mid ∧ hi' = hi))) ∧
      (∀ lo' hi', ((lo' = lo ∧ hi' = mid) ∨ (lo' = mid ∧ hi' = hi)) → ∀ s ∈ Set.Icc lo' hi',
        (∑ i ∈ Finset.range (d + 1), t d i * s ^ i) =
          (parts.map (fun p => match p.1 with
            | SkeletonKey.velocity _ _ _ lo'' hi'' t'' _ d'' =>
                if lo'' = lo' ∧ hi'' = hi' then p.2 * ∑ i ∈ Finset.range (d'' + 1), t'' d'' i * s ^ i else 0
            | _ => 0)).sum)
  | SkeletonKey.gradient n rad lev lo hi t a d, parts => ∃ mid, lo < mid ∧ mid < hi ∧
      (∀ p ∈ parts, ∃ lo' hi' t' d', p.1 = SkeletonKey.gradient n rad lev lo' hi' t' a d' ∧
        ((lo' = lo ∧ hi' = mid) ∨ (lo' = mid ∧ hi' = hi))) ∧
      (∀ lo' hi', ((lo' = lo ∧ hi' = mid) ∨ (lo' = mid ∧ hi' = hi)) → ∀ s ∈ Set.Icc lo' hi',
        (∑ i ∈ Finset.range (d + 1), t d i * s ^ i) =
          (parts.map (fun p => match p.1 with
            | SkeletonKey.gradient _ _ _ lo'' hi'' t'' _ d'' =>
                if lo'' = lo' ∧ hi'' = hi' then p.2 * ∑ i ∈ Finset.range (d'' + 1), t'' d'' i * s ^ i else 0
            | _ => 0)).sum)
  | SkeletonKey.pressure n rad lev lo hi t d, parts => ∃ mid, lo < mid ∧ mid < hi ∧
      (∀ p ∈ parts, ∃ lo' hi' t' d', p.1 = SkeletonKey.pressure n rad lev lo' hi' t' d' ∧
        ((lo' = lo ∧ hi' = mid) ∨ (lo' = mid ∧ hi' = hi))) ∧
      (∀ lo' hi', ((lo' = lo ∧ hi' = mid) ∨ (lo' = mid ∧ hi' = hi)) → ∀ s ∈ Set.Icc lo' hi',
        (∑ i ∈ Finset.range (d + 1), t d i * s ^ i) =
          (parts.map (fun p => match p.1 with
            | SkeletonKey.pressure _ _ _ lo'' hi'' t'' d'' =>
                if lo'' = lo' ∧ hi'' = hi' then p.2 * ∑ i ∈ Finset.range (d'' + 1), t'' d'' i * s ^ i else 0
            | _ => 0)).sum)
  | _, _ => False

open Classical in
def streamEval (val : SkeletonKey → ℝ) (q : ℝ × ℝ) : ℝ :=
  if q.1 = 0 ∨ q.2 = 0 then 0 else val (SkeletonKey.stream q)

def FluxSplit : SkeletonKey → List (SkeletonKey × ℝ) → Prop
  | SkeletonKey.velocity n rad lev lo hi t a d, parts =>
      n = 0 ∧ a = (if rad then 0 else 2) ∧
      (∀ p ∈ parts, (∃ lo' hi' t' a' d', p.1 = SkeletonKey.velocity 0 rad lev lo' hi' t' a' d') ∨
        ∃ q, p.1 = SkeletonKey.stream q) ∧
      ∃ mid, lo < mid ∧ mid < hi ∧
      ∃ (th : Bool → ℕ → ℕ → ℝ) (D : ℕ) (e : Bool → ℕ → ℝ) (c0 c1 : Bool → ℝ),
        (∀ b : Bool, ∀ s ∈ Set.Icc (if b then mid else lo) (if b then hi else mid),
          (∑ i ∈ Finset.range (d + 1), t d i * s ^ i) =
            ∑ d' ∈ Finset.range (D + 1), e b d' * ∑ i ∈ Finset.range (d' + 1), th b d' i * s ^ i) ∧
        (∀ b : Bool, ∀ s ∈ Set.Icc (if b then mid else lo) (if b then hi else mid),
          (if rad then (1 : ℝ) else s) = c0 b * th b 0 0 + (if rad then 0 else c1 b * (th b 1 0 + th b 1 1 * s))) ∧
        ∀ val : SkeletonKey → ℝ,
          (∀ b : Bool,
            if rad then
              lev * c0 b * val (SkeletonKey.velocity 0 rad lev (if b then mid else lo) (if b then hi else mid) (th b) a 0) =
                streamEval val (lev, if b then mid else lo) - streamEval val (lev, if b then hi else mid)
            else
              c0 b * val (SkeletonKey.velocity 0 rad lev (if b then mid else lo) (if b then hi else mid) (th b) a 0)
                + c1 b * val (SkeletonKey.velocity 0 rad lev (if b then mid else lo) (if b then hi else mid) (th b) a 1) =
                streamEval val (if b then hi else mid, lev) - streamEval val (if b then mid else lo, lev)) →
          (∑ b : Bool, ∑ d' ∈ Finset.range (D + 1),
              e b d' * val (SkeletonKey.velocity 0 rad lev (if b then mid else lo) (if b then hi else mid) (th b) a d'))
            = (parts.map (fun p => p.2 * val p.1)).sum
  | _, _ => False

structure MeshData (k N : ℕ) (Sp : CellSplit k N) where
  coords : Fin Sp.cellCount → CellCoords k Sp.slots
  ownerCell : Fin Sp.slots → Fin Sp.cellCount
  ownerRow : (i : Fin Sp.slots) →
    Fin (systemSkeletonCoords (coords (ownerCell i)).layout (coords (ownerCell i)).param).card
  classCount : ℕ
  nodeClass : Fin Sp.cellCount → Bool → Fin classCount
  classRoot : Fin classCount → Fin Sp.cellCount
  classRootSide : Fin classCount → Bool
  classRootDatum : (cl : Fin classCount) →
    Fin (coords (classRoot cl)).layout.presCount × Fin (coords (classRoot cl)).layout.degSide
  classPath : Fin classCount → List (Fin Sp.cellCount × Bool)
  delaySlot : Fin Sp.delayCount → Fin Sp.slots
  delayRow : Fin Sp.delayCount → List (Fin Sp.slots × ℝ)
  delayExpansion : Fin Sp.slots → List (Fin Sp.slots × ℝ)

namespace MeshData

variable {k N : ℕ} {Sp : CellSplit k N} (M : MeshData k N Sp)

def rowDatum (K : Fin Sp.cellCount) (j : Fin (systemSkeletonCoords (M.coords K).layout (M.coords K).param).card) :
    (M.coords K).layout.Datum × Fin 2 :=
  ((systemSkeletonCoords (M.coords K).layout (M.coords K).param).equivFin.symm j).1

def rootValue (x : FieldTuple k) (cl : Fin M.classCount) : ℝ :=
  -((M.coords (M.classRoot cl)).layout.pressureDatumValue x (M.classRootDatum cl)) /
    (if M.classRootSide cl then (M.coords (M.classRoot cl)).layout.shiftCoefRight (M.classRootDatum cl)
      else (M.coords (M.classRoot cl)).layout.shiftCoefLeft (M.classRootDatum cl))

def classValue (x : FieldTuple k) (cl : Fin M.classCount) : ℝ :=
  M.rootValue x cl
    + ((M.classPath cl).map (fun e => if e.2 then (M.coords e.1).layout.gaugeJump (M.coords e.1).gaugeSpec x
        else -(M.coords e.1).layout.gaugeJump (M.coords e.1).gaugeSpec x)).sum

def canonicalLeft (K : Fin Sp.cellCount) (x : FieldTuple k) : ℝ := M.classValue x (M.nodeClass K false)

def canonicalRight (K : Fin Sp.cellCount) (x : FieldTuple k) : ℝ := M.classValue x (M.nodeClass K true)

def localValue {N' : ℕ} (c : FracCellData k N') (K : Fin Sp.cellCount) (x : FieldTuple k)
    (j : Fin (systemSkeletonCoords (M.coords K).layout (M.coords K).param).card) : ℝ :=
  (M.coords K).layout.realPart
      ((M.coords K).layout.shiftedData ((M.coords K).layout.gaugeShiftOf (M.canonicalLeft K) (M.canonicalRight K)) x)
      (M.rowDatum K j)
    / presetScale (M.coords K).layout c.splitVisc (M.rowDatum K j).1

def ownerKey (i : Fin Sp.slots) : SkeletonKey :=
  keyOf (M.coords (M.ownerCell i)).layout (M.rowDatum (M.ownerCell i) (M.ownerRow i)).1

def rowKey (K : Fin Sp.cellCount) (j : Fin (systemSkeletonCoords (M.coords K).layout (M.coords K).param).card) :
    SkeletonKey :=
  keyOf (M.coords K).layout (M.rowDatum K j).1

def ownerNodes (i : Fin Sp.slots) : List (ℝ × Fin M.classCount) :=
  (pressurePositions (M.coords (M.ownerCell i)).layout (M.rowDatum (M.ownerCell i) (M.ownerRow i)).1).map
    (fun q => (q.1, M.nodeClass (M.ownerCell i) q.2))

def rowNodes (K : Fin Sp.cellCount) (j : Fin (systemSkeletonCoords (M.coords K).layout (M.coords K).param).card) :
    List (ℝ × Fin M.classCount) :=
  (pressurePositions (M.coords K).layout (M.rowDatum K j).1).map (fun q => (q.1, M.nodeClass K q.2))

def participantNodes (K : Fin Sp.cellCount) (j : Fin (systemSkeletonCoords (M.coords K).layout (M.coords K).param).card)
    (parts : List (Fin Sp.slots × ℝ)) : List (ℝ × Fin M.classCount) :=
  M.rowNodes K j ++ (parts.map (fun p => M.ownerNodes p.1)).flatten

def baseMoment {N' : ℕ} (c : FracCellData k N') (x : FieldTuple k) (i : Fin Sp.slots) : ℝ :=
  if h : ∃ a, Sp.kappaSlot a = i then x.2.2.2.1 h.choose else M.localValue c (M.ownerCell i) x (M.ownerRow i)

def IsDelaySlot (i : Fin Sp.slots) : Prop := ∃ j, M.delaySlot j = i

open Classical in
def canonicalMoment {N' : ℕ} (c : FracCellData k N') (x : FieldTuple k) (i : Fin Sp.slots) : ℝ :=
  if M.IsDelaySlot i then ((M.delayExpansion i).map (fun p => p.2 * M.baseMoment c x p.1)).sum
  else M.baseMoment c x i

open Classical in
def delayVector (j : Fin Sp.delayCount) : Fin Sp.slots ⊕ Fin k → ℝ :=
  Sum.elim (fun i => (if M.delaySlot j = i then 1 else 0) - rowEntries (M.delayRow j) i) (fun _ => 0)

def extraKeys (extra : List ((K' : Fin Sp.cellCount) × (M.coords K').layout.Datum × ℝ)) :
    List (SkeletonKey × ℝ) :=
  extra.map (fun e => (keyOf (M.coords e.1).layout e.2.1, e.2.2))

def extraNodes (extra : List ((K' : Fin Sp.cellCount) × (M.coords K').layout.Datum × ℝ)) :
    List (ℝ × Fin M.classCount) :=
  (extra.map (fun e => (pressurePositions (M.coords e.1).layout e.2.1).map
    (fun q => (q.1, M.nodeClass e.1 q.2)))).flatten

def DeletedKey (K : Fin Sp.cellCount) (j : Fin (systemSkeletonCoords (M.coords K).layout (M.coords K).param).card)
    (key : SkeletonKey) : Prop :=
  ∃ (K' : Fin Sp.cellCount) (d : (M.coords K').layout.Datum), (M.coords K').layout.IsGaugeDeleted d ∧
    keyOf (M.coords K').layout d = key ∧
    ∀ u ∈ M.rowNodes K j, ∀ v ∈ (pressurePositions (M.coords K').layout d).map (fun q => (q.1, M.nodeClass K' q.2)),
      u.1 = v.1 → u.2 = v.2

end MeshData

open Classical in
structure IsMeshData (α : ℝ) {k N : ℕ} (c : FracCellData k N) (Sp : CellSplit k N) (M : MeshData k N Sp) : Prop where
  gauge_specs : ∀ K, IsGaugeSpec (M.coords K).layout (M.coords K).gaugeSpec
  gauge_valid : ∀ K, IsFaceSegment (M.coords K).layout.gauge ∧ (M.coords K).layout.gauge.testCoef 0 0 ≠ 0 ∧
    0 ≤ (M.coords K).layout.gauge.lo ∧
    ((M.coords K).layout.gauge.radial = true → (M.coords K).layout.gauge.level ≠ 0 ∧
      0 ≤ min (M.coords K).layout.gauge.level (M.coords K).layout.gauge.other)
  gauge_canonical : ∀ K, (M.coords K).gaugeLeft = M.canonicalLeft K ∧ (M.coords K).gaugeRight = M.canonicalRight K
  kappa_injective : Function.Injective Sp.kappaSlot
  kappa_unowned : ∀ a K j, (M.coords K).Tmap j (Sp.kappaSlot a) = 0
  delay_injective : Function.Injective M.delaySlot
  delay_not_kappa : ∀ j a, M.delaySlot j ≠ Sp.kappaSlot a
  delay_unowned : ∀ j K r, (M.coords K).Tmap r (M.delaySlot j) = 0
  expansion_base : ∀ i, ∀ p ∈ M.delayExpansion i, ¬ M.IsDelaySlot p.1
  expansion_consistent : ∀ j l, ¬ M.IsDelaySlot l → rowEntries (M.delayExpansion (M.delaySlot j)) l =
    ((M.delayRow j).map (fun p => p.2 *
      (if M.IsDelaySlot p.1 then rowEntries (M.delayExpansion p.1) l else if p.1 = l then 1 else 0))).sum
  delay_free : ∀ j i, Sp.freeMap (M.delaySlot j) i = ((M.delayRow j).map (fun p => p.2 * Sp.freeMap p.1 i)).sum
  delay_form : ∀ j, Sp.delayForm j = Matrix.vecMulVec (M.delayVector j) (M.delayVector j)
  rows : ∀ K j, ∃ (parts : List (Fin Sp.slots × ℝ))
      (extra : List ((K' : Fin Sp.cellCount) × (M.coords K').layout.Datum × ℝ)),
    (∀ i', (M.coords K).Tmap j i' = rowEntries parts i') ∧
    (∀ p ∈ parts, ∀ a, Sp.kappaSlot a ≠ p.1) ∧
    (∀ p ∈ parts, ¬ M.IsDelaySlot p.1) ∧
    (∀ p ∈ parts, (M.rowDatum (M.ownerCell p.1) (M.ownerRow p.1)).2 = (M.rowDatum K j).2) ∧
    (∀ e ∈ extra, (M.coords e.1).layout.IsGaugeDeleted e.2.1) ∧
    ((extra = [] ∧ ∃ i, parts = [(i, 1)] ∧ M.rowKey K j = M.ownerKey i ∧
        (M.rowKey K j = SkeletonKey.private_ → M.ownerCell i = K ∧ HEq (M.ownerRow i) j)) ∨
      SegmentSplit (M.rowKey K j) (parts.map (fun p => (M.ownerKey p.1, p.2)) ++ M.extraKeys extra) ∨
      FluxSplit (M.rowKey K j) (parts.map (fun p => (M.ownerKey p.1, p.2)) ++ M.extraKeys extra) ∨
      (parts = [] ∧ extra = [] ∧ M.DeletedKey K j (M.rowKey K j))) ∧
    (∀ u ∈ M.participantNodes K j parts ++ M.extraNodes extra,
      ∀ v ∈ M.participantNodes K j parts ++ M.extraNodes extra, u.1 = v.1 → u.2 = v.2)
  owner_row : ∀ i, (∀ a, Sp.kappaSlot a ≠ i) → ¬ M.IsDelaySlot i →
    ∀ i', (M.coords (M.ownerCell i)).Tmap (M.ownerRow i) i' = if i' = i then 1 else 0
  same_order : ∀ K, (M.coords K).layout.order = c.order
  same_gauge : ∀ K K', (M.coords K).layout.gauge = (M.coords K').layout.gauge
  radial_segments : ∀ K s, ((M.coords K).layout.segment s).radial →
    ((M.coords K).layout.segment s).level ≠ 0 ∧
      0 ≤ min ((M.coords K).layout.segment s).level ((M.coords K).layout.segment s).other
  radial_pressure_segments : ∀ K s, ((M.coords K).layout.presSegment s).radial →
    ((M.coords K).layout.presSegment s).level ≠ 0 ∧
      0 ≤ min ((M.coords K).layout.presSegment s).level ((M.coords K).layout.presSegment s).other
  corners_valid : ∀ K cr, ((M.coords K).layout.corner cr).1 ≠ 0 ∧
    ((M.coords K).layout.cornerOther cr).1 ≠ ((M.coords K).layout.corner cr).1 ∧
    ((M.coords K).layout.cornerOther cr).2 ≠ ((M.coords K).layout.corner cr).2 ∧
    0 ≤ min ((M.coords K).layout.corner cr).1 ((M.coords K).layout.cornerOther cr).1
  segments_valid : ∀ K, (∀ s, IsFaceSegment ((M.coords K).layout.segment s)) ∧
    ∀ s, IsFaceSegment ((M.coords K).layout.presSegment s)
  segments_nonneg : ∀ K, (∀ s, 0 ≤ ((M.coords K).layout.segment s).lo) ∧
    ∀ s, 0 ≤ ((M.coords K).layout.presSegment s).lo
  root_cells : ∀ cl, (M.classPath cl = [] ↔ M.nodeClass (M.classRoot cl) (M.classRootSide cl) = cl) ∧
    M.classRootDatum cl ∈ (M.coords (M.classRoot cl)).gaugeSpec.roots ∧
    (M.classRootSide cl = true →
      (M.coords (M.classRoot cl)).layout.shiftCoefRight (M.classRootDatum cl) ≠ 0 ∧
        (M.coords (M.classRoot cl)).layout.shiftCoefLeft (M.classRootDatum cl) = 0) ∧
    (M.classRootSide cl = false →
      (M.coords (M.classRoot cl)).layout.shiftCoefLeft (M.classRootDatum cl) ≠ 0 ∧
        (M.coords (M.classRoot cl)).layout.shiftCoefRight (M.classRootDatum cl) = 0)
  roots_exact : ∀ K r, r ∈ (M.coords K).gaugeSpec.roots →
    ∃ cl, ∃ _ : M.classRoot cl = K, HEq (M.classRootDatum cl) r ∧ M.classPath cl = []
  path_edges : ∀ K e, (M.coords K).gaugeSpec.edge = some e →
      (M.classRoot (M.nodeClass K true) = M.classRoot (M.nodeClass K false) ∧
        M.classRootSide (M.nodeClass K true) = M.classRootSide (M.nodeClass K false) ∧
        HEq (M.classRootDatum (M.nodeClass K true)) (M.classRootDatum (M.nodeClass K false))) ∧
      (M.classPath (M.nodeClass K true) = M.classPath (M.nodeClass K false) ++ [(K, true)] ∨
        M.classPath (M.nodeClass K false) = M.classPath (M.nodeClass K true) ++ [(K, false)])
  axis_left : ∀ K K', (M.coords K).layout.box.r₁ = 0 → (M.coords K').layout.box.r₁ = 0 →
    M.nodeClass K false = M.nodeClass K' false

end CellCoordinates

end CellCert

end Breakdown

end
end

section

open scoped ContDiff

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

structure ChartParams where
  L0 : ℝ
  rc : ℝ
  eps : ℝ
  m : ℕ

structure IsChartParams (P : ChartParams) : Prop where
  L0_pos : 0 < P.L0
  rc_pos : 0 < P.rc
  eps_pos : 0 < P.eps
  eps_lt : P.eps < 1 / 8
  m_pos : 0 < P.m

def heightRatio (y : Space) : ℝ := y 2 / ‖y‖

def qOf (y : Space) : ℝ := 1 - heightRatio y ^ 2

def angleOf (y : Space) : ℝ := Complex.arg (⟨y 0, y 1⟩ : ℂ)

def chartT (P : ChartParams) (y : Space) : ℝ := ‖y‖ / (‖y‖ + P.L0)

def chartS (P : ChartParams) (y : Space) : ℝ := 1 - chartT P y

def coreRatioT (P : ChartParams) (t : ℝ) : ℝ :=
  P.L0 ^ 2 * t ^ 2 / (P.L0 ^ 2 * t ^ 2 + P.rc ^ 2 * (1 - t) ^ 2)

def logPhase (P : ChartParams) (y : Space) : ℝ := (1 / 2) * Real.log (1 + ‖y‖ ^ 2 / P.rc ^ 2)

def decayFactor (P : ChartParams) (y : Space) : ℝ := chartS P y ^ (2 * P.eps)

def radialVec (y : Space) (i : Fin 3) : ℝ := y i / ‖y‖

def polarVecQ (y : Space) (i : Fin 3) : ℝ :=
  ![heightRatio y * y 0 / ‖y‖, heightRatio y * y 1 / ‖y‖, -(qOf y)] i

def azimVecQ (y : Space) (i : Fin 3) : ℝ := ![-(y 1) / ‖y‖, y 0 / ‖y‖, 0] i

def ofComponents (w : Fin 3 → ℝ) : Space :=
  EuclideanSpace.single 0 (w 0) + EuclideanSpace.single 1 (w 1) + EuclideanSpace.single 2 (w 2)

structure TensorMesh where
  tBreaks : List ℝ
  xBreaks : List ℝ

structure IsTensorMesh (M : TensorMesh) : Prop where
  t_sorted : M.tBreaks.Pairwise (· < ·)
  x_sorted : M.xBreaks.Pairwise (· < ·)
  t_first : M.tBreaks.head? = some 0
  t_last : M.tBreaks.getLast? = some 1
  x_first : M.xBreaks.head? = some 0
  x_last : M.xBreaks.getLast? = some 1

def cellIndex (l : List ℝ) (u : ℝ) : ℕ := ((l.drop 1).dropLast.filter (fun b => decide (b ≤ u))).length

def cellCount (l : List ℝ) : ℕ := l.length - 1

structure Spline where
  mesh : TensorMesh
  piece : ℕ → ℕ → MvPolynomial (Fin 2) ℂ

def Spline.evalHalf (S : Spline) (t x : ℝ) : ℂ :=
  MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (S.piece (cellIndex S.mesh.tBreaks t) (cellIndex S.mesh.xBreaks x))

def Spline.eval (S : Spline) (odd : Bool) (t x : ℝ) : ℂ :=
  (if odd && decide (x < 0) then -1 else 1) * S.evalHalf t |x|

def atFirst (c : ℂ) (P : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.bind₁ (fun k => if k = 0 then MvPolynomial.C c else MvPolynomial.X 1) P

def atSecond (c : ℂ) (P : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.bind₁ (fun k => if k = 1 then MvPolynomial.C c else MvPolynomial.X 0) P

def tDeriv (o : ℕ) (P : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ := (MvPolynomial.pderiv 0)^[o] P

def xDeriv (o : ℕ) (P : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ := (MvPolynomial.pderiv 1)^[o] P

structure IsSplineClass (a b : ℕ) (odd : Bool) (S : Spline) : Prop where
  mesh : IsTensorMesh S.mesh
  t_joins : ∀ i, 1 ≤ i → i < cellCount S.mesh.tBreaks → ∀ j < cellCount S.mesh.xBreaks, ∀ o ≤ a,
    atFirst (S.mesh.tBreaks.getD i 0 : ℂ) (tDeriv o (S.piece (i - 1) j)) =
      atFirst (S.mesh.tBreaks.getD i 0 : ℂ) (tDeriv o (S.piece i j))
  x_joins : ∀ j, 1 ≤ j → j < cellCount S.mesh.xBreaks → ∀ i < cellCount S.mesh.tBreaks, ∀ o ≤ b,
    atSecond (S.mesh.xBreaks.getD j 0 : ℂ) (xDeriv o (S.piece i (j - 1))) =
      atSecond (S.mesh.xBreaks.getD j 0 : ℂ) (xDeriv o (S.piece i j))
  parity : ∀ i < cellCount S.mesh.tBreaks, ∀ o ≤ b, (Even o ↔ odd = true) →
    atSecond 0 (xDeriv o (S.piece i 0)) = 0

def Spline.IsReal (S : Spline) : Prop := ∀ i j (μ : Fin 2 →₀ ℕ), (MvPolynomial.coeff μ (S.piece i j)).im = 0

def Spline.conj (S : Spline) : Spline :=
  ⟨S.mesh, fun i j => MvPolynomial.map (starRingEnd ℂ) (S.piece i j)⟩

def Spline.VanishesFrom (S : Spline) (tb : ℝ) : Prop :=
  ∀ i j, tb ≤ S.mesh.tBreaks.getD i 1 → S.piece i j = 0

structure ModeAmp where
  radialAmp : Spline
  polarAmp : Spline
  streamAmp : Spline
  swirlAmp : Spline

def ModeAmp.conj (A : ModeAmp) : ModeAmp :=
  ⟨A.radialAmp.conj, A.polarAmp.conj, A.streamAmp.conj, A.swirlAmp.conj⟩

structure FieldData where
  modes : Finset ℤ
  amp : ℤ → ModeAmp
  lowOrder : ℤ → ℕ
  highOrder : ℕ
  axisOrder : ℤ → ℕ
  guardStream : ℝ
  guardSwirl : ℝ

def weightPoly (e0 e1 : ℕ) (t : ℝ) : ℂ := ((t ^ e0 * (1 - t) ^ e1 : ℝ) : ℂ)

def radialScale (f : ℝ → ℝ → ℂ) (t x : ℝ) : ℂ := ((t * (1 - t) : ℝ) : ℂ) * deriv (fun t' => f t' x) t

def twistedScale (P : ChartParams) (n : ℤ) (β : ℝ) (f : ℝ → ℝ → ℂ) (t x : ℝ) : ℂ :=
  radialScale f t x + (Complex.I * ((n : ℝ) * β * coreRatioT P t : ℝ) - ((2 * P.eps * t : ℝ) : ℂ)) * f t x

def heightDeriv (f : ℝ → ℝ → ℂ) (t x : ℝ) : ℂ := deriv (fun x' => f t x') x

def reducedField (P : ChartParams) (D : FieldData) (n : ℤ) (β : ℝ) (t x : ℝ) : Fin 3 → ℂ :=
  if n = 0 then
    let p := fun t' : ℝ => weightPoly 1 D.highOrder t'
    let Ψ := (D.amp 0).streamAmp.eval true
    let G := (D.amp 0).swirlAmp.eval false
    ![-(p t * heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * Ψ t' x') t x),
      -(twistedScale P 0 β (fun t' x' => p t' * Ψ t' x') t x + 2 * (p t * Ψ t x)),
      p t * G t x]
  else
    let p := fun t' : ℝ => weightPoly (D.lowOrder n) D.highOrder t'
    let ur := fun t' x' => p t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).radialAmp.eval false t' x'
    let uθ := fun t' x' => p t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).polarAmp.eval true t' x'
    ![ur t x, uθ t x,
      (Complex.I / ((n * P.m : ℤ) : ℂ)) *
        (twistedScale P n β ur t x + 2 * ur t x - heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * uθ t' x') t x)]

def modePhase (P : ChartParams) (n : ℤ) (β : ℝ) (y : Space) : ℂ :=
  Complex.exp (Complex.I * (((n * P.m : ℤ) : ℝ) * angleOf y + n * β * logPhase P y : ℝ))

def fieldOf (P : ChartParams) (D : FieldData) (β : ℝ) (y : Space) : Space :=
  ofComponents (fun i => ((decayFactor P y : ℂ) * ∑ n ∈ D.modes, modePhase P n β y *
    (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
      reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
      reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i)).re)

structure IsFieldData (P : ChartParams) (e : ℕ) (D : FieldData) : Prop where
  modes_symm : ∀ n, n ∈ D.modes ↔ -n ∈ D.modes
  amp_conj : ∀ n ∈ D.modes, D.amp (-n) = (D.amp n).conj
  waveRadial : ∀ n ∈ D.modes, n ≠ 0 → IsSplineClass 2 1 false (D.amp n).radialAmp
  wavePolar : ∀ n ∈ D.modes, n ≠ 0 → IsSplineClass 1 2 true (D.amp n).polarAmp
  meanStream : 0 ∈ D.modes → IsSplineClass 2 2 true (D.amp 0).streamAmp ∧ (D.amp 0).streamAmp.IsReal
  meanSwirl : 0 ∈ D.modes → IsSplineClass 1 1 false (D.amp 0).swirlAmp ∧ (D.amp 0).swirlAmp.IsReal
  guard_stream : 0 ∈ D.modes → ∀ j < cellCount (D.amp 0).streamAmp.mesh.xBreaks,
    atFirst 0 ((D.amp 0).streamAmp.piece 0 j) = MvPolynomial.C (D.guardStream : ℂ) * MvPolynomial.X 1
  guard_swirl : 0 ∈ D.modes → ∀ j < cellCount (D.amp 0).swirlAmp.mesh.xBreaks,
    atFirst 0 ((D.amp 0).swirlAmp.piece 0 j) = MvPolynomial.C (D.guardSwirl : ℂ)
  lowOrder_ge : ∀ n ∈ D.modes, n ≠ 0 → 2 ≤ D.lowOrder n
  axisOrder_ge : ∀ n ∈ D.modes, n ≠ 0 → 2 ≤ D.axisOrder n
  orders_conj : ∀ n ∈ D.modes, D.lowOrder (-n) = D.lowOrder n ∧ D.axisOrder (-n) = D.axisOrder n
  highOrder_eq : D.highOrder = e

structure IsCompactFieldData (P : ChartParams) (e : ℕ) (tb : ℝ) (D : FieldData) : Prop where
  field : IsFieldData P e D
  one_le : 1 ≤ e
  tb_lt : tb < 1
  vanish : ∀ n ∈ D.modes, (D.amp n).radialAmp.VanishesFrom tb ∧ (D.amp n).polarAmp.VanishesFrom tb ∧
    (D.amp n).streamAmp.VanishesFrom tb ∧ (D.amp n).swirlAmp.VanishesFrom tb
  tb_break : ∀ n ∈ D.modes, tb ∈ (D.amp n).radialAmp.mesh.tBreaks ∧ tb ∈ (D.amp n).polarAmp.mesh.tBreaks ∧
    tb ∈ (D.amp n).streamAmp.mesh.tBreaks ∧ tb ∈ (D.amp n).swirlAmp.mesh.tBreaks

end GivenFields

end CellCert

end Breakdown

end
end

section

open scoped ContDiff

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

structure ProfileData (k : ℕ) where
  chart : ChartParams
  power : ℝ
  baseRate : ℝ
  rateSlope : Fin k → ℝ
  radius : Fin k → ℝ
  index : Finset (Fin k → ℕ)
  part : (Fin k → ℕ) → FieldData
  multCoef : (Fin k → ℕ) → Fin k → ℝ

namespace ProfileData

variable {k : ℕ} (D : ProfileData k)

def rate (p : Fin k → ℝ) : ℝ := D.baseRate + ∑ j, D.rateSlope j * p j

def phase (p : Fin k → ℝ) : ℝ := -(2 * D.power * (D.chart.m : ℝ) * D.rate p)

def monomialOf (p : Fin k → ℝ) (μ : Fin k → ℕ) : ℝ := ∏ j, p j ^ μ j

def profile (p : Fin k → ℝ) (y : Space) : Space :=
  ∑ μ ∈ D.index, monomialOf p μ • fieldOf D.chart (D.part μ) (D.phase p) y

def multiplier (p : Fin k → ℝ) (j : Fin k) : ℝ :=
  ∑ μ ∈ D.index, monomialOf p μ * D.multCoef μ j

def second (p : Fin k → ℝ) (y : Space) : Space →L[ℝ] Space →L[ℝ] Space :=
  fderiv ℝ (fderiv ℝ (D.profile p)) y

open Classical in
def powerField (p : Fin k → ℝ) : Space → Space :=
  if h : ∃ P, IsWeakFractionalPower D.power (D.profile p) P then h.choose else fun _ => 0

end ProfileData

structure IsProfileData {k : ℕ} (D : ProfileData k) : Prop where
  chart : IsChartParams D.chart
  power_eq : D.power = 1 + D.chart.eps
  radius_nonneg : ∀ j, 0 ≤ D.radius j
  index_zero : (0 : Fin k → ℕ) ∈ D.index
  index_down : ∀ μ ∈ D.index, ∀ ν : Fin k → ℕ, ν ≤ μ → ν ∈ D.index
  parts : ∀ μ ∈ D.index, IsFieldData D.chart 1 (D.part μ)

structure IsProfileInstance {k N : ℕ} (D : ProfileData k) (d : FracCertData k N) : Prop where
  profile_eq : d.profile = D.profile
  second_eq : d.profileSecond = D.second
  power_eq : d.profilePower = D.powerField
  rate_eq : d.rotationRate = D.rate
  radius_eq : d.radius = D.radius
  order_eq : d.order = D.chart.m
  multiplier_eq : d.multiplier = D.multiplier

structure IsCentreInstance {k N : ℕ} (D : ProfileData k) (c : FracCellData k N) : Prop where
  centre_eq : c.centre = D.profile 0
  centreSecond_eq : c.centreSecond = D.second 0
  order_eq : c.order = D.chart.m

end GivenFields

end CellCert

end Breakdown

end
end

section

open MeasureTheory

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

def horizontalNorm (y : Space) : ℝ := Real.sqrt (y 0 ^ 2 + y 1 ^ 2)

def kernelShell (μ M d : ℝ) : ℝ :=
  if 0 < d then min (μ / (4 * Real.pi * d)) ((M / 2) * ((d ^ 3 + 3 * μ / (4 * Real.pi * M)) ^ ((2 : ℝ) / 3) - d ^ 2))
  else (M / 2) * (3 * μ / (4 * Real.pi * M)) ^ ((2 : ℝ) / 3)

def gapDist (aLo : ℝ) (aHi : Option ℝ) (bLo : ℝ) (bHi : Option ℝ) : ℝ :=
  max 0 (max (match bHi with | some h => aLo - h | none => 0) (match aHi with | some h => bLo - h | none => 0))

def sheetArea (l D : ℝ) : ℝ := Real.pi * (D ^ 2 * Real.arsinh (l / D) + l * Real.sqrt (D ^ 2 + l ^ 2))

structure CellSumData where
  pieceCount : ℕ
  pieceRhoLo : Fin pieceCount → ℝ
  pieceRhoHi : Fin pieceCount → Option ℝ
  pieceZLo : Fin pieceCount → ℝ
  pieceZHi : Fin pieceCount → Option ℝ
  pieceSolid : Fin pieceCount → Set Space
  pieceSup : Fin pieceCount → ℝ
  pieceMass : Fin pieceCount → ℝ
  boxCount : ℕ
  boxRhoLo : Fin boxCount → ℝ
  boxRhoHi : Fin boxCount → Option ℝ
  boxZLo : Fin boxCount → ℝ
  boxZHi : Fin boxCount → Option ℝ
  rule : Fin boxCount → Fin pieceCount → Bool → Fin 3
  sectorLength : Fin boxCount → Fin pieceCount → Bool → ℝ
  boxBound : Fin boxCount → ℝ

namespace CellSumData

variable (D : CellSumData) (m : ℕ)

def sectorDist (a : Fin D.boxCount) (b : Fin D.pieceCount) (mirrored : Bool) (i : ℕ) : ℝ :=
  Real.sqrt (gapDist (D.boxRhoLo a) (D.boxRhoHi a) (D.pieceRhoLo b) (D.pieceRhoHi b) ^ 2
    + (if mirrored then D.boxZLo a + D.pieceZLo b
        else gapDist (D.boxZLo a) (D.boxZHi a) (D.pieceZLo b) (D.pieceZHi b)) ^ 2
    + 4 * D.boxRhoLo a * D.pieceRhoLo b * Real.sin (Real.pi * i / m) ^ 2)

def sectorSum (a : Fin D.boxCount) (b : Fin D.pieceCount) (mirrored : Bool) (first : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico first (m / 2), 2 * kernelShell (D.pieceMass b / m) (D.pieceSup b) (D.sectorDist m a b mirrored i)

def sectorConst (a : Fin D.boxCount) (b : Fin D.pieceCount) : ℝ :=
  Real.sqrt (D.boxRhoLo a * D.pieceRhoLo b) * Real.sin (Real.pi / m) / (Real.pi / m)

def nearTerm (a : Fin D.boxCount) (b : Fin D.pieceCount) (mirrored : Bool) : ℝ :=
  let d₀ := D.sectorDist m a b mirrored 0
  let l := D.sectorLength a b mirrored
  let D₁ := Real.sqrt (d₀ ^ 2 + ((D.pieceRhoHi b).getD 0 - D.pieceRhoLo b) * ((D.pieceZHi b).getD 0 - D.pieceZLo b) / Real.pi)
  2 * (D.pieceMass b / m) / (4 * Real.pi * Real.sqrt (d₀ ^ 2 + l ^ 2))
    + D.pieceSup b * (D.pieceRhoHi b).getD 0 * (sheetArea l D₁ - sheetArea l d₀) / (2 * Real.pi * D.sectorConst m a b)

def pairTerm (a : Fin D.boxCount) (b : Fin D.pieceCount) (mirrored : Bool) : ℝ :=
  match D.rule a b mirrored with
  | 0 => D.sectorSum m a b mirrored 0
  | 1 => kernelShell (D.pieceMass b) (D.pieceSup b) (D.sectorDist m a b mirrored 0)
  | _ => D.nearTerm m a b mirrored + D.sectorSum m a b mirrored 1

end CellSumData

end Reduction

end CellCert

end Breakdown

end
end

section

open MeasureTheory

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

def IsWeakNegTraceOf (X L : Space → Space) : Prop :=
  ∀ φ : Space → Space, IsTestVectorField φ →
    ∫ y, inner ℝ (X y) (-sumSecondPartialsAt φ y) = ∫ y, inner ℝ (L y) (φ y)

def IsWeakMatrixDivergenceOf (Y : Space → (Space →L[ℝ] Space)) (D : Space → Space) : Prop :=
  ∀ φ : Space → Space, IsTestVectorField φ →
    ∫ y, entryInner (fderiv ℝ φ y) (Y y) = -∫ y, inner ℝ (D y) (φ y)

def lowPowerNormalizer (ε : ℝ) : ℝ :=
  ∫ z : Space, ‖z‖ ^ (-(3 + 2 * ε)) * (1 - Real.cos (z 0))

def lowPowerAt (ε : ℝ) (f : Space → Space) (x : Space) : Space :=
  (lowPowerNormalizer ε)⁻¹ • ∫ z : Space, ‖z‖ ^ (-(3 + 2 * ε)) • ((1 / 2 : ℝ) • ((2 : ℝ) • f x - f (x + z) - f (x - z)))

def ringPoint (ρ θ z : ℝ) : Space :=
  EuclideanSpace.single 0 (ρ * Real.cos θ) + EuclideanSpace.single 1 (ρ * Real.sin θ) + EuclideanSpace.single 2 z

def horizontalPart (F : Space → Space) (y : Space) : ℂ := (F y 0 : ℂ) + Complex.I * (F y 1 : ℂ)

def verticalPart (F : Space → Space) (y : Space) : ℂ := (F y 2 : ℂ)

def angularMode (u : Space → ℂ) (k : ℤ) (ρ z : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ θ in (-Real.pi)..Real.pi, Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) * u (ringPoint ρ θ z)

def harmonicWeightSqOn (modes : Finset ℤ) (F : Space → Space) : ENNReal :=
  ∑ k ∈ modes, ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ),
    ENNReal.ofReal (2 * Real.pi * q.1 * (q.1 ^ 2 + q.2 ^ 2) *
      (‖angularMode (horizontalPart F) k q.1 q.2‖ ^ 2 / (((|k| : ℤ) : ℝ) + 1 / 2) ^ 2
        + ‖angularMode (verticalPart F) k q.1 q.2‖ ^ 2 / (((|k| : ℤ) : ℝ) + 3 / 2) ^ 2))

def driftAdjointField (α a : ℝ) (ζ : Space → Space) (Dζ : Space → (Space →L[ℝ] Space)) (y : Space) : Space :=
  (1 - 4 * (1 / (2 * α))) • ζ y - (1 / (2 * α)) • Dζ y y - a • (Dζ y (axialTurn y) - axialTurn (ζ y))

def convectionAdjointField (W : Space → Space) (DW : Space → (Space →L[ℝ] Space)) (ζ : Space → Space)
    (Dζ : Space → (Space →L[ℝ] Space)) (y : Space) : Space :=
  -crossVec (curlOf (Dζ y)) (W y) + (2 : ℝ) • ContinuousLinearMap.adjoint (DW y) (ζ y)

structure AdjointDual (k : ℕ) where
  adjointGrad : Space → (Space →L[ℝ] Space)
  adjointSecond : Space → (Space →L[ℝ] Space →L[ℝ] Space)
  sharpTrace : Space → Space
  sharpGrad : Space → (Space →L[ℝ] Space)
  pinPotential : Fin k → Space → Space
  pinSecond : Fin k → Space → (Space →L[ℝ] Space →L[ℝ] Space)
  pinTrace : Fin k → Space → Space
  pinScale : Fin k → ℝ
  pressure : Space → ℝ
  pressureGrad : Space → Space
  dualField : Space → Space
  dualGrad : Space → (Space →L[ℝ] Space)
  dualTrace : Space → Space
  potentialField : Space → Space
  potentialGrad : Space → (Space →L[ℝ] Space)
  potentialTrace : Space → Space
  potentialScale : ℝ
  fluxField : Space → (Space →L[ℝ] Space)
  fluxDiv : Space → Space
  inverseSquarePart : Space → Space
  exactSet : Finset (Fin k)
  shiftField : Fin k → Space → Space
  shiftGrad : Fin k → Space → (Space →L[ℝ] Space)
  dualBound : ℝ
  potentialBound : ℝ
  fluxBound : ℝ
  inverseSquareBound : ℝ
  inverseSquareModes : Finset ℤ
  shiftBound : Fin k → ℝ
  shiftGradBound : Fin k → ℝ

namespace AdjointDual

variable {k : ℕ} (D : AdjointDual k)

def pinDual (l : Fin k) (y : Space) : Space := (1 / D.pinScale l) • D.pinTrace l y

def residualField (α : ℝ) {N : ℕ} (d : FracCertData k N) (j : Fin k) (p : Fin k → ℝ) (y : Space) : Space :=
  driftAdjointField α (d.rotationRate p) (d.adjoint j p) D.adjointGrad y + D.sharpTrace y
    + convectionAdjointField (d.profile p) (d.gradProfile p) (d.adjoint j p) D.adjointGrad y
    - ∑ l, d.adjointPin j p l • D.pinDual l y + D.pressureGrad y

def remainderField (α : ℝ) {N : ℕ} (d : FracCertData k N) (j : Fin k) (p : Fin k → ℝ) (y : Space) : Space :=
  D.residualField α d j p y - D.dualTrace y - D.potentialScale • D.potentialTrace y - D.fluxDiv y

end AdjointDual

end Reduction

end CellCert

end Breakdown

end
end

section

open scoped ContDiff ENNReal

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

def multiPow {k : ℕ} (γ : Fin k → ℕ) (p : Fin k → ℝ) : ℝ := ∏ j, p j ^ γ j

structure FieldFamily (k : ℕ) where
  indices : Finset (Fin k → ℕ)
  coef : (Fin k → ℕ) → FieldData

def FieldFamily.eval {k : ℕ} (P : ChartParams) (F : FieldFamily k) (phase : (Fin k → ℝ) → ℝ)
    (p : Fin k → ℝ) (y : Space) : Space :=
  ∑ γ ∈ F.indices, multiPow γ p • fieldOf P (F.coef γ) (phase p) y

def IsDownClosed {k : ℕ} (S : Finset (Fin k → ℕ)) : Prop :=
  ∀ γ ∈ S, ∀ γ' : Fin k → ℕ, γ' ≤ γ → γ' ∈ S

structure PressureData where
  modes : Finset ℤ
  firstAmp : ℤ → Spline
  secondAmp : ℤ → Spline
  firstLow : ℤ → ℕ
  firstHigh : ℕ
  secondLow : ℤ → ℕ
  secondHigh : ℕ
  axisOrder : ℤ → ℕ

def pressureShape (P : ChartParams) (low high axis : ℕ) (S : Spline) (y : Space) : ℂ :=
  ((chartT P y ^ low * chartS P y ^ high * qOf y ^ axis : ℝ) : ℂ) * S.eval false (chartT P y) (heightRatio y)

def pressureOf (P : ChartParams) (D : PressureData) (β : ℝ) (y : Space) : ℝ :=
  (∑ n ∈ D.modes, (((decayFactor P y : ℝ) : ℂ) * modePhase P n β y * pressureShape P (D.firstLow n) D.firstHigh (D.axisOrder n) (D.firstAmp n) y
    + ((decayFactor P y ^ 2 : ℝ) : ℂ) * modePhase P n β y * pressureShape P (D.secondLow n) D.secondHigh (D.axisOrder n) (D.secondAmp n) y)).re

structure IsPressureData (P : ChartParams) (D : PressureData) : Prop where
  amp_class : ∀ n ∈ D.modes, IsSplineClass 0 0 false (D.firstAmp n) ∧ IsSplineClass 0 0 false (D.secondAmp n)
  conj_closed : ∀ n ∈ D.modes, -n ∈ D.modes
  conj_data : ∀ n ∈ D.modes, D.firstAmp (-n) = (D.firstAmp n).conj ∧ D.secondAmp (-n) = (D.secondAmp n).conj
  high_ge : 2 ≤ D.firstHigh ∧ 2 ≤ D.secondHigh
  low_axis_ge : ∀ n ∈ D.modes, n ≠ 0 → 1 ≤ D.axisOrder n
  orders_conj : ∀ n ∈ D.modes, D.firstLow (-n) = D.firstLow n ∧ D.secondLow (-n) = D.secondLow n ∧
    D.axisOrder (-n) = D.axisOrder n

structure AtomData where
  harmonics : Finset ℕ
  plusAmp : ℕ → Spline
  minusAmp : ℕ → Spline
  heightAmp : ℕ → Spline

def atomLastT (S : Spline) : ℕ := cellCount S.mesh.tBreaks - 1

def atomLastX (S : Spline) : ℕ := cellCount S.mesh.xBreaks - 1

structure IsAtomSpline (odd : Bool) (S : Spline) (harmonic : ℕ) : Prop where
  spline : IsSplineClass 1 1 odd S
  at_origin : ∀ j < cellCount S.mesh.xBreaks, atFirst 0 (S.piece 0 j) = 0
  at_infinity : ∀ j < cellCount S.mesh.xBreaks, atFirst 1 (S.piece (atomLastT S) j) = 0 ∧
    atFirst 1 (tDeriv 1 (S.piece (atomLastT S) j)) = 0
  at_axis : harmonic ≠ 0 → ∀ i < cellCount S.mesh.tBreaks, atSecond 1 (S.piece i (atomLastX S)) = 0

def atomTerm (P : ChartParams) (j : ℕ) (a : ℕ) (M : ℤ) (β : ℝ) (S : Spline) (y : Space) : ℂ :=
  Complex.exp (Complex.I * ((j : ℝ) * β * logPhase P y + (M : ℝ) * angleOf y : ℝ)) *
    ((Real.sqrt (qOf y) ^ a : ℝ) : ℂ) * S.eval (decide (a = 0)) (chartT P y) (heightRatio y)

def atomPlane (P : ChartParams) (X : AtomData) (β : ℝ) (y : Space) : ℂ :=
  ((decayFactor P y : ℝ) : ℂ) *
    ((∑ j ∈ X.harmonics, atomTerm P j 1 ((j : ℤ) * P.m + 1) β (X.plusAmp j) y) +
      ∑ j ∈ X.harmonics.filter (fun j => 1 ≤ j),
        (starRingEnd ℂ) (atomTerm P j 1 ((j : ℤ) * P.m - 1) β (X.minusAmp j) y))

def atomHeight (P : ChartParams) (X : AtomData) (β : ℝ) (y : Space) : ℂ :=
  ((decayFactor P y : ℝ) : ℂ) *
    ∑ j ∈ X.harmonics, ((if j = 0 then 1 else 2 : ℝ) : ℂ) * atomTerm P j 0 ((j : ℤ) * P.m) β (X.heightAmp j) y

def atomOf (P : ChartParams) (X : AtomData) (β : ℝ) (y : Space) : Space :=
  ofComponents ![(atomPlane P X β y).re, (atomPlane P X β y).im, (atomHeight P X β y).re]

structure IsAtomData (P : ChartParams) (X : AtomData) : Prop where
  plus_shape : ∀ j ∈ X.harmonics, IsAtomSpline false (X.plusAmp j) j
  minus_shape : ∀ j ∈ X.harmonics, 1 ≤ j → IsAtomSpline false (X.minusAmp j) j
  height_shape : ∀ j ∈ X.harmonics, IsAtomSpline true (X.heightAmp j) j
  height_zero_real : 0 ∈ X.harmonics → (X.heightAmp 0).IsReal

structure IsRadialContinuous (S : Spline) : Prop where
  mesh : IsTensorMesh S.mesh
  t_joins : ∀ i, 1 ≤ i → i < cellCount S.mesh.tBreaks → ∀ j < cellCount S.mesh.xBreaks,
    atFirst (S.mesh.tBreaks.getD i 0 : ℂ) (S.piece (i - 1) j) = atFirst (S.mesh.tBreaks.getD i 0 : ℂ) (S.piece i j)

structure IsFluxSpline (S : Spline) : Prop where
  continuous : IsRadialContinuous S
  at_infinity : ∀ j < cellCount S.mesh.xBreaks, atFirst 1 (S.piece (atomLastT S) j) = 0 ∧
    atFirst 1 (tDeriv 1 (S.piece (atomLastT S) j)) = 0

def FluxData := AtomData

def fluxOf (P : ChartParams) (F : FluxData) (β : ℝ) (y : Space) : Space →L[ℝ] Space :=
  (innerSL ℝ (ofComponents (radialVec y))).smulRight (atomOf P F β y)

structure IsFluxData (F : FluxData) : Prop where
  plus_shape : ∀ j ∈ F.harmonics, IsFluxSpline (F.plusAmp j)
  minus_shape : ∀ j ∈ F.harmonics, 1 ≤ j → IsFluxSpline (F.minusAmp j)
  height_shape : ∀ j ∈ F.harmonics, IsFluxSpline (F.heightAmp j)
  height_zero_real : 0 ∈ F.harmonics → (F.heightAmp 0).IsReal

structure AtomFamily (k : ℕ) where
  indices : Finset (Fin k → ℕ)
  coef : (Fin k → ℕ) → AtomData

def AtomFamily.eval {k : ℕ} (P : ChartParams) (F : AtomFamily k) (phase : (Fin k → ℝ) → ℝ)
    (p : Fin k → ℝ) (y : Space) : Space :=
  ∑ γ ∈ F.indices, multiPow γ p • atomOf P (F.coef γ) (phase p) y

structure AuxData (k : ℕ) where
  actuatorData : Fin k → FieldData
  pinData : Fin k → FieldData
  pinScale : Fin k → ℝ
  supportBreak : ℝ
  adjointFamily : Fin k → FieldFamily k
  sharpSum : Fin k → AtomFamily k
  sharpLead : Fin k → ℝ
  phaseBase : ℝ
  phaseSlope : Fin k → ℝ
  adjointPressure : Fin k → (Fin k → ℕ) → PressureData
  dualFamily : Fin k → AtomFamily k
  potentialFamily : Fin k → AtomFamily k
  fluxData : Fin k → (Fin k → ℕ) → FluxData

namespace AuxData

variable {k : ℕ} (A : AuxData k)

def phase (p : Fin k → ℝ) : ℝ := A.phaseBase + ∑ j, A.phaseSlope j * p j

def actuatorField (P : ChartParams) (i : Fin k) : Space → Space := fieldOf P (A.actuatorData i) A.phaseBase

def pinPotentialField (P : ChartParams) (l : Fin k) : Space → Space := fieldOf P (A.pinData l) A.phaseBase

def smoothPinField (P : ChartParams) (l : Fin k) (y : Space) : Space →L[ℝ] Space :=
  (A.pinScale l)⁻¹ • fderiv ℝ (A.pinPotentialField P l) y

def adjointField (P : ChartParams) (j : Fin k) (p : Fin k → ℝ) : Space → Space :=
  (A.adjointFamily j).eval P A.phase p

def sharpField (P : ChartParams) (ν : ℝ) (j : Fin k) (p : Fin k → ℝ) (y : Space) : Space :=
  A.sharpLead j • A.adjointField P j p y - (A.sharpSum j).eval P A.phase p y - ν • A.adjointField P j p y

def dualFieldOf (P : ChartParams) (j : Fin k) (p : Fin k → ℝ) : Space → Space :=
  (A.dualFamily j).eval P A.phase p

def potentialFieldOf (P : ChartParams) (j : Fin k) (p : Fin k → ℝ) : Space → Space :=
  (A.potentialFamily j).eval P A.phase p

def fluxFieldOf (P : ChartParams) (j : Fin k) (p : Fin k → ℝ) (y : Space) : Space →L[ℝ] Space :=
  ∑ γ ∈ (A.adjointFamily j).indices, multiPow γ p • fluxOf P (A.fluxData j γ) (A.phase p) y

def adjointPressureField (P : ChartParams) (j : Fin k) (p : Fin k → ℝ) (y : Space) : ℝ :=
  ∑ γ ∈ (A.adjointFamily j).indices, multiPow γ p * pressureOf P (A.adjointPressure j γ) (A.phase p) y

end AuxData

structure IsAuxData (P : ChartParams) {k : ℕ} (A : AuxData k) : Prop where
  break_pos : 0 < A.supportBreak
  break_lt : A.supportBreak < 1
  actuator_shape : ∀ i, ∃ e, IsCompactFieldData P e A.supportBreak (A.actuatorData i)
  pin_shape : ∀ l, ∃ e, IsCompactFieldData P e A.supportBreak (A.pinData l)
  pinScale_pos : ∀ l, 0 < A.pinScale l
  adjoint_down : ∀ j, IsDownClosed (A.adjointFamily j).indices
  adjoint_shape : ∀ j, ∀ γ ∈ (A.adjointFamily j).indices, IsFieldData P 3 ((A.adjointFamily j).coef γ)
  sharp_shape : ∀ j, ∀ γ ∈ (A.sharpSum j).indices, IsAtomData P ((A.sharpSum j).coef γ)
  pressure_shape : ∀ j, ∀ γ ∈ (A.adjointFamily j).indices, IsPressureData P (A.adjointPressure j γ) ∧
    (3 ≤ (A.adjointPressure j γ).secondHigh ∨
      ∀ n ∈ (A.adjointPressure j γ).modes, ∀ x < cellCount ((A.adjointPressure j γ).secondAmp n).mesh.xBreaks,
        ((A.adjointPressure j γ).secondAmp n).piece (cellCount ((A.adjointPressure j γ).secondAmp n).mesh.tBreaks - 1) x = 0)
  dual_shape : ∀ j, ∀ γ ∈ (A.dualFamily j).indices, IsAtomData P ((A.dualFamily j).coef γ)
  potential_shape : ∀ j, ∀ γ ∈ (A.potentialFamily j).indices, IsAtomData P ((A.potentialFamily j).coef γ)
  flux_shape : ∀ j, ∀ γ ∈ (A.adjointFamily j).indices, IsFluxData (A.fluxData j γ)

structure IsAuxInstance {k N : ℕ} (D : ProfileData k) (A : AuxData k) (c : FracCellData k N) : Prop where
  phaseBase_eq : A.phaseBase = D.phase 0
  phaseSlope_eq : ∀ j, A.phaseSlope j = -(2 * D.power * (D.chart.m : ℝ) * D.rateSlope j)
  actuator_eq : ∀ i, c.actuator i = A.actuatorField D.chart i
  actuatorGrad_eq : ∀ i, c.actuatorGrad i = fun y => fderiv ℝ (A.actuatorField D.chart i) y
  smoothPin_eq : ∀ l, c.smoothPin l = A.smoothPinField D.chart l
  adjoint_eq : ∀ j p, c.adjoint j p = A.adjointField D.chart j p
  adjointSharp_eq : ∀ j p, c.adjointSharp j p = A.sharpField D.chart c.splitVisc j p

def amplitudeFieldAt {k : ℕ} (D : ProfileData k) (i : Fin k) (p : Fin k → ℝ) (y : Space) : Space :=
  fieldOf D.chart (D.part (Pi.single i 1)) (D.phase p) y

def inverseSquarePartOf (α : ℝ) {k N : ℕ} (D : ProfileData k) (d : FracCertData k N) (j : Fin k)
    (p : Fin k → ℝ) (Dd : Reduction.AdjointDual k) (y : Space) : Space :=
  Dd.remainderField α d j p y -
    ∑ i ∈ Finset.univ \ Dd.exactSet, p i • Reduction.convectionAdjointField (amplitudeFieldAt D i p)
      (fun z => fderiv ℝ (amplitudeFieldAt D i p) z) (d.adjoint j p) Dd.adjointGrad y

end GivenFields

end CellCert

end Breakdown

end
end

section

open MeasureTheory Polynomial

open scoped Interval

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

def evenSeries (μ : ℝ) (p : ℝ[X]) : ℝ[X] :=
  ∑ i ∈ Finset.range (p.natDegree + 1), (μ ^ i)⁻¹ • (derivative^[2 * i] p)

def intervalSmoothed (μ : ℝ) (p : ℝ[X]) (x : ℝ) : ℝ :=
  p.eval x - (evenSeries μ p).eval x
    + ((evenSeries μ p).eval 1 + (evenSeries μ p).eval (-1)) / (2 * Real.cosh (Real.sqrt μ))
      * Real.cosh (Real.sqrt μ * x)
    + ((evenSeries μ p).eval 1 - (evenSeries μ p).eval (-1)) / (2 * Real.sinh (Real.sqrt μ))
      * Real.sinh (Real.sqrt μ * x)

def IntervalCertificate (q : ℕ) (μ v : ℝ) : Prop :=
  0 < μ ∧ ∀ p : ℝ[X], p.natDegree ≤ q →
    (∫ x in (-1 : ℝ)..1, intervalSmoothed μ p x * p.eval x) ≤ v * ∫ x in (-1 : ℝ)..1, p.eval x ^ 2

def axisFunctional (i : ℕ) (χ : ℝ → ℝ) (μ : ℝ) (p : ℝ[X]) : ℝ :=
  ∫ r in (0 : ℝ)..1, ((1 - χ r) ^ 2 * p.eval r ^ 2
    + μ⁻¹ * (deriv (fun s => χ s * p.eval s) r ^ 2 + (i : ℝ) ^ 2 * χ r ^ 2 * p.eval r ^ 2 / r ^ 2)) * r

def AxisCertificate (q : ℕ) (μ v : ℝ) (χ : ℝ → ℝ) : Prop :=
  0 < μ ∧ χ 1 = 0 ∧ (∃ K, LipschitzWith K χ) ∧
    ∀ i : ℕ, i ≤ 1 → ∀ p : ℝ[X], p.natDegree ≤ q → (i = 1 → X ∣ p) →
      axisFunctional i χ μ p ≤ v * ∫ r in (0 : ℝ)..1, p.eval r ^ 2 * r

def AxisGradientBound (q : ℕ) (M : ℝ) : Prop :=
  ∀ i : ℕ, i ≤ 1 → ∀ p : ℝ[X], p.natDegree ≤ q → (i = 1 → X ∣ p) →
    (∫ r in (0 : ℝ)..1, ((derivative p).eval r ^ 2 + (i : ℝ) ^ 2 * p.eval r ^ 2 / r ^ 2) * r)
      ≤ M * ∫ r in (0 : ℝ)..1, p.eval r ^ 2 * r

def certMin (S : Finset (ℝ × ℝ)) (μ : ℝ) : ℝ :=
  sInf (insert 1 {v | ∃ ν, (ν, v) ∈ S ∧ ν ≤ μ})

def intervalClosed (q : ℕ) (μ : ℝ) : ℝ :=
  4 / Real.sqrt 3 * ((q : ℝ) + 1) ^ 2 * μ ^ (-(1 / 2 : ℝ)) + (1 / 2) * ((q : ℝ) + 1) ^ 4 * μ⁻¹

def axisClosed (q : ℕ) (M μ : ℝ) : ℝ :=
  8 * Real.sqrt 6 / 3 * ((q : ℝ) + 1) ^ 2 * μ ^ (-(1 / 2 : ℝ)) + 2 * M * μ⁻¹

structure CellBlock where
  innerRadius : ℝ
  outerRadius : ℝ
  lowerHeight : ℝ
  upperHeight : ℝ
  degree : ℕ
  mode : ℕ
  onAxis : Bool

structure SpectralData where
  block : ℕ → CellBlock
  intervalCerts : ℕ → Finset (ℝ × ℝ)
  axisCerts : ℕ → Finset (ℝ × ℝ)
  axisCutoff : ℕ → ℝ × ℝ → ℝ → ℝ
  axisGradient : ℕ → ℝ

namespace SpectralData

variable (sd : SpectralData)

def intervalUpper (q : ℕ) (μ : ℝ) : ℝ := min (certMin (sd.intervalCerts q) μ) (intervalClosed q μ)

def axisUpper (q : ℕ) (μ : ℝ) : ℝ :=
  min (certMin (sd.axisCerts q) μ) (if 24 ≤ μ then axisClosed q (sd.axisGradient q) μ else 1)

def blockSpectral (β : ℕ) (lam : ℝ) : ℝ :=
  if (sd.block β).onAxis then
    min 1 (sd.axisUpper (sd.block β).degree (lam * ((sd.block β).outerRadius - (sd.block β).innerRadius) ^ 2)
      + sd.intervalUpper (sd.block β).degree
          (lam * ((sd.block β).upperHeight - (sd.block β).lowerHeight) ^ 2 / 4))
  else
    min 1 ((sd.block β).outerRadius / (sd.block β).innerRadius
      * (sd.intervalUpper (sd.block β).degree
            (lam * ((sd.block β).outerRadius - (sd.block β).innerRadius) ^ 2 / 4)
        + sd.intervalUpper (sd.block β).degree
            (lam * ((sd.block β).upperHeight - (sd.block β).lowerHeight) ^ 2 / 4)
        + ratioFn lam (((sd.block β).mode + 1 : ℝ) ^ 2 / (sd.block β).innerRadius ^ 2)))

def tailFormula (Λ : ℝ) (β : ℕ) : ℝ :=
  if (sd.block β).onAxis then
    ((sd.block β).degree + 1 : ℝ) ^ 2 * (8 * Real.sqrt 6 / 3 / ((sd.block β).outerRadius - (sd.block β).innerRadius)
        + 8 / Real.sqrt 3 / ((sd.block β).upperHeight - (sd.block β).lowerHeight))
      + Λ ^ (-(1 / 2 : ℝ)) * (2 * sd.axisGradient (sd.block β).degree
          / ((sd.block β).outerRadius - (sd.block β).innerRadius) ^ 2
        + 2 * ((sd.block β).degree + 1 : ℝ) ^ 4 / ((sd.block β).upperHeight - (sd.block β).lowerHeight) ^ 2)
  else
    (sd.block β).outerRadius / (sd.block β).innerRadius
      * (8 / Real.sqrt 3 * ((sd.block β).degree + 1 : ℝ) ^ 2
          * (1 / ((sd.block β).outerRadius - (sd.block β).innerRadius)
            + 1 / ((sd.block β).upperHeight - (sd.block β).lowerHeight))
        + Λ ^ (-(1 / 2 : ℝ)) * (2 * ((sd.block β).degree + 1 : ℝ) ^ 4
            * (1 / ((sd.block β).outerRadius - (sd.block β).innerRadius) ^ 2
              + 1 / ((sd.block β).upperHeight - (sd.block β).lowerHeight) ^ 2)
          + ((sd.block β).mode + 1 : ℝ) ^ 2 / (sd.block β).innerRadius ^ 2))

end SpectralData

def radialCoord (y : Space) : ℝ := Real.sqrt (y 0 ^ 2 + y 1 ^ 2)

def cellSolid (g : CellBlock) (s : Fin 2) : Set Space :=
  {y | g.innerRadius ≤ radialCoord y ∧ radialCoord y ≤ g.outerRadius ∧
    g.lowerHeight ≤ (if s = 0 then y 2 else -y 2) ∧ (if s = 0 then y 2 else -y 2) ≤ g.upperHeight}

end Spectral

end CellCert

end Breakdown

end
end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenModel

open SteadyCert CellAnalysis

structure CellMesh where
  cellCount : ℕ
  box : Fin cellCount → CellBox
  outerSize : ℝ

namespace CellMesh

variable (M : CellMesh)

def region : Set Space := ⋃ K, (M.box K).solid

def piece (K : Fin M.cellCount) : Set Space :=
  (M.box K).solid \ ⋃ K' ∈ Finset.univ.filter (fun K' => K' < K), (M.box K').solid

def piecewise {E : Type*} [AddCommMonoid E] (f : Fin M.cellCount → Space → E) (y : Space) : E :=
  ∑ K, Set.indicator (M.piece K) (f K) y

end CellMesh

structure IsCellMesh (M : CellMesh) : Prop where
  boxes : ∀ K, IsCellBox (M.box K)
  outerSize_pos : 0 < M.outerSize
  boxes_inside : ∀ K, (M.box K).r₂ ≤ M.outerSize ∧ (M.box K).z₂ ≤ M.outerSize
  interiors_disjoint : ∀ K K', K ≠ K' →
    (M.box K).r₂ ≤ (M.box K').r₁ ∨ (M.box K').r₂ ≤ (M.box K).r₁ ∨
      (M.box K).z₂ ≤ (M.box K').z₁ ∨ (M.box K').z₂ ≤ (M.box K).z₁
  boxes_cover : ∀ p : ℝ × ℝ, 0 ≤ p.1 → p.1 ≤ M.outerSize → 0 ≤ p.2 → p.2 ≤ M.outerSize →
    ∃ K, p ∈ (M.box K).rect

def CellPoly (d : ℕ) : Type := Fin (d + 1) → Fin (d + 1) → ℂ

def evalPoly {d : ℕ} (P : CellPoly d) (r z : ℝ) : ℂ :=
  ∑ j, ∑ l, P j l * ((r : ℂ) ^ (j : ℕ)) * ((z : ℂ) ^ (l : ℕ))

def harmonicValue (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → CellPoly d) (y : Space) : ℝ :=
  (∑ β : Fin (J + 1), (((if (β : ℕ) = 0 then (1 : ℝ) else 2) : ℝ) : ℂ) * evalPoly (P β) (cylRadius y) |cylHeight y| *
    Complex.exp ((azimuth m (β : ℤ) * cylAngle y : ℝ) * Complex.I)).re

def vectorSign (y : Space) (a : Fin 3) : ℝ := if cylHeight y < 0 ∧ a = 2 then -1 else 1

def pseudoSign (y : Space) (a : Fin 3) : ℝ := if cylHeight y < 0 then -vectorSign y a else 1

def vectorOf (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → CellPoly d) (y : Space) : Space :=
  cartOfFrame (cylAngle y) (fun a => vectorSign y a * harmonicValue m (fun β => P β a) y)

def pseudoOf (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → CellPoly d) (y : Space) : Space :=
  cartOfFrame (cylAngle y) (fun a => pseudoSign y a * harmonicValue m (fun β => P β a) y)

def tensorOf (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d) (y : Space) : Space →L[ℝ] Space :=
  cartOpOfFrame (cylAngle y) (fun a b => vectorSign y a * vectorSign y b * harmonicValue m (fun β => P β a b) y)

def pseudoTensorOf (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d) (y : Space) :
    Space →L[ℝ] Space :=
  cartOpOfFrame (cylAngle y) (fun a b => pseudoSign y a * vectorSign y b * harmonicValue m (fun β => P β a b) y)

structure ModelData (M : CellMesh) (k : ℕ) where
  degree : ℕ
  columnDegree : ℕ
  harmonicCount : ℕ
  harmonicsOf : Fin M.cellCount → ℕ
  velocity : Fin M.cellCount → Fin (harmonicCount + 1) → Fin 3 → CellPoly degree
  curl : Fin M.cellCount → Fin (harmonicCount + 1) → Fin 3 → CellPoly degree
  strain : Fin M.cellCount → Fin (harmonicCount + 1) → Fin 3 → Fin 3 → CellPoly degree
  curlGrad : Fin M.cellCount → Fin (harmonicCount + 1) → Fin 3 → Fin 3 → CellPoly degree
  actuator : Fin k → Fin M.cellCount → Fin (harmonicCount + 1) → Fin 3 → CellPoly columnDegree
  actuatorGrad : Fin k → Fin M.cellCount → Fin (harmonicCount + 1) → Fin 3 → Fin 3 → CellPoly columnDegree
  pinField : Fin k → Fin M.cellCount → Fin (harmonicCount + 1) → Fin 3 → Fin 3 → CellPoly columnDegree
  pin : Fin k → Fin M.cellCount → Fin (harmonicCount + 1) → Fin 3 → Fin 3 → CellPoly columnDegree

structure IsModelData {M : CellMesh} {k : ℕ} (D : ModelData M k) : Prop where
  strain_symm : ∀ K β a b, D.strain K β a b = D.strain K β b a
  curlGrad_traceFree : ∀ K β, ∀ j l, ∑ a : Fin 3, D.curlGrad K β a a j l = 0
  harmonics_le : ∀ K, D.harmonicsOf K ≤ D.harmonicCount
  zero_above : ∀ K (β : Fin (D.harmonicCount + 1)), D.harmonicsOf K < (β : ℕ) →
    (∀ a i j, D.velocity K β a i j = 0) ∧ (∀ a i j, D.curl K β a i j = 0) ∧
      (∀ a b i j, D.strain K β a b i j = 0) ∧ (∀ a b i j, D.curlGrad K β a b i j = 0)

namespace ModelData

variable {M : CellMesh} {k : ℕ} (D : ModelData M k) (m : ℕ)

def velocityField : Space → Space := M.piecewise (fun K => vectorOf m (D.velocity K))

def curlField : Space → Space := M.piecewise (fun K => pseudoOf m (D.curl K))

def strainField (centreGrad : Space → (Space →L[ℝ] Space)) (y : Space) : Space →L[ℝ] Space :=
  M.piecewise (fun K => tensorOf m (D.strain K)) y + Set.indicator M.regionᶜ (fun z => symPart (centreGrad z)) y

def curlGradField (centreSecond : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (y : Space) : Space →L[ℝ] Space :=
  M.piecewise (fun K => pseudoTensorOf m (D.curlGrad K)) y
    + Set.indicator M.regionᶜ (fun z => curlGradMatrix (centreSecond z)) y

def actuatorField (i : Fin k) : Space → Space := M.piecewise (fun K => vectorOf m (D.actuator i K))

def actuatorGradField (i : Fin k) : Space → (Space →L[ℝ] Space) :=
  M.piecewise (fun K => tensorOf m (D.actuatorGrad i K))

def pinFieldField (i : Fin k) : Space → (Space →L[ℝ] Space) := M.piecewise (fun K => tensorOf m (D.pinField i K))

def pinValueField (i : Fin k) : Space → (Space →L[ℝ] Space) := M.piecewise (fun K => tensorOf m (D.pin i K))

end ModelData

structure IsModelInstance {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (D : ModelData M k) : Prop where
  region_eq : c.cellRegion = M.region
  velocity_eq : c.modelVelocity = D.velocityField c.order
  curl_eq : c.modelCurl = D.curlField c.order
  strain_eq : c.modelStrain = D.strainField c.order c.centreGrad
  curlGrad_eq : c.modelCurlGrad = D.curlGradField c.order c.centreSecond
  actuator_eq : ∀ i, c.modelActuator i = D.actuatorField c.order i
  actuatorGrad_eq : ∀ i, c.modelActuatorGrad i = D.actuatorGradField c.order i
  pinField_eq : ∀ i, c.modelPinField i = D.pinFieldField c.order i
  pin_eq : ∀ i, c.pin i = D.pinValueField c.order i

end GivenModel

namespace GivenModel

open SteadyCert CellAnalysis

def polyDr {d : ℕ} (P : CellPoly d) (r z : ℝ) : ℂ :=
  ∑ j, ∑ l, P j l * ((j : ℕ) : ℂ) * ((r : ℂ) ^ ((j : ℕ) - 1)) * ((z : ℂ) ^ (l : ℕ))

def polyDz {d : ℕ} (P : CellPoly d) (r z : ℝ) : ℂ :=
  ∑ j, ∑ l, P j l * ((r : ℂ) ^ (j : ℕ)) * ((l : ℕ) : ℂ) * ((z : ℂ) ^ ((l : ℕ) - 1))

def IsSolenoidalProfile {d : ℕ} (k : ℝ) (Φ : Fin 3 → CellPoly d) : Prop :=
  ∀ r z : ℝ, (r : ℂ) * polyDr (Φ 0) r z + evalPoly (Φ 0) r z + Complex.I * (k : ℂ) * evalPoly (Φ 1) r z
    + (r : ℂ) * polyDz (Φ 2) r z = 0

structure RowData (M : CellMesh) (N : ℕ) where
  degree : ℕ
  cell : Fin N → Fin M.cellCount
  harmonic : Fin N → ℕ
  profile : Fin N → Fin 3 → CellPoly degree
  cellWeight : Fin M.cellCount → ℝ
  partner : Fin N → Fin N
  positive : Fin N → Bool

namespace RowData

variable {M : CellMesh} {N : ℕ} (R : RowData M N) (m : ℕ)

def testField (a : Fin N) (y : Space) : Space :=
  Set.indicator (M.box (R.cell a)).solid
    (fun z => cartOfFrame (cylAngle z) (fun c => vectorSign z c *
      (evalPoly (R.profile a c) (cylRadius z) |cylHeight z| *
        Complex.exp ((azimuth m (R.harmonic a : ℤ) * cylAngle z : ℝ) * Complex.I)).re)) y

def modePairDensity (zeroMode : Prop) [Decidable zeroMode] (A B : Fin 3 → ℂ) : ℝ :=
  if zeroMode then ∑ c : Fin 3, (A c).re * (B c).re else (1 / 2 : ℝ) * ∑ c : Fin 3, (A c * (starRingEnd ℂ) (B c)).re

open Classical in
def testPairing : Matrix (Fin N) (Fin N) ℝ := fun a b =>
  if R.cell a = R.cell b ∧ R.harmonic a = R.harmonic b then
    2 * (2 * Real.pi) * ∫ p in (M.box (R.cell a)).rect, p.1 *
      modePairDensity (R.harmonic a = 0) (fun c => evalPoly (R.profile a c) p.1 p.2)
        (fun c => evalPoly (R.profile b c) p.1 p.2)
  else 0

open Classical in
def mix : Matrix (Fin N) (Fin N) ℝ :=
  if h : R.testPairing.IsHermitian then h.cfc (fun x => Real.sqrt x⁻¹) else 0

def rowField (a : Fin N) (y : Space) : Space := ∑ b, R.mix a b • R.testField m b y

def rowWeightOf (a : Fin N) : ℝ := R.cellWeight (R.cell a)

end RowData

structure IsRowData {M : CellMesh} {N : ℕ} (R : RowData M N) (m : ℕ) (rowMax : ℝ) : Prop where
  pairing_posDef : R.testPairing.PosDef
  profile_solenoidal : ∀ a, IsSolenoidalProfile (azimuth m (R.harmonic a : ℤ)) (R.profile a)
  cellWeight_pos : ∀ K, 0 < R.cellWeight K
  cellWeight_le : ∀ K, R.cellWeight K ≤ rowMax
  axis_zeroMode : ∀ a, (M.box (R.cell a)).r₁ = 0 → R.harmonic a = 0
  axis_regular : ∀ a, (M.box (R.cell a)).r₁ = 0 → ∀ l, R.profile a 0 0 l = 0 ∧ R.profile a 1 0 l = 0
  normal_degree : ∀ a (j : Fin (R.degree + 1)), R.profile a 0 j (Fin.last R.degree) = 0 ∧ R.profile a 2 (Fin.last R.degree) j = 0
  partner_invol : ∀ a, R.partner (R.partner a) = a
  partner_cell : ∀ a, R.cell (R.partner a) = R.cell a
  partner_harmonic : ∀ a, R.harmonic (R.partner a) = R.harmonic a
  partner_zero : ∀ a, R.harmonic a = 0 → R.partner a = a
  partner_sign : ∀ a, R.harmonic a ≠ 0 → R.positive (R.partner a) = !R.positive a
  partner_profile : ∀ a, R.harmonic a ≠ 0 → R.positive a = true →
    ∀ c j l, R.profile (R.partner a) c j l = Complex.I * R.profile a c j l

def cellWeightField (M : CellMesh) (τ : Fin M.cellCount → ℝ) : Space → ℝ := M.piecewise (fun K _ => τ K)

structure IsRowInstance {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (R : RowData M N) : Prop where
  region_eq : c.cellRegion = M.region
  row_eq : c.row = R.rowField c.order
  rowWeight_eq : c.rowWeight = R.rowWeightOf
  cellWeight_eq : c.cellWeight = cellWeightField M R.cellWeight

def boxRadius (L : ℝ) (y : Space) : ℝ :=
  if max (cylRadius y) |cylHeight y| = 0 then L else L * ‖y‖ / max (cylRadius y) |cylHeight y|

end GivenModel

namespace GivenModel

open SteadyCert CellAnalysis CellFormula

structure IsRowsInstance {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) : Prop where
  region_eq : c.cellRegion = M.region
  row_eq : c.row = RD.rowField c.order
  rowSet_eq : ∀ a, a ∈ R.rowSet ↔ RD.cell a = K₀
  rowModeOf_eq : ∀ a ∈ R.rowSet, R.rowModeOf a = (RD.harmonic a : ℤ)
  rowModes_cover : ∀ a ∈ R.rowSet, (RD.harmonic a : ℤ) ∈ R.rowModes ∧ -(RD.harmonic a : ℤ) ∈ R.rowModes

def rowBlock (M : CellMesh) {N : ℕ} (RD : RowData M N) (m : ℕ) (a : Fin N) : Spectral.CellBlock where
  innerRadius := (M.box (RD.cell a)).r₁
  outerRadius := (M.box (RD.cell a)).r₂
  lowerHeight := (M.box (RD.cell a)).z₁
  upperHeight := (M.box (RD.cell a)).z₂
  degree := RD.degree
  mode := m * RD.harmonic a
  onAxis := decide ((M.box (RD.cell a)).r₁ = 0)

end GivenModel

end CellCert

end Breakdown

end
end

section

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open GivenModel

structure IsGivenData {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (R : RowData M N) : Prop where
  profile : IsProfileData D
  profile_instance : IsProfileInstance D c.toFracCertData
  centre_instance : IsCentreInstance D c
  aux : IsAuxData D.chart A
  aux_instance : IsAuxInstance D A c
  mesh : IsCellMesh M
  model : IsModelData MD
  model_instance : IsModelInstance c M MD
  rows : IsRowData R c.order c.rowMax
  rows_instance : IsRowInstance c M R

end GivenFields

end CellCert

end Breakdown

end
end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert Assembly CellAnalysis

def polyPair (w : ℝ → ℝ) (a b : ℝ) (P Q : Polynomial ℝ) : ℝ :=
  ∫ x in Set.Icc a b, w x * P.eval x * Q.eval x

def orthoFamily (w : ℝ → ℝ) (a b : ℝ) : ℕ → Polynomial ℝ
  | n =>
    let q : Polynomial ℝ := Polynomial.X ^ n -
      ∑ i : Fin n, polyPair w a b (Polynomial.X ^ n) (orthoFamily w a b i) • orthoFamily w a b i
    (Real.sqrt (polyPair w a b q q))⁻¹ • q
termination_by n => n
decreasing_by all_goals simp_wf

def canonicalBases (K : CellBox) : CellBases where
  radialCoef := fun j i => (orthoFamily K.lineWeight K.r₁ K.r₂ j).coeff i
  heightCoef := fun l i => (orthoFamily (fun _ => 1) K.z₁ K.z₂ l).coeff i

open Classical in
def extendBases (K : CellBox) (D : ℕ) (B₀ : CellBases) : CellBases where
  radialCoef := fun j i => if j ≤ D then B₀.radialCoef j i else (canonicalBases K).radialCoef j i
  heightCoef := fun l i => if l ≤ D then B₀.heightCoef l i else (canonicalBases K).heightCoef l i

structure IsGivenBases (K : CellBox) (D : ℕ) (B₀ : CellBases) : Prop where
  radial_leading : ∀ j ≤ D, 0 < B₀.radialCoef j j
  height_leading : ∀ l ≤ D, 0 < B₀.heightCoef l l
  radial_orthonormal : ∀ j ≤ D, ∀ j' ≤ D,
    ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * B₀.radialPoly j r * B₀.radialPoly j' r = if j = j' then 1 else 0
  height_orthonormal : ∀ l ≤ D, ∀ l' ≤ D,
    ∫ z in Set.Icc K.z₁ K.z₂, B₀.heightPoly l z * B₀.heightPoly l' z = if l = l' then 1 else 0

def angularConst (K : CellBox) : ℝ := CellBox.angularWeight K 1

structure WeightData where
  J : ℕ
  JB : ℕ
  JC : ℕ
  energy : ℝ
  vorticity : ℝ
  shift : ℝ
  resolvedCurl : ℝ
  resolvedStrain : ℝ
  resolvedVelocity : ℝ
  curlBand : ℝ
  curlOut : ℝ
  strainBase : ℝ
  strainQuad : ℝ
  meanConst : ℝ
  waveConst : ℝ
  lamMax : ℝ
  weightMax : ℝ
  rLo : ℝ
  rHi : ℝ

namespace WeightData

variable (W : WeightData)

def kEff (m : ℕ) (n : ℤ) : ℝ :=
  if n.natAbs ≤ max (W.J + W.JB) W.JC then modeNumber m n else ((W.J + W.JB + 1 : ℕ) : ℝ) * m

def strainAt (K : CellBox) (S : CellScalars) (k : ℝ) (isBand : Bool) : ℝ :=
  W.strainBase + W.rHi * (if isBand then 0 else S.penaltyStrain)
    + 2 * W.meanConst * W.rHi * K.r₂ / (k - 1)
    + (W.strainQuad + W.rHi * (if isBand then 0 else S.penaltyVelocity)) * K.r₂ ^ 2 / (k - 1) ^ 2

def symAt (K : CellBox) (S : CellScalars) (j l : ℕ) (k : ℝ) (isBand : Bool) : ℝ :=
  W.energy * (CellScalars.tailLam K j l + angularConst K * (max (k - 2) 0) ^ 2)
    - W.strainAt K S k isBand

def antiAt (K : CellBox) (S : CellScalars) (j l : ℕ) (k : ℝ) (isBand : Bool) : ℝ :=
  (W.energy + 2 * W.vorticity) * (CellScalars.tailLam K j l + angularConst K * (max (k - 1) 0) ^ 2)
    - 2 * (if isBand then W.curlBand else W.curlOut) - W.strainAt K S k isBand

end WeightData

structure IsWeightForm {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (W : WeightData) : Prop where
  resolved_eq : S.resolved = Finset.Icc (-(W.J : ℤ)) W.J
  band_eq : S.band = Finset.Icc (-((W.J + W.JB : ℕ) : ℤ)) ((W.J + W.JB : ℕ) : ℤ) \ Finset.Icc (-(W.J : ℤ)) W.J
  energy_form : ∀ n, S.energyWeight n = W.energy
  vorticity_form : ∀ n, S.vorticityWeight n = W.vorticity
  shift_form : ∀ n, S.tailShift n = if n ∈ S.resolved then W.shift else 0
  curl_form : ∀ n, S.curlAbsorb n =
    if n ∈ S.resolved then W.resolvedCurl else if n ∈ S.band then W.curlBand else W.curlOut
  strain_form : ∀ n, S.strainAbsorb n =
    if n ∈ S.resolved then W.resolvedStrain else W.strainAt K S (W.kEff c.order n) (decide (n ∈ S.band))
  velocity_form : ∀ n, S.velocityAbsorb n = if n ∈ S.resolved then W.resolvedVelocity else 0
  sym_form : ∀ n j l, S.symWeight n j l = S.energyWeight n * (CellScalars.tailLam K j l
    + CellBox.angularWeight K n * (max (modeNumber c.order n - 2) 0) ^ 2) - S.strainAbsorb n - S.tailShift n
  anti_form : ∀ n j l, S.antiWeight n j l = (S.energyWeight n + 2 * S.vorticityWeight n) * (CellScalars.tailLam K j l
    + CellBox.angularWeight K n * (max (modeNumber c.order n - 1) 0) ^ 2)
    - 2 * S.curlAbsorb n - S.strainAbsorb n - S.tailShift n
  vel_form : ∀ n j l, S.velWeight n j l =
    S.tailShift n * (if S.degHigh ≤ j then radialEigen K j else heightEigen K l) - S.velocityAbsorb n

structure IsWeightTests (α : ℝ) {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (W : WeightData) :
    Prop where
  order_ge : 3 ≤ c.order
  energy_pos : 0 < W.energy
  energy_le : W.energy ≤ c.innerWeight - c.coercivity
  vorticity_nonneg : 0 ≤ W.vorticity
  vorticity_le : W.vorticity ≤ c.splitVisc - c.innerWeight
  shift_nonneg : 0 ≤ W.shift
  floor_pos : 0 < S.weightFloor
  range_pos : 0 ≤ W.rLo
  range_spec : ∀ p ∈ K.rect, p.1 ≠ 0 → W.rLo ≤ CellScalars.rHat K p ∧ CellScalars.rHat K p ≤ W.rHi
  mean_le : ∀ p ∈ K.rect, Exterior.traceFreeConst * S.meanGradBound p ≤ 2 * W.meanConst
  wave_le : ∀ p ∈ K.rect, Exterior.traceFreeConst * S.waveGradBound p ≤ 2 * W.waveConst
  lam_le : ∀ p ∈ K.rect, S.strainBound p ≤ W.lamMax
  weight_le : ∀ p ∈ K.rect, CellScalars.sampleWeight c p ≤ W.weightMax
  splitLength_pos : 0 < S.splitLength
  consts_nonneg : 0 ≤ W.meanConst ∧ 0 ≤ W.waveConst ∧ 0 ≤ c.coercivity
  penalties_nonneg : 0 ≤ S.penaltyStrain ∧ 0 ≤ S.penaltyCurl ∧ 0 ≤ S.penaltyVelocity
  curl_band_ge : max (W.rLo * (W.lamMax - (1 - 3 / (4 * α) - c.curlWeight)))
      (W.rHi * (W.lamMax - (1 - 3 / (4 * α) - c.curlWeight))) ≤ W.curlBand
  curl_out_ge : max (W.rLo * (W.lamMax + S.penaltyCurl - (1 - 3 / (4 * α) - c.curlWeight)))
      (W.rHi * (W.lamMax + S.penaltyCurl - (1 - 3 / (4 * α) - c.curlWeight))) ≤ W.curlOut
  strain_base_ge : max (W.rLo * (W.waveConst * S.splitLength - (c.curlWeight - c.coercivity * W.weightMax)))
      (W.rHi * (W.waveConst * S.splitLength - (c.curlWeight - c.coercivity * W.weightMax))) ≤ W.strainBase
  strain_quad_ge : W.rHi * W.waveConst / S.splitLength ≤ W.strainQuad
  sym_resolved_radial : S.weightFloor ≤ W.energy * CellScalars.tailLam K (S.degHigh + 1) 0 - W.resolvedStrain - W.shift
  sym_resolved_height : S.weightFloor ≤ W.energy * CellScalars.tailLam K 0 (S.degHigh + 1) - W.resolvedStrain - W.shift
  anti_resolved_radial : S.weightFloor ≤
    (W.energy + 2 * W.vorticity) * CellScalars.tailLam K (S.degHigh + 1) 0 - 2 * W.resolvedCurl - W.resolvedStrain - W.shift
  anti_resolved_height : S.weightFloor ≤
    (W.energy + 2 * W.vorticity) * CellScalars.tailLam K 0 (S.degHigh + 1) - 2 * W.resolvedCurl - W.resolvedStrain - W.shift
  sym_band : S.weightFloor ≤ W.symAt K S 0 0 (((W.J + 1 : ℕ) : ℝ) * c.order) true
  sym_out : S.weightFloor ≤ W.symAt K S 0 0 (((W.J + W.JB + 1 : ℕ) : ℝ) * c.order) false
  anti_band : S.weightFloor ≤ W.antiAt K S 0 0 (((W.J + 1 : ℕ) : ℝ) * c.order) true
  anti_out : S.weightFloor ≤ W.antiAt K S 0 0 (((W.J + W.JB + 1 : ℕ) : ℝ) * c.order) false
  vel_radial : S.weightFloor ≤ W.shift * radialEigen K S.degHigh - W.resolvedVelocity
  vel_height : S.weightFloor ≤ W.shift * heightEigen K S.degHigh - W.resolvedVelocity

def strainScalarMatrix (a : ℝ) : Matrix (Fin 12) (Fin 12) ℂ :=
  Matrix.diagonal (fun i => if i.val < 9 then (a : ℂ) else 0)

structure IsResolvedTests (α : ℝ) {k N : ℕ} (c : FracCellData k N) (S : CellScalars) (W : WeightData)
    (aS lowConst : ℝ) : Prop where
  local_form : ∀ n ∈ S.resolved, ∀ p, S.localMatrix n p = strainScalarMatrix aS
  lowConst_pos : 0 < lowConst
  curl_coef_nonneg : 0 ≤ 1 - 3 / (4 * α) - c.curlWeight
  strain_scalar_le : aS ≤ c.curlWeight - c.coercivity * W.weightMax
  resolved_curl_ge : max (W.rLo * W.lamMax) (W.rHi * W.lamMax) ≤ W.resolvedCurl
  resolved_strain_ge : max (W.rLo * (W.waveConst * S.splitLength + W.meanConst * lowConst - aS))
      (W.rHi * (W.waveConst * S.splitLength + W.meanConst * lowConst - aS)) ≤ W.resolvedStrain
  resolved_velocity_ge : W.rHi * (W.waveConst / S.splitLength + W.meanConst / lowConst) ≤ W.resolvedVelocity

end Reduction

end CellCert

end Breakdown

end
end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert Assembly CellAnalysis

structure IsFarFloorTests {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (W : WeightData)
    (F : FarMajorantData) : Prop where
  strain_resolved_radial :
    F.strainFloor ≤ W.energy * CellScalars.tailLam K (S.degNear + 1) 0 - W.resolvedStrain - W.shift
  strain_resolved_height :
    F.strainFloor ≤ W.energy * CellScalars.tailLam K 0 (S.degNear + 1) - W.resolvedStrain - W.shift
  anti_resolved_radial : F.strainFloor ≤
    (W.energy + 2 * W.vorticity) * CellScalars.tailLam K (S.degNear + 1) 0
      - 2 * W.resolvedCurl - W.resolvedStrain - W.shift
  anti_resolved_height : F.strainFloor ≤
    (W.energy + 2 * W.vorticity) * CellScalars.tailLam K 0 (S.degNear + 1)
      - 2 * W.resolvedCurl - W.resolvedStrain - W.shift
  strain_band_radial : F.strainFloor ≤ W.symAt K S (S.degNear + 1) 0 (((W.J + 1 : ℕ) : ℝ) * c.order) true
  strain_band_height : F.strainFloor ≤ W.symAt K S 0 (S.degNear + 1) (((W.J + 1 : ℕ) : ℝ) * c.order) true
  anti_band_radial : F.strainFloor ≤ W.antiAt K S (S.degNear + 1) 0 (((W.J + 1 : ℕ) : ℝ) * c.order) true
  anti_band_height : F.strainFloor ≤ W.antiAt K S 0 (S.degNear + 1) (((W.J + 1 : ℕ) : ℝ) * c.order) true
  velocity_radial : F.velocityFloor ≤ W.shift * radialEigen K S.degHigh - W.resolvedVelocity
  velocity_height : F.velocityFloor ≤ W.shift * heightEigen K (S.degNear + 1) - W.resolvedVelocity

structure IsTailColumnBound (K : CellBox) (B : CellBases) (D : ℕ) {I O : Type} [Fintype I] [Fintype O]
    (T : TailFamily I O) : Prop where
  outWeight_nonneg : ∀ o, 0 ≤ T.outWeight o
  radialBound_nonneg : ∀ i j, 0 ≤ T.radialBound i j
  heightBound_nonneg : ∀ i l, 0 ≤ T.heightBound i l
  radial_sections : ∀ i o c, ∀ z ∈ Set.Icc K.z₁ K.z₂, ∀ θ : ℝ,
    AEStronglyMeasurable (fun r => T.mult i o c (r, z) θ) (volume.restrict (Set.Icc K.r₁ K.r₂))
  height_sections : ∀ i o c, ∀ r ∈ Set.Icc K.r₁ K.r₂, ∀ θ : ℝ,
    AEStronglyMeasurable (fun z => T.mult i o c (r, z) θ) (volume.restrict (Set.Icc K.z₁ K.z₂))
  radial_columns : ∀ i, ∀ j ≤ T.inputDeg i, ∀ z ∈ Set.Ioo K.z₁ K.z₂, ∀ θ : ℝ,
    (∑ o, T.outWeight o * ∑ c, K.radialTail B D (fun r => T.mult i o c (r, z) θ * (B.radialPoly j r : ℂ)))
      ≤ T.radialBound i j ^ 2
  height_columns : ∀ i, ∀ l ≤ T.inputDeg i, ∀ r ∈ Set.Ioo K.r₁ K.r₂, ∀ θ : ℝ,
    (∑ o, T.outWeight o * ∑ c, K.heightTail B D (fun z => T.mult i o c (r, z) θ * (B.heightPoly l z : ℂ)))
      ≤ T.heightBound i l ^ 2

end Reduction

end CellCert

end Breakdown

end
end

section

open scoped ContDiff ENNReal

open MeasureTheory Matrix Polynomial

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellSystem

open SteadyCert Assembly Reduction GivenFields GivenModel Exterior Spectral CellAnalysis CellCoordinates CellFormula

open _root_.Breakdown.CellCert.Finite

structure IsRowTurnNumbers {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N) (rate : ℝ) : Prop where
  order_ge : 2 ≤ c.order
  rate_nonneg : 0 ≤ rate
  const_ge : ∀ a, RD.harmonic a ≠ 0 → RD.cellWeight (RD.cell a) * (M.box (RD.cell a)).r₂ ^ 2 ≤ rate ^ 2

structure CellSumValues where
  pieceCount : ℕ
  pieceRhoLo : Fin pieceCount → ℝ
  pieceRhoHi : Fin pieceCount → Option ℝ
  pieceZLo : Fin pieceCount → ℝ
  pieceZHi : Fin pieceCount → Option ℝ
  pieceChart : Fin pieceCount → Option (ℝ × ℝ × ℝ × ℝ)
  chartScale : ℝ
  pieceSup : Fin pieceCount → ℝ
  pieceMass : Fin pieceCount → ℝ
  boxCount : ℕ
  boxRhoLo : Fin boxCount → ℝ
  boxRhoHi : Fin boxCount → Option ℝ
  boxZLo : Fin boxCount → ℝ
  boxZHi : Fin boxCount → Option ℝ
  boxBound : Fin boxCount → ℝ

def pieceSolidOf (lo : ℝ) (hi : Option ℝ) (zlo : ℝ) (zhi : Option ℝ) : Set Space :=
  {y | lo ≤ horizontalNorm y ∧ (∀ h, hi = some h → horizontalNorm y ≤ h) ∧ zlo ≤ y 2 ∧ (∀ h, zhi = some h → y 2 ≤ h)}

def chartSolid (L t₀ t₁ x₀ x₁ : ℝ) : Set Space :=
  {y | t₀ ≤ ‖y‖ / (‖y‖ + L) ∧ ‖y‖ / (‖y‖ + L) ≤ t₁ ∧ x₀ * ‖y‖ ≤ y 2 ∧ y 2 ≤ x₁ * ‖y‖}

namespace CellSumValues

variable (T : CellSumValues) (m : ℕ)

def pieceSolid (b : Fin T.pieceCount) : Set Space :=
  match T.pieceChart b with
  | some (t₀, t₁, x₀, x₁) => chartSolid T.chartScale t₀ t₁ x₀ x₁
  | none => pieceSolidOf (T.pieceRhoLo b) (T.pieceRhoHi b) (T.pieceZLo b) (T.pieceZHi b)

def baseData : CellSumData where
  pieceCount := T.pieceCount
  pieceRhoLo := T.pieceRhoLo
  pieceRhoHi := T.pieceRhoHi
  pieceZLo := T.pieceZLo
  pieceZHi := T.pieceZHi
  pieceSolid := T.pieceSolid
  pieceSup := T.pieceSup
  pieceMass := T.pieceMass
  boxCount := T.boxCount
  boxRhoLo := T.boxRhoLo
  boxRhoHi := T.boxRhoHi
  boxZLo := T.boxZLo
  boxZHi := T.boxZHi
  rule := fun _ _ _ => 0
  sectorLength := fun _ _ _ => 0
  boxBound := T.boxBound

def nearFactors : List ℝ := [1, 1 / 2, 1 / 4, 3 / 25, 3 / 50, 3 / 100]

def nearLength (a : Fin T.boxCount) (b : Fin T.pieceCount) (f : ℝ) : ℝ :=
  T.baseData.sectorConst m a b * (f * (2 * Real.pi / m))

def NearValid (a : Fin T.boxCount) (b : Fin T.pieceCount) (l : ℝ) : Prop :=
  0 < l ∧ 0 < T.baseData.sectorConst m a b ∧ (T.pieceRhoHi b).isSome ∧ (T.pieceZHi b).isSome

def nearValue (a : Fin T.boxCount) (b : Fin T.pieceCount) (mirrored : Bool) (l : ℝ) : ℝ :=
  ({ T.baseData with sectorLength := fun _ _ _ => l } : CellSumData).nearTerm m a b mirrored
    + T.baseData.sectorSum m a b mirrored 1

open Classical in
def bestNear (a : Fin T.boxCount) (b : Fin T.pieceCount) (mirrored : Bool) : Option ℝ :=
  nearFactors.foldl (fun acc f =>
    let l := T.nearLength m a b f
    if T.NearValid m a b l then
      match acc with
      | none => some l
      | some l' => if T.nearValue m a b mirrored l < T.nearValue m a b mirrored l' then some l else some l'
    else acc) none

open Classical in
def ruleOf (a : Fin T.boxCount) (b : Fin T.pieceCount) (mirrored : Bool) : Fin 3 :=
  let v₀ := T.baseData.sectorSum m a b mirrored 0
  let v₁ := kernelShell (T.pieceMass b) (T.pieceSup b) (T.baseData.sectorDist m a b mirrored 0)
  match T.bestNear m a b mirrored with
  | some l => if T.nearValue m a b mirrored l ≤ min v₀ v₁ then 2 else if v₁ ≤ v₀ then 1 else 0
  | none => if v₁ ≤ v₀ then 1 else 0

def lengthOf (a : Fin T.boxCount) (b : Fin T.pieceCount) (mirrored : Bool) : ℝ :=
  (T.bestNear m a b mirrored).getD 0

def toData : CellSumData :=
  { T.baseData with rule := T.ruleOf m, sectorLength := T.lengthOf m }

end CellSumValues

structure IsCellSumValues (m : ℕ) (T : CellSumValues) : Prop where
  order_even : Even m ∧ 4 ≤ m
  piece_box : ∀ b, 0 ≤ T.pieceRhoLo b ∧ (∀ h, T.pieceRhoHi b = some h → T.pieceRhoLo b ≤ h) ∧ 0 ≤ T.pieceZLo b ∧
    (∀ h, T.pieceZHi b = some h → T.pieceZLo b ≤ h)
  chart_scale : 0 < T.chartScale
  chart_box : ∀ b t₀ t₁ x₀ x₁, T.pieceChart b = some (t₀, t₁, x₀, x₁) → 0 ≤ x₀ ∧
    ∀ y ∈ chartSolid T.chartScale t₀ t₁ x₀ x₁, T.pieceRhoLo b ≤ horizontalNorm y ∧
      (∀ h, T.pieceRhoHi b = some h → horizontalNorm y ≤ h) ∧ T.pieceZLo b ≤ y 2 ∧ (∀ h, T.pieceZHi b = some h → y 2 ≤ h)
  sup_nonneg : ∀ b, 0 ≤ T.pieceSup b
  pieces_cover : ∀ y : Space, 0 ≤ y 2 → ∃ b, y ∈ T.pieceSolid b
  box_cover : ∀ ρ z : ℝ, 0 ≤ ρ → 0 ≤ z → ∃ a, T.boxRhoLo a ≤ ρ ∧ (∀ h, T.boxRhoHi a = some h → ρ ≤ h) ∧
    T.boxZLo a ≤ z ∧ (∀ h, T.boxZHi a = some h → z ≤ h)
  box_lower : ∀ a, 0 ≤ T.boxRhoLo a ∧ 0 ≤ T.boxZLo a

structure IsCellSumBounded (m : ℕ) (V : Space → ℝ) (T : CellSumValues) : Prop where
  sup_le : ∀ b, ∀ᵐ y ∂volume, y ∈ T.pieceSolid b → V y ≤ T.pieceSup b
  mass_le : ∀ b, (∫ y in T.pieceSolid b, V y) ≤ T.pieceMass b
  box_sum : ∀ a, (∑ b, ∑ mirrored : Bool, (T.toData m).pairTerm m a b mirrored) ≤ T.boxBound a

structure IsAdjointDualNumbers (α : ℝ) {k N : ℕ} (d : FracCertData k N) (j : Fin k) (p : Fin k → ℝ) (D : AdjointDual k) :
    Prop where
  pin_scale : ∀ l, 0 < D.pinScale l
  potentialScale_nonneg : 0 ≤ D.potentialScale
  dual_bound : l2Norm D.dualField ≤ D.dualBound
  potential_bound : Real.sqrt (∫ y, entrySq (D.potentialGrad y)) ≤ D.potentialBound
  flux_bound : Real.sqrt (∫ y, entrySq (D.fluxField y)) ≤ D.fluxBound
  inverseSquare_weight : harmonicWeightSqOn D.inverseSquareModes D.inverseSquarePart ≤
    ENNReal.ofReal (D.inverseSquareBound ^ 2)
  inverseSquareBound_nonneg : 0 ≤ D.inverseSquareBound
  shift_bound : ∀ i, Real.sqrt (∫ y, ‖D.shiftField i y‖ ^ 2 * ‖d.adjoint j p y‖ ^ 2) ≤ D.shiftBound i
  shiftGrad_bound : ∀ i, Real.sqrt (∫ y, ‖y‖ ^ 2 * ‖D.shiftGrad i y‖ ^ 2 * ‖d.adjoint j p y‖ ^ 2) ≤ D.shiftGradBound i

def phaseDerivField (P : ChartParams) (F : FieldData) (β : ℝ) (y : Space) : Space :=
  deriv (fun b => fieldOf P F b y) β

def phaseCurvField (P : ChartParams) (F : FieldData) (β : ℝ) (y : Space) : Space :=
  deriv (fun b => deriv (fun b' => fieldOf P F b' y) b) β

def ampField {k : ℕ} (D : ProfileData k) (step : Fin k → ℝ) (i : Fin k) (β : ℝ) (y : Space) : Space :=
  fieldOf D.chart (D.part (Pi.single i 1)) β y + step i • phaseDerivField D.chart (D.part 0) β y

def gradSq (f : Space → Space) (y : Space) : ℝ := ‖fderiv ℝ f y‖ ^ 2

def splitWidth {k : ℕ} (radius step : Fin k → ℝ) : ℝ := ∑ i, |step i| * radius i

structure AdjointNumbers (k : ℕ) where
  potentialScale : ℝ
  dualBound : ℝ
  potentialBound : ℝ
  fluxBound : ℝ
  inverseSquareBound : ℝ
  shiftBound : Fin k → ℝ
  shiftGradBound : Fin k → ℝ
  exactSet : Finset (Fin k)

section Choices

variable {k : ℕ} (P : ChartParams) (A : AuxData k) (ν : ℝ) (j : Fin k) (p : Fin k → ℝ)

open Classical in
def sharpTraceOf : Space → Space :=
  if h : ∃ L : Space → Space, IsWeakNegTraceOf (fun y => ν • A.adjointField P j p y + A.sharpField P ν j p y) L ∧
      MemLp (fun y => ‖y‖ • L y) 2 volume then h.choose else fun _ => 0

open Classical in
def pinSecondTraceOf (l : Fin k) : (Space → (Space →L[ℝ] Space →L[ℝ] Space)) × (Space → Space) :=
  if h : ∃ q : (Space → (Space →L[ℝ] Space →L[ℝ] Space)) × (Space → Space),
      AEStronglyMeasurable q.1 volume ∧ IsWeakSecondDerivOf (fun y => fderiv ℝ (A.pinPotentialField P l) y) q.1 ∧
      (∃ C : ℝ, ∀ᵐ y ∂volume, ‖q.1 y‖ ≤ C) ∧
      IsWeakNegTraceOf (A.pinPotentialField P l) q.2 ∧ AEStronglyMeasurable q.2 volume ∧
      (∃ C : ℝ, ∀ᵐ y ∂volume, ‖q.2 y‖ ≤ C) then h.choose else (fun _ => 0, fun _ => 0)

open Classical in
def dualTraceOf : Space → Space :=
  if h : ∃ L : Space → Space, IsWeakNegTraceOf (A.dualFieldOf P j p) L ∧ MemLp (fun y => ‖y‖ • L y) 2 volume
  then h.choose else fun _ => 0

open Classical in
def potentialTraceOf : Space → Space :=
  if h : ∃ L : Space → Space, IsWeakNegTraceOf (A.potentialFieldOf P j p) L ∧ MemLp (fun y => ‖y‖ • L y) 2 volume
  then h.choose else fun _ => 0

open Classical in
def fluxDivOf : Space → Space :=
  if h : ∃ Dv : Space → Space, IsWeakMatrixDivergenceOf (A.fluxFieldOf P j p) Dv ∧ MemLp (fun y => ‖y‖ • Dv y) 2 volume
  then h.choose else fun _ => 0

end Choices

def adjointDualCore {k : ℕ} (D : ProfileData k) (A : AuxData k) (ν : ℝ) (j : Fin k) (p : Fin k → ℝ)
    (nums : AdjointNumbers k) : AdjointDual k where
  adjointGrad := fun y => fderiv ℝ (A.adjointField D.chart j p) y
  adjointSecond := fun y => fderiv ℝ (fun z => fderiv ℝ (A.adjointField D.chart j p) z) y
  sharpTrace := sharpTraceOf D.chart A ν j p
  sharpGrad := fun y => fderiv ℝ (A.sharpField D.chart ν j p) y
  pinPotential := fun l => A.pinPotentialField D.chart l
  pinSecond := fun l => (pinSecondTraceOf D.chart A l).1
  pinTrace := fun l => (pinSecondTraceOf D.chart A l).2
  pinScale := A.pinScale
  pressure := A.adjointPressureField D.chart j p
  pressureGrad := fun y => gradientAt (A.adjointPressureField D.chart j p) y
  dualField := A.dualFieldOf D.chart j p
  dualGrad := fun y => fderiv ℝ (A.dualFieldOf D.chart j p) y
  dualTrace := dualTraceOf D.chart A j p
  potentialField := A.potentialFieldOf D.chart j p
  potentialGrad := fun y => fderiv ℝ (A.potentialFieldOf D.chart j p) y
  potentialTrace := potentialTraceOf D.chart A j p
  potentialScale := nums.potentialScale
  fluxField := A.fluxFieldOf D.chart j p
  fluxDiv := fluxDivOf D.chart A j p
  inverseSquarePart := fun _ => 0
  exactSet := nums.exactSet
  shiftField := fun i => amplitudeFieldAt D i p
  shiftGrad := fun i y => fderiv ℝ (amplitudeFieldAt D i p) y
  dualBound := nums.dualBound
  potentialBound := nums.potentialBound
  fluxBound := nums.fluxBound
  inverseSquareBound := nums.inverseSquareBound
  inverseSquareModes := ∅
  shiftBound := nums.shiftBound
  shiftGradBound := nums.shiftGradBound

open Classical in
def inverseSquareChoice (α : ℝ) {k N : ℕ} (D : ProfileData k) (d : FracCertData k N) (j : Fin k)
    (p : Fin k → ℝ) (Dd : AdjointDual k) : (Space → Space) × Finset ℤ :=
  if h : ∃ q : (Space → Space) × Finset ℤ, (∀ᵐ y ∂volume, q.1 y = inverseSquarePartOf α D d j p Dd y) ∧
      AEStronglyMeasurable q.1 volume ∧ MemLp (fun y => ‖y‖ • q.1 y) 2 volume ∧
      ∀ n ∉ q.2, ∀ ρ z : ℝ, angularMode (horizontalPart q.1) n ρ z = 0 ∧ angularMode (verticalPart q.1) n ρ z = 0
  then h.choose else (inverseSquarePartOf α D d j p Dd, ∅)

def adjointDualOf (α : ℝ) {k N : ℕ} (D : ProfileData k) (d : FracCertData k N) (A : AuxData k) (ν : ℝ)
    (j : Fin k) (p : Fin k → ℝ) (nums : AdjointNumbers k) : AdjointDual k :=
  { adjointDualCore D A ν j p nums with
    inverseSquarePart := (inverseSquareChoice α D d j p (adjointDualCore D A ν j p nums)).1
    inverseSquareModes := (inverseSquareChoice α D d j p (adjointDualCore D A ν j p nums)).2 }

structure CellEntry (M : CellMesh) (N k slots : ℕ) where
  meshCell : Fin M.cellCount
  scalars : CellScalars
  givenBases : CellBases
  baseDegree : ℕ
  classes : CellClasses
  rows : CellRows N slots k
  weights : WeightData
  strainScalar : ℝ
  lowConst : ℝ
  strainConst : ℝ
  meanConst : ℝ
  waveConst : ℝ
  devConst : Fin 4 → Fin classes.count → ℝ
  devSlope : Fin 4 → Fin classes.count → ℝ
  far : FarMajorantData
  rowDegree : ℕ
  systemMultiplier : Matrix (Fin N) (Fin N) ℝ
  systemReducer : Matrix (Fin rows.reducerCount) (Fin N) ℝ

namespace CellEntry

variable {M : CellMesh} {N k slots : ℕ} (r : CellEntry M N k slots)

def box : CellBox := M.box r.meshCell

def bases : CellBases := extendBases r.box r.baseDegree r.givenBases

end CellEntry

structure CellSystemData (k N : ℕ) (M : CellMesh) where
  split : CellSplit k N
  tree : Finite.TreeCertificate split.slots k
  spectral : Spectral.SpectralData
  exterior : Exterior.ExteriorData
  mesh : MeshData k N split
  cell : Fin split.cellCount → CellEntry M N k split.slots
  weightValue : ℝ
  exteriorStrain : ℝ
  exteriorMean : ℝ
  exteriorWave : ℝ
  strainOpBound : ℝ
  curlGradSums : CellSumValues
  curlGradKernel : ℝ
  curlSums : CellSumValues
  curlKernel : ℝ
  rateRowConst : ℝ
  centreSup : (Fin k → ℝ) → ℝ
  centreKernel : ℝ
  splitRange : ℝ
  splitStep : Fin k → ℝ
  ampSums : Fin k → CellSumValues
  ampKernel : Fin k → ℝ
  higherSums : (Fin k → ℕ) → CellSumValues
  higherKernel : (Fin k → ℕ) → ℝ
  curvSums : CellSumValues
  curvKernel : ℝ
  ampSup : Fin k → ℝ
  higherSup : (Fin k → ℕ) → ℝ
  curvSup : ℝ
  adjointKernel : Fin k → ℝ
  adjointSums : Fin k → (Fin k → ℕ) → CellSumValues
  adjointPartKernel : Fin k → (Fin k → ℕ) → ℝ
  adjointNumbers : Fin k → (Fin k → ℝ) → AdjointNumbers k

structure IsSystemInstance {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (RD : RowData M N) (X : CellSystemData k N M) : Prop where
  power_eq : D.power = 501 / 500
  weight_eq : c.weight = fun _ => X.weightValue
  weightMin_eq : c.weightMin = X.weightValue
  weightMax_eq : c.weightMax = X.weightValue
  weightValue_pos : 0 < X.weightValue
  exterior_radius : X.exterior.radius = boxRadius M.outerSize
  exterior_radiusMin : X.exterior.radiusMin = M.outerSize
  exterior_radiusMax : X.exterior.radiusMax = Real.sqrt 2 * M.outerSize
  exterior_strain : X.exterior.strainBound = fun y => X.exteriorStrain / ‖y‖ ^ 2
  exterior_mean : X.exterior.meanCurlGradBound = fun y => X.exteriorMean / ‖y‖ ^ 3
  exterior_wave : X.exterior.waveCurlGradBound = fun y => X.exteriorWave / ‖y‖ ^ 3
  exterior_split : X.exterior.splitLength = fun y => 2 * ‖y‖
  support_inside : D.chart.L0 * A.supportBreak / (1 - A.supportBreak) ≤ M.outerSize
  cell_solid : ∀ K₂, X.split.cell K₂ = (X.cell K₂).box.solid
  cell_bijective : Function.Bijective (fun K₂ => (X.cell K₂).meshCell)
  row_cell : ∀ a, (X.cell (X.split.rowCell a)).meshCell = RD.cell a
  moment_eq : ∀ x, X.split.moment x = X.mesh.canonicalMoment c x
  gauge_left : ∀ K₂, (X.mesh.coords K₂).gaugeLeft = X.mesh.canonicalLeft K₂
  gauge_right : ∀ K₂, (X.mesh.coords K₂).gaugeRight = X.mesh.canonicalRight K₂
  spectralBound_eq : c.spectralBound = X.spectral.blockSpectral
  block_eq : ∀ a, X.spectral.block (c.blockIndex a) = rowBlock M RD c.order a

structure IsBaseSystem (α : ℝ) {k N : ℕ} (d : FracCertData k N) : Prop where
  order_ge : 3 ≤ d.order
  coercivity_pos : 0 < d.coercivity
  coercivity_lt : d.coercivity < d.splitVisc
  pinWeight_pos : 0 < d.pinWeight
  rowMax_pos : 0 < d.rowMax
  multiplierScale_pos : 0 < d.multiplierScale
  radius_nonneg : ∀ j, 0 ≤ d.radius j
  slope_ne_zero : ∀ j, d.slope j ≠ 0
  ellipsoidRadius_nonneg : 0 ≤ d.ellipsoidRadius
  ellipsoid_le : ∀ j ∉ d.activeSet, d.ellipsoidRadius ≤ |d.slope j| * d.radius j
  frame_near : ∀ z : Fin k → ℝ, |∑ j, (d.frame *ᵥ z) j ^ 2 - ∑ j, z j ^ 2| ≤ d.frameDefect * ∑ j, z j ^ 2
  frameDefect_lt : d.frameDefect < 1
  pinGap_bound : ∑ l, ∫ y, entrySq (d.smoothPin l y - d.pin l y) ≤ d.pinGap ^ 2
  pinGap_nonneg : 0 ≤ d.pinGap
  losses_nonneg : 0 ≤ d.potLoss ∧ 0 ≤ d.rowLoss ∧ 0 ≤ d.pinLoss
  reduced_pos : 0 < d.reducedCoercivity
  reduced_le : d.reducedCoercivity ≤ d.coercivity - d.potLoss
  lowLoss_bound : ∀ κ₀ : ℝ, 0 < κ₀ →
    max (d.splitVisc - κ₀ ^ (2 * (α - 1))) 0 ≤ d.lowLoss * (1 + d.weightMin / κ₀ ^ 2)
  reducedGap_pos : 0 < d.reducedGap
  formScale_nonneg : 0 ≤ d.formScale
  formScale_bound : ∀ κ₀ : ℝ, 0 < κ₀ →
    1 ≤ d.formScale ^ 2 * (κ₀ ^ (2 * (α - 1)) - d.splitVisc + d.reducedCoercivity * (1 + d.weightMin / κ₀ ^ 2))
  splitBound_nonneg : 0 ≤ d.splitBound
  contraction_lt : d.contraction < 1
  productConst_nonneg : 0 ≤ d.productConst
  defect_norm : ∀ p ∈ box d.radius, projectedNorm (d.defect α p) ≤ d.defectBound
  defect_rows : ∀ p ∈ box d.radius, d.rowsModGrad (d.defect α p) ≤ d.defectRowBound
  size_ge : d.boundFn d.defectBound d.defectRowBound 0 ≤ d.sizeBound
  size_small : 4 * d.rowConst * d.productConst * d.sizeBound < 1
  adjointQuad_nonneg : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, 0 ≤ d.adjointQuad j p
  active_inclusion : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, ∀ p' ∈ d.testBox,
    d.adjointQuad j p * d.heldRadius ^ 2 + d.heldRadius * Real.sqrt ((d.adjointLocal j p + d.adjointSpread j p
      + vecNorm (d.adjointPin j p) * d.pinGap / Real.sqrt d.weightMin) ^ 2
      + vecNorm (d.adjointError j p) ^ 2 / d.multiplierScale ^ 2) + |d.adjustedMultiplier α p' j|
      ≤ |d.slope j| * d.radius j
  stiff_inclusion : ∀ p' ∈ d.testBox, Real.sqrt (1 + d.frameDefect) * d.heldRadius / d.multiplierScale +
    Real.sqrt (∑ j ∈ d.activeSetᶜ, ((d.frameᵀ *ᵥ d.multiplier p') j - d.slope j * p' j) ^ 2) ≤ d.ellipsoidRadius
  nontrivial : ∀ p ∈ box d.radius, d.heldRadius / Real.sqrt d.weightMin < Real.sqrt (∫ y, entrySq (d.gradProfile p y))

structure IsCellNumbers (α : ℝ) {k N : ℕ} (c : FracCellData k N) : Prop where
  innerWeight_nonneg : 0 ≤ c.innerWeight
  innerWeight_le : c.innerWeight ≤ c.splitVisc
  velocityLoss_bound : ∀ y, Real.sqrt (c.cellWeight y) * ‖c.velocityError y‖ ≤ c.velocityLoss
  actuatorGradLoss_bound : ∑ i, (∫ y, entrySq (c.actuatorGrad i y - c.modelActuatorGrad i y)) ≤ c.actuatorGradLoss ^ 2
  actuatorLoss_bound : ∑ i, c.toFracCertData.rows (fun y => c.actuator i y - c.modelActuator i y) ^ 2
    ≤ c.actuatorLoss ^ 2
  pinFieldLoss_bound : ∑ i, (∫ y, entrySq (c.pin i y - c.modelPinField i y)) ≤ c.pinFieldLoss ^ 2
  losses_nonneg' : 0 ≤ c.centreLoss ∧ 0 ≤ c.rateLoss ∧ 0 ≤ c.strainLoss ∧ 0 ≤ c.curlGradLoss ∧
    0 ≤ c.velocityLoss ∧ 0 ≤ c.curlLoss ∧ 0 ≤ c.actuatorGradLoss ∧ 0 ≤ c.actuatorLoss ∧ 0 ≤ c.pinFieldLoss
  potLoss_ge : c.centreLoss + (c.strainLoss + Real.sqrt (7 / 2) * c.curlGradLoss) / c.weightMin
    + c.actuatorGradLoss / (2 * c.multiplierScale * Real.sqrt c.weightMin) ≤ c.potLoss
  rowLoss_ge : Real.sqrt c.rowMax * c.centreLoss + c.rateLoss
    + (c.velocityLoss + c.curlLoss) / Real.sqrt c.weightMin + c.actuatorLoss / c.multiplierScale ≤ c.rowLoss
  pinLoss_ge : c.pinFieldLoss / Real.sqrt c.weightMin ≤ c.pinLoss
  rowWeight_block : ∀ a b, c.blockIndex a = c.blockIndex b → c.rowWeight a = c.rowWeight b
  baseCoef_nonneg : 0 ≤ c.baseCoef
  levelCoef_nonneg : ∀ i, 0 ≤ c.levelCoef i
  levelRate_pos : ∀ i, 0 < c.levelRate i
  cutoff_ge : c.splitVisc ^ (1 / (α - 1)) ≤ c.cutoff
  symbol_fit : ∀ x : ℝ, 0 < x → x ≤ c.cutoff → c.ratioSymbol α x ≤ c.levelSum x
  symbol_end : c.gapSymbol α c.cutoff ^ 2 / (c.gapSymbol α c.cutoff + c.reducedCoercivity) ≤ c.levelSum c.cutoff
  splitBound_ge : ∀ a, c.rowWeight a * (c.baseCoef + ∑ i, c.levelCoef i * c.spectralBound (c.blockIndex a) (c.levelRate i)
    + (α - 1) * c.tailConst * c.cutoff ^ ((α - 1) - 1 / 2) / (1 / 2 - (α - 1))) ≤ c.splitBound ^ 2

structure IsReducedLosses {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (RD : RowData M N) (X : CellSystemData k N M) : Prop where
  strain_opNorm : ∀ y, ‖c.strainError y‖ ≤ X.strainOpBound
  strain_le : X.strainOpBound ≤ c.strainLoss
  curlGrad_sums_bounded : IsCellSumBounded c.order (fun y => ‖c.curlGradError y‖ ^ 2) X.curlGradSums
  curlGrad_sums_values : IsCellSumValues c.order X.curlGradSums
  curlGrad_boxes : ∀ a, X.curlGradSums.boxBound a ≤ X.curlGradKernel
  curlGrad_le : Real.sqrt X.curlGradKernel ≤ c.curlGradLoss
  curl_sums_bounded : IsCellSumBounded c.order (fun y => c.cellWeight y * ‖c.curlError y‖ ^ 2) X.curlSums
  curl_sums_values : IsCellSumValues c.order X.curlSums
  curl_boxes : ∀ a, X.curlSums.boxBound a ≤ X.curlKernel
  curl_le : Real.sqrt X.curlKernel ≤ c.curlLoss
  turn_numbers : IsRowTurnNumbers c M RD X.rateRowConst
  rate_le : ∀ p ∈ box c.radius, |c.rotationRate p - c.modelRate| * ((c.order : ℝ) / ((c.order : ℝ) - 1))
    * X.rateRowConst ≤ c.rateLoss * Real.sqrt c.weightMin
  amp_sup : ∀ i, ∀ β, |β - D.phase 0| ≤ X.splitRange → ∀ y, ‖ampField D X.splitStep i β y‖ ≤ X.ampSup i
  higher_sup : ∀ μ ∈ D.index, 2 ≤ ∑ i, μ i → ∀ β, |β - D.phase 0| ≤ X.splitRange →
    ∀ y, ‖fieldOf D.chart (D.part μ) β y‖ ≤ X.higherSup μ
  curv_sup : ∀ β, |β - D.phase 0| ≤ X.splitRange → ∀ y, ‖phaseCurvField D.chart (D.part 0) β y‖ ≤ X.curvSup
  centreSup_eq : ∀ p, X.centreSup p = ∑ i, c.radius i * X.ampSup i
      + ∑ μ ∈ D.index.filter (fun μ => 2 ≤ ∑ i, μ i), (∏ i, c.radius i ^ μ i) * X.higherSup μ
      + splitWidth c.radius X.splitStep ^ 2 / 2 * X.curvSup
  split_step : ∀ i, X.splitStep i = -(2 * D.power * (D.chart.m : ℝ) * D.rateSlope i)
  split_width : splitWidth c.radius X.splitStep ≤ X.splitRange
  amp_index : ∀ i, Pi.single i 1 ∈ D.index
  amp_le_bound : ∀ i, ∀ β, |β - D.phase 0| ≤ X.splitRange →
    IsCellSumBounded c.order (gradSq (ampField D X.splitStep i β)) (X.ampSums i)
  amp_values : ∀ i, IsCellSumValues c.order (X.ampSums i)
  amp_boxes : ∀ i a, (X.ampSums i).boxBound a ≤ X.ampKernel i ^ 2
  higher_bounded : ∀ μ ∈ D.index, 2 ≤ ∑ i, μ i → ∀ β, |β - D.phase 0| ≤ X.splitRange →
    IsCellSumBounded c.order (gradSq (fieldOf D.chart (D.part μ) β)) (X.higherSums μ)
  higher_values : ∀ μ ∈ D.index, 2 ≤ ∑ i, μ i → IsCellSumValues c.order (X.higherSums μ)
  higher_boxes : ∀ μ ∈ D.index, 2 ≤ ∑ i, μ i → ∀ a, (X.higherSums μ).boxBound a ≤ X.higherKernel μ ^ 2
  curv_bounded : ∀ β, |β - D.phase 0| ≤ X.splitRange →
    IsCellSumBounded c.order (gradSq (phaseCurvField D.chart (D.part 0) β)) X.curvSums
  curv_values : IsCellSumValues c.order X.curvSums
  curv_boxes : ∀ a, X.curvSums.boxBound a ≤ X.curvKernel ^ 2
  split_kernels_nonneg : (∀ i, 0 ≤ X.ampKernel i) ∧ (∀ μ, 0 ≤ X.higherKernel μ) ∧ 0 ≤ X.curvKernel
  centreKernel_ge : ∑ i, c.radius i * X.ampKernel i
      + ∑ μ ∈ D.index.filter (fun μ => 2 ≤ ∑ i, μ i), (∏ i, c.radius i ^ μ i) * X.higherKernel μ
      + splitWidth c.radius X.splitStep ^ 2 / 2 * X.curvKernel ≤ X.centreKernel
  centreKernel_nonneg : 0 ≤ X.centreKernel
  centre_le : ∀ p ∈ box c.radius, X.centreSup p + X.centreKernel ≤ c.centreLoss * Real.sqrt c.weightMin
  productConst_ge : (2 * Real.pi) ^ (-(1 : ℝ) / 2) * (27 / 256 : ℝ) ^ ((1 : ℝ) / 4) * c.weightMin ^ (-(3 : ℝ) / 4)
    ≤ c.productConst
  adjoint_width : splitWidth c.radius A.phaseSlope ≤ X.splitRange
  adjoint_bounded : ∀ j ∈ c.activeSet, ∀ γ ∈ (A.adjointFamily j).indices, ∀ β, |β - A.phase 0| ≤ X.splitRange →
    IsCellSumBounded c.order (fun y => ‖fieldOf D.chart ((A.adjointFamily j).coef γ) β y‖ ^ 2 / X.weightValue)
      (X.adjointSums j γ)
  adjoint_values : ∀ j ∈ c.activeSet, ∀ γ ∈ (A.adjointFamily j).indices, IsCellSumValues c.order (X.adjointSums j γ)
  adjoint_boxes : ∀ j ∈ c.activeSet, ∀ γ ∈ (A.adjointFamily j).indices, ∀ a,
    (X.adjointSums j γ).boxBound a ≤ X.adjointPartKernel j γ ^ 2
  adjointPartKernel_nonneg : ∀ j γ, 0 ≤ X.adjointPartKernel j γ
  adjointKernel_ge : ∀ j ∈ c.activeSet,
    ∑ γ ∈ (A.adjointFamily j).indices, multiPow γ c.radius * X.adjointPartKernel j γ ≤ Real.sqrt (X.adjointKernel j)
  adjointKernel_nonneg : ∀ j, 0 ≤ X.adjointKernel j
  adjointQuad_ge : ∀ j ∈ c.activeSet, ∀ p ∈ box c.radius,
    Real.sqrt (X.adjointKernel j) / Real.sqrt c.weightMin ≤ c.adjointQuad j p
  adjoint_numbers : ∀ j ∈ c.activeSet, ∀ p ∈ box c.radius, IsAdjointDualNumbers (501 / 500) c.toFracCertData j p
    (adjointDualOf (501 / 500) D c.toFracCertData A c.splitVisc j p (X.adjointNumbers j p))
  adjointLocal_ge : ∀ j ∈ c.activeSet, ∀ p ∈ box c.radius,
    Real.sqrt ((X.adjointNumbers j p).dualBound ^ 2 + ((X.adjointNumbers j p).potentialScale * (X.adjointNumbers j p).potentialBound
      + (X.adjointNumbers j p).fluxBound + (X.adjointNumbers j p).inverseSquareBound
      + ∑ i ∈ Finset.univ \ (X.adjointNumbers j p).exactSet,
          |p i| * ((X.adjointNumbers j p).shiftBound i + 2 * (X.adjointNumbers j p).shiftGradBound i)) ^ 2
        / c.weightMin) ≤ c.adjointLocal j p
  adjointSpread_ge : ∀ j ∈ c.activeSet, ∀ p ∈ box c.radius,
    l2Norm (fun y => lowPowerAt ((501 / 500 : ℝ) - 1) (c.adjoint j p) y - (c.splitVisc • c.adjoint j p y + c.adjointSharp j p y))
      ≤ c.adjointSpread j p

structure IsExteriorSystem (α : ℝ) {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (X : CellSystemData k N M) : Prop where
  innerWeight_ge : c.coercivity ≤ c.innerWeight
  innerWeight_le : c.innerWeight ≤ c.splitVisc
  consts_nonneg : 0 ≤ X.exteriorMean ∧ 0 ≤ X.exteriorWave
  strain_le : ∀ y ∉ c.cellRegion, ∀ u : Space, inner ℝ (c.centreStrain y u) u ≤ X.exterior.strainBound y * ‖u‖ ^ 2
  curlGrad_le : ∀ y ∉ c.cellRegion, ‖c.centreCurlGrad y‖ ≤ X.exterior.meanCurlGradBound y + X.exterior.waveCurlGradBound y
  coef_lower : ∀ y ∉ c.cellRegion, X.exterior.coefLower ≤ ExteriorData.gradientCoef c X.exterior α y
  wave_bound : ∀ y ∉ c.cellRegion,
    ‖y‖ ^ 2 * ((traceFreeConst / 2) * X.exterior.waveCurlGradBound y / X.exterior.splitLength y) ≤ X.exterior.weightedWave
  mean_bound : ∀ y ∉ c.cellRegion, ‖y‖ * (traceFreeConst * X.exterior.meanCurlGradBound y) ≤ X.exterior.weightedMean
  exterior_test : 4 * X.exterior.weightedWave + 2 * X.exterior.weightedMean ≤ X.exterior.coefLower

structure IsSpectralSystem {k N : ℕ} (c : FracCellData k N) (sd : Spectral.SpectralData) : Prop where
  block_geometry : ∀ a, (sd.block (c.blockIndex a)).innerRadius < (sd.block (c.blockIndex a)).outerRadius ∧
    (sd.block (c.blockIndex a)).lowerHeight < (sd.block (c.blockIndex a)).upperHeight ∧
    0 ≤ (sd.block (c.blockIndex a)).lowerHeight ∧ 1 ≤ (sd.block (c.blockIndex a)).degree
  off_axis : ∀ a, (sd.block (c.blockIndex a)).onAxis = false → 0 < (sd.block (c.blockIndex a)).innerRadius
  on_axis : ∀ a, (sd.block (c.blockIndex a)).onAxis = true →
    (sd.block (c.blockIndex a)).innerRadius = 0 ∧ (sd.block (c.blockIndex a)).mode = 0 ∧
    24 ≤ c.cutoff * ((sd.block (c.blockIndex a)).outerRadius - (sd.block (c.blockIndex a)).innerRadius) ^ 2
  blocks_apart : ∀ a b, c.blockIndex a ≠ c.blockIndex b →
    volume (⋃ s, cellSolid (sd.block (c.blockIndex a)) s ∩ ⋃ s, cellSolid (sd.block (c.blockIndex b)) s) = 0 ∨
    ((sd.block (c.blockIndex a)).innerRadius = (sd.block (c.blockIndex b)).innerRadius ∧
      (sd.block (c.blockIndex a)).outerRadius = (sd.block (c.blockIndex b)).outerRadius ∧
      (sd.block (c.blockIndex a)).lowerHeight = (sd.block (c.blockIndex b)).lowerHeight ∧
      (sd.block (c.blockIndex a)).upperHeight = (sd.block (c.blockIndex b)).upperHeight ∧
      (sd.block (c.blockIndex a)).mode ≠ (sd.block (c.blockIndex b)).mode)
  axis_gradient : ∀ a, (sd.block (c.blockIndex a)).onAxis = true →
    AxisGradientBound (sd.block (c.blockIndex a)).degree (sd.axisGradient (sd.block (c.blockIndex a)).degree)
  cutoff_pos : 0 < c.cutoff
  tail_le : ∀ a, sd.tailFormula c.cutoff (c.blockIndex a) ≤ c.tailConst

structure IsSpectralBounds (sd : Spectral.SpectralData) : Prop where
  interval_bounded : ∀ q, ∀ e ∈ sd.intervalCerts q, IntervalCertificate q e.1 e.2
  axis_bounded : ∀ q, ∀ e ∈ sd.axisCerts q, AxisCertificate q e.1 e.2 (sd.axisCutoff q e)

structure IsSplitSystem {k N : ℕ} (c : FracCellData k N) (S : CellSplit k N) : Prop where
  kappa_slot_injective : Function.Injective S.kappaSlot
  kappa_slot_free : ∀ i j, S.freeMap (S.kappaSlot i) j = 0

structure IsTreeSystem {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (X : CellSystemData k N M) : Prop where
  tree : Finite.IsTreeCertificate X.tree
  cells_match : ∃ e : X.tree.Cell ≃ Fin X.split.cellCount ⊕ Fin X.split.delayCount,
    ∀ K, X.tree.cellForm K = Sum.elim X.split.cellMatrix X.split.delayForm (e K)
  global_eq : X.tree.globalForm = X.split.globalMatrix c

def systemWeight {M : CellMesh} {N : ℕ} (RD : RowData M N) (a : Fin N) : ℝ :=
  if RD.harmonic a = 0 then 1 else 2

def systemScale {k N : ℕ} (c : FracCellData k N) {M : CellMesh} (RD : RowData M N) (a : Fin N) : ℝ :=
  Real.sqrt c.splitVisc / systemWeight RD a

def testMultiplierOf {k N : ℕ} (c : FracCellData k N) {M : CellMesh} (RD : RowData M N) {slots : ℕ}
    (r : CellEntry M N k slots) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (systemScale c RD) * r.systemMultiplier * Matrix.diagonal (systemScale c RD)

def testReducerOf {k N : ℕ} (c : FracCellData k N) {M : CellMesh} (RD : RowData M N) {slots : ℕ}
    (r : CellEntry M N k slots) : Matrix (Fin r.rows.reducerCount) (Fin N) ℝ :=
  r.systemReducer * Matrix.diagonal (fun a => (systemScale c RD a)⁻¹)

def multiplierLHS {k N : ℕ} (c : FracCellData k N) {M : CellMesh} {slots : ℕ} (r : CellEntry M N k slots)
    (μ : Fin N → ℝ) : ℝ :=
  (∑ a ∈ r.rows.rowSet, μ a ^ 2 / (4 * Real.pi * c.rowWeight a)) + (∑ a ∈ r.rows.rowSet, r.rows.classRowWeight a * μ a ^ 2)
    + CellScalars.rowSquare c r.box r.scalars r.rows r.bases μ (fun _ _ => True)
    + CellScalars.rowSquareUpTo c r.box r.scalars r.bases r.rows r.rowDegree μ / (1 - r.rows.farShare)

structure IsCellSystemFacts (α : ℝ) {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (MD : ModelData M k)
    (RD : RowData M N) (Sp : CellSplit k N) (K₂ : Fin Sp.cellCount) (r : CellEntry M N k Sp.slots)
    (C : CellCoords k Sp.slots) : Prop where
  rows_instance : IsRowsInstance c M RD r.meshCell r.rows
  weight_form : IsWeightForm c r.box r.scalars r.weights
  local_zero : ∀ n ∉ r.scalars.resolved, ∀ p, r.scalars.localMatrix n p = 0
  resolved_tests : IsResolvedTests α c r.scalars r.weights r.strainScalar r.lowConst
  strain_const : r.scalars.strainBound = fun _ => r.strainConst
  mean_const : r.scalars.meanGradBound = fun _ => r.meanConst
  wave_const : r.scalars.waveGradBound = fun _ => r.waveConst
  dev_affine : ∀ i p,
    r.classes.strainDev i p = r.devConst 0 i + r.devSlope 0 i * CellScalars.rHat r.box p ∧
    r.classes.gradDev i p = r.devConst 1 i + r.devSlope 1 i * CellScalars.rHat r.box p ∧
    r.classes.velocityDev i p = r.devConst 2 i + r.devSlope 2 i * CellScalars.rHat r.box p ∧
    r.classes.curlDev i p = r.devConst 3 i + r.devSlope 3 i * CellScalars.rHat r.box p
  weight_tests : IsWeightTests α c r.box r.scalars r.weights
  axis_resolved_test : r.box.IsAxis → r.weights.J = 0
  degrees : 3 ≤ r.scalars.degLow ∧ r.scalars.degLow + 2 ≤ r.scalars.degHigh ∧ r.scalars.degHigh + 1 ≤ r.scalars.degNear
  row_degree : RD.degree + 2 ≤ r.scalars.degHigh
  model_degree : MD.columnDegree + 1 ≤ r.scalars.degNear
  row_poly_degree : RD.degree + MD.degree + 2 ≤ r.rowDegree
  grad_consts_nonneg : 0 ≤ r.meanConst ∧ 0 ≤ r.waveConst
  given_bases : IsGivenBases r.box r.baseDegree r.givenBases
  strain_le : ∀ p ∈ Set.Ioo r.box.r₁ r.box.r₂ ×ˢ Set.Ioo r.box.z₁ r.box.z₂, p.1 ≠ 0 → ∀ θ : ℝ, ∀ u : Space,
    inner ℝ (c.modelStrain (cylPoint p.1 θ p.2) u) u ≤ r.strainConst * ‖u‖ ^ 2
  mean_le : ∀ p ∈ Set.Ioo r.box.r₁ r.box.r₂ ×ˢ Set.Ioo r.box.z₁ r.box.z₂, p.1 ≠ 0 →
    OpBound (modeMat c.order 0 c.modelCurlGrad p.1 p.2) r.meanConst
  wave_le : ∀ p ∈ Set.Ioo r.box.r₁ r.box.r₂ ×ˢ Set.Ioo r.box.z₁ r.box.z₂, p.1 ≠ 0 → ∀ θ : ℝ,
    OpBound (fun a b => (frameMat θ (c.modelCurlGrad (cylPoint p.1 θ p.2)) a b : ℂ)
      - modeMat c.order 0 c.modelCurlGrad p.1 p.2 a b) r.waveConst
  class_bounds : ∀ i, ∀ p ∈ Set.Ioo r.box.r₁ r.box.r₂ ×ˢ Set.Ioo r.box.z₁ r.box.z₂, p.1 ≠ 0 → ∀ θ : ℝ,
    OpBound (classField c.order (r.classes.modes i) c.modelStrain p θ) (r.classes.strainDev i p) ∧
    OpBound (classField c.order (r.classes.modes i) c.modelCurlGrad p θ) (r.classes.gradDev i p) ∧
    vecSq (classVec c.order (r.classes.modes i) c.modelVelocity p θ) ≤ r.classes.velocityDev i p ^ 2 ∧
    vecSq (classVec c.order (r.classes.modes i) c.modelCurl p θ) ≤ r.classes.curlDev i p ^ 2
  harmonics_in_yModes : ∀ β : Fin (MD.harmonicCount + 1), (β : ℤ) ∈ r.rows.yModes ∧ -(β : ℤ) ∈ r.rows.yModes
  yModes_contain : r.scalars.resolved ∪ r.scalars.band ⊆ r.rows.yModes
  row_mode_resolved : ∀ a ∈ r.rows.rowSet, r.rows.rowModeOf a ∈ r.scalars.resolved
  class_modes_symm : ∀ i n, n ∈ r.classes.modes i ↔ -n ∈ r.classes.modes i
  class_disjoint : ∀ i j, i ≠ j → Disjoint (r.classes.modes i) (r.classes.modes j)
  class_cover_test : ∀ n ∈ r.scalars.resolved, ∀ n' ∉ r.scalars.resolved ∪ r.scalars.band,
    ∀ β : Fin (MD.harmonicCount + 1), (β : ℕ) ≤ MD.harmonicsOf r.meshCell →
      (n - n' = (β : ℤ) ∨ n - n' = -(β : ℤ)) → ∃ i, n - n' ∈ r.classes.modes i
  class_resolved : ∀ i, r.classes.resolvedPart i ⊆ r.scalars.resolved
  class_resolved_cover : ∀ i, ∀ n ∈ r.scalars.resolved,
    (∃ n' ∉ r.scalars.resolved ∪ r.scalars.band, n - n' ∈ r.classes.modes i) → n ∈ r.classes.resolvedPart i
  class_weights_pos : ∀ i, 0 < r.classes.shareWeight i ∧ 0 < r.classes.rowWeight i
  class_devs_nonneg : ∀ i p, 0 ≤ r.classes.strainDev i p ∧ 0 ≤ r.classes.gradDev i p ∧
    0 ≤ r.classes.velocityDev i p ∧ 0 ≤ r.classes.curlDev i p
  penalty_ge : ∀ p ∈ r.box.rect,
    (∑ i, (1 / 2) * Exterior.traceFreeConst * r.classes.gradDev i p * r.scalars.splitLength / r.classes.shareWeight i)
      ≤ r.scalars.penaltyStrain ∧
    (∑ i, (r.classes.strainDev i p / r.classes.shareWeight i + 2 * r.classes.rowWeight i * r.classes.velocityDev i p ^ 2))
      ≤ r.scalars.penaltyCurl ∧
    (∑ i, ((1 / 2) * Exterior.traceFreeConst * r.classes.gradDev i p / (r.scalars.splitLength * r.classes.shareWeight i)
      + 2 * r.classes.rowWeight i * r.classes.curlDev i p ^ 2)) ≤ r.scalars.penaltyVelocity
  farShare_mem : 0 < r.rows.farShare ∧ r.rows.farShare < 1
  rowSet_blocks : ∀ a b, RD.cell a = RD.cell b → RD.harmonic a = RD.harmonic b →
    (a ∈ r.rows.rowSet ↔ b ∈ r.rows.rowSet)
  multiplier_of_test : r.rows.multiplierMatrix = RD.mix * testMultiplierOf c RD r * RD.mix.transpose
  reducer_of_test : r.rows.reducer = testReducerOf c RD r * RD.mix⁻¹
  system_multiplier_symm : r.systemMultiplier.IsSymm
  system_multiplier_rows : ∀ a b, (a ∉ r.rows.rowSet ∨ b ∉ r.rows.rowSet) → r.systemMultiplier a b = 0
  classRowWeight_eq : ∀ a ∈ r.rows.rowSet, r.rows.classRowWeight a =
    ∑ i, if r.rows.rowModeOf a ∈ r.classes.resolvedPart i then 1 / (4 * Real.pi * r.classes.rowWeight i) else 0
  test_multiplier_bound : ∀ μ : Fin N → ℝ, (∀ a ∉ r.rows.rowSet, μ a = 0) →
    multiplierLHS c r ((RD.mix.transpose)⁻¹ *ᵥ μ) ≤ μ ⬝ᵥ (testMultiplierOf c RD r *ᵥ μ)
  far_share_pos : 0 < r.far.share
  far_turnBound_nonneg : 0 ≤ r.far.turnBound
  far_turn_ge : 1 / ((((r.weights.J + 1 : ℕ) : ℝ) * c.order) - 1) ≤ r.far.turnBound
  far_floors_pos : 0 < r.far.strainFloor ∧ 0 < r.far.velocityFloor
  far_floor_tests : IsFarFloorTests c r.box r.scalars r.weights r.far
  far_strainWeight_ge : (if r.scalars.band = ∅ then 1 else 1 + r.far.share) / r.far.strainFloor ≤ r.far.strainWeight
  far_resolvedVelocityWeight_ge : 1 / r.far.velocityFloor ≤ r.far.resolvedVelocityWeight
  far_bandVelocityWeight_ge : r.scalars.band ≠ ∅ →
    (1 + 1 / r.far.share) * r.far.turnBound ^ 2 / r.far.strainFloor ≤ r.far.bandVelocityWeight
  far_strain_columns : IsTailColumnBound r.box r.bases r.scalars.degNear (CellScalars.strainGroupFamily c r.box r.scalars r.far)
  far_velocity_columns : IsTailColumnBound r.box r.bases r.scalars.degNear (CellScalars.velocityGroupFamily c r.box r.scalars r.far)
  far_band_columns : r.scalars.band ≠ ∅ →
    IsTailColumnBound r.box r.bases r.scalars.degNear (CellScalars.bandGroupFamily c r.box r.scalars r.far)
  far_support_contains : ∀ n ∈ r.scalars.resolved, ∀ (a : Fin 3) (comp : Fin 4) (j l : ℕ), j ≤ r.scalars.degHigh →
    l ≤ r.scalars.degHigh → (n, a, comp, j, l) ∈ r.rows.farSupport
  far_kernel_dominates : ∀ u : (ℤ × Fin 3 × Fin 4 × ℕ × ℕ) ⊕ (Fin k ⊕ Fin k) → ℂ,
    CellScalars.farMajorantForm c r.box r.scalars r.far u
      ≤ (∑ i ∈ r.rows.farSupport.disjSum Finset.univ, ∑ i' ∈ r.rows.farSupport.disjSum Finset.univ,
          (starRingEnd ℂ) (u i) * r.rows.farKernel i i' * u i').re
  system_reducer_bound : ∀ w : Fin r.rows.reducerCount → ℝ,
    (r.systemReducer.transpose *ᵥ w) ⬝ᵥ (r.systemMultiplier *ᵥ (r.systemReducer.transpose *ᵥ w)) ≤ ∑ i, w i ^ 2
  given_symm : C.given.IsSymm
  layout_valid : IsPressureLayout c r.box r.scalars r.bases C.layout
  param_valid : IsCellParam C.layout C.param C.selection
  param_conj_closed : ∀ d, (d ∈ C.param.skeleton ↔ C.layout.conjDatum d ∈ C.param.skeleton) ∧
    (d ∈ C.param.solvedSet ↔ C.layout.conjDatum d ∈ C.param.solvedSet)
  row_side_degree : RD.degree ≤ C.layout.degSide
  skeleton_free : ∀ j i, ∑ l, C.Tmap j l * Sp.freeMap l i = 0
  far_low : r.rows.farSupport ⊆ lowSupport r.scalars
  matrix_embedding : ∀ w : Fin Sp.slots ⊕ Fin k → ℝ,
    quadValue (Sp.cellMatrix K₂) w ≤
      4 * Real.pi * c.splitVisc * quadValue C.given (C.restrictState c.splitVisc Sp.kappaSlot w)
  given_le_exact : ∀ (s : Fin (systemSkeletonCoords C.layout C.param).card → ℝ)
    (ξ : Fin (systemInteriorCoords C.layout C.param).card → ℝ) (κ' ζ' : Fin k → ℝ),
    quadValue C.given (Sum.elim s (Sum.elim κ' ζ')) ≤
      quadValue ((C.formula c r.box r.scalars r.bases r.classes r.rows α).exactFormula c r.box r.bases r.rows)
        (Sum.elim (fun i => expandedCoords C.layout C.param c.splitVisc s ξ (Sum.inl i))
          (Sum.elim (fun j => expandedCoords C.layout C.param c.splitVisc s ξ (Sum.inr j)) (Sum.elim κ' ζ')))

structure CellSystemCondition {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M) : Prop where
  given : IsGivenData c D A M MD RD
  inst : IsSystemInstance c D A M RD X
  base : IsBaseSystem (501 / 500) c.toFracCertData
  numbers : IsCellNumbers (501 / 500) c
  losses : IsReducedLosses c D A M RD X
  exterior : IsExteriorSystem (501 / 500) c M X
  spectral : IsSpectralSystem c X.spectral
  spectral_bounds : IsSpectralBounds X.spectral
  split : IsSplitSystem c X.split
  mesh : IsMeshData (501 / 500) c X.split X.mesh
  tree : IsTreeSystem c M X
  cells : ∀ K₂, IsCellSystemFacts (501 / 500) c M MD RD X.split K₂ (X.cell K₂) (X.mesh.coords K₂)

end CellSystem

end CellCert

end Breakdown

end
end
