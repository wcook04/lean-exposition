import Breakdown.CertCell.InstanceStatements
import Mathlib.RingTheory.Polynomial.Bernstein
import Breakdown.CertCell.StatementDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace ScalarShape

open CellCert.GivenFields (ChartParams IsChartParams chartT heightRatio Spline TensorMesh IsTensorMesh
  cellCount cellIndex atFirst atSecond tDeriv xDeriv)
open Instance (ChartScalar SplineJoins IsJoinedScalar IsConstantCore IsFlatAtOrigin HasNonnegValues StepDatum
  IsPositiveStep EpsGiven MuGiven WeightValues IsWeightValues IsFlipClosedValues)

def PlaneMinEvalFacts : Prop :=
  ∀ (P : ChartParams) (S : StepDatum), Measurable (planeMinEval P S) ∧ IsAxisymmetric (planeMinEval P S) ∧
    ∀ y : Space, planeMinEval P S.mirror (flipPoint y) = planeMinEval P S y

namespace ChartBound

def mirror (B : ChartBound) : ChartBound := ⟨B.data.mirror, B.tPower, B.originValue⟩

end ChartBound

def ChartBoundFacts : Prop :=
  ∀ (P : ChartParams) (B : ChartBound), Measurable (B.eval P) ∧ IsAxisymmetric (B.eval P) ∧
    ∀ y : Space, B.mirror.eval P (flipPoint y) = B.eval P y

structure Frac where
  num : ℤ
  den : ℕ

namespace Frac

def val (a : Frac) : ℚ := (a.num : ℚ) / (a.den : ℚ)

def ofInt (n : ℤ) : Frac := ⟨n, 1⟩

def add (a b : Frac) : Frac := ⟨a.num * b.den + b.num * a.den, a.den * b.den⟩

def mul (a b : Frac) : Frac := ⟨a.num * b.num, a.den * b.den⟩

def neg (a : Frac) : Frac := ⟨-a.num, a.den⟩

def sub (a b : Frac) : Frac := add a (neg b)

def pow (a : Frac) : ℕ → Frac
  | 0 => ofInt 1
  | n + 1 => mul (pow a n) a

def sum : List Frac → Frac
  | [] => ofInt 0
  | a :: l => add a (sum l)

end Frac

def fracAt (l : List Frac) (i : ℕ) (d : ℤ) : Frac := l.getD i (Frac.ofInt d)

structure RationalMesh where
  tBreaks : List Frac
  xBreaks : List Frac

namespace RationalMesh

def toMesh (M : RationalMesh) : TensorMesh :=
  ⟨M.tBreaks.map (fun b : Frac => ((b.val : ℚ) : ℝ)), M.xBreaks.map (fun b : Frac => ((b.val : ℚ) : ℝ))⟩

def IsValid (M : RationalMesh) : Prop :=
  (∀ b ∈ M.tBreaks, 0 < b.den) ∧ (∀ b ∈ M.xBreaks, 0 < b.den) ∧
    M.tBreaks.IsChain (fun a b : Frac => a.num * (b.den : ℤ) < b.num * (a.den : ℤ)) ∧
    M.xBreaks.IsChain (fun a b : Frac => a.num * (b.den : ℤ) < b.num * (a.den : ℤ)) ∧
    (M.tBreaks.head?.map Frac.num) = some 0 ∧ (M.xBreaks.head?.map Frac.num) = some 0 ∧
    (M.tBreaks.getLast?.map (fun b : Frac => b.num - b.den)) = some 0 ∧
    (M.xBreaks.getLast?.map (fun b : Frac => b.num - b.den)) = some 0

def tCount (M : RationalMesh) : ℕ := M.tBreaks.length - 1

def xCount (M : RationalMesh) : ℕ := M.xBreaks.length - 1

def tWidth (M : RationalMesh) (i : ℕ) : Frac := Frac.sub (fracAt M.tBreaks (i + 1) 1) (fracAt M.tBreaks i 0)

def xWidth (M : RationalMesh) (j : ℕ) : Frac := Frac.sub (fracAt M.xBreaks (j + 1) 1) (fracAt M.xBreaks j 0)

end RationalMesh

def cellBasisPoly (n ν : ℕ) (lo hi : ℚ) (v : Fin 2) : MvPolynomial (Fin 2) ℂ :=
  Polynomial.aeval (MvPolynomial.C (((hi - lo)⁻¹ : ℚ) : ℂ) * (MvPolynomial.X v - MvPolynomial.C ((lo : ℚ) : ℂ)))
    (bernsteinPolynomial ℂ n ν)

def coefAt (c : List (List Frac)) (a b : ℕ) : Frac := fracAt (c.getD a []) b 0

def cellPiecePoly (degT degX : ℕ) (tlo thi xlo xhi : ℚ) (c : List (List Frac)) : MvPolynomial (Fin 2) ℂ :=
  ∑ a ∈ Finset.range (degT + 1), ∑ b ∈ Finset.range (degX + 1),
    MvPolynomial.C (((coefAt c a b).val : ℚ) : ℂ) * cellBasisPoly degT a tlo thi 0 * cellBasisPoly degX b xlo xhi 1

def windowDiff (o : ℕ) (w : ℕ → Frac) : Frac :=
  Frac.sum ((List.range (o + 1)).map fun k =>
    Frac.mul (Frac.ofInt ((-1 : ℤ) ^ (o - k) * (Nat.choose o k : ℤ))) (w k))

def scaledDiff (o deg : ℕ) (w : ℕ → Frac) (h : Frac) : Frac :=
  Frac.mul (Frac.mul (windowDiff o w) (Frac.ofInt (Nat.descFactorial deg o : ℤ))) (Frac.pow h o)

def FracEq (a b : Frac) : Prop := a.num * (b.den : ℤ) = b.num * (a.den : ℤ)

instance (a b : Frac) : Decidable (FracEq a b) := by unfold FracEq; infer_instance

structure CoefficientHalf where
  mesh : RationalMesh
  degT : ℕ
  degX : ℕ
  coef : List (List (List (List Frac)))

namespace CoefficientHalf

variable (H : CoefficientHalf)

def cell (i j : ℕ) : List (List Frac) := (H.coef.getD i []).getD j []

def toSpline : Spline where
  mesh := H.mesh.toMesh
  piece i j := cellPiecePoly H.degT H.degX (fracAt H.mesh.tBreaks i 0).val (fracAt H.mesh.tBreaks (i + 1) 1).val
    (fracAt H.mesh.xBreaks j 0).val (fracAt H.mesh.xBreaks (j + 1) 1).val (H.cell i j)

def CoefDenPos : Prop :=
  ∀ i < H.mesh.tCount, ∀ j < H.mesh.xCount, ∀ a ≤ H.degT, ∀ b ≤ H.degX, 0 < (coefAt (H.cell i j) a b).den

def TJoins (a : ℕ) : Prop :=
  ∀ i < H.mesh.tCount, 1 ≤ i → ∀ j < H.mesh.xCount, ∀ o ≤ a, ∀ b ≤ H.degX,
    FracEq (scaledDiff o H.degT (fun k => coefAt (H.cell (i - 1) j) (H.degT - o + k) b) (H.mesh.tWidth i))
      (scaledDiff o H.degT (fun k => coefAt (H.cell i j) k b) (H.mesh.tWidth (i - 1)))

def XJoins (a : ℕ) : Prop :=
  ∀ j < H.mesh.xCount, 1 ≤ j → ∀ i < H.mesh.tCount, ∀ o ≤ a, ∀ t ≤ H.degT,
    FracEq (scaledDiff o H.degX (fun k => coefAt (H.cell i (j - 1)) t (H.degX - o + k)) (H.mesh.xWidth j))
      (scaledDiff o H.degX (fun k => coefAt (H.cell i j) t k) (H.mesh.xWidth (j - 1)))

def CoefNonneg : Prop :=
  ∀ i < H.mesh.tCount, ∀ j < H.mesh.xCount, ∀ a ≤ H.degT, ∀ b ≤ H.degX, 0 ≤ (coefAt (H.cell i j) a b).num

def CoefConstantBelow (tStar v : Frac) : Prop :=
  ∀ i < H.mesh.tCount,
    (fracAt H.mesh.tBreaks (i + 1) 1).num * (tStar.den : ℤ) ≤ tStar.num * ((fracAt H.mesh.tBreaks (i + 1) 1).den : ℤ) →
    ∀ j < H.mesh.xCount, ∀ a ≤ H.degT, ∀ b ≤ H.degX, FracEq (coefAt (H.cell i j) a b) v

def CoefFlatAtZero (v : Frac) : Prop :=
  ∀ j < H.mesh.xCount, ∀ b ≤ H.degX, FracEq (coefAt (H.cell 0 j) 0 b) v

instance (a : ℕ) : Decidable (H.TJoins a) := by unfold TJoins; infer_instance

instance (a : ℕ) : Decidable (H.XJoins a) := by unfold XJoins; infer_instance

instance : Decidable H.CoefNonneg := by unfold CoefNonneg; infer_instance

instance : Decidable H.CoefDenPos := by unfold CoefDenPos; infer_instance

instance (tStar v : Frac) : Decidable (H.CoefConstantBelow tStar v) := by unfold CoefConstantBelow; infer_instance

instance (v : Frac) : Decidable (H.CoefFlatAtZero v) := by unfold CoefFlatAtZero; infer_instance

end CoefficientHalf

instance (M : RationalMesh) : Decidable M.IsValid := by unfold RationalMesh.IsValid; infer_instance

structure CoefficientScalar where
  upper : CoefficientHalf
  lower : CoefficientHalf
  decay : ℕ

namespace CoefficientScalar

variable (B : CoefficientScalar)

def toChartScalar : ChartScalar := ⟨B.upper.toSpline, B.lower.toSpline, B.decay⟩

def mirror : CoefficientScalar := ⟨B.lower, B.upper, B.decay⟩

def PlaneJoins (a : ℕ) : Prop :=
  ∀ i < B.upper.mesh.tCount, ∀ o ≤ a, ∀ t ≤ B.upper.degT,
    FracEq (scaledDiff o B.upper.degX (fun k => coefAt (B.upper.cell i 0) t k) (B.lower.mesh.xWidth 0))
      (Frac.mul (Frac.ofInt ((-1 : ℤ) ^ o))
        (scaledDiff o B.lower.degX (fun k => coefAt (B.lower.cell i 0) t k) (B.upper.mesh.xWidth 0)))

instance (a : ℕ) : Decidable (B.PlaneJoins a) := by unfold PlaneJoins; infer_instance

structure JoinClauses (a : ℕ) : Prop where
  upper_den : B.upper.CoefDenPos
  lower_den : B.lower.CoefDenPos
  same_t : B.upper.mesh.tBreaks = B.lower.mesh.tBreaks
  same_degT : B.upper.degT = B.lower.degT
  same_degX : B.upper.degX = B.lower.degX
  upper_t : B.upper.TJoins a
  upper_x : B.upper.XJoins a
  lower_t : B.lower.TJoins a
  lower_x : B.lower.XJoins a
  plane : B.PlaneJoins a

def CoefNonneg : Prop := B.upper.CoefDenPos ∧ B.lower.CoefDenPos ∧ B.upper.CoefNonneg ∧ B.lower.CoefNonneg

def CoefConstantCore (tStar v : Frac) : Prop :=
  0 < tStar.den ∧ 0 < v.den ∧ 0 < tStar.num ∧
    (∃ i < B.upper.mesh.tBreaks.length, FracEq (fracAt B.upper.mesh.tBreaks i 0) tStar) ∧ B.upper.CoefDenPos ∧
    B.lower.CoefDenPos ∧ B.upper.CoefConstantBelow tStar v ∧ B.lower.CoefConstantBelow tStar v

def CoefFlat (v : Frac) : Prop :=
  0 < v.den ∧ B.upper.CoefDenPos ∧ B.lower.CoefDenPos ∧ B.upper.CoefFlatAtZero v ∧ B.lower.CoefFlatAtZero v

end CoefficientScalar

structure StepValues where
  mesh : RationalMesh
  upper : List (List Frac)
  lower : List (List Frac)
  decay : ℤ

namespace StepValues

variable (T : StepValues)

def toStepDatum : StepDatum :=
  ⟨T.mesh.toMesh, fun i j => (((coefAt T.upper i j).val : ℚ) : ℝ), fun i j => (((coefAt T.lower i j).val : ℚ) : ℝ),
    T.decay⟩

def mirror : StepValues := ⟨T.mesh, T.lower, T.upper, T.decay⟩

def EntriesPositive : Prop :=
  T.mesh.IsValid ∧ ∀ i < T.mesh.tCount, ∀ j < T.mesh.xCount,
    0 < (coefAt T.upper i j).den ∧ 0 < (coefAt T.upper i j).num ∧
      0 < (coefAt T.lower i j).den ∧ 0 < (coefAt T.lower i j).num

instance : Decidable T.EntriesPositive := by unfold EntriesPositive; infer_instance

end StepValues

def MeshOfRational : Prop :=
  ∀ M : RationalMesh, M.IsValid → IsTensorMesh M.toMesh

def JoinsOfCoefficients : Prop :=
  ∀ (a : ℕ) (B : CoefficientScalar), B.upper.mesh.IsValid → B.lower.mesh.IsValid → B.JoinClauses a →
    IsJoinedScalar a B.toChartScalar

def NonnegOfCoefficients : Prop :=
  ∀ B : CoefficientScalar, B.upper.mesh.IsValid → B.lower.mesh.IsValid → B.CoefNonneg →
    HasNonnegValues B.toChartScalar

def CoreOfCoefficients : Prop :=
  ∀ (B : CoefficientScalar) (tStar v : Frac), B.upper.mesh.IsValid → B.lower.mesh.IsValid →
    B.upper.mesh.tBreaks = B.lower.mesh.tBreaks → B.CoefConstantCore tStar v → IsConstantCore ((tStar.val : ℚ) : ℝ) B.toChartScalar

def FlatOfCoefficients : Prop :=
  ∀ (B : CoefficientScalar) (v : Frac), B.upper.mesh.IsValid → B.lower.mesh.IsValid → B.CoefFlat v →
    IsFlatAtOrigin B.toChartScalar

def StepPositiveOfEntries : Prop :=
  ∀ T : StepValues, T.EntriesPositive → IsPositiveStep T.toStepDatum

structure EpsValues where
  modes : Set (ℤ × ℤ)
  weight : CoefficientScalar
  share1 : StepValues
  share2 : StepValues
  len : StepValues
  t0 : StepValues
  t1 : StepValues
  t2 : StepValues
  t3 : StepValues
  scale : StepValues

structure MuValues where
  modes : Set (ℤ × ℤ)
  weight : CoefficientScalar
  share : StepValues
  t4 : StepValues
  eta : ℝ

def EpsValues.toGiven (e : EpsValues) : EpsGiven :=
  ⟨e.modes, e.weight.toChartScalar, e.share1.toStepDatum, e.share2.toStepDatum, e.len.toStepDatum,
    e.t0.toStepDatum, e.t1.toStepDatum, e.t2.toStepDatum, e.t3.toStepDatum, e.scale.toStepDatum⟩

def MuValues.toGiven (u : MuValues) : MuGiven :=
  ⟨u.modes, u.weight.toChartScalar, u.share.toStepDatum, u.t4.toStepDatum, u.eta⟩

def EpsValues.mirror (e : EpsValues) : EpsValues :=
  ⟨flipLabel '' e.modes, e.weight.mirror, e.share1.mirror, e.share2.mirror, e.len.mirror, e.t0.mirror,
    e.t1.mirror, e.t2.mirror, e.t3.mirror, e.scale.mirror⟩

def MuValues.mirror (u : MuValues) : MuValues :=
  ⟨flipLabel '' u.modes, u.weight.mirror, u.share.mirror, u.t4.mirror, u.eta⟩

structure RationalWeightValues (C : Type) (nE nM : ℕ) where
  chart : ChartParams
  centralRadius : Frac
  classOf : ℤ × ℤ → C
  strainWeight : C → CoefficientScalar
  vorticityWeight : C → CoefficientScalar
  eps : Fin nE → EpsValues
  mu : Fin nM → MuValues
  c : ℝ
  cμ : ℝ

namespace RationalWeightValues

variable {C : Type} {nE nM : ℕ} (W : RationalWeightValues C nE nM)

def toWeightValues : WeightValues C nE nM where
  chart := W.chart
  centralRadius := ((W.centralRadius.val : ℚ) : ℝ)
  classOf := W.classOf
  strainWeight c := (W.strainWeight c).toChartScalar
  vorticityWeight c := (W.vorticityWeight c).toChartScalar
  eps β := (W.eps β).toGiven
  mu β := (W.mu β).toGiven
  c := W.c
  cμ := W.cμ

end RationalWeightValues

def EpsValues.StepsPositive (e : EpsValues) : Prop :=
  e.share1.EntriesPositive ∧ e.share2.EntriesPositive ∧ e.len.EntriesPositive ∧ e.t0.EntriesPositive ∧
    e.t1.EntriesPositive ∧ e.t2.EntriesPositive ∧ e.t3.EntriesPositive ∧ e.scale.EntriesPositive

def MuValues.StepsPositive (u : MuValues) : Prop := u.share.EntriesPositive ∧ u.t4.EntriesPositive

structure WeightValuesShape {C : Type} {nE nM : ℕ} (W : RationalWeightValues C nE nM) : Prop where
  classes_finite : Finite C
  chart_valid : IsChartParams W.chart
  c_pos : 0 < W.c
  c_lt_one : W.c < 1
  cμ_pos : 0 < W.cμ
  cμ_lt_one : W.cμ < 1
  strain_meshes : ∀ c, (W.strainWeight c).upper.mesh.IsValid ∧ (W.strainWeight c).lower.mesh.IsValid
  vorticity_meshes : ∀ c, (W.vorticityWeight c).upper.mesh.IsValid ∧ (W.vorticityWeight c).lower.mesh.IsValid
  eps_meshes : ∀ β, (W.eps β).weight.upper.mesh.IsValid ∧ (W.eps β).weight.lower.mesh.IsValid
  mu_meshes : ∀ β, (W.mu β).weight.upper.mesh.IsValid ∧ (W.mu β).weight.lower.mesh.IsValid
  strain_decay : ∀ c, (W.strainWeight c).decay = 0
  vorticity_decay : ∀ c, (W.vorticityWeight c).decay = 0
  eps_decay : ∀ β, (W.eps β).weight.decay = 1
  mu_decay : ∀ β, (W.mu β).weight.decay = 2

structure WeightCoefficientsGiven {C : Type} {nE nM : ℕ} (W : RationalWeightValues C nE nM) : Prop where
  strain_joins_given : ∀ c, (W.strainWeight c).JoinClauses 2
  strain_core_given : ∀ c, ∃ v : Frac, (W.strainWeight c).CoefConstantCore W.centralRadius v
  strain_nonneg_given : ∀ c, (W.strainWeight c).CoefNonneg
  vorticity_joins_given : ∀ c, (W.vorticityWeight c).JoinClauses 2
  vorticity_core_given : ∀ c, ∃ v : Frac, (W.vorticityWeight c).CoefConstantCore W.centralRadius v
  eps_joins_given : ∀ β, (W.eps β).weight.JoinClauses 0
  eps_flat_given : ∀ β, ∃ v : Frac, (W.eps β).weight.CoefFlat v
  eps_nonneg_given : ∀ β, (W.eps β).weight.CoefNonneg
  eps_steps_given : ∀ β, (W.eps β).StepsPositive
  mu_joins_given : ∀ β, (W.mu β).weight.JoinClauses 0
  mu_flat_given : ∀ β, ∃ v : Frac, (W.mu β).weight.CoefFlat v
  mu_nonneg_given : ∀ β, (W.mu β).weight.CoefNonneg
  mu_steps_given : ∀ β, (W.mu β).StepsPositive
  mu_eta_given : ∀ β, 0 < (W.mu β).eta
  class_neg_given : ∀ ι, W.strainWeight (W.classOf (-ι)) = W.strainWeight (W.classOf ι) ∧
    W.vorticityWeight (W.classOf (-ι)) = W.vorticityWeight (W.classOf ι)

structure IsMirrorClosedRational {C : Type} {nE nM : ℕ} (W : RationalWeightValues C nE nM)
    (epsMirror : Equiv.Perm (Fin nE)) (muMirror : Equiv.Perm (Fin nM)) : Prop where
  strain_flip : ∀ ι, W.strainWeight (W.classOf (flipLabel ι)) = (W.strainWeight (W.classOf ι)).mirror
  vorticity_flip : ∀ ι, W.vorticityWeight (W.classOf (flipLabel ι)) = (W.vorticityWeight (W.classOf ι)).mirror
  eps_flip : ∀ β, W.eps (epsMirror β) = (W.eps β).mirror
  mu_flip : ∀ β, W.mu (muMirror β) = (W.mu β).mirror

theorem isWeightValues_of_conditions (hmesh : MeshOfRational) (hjoin : JoinsOfCoefficients)
    (hnn : NonnegOfCoefficients) (hcore : CoreOfCoefficients) (hflat : FlatOfCoefficients)
    (hstep : StepPositiveOfEntries) {C : Type} {nE nM : ℕ} (W : RationalWeightValues C nE nM)
    (hshape : WeightValuesShape W) (hsystem : WeightCoefficientsGiven W) : IsWeightValues W.toWeightValues := by
  exact
    { classes_finite := hshape.classes_finite
      chart_valid := hshape.chart_valid
      c_pos := hshape.c_pos
      c_lt_one := hshape.c_lt_one
      cμ_pos := hshape.cμ_pos
      cμ_lt_one := hshape.cμ_lt_one
      strain_joined := fun c =>
        hjoin _ _ (hshape.strain_meshes c).1 (hshape.strain_meshes c).2 (hsystem.strain_joins_given c)
      strain_core := fun c =>
        (hsystem.strain_core_given c).elim fun v hv =>
          hcore _ _ v (hshape.strain_meshes c).1 (hshape.strain_meshes c).2
            (hsystem.strain_joins_given c).same_t hv
      strain_decay := fun c => hshape.strain_decay c
      strain_nonneg := fun c =>
        hnn _ (hshape.strain_meshes c).1 (hshape.strain_meshes c).2 (hsystem.strain_nonneg_given c)
      vorticity_joined := fun c =>
        hjoin _ _ (hshape.vorticity_meshes c).1 (hshape.vorticity_meshes c).2 (hsystem.vorticity_joins_given c)
      vorticity_core := fun c =>
        (hsystem.vorticity_core_given c).elim fun v hv =>
          hcore _ _ v (hshape.vorticity_meshes c).1 (hshape.vorticity_meshes c).2
            (hsystem.vorticity_joins_given c).same_t hv
      vorticity_decay := fun c => hshape.vorticity_decay c
      eps_joined := fun β =>
        hjoin _ _ (hshape.eps_meshes β).1 (hshape.eps_meshes β).2 (hsystem.eps_joins_given β)
      eps_flat := fun β =>
        (hsystem.eps_flat_given β).elim fun v hv =>
          hflat _ v (hshape.eps_meshes β).1 (hshape.eps_meshes β).2 hv
      eps_decay := fun β => hshape.eps_decay β
      eps_nonneg := fun β =>
        hnn _ (hshape.eps_meshes β).1 (hshape.eps_meshes β).2 (hsystem.eps_nonneg_given β)
      eps_steps := fun β => by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hsystem.eps_steps_given β
        exact ⟨hstep _ h1, hstep _ h2, hstep _ h3, hstep _ h4, hstep _ h5, hstep _ h6, hstep _ h7, hstep _ h8⟩
      mu_joined := fun β =>
        hjoin _ _ (hshape.mu_meshes β).1 (hshape.mu_meshes β).2 (hsystem.mu_joins_given β)
      mu_flat := fun β =>
        (hsystem.mu_flat_given β).elim fun v hv =>
          hflat _ v (hshape.mu_meshes β).1 (hshape.mu_meshes β).2 hv
      mu_decay := fun β => hshape.mu_decay β
      mu_nonneg := fun β =>
        hnn _ (hshape.mu_meshes β).1 (hshape.mu_meshes β).2 (hsystem.mu_nonneg_given β)
      mu_steps := fun β => by
        obtain ⟨h1, h2⟩ := hsystem.mu_steps_given β
        exact ⟨hstep _ h1, hstep _ h2⟩
      mu_eta_pos := fun β => hsystem.mu_eta_given β
      class_neg := fun ι => by
        obtain ⟨h1, h2⟩ := hsystem.class_neg_given ι
        exact ⟨congrArg CoefficientScalar.toChartScalar h1, congrArg CoefficientScalar.toChartScalar h2⟩ }

theorem isFlipClosed_of_rational {C : Type} {nE nM : ℕ} (W : RationalWeightValues C nE nM)
    (epsMirror : Equiv.Perm (Fin nE)) (muMirror : Equiv.Perm (Fin nM))
    (h : IsMirrorClosedRational W epsMirror muMirror) : IsFlipClosedValues W.toWeightValues epsMirror muMirror := by
  exact
    { strain_flip := fun ι => by
        show (W.strainWeight (W.classOf (flipLabel ι))).toChartScalar = _
        rw [h.strain_flip ι]
        rfl
      vorticity_flip := fun ι => by
        show (W.vorticityWeight (W.classOf (flipLabel ι))).toChartScalar = _
        rw [h.vorticity_flip ι]
        rfl
      eps_flip := fun β => by
        show (W.eps (epsMirror β)).toGiven = _
        rw [h.eps_flip β]
        rfl
      mu_flip := fun β => by
        show (W.mu (muMirror β)).toGiven = _
        rw [h.mu_flip β]
        rfl }

structure BoundValueSetsMirrorClosed (T : BoundValues) : Prop where
  harmonics_flip : ∀ β ∈ T.harmonics, flipLabel β ∈ T.harmonics
  ampW_flip : ∀ β, T.ampW (flipLabel β) = (T.ampW β).mirror
  ampGradW_flip : ∀ β, T.ampGradW (flipLabel β) = (T.ampGradW β).mirror
  ampVort_flip : ∀ β, T.ampVort (flipLabel β) = (T.ampVort β).mirror
  ampGradVort_flip : ∀ β, T.ampGradVort (flipLabel β) = (T.ampGradVort β).mirror
  supVort_even : T.supVort.mirror = T.supVort
  supGradVort_even : T.supGradVort.mirror = T.supGradVort

structure BoundValuesFlipFacts (h : HarmonicBounds) : Prop where
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

theorem boundValuesFlipFacts_of_mirror (hcb : ChartBoundFacts) (T : BoundValues) (hT : BoundValueSetsMirrorClosed T) :
    BoundValuesFlipFacts T.bounds := by
  have hflip : ∀ (B : ℤ × ℤ → ChartBound), (∀ β, B (flipLabel β) = (B β).mirror) →
      ∀ β y, (B (flipLabel β)).eval T.chart (flipPoint y) = (B β).eval T.chart y := by
    intro B hB β y
    rw [hB β]
    exact (hcb T.chart (B β)).2.2 y
  have heven : ∀ B : ChartBound, B.mirror = B → ∀ y, B.eval T.chart (flipPoint y) = B.eval T.chart y := by
    intro B hB y
    have h := (hcb T.chart B).2.2 y
    rw [hB] at h
    exact h
  refine ⟨hT.harmonics_flip, ?_, ?_, ?_, ?_⟩
  · intro β y
    exact ⟨hflip T.ampW hT.ampW_flip β y, hflip T.ampGradW hT.ampGradW_flip β y,
      hflip T.ampVort hT.ampVort_flip β y, hflip T.ampGradVort hT.ampGradVort_flip β y⟩
  · intro y
    exact ⟨heven T.supVort hT.supVort_even y, heven T.supGradVort hT.supGradVort_even y⟩
  · intro β φ y
    exact ⟨(hcb T.chart (T.ampW β)).2.1 φ y, (hcb T.chart (T.ampGradW β)).2.1 φ y,
      (hcb T.chart (T.ampVort β)).2.1 φ y, (hcb T.chart (T.ampGradVort β)).2.1 φ y⟩
  · intro φ y
    exact ⟨(hcb T.chart T.supVort).2.1 φ y, (hcb T.chart T.supGradVort).2.1 φ y⟩

theorem speedFacts_of_values (hcb : ChartBoundFacts) (P : ChartParams) {n : ℕ} (speed : Fin n → ChartBound)
    (mirrorPerm : Equiv.Perm (Fin n)) (speed_mirror : ∀ β, speed (mirrorPerm β) = (speed β).mirror) :
    (∀ β, IsAxisymmetric ((speed β).eval P)) ∧
      ∀ β y, (speed (mirrorPerm β)).eval P (flipPoint y) = (speed β).eval P y := by
  refine ⟨fun β => (hcb P (speed β)).2.1, ?_⟩
  intro β y
  rw [speed_mirror β]
  exact (hcb P (speed β)).2.2 y

end ScalarShape

end CertCell

end Breakdown
