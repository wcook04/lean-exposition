/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorFullFieldSeeds

/-!
# Executable field operations used by verifier queries

Finite products compute interpolation weights and grid recovery points directly.
The transpose of multiplication computes weighted binary labels coefficientwise.
The seed decoder decides precisely four nonzero tests. The equalities below tie
these algorithms to the semantic verifier without any polynomial construction at
runtime. Machine-level cost certificates remain separate.
-/

namespace PCP.Algebraic.FieldQueryArithmetic

open Finset BinaryPolynomialSpace

variable {F : Type*} [Field F] {c m n t : ℕ}

/-- Compute one interpolation weight using its finite product formula. -/
def interpolationWeight (a : Fin (c + 1) → F) (z : F) (i : Fin (c + 1)) : F :=
  ∏ j ∈ univ.erase i, (z - a j) / (a i - a j)

@[simp] theorem interpolationWeight_eq (a : Fin (c + 1) → F) (z : F)
    (i : Fin (c + 1)) : interpolationWeight a z i = LagrangeConstraint.weight a z i :=
  (LagrangeConstraint.weight_eq_prod a z i).symm

/-- Evaluate the grid-vanishing factor in each coordinate. -/
def recoveryPoint (H : Finset F) (x : Fin n → F) : (Fin n ⊕ Fin n) → F :=
  Sum.elim x (fun i => ∏ a ∈ H, (x i - a))

@[simp] theorem recoveryPoint_eq (H : Finset F) (x : Fin n → F) :
    recoveryPoint H x = BinaryZeroOnGrid.recoveryPoint H x := by
  funext i
  cases i with
  | inl i => rfl
  | inr i => exact (GridVanishing.eval_coordinate H i x).symm

section Coordinates

variable [Algebra (ZMod 2) F]

/-- The transpose of field multiplication, evaluated on binary basis vectors. -/
def scaleLabel (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a : F)
    (w : Fin t → ZMod 2) : Fin t → ZMod 2 :=
  fun i => ∑ j, ρ (a * ρ.symm (Pi.single i 1)) j * w j

@[simp] theorem scaleLabel_eq (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a : F)
    (w : Fin t → ZMod 2) : scaleLabel ρ a w = HadamardWeights.scaleLabel ρ a w := by
  funext i
  simp only [scaleLabel, HadamardWeights.scaleLabel, HadamardWeights.pullbackLabel,
    HadamardWeights.coordinateScale_apply, Hadamard.linearEncode_apply,
    LinearMap.coe_mk, AddHom.coe_mk]

end Coordinates

section Grid

variable {σ : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq F]

/-- Evaluate one tensor Lagrange basis element without constructing a polynomial. -/
def gridBasis (H : Finset F) (a : σ → H) (x : σ → F) : F :=
  ∏ i, ∏ b ∈ H.erase (a i : F), (x i - b) / ((a i : F) - b)

omit [DecidableEq σ] in
@[simp] theorem gridBasis_eq (H : Finset F) (a : σ → H) (x : σ → F) :
    gridBasis H a x = MvPolynomial.eval x (GridInterpolation.basis H a) := by
  simp only [gridBasis, GridInterpolation.basis, map_prod, MvPolynomial.eval_toMvPolynomial,
    Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X, id_eq,
    div_eq_mul_inv, mul_comm]

/-- Evaluate a table's low-degree extension by a finite tensor interpolation sum. -/
def gridInterpolate (H : Finset F) (f : (σ → H) → F) (x : σ → F) : F :=
  ∑ a : σ → H, f a * gridBasis H a x

@[simp] theorem gridInterpolate_eq (H : Finset F) (f : (σ → H) → F) (x : σ → F) :
    gridInterpolate H f x = MvPolynomial.eval x (GridInterpolation.interpolate H f) := by
  simp only [gridInterpolate, GridInterpolation.interpolate_apply, map_sum,
    MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, gridBasis_eq]

/-- Public adjacency evaluation uses only the graph's decidable edge relation. -/
def edgeValue (H : Finset F) (G : SimpleGraph (Fin n → H)) [DecidableRel G.Adj]
    (x : Fin (n + n) → F) : F :=
  gridInterpolate H (fun a : (Fin n ⊕ Fin n) → H =>
    if G.Adj (fun i => a (Sum.inl i)) (fun i => a (Sum.inr i)) then 1 else 0)
    (x ∘ ThreeColorVerifier.flatten n)

@[simp] theorem edgeValue_eq (H : Finset F) (G : SimpleGraph (Fin n → H))
    [DecidableRel G.Adj] (x : Fin (n + n) → F) :
    edgeValue H G x = ThreeColorVerifier.edgeValue H G x := by
  classical
  simp only [edgeValue, gridInterpolate_eq, ThreeColorVerifier.edgeValue,
    ThreeColorGrid.edgeExtension]
  congr 10 <;> first | rfl | exact Subsingleton.elim _ _ | (funext a; split_ifs <;> rfl)

end Grid

/-- Decide the validity event using just the four whole-field correction parameters. -/
def validSeed [DecidableEq F]
    (s : ThreeColorFullFieldSampling.RawSample F n m c t) : Bool :=
  decide ((s 4).2.1.2.1.2.1 ≠ 0 ∧ (s 4).2.1.2.2.2.1 ≠ 0 ∧
    (s 5).2.1.2.1.2.1 ≠ 0 ∧ (s 5).2.1.2.2.2.1 ≠ 0)

@[simp] theorem validSeed_eq_true [DecidableEq F]
    (s : ThreeColorFullFieldSampling.RawSample F n m c t) :
    validSeed s = true ↔ ThreeColorFullFieldSampling.Valid s := by
  simp only [validSeed, decide_eq_true_eq, ThreeColorFullFieldSampling.valid_iff]

/-- Recover the original seed or accept the zero-parameter case immediately. -/
def decodeSeed [DecidableEq F]
    (s : ThreeColorFullFieldSampling.RawSample F n m c t) :
    Option (ThreeColorVerifier.Sample F n m c t) :=
  if h : validSeed s = true then
    some (ThreeColorFullFieldSampling.unpad s ((validSeed_eq_true s).mp h))
  else none

@[simp] theorem decodeSeed_eq [DecidableEq F]
    (s : ThreeColorFullFieldSampling.RawSample F n m c t) :
    decodeSeed s = ThreeColorFullFieldSampling.decode s := by
  classical
  by_cases h : ThreeColorFullFieldSampling.Valid s
  · simp [decodeSeed, (validSeed_eq_true s).mpr h, ThreeColorFullFieldSampling.decode, h]
  · have hn : validSeed s ≠ true := fun hs => h ((validSeed_eq_true s).mp hs)
    simp [decodeSeed, hn, ThreeColorFullFieldSampling.decode, h]

end PCP.Algebraic.FieldQueryArithmetic
