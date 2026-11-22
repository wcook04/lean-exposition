/-
The eigenspace spanning and support-kernel arguments are adapted from
complexitylib, Copyright (c) 2026 Samuel Schlesinger, Apache-2.0.
-/

module

public import QuarticQuery.Statement
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
import all Mathlib.Basic.Real.Basic

/-!
# Appendix A: the literal recursive signed cube

Compiled as part of the `QuarticQuery` library target.

`HuangVertex d` is the recursive binary-word presentation of the `d`-cube.
Splitting on the first bit gives precisely the block recursion in Appendix A.
The harmless zero-dimensional starting matrix is zero on a singleton; the
one-dimensional matrix has zero diagonal and two off-diagonal entries equal to
one. All multiplicity and positive-eigenvector assertions explicitly assume
`0 < d`.

These declarations expose the literal signed-matrix, spectrum and supported
positive-eigenvector statements. `AppendixAHuangRoute.lean` connects these
recursively indexed vertices to the genuine restricted face and the original
sensitivity graph. `AppendixAHuang.lean` separately retains the alternative
full-cube directional proof from complexitylib.
-/

@[expose] public section

namespace QuarticQuery.Paper

open Finset Function Module
open scoped Matrix

/-- Ledger: def-huang. Binary words presented recursively by their first bit. -/
def HuangVertex : ℕ → Type
  | 0 => Unit
  | d + 1 => HuangVertex d ⊕ HuangVertex d

/-- Ledger: def-huang. The recursive finite enumeration of binary words. -/
instance huangVertexFintype : (d : ℕ) → Fintype (HuangVertex d)
  | 0 => inferInstanceAs (Fintype Unit)
  | d + 1 => by
      letI := huangVertexFintype d
      exact inferInstanceAs (Fintype (HuangVertex d ⊕ HuangVertex d))

/-- Ledger: def-huang. Equality of recursive binary words is decidable. -/
instance huangVertexDecidableEq : (d : ℕ) → DecidableEq (HuangVertex d)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | d + 1 => by
      letI := huangVertexDecidableEq d
      exact inferInstanceAs (DecidableEq (HuangVertex d ⊕ HuangVertex d))

/-- Ledger: def-huang. The `d`-cube has `2^d` vertices. -/
theorem huangVertex_card (d : ℕ) : Fintype.card (HuangVertex d) = 2 ^ d := by
  induction d with
  | zero =>
    letI : Unique (HuangVertex 0) := inferInstanceAs (Unique Unit)
    simpa only [pow_zero] using (Fintype.card_unique (α := HuangVertex 0))
  | succ d ih =>
    change Fintype.card (HuangVertex d ⊕ HuangVertex d) = 2 ^ (d + 1)
    rw [Fintype.card_sum, ih, pow_succ]
    omega

/-- Ledger: def-huang. Read the recursive word as the paper's bit input. -/
def huangVertexInput : (d : ℕ) → HuangVertex d → BitInput (Fin d)
  | 0, _ => fun i => Fin.elim0 i
  | d + 1, Sum.inl x => Fin.cases false (huangVertexInput d x)
  | d + 1, Sum.inr x => Fin.cases true (huangVertexInput d x)

/-- Ledger: def-huang. Split a bit input into its first bit and its tail. -/
def huangInputVertex : (d : ℕ) → BitInput (Fin d) → HuangVertex d
  | 0, _ => ()
  | d + 1, x =>
      if x 0 then Sum.inr (huangInputVertex d fun i => x i.succ)
      else Sum.inl (huangInputVertex d fun i => x i.succ)

/-- Ledger: def-huang. Reading and splitting a recursive word are inverse. -/
theorem huangInputVertex_vertexInput (d : ℕ) (x : HuangVertex d) :
    huangInputVertex d (huangVertexInput d x) = x := by
  induction d with
  | zero => cases x; rfl
  | succ d ih => cases x <;> simp [huangInputVertex, huangVertexInput, ih] <;> rfl

/-- Ledger: def-huang. Splitting and reading a bit input are inverse. -/
theorem huangVertexInput_inputVertex (d : ℕ) (x : BitInput (Fin d)) :
    huangVertexInput d (huangInputVertex d x) = x := by
  induction d with
  | zero => funext i; exact Fin.elim0 i
  | succ d ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · cases hx : x 0 <;> simp [huangInputVertex, huangVertexInput, hx]
    · cases hx : x 0 <;> simp [huangInputVertex, huangVertexInput, hx, ih]

/-- Ledger: def-huang. The recursive indexing is equivalent to `Fin d → Bool`. -/
def huangVertexEquivInput (d : ℕ) : HuangVertex d ≃ BitInput (Fin d) where
  toFun := huangVertexInput d
  invFun := huangInputVertex d
  left_inv := huangInputVertex_vertexInput d
  right_inv := huangVertexInput_inputVertex d

/-- Ledger: def-huang. Equality is preserved and reflected by the cube indexing. -/
theorem huangVertexInput_inj (d : ℕ) (x y : HuangVertex d) :
    huangVertexInput d x = huangVertexInput d y ↔ x = y :=
  (huangVertexEquivInput d).injective.eq_iff

/-- Ledger: def-huang. Two standard bit inputs differ in exactly one coordinate. -/
def appendixACubeEdge {d : ℕ} (x y : BitInput (Fin d)) : Prop :=
  ∃ i, x i ≠ y i ∧ ∀ j, j ≠ i → x j = y j

/-- Ledger: def-huang. The one-coordinate relation is exactly a bit flip. -/
theorem appendixACubeEdge_iff_update {d : ℕ} (x y : BitInput (Fin d)) :
    appendixACubeEdge x y ↔ ∃ i, update x i (!(x i)) = y := by
  constructor
  · rintro ⟨i, hi, hrest⟩
    have hbit : (!(x i)) = y i := Bool.not_eq_iff.2 hi
    refine ⟨i, funext fun j => ?_⟩
    by_cases hji : j = i
    · subst j
      simpa only [update_self] using hbit
    · rw [update_of_ne hji]
      exact hrest j hji
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_, fun j hji => ?_⟩
    · have hbit := congrFun hi i
      simp only [update_self] at hbit
      rw [← hbit]
      cases x i <;> decide
    · rw [← hi, update_of_ne hji]

/-- Ledger: def-huang. Splitting the first coordinate gives the cube recursion. -/
theorem appendixACubeEdge_cons {d : ℕ} (b c : Bool)
    (x y : BitInput (Fin d)) :
    appendixACubeEdge (Fin.cases b x) (Fin.cases c y) ↔
      (b = c ∧ appendixACubeEdge x y) ∨ (b ≠ c ∧ x = y) := by
  constructor
  · rintro ⟨i, hi, hrest⟩
    revert hi hrest
    refine Fin.cases ?_ (fun i => ?_) i
    · intro hi hrest
      right
      refine ⟨by simpa using hi, funext fun j => ?_⟩
      exact hrest j.succ (Fin.succ_ne_zero j)
    · intro hi hrest
      left
      refine ⟨hrest 0 (Fin.succ_ne_zero i).symm, i, by simpa using hi, ?_⟩
      intro j hji
      exact hrest j.succ (fun h => hji (Fin.succ_injective d h))
  · rintro (⟨hbc, i, hi, hrest⟩ | ⟨hbc, hxy⟩)
    · refine ⟨i.succ, by simpa using hi, ?_⟩
      intro j
      refine Fin.cases ?_ (fun j hji => ?_) j
      · intro _
        exact hbc
      · exact hrest j (fun h => hji (congrArg Fin.succ h))
    · subst y
      refine ⟨0, by simpa using hbc, ?_⟩
      intro j
      refine Fin.cases ?_ (fun _ _ => rfl) j
      intro h
      exact (h rfl).elim

/-- Ledger: def-huang. Hypercube adjacency on recursive words: equal leading
bits require adjacent tails; different leading bits require identical tails. -/
def huangAdjacent : (d : ℕ) → HuangVertex d → HuangVertex d → Prop
  | 0, _, _ => False
  | d + 1, Sum.inl x, Sum.inl y => huangAdjacent d x y
  | d + 1, Sum.inr x, Sum.inr y => huangAdjacent d x y
  | _ + 1, Sum.inl x, Sum.inr y => x = y
  | _ + 1, Sum.inr x, Sum.inl y => x = y

/-- Ledger: def-huang. The adjacency relation has a classical decision procedure. -/
noncomputable instance huangAdjacentDecidable (d : ℕ) :
    DecidableRel (huangAdjacent d) := fun x y => Classical.propDecidable _

/-- Ledger: def-huang. Recursive adjacency is the standard bit-cube relation
under the explicit indexing equivalence. -/
theorem huangAdjacent_iff_cubeEdge (d : ℕ) (x y : HuangVertex d) :
    huangAdjacent d x y ↔
      appendixACubeEdge (huangVertexInput d x) (huangVertexInput d y) := by
  induction d with
  | zero => simp [huangAdjacent, appendixACubeEdge]
  | succ d ih =>
    cases x <;> cases y <;>
      simp [huangAdjacent, huangVertexInput, appendixACubeEdge_cons,
        huangVertexInput_inj, ih]

/-- Ledger: def-huang. The paper's recursion, extended by `H'_0 = 0`. -/
def huangMatrix : (d : ℕ) → Matrix (HuangVertex d) (HuangVertex d) ℝ
  | 0 => 0
  | d + 1 => Matrix.fromBlocks (huangMatrix d) 1 1 (-(huangMatrix d))

/-- Ledger: def-huang. The initial one-dimensional matrix is `[[0,1],[1,0]]`. -/
theorem huangMatrix_one :
    huangMatrix 1 = Matrix.fromBlocks (0 : Matrix Unit Unit ℝ)
      (1 : Matrix Unit Unit ℝ) (1 : Matrix Unit Unit ℝ) (0 : Matrix Unit Unit ℝ) := by
  simp [huangMatrix] <;> rfl

/-- Ledger: def-huang. The ordinary cube adjacency has the same two copies
on its diagonal blocks and the coordinate matching on the off-diagonal blocks. -/
def huangCubeMatrix : (d : ℕ) → Matrix (HuangVertex d) (HuangVertex d) ℝ
  | 0 => 0
  | d + 1 => Matrix.fromBlocks (huangCubeMatrix d) 1 1 (huangCubeMatrix d)

/-- Ledger: def-huang. The unsigned matrix is exactly the indicator of
one-coordinate adjacency on recursively indexed binary words. -/
theorem huangCubeMatrix_eq_ite (d : ℕ) (x y : HuangVertex d) :
    huangCubeMatrix d x y = if huangAdjacent d x y then 1 else 0 := by
  classical
  induction d with
  | zero => simp [huangCubeMatrix, huangAdjacent]
  | succ d ih =>
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        change huangCubeMatrix d x y = if huangAdjacent d x y then 1 else 0
        exact ih x y
      | inr y =>
        by_cases hxy : x = y <;>
          simp [huangCubeMatrix, huangAdjacent, Matrix.fromBlocks, Matrix.one_apply, hxy]
    | inr x =>
      cases y with
      | inl y =>
        by_cases hxy : x = y <;>
          simp [huangCubeMatrix, huangAdjacent, Matrix.fromBlocks, Matrix.one_apply, hxy]
      | inr y =>
        change huangCubeMatrix d x y = if huangAdjacent d x y then 1 else 0
        exact ih x y

/-- Ledger: def-huang. Entrywise absolute values give the unsigned cube. -/
theorem abs_huangMatrix (d : ℕ) (x y : HuangVertex d) :
    |huangMatrix d x y| = huangCubeMatrix d x y := by
  induction d with
  | zero => simp [huangMatrix, huangCubeMatrix]
  | succ d ih =>
    cases x <;> cases y <;>
      simp [huangMatrix, huangCubeMatrix, Matrix.fromBlocks, Matrix.one_apply, ih] <;>
      split_ifs <;> norm_num

/-- Ledger: claim-huang-spectrum. The matrix is real symmetric. -/
theorem huangMatrix_transpose (d : ℕ) : (huangMatrix d)ᵀ = huangMatrix d := by
  induction d with
  | zero => simp [huangMatrix]
  | succ d ih =>
    change (Matrix.fromBlocks (huangMatrix d) 1 1 (-(huangMatrix d)))ᵀ =
      Matrix.fromBlocks (huangMatrix d) 1 1 (-(huangMatrix d))
    simp only [Matrix.fromBlocks_transpose, Matrix.transpose_one,
      Matrix.transpose_neg, ih]

/-- Ledger: claim-huang-spectrum. The block recursion squares to `d I`. -/
theorem huangMatrix_square (d : ℕ) :
    huangMatrix d * huangMatrix d = (d : ℝ) • (1 : Matrix (HuangVertex d) _ ℝ) := by
  induction d with
  | zero => simp [huangMatrix]
  | succ d ih =>
    change Matrix.fromBlocks (huangMatrix d) 1 1 (-(huangMatrix d)) *
      Matrix.fromBlocks (huangMatrix d) 1 1 (-(huangMatrix d)) =
      ((d + 1 : ℕ) : ℝ) • (1 : Matrix (HuangVertex d ⊕ HuangVertex d) _ ℝ)
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul,
      neg_neg, ih, add_neg_cancel, neg_add_cancel]
    ext x y
    cases x <;> cases y <;>
      simp [Matrix.fromBlocks, Matrix.one_apply, Nat.cast_add, Nat.cast_one] <;>
      split_ifs <;> ring

/-- Ledger: claim-huang-spectrum. The recursive matrix has zero trace. -/
theorem huangMatrix_trace (d : ℕ) : Matrix.trace (huangMatrix d) = 0 := by
  cases d with
  | zero => simp [huangMatrix]
  | succ d =>
    change (∑ x : HuangVertex d ⊕ HuangVertex d,
      Matrix.fromBlocks (huangMatrix d) 1 1 (-(huangMatrix d)) x x) = 0
    rw [Fintype.sum_sum_type]
    simp

/-- Ledger: claim-huang-spectrum. The signed matrix acting on real vectors. -/
noncomputable def huangEnd (d : ℕ) : Module.End ℝ (HuangVertex d → ℝ) :=
  (huangMatrix d).mulVecLin

/-- Ledger: claim-huang-spectrum. The operator form of the square identity. -/
theorem huangEnd_square (d : ℕ) (v : HuangVertex d → ℝ) :
    huangEnd d (huangEnd d v) = (d : ℝ) • v := by
  change huangMatrix d *ᵥ (huangMatrix d *ᵥ v) = _
  rw [Matrix.mulVec_mulVec, huangMatrix_square]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec]

/-- Ledger: claim-huang-spectrum. Every real eigenvalue is one of the two
square roots of `d`; the statement also handles `d = 0`. -/
theorem huangEnd_eigenvalue (d : ℕ) (μ : ℝ) (v : HuangVertex d → ℝ)
    (hv0 : v ≠ 0) (hv : huangEnd d v = μ • v) :
    μ = √(d : ℝ) ∨ μ = -√(d : ℝ) := by
  have hAA := huangEnd_square d v
  rw [hv, map_smul, hv, smul_smul] at hAA
  have hz : (μ * μ - (d : ℝ)) • v = 0 := by
    rw [sub_smul, hAA, sub_self]
  have hμ : μ * μ = (d : ℝ) :=
    sub_eq_zero.1 ((smul_eq_zero.1 hz).resolve_right hv0)
  have hfactor : (μ - √(d : ℝ)) * (μ + √(d : ℝ)) = 0 := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg d)]
  rcases mul_eq_zero.1 hfactor with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · right
    linarith

/-- Ledger: claim-huang-spectrum. The sign of a binary word's parity. -/
def huangParity : (d : ℕ) → HuangVertex d → ℝ
  | 0, _ => 1
  | d + 1, Sum.inl x => huangParity d x
  | d + 1, Sum.inr x => -huangParity d x

/-- Ledger: claim-huang-spectrum. Squaring a parity sign gives one. -/
theorem huangParity_square (d : ℕ) (x : HuangVertex d) :
    huangParity d x * huangParity d x = 1 := by
  induction d with
  | zero => simp [huangParity]
  | succ d ih => cases x <;> simp [huangParity, ih]

/-- Ledger: claim-huang-spectrum. Every signed cube edge joins opposite parities. -/
theorem huangParity_matrix (d : ℕ) (x y : HuangVertex d) :
    huangMatrix d x y * huangParity d y =
      -(huangParity d x * huangMatrix d x y) := by
  induction d with
  | zero => simp [huangMatrix]
  | succ d ih =>
    cases x with
    | inl x =>
      cases y with
      | inl y => simpa [huangMatrix, Matrix.fromBlocks, huangParity] using ih x y
      | inr y =>
        by_cases hxy : x = y <;>
          simp [huangMatrix, Matrix.fromBlocks, Matrix.one_apply, huangParity, hxy]
    | inr x =>
      cases y with
      | inl y =>
        by_cases hxy : x = y <;>
          simp [huangMatrix, Matrix.fromBlocks, Matrix.one_apply, huangParity, hxy]
      | inr y =>
        simpa [huangMatrix, Matrix.fromBlocks, huangParity] using ih x y

/-- Ledger: claim-huang-spectrum. Multiplication by the parity signs. -/
def huangParityEnd (d : ℕ) : Module.End ℝ (HuangVertex d → ℝ) where
  toFun v x := huangParity d x * v x
  map_add' v w := by ext x; simp [mul_add]
  map_smul' c v := by ext x; simp [mul_left_comm]

/-- Ledger: claim-huang-spectrum. Parity multiplication is an involution. -/
theorem huangParityEnd_involutive (d : ℕ) :
    Function.Involutive (huangParityEnd d) := by
  intro v
  ext x
  change huangParity d x * (huangParity d x * v x) = v x
  rw [← mul_assoc, huangParity_square, one_mul]

/-- Ledger: claim-huang-spectrum. Parity interchanges the positive and negative
eigenspaces. This replaces the trace count by an explicit linear symmetry. -/
theorem huangEnd_parity (d : ℕ) (v : HuangVertex d → ℝ) :
    huangEnd d (huangParityEnd d v) = -huangParityEnd d (huangEnd d v) := by
  ext x
  change (∑ y, huangMatrix d x y * (huangParity d y * v y)) =
    -(huangParity d x * ∑ y, huangMatrix d x y * v y)
  rw [mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun y _ => ?_
  rw [← mul_assoc, huangParity_matrix]
  ring

/-- Ledger: claim-huang-spectrum. The two eigenspaces span every vector when
the cube dimension is positive. -/
theorem huangEnd_eigenspaces_sup (d : ℕ) (hd : 0 < d) :
    (huangEnd d).eigenspace √(d : ℝ) ⊔
      (huangEnd d).eigenspace (-√(d : ℝ)) = ⊤ := by
  set A := huangEnd d
  set c : ℝ := √(d : ℝ)
  have hc : c * c = d := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hc0 : c ≠ 0 := Real.sqrt_ne_zero'.2 (by exact_mod_cast hd)
  refine eq_top_iff.2 fun v _ => ?_
  have hplus : A v + c • v ∈ A.eigenspace c := by
    rw [Module.End.mem_eigenspace_iff, map_add, map_smul, huangEnd_square, ← hc]
    module
  have hminus : A v - c • v ∈ A.eigenspace (-c) := by
    rw [Module.End.mem_eigenspace_iff, map_sub, map_smul, huangEnd_square, ← hc]
    module
  have hv : v = (2 * c)⁻¹ • (A v + c • v) +
      (-(2 * c)⁻¹) • (A v - c • v) := by
    rw [smul_add, smul_sub, smul_smul, smul_smul, neg_mul]
    have : (2 * c)⁻¹ * c = 2⁻¹ := by field_simp
    rw [this]
    module
  rw [hv]
  exact Submodule.add_mem_sup (Submodule.smul_mem _ _ hplus)
    (Submodule.smul_mem _ _ hminus)

/-- Ledger: claim-huang-spectrum. The two eigenspaces have zero intersection. -/
theorem huangEnd_eigenspaces_inf (d : ℕ) (hd : 0 < d) :
    (huangEnd d).eigenspace √(d : ℝ) ⊓
      (huangEnd d).eigenspace (-√(d : ℝ)) = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  have hp := Module.End.mem_eigenspace_iff.1 hv.1
  have hn := Module.End.mem_eigenspace_iff.1 hv.2
  have hc : 0 < √(d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hz : (√(d : ℝ) - (-√(d : ℝ))) • v = 0 := by
    rw [sub_smul, ← hp, ← hn, sub_self]
  exact (smul_eq_zero.1 hz).resolve_left (by linarith)

/-- Ledger: claim-huang-spectrum. Opposite eigenspaces have equal dimension. -/
theorem huangEnd_eigenspaces_finrank (d : ℕ) (μ : ℝ) :
    finrank ℝ ((huangEnd d).eigenspace μ) =
      finrank ℝ ((huangEnd d).eigenspace (-μ)) := by
  have hle (μ : ℝ) : finrank ℝ ((huangEnd d).eigenspace μ) ≤
      finrank ℝ ((huangEnd d).eigenspace (-μ)) := by
    let T : (huangEnd d).eigenspace μ →ₗ[ℝ]
        (huangEnd d).eigenspace (-μ) :=
      { toFun := fun v => ⟨huangParityEnd d v, by
          rw [Module.End.mem_eigenspace_iff, huangEnd_parity,
            Module.End.mem_eigenspace_iff.1 v.property, map_smul]
          simp⟩
        map_add' := fun v w => by
          apply Subtype.ext
          exact map_add (huangParityEnd d) (v : HuangVertex d → ℝ) (w : HuangVertex d → ℝ)
        map_smul' := fun c v => by
          apply Subtype.ext
          exact map_smul (huangParityEnd d) c (v : HuangVertex d → ℝ) }
    have hT : Function.Injective T := by
      intro v w h
      apply Subtype.ext
      exact (huangParityEnd_involutive d).injective (congrArg Subtype.val h)
    exact LinearMap.finrank_le_finrank_of_injective hT
  have hdouble : (huangEnd d).eigenspace (-(-μ)) = (huangEnd d).eigenspace μ :=
    congrArg (fun a : ℝ => (huangEnd d).eigenspace a) (neg_neg μ)
  have hdim := (LinearEquiv.ofEq _ _ hdouble).finrank_eq
  exact le_antisymm (hle μ) (le_trans (hle (-μ)) (le_of_eq hdim))

/-- Ledger: claim-huang-spectrum. Each of `+sqrt d` and `-sqrt d` has exactly
`2^(d-1)` independent eigenvectors, for positive `d`. -/
theorem huangEnd_eigenspaces_half (d : ℕ) (hd : 0 < d) :
    finrank ℝ ((huangEnd d).eigenspace √(d : ℝ)) = 2 ^ (d - 1) ∧
      finrank ℝ ((huangEnd d).eigenspace (-√(d : ℝ))) = 2 ^ (d - 1) := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    ((huangEnd d).eigenspace √(d : ℝ)) ((huangEnd d).eigenspace (-√(d : ℝ)))
  rw [huangEnd_eigenspaces_sup d hd, huangEnd_eigenspaces_inf d hd,
    finrank_top, finrank_bot, add_zero, Module.finrank_pi, huangVertex_card] at hdim
  have heq := huangEnd_eigenspaces_finrank d √(d : ℝ)
  have hpow : 2 ^ d = 2 * 2 ^ (d - 1) := by
    cases d with
    | zero => omega
    | succ d => simp [pow_succ, Nat.mul_comm]
  constructor <;> omega

/-- Ledger: claim-interlace. A set containing more than half the cube supports
a nonzero eigenvector of the literal recursive matrix for the positive
eigenvalue `sqrt d`. This is the dimension-intersection proof in Appendix A. -/
theorem huang_supported_positive_eigenvector (d : ℕ) (hd : 0 < d)
    (U : Finset (HuangVertex d)) (hU : 2 ^ (d - 1) < #U) :
    ∃ v : HuangVertex d → ℝ,
      huangEnd d v = √(d : ℝ) • v ∧ v ≠ 0 ∧ ∀ x ∉ U, v x = 0 := by
  let E := (huangEnd d).eigenspace √(d : ℝ)
  let r : E →ₗ[ℝ] ((Uᶜ : Finset (HuangVertex d)) → ℝ) :=
    (LinearMap.funLeft ℝ ℝ Subtype.val).comp E.subtype
  have hpow : 2 ^ d = 2 * 2 ^ (d - 1) := by
    cases d with
    | zero => omega
    | succ d => simp [pow_succ, Nat.mul_comm]
  have hdim : finrank ℝ E = 2 ^ (d - 1) := (huangEnd_eigenspaces_half d hd).1
  have hUle : #U ≤ 2 ^ d := by
    simpa only [huangVertex_card] using card_le_univ U
  have hr : finrank ℝ ((Uᶜ : Finset (HuangVertex d)) → ℝ) < finrank ℝ E := by
    rw [Module.finrank_pi, Fintype.card_coe, card_compl, huangVertex_card, hdim]
    omega
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1
    (LinearMap.ker_ne_bot_of_finrank_lt (f := r) hr)
  refine ⟨w.1, Module.End.mem_eigenspace_iff.1 w.2,
    fun h => hw0 (Subtype.ext h), fun x hx => ?_⟩
  exact congrFun (LinearMap.mem_ker.1 hw) ⟨x, mem_compl.2 hx⟩

/-- Ledger: claim-interlace. Taking absolute values of a positive eigenvector
gives the unsigned Rayleigh inequality, on the full recursively indexed cube.
The support hypothesis is recorded by `huang_supported_positive_eigenvector`;
the zero terms outside its set may be removed from this finite sum. -/
theorem huang_absolute_rayleigh (d : ℕ) (v : HuangVertex d → ℝ)
    (hv : huangEnd d v = √(d : ℝ) • v) :
    √(d : ℝ) * (∑ x, |v x| ^ 2) ≤
      ∑ x, ∑ y, |v x| * huangCubeMatrix d x y * |v y| := by
  have hpoint (x : HuangVertex d) :
      √(d : ℝ) * |v x| ≤ ∑ y, huangCubeMatrix d x y * |v y| := by
    calc
      √(d : ℝ) * |v x| = |(huangEnd d v) x| := by
        rw [hv, Pi.smul_apply, smul_eq_mul, abs_mul,
          abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ ∑ y, |huangMatrix d x y * v y| :=
        abs_sum_le_sum_abs _ _
      _ = ∑ y, huangCubeMatrix d x y * |v y| := by
        simp only [abs_mul, abs_huangMatrix]
  rw [mul_sum]
  refine sum_le_sum fun x _ => ?_
  have h := mul_le_mul_of_nonneg_left (hpoint x) (abs_nonneg (v x))
  simpa only [mul_sum, ← mul_assoc, mul_comm (|v x|) (√(d : ℝ)), pow_two] using h

/-- Ledger: claim-interlace. The same Rayleigh inequality on the induced
vertex set, after the zero terms outside the support have been removed. -/
theorem huang_absolute_rayleigh_supported (d : ℕ) (U : Finset (HuangVertex d))
    (v : HuangVertex d → ℝ) (hv : huangEnd d v = √(d : ℝ) • v)
    (hsupp : ∀ x ∉ U, v x = 0) :
    √(d : ℝ) * (∑ x, |v x| ^ 2) ≤
      ∑ x ∈ U, ∑ y ∈ U, |v x| * huangCubeMatrix d x y * |v y| := by
  have h := huang_absolute_rayleigh d v hv
  have hsum : (∑ x, ∑ y, |v x| * huangCubeMatrix d x y * |v y|) =
      ∑ x ∈ U, ∑ y ∈ U, |v x| * huangCubeMatrix d x y * |v y| := by
    rw [← sum_subset (subset_univ U)
      (f := fun x => ∑ y, |v x| * huangCubeMatrix d x y * |v y|)
      (fun x _ hx => by simp [hsupp x hx])]
    refine sum_congr rfl fun x _ => ?_
    exact (sum_subset (subset_univ U)
      (fun y _ hy => by simp [hsupp y hy])).symm
  rwa [hsum] at h

/-- Ledger: claim-interlace. The literal Appendix A dimension-intersection
and absolute-value Rayleigh statement, including the positive eigenvalue. -/
theorem huang_positive_rayleigh_witness (d : ℕ) (hd : 0 < d)
    (U : Finset (HuangVertex d)) (hU : 2 ^ (d - 1) < #U) :
    ∃ v : HuangVertex d → ℝ,
      huangEnd d v = √(d : ℝ) • v ∧ v ≠ 0 ∧ (∀ x ∉ U, v x = 0) ∧
      √(d : ℝ) * (∑ x, |v x| ^ 2) ≤
        ∑ x ∈ U, ∑ y ∈ U, |v x| * huangCubeMatrix d x y * |v y| := by
  obtain ⟨v, hv, hv0, hsupp⟩ := huang_supported_positive_eigenvector d hd U hU
  exact ⟨v, hv, hv0, hsupp, huang_absolute_rayleigh_supported d U v hv hsupp⟩

end QuarticQuery.Paper
