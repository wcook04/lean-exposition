module

public import QuarticQuery.Model.Quantum
public import Complexity.Computability.QueryComplexity.Quantum.Search

/-!
# The bit oracle and the controlled phase oracle

A Hadamard on the answer qubit conjugates complexitylib's controlled phase oracle
`|i, b, z⟩ ↦ (-1)^(b ∧ x_i) |i, b, z⟩` into our bit oracle
`|i, b, z⟩ ↦ |i, b ⊕ x_i, z⟩`, in both directions. The Hadamard does not depend on
the input, so a fixed sequence in one oracle is a fixed sequence in the other with
the same number of queries.
-/

public section

namespace QuarticQuery

open Cslib.Quantum (phaseOracle phaseOracle_apply run)

/-- The state space of complexitylib, for any workspace type. -/
abbrev QState (N : ℕ) (W : Type) := Cslib.Quantum.State N W

variable {N : ℕ} {W : Type}

/-- `1/√2`. -/
noncomputable def invSqrtTwo : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

theorem invSqrtTwo_mul_self : invSqrtTwo * invSqrtTwo = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [invSqrtTwo, ← mul_inv, h]
  norm_num

theorem norm_invSqrtTwo_sq : ‖invSqrtTwo‖ ^ 2 = 1 / 2 := by
  rw [invSqrtTwo, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2), inv_pow,
    Real.sq_sqrt (by norm_num)]
  norm_num

/-- Ledger: def-query-oracle. The Hadamard on the answer qubit. -/
@[expose] noncomputable def hadamardL : QState N W →ₗ[ℂ] QState N W where
  toFun ψ := WithLp.toLp 2 fun p => invSqrtTwo *
    (ψ.ofLp (p.1, false, p.2.2) + (if p.2.1 then -1 else 1) * ψ.ofLp (p.1, true, p.2.2))
  map_add' ψ φ := by
    ext p
    simp only [PiLp.add_apply]
    ring
  map_smul' c ψ := by
    ext p
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem hadamardL_apply (ψ : QState N W) (i : Fin N) (b : Bool) (z : W) :
    (hadamardL ψ).ofLp (i, b, z) = invSqrtTwo *
      (ψ.ofLp (i, false, z) + (if b then -1 else 1) * ψ.ofLp (i, true, z)) := rfl

/-- Ledger: def-query-oracle. The Hadamard is an involution. -/
theorem hadamardL_hadamardL (ψ : QState N W) : hadamardL (hadamardL ψ) = ψ := by
  ext ⟨i, b, z⟩
  simp only [hadamardL_apply]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    linear_combination (2 * ψ.ofLp (i, false, z)) * invSqrtTwo_mul_self
  · simp only [Bool.false_eq_true, ↓reduceIte]
    linear_combination (2 * ψ.ofLp (i, true, z)) * invSqrtTwo_mul_self

private theorem norm_pair (a c : ℂ) :
    ‖invSqrtTwo * (a + c)‖ ^ 2 + ‖invSqrtTwo * (a - c)‖ ^ 2 = ‖a‖ ^ 2 + ‖c‖ ^ 2 := by
  have h := parallelogram_law_with_norm ℝ a c
  rw [norm_mul, norm_mul, mul_pow, mul_pow, norm_invSqrtTwo_sq]
  nlinarith

/-- Ledger: def-query-oracle. The Hadamard preserves the norm. -/
theorem norm_hadamardL [Fintype W] (ψ : QState N W) : ‖hadamardL ψ‖ = ‖ψ‖ := by
  have h : ‖hadamardL ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fintype.sum_bool,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun z _ => ?_
    have := norm_pair (ψ.ofLp (i, false, z)) (ψ.ofLp (i, true, z))
    simp only [hadamardL_apply, Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul,
      ← sub_eq_add_neg]
    linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Ledger: def-query-oracle. The Hadamard as a gate. -/
@[expose] noncomputable def hadamard [Fintype W] : QState N W →ₗᵢ[ℂ] QState N W where
  toLinearMap := hadamardL
  norm_map' := norm_hadamardL

theorem hadamard_apply [Fintype W] (ψ : QState N W) : hadamard ψ = hadamardL ψ := rfl

/-- Ledger: def-query-oracle. The Hadamard is an involution. -/
theorem hadamard_hadamard [Fintype W] (ψ : QState N W) : hadamard (hadamard ψ) = ψ :=
  hadamardL_hadamardL ψ

variable {w : ℕ}

/-- Ledger: def-query-oracle. `O_x = H · Phase_x · H`. -/
theorem hadamard_phaseOracle_hadamard (x : BitInput (Fin N)) (ψ : State (Fin N) w) :
    hadamard (phaseOracle x (hadamard ψ)) = bitOracle x ψ := by
  ext ⟨i, b, z⟩
  rw [hadamard_apply, hadamardL_apply, bitOracle_apply]
  simp only [phaseOracle_apply, hadamard_apply, hadamardL_apply, flipPoint]
  cases hx : x i <;> cases b <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.and_true,
      Bool.not_false, Bool.not_true]
  · linear_combination (2 * ψ.ofLp (i, false, z)) * invSqrtTwo_mul_self
  · linear_combination (2 * ψ.ofLp (i, true, z)) * invSqrtTwo_mul_self
  · linear_combination (2 * ψ.ofLp (i, true, z)) * invSqrtTwo_mul_self
  · linear_combination (2 * ψ.ofLp (i, false, z)) * invSqrtTwo_mul_self

/-- Ledger: def-query-oracle. `Phase_x = H · O_x · H`. -/
theorem hadamard_bitOracle_hadamard (x : BitInput (Fin N)) (ψ : State (Fin N) w) :
    hadamard (bitOracle x (hadamard ψ)) = phaseOracle x ψ := by
  rw [← hadamard_phaseOracle_hadamard, hadamard_hadamard, hadamard_hadamard]

/-- Ledger: def-query-oracle. The state of a fixed sequence in our bit oracle. -/
noncomputable def bitRun (V : ℕ → State (Fin N) w →ₗᵢ[ℂ] State (Fin N) w) (ψ₀ : State (Fin N) w)
    (x : BitInput (Fin N)) : ℕ → State (Fin N) w
  | 0 => V 0 ψ₀
  | t + 1 => V (t + 1) (bitOracle x (bitRun V ψ₀ x t))

/-- Ledger: def-query-oracle. Conjugate each gate of a bit-oracle sequence ending at
`T`: a Hadamard after every gate before `T` and before every gate after `0`. -/
noncomputable def phaseGates (V : ℕ → State (Fin N) w →ₗᵢ[ℂ] State (Fin N) w) (T : ℕ) :
    ℕ → State (Fin N) w →ₗᵢ[ℂ] State (Fin N) w := fun t =>
  (if t = T then LinearIsometry.id else hadamard).comp
    ((V t).comp (if t = 0 then LinearIsometry.id else hadamard))

/-- Ledger: def-query-oracle. A fixed sequence of `T` bit queries is a fixed sequence
of `T` phase queries, with the same final state. -/
theorem run_phaseGates (V : ℕ → State (Fin N) w →ₗᵢ[ℂ] State (Fin N) w) (ψ₀ : State (Fin N) w)
    (x : BitInput (Fin N)) (T : ℕ) : run (phaseGates V T) ψ₀ x T = bitRun V ψ₀ x T := by
  have key : ∀ t, t < T → run (phaseGates V T) ψ₀ x t = hadamard (bitRun V ψ₀ x t) := by
    intro t
    induction t with
    | zero =>
      intro h
      simp [run, bitRun, phaseGates, h.ne]
    | succ t ih =>
      intro h
      have hne : t + 1 ≠ T := h.ne
      simp only [run, bitRun, phaseGates, hne, ↓reduceIte, Nat.succ_ne_zero,
        LinearIsometry.coe_comp, Function.comp_apply]
      rw [ih (by omega), ← hadamard_bitOracle_hadamard]
      simp only [hadamard_hadamard]
  cases T with
  | zero => simp [run, bitRun, phaseGates]
  | succ T =>
    simp only [run, bitRun, phaseGates, ↓reduceIte, Nat.succ_ne_zero,
      LinearIsometry.coe_comp, Function.comp_apply, LinearIsometry.coe_id, id_eq]
    rw [key T (by omega), ← hadamard_bitOracle_hadamard]
    simp only [hadamard_hadamard]

end QuarticQuery
