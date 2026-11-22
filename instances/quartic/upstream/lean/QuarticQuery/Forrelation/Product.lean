module

public import QuarticQuery.Forrelation.Walsh

/-!
# `Phi` is the matrix product of equation (3)

`forrelationNumerator` expands `N` over paths. `walkN` is the same scalar computed
right to left: `v_k = z_k` and `v_h = z_h ∘ (W v_{h+1})`. The walk is the
recursion the circuit follows, and it gives `Phi = uᵀ D_{z₁} H D_{z₂} H ⋯ H D_{z_k} u`.
Orthogonality of each factor then bounds `|Phi|` by one.
-/

@[expose] public section

namespace QuarticQuery.Forrelation

open Finset Matrix

/-- Ledger: claim-N-phi. `v_h(i)` with layers indexed from the current one:
layer `0` is multiplied last. -/
def walkN (n : ℕ) : ℕ → (ℕ → ℕ → ℤ) → ℕ → ℤ
  | 0, σ, i => σ 0 i
  | l + 1, σ, i =>
      σ 0 i * ∑ j ∈ range (2 ^ n), walshN n i j * walkN n l (fun h => σ (h + 1)) j

/-- The weight of one path through `l + 1` layers. -/
def pathWeight (t l : ℕ) (σ : ℕ → ℕ → ℤ) (p : Fin (l + 1) → Fin (mValue t)) : ℤ :=
  (∏ h : Fin (l + 1), σ h (p h)) * ∏ h : Fin l, walshN (2 * t) (p h.castSucc) (p h.succ)

theorem pathWeight_cons (t l : ℕ) (σ : ℕ → ℕ → ℤ) (i : Fin (mValue t))
    (q : Fin (l + 1) → Fin (mValue t)) :
    pathWeight t (l + 1) σ (Fin.cons i q) =
      σ 0 i * (walshN (2 * t) i (q 0) * pathWeight t l (fun h => σ (h + 1)) q) := by
  have e1 : ∏ h : Fin (l + 2), σ h ((Fin.cons i q : Fin (l + 2) → Fin (mValue t)) h) =
      σ 0 i * ∏ h : Fin (l + 1), σ (h + 1) (q h) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ]
  have e2 : ∏ h : Fin (l + 1), walshN (2 * t)
        ((Fin.cons i q : Fin (l + 2) → Fin (mValue t)) h.castSucc)
        ((Fin.cons i q : Fin (l + 2) → Fin (mValue t)) h.succ) =
      walshN (2 * t) i (q 0) * ∏ h : Fin l, walshN (2 * t) (q h.castSucc) (q h.succ) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ← Fin.succ_castSucc]
  unfold pathWeight
  rw [e1, e2]
  ring

theorem sum_fin_cons {α : Type} [Fintype α] (l : ℕ) (f : (Fin (l + 1) → α) → ℤ) :
    ∑ p, f p = ∑ i, ∑ q : Fin l → α, f (Fin.cons i q) := by
  rw [← Fintype.sum_prod_type', ← (Fin.consEquiv fun _ => α).sum_comp]
  rfl

theorem sum_pathWeight_cons (t l : ℕ) (σ : ℕ → ℕ → ℤ) (i : Fin (mValue t)) :
    ∑ q : Fin l → Fin (mValue t), pathWeight t l σ (Fin.cons i q) = walkN (2 * t) l σ i := by
  induction l generalizing σ i with
  | zero => simp [pathWeight, walkN]
  | succ l ih =>
    rw [walkN, ← sum_range_mValue t (fun j => walshN (2 * t) i j *
      walkN (2 * t) l (fun h => σ (h + 1)) j), sum_fin_cons, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [← ih (fun h => σ (h + 1)) j, mul_sum, mul_sum]
    refine sum_congr rfl fun q _ => ?_
    rw [pathWeight_cons, Fin.cons_zero]

/-- The sign of layer `h` at index `i`. Out-of-range indices are never read. -/
def layerSign {k t : ℕ} (z : BitInput (ForrelationCoord k t)) (h i : ℕ) : ℤ :=
  if hh : h < k ∧ i < mValue t then bitSign (z (⟨h, hh.1⟩, ⟨i, hh.2⟩)) else 1

/-- Ledger: claim-N-phi. The path expansion of `N` equals the right-to-left walk. -/
theorem numerator_eq_walk (l t : ℕ) (z : BitInput (ForrelationCoord (l + 1) t)) :
    forrelationNumerator (l + 1) t z =
      ∑ i ∈ range (2 ^ (2 * t)), walkN (2 * t) l (layerSign z) i := by
  have h1 : forrelationNumerator (l + 1) t z = ∑ p, pathWeight t l (layerSign z) p := by
    unfold forrelationNumerator
    refine sum_congr rfl fun p _ => ?_
    unfold pathWeight
    congr 1
    refine Finset.prod_congr rfl fun h _ => ?_
    have hh : h.val < l + 1 ∧ (p h).val < mValue t := ⟨h.isLt, (p h).isLt⟩
    simp only [layerSign, dite_eq_left_of_eq_true (eq_true hh)]
  rw [h1, sum_fin_cons, ← sum_range_mValue t (walkN (2 * t) l (layerSign z))]
  exact sum_congr rfl fun i _ => sum_pathWeight_cons t l _ i

/-! ## Matrix form -/

/-- Ledger: eq-3. `u = m^(-1/2) (1, …, 1)`, using `√m = 2 ^ t`. -/
noncomputable def u (t : ℕ) : Fin (mValue t) → ℝ := fun _ => ((2 : ℝ) ^ t)⁻¹

/-- Ledger: eq-3. `D_{z_h}`, the diagonal matrix of the signs of layer `h`. -/
noncomputable def signDiag {k t : ℕ} (z : BitInput (ForrelationCoord k t)) (h : Fin k) :
    Matrix (Fin (mValue t)) (Fin (mValue t)) ℝ :=
  Matrix.diagonal fun i => (bitSign (z (h, i)) : ℝ)

variable {n : Type} [Fintype n] [DecidableEq n]

/-- `H D₂ H D₃ ⋯ H D_k`. -/
def tailProd (A : Matrix n n ℝ) : List (Matrix n n ℝ) → Matrix n n ℝ
  | [] => 1
  | D :: r => A * D * tailProd A r

/-- Ledger: eq-3. `D₁ H D₂ H ⋯ H D_k`: the listed matrices with `A` between
consecutive entries, and no `A` at either end. -/
def alternate (A : Matrix n n ℝ) : List (Matrix n n ℝ) → Matrix n n ℝ
  | [] => 1
  | D :: r => D * tailProd A r

theorem tailProd_cons_eq (A D : Matrix n n ℝ) (r : List (Matrix n n ℝ)) :
    tailProd A (D :: r) = A * alternate A (D :: r) := by
  simp [tailProd, alternate, mul_assoc]

theorem alternate_ofFn_succ (A : Matrix n n ℝ) (l : ℕ) (D : Fin (l + 2) → Matrix n n ℝ) :
    alternate A (List.ofFn D) =
      D 0 * (A * alternate A (List.ofFn fun i : Fin (l + 1) => D i.succ)) := by
  rw [List.ofFn_succ, alternate, List.ofFn_succ, tailProd_cons_eq]

/-- The diagonal of layer `h` of a sign table. -/
noncomputable def diagOf (t : ℕ) (σ : ℕ → ℕ → ℤ) (h : ℕ) :
    Matrix (Fin (mValue t)) (Fin (mValue t)) ℝ :=
  Matrix.diagonal fun i => (σ h i : ℝ)

theorem H_mulVec_cast (t : ℕ) (f : ℕ → ℤ) (i : Fin (mValue t)) :
    (H t *ᵥ fun j => (f j : ℝ)) i =
      ((2 : ℝ) ^ t)⁻¹ * ((∑ j ∈ range (2 ^ (2 * t)), walshN (2 * t) i j * f j : ℤ) : ℝ) := by
  rw [← sum_range_mValue t (fun j => walshN (2 * t) i j * f j), H, Matrix.smul_mulVec,
    Pi.smul_apply, smul_eq_mul]
  congr 1
  simp only [Matrix.mulVec, dotProduct, W, walshZ, Matrix.map_apply, Matrix.of_apply,
    Int.cast_sum, Int.cast_mul, Int.coe_castRingHom, walshSign_eq]

theorem alternate_mulVec_one (t l : ℕ) (σ : ℕ → ℕ → ℤ) :
    alternate (H t) (List.ofFn fun h : Fin (l + 1) => diagOf t σ h) *ᵥ (fun _ => 1) =
      fun i : Fin (mValue t) => (walkN (2 * t) l σ i : ℝ) * ((2 : ℝ) ^ t)⁻¹ ^ l := by
  induction l generalizing σ with
  | zero =>
    ext i
    simp [alternate, tailProd, diagOf, walkN, Matrix.mulVec_diagonal]
  | succ l ih =>
    have shift : (fun i : Fin (l + 1) => diagOf t σ (i.succ : Fin (l + 2)).val) =
        fun i : Fin (l + 1) => diagOf t (fun h => σ (h + 1)) i := by
      funext i
      simp [diagOf]
    rw [alternate_ofFn_succ, shift, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih]
    ext i
    have hc : (fun j : Fin (mValue t) => (walkN (2 * t) l (fun h => σ (h + 1)) j : ℝ) * ((2 : ℝ) ^ t)⁻¹ ^ l)
        = (((2 : ℝ) ^ t)⁻¹ ^ l) • fun j : Fin (mValue t) =>
          ((walkN (2 * t) l (fun h => σ (h + 1)) j : ℤ) : ℝ) := by
      funext j
      simp [mul_comm]
    rw [hc, Matrix.mulVec_smul]
    simp only [diagOf, Fin.val_zero, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    rw [H_mulVec_cast t (walkN (2 * t) l fun h => σ (h + 1)) i, walkN]
    push_cast
    ring

/-- Ledger: eq-3, claim-N-phi. `Phi` is the matrix product
`uᵀ D_{z₁} H D_{z₂} H ⋯ H D_{z_k} u`. -/
theorem Phi_eq_matrix_product (k t : ℕ) (hk : 1 ≤ k) (z : BitInput (ForrelationCoord k t)) :
    Phi k t z = u t ⬝ᵥ
      (alternate (H t) (List.ofFn fun h : Fin k => signDiag z h) *ᵥ u t) := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  have hD : (fun h : Fin (l + 1) => signDiag z h) =
      fun h : Fin (l + 1) => diagOf t (layerSign z) h := by
    funext h
    unfold signDiag diagOf
    congr 1
    funext i
    have hh : h.val < l + 1 ∧ i.val < mValue t := ⟨h.isLt, i.isLt⟩
    simp only [layerSign, dite_eq_left_of_eq_true (eq_true hh)]
  have hu : u t = ((2 : ℝ) ^ t)⁻¹ • fun _ => (1 : ℝ) := by
    funext i
    simp [u]
  rw [hD]
  conv_rhs => rw [hu, Matrix.mulVec_smul, alternate_mulVec_one]
  rw [Phi, numerator_eq_walk, ← sum_range_mValue t (walkN (2 * t) l (layerSign z))]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, forrelationDenominator, Nat.add_sub_cancel]
  push_cast
  rw [div_eq_mul_inv, sum_mul, ]
  refine sum_congr rfl fun i _ => ?_
  have h2 : (2 : ℝ) ^ (2 * t) = (2 : ℝ) ^ t * (2 : ℝ) ^ t := by rw [two_mul, pow_add]
  rw [h2]
  simp only [mul_inv, inv_pow]
  ring

/-- The case `k = 2`, spelled out. -/
theorem Phi_two (t : ℕ) (z : BitInput (ForrelationCoord 2 t)) :
    Phi 2 t z = u t ⬝ᵥ ((signDiag z 0 * H t * signDiag z 1) *ᵥ u t) := by
  rw [Phi_eq_matrix_product 2 t (by norm_num)]
  simp [List.ofFn_succ, alternate, tailProd, mul_assoc]

/-- The case `k = 3`, spelled out. -/
theorem Phi_three (t : ℕ) (z : BitInput (ForrelationCoord 3 t)) :
    Phi 3 t z =
      u t ⬝ᵥ ((signDiag z 0 * H t * signDiag z 1 * H t * signDiag z 2) *ᵥ u t) := by
  rw [Phi_eq_matrix_product 3 t (by norm_num)]
  simp [List.ofFn_succ, alternate, tailProd, mul_assoc, Fin.succ]

/-! ## Unitarity -/

/-- `Aᵀ A = I`. -/
def IsOrth (A : Matrix n n ℝ) : Prop := Aᵀ * A = 1

theorem IsOrth.mul {A B : Matrix n n ℝ} (hA : IsOrth A) (hB : IsOrth B) : IsOrth (A * B) := by
  unfold IsOrth at *
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ, hA, Matrix.one_mul, hB]

theorem isOrth_one : IsOrth (1 : Matrix n n ℝ) := by simp [IsOrth]

theorem IsOrth.dot_self {A : Matrix n n ℝ} (hA : IsOrth A) (v : n → ℝ) :
    (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hA,
    Matrix.one_mulVec]

theorem isOrth_tailProd {A : Matrix n n ℝ} (hA : IsOrth A) :
    ∀ L : List (Matrix n n ℝ), (∀ D ∈ L, IsOrth D) → IsOrth (tailProd A L)
  | [], _ => isOrth_one
  | D :: r, h => ((hA.mul (h D (by simp))).mul
      (isOrth_tailProd hA r fun E hE => h E (by simp [hE])))

theorem isOrth_alternate {A : Matrix n n ℝ} (hA : IsOrth A) :
    ∀ L : List (Matrix n n ℝ), (∀ D ∈ L, IsOrth D) → IsOrth (alternate A L)
  | [], _ => isOrth_one
  | D :: r, h => (h D (by simp)).mul
      (isOrth_tailProd hA r fun E hE => h E (by simp [hE]))

theorem isOrth_H (t : ℕ) : IsOrth (H t) := by
  rw [IsOrth, H_transpose, H_mul_H]

theorem isOrth_signDiag {k t : ℕ} (z : BitInput (ForrelationCoord k t)) (h : Fin k) :
    IsOrth (signDiag z h) := by
  unfold IsOrth signDiag
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have := bitSign_mul_self (z (h, i))
  exact_mod_cast this

/-- The state `ψ_z = D_{z₁} H ⋯ H D_{z_k} u` of the algorithm. -/
noncomputable def psi {k t : ℕ} (z : BitInput (ForrelationCoord k t)) : Fin (mValue t) → ℝ :=
  alternate (H t) (List.ofFn fun h : Fin k => signDiag z h) *ᵥ u t

theorem u_dot_self (t : ℕ) : u t ⬝ᵥ u t = 1 := by
  simp only [dotProduct, u, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mValue_cast]
  have h2 : ((2 : ℝ) ^ t) ≠ 0 := by positivity
  field_simp

theorem psi_dot_self {k t : ℕ} (z : BitInput (ForrelationCoord k t)) : psi z ⬝ᵥ psi z = 1 := by
  rw [psi, IsOrth.dot_self _ _, u_dot_self]
  refine isOrth_alternate (isOrth_H t) _ fun D hD => ?_
  obtain ⟨h, rfl⟩ := (List.mem_ofFn' _ _).1 hD
  exact isOrth_signDiag z h

theorem dot_sq_le {n : Type} [Fintype n] (a b : n → ℝ) :
    (a ⬝ᵥ b) ^ 2 ≤ (a ⬝ᵥ a) * (b ⬝ᵥ b) := by
  simpa [dotProduct, sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b

/-- Ledger: eq-3. `Φ² ≤ 1`, by unitarity. -/
theorem Phi_sq_le_one (k t : ℕ) (hk : 1 ≤ k) (z : BitInput (ForrelationCoord k t)) :
    Phi k t z ^ 2 ≤ 1 := by
  rw [Phi_eq_matrix_product k t hk]
  have := dot_sq_le (u t) (psi z)
  rwa [u_dot_self, psi_dot_self, one_mul] at this

/-- Ledger: eq-3. `|Φ| ≤ 1`, by unitarity. -/
theorem abs_Phi_le_one (k t : ℕ) (hk : 1 ≤ k) (z : BitInput (ForrelationCoord k t)) :
    |Phi k t z| ≤ 1 :=
  abs_le_one_iff_mul_self_le_one.2 (by nlinarith [Phi_sq_le_one k t hk z])

end QuarticQuery.Forrelation
