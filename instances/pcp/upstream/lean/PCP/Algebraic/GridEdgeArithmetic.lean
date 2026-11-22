import PCP.Algebraic.FieldQueryArithmetic
import PCP.Algebraic.ThreeColorGridIndex

/-!
# Numeric summation indices for the public graph edge extension

The low and high halves of one little-endian grid address are the two vertex
addresses. The finite interpolation sum uses exactly this arithmetic order.
-/

namespace PCP.Algebraic.GridEdgeArithmetic

open FieldQueryArithmetic ThreeColorGridIndex

variable {h n N : ℕ}

/-- Splitting a coordinate vector splits its little-endian integer address. -/
theorem address_split (f : Fin (n + n) → Fin h) :
    (finFunctionFinEquiv f).val =
      (finFunctionFinEquiv (fun i : Fin n => f (i.castAdd n))).val +
        h ^ n * (finFunctionFinEquiv (fun i : Fin n => f (i.natAdd n))).val := by
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_add]
  simp only [finFunctionFinEquiv_apply, Fin.val_castAdd, Fin.val_natAdd, pow_add]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem address_low (f : Fin (n + n) → Fin h) :
    (finFunctionFinEquiv (fun i : Fin n => f (i.castAdd n))).val =
      (finFunctionFinEquiv f).val % h ^ n := by
  rw [address_split, Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt (finFunctionFinEquiv _).isLt).symm

theorem address_high (f : Fin (n + n) → Fin h) :
    (finFunctionFinEquiv (fun i : Fin n => f (i.natAdd n))).val =
      (finFunctionFinEquiv f).val / h ^ n := by
  have hp : 0 < h ^ n := lt_of_le_of_lt (Nat.zero_le _)
    (finFunctionFinEquiv (fun i : Fin n => f (i.castAdd n))).isLt
  rw [address_split, Nat.add_mul_div_left _ _ hp]
  rw [Nat.div_eq_of_lt (finFunctionFinEquiv _).isLt, Nat.zero_add]

variable {F : Type*} [Field F] [DecidableEq F]

/-- The tensor basis is invariant under a bijection of its coordinates. -/
theorem gridBasis_reindex {σ τ : Type*} [Fintype σ] [Fintype τ]
    (e : σ ≃ τ) (H : Finset F)
    (a : τ → H) (x : τ → F) :
    gridBasis H (a ∘ e) (x ∘ e) = gridBasis H a x := by
  exact e.prod_comp (fun i => ∏ b ∈ H.erase (a i : F), (x i - b) / ((a i : F) - b))

/-- Replace the sum-coordinate presentation by the stored flat coordinate vector. -/
theorem edgeValue_flatten (H : Finset F) (G : SimpleGraph (Fin n → H))
    [DecidableRel G.Adj] (x : Fin (n + n) → F) :
    edgeValue H G x = ∑ a : Fin (n + n) → H,
      if G.Adj (fun i => a (i.castAdd n)) (fun i => a (i.natAdd n))
      then gridBasis H a x else 0 := by
  let e := GridCoordinateTransport.pointEquiv (ThreeColorVerifier.flatten n) H
  have he := e.sum_comp (fun a : (Fin n ⊕ Fin n) → H =>
    (if G.Adj (fun i => a (.inl i)) (fun i => a (.inr i)) then (1 : F) else 0) *
      gridBasis H a (x ∘ ThreeColorVerifier.flatten n))
  change _ = _ at he
  rw [edgeValue, gridInterpolate, ← he]
  apply Finset.sum_congr rfl
  intro a _
  change (if G.Adj (fun i => a (i.castAdd n)) (fun i => a (i.natAdd n))
    then (1 : F) else 0) * gridBasis H (a ∘ ThreeColorVerifier.flatten n)
      (x ∘ ThreeColorVerifier.flatten n) = _
  rw [gridBasis_reindex]
  split_ifs <;> simp

/-- Numeric bounded vertex decoding retains exactly the padded graph's adjacency. -/
def Adj (G : SimpleGraph (Fin N)) (u v : ℕ) : Prop :=
  if hu : u < N then if hv : v < N then G.Adj ⟨u, hu⟩ ⟨v, hv⟩ else False else False

instance (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (u v : ℕ) : Decidable (Adj G u v) := by
  unfold Adj
  split_ifs <;> infer_instance

omit [Field F] [DecidableEq F] in
theorem pad_adj (H : Finset F) (eH : H ≃ Fin h) (G : SimpleGraph (Fin N))
    (a b : Fin n → H) :
    (pad eH n G).Adj a b ↔ Adj G (gridEquiv eH n a).val (gridEquiv eH n b).val := by
  change (match decodeVertex eH N a, decodeVertex eH N b with
    | some u, some v => G.Adj u v
    | _, _ => False) ↔ _
  unfold decodeVertex Adj
  split_ifs <;> rfl

/-- One integer names the full pair of grid points in the exact interpolation order. -/
def summand (H : Finset F) (eH : H ≃ Fin h) (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (x : Fin (n + n) → F) (j : Fin (h ^ (n + n))) : F :=
  if Adj G (j.val % h ^ n) (j.val / h ^ n) then
    gridBasis H ((gridEquiv eH (n + n)).symm j) x else 0

/-- The actual public edge extension is an arithmetic-order finite interpolation sum. -/
theorem edgeValue_sum (H : Finset F) (eH : H ≃ Fin h) (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (x : Fin (n + n) → F) :
    edgeValue H (pad eH n G) x = ∑ j : Fin (h ^ (n + n)), summand H eH G x j := by
  rw [edgeValue_flatten]
  have he := (gridEquiv eH (n + n)).symm.sum_comp
    (fun a : Fin (n + n) → H =>
      if (pad eH n G).Adj (fun i => a (i.castAdd n)) (fun i => a (i.natAdd n))
      then gridBasis H a x else 0)
  rw [← he]
  apply Finset.sum_congr rfl
  intro j _
  let a := (gridEquiv eH (n + n)).symm j
  have hc : finFunctionFinEquiv (eH ∘ a) = j := by
    exact (gridEquiv eH (n + n)).apply_symm_apply j
  have hl := address_low (eH ∘ a)
  have hh := address_high (eH ∘ a)
  rw [hc] at hl hh
  simp only [Function.comp_apply] at hl hh
  have ha : (pad eH n G).Adj (fun i => a (i.castAdd n)) (fun i => a (i.natAdd n)) ↔
      Adj G (j.val % h ^ n) (j.val / h ^ n) := by
    rw [pad_adj]
    change Adj G (finFunctionFinEquiv (fun i => eH (a (i.castAdd n)))).val
      (finFunctionFinEquiv (fun i => eH (a (i.natAdd n)))).val ↔ _
    rw [hl, hh]
  simp only [summand, ← ha]
  rfl

end PCP.Algebraic.GridEdgeArithmetic
