module

public import QuarticQuery.Paper.QuantumTensor

@[expose] public section

namespace QuarticQuery.Paper

open QuarticQuery.Upper

/-- Flatten the nested fresh-register basis into ordinary `Fin n` coordinates.
The outermost register is the last coordinate, matching `tensorVector`. -/
def tensorCoordEquiv {Z : Type} : (n : ℕ) → TensorBasis Z n ≃ (Fin n → Z)
  | 0 =>
      { toFun := fun _ i => Fin.elim0 i
        invFun := fun _ => ()
        left_inv := by intro p; cases p; rfl
        right_inv := by intro f; funext i; exact Fin.elim0 i }
  | n + 1 =>
      let unpack : (Σ _ : Z, TensorBasis Z n) ≃ Z × TensorBasis Z n :=
        { toFun := fun p => (p.1, p.2)
          invFun := fun p => ⟨p.1, p.2⟩
          left_inv := by intro p; cases p; rfl
          right_inv := by intro p; cases p; rfl }
      unpack.trans ((Equiv.prodCongr (Equiv.refl Z) (tensorCoordEquiv n)).trans
        (Fin.snocEquiv (fun _ : Fin (n + 1) => Z)))

/-- All fresh registers begin at the same computational basis coordinate. -/
theorem tensorCoordEquiv_origin {Z : Type} (o : Z) (n : ℕ) :
    (tensorCoordEquiv n).toFun (tensorOrigin o n) = fun _ => o := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
      funext i
      induction i using Fin.lastCases with
      | last => simp [tensorCoordEquiv, tensorOrigin]
      | cast i => simpa [tensorCoordEquiv, tensorOrigin] using congrFun ih i

/-- A tensor of identical trial vectors has the expected coordinate product. -/
theorem tensorVector_coord_product {Z : Type} [Fintype Z] (v : Reg Z)
    (n : ℕ) (p : TensorBasis Z n) :
    (tensorVector (fun _ => v) n).ofLp p =
      ∏ i : Fin n, v.ofLp ((tensorCoordEquiv n).toFun p i) := by
  induction n with
  | zero =>
      cases p
      simp [tensorVector, tensorCoordEquiv, rket_apply]
  | succ n ih =>
      rcases p with ⟨z, t⟩
      change v.ofLp z * (tensorVector (fun _ => v) n).ofLp t = _
      rw [ih t, Fin.prod_univ_castSucc]
      simp [tensorCoordEquiv]
      ring

end QuarticQuery.Paper
