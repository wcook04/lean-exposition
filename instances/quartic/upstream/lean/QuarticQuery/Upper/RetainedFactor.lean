module

public import QuarticQuery.Upper.Circuit

/-!
Finite-coordinate seam for a retained-state amplifier.
Compiled as part of the `QuarticQuery` library target.
It does not implement the full circuit.
The first coordinate is the auxiliary history.  The second is the fixed
original Hilbert register, including its original preparation workspace.
-/

@[expose] public section

namespace QuarticQuery.Upper

variable {Aux Z : Type} [Fintype Aux] [Fintype Z]

/-- The coordinate form of `ξ ⊗ g`, with a designated `Reg Z` subsystem. -/
noncomputable def retainedProduct (ξ : Reg Aux) (g : Reg Z) :
    Reg (Σ _ : Aux, Z) :=
  WithLp.toLp 2 fun p => ξ.ofLp p.1 * g.ofLp p.2

theorem retainedProduct_apply (ξ : Reg Aux) (g : Reg Z) (a : Aux) (z : Z) :
    (retainedProduct ξ g).ofLp ⟨a, z⟩ = ξ.ofLp a * g.ofLp z := rfl

/-- A slice equation is sufficient for exact retained-state factorization. -/
theorem retainedProduct_of_slices (ψ : Reg (Σ _ : Aux, Z))
    (ξ : Reg Aux) (g : Reg Z)
    (h : ∀ a, slice a ψ = (ξ.ofLp a) • g) :
    ψ = retainedProduct ξ g := by
  ext ⟨a, z⟩
  have ha := congrArg (fun v : Reg Z => v.ofLp z) (h a)
  simpa only [slice_apply, PiLp.smul_apply, smul_eq_mul,
    retainedProduct_apply] using ha

/-- The success branch has a unit original state after the whole auxiliary
history is discarded. The second conclusion is the unnormalised mass. -/
theorem retainedProduct_norm_sq (ξ : Reg Aux) (g : Reg Z) :
    ‖retainedProduct ξ g‖ ^ 2 = ‖ξ‖ ^ 2 * ‖g‖ ^ 2 := by
  rw [reg_norm_sq, reg_norm_sq, reg_norm_sq, Fintype.sum_sigma]
  simp only [retainedProduct_apply, norm_mul, mul_pow]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_mul]

end QuarticQuery.Upper
