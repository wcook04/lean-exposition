module

public import QuarticQuery.Upper.GateStateDefs
public import QuarticQuery.Upper.SuccessMass

/-!
Candidate norm bridge for the retained-success state. This file is separate
from the amplifier owner's modules and is not yet native-checked.
-/

public section
namespace QuarticQuery.Upper

variable {N : ℕ} {Z : Type} [Fintype Z]

private theorem firstSuccess_isSome_iff (b : Fin N → Bool) :
    (firstSuccess b).isSome = true ↔ ∃ i, b i = true := by
  cases h : firstSuccess b with
  | some i =>
      constructor
      · intro _
        exact ⟨i, firstSuccess_some h⟩
      · intro _
        rfl
  | none =>
      have hb := (firstSuccess_none_iff b).mp h
      simp [hb]

/-- The two reversible gates are norm-preserving permutations. The route
leaves flags unchanged, so its success mask can be moved before the route.
The XOR marker then changes the all-false initial flags to `S(y i)`. -/
theorem assembledSuccess_norm_sum (o : Z) (S : Z → Bool)
    (v : Fin N → Reg Z) :
    ‖assembledSuccess o S v‖ ^ 2 =
      ∑ y : Fin N → Z,
        if ∃ i, S (y i) = true then
          ∏ i, ‖(v i).ofLp (y i)‖ ^ 2 else 0 := by
  classical
  let M : MarkRouteBasis N Z ≃ MarkRouteBasis N Z :=
    ⟨markWhole S, markWhole S, markWhole_involutive S,
      markWhole_involutive S⟩
  rw [reg_norm_sq]
  simp only [assembledSuccess, PiLp.toLp_apply, apply_ite, norm_zero, ite_pow,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  change (∑ p : MarkRouteBasis N Z,
      if (firstSuccess p.1).isSome then
        ‖(assembledTrials o S v).ofLp p‖ ^ 2 else 0) = _
  calc
    _ = ∑ p : MarkRouteBasis N Z,
        if (firstSuccess p.1).isSome then
          ‖(markWholeGate S (startTrials o v)).ofLp p‖ ^ 2 else 0 := by
        rw [← Equiv.sum_comp (routeWithFlags (N := N) (Z := Z))]
        apply Finset.sum_congr rfl
        intro p _
        simp only [assembledTrials, routeFlagsGate, regCongr_apply,
          Equiv.symm_apply_apply]
        rfl
    _ = ∑ p : MarkRouteBasis N Z,
        if (firstSuccess (markWhole S p).1).isSome then
          ‖(startTrials o v).ofLp p‖ ^ 2 else 0 := by
        rw [← Equiv.sum_comp M]
        apply Finset.sum_congr rfl
        intro p _
        simp only [markWholeGate, regCongr_apply]
        change (if (firstSuccess (M p).1).isSome then
          ‖(startTrials o v).ofLp (M.symm (M p))‖ ^ 2 else 0) = _
        rw [Equiv.symm_apply_apply]
        rfl
    _ = ∑ y : Fin N → Z,
          if ∃ i, S (y i) = true then
            ∏ i, ‖(v i).ofLp (y i)‖ ^ 2 else 0 := by
        let b₀ : Fin N → Bool := fun _ => false
        have hflags (b : Fin N → Bool) :
            (∀ i, b i = false) ↔ b = b₀ := by
          constructor
          · intro h
            funext i
            exact h i
          · rintro rfl i
            rfl
        simp only [Fintype.sum_prod_type]
        simp only [startTrials, markWhole, firstSuccess_isSome_iff,
          hflags, apply_ite, norm_zero, ite_pow,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        conv_lhs =>
          arg 2
          intro b
          rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        have hzsum (b : Fin N → Bool) (y : Fin N → Z) :
            (∑ z : Z,
              if z = o ∧ b = b₀ then
                (∏ i, ‖(v i).ofLp (y i)‖) ^ 2 else 0) =
              if b = b₀ then (∏ i, ‖(v i).ofLp (y i)‖) ^ 2 else 0 := by
          by_cases hb : b = b₀ <;> simp [hb]
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.sum_eq_single b₀]
        · simp [b₀, Finset.prod_pow]
        · intro b _ hb
          simp [hb]
        · simp

/-- Exact success mass, including the zero-success case. -/
theorem assembledSuccess_norm_product (o : Z) (S : Z → Bool)
    (v : Fin N → Reg Z) :
    ‖assembledSuccess o S v‖ ^ 2 =
      (∏ i, ∑ z, ‖(v i).ofLp z‖ ^ 2) -
        (∏ i, ∑ z, if S z = false then ‖(v i).ofLp z‖ ^ 2 else 0) := by
  rw [assembledSuccess_norm_sum]
  simpa only [] using success_mass_product (fun i z => ‖(v i).ofLp z‖ ^ 2) S

end QuarticQuery.Upper
end
