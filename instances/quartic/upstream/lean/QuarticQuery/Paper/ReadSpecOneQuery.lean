module

public import QuarticQuery.Upper.Compile

/-!
One-query physical realization of a signed-involution `ReadSpec` in the
supplied model. This is a candidate, not a native-checked theorem. It uses a
larger encoded subspace and the model's free input-independent unitary
extension. No `sorry` or custom axiom is introduced.
-/

public section
namespace QuarticQuery.Upper

variable {ι Z : Type} [Fintype ι] [Inhabited ι] [Fintype Z] {w : ℕ}

private def readSign (R : ReadSpec ι Z) (z : Z) : ℂ :=
  if R.sign z then -1 else 1

/-- The `z`-th codeword, including the oracle answer and the permuted label
in its true sector. The two sectors each contribute half the norm. -/
noncomputable def readBasis (e : Z ↪ Fin (w + 1))
    (R : ReadSpec ι Z) (z : Z) : State ι w :=
  (((Real.sqrt 2)⁻¹ : ℂ) •
    ((ket (R.addr z, false, e z) : State ι w) +
      readSign R z • ket (R.addr z, true, e (R.perm z))))

theorem readBasis_orthonormal (e : Z ↪ Fin (w + 1))
    (R : ReadSpec ι Z) : Orthonormal ℂ (readBasis e R) := by
  classical
  rw [orthonormal_iff_ite]
  intro z z'
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hR : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * 2 = (1 : ℝ) := by
    field_simp [hs0]
    nlinarith [hs]
  have hC : (((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * 2 : ℝ) : ℂ) = 1 := by
    exact_mod_cast hR
  by_cases h : z = z'
  · subst z'
    simp only [readBasis, inner_smul_left, inner_smul_right,
      inner_add_left, inner_add_right, inner_ket]
    cases hz : R.sign z <;>
      simp [readSign, hz]
      <;> convert hC using 1 <;> norm_cast <;> ring
  · have hff : (R.addr z, false, e z) ≠ (R.addr z', false, e z') := by
      intro he
      exact h (e.injective (congrArg (fun p : Basis ι w => p.2.2) he))
    have htt : (R.addr z, true, e (R.perm z)) ≠
        (R.addr z', true, e (R.perm z')) := by
      intro he
      have hp := e.injective (congrArg (fun p : Basis ι w => p.2.2) he)
      exact h (by calc
        z = R.perm (R.perm z) := (R.perm_perm z).symm
        _ = R.perm (R.perm z') := congrArg R.perm hp
        _ = z' := R.perm_perm z')
    have hft : (R.addr z, false, e z) ≠
        (R.addr z', true, e (R.perm z')) := by
      intro he
      have := congrArg (fun p : Basis ι w => p.2.1) he
      contradiction
    have htf : (R.addr z, true, e (R.perm z)) ≠
        (R.addr z', false, e z') := by
      intro he
      have := congrArg (fun p : Basis ι w => p.2.1) he
      contradiction
    simp only [readBasis, inner_smul_left, inner_smul_right,
      inner_add_left, inner_add_right, inner_ket]
    simp [h, hff, htt, hft, htf]

/-- Direct basis action of the physical bit oracle on the codewords. -/
theorem bitOracle_readBasis (e : Z ↪ Fin (w + 1))
    (R : ReadSpec ι Z) (x : BitInput ι) (z : Z) :
    bitOracle x (readBasis e R z) =
      R.coef x z • readBasis e R (R.dest x z) := by
  have hlin : bitOracle x (readBasis e R z) =
      (((Real.sqrt 2)⁻¹ : ℂ) •
        ((ket (flipPoint x (R.addr z, false, e z)) : State ι w) +
          readSign R z • ket (flipPoint x (R.addr z, true, e (R.perm z))))) := by
    simp [readBasis, bitOracle_smul, bitOracle_add, bitOracle_ket, smul_add]
  rw [hlin]
  cases hx : x (R.addr z)
  · cases hz : R.sign z <;>
      simp [readBasis, readSign, ReadSpec.coef, ReadSpec.dest,
        flipPoint, hx, hz]
  · cases hz : R.sign z <;>
      simp [readBasis, readSign, ReadSpec.coef, ReadSpec.dest,
        flipPoint, hx, R.addr_perm, R.sign_perm, R.perm_perm, hz, smul_add]
      <;> abel

/-- The codeword family intertwines one physical query with the complete
logical read on every complex superposition. -/
theorem readEmbedding (e : Z ↪ Fin (w + 1)) (R : ReadSpec ι Z) :
    ∃ E : Reg Z →ₗᵢ[ℂ] State ι w,
      ∀ x ψ, bitOracle x (E ψ) = E (R.op x ψ) := by
  let E := embOrth (readBasis e R) (readBasis_orthonormal e R)
  refine ⟨E, fun x ψ => ?_⟩
  let f : Reg Z →ₗ[ℂ] State ι w :=
    (bitOracleL x).toLinearEquiv.toLinearMap ∘ₗ E.toLinearMap
  let g : Reg Z →ₗ[ℂ] State ι w :=
    E.toLinearMap ∘ₗ (R.op x).toLinearEquiv.toLinearMap
  have hfg : ∀ z, f (rket z) = g (rket z) := by
    intro z
    change bitOracle x (E (rket z)) = E (R.op x (rket z))
    rw [embOrth_rket, ReadSpec.op_rket, map_smul, embOrth_rket]
    exact bitOracle_readBasis e R x z
  exact reg_map_ext f g hfg ψ

/-- Generic one-query realization in this exact physical model. -/
theorem compile_read_one (e : Z ↪ Fin (w + 1)) (R : ReadSpec ι Z) :
    ∃ P : AdaptiveProgram ι w → AdaptiveProgram ι w, ∀ next,
      (P next).queryCap = 1 + next.queryCap ∧
      ∀ x ψ b, (P next).outputMass x (clEmb e ψ) b =
        next.outputMass x (clEmb e (R.op x ψ)) b := by
  obtain ⟨E, hE⟩ := readEmbedding e R
  obtain ⟨G₁, hG₁⟩ := exists_extend (clEmb (ι := ι) e) E
  obtain ⟨G₃, hG₃⟩ := exists_extend E (clEmb (ι := ι) e)
  refine ⟨fun next => .unitary G₁ (.query (.unitary G₃ next)),
    fun next => ⟨by simp [AdaptiveProgram.queryCap], ?_⟩⟩
  intro x ψ b
  simp only [AdaptiveProgram.outputMass, hG₁, hE, hG₃]

/-- Induction over the existing `IsCirc` syntax improves its physical cap to
one query per read, without changing the logical isometry or its output law. -/
theorem compile_circ_one (e : Z ↪ Fin (w + 1))
    {n : ℕ} {F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z}
    (hF : IsCirc n F) :
    ∃ K : AdaptiveProgram ι w → AdaptiveProgram ι w, ∀ next,
      (K next).queryCap ≤ n + next.queryCap ∧
      ∀ x ψ b, (K next).outputMass x (clEmb e ψ) b =
        next.outputMass x (clEmb e (F x ψ)) b := by
  induction hF with
  | gate U =>
      obtain ⟨G, hG⟩ := exists_extend (clEmb (ι := ι) e)
        ((clEmb (ι := ι) e).comp U.toLinearIsometry)
      refine ⟨fun next => .unitary G next,
        fun next => ⟨by simp [AdaptiveProgram.queryCap], ?_⟩⟩
      intro x ψ b
      simp only [AdaptiveProgram.outputMass, hG]
      rfl
  | @step m F h R U ih =>
      obtain ⟨P, hP⟩ := ih
      obtain ⟨Q, hQ⟩ := compile_read_one e R
      obtain ⟨G, hG⟩ := exists_extend (clEmb (ι := ι) e)
        ((clEmb (ι := ι) e).comp U.toLinearIsometry)
      refine ⟨fun next => P (Q (.unitary G next)),
        fun next => ⟨?_, ?_⟩⟩
      · have h₁ := (hP (Q (.unitary G next))).1
        have h₂ := (hQ (.unitary G next)).1
        simp only [AdaptiveProgram.queryCap] at h₂
        change (P (Q (.unitary G next))).queryCap ≤ (m + 1) + next.queryCap
        omega
      · intro x ψ b
        rw [(hP _).2, (hQ _).2]
        simp only [AdaptiveProgram.outputMass, hG]
        rfl


theorem Samples.runs_one {α : Type} [Fintype α]
    {n : ℕ} {L : BitInput ι → α → ℝ} (h : Samples n L) :
    Runs n L := by
  classical
  obtain ⟨Z, _, o, out, F, hF, hL⟩ := h
  refine ⟨Fintype.card Z, fun w hw => ?_⟩
  have hcard : Fintype.card Z ≤ Fintype.card (Fin (w + 1)) := by simp; omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  obtain ⟨P, hP⟩ := compile_circ_one e hF
  let g : AdaptiveProgram ι w → AdaptiveProgram ι w :=
    fun n => .unitary (swapGate (default, false, 0) (clPoint e o)) n
  refine ⟨fun k => g (P (measureAll e (fun z => k (out z)) Finset.univ.toList)),
    fun k d hk => ⟨?_, fun x b => ?_⟩⟩
  · have h1 := (hP (measureAll e (fun z => k (out z)) Finset.univ.toList)).1
    have h2 := queryCap_measureAll e (fun z => k (out z)) (fun z => hk (out z)) Finset.univ.toList
    simp only [g, AdaptiveProgram.queryCap]
    omega
  · simp only [g, AdaptiveProgram.outputMass]
    have hs : swapGate (ι := ι) (w := w) (default, false, 0) (clPoint e o) startState =
        clEmb e (rket o) := by
      rw [clEmb_rket]
      exact swapGate_ket _ _
    rw [hs, (hP _).2, outputMass_measureAll e _ x b _ (Finset.nodup_toList _) _ ?_]
    · simp only [clEmb_apply_cl, hL, lawOf, Finset.sum_mul]
      rw [Finset.sum_map_toList, Finset.sum_comm]
      · refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_eq_single (out z)]
        · simp
        · intro a _ ha
          simp [Ne.symm ha]
        · simp
    · intro p hp
      exact clEmb_apply_of_ne e _ p fun z => hp z (Finset.mem_toList.2 (Finset.mem_univ z))


end QuarticQuery.Upper
end
