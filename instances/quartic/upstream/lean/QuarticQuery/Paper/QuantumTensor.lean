module

public import QuarticQuery.Upper.Sampler
public import QuarticQuery.Paper.QuantumWorkspace

/-!
# The fresh-workspace state in equation (15)

Compiled as part of the `QuarticQuery` library target.
Toolchain: leanprover/lean4:v4.36.0-rc2, with the repository's lake manifest.

This file constructs the full tensor state. It does not identify that state with
`Upper.stage_samples`: that implementation short-circuits comparisons on its
failure label. The two implementations have the same successful index law.
All costs in `IsCirc` are reads. `Upper.compile_circ` converts them to ordinary
bit queries at a factor of two.

The tensor basis is nested in reverse pivot order. This fixes a basis convention;
reassociating or permuting distinct fresh registers costs no queries.
-/

@[expose] public section

namespace QuarticQuery.Paper

open QuarticQuery.Upper

/-- Ledger: eq-15. A computational basis for `n` fresh copies of a register. -/
@[reducible] def TensorBasis (Z : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => Σ _ : Z, TensorBasis Z n

/-- Ledger: eq-15. The tensor workspace is a finite register. -/
@[reducible] def tensorBasisFintype {Z : Type} [Fintype Z] :
    (n : ℕ) → Fintype (TensorBasis Z n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => by
      letI := tensorBasisFintype (Z := Z) n
      exact inferInstanceAs (Fintype (Σ _ : Z, TensorBasis Z n))

attribute [instance] tensorBasisFintype

/-- Ledger: eq-15. Every fresh register starts in the same fixed basis state. -/
def tensorOrigin {Z : Type} (o : Z) : (n : ℕ) → TensorBasis Z n
  | 0 => ()
  | n + 1 => ⟨o, tensorOrigin o n⟩

/-- Ledger: eq-15. The tensor product, expressed by its computational-basis amplitudes. -/
noncomputable def tensorVector {Z : Type} [Fintype Z] (ψ : ℕ → Reg Z) :
    (n : ℕ) → Reg (TensorBasis Z n)
  | 0 => rket ()
  | n + 1 => WithLp.toLp 2 fun z =>
      (ψ n).ofLp z.1 * (tensorVector ψ n).ofLp z.2

/-- Ledger: eq-15. One tensor slice is the corresponding scalar times the remaining tensor. -/
theorem tensorVector_slice {Z : Type} [Fintype Z] (ψ : ℕ → Reg Z)
    (n : ℕ) (z : Z) :
    slice z (tensorVector ψ (n + 1)) = (ψ n).ofLp z • tensorVector ψ n := by
  ext w
  simp only [tensorVector, slice_apply, PiLp.smul_apply, smul_eq_mul]

/-- Ledger: eq-15. Run a preparation on each fresh register, retaining every register. -/
noncomputable def tensorPreparation {Z : Type} [Fintype Z]
    (F : ℕ → Reg Z ≃ₗᵢ[ℂ] Reg Z) :
    (n : ℕ) → Reg (TensorBasis Z n) ≃ₗᵢ[ℂ] Reg (TensorBasis Z n)
  | 0 => LinearIsometryEquiv.refl ℂ _
  | n + 1 => (leftOp (F n)).trans
      (sigmaOp fun _ : Z => tensorPreparation F n)

/-- Ledger: eq-15. The tensor preparation really produces the tensor of the prepared states. -/
theorem tensorPreparation_state {Z : Type} [Fintype Z]
    (F : ℕ → Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (n : ℕ) :
    tensorPreparation F n (rket (tensorOrigin o n)) =
      tensorVector (fun b => F b (rket o)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      apply sigma_ext
      intro z
      change slice z (sigmaOp (fun _ : Z => tensorPreparation F n)
          (leftOp (F n) (rket (⟨o, tensorOrigin o n⟩ : Σ _ : Z, TensorBasis Z n)))) = _
      rw [slice_sigmaOp, slice_leftOp_rket, map_smul, ih, tensorVector_slice]

/-- Ledger: eq-15. The read count is the number of copies times the common comparison count. -/
theorem tensorPreparation_isCirc {ι Z : Type} [Fintype Z] {c : ℕ}
    (F : ℕ → BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z)
    (hF : ∀ b, IsCirc c (F b)) (n : ℕ) :
    IsCirc (n * c) (fun x => tensorPreparation (fun b => F b x) n) := by
  induction n with
  | zero =>
      simpa only [Nat.zero_mul, tensorPreparation] using
        (IsCirc.gate (ι := ι) (LinearIsometryEquiv.refl ℂ (Reg Unit)))
  | succ n ih =>
      have h := (IsCirc.left (hF n)).comp
        (IsCirc.sigma fun _ : Z => ih)
      simpa only [tensorPreparation, Nat.succ_mul, Nat.add_comm] using h

/-- Ledger: eq-15. The uniform state on the candidate register. -/
noncomputable def uniformIndex {Col : Type} [Fintype Col] : Reg Col :=
  WithLp.toLp 2 fun _ => ((Real.sqrt ((Fintype.card Col : ℝ)⁻¹) : ℝ) : ℂ)

/-- Ledger: eq-15. The uniform index state has norm one. -/
theorem uniformIndex_norm {Col : Type} [Fintype Col] [Nonempty Col] :
    ‖(uniformIndex : Reg Col)‖ = 1 := by
  have hm : (Fintype.card Col : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsq : ‖(uniformIndex : Reg Col)‖ ^ 2 = 1 := by
    rw [reg_norm_sq]
    simp only [uniformIndex, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (inv_nonneg.mpr (Nat.cast_nonneg _))]
    simp [hm]
  nlinarith [norm_nonneg (uniformIndex : Reg Col)]

/-- Ledger: eq-15. A coherent comparison family with a common workspace prepares
exactly the uniform candidate register tensored with one fresh complete comparison
state per pivot. The slice identity is the coordinate form of equation (15), and
`IsCirc (t*c)` supplies the circuit witness. No comparison is skipped on failure.
The pivots used are `p 0, ..., p (t-1)`; the values `p b` for `b ≥ t` are irrelevant.
-/
theorem equation_15 {ι Col Z : Type} [Fintype Col] [Nonempty Col] [Fintype Z]
    {c : ℕ} (o : Z)
    (F : Col → Col → BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z)
    (hF : ∀ i j, IsCirc c (F i j)) (p : ℕ → Col) (t : ℕ) :
    ∃ (i₀ : Col)
      (A : BitInput ι → Reg (Σ _ : Col, TensorBasis Z t) ≃ₗᵢ[ℂ]
        Reg (Σ _ : Col, TensorBasis Z t)),
      IsCirc (t * c) A ∧
      ∀ x i, slice i (A x (rket (⟨i₀, tensorOrigin o t⟩ :
          Σ _ : Col, TensorBasis Z t))) =
        (((Real.sqrt ((Fintype.card Col : ℝ)⁻¹) : ℝ) : ℂ) •
          tensorVector (fun b => F i (p b) x (rket o)) t) := by
  classical
  obtain ⟨i₀⟩ := (inferInstance : Nonempty Col)
  obtain ⟨U, hU⟩ := exists_unit_gate (norm_rket i₀)
    (uniformIndex_norm (Col := Col))
  let V : Col → BitInput ι → Reg (TensorBasis Z t) ≃ₗᵢ[ℂ] Reg (TensorBasis Z t) :=
    fun i x => tensorPreparation (fun b => F i (p b) x) t
  have hV : ∀ i, IsCirc (t * c) (V i) := fun i =>
    tensorPreparation_isCirc (fun b => F i (p b)) (fun b => hF i (p b)) t
  let A : BitInput ι → Reg (Σ _ : Col, TensorBasis Z t) ≃ₗᵢ[ℂ]
      Reg (Σ _ : Col, TensorBasis Z t) :=
    fun x => (leftOp U).trans (sigmaOp fun i => V i x)
  refine ⟨i₀, A, ?_, ?_⟩
  · have h := (IsCirc.left (IsCirc.gate (ι := ι) U)).comp (IsCirc.sigma hV)
    simpa only [Nat.zero_add] using h
  · intro x i
    change slice i (sigmaOp (fun i => V i x)
      (leftOp U (rket (⟨i₀, tensorOrigin o t⟩ : Σ _ : Col, TensorBasis Z t)))) = _
    rw [slice_sigmaOp, slice_leftOp_rket, map_smul, hU]
    change ((uniformIndex : Reg Col).ofLp i) •
      tensorPreparation (fun b => F i (p b) x) t (rket (tensorOrigin o t)) = _
    rw [tensorPreparation_state]
    rfl

/-- Ledger: claim-success-prob. All comparison result bits are true, without dropping earlier workspaces. -/
def tensorGood {Z : Type} (out : ℕ → Z → Bool) :
    (n : ℕ) → TensorBasis Z n → Bool
  | 0, _ => true
  | n + 1, z => out n z.1 && tensorGood out n z.2

/-- Ledger: claim-success-prob. In the literal fresh-register construction, the
success mass factors as the product of the individual comparison success masses.
The case `t=0` is the empty product, equal to one. -/
theorem tensor_success_mass {Z : Type} [Fintype Z]
    (ψ : ℕ → Reg Z) (out : ℕ → Z → Bool) (t : ℕ) :
    lawOf (tensorVector ψ t) (tensorGood out t) true =
      ∏ b ∈ Finset.range t, lawOf (ψ b) (out b) true := by
  classical
  induction t with
  | zero =>
      simp only [Finset.range_zero, Finset.prod_empty, tensorVector, tensorGood,
        lawOf, ite_true]
      change (∑ z : Unit, ‖(rket () : Reg Unit).ofLp z‖ ^ 2) = 1
      rw [← reg_norm_sq, norm_rket]
      norm_num
  | succ t ih =>
      rw [lawOf_sigma]
      calc
        (∑ z : Z, lawOf (slice z (tensorVector ψ (t + 1)))
            (fun w => tensorGood out (t + 1) ⟨z, w⟩) true)
            = ∑ z : Z, (if out t z = true then ‖(ψ t).ofLp z‖ ^ 2 else 0) *
                (∏ b ∈ Finset.range t, lawOf (ψ b) (out b) true) := by
                  apply Finset.sum_congr rfl
                  intro z _
                  cases hz : out t z with
                  | false => simp [tensorGood, hz, lawOf]
                  | true =>
                      simp only [tensorGood, hz, Bool.true_and, ite_true]
                      rw [tensorVector_slice, lawOf_smul, ih]
        _ = lawOf (ψ t) (out t) true *
              (∏ b ∈ Finset.range t, lawOf (ψ b) (out b) true) := by
                rw [← Finset.sum_mul]
                simp only [lawOf]
        _ = ∏ b ∈ Finset.range (t + 1), lawOf (ψ b) (out b) true := by
              rw [Finset.prod_range_succ]
              ring


/-- Ledger: claim-success-prob. Keep the candidate index exactly on success. -/
noncomputable def tensorIndexOut {Col Z : Type} (out : Col → ℕ → Z → Bool) (t : ℕ)
    (z : Σ _ : Col, TensorBasis Z t) : Option Col :=
  if tensorGood (out z.1) t z.2 then some z.1 else none

open Classical in
/-- Ledger: claim-success-prob. Labelling a success by a fixed candidate
selects precisely that candidate's success mass. -/
theorem lawOf_keep_candidate {Z Col : Type} [Fintype Z]
    (ψ : Reg Z) (out : Z → Bool) (i j : Col) :
    lawOf ψ (fun z => if out z then some i else none) (some j) =
      if i = j then lawOf ψ out true else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [ite_true, lawOf]
    apply Finset.sum_congr rfl
    intro z _
    cases hout : out z <;> simp [hout]
  · rw [if_neg hij]
    unfold lawOf
    apply Finset.sum_eq_zero
    intro z _
    cases hout : out z <;> simp [hout, hij]

/-- Ledger: claim-success-prob. Equation (15) gives successful index mass
`m⁻¹` times the product of the comparison success probabilities. This theorem
uses the actual full state slices, so it is independent of the short-circuit
implementation of `Upper.stage_samples`. -/
theorem equation_15_index_law {Col Z : Type} [Fintype Col] [Fintype Z]
    (ψ : Col → ℕ → Reg Z) (out : Col → ℕ → Z → Bool) (t : ℕ)
    (v : Reg (Σ _ : Col, TensorBasis Z t))
    (hv : ∀ i, slice i v =
      (((Real.sqrt ((Fintype.card Col : ℝ)⁻¹) : ℝ) : ℂ) • tensorVector (ψ i) t))
    (i : Col) :
    lawOf v (tensorIndexOut out t) (some i) =
      (∏ b ∈ Finset.range t, lawOf (ψ i b) (out i b) true) / Fintype.card Col := by
  classical
  have hc : ‖(((Real.sqrt ((Fintype.card Col : ℝ)⁻¹) : ℝ) : ℂ))‖ ^ 2 =
      (Fintype.card Col : ℝ)⁻¹ := by
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact Real.sq_sqrt (by positivity)
  rw [lawOf_sigma, Finset.sum_eq_single i]
  · rw [hv, lawOf_smul]
    change ‖(((Real.sqrt ((Fintype.card Col : ℝ)⁻¹) : ℝ) : ℂ))‖ ^ 2 *
      lawOf (tensorVector (ψ i) t)
        (fun z => if tensorGood (out i) t z then some i else none) (some i) = _
    rw [lawOf_keep_candidate, if_pos rfl, tensor_success_mass, hc]
    ring
  · intro j _ hji
    rw [hv, lawOf_smul]
    change _ * lawOf (tensorVector (ψ j) t)
      (fun z => if tensorGood (out j) t z then some j else none) (some i) = 0
    rw [lawOf_keep_candidate, if_neg hji, mul_zero]
  · simp

/-- Ledger: claim-success-prob. Sum the successful index masses to obtain
`W/m`. For arbitrary input vectors this is a mass identity. Applied to the
normalized unitary witness in `equation_15`, it is a probability identity. -/
theorem equation_15_success_probability {Col Z : Type} [Fintype Col] [Fintype Z]
    (ψ : Col → ℕ → Reg Z) (out : Col → ℕ → Z → Bool) (t : ℕ)
    (v : Reg (Σ _ : Col, TensorBasis Z t))
    (hv : ∀ i, slice i v =
      (((Real.sqrt ((Fintype.card Col : ℝ)⁻¹) : ℝ) : ℂ) • tensorVector (ψ i) t)) :
    (∑ i, lawOf v (tensorIndexOut out t) (some i)) =
      (∑ i, ∏ b ∈ Finset.range t, lawOf (ψ i b) (out i b) true) /
        Fintype.card Col := by
  simp only [equation_15_index_law ψ out t v hv, Finset.sum_div]

/-- Ledger: claim-success-prob. Conditioning is asserted only when the
successful mass is positive. Cancelling `m` yields `w_i/W` exactly. For the
normalized unitary witness in `equation_15` this is its conditional probability.
The more general statement here is an identity of normalized positive masses. -/
theorem equation_15_conditional_index {Col Z : Type} [Fintype Col] [Nonempty Col]
    [Fintype Z] (ψ : Col → ℕ → Reg Z) (out : Col → ℕ → Z → Bool) (t : ℕ)
    (v : Reg (Σ _ : Col, TensorBasis Z t))
    (hv : ∀ i, slice i v =
      (((Real.sqrt ((Fintype.card Col : ℝ)⁻¹) : ℝ) : ℂ) • tensorVector (ψ i) t))
    (hW : 0 < ∑ i, ∏ b ∈ Finset.range t, lawOf (ψ i b) (out i b) true) (i : Col) :
    0 < (∑ j, lawOf v (tensorIndexOut out t) (some j)) ∧
    lawOf v (tensorIndexOut out t) (some i) /
        (∑ j, lawOf v (tensorIndexOut out t) (some j)) =
      (∏ b ∈ Finset.range t, lawOf (ψ i b) (out i b) true) /
        (∑ j, ∏ b ∈ Finset.range t, lawOf (ψ j b) (out j b) true) := by
  have hm : (0 : ℝ) < Fintype.card Col := by
    exact_mod_cast Fintype.card_pos
  constructor
  · rw [equation_15_success_probability ψ out t v hv]
    exact div_pos hW hm
  · rw [equation_15_index_law ψ out t v hv,
      equation_15_success_probability ψ out t v hv]
    exact div_div_div_cancel_right₀ hm.ne' _ _


/-- Ledger: construct-sampler. The literal tensor construction is a coherent
sampler with exactly the successful masses used by the tournament. Its input
circuit and labelling are fixed before the oracle input is supplied. -/
theorem quantumTensorStage {ι Col Z : Type} [Fintype Col] [Nonempty Col] [Fintype Z]
    {c : ℕ} (o : Z)
    (F : Col → Col → BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z)
    (hF : ∀ i j, IsCirc c (F i j)) (out : Col → Col → Z → Bool)
    (a : BitInput ι → Col → Col → ℝ)
    (ha : ∀ x i j, lawOf (F i j x (rket o)) (out i j) true = a x i j)
    (p : ℕ → Col) (t : ℕ) :
    ∃ L : BitInput ι → Option Col → ℝ,
      Samples (t * c) L ∧
      ∀ x i, L x (some i) =
        (∏ b ∈ Finset.range t, a x i (p b)) / Fintype.card Col := by
  obtain ⟨i₀, A, hA, hstate⟩ := equation_15 o F hF p t
  let O : (Σ _ : Col, TensorBasis Z t) → Option Col :=
    tensorIndexOut (fun i b => out i (p b)) t
  let L : BitInput ι → Option Col → ℝ := fun x b =>
    lawOf (A x (rket (⟨i₀, tensorOrigin o t⟩ : Σ _ : Col, TensorBasis Z t))) O b
  refine ⟨L, ?_, ?_⟩
  · exact ⟨Σ _ : Col, TensorBasis Z t, inferInstance, ⟨i₀, tensorOrigin o t⟩,
      O, A, hA, fun _ _ => rfl⟩
  · intro x i
    have h := equation_15_index_law
      (fun i b => F i (p b) x (rket o)) (fun i b => out i (p b)) t
      (A x (rket (⟨i₀, tensorOrigin o t⟩ : Σ _ : Col, TensorBasis Z t)))
      (hstate x) i
    simpa only [ha] using h

/-- Ledger: construct-sampler. A finite comparison family supplied through
`Samples` can be put into one common finite workspace and then used in the
literal tensor preparation. The resulting coherent sampler has the exact
product successful-index law and uses `t*c` logical reads. The full tensor
identity is proved inside `quantumTensorStage` through `equation_15`.
-/
theorem quantumTensorStage_of_samples {ι Col : Type} [Fintype Col] [Nonempty Col]
    {c : ℕ} {a : BitInput ι → Col → Col → ℝ}
    (hcmp : ∀ i j, Samples c fun x b => bern (a x i j) b)
    (p : ℕ → Col) (t : ℕ) :
    ∃ L : BitInput ι → Option Col → ℝ,
      Samples (t * c) L ∧
      ∀ x i, L x (some i) =
        (∏ b ∈ Finset.range t, a x i (p b)) / Fintype.card Col := by
  obtain ⟨Z, instZ, o, out, F, hF, hlaw⟩ :=
    quantumWorkspace_uniformize (J := Col × Col)
      (fun ij => hcmp ij.1 ij.2)
  letI := instZ
  refine quantumTensorStage o (fun i j => F (i, j))
    (fun i j => hF (i, j)) (fun _ _ => out) a ?_ p t
  intro x i j
  simpa [bern] using hlaw (i, j) x true

end QuarticQuery.Paper
