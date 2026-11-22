module

public import QuarticCorpus.Independent.ModelZero.Spec
public import QuarticQuery.Model.Quantum
public import QuarticCorpus.Independent.Semantics

/-!
General zero-query characterizations for every finite Boolean promise.
The new quantum induction covers every initial vector, not just normalized
vectors. Numerical minima are connected to budgets using attained minima.
-/

@[expose] public section

set_option autoImplicit false

namespace QuarticQuery.Independent.ModelZero

theorem labelsAgree_iff_constant {ι : Type} (f : PartialBool ι) :
    LabelsAgree f ↔ ConstantOnPromise f := by
  classical
  constructor
  · intro h
    by_cases hex : ∃ x b, f x = some b
    · obtain ⟨x, b, hb⟩ := hex
      exact ⟨b, fun y c hc => h y x c b hc hb⟩
    · exact ⟨false, fun x b hb => False.elim (hex ⟨x, b, hb⟩)⟩
  · rintro ⟨a, ha⟩ x y b c hb hc
    exact (ha x b hb).trans (ha y c hc).symm

theorem zero_quantum_mass_input_independent {ι : Type} [Fintype ι] {w : ℕ}
    (A : AdaptiveProgram ι w) (hA : A.queryCap ≤ 0)
    (x y : BitInput ι) (ψ : State ι w) (b : Bool) :
    A.outputMass x ψ b = A.outputMass y ψ b := by
  induction A generalizing ψ with
  | output a => rfl
  | unitary U next ih => exact ih hA (U ψ)
  | query next ih =>
      change 1 + next.queryCap ≤ 0 at hA
      omega
  | measure S yes no ihy ihn =>
      change max yes.queryCap no.queryCap ≤ 0 at hA
      have hy : yes.queryCap ≤ 0 := (le_max_left _ _).trans hA
      have hn : no.queryCap ≤ 0 := (le_max_right _ _).trans hA
      change yes.outputMass x (project S ψ) b +
        no.outputMass x (ψ - project S ψ) b =
        yes.outputMass y (project S ψ) b +
        no.outputMass y (ψ - project S ψ) b
      rw [ihy hy, ihn hn]

theorem labelsAgree_of_RLe_zero {ι : Type} {f : PartialBool ι}
    (h : RLe f 0) : LabelsAgree f := by
  intro x y b c hb hc
  cases b <;> cases c
  · rfl
  · exact False.elim (SemanticReview.both_labels_preclude_zero f x y hb hc h)
  · exact False.elim (SemanticReview.both_labels_preclude_zero f y x hc hb h)
  · rfl

theorem labelsAgree_DLe_zero {ι : Type} {f : PartialBool ι}
    (h : LabelsAgree f) : DLe f 0 := by
  obtain ⟨b, hb⟩ := (labelsAgree_iff_constant f).mp h
  refine ⟨.leaf b, by simp, ?_⟩
  intro x c hc
  exact (hb x c hc).symm

theorem DLe_zero_iff {ι : Type} (f : PartialBool ι) :
    DLe f 0 ↔ LabelsAgree f :=
  ⟨fun h => labelsAgree_of_RLe_zero h.toRLe, labelsAgree_DLe_zero⟩

theorem RLe_zero_iff {ι : Type} (f : PartialBool ι) :
    RLe f 0 ↔ LabelsAgree f :=
  ⟨labelsAgree_of_RLe_zero, fun h => (labelsAgree_DLe_zero h).toRLe⟩

theorem QLe_zero_iff {ι : Type} [Fintype ι] (f : PartialBool ι) :
    QLe f 0 ↔ LabelsAgree f := by
  constructor
  · intro h
    rcases h with h | ⟨w, ψ, A, hψ, hcap, hcorrect⟩
    · exact (labelsAgree_iff_constant f).mpr h
    · intro x y b c hb hc
      have hb' := hcorrect x b hb
      have hc' := hcorrect y c hc
      rw [zero_quantum_mass_input_independent A hcap y x ψ c] at hc'
      have hsum := A.outputMass_true_add_false x ψ
      rw [hψ] at hsum
      cases b <;> cases c <;> first | rfl | (norm_num at hsum; linarith)
  · intro h
    exact Or.inl ((labelsAgree_iff_constant f).mp h)

theorem D_zero_iff {ι : Type} [Fintype ι] (f : PartialBool ι) :
    D f = 0 ↔ LabelsAgree f := by
  rw [← Nat.le_zero, D_le_iff, DLe_zero_iff]

theorem R_zero_iff {ι : Type} [Fintype ι] (f : PartialBool ι) :
    R f = 0 ↔ LabelsAgree f := by
  rw [← Nat.le_zero, R_le_iff, RLe_zero_iff]

theorem Q_zero_iff {ι : Type} [Fintype ι] (f : PartialBool ι) :
    Q f = 0 ↔ LabelsAgree f := by
  rw [← Nat.le_zero, Q_le_iff, QLe_zero_iff]

/-- A single common promise has the three expected zero-cost meanings. -/
theorem zero_query_characterization {ι : Type} [Fintype ι] (f : PartialBool ι) :
    (D f = 0 ↔ LabelsAgree f) ∧
    (R f = 0 ↔ LabelsAgree f) ∧
    (Q f = 0 ↔ LabelsAgree f) :=
  ⟨D_zero_iff f, R_zero_iff f, Q_zero_iff f⟩

/-- A concrete discriminator for the independent, input-uniform target. -/
theorem identity_labels_disagree :
    ¬ LabelsAgree SemanticReview.oneBitIdentity := by
  intro h
  have hf := h (fun _ => false) (fun _ => true) false true rfl rfl
  cases hf

theorem identity_Q_eq_one : Q SemanticReview.oneBitIdentity = 1 := by
  have hne : Q SemanticReview.oneBitIdentity ≠ 0 :=
    fun h => identity_labels_disagree ((Q_zero_iff _).mp h)
  have hle := Q_le_card SemanticReview.oneBitIdentity
  norm_num at hle
  omega

end QuarticQuery.Independent.ModelZero
