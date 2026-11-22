/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorVerifier

/-!
# Whole-field seeds for the seven-check verifier

Only the four nonzero parameters in the two grid branches are replaced by
whole-field parameters. The explicit partial decoder keeps every other seed
coordinate unchanged and succeeds precisely when all four parameters are nonzero.
-/

namespace PCP.Algebraic.ThreeColorFullFieldSampling

open BinaryPolynomialSpace BinaryLocalCorrection

abbrev RawCallSeed (F σ : Type*) (m c t : ℕ) :=
  (σ → F) × (F × (InnerPoint F m c × InnerSeed F m c t))

abbrev RawGridRandomness (F : Type*) (n m c t : ℕ) :=
  (Fin t → ZMod 2) ×
    (RawCallSeed F (Fin n ⊕ Fin n) m c t × RawCallSeed F (Fin n ⊕ Fin n) m c t)

abbrev RawDerivedSample (F : Type*) (n m c t r : ℕ) :=
  (Fin n → F) × (RawGridRandomness F n m c t × Coefficients t r)

/-- The same seven branch seeds, replacing just the four unit coordinates. -/
def RawBranchSeed (F : Type*) (n m c t : ℕ) : Fin 7 → Type _ :=
  ![EncodedLineLowDegreeTest.Sample F (Fin n) m c t 3,
    EncodedLineLowDegreeTest.Sample F (Fin n ⊕ Fin n) m c t 1,
    EncodedLineLowDegreeTest.Sample F (Fin n ⊕ Fin n) m c t 3,
    EncodedLineLowDegreeTest.Sample F (Fin (n + n) ⊕ Fin (n + n)) m c t 1,
    RawDerivedSample F n m c t 3,
    RawDerivedSample F (n + n) m c t 3,
    (((Fin n → F) × (Fin n → F)) × (Fin t → ZMod 2))]

abbrev RawSample (F : Type*) (n m c t : ℕ) :=
  (i : Fin 7) → RawBranchSeed F n m c t i

variable {F : Type*} [Field F] {σ : Type*} {n m c t r : ℕ}

def padCall (s : BinaryZeroOnGridCorrection.CallSeed F σ m c t) :
    RawCallSeed F σ m c t := (s.1, (s.2.1.val, s.2.2))

def ValidCall (s : RawCallSeed F σ m c t) : Prop := s.2.1 ≠ 0

def unpadCall (s : RawCallSeed F σ m c t) (h : ValidCall s) :
    BinaryZeroOnGridCorrection.CallSeed F σ m c t :=
  (s.1, (Units.mk0 s.2.1 h, s.2.2))

@[simp] theorem validCall_pad (s : BinaryZeroOnGridCorrection.CallSeed F σ m c t) :
    ValidCall (padCall s) := s.2.1.ne_zero

@[simp] theorem pad_unpadCall (s : RawCallSeed F σ m c t) (h : ValidCall s) :
    padCall (unpadCall s h) = s := rfl

@[simp] theorem unpad_padCall (s : BinaryZeroOnGridCorrection.CallSeed F σ m c t)
    (h : ValidCall (padCall s)) : unpadCall (padCall s) h = s := by
  simp only [unpadCall, padCall]
  congr 2
  exact Units.ext rfl

def padDerived (s : DerivedZeroOnGrid.TestSample F n m c t r) :
    RawDerivedSample F n m c t r :=
  (s.1, ((s.2.1.1, (padCall s.2.1.2.1, padCall s.2.1.2.2)), s.2.2))

def ValidDerived (s : RawDerivedSample F n m c t r) : Prop :=
  ValidCall s.2.1.2.1 ∧ ValidCall s.2.1.2.2

def unpadDerived (s : RawDerivedSample F n m c t r) (h : ValidDerived s) :
    DerivedZeroOnGrid.TestSample F n m c t r :=
  (s.1, ((s.2.1.1, (unpadCall s.2.1.2.1 h.1, unpadCall s.2.1.2.2 h.2)), s.2.2))

@[simp] theorem validDerived_pad (s : DerivedZeroOnGrid.TestSample F n m c t r) :
    ValidDerived (padDerived s) := ⟨validCall_pad _, validCall_pad _⟩

@[simp] theorem pad_unpadDerived (s : RawDerivedSample F n m c t r)
    (h : ValidDerived s) : padDerived (unpadDerived s h) = s := rfl

@[simp] theorem unpad_padDerived (s : DerivedZeroOnGrid.TestSample F n m c t r)
    (h : ValidDerived (padDerived s)) : unpadDerived (padDerived s) h = s := by
  simp [unpadDerived, padDerived]

def padBranch (i : Fin 7) : ThreeColorVerifier.BranchSeed F n m c t i →
    RawBranchSeed F n m c t i := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))) i
  · exact id
  · exact id
  · exact id
  · exact id
  · exact padDerived
  · exact padDerived
  · exact id

def ValidBranch (i : Fin 7) : RawBranchSeed F n m c t i → Prop := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))) i
  · exact fun _ => True
  · exact fun _ => True
  · exact fun _ => True
  · exact fun _ => True
  · exact ValidDerived
  · exact ValidDerived
  · exact fun _ => True

def unpadBranch (i : Fin 7) : (s : RawBranchSeed F n m c t i) →
    ValidBranch i s → ThreeColorVerifier.BranchSeed F n m c t i := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))) i
  · exact fun s _ => s
  · exact fun s _ => s
  · exact fun s _ => s
  · exact fun s _ => s
  · exact unpadDerived
  · exact unpadDerived
  · exact fun s _ => s

theorem validBranch_pad (i : Fin 7) (s : ThreeColorVerifier.BranchSeed F n m c t i) :
    ValidBranch i (padBranch i s) := by
  fin_cases i
  all_goals first | exact True.intro | exact validDerived_pad s

theorem pad_unpadBranch (i : Fin 7) (s : RawBranchSeed F n m c t i)
    (h : ValidBranch i s) : padBranch i (unpadBranch i s h) = s := by
  fin_cases i <;> rfl

theorem unpad_padBranch (i : Fin 7) (s : ThreeColorVerifier.BranchSeed F n m c t i)
    (h : ValidBranch i (padBranch i s)) : unpadBranch i (padBranch i s) h = s := by
  fin_cases i
  all_goals first | rfl | exact unpad_padDerived s h

def pad (s : ThreeColorVerifier.Sample F n m c t) : RawSample F n m c t :=
  fun i => padBranch i (s i)

/-- Exactly the four correction parameters must be nonzero. -/
def Valid (s : RawSample F n m c t) : Prop := ∀ i, ValidBranch i (s i)

theorem valid_iff (s : RawSample F n m c t) : Valid s ↔
    (s 4).2.1.2.1.2.1 ≠ 0 ∧ (s 4).2.1.2.2.2.1 ≠ 0 ∧
      (s 5).2.1.2.1.2.1 ≠ 0 ∧ (s 5).2.1.2.2.2.1 ≠ 0 := by
  constructor
  · intro h
    exact ⟨(h 4).1, (h 4).2, (h 5).1, (h 5).2⟩
  · rintro ⟨h1, h2, h3, h4⟩ i
    fin_cases i
    all_goals first | exact True.intro | exact ⟨h1, h2⟩ | exact ⟨h3, h4⟩

def unpad (s : RawSample F n m c t) (h : Valid s) :
    ThreeColorVerifier.Sample F n m c t := fun i => unpadBranch i (s i) (h i)

@[simp] theorem valid_pad (s : ThreeColorVerifier.Sample F n m c t) : Valid (pad s) :=
  fun i => validBranch_pad i (s i)

@[simp] theorem pad_unpad (s : RawSample F n m c t) (h : Valid s) :
    pad (unpad s h) = s := funext fun i => pad_unpadBranch i (s i) (h i)

@[simp] theorem unpad_pad (s : ThreeColorVerifier.Sample F n m c t)
    (h : Valid (pad s)) : unpad (pad s) h = s :=
  funext fun i => unpad_padBranch i (s i) (h i)

theorem pad_injective : Function.Injective (pad (F := F) (n := n) (m := m)
    (c := c) (t := t)) := by
  classical
  intro s s' h
  have he := congrArg (fun x => if hx : Valid x then some (unpad x hx) else none) h
  simpa only [dite_eq_left (valid_pad _), unpad_pad, Option.some.injEq] using he

def embedding : ThreeColorVerifier.Sample F n m c t ↪ RawSample F n m c t :=
  ⟨pad, pad_injective⟩

@[simp] theorem mem_range_embedding (s : RawSample F n m c t) :
    s ∈ Set.range (embedding (F := F) (n := n) (m := m) (c := c) (t := t)) ↔
      Valid s := by
  constructor
  · rintro ⟨a, rfl⟩
    exact valid_pad a
  · intro h
    exact ⟨unpad s h, pad_unpad s h⟩

/-- The explicit decoder only changes each nonzero parameter into its unit. -/
noncomputable def decode (s : RawSample F n m c t) :
    Option (ThreeColorVerifier.Sample F n m c t) := by
  classical
  exact if h : Valid s then some (unpad s h) else none

@[simp] theorem decode_pad (s : ThreeColorVerifier.Sample F n m c t) :
    decode (pad s) = some s := by simp [decode]

theorem decode_of_not_valid (s : RawSample F n m c t) (h : ¬ Valid s) :
    decode s = none := by simp [decode, h]

section Finite

variable [Fintype F] [DecidableEq F]

local instance : Fintype (InnerPoint F m c) := inferInstance
local instance : Fintype (InnerSeed F m c t) := inferInstance
local instance {r : ℕ} : Fintype (Hadamard.TestRandomness t r × InnerSeed F m c t) :=
  inferInstance
local instance {σ : Type*} [Fintype σ] [DecidableEq σ] {r : ℕ} :
    Fintype (EncodedLineLowDegreeTest.Sample F σ m c t r) := inferInstance
local instance {σ : Type*} [Fintype σ] [DecidableEq σ] :
    Fintype (RawCallSeed F σ m c t) := inferInstance
local instance {k : ℕ} : Fintype (RawGridRandomness F k m c t) := inferInstance
local instance {k r : ℕ} : Fintype (RawDerivedSample F k m c t r) := inferInstance
local instance {σ : Type*} [Fintype σ] [DecidableEq σ] :
    Fintype (BinaryZeroOnGridCorrection.CallSeed F σ m c t) := inferInstance
local instance {k : ℕ} : Fintype (DerivedZeroOnGrid.GridRandomness F k m c t) := inferInstance
local instance {k r : ℕ} : Fintype (DerivedZeroOnGrid.TestSample F k m c t r) := inferInstance

/-- All coordinates in the enlarged seed are genuine finite uniform choices. -/
noncomputable instance rawBranchSeedFintype (i : Fin 7) :
    Fintype (RawBranchSeed F n m c t i) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))) i
  all_goals dsimp [RawBranchSeed]; infer_instance

private theorem card_branch_eq (i : Fin 7) :
    Fintype.card (ThreeColorVerifier.BranchSeed F n m c t i) =
      ![Fintype.card (EncodedLineLowDegreeTest.Sample F (Fin n) m c t 3),
        Fintype.card (EncodedLineLowDegreeTest.Sample F (Fin n ⊕ Fin n) m c t 1),
        Fintype.card (EncodedLineLowDegreeTest.Sample F (Fin n ⊕ Fin n) m c t 3),
        Fintype.card (EncodedLineLowDegreeTest.Sample F
          (Fin (n + n) ⊕ Fin (n + n)) m c t 1),
        Fintype.card (DerivedZeroOnGrid.TestSample F n m c t 3),
        Fintype.card (DerivedZeroOnGrid.TestSample F (n + n) m c t 3),
        Fintype.card (((Fin n → F) × (Fin n → F)) × (Fin t → ZMod 2))] i := by
  fin_cases i
  all_goals exact Fintype.card_congr (Equiv.refl _)

omit [Field F] [DecidableEq F] in
private theorem card_rawBranch_eq (i : Fin 7) :
    Fintype.card (RawBranchSeed F n m c t i) =
      ![Fintype.card (EncodedLineLowDegreeTest.Sample F (Fin n) m c t 3),
        Fintype.card (EncodedLineLowDegreeTest.Sample F (Fin n ⊕ Fin n) m c t 1),
        Fintype.card (EncodedLineLowDegreeTest.Sample F (Fin n ⊕ Fin n) m c t 3),
        Fintype.card (EncodedLineLowDegreeTest.Sample F
          (Fin (n + n) ⊕ Fin (n + n)) m c t 1),
        Fintype.card (RawDerivedSample F n m c t 3),
        Fintype.card (RawDerivedSample F (n + n) m c t 3),
        Fintype.card (((Fin n → F) × (Fin n → F)) × (Fin t → ZMod 2))] i := by
  classical
  fin_cases i
  all_goals exact Fintype.card_congr (Equiv.refl _)

/-- Exactly four factors change from `q-1` choices to `q` choices. -/
theorem card_sample_mul_card_pow :
    Fintype.card (ThreeColorVerifier.Sample F n m c t) * Fintype.card F ^ 4 =
      Fintype.card (RawSample F n m c t) * (Fintype.card F - 1) ^ 4 := by
  rw [Fintype.card_pi, Fintype.card_pi]
  simp_rw [card_branch_eq, card_rawBranch_eq]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, mul_one]
  simp only [Fintype.card_prod, Fintype.card_units]
  ring

end Finite

instance rawBranchSeedNonempty (i : Fin 7) : Nonempty (RawBranchSeed F n m c t i) := by
  let s := Classical.choice (ThreeColorVerifier.branchSeedNonempty
    (F := F) (n := n) (m := m) (c := c) (t := t) i)
  exact ⟨padBranch i s⟩

end PCP.Algebraic.ThreeColorFullFieldSampling
