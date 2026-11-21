import PCP.Complexity.NumericDifferenceWords

/-! # Complete difference consistency callback from its actual numeric seed -/

namespace PCP.Lang.NumericDifference

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode ThreeColorVerifier

variable {t n m : ℕ} [NeZero t]

def branch : Stmt 120 40 := call (by decide) (by decide) DifferenceBranch.program

def program : Stmt 120 40 := .seq load branch

def index (t n m : ℕ) [NeZero t]
    (z : BinaryDifferenceConsistency.Query (Field t) (Fin n) t 3) : ℕ :=
  (ThreeColorQueryIndex.equiv (m := m) (c := 4) (fieldEquiv t)
    (BooleanCoefficientIndex.coefficientEquiv t 1) (BooleanCoefficientIndex.coefficientEquiv t 3)
    (differenceCheckQuery z)).val

def queries (m : ℕ) (s : Sample t n) : List ℕ :=
  (ComputableBinaryDifferenceConsistency.queries (by decide : 1 ≤ 3) s.1.1 s.1.2 s.2).map
    (index t n m)

def verdict (m : ℕ) (s : Sample t n) (qs : List ℕ) (bs : List Bool) : Bool :=
  decide (ComputableBinaryDifferenceConsistency.check (by decide : 1 ≤ 3)
    (fun x p => BinarySeedPadding.boolEquiv
      (QueryTree.answersOracle qs bs (index t n m (.inl (x, p)))))
    (fun x p => BinarySeedPadding.boolEquiv
      (QueryTree.answersOracle qs bs (index t n m (.inr (x, p))))) s.1.1 s.1.2 s.2 = 0)

attribute [local irreducible] DifferenceBranch.program branch

theorem branch_run (s : Sample t n) (qs : List ℕ) (bs : List Bool)
    (st : State 120 40) (hc : Context s qs bs st) :
    (branch.run st).1.lists 24 = queries m s ∧
      (branch.run st).1.regs 13 = (verdict m s qs bs).toNat := by
  have h := DifferenceBranch.program_difference (m := m) (c := 4)
    (fieldEquiv t) s.1.1 s.1.2 s.2 qs bs
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    hc.width hc.empty hc.label hc.history hc.answers hc.left hc.right hc.vertices hc.pairs
    hc.affineLabels hc.cubicLabels
  rw [← call_result (by decide) (by decide) DifferenceBranch.program] at h
  rw [show call (by decide) (by decide) DifferenceBranch.program = branch by
    unfold branch; rfl] at h
  exact h

theorem program_run (s : Sample t n) (qs : List ℕ) (bs : List Bool)
    (st : State 120 40) (hp : Public (t := t) n m qs bs st)
    (hs : st.regs 108 = ((seedCodec t n).equiv s).val) :
    (program.run st).1.lists 24 = queries m s ∧
      (program.run st).1.regs 13 = (verdict m s qs bs).toNat ∧
      Frame st (program.run st).1 := by
  obtain ⟨hc, _, hf⟩ := load_run s qs bs st hp hs
  obtain ⟨hq, hv⟩ := branch_run (m := m) s qs bs _ hc
  refine ⟨hq, hv, hf.trans ?_⟩
  change Frame (load.run st).1 (branch.run (load.run st).1).1
  unfold branch
  exact call_frame (by decide) (by decide) DifferenceBranch.program _

end PCP.Lang.NumericDifference
