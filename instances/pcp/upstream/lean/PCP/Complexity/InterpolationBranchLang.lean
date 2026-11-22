import PCP.Complexity.InterpolationBranchQueries

/-!
# The complete interpolation branch on stored answer histories

This program constructs all physical addresses, omits the zero-weight reads,
and computes exactly the original named test's verdict on arbitrary histories.
-/

namespace PCP.Lang.InterpolationBranch

open PCP.Algebraic BinaryFieldCode

variable {t n m : ℕ} [NeZero t]

def verdictLists : Fin 6 → Fin 40 := ![36, 37, 22, 23, 20, 24]

theorem verdictLists_injective : Function.Injective verdictLists := by decide

def verdict : Stmt 100 40 :=
  HistoryParity.program.rename (Fin.castLE (by decide : 12 ≤ 100)) verdictLists

def program : Stmt 100 40 := .seq queries verdict

attribute [local irreducible] queries

def oracle (site : StandardCorrection.Site (Field t) n) (qs : List ℕ) (bs : List Bool)
    (x : Point t m) (label : BinaryPolynomialSpace.Coefficients t 1) : ZMod 2 :=
  BinarySeedPadding.boolEquiv (QueryTree.answersOracle qs bs (address site x label))

def check (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (qs : List ℕ) (bs : List Bool) : Bool :=
  decide (ComputableBinaryLagrangeConstraint.check (le_refl 1)
    (BinaryMaterializedField.coordinates t) a (oracle site qs bs) u v z w = 0)

theorem verdict_result (st : State 100 40) :
    ((verdict.run st).1.restrict (Fin.castLE (by decide : 12 ≤ 100)) verdictLists,
      (verdict.run st).2) =
      HistoryParity.program.run (st.restrict (Fin.castLE (by decide : 12 ≤ 100)) verdictLists) :=
  HistoryParity.program.run_rename _ _ (Fin.castLE_injective _) verdictLists_injective st

theorem verdict_run (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (qs : List ℕ) (bs : List Bool) (st : State 100 40)
    (hq : st.lists 36 = qs) (hb : st.lists 37 = bs.map Bool.toNat)
    (hx : st.lists 20 = queryCodes a z u v w site) :
    (verdict.run st).1.regs 11 = (check a z u v w site qs bs).toNat ∧
    (verdict.run st).1.lists 20 = st.lists 20 := by
  have hr := verdict_result st
  have hp := HistoryParity.program_interpolation (le_refl 1)
    (BinaryMaterializedField.coordinates t) a u v z w (fun p => address site p.1 p.2)
    qs bs (st.restrict (Fin.castLE (by decide : 12 ≤ 100)) verdictLists) hq hb hx
  rw [← hr] at hp
  have hf := (HistoryParity.parity_run
    (st.restrict (Fin.castLE (by decide : 12 ≤ 100)) verdictLists)).2.2.2
  have hf' : (HistoryParity.program.run
      (st.restrict (Fin.castLE (by decide : 12 ≤ 100)) verdictLists)).1.lists 4 =
      (st.restrict (Fin.castLE (by decide : 12 ≤ 100)) verdictLists).lists 4 := hf
  rw [← hr] at hf'
  exact ⟨hp, hf'⟩

/-- Complete exact query generation and verdict, without a branch-correctness callback premise. -/
theorem program_run (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (qs : List ℕ) (bs : List Bool) (st : State 100 40)
    (hc : Context a z u v w site st)
    (hq : st.lists 36 = qs) (hb : st.lists 37 = bs.map Bool.toNat) :
    (program.run st).1.lists 20 = queryCodes a z u v w site ∧
    (program.run st).1.regs 11 = (check a z u v w site qs bs).toNat := by
  have h := queries_run a z u v w site st hc
  generalize hu : (queries.run st).1 = out at *
  have hv := verdict_run a z u v w site qs bs out
    ((h.2.lists 36 (by decide)).trans hq) ((h.2.lists 37 (by decide)).trans hb) h.1
  simp only [program, run_seq_fst, hu]
  exact ⟨hv.2.trans h.1, hv.1⟩

end PCP.Lang.InterpolationBranch
