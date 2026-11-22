import PCP.Complexity.LangDifferenceQueries
import PCP.Complexity.LangDifferenceVerdictCost

/-!
# Complete difference branch on the physical answer history

The program constructs the three actual production addresses, then evaluates the
named consistency residual against first-occurrence physical history answers.
-/

namespace PCP.Lang.DifferenceBranch

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientIndex ThreeColorVerifier

variable {t : ℕ}

def verdictLists : Fin 4 → Fin 32 := ![30, 31, 25, 26]

def verdict : Stmt 80 32 := DifferenceVerdict.program.rename
  (Fin.castLE (by decide)) verdictLists

def prepare : Stmt 80 32 := .seq (.copy 24 27)
  (.seq (.pop 27 8 67) (.seq (.pop 27 9 67) (.pop 27 10 67)))

def program : Stmt 80 32 := .seq DifferenceQueries.program (.seq prepare verdict)

theorem verdict_result (st : State 80 32) :
    ((verdict.run st).1.restrict (Fin.castLE (by decide)) verdictLists, (verdict.run st).2) =
      DifferenceVerdict.program.run (st.restrict (Fin.castLE (by decide)) verdictLists) := by
  unfold verdict
  exact DifferenceVerdict.program.run_rename (Fin.castLE (by decide)) verdictLists
    (Fin.castLE_injective _) (by decide) st

theorem verdict_run (qs : List ℕ) (bs : List Bool) (x y z : ℕ) (st : State 80 32)
    (hq : st.lists 30 = qs) (hb : st.lists 31 = bs.map Bool.toNat)
    (hx : st.regs 8 = x) (hy : st.regs 9 = y) (hz : st.regs 10 = z) :
    (verdict.run st).1.regs 13 = (DifferenceVerdict.check qs bs x y z).toNat := by
  have hc : DifferenceVerdict.Context qs (bs.map Bool.toNat) x y z
      (st.restrict (Fin.castLE (by decide)) verdictLists) := ⟨hq, hb, hx, hy, hz⟩
  have h := DifferenceVerdict.program_check qs bs x y z _ hc
  rw [← verdict_result st] at h
  simpa only [State.restrict_regs,
    show Fin.castLE (by decide : 14 ≤ 80) (13 : Fin 14) = (13 : Fin 80) from rfl] using h

theorem prepare_run (st : State 80 32) (x y z : ℕ) (hq : st.lists 24 = [x, y, z]) :
    (prepare.run st).1.regs 8 = x ∧ (prepare.run st).1.regs 9 = y ∧
    (prepare.run st).1.regs 10 = z := by
  simp [prepare, Stmt.run, hq, Function.update]

theorem query_program_frame (L : Fin 32) (hL : 25 ≤ L.val) (st : State 80 32) :
    (DifferenceQueries.program.run st).1.lists L = st.lists L := by
  have h24 : L ≠ 24 := by intro h; subst L; norm_num at hL
  have h0 : L ≠ 0 := by intro h; subst L; norm_num at hL
  have hdecode (s : State 80 32) : (HadamardLabel.decode.run s).1.lists L = s.lists L := by
    unfold HadamardLabel.decode
    apply Stmt.run_rename_list_outside
    intro i hi
    exact h0 hi.symm
  have hpack (s : State 80 32) : (DifferenceQueries.pack.run s).1.lists L = s.lists L := by
    simp only [DifferenceQueries.pack, run_seq_fst, run_copy_fst, run_assign_fst,
      setReg_lists, hdecode, setList_lists, Function.update_of_ne h0]
  have hemit (s : State 80 32) : (DifferenceQueries.emit.run s).1.lists L = s.lists L := by
    exact run_lists_frame _ L (by
      simp [DifferenceQueries.emit, DifferenceQueries.addresses, Stmt.listWrites, h24]) s
  simp only [DifferenceQueries.program, run_seq_fst, run_copy_fst, run_assign_fst,
    run_rev_fst, setList_lists, Function.update_of_ne h24, hemit, hpack,
    DifferenceQueries.homogeneous_list L (by omega), setReg_lists]

theorem program_run (w : Fin t → ZMod 2) (qs : List ℕ) (bs : List Bool)
    (st : State 80 32) (ht : st.regs 20 = t) (he : st.lists 7 = [])
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val))
    (hq : st.lists 30 = qs) (hb : st.lists 31 = bs.map Bool.toNat) :
    let z := HadamardLabel.code
      (BooleanCoefficientArithmetic.homogeneousIndex (by decide : 1 ≤ 3) w)
    let x := DifferenceQueries.differenceAddress (st.regs 59) (st.regs 60)
      (st.regs 61) (st.regs 62) (st.regs 57) (st.regs 58) z
    let y := z + st.regs 62 * st.regs 57
    let v := z + st.regs 62 * st.regs 58
    (program.run st).1.lists 24 = [x, y, v] ∧
      (program.run st).1.regs 13 = (DifferenceVerdict.check qs bs x y v).toNat := by
  have hquery := DifferenceQueries.program_run w st ht he hw
  have hqs := (query_program_frame 30 (by decide) st).trans hq
  have hbs := (query_program_frame 31 (by decide) st).trans hb
  generalize hu : (DifferenceQueries.program.run st).1 = u at *
  have hp := prepare_run u _ _ _ hquery
  have hpq := run_lists_frame prepare 30 (by decide) u
  have hpb := run_lists_frame prepare 31 (by decide) u
  have hp24 := run_lists_frame prepare 24 (by decide) u
  generalize hv : (prepare.run u).1 = v at *
  have hc := verdict_run qs bs _ _ _ v (hpq.trans hqs) (hpb.trans hbs) hp.1 hp.2.1 hp.2.2
  have hf : (verdict.run v).1.lists 24 = v.lists 24 := by
    unfold verdict
    apply Stmt.run_rename_list_outside
    decide
  simp only [program, run_seq_fst, hu, hv]
  exact ⟨hf.trans (hp24.trans hquery), hc⟩

/-- The physical query list and residual are the named verifier branch on every answer history. -/
theorem program_difference {F : Type*} {q n m c : ℕ} (eF : F ≃ Fin q)
    (a b : Fin n → F) (w : Fin t → ZMod 2) (qs : List ℕ) (bs : List Bool)
    (st : State 80 32) (ht : st.regs 20 = t) (he : st.lists 7 = [])
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val))
    (hq : st.lists 30 = qs) (hb : st.lists 31 = bs.map Bool.toNat)
    (ha : st.regs 57 = (ThreeColorQueryIndex.vertexIndex eF n a).val)
    (ha' : st.regs 58 = (ThreeColorQueryIndex.vertexIndex eF n b).val)
    (hA : st.regs 59 = q ^ n) (hB : st.regs 60 = q ^ (n + n))
    (hC1 : st.regs 61 = 2 ^ dimension t 1) (hC3 : st.regs 62 = 2 ^ dimension t 3) :
    let index := fun z : BinaryDifferenceConsistency.Query F (Fin n) t 3 =>
      (ThreeColorQueryIndex.equiv (m := m) (c := c) eF
        (coefficientEquiv t 1) (coefficientEquiv t 3) (differenceCheckQuery z)).val
    (program.run st).1.lists 24 =
      (ComputableBinaryDifferenceConsistency.queries (by decide : 1 ≤ 3) a b w).map index ∧
    (program.run st).1.regs 13 = (decide (ComputableBinaryDifferenceConsistency.check
      (by decide : 1 ≤ 3)
      (fun x p => BinarySeedPadding.boolEquiv (QueryTree.answersOracle qs bs (index (.inl (x, p)))))
      (fun x p => BinarySeedPadding.boolEquiv (QueryTree.answersOracle qs bs (index (.inr (x, p)))))
      a b w = 0)).toNat := by
  have h := program_run w qs bs st ht he hw hq hb
  dsimp only at h ⊢
  rw [ha, ha', hA, hB, hC1, hC3] at h
  simpa only [ComputableBinaryDifferenceConsistency.queries,
    ComputableBinaryDifferenceConsistency.check, List.map_cons, List.map_nil,
    differenceCheckQuery, DifferenceQueries.color_address, DifferenceQueries.difference_address,
    DifferenceVerdict.check] using h

end PCP.Lang.DifferenceBranch
