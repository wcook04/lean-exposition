import PCP.Complexity.LangRunOnFirst

/-!+# Charged cost of the input-reduction wrapper
-/

namespace PCP.Lang.RunOnFirst

variable (P : Prog)

theorem finish_cost (st : State (5 + P.R) (2 + P.Q)) :
    ((finish P).run st).2 = listSize (st.lists (q P 0)) +
      2 * listSize (st.lists (pq P P.outL)) + 15 := by
  have hright : pq P P.outL ≠ q P 1 := by
    intro he
    have hv := congrArg Fin.val he
    change 2 + P.outL.val = 1 at hv
    omega
  simp only [finish, Stmt.run, Expr.eval, Expr.cost, Expr.readSize, setList_lists, setReg_lists,
    setReg_regs, Function.update_self, Function.update_of_ne hright, listSize_reverse]
  change listSize (st.lists (q P 0)) + 1 +
    (5 + (3 + (listSize (st.lists (pq P P.outL)) + 1 +
      (listSize (st.lists (pq P P.outL)) + 1) + 1) + 1) + 1) + 1 = _
  omega

theorem program_cost_eq (xs ys : List ℕ) (hx : ∀ v ∈ xs, v ≠ 2) :
    (program P).cost (xs ++ 2 :: ys) =
      ((split P).run (initial P (xs ++ 2 :: ys))).2 + P.cost xs +
        listSize xs + listSize ys + 2 * listSize (P.run xs) + 19 := by
  have hc := congrArg Prod.snd (call_result P xs ys)
  have ho := congrArg (fun z => z.1.lists P.outL) (call_result P xs ys)
  change ((call P).run (callState P xs ys)).2 = P.cost xs at hc
  change ((call P).run (callState P xs ys)).1.lists (pq P P.outL) = P.run xs at ho
  have hs := split_result P xs ys hx
  unfold Prog.cost
  rw [init_program]
  simp only [program, run_seq_snd, run_copy_snd, run_copy_fst]
  change ((split P).run (initial P (xs ++ 2 :: ys))).2 +
    (listSize ((splitState P (xs ++ 2 :: ys)).lists (q P 1)) + 1 +
      (((call P).run (setList (splitState P (xs ++ 2 :: ys)) (pq P P.inL)
        ((splitState P (xs ++ 2 :: ys)).lists (q P 1)))).2 +
        ((finish P).run ((call P).run
          (setList (splitState P (xs ++ 2 :: ys)) (pq P P.inL)
            ((splitState P (xs ++ 2 :: ys)).lists (q P 1)))).1).2 + 1) + 1) + 1 = _
  rw [hs.2]
  change _ + (listSize xs + 1 + (((call P).run (callState P xs ys)).2 +
    ((finish P).run ((call P).run (callState P xs ys)).1).2 + 1) + 1) + 1 = _
  rw [finish_cost, hc, ho, call_suffix P xs ys hx]
  dsimp only [Prog.cost]
  omega

/-- The overhead is quadratic in the original input, plus three times the called cost. -/
theorem program_cost (xs ys : List ℕ) (hx : ∀ v ∈ xs, v ≠ 2)
    (hb : ∀ v ∈ xs ++ 2 :: ys, v ≤ 2) :
    (program P).cost (xs ++ 2 :: ys) ≤
      130 * (listSize (xs ++ 2 :: ys) + 1) ^ 2 + 3 * P.cost xs := by
  let B := listSize (xs ++ 2 :: ys)
  have hs := SplitFirst.program.run_rename_cost (r P) (q P)
    (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _)
    (initial P (xs ++ 2 :: ys))
  have hb' : ∀ v ∈ ((initial P (xs ++ 2 :: ys)).restrict (r P) (q P)).lists 0,
      v ≤ 2 := hb
  have hp := SplitFirst.program_cost
    ((initial P (xs ++ 2 :: ys)).restrict (r P) (q P)) hb' rfl
  change (SplitFirst.program.run
    ((initial P (xs ++ 2 :: ys)).restrict (r P) (q P))).2 ≤ 100 * (B + 1) ^ 2 at hp
  rw [← hs] at hp
  have ho := P.run_listSize_le xs
  have hB : listSize xs + listSize ys ≤ B := by
    dsimp only [B]
    rw [listSize_append]
    simp only [listSize, List.map_cons, List.sum_cons]
    omega
  rw [program_cost_eq P xs ys hx]
  change _ ≤ 130 * (B + 1) ^ 2 + 3 * P.cost xs
  change ((split P).run (initial P (xs ++ 2 :: ys))).2 ≤ _ at hp
  nlinarith

end PCP.Lang.RunOnFirst
