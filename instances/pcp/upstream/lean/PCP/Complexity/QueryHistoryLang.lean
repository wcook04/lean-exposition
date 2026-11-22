import PCP.Complexity.LangCost
import PCP.Verifier.QueryListAlgorithm

/-!
# Reading a finite query history with the verifier's exact precedence

The program scans stored query addresses and answers together. The first matching
address wins, including for inconsistent hypothetical histories. Missing answers
and absent addresses return zero. The source lists and requested address are
preserved; only work copies are consumed.
-/

namespace PCP.Lang.QueryHistory

/-- Numeric version of the verifier's collected-answer oracle. -/
def read : List ℕ → List ℕ → ℕ → ℕ
  | q :: qs, b :: bs, a => if q = a then b else read qs bs a
  | _, _, _ => 0

/-- The correspondence includes repeated addresses and short answer lists. -/
theorem read_bool (qs : List ℕ) (bs : List Bool) (a : ℕ) :
    read qs (bs.map Bool.toNat) a = (QueryTree.answersOracle qs bs a).toNat := by
  induction qs generalizing bs with
  | nil => rfl
  | cons q qs ih =>
      cases bs with
      | nil => rfl
      | cons b bs =>
          simp only [read, List.map_cons, QueryTree.answersOracle, Function.update_apply]
          by_cases h : q = a
          · subst q; simp
          · simp [h, Ne.symm h, ih]

def body : Stmt 8 4 :=
  .seq (.pop 2 4 6) (.seq (.pop 3 5 6)
    (.ite 3 .skip (.ite 6
      (.seq (.assign 7 (.eq 0 4))
        (.ite 7 (.seq (.assign 2 (.var 5)) (.assign 3 (.const 1))) .skip)) .skip)))

def setup : Stmt 8 4 :=
  .seq (.copy 0 2) (.seq (.copy 1 3) (.seq (.len 0 1)
    (.seq (.assign 2 (.const 0)) (.assign 3 (.const 0)))))

def program : Stmt 8 4 := .seq setup (.loop 1 body)

/-- A single scan position: only the earliest successful comparison writes the answer. -/
theorem body_step (st : State 8 4) (q : ℕ) (qs bs : List ℕ)
    (hq : st.lists 2 = q :: qs) (hb : st.lists 3 = bs) :
    (body.run st).1.regs 0 = st.regs 0 ∧
    (body.run st).1.regs 2 =
      (if st.regs 3 = 0 ∧ bs ≠ [] ∧ q = st.regs 0 then bs.headD 0 else st.regs 2) ∧
    (body.run st).1.regs 3 =
      (if st.regs 3 = 0 ∧ bs ≠ [] ∧ q = st.regs 0 then 1 else st.regs 3) ∧
    (body.run st).1.lists 2 = qs ∧ (body.run st).1.lists 3 = bs.tail ∧
    (body.run st).1.lists 0 = st.lists 0 ∧ (body.run st).1.lists 1 = st.lists 1 := by
  cases bs with
  | nil =>
      by_cases hf : st.regs 3 = 0 <;>
        simp [body, Stmt.run, Function.update, hq, hb, hf]
  | cons b bs =>
      by_cases hf : st.regs 3 = 0 <;> by_cases he : q = st.regs 0 <;>
        simp [body, Stmt.run, Expr.eval, Function.update, hq, hb, hf, he, Ne.symm,
          eq_comm]

/-- Complete paired scan with an optional already-found accumulator. -/
theorem iterate_result (c : ℕ) (qs bs : List ℕ) (st : State 8 4)
    (hq : st.lists 2 = qs) (hb : st.lists 3 = bs)
    (hzero : st.regs 3 = 0 → st.regs 2 = 0) :
    (iterate body.run c qs.length st).1.regs 2 =
      (if st.regs 3 = 0 then read qs bs (st.regs 0) else st.regs 2) ∧
    (iterate body.run c qs.length st).1.lists 2 = [] ∧
    (iterate body.run c qs.length st).1.lists 3 = bs.drop qs.length ∧
    (iterate body.run c qs.length st).1.lists 0 = st.lists 0 ∧
    (iterate body.run c qs.length st).1.lists 1 = st.lists 1 ∧
    (iterate body.run c qs.length st).1.regs 0 = st.regs 0 := by
  induction qs generalizing bs st with
  | nil =>
      change st.regs 2 = (if st.regs 3 = 0 then 0 else st.regs 2) ∧
        st.lists 2 = [] ∧ st.lists 3 = bs ∧ st.lists 0 = st.lists 0 ∧
        st.lists 1 = st.lists 1 ∧ st.regs 0 = st.regs 0
      refine ⟨?_, hq, hb, rfl, rfl, rfl⟩
      by_cases hf : st.regs 3 = 0
      · simp [hf, hzero hf]
      · simp [hf]
  | cons q qs ih =>
      obtain ⟨h0, h2, h3, hq', hb', hs0, hs1⟩ := body_step st q qs bs hq hb
      have hz : (body.run st).1.regs 3 = 0 → (body.run st).1.regs 2 = 0 := by
        rw [h2, h3]
        split <;> simp_all
      obtain ⟨hr, hq'', hb'', hs0', hs1', h0'⟩ := ih bs.tail (body.run st).1 hq' hb' hz
      rw [List.length_cons, iterate_succ_fst]
      refine ⟨?_, hq'', ?_, hs0'.trans hs0, hs1'.trans hs1, h0'.trans h0⟩
      · rw [hr, h0, h2, h3]
        cases bs with
        | nil => simp [read]
        | cons b bs =>
            by_cases hf : st.regs 3 = 0 <;> by_cases he : q = st.regs 0 <;>
              simp [read, hf, he]
      · cases bs with
        | nil => simpa using hb''
        | cons b bs => simpa using hb''

/-- The source lists are retained and the stored result is the exact numeric history read. -/
theorem program_run (st : State 8 4) :
    (program.run st).1.regs 2 = read (st.lists 0) (st.lists 1) (st.regs 0) ∧
    (program.run st).1.lists 0 = st.lists 0 ∧
    (program.run st).1.lists 1 = st.lists 1 ∧
    (program.run st).1.regs 0 = st.regs 0 := by
  let s := (setup.run st).1
  have hn : s.regs 1 = (st.lists 0).length := by
    simp [s, setup, Stmt.run, Expr.eval, Function.update]
  have h := iterate_result (Nat.size (st.lists 0).length + 1)
    (st.lists 0) (st.lists 1) s (by rfl) (by rfl) (by intro _; rfl)
  change (iterate body.run (Nat.size (s.regs 1) + 1) (s.regs 1) s).1.regs 2 = _ ∧
    (iterate body.run (Nat.size (s.regs 1) + 1) (s.regs 1) s).1.lists 0 = _ ∧
    (iterate body.run (Nat.size (s.regs 1) + 1) (s.regs 1) s).1.lists 1 = _ ∧
    (iterate body.run (Nat.size (s.regs 1) + 1) (s.regs 1) s).1.regs 0 = _
  rw [hn]
  exact ⟨h.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- Exact precedence of the named verifier's oracle, on arbitrary Boolean histories. -/
theorem program_answersOracle (st : State 8 4) (bs : List Bool)
    (hb : st.lists 1 = bs.map Bool.toNat) :
    (program.run st).1.regs 2 = (QueryTree.answersOracle (st.lists 0) bs (st.regs 0)).toNat := by
  rw [(program_run st).1, hb, read_bool]

private theorem listSize_drop_le (xs : List ℕ) (j : ℕ) : listSize (xs.drop j) ≤ listSize xs := by
  have h := listSize_append (xs.take j) (xs.drop j)
  rw [List.take_append_drop] at h
  omega

private theorem size_headD_le (xs : List ℕ) : Nat.size (xs.headD 0) ≤ listSize xs := by
  cases xs with
  | nil => simp
  | cons x xs => exact size_le_listSize (by simp)

/-- Values read by a scan remain bounded by the original stored input size. -/
def Inv (qs bs : List ℕ) (a W j : ℕ) (st : State 8 4) : Prop :=
  st.regs 0 = a ∧ Nat.size (st.regs 2) ≤ W ∧ Nat.size (st.regs 3) ≤ W ∧
    st.lists 2 = qs.drop j ∧ st.lists 3 = bs.drop j

theorem body_inv (qs bs : List ℕ) (a W j : ℕ) (st : State 8 4)
    (hW : 1 ≤ W) (hbs : listSize bs ≤ W) (hj : j < qs.length) (hs : Inv qs bs a W j st) :
    Inv qs bs a W (j + 1) (body.run st).1 := by
  have hq : st.lists 2 = qs[j] :: qs.drop (j + 1) :=
    hs.2.2.2.1.trans (List.drop_eq_getElem_cons hj)
  obtain ⟨h0, h2, h3, hq', hb', _, _⟩ := body_step st qs[j] _ (bs.drop j) hq hs.2.2.2.2
  refine ⟨h0.trans hs.1, ?_, ?_, hq', ?_⟩
  · rw [h2]
    split
    · exact (size_headD_le _).trans ((listSize_drop_le bs j).trans hbs)
    · exact hs.2.1
  · rw [h3]
    split
    · simpa using hW
    · exact hs.2.2.1
  · simpa only [List.tail_drop] using hb'

def passConstant : ℕ := body.C * (body.width + body.csize + 1)

theorem body_cost (qs bs : List ℕ) (a W j : ℕ) (st : State 8 4)
    (ha : Nat.size a ≤ W) (hqs : listSize qs ≤ W) (hbs : listSize bs ≤ W)
    (hs : Inv qs bs a W j st) : (body.run st).2 ≤ passConstant * (W + 1) := by
  apply loopFree_cost_le body (by decide) st W
  · intro r hr
    have h0 : Nat.size (st.regs 0) ≤ W := hs.1 ▸ ha
    have h2 := hs.2.1
    have h3 := hs.2.2.1
    fin_cases r <;> simp [body, Stmt.uses, Stmt.mustW, Expr.uses] at hr <;> dsimp <;> omega
  · intro L hL
    have h2 : listSize (st.lists 2) ≤ W := by
      rw [hs.2.2.2.1]; exact (listSize_drop_le qs j).trans hqs
    have h3 : listSize (st.lists 3) ≤ W := by
      rw [hs.2.2.2.2]; exact (listSize_drop_le bs j).trans hbs
    fin_cases L <;> simp [body, Stmt.lUses] at hL <;> dsimp <;> omega

/-- Quadratic charged cost in the two source lists and the requested address bit length. -/
theorem program_cost (st : State 8 4) :
    (program.run st).2 ≤ (passConstant + 20) *
      (listSize (st.lists 0) + listSize (st.lists 1) + Nat.size (st.regs 0) + 2) ^ 2 := by
  let qs := st.lists 0
  let bs := st.lists 1
  let a := st.regs 0
  let W := listSize qs + listSize bs + Nat.size a + 1
  let s := (setup.run st).1
  have hW : 1 ≤ W := by dsimp [W]; omega
  have hqs : listSize qs ≤ W := by dsimp [W]; omega
  have hbs : listSize bs ≤ W := by dsimp [W]; omega
  have ha : Nat.size a ≤ W := by dsimp [W]; omega
  have hs : Inv qs bs a W 0 s := by
    simp [Inv, qs, bs, a, s, setup, Stmt.run, Expr.eval, Function.update]
  have hn : s.regs 1 = qs.length := by simp [s, qs, setup, Stmt.run, Expr.eval, Function.update]
  have hl : qs.length ≤ W := (length_le_listSize qs).trans hqs
  have hsN : Nat.size qs.length ≤ W := (size_le_self _).trans hl
  have hi := iterate_cost_idx body.run (Nat.size qs.length + 1)
    (passConstant * (W + 1)) qs.length (Inv qs bs a W)
    (fun j s hj hs => ⟨body_inv qs bs a W j s hW hbs hj hs,
      body_cost qs bs a W j s ha hqs hbs hs⟩) s hs
  have hsetup : (setup.run st).2 ≤ 4 * W + 10 := by
    simp [setup, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, Function.update]
    dsimp [qs, bs] at hqs hbs hsN
    omega
  have hsum : (program.run st).2 ≤ 4 * W + 10 +
      qs.length * (Nat.size qs.length + 1 + passConstant * (W + 1)) + Nat.size qs.length + 2 := by
    change (setup.run st).2 + ((iterate body.run (Nat.size (s.regs 1) + 1)
      (s.regs 1) s).2 + Nat.size (s.regs 1) + 1) + 1 ≤ _
    rw [hn]
    omega
  have hp := Nat.mul_le_mul hl
    (show Nat.size qs.length + 1 + passConstant * (W + 1) ≤ W + 1 + passConstant * (W + 1) by omega)
  apply hsum.trans
  change _ ≤ (passConstant + 20) * (W + 1) ^ 2
  nlinarith [Nat.zero_le (passConstant * W ^ 2)]

end PCP.Lang.QueryHistory
