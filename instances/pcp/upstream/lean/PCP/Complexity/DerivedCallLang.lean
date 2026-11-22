import PCP.Complexity.DerivedCallPrimary
import PCP.Complexity.DerivedCallCorrection

/-!
# Complete primary read and two certificate-correction calls

The fixed program executes all three physical query segments against the same
history, then computes the exact optional-bit acceptance condition. Neither
corrector nor coefficient translation is an abstract callback.
-/

namespace PCP.Lang.DerivedCall

open PCP.Algebraic BinaryFieldCode LocalCorrection BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t] [NeZero m]

-- The fixed verdict renaming targets 300 registers.
set_option maxRecDepth 1024

def verdictRegs : Fin 7 → Fin 300 := ![270,271,272,273,274,275,276]

def finish : Stmt 300 112 :=
  .seq (DerivedGrid.verdict.rename verdictRegs Fin.elim0) (.rev 110)

def program (weighted : Bool) (k : Certificate) : Stmt 300 112 :=
  .seq (primary weighted) (.seq (correction k true) (.seq (correction k false) finish))

theorem finish_run (p : ZMod 2) (a b : Option (ZMod 2)) (st : State 300 112)
    (h0 : st.regs 270 = p.val) (h1 : st.regs 271 = present a)
    (h2 : st.regs 272 = answer a) (h3 : st.regs 273 = present b)
    (h4 : st.regs 274 = answer b) :
    (finish.run st).1.regs 275 = (DerivedGrid.accepts p a b).toNat ∧
    (finish.run st).1.lists 110 = (st.lists 110).reverse := by
  have hv := DerivedGrid.verdict_run p a b (st.restrict verdictRegs Fin.elim0) h0 h1 h2 h3 h4
  rw [← DerivedGrid.verdict.run_rename verdictRegs Fin.elim0 (by decide)
    (fun i => Fin.elim0 i) st] at hv
  have hl := Stmt.run_rename_list_outside DerivedGrid.verdict verdictRegs Fin.elim0
    (110 : Fin 112) (fun i => Fin.elim0 i) st
  exact ⟨hv, by simp only [finish, run_seq_fst, run_rev_fst,
    setList_lists, Function.update_self, hl]⟩

theorem finish_frame (st : State 300 112) : Frame st (finish.run st).1 :=
  frame_of_writes finish (by decide) (by decide) st

attribute [local irreducible] primary correction finish

private theorem compose (P A B T : Stmt 300 112) (Inv : State 300 112 → Prop)
    (p : ZMod 2) (x y : Option (ZMod 2)) (ps xs ys : List ℕ)
    (hP : ∀ st, Inv st → (P.run st).1.regs 270 = p.val ∧
      (P.run st).1.lists 110 = ps.reverse ∧ Inv (P.run st).1)
    (hA : ∀ st, Inv st → (A.run st).1.regs 271 = present x ∧
      (A.run st).1.regs 272 = answer x ∧
      (A.run st).1.lists 110 = xs.reverse ++ st.lists 110 ∧ Inv (A.run st).1)
    (hB : ∀ st, Inv st → (B.run st).1.regs 273 = present y ∧
      (B.run st).1.regs 274 = answer y ∧
      (B.run st).1.lists 110 = ys.reverse ++ st.lists 110)
    (hAP : ∀ st, (A.run st).1.regs 270 = st.regs 270)
    (hBP : ∀ st, (B.run st).1.regs 270 = st.regs 270)
    (hBA : ∀ st, (B.run st).1.regs 271 = st.regs 271 ∧
      (B.run st).1.regs 272 = st.regs 272)
    (hT : ∀ st, st.regs 270 = p.val → st.regs 271 = present x →
      st.regs 272 = answer x → st.regs 273 = present y → st.regs 274 = answer y →
      (T.run st).1.regs 275 = (DerivedGrid.accepts p x y).toNat ∧
      (T.run st).1.lists 110 = (st.lists 110).reverse)
    (st : State 300 112) (hc : Inv st) :
    ((Stmt.seq P (.seq A (.seq B T))).run st).1.regs 275 =
      (DerivedGrid.accepts p x y).toNat ∧
    ((Stmt.seq P (.seq A (.seq B T))).run st).1.lists 110 = ps ++ xs ++ ys := by
  have hp := hP st hc
  generalize hu : (P.run st).1 = u at *
  have ha := hA u hp.2.2
  have hap := (hAP u).trans hp.1
  generalize hv : (A.run u).1 = v at *
  have hb := hB v ha.2.2.2
  have hbp := (hBP v).trans hap
  have hba := hBA v
  generalize hw : (B.run v).1 = w at *
  have ht := hT w hbp (hba.1.trans ha.1) (hba.2.trans ha.2.1) hb.1 hb.2.1
  simp only [run_seq_fst, hu, hv, hw]
  refine ⟨ht.1, ?_⟩
  rw [ht.2, hb.2.2, ha.2.2.1, hp.2.1]
  simp only [List.reverse_append, List.reverse_reverse, List.append_assoc]

theorem program_frame (weighted : Bool) (k : Certificate) (st : State 300 112) :
    Frame st ((program weighted k).run st).1 :=
  (primary_frame weighted st).trans ((correction_frame k true _).trans
    ((correction_frame k false _).trans (finish_frame _)))

/-- Every component is an actual language program, with the original optional-answer rule. -/
theorem program_run (weighted : Bool) (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a b : k.Point t n) (w : Fin t → ZMod 2)
    (mask : Coefficients t 3) (weight : OuterBranch.Field t)
    (loc : HadamardRow.Location (OuterBranch.Field t) n m 4 3)
    (first second : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (st : State 300 112)
    (hc : Context k nodes ζ a b w mask weight loc first second qs bs st) :
    let p := primaryBit weighted weight w mask loc qs bs
    let x := callValue k nodes ζ a w first qs bs
    let y := callValue k nodes ζ b w second qs bs
    ((program weighted k).run st).1.regs 275 = (DerivedGrid.accepts p x y).toNat ∧
    ((program weighted k).run st).1.lists 110 =
      primaryQueries weighted weight w mask loc ++ callQueries k nodes ζ a w first ++
        callQueries k nodes ζ b w second ∧
    Frame st ((program weighted k).run st).1 := by
  have h := compose (primary weighted) (correction k true) (correction k false) finish
    (Context k nodes ζ a b w mask weight loc first second qs bs)
    (primaryBit weighted weight w mask loc qs bs)
    (callValue k nodes ζ a w first qs bs) (callValue k nodes ζ b w second qs bs)
    (primaryQueries weighted weight w mask loc)
    (callQueries k nodes ζ a w first) (callQueries k nodes ζ b w second)
    (fun u hu => by
      have h := primary_run weighted k nodes ζ a b w mask weight loc first second qs bs u hu
      exact ⟨h.1, h.2.1, hu.of_frame h.2.2⟩)
    (fun u hu => by
      have h := correction_run true k nodes ζ a b w mask weight loc first second qs bs u hu
      exact ⟨h.1, h.2.1, h.2.2.1, hu.of_frame h.2.2.2⟩)
    (fun u hu => by
      have h := correction_run false k nodes ζ a b w mask weight loc first second qs bs u hu
      exact ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun u => correction_reg k true u 270 (by decide) (by decide) (by decide))
    (fun u => correction_reg k false u 270 (by decide) (by decide) (by decide))
    (fun u => ⟨correction_reg k false u 271 (by decide) (by decide) (by decide),
      correction_reg k false u 272 (by decide) (by decide) (by decide)⟩)
    (finish_run _ _ _) st hc
  exact ⟨h.1, h.2, program_frame weighted k st⟩

end PCP.Lang.DerivedCall
