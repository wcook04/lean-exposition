import PCP.Complexity.ThreeColorSeedRadicesCost
import PCP.Complexity.LangSeedDecode

/-!
# Actual structural seven-way seed decoding

The caller supplies the dimensions and one numeric seed. All seven radices are
constructed by the program before the exact mixed-radix division pass.
-/

set_option maxRecDepth 4096

namespace PCP.Lang.RawSeed

open PCP.Algebraic ThreeColorSeedIndex SeedArithmetic

def liftRadices (p : Stmt 15 2) : Stmt 16 4 := p.rename (Fin.castAdd 1) (Fin.castAdd 2)

def radices : Stmt 16 4 := liftRadices SeedRadices.program

def decoder : Stmt 16 4 := MixedRadixDecode.program.rename
  (Fin.castLE (by decide)) (Fin.castLE (by decide))

def program : Stmt 16 4 := .seq (.copy 3 0) (.seq radices
  (.seq (.assign 0 (.var 15)) (.seq (.copy 3 1) decoder)))

def Context (n m c t code : ℕ) (st : State 16 4) : Prop :=
  (∀ i : Fin 4, st.regs (i.castAdd 12) = ![n, m, c, t] i) ∧
  st.regs 15 = code ∧ st.lists 3 = []

private theorem liftRadices_result (p : Stmt 15 2) (st : State 16 4) :
    (((liftRadices p).run st).1.restrict (Fin.castAdd 1) (Fin.castAdd 2),
      ((liftRadices p).run st).2) = p.run (st.restrict (Fin.castAdd 1) (Fin.castAdd 2)) := by
  exact p.run_rename (Fin.castAdd 1) (Fin.castAdd 2)
    (Fin.castAdd_injective 15 1) (Fin.castAdd_injective 2 2) st

theorem radices_result (st : State 16 4) :
    ((radices.run st).1.restrict (Fin.castAdd 1) (Fin.castAdd 2), (radices.run st).2) =
      SeedRadices.program.run (st.restrict (Fin.castAdd 1) (Fin.castAdd 2)) :=
  liftRadices_result SeedRadices.program st

theorem decoder_result (st : State 16 4) :
    ((decoder.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)),
      (decoder.run st).2) = MixedRadixDecode.program.run
        (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  unfold decoder
  exact MixedRadixDecode.program.run_rename _ _ (Fin.castLE_injective _)
    (Fin.castLE_injective _) st

theorem radices_run (n m c t : ℕ) (st : State 16 4)
    (hc : ∀ i : Fin 4, st.regs (i.castAdd 12) = ![n, m, c, t] i)
    (he : st.lists 0 = []) :
    (radices.run st).1.lists 0 = List.ofFn (fun i => 2 ^ branchBits n m c t i) := by
  have h := (SeedRadices.program_run n m c t
    (st.restrict (Fin.castAdd 1) (Fin.castAdd 2)) hc he).1
  rw [← radices_result st] at h
  simpa only [State.restrict_lists,
    show (0 : Fin 2).castAdd 2 = (0 : Fin 4) from rfl] using h

theorem radices_reg (st : State 16 4) : (radices.run st).1.regs 15 = st.regs 15 := by
  unfold radices liftRadices
  apply Stmt.run_rename_reg_outside
  intro i hi
  have := congrArg Fin.val hi
  simp only [Fin.val_castAdd] at this
  norm_num at this
  omega

theorem radices_empty (st : State 16 4) : (radices.run st).1.lists 3 = st.lists 3 := by
  unfold radices liftRadices
  apply Stmt.run_rename_list_outside
  intro i hi
  have := congrArg Fin.val hi
  simp only [Fin.val_castAdd] at this
  norm_num at this
  omega

/-- The output is the exact ordered sequence of seven branch codes. -/
theorem program_run (n m c t code : ℕ) (st : State 16 4)
    (hc : Context n m c t code st) :
    (program.run st).1.lists 1 =
      (MixedRadixDecode.split code (List.ofFn (fun i => 2 ^ branchBits n m c t i))).1 := by
  let s := setList st 0 []
  have hr := radices_run n m c t s hc.1 (by simp [s])
  have h15 := (radices_reg s).trans hc.2.1
  have h3 : (radices.run s).1.lists 3 = [] :=
    (radices_empty s).trans (by simpa [s, Function.update] using hc.2.2)
  generalize hu : (radices.run s).1 = u at *
  let v := setList (setReg u 0 code) 1 []
  have hd := MixedRadixDecode.program_run
    (v.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
  rw [← decoder_result v] at hd
  have hv0 : v.regs 0 = code := by simp [v]
  have hvL0 : v.lists 0 = List.ofFn (fun i => 2 ^ branchBits n m c t i) := by
    simpa [v, Function.update] using hr
  have hvL1 : v.lists 1 = [] := by simp [v]
  have hout := hd.2.2
  change (decoder.run v).1.lists 1 = (v.lists 1).reverse ++
    (MixedRadixDecode.split (v.regs 0) (v.lists 0)).1 at hout
  rw [hv0, hvL0, hvL1, List.reverse_nil, List.nil_append] at hout
  simp only [program, run_seq_fst, run_copy_fst, hc.2.2]
  dsimp only [s] at hu
  rw [hu, run_assign_fst, Expr.eval, h15, setReg_lists, h3]
  exact hout

end PCP.Lang.RawSeed
