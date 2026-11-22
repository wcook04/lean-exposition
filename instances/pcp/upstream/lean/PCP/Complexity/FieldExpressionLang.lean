import PCP.Complexity.BinaryFieldCodeSemantics
import PCP.Complexity.BinaryFieldCodeCost

/-!
# Compiling finite field expressions to stored code arithmetic

Source field values occupy a preserved register prefix. A separate list stack
holds intermediate codes; all arithmetic is performed by the concrete binary
field routines. The final scalar evaluator restores this stack exactly.
-/

namespace PCP.Lang.FieldExpression

open PCP.Algebraic BinaryField BinaryFieldCode

inductive Term (n : ℕ)
  | bit : Bool → Term n
  | input : Fin n → Term n
  | bin : Op → Term n → Term n → Term n
  | inv : Term n → Term n

variable {n t : ℕ}

def Term.eval [NeZero t] (env : Fin n → BinaryMaterializedField.Element t) :
    Term n → BinaryMaterializedField.Element t
  | .bit b => if b then 1 else 0
  | .input i => env i
  | .bin op a b => op.fieldEval (a.eval env) (b.eval env)
  | .inv a => (a.eval env)⁻¹

/-- Arithmetic scratch follows the preserved source-register prefix. -/
def slot (n : ℕ) : Fin 36 → Fin (n + 36) := Fin.natAdd n

theorem slot_injective : Function.Injective (slot n) := by
  intro i j h
  apply Fin.ext
  have he := congrArg Fin.val h
  simpa [slot] using he

private theorem source_ne (i : Fin n) (j : Fin 36) : i.castAdd 36 ≠ slot n j := by
  intro h
  have he := congrArg Fin.val h
  simp only [Fin.val_castAdd, slot, Fin.val_natAdd] at he
  have := i.isLt
  omega

/-- Add one stack list outside all arithmetic work lists. -/
def embed (p : Stmt 36 11) : Stmt (n + 36) 12 := p.rename (slot n) Fin.castSucc

def View (t : ℕ) [NeZero t] (env : Fin n → BinaryMaterializedField.Element t)
    (st : State (n + 36) 12) : Prop :=
  (∀ i, st.regs (i.castAdd 36) = (fieldEquiv t (env i)).val) ∧
  st.regs (slot n 20) = t ∧
  st.lists 3 = encode (BinaryWordMaterialization.modulus t) ∧ st.lists 7 = []

/-- Exact arithmetic subprogram effects at the extended register layout. -/
theorem embed_result (p : Stmt 36 11) (st : State (n + 36) 12) :
    (((embed p).run st).1.restrict (slot n) Fin.castSucc, ((embed p).run st).2) =
      p.run (st.restrict (slot n) Fin.castSucc) :=
  p.run_rename (slot n) Fin.castSucc slot_injective (Fin.castSucc_injective _) st

theorem embed_stack (p : Stmt 36 11) (st : State (n + 36) 12) :
    ((embed p).run st).1.lists 11 = st.lists 11 := by
  exact p.run_rename_list_outside (slot n) Fin.castSucc 11
    (by intro i hi; have := congrArg Fin.val hi; have := i.isLt; simp at *; omega) st

theorem embed_view [NeZero t] (p : Stmt 36 11)
    (hframe : ∀ s, (p.run s).1.regs 20 = s.regs 20 ∧
      (p.run s).1.lists 3 = s.lists 3 ∧ (p.run s).1.lists 7 = s.lists 7)
    (env : Fin n → BinaryMaterializedField.Element t) (st : State (n + 36) 12)
    (hv : View t env st) : View t env ((embed p).run st).1 := by
  have h := congrArg Prod.fst (embed_result p st)
  have hf := hframe (st.restrict (slot n) Fin.castSucc)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact (p.run_rename_reg_outside (slot n) Fin.castSucc (i.castAdd 36)
      (fun j => (source_ne i j).symm) st).trans (hv.1 i)
  · exact (congrArg (fun s : State 36 11 => s.regs 20) h).trans (hf.1.trans hv.2.1)
  · exact (congrArg (fun s : State 36 11 => s.lists 3) h).trans (hf.2.1.trans hv.2.2.1)
  · exact (congrArg (fun s : State 36 11 => s.lists 7) h).trans (hf.2.2.trans hv.2.2.2)

/-- Writing arithmetic scratch leaves the source field environment intact. -/
theorem View.setReg [NeZero t] {env : Fin n → BinaryMaterializedField.Element t}
    {st : State (n + 36) 12} (hv : View t env st) (j : Fin 36) (v : ℕ) (hj : j ≠ 20) :
    View t env (setReg st (slot n j) v) := by
  refine ⟨?_, ?_, hv.2.2⟩
  · intro i
    simpa only [setReg_regs, Function.update_of_ne (source_ne i j)] using hv.1 i
  · simpa only [setReg_regs, Function.update_of_ne
      (slot_injective.ne (Ne.symm hj))] using hv.2.1

theorem View.setStack [NeZero t] {env : Fin n → BinaryMaterializedField.Element t}
    {st : State (n + 36) 12} (hv : View t env st) (xs : List ℕ) :
    View t env (setList st 11 xs) := by
  exact ⟨hv.1, hv.2.1, by simpa [Function.update] using hv.2.2.1,
    by simpa [Function.update] using hv.2.2.2⟩

def binaryStep (op : Op) : Stmt (n + 36) 12 :=
  .seq (.pop 11 (slot n 25) (slot n 35))
    (.seq (.pop 11 (slot n 24) (slot n 35))
      (.seq (embed (binary op)) (.push 11 (slot n 26))))

def inverseStep : Stmt (n + 36) 12 :=
  .seq (.pop 11 (slot n 24) (slot n 35))
    (.seq (embed inverse) (.push 11 (slot n 26)))

def compile : Term n → Stmt (n + 36) 12
  | .bit b => .seq (.assign (slot n 26) (.const b.toNat)) (.push 11 (slot n 26))
  | .input i => .push 11 (i.castAdd 36)
  | .bin op a b => .seq (compile a) (.seq (compile b) (binaryStep op))
  | .inv a => .seq (compile a) inverseStep

theorem binaryStep_spec [NeZero t] (op : Op) (st : State (n + 36) 12)
    (env : Fin n → BinaryMaterializedField.Element t) (hv : View t env st)
    (a b : BinaryMaterializedField.Element t) (tail : List ℕ)
    (hs : st.lists 11 = (fieldEquiv t b).val :: (fieldEquiv t a).val :: tail) :
    ((binaryStep op).run st).1.lists 11 = (fieldEquiv t (op.fieldEval a b)).val :: tail ∧
      View t env ((binaryStep op).run st).1 := by
  let s := setReg (setReg (setList st 11 ((fieldEquiv t a).val :: tail))
    (slot n 25) (fieldEquiv t b).val) (slot n 35) 1
  let u := setReg (setReg (setList s 11 tail) (slot n 24) (fieldEquiv t a).val) (slot n 35) 1
  have hvs : View t env s := ((hv.setStack _).setReg 25 _ (by decide)).setReg 35 _ (by decide)
  have hvu : View t env u := ((hvs.setStack _).setReg 24 _ (by decide)).setReg 35 _ (by decide)
  have hu24 : u.regs (slot n 24) = (fieldEquiv t a).val := by simp [u, slot, Function.update]
  have hu25 : u.regs (slot n 25) = (fieldEquiv t b).val := by simp [u, s, slot, Function.update]
  have hout := binary_run_field op (u.restrict (slot n) Fin.castSucc) a b hvu.2.1
    hu24 hu25 hvu.2.2.1 hvu.2.2.2
  have hr := congrArg (fun z : State 36 11 × ℕ => z.1.regs 26) (embed_result (binary op) u)
  have hcode : ((embed (binary op)).run u).1.regs (slot n 26) =
      (fieldEquiv t (op.fieldEval a b)).val := hr.trans hout
  have hstack : ((embed (binary op)).run u).1.lists 11 = tail :=
    (embed_stack _ u).trans (by simp [u])
  have hview := embed_view (binary op)
    (fun s => ⟨(binary_frame op s).1, (binary_frame op s).2.2.2⟩) env u hvu
  have hfirst : ((Stmt.pop 11 (slot n 25) (slot n 35)).run st).1 = s := by
    simp [Stmt.run, hs, s]
  have hsecond : ((Stmt.pop 11 (slot n 24) (slot n 35)).run s).1 = u := by
    simp [Stmt.run, s, u]
  simp only [binaryStep, run_seq_fst, hfirst, hsecond, run_push_fst]
  exact ⟨by simp [hcode, hstack], hview.setStack _⟩

theorem inverseStep_spec [NeZero t] (st : State (n + 36) 12)
    (env : Fin n → BinaryMaterializedField.Element t) (hv : View t env st)
    (a : BinaryMaterializedField.Element t) (tail : List ℕ)
    (hs : st.lists 11 = (fieldEquiv t a).val :: tail) :
    (inverseStep.run st).1.lists 11 = (fieldEquiv t a⁻¹).val :: tail ∧
      View t env (inverseStep.run st).1 := by
  let u := setReg (setReg (setList st 11 tail) (slot n 24) (fieldEquiv t a).val) (slot n 35) 1
  have hvu : View t env u := ((hv.setStack _).setReg 24 _ (by decide)).setReg 35 _ (by decide)
  have hu24 : u.regs (slot n 24) = (fieldEquiv t a).val := by simp [u, slot, Function.update]
  have hout := inverse_run_field (u.restrict (slot n) Fin.castSucc) a hvu.2.1
    hu24 hvu.2.2.1 hvu.2.2.2
  have hr := congrArg (fun z : State 36 11 × ℕ => z.1.regs 26) (embed_result inverse u)
  have hcode : ((embed inverse).run u).1.regs (slot n 26) =
      (fieldEquiv t a⁻¹).val := hr.trans hout
  have hstack : ((embed inverse).run u).1.lists 11 = tail :=
    (embed_stack _ u).trans (by simp [u])
  have hview := embed_view inverse
    (fun s => ⟨(inverse_frame s).1, (inverse_frame s).2.2.2⟩) env u hvu
  have hfirst : ((Stmt.pop 11 (slot n 24) (slot n 35)).run st).1 = u := by
    simp [Stmt.run, hs, u]
  simp only [inverseStep, run_seq_fst, hfirst, run_push_fst]
  exact ⟨by simp [hcode, hstack], hview.setStack _⟩

@[simp] theorem code_zero :
    (fieldEquiv t (0 : BinaryMaterializedField.Element t)).val = 0 := by
  change WordCodec.value (encode (BinaryWordMaterialization.zero t)) = 0
  rw [encode_zero]
  induction t with
  | zero => rfl
  | succ t ih => simp [WordCodec.value, List.replicate_succ, ih]

@[simp] theorem code_one [NeZero t] :
    (fieldEquiv t (1 : BinaryMaterializedField.Element t)).val = 1 :=
  BinaryFieldWordCode.value_encode_one t (Nat.pos_of_ne_zero (NeZero.ne t))

/-- Every compiled expression pushes its exact field code and preserves its environment. -/
theorem compile_spec [NeZero t] (a : Term n) (st : State (n + 36) 12)
    (env : Fin n → BinaryMaterializedField.Element t) (hv : View t env st) :
    ((compile a).run st).1.lists 11 = (fieldEquiv t (a.eval env)).val :: st.lists 11 ∧
      View t env ((compile a).run st).1 := by
  induction a generalizing st with
  | bit b =>
      simp only [compile, run_seq_fst, run_assign_fst, Expr.eval, run_push_fst,
        setReg_regs, Function.update_self, setReg_lists]
      refine ⟨?_, ((hv.setReg 26 b.toNat (by decide)).setStack _)⟩
      cases b
      · change 0 :: st.lists 11 = (fieldEquiv t (0 : BinaryMaterializedField.Element t)).val :: _
        rw [code_zero]
      · change 1 :: st.lists 11 = (fieldEquiv t (1 : BinaryMaterializedField.Element t)).val :: _
        rw [code_one]
  | input i =>
      simp only [compile, run_push_fst]
      exact ⟨congrArg (· :: st.lists 11) (hv.1 i), hv.setStack _⟩
  | bin op a b iha ihb =>
      obtain ⟨ha, hva⟩ := iha st hv
      obtain ⟨hb, hvb⟩ := ihb ((compile a).run st).1 hva
      simp only [compile, run_seq_fst]
      exact binaryStep_spec op _ env hvb (a.eval env) (b.eval env) (st.lists 11)
        (by rw [hb, ha])
  | inv a ih =>
      obtain ⟨ha, hva⟩ := ih st hv
      simp only [compile, run_seq_fst]
      exact inverseStep_spec _ env hva (a.eval env) (st.lists 11) ha

/-- Scalar evaluation consumes the final stack cell into the result register. -/
def scalar (a : Term n) : Stmt (n + 36) 12 :=
  .seq (compile a) (.pop 11 (slot n 26) (slot n 35))

theorem scalar_spec [NeZero t] (a : Term n) (st : State (n + 36) 12)
    (env : Fin n → BinaryMaterializedField.Element t) (hv : View t env st) :
    ((scalar a).run st).1.regs (slot n 26) = (fieldEquiv t (a.eval env)).val ∧
      ((scalar a).run st).1.lists 11 = st.lists 11 ∧
      View t env ((scalar a).run st).1 := by
  obtain ⟨ha, hva⟩ := compile_spec a st env hv
  simp only [scalar, Stmt.run, ha]
  refine ⟨?_, rfl, ((hva.setStack _).setReg 26 _ (by decide)).setReg 35 _ (by decide)⟩
  simp [slot, Function.update]

end PCP.Lang.FieldExpression
