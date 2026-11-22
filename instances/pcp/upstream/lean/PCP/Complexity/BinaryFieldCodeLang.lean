import PCP.Complexity.BinaryRootPredicateCost

/-!
# Binary field arithmetic on natural-number codes

The interface uses degree register `20`, operand codes `24` and `25`, stored
modulus list `3`, and empty list `7`. It materializes fixed-width words, performs
proved coefficient arithmetic, and returns the result code in register `26`.
The degree, input codes, modulus, and empty-list source are preserved.
-/

namespace PCP.Lang.BinaryFieldCode

open PCP.Algebraic BinaryField BinaryFieldWordCode BinaryRootPredicate

/-- Serialize one numeric operand and retain its fixed-width coefficient list. -/
def loadCode (x : Fin 36) (L : Fin 11) : Stmt 36 11 :=
  .seq (.assign 33 (.var x)) (.seq serialize (.copy 8 L))

theorem loadCode_run (x : Fin 36) (L : Fin 11) (st : State 36 11)
    (he : st.lists 7 = []) :
    ((loadCode x L).run st).1.lists L =
      BinaryPolynomialSelector.digits (st.regs 20) (st.regs x) := by
  have h := serialize_run (setReg st 33 (st.regs x)) (by simpa using he)
  simpa [loadCode, run_seq_fst, run_assign_fst, run_copy_fst, Expr.eval,
    Function.update] using h

def add36 : Stmt 36 11 :=
  BinaryField.add.rename powerRegs BinaryFieldPower.listEmbedding

def mul36 : Stmt 36 11 := BinaryFieldPower.multiplication.rename powerRegs id

def inverse36 : Stmt 36 11 := BinaryFieldInverse.inverse.rename powerRegs id

inductive Op | add | mul
  deriving DecidableEq

/-- The word semantics of the selected operation, with the production modulus. -/
def Op.eval {t : ℕ} [NeZero t] (op : Op) (ht : 0 < t)
    (v w : BinaryWordMaterialization.Word t) : BinaryWordMaterialization.Word t :=
  match op with
  | .add => BinaryWordMaterialization.add v w
  | .mul => BinaryWordMaterialization.mul ht (BinaryWordMaterialization.modulus t) v w

/-- Prepare the destructive addition routine from saved word operands. -/
def addSaved : Stmt 36 11 :=
  .seq (.copy 4 0) (.seq (.copy 5 2) (.seq (.copy 7 1) add36))

def operate : Op → Stmt 36 11
  | .add => addSaved
  | .mul => mul36

theorem add36_run {t : ℕ} [NeZero t] (st : State 36 11)
    (v w : BinaryWordMaterialization.Word t)
    (hv : st.lists 0 = encode v) (hw : st.lists 2 = encode w) (he : st.lists 1 = []) :
    (add36.run st).1.lists 1 = encode (BinaryWordMaterialization.add v w) := by
  have h := congrArg (fun z : State 8 8 × ℕ => z.1.lists 1)
    (BinaryField.add.run_rename powerRegs BinaryFieldPower.listEmbedding
      (Fin.castLE_injective _) BinaryFieldPower.listEmbedding_injective st)
  exact h.trans (BinaryField.add_run_encode _ v w hv hw he)

theorem mul36_run {t : ℕ} [NeZero t] (ht : 0 < t) (st : State 36 11)
    (v w : BinaryWordMaterialization.Word t)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t))
    (hv : st.lists 4 = encode v) (hw : st.lists 5 = encode w) (he : st.lists 7 = []) :
    (mul36.run st).1.lists 1 =
      encode (BinaryWordMaterialization.mul ht (BinaryWordMaterialization.modulus t) v w) := by
  have h := congrArg (fun z : State 8 11 × ℕ => z.1.lists 1)
    (BinaryFieldPower.multiplication.run_rename powerRegs id
      (Fin.castLE_injective _) Function.injective_id st)
  exact h.trans (BinaryFieldPower.multiplication_run ht _ _ v w hm hv hw he)

theorem inverse36_run {t : ℕ} [NeZero t] (st : State 36 11)
    (v : BinaryWordMaterialization.Word t)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t))
    (hv : st.lists 8 = encode v) (he : st.lists 7 = []) :
    (inverse36.run st).1.lists 1 = encode (BinaryWordMaterialization.inverse v) := by
  have h := congrArg (fun z : State 8 11 × ℕ => z.1.lists 1)
    (BinaryFieldInverse.inverse.run_rename powerRegs id
      (Fin.castLE_injective _) Function.injective_id st)
  exact h.trans (BinaryFieldInverse.inverse_run_encode (Nat.pos_of_ne_zero (NeZero.ne t)) _
    _ v (BinaryWordMaterialization.toWord_ofWord _) hm hv he)

theorem operate_run {t : ℕ} [NeZero t] (op : Op) (ht : 0 < t) (st : State 36 11)
    (v w : BinaryWordMaterialization.Word t)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t))
    (hv : st.lists 4 = encode v) (hw : st.lists 5 = encode w) (he : st.lists 7 = []) :
    ((operate op).run st).1.lists 1 = encode (op.eval ht v w) := by
  cases op with
  | mul => exact mul36_run ht st v w hm hv hw he
  | add =>
      simp only [operate, addSaved, run_seq_fst, run_copy_fst]
      apply add36_run
      · simp [hv, Function.update]
      · simp [hw, Function.update]
      · simp [he, Function.update]

def binaryWords (op : Op) : Stmt 36 11 :=
  .seq (loadCode 24 4) (.seq (loadCode 25 5) (operate op))

theorem binaryWords_run {t : ℕ} [NeZero t] (op : Op) (ht : 0 < t) (st : State 36 11)
    (i j : Fin (2 ^ t)) (h20 : st.regs 20 = t)
    (h24 : st.regs 24 = i.val) (h25 : st.regs 25 = j.val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    ((binaryWords op).run st).1.lists 1 = encode (op.eval ht (word t i) (word t j)) := by
  have hs4 := loadCode_run 24 4 st he
  rw [h20, h24, ← encode_word] at hs4
  have hs20 := run_regs_frame (loadCode 24 4) 20 (by decide) st
  have hs25 := run_regs_frame (loadCode 24 4) 25 (by decide) st
  have hs3 := run_lists_frame (loadCode 24 4) 3 (by decide) st
  have hs7 := run_lists_frame (loadCode 24 4) 7 (by decide) st
  simp only [binaryWords, run_seq_fst]
  generalize hs : ((loadCode 24 4).run st).1 = s at *
  have hu5 := loadCode_run 25 5 s (hs7.trans he)
  rw [hs20, h20, hs25, h25, ← encode_word] at hu5
  have hu4 := run_lists_frame (loadCode 25 5) 4 (by decide) s
  have hu3 := run_lists_frame (loadCode 25 5) 3 (by decide) s
  have hu7 := run_lists_frame (loadCode 25 5) 7 (by decide) s
  generalize hu : ((loadCode 25 5).run s).1 = u at *
  exact operate_run op ht u _ _ (hu3.trans (hs3.trans hm)) (hu4.trans hs4) hu5
    (hu7.trans (hs7.trans he))

/-- Decode the computed word and move the result above the arithmetic scratch registers. -/
def finish : Stmt 36 11 := .seq decode36 (.assign 26 (.var 1))

theorem finish_run (st : State 36 11) :
    (finish.run st).1.regs 26 = WordCodec.value (st.lists 1) := by
  simpa only [finish, run_seq_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update_self] using decode36_run st

def binary (op : Op) : Stmt 36 11 := .seq (binaryWords op) finish

theorem binary_run {t : ℕ} [NeZero t] (op : Op) (ht : 0 < t) (st : State 36 11)
    (i j : Fin (2 ^ t)) (h20 : st.regs 20 = t)
    (h24 : st.regs 24 = i.val) (h25 : st.regs 25 = j.val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    ((binary op).run st).1.regs 26 =
      WordCodec.value (encode (op.eval ht (word t i) (word t j))) := by
  rw [binary, run_seq_fst, finish_run, binaryWords_run op ht st i j h20 h24 h25 hm he]

def inverseWords : Stmt 36 11 := .seq (loadCode 24 8) inverse36

theorem inverseWords_run {t : ℕ} [NeZero t] (st : State 36 11)
    (i : Fin (2 ^ t)) (h20 : st.regs 20 = t) (h24 : st.regs 24 = i.val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    (inverseWords.run st).1.lists 1 = encode (BinaryWordMaterialization.inverse (word t i)) := by
  have hs8 := loadCode_run 24 8 st he
  rw [h20, h24, ← encode_word] at hs8
  have hs3 := run_lists_frame (loadCode 24 8) 3 (by decide) st
  have hs7 := run_lists_frame (loadCode 24 8) 7 (by decide) st
  rw [inverseWords, run_seq_fst]
  exact inverse36_run _ _ (hs3.trans hm) hs8 (hs7.trans he)

def inverse : Stmt 36 11 := .seq inverseWords finish

theorem inverse_run {t : ℕ} [NeZero t] (st : State 36 11)
    (i : Fin (2 ^ t)) (h20 : st.regs 20 = t) (h24 : st.regs 24 = i.val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    (inverse.run st).1.regs 26 =
      WordCodec.value (encode (BinaryWordMaterialization.inverse (word t i))) := by
  rw [inverse, run_seq_fst, finish_run, inverseWords_run st i h20 h24 hm he]

/-- Each binary operation retains the degree, input codes, modulus, and empty source. -/
theorem binary_frame (op : Op) (st : State 36 11) :
    ((binary op).run st).1.regs 20 = st.regs 20 ∧
    ((binary op).run st).1.regs 24 = st.regs 24 ∧
    ((binary op).run st).1.regs 25 = st.regs 25 ∧
    ((binary op).run st).1.lists 3 = st.lists 3 ∧
    ((binary op).run st).1.lists 7 = st.lists 7 := by
  exact ⟨run_regs_frame _ _ (by cases op <;> decide) _,
    run_regs_frame _ _ (by cases op <;> decide) _,
    run_regs_frame _ _ (by cases op <;> decide) _,
    run_lists_frame _ _ (by cases op <;> decide) _,
    run_lists_frame _ _ (by cases op <;> decide) _⟩

theorem inverse_frame (st : State 36 11) :
    (inverse.run st).1.regs 20 = st.regs 20 ∧
    (inverse.run st).1.regs 24 = st.regs 24 ∧
    (inverse.run st).1.regs 25 = st.regs 25 ∧
    (inverse.run st).1.lists 3 = st.lists 3 ∧
    (inverse.run st).1.lists 7 = st.lists 7 := by
  exact ⟨run_regs_frame _ _ (by decide) _, run_regs_frame _ _ (by decide) _,
    run_regs_frame _ _ (by decide) _, run_lists_frame _ _ (by decide) _,
    run_lists_frame _ _ (by decide) _⟩

end PCP.Lang.BinaryFieldCode
