import PCP.Complexity.BinaryCubicQueryCost
import PCP.Complexity.BooleanLabelConstructorsCost
import PCP.Complexity.BooleanLabelAddition
import PCP.Complexity.HadamardLabelCost

/-!
# Actual two-label derived cubic query

The homogeneous word and fresh coefficient mask are retained in source lists
20 and 21. The program computes the cubic transform, adds the mask, and serializes
both coefficient labels in their required order. The field width and scalar weight
are stored in registers 98 and 99, with modulus and empty source lists 22 and 23.
-/

namespace PCP.Lang.DerivedPrimary

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList BinaryFieldCode

variable {t : ℕ} [NeZero t]

def call {R Q : ℕ} (hR : R ≤ 80) (hQ : Q ≤ 20) (p : Stmt R Q) : Stmt 100 32 :=
  p.rename (Fin.castLE (hR.trans (by decide))) (Fin.castLE (hQ.trans (by decide)))

theorem call_result {R Q : ℕ} (hR : R ≤ 80) (hQ : Q ≤ 20) (p : Stmt R Q)
    (st : State 100 32) :
    (((call hR hQ p).run st).1.restrict (Fin.castLE (hR.trans (by decide)))
      (Fin.castLE (hQ.trans (by decide))), ((call hR hQ p).run st).2) =
    p.run (st.restrict (Fin.castLE (hR.trans (by decide)))
      (Fin.castLE (hQ.trans (by decide)))) :=
  p.run_rename _ _ (Fin.castLE_injective _) (Fin.castLE_injective _) st

structure Frame (st out : State 100 32) : Prop where
  regs : ∀ i : Fin 100, 80 ≤ i.val → out.regs i = st.regs i
  lists : ∀ i : Fin 32, 20 ≤ i.val → out.lists i = st.lists i

theorem Frame.trans {st u v : State 100 32} (h : Frame st u) (g : Frame u v) :
    Frame st v := ⟨fun i hi => (g.regs i hi).trans (h.regs i hi),
      fun i hi => (g.lists i hi).trans (h.lists i hi)⟩

theorem call_frame {R Q : ℕ} (hR : R ≤ 80) (hQ : Q ≤ 20) (p : Stmt R Q)
    (st : State 100 32) : Frame st ((call hR hQ p).run st).1 := by
  constructor
  · intro i hi
    apply Stmt.run_rename_reg_outside
    intro j hj
    have := congrArg Fin.val hj
    simp only [Fin.val_castLE] at this
    omega
  · intro i hi
    apply Stmt.run_rename_list_outside
    intro j hj
    have := congrArg Fin.val hj
    simp only [Fin.val_castLE] at this
    omega

theorem frame_of_writes (p : Stmt 100 32)
    (hr : ∀ i ∈ p.regWrites, i.val < 80) (hl : ∀ i ∈ p.listWrites, i.val < 20)
    (st : State 100 32) : Frame st (p.run st).1 := by
  constructor
  · intro i hi
    apply run_regs_frame
    intro hm
    have := hr i hm
    omega
  · intro i hi
    apply run_lists_frame
    intro hm
    have := hl i hm
    omega

structure Context (w : BinaryMaterializedField.Element t) (v : Fin t → ZMod 2)
    (mask : Coefficients t 3) (st : State 100 32) : Prop where
  width : st.regs 98 = t
  weight : st.regs 99 = (fieldEquiv t w).val
  word : st.lists 20 = List.ofFn (fun i => (v i).val)
  mask : st.lists 21 = encode mask
  modulus : st.lists 22 = BinaryField.encode (BinaryWordMaterialization.modulus t)
  empty : st.lists 23 = []

theorem Context.of_frame {w : BinaryMaterializedField.Element t} {v : Fin t → ZMod 2}
    {mask : Coefficients t 3} {st out : State 100 32}
    (hc : Context w v mask st) (hf : Frame st out) : Context w v mask out :=
  ⟨(hf.regs 98 (by decide)).trans hc.width, (hf.regs 99 (by decide)).trans hc.weight,
    (hf.lists 20 (by decide)).trans hc.word, (hf.lists 21 (by decide)).trans hc.mask,
    (hf.lists 22 (by decide)).trans hc.modulus, (hf.lists 23 (by decide)).trans hc.empty⟩

def prepare : Stmt 100 32 := .seq (.copy 22 3) (.seq (.copy 23 7)
  (.seq (.copy 20 17) (.seq (.assign 20 (.var 98)) (.assign 56 (.const 1)))))

def homogeneous : Stmt 100 32 :=
  call (by decide) (by decide) BooleanLabelConstructors.homogeneous

def affine : Stmt 100 32 := .seq prepare homogeneous

def translatePrepare : Stmt 100 32 := .seq (.copy 5 13)
  (.seq (.copy 22 3) (.seq (.copy 23 7)
    (.seq (.assign 20 (.var 98)) (.assign 51 (.var 99)))))

def translate (weighted : Bool) : Stmt 100 32 := .seq translatePrepare
  (call (by decide) (by decide) (BinaryCubicQueryLang.query weighted))

def maskPrepare : Stmt 100 32 := .seq (.copy 5 4) (.copy 21 5)

def maskQuery : Stmt 100 32 := .seq maskPrepare
  (call (by decide) (by decide) BooleanLabelAddition.add)

attribute [local irreducible] homogeneous BooleanLabelConstructors.homogeneous
  BinaryCubicQueryLang.query

theorem affine_run (w : BinaryMaterializedField.Element t) (v : Fin t → ZMod 2)
    (mask : Coefficients t 3) (st : State 100 32) (hc : Context w v mask st) :
    (affine.run st).1.lists 5 = encode
      (BooleanCoefficientArithmetic.homogeneousIndex (le_refl 1) v) ∧
    Frame st (affine.run st).1 := by
  have hp := BooleanLabelConstructors.homogeneous_run (le_refl 1) v
    ((prepare.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (by simp [prepare, Stmt.run, Expr.eval, Function.update, State.restrict, hc.width])
    (by simp [prepare, Stmt.run, Expr.eval, Function.update, State.restrict])
    (by simp [prepare, Stmt.run, Expr.eval, Function.update, State.restrict, hc.empty])
    (by simp [prepare, Stmt.run, Expr.eval, Function.update, State.restrict, hc.word])
  rw [← call_result (by decide) (by decide) BooleanLabelConstructors.homogeneous
    (prepare.run st).1] at hp
  have hpf : Frame st (prepare.run st).1 :=
    frame_of_writes _ (by decide) (by decide) st
  have hcf := call_frame (by decide) (by decide) BooleanLabelConstructors.homogeneous
    (prepare.run st).1
  simp only [affine, run_seq_fst]
  refine ⟨?_, hpf.trans (by simpa only [homogeneous] using hcf)⟩
  simpa only [homogeneous, State.restrict_lists,
    show Fin.castLE (by decide : 20 ≤ 32) (5 : Fin 20) = (5 : Fin 32) from rfl] using hp

theorem translate_run (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) (st : State 100 32)
    (ht : st.regs 98 = t) (hw : st.regs 99 = (fieldEquiv t w).val)
    (hm : st.lists 22 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 23 = []) (hL : st.lists 5 = encode L) :
    ((translate weighted).run st).1.lists 5 = encode
      (BinaryCubicQueryLang.translated weighted w L) ∧
    ((translate weighted).run st).1.lists 7 = [] ∧
    Frame st ((translate weighted).run st).1 := by
  have hp := BinaryCubicQueryLang.query_run weighted w L
    ((translatePrepare.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (by simpa [translatePrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using ht)
    (by simpa [translatePrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using hw)
    (by simpa [translatePrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using hm)
    (by simpa [translatePrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using he)
    (by simpa [translatePrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using hL)
  rw [← call_result (by decide) (by decide) (BinaryCubicQueryLang.query weighted)
    (translatePrepare.run st).1] at hp
  have h7 : ((call (by decide) (by decide) (BinaryCubicQueryLang.query weighted)).run
      (translatePrepare.run st).1).1.lists 7 = (translatePrepare.run st).1.lists 7 := by
    apply run_lists_frame
    cases weighted <;> unfold call BinaryCubicQueryLang.query <;> decide
  have hpf : Frame st (translatePrepare.run st).1 :=
    frame_of_writes _ (by decide) (by decide) st
  simp only [translate, run_seq_fst]
  exact ⟨by simpa only [State.restrict_lists,
      show Fin.castLE (by decide : 17 ≤ 32) (5 : Fin 17) = (5 : Fin 32) from rfl] using hp,
    h7.trans (by simpa [translatePrepare, Stmt.run, Function.update] using he),
    hpf.trans (call_frame (by decide) (by decide) _ _)⟩

omit [NeZero t] in
theorem maskQuery_run (p mask : Coefficients t 3) (st : State 100 32)
    (hp : st.lists 5 = encode p) (hm : st.lists 21 = encode mask)
    (he : st.lists 7 = []) :
    (maskQuery.run st).1.lists 1 = encode (p + mask) ∧ Frame st (maskQuery.run st).1 := by
  have ha := BooleanLabelAddition.add_run p mask
    ((maskPrepare.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (by simpa [maskPrepare, Stmt.run, Function.update, State.restrict] using hp)
    (by simpa [maskPrepare, Stmt.run, Function.update, State.restrict] using hm)
    (by simpa [maskPrepare, Stmt.run, Function.update, State.restrict] using he)
  rw [← call_result (by decide) (by decide) BooleanLabelAddition.add (maskPrepare.run st).1] at ha
  simp only [maskQuery, run_seq_fst]
  exact ⟨by simpa only [State.restrict_lists,
      show Fin.castLE (by decide : 8 ≤ 32) (1 : Fin 8) = (1 : Fin 32) from rfl] using ha,
    (frame_of_writes _ (by decide) (by decide) st).trans (call_frame _ _ _ _)⟩

theorem affine_frame (st : State 100 32) : Frame st (affine.run st).1 := by
  rw [affine, run_seq_fst, homogeneous]
  exact (frame_of_writes prepare (by decide) (by decide) st).trans
    (call_frame (by decide) (by decide) BooleanLabelConstructors.homogeneous _)

theorem translate_frame (weighted : Bool) (st : State 100 32) :
    Frame st ((translate weighted).run st).1 := by
  rw [translate, run_seq_fst]
  exact (frame_of_writes translatePrepare (by decide) (by decide) st).trans
    (call_frame (by decide) (by decide) (BinaryCubicQueryLang.query weighted) _)

theorem maskQuery_frame (st : State 100 32) : Frame st (maskQuery.run st).1 := by
  rw [maskQuery, run_seq_fst]
  exact (frame_of_writes maskPrepare (by decide) (by decide) st).trans
    (call_frame (by decide) (by decide) BooleanLabelAddition.add _)

attribute [local irreducible] affine translate maskQuery

def masked (weighted : Bool) : Stmt 100 32 :=
  .seq affine (.seq (translate weighted) maskQuery)

private theorem compose_masked (p₁ p₂ p₃ : Stmt 100 32)
    (w : BinaryMaterializedField.Element t) (v : Fin t → ZMod 2)
    (mask p : Coefficients t 3) (L : Coefficients t 1)
    (h₁ : ∀ st, Context w v mask st →
      (p₁.run st).1.lists 5 = encode L ∧ Frame st (p₁.run st).1)
    (h₂ : ∀ st, Context w v mask st → st.lists 5 = encode L →
      (p₂.run st).1.lists 5 = encode p ∧ (p₂.run st).1.lists 7 = [] ∧
      Frame st (p₂.run st).1)
    (h₃ : ∀ st, st.lists 5 = encode p → st.lists 21 = encode mask →
      st.lists 7 = [] → (p₃.run st).1.lists 1 = encode (p + mask) ∧
      Frame st (p₃.run st).1)
    (st : State 100 32) (hc : Context w v mask st) :
    ((Stmt.seq p₁ (.seq p₂ p₃)).run st).1.lists 1 = encode (p + mask) ∧
    Frame st ((Stmt.seq p₁ (.seq p₂ p₃)).run st).1 := by
  have ha := h₁ st hc
  have hcs := hc.of_frame ha.2
  have hb := h₂ (p₁.run st).1 hcs ha.1
  have hcu := hcs.of_frame hb.2.2
  have h := h₃ (p₂.run (p₁.run st).1).1 hb.1 hcu.mask hb.2.1
  exact ⟨h.1, ha.2.trans (hb.2.2.trans h.2)⟩

theorem masked_run (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (v : Fin t → ZMod 2) (mask : Coefficients t 3) (st : State 100 32)
    (hc : Context w v mask st) :
    ((masked weighted).run st).1.lists 1 = encode
      (BinaryCubicQueryLang.translated weighted w
        (BooleanCoefficientArithmetic.homogeneousIndex (le_refl 1) v) + mask) ∧
    Frame st ((masked weighted).run st).1 :=
  compose_masked affine (translate weighted) maskQuery w v mask _ _
    (affine_run w v mask)
    (fun st hc hL => translate_run weighted w _ st
      hc.width hc.weight hc.modulus hc.empty hL)
    (maskQuery_run _ mask) st hc

def decode : Stmt 100 32 := call (by decide) (by decide) WordCodec.decode

omit [NeZero t] in
theorem decode_run {r : ℕ} (p : Coefficients t r) (st : State 100 32)
    (hp : st.lists 0 = encode p) :
    (decode.run st).1.regs 1 = HadamardLabel.code p := by
  have h := (WordCodec.decode_run
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))).1
  rw [← call_result (by decide) (by decide) WordCodec.decode st] at h
  simpa only [decode, State.restrict_regs, State.restrict_lists,
    show Fin.castLE (by decide : 5 ≤ 100) (1 : Fin 5) = (1 : Fin 100) from rfl,
    show Fin.castLE (by decide : 1 ≤ 32) (0 : Fin 1) = (0 : Fin 32) from rfl,
    hp, HadamardLabel.value_encode] using h

def loadCode (src : Fin 32) (dst : Fin 100) : Stmt 100 32 :=
  .seq (.copy src 0) (.seq decode (.assign dst (.var 1)))

omit [NeZero t] in
theorem loadCode_run {r : ℕ} (src : Fin 32) (dst : Fin 100)
    (p : Coefficients t r) (st : State 100 32) (hp : st.lists src = encode p) :
    ((loadCode src dst).run st).1.regs dst = HadamardLabel.code p := by
  have h := decode_run p (setList st 0 (st.lists src)) (by simpa using hp)
  simpa only [loadCode, run_seq_fst, run_copy_fst, run_assign_fst,
    Expr.eval, setReg_regs, Function.update_self] using h

def serialize : Stmt 100 32 := .seq (loadCode 1 96) (.seq (loadCode 21 97)
  (.seq (.copy 23 24) (.seq (.push 24 97) (.push 24 96))))

omit [NeZero t] in
theorem serialize_run (p mask : Coefficients t 3) (st : State 100 32)
    (hp : st.lists 1 = encode p) (hm : st.lists 21 = encode mask) (he : st.lists 23 = []) :
    (serialize.run st).1.lists 24 = [HadamardLabel.code p, HadamardLabel.code mask] := by
  have h1 := loadCode_run 1 96 p st hp
  have hm1 := (run_lists_frame (loadCode 1 96) 21 (by decide) st).trans hm
  have he1 := (run_lists_frame (loadCode 1 96) 23 (by decide) st).trans he
  generalize hs : ((loadCode 1 96).run st).1 = s at *
  have h2 := loadCode_run 21 97 mask s hm1
  have h1' := (run_regs_frame (loadCode 21 97) 96 (by decide) s).trans h1
  have he2 := (run_lists_frame (loadCode 21 97) 23 (by decide) s).trans he1
  simp only [serialize, run_seq_fst, hs]
  generalize hu : ((loadCode 21 97).run s).1 = u at *
  simp [run_copy_fst, run_push_fst, Function.update, h1', h2, he2]

def labels (weighted : Bool) : Stmt 100 32 := .seq (masked weighted) serialize

theorem labels_run (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (v : Fin t → ZMod 2) (mask : Coefficients t 3) (st : State 100 32)
    (hc : Context w v mask st) :
    ((labels weighted).run st).1.lists 24 =
      [HadamardLabel.code (BinaryCubicQueryLang.translated weighted w
        (BooleanCoefficientArithmetic.homogeneousIndex (le_refl 1) v) + mask),
       HadamardLabel.code mask] := by
  have hm := masked_run weighted w v mask st hc
  have hctx := hc.of_frame hm.2
  simp only [labels, run_seq_fst]
  exact serialize_run _ mask _ hm.1 hctx.mask hctx.empty

theorem labels_reg (weighted : Bool) (st : State 100 32) (i : Fin 100)
    (hi : 80 ≤ i.val) (h96 : i ≠ 96) (h97 : i ≠ 97) :
    ((labels weighted).run st).1.regs i = st.regs i := by
  have hs : ∀ s : State 100 32, (serialize.run s).1.regs i = s.regs i := by
    intro s
    apply run_regs_frame
    have hlow : ∀ j ∈ serialize.regWrites, j.val < 80 ∨ j = 96 ∨ j = 97 := by decide
    intro hm
    rcases hlow i hm with h | h | h <;> simp_all
    omega
  simp only [labels, run_seq_fst, hs, masked]
  exact ((affine_frame st).trans ((translate_frame weighted _).trans
    (maskQuery_frame _))).regs i hi

theorem labels_list (weighted : Bool) (st : State 100 32) (i : Fin 32)
    (hi : 20 ≤ i.val) (h24 : i ≠ 24) :
    ((labels weighted).run st).1.lists i = st.lists i := by
  have hs : ∀ s : State 100 32, (serialize.run s).1.lists i = s.lists i := by
    intro s
    apply run_lists_frame
    have hlow : ∀ j ∈ serialize.listWrites, j.val < 20 ∨ j = 24 := by decide
    intro hm
    rcases hlow i hm with h | h
    · omega
    · exact h24 h
  simp only [labels, run_seq_fst, hs, masked]
  exact ((affine_frame st).trans ((translate_frame weighted _).trans
    (maskQuery_frame _))).lists i hi

end PCP.Lang.DerivedPrimary
