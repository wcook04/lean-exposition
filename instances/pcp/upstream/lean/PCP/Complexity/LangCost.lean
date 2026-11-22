import PCP.Complexity.Lang
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Cost of loop-free statements

**`loopFree_bound`**: a loop-free statement `s` costs at most `s.C · s.meas st`, where `s.C` is a
constant depending only on `s`, and `s.meas st` counts only what `s` actually reads: the sizes of
the registers it reads *before writing them* (`Stmt.uses`, upward-exposed uses), the sizes of the
lists it reads (`Stmt.lUses`), and its constants.  It also bounds the sizes it leaves behind.

This is what makes a program's cost proof local: a loop body's cost depends on the counter and the
few registers it reads, not on scratch registers left over from earlier iterations, which `uses`
excludes because the body overwrites them first (`Stmt.mustW`).
-/

namespace PCP.Lang

variable {R Q : ℕ}

/-! ## Expressions -/

/-- The registers an expression reads. -/
def Expr.uses : Expr R → List (Fin R)
  | .const _ => []
  | .var x => [x]
  | .add x y | .sub x y | .mul x y | .div x y | .mod x y | .eq x y | .lt x y => [x, y]

/-- The size of an expression's constant. -/
def Expr.csize : Expr R → ℕ
  | .const c => Nat.size c
  | _ => 0

theorem size_add_le (a b : ℕ) : Nat.size (a + b) ≤ Nat.size a + Nat.size b + 1 := by
  rw [Nat.size_le]
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have h1 : 2 ^ Nat.size a ≤ 2 ^ (Nat.size a + Nat.size b) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ Nat.size b ≤ 2 ^ (Nat.size a + Nat.size b) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega

theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem size_le_one_of_le_one {a : ℕ} (h : a ≤ 1) : Nat.size a ≤ 1 := by
  rw [Nat.size_le]; omega

theorem Expr.readSize_le (r : Fin R → ℕ) (e : Expr R) :
    e.readSize r ≤ (e.uses.map fun x => Nat.size (r x)).sum + e.csize := by
  cases e <;> simp [Expr.readSize, Expr.uses, Expr.csize]

theorem Expr.size_eval_le (r : Fin R → ℕ) (e : Expr R) :
    Nat.size (e.eval r) ≤ (e.uses.map fun x => Nat.size (r x)).sum + e.csize + 1 := by
  cases e with
  | const c => simp [Expr.eval, Expr.uses, Expr.csize]
  | var x => simp [Expr.eval, Expr.uses, Expr.csize]
  | add x y => simpa [Expr.eval, Expr.uses, Expr.csize] using size_add_le (r x) (r y)
  | sub x y =>
    simp only [Expr.eval, Expr.uses, Expr.csize, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    have := Nat.size_le_size (Nat.sub_le (r x) (r y)); omega
  | mul x y => simpa [Expr.eval, Expr.uses, Expr.csize] using
      (size_mul_le (r x) (r y)).trans (Nat.le_succ _)
  | div x y =>
    simp only [Expr.eval, Expr.uses, Expr.csize, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    have := Nat.size_le_size (Nat.div_le_self (r x) (r y)); omega
  | mod x y =>
    simp only [Expr.eval, Expr.uses, Expr.csize, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    have := Nat.size_le_size (Nat.mod_le (r x) (r y)); omega
  | eq x y =>
    simp only [Expr.eval, Expr.uses, Expr.csize]
    have := size_le_one_of_le_one (show (if r x = r y then 1 else 0) ≤ 1 by split_ifs <;> omega)
    simp; omega
  | lt x y =>
    simp only [Expr.eval, Expr.uses, Expr.csize]
    have := size_le_one_of_le_one (show (if r x < r y then 1 else 0) ≤ 1 by split_ifs <;> omega)
    simp; omega

/-! ## Statements: uses, must-writes, constants -/

/-- Registers a statement certainly writes. -/
def Stmt.mustW : Stmt R Q → List (Fin R)
  | .skip | .push _ _ | .rev _ | .copy _ _ | .revApp _ _ | .loop _ _ => []
  | .seq s t => s.mustW ++ t.mustW
  | .assign x _ | .len _ x => [x]
  | .pop _ x flag => [x, flag]
  | .ite _ s t => s.mustW.filter fun r => decide (r ∈ t.mustW)

/-- **Upward-exposed register uses**: registers read before the statement writes them. -/
def Stmt.uses : Stmt R Q → List (Fin R)
  | .skip | .pop _ _ _ | .len _ _ | .rev _ | .copy _ _ | .revApp _ _ => []
  | .seq s t => s.uses ++ t.uses.filter fun r => decide (r ∉ s.mustW)
  | .assign _ e => e.uses
  | .push _ x => [x]
  | .ite x s t => x :: (s.uses ++ t.uses)
  | .loop x s => x :: s.uses

/-- Lists a statement reads (whose size its cost or effect depends on). -/
def Stmt.lUses : Stmt R Q → List (Fin Q)
  | .skip | .assign _ _ | .push _ _ => []
  | .seq s t | .ite _ s t => s.lUses ++ t.lUses
  | .pop L _ _ | .len L _ | .rev L | .copy L _ | .revApp L _ => [L]
  | .loop _ s => s.lUses

/-- The total size of a statement's constants. -/
def Stmt.csize : Stmt R Q → ℕ
  | .assign _ e => e.csize
  | .seq s t | .ite _ s t => s.csize + t.csize
  | .loop _ s => s.csize
  | _ => 0

/-- No loops. -/
def Stmt.loopFree : Stmt R Q → Bool
  | .seq s t | .ite _ s t => s.loopFree && t.loopFree
  | .loop _ _ => false
  | _ => true

/-- The statement's read width. -/
def Stmt.width (s : Stmt R Q) : ℕ := s.uses.length + s.lUses.length

/-- **The cost constant.** -/
def Stmt.C : Stmt R Q → ℕ
  | .seq s t => s.C + t.C * (1 + t.width * s.C) + 1
  | .ite _ s t => s.C + t.C + 1
  | _ => 3

/-- **What a statement's cost is measured against**: the sizes of its exposed register uses and its
list uses, its constants, plus one. -/
def Stmt.meas (s : Stmt R Q) (st : State R Q) : ℕ :=
  (s.uses.map fun r => Nat.size (st.regs r)).sum + (s.lUses.map fun L => listSize (st.lists L)).sum
    + s.csize + 1

/-! ## Helpers -/

theorem run_ite_snd (st : State R Q) (x : Fin R) (s t : Stmt R Q) :
    ((Stmt.ite x s t).run st).2
      = (if st.regs x ≠ 0 then (s.run st).2 else (t.run st).2) + Nat.size (st.regs x) + 1 := by
  simp only [Stmt.run]; split_ifs <;> rfl

theorem sum_le_filter {α : Type*} (l : List α) (f g : α → ℕ) (p : α → Bool) (c : ℕ)
    (h : ∀ a ∈ l, f a ≤ (if p a then g a else 0) + c) :
    (l.map f).sum ≤ ((l.filter p).map g).sum + l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h a (by simp)
    have ht := ih fun b hb => h b (by simp [hb])
    simp only [List.map_cons, List.sum_cons, List.filter_cons, List.length_cons]
    split_ifs at ha ⊢ with hp
    · simp only [List.map_cons, List.sum_cons]; nlinarith
    · nlinarith

theorem sum_le_add (l : List α) (f g : α → ℕ) (c : ℕ) (h : ∀ a ∈ l, f a ≤ g a + c) :
    (l.map f).sum ≤ (l.map g).sum + l.length * c := by
  have := sum_le_filter l f g (fun _ => true) c (by simpa using h)
  simpa using this

theorem listSize_append (a b : List ℕ) : listSize (a ++ b) = listSize a + listSize b := by
  simp [listSize]

theorem le_listSize_of_mem {l : List (Fin Q)} {L : Fin Q} (h : L ∈ l) (g : Fin Q → ℕ) :
    g L ≤ (l.map g).sum := List.le_sum_of_mem (List.mem_map_of_mem h)

/-! ## The bound -/

theorem loopFree_bound (s : Stmt R Q) (hs : s.loopFree = true) :
    ∀ st : State R Q,
      (s.run st).2 ≤ s.C * s.meas st ∧
      (∀ r, Nat.size ((s.run st).1.regs r) ≤ Nat.size (st.regs r) + s.C * s.meas st) ∧
      (∀ r ∈ s.mustW, Nat.size ((s.run st).1.regs r) ≤ s.C * s.meas st) ∧
      (∀ L, listSize ((s.run st).1.lists L) ≤ listSize (st.lists L) + s.C * s.meas st) := by
  induction s with
  | skip =>
    intro st
    refine ⟨?_, fun r => ?_, fun r hr => by simp [Stmt.mustW] at hr, fun L => ?_⟩ <;>
      simp [Stmt.run, Stmt.C, Stmt.meas, Stmt.uses, Stmt.lUses, Stmt.csize]
  | assign x e =>
    intro st
    have h1 := e.readSize_le st.regs
    have h2 := e.size_eval_le st.regs
    simp only [Stmt.meas, Stmt.uses, Stmt.lUses, Stmt.csize, Stmt.C, Stmt.mustW, List.map_nil,
      List.sum_nil, add_zero]
    refine ⟨?_, fun r => ?_, fun r hr => ?_, fun L => ?_⟩
    · show e.cost st.regs ≤ _; unfold Expr.cost; omega
    · rw [run_assign_fst]; simp only [setReg_regs, Function.update_apply]; split_ifs <;> omega
    · simp only [List.mem_singleton] at hr; subst hr
      rw [run_assign_fst]; simp only [setReg_regs, Function.update_self]; omega
    · rw [run_assign_fst]; simp
  | push L x =>
    intro st
    simp only [Stmt.meas, Stmt.uses, Stmt.lUses, Stmt.csize, Stmt.C, Stmt.mustW, List.map_nil,
      List.sum_nil, List.map_cons, List.sum_cons, add_zero]
    refine ⟨?_, fun r => ?_, fun r hr => by simp at hr, fun L' => ?_⟩
    · rw [run_push_snd]; omega
    · rw [run_push_fst]; simp
    · rw [run_push_fst]; simp only [setList_lists, Function.update_apply]
      split_ifs with h
      · subst h; simp [listSize]; omega
      · omega
  | pop L x flag =>
    intro st
    simp only [Stmt.meas, Stmt.uses, Stmt.lUses, Stmt.csize, Stmt.C, Stmt.mustW, List.map_nil,
      List.sum_nil, List.map_cons, List.sum_cons, add_zero, zero_add]
    rcases hl : st.lists L with _ | ⟨v, l⟩
    · rw [run_pop_nil_fst _ _ _ _ hl]
      refine ⟨by simp [Stmt.run, hl, listSize], fun r => ?_, fun r hr => ?_, fun L' => by simp⟩
      · simp only [setReg_regs, Function.update_apply]
        split_ifs <;> (try simp only [Nat.size_zero]) <;> omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [setReg_regs, Function.update_apply]
        split_ifs <;> (try simp only [Nat.size_zero]) <;> omega
    · rw [run_pop_cons_fst _ _ _ _ hl]
      have hv : Nat.size v + 1 ≤ listSize (v :: l) := by simp [listSize]
      have hl' : listSize l ≤ listSize (v :: l) := by simp [listSize]
      refine ⟨by simp only [Stmt.run, hl]; omega, fun r => ?_, fun r hr => ?_, fun L' => ?_⟩
      · simp only [setReg_regs, setList_regs, Function.update_apply]
        split_ifs <;> (try simp only [Nat.size_one]) <;> omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [setReg_regs, setList_regs, Function.update_apply]
        split_ifs <;> (try simp only [Nat.size_one]) <;> omega
      · simp only [setReg_lists, setList_lists, Function.update_apply]
        split_ifs with h
        · subst h; rw [hl] ; omega
        · omega
  | len L x =>
    intro st
    have h1 := length_le_listSize (st.lists L)
    have h2 := size_le_self (st.lists L).length
    simp only [Stmt.meas, Stmt.uses, Stmt.lUses, Stmt.csize, Stmt.C, Stmt.mustW, List.map_nil,
      List.sum_nil, List.map_cons, List.sum_cons, add_zero, zero_add]
    refine ⟨by rw [run_len_snd]; omega, fun r => ?_, fun r hr => ?_, fun L' => by simp [run_len_fst]⟩
    · rw [run_len_fst]; simp only [setReg_regs, Function.update_apply]; split_ifs <;> omega
    · simp only [List.mem_singleton] at hr; subst hr
      rw [run_len_fst]; simp only [setReg_regs, Function.update_self]; omega
  | rev L =>
    intro st
    simp only [Stmt.meas, Stmt.uses, Stmt.lUses, Stmt.csize, Stmt.C, Stmt.mustW, List.map_nil,
      List.sum_nil, List.map_cons, List.sum_cons, add_zero, zero_add]
    refine ⟨by rw [run_rev_snd]; omega, fun r => by simp [run_rev_fst], fun r hr => by simp at hr,
      fun L' => ?_⟩
    rw [run_rev_fst]; simp only [setList_lists, Function.update_apply]
    split_ifs with h
    · subst h; rw [listSize_reverse]; omega
    · omega
  | copy L L₂ =>
    intro st
    simp only [Stmt.meas, Stmt.uses, Stmt.lUses, Stmt.csize, Stmt.C, Stmt.mustW, List.map_nil,
      List.sum_nil, List.map_cons, List.sum_cons, add_zero, zero_add]
    refine ⟨by rw [run_copy_snd]; omega, fun r => by simp [run_copy_fst],
      fun r hr => by simp at hr, fun L' => ?_⟩
    rw [run_copy_fst]; simp only [setList_lists, Function.update_apply]
    split_ifs <;> omega
  | revApp L L₂ =>
    intro st
    simp only [Stmt.meas, Stmt.uses, Stmt.lUses, Stmt.csize, Stmt.C, Stmt.mustW, List.map_nil,
      List.sum_nil, List.map_cons, List.sum_cons, add_zero, zero_add]
    refine ⟨by rw [run_revApp_snd]; omega, fun r => by simp [run_revApp_fst],
      fun r hr => by simp at hr, fun L' => ?_⟩
    rw [run_revApp_fst]; simp only [setList_lists, Function.update_apply]
    split_ifs with h
    · subst h; rw [listSize_append, listSize_reverse]; omega
    · omega
  | loop x s _ => simp [Stmt.loopFree] at hs
  | seq s t ihs iht =>
    intro st
    simp only [Stmt.loopFree, Bool.and_eq_true] at hs
    obtain ⟨cs, rs, ms, ls⟩ := ihs hs.1 st
    obtain ⟨ct, rt, mt, lt⟩ := iht hs.2 (s.run st).1
    set st1 := (s.run st).1 with hst1
    set a := s.C
    set b := t.C
    set Ms := s.meas st
    set Mt := t.meas st1
    set Mq := (Stmt.seq s t).meas st
    have hMs : Ms ≤ Mq := by
      simp only [Ms, Mq, Stmt.meas, Stmt.uses, Stmt.lUses, Stmt.csize, List.map_append,
        List.sum_append]
      omega
    have hMt : Mt ≤ Mq + t.width * a * Ms := by
      have hU := sum_le_filter t.uses (fun r => Nat.size (st1.regs r))
        (fun r => Nat.size (st.regs r)) (fun r => decide (r ∉ s.mustW)) (a * Ms) (by
          intro r _
          by_cases hr : r ∈ s.mustW
          · simp only [hr, not_true_eq_false, decide_false]; simpa using ms r hr
          · simp only [hr, not_false_eq_true, decide_true, ite_true]; exact rs r)
      have hL := sum_le_add t.lUses (fun L => listSize (st1.lists L))
        (fun L => listSize (st.lists L)) (a * Ms) (fun L _ => ls L)
      have hq : ((t.uses.filter fun r => decide (r ∉ s.mustW)).map
          fun r => Nat.size (st.regs r)).sum + (t.lUses.map fun L => listSize (st.lists L)).sum
          + t.csize + 1 ≤ Mq := by
        simp only [Mq, Stmt.meas, Stmt.uses, Stmt.lUses, Stmt.csize, List.map_append,
          List.sum_append]
        omega
      have e : t.width * a * Ms = t.uses.length * (a * Ms) + t.lUses.length * (a * Ms) := by
        simp only [Stmt.width]; ring
      simp only [Mt, Stmt.meas]
      omega
    have hbMt : b * Mt ≤ b * Mq + b * (t.width * a * Mq) := by
      calc b * Mt ≤ b * (Mq + t.width * a * Ms) := Nat.mul_le_mul_left _ hMt
        _ = b * Mq + b * (t.width * a * Ms) := by ring
        _ ≤ b * Mq + b * (t.width * a * Mq) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hMs)) _
    have haMs : a * Ms ≤ a * Mq := Nat.mul_le_mul_left _ hMs
    have hC : (Stmt.seq s t).C * Mq = a * Mq + b * Mq + b * (t.width * a * Mq) + Mq := by
      simp only [Stmt.C, a, b]; ring
    have hpos : 1 ≤ Mq := by simp only [Mq, Stmt.meas]; omega
    rw [hC]
    refine ⟨?_, fun r => ?_, fun r hr => ?_, fun L => ?_⟩
    · rw [run_seq_snd, ← hst1]; omega
    · rw [run_seq_fst, ← hst1]; have := rs r; have := rt r; omega
    · rw [run_seq_fst, ← hst1]
      simp only [Stmt.mustW, List.mem_append] at hr
      rcases hr with hr | hr
      · have := ms r hr; have := rt r; omega
      · have := mt r hr; omega
    · rw [run_seq_fst, ← hst1]; have := ls L; have := lt L; omega
  | ite x s t ihs iht =>
    intro st
    simp only [Stmt.loopFree, Bool.and_eq_true] at hs
    obtain ⟨cs, rs, ms, ls⟩ := ihs hs.1 st
    obtain ⟨ct, rt, mt, lt⟩ := iht hs.2 st
    set Mq := (Stmt.ite x s t).meas st
    have hMs : s.meas st ≤ Mq := by
      simp only [Mq, Stmt.meas, Stmt.uses, Stmt.lUses, Stmt.csize, List.map_append,
        List.sum_append, List.map_cons, List.sum_cons]
      omega
    have hMt : t.meas st ≤ Mq := by
      simp only [Mq, Stmt.meas, Stmt.uses, Stmt.lUses, Stmt.csize, List.map_append,
        List.sum_append, List.map_cons, List.sum_cons]
      omega
    have hx : Nat.size (st.regs x) + 1 ≤ Mq := by
      simp only [Mq, Stmt.meas, Stmt.uses, List.map_cons, List.sum_cons]; omega
    have h1 : s.C * s.meas st ≤ s.C * Mq := Nat.mul_le_mul_left _ hMs
    have h2 : t.C * t.meas st ≤ t.C * Mq := Nat.mul_le_mul_left _ hMt
    have hC : (Stmt.ite x s t).C * Mq = s.C * Mq + t.C * Mq + Mq := by simp only [Stmt.C]; ring
    rw [hC]
    refine ⟨?_, fun r => ?_, fun r hr => ?_, fun L => ?_⟩
    · rw [run_ite_snd]; split_ifs <;> omega
    · rw [run_ite_fst]; split_ifs
      · have := rs r; omega
      · have := rt r; omega
    · simp only [Stmt.mustW, List.mem_filter, decide_eq_true_eq] at hr
      rw [run_ite_fst]; split_ifs
      · have := ms r hr.1; omega
      · have := mt r hr.2; omega
    · rw [run_ite_fst]; split_ifs
      · have := ls L; omega
      · have := lt L; omega

/-! ## Uniform bounds -/

theorem meas_le (s : Stmt R Q) (st : State R Q) (W : ℕ)
    (hr : ∀ r ∈ s.uses, Nat.size (st.regs r) ≤ W)
    (hl : ∀ L ∈ s.lUses, listSize (st.lists L) ≤ W) :
    s.meas st ≤ (s.width + s.csize + 1) * (W + 1) := by
  have h1 := sum_le_add s.uses (fun r => Nat.size (st.regs r)) (fun _ => 0) W
    (fun r hr' => by simpa using hr r hr')
  have h2 := sum_le_add s.lUses (fun L => listSize (st.lists L)) (fun _ => 0) W
    (fun L hl' => by simpa using hl L hl')
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_zero, zero_add,
    Nat.cast_id] at h1 h2
  simp only [Stmt.meas, Stmt.width]
  nlinarith

/-- **A loop-free statement under a uniform size bound** `W` on what it reads. -/
theorem loopFree_cost_le (s : Stmt R Q) (hs : s.loopFree = true) (st : State R Q) (W : ℕ)
    (hr : ∀ r ∈ s.uses, Nat.size (st.regs r) ≤ W)
    (hl : ∀ L ∈ s.lUses, listSize (st.lists L) ≤ W) :
    (s.run st).2 ≤ s.C * (s.width + s.csize + 1) * (W + 1) := by
  have := (loopFree_bound s hs st).1
  have hm := meas_le s st W hr hl
  calc (s.run st).2 ≤ s.C * s.meas st := this
    _ ≤ s.C * ((s.width + s.csize + 1) * (W + 1)) := Nat.mul_le_mul_left _ hm
    _ = _ := by ring

/-- Indexed loop cost. -/
theorem iterate_cost_idx (f : State R Q → State R Q × ℕ) (c B N : ℕ)
    (Inv : ℕ → State R Q → Prop)
    (hstep : ∀ j st, j < N → Inv j st → Inv (j + 1) (f st).1 ∧ (f st).2 ≤ B) :
    ∀ st, Inv 0 st → (iterate f c N st).2 ≤ N * (c + B) := by
  suffices h : ∀ k j st, j + k = N → Inv j st → (iterate f c k st).2 ≤ k * (c + B) by
    intro st h0; exact h N 0 st (by omega) h0
  intro k
  induction k with
  | zero => intro j st _ _; simp [iterate]
  | succ k ih =>
    intro j st hj h
    obtain ⟨h1, h2⟩ := hstep j st (by omega) h
    have h3 := ih (j + 1) (f st).1 (by omega) h1
    simp only [iterate]
    rw [Nat.succ_mul]
    omega

/-- **A counted loop with a loop-free body**: if, along an invariant, everything the body reads has
size at most `W`, and the count is at most `W`, the loop costs `O((W + 1)²)`. -/
theorem loop_cost_le (x : Fin R) (body : Stmt R Q) (hb : body.loopFree = true) (st₀ : State R Q)
    (W : ℕ) (Inv : ℕ → State R Q → Prop) (hN : st₀.regs x ≤ W)
    (hstep : ∀ j st, j < st₀.regs x → Inv j st → Inv (j + 1) (body.run st).1)
    (hr : ∀ j st, j < st₀.regs x → Inv j st → ∀ r ∈ body.uses, Nat.size (st.regs r) ≤ W)
    (hl : ∀ j st, j < st₀.regs x → Inv j st → ∀ L ∈ body.lUses, listSize (st.lists L) ≤ W)
    (h0 : Inv 0 st₀) :
    ((Stmt.loop x body).run st₀).2
      ≤ (body.C * (body.width + body.csize + 1) + 3) * (W + 1) ^ 2 := by
  set N := st₀.regs x
  set B := body.C * (body.width + body.csize + 1) * (W + 1)
  have hit := iterate_cost_idx body.run (Nat.size N + 1) B N Inv
    (fun j st hj h => ⟨hstep j st hj h, loopFree_cost_le body hb st W (hr j st hj h) (hl j st hj h)⟩)
    st₀ h0
  have hsN : Nat.size N ≤ W := (size_le_self N).trans hN
  rw [run_loop_snd]
  have h1 : N * (Nat.size N + 1 + B) ≤ W * (W + 1 + B) :=
    Nat.mul_le_mul hN (by omega)
  have hB : B = body.C * (body.width + body.csize + 1) * (W + 1) := rfl
  calc (iterate body.run (Nat.size N + 1) N st₀).2 + Nat.size N + 1
      ≤ W * (W + 1 + B) + W + 1 := by omega
    _ ≤ _ := by rw [hB]; nlinarith

end PCP.Lang
