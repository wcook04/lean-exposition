import PCP.Complexity.LangStep
import PCP.Complexity.NaturalListEncoding
import PCP.Complexity.BinaryCounter

/-!
# Materialized tapes and finite code for the structured language

Natural registers use little-endian bit tapes. List registers use the exact
separator-delimited encoding expected by COMPILE. The representation is injective
and its tape lengths are precisely the sizes charged by the language semantics.

Only finitely many substatements of a fixed program can occur in a reachable
continuation. Their explicit list provides finite control addresses; unbounded
loop counts and widths remain data and are not placed in finite machine control.
This file proves representation and reachability facts, not the compiler theorem.
-/

namespace PCP.Lang

open PCP.Machine

variable {R Q : ℕ}

/-- The two existing little-endian canonical encodings agree. -/
theorem binDigits_eq_bits (n : ℕ) : binDigits n = n.bits := by
  rw [binDigits, Nat.digits_two_eq_bits, List.map_map]
  have h : (fun b : Bool => (cond b 1 0 == 1)) = id := by
    funext b
    cases b <;> rfl
  simp only [Function.comp_def, h, List.map_id]

/-- A register is a materialized tape, without any separator. -/
def natTape (n : ℕ) : List Sym := ofBits (binDigits n)

/-- Decoding a natural's canonical bit word recovers that natural. -/
@[simp] theorem bitsValue_binDigits (n : ℕ) : bitsValue (binDigits n) = n := by
  rw [binDigits_eq_bits, bitsValue_bits]

theorem natTape_injective : Function.Injective natTape := by
  intro m n h
  apply binDigits_injective
  exact List.map_injective_iff.mpr (fun a b h => Sym.bit.inj h) h

/-- The charged bit size is exactly the register's physical tape length. -/
@[simp] theorem natTape_length (n : ℕ) : (natTape n).length = Nat.size n := by
  simp only [natTape, length_ofBits, binDigits, List.length_map]
  apply le_antisymm
  · exact (Nat.digits_length_le_iff (by norm_num) n).2 (Nat.lt_size_self n)
  · exact Nat.size_le.2 (Nat.lt_base_pow_length_digits (by norm_num))

/-- The list charge counts every physical bit and every separator. -/
@[simp] theorem listTape_length (xs : List ℕ) : (encodeNats xs).length = listSize xs := by
  rw [length_encodeNats, listSize]
  congr 1
  apply List.map_congr_left
  intro n hn
  have h := natTape_length n
  simpa only [natTape, length_ofBits] using congrArg (fun k => k + 1) h

/-- Static register indices are finite; each register owns a materialized symbol stack. -/
abbrev DataSlot (R Q : ℕ) := Fin R ⊕ Fin Q

/-- All language registers represented on separate fixed-index stacks. -/
def stateTapes (st : State R Q) : DataSlot R Q → List Sym
  | .inl r => natTape (st.regs r)
  | .inr l => encodeNats (st.lists l)

theorem stateTapes_injective : Function.Injective (stateTapes (R := R) (Q := Q)) := by
  intro a b h
  have hr : a.regs = b.regs := by
    funext r
    exact natTape_injective (congrFun h (.inl r))
  have hl : a.lists = b.lists := by
    funext l
    exact encodeNats_injective (congrFun h (.inr l))
  cases a
  cases b
  cases hr
  cases hl
  rfl

/-- The language's size invariant controls every physical data tape. -/
theorem stateTapes_length_le {st : State R Q} {B : ℕ} (h : st.Sized B)
    (i : DataSlot R Q) : (stateTapes st i).length ≤ B := by
  cases i with
  | inl r => exact (natTape_length _).trans_le (h.1 r)
  | inr l => exact (listTape_length _).trans_le (h.2 l)

/-- Total materialized data occupies at most the number of registers times the size bound. -/
theorem stateTapes_total_length_le {st : State R Q} {B : ℕ} (h : st.Sized B) :
    (∑ i : DataSlot R Q, (stateTapes st i).length) ≤ (R + Q) * B := by
  calc
    (∑ i : DataSlot R Q, (stateTapes st i).length) ≤ ∑ _i : DataSlot R Q, B :=
      Finset.sum_le_sum (fun i _ => stateTapes_length_le h i)
    _ = (R + Q) * B := by simp [DataSlot]

/-- Explicit finite syntax table, containing a node before its descendants. -/
def Stmt.nodes : Stmt R Q → List (Stmt R Q)
  | .seq s t => .seq s t :: (s.nodes ++ t.nodes)
  | .ite x s t => .ite x s t :: (s.nodes ++ t.nodes)
  | .loop x s => .loop x s :: s.nodes
  | s => [s]

@[simp] theorem Stmt.mem_nodes (s : Stmt R Q) : s ∈ s.nodes := by
  cases s <;> simp [nodes]

/-- Descendants of a listed code node remain in the same finite syntax table. -/
theorem Stmt.nodes_closed (s : Stmt R Q) :
    ∀ q ∈ s.nodes, q.nodes ⊆ s.nodes := by
  induction s with
  | seq s t ihs iht =>
      intro q h r hr
      simp only [nodes, List.mem_cons, List.mem_append] at h ⊢
      rcases h with rfl | h | h
      · simpa only [nodes, List.mem_cons, List.mem_append] using hr
      · exact Or.inr (Or.inl (ihs q h hr))
      · exact Or.inr (Or.inr (iht q h hr))
  | ite x s t ihs iht =>
      intro q h r hr
      simp only [nodes, List.mem_cons, List.mem_append] at h ⊢
      rcases h with rfl | h | h
      · simpa only [nodes, List.mem_cons, List.mem_append] using hr
      · exact Or.inr (Or.inl (ihs q h hr))
      · exact Or.inr (Or.inr (iht q h hr))
  | loop x s ih =>
      intro q h r hr
      simp only [nodes, List.mem_cons] at h ⊢
      rcases h with rfl | h
      · simpa only [nodes, List.mem_cons] using hr
      · exact Or.inr (ih q h hr)
  | _ => simp [nodes]

/-- The static code attached to an operational continuation frame. -/
def Frame.code : Frame R Q → Stmt R Q
  | .exec s => s
  | .repeat s _ _ => s

/-- A single control step only schedules substatements of the current code. -/
theorem Frame.next_code_mem (f : Frame R Q) (st : State R Q) :
    ∀ g ∈ (f.next st).1, g.code ∈ f.code.nodes := by
  cases f with
  | exec s =>
      cases s with
      | seq s t => simp [Frame.next, Frame.code, Stmt.nodes]
      | ite x s t =>
          by_cases h : st.regs x ≠ 0 <;>
            simp [Frame.next, Frame.code, Stmt.nodes, h]
      | loop x s =>
          cases h : st.regs x <;> simp [Frame.next, Frame.code, Stmt.nodes, h]
      | _ => simp [Frame.next]
  | «repeat» s n w => cases n <;> simp [Frame.next, Frame.code]

/-- All continuation code belongs to the fixed program's finite syntax table. -/
def Config.CodeSupported (P : Prog) (a : Config P.R P.Q) : Prop :=
  ∀ f ∈ a.todo, f.code ∈ P.body.nodes

theorem Config.step_codeSupported (P : Prog) {a b : Config P.R P.Q} {c : ℕ}
    (h : a.step = some (b, c)) (ha : a.CodeSupported P) : b.CodeSupported P := by
  cases a with
  | mk todo st =>
      cases todo with
      | nil => simp [Config.step] at h
      | cons f fs =>
          simp only [Config.step, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          intro g hg
          rcases List.mem_append.mp hg with hg | hg
          · exact P.body.nodes_closed f.code (ha f (by simp)) (f.next_code_mem st g hg)
          · exact ha g (List.mem_cons_of_mem _ hg)

theorem Steps.codeSupported (P : Prog) {a b : Config P.R P.Q} {n c : ℕ}
    (h : Steps a n c b) (ha : a.CodeSupported P) : b.CodeSupported P := by
  induction h with
  | refl => exact ha
  | cons h tail ih => exact ih (Config.step_codeSupported P h ha)

/-- Every operational prefix uses only the fixed program's finite code table. -/
theorem Prog.prefix_codeSupported (P : Prog) (xs : List ℕ) {n c : ℕ} {a : Config P.R P.Q}
    (h : Steps (P.start xs) n c a) : a.CodeSupported P := by
  apply h.codeSupported P
  simp [Config.CodeSupported, Prog.start, Frame.code]

/-- Every physical data stack in every prefix has the compiler's input-and-cost bound. -/
theorem Prog.prefix_tape_length_le (P : Prog) (xs : List ℕ) {n c : ℕ}
    {a : Config P.R P.Q} (h : Steps (P.start xs) n c a) (i : DataSlot P.R P.Q) :
    (stateTapes a.state i).length ≤ (encodeNats xs).length + P.cost xs := by
  simpa only [listTape_length] using stateTapes_length_le (P.prefix_bound xs h).2.2.1.1 i

end PCP.Lang
