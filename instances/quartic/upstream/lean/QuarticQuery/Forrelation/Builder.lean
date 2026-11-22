module

public import QuarticQuery.Statement

/-!
# Straight-line gate lists

A `Prog` is a list of gates whose wires are natural numbers, so no `Fin` bound is
carried while a circuit is built. A wire that points at or past its own gate reads
`false`, in `run` and in `Prog.toCircuit` alike, so the packaging into a `Circuit`
is total and needs no well-formedness hypothesis. `Ext` records that a builder step
only appended gates, and how many.
-/

@[expose] public section

namespace QuarticQuery.Forrelation

variable {ι : Type}

/-- A wire: constant false, an input bit, or an earlier gate. -/
abbrev Wire (ι : Type) := Option (ι ⊕ ℕ)

structure RawGate (ι : Type) where
  left : Wire ι
  right : Wire ι
  table : Bool → Bool → Bool

abbrev Prog (ι : Type) := List (RawGate ι)

def wireVal (x : BitInput ι) (vals : List Bool) : Wire ι → Bool
  | none => false
  | some (.inl i) => x i
  | some (.inr h) => vals.getD h false

def RawGate.value (g : RawGate ι) (x : BitInput ι) (vals : List Bool) : Bool :=
  g.table (wireVal x vals g.left) (wireVal x vals g.right)

/-- The gate values, in order. -/
def run (x : BitInput ι) (p : Prog ι) : List Bool :=
  p.foldl (fun vals g => vals ++ [g.value x vals]) []

theorem run_concat (x : BitInput ι) (p : Prog ι) (g : RawGate ι) :
    run x (p ++ [g]) = run x p ++ [g.value x (run x p)] := by
  simp [run, List.foldl_append]

@[simp] theorem run_nil (x : BitInput ι) : run x ([] : Prog ι) = [] := rfl

@[simp] theorem length_run (x : BitInput ι) (p : Prog ι) : (run x p).length = p.length := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p g ih => simp [run_concat, ih]

theorem run_append (x : BitInput ι) (p q : Prog ι) : ∃ r, run x (p ++ q) = run x p ++ r := by
  induction q using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton q g ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨r ++ [g.value x (run x (p ++ q))], ?_⟩
    rw [← List.append_assoc, run_concat, hr, List.append_assoc]

/-- A wire is usable once the gates it names exist. -/
def Wire.Valid (n : ℕ) : Wire ι → Prop
  | some (.inr h) => h < n
  | _ => True

theorem Wire.Valid.mono {n n' : ℕ} {w : Wire ι} (hn : n ≤ n') (h : w.Valid n) : w.Valid n' := by
  rcases w with _ | i | h'
  · trivial
  · trivial
  · exact lt_of_lt_of_le h hn

/-- The value of a wire after running `p`. -/
def val (x : BitInput ι) (p : Prog ι) (w : Wire ι) : Bool := wireVal x (run x p) w

/-- `p'` is `p` followed by exactly `c` more gates. -/
def Ext (p p' : Prog ι) (c : ℕ) : Prop := ∃ q : Prog ι, p' = p ++ q ∧ q.length = c

theorem Ext.refl (p : Prog ι) : Ext p p 0 := ⟨[], by simp, rfl⟩

theorem Ext.trans {p q r : Prog ι} {a b : ℕ} (h : Ext p q a) (h' : Ext q r b) :
    Ext p r (a + b) := by
  obtain ⟨u, rfl, rfl⟩ := h
  obtain ⟨v, rfl, rfl⟩ := h'
  exact ⟨u ++ v, by simp, by simp⟩

theorem Ext.length_eq {p p' : Prog ι} {c : ℕ} (h : Ext p p' c) :
    p'.length = p.length + c := by
  obtain ⟨q, rfl, rfl⟩ := h
  simp

theorem Ext.valid {p p' : Prog ι} {c : ℕ} {w : Wire ι} (h : Ext p p' c)
    (hw : w.Valid p.length) : w.Valid p'.length :=
  hw.mono (by rw [h.length_eq]; omega)

theorem Ext.val_eq {p p' : Prog ι} {c : ℕ} {w : Wire ι} (h : Ext p p' c)
    (hw : w.Valid p.length) (x : BitInput ι) : val x p' w = val x p w := by
  obtain ⟨q, rfl, -⟩ := h
  obtain ⟨r, hr⟩ := run_append x p q
  rcases w with _ | i | g
  · rfl
  · rfl
  · have hg : g < (run x p).length := by
      rw [length_run]
      exact hw
    simp only [val, wireVal, hr]
    rw [List.getD_eq_getElem _ _ hg,
      List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
      List.getElem_append_left hg]

/-- `w` carries the Boolean function `f` of the input after `p`. -/
def Rep (p : Prog ι) (w : Wire ι) (f : BitInput ι → Bool) : Prop :=
  w.Valid p.length ∧ ∀ x, val x p w = f x

theorem Rep.mono {p p' : Prog ι} {c : ℕ} {w : Wire ι} {f : BitInput ι → Bool}
    (h : Rep p w f) (e : Ext p p' c) : Rep p' w f :=
  ⟨e.valid h.1, fun x => by rw [e.val_eq h.1, h.2]⟩

/-- Append one gate and return its wire. -/
def gate (a b : Wire ι) (t : Bool → Bool → Bool) (p : Prog ι) : Wire ι × Prog ι :=
  (some (.inr p.length), p ++ [⟨a, b, t⟩])

theorem gate_spec {p : Prog ι} {a b : Wire ι} {f g : BitInput ι → Bool}
    (ha : Rep p a f) (hb : Rep p b g) (t : Bool → Bool → Bool) :
    ∃ w p', gate a b t p = (w, p') ∧ Ext p p' 1 ∧ Rep p' w fun x => t (f x) (g x) := by
  refine ⟨_, _, rfl, ⟨[_], rfl, rfl⟩, ?_, fun x => ?_⟩
  · simp [Wire.Valid]
  · simp only [val, wireVal, run_concat]
    have h1 := ha.2 x
    have h2 := hb.2 x
    simp only [val] at h1 h2
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp [RawGate.value, h1, h2]

theorem rep_none (p : Prog ι) : Rep p none fun _ => false := ⟨trivial, fun _ => rfl⟩

theorem rep_input (p : Prog ι) (i : ι) : Rep p (some (.inl i)) fun x => x i :=
  ⟨trivial, fun _ => rfl⟩

/-! ## Packaging -/

/-- Keep a wire only if it points strictly before gate `g`. -/
def narrow (g : ℕ) : Wire ι → Option (ι ⊕ Fin g)
  | none => none
  | some (.inl i) => some (.inl i)
  | some (.inr h) => if hh : h < g then some (.inr ⟨h, hh⟩) else none

/-- The `Circuit` of a gate list with two chosen output gates. -/
def Prog.toCircuit (p : Prog ι) (d b : Fin p.length) : Circuit ι where
  size := p.length
  gate g := ⟨narrow g p[g].left, narrow g p[g].right, p[g].table⟩
  domainOut := d
  valueOut := b

theorem run_take (x : BitInput ι) (p : Prog ι) (g : ℕ) (hg : g ≤ p.length) :
    run x (p.take g) = (run x p).take g := by
  obtain ⟨r, hr⟩ := run_append x (p.take g) (p.drop g)
  rw [List.take_append_drop] at hr
  have hl : (run x (p.take g)).length = g := by simp [hg]
  rw [hr, List.take_left' hl]

theorem getD_run (x : BitInput ι) (p : Prog ι) (g : ℕ) (hg : g < p.length) :
    (run x p).getD g false = p[g].value x ((run x p).take g) := by
  have e : p = p.take g ++ [p[g]] ++ p.drop (g + 1) := by simp
  obtain ⟨r, hr⟩ := run_append x (p.take g ++ [p[g]]) (p.drop (g + 1))
  rw [← e, run_concat, run_take x p g hg.le] at hr
  rw [hr, ← run_take x p g hg.le]
  have hl : (run x (p.take g)).length = g := by simp [hg.le]
  rw [List.getD_eq_getElem _ _ (by simp [hl])]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [List.getElem_append_right (by omega)]
  simp [hl]

theorem wireVal_take (x : BitInput ι) (vals : List Bool) (g : ℕ) (w : Wire ι) :
    wireVal x (vals.take g) w =
      match narrow g w with
      | none => false
      | some (.inl i) => x i
      | some (.inr h) => vals.getD h.val false := by
  rcases w with _ | i | h
  · rfl
  · rfl
  · simp only [wireVal, narrow]
    by_cases hh : h < g <;> simp [hh, List.getD_eq_getElem?_getD]

/-- The honest transcript. -/
def honest (p : Prog ι) (d b : Fin p.length) (x : BitInput ι) :
    Fin (p.toCircuit d b).size → Bool :=
  fun g => (run x p).getD g.val false

theorem pred_eq (p : Prog ι) (d b : Fin p.length) (x : BitInput ι)
    (tr : Fin (p.toCircuit d b).size → Bool) (g : Fin (p.toCircuit d b).size)
    (w : Wire ι) (htr : ∀ h : Fin (p.toCircuit d b).size, h.val < g.val →
      tr h = (run x p).getD h.val false) :
    predecessorValue (p.toCircuit d b) x tr g (narrow g.val w) =
      wireVal x ((run x p).take g.val) w := by
  rw [wireVal_take]
  rcases hn : narrow g.val w with _ | i | h
  · rfl
  · rfl
  · exact htr ⟨h.val, lt_trans h.isLt g.isLt⟩ h.isLt

theorem honest_consistent (p : Prog ι) (d b : Fin p.length) (x : BitInput ι) :
    GateConsistent (p.toCircuit d b) x (honest p d b x) := by
  intro g
  have hg : g.val < p.length := g.isLt
  change (run x p).getD g.val false = p[g.val].table
    (predecessorValue (p.toCircuit d b) x (honest p d b x) g (narrow g.val p[g.val].left))
    (predecessorValue (p.toCircuit d b) x (honest p d b x) g (narrow g.val p[g.val].right))
  rw [pred_eq p d b x (honest p d b x) g _ fun _ _ => rfl,
    pred_eq p d b x (honest p d b x) g _ fun _ _ => rfl, getD_run x p g hg]
  rfl

theorem consistent_unique (p : Prog ι) (d b : Fin p.length) (x : BitInput ι)
    (tr : Fin (p.toCircuit d b).size → Bool) (h : GateConsistent (p.toCircuit d b) x tr)
    (g : Fin (p.toCircuit d b).size) : tr g = (run x p).getD g.val false := by
  induction hn : g.val using Nat.strong_induction_on generalizing g with
  | _ n ih =>
    subst hn
    have hg : g.val < p.length := g.isLt
    rw [h g, getD_run x p g hg]
    change p[g.val].table
      (predecessorValue (p.toCircuit d b) x tr g (narrow g.val p[g.val].left))
      (predecessorValue (p.toCircuit d b) x tr g (narrow g.val p[g.val].right)) = _
    rw [pred_eq p d b x tr g _ fun k hk => ih k.val hk k rfl,
      pred_eq p d b x tr g _ fun k hk => ih k.val hk k rfl]
    rfl

/-- Ledger: lem-2.1.iii. A gate list whose two output gates decide `f` packages
into a `Circuit` realising `f`. -/
theorem realises_of_run (p : Prog ι) (d b : Fin p.length) (f : PartialBool ι)
    (hd : ∀ x, (run x p).getD d.val false = true ↔ promised f x)
    (hb : ∀ x, (run x p).getD d.val false = true →
      f x = some ((run x p).getD b.val false)) :
    CircuitRealises (p.toCircuit d b) f where
  exists_transcript x := ⟨_, honest_consistent p d b x⟩
  correct x tr htr := by
    have e1 := consistent_unique p d b x tr htr
    constructor
    · rw [e1]
      exact hd x
    · rw [e1, e1]
      exact hb x

end QuarticQuery.Forrelation
