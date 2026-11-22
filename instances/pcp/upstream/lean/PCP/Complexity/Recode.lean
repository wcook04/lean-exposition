import PCP.Complexity.Support

/-!
# Recoding a machine over finite alphabets

`PCP/Complexity/Support.lean` shows a machine uses only finitely many symbols per stack. This module
recodes over those finite alphabets and proves the recoding changes nothing observable.

## Why the support is a parameter

The translation is parameterised by a `SupportData` — **any** finite family containing `Supported`
— rather than by `Supported` itself. The reason is the alphabet interface: packaging a recoded
witness needs equivalences for the *whole* external input and output alphabets, and a support that
omits a symbol of a finite external alphabet cannot supply one. Enlarging at those stacks is then a
different `SupportData`, not a second translator.

`SupportData.ofSupported` is the default instance; `Supported` itself is already an
over-approximation of what runs actually use, and nothing here needs it to be tight.

## Status

C1-C4 are complete: the support parameter, the recoded alphabet, the decoding API with its dependent
update identity, the statement translator and its commuting square, the bundled machine, the trace
lifting, and transport of execution certificates in both directions.

3D is complete too: `SupportData.enlargeOutput` raises the support at the output stack to the whole
alphabet when that alphabet is finite, `inputAlphabetEquiv`/`outputAlphabetEquiv` rebuild the
**external** equivalences from it, and `recodeWitness` repackages a polynomial-time witness with the
same encoders, function, polynomial and per-certificate step counts.

What this module does **not** do is certify an executable compiler: the finite enumeration is
classical, so `recodedTM` and `recodeWitness` are `noncomputable`. The computability bridge is
separate work and begins in `PCP/Complexity/BoundedEval.lean` and `PCP/Complexity/Codec.lean`.
-/

namespace PCP.Machine

open Turing Turing.TM2

attribute [local instance] Turing.FinTM2.kDecidableEq Turing.FinTM2.kFin
  Turing.FinTM2.ΛFin Turing.FinTM2.σFin Turing.FinTM2.Γk₀Fin

/-! ## C1: the support parameter -/

/-- A finite family of symbols per stack, containing everything the machine can use.

`covers` is what makes the translation possible at all: it supplies membership for every input
symbol and for every push the program performs. Any larger finite family works equally well, which
is what lets an output stack be enlarged to its whole alphabet later. -/
structure SupportData (tm : FinTM2) where
  /-- Which symbols are kept at each stack. -/
  mem : ∀ k, tm.Γ k → Prop
  /-- Finitely many at each stack — the point of the exercise. -/
  finite : ∀ k, {c | mem k c}.Finite
  /-- At least everything the machine can use. -/
  covers : ∀ k c, Supported tm k c → mem k c

/-- The default instance: the support proved finite in `PCP/Complexity/Support.lean`. -/
def SupportData.ofSupported (tm : FinTM2) : SupportData tm where
  mem k c := Supported tm k c
  finite := supported_finite tm
  covers _ _ h := h

variable {tm : FinTM2} (A : SupportData tm)

/-- The recoded alphabet at stack `k`: the kept symbols, carrying their membership proofs. -/
def RecodedΓ (k : tm.K) : Type := {c : tm.Γ k // A.mem k c}

noncomputable instance (k : tm.K) : Fintype (RecodedΓ A k) := by
  classical
  exact (A.finite k).fintype

/-- An unused stack may have empty support; that is fine, and no default symbol is needed. -/
example (k : tm.K) (h : ∀ c, ¬ A.mem k c) : IsEmpty (RecodedΓ A k) :=
  ⟨fun c => h c.1 c.2⟩

/-! ## C2: decoding

Decoding forgets the membership proofs. Everything below is proved *before* any statement is
translated, so the translation proof can use it as an API. -/

/-- Forget the membership proofs on every stack. -/
def decodeStacks (S : ∀ k, List (RecodedΓ A k)) : ∀ k, List (tm.Γ k) :=
  fun k => (S k).map Subtype.val

/-- Deliberately **not** `@[simp]`: unfolding `decodeStacks` first would destroy the patterns that
`decodeStacks_tail` and `decodeStacks_head?` match on. -/
theorem decodeStacks_apply (S : ∀ k, List (RecodedΓ A k)) (k : tm.K) :
    decodeStacks A S k = (S k).map Subtype.val := rfl

/-- **The dependent update identity.**  Updating a stack and then decoding is decoding and then
updating — with the same `DecidableEq tm.K` on both sides, which is the machine's own field. -/
theorem decodeStacks_update (S : ∀ k, List (RecodedΓ A k)) (k : tm.K)
    (xs : List (RecodedΓ A k)) :
    decodeStacks A (Function.update S k xs)
      = Function.update (decodeStacks A S) k (xs.map Subtype.val) := by
  funext j
  by_cases h : j = k
  · subst h
    simp [decodeStacks, Function.update_self]
  · simp [decodeStacks, Function.update_of_ne h]

theorem decodeStacks_nil (S : ∀ k, List (RecodedΓ A k)) (k : tm.K) (h : S k = []) :
    decodeStacks A S k = [] := by rw [decodeStacks_apply, h]; rfl

/-- Decoding commutes with `tail`. -/
@[simp] theorem decodeStacks_tail (S : ∀ k, List (RecodedΓ A k)) (k : tm.K) :
    (decodeStacks A S k).tail = ((S k).tail).map Subtype.val := by
  rw [decodeStacks_apply]
  cases h : S k with
  | nil => rfl
  | cons a l => rfl

/-- Decoding commutes with `head?`, through `Option.map`.  An empty stack stays empty; no default
symbol is invented. -/
@[simp] theorem decodeStacks_head? (S : ∀ k, List (RecodedΓ A k)) (k : tm.K) :
    (decodeStacks A S k).head? = ((S k).head?).map Subtype.val := by
  rw [decodeStacks_apply]
  cases h : S k with
  | nil => rfl
  | cons a l => rfl

theorem decodeStacks_length (S : ∀ k, List (RecodedΓ A k)) (k : tm.K) :
    (decodeStacks A S k).length = (S k).length := by
  rw [decodeStacks_apply]
  exact List.length_map _

theorem decodeStacks_injective : Function.Injective (decodeStacks A) := by
  intro S T h
  funext k
  have hk : (S k).map Subtype.val = (T k).map Subtype.val := congrFun h k
  exact (List.map_injective_iff.mpr Subtype.val_injective) hk

/-- Decoding a configuration: keep the label and internal state, decode the stacks. -/
def decodeCfg (c : Cfg (RecodedΓ A) tm.Λ tm.σ) : tm.Cfg :=
  ⟨c.l, c.var, decodeStacks A c.stk⟩

@[simp] theorem decodeCfg_l (c : Cfg (RecodedΓ A) tm.Λ tm.σ) : (decodeCfg A c).l = c.l := rfl

@[simp] theorem decodeCfg_var (c : Cfg (RecodedΓ A) tm.Λ tm.σ) :
    (decodeCfg A c).var = c.var := rfl

@[simp] theorem decodeCfg_stk (c : Cfg (RecodedΓ A) tm.Λ tm.σ) :
    (decodeCfg A c).stk = decodeStacks A c.stk := rfl

theorem decodeCfg_injective : Function.Injective (decodeCfg A) := by
  intro c₁ c₂ h
  have hl : c₁.l = c₂.l := congrArg (fun c : tm.Cfg => c.l) h
  have hv : c₁.var = c₂.var := congrArg (fun c : tm.Cfg => c.var) h
  have hstk : c₁.stk = c₂.stk :=
    decodeStacks_injective A (congrArg (fun c : tm.Cfg => c.stk) h)
  cases c₁ with | mk l₁ v₁ S₁ =>
  cases c₂ with | mk l₂ v₂ S₂ =>
  subst hl; subst hv; subst hstk; rfl

/-! ## C3: translating statements

The translator takes a statement together with a proof that *its* pushes are kept. Continuation
proofs come from the collector's own constructors, so no cast appears: this is the payoff for
making `Pushes` an inductive relation in `PCP/Complexity/Support.lean`.

A push carries its membership proof into the subtype. A peek or pop hands the original state-update
function the **decoded** optional symbol, which is why `decodeStacks_head?` had to be proved first.
Loads, branch conditions and `goto` destinations are unchanged. -/

/-- Translate a statement to the recoded alphabets. -/
def recodeStmt : ∀ (q : Stmt tm.Γ tm.Λ tm.σ), (∀ k c, Pushes q k c → A.mem k c) →
    Stmt (RecodedΓ A) tm.Λ tm.σ
  | .push k f q, h =>
      .push k (fun v => ⟨f v, h k (f v) (Pushes.here f q v)⟩)
        (recodeStmt q fun j c hc => h j c (Pushes.push f hc))
  | .peek k f q, h =>
      .peek k (fun v o => f v (o.map Subtype.val))
        (recodeStmt q fun j c hc => h j c (Pushes.peek f hc))
  | .pop k f q, h =>
      .pop k (fun v o => f v (o.map Subtype.val))
        (recodeStmt q fun j c hc => h j c (Pushes.pop f hc))
  | .load a q, h => .load a (recodeStmt q fun j c hc => h j c (Pushes.load a hc))
  | .branch f q₁ q₂, h =>
      .branch f (recodeStmt q₁ fun j c hc => h j c (Pushes.branchL f hc))
        (recodeStmt q₂ fun j c hc => h j c (Pushes.branchR f hc))
  | .goto f, _ => .goto f
  | .halt, _ => .halt

/-- **The statement-level commuting square.**  Executing the translated statement on recoded stacks
and then decoding is the same as decoding first and executing the original.

Holds for *arbitrary* recoded stacks and *arbitrary* internal states — no restriction to reachable
ones, which is what lets it lift to whole traces. -/
theorem decodeCfg_stepAux : ∀ (q : Stmt tm.Γ tm.Λ tm.σ) (h : ∀ k c, Pushes q k c → A.mem k c)
    (v : tm.σ) (S : ∀ k, List (RecodedΓ A k)),
    decodeCfg A (stepAux (recodeStmt A q h) v S) = stepAux q v (decodeStacks A S)
  | .push k f q, h, v, S => by
      have ih := decodeCfg_stepAux q (fun j c hc => h j c (Pushes.push f hc)) v
        (Function.update S k (⟨f v, h k (f v) (Pushes.here f q v)⟩ :: S k))
      simp only [recodeStmt, stepAux]
      rw [ih, decodeStacks_update]
      -- what remains is `List.map Subtype.val (⟨f v, _⟩ :: S k) = f v :: decodeStacks A S k`,
      -- which is definitional; `List.map_cons` cannot be *rewritten* with because `Subtype.val`
      -- runs out of the def `RecodedΓ A k`.
      rfl
  | .peek k f q, h, v, S => by
      have ih := decodeCfg_stepAux q (fun j c hc => h j c (Pushes.peek f hc))
        (f v (((S k).head?).map Subtype.val)) S
      simp only [recodeStmt, stepAux, decodeStacks_head?]
      exact ih
  | .pop k f q, h, v, S => by
      have ih := decodeCfg_stepAux q (fun j c hc => h j c (Pushes.pop f hc))
        (f v (((S k).head?).map Subtype.val)) (Function.update S k (S k).tail)
      simp only [recodeStmt, stepAux, decodeStacks_head?, decodeStacks_tail]
      rw [ih, decodeStacks_update]
  | .load a q, h, v, S => by
      have ih := decodeCfg_stepAux q (fun j c hc => h j c (Pushes.load a hc)) (a v) S
      simp only [recodeStmt, stepAux]
      exact ih
  | .branch f q₁ q₂, h, v, S => by
      cases hf : f v with
      | false =>
          have ih := decodeCfg_stepAux q₂ (fun j c hc => h j c (Pushes.branchR f hc)) v S
          simp only [recodeStmt, stepAux, hf, Bool.cond_false]
          exact ih
      | true =>
          have ih := decodeCfg_stepAux q₁ (fun j c hc => h j c (Pushes.branchL f hc)) v S
          simp only [recodeStmt, stepAux, hf, Bool.cond_true]
          exact ih
  | .goto f, _, v, S => rfl
  | .halt, _, v, S => rfl

/-! ## C4: the bundled machine, traces, and execution certificates -/

/-- The recoded machine.  Everything except the alphabets is copied verbatim — stack indices,
labels, internal states, the input and output indices, and the original instance fields, so that
dependent updates stay aligned.

`noncomputable` because the alphabet `Fintype` comes from a classical finiteness proof. That is
consistent with a *semantic* translation; nothing here claims an executable compiler. -/
noncomputable def recodedTM : FinTM2 where
  K := tm.K
  kDecidableEq := tm.kDecidableEq
  kFin := tm.kFin
  k₀ := tm.k₀
  k₁ := tm.k₁
  Γ := RecodedΓ A
  Λ := tm.Λ
  main := tm.main
  ΛFin := tm.ΛFin
  σ := tm.σ
  initialState := tm.initialState
  σFin := tm.σFin
  Γk₀Fin := inferInstance
  m l := recodeStmt A (tm.m l) fun k c hp => A.covers k c (Supported.pushed hp)

@[simp] theorem recodedTM_k₀ : (recodedTM A).k₀ = tm.k₀ := rfl
@[simp] theorem recodedTM_k₁ : (recodedTM A).k₁ = tm.k₁ := rfl
@[simp] theorem recodedTM_main : (recodedTM A).main = tm.main := rfl
@[simp] theorem recodedTM_initialState : (recodedTM A).initialState = tm.initialState := rfl

/-- The recoded machine keeps the original's decidable equality on stack indices.  Normalising with
this is what lets the two `dite`s in the endpoint proofs be split together. -/
@[simp] theorem recodedTM_kDecidableEq : (recodedTM A).kDecidableEq = tm.kDecidableEq := rfl

/-- **The machine-step square.**  Both levels of optionality are kept apart: a configuration whose
label is `none` still carries its stacks, whereas an outer `none` carries no configuration at all.
-/
theorem decodeCfg_step (c : (recodedTM A).Cfg) :
    Option.map (decodeCfg A) ((recodedTM A).step c) = tm.step (decodeCfg A c) := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => rfl
  | some l =>
      show some (decodeCfg A (stepAux ((recodedTM A).m l) v S))
        = some (stepAux (tm.m l) v (decodeStacks A S))
      exact congrArg some (decodeCfg_stepAux A (tm.m l) _ v S)

/-- Decoding semiconjugates the two optional transition functions. -/
theorem semiconj_decode :
    Function.Semiconj (Option.map (decodeCfg A))
      (flip Bind.bind (recodedTM A).step) (flip Bind.bind tm.step) := by
  intro x
  cases x with
  | none => rfl
  | some c => exact decodeCfg_step A c

/-- **Trace lifting.**  One application of `Function.Semiconj.iterate_right`; the step count is
carried through unchanged, which is what the certificate transport below needs. -/
theorem decode_iterate (n : ℕ) (x : Option (recodedTM A).Cfg) :
    Option.map (decodeCfg A) ((flip Bind.bind (recodedTM A).step)^[n] x)
      = (flip Bind.bind tm.step)^[n] (Option.map (decodeCfg A) x) :=
  (semiconj_decode A).iterate_right n x

/-! ### Endpoints -/

/-- Mapping commutes with the `dite` that `initList` and `haltList` use for their stacks.

The two branches are taken as **opaque parameters** `a` and `b`. That is the point: in the endpoint
goals the two `dite`s carry different instance terms *and* spell their transport differently
(`Eq.mpr` on one side, `▸` on the other), so no rewrite acts on both. Abstracting the branches makes
`dif_pos`/`dif_neg` first-order, and the caller discharges the branch relation by `subst`. -/
theorem map_dite_gen {J : Type} [DecidableEq J] {Γ₁ Γ₂ : J → Type} (j j₀ : J)
    (f : Γ₁ j → Γ₂ j) (a : j = j₀ → List (Γ₁ j)) (b : j = j₀ → List (Γ₂ j))
    (hab : ∀ h, List.map f (a h) = b h) :
    List.map f (dite (j = j₀) a (fun _ => [])) = dite (j = j₀) b (fun _ => []) := by
  by_cases h : j = j₀
  · rw [dite_eq_left h, dite_eq_left h]; exact hab h
  · rw [dite_eq_right h, dite_eq_right h]; rfl

theorem decodeCfg_initList (s : List (RecodedΓ A tm.k₀)) :
    decodeCfg A (initList (recodedTM A) s) = initList tm (s.map Subtype.val) := by
  unfold decodeCfg initList
  congr 1
  funext k
  simp only [decodeStacks]
  refine map_dite_gen (Γ₁ := RecodedΓ A) (Γ₂ := tm.Γ) k tm.k₀ Subtype.val _ _ (fun h => ?_)
  subst h
  rfl

theorem decodeCfg_haltList (o : List (RecodedΓ A tm.k₁)) :
    decodeCfg A (haltList (recodedTM A) o) = haltList tm (o.map Subtype.val) := by
  unfold decodeCfg haltList
  congr 1
  funext k
  simp only [decodeStacks]
  refine map_dite_gen (Γ₁ := RecodedΓ A) (Γ₂ := tm.Γ) k tm.k₁ Subtype.val _ _ (fun h => ?_)
  subst h
  rfl

/-! ### Lifting an input list

Every raw input symbol is supported at `k₀`, so input lists lift totally. Output lists do **not**:
an arbitrary symbol of an infinite output alphabet has no reason to be supported, which is why the
output direction goes through `reachable_stackSupported` instead. -/

/-- Every input symbol is kept, so the input alphabet lifts totally. -/
def liftInput (c : tm.Γ tm.k₀) : RecodedΓ A tm.k₀ := ⟨c, A.covers _ c (Supported.input c)⟩

@[simp] theorem map_liftInput : ∀ s : List (tm.Γ tm.k₀),
    (s.map (liftInput A)).map Subtype.val = s
  | [] => rfl
  | c :: s => by
      show Subtype.val (liftInput A c) :: (s.map (liftInput A)).map Subtype.val = c :: s
      rw [map_liftInput s]
      rfl

/-! ### Transporting execution certificates

`TM2OutputsInTime` is *data*, not a proposition: it records a step count. Both directions below copy
that count verbatim rather than asserting that some new bound exists. -/

/-- A recoded execution decodes to an original one, with the same step count. -/
def outputsInTime_decode {s : List (RecodedΓ A tm.k₀)} {o : List (RecodedΓ A tm.k₁)} {m : ℕ}
    (h : TM2OutputsInTime (recodedTM A) s (some o) m) :
    TM2OutputsInTime tm (s.map Subtype.val) (some (o.map Subtype.val)) m where
  steps := h.steps
  evals_in_steps := by
    -- `Option.map f (some x) = some (f x)` holds definitionally, so the endpoint lemmas can be
    -- lifted with `congrArg some` and no `Option.map` simp set is needed.
    have h1 : Option.map (decodeCfg A) (some (initList (recodedTM A) s))
        = some (initList tm (s.map Subtype.val)) := congrArg some (decodeCfg_initList A s)
    have h2 : Option.map (decodeCfg A) (Option.map (haltList (recodedTM A)) (some o))
        = Option.map (haltList tm) (some (o.map Subtype.val)) :=
      congrArg some (decodeCfg_haltList A o)
    -- `rw` cannot act here: the two `Option.map` terms print identically but their implicit type
    -- argument is `(recodedTM A).Cfg` on one side and `Cfg (RecodedΓ A) tm.Λ tm.σ` on the other.
    -- A `calc` elaborates every step in one place, so no matching is needed.
    calc (flip Bind.bind tm.step)^[h.steps] (some (initList tm (s.map Subtype.val)))
        = (flip Bind.bind tm.step)^[h.steps]
            (Option.map (decodeCfg A) (some (initList (recodedTM A) s))) := by rw [h1]
      _ = Option.map (decodeCfg A)
            ((flip Bind.bind (recodedTM A).step)^[h.steps] (some (initList (recodedTM A) s))) :=
          (decode_iterate A h.steps _).symm
      _ = Option.map (decodeCfg A) (Option.map (haltList (recodedTM A)) (some o)) :=
          congrArg _ h.evals_in_steps
      _ = Option.map (haltList tm) (some (o.map Subtype.val)) := h2
  steps_le_m := h.steps_le_m

/-- An original execution lifts to a recoded one, with the same step count.

The output list must already be recoded; `outputsInTime_recode` below removes that requirement by
obtaining the membership proofs from the support theorem. -/
def outputsInTime_encode {s : List (RecodedΓ A tm.k₀)} {o : List (RecodedΓ A tm.k₁)} {m : ℕ}
    (h : TM2OutputsInTime tm (s.map Subtype.val) (some (o.map Subtype.val)) m) :
    TM2OutputsInTime (recodedTM A) s (some o) m where
  steps := h.steps
  evals_in_steps := by
    have h1 : Option.map (decodeCfg A) (some (initList (recodedTM A) s))
        = some (initList tm (s.map Subtype.val)) := congrArg some (decodeCfg_initList A s)
    have h2 : Option.map (decodeCfg A) (some (haltList (recodedTM A) o))
        = some (haltList tm (o.map Subtype.val)) := congrArg some (decodeCfg_haltList A o)
    have hgoal : Option.map (decodeCfg A)
        ((flip Bind.bind (recodedTM A).step)^[h.steps] (some (initList (recodedTM A) s)))
        = Option.map (decodeCfg A) (some (haltList (recodedTM A) o)) :=
      calc Option.map (decodeCfg A)
            ((flip Bind.bind (recodedTM A).step)^[h.steps] (some (initList (recodedTM A) s)))
          = (flip Bind.bind tm.step)^[h.steps]
              (Option.map (decodeCfg A) (some (initList (recodedTM A) s))) :=
            decode_iterate A h.steps _
        _ = (flip Bind.bind tm.step)^[h.steps] (some (initList tm (s.map Subtype.val))) := by
            rw [h1]
        _ = some (haltList tm (o.map Subtype.val)) := h.evals_in_steps
        _ = Option.map (decodeCfg A) (some (haltList (recodedTM A) o)) := h2.symm
    exact Option.map_injective (decodeCfg_injective A) hgoal
  steps_le_m := h.steps_le_m

/-! ### The transports preserve the step count

The definitions above copy `steps` verbatim, but a consumer should not have to unfold them to see
it. `RecodedOutput` records only the budget `m`, so the count fact is exported here rather than
built into the type. -/

@[simp] theorem outputsInTime_decode_steps {s : List (RecodedΓ A tm.k₀)}
    {o : List (RecodedΓ A tm.k₁)} {m : ℕ} (h : TM2OutputsInTime (recodedTM A) s (some o) m) :
    (outputsInTime_decode A h).steps = h.steps := rfl

@[simp] theorem outputsInTime_encode_steps {s : List (RecodedΓ A tm.k₀)}
    {o : List (RecodedΓ A tm.k₁)} {m : ℕ}
    (h : TM2OutputsInTime tm (s.map Subtype.val) (some (o.map Subtype.val)) m) :
    (outputsInTime_encode A h).steps = h.steps := rfl

/-! ### Lifting an arbitrary successful output

An arbitrary original output list has no reason to lift: its symbols need not be kept, and if the
original output alphabet is infinite no total inverse into the finite support can exist. But a
*successful execution's* output is another matter — every symbol on its final stack is reachable,
hence supported, hence kept. `reachable_stackSupported` supplies exactly that. -/

/-- `dif_pos` with the branch abstracted, so the rewrite is first-order.  See `map_dite_gen`. -/
theorem dite_pos_eq {P : Prop} [Decidable P] {α : Type} (hp : P) (a : P → α) (b : ¬P → α)
    (x : α) (hax : a hp = x) : dite P a b = x := by rw [dite_eq_left hp]; exact hax

/-- The negative companion to `dite_pos_eq`. -/
theorem dite_neg_eq {P : Prop} [Decidable P] {α : Type} (hp : ¬P) (a : P → α) (b : ¬P → α)
    (x : α) (hbx : b hp = x) : dite P a b = x := by rw [dite_eq_right hp]; exact hbx

theorem haltList_stk_k₁ (tm : FinTM2) (o : List (tm.Γ tm.k₁)) :
    (haltList tm o).stk tm.k₁ = o := by
  unfold haltList
  exact dite_pos_eq rfl _ _ o rfl

/-- Attach membership proofs to a list whose symbols are all kept. -/
def liftSupportedList {k : tm.K} :
    ∀ (o : List (tm.Γ k)), (∀ c ∈ o, A.mem k c) → List (RecodedΓ A k)
  | [], _ => []
  | c :: o, h =>
      ⟨c, h c List.mem_cons_self⟩ ::
        liftSupportedList o fun d hd => h d (List.mem_cons_of_mem _ hd)

@[simp] theorem map_liftSupportedList {k : tm.K} :
    ∀ (o : List (tm.Γ k)) (h : ∀ c ∈ o, A.mem k c),
      (liftSupportedList A o h).map Subtype.val = o
  | [], _ => rfl
  | c :: o, h => by
      show c :: (liftSupportedList A o _).map Subtype.val = c :: o
      rw [map_liftSupportedList o]

/-- What `outputsInTime_recode` returns: a recoded output, a proof it decodes to the original, and
the transported certificate.  A structure rather than a conjunction because `TM2OutputsInTime` is
*data* — it records a step count — not a proposition. -/
structure RecodedOutput (A : SupportData tm) (s : List (tm.Γ tm.k₀)) (o : List (tm.Γ tm.k₁))
    (m : ℕ) where
  /-- The output, over the recoded alphabet. -/
  out : List (RecodedΓ A tm.k₁)
  /-- It decodes to the original output. -/
  decodes : out.map Subtype.val = o
  /-- The transported certificate, with the original's step count. -/
  cert : TM2OutputsInTime (recodedTM A) (s.map (liftInput A)) (some out) m

/-- **Raw-machine preservation.**  Any successful original execution lifts to a recoded one with the
**same step count** and an output that decodes back to the original.

This is the useful theorem even when the original output alphabet is infinite: it needs no
full-alphabet equivalence, only that the output actually produced is reachable. -/
def outputsInTime_recode {s : List (tm.Γ tm.k₀)} {o : List (tm.Γ tm.k₁)} {m : ℕ}
    (h : TM2OutputsInTime tm s (some o) m) : RecodedOutput A s o m := by
  classical
  -- every symbol of the output is on a reachable configuration's stack, hence supported
  have hsupp : StackSupported tm (haltList tm o).stk :=
    reachable_stackSupported tm s h.steps (haltList tm o) h.evals_in_steps
  have hmem : ∀ c ∈ o, A.mem tm.k₁ c := by
    intro c hc
    exact A.covers _ c (hsupp tm.k₁ c (by rw [haltList_stk_k₁]; exact hc))
  refine ⟨liftSupportedList A o hmem, map_liftSupportedList A o hmem, ?_⟩
  -- Build the intermediate certificate field-by-field with `steps := h.steps`, rather than
  -- transporting `h` wholesale across the two list equalities. Transporting it would hide the step
  -- count behind an `Eq.mpr`, and `outputsInTime_recode_steps` below would stop being `rfl`.
  refine outputsInTime_encode A
    { steps := h.steps, steps_le_m := h.steps_le_m, evals_in_steps := ?_ }
  have e1 : (s.map (liftInput A)).map Subtype.val = s := map_liftInput A s
  have e2 : (liftSupportedList A o hmem).map Subtype.val = o := map_liftSupportedList A o hmem
  calc (flip Bind.bind tm.step)^[h.steps]
        (some (initList tm ((s.map (liftInput A)).map Subtype.val)))
      = (flip Bind.bind tm.step)^[h.steps] (some (initList tm s)) := by rw [e1]
    _ = Option.map (haltList tm) (some o) := h.evals_in_steps
    _ = Option.map (haltList tm)
          (some ((liftSupportedList A o hmem).map Subtype.val)) := by rw [e2]

/-- The lifted certificate runs for exactly as many steps as the original.  The equality transports
used to build the intermediate hypothesis leave the step field untouched. -/
@[simp] theorem outputsInTime_recode_steps {s : List (tm.Γ tm.k₀)} {o : List (tm.Γ tm.k₁)} {m : ℕ}
    (h : TM2OutputsInTime tm s (some o) m) :
    (outputsInTime_recode A h).cert.steps = h.steps := rfl

/-! ## 3D: preserving the external alphabet interface

`TM2ComputableAux` needs equivalences for the **whole** external input and output alphabets. The
input side is free — every input symbol is supported. The output side is not: a support that keeps
only the symbols actually emitted cannot be equivalent to a larger finite alphabet.

The fix is to enlarge the support at `k₁` to that stack's entire alphabet, which is exactly what
`SupportData` was parameterised for. -/

/-- Enlarge a support so the output stack keeps its whole alphabet.

`k = tm.k₁` is a disjunct on the *index*, not on the symbol, so nothing is transported between
alphabet types. When `k₀ = k₁` this adds nothing, because the input stack already keeps
everything. -/
def SupportData.enlargeOutput (A : SupportData tm)
    (hout : (Set.univ : Set (tm.Γ tm.k₁)).Finite) : SupportData tm where
  mem k c := A.mem k c ∨ k = tm.k₁
  finite k := by
    by_cases h : k = tm.k₁
    · subst h
      exact Set.Finite.subset hout (Set.subset_univ _)
    · have hset : {c | A.mem k c ∨ k = tm.k₁} = {c | A.mem k c} := by
        ext c; simp [h]
      rw [hset]
      exact A.finite k
  covers k c hc := Or.inl (A.covers k c hc)

/-- Every output symbol is kept by the enlarged support. -/
theorem enlargeOutput_mem_k₁ (A : SupportData tm) (hout : (Set.univ : Set (tm.Γ tm.k₁)).Finite)
    (c : tm.Γ tm.k₁) : (A.enlargeOutput hout).mem tm.k₁ c := Or.inr rfl

/-! ### The alphabet equivalences

Forward is subtype inclusion; backward attaches the universal membership proof. These are genuine
equivalences, not inclusions — which is the whole point of the enlargement. -/

/-- The input stack's recoded alphabet is equivalent to the original: every input symbol is kept. -/
def inputAlphabetEquiv (A : SupportData tm) : RecodedΓ A tm.k₀ ≃ tm.Γ tm.k₀ where
  toFun := Subtype.val
  invFun := liftInput A
  left_inv _ := rfl
  right_inv _ := rfl

/-- After enlargement, the output stack's recoded alphabet is equivalent to the original. -/
def outputAlphabetEquiv (A : SupportData tm) (hout : (Set.univ : Set (tm.Γ tm.k₁)).Finite) :
    RecodedΓ (A.enlargeOutput hout) tm.k₁ ≃ tm.Γ tm.k₁ where
  toFun := Subtype.val
  invFun c := ⟨c, enlargeOutput_mem_k₁ A hout c⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem inputAlphabetEquiv_symm_val (A : SupportData tm) (c : tm.Γ tm.k₀) :
    ((inputAlphabetEquiv A).symm c).val = c := rfl

@[simp] theorem outputAlphabetEquiv_symm_val (A : SupportData tm)
    (hout : (Set.univ : Set (tm.Γ tm.k₁)).Finite) (c : tm.Γ tm.k₁) :
    ((outputAlphabetEquiv A hout).symm c).val = c := rfl

/-- Decoding the lifted input list returns it unchanged — for **every** list, not only those
arising from some particular execution. -/
@[simp] theorem map_inputAlphabetEquiv_symm (A : SupportData tm) :
    ∀ l : List (tm.Γ tm.k₀), (l.map (inputAlphabetEquiv A).symm).map Subtype.val = l
  | [] => rfl
  | c :: l => by
      show c :: (l.map (inputAlphabetEquiv A).symm).map Subtype.val = c :: l
      rw [map_inputAlphabetEquiv_symm A l]

/-- Likewise on the output side, for every list over the whole external alphabet. -/
@[simp] theorem map_outputAlphabetEquiv_symm (A : SupportData tm)
    (hout : (Set.univ : Set (tm.Γ tm.k₁)).Finite) :
    ∀ l : List (tm.Γ tm.k₁), (l.map (outputAlphabetEquiv A hout).symm).map Subtype.val = l
  | [] => rfl
  | c :: l => by
      show c :: (l.map (outputAlphabetEquiv A hout).symm).map Subtype.val = c :: l
      rw [map_outputAlphabetEquiv_symm A hout l]

/-! ### D3: repackaging a polynomial-time witness

The wrapper returns a witness for the **same** encoders, the **same** function and the **same** time
polynomial, whose underlying machine has finite alphabets at every stack. The external encoded input
length is untouched, so the polynomial is still evaluated at the same quantity, and C4 preserves the
step count, so no growth or copying charge arises.

This remains a *semantic* translation over classical finite enumeration. It does not discharge the
computability bridge (NP-1b, NP-1c) and certifies no executable compiler. -/

/-- **The wrapper.**  Recode a witness over finite alphabets, keeping its external interface.

`houtFin` is the external output alphabet's finiteness; this cannot be dispensed with in
general, since a raw `FinTM2` guarantees finiteness only at the input stack. -/
noncomputable def recodeWitness {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f : α → β} (h : TM2ComputableInPolyTime ea eb f)
    (hout : (Set.univ : Set (h.tm.Γ h.tm.k₁)).Finite) :
    TM2ComputableInPolyTime ea eb f :=
  let A := (SupportData.ofSupported h.tm).enlargeOutput hout
  { tm := recodedTM A
    inputAlphabet := (inputAlphabetEquiv A).trans h.inputAlphabet
    outputAlphabet := (outputAlphabetEquiv (SupportData.ofSupported h.tm) hout).trans
      h.outputAlphabet
    time := h.time
    outputsFun := fun a => by
      refine outputsInTime_encode A
        { steps := (h.outputsFun a).steps, steps_le_m := (h.outputsFun a).steps_le_m,
          evals_in_steps := ?_ }
      have e1 : ((ea a).map ((inputAlphabetEquiv A).trans h.inputAlphabet).invFun).map Subtype.val
          = (ea a).map h.inputAlphabet.invFun := by
        simpa using map_inputAlphabetEquiv_symm A ((ea a).map h.inputAlphabet.invFun)
      have e2 : ((eb (f a)).map
            ((outputAlphabetEquiv (SupportData.ofSupported h.tm) hout).trans
              h.outputAlphabet).invFun).map Subtype.val
          = (eb (f a)).map h.outputAlphabet.invFun := by
        simpa using map_outputAlphabetEquiv_symm (SupportData.ofSupported h.tm) hout
          ((eb (f a)).map h.outputAlphabet.invFun)
      calc (flip Bind.bind h.tm.step)^[(h.outputsFun a).steps]
            (some (initList h.tm
              (((ea a).map ((inputAlphabetEquiv A).trans h.inputAlphabet).invFun).map
                Subtype.val)))
          = (flip Bind.bind h.tm.step)^[(h.outputsFun a).steps]
              (some (initList h.tm ((ea a).map h.inputAlphabet.invFun))) := by rw [e1]
        _ = Option.map (haltList h.tm) (some ((eb (f a)).map h.outputAlphabet.invFun)) :=
            (h.outputsFun a).evals_in_steps
        _ = Option.map (haltList h.tm) (some (((eb (f a)).map
              ((outputAlphabetEquiv (SupportData.ofSupported h.tm) hout).trans
                h.outputAlphabet).invFun).map Subtype.val)) := by rw [e2] }

@[simp] theorem recodeWitness_time {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f : α → β} (h : TM2ComputableInPolyTime ea eb f)
    (hout : (Set.univ : Set (h.tm.Γ h.tm.k₁)).Finite) :
    (recodeWitness h hout).time = h.time := rfl

/-- The **returned witness's** machine has a finite alphabet at every stack — not just the input
stack, which is all `FinTM2` itself guarantees.

Stated about `(recodeWitness h hout).tm.Γ k` rather than about the subtype the implementation
happens to use: the latter would keep holding if the wrapper were changed to return something else.
-/
theorem recodeWitness_alphabets_finite {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f : α → β} (h : TM2ComputableInPolyTime ea eb f)
    (hout : (Set.univ : Set (h.tm.Γ h.tm.k₁)).Finite) (k : (recodeWitness h hout).tm.K) :
    Finite ((recodeWitness h hout).tm.Γ k) :=
  Set.Finite.to_subtype (((SupportData.ofSupported h.tm).enlargeOutput hout).finite k)

/-- Each `outputsFun` certificate of the returned witness runs for exactly as many steps as the
original's.  Also stated about the returned witness. -/
@[simp] theorem recodeWitness_steps {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f : α → β} (h : TM2ComputableInPolyTime ea eb f)
    (hout : (Set.univ : Set (h.tm.Γ h.tm.k₁)).Finite) (a : α) :
    ((recodeWitness h hout).outputsFun a).steps = (h.outputsFun a).steps := rfl

end PCP.Machine
