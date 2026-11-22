import PCP.Complexity.BinaryDivisionCore
import PCP.Complexity.BinaryZipSurvey
import PCP.Complexity.InPlaceReverseTransducer
import PCP.Complexity.RelocatedBlock

/-!
# A concrete binary division and modulo machine

The dividend is reversed once. Each high-to-low bit updates an on-tape remainder,
compares it with the retained divisor, and conditionally runs actual subtraction
and normalization scans. Quotient bits are materialized as they are determined.
-/

namespace PCP.Machine.BinaryDivision

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition PCP.Lang FiniteBlocks
open PreservingBinaryZip (Slot)

inductive FrameSlot | source | bits | quotient
  deriving DecidableEq, Inhabited, Repr
instance : Fintype FrameSlot where
  elems := {.source, .bits, .quotient}
  complete := by intro x; cases x <;> decide

inductive Callee | compare | subtract | normalize
  deriving DecidableEq, Inhabited, Repr
instance : Fintype Callee where
  elems := {.compare, .subtract, .normalize}
  complete := by intro x; cases x <;> decide

inductive Node | reverse | scan | compared | normalize
  deriving DecidableEq, Inhabited, Repr
instance : Fintype Node where
  elems := {.reverse, .scan, .compared, .normalize}
  complete := by intro x; cases x <;> decide

variable (F : Type) [DecidableEq F] [Fintype F]

abbrev Frame := FrameSlot ⊕ F
abbrev Tapes := Slot ⊕ Frame F
abbrev comparisonSpec := BinaryComparison.spec (fun _ => false)

abbrev survey : Block (Tapes F) (fun _ => Sym) where
  Label := MovePhase
  Control := Ordering × Option Sym × Option Sym
  entry := .one
  initial := (.eq, none, none)
  code := (BinaryZipSurvey.machine comparisonSpec (Frame F)).m

abbrev subtractor : Block (Tapes F) (fun _ => Sym) where
  Label := MovePhase
  Control := Bool × Option Sym × Option Sym
  entry := .one
  initial := (false, none, none)
  code := (PreservingBinaryZip.machine subSpec (Frame F)).m

/-- A static, executable permutation puts the normalizer on right/result. -/
def normalizePositions : Bool ⊕ (Bool ⊕ Frame F) ≃ Tapes F where
  toFun := fun
    | .inl false => .inl .right
    | .inl true => .inl .result
    | .inr (.inl false) => .inl .left
    | .inr (.inl true) => .inl .save
    | .inr (.inr j) => .inr j
  invFun := fun
    | .inl .left => .inr (.inl false)
    | .inl .right => .inl false
    | .inl .save => .inr (.inl true)
    | .inl .result => .inl true
    | .inr j => .inr (.inr j)
  left_inv := by rintro ((_ | _) | ((_ | _) | j)) <;> rfl
  right_inv := by rintro ((_ | _ | _ | _) | j) <;> rfl

abbrev normalizer : Block (Tapes F) (fun _ => Sym) :=
  relocatedBlock (InPlaceReverseTransducer.machine BinaryNormalize.spec (Bool ⊕ Frame F))
    (normalizePositions F) (fun _ => Equiv.refl Sym)

abbrev blocks : Callee → Block (Tapes F) (fun _ => Sym)
  | .compare => survey F
  | .subtract => subtractor F
  | .normalize => normalizer F

abbrev Label := Labels (blocks F) (L := Node)
abbrev Control := Controls (blocks F) × (Option Sym × Bool)

/-- Only the comparison return carries noninitial callee control. -/
def states (order : Ordering) : Controls (blocks F)
  | .compare => (order, none, none)
  | .subtract => (false, none, none)
  | .normalize => (BinaryNormalize.spec.init, none, false)

abbrev initial : Control F := (states F .eq, none, false)

def returns : Callee → Node
  | .compare => .compared
  | .subtract => .normalize
  | .normalize => .scan

/-- Dividing by zero still scans every bit into the remainder and leaves quotient zero. -/
def beginCompare : Stmt (fun _ : Tapes F => Sym) (Label F) (Control F) :=
  .peek (.inl .left) (fun v o => (v.1, v.2.1, o.isSome)) <|
    .branch (fun v => v.2.2)
      (.load (fun _ => initial F) (.goto (fun _ => .inl ⟨.compare, .one⟩)))
      (.load (fun _ => initial F) (.goto (fun _ => .inr .scan)))

/-- Four caller nodes connect three genuine finite machine blocks. -/
def caller : Node → Stmt (fun _ : Tapes F => Sym) (Label F) (Control F)
  | .reverse =>
      .pop (.inr (.inl .source)) (fun v o => (v.1, o, false)) <|
        .branch (fun v => v.2.1.isNone)
          (.load (fun _ => initial F) (.goto (fun _ => .inr .scan)))
          (.push (.inr (.inl .bits)) (fun v => v.2.1.getD .sep)
            (.load (fun _ => initial F) (.goto (fun _ => .inr .reverse))))
  | .scan =>
      .pop (.inr (.inl .bits)) (fun v o => (v.1, o, false)) <|
        .branch (fun v => v.2.1.isNone)
          (.load (fun _ => initial F) .halt)
          (.branch (fun v => v.2.1 = some (.bit true))
            (.push (.inl .right) (fun _ => .bit true) (beginCompare F))
            (.peek (.inl .right) (fun v o => (v.1, v.2.1, o.isSome))
              (.branch (fun v => v.2.2)
                (.push (.inl .right) (fun _ => .bit false) (beginCompare F)) (beginCompare F))))
  | .compared =>
      .branch (fun v => (v.1 .compare).1 != .gt)
        (.push (.inr (.inl .quotient)) (fun _ => .bit true)
          (.load (fun _ => initial F) (.goto (fun _ => .inl ⟨.subtract, .one⟩))))
        (.peek (.inr (.inl .quotient)) (fun v o => (v.1, none, o.isSome))
          (.branch (fun v => v.2.2)
            (.push (.inr (.inl .quotient)) (fun _ => .bit false)
              (.load (fun _ => initial F) (.goto (fun _ => .inr .scan))))
            (.load (fun _ => initial F) (.goto (fun _ => .inr .scan)))))
  | .normalize => .load (fun _ => initial F) (.goto (fun _ => .inl ⟨.normalize, .one⟩))

abbrev machine : FinTM2 :=
  FiniteBlocks.machine (blocks F) (.inr (.inl .source)) (.inr (.inl .quotient))
    .reverse (none, false) returns (caller F)

def frame (source bits quotient : List Sym) (S : F → List Sym) : Frame F → List Sym
  | .inl .source => source
  | .inl .bits => bits
  | .inl .quotient => quotient
  | .inr j => S j

/-- Boundary tapes have empty arithmetic scratch, and optionally a returned comparison. -/
def cfg (l : Option (Label F)) (left right source bits quotient : List Sym)
    (S : F → List Sym) (order : Ordering := .eq) : (machine F).Cfg :=
  ⟨l, (states F order, none, false), fun k => match k with
    | .inl .left => left
    | .inl .right => right
    | .inl .save => []
    | .inl .result => []
    | .inr j => frame F source bits quotient S j⟩

variable {F}

/-- The comparison block restores both operands and returns their exact ordering. -/
theorem comparison_trace (d r : ℕ) (source bits quotient : List Sym) (S : F → List Sym) :
    (flip Bind.bind (machine F).step)^[comparisonTime d r]
      (some (cfg F (some (.inl ⟨.compare, .one⟩))
        (natTape d) (natTape r) source bits quotient S)) =
      some (cfg F (some (.inr .compared)) (natTape d) (natTape r) source bits quotient S
        (BinaryComparison.compareValue d r .eq)) := by
  have h := BinaryZipSurvey.trace (spec := comparisonSpec)
    (natTape d) (natTape r) .eq (frame F source bits quotient S)
  simp only [BinaryZipSurvey.comparison_natTape, natTape_length] at h
  have hi := FiniteBlocks.iterate_embedCfg (blocks F) (.inr (.inl .source))
    (.inr (.inl .quotient)) .reverse (none, false) returns (caller F) .compare
    (states F .eq) (none, false) (comparisonTime d r) h
  have hc (l : Option MovePhase) (o : Ordering) (x y : List Sym) :
      FiniteBlocks.embedCfg (blocks F) returns .compare (states F .eq) (none, false)
        (BinaryZipSurvey.cfg comparisonSpec (Frame F) l o x y [] []
          (frame F source bits quotient S)) =
      cfg F (some (l.elim (.inr .compared) (fun k => .inl ⟨.compare, k⟩)))
        x y source bits quotient S o := by
    have hu : Function.update (states F .eq) Callee.compare (o, none, none) = states F o := by
      funext i
      cases i <;> simp only [Function.update, states] <;> rfl
    cases l <;>
      dsimp only [FiniteBlocks.embedCfg, BinaryZipSurvey.cfg, cfg, returns, Option.elim]
    all_goals
      rw [hu]
      congr 1
      funext k
      rcases k with (_ | _ | _ | _) | j <;> rfl
  simp only [hc, Option.elim] at hi
  dsimp only [FinTM2.Cfg, machine, FiniteBlocks.machine] at hi ⊢
  exact hi

/-- Raw subtraction is an actual retained-divisor scan, before canonical normalization. -/
theorem subtraction_trace (d r : ℕ) (source bits quotient : List Sym) (S : F → List Sym) :
    (flip Bind.bind (machine F).step)^[subtractionTime d r]
      (some (cfg F (some (.inl ⟨.subtract, .one⟩))
        (natTape d) (natTape r) source bits quotient S)) =
      some (cfg F (some (.inr .normalize)) (natTape d) (raw d r) source bits quotient S) := by
  have h := PreservingBinaryZip.trace (spec := subSpec)
    (natTape d) (natTape r) (frame F source bits quotient S)
  simp only [natTape_length] at h
  have hi := FiniteBlocks.iterate_embedCfg (blocks F) (.inr (.inl .source))
    (.inr (.inl .quotient)) .reverse (none, false) returns (caller F) .subtract
    (states F .eq) (none, false) (subtractionTime d r) h
  have hc (l : Option MovePhase) (x y : List Sym) :
      FiniteBlocks.embedCfg (blocks F) returns .subtract (states F .eq) (none, false)
        (PreservingBinaryZip.cfg subSpec (Frame F) l false x y [] []
          (frame F source bits quotient S)) =
      cfg F (some (l.elim (.inr .normalize) (fun k => .inl ⟨.subtract, k⟩)))
        x y source bits quotient S := by
    cases l <;>
      dsimp only [FiniteBlocks.embedCfg, PreservingBinaryZip.cfg, cfg, returns, Option.elim]
    all_goals
      simp only [show ((false, none, none) : (blocks F Callee.subtract).Control) =
        states F .eq .subtract from rfl, Function.update_eq_self]
      congr 1
      funext k
      rcases k with (_ | _ | _ | _) | j <;> rfl
  simp only [hc, Option.elim] at hi
  dsimp only [FinTM2.Cfg, machine, FiniteBlocks.machine] at hi ⊢
  exact hi

/-- Private layout frame for in-place normalization, with retained divisor and spare scratch. -/
def normalizeFrame (left save : List Sym) (rest : Frame F → List Sym) :
    Bool ⊕ Frame F → List Sym
  | .inl false => left
  | .inl true => save
  | .inr j => rest j

/-- Relocated normalization returns the exact canonical truncated difference. -/
theorem normalization_trace (d r : ℕ) (source bits quotient : List Sym) (S : F → List Sym) :
    (flip Bind.bind (machine F).step)^[normalizationTime d r]
      (some (cfg F (some (.inl ⟨.normalize, .one⟩))
        (natTape d) (raw d r) source bits quotient S)) =
      some (cfg F (some (.inr .scan)) (natTape d) (natTape (r - d)) source bits quotient S) := by
  let nf := normalizeFrame (natTape d) [] (frame F source bits quotient S)
  have h := InPlaceReverseTransducer.trace (spec := BinaryNormalize.spec) (raw d r) nf
  have hr := iterate_relocatedBlock
    (InPlaceReverseTransducer.machine BinaryNormalize.spec (Bool ⊕ Frame F))
    (normalizePositions F) (fun _ => Equiv.refl Sym)
    (.inr (.inl .source)) (.inr (.inl .quotient)) (normalizationTime d r) h
  have hi := FiniteBlocks.iterate_embedCfg (blocks F) (.inr (.inl .source))
    (.inr (.inl .quotient)) .reverse (none, false) returns (caller F) .normalize
    (states F .eq) (none, false) (normalizationTime d r) hr
  have hc (l : Option MovePhase) (xs : List Sym) :
      FiniteBlocks.embedCfg (blocks F) returns .normalize (states F .eq) (none, false)
        (relocateCfg (InPlaceReverseTransducer.machine BinaryNormalize.spec (Bool ⊕ Frame F))
          (normalizePositions F) (fun _ => Equiv.refl Sym)
          (InPlaceReverseTransducer.cfg BinaryNormalize.spec (Bool ⊕ Frame F)
            l BinaryNormalize.spec.init xs [] nf)) =
      cfg F (some (l.elim (.inr .scan) (fun k => .inl ⟨.normalize, k⟩)))
        (natTape d) xs source bits quotient S := by
    cases l <;>
      dsimp only [FiniteBlocks.embedCfg, relocateCfg, InPlaceReverseTransducer.cfg,
        cfg, returns, Option.elim]
    all_goals
      simp only [show ((BinaryNormalize.spec.init, none, false) :
        (blocks F Callee.normalize).Control) = states F .eq .normalize from rfl,
        Function.update_eq_self]
      congr 1
      funext k
      rcases k with (_ | _ | _ | _) | j <;>
        (change List.map id _ = _; simp only [List.map_id]; rfl)
  simp only [hc, Option.elim] at hi
  have hout : (BinaryNormalize.spec.output BinaryNormalize.spec.init (raw d r).reverse).reverse =
      natTape (r - d) := subSpec_normalized d r
  rw [hout] at hi
  dsimp only [FinTM2.Cfg, machine, FiniteBlocks.machine] at hi ⊢
  exact hi

/-- Static reset states agree with each block's stored initial finite control. -/
lemma states_initial (i : Callee) : (blocks F i).initial = states F .eq i := by
  cases i <;> rfl

lemma update_initial (i : Callee) :
    Function.update (states F .eq) i (blocks F i).initial = states F .eq := by
  rw [states_initial]
  exact Function.update_eq_self _ _

/-- Canonical binary shift-and-append avoids representing zero by a padded word. -/
def bitTape (b : Bool) : List Sym → List Sym
  | [] => if b then [.bit true] else []
  | c :: cs => .bit b :: c :: cs

theorem bitTape_natTape (b : Bool) (r : ℕ) : bitTape b (natTape r) = natTape (Nat.bit b r) := by
  by_cases hr : r = 0
  · subst r; cases b <;> rfl
  · have ht : natTape r ≠ [] := fun h => hr (natTape_injective h)
    have he : bitTape b (natTape r) = .bit b :: natTape r := by
      cases h : natTape r with
      | nil => exact False.elim (ht h)
      | cons c cs => rfl
    rw [he]
    simp only [natTape, binDigits_eq_bits, Nat.bits_append_bit r b (by omega),
      ofBits, List.map_cons]

/-- Input reversal consumes precisely one source cell per counted step. -/
theorem step_reverse_cons (c : Sym) (left right source bits quotient : List Sym)
    (S : F → List Sym) :
    (machine F).step
      (cfg F (some (.inr .reverse)) left right (c :: source) bits quotient S) =
      some (cfg F (some (.inr .reverse)) left right source (c :: bits) quotient S) := by
  dsimp only [machine, FiniteBlocks.machine, FinTM2.step, TM2.step, caller, cfg,
    TM2.stepAux, frame, initial]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr .reverse), (states F .eq, none, false), T⟩ : (machine F).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _ | _) | (j | k)
  all_goals first | cases j <;> simp [Function.update] | simp [Function.update]

theorem step_reverse_nil (left right bits quotient : List Sym) (S : F → List Sym) :
    (machine F).step (cfg F (some (.inr .reverse)) left right [] bits quotient S) =
      some (cfg F (some (.inr .scan)) left right [] bits quotient S) := by
  dsimp only [machine, FiniteBlocks.machine, FinTM2.step, TM2.step, caller, cfg,
    TM2.stepAux, frame, initial]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr .scan), (states F .eq, none, false), T⟩ : (machine F).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _ | _) | (j | k)
  all_goals first | cases j <;> simp [Function.update] | simp [Function.update]

theorem step_scan_nil (left right source quotient : List Sym) (S : F → List Sym) :
    (machine F).step (cfg F (some (.inr .scan)) left right source [] quotient S) =
      some (cfg F none left right source [] quotient S) := by
  dsimp only [machine, FiniteBlocks.machine, FinTM2.step, TM2.step, caller, cfg,
    TM2.stepAux, frame, initial]
  refine congrArg some (congrArg (fun T =>
    (⟨none, (states F .eq, none, false), T⟩ : (machine F).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _ | _) | (j | k)
  all_goals first | cases j <;> simp [Function.update] | simp [Function.update]

/-- Processing one dividend bit shifts the remainder and dispatches the finite survey. -/
theorem step_scan (b : Bool) (left right source bits quotient : List Sym) (S : F → List Sym) :
    (machine F).step
      (cfg F (some (.inr .scan)) left right source (.bit b :: bits) quotient S) =
      some (cfg F (some (if left = [] then .inr .scan else .inl ⟨.compare, .one⟩))
        left (bitTape b right) source bits quotient S) := by
  cases left <;> cases right <;> cases b <;>
    dsimp only [machine, FiniteBlocks.machine, FinTM2.step, TM2.step, caller, cfg,
      TM2.stepAux, frame, initial, beginCompare, bitTape, enter]
  all_goals
    refine congrArg some (congrArg (fun T =>
      (⟨_, (states F .eq, none, false), T⟩ : (machine F).Cfg)) ?_)
    funext k
    rcases k with (_ | _ | _ | _) | (j | k)
    all_goals first | cases j <;> simp [Function.update] | simp [Function.update]

/-- A divisor no larger than the shifted remainder emits a set quotient bit and subtracts. -/
theorem step_compared_le (o : Ordering) (h : o ≠ .gt)
    (left right source bits quotient : List Sym) (S : F → List Sym) :
    (machine F).step (cfg F (some (.inr .compared)) left right source bits quotient S o) =
      some (cfg F (some (.inl ⟨.subtract, .one⟩)) left right source bits
        (.bit true :: quotient) S) := by
  cases o with
  | gt => exact False.elim (h rfl)
  | lt =>
      dsimp only [machine, FiniteBlocks.machine, FinTM2.step, TM2.step, caller, cfg,
        TM2.stepAux, frame, initial, enter, states]
      refine congrArg some (congrArg (fun T =>
        (⟨_, (states F .eq, none, false), T⟩ : (machine F).Cfg)) ?_)
      funext k
      rcases k with (_ | _ | _ | _) | (j | k)
      all_goals first | cases j <;> simp [Function.update] | simp [Function.update]
  | eq =>
      dsimp only [machine, FiniteBlocks.machine, FinTM2.step, TM2.step, caller, cfg,
        TM2.stepAux, frame, initial, enter, states]
      refine congrArg some (congrArg (fun T =>
        (⟨_, (states F .eq, none, false), T⟩ : (machine F).Cfg)) ?_)
      funext k
      rcases k with (_ | _ | _ | _) | (j | k)
      all_goals first | cases j <;> simp [Function.update] | simp [Function.update]

/-- A larger divisor leaves the remainder intact and appends a canonical zero quotient bit. -/
theorem step_compared_gt (left right source bits quotient : List Sym) (S : F → List Sym) :
    (machine F).step (cfg F (some (.inr .compared)) left right source bits quotient S .gt) =
      some (cfg F (some (.inr .scan)) left right source bits (bitTape false quotient) S) := by
  cases quotient <;>
    dsimp only [machine, FiniteBlocks.machine, FinTM2.step, TM2.step, caller, cfg,
      TM2.stepAux, frame, initial, states, bitTape]
  all_goals
    refine congrArg some (congrArg (fun T =>
      (⟨_, (states F .eq, none, false), T⟩ : (machine F).Cfg)) ?_)
    funext k
    rcases k with (_ | _ | _ | _) | (j | k)
    all_goals first | cases j <;> simp [Function.update] | simp [Function.update]

/-- The normalization call costs one actual transition between the two arithmetic blocks. -/
theorem step_normalize (left right source bits quotient : List Sym) (S : F → List Sym) :
    (machine F).step (cfg F (some (.inr .normalize)) left right source bits quotient S) =
      some (cfg F (some (.inl ⟨.normalize, .one⟩)) left right source bits quotient S) := by
  dsimp only [machine, FiniteBlocks.machine, FinTM2.step, TM2.step, caller, cfg,
    TM2.stepAux, frame, initial, enter]
  rfl

@[simp] theorem bitTape_true (xs : List Sym) : bitTape true xs = .bit true :: xs := by
  cases xs <;> rfl

/-- One whole bit iteration includes every executed comparison, subtraction, and normalization. -/
theorem iteration_trace (d q r : ℕ) (b : Bool) (source bits : List Sym) (S : F → List Sym) :
    (flip Bind.bind (machine F).step)^[stepTime d r b]
      (some (cfg F (some (.inr .scan)) (natTape d) (natTape r)
        source (.bit b :: bits) (natTape q) S)) =
      some (cfg F (some (.inr .scan)) (natTape d) (natTape (stepValue d q r b).2)
        source bits (natTape (stepValue d q r b).1) S) := by
  have hscan := step_scan b (natTape d) (natTape r) source bits (natTape q) S
  rw [bitTape_natTape] at hscan
  by_cases hd : d = 0
  · subst d
    change (machine F).step (cfg F (some (.inr .scan)) [] (natTape r)
      source (.bit b :: bits) (natTape q) S) =
      some (cfg F (some (.inr .scan)) [] (natTape (Nat.bit b r)) source bits (natTape q) S)
    simpa only [show natTape 0 = [] from rfl, ite_true] using hscan
  have hleft : natTape d ≠ [] := fun h => hd (natTape_injective h)
  simp only [hleft, ite_false] at hscan
  by_cases hge : d ≤ Nat.bit b r
  · have horder : BinaryComparison.compareValue d (Nat.bit b r) .eq ≠ .gt := by
      simp only [BinaryComparison.compareValue, show ¬Nat.bit b r < d from by omega, ite_false]
      split_ifs <;> decide
    have htime : stepTime d r b =
        normalizationTime d (Nat.bit b r) + 1 + subtractionTime d (Nat.bit b r) + 1 +
          comparisonTime d (Nat.bit b r) + 1 := by
      simp only [stepTime, hd, ite_false, hge, ite_true]
      omega
    rw [htime, Function.iterate_succ_apply]
    change (flip Bind.bind (machine F).step)^[
      normalizationTime d (Nat.bit b r) + 1 + subtractionTime d (Nat.bit b r) + 1 +
        comparisonTime d (Nat.bit b r)]
      ((machine F).step (cfg F (some (.inr .scan)) (natTape d) (natTape r)
        source (.bit b :: bits) (natTape q) S)) = _
    rw [hscan, Function.iterate_add_apply, comparison_trace, Function.iterate_succ_apply]
    change (flip Bind.bind (machine F).step)^[
      normalizationTime d (Nat.bit b r) + 1 + subtractionTime d (Nat.bit b r)]
      ((machine F).step (cfg F (some (.inr .compared)) (natTape d) (natTape (Nat.bit b r))
        source bits (natTape q) S (BinaryComparison.compareValue d (Nat.bit b r) .eq))) = _
    rw [step_compared_le _ horder, Function.iterate_add_apply, subtraction_trace,
      Function.iterate_succ_apply]
    change (flip Bind.bind (machine F).step)^[normalizationTime d (Nat.bit b r)]
      ((machine F).step (cfg F (some (.inr .normalize)) (natTape d) (raw d (Nat.bit b r))
        source bits (.bit true :: natTape q) S)) = _
    rw [step_normalize, normalization_trace]
    have hq : Sym.bit true :: natTape q = natTape (Nat.bit true q) := by
      simpa only [bitTape_true] using bitTape_natTape true q
    simp only [stepValue, hd, ite_false, hge, ite_true, hq]
  · have horder : BinaryComparison.compareValue d (Nat.bit b r) .eq = .gt := by
      simp [BinaryComparison.compareValue, show ¬d < Nat.bit b r from by omega,
        show Nat.bit b r < d from by omega]
    have htime : stepTime d r b = 1 + comparisonTime d (Nat.bit b r) + 1 := by
      simp only [stepTime, hd, ite_false, hge, Nat.add_zero]
      omega
    rw [htime, Function.iterate_succ_apply]
    change (flip Bind.bind (machine F).step)^[1 + comparisonTime d (Nat.bit b r)]
      ((machine F).step (cfg F (some (.inr .scan)) (natTape d) (natTape r)
        source (.bit b :: bits) (natTape q) S)) = _
    rw [hscan, Function.iterate_add_apply, comparison_trace]
    change (machine F).step (cfg F (some (.inr .compared)) (natTape d) (natTape (Nat.bit b r))
      source bits (natTape q) S (BinaryComparison.compareValue d (Nat.bit b r) .eq)) = _
    rw [horder, step_compared_gt, bitTape_natTape]
    simp only [stepValue, hd, ite_false, hge]

/-- Input reversal charges every materialized bit and one phase transition. -/
theorem reverse_trace (left right source bits quotient : List Sym) (S : F → List Sym) :
    (flip Bind.bind (machine F).step)^[source.length + 1]
      (some (cfg F (some (.inr .reverse)) left right source bits quotient S)) =
      some (cfg F (some (.inr .scan)) left right [] (source.reverse ++ bits) quotient S) := by
  induction source generalizing bits with
  | nil => exact step_reverse_nil left right bits quotient S
  | cons c source ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (machine F).step)^[source.length + 1]
        ((machine F).step
          (cfg F (some (.inr .reverse)) left right (c :: source) bits quotient S)) = _
      rw [step_reverse_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

/-- Exact long-division trace from arbitrary initial canonical quotient and remainder. -/
theorem loop_trace (d q r : ℕ) (bs : List Bool) (source : List Sym) (S : F → List Sym) :
    (flip Bind.bind (machine F).step)^[runtime d q r bs]
      (some (cfg F (some (.inr .scan)) (natTape d) (natTape r) source (ofBits bs) (natTape q) S)) =
      some (cfg F none (natTape d) (natTape (value d q r bs).2)
        source [] (natTape (value d q r bs).1) S) := by
  induction bs generalizing q r with
  | nil => exact step_scan_nil (natTape d) (natTape r) source (natTape q) S
  | cons b bs ih =>
      simp only [runtime]
      rw [Function.iterate_add_apply]
      change (flip Bind.bind (machine F).step)^[
        runtime d (stepValue d q r b).1 (stepValue d q r b).2 bs]
        ((flip Bind.bind (machine F).step)^[stepTime d r b]
          (some (cfg F (some (.inr .scan)) (natTape d) (natTape r)
            source (.bit b :: ofBits bs) (natTape q) S))) = _
      rw [iteration_trace]
      exact ih _ _

/-- Actual polynomial-time division and modulo, retaining the divisor and caller frame. -/
def evals (n d : ℕ) (S : F → List Sym) :
    EvalsToInTime (machine F).step
      (cfg F (some (.inr .reverse)) (natTape d) [] (natTape n) [] [] S)
      (some (cfg F none (natTape d) (natTape (n % d)) [] [] (natTape (n / d)) S))
      (40 * (Nat.size d + Nat.size n + 1) ^ 2) where
  steps := Nat.size n + 1 + runtime d 0 0 n.bits.reverse
  evals_in_steps := by
    rw [Nat.add_comm, Function.iterate_add_apply]
    rw [← natTape_length n, reverse_trace, List.append_nil]
    have he : (natTape n).reverse = ofBits n.bits.reverse := by
      simp only [natTape, binDigits_eq_bits, ofBits, List.map_reverse]
    rw [he]
    have h := loop_trace d 0 0 n.bits.reverse [] S
    simpa only [show natTape 0 = [] from rfl, value_bits] using h
  steps_le_m := full_runtime_le d n

end PCP.Machine.BinaryDivision
