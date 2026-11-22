import PCP.Complexity.ReferencePairMachine
import PCP.Complexity.TapeBooleanInterface
import Complexitylib.Interop.Mathlib.TM0
import Complexitylib.Encoding.Pairing

/-!
# Concrete Boolean stack computations transferred to reference tape machines

Every concrete relation checker is converted to one finite binary Mathlib TM0 with
polynomial time at Complexitylib's exact pair encoding. This is a machine construction,
not yet NP membership: totalization on malformed pair strings is supplied separately.
-/

namespace PCP.Machine.ReferenceTM0

open Turing
open Complexity.MathlibTM0
open TMTime

/-- The reference adapter and the quantitative compiler count the same TM0 transitions. -/
theorem run_eq_exec (M : BinaryMachine) (t : ℕ) (a : M.Config) :
    M.run t a = exec M.step t a := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih => simp only [BinaryMachine.run, exec, ih]

set_option backward.isDefEq.respectTransparency false in
/-- An arbitrary concrete clean-output Boolean stack witness yields a finite binary
tape machine, with a polynomial bound measured in the actual encoded input length. -/
theorem exists_binary_machine {α : Type} (encoding : α → List Bool) (f : α → Bool)
    (h : TM2ComputableInPolyTime (fun a => (ofBits (encoding a)).reverse) encodeBool f) :
    ∃ (M : BinaryMachine) (p : Polynomial ℕ),
      ∀ a, M.OutputsWithin (encoding a) [f a] (p.eval (encoding a).length) := by
  classical
  have hout : (Set.univ : Set (h.tm.Γ h.tm.k₁)).Finite := by
    let : Finite (h.tm.Γ h.tm.k₁) := Finite.of_equiv Sym h.outputAlphabet.symm
    exact Set.toFinite _
  let source := recodeWitness h hout
  have hΓ := recodeWitness_alphabets_finite h hout
  let : Finite (TapeAlphabet source.tm) := tapeAlphabet_finite source.tm hΓ
  let : Fintype (TapeAlphabet source.tm) := Fintype.ofFinite _
  obtain ⟨S⟩ := exists_tapeSimulation source.tm
  let inputBit : Bool → source.tm.Γ source.tm.k₀ :=
    fun b => source.inputAlphabet.invFun (.bit b)
  let outputBit : Bool → source.tm.Γ source.tm.k₁ :=
    fun b => source.outputAlphabet.invFun (.bit b)
  let decodeOutput : source.tm.Γ source.tm.k₁ → Bool := fun a =>
    match source.outputAlphabet a with
    | .bit b => b
    | .sep => false
  have hinput : Function.Injective inputBit := by
    intro a b hab
    exact Sym.bit.inj (source.inputAlphabet.symm.injective hab)
  have hdecode : ∀ b, decodeOutput (outputBit b) = b := by
    intro b
    exact congrArg (fun z : Sym => match z with | .bit b => b | .sep => false)
      (source.outputAlphabet.right_inv (.bit b))
  let M : BinaryMachine := {
    Alphabet := TapeAlphabet source.tm
    State := BooleanInterface.Control (Fin (S.states + 1))
    bit := BooleanInterface.cell source.tm inputBit
    readBit := BooleanInterface.readCell source.tm inputBit
    readBit_bit := BooleanInterface.readCell_cell source.tm inputBit hinput
    readBit_blank := BooleanInterface.readCell_blank source.tm inputBit
    code := BooleanInterface.code source.tm inputBit decodeOutput S.code }
  let p : Polynomial ℕ := Polynomial.C S.overhead *
    (Polynomial.X + source.time + Polynomial.C 3) ^ 2 + Polynomial.C 2
  refine ⟨M, p, ?_⟩
  intro a
  have hc : TM2OutputsInTime source.tm ((encoding a).reverse.map inputBit)
      (some [outputBit (f a)]) (source.time.eval (encoding a).length) := by
    simpa only [ofBits, ← List.map_reverse, List.map_map, List.length_reverse,
      List.length_map, encodeBool, List.map_cons, List.map_nil, inputBit, outputBit,
      Function.comp_def] using source.outputsFun a
  obtain ⟨u, hu, c, hrun, hhalt, houtput⟩ := BooleanInterface.outputs source.tm
    inputBit outputBit decodeOutput S hdecode (encoding a) (f a)
      (source.time.eval (encoding a).length) hc
  refine ⟨u, ?_, c, ?_, hhalt, houtput⟩
  · simpa only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] using hu
  · rw [run_eq_exec]
    exact hrun

end PCP.Machine.ReferenceTM0

namespace PCP.Machine.ReferencePair

/-- The local binary codec is the unchanged reference library's pairing function. -/
theorem bits_eq_pair (x y : List Bool) : bits x y = Complexity.pair x y := by
  induction x with
  | nil => rfl
  | cons b x ih => rw [bits, Complexity.pair_cons_eq, ih]

/-- Every actual polynomial-time relation checker has one reference binary TM0
computing that relation on every canonical reference pair input. -/
theorem exists_pair_machine (R : List Bool → List Bool → Bool) (hR : PolyTimeRel R) :
    ∃ (M : Complexity.MathlibTM0.BinaryMachine) (p : Polynomial ℕ),
      ∀ x w, M.OutputsWithin (Complexity.pair x w) [R x w]
        (p.eval (Complexity.pair x w).length) := by
  obtain ⟨hR⟩ := hR
  obtain ⟨M, p, hp⟩ := ReferenceTM0.exists_binary_machine
    (fun a : List Bool × List Bool => bits a.1 a.2) (fun a => R a.1 a.2)
    (checkerWitness R hR)
  refine ⟨M, p, fun x w => ?_⟩
  simpa only [bits_eq_pair] using hp (x, w)

end PCP.Machine.ReferencePair
