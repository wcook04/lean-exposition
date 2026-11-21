import PCP.Complexity.Machine

/-!
# Reversing an input word with an actual finite stack machine

This adapter supplies the input-order conversion required by the multitrack TM0
simulation. It uses two stacks, cleans its input, resets its control, and takes
exactly one transition per input symbol plus one terminating transition.
-/

namespace PCP.Machine.ReverseSymbols

open Turing Turing.TM2 Turing.TM2.Stmt

/-- Two-stack reversal with constant finite control. -/
def machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := fun _ => Sym
  Γk₀Fin := inferInstance
  Λ := Unit
  main := ()
  σ := Option Sym
  initialState := none
  m := fun _ =>
    pop false (fun _ a => a) <|
      branch Option.isSome
        (push true (fun a => a.getD Sym.sep) <|
          load (fun _ => none) (goto (fun _ => ())))
        (load (fun _ => none) halt)

/-- Source and accumulated output, with reset finite control. -/
def cfg (label : Option Unit) (src dst : List Sym) : machine.Cfg :=
  ⟨label, none, fun k : Bool => bif k then dst else src⟩

theorem step_cons (a : Sym) (src dst : List Sym) :
    machine.step (cfg (some ()) (a :: src) dst) =
      some (cfg (some ()) src (a :: dst)) := by
  simp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  apply congrArg some
  apply congrArg (TM2.Cfg.mk (some ()) none)
  funext k
  cases k <;> rfl

theorem step_nil (dst : List Sym) :
    machine.step (cfg (some ()) [] dst) = some (cfg none [] dst) := by
  simp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  apply congrArg some
  apply congrArg (TM2.Cfg.mk none none)
  funext k
  cases k <;> rfl

theorem trace (src dst : List Sym) :
    (Function.swap Bind.bind machine.step)^[src.length + 1] (some (cfg (some ()) src dst)) =
      some (cfg none [] (src.reverse ++ dst)) := by
  induction src generalizing dst with
  | nil => exact step_nil dst
  | cons a src ih =>
    rw [List.length_cons, Nat.succ_add, Function.iterate_succ_apply]
    change (Function.swap Bind.bind machine.step)^[src.length + 1]
      (machine.step (cfg (some ()) (a :: src) dst)) = _
    rw [step_cons, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem cfg_init (src : List Sym) : cfg (some ()) src [] = initList machine src := by
  unfold cfg initList
  apply congrArg (TM2.Cfg.mk (some ()) none)
  funext k
  cases k <;> rfl

theorem cfg_halt (dst : List Sym) : cfg none [] dst = haltList machine dst := by
  unfold cfg haltList
  apply congrArg (TM2.Cfg.mk none none)
  funext k
  cases k <;> rfl

/-- The exact clean-output reversal certificate. -/
def outputs (src : List Sym) :
    TM2OutputsInTime machine src (some src.reverse) (src.length + 1) where
  steps := src.length + 1
  steps_le_m := le_rfl
  evals_in_steps := by
    rw [← cfg_init]
    exact (trace src []).trans (by rw [List.append_nil, cfg_halt]; rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Reversal of any fixed external encoding is linear-time at that encoding. -/
noncomputable def witness {α : Type} (encoding : α → List Sym) :
    TM2ComputableInPolyTime encoding (fun a => (encoding a).reverse) id where
  tm := machine
  inputAlphabet := Equiv.refl Sym
  outputAlphabet := Equiv.refl Sym
  time := Polynomial.X + 1
  outputsFun a := by
    simpa only [Equiv.refl, List.map_id, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one, id_eq] using outputs (encoding a)

end PCP.Machine.ReverseSymbols
