/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Combinators.Internal.IdleHeads

/-!
# One `loopTM` iteration that continues

`TM.loopTM_iteration_halt` traces a single pass through `loopTM` that ends in the halting
branch. The complementary pass — the one where the test says *keep going* — had no counterpart,
which left the indexed loop rule `TM.loopTM_hoareTime_indexed` without a way to discharge its
per-iteration obligation: that obligation asks for a run from the loop's start state back to the
loop's start state, and only the check phase's continue branch produces one.

The pass is body, then test, then the rewind of the output tape, then the check. Everything
outside the two simulations moves each tape by `idleDir` and writes back what it read, so on
tapes that carry their left marker and are parked past it the whole phase machinery is the
identity — which is what makes an invariant on the work tapes survive into the next iteration.

## Main results

- `TM.loopTM_check_continue_frame` — the continue branch of the check phase leaves every tape
  identical
- `TM.loopTM_iteration_continue` — a full iteration returning to `qstart`, tapes and all
- `TM.loopTM_check_halt_frame`, `TM.loopTM_iteration_halt_frame` — the halting pass, likewise
  reporting the tapes it ends on
- `TM.loopTM_continue_of_hoare`, `TM.loopTM_halt_of_hoare` — both passes packaged as the two
  obligations of `TM.loopTM_hoareTime_indexed`, from a contract for the body and one for the test
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- **The continue branch of the check phase, framed.** Everything the branch does is write back
what it read and move by `idleDir`, so a tape parked past its left marker is untouched. -/
theorem loopTM_check_continue_frame (tmBody tmTest : TM n)
    (c : Cfg n (LoopQ tmBody.Q tmTest.Q))
    (hstate : c.state = Sum.inr (Sum.inl LoopPhase.check))
    (hhead : c.output.head = 1)
    (hcell1 : c.output.cells 1 ≠ Γ.one)
    (hout : Parked c.output) (hinp : Parked c.input) (hwork : ∀ i, Parked (c.work i)) :
    ∃ c', (loopTM tmBody tmTest).step c = some c' ∧
      c'.state = (loopTM tmBody tmTest).qstart ∧
      c'.input = c.input ∧ c'.work = c.work ∧ c'.output = c.output := by
  have hne : c.state ≠ (loopTM tmBody tmTest).qhalt := by
    rw [hstate]; nofun
  have hread_ne : c.output.read ≠ Γ.one := by
    simp only [Tape.read, hhead]; exact hcell1
  simp only [TM.step, ↓reduceIte, hstate, loopTM, hread_ne]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · exact transitionInput_eq_self hinp.read_ne_start
  · funext i
    exact transitionTape_eq_self (hwork i).read_ne_start
  · exact transitionTape_eq_self hout.read_ne_start

/-- **One full `loopTM` iteration that continues.** The body runs to its halt state, the test
runs to its halt state, the output tape is rewound to cell one, and the verdict cell fails to
hold `1` — so the machine returns to its own start state with the test's tapes intact.

The step count matches `TM.loopTM_iteration_halt`: the two simulations, the two phase
transitions between them, the rewind of `p + 1` steps, and the check. -/
theorem loopTM_iteration_continue (tmBody tmTest : TM n)
    {t_body : ℕ} {c_body_start c_body_end : Cfg n tmBody.Q}
    (hreach_body : tmBody.reachesIn t_body c_body_start c_body_end)
    (hhalt_body : c_body_end.state = tmBody.qhalt)
    (hinp_body : Parked c_body_end.input) (hwork_body : ∀ i, Parked (c_body_end.work i))
    (hout_body : Parked c_body_end.output)
    {t_test : ℕ} {c_test_end : Cfg n tmTest.Q}
    (hreach_test : tmTest.reachesIn t_test
      ⟨tmTest.qstart, c_body_end.input, c_body_end.work, c_body_end.output⟩ c_test_end)
    (hhalt_test : c_test_end.state = tmTest.qhalt)
    (hinp_test : Parked c_test_end.input) (hwork_test : ∀ i, Parked (c_test_end.work i))
    (hout_test : Parked c_test_end.output) (hout0 : c_test_end.output.cells 0 = Γ.start)
    {p : ℕ} (hp : c_test_end.output.head = p)
    (hcell1 : c_test_end.output.cells 1 ≠ Γ.one) :
    ∃ c_final,
      (loopTM tmBody tmTest).reachesIn (t_body + 1 + t_test + 1 + (p + 1) + 1)
        (loopBodyWrap tmBody tmTest c_body_start) c_final ∧
      c_final.state = (loopTM tmBody tmTest).qstart ∧
      c_final.input = c_test_end.input ∧
      c_final.work = c_test_end.work ∧
      c_final.output.head = 1 ∧
      c_final.output.cells = c_test_end.output.cells := by
  -- Phase 1: the body simulation.
  have hp1 := loopTM_body_simulation tmBody tmTest hreach_body
  -- Body → test: one step, and the parked tapes pass through unchanged.
  have h_tr1 : (loopTM tmBody tmTest).reachesIn 1
      (loopBodyWrap tmBody tmTest c_body_end)
      (loopTestWrap tmBody tmTest
        ⟨tmTest.qstart, c_body_end.input, c_body_end.work, c_body_end.output⟩) := by
    refine .step ?_ .zero
    have h := loopTM_body_to_test tmBody tmTest hhalt_body
    rw [h]
    congr 1
    refine Cfg.ext rfl ?_ ?_ ?_
    · exact transitionInput_eq_self hinp_body.read_ne_start
    · funext i
      exact transitionTape_eq_self (hwork_body i).read_ne_start
    · exact transitionTape_eq_self hout_body.read_ne_start
  -- Phase 2: the test simulation.
  have hp2 := loopTM_test_simulation tmBody tmTest hreach_test
  -- Test → rewind: one step, again the identity on parked tapes.
  have h_tr2 : (loopTM tmBody tmTest).reachesIn 1
      (loopTestWrap tmBody tmTest c_test_end)
      ⟨Sum.inr (Sum.inl LoopPhase.rewindOut), c_test_end.input, c_test_end.work,
        c_test_end.output⟩ := by
    refine .step ?_ .zero
    have h := loopTM_test_to_rewind tmBody tmTest hhalt_test
    rw [h]
    congr 1
    refine Cfg.ext rfl ?_ ?_ ?_
    · exact transitionInput_eq_self hinp_test.read_ne_start
    · funext i
      exact transitionTape_eq_self (hwork_test i).read_ne_start
    · exact transitionTape_eq_self hout_test.read_ne_start
  -- The rewind, which is where the output head returns to cell one.
  obtain ⟨c_check, hreach_rw, hst_check, hh_check, hcells_check, hin_check, hwk_check⟩ :=
    loopTM_rewind_loop_frame tmBody tmTest p
      ⟨Sum.inr (Sum.inl LoopPhase.rewindOut), c_test_end.input, c_test_end.work,
        c_test_end.output⟩
      rfl hout0 hout_test.2 hp hinp_test.1 hinp_test.2
      (fun i => (hwork_test i).1) (fun i => (hwork_test i).2)
  -- The check, taking the continue branch.
  obtain ⟨c_done, hstep_done, hst_done, hin_done, hwk_done, hout_done⟩ :=
    loopTM_check_continue_frame tmBody tmTest c_check hst_check hh_check
      (by rw [hcells_check]; exact hcell1)
      ⟨by omega, by rw [hcells_check]; exact hout_test.2⟩
      (by rw [hin_check]; exact hinp_test)
      (by rw [hwk_check]; exact fun i => hwork_test i)
  refine ⟨c_done, ?_, hst_done, ?_, ?_, ?_, ?_⟩
  · exact reachesIn_trans _ (reachesIn_trans _ (reachesIn_trans _
      (reachesIn_trans _ (reachesIn_trans _ hp1 h_tr1) hp2) h_tr2) hreach_rw)
      (.step hstep_done .zero)
  · rw [hin_done, hin_check]
  · rw [hwk_done, hwk_check]
  · rw [hout_done, hh_check]
  · rw [hout_done, hcells_check]


/-- **The halting branch of the check phase, framed.** As with the continue branch, the step
writes back what it read and idles, so parked tapes are untouched. -/
theorem loopTM_check_halt_frame (tmBody tmTest : TM n)
    (c : Cfg n (LoopQ tmBody.Q tmTest.Q))
    (hstate : c.state = Sum.inr (Sum.inl LoopPhase.check))
    (hhead : c.output.head = 1)
    (hcell1 : c.output.cells 1 = Γ.one)
    (hout : Parked c.output) (hinp : Parked c.input) (hwork : ∀ i, Parked (c.work i)) :
    ∃ c', (loopTM tmBody tmTest).step c = some c' ∧
      (loopTM tmBody tmTest).halted c' ∧
      c'.input = c.input ∧ c'.work = c.work ∧ c'.output = c.output := by
  have hne : c.state ≠ (loopTM tmBody tmTest).qhalt := by
    rw [hstate]; nofun
  have hread : c.output.read = Γ.one := by simp only [Tape.read, hhead]; exact hcell1
  simp only [TM.step, ↓reduceIte, hstate, loopTM, hread]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · exact transitionInput_eq_self hinp.read_ne_start
  · funext i
    exact transitionTape_eq_self (hwork i).read_ne_start
  · show c.output.writeAndMove (readBackWrite Γ.one).toΓ (idleDir Γ.one) = c.output
    rw [← hread]
    exact transitionTape_eq_self hout.read_ne_start

/-- **One full `loopTM` iteration that halts, framed.** The same pass as
`TM.loopTM_iteration_halt`, but reporting the input and work tapes of the halted configuration —
which a loop's postcondition generally talks about, and which the unframed version discards. -/
theorem loopTM_iteration_halt_frame (tmBody tmTest : TM n)
    {t_body : ℕ} {c_body_start c_body_end : Cfg n tmBody.Q}
    (hreach_body : tmBody.reachesIn t_body c_body_start c_body_end)
    (hhalt_body : c_body_end.state = tmBody.qhalt)
    (hinp_body : Parked c_body_end.input) (hwork_body : ∀ i, Parked (c_body_end.work i))
    (hout_body : Parked c_body_end.output)
    {t_test : ℕ} {c_test_end : Cfg n tmTest.Q}
    (hreach_test : tmTest.reachesIn t_test
      ⟨tmTest.qstart, c_body_end.input, c_body_end.work, c_body_end.output⟩ c_test_end)
    (hhalt_test : c_test_end.state = tmTest.qhalt)
    (hinp_test : Parked c_test_end.input) (hwork_test : ∀ i, Parked (c_test_end.work i))
    (hout_test : Parked c_test_end.output) (hout0 : c_test_end.output.cells 0 = Γ.start)
    {p : ℕ} (hp : c_test_end.output.head = p)
    (hcell1 : c_test_end.output.cells 1 = Γ.one) :
    ∃ c_final,
      (loopTM tmBody tmTest).reachesIn (t_body + 1 + t_test + 1 + (p + 1) + 1)
        (loopBodyWrap tmBody tmTest c_body_start) c_final ∧
      (loopTM tmBody tmTest).halted c_final ∧
      c_final.input = c_test_end.input ∧
      c_final.work = c_test_end.work ∧
      c_final.output.head = 1 ∧
      c_final.output.cells = c_test_end.output.cells := by
  have hp1 := loopTM_body_simulation tmBody tmTest hreach_body
  have h_tr1 : (loopTM tmBody tmTest).reachesIn 1
      (loopBodyWrap tmBody tmTest c_body_end)
      (loopTestWrap tmBody tmTest
        ⟨tmTest.qstart, c_body_end.input, c_body_end.work, c_body_end.output⟩) := by
    refine .step ?_ .zero
    rw [loopTM_body_to_test tmBody tmTest hhalt_body]
    congr 1
    refine Cfg.ext rfl (transitionInput_eq_self hinp_body.read_ne_start) ?_
      (transitionTape_eq_self hout_body.read_ne_start)
    funext i
    exact transitionTape_eq_self (hwork_body i).read_ne_start
  have hp2 := loopTM_test_simulation tmBody tmTest hreach_test
  have h_tr2 : (loopTM tmBody tmTest).reachesIn 1
      (loopTestWrap tmBody tmTest c_test_end)
      ⟨Sum.inr (Sum.inl LoopPhase.rewindOut), c_test_end.input, c_test_end.work,
        c_test_end.output⟩ := by
    refine .step ?_ .zero
    rw [loopTM_test_to_rewind tmBody tmTest hhalt_test]
    congr 1
    refine Cfg.ext rfl (transitionInput_eq_self hinp_test.read_ne_start) ?_
      (transitionTape_eq_self hout_test.read_ne_start)
    funext i
    exact transitionTape_eq_self (hwork_test i).read_ne_start
  obtain ⟨c_check, hreach_rw, hst_check, hh_check, hcells_check, hin_check, hwk_check⟩ :=
    loopTM_rewind_loop_frame tmBody tmTest p
      ⟨Sum.inr (Sum.inl LoopPhase.rewindOut), c_test_end.input, c_test_end.work,
        c_test_end.output⟩
      rfl hout0 hout_test.2 hp hinp_test.1 hinp_test.2
      (fun i => (hwork_test i).1) (fun i => (hwork_test i).2)
  obtain ⟨c_done, hstep_done, hst_done, hin_done, hwk_done, hout_done⟩ :=
    loopTM_check_halt_frame tmBody tmTest c_check hst_check hh_check
      (by rw [hcells_check]; exact hcell1)
      ⟨by omega, by rw [hcells_check]; exact hout_test.2⟩
      (by rw [hin_check]; exact hinp_test)
      (by rw [hwk_check]; exact fun i => hwork_test i)
  refine ⟨c_done, ?_, hst_done, ?_, ?_, ?_, ?_⟩
  · exact reachesIn_trans _ (reachesIn_trans _ (reachesIn_trans _
      (reachesIn_trans _ (reachesIn_trans _ hp1 h_tr1) hp2) h_tr2) hreach_rw)
      (.step hstep_done .zero)
  · rw [hin_done, hin_check]
  · rw [hwk_done, hwk_check]
  · rw [hout_done, hh_check]
  · rw [hout_done, hcells_check]

/-- The side conditions a loop's intermediate and final tape states must meet for the phase
machinery to be transparent: every tape carries its left marker nowhere but cell zero, and every
head is parked past it. -/
def LoopParked {n : ℕ} (inp : Tape) (work : Fin n → Tape) (out : Tape) : Prop :=
  Parked inp ∧ (∀ i, Parked (work i)) ∧ Parked out ∧ out.cells 0 = Γ.start ∧ out.head = 1

/-- **The per-iteration obligation of `TM.loopTM_hoareTime_indexed`, from two Hoare triples.**
Give a contract for the body and one for the test; if the test's postcondition leaves the tapes
parked with a verdict cell that is not `1`, the loop returns to its own start state with that
postcondition intact. -/
theorem loopTM_continue_of_hoare (tmBody tmTest : TM n)
    {E mid E' : TapePred n} {bBody bTest : ℕ}
    (hbody : tmBody.HoareTime E mid bBody)
    (htest : tmTest.HoareTime mid E' bTest)
    (hmid : ∀ inp work out, mid inp work out → LoopParked inp work out)
    (hpost : ∀ inp work out, E' inp work out →
      LoopParked inp work out ∧ out.cells 1 ≠ Γ.one) :
    ∀ inp work out, E inp work out →
      ∃ inp' work' out' t, 1 ≤ t ∧ t ≤ bBody + bTest + 5 ∧
        (loopTM tmBody tmTest).reachesIn t
          ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩
          ⟨(loopTM tmBody tmTest).qstart, inp', work', out'⟩ ∧
        E' inp' work' out' := by
  intro inp work out hE
  obtain ⟨cb, tb, htb, hreachb, hhb, hmidb⟩ := hbody inp work out hE
  obtain ⟨hbi, hbw, hbo, hbo0, hbo1⟩ := hmid _ _ _ hmidb
  obtain ⟨ct, tt, htt, hreacht, hht, hE't⟩ := htest cb.input cb.work cb.output hmidb
  obtain ⟨⟨hti, htw, hto, hto0, hto1⟩, hne⟩ := hpost _ _ _ hE't
  obtain ⟨cf, hreach, hstf, hinf, hwkf, hheadf, hcellsf⟩ :=
    loopTM_iteration_continue tmBody tmTest hreachb hhb hbi hbw hbo hreacht hht hti htw hto
      hto0 hto1 hne
  refine ⟨cf.input, cf.work, cf.output, tb + 1 + tt + 1 + (1 + 1) + 1, by omega, by omega, ?_, ?_⟩
  · have : (⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩ : Cfg n _)
        = loopBodyWrap tmBody tmTest ⟨tmBody.qstart, inp, work, out⟩ := rfl
    rw [this]
    have hcf : (⟨(loopTM tmBody tmTest).qstart, cf.input, cf.work, cf.output⟩ : Cfg n _) = cf :=
      Cfg.ext hstf.symm rfl rfl rfl
    rw [hcf]
    exact hreach
  · have hout' : cf.output = ct.output := Tape.ext (by rw [hheadf, hto1]) hcellsf
    rw [hinf, hwkf, hout']
    exact hE't

/-- **The terminating obligation of `TM.loopTM_hoareTime_indexed`, from two Hoare triples.** The
companion of `TM.loopTM_continue_of_hoare` for the pass whose verdict cell does hold `1`. -/
theorem loopTM_halt_of_hoare (tmBody tmTest : TM n)
    {E mid E' : TapePred n} {bBody bTest : ℕ}
    (hbody : tmBody.HoareTime E mid bBody)
    (htest : tmTest.HoareTime mid E' bTest)
    (hmid : ∀ inp work out, mid inp work out → LoopParked inp work out)
    (hpost : ∀ inp work out, E' inp work out →
      LoopParked inp work out ∧ out.cells 1 = Γ.one) :
    ∀ inp work out, E inp work out →
      ∃ c' t, t ≤ bBody + bTest + 5 ∧
        (loopTM tmBody tmTest).reachesIn t
          ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩ c' ∧
        (loopTM tmBody tmTest).halted c' ∧ E' c'.input c'.work c'.output := by
  intro inp work out hE
  obtain ⟨cb, tb, htb, hreachb, hhb, hmidb⟩ := hbody inp work out hE
  obtain ⟨hbi, hbw, hbo, hbo0, hbo1⟩ := hmid _ _ _ hmidb
  obtain ⟨ct, tt, htt, hreacht, hht, hE't⟩ := htest cb.input cb.work cb.output hmidb
  obtain ⟨⟨hti, htw, hto, hto0, hto1⟩, heq⟩ := hpost _ _ _ hE't
  obtain ⟨cf, hreach, hstf, hinf, hwkf, hheadf, hcellsf⟩ :=
    loopTM_iteration_halt_frame tmBody tmTest hreachb hhb hbi hbw hbo hreacht hht hti htw hto
      hto0 hto1 heq
  refine ⟨cf, tb + 1 + tt + 1 + (1 + 1) + 1, by omega, hreach, hstf, ?_⟩
  have hout' : cf.output = ct.output := Tape.ext (by rw [hheadf, hto1]) hcellsf
  rw [hinf, hwkf, hout']
  exact hE't

end TM

end Complexity
