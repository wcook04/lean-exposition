/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.InnerSeedWords

/-! # Complete materialized arrays for both arms of the inner selector -/

namespace PCP.Lang.InnerSeed

open PCP.Algebraic ThreeColorSeedIndex InterpolationBranch

variable {t n m : ℕ} [NeZero t]

structure Stored (s : InnerBranch.Seed t m) (st : State 140 44) : Prop where
  hadamard : HadamardRow.Context s.2.1.2 (rowState st)
  left : st.lists 32 = List.ofFn
    (fun i => (BinaryFieldCode.fieldEquiv t (StandardCorrection.vector s.2.2.1.1.1 i)).val)
  right : st.lists 33 = List.ofFn
    (fun i => (BinaryFieldCode.fieldEquiv t (StandardCorrection.vector s.2.2.1.1.2 i)).val)
  label : st.lists 34 = List.ofFn (fun i => (s.2.2.2 i).val)

def materialize : Stmt 140 44 := .seq hadamard
  (.seq (point 106 32) (.seq (point 105 33) bits))

attribute [local irreducible] hadamard point bits

theorem materialize_run (a : Fin 5 → Field t) (site : StandardCorrection.Site (Field t) n)
    (s : InnerBranch.Seed t m) (st : State 140 44) (hc : Public m a site st)
    (hd : Data s st) : Stored s (materialize.run st).1 ∧ Data s (materialize.run st).1 ∧
      Public m a site (materialize.run st).1 ∧ Frame st (materialize.run st).1 := by
  have hh := hadamard_run s st hc.width hc.empty hd
  have hf := hadamard_frame st
  have hdata := hadamard_data s st hd
  have hp := hc.of_frame hf
  simp only [materialize, run_seq_fst]
  generalize hu : (hadamard.run st).1 = u at *
  have hl := point_run s.2.2.1.1.1 106 32 u (hdata 3) hp.base hp.card hp.empty
  have hlf := point_frame 106 32 (by decide) u
  have hlh := hlf.hadamard (by decide) s hp.empty hh
  have hld := hlf.data s hdata
  have hlp := hp.of_frame (hlf.public (by decide))
  have hlfull := hf.trans (hlf.public (by decide))
  generalize hv : ((point 106 32).run u).1 = v at *
  have hr := point_run s.2.2.1.1.2 105 33 v (hld 2) hlp.base hlp.card hlp.empty
  have hrf := point_frame 105 33 (by decide) v
  have hrh := hrf.hadamard (by decide) s hlp.empty hlh
  have hrd := hrf.data s hld
  have hrp := hlp.of_frame (hrf.public (by decide))
  have hrfull := hlfull.trans (hrf.public (by decide))
  have hrl := (hrf.lists 32 (by decide) (by decide)).trans hl
  generalize hw : ((point 105 33).run v).1 = w at *
  have hb := bits_run s.2.2.2 w (hrd 0) hrp.width hrp.empty
  have hbf := bits_frame w
  exact ⟨⟨hbf.hadamard (by decide) s hrp.empty hrh,
    (hbf.lists 32 (by decide) (by decide)).trans hrl,
    (hbf.lists 33 (by decide) (by decide)).trans hr, hb⟩,
    hbf.data s hrd, hrp.of_frame (hbf.public (by decide)),
    hrfull.trans (hbf.public (by decide))⟩

end PCP.Lang.InnerSeed
