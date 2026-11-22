import PCP.Complexity.ThreeColorBaseOuter
import PCP.Complexity.ThreeColorBaseDerivedLang
import PCP.Complexity.ThreeColorBaseDifference
import PCP.Complexity.ThreeColorBasePreflight

/-! # Shared preserved state of all seven production callbacks -/

namespace PCP.Lang.ThreeColorBaseBranches

open PCP.Algebraic ThreeColorBaseSetup ThreeColorBasePreflight

structure Frame (st out : State 400 128) : Prop where
  regs : ∀ i : Fin 400, 320 ≤ i.val → out.regs i = st.regs i
  lists : ∀ L : Fin 128, (115 ≤ L.val ∨ (100 ≤ L.val ∧ L.val < 103)) → L ≠ 124 →
    out.lists L = st.lists L

theorem Frame.trans {st u v : State 400 128} (h : Frame st u) (g : Frame u v) : Frame st v :=
  ⟨fun i hi => (g.regs i hi).trans (h.regs i hi),
    fun L hi hj => (g.lists L hi hj).trans (h.lists L hi hj)⟩

structure Context (x bits answers : List Bool) (qs : List ℕ) (st : State 400 128) : Prop where
  ready : Ready x bits answers st
  history : st.lists 123 = qs

theorem ready_of_frame {x bits answers : List Bool} {st out : State 400 128}
    (h : Ready x bits answers st) (hf : Frame st out) : Ready x bits answers out := by
  constructor
  · constructor
    · exact (hf.regs 320 (by decide)).trans h.data.order
    · exact (hf.regs 321 (by decide)).trans h.data.exponent
    · exact (hf.regs 322 (by decide)).trans h.data.dimension
    · exact (hf.regs 323 (by decide)).trans h.data.volume
    · exact (hf.regs 324 (by decide)).trans h.data.width
    · exact (hf.regs 325 (by decide)).trans h.data.card
    · exact (hf.regs 326 (by decide)).trans h.data.cube
    · exact (hf.regs 327 (by decide)).trans h.data.generatorCode
    · exact (hf.lists 120 (by decide) (by decide)).trans h.data.modulus
    · exact (hf.lists 121 (by decide) (by decide)).trans h.data.nodes
    · exact (hf.lists 122 (by decide) (by decide)).trans h.data.empty
  · constructor
    · exact (hf.regs 328 (by decide)).trans h.cardinal.vertices
    · exact (hf.regs 329 (by decide)).trans h.cardinal.pairs
    · exact (hf.regs 330 (by decide)).trans h.cardinal.proper
    · exact (hf.regs 331 (by decide)).trans h.cardinal.inner
    · exact (hf.regs 332 (by decide)).trans h.cardinal.affine
    · exact (hf.regs 333 (by decide)).trans h.cardinal.cubic
  · intro i
    exact (hf.regs (ThreeColorBaseSeed.port i)
      (by simp [ThreeColorBaseSeed.port]; omega)).trans (h.seeds i)
  · constructor
    · exact (hf.lists 100 (by decide) (by decide)).trans h.sources.graph
    · exact (hf.lists 101 (by decide) (by decide)).trans h.sources.bits
    · exact (hf.lists 102 (by decide) (by decide)).trans h.sources.answers
    · exact (hf.lists 122 (by decide) (by decide)).trans h.sources.empty
  · exact (hf.regs 357 (by decide)).trans h.guard

theorem Context.of_frame {x bits answers : List Bool} {qs : List ℕ} {st out : State 400 128}
    (h : Context x bits answers qs st) (hf : Frame st out) : Context x bits answers qs out :=
  ⟨ready_of_frame h.ready hf, (hf.lists 123 (by decide) (by decide)).trans h.history⟩

def branch (i : Fin 7) : Stmt 400 128 :=
  ![ThreeColorBaseOuter.program .color, ThreeColorBaseOuter.program .valid,
    ThreeColorBaseOuter.program .difference, ThreeColorBaseOuter.program .proper,
    ThreeColorBaseDerived.program .valid, ThreeColorBaseDerived.program .proper,
    ThreeColorBaseDifference.program] i

def resultPort (i : Fin 7) : Fin 400 := ⟨301+i.val, by omega⟩

theorem outer_frame (k : OuterBranch.Kind) (st : State 400 128) :
    Frame st ((ThreeColorBaseOuter.program k).run st).1 :=
  ⟨fun i hi => ThreeColorBaseOuter.program_metadata k i hi st,
    fun L hL hn => ThreeColorBaseOuter.program_list k L (by omega) hn st⟩

theorem derived_frame (k : LocalCorrection.Certificate) (st : State 400 128) :
    Frame st ((ThreeColorBaseDerived.program k).run st).1 :=
  ⟨ThreeColorBaseDerived.program_metadata k st, ThreeColorBaseDerived.program_list k st⟩

theorem difference_frame (st : State 400 128) :
    Frame st (ThreeColorBaseDifference.program.run st).1 :=
  ⟨fun i hi => ThreeColorBaseDifference.program_reg i (by omega) (by omega) st,
    fun L hL hn => ThreeColorBaseDifference.program_list L (by omega) hn st⟩

attribute [local irreducible] ThreeColorBaseOuter.program ThreeColorBaseDerived.program
  ThreeColorBaseDifference.program

theorem branch_frame (i : Fin 7) (st : State 400 128) : Frame st ((branch i).run st).1 := by
  fin_cases i
  · exact outer_frame .color st
  · exact outer_frame .valid st
  · exact outer_frame .difference st
  · exact outer_frame .proper st
  · exact derived_frame .valid st
  · exact derived_frame .proper st
  · exact difference_frame st

theorem branch_accumulator (i : Fin 7) (st : State 400 128) :
    ((branch i).run st).1.regs 300 = st.regs 300 := by
  fin_cases i
  · exact ThreeColorBaseOuter.program_reg .color 300 (by decide) (by decide) (by decide) st
  · exact ThreeColorBaseOuter.program_reg .valid 300 (by decide) (by decide) (by decide) st
  · exact ThreeColorBaseOuter.program_reg .difference 300 (by decide) (by decide) (by decide) st
  · exact ThreeColorBaseOuter.program_reg .proper 300 (by decide) (by decide) (by decide) st
  · exact ThreeColorBaseDerived.program_reg .valid st 300 (by decide) (by decide) (by decide)
  · exact ThreeColorBaseDerived.program_reg .proper st 300 (by decide) (by decide) (by decide)
  · exact ThreeColorBaseDifference.program_reg 300 (by decide) (by decide) st

end PCP.Lang.ThreeColorBaseBranches
