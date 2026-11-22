/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.InnerSeedFinalize

/-!
# Complete numeric inner-seed materialization

The runtime starts from the actual structural seed code. It constructs both
selector arms, their physical payloads, and the shared modulus/node sources.
Only the public source cells are assumed; all work arrays are initialized.
-/

namespace PCP.Lang.InnerSeed

open PCP.Algebraic ThreeColorSeedIndex InterpolationBranch

variable {t n m : ℕ} [NeZero t]

def program : Stmt 140 44 := .seq unpack (.seq materialize finalize)

attribute [local irreducible] unpack materialize finalize

/-- Exact actual-seed semantics, together with all retained source and decoded cells. -/
theorem program_run (a : Fin 5 → Field t) (site : StandardCorrection.Site (Field t) n)
    (s : InnerBranch.Seed t m) (st : State 140 44) (hc : Public m a site st)
    (hs : st.regs 132 = ((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s).val) :
    InnerBranch.Context a site s (selectorState (program.run st).1) ∧
      Stored s (program.run st).1 ∧ Data s (program.run st).1 ∧
      Public m a site (program.run st).1 ∧ Frame st (program.run st).1 := by
  have hu := unpack_run a site s st hc hs
  simp only [program, run_seq_fst]
  generalize hx : (unpack.run st).1 = u at *
  have hm := materialize_run a site s u hu.2.1 hu.1
  generalize hy : (materialize.run u).1 = v at *
  exact ⟨finalize_run a site s v hm.2.2.1 hm.2.1 hm.1,
    finalize_stored s v hm.1 hm.2.2.1.empty, finalize_data s v hm.2.1,
    hm.2.2.1.of_frame (finalize_frame v), hu.2.2.trans (hm.2.2.2.trans (finalize_frame v))⟩

/-- The three primitive selector scalars are ready for a caller's protected copy. -/
theorem program_scalars (a : Fin 5 → Field t) (site : StandardCorrection.Site (Field t) n)
    (s : InnerBranch.Seed t m) (st : State 140 44) (hc : Public m a site st)
    (hs : st.regs 132 = ((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s).val) :
    (program.run st).1.regs 100 = s.1.toNat ∧
      (program.run st).1.regs 104 = (BinaryFieldCode.fieldEquiv t s.2.2.1.2).val ∧
      (program.run st).1.regs 119 =
        (ThreeColorQueryIndex.innerIndex (BinaryFieldCode.fieldEquiv t) m 4 s.2.1.1).val := by
  have hr := program_run a site s st hc hs
  have h := hr.1
  have hz := hr.2.2.1 1
  change (program.run st).1.regs 104 =
    ((fieldCodec (BinaryMaterializedField.coordinates t)).equiv s.2.2.1.2).val at hz
  rw [UniformDecode.fieldCodec_materialized] at hz
  refine ⟨h.coin, hz, ?_⟩
  have hx := h.payload 9
  rw [location_point] at hx
  exact hx

end PCP.Lang.InnerSeed
