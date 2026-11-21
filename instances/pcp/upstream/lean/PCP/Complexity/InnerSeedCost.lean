/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.InnerSeedDecodeCost
import PCP.Complexity.InnerSeedWordCost

/-!
# Polynomial charged cost of the complete numeric inner-seed loader

The bound charges actual public source bit sizes, field cardinality, dimension,
and the bit size of the original seed. Scratch contents are unrestricted.
-/

namespace PCP.Lang.InnerSeed

open PCP.Algebraic ThreeColorSeedIndex InterpolationBranch

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] unpack hadamard point bits materialize finalize

def materializeConstant : ℕ := hadConstant + pointConstant 106 + pointConstant 105 +
  bitsConstant + 3

theorem materialize_cost (a : Fin 5 → Field t) (site : StandardCorrection.Site (Field t) n)
    (s : InnerBranch.Seed t m) (W : ℕ) (st : State 140 44) (hc : Public m a site st)
    (hd : Data s st) (hb : SourceBound W st)
    (hcode : Nat.size ((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s).val ≤ W) :
    (materialize.run st).2 ≤ materializeConstant * (budget t m W) ^ 5 := by
  have hh := hadamard_cost s W st hc.width hc.empty hd hb (hd.bound s W st hcode)
  have hf := hadamard_frame st
  have hdata := hadamard_data s st hd
  have hp := hc.of_frame hf
  have hbound := hb.of_frame hf
  unfold materialize
  simp only [run_seq_snd]
  generalize hu : (hadamard.run st).1 = u at *
  have hl := point_cost 106 (by decide) 32 W u hp.base hp.card hp.empty hbound
    (hdata.bound s W u hcode)
  have hlf := point_frame 106 32 (by decide) u
  have hld := hlf.data s hdata
  have hlp := hp.of_frame (hlf.public (by decide))
  have hlb := hbound.of_frame (hlf.public (by decide))
  generalize hv : ((point 106 32).run u).1 = v at *
  have hr := point_cost 105 (by decide) 33 W v hlp.base hlp.card hlp.empty hlb
    (hld.bound s W v hcode)
  have hrf := point_frame 105 33 (by decide) v
  have hrd := hrf.data s hld
  have hrp := hlp.of_frame (hrf.public (by decide))
  have hrb := hlb.of_frame (hrf.public (by decide))
  generalize hw : ((point 105 33).run v).1 = w at *
  have hcbit := bits_cost (m := m) W w hrp.width hrp.empty hrb (hrd.bound s W w hcode)
  have hA : 1 ≤ budget t m W := (by decide : 1 ≤ 10).trans (budget_basic t m W).1
  have h45 : (budget t m W) ^ 4 ≤ (budget t m W) ^ 5 :=
    Nat.pow_le_pow_right hA (by decide)
  have hl' := hl.trans (Nat.mul_le_mul_left _ h45)
  have hr' := hr.trans (Nat.mul_le_mul_left _ h45)
  have hb' := hcbit.trans (Nat.mul_le_mul_left _ h45)
  have h1 : 1 ≤ (budget t m W) ^ 5 := Nat.one_le_pow _ _ hA
  unfold materializeConstant
  nlinarith only [hh, hl', hr', hb', h1]

-- The final stage contains only a fixed sequence of protected-source copies.
set_option maxRecDepth 4096 in
theorem finalize_cost (W : ℕ) (st : State 140 44)
    (hb : SourceBound W st) (hd : DataBound W st) :
    (finalize.run st).2 ≤ fixedConstant finalize * (W + 1) := by
  apply fixed_cost finalize (by unfold finalize; decide)
    (by unfold finalize; decide) (by unfold finalize; decide) W st hb hd

def costConstant : ℕ := unpackConstant + materializeConstant + fixedConstant finalize + 2

/-- Full cost bound for the actual materializer, with no runtime or callback premise. -/
theorem program_cost (a : Fin 5 → Field t) (site : StandardCorrection.Site (Field t) n)
    (s : InnerBranch.Seed t m) (W : ℕ) (st : State 140 44) (hc : Public m a site st)
    (hb : SourceBound W st)
    (hs : st.regs 132 = ((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s).val) :
    (program.run st).2 ≤ costConstant * (budget t m W) ^ 5 := by
  have hu := unpack_run a site s st hc hs
  have huc := unpack_cost a site s W st hc hb hs
  have hub := hb.of_frame hu.2.2
  have hcode :
      Nat.size ((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s).val ≤ W :=
    hs ▸ hb.regs 132 (by decide) (by decide)
  simp only [program, run_seq_snd]
  generalize hx : (unpack.run st).1 = u at *
  have hm := materialize_run a site s u hu.2.1 hu.1
  have hmc := materialize_cost a site s W u hu.2.1 hu.1 hub hcode
  have hmb := hub.of_frame hm.2.2.2
  generalize hy : (materialize.run u).1 = v at *
  have hf := finalize_cost W v hmb (hm.2.1.bound s W v hcode)
  have hA : 1 ≤ budget t m W := (by decide : 1 ≤ 10).trans (budget_basic t m W).1
  have hu' := huc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hA (by decide : 4 ≤ 5)))
  have hf' := hf.trans (Nat.mul_le_mul_left _ ((budget_basic t m W).2.1.trans
    (Nat.le_pow (by decide : 0 < 5))))
  have h1 : 1 ≤ (budget t m W) ^ 5 := Nat.one_le_pow _ _ hA
  unfold costConstant
  nlinarith only [hu', hmc, hf', h1]

end PCP.Lang.InnerSeed
