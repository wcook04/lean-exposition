import PCP.Complexity.ThreeColorBasePreflightResources
import PCP.Complexity.ThreeColorSeedGuardCost

/-! # Charged polynomial cost of the complete production preflight -/

namespace PCP.Lang.ThreeColorBasePreflight

open PCP.Algebraic ThreeColorBaseSetup CanonicalResourceBounds

def costConstant : ℕ := ThreeColorBaseSetup.costConstant+cardinalConstant*coreConstant^4+
  ThreeColorBaseSeed.costConstant+ThreeColorSeedGuard.costConstant+3

attribute [local irreducible] ThreeColorBaseSetup.field ThreeColorBaseCardinal.program
  ThreeColorBaseSeed.program ThreeColorSeedGuard.program ThreeColorBaseSetup.costConstant
  cardinalConstant coreConstant ThreeColorBaseSeed.costConstant ThreeColorSeedGuard.costConstant

theorem program_cost (x bits answers : List Bool) (st : State 400 128)
    (hs : Sources x bits answers st) :
    (program.run st).2 ≤ costConstant*(x.length+bits.length+1)^84 := by
  have hfield := field_cost x st hs.graph hs.empty
  have hd := field_run x st hs.graph hs.empty
  have hsrc := field_sources x bits answers st hs
  generalize hu : (ThreeColorBaseSetup.field.run st).1 = u at *
  have hcard := cardinal_input_cost x u hd
  have hd' := ThreeColorBaseCardinal.program_data _ u hd
  have hsrc' := ThreeColorBaseCardinal.program_sources x bits answers u hsrc
  generalize hv : (ThreeColorBaseCardinal.program.run u).1 = v at *
  have hseed := ThreeColorBaseSeed.program_input_cost x bits v hd' hsrc'.bits
  have hseeds := ThreeColorBaseSeed.program_run _ bits v hd' hsrc'.bits
  have hd'' := hd'.of_frame (ThreeColorBaseSeed.program_frame v)
  generalize hw : (ThreeColorBaseSeed.program.run v).1 = w at *
  have hguard := ThreeColorSeedGuard.program_input_cost x bits w hd'' hseeds
  let B := x.length+bits.length+1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have harg : x.length+1 ≤ B := by dsimp [B]; omega
  have hfield' := hfield.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 84))
  have hp48 : (x.length+1)^48 ≤ B^84 :=
    (Nat.pow_le_pow_left harg 48).trans (Nat.pow_le_pow_right hB (by decide))
  have hcard' := hcard.trans (Nat.mul_le_mul_left _ hp48)
  have hseed' := hseed.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right hB (by decide : 24 ≤ 84)))
  have hguard' := hguard.trans (Nat.mul_le_mul_left _ hp48)
  have h1 : 1 ≤ B^84 := Nat.one_le_pow _ _ hB
  simp only [program, run_seq_snd, hu, hv, hw]
  change _ ≤ costConstant*B^84
  unfold costConstant
  nlinarith only [hfield',hcard',hseed',hguard',h1]

end PCP.Lang.ThreeColorBasePreflight
