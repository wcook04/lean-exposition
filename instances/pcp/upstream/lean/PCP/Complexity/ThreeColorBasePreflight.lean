import PCP.Complexity.ThreeColorBaseSetupCost
import PCP.Complexity.ThreeColorBaseCardinalCost
import PCP.Complexity.ThreeColorBaseSeedCost
import PCP.Complexity.ThreeColorSeedGuard

/-! # Complete public setup, table cardinalities, sampler decoding, and zero guard -/

namespace PCP.Lang.ThreeColorBasePreflight

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters ThreeColorBaseSetup
  CanonicalResourceBounds ThreeColorBaseCardinal

def program : Stmt 400 128 := .seq ThreeColorBaseSetup.field
  (.seq ThreeColorBaseCardinal.program
    (.seq ThreeColorBaseSeed.program ThreeColorSeedGuard.program))

open Classical in
structure Ready (x bits answers : List Bool) (st : State 400 128) : Prop where
  data : Data (ThreeColorEncoding.vertexCount x) st
  cardinal : Cardinal (fieldWidth (ThreeColorEncoding.vertexCount x))
    (dimension (ThreeColorEncoding.vertexCount x)) st
  seeds : ThreeColorBaseSeed.Seeds (ThreeColorEncoding.vertexCount x) bits st
  sources : Sources x bits answers st
  guard : st.regs 357 =
    (decide (¬ ThreeColorFullFieldSampling.Valid
      (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))).toNat

theorem cardinal_of_frame {t n : ℕ} {st out : State 400 128}
    (h : Cardinal t n st) (hf : ThreeColorBaseSetup.Frame st out) : Cardinal t n out :=
  ⟨(hf.regs 328 (by decide) (by decide)).trans h.vertices,
    (hf.regs 329 (by decide) (by decide)).trans h.pairs,
    (hf.regs 330 (by decide) (by decide)).trans h.proper,
    (hf.regs 331 (by decide) (by decide)).trans h.inner,
    (hf.regs 332 (by decide) (by decide)).trans h.affine,
    (hf.regs 333 (by decide) (by decide)).trans h.cubic⟩

theorem guard_seeds (N : ℕ) (bits : List Bool) (st : State 400 128)
    (h : ThreeColorBaseSeed.Seeds N bits st) :
    ThreeColorBaseSeed.Seeds N bits (ThreeColorSeedGuard.program.run st).1 := by
  intro i
  rw [ThreeColorSeedGuard.program_reg (ThreeColorBaseSeed.port i)
    (by simp only [ThreeColorBaseSeed.port]; omega)
    (by simp only [ThreeColorBaseSeed.port]; omega)]
  exact h i

attribute [local irreducible] ThreeColorBaseSetup.field ThreeColorBaseCardinal.program
  ThreeColorBaseSeed.program ThreeColorSeedGuard.program

theorem program_run (x bits answers : List Bool) (st : State 400 128)
    (hs : Sources x bits answers st) : Ready x bits answers (program.run st).1 := by
  have hd := field_run x st hs.graph hs.empty
  have hsrc := field_sources x bits answers st hs
  generalize hu : (ThreeColorBaseSetup.field.run st).1 = u at *
  have hc := ThreeColorBaseCardinal.program_run _ _ u hd.width hd.dimension hd.empty
  have hd' := ThreeColorBaseCardinal.program_data _ u hd
  have hsrc' := ThreeColorBaseCardinal.program_sources x bits answers u hsrc
  generalize hv : (ThreeColorBaseCardinal.program.run u).1 = v at *
  have hseed := ThreeColorBaseSeed.program_run _ bits v hd' hsrc'.bits
  have hf := ThreeColorBaseSeed.program_frame v
  have hd'' := hd'.of_frame hf
  have hc' := cardinal_of_frame hc hf
  have hsrc'' := hsrc'.of_frame hf
  generalize hw : (ThreeColorBaseSeed.program.run v).1 = w at *
  have hguard := ThreeColorSeedGuard.canonical_run _ bits w hd'' hseed
  have hgf := ThreeColorSeedGuard.program_frame w
  have hseed' := guard_seeds _ bits w hseed
  simp only [program, run_seq_fst, hu, hv, hw]
  exact ⟨hd''.of_frame hgf, cardinal_of_frame hc' hgf, hseed', hsrc''.of_frame hgf, hguard⟩

end PCP.Lang.ThreeColorBasePreflight
