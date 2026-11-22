import PCP.Complexity.ThreeColorBaseDerivedState

/-! # Preparing numeric derived-grid source ports from the base verifier's computed metadata -/

set_option maxRecDepth 1024

namespace PCP.Lang.ThreeColorBaseDerived

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters ThreeColorFullFieldSampling
  LocalCorrection DerivedGrid ThreeColorBaseSetup

def load (k : Certificate) : Stmt 400 128 :=
  .seq (.assign 310 (.const (factor k))) (
  .seq (.assign 240 (.var 324)) (
  .seq (.assign 241 (.var 322)) (
  .seq (.assign 243 (.var 325)) (
  .seq (.assign 244 (.var 327)) (
  .seq (.assign 250 (.var 328)) (
  .seq (.assign 251 (.var 329)) (
  .seq (.assign 252 (.var 330)) (
  .seq (.assign 253 (.var 331)) (
  .seq (.assign 254 (.var 332)) (
  .seq (.assign 255 (.var 333)) (
  .seq (.assign 256 (.mul 310 322)) (
  .seq (.assign 257 (.var (ThreeColorBaseSeed.port (index k)))) (
  .seq (.assign 279 (.var 322)) (
  .seq (.assign 280 (.var 322)) (
  .seq (.copy 122 103) (
  .seq (.copy 120 104) (
  .seq (.copy 121 105) (
  .seq (.copy 123 110) (
  .seq (.copy 102 111) (.copy 100 114))))))))))))))))))))

theorem load_input (k : Certificate) (N : ℕ) (bits : List Bool) (st : State 400 128)
    (hd : Data N st) (hs : ThreeColorBaseSeed.Seeds N bits st)
    (hv : Valid (ThreeColorBaseSeed.sample N bits)) :
    DerivedSeed.Input k (padDerived (sample k N bits hv)) (view ((load k).run st).1) := by
  have hdim : factor k * size (exponent N) = baseDimension k (size (exponent N)) := by
    cases k <;> simp [factor, baseDimension, two_mul]
  have hseed : st.regs (ThreeColorBaseSeed.port (index k)) =
      ((ThreeColorSeedIndex.derivedCodec (BinaryMaterializedField.coordinates
        (binaryDimension (exponent N))) (baseDimension k (size (exponent N)))
          (size (exponent N)) 4 3).equiv (rawSample k N bits)).val := by
    rw [hs]
    cases k <;> rfl
  constructor
  all_goals dsimp [load, Stmt.run, Expr.eval, Function.update, view, State.restrict, lists]
  all_goals simp only [hd.width, hd.dimension, hd.card, hd.empty, hdim]
  cases k <;> simpa [index, ThreeColorBaseSeed.port, sample, pad_unpadDerived] using hseed

theorem load_public (k : Certificate) (N : ℕ) (x : List Bool) (qs : List ℕ) (bs : List Bool)
    (st : State 400 128) (hd : Data N st)
    (hc : ThreeColorBaseCardinal.Cardinal (binaryDimension (exponent N))
      (size (exponent N)) st)
    (hx : st.lists 100 = x.map Bool.toNat) (hq : st.lists 123 = qs)
    (hb : st.lists 102 = bs.map Bool.toNat) :
    DerivedSeed.Public (n := size (exponent N)) (m := size (exponent N))
      (nodes (exponent N)) (generator (exponent N)) (size (exponent N)) x qs bs
      (view ((load k).run st).1) := by
  constructor
  all_goals dsimp [load, Stmt.run, Expr.eval, Function.update, view, State.restrict, lists]
  all_goals simp only [hd.generatorCode, hd.dimension, hd.modulus, hd.nodes, hc.vertices, hc.pairs,
    hc.proper, hc.inner, hc.affine, hc.cubic, hx, hq, hb,
    ← ProductionGrid.fieldEquiv_eq_fieldCode]
  all_goals rfl

theorem load_reg (k : Certificate) (st : State 400 128) (i : Fin 400)
    (hi : 300 ≤ i.val) (hne : i ≠ 310) : ((load k).run st).1.regs i = st.regs i := by
  apply run_regs_frame
  simp [load, Stmt.regWrites, hne]
  omega

theorem load_list (k : Certificate) (st : State 400 128) (L : Fin 128)
    (hL : 115 ≤ L.val ∨ (100 ≤ L.val ∧ L.val < 103)) :
    ((load k).run st).1.lists L = st.lists L := by
  apply run_lists_frame
  simp [load, Stmt.listWrites]
  omega

end PCP.Lang.ThreeColorBaseDerived
