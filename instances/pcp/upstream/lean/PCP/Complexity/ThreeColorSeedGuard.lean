import PCP.Complexity.ThreeColorSeedGuardDerived
import PCP.Complexity.InterpolationBranchPass
import PCP.Complexity.LangSeedMaterialization

/-! The four-zero acceptance guard for the actual seven-way finite sampler. -/

set_option maxRecDepth 1024

namespace PCP.Lang.ThreeColorSeedGuard

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling ThreeColorBaseSetup

/-- Extract the four raw field parameters, then test whether at least one is zero. -/
def parameters : Stmt 400 128 :=
  .seq (readDerived 1 354 360 361) (readDerived 2 355 362 363)

def finish : Stmt 400 128 := .seq (.assign 310 (.const 0))
  (.seq (.assign 311 (.eq 360 310)) (.seq (.assign 312 (.eq 361 310))
  (.seq (.assign 313 (.eq 362 310)) (.seq (.assign 314 (.eq 363 310))
  (.seq (.assign 315 (.add 311 312)) (.seq (.assign 316 (.add 313 314))
  (.seq (.assign 317 (.add 315 316))
    (.ite 317 (.assign 357 (.const 1)) (.assign 357 (.const 0))))))))))

def program : Stmt 400 128 := .seq parameters finish

attribute [local irreducible] readDerived parameters

variable {t n : ℕ} [NeZero t]

local notation "F" => BinaryMaterializedField.Element t
local notation "ρ" => BinaryMaterializedField.coordinates t

def SeedSources (s : RawSample F n n 4 t) (st : State 400 128) : Prop :=
  st.regs 354 = ((derivedCodec ρ n n 4 3).equiv (s 4)).val ∧
    st.regs 355 = ((derivedCodec ρ (n+n) n 4 3).equiv (s 5)).val

theorem parameters_run (s : RawSample F n n 4 t) (st : State 400 128)
    (hn : st.regs 322 = n) (ht : st.regs 324 = t) (he : st.lists 122 = [])
    (hs : SeedSources s st) :
    let out := (parameters.run st).1
    out.regs 360 = (BinaryFieldCode.fieldEquiv t (s 4).2.1.2.1.2.1).val ∧
    out.regs 361 = (BinaryFieldCode.fieldEquiv t (s 4).2.1.2.2.2.1).val ∧
    out.regs 362 = (BinaryFieldCode.fieldEquiv t (s 5).2.1.2.1.2.1).val ∧
    out.regs 363 = (BinaryFieldCode.fieldEquiv t (s 5).2.1.2.2.2.1).val := by
  have hv := readDerived_run_dim (n := n) ρ 1 n (one_mul n) (s 4) 354 360 361 st hn ht he
    (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hs.1
  have hun := (readDerived_reg 1 354 360 361 322 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) st).trans hn
  have hut := (readDerived_reg 1 354 360 361 324 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) st).trans ht
  have hue := (readDerived_list 1 354 360 361 122 (by decide) st).trans he
  have hus := (readDerived_reg 1 354 360 361 355 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) st).trans hs.2
  generalize hU : ((readDerived 1 354 360 361).run st).1 = u at *
  have hp := readDerived_run_dim (n := n) ρ 2 (n+n) (two_mul n) (s 5) 355 362 363 u hun hut hue
    (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hus
  have ha := (readDerived_reg 2 355 362 363 360 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) u).trans hv.1
  have hb := (readDerived_reg 2 355 362 363 361 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) u).trans hv.2
  simp only [parameters, run_seq_fst, hU]
  simp only [UniformDecode.fieldCodec_materialized] at ha hb hp
  exact ⟨ha, hb, hp⟩

omit [NeZero t] in
theorem finish_run (a b c d : ℕ) (st : State 400 128)
    (h0 : st.regs 360 = a) (h1 : st.regs 361 = b)
    (h2 : st.regs 362 = c) (h3 : st.regs 363 = d) :
    (finish.run st).1.regs 357 = (decide (a=0 ∨ b=0 ∨ c=0 ∨ d=0)).toNat := by
  by_cases ha : a=0 <;> by_cases hb : b=0 <;> by_cases hc : c=0 <;> by_cases hd : d=0 <;>
    simp [finish, Stmt.run, Expr.eval, Function.update, h0, h1, h2, h3, ha, hb, hc, hd]

open Classical in
/-- The guard is exactly the invalid whole-field seed predicate, before any physical read. -/
theorem program_run (s : RawSample F n n 4 t) (st : State 400 128)
    (hn : st.regs 322 = n) (ht : st.regs 324 = t) (he : st.lists 122 = [])
    (hs : SeedSources s st) :
    (program.run st).1.regs 357 = (decide (¬ Valid s)).toNat := by
  have h := parameters_run s st hn ht he hs
  have hf := finish_run _ _ _ _ (parameters.run st).1 h.1 h.2.1 h.2.2.1 h.2.2.2
  simpa only [program, run_seq_fst, InterpolationBranch.fieldCode_eq_zero,
    valid_iff, not_and_or, not_not] using hf

omit [NeZero t] in
theorem program_reg (i : Fin 400) (hi : 320 ≤ i.val) (hj : i.val < 357)
    (st : State 400 128) : (program.run st).1.regs i = st.regs i := by
  simp only [program, run_seq_fst]
  rw [run_regs_frame finish i (by simp [finish, Stmt.regWrites]; omega)]
  simp only [parameters, run_seq_fst]
  rw [readDerived_reg 2 355 362 363 i hi (by omega) (by omega) (by omega) (by omega) (by omega)]
  exact readDerived_reg 1 354 360 361 i hi (by omega) (by omega) (by omega) (by omega) (by omega) st

omit [NeZero t] in
theorem program_list (L : Fin 128) (hL : 100 ≤ L.val) (st : State 400 128) :
    (program.run st).1.lists L = st.lists L := by
  simp only [program, run_seq_fst]
  rw [run_lists_frame finish L (by simp [finish, Stmt.listWrites])]
  simp only [parameters, run_seq_fst, readDerived_list _ _ _ _ L hL]

omit [NeZero t] in
theorem program_frame (st : State 400 128) : ThreeColorBaseSetup.Frame st (program.run st).1 :=
  ⟨fun i hi hj => program_reg i hi (by omega) st, fun L hL => program_list L hL st⟩

open Classical in
/-- Specialization to the canonical bit-list seed computed by the base setup. -/
theorem canonical_run (N : ℕ) (bits : List Bool) (st : State 400 128)
    (hd : ThreeColorBaseSetup.Data N st) (hs : ThreeColorBaseSeed.Seeds N bits st) :
    (program.run st).1.regs 357 =
      (decide (¬ Valid (ThreeColorBaseSeed.sample N bits))).toNat := by
  apply program_run _ st hd.dimension hd.width hd.empty
  exact ⟨hs 4, hs 5⟩

end PCP.Lang.ThreeColorSeedGuard
