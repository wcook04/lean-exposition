import PCP.Complexity.OuterSeedLang

/-! # The numeric outer materializer preserves the accumulated physical queries -/

namespace PCP.Lang.OuterSeed

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode OuterBranch

private theorem call_not_writes49 {R Q : ℕ} (hR : R ≤ 140) (hQ : Q ≤ 44) (p : Stmt R Q) :
    (49 : Fin 80) ∉ (call hR hQ p).listWrites := by
  simp only [call, Stmt.listWrites_rename, List.mem_map]
  rintro ⟨i, _, hi⟩
  have he := congrArg Fin.val hi
  simp only [Fin.val_castLE] at he
  have := i.isLt
  omega

theorem program_queries (k : Kind) (st : State 180 80) :
    ((program k).run st).1.lists 49 = st.lists 49 := by
  apply run_lists_frame
  simp only [program, unpack, decode, decoder, prepare, parse, inner, loadInner,
    innerCall, saveInner, materialize, hadamard, hadPrepare, hadCall, hadSave,
    point, pointPrepare, direction, directionPrepare, bits, bitPrepare, uniform,
    finalize, Stmt.listWrites, List.mem_append, List.mem_singleton, List.not_mem_nil,
    or_false, false_or, not_or, call_not_writes49]
  decide

end PCP.Lang.OuterSeed
