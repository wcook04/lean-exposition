import PCP.Complexity.ThreeColorBaseCardinal
import PCP.Complexity.ThreeColorBaseSeed
import PCP.Complexity.NumericOuterCost

/-! Executing the four numeric outer branches in the concrete base-verifier workspace. -/

set_option maxRecDepth 1024

namespace PCP.Lang.ThreeColorBaseOuter

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters ThreeColorBaseSetup
  OuterBranch

def index : Kind → Fin 7
  | .color => 0
  | .valid => 1
  | .difference => 2
  | .proper => 3

def factor : Kind → ℕ
  | .color => 1
  | .valid | .difference => 2
  | .proper => 4

def resultPort (k : Kind) : Fin 400 := ⟨301+k.tag, by cases k <;> decide⟩

def sample (k : Kind) (N : ℕ) (bits : List Bool) :
    OuterBranch.Sample k (binaryDimension (exponent N))
      (size (exponent N)) (size (exponent N)) :=
  match k with
  | .color => ThreeColorBaseSeed.sample N bits 0
  | .valid => ThreeColorBaseSeed.sample N bits 1
  | .difference => ThreeColorBaseSeed.sample N bits 2
  | .proper => ThreeColorBaseSeed.sample N bits 3

theorem fieldCode_eq (a : ℕ) :
    fieldCode a = BinaryFieldCode.fieldEquiv (binaryDimension a) :=
  UniformDecode.fieldCodec_materialized (binaryDimension a)

def load (k : Kind) : Stmt 400 128 :=
  .seq (.assign 310 (.const (factor k)))
  (.seq (.assign 160 (.var 324)) (.seq (.assign 161 (.var 322))
  (.seq (.assign 162 (.var 325)) (.seq (.assign 163 (.var 327))
  (.seq (.assign 164 (.mul 310 322)) (.seq (.assign 165 (.var 328))
  (.seq (.assign 166 (.var 329)) (.seq (.assign 167 (.var 330))
  (.seq (.assign 168 (.var 331)) (.seq (.assign 169 (.var 332))
  (.seq (.assign 170 (.var 333))
  (.seq (.assign 171 (.var (ThreeColorBaseSeed.port (index k))))
  (.seq (.copy 120 64) (.seq (.copy 122 65) (.seq (.copy 121 66)
  (.seq (.copy 123 67) (.seq (.copy 102 68) (.copy 122 49))))))))))))))))))

def branch (k : Kind) : Stmt 400 128 :=
  ThreeColorBaseSetup.call (by decide) (by decide) (NumericOuter.program k)

/-- `124` retains the reversed concatenation of every completed branch trace. -/
def finish (k : Kind) : Stmt 400 128 :=
  .seq (.assign (resultPort k) (.var 144)) (.seq (.rev 49) (.revApp 49 124))

def program (k : Kind) : Stmt 400 128 := .seq (load k) (.seq (branch k) (finish k))

attribute [local irreducible] branch NumericOuter.program

theorem load_public (k : Kind) (N : ℕ) (qs : List ℕ) (bs : List Bool) (st : State 400 128)
    (hd : Data N st)
    (hc : ThreeColorBaseCardinal.Cardinal (binaryDimension (exponent N))
      (size (exponent N)) st)
    (hq : st.lists 123 = qs) (hb : st.lists 102 = bs.map Bool.toNat) :
    OuterSeed.Public (n := size (exponent N)) (m := size (exponent N)) k
      (nodes (exponent N)) (generator (exponent N)) qs bs
      (((load k).run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  have hdim : factor k*size (exponent N) = k.dimension (size (exponent N)) := by
    cases k <;> simp [factor, Kind.dimension] <;> omega
  constructor
  all_goals dsimp [load, Stmt.run, Expr.eval, Function.update, State.restrict]
  all_goals simp only [hd.width, hd.dimension, hd.card, hd.generatorCode, hd.modulus, hd.nodes,
    hd.empty, hc.vertices, hc.pairs, hc.proper, hc.inner, hc.affine, hc.cubic, hq, hb,
    hdim, fieldCode_eq]
  all_goals rfl

theorem load_seed (k : Kind) (N : ℕ) (bits : List Bool) (st : State 400 128)
    (hs : ThreeColorBaseSeed.Seeds N bits st) :
    ((load k).run st).1.regs 171 =
      ((seedCodec k (binaryDimension (exponent N)) (size (exponent N))
        (size (exponent N))).equiv (sample k N bits)).val := by
  have hp : ((load k).run st).1.regs 171 =
      st.regs (ThreeColorBaseSeed.port (index k)) := by
    cases k <;> simp [load, Stmt.run, Expr.eval, Function.update, index,
      ThreeColorBaseSeed.port]
  rw [hp, hs]
  cases k <;> rfl

theorem load_empty (k : Kind) (st : State 400 128) (he : st.lists 122 = []) :
    ((load k).run st).1.lists 49 = [] := by
  simp [load, Stmt.run, Expr.eval, Function.update, he]

theorem load_frame (k : Kind) (st : State 400 128) :
    ThreeColorBaseSetup.Frame st ((load k).run st).1 := by
  apply ThreeColorBaseSetup.frame_of_writes
  · simp [load, Stmt.regWrites]
  · simp [load, Stmt.listWrites]

theorem finish_run (k : Kind) (v : Bool) (qs : List ℕ) (st : State 400 128)
    (hv : st.regs 144 = v.toNat) (hq : st.lists 49 = qs.reverse) :
    ((finish k).run st).1.regs (resultPort k) = v.toNat ∧
      ((finish k).run st).1.lists 124 = qs.reverse ++ st.lists 124 := by
  simp [finish, Stmt.run, Expr.eval, Function.update, hv, hq]

theorem branch_run (k : Kind) (N : ℕ) (bits : List Bool) (qs : List ℕ) (bs : List Bool)
    (st : State 400 128) (hd : Data N st)
    (hc : ThreeColorBaseCardinal.Cardinal (binaryDimension (exponent N))
      (size (exponent N)) st) (hs : ThreeColorBaseSeed.Seeds N bits st)
    (hq : st.lists 123 = qs) (hb : st.lists 102 = bs.map Bool.toNat) :
    ((branch k).run ((load k).run st).1).1.regs 144 =
      (OuterBranch.verdict k (nodes (exponent N)) (generator (exponent N))
        (sample k N bits) qs bs).toNat ∧
    ((branch k).run ((load k).run st).1).1.lists 49 =
      (OuterBranch.queryCodes k (nodes (exponent N)) (generator (exponent N))
        (sample k N bits)).reverse := by
  have h := NumericOuter.program_run k (nodes (exponent N)) (generator (exponent N))
    (sample k N bits) qs bs _ (load_public k N qs bs st hd hc hq hb) (load_seed k N bits st hs)
  rw [← ThreeColorBaseSetup.call_result (by decide) (by decide) (NumericOuter.program k)
    ((load k).run st).1] at h
  have h' : (branch k |>.run ((load k).run st).1).1.regs 144 =
      (OuterBranch.verdict k (nodes (exponent N)) (generator (exponent N))
        (sample k N bits) qs bs).toNat ∧
      (branch k |>.run ((load k).run st).1).1.lists 49 =
        (OuterBranch.queryCodes k (nodes (exponent N)) (generator (exponent N))
          (sample k N bits)).reverse := by
    change ((ThreeColorBaseSetup.call (by decide) (by decide) (NumericOuter.program k)).run
      ((load k).run st).1).1.regs 144 = _ ∧
      ((ThreeColorBaseSetup.call (by decide) (by decide) (NumericOuter.program k)).run
      ((load k).run st).1).1.lists 49 = _ at h
    have he : (State.restrict (Fin.castLE (by decide : 180 ≤ 400))
        (Fin.castLE (by decide : 80 ≤ 128)) ((load k).run st).1).lists 49 = [] :=
      load_empty k st hd.empty
    rw [he, List.append_nil] at h
    unfold branch
    exact h
  exact h'

theorem program_run (k : Kind) (N : ℕ) (bits : List Bool) (qs : List ℕ) (bs : List Bool)
    (st : State 400 128) (hd : Data N st)
    (hc : ThreeColorBaseCardinal.Cardinal (binaryDimension (exponent N))
      (size (exponent N)) st) (hs : ThreeColorBaseSeed.Seeds N bits st)
    (hq : st.lists 123 = qs) (hb : st.lists 102 = bs.map Bool.toNat) :
    let s := sample k N bits
    let a := nodes (exponent N)
    let ζ := generator (exponent N)
    ((program k).run st).1.regs (resultPort k) =
      (OuterBranch.verdict k a ζ s qs bs).toNat ∧
    ((program k).run st).1.lists 124 =
      (OuterBranch.queryCodes k a ζ s).reverse ++ st.lists 124 := by
  have h' := branch_run k N bits qs bs st hd hc hs hq hb
  have h124 : ((branch k).run ((load k).run st).1).1.lists 124 = st.lists 124 := by
    unfold branch
    rw [ThreeColorBaseSetup.call_list (by decide) (by decide) (NumericOuter.program k)
      _ 124 (by decide)]
    exact (load_frame k st).lists 124 (by decide)
  have hf := finish_run k _ _ _ h'.1 h'.2
  rw [h124] at hf
  simp only [program, run_seq_fst]
  exact hf

theorem program_reg (k : Kind) (i : Fin 400) (hi : 300 ≤ i.val)
    (hne : i ≠ resultPort k) (hwork : i ≠ 310) (st : State 400 128) :
    ((program k).run st).1.regs i = st.regs i := by
  simp only [program, run_seq_fst]
  rw [run_regs_frame (finish k) i (by simp [finish, Stmt.regWrites, hne])]
  rw [show ((branch k).run ((load k).run st).1).1.regs i =
      ((load k).run st).1.regs i from by
    unfold branch
    exact ThreeColorBaseSetup.call_reg (by decide) (by decide) (NumericOuter.program k)
      _ i (by omega)]
  exact run_regs_frame (load k) i (by simp [load, Stmt.regWrites, hwork]; omega) st

theorem program_metadata (k : Kind) (i : Fin 400) (hi : 320 ≤ i.val)
    (st : State 400 128) : ((program k).run st).1.regs i = st.regs i :=
  program_reg k i (by omega) (by
    intro h
    have hv := congrArg Fin.val h
    cases k <;> norm_num [resultPort, Kind.tag] at hv <;> omega) (by omega) st

theorem program_list (k : Kind) (L : Fin 128) (hL : 100 ≤ L.val) (hne : L ≠ 124)
    (st : State 400 128) : ((program k).run st).1.lists L = st.lists L := by
  simp only [program, run_seq_fst]
  rw [run_lists_frame (finish k) L (by simp [finish, Stmt.listWrites, hne]; omega)]
  rw [show ((branch k).run ((load k).run st).1).1.lists L =
      ((load k).run st).1.lists L from by
    unfold branch
    exact ThreeColorBaseSetup.call_list (by decide) (by decide) (NumericOuter.program k)
      _ L (by omega)]
  exact (load_frame k st).lists L hL

theorem program_data (k : Kind) (N : ℕ) (st : State 400 128) (h : Data N st) :
    Data N ((program k).run st).1 := by
  constructor
  · exact (program_metadata k 320 (by decide) st).trans h.order
  · exact (program_metadata k 321 (by decide) st).trans h.exponent
  · exact (program_metadata k 322 (by decide) st).trans h.dimension
  · exact (program_metadata k 323 (by decide) st).trans h.volume
  · exact (program_metadata k 324 (by decide) st).trans h.width
  · exact (program_metadata k 325 (by decide) st).trans h.card
  · exact (program_metadata k 326 (by decide) st).trans h.cube
  · exact (program_metadata k 327 (by decide) st).trans h.generatorCode
  · exact (program_list k 120 (by decide) (by decide) st).trans h.modulus
  · exact (program_list k 121 (by decide) (by decide) st).trans h.nodes
  · exact (program_list k 122 (by decide) (by decide) st).trans h.empty

theorem program_cardinal (k : Kind) (t n : ℕ) (st : State 400 128)
    (h : ThreeColorBaseCardinal.Cardinal t n st) :
    ThreeColorBaseCardinal.Cardinal t n ((program k).run st).1 := by
  constructor
  · exact (program_metadata k 328 (by decide) st).trans h.vertices
  · exact (program_metadata k 329 (by decide) st).trans h.pairs
  · exact (program_metadata k 330 (by decide) st).trans h.proper
  · exact (program_metadata k 331 (by decide) st).trans h.inner
  · exact (program_metadata k 332 (by decide) st).trans h.affine
  · exact (program_metadata k 333 (by decide) st).trans h.cubic

theorem program_seeds (k : Kind) (N : ℕ) (bits : List Bool) (st : State 400 128)
    (h : ThreeColorBaseSeed.Seeds N bits st) :
    ThreeColorBaseSeed.Seeds N bits ((program k).run st).1 := by
  intro i
  exact (program_metadata k (ThreeColorBaseSeed.port i)
    (by simp [ThreeColorBaseSeed.port]; omega) st).trans (h i)

theorem program_sources (k : Kind) (x bits answers : List Bool) (st : State 400 128)
    (h : Sources x bits answers st) : Sources x bits answers ((program k).run st).1 :=
  ⟨(program_list k 100 (by decide) (by decide) st).trans h.graph,
    (program_list k 101 (by decide) (by decide) st).trans h.bits,
    (program_list k 102 (by decide) (by decide) st).trans h.answers,
    (program_list k 122 (by decide) (by decide) st).trans h.empty⟩

end PCP.Lang.ThreeColorBaseOuter
