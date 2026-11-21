import PCP.Complexity.CanonicalResourceBounds
import PCP.Complexity.ThreeColorSeedBitsCost
import PCP.Complexity.ThreeColorNestedSeedSemantics
import PCP.Complexity.HadamardSeedCardinal

/-! Concrete public setup and protected storage for the seven-branch base verifier. -/

namespace PCP.Lang.ThreeColorBaseSetup

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters

/-- The small setup routines cannot reach the three source words or permanent metadata. -/
def call {R Q : ℕ} (hR : R ≤ 300) (hQ : Q ≤ 100) (p : Stmt R Q) : Stmt 400 128 :=
  p.rename (Fin.castLE (hR.trans (by decide))) (Fin.castLE (hQ.trans (by decide)))

theorem call_result {R Q : ℕ} (hR : R ≤ 300) (hQ : Q ≤ 100) (p : Stmt R Q)
    (st : State 400 128) :
    (((call hR hQ p).run st).1.restrict (Fin.castLE (hR.trans (by decide)))
      (Fin.castLE (hQ.trans (by decide))), ((call hR hQ p).run st).2) =
      p.run (st.restrict (Fin.castLE (hR.trans (by decide)))
        (Fin.castLE (hQ.trans (by decide)))) :=
  p.run_rename _ _ (Fin.castLE_injective _) (Fin.castLE_injective _) st

theorem call_reg {R Q : ℕ} (hR : R ≤ 300) (hQ : Q ≤ 100) (p : Stmt R Q)
    (st : State 400 128) (i : Fin 400) (hi : R ≤ i.val) :
    ((call hR hQ p).run st).1.regs i = st.regs i := by
  apply Stmt.run_rename_reg_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_castLE] at this
  omega

theorem call_list {R Q : ℕ} (hR : R ≤ 300) (hQ : Q ≤ 100) (p : Stmt R Q)
    (st : State 400 128) (L : Fin 128) (hL : Q ≤ L.val) :
    ((call hR hQ p).run st).1.lists L = st.lists L := by
  apply Stmt.run_rename_list_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_castLE] at this
  omega

/-- Public graph, random bits and answers are never consumed by setup. -/
structure Sources (x bits answers : List Bool) (st : State 400 128) : Prop where
  graph : st.lists 100 = x.map Bool.toNat
  bits : st.lists 101 = bits.map Bool.toNat
  answers : st.lists 102 = answers.map Bool.toNat
  empty : st.lists 122 = []

structure Data (N : ℕ) (st : State 400 128) : Prop where
  order : st.regs 320 = N
  exponent : st.regs 321 = ThreeColorParameterChoice.exponent N
  dimension : st.regs 322 = size (ThreeColorParameterChoice.exponent N)
  volume : st.regs 323 = ThreeColorParameterChoice.volume N
  width : st.regs 324 = binaryDimension (ThreeColorParameterChoice.exponent N)
  card : st.regs 325 = 2^binaryDimension (ThreeColorParameterChoice.exponent N)
  cube : st.regs 326 = (fieldCode (ThreeColorParameterChoice.exponent N)
    (cubeRoot (ThreeColorParameterChoice.exponent N))).val
  generatorCode : st.regs 327 = (fieldCode (ThreeColorParameterChoice.exponent N)
    (generator (ThreeColorParameterChoice.exponent N))).val
  modulus : st.lists 120 = BinaryField.encode
    (BinaryWordMaterialization.modulus (binaryDimension (ThreeColorParameterChoice.exponent N)))
  nodes : st.lists 121 = List.ofFn (fun i : Fin 5 =>
    (fieldCode (ThreeColorParameterChoice.exponent N)
      (ThreeColorParameters.nodes (ThreeColorParameterChoice.exponent N) i)).val)
  empty : st.lists 122 = []

structure Frame (st out : State 400 128) : Prop where
  regs : ∀ i : Fin 400, 320 ≤ i.val → i.val < 350 → out.regs i = st.regs i
  lists : ∀ L : Fin 128, 100 ≤ L.val → out.lists L = st.lists L

theorem Frame.trans {st u v : State 400 128} (h : Frame st u) (g : Frame u v) : Frame st v :=
  ⟨fun i hi hj => (g.regs i hi hj).trans (h.regs i hi hj),
    fun L hL => (g.lists L hL).trans (h.lists L hL)⟩

theorem Data.of_frame {N : ℕ} {st out : State 400 128} (h : Data N st)
    (hf : Frame st out) : Data N out := by
  constructor
  · exact (hf.regs 320 (by decide) (by decide)).trans h.order
  · exact (hf.regs 321 (by decide) (by decide)).trans h.exponent
  · exact (hf.regs 322 (by decide) (by decide)).trans h.dimension
  · exact (hf.regs 323 (by decide) (by decide)).trans h.volume
  · exact (hf.regs 324 (by decide) (by decide)).trans h.width
  · exact (hf.regs 325 (by decide) (by decide)).trans h.card
  · exact (hf.regs 326 (by decide) (by decide)).trans h.cube
  · exact (hf.regs 327 (by decide) (by decide)).trans h.generatorCode
  · exact (hf.lists 120 (by decide)).trans h.modulus
  · exact (hf.lists 121 (by decide)).trans h.nodes
  · exact (hf.lists 122 (by decide)).trans h.empty

theorem Sources.of_frame {x bits answers : List Bool} {st out : State 400 128}
    (h : Sources x bits answers st) (hf : Frame st out) : Sources x bits answers out :=
  ⟨(hf.lists 100 (by decide)).trans h.graph, (hf.lists 101 (by decide)).trans h.bits,
    (hf.lists 102 (by decide)).trans h.answers, (hf.lists 122 (by decide)).trans h.empty⟩

theorem frame_of_writes (p : Stmt 400 128)
    (hr : ∀ i ∈ p.regWrites, i.val < 320 ∨ 350 ≤ i.val)
    (hl : ∀ L ∈ p.listWrites, L.val < 100) (st : State 400 128) : Frame st (p.run st).1 := by
  constructor
  · intro i hi hj
    apply run_regs_frame
    intro hm
    have := hr i hm
    omega
  · intro L hL
    apply run_lists_frame
    intro hm
    have := hl L hm
    omega

theorem call_frame {R Q : ℕ} (hR : R ≤ 300) (hQ : Q ≤ 100) (p : Stmt R Q)
    (st : State 400 128) : Frame st ((call hR hQ p).run st).1 :=
  ⟨fun i hi _ => call_reg hR hQ p st i (by omega),
    fun L hL => call_list hR hQ p st L (by omega)⟩

def load : Stmt 400 128 := .seq (.copy 100 11) (.copy 122 7)
def fieldCall : Stmt 400 128 := call (by decide) (by decide) ThreeColorContext.setup

def save : Stmt 400 128 :=
  .seq (.assign 320 (.var 42)) (.seq (.assign 321 (.var 43))
  (.seq (.assign 322 (.var 44)) (.seq (.assign 323 (.var 45))
  (.seq (.assign 324 (.var 46)) (.seq (.assign 325 (.var 47))
  (.seq (.assign 326 (.var 48)) (.seq (.assign 327 (.var 49))
  (.seq (.copy 3 120) (.copy 14 121)))))))))

def field : Stmt 400 128 := .seq load (.seq fieldCall save)

attribute [local irreducible] fieldCall ThreeColorContext.setup

theorem fieldCall_run (x : List Bool) (st : State 400 128)
    (hx : st.lists 11 = x.map Bool.toNat) (he : st.lists 7 = []) :
    ThreeColorContext.Prepared (ThreeColorEncoding.vertexCount x)
      ((fieldCall.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  have h := ThreeColorContext.setup_run x
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) hx he
  rw [← call_result (by decide) (by decide) ThreeColorContext.setup st] at h
  simpa only [fieldCall] using h

theorem save_run (N : ℕ) (st : State 400 128)
    (hc : ThreeColorContext.Prepared N
      (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))))
    (he : st.lists 122 = []) : Data N (save.run st).1 := by
  rcases hc with ⟨⟨hN, ha, hn, hv, ht⟩, ⟨⟨_, _, hmod, _⟩, hq, hc, hf⟩, hnodes⟩
  change st.regs 42 = N at hN
  change st.regs 43 = _ at ha
  change st.regs 44 = _ at hn
  change st.regs 45 = _ at hv
  change st.regs 46 = _ at ht
  change st.regs 47 = _ at hq
  change st.regs 48 = _ at hc
  change st.regs 49 = _ at hf
  change st.lists 3 = _ at hmod
  change st.lists 14 = _ at hnodes
  constructor <;> simp [save, Stmt.run, Expr.eval, Function.update,
    hN, ha, hn, hv, ht, hq, hc, hf, hmod, hnodes, he]

theorem field_run (x : List Bool) (st : State 400 128)
    (hx : st.lists 100 = x.map Bool.toNat) (he : st.lists 122 = []) :
    Data (ThreeColorEncoding.vertexCount x) (field.run st).1 := by
  have hl : (load.run st).1.lists 11 = x.map Bool.toNat ∧
      (load.run st).1.lists 7 = [] ∧ (load.run st).1.lists 122 = [] := by
    simp [load, Stmt.run, Function.update, hx, he]
  have h := fieldCall_run x (load.run st).1 hl.1 hl.2.1
  have he' := (call_list (by decide) (by decide) ThreeColorContext.setup
    (load.run st).1 122 (by decide)).trans hl.2.2
  simp only [field, run_seq_fst]
  apply save_run _ _ h
  simpa only [fieldCall] using he'

theorem field_sources (x bits answers : List Bool) (st : State 400 128)
    (hs : Sources x bits answers st) : Sources x bits answers (field.run st).1 := by
  have hf (L : Fin 128) (hL : L = 100 ∨ L = 101 ∨ L = 102 ∨ L = 122) :
      (field.run st).1.lists L = st.lists L := by
    simp only [field, run_seq_fst]
    rw [run_lists_frame save L (by rcases hL with rfl | rfl | rfl | rfl <;> decide)]
    rw [show (fieldCall.run (load.run st).1).1.lists L = (load.run st).1.lists L from
      by simpa only [fieldCall] using
        call_list (by decide) (by decide) ThreeColorContext.setup (load.run st).1 L (by omega)]
    exact run_lists_frame load L (by rcases hL with rfl | rfl | rfl | rfl <;> decide) st
  exact ⟨(hf 100 (by simp)).trans hs.graph, (hf 101 (by simp)).trans hs.bits,
    (hf 102 (by simp)).trans hs.answers, (hf 122 (by simp)).trans hs.empty⟩

end PCP.Lang.ThreeColorBaseSetup
