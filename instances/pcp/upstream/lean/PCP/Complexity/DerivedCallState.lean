import PCP.Complexity.NumericCorrectionLang
import PCP.Complexity.DerivedPrimaryCost
import PCP.Complexity.DerivedGridVerdict

/-!
# Shared protected sources for the three parts of a derived-grid check

The primary read and the two numeric corrected certificate calls share one
physical history. Their immutable sources live beyond every callee workspace.
The two independent correction seeds and the fresh primary mask remain explicit.
-/

namespace PCP.Lang.DerivedCall

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t]

def payloadPort (i : Fin 10) : Fin 300 := ⟨260+i.val, by omega⟩

structure Context (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a b : k.Point t n) (w : Fin t → ZMod 2)
    (mask : Coefficients t 3) (weight : OuterBranch.Field t)
    (loc : HadamardRow.Location (OuterBranch.Field t) n m 4 3)
    (first second : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (st : State 300 112) : Prop where
  width : st.regs 240 = t
  base : st.regs 241 = m
  dimension : st.regs 242 = k.outer.dimension n
  card : st.regs 243 = 2^t
  root : st.regs 244 = (fieldEquiv t ζ).val
  weight : st.regs 245 = (fieldEquiv t weight).val
  firstCode : st.regs 246 = k.outer.pointCode (fieldEquiv t) a
  secondCode : st.regs 247 = k.outer.pointCode (fieldEquiv t) b
  firstSeed : st.regs 248 = ((callCodec (BinaryMaterializedField.coordinates t)
    (CorrectionContext.coordinateCodec k n) m 4).equiv (padCall first)).val
  secondSeed : st.regs 249 = ((callCodec (BinaryMaterializedField.coordinates t)
    (CorrectionContext.coordinateCodec k n) m 4).equiv (padCall second)).val
  vertices : st.regs 250 = (2^t)^n
  pairs : st.regs 251 = (2^t)^(n+n)
  proper : st.regs 252 = (2^t)^((n+n)+(n+n))
  inner : st.regs 253 = (2^t)^(4*m)
  affineLabels : st.regs 254 = 2^BooleanCoefficientIndex.dimension t 1
  cubicLabels : st.regs 255 = 2^BooleanCoefficientIndex.dimension t 3
  payload : ∀ i, st.regs (payloadPort i) = (loc.payload (t := t) (fieldEquiv t)) i
  empty : st.lists 100 = []
  modulus : st.lists 101 = BinaryField.encode (BinaryWordMaterialization.modulus t)
  nodes : st.lists 102 = List.ofFn (fun i => (fieldEquiv t (nodes i)).val)
  firstPoint : st.lists 103 = List.ofFn (fun i => (fieldEquiv t (k.outer.vector a i)).val)
  secondPoint : st.lists 104 = List.ofFn (fun i => (fieldEquiv t (k.outer.vector b i)).val)
  label : st.lists 105 = List.ofFn (fun i => (w i).val)
  mask : st.lists 106 = BooleanCoefficientList.encode mask
  history : st.lists 107 = qs
  answers : st.lists 108 = bs.map Bool.toNat

structure Frame (st out : State 300 112) : Prop where
  regs : ∀ i : Fin 300, 240 ≤ i.val → i.val < 270 → out.regs i = st.regs i
  lists : ∀ L : Fin 112, 100 ≤ L.val → L.val < 109 → out.lists L = st.lists L

theorem Frame.trans {st u v : State 300 112} (h : Frame st u) (g : Frame u v) : Frame st v :=
  ⟨fun i hi hj => (g.regs i hi hj).trans (h.regs i hi hj),
    fun L hL hU => (g.lists L hL hU).trans (h.lists L hL hU)⟩

theorem Context.of_frame {k : Certificate} {nodes : Fin 5 → OuterBranch.Field t}
    {ζ : OuterBranch.Field t} {a b : k.Point t n} {w : Fin t → ZMod 2}
    {mask : Coefficients t 3} {weight : OuterBranch.Field t}
    {loc : HadamardRow.Location (OuterBranch.Field t) n m 4 3}
    {first second : k.Seed t n m} {qs : List ℕ} {bs : List Bool} {st out : State 300 112}
    (h : Context k nodes ζ a b w mask weight loc first second qs bs st) (hf : Frame st out) :
    Context k nodes ζ a b w mask weight loc first second qs bs out := by
  constructor
  all_goals first
    | exact (hf.regs _ (by decide) (by decide)).trans h.width
    | exact (hf.regs _ (by decide) (by decide)).trans h.base
    | exact (hf.regs _ (by decide) (by decide)).trans h.dimension
    | exact (hf.regs _ (by decide) (by decide)).trans h.card
    | exact (hf.regs _ (by decide) (by decide)).trans h.root
    | exact (hf.regs _ (by decide) (by decide)).trans h.weight
    | exact (hf.regs _ (by decide) (by decide)).trans h.firstCode
    | exact (hf.regs _ (by decide) (by decide)).trans h.secondCode
    | exact (hf.regs _ (by decide) (by decide)).trans h.firstSeed
    | exact (hf.regs _ (by decide) (by decide)).trans h.secondSeed
    | exact (hf.regs _ (by decide) (by decide)).trans h.vertices
    | exact (hf.regs _ (by decide) (by decide)).trans h.pairs
    | exact (hf.regs _ (by decide) (by decide)).trans h.proper
    | exact (hf.regs _ (by decide) (by decide)).trans h.inner
    | exact (hf.regs _ (by decide) (by decide)).trans h.affineLabels
    | exact (hf.regs _ (by decide) (by decide)).trans h.cubicLabels
    | exact (hf.lists _ (by decide) (by decide)).trans h.empty
    | exact (hf.lists _ (by decide) (by decide)).trans h.modulus
    | exact (hf.lists _ (by decide) (by decide)).trans h.nodes
    | exact (hf.lists _ (by decide) (by decide)).trans h.firstPoint
    | exact (hf.lists _ (by decide) (by decide)).trans h.secondPoint
    | exact (hf.lists _ (by decide) (by decide)).trans h.label
    | exact (hf.lists _ (by decide) (by decide)).trans h.mask
    | exact (hf.lists _ (by decide) (by decide)).trans h.history
    | exact (hf.lists _ (by decide) (by decide)).trans h.answers
    | skip
  intro i
  exact (hf.regs (payloadPort i) (by simp only [payloadPort]; omega)
    (by simp only [payloadPort]; omega)).trans (h.payload i)

def call {R Q : ℕ} (hR : R ≤ 220) (hQ : Q ≤ 96) (p : Stmt R Q) : Stmt 300 112 :=
  p.rename (Fin.castLE (hR.trans (by decide))) (Fin.castLE (hQ.trans (by decide)))

def view {R Q : ℕ} (hR : R ≤ 300) (hQ : Q ≤ 112) (st : State 300 112) : State R Q :=
  st.restrict (Fin.castLE hR) (Fin.castLE hQ)

theorem call_result {R Q : ℕ} (hR : R ≤ 220) (hQ : Q ≤ 96) (p : Stmt R Q)
    (st : State 300 112) :
    (view (hR.trans (by decide)) (hQ.trans (by decide)) ((call hR hQ p).run st).1,
      ((call hR hQ p).run st).2) =
      p.run (view (hR.trans (by decide)) (hQ.trans (by decide)) st) :=
  p.run_rename _ _ (Fin.castLE_injective _) (Fin.castLE_injective _) st

theorem call_reg {R Q : ℕ} (hR : R ≤ 220) (hQ : Q ≤ 96) (p : Stmt R Q)
    (st : State 300 112) (i : Fin 300) (hi : 220 ≤ i.val) :
    ((call hR hQ p).run st).1.regs i = st.regs i := by
  apply Stmt.run_rename_reg_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_castLE] at this
  omega

theorem call_list {R Q : ℕ} (hR : R ≤ 220) (hQ : Q ≤ 96) (p : Stmt R Q)
    (st : State 300 112) (L : Fin 112) (hL : 96 ≤ L.val) :
    ((call hR hQ p).run st).1.lists L = st.lists L := by
  apply Stmt.run_rename_list_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_castLE] at this
  omega

theorem call_frame {R Q : ℕ} (hR : R ≤ 220) (hQ : Q ≤ 96) (p : Stmt R Q)
    (st : State 300 112) : Frame st ((call hR hQ p).run st).1 :=
  ⟨fun i hi _ => call_reg hR hQ p st i (by omega),
    fun L hL _ => call_list hR hQ p st L (by omega)⟩

theorem frame_of_writes (p : Stmt 300 112)
    (hr : ∀ i ∈ p.regWrites, i.val < 240 ∨ 270 ≤ i.val)
    (hl : ∀ L ∈ p.listWrites, L.val < 100 ∨ 109 ≤ L.val)
    (st : State 300 112) : Frame st (p.run st).1 := by
  constructor
  · intro i hi hj
    apply run_regs_frame
    intro h
    rcases hr i h with h | h <;> omega
  · intro L hL hU
    apply run_lists_frame
    intro h
    rcases hl L h with h | h <;> omega

end PCP.Lang.DerivedCall
