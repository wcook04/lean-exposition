import PCP.Complexity.OuterBranchSite
import PCP.Complexity.HadamardRowBranchCost
import PCP.Complexity.StandardCorrectionCost
import PCP.Complexity.InterpolationBranchCost
import PCP.Complexity.LangEvaluationPointCost

/-!
# Protected stored inputs of an outer encoded-line branch

All arithmetic and row-test subroutines run in a fixed prefix of the state.
The immutable sample, field parameters and global histories are stored beyond
that prefix; each stage materializes its actual input context from these sources.
-/

namespace PCP.Lang.OuterBranch

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace

abbrev Field (t : ℕ) := BinaryMaterializedField.Element t
abbrev Sample (k : Kind) (t n m : ℕ) :=
  EncodedLineLowDegreeTest.Sample (Field t) (k.Coordinates n) m 4 t k.degree
abbrev Point (k : Kind) (t n : ℕ) := k.Coordinates n → Field t

def Kind.tag : Kind → ℕ
  | .color => 0
  | .valid => 1
  | .difference => 2
  | .proper => 3

def Kind.lineLocation {F : Type*} {n m : ℕ} (k : Kind)
    (uv : (k.Coordinates n → F) × (k.Coordinates n → F))
    (x : BinaryLocalCorrection.InnerPoint F m 4) : HadamardRow.Location F n m 4 1 :=
  match k with
  | .color => .colorLine uv x
  | .valid => .validLine uv x
  | .difference => .differenceLine uv x
  | .proper => .properLine uv x

theorem Kind.lineLocation_query {F : Type*} {n m t : ℕ} (k : Kind)
    (uv : (k.Coordinates n → F) × (k.Coordinates n → F))
    (x : BinaryLocalCorrection.InnerPoint F m 4) (w : Coefficients t 1) :
    (k.lineLocation uv x).query w = (k.line uv).query x w := by cases k <;> rfl

abbrev primarySeed {k : Kind} {t n m : ℕ} (s : Sample k t n m) := s.2.2.2.1
abbrev innerSeed {k : Kind} {t n m : ℕ} (s : Sample k t n m) := s.2.2.2.2
abbrev innerHadPoint {k : Kind} {t n m : ℕ} (s : Sample k t n m) := (innerSeed s).2.1.1
abbrev innerHadSeed {k : Kind} {t n m : ℕ} (s : Sample k t n m) := (innerSeed s).2.1.2
abbrev interpolationSeed {k : Kind} {t n m : ℕ} (s : Sample k t n m) := (innerSeed s).2.2

/-- The exact stored semantic sample. Every numerical field has a concrete production codec. -/
structure Context {t n m : ℕ} [NeZero t] (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80) : Prop where
  width : st.regs 120 = t
  degree : st.regs 121 = k.degree
  base : st.regs 122 = m
  card : st.regs 123 = 2^t
  root : st.regs 124 = (fieldEquiv t ζ).val
  param : st.regs 125 = (fieldEquiv t s.2.1).val
  coin : st.regs 126 = (innerSeed s).1.toNat
  interpParam : st.regs 127 = (fieldEquiv t (interpolationSeed s).1.2).val
  dimension : st.regs 128 = k.dimension n
  tag : st.regs 129 = k.tag
  vertices : st.regs 130 = (2^t)^n
  pairs : st.regs 131 = (2^t)^(n+n)
  proper : st.regs 132 = (2^t)^((n+n)+(n+n))
  inner : st.regs 133 = (2^t)^(4*m)
  affineLabels : st.regs 134 = 2^BooleanCoefficientIndex.dimension t 1
  cubicLabels : st.regs 135 = 2^BooleanCoefficientIndex.dimension t 3
  leftCode : st.regs 136 = k.pointCode (fieldEquiv t) s.1.1
  rightCode : st.regs 137 = k.pointCode (fieldEquiv t) s.1.2
  innerHadCode : st.regs 138 =
    (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 (innerHadPoint s)).val
  modulus : st.lists 40 = BinaryField.encode (BinaryWordMaterialization.modulus t)
  empty : st.lists 41 = []
  left : st.lists 42 = List.ofFn (fun i => (fieldEquiv t (k.vector s.1.1 i)).val)
  right : st.lists 43 = List.ofFn (fun i => (fieldEquiv t (k.vector s.1.2 i)).val)
  direction : st.lists 44 = List.ofFn (fun i =>
    (fieldEquiv t (StandardCorrection.vector s.2.2.1.1 i)).val)
  label : st.lists 45 = List.ofFn (fun i => (s.2.2.1.2 i).val)
  nodes : st.lists 46 = List.ofFn (fun i => (fieldEquiv t (a i)).val)
  history : st.lists 47 = qs
  answers : st.lists 48 = bs.map Bool.toNat
  primaryBase : st.lists 50 = BooleanCoefficientList.encode (primarySeed s).base
  primaryAuxiliary : st.lists 51 = BooleanCoefficientList.encode (primarySeed s).auxiliary
  primaryLinear : st.lists 52 = BooleanCoefficientList.encode (primarySeed s).linear
  primaryFactors : st.lists 53 = HadamardRow.factorCodes (primarySeed s)
  innerBase : st.lists 55 = BooleanCoefficientList.encode (innerHadSeed s).base
  innerAuxiliary : st.lists 56 = BooleanCoefficientList.encode (innerHadSeed s).auxiliary
  innerLinear : st.lists 57 = BooleanCoefficientList.encode (innerHadSeed s).linear
  innerFactors : st.lists 58 = HadamardRow.factorCodes (innerHadSeed s)
  interpLeft : st.lists 59 = List.ofFn (fun i =>
    (fieldEquiv t (StandardCorrection.vector (interpolationSeed s).1.1.1 i)).val)
  interpRight : st.lists 60 = List.ofFn (fun i =>
    (fieldEquiv t (StandardCorrection.vector (interpolationSeed s).1.1.2 i)).val)
  interpLabel : st.lists 61 = List.ofFn (fun i => ((interpolationSeed s).2 i).val)

/-- Sample and history sources are retained; list49 is the growing query accumulator. -/
structure Frame (st out : State 180 80) : Prop where
  regs : ∀ i : Fin 180, 120 ≤ i.val → i.val < 139 → out.regs i = st.regs i
  lists : ∀ i : Fin 80, 40 ≤ i.val → i.val < 62 → i ≠ 49 → out.lists i = st.lists i

theorem Frame.refl (st : State 180 80) : Frame st st :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem Frame.trans {st u v : State 180 80} (h : Frame st u) (g : Frame u v) : Frame st v :=
  ⟨fun i hi hj => (g.regs i hi hj).trans (h.regs i hi hj),
    fun i hi hj hk => (g.lists i hi hj hk).trans (h.lists i hi hj hk)⟩

theorem Context.of_frame {t n m : ℕ} [NeZero t] {k : Kind} {a : Fin 5 → Field t}
    {ζ : Field t} {s : Sample k t n m} {qs : List ℕ} {bs : List Bool} {st out : State 180 80}
    (hc : Context k a ζ s qs bs st) (hf : Frame st out) : Context k a ζ s qs bs out := by
  exact {
    width := (hf.regs 120 (by decide) (by decide)).trans hc.width
    degree := (hf.regs 121 (by decide) (by decide)).trans hc.degree
    base := (hf.regs 122 (by decide) (by decide)).trans hc.base
    card := (hf.regs 123 (by decide) (by decide)).trans hc.card
    root := (hf.regs 124 (by decide) (by decide)).trans hc.root
    param := (hf.regs 125 (by decide) (by decide)).trans hc.param
    coin := (hf.regs 126 (by decide) (by decide)).trans hc.coin
    interpParam := (hf.regs 127 (by decide) (by decide)).trans hc.interpParam
    dimension := (hf.regs 128 (by decide) (by decide)).trans hc.dimension
    tag := (hf.regs 129 (by decide) (by decide)).trans hc.tag
    vertices := (hf.regs 130 (by decide) (by decide)).trans hc.vertices
    pairs := (hf.regs 131 (by decide) (by decide)).trans hc.pairs
    proper := (hf.regs 132 (by decide) (by decide)).trans hc.proper
    inner := (hf.regs 133 (by decide) (by decide)).trans hc.inner
    affineLabels := (hf.regs 134 (by decide) (by decide)).trans hc.affineLabels
    cubicLabels := (hf.regs 135 (by decide) (by decide)).trans hc.cubicLabels
    leftCode := (hf.regs 136 (by decide) (by decide)).trans hc.leftCode
    rightCode := (hf.regs 137 (by decide) (by decide)).trans hc.rightCode
    innerHadCode := (hf.regs 138 (by decide) (by decide)).trans hc.innerHadCode
    modulus := (hf.lists 40 (by decide) (by decide) (by decide)).trans hc.modulus
    empty := (hf.lists 41 (by decide) (by decide) (by decide)).trans hc.empty
    left := (hf.lists 42 (by decide) (by decide) (by decide)).trans hc.left
    right := (hf.lists 43 (by decide) (by decide) (by decide)).trans hc.right
    direction := (hf.lists 44 (by decide) (by decide) (by decide)).trans hc.direction
    label := (hf.lists 45 (by decide) (by decide) (by decide)).trans hc.label
    nodes := (hf.lists 46 (by decide) (by decide) (by decide)).trans hc.nodes
    history := (hf.lists 47 (by decide) (by decide) (by decide)).trans hc.history
    answers := (hf.lists 48 (by decide) (by decide) (by decide)).trans hc.answers
    primaryBase := (hf.lists 50 (by decide) (by decide) (by decide)).trans hc.primaryBase
    primaryAuxiliary := (hf.lists 51 (by decide) (by decide) (by decide)).trans hc.primaryAuxiliary
    primaryLinear := (hf.lists 52 (by decide) (by decide) (by decide)).trans hc.primaryLinear
    primaryFactors := (hf.lists 53 (by decide) (by decide) (by decide)).trans hc.primaryFactors
    innerBase := (hf.lists 55 (by decide) (by decide) (by decide)).trans hc.innerBase
    innerAuxiliary := (hf.lists 56 (by decide) (by decide) (by decide)).trans hc.innerAuxiliary
    innerLinear := (hf.lists 57 (by decide) (by decide) (by decide)).trans hc.innerLinear
    innerFactors := (hf.lists 58 (by decide) (by decide) (by decide)).trans hc.innerFactors
    interpLeft := (hf.lists 59 (by decide) (by decide) (by decide)).trans hc.interpLeft
    interpRight := (hf.lists 60 (by decide) (by decide) (by decide)).trans hc.interpRight
    interpLabel := (hf.lists 61 (by decide) (by decide) (by decide)).trans hc.interpLabel
  }

def call {R Q : ℕ} (hR : R ≤ 120) (hQ : Q ≤ 40) (p : Stmt R Q) : Stmt 180 80 :=
  p.rename (Fin.castLE (hR.trans (by decide))) (Fin.castLE (hQ.trans (by decide)))

theorem call_result {R Q : ℕ} (hR : R ≤ 120) (hQ : Q ≤ 40) (p : Stmt R Q)
    (st : State 180 80) :
    (((call hR hQ p).run st).1.restrict (Fin.castLE (hR.trans (by decide)))
      (Fin.castLE (hQ.trans (by decide))), ((call hR hQ p).run st).2) =
    p.run (st.restrict (Fin.castLE (hR.trans (by decide)))
      (Fin.castLE (hQ.trans (by decide)))) :=
  p.run_rename _ _ (Fin.castLE_injective _) (Fin.castLE_injective _) st

theorem call_frame {R Q : ℕ} (hR : R ≤ 120) (hQ : Q ≤ 40) (p : Stmt R Q)
    (st : State 180 80) : Frame st ((call hR hQ p).run st).1 := by
  constructor
  · intro i hi _
    apply Stmt.run_rename_reg_outside
    intro j hj
    have := congrArg Fin.val hj
    simp only [Fin.val_castLE] at this
    omega
  · intro i hi _ _
    apply Stmt.run_rename_list_outside
    intro j hj
    have := congrArg Fin.val hj
    simp only [Fin.val_castLE] at this
    omega

theorem call_reg {R Q : ℕ} (hR : R ≤ 120) (hQ : Q ≤ 40) (p : Stmt R Q)
    (st : State 180 80) (i : Fin 180) (hi : 120 ≤ i.val) :
    ((call hR hQ p).run st).1.regs i = st.regs i := by
  apply Stmt.run_rename_reg_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_castLE] at this
  omega

theorem call_list {R Q : ℕ} (hR : R ≤ 120) (hQ : Q ≤ 40) (p : Stmt R Q)
    (st : State 180 80) (i : Fin 80) (hi : 40 ≤ i.val) :
    ((call hR hQ p).run st).1.lists i = st.lists i := by
  apply Stmt.run_rename_list_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_castLE] at this
  omega

theorem frame_of_writes (p : Stmt 180 80)
    (hr : ∀ i ∈ p.regWrites, i.val < 120 ∨ 139 ≤ i.val)
    (hl : ∀ i ∈ p.listWrites, i.val < 40 ∨ 62 ≤ i.val ∨ i = 49)
    (st : State 180 80) : Frame st (p.run st).1 := by
  constructor
  · intro i hi hj
    apply run_regs_frame
    intro h
    have := hr i h
    omega
  · intro i hi hj hk
    apply run_lists_frame
    intro h
    rcases hl i h with h | h | h
    · omega
    · omega
    · exact hk h

end PCP.Lang.OuterBranch
