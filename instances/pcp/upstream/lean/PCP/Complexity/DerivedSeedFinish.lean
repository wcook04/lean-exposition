import PCP.Complexity.DerivedSeedContext
import PCP.Complexity.DerivedSeedCodec

/-! # Joining both recovery vectors, numeric point codes and the public edge computation -/

namespace PCP.Lang.DerivedSeed

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection DerivedGrid

variable {t n m : ℕ} [NeZero t]

set_option maxRecDepth 1024

def encodePoints : Stmt 300 112 :=
  .seq points (.seq (encode 103 246) (encode 104 247))

theorem encodePoints_reg (st : State 300 112) (i : Fin 300) (hi : 220 ≤ i.val)
    (h6 : i ≠ 246) (h7 : i ≠ 247) : (encodePoints.run st).1.regs i = st.regs i := by
  simp only [encodePoints, run_seq_fst, encode_reg _ _ i hi h7,
    encode_reg _ _ i hi h6, points_reg _ i hi]

theorem encodePoints_list (st : State 300 112) (L : Fin 112) (hL : 96 ≤ L.val)
    (h3 : L ≠ 103) (h4 : L ≠ 104) : (encodePoints.run st).1.lists L = st.lists L := by
  simp only [encodePoints, run_seq_fst, encode_list _ L _ hL,
    points_list _ L hL h3 h4]

attribute [local irreducible] points encode edge payload

theorem encodePoints_run (k : Certificate) (h : ℕ) (hh : h ≤ 2 ^ t)
    (s : DerivedGrid.Sample k t n m) (st : State 300 112)
    (ht : st.regs 240 = t) (hq : st.regs 243 = 2 ^ t) (hcount : st.regs 279 = h)
    (hmod : st.lists 101 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 100 = [])
    (hx : st.lists 109 = List.ofFn (fun i => (fieldEquiv t (s.1 i)).val)) :
    let H := FiniteAlphabetIndex.alphabet (fieldEquiv t) hh
    (encodePoints.run st).1.regs 246 = k.outer.pointCode (fieldEquiv t) (firstPoint k s) ∧
    (encodePoints.run st).1.regs 247 = k.outer.pointCode (fieldEquiv t) (secondPoint k H s) ∧
    (encodePoints.run st).1.lists 103 =
      List.ofFn (fun i => (fieldEquiv t (k.outer.vector (firstPoint k s) i)).val) ∧
    (encodePoints.run st).1.lists 104 =
      List.ofFn (fun i => (fieldEquiv t (k.outer.vector (secondPoint k H s) i)).val) := by
  have hp := points_run k h hh s st ht hcount hmod he hx
  have hpq := (points_reg st 243 (by decide)).trans hq
  generalize hu : (points.run st).1 = u at *
  have ha := encode_run k (firstPoint k s) 103 246 u hpq hp.1
  have haq := (encode_reg 103 246 243 (by decide) (by decide) u).trans hpq
  have hap := (encode_list 103 104 246 (by decide) u).trans hp.2
  have hap1 := (encode_list 103 103 246 (by decide) u).trans hp.1
  generalize hv : ((encode 103 246).run u).1 = v at *
  have hb := encode_run k (secondPoint k (FiniteAlphabetIndex.alphabet (fieldEquiv t) hh) s)
    104 247 v haq hap
  have hba := (encode_reg 104 247 246 (by decide) (by decide) v).trans ha
  simp only [encodePoints, run_seq_fst, hu, hv]
  exact ⟨hba, hb, (encode_list 104 103 247 (by decide) v).trans
    hap1,
    (encode_list 104 104 247 (by decide) v).trans hap⟩

def computed (k : Certificate) : Stmt 300 112 := .seq encodePoints (edge k)

theorem computed_reg (k : Certificate) (st : State 300 112) (i : Fin 300)
    (hi : 220 ≤ i.val) (h5 : i ≠ 245) (h6 : i ≠ 246) (h7 : i ≠ 247) :
    ((computed k).run st).1.regs i = st.regs i := by
  simp only [computed, run_seq_fst, edge_reg k _ i hi h5,
    encodePoints_reg _ i hi h6 h7]

theorem computed_list (k : Certificate) (st : State 300 112) (L : Fin 112)
    (hL : 96 ≤ L.val) (h3 : L ≠ 103) (h4 : L ≠ 104) :
    ((computed k).run st).1.lists L = st.lists L := by
  simp only [computed, run_seq_fst, edge_list k _ L hL, encodePoints_list _ L hL h3 h4]

theorem Input.computed {k : Certificate} {s : DerivedGrid.RawSample k t n m}
    {st : State 300 112} (hi : Input k s st) : Input k s ((computed k).run st).1 := by
  constructor
  · exact (computed_reg k st 240 (by decide) (by decide) (by decide) (by decide)).trans hi.width
  · exact (computed_reg k st 241 (by decide) (by decide) (by decide) (by decide)).trans hi.base
  · exact (computed_reg k st 256 (by decide) (by decide) (by decide) (by decide)).trans hi.dimension
  · exact (computed_reg k st 257 (by decide) (by decide) (by decide) (by decide)).trans hi.seed
  · exact (computed_reg k st 243 (by decide) (by decide) (by decide) (by decide)).trans hi.card
  · exact (computed_list k st 100 (by decide) (by decide) (by decide)).trans hi.empty

theorem Data.computed {k : Certificate} {s : DerivedGrid.RawSample k t n m}
    {st : State 300 112} (hd : Data k s st) : Data k s ((computed k).run st).1 := by
  constructor
  · exact (computed_reg k st 277 (by decide) (by decide) (by decide) (by decide)).trans hd.mask
  · exact (computed_reg k st 248 (by decide) (by decide) (by decide) (by decide)).trans hd.first
  · exact (computed_reg k st 249 (by decide) (by decide) (by decide) (by decide)).trans hd.second
  · exact (computed_reg k st 258 (by decide) (by decide) (by decide) (by decide)).trans hd.label
  · exact (computed_reg k st 259 (by decide) (by decide) (by decide) (by decide)).trans hd.point

theorem Public.computed {k : Certificate} {nodes : Fin 5 → OuterBranch.Field t}
    {ζ : OuterBranch.Field t} {h : ℕ} {x : List Bool} {qs : List ℕ} {bs : List Bool}
    {st : State 300 112} (hp : Public (n := n) (m := m) nodes ζ h x qs bs st) :
    Public (n := n) (m := m) nodes ζ h x qs bs ((computed k).run st).1 := by
  apply hp.of_eq
  · intro i hi
    apply computed_reg <;> simp [publicRegs] at hi <;> omega
  · intro L hL
    apply computed_list <;> simp [publicLists] at hL <;> omega

theorem computed_run (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (h : ℕ) (hh : h ≤ 2 ^ t) (x : List Bool)
    (s : DerivedGrid.Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 300 112)
    (hi : Input k (padDerived s) st) (hp : Public (n := n) (m := m) nodes ζ h x qs bs st)
    (hx : st.lists 109 = List.ofFn (fun i => (fieldEquiv t (s.1 i)).val)) :
    let H := FiniteAlphabetIndex.alphabet (fieldEquiv t) hh
    ((computed k).run st).1.regs 246 = k.outer.pointCode (fieldEquiv t) (firstPoint k s) ∧
    ((computed k).run st).1.regs 247 = k.outer.pointCode (fieldEquiv t) (secondPoint k H s) ∧
    ((computed k).run st).1.lists 103 =
      List.ofFn (fun i => (fieldEquiv t (k.outer.vector (firstPoint k s) i)).val) ∧
    ((computed k).run st).1.lists 104 =
      List.ofFn (fun i => (fieldEquiv t (k.outer.vector (secondPoint k H s) i)).val) ∧
    ((computed k).run st).1.regs 245 = (fieldEquiv t (weight k h hh x s)).val := by
  have hc := encodePoints_run k h hh s st hi.width hi.card hp.count hp.modulus hi.empty hx
  have hwidth := (encodePoints_reg st 240 (by decide) (by decide) (by decide)).trans hi.width
  have hcount := (encodePoints_reg st 279 (by decide) (by decide) (by decide)).trans hp.count
  have hn := (encodePoints_reg st 280 (by decide) (by decide) (by decide)).trans hp.dimension
  have hmod := (encodePoints_list st 101 (by decide) (by decide) (by decide)).trans hp.modulus
  have hempty := (encodePoints_list st 100 (by decide) (by decide) (by decide)).trans hi.empty
  have hpoint := (encodePoints_list st 109 (by decide) (by decide) (by decide)).trans hx
  have hgraph := (encodePoints_list st 111 (by decide) (by decide) (by decide)).trans hp.graph
  generalize hu : (encodePoints.run st).1 = u at *
  have he := edge_run k h hh x s u hwidth hcount hn hmod hempty hpoint hgraph
  simp only [computed, run_seq_fst, hu]
  exact ⟨(edge_reg k u 246 (by decide) (by decide)).trans hc.1,
    (edge_reg k u 247 (by decide) (by decide)).trans hc.2.1,
    (edge_list k u 103 (by decide)).trans hc.2.2.1,
    (edge_list k u 104 (by decide)).trans hc.2.2.2, he⟩

def finish (k : Certificate) : Stmt 300 112 := .seq (computed k) (payload k)

/-- Exact complete checker inputs, computed from decoded words and public field metadata. -/
theorem finish_run (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (h : ℕ) (hh : h ≤ 2 ^ t) (x : List Bool)
    (s : DerivedGrid.Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 300 112)
    (hi : Input k (padDerived s) st) (hd : Data k (padDerived s) st)
    (hp : Public (n := n) (m := m) nodes ζ h x qs bs st)
    (hx : st.lists 109 = List.ofFn (fun i => (fieldEquiv t (s.1 i)).val))
    (hw : st.lists 105 = List.ofFn (fun i => (s.2.1.1 i).val))
    (hm : st.lists 106 = BooleanCoefficientList.encode s.2.2) :
    DerivedCall.Context k nodes ζ (firstPoint k s)
      (secondPoint k (FiniteAlphabetIndex.alphabet (fieldEquiv t) hh) s)
      s.2.1.1 s.2.2 (weight k h hh x s) (primaryLocation k s.1)
      (firstSeed k s) (secondSeed k s) qs bs ((finish k).run st).1 := by
  have hc := computed_run k nodes ζ h hh x s qs bs st hi hp hx
  have hu := hi.computed
  have hd' := hd.computed
  have hp' := hp.computed (k := k)
  have hw' := (computed_list k st 105 (by decide) (by decide) (by decide)).trans hw
  have hm' := (computed_list k st 106 (by decide) (by decide) (by decide)).trans hm
  generalize hv : ((computed k).run st).1 = v at *
  have hf := payload_run k (padDerived s) nodes ζ h x qs bs v hu hd' hp'
  simp only [finish, run_seq_fst, hv]
  constructor
  · exact (payload_reg k v 240 (by decide) (by decide)).trans (hu.width)
  · exact (payload_reg k v 241 (by decide) (by decide)).trans (hu.base)
  · exact hf.1
  · exact (payload_reg k v 243 (by decide) (by decide)).trans (hu.card)
  · exact (payload_reg k v 244 (by decide) (by decide)).trans (hp'.root)
  · exact (payload_reg k v 245 (by decide) (by decide)).trans (hc.2.2.2.2)
  · exact (payload_reg k v 246 (by decide) (by decide)).trans (hc.1)
  · exact (payload_reg k v 247 (by decide) (by decide)).trans (hc.2.1)
  · exact (payload_reg k v 248 (by decide) (by decide)).trans
      (hd'.first.trans (firstSeed_code k s))
  · exact (payload_reg k v 249 (by decide) (by decide)).trans
      (hd'.second.trans (secondSeed_code k s))
  · exact (payload_reg k v 250 (by decide) (by decide)).trans (hp'.vertices)
  · exact (payload_reg k v 251 (by decide) (by decide)).trans (hp'.pairs)
  · exact (payload_reg k v 252 (by decide) (by decide)).trans (hp'.proper)
  · exact (payload_reg k v 253 (by decide) (by decide)).trans (hp'.inner)
  · exact (payload_reg k v 254 (by decide) (by decide)).trans (hp'.affineLabels)
  · exact (payload_reg k v 255 (by decide) (by decide)).trans (hp'.cubicLabels)
  · exact hf.2
  · exact (payload_list k v 100).trans (hu.empty)
  · exact (payload_list k v 101).trans (hp'.modulus)
  · exact (payload_list k v 102).trans (hp'.nodes)
  · exact (payload_list k v 103).trans (hc.2.2.1)
  · exact (payload_list k v 104).trans (hc.2.2.2.1)
  · exact (payload_list k v 105).trans (hw')
  · exact (payload_list k v 106).trans (hm')
  · exact (payload_list k v 107).trans (hp'.history)
  · exact (payload_list k v 108).trans (hp'.answers)

end PCP.Lang.DerivedSeed
