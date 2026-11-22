import PCP.Complexity.DerivedSeedWords

/-! # Materializing all three explicit words of the raw derived seed -/

namespace PCP.Lang.DerivedSeed

open PCP.Algebraic ThreeColorSeedIndex LocalCorrection DerivedGrid BinaryFieldCode

variable {t n m : ℕ} [NeZero t]

def words : Stmt 300 112 := .seq (vector 259 256 (.var 243) 109)
  (.seq (vector 258 240 (.const 2) 105) mask)

theorem words_reg (st : State 300 112) (i : Fin 300) (hi : 220 ≤ i.val) :
    (words.run st).1.regs i = st.regs i := by
  simp only [words, run_seq_fst, mask_reg _ i hi,
    vector_reg _ _ i _ _ hi]

theorem words_list (st : State 300 112) (L : Fin 112) (hL : 96 ≤ L.val)
    (h5 : L ≠ 105) (h6 : L ≠ 106) (h9 : L ≠ 109) :
    (words.run st).1.lists L = st.lists L := by
  simp only [words, run_seq_fst, mask_list _ L hL h6,
    vector_list _ _ _ _ L hL h5, vector_list _ _ _ _ L hL h9]

theorem Input.of_regs {k : Certificate} {s : DerivedGrid.RawSample k t n m}
    {st out : State 300 112} (h : Input k s st)
    (hr : ∀ i : Fin 300, 220 ≤ i.val → out.regs i = st.regs i)
    (he : out.lists 100 = st.lists 100) : Input k s out :=
  ⟨(hr 240 (by decide)).trans h.width, (hr 241 (by decide)).trans h.base,
    (hr 256 (by decide)).trans h.dimension, (hr 257 (by decide)).trans h.seed,
    (hr 243 (by decide)).trans h.card, he.trans h.empty⟩

theorem Data.of_regs {k : Certificate} {s : DerivedGrid.RawSample k t n m}
    {st out : State 300 112} (h : Data k s st)
    (hr : ∀ i : Fin 300, 220 ≤ i.val → out.regs i = st.regs i) : Data k s out :=
  ⟨(hr 277 (by decide)).trans h.mask, (hr 248 (by decide)).trans h.first,
    (hr 249 (by decide)).trans h.second, (hr 258 (by decide)).trans h.label,
    (hr 259 (by decide)).trans h.point⟩

attribute [local irreducible] vector mask

theorem words_run (k : Certificate) (s : DerivedGrid.RawSample k t n m) (st : State 300 112)
    (hi : Input k s st) (hd : Data k s st) :
    (words.run st).1.lists 109 = List.ofFn (fun i => (fieldEquiv t (s.1 i)).val) ∧
    (words.run st).1.lists 105 = List.ofFn (fun i => (s.2.1.1 i).val) ∧
    (words.run st).1.lists 106 = BooleanCoefficientList.encode s.2.2 ∧
    Input k s (words.run st).1 ∧ Data k s (words.run st).1 := by
  have hp := vector_field (Codec.fin (baseDimension k n)) s.1 259 256 109 (by decide)
    st hd.point hi.dimension hi.card hi.empty
  have fp := vector_reg 259 256
  have up := hi.of_regs (fun i h => fp i (.var 243) 109 h st)
    (vector_list 259 256 (.var 243) 109 100 (by decide) (by decide) st)
  have dp := hd.of_regs (fun i h => fp i (.var 243) 109 h st)
  generalize hu : ((vector 259 256 (.var 243) 109).run st).1 = u at *
  have hb := vector_bits s.2.1.1 258 105 u dp.label up.width up.empty
  have fb := vector_list 258 240 (.const 2) 105 109 (by decide) (by decide) u
  have ub := up.of_regs (fun i h => vector_reg 258 240 i (.const 2) 105 h u)
    (vector_list 258 240 (.const 2) 105 100 (by decide) (by decide) u)
  have db := dp.of_regs (fun i h => vector_reg 258 240 i (.const 2) 105 h u)
  generalize hv : ((vector 258 240 (.const 2) 105).run u).1 = v at *
  have hm := mask_run s.2.2 v ub.width ub.empty db.mask
  have fm1 := mask_list v 109 (by decide) (by decide)
  have fm2 := mask_list v 105 (by decide) (by decide)
  refine ⟨?_, ?_, ?_, hi.of_regs (words_reg st)
    (words_list st 100 (by decide) (by decide) (by decide) (by decide)),
    hd.of_regs (words_reg st)⟩
  · calc _ = u.lists 109 := by simp only [words, run_seq_fst, hu, hv, fm1, fb]
         _ = _ := hp
  · simpa only [words, run_seq_fst, hu, hv, fm2] using hb
  · simpa only [words, run_seq_fst, hu, hv] using hm

def materialize : Stmt 300 112 := .seq split words

theorem materialize_run (k : Certificate) (s : DerivedGrid.RawSample k t n m)
    (st : State 300 112) (hi : Input k s st) :
    (materialize.run st).1.lists 109 = List.ofFn (fun i => (fieldEquiv t (s.1 i)).val) ∧
    (materialize.run st).1.lists 105 = List.ofFn (fun i => (s.2.1.1 i).val) ∧
    (materialize.run st).1.lists 106 = BooleanCoefficientList.encode s.2.2 ∧
    Input k s (materialize.run st).1 ∧ Data k s (materialize.run st).1 :=
  words_run k s _ hi.split (split_run k s st hi)

theorem materialize_reg (st : State 300 112) (i : Fin 300) (hi : 240 ≤ i.val)
    (h1 : i ≠ 248) (h2 : i ≠ 249) (h3 : i ≠ 258) (h4 : i ≠ 259)
    (h5 : i ≠ 277) (h6 : i ≠ 278) : (materialize.run st).1.regs i = st.regs i := by
  simp only [materialize, run_seq_fst, words_reg _ i (by omega)]
  exact split_reg st i hi h1 h2 h3 h4 h5 h6

theorem materialize_list (st : State 300 112) (L : Fin 112) (hL : 96 ≤ L.val)
    (h5 : L ≠ 105) (h6 : L ≠ 106) (h9 : L ≠ 109) :
    (materialize.run st).1.lists L = st.lists L := by
  simp only [materialize, run_seq_fst, words_list _ L hL h5 h6 h9, split_list _ L hL]

end PCP.Lang.DerivedSeed
