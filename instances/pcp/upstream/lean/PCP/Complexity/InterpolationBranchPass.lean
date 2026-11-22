import PCP.Complexity.InterpolationBranchWeight
import PCP.Complexity.InterpolationBranchFrame
import PCP.Complexity.InterpolationBranchEmit

/-!
# Lagrange constraint queries with exact zero-weight omission
-/

namespace PCP.Lang.InterpolationBranch

open PCP.Algebraic BinaryFieldCode BooleanCoefficientArithmetic

variable {t n m : ℕ} [NeZero t]

def firstQuery : Stmt 100 40 := .seq (pointStep 82) (.seq plainLabel emitStep)

def nodeEmit : Stmt 100 40 := .seq (pointStep 93) (.seq scaledLabel emitStep)

def nodeStep (i : Fin 5) : Stmt 100 40 :=
  .seq (weightStep i) (.ite 92 nodeEmit .skip)

def firstAddress (z : Field t) (u v : Point t m) (w : Fin t → ZMod 2)
    (site : StandardCorrection.Site (Field t) n) : ℕ :=
  address site (PolynomialLine.point u v z) (homogeneousIndex (le_refl 1) w)

def nodeAddress (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n) (i : Fin 5) : ℕ :=
  address site (PolynomialLine.point u v (a i)) (homogeneousIndex (le_refl 1)
    (FieldQueryArithmetic.scaleLabel (BinaryMaterializedField.coordinates t)
      (FieldQueryArithmetic.interpolationWeight a z i) w))

def nodeQueries (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n) (i : Fin 5) : List ℕ :=
  if FieldQueryArithmetic.interpolationWeight a z i = 0 then []
  else [nodeAddress a z u v w site i]

theorem firstQuery_run (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (st : State 100 40) (hc : Context a z u v w site st) :
    (firstQuery.run st).1.lists 20 = firstAddress z u v w site :: st.lists 20 ∧
    Frame st (firstQuery.run st).1 := by
  have hp := pointStep_run 82 (by decide) a z u v w site z st hc hc.param
  have hq := pointStep_queries 82 st
  generalize hs : ((pointStep 82).run st).1 = s at *
  have hsc := hc.of_frame hp.2
  have hl := plainLabel_run a z u v w site s hsc
  have hlq := plainLabel_queries s
  have hlp := plainLabel_reg 95 (by decide) (by decide) s
  generalize hout : (plainLabel.run s).1 = out at *
  have he := emitStep_run a z u v w site (PolynomialLine.point u v z)
    (homogeneousIndex (le_refl 1) w) out (hsc.of_frame hl.2) (hlp.trans hp.1) hl.1
  rw [hlq, hq] at he
  simp only [firstQuery, run_seq_fst, hs, hout]
  exact ⟨he.1, hp.2.trans (hl.2.trans he.2)⟩

theorem nodeEmit_run (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n) (i : Fin 5)
    (st : State 100 40) (hc : Context a z u v w site st)
    (hw : st.regs 92 = (fieldEquiv t (FieldQueryArithmetic.interpolationWeight a z i)).val)
    (hn : st.regs 93 = (fieldEquiv t (a i)).val) :
    (nodeEmit.run st).1.lists 20 = nodeAddress a z u v w site i :: st.lists 20 ∧
    Frame st (nodeEmit.run st).1 := by
  have hp := pointStep_run 93 (by decide) a z u v w site (a i) st hc hn
  have hpw := pointStep_reg 93 92 (by decide) (by decide) st
  have hq := pointStep_queries 93 st
  generalize hs : ((pointStep 93).run st).1 = s at *
  have hsc := hc.of_frame hp.2
  have hl := scaledLabel_run a z u v w site
    (FieldQueryArithmetic.interpolationWeight a z i) s hsc (hpw.trans hw)
  have hlq := scaledLabel_queries s
  have hlp := scaledLabel_reg 95 (by decide) (by decide) s
  generalize hout : (scaledLabel.run s).1 = out at *
  have he := emitStep_run a z u v w site (PolynomialLine.point u v (a i))
    (homogeneousIndex (le_refl 1) (FieldQueryArithmetic.scaleLabel
      (BinaryMaterializedField.coordinates t) (FieldQueryArithmetic.interpolationWeight a z i) w))
    out (hsc.of_frame hl.2) (hlp.trans hp.1) hl.1
  rw [hlq, hq] at he
  simp only [nodeEmit, run_seq_fst, hs, hout]
  exact ⟨he.1, hp.2.trans (hl.2.trans he.2)⟩

omit [NeZero t] in
theorem fieldCode_eq_zero (α : Field t) : (fieldEquiv t α).val = 0 ↔ α = 0 := by
  constructor
  · intro h
    apply (fieldEquiv t).injective
    apply Fin.ext
    rw [h, FieldExpression.code_zero]
  · rintro rfl
    exact FieldExpression.code_zero

/-- Only nonzero weights trigger point construction, label scaling, and a proof query. -/
theorem nodeStep_run (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n) (i : Fin 5)
    (st : State 100 40) (hc : Context a z u v w site st) :
    ((nodeStep i).run st).1.lists 20 = nodeQueries a z u v w site i ++ st.lists 20 ∧
    Frame st ((nodeStep i).run st).1 := by
  have hw := weightStep_run a z u v w site i st hc
  have hq := weightStep_queries i st
  generalize hs : ((weightStep i).run st).1 = s at *
  have hsc := hc.of_frame hw.2.2
  have hz : s.regs 92 = 0 ↔ FieldQueryArithmetic.interpolationWeight a z i = 0 := by
    rw [hw.1, fieldCode_eq_zero]
  simp only [nodeStep, run_seq_fst, hs]
  by_cases hzero : FieldQueryArithmetic.interpolationWeight a z i = 0
  · have h0 := hz.mpr hzero
    rw [run_ite_fst, ite_eq_right (not_not_intro h0)]
    simp only [nodeQueries, hzero, ↓reduceIte, List.nil_append]
    exact ⟨hq, hw.2.2⟩
  · have h0 : s.regs 92 ≠ 0 := fun h => hzero (hz.mp h)
    have he := nodeEmit_run a z u v w site i s hsc hw.1 hw.2.1
    rw [hq] at he
    rw [run_ite_fst, ite_eq_left h0]
    simp only [nodeQueries, hzero, ↓reduceIte, List.singleton_append]
    exact ⟨he.1, hw.2.2.trans he.2⟩

end PCP.Lang.InterpolationBranch
