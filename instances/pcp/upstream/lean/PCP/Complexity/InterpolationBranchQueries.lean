import PCP.Complexity.InterpolationBranchPass

/-!
# The full physical query list of the degree-four interpolation test
-/

namespace PCP.Lang.InterpolationBranch

open PCP.Algebraic BinaryFieldCode BooleanCoefficientArithmetic

variable {t n m : ℕ} [NeZero t]

def passes : List (Fin 5) → Stmt 100 40
  | [] => .skip
  | i :: is => .seq (nodeStep i) (passes is)

def queries : Stmt 100 40 := .seq (.copy 7 20)
  (.seq firstQuery (.seq (passes (List.finRange 5)) (.rev 20)))

attribute [local irreducible] passes firstQuery nodeStep nodeEmit

def queryCodes (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n) : List ℕ :=
  (ComputableBinaryLagrangeConstraint.queries (le_refl 1)
    (BinaryMaterializedField.coordinates t) a u v z w).map
      (fun p => address site p.1 p.2)

theorem nodeQueries_reverse (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n) (i : Fin 5) :
    (nodeQueries a z u v w site i).reverse = nodeQueries a z u v w site i := by
  unfold nodeQueries
  split <;> rfl

theorem passes_run (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (is : List (Fin 5)) (st : State 100 40) (hc : Context a z u v w site st) :
    ((passes is).run st).1.lists 20 =
      (is.flatMap (nodeQueries a z u v w site)).reverse ++ st.lists 20 ∧
    Frame st ((passes is).run st).1 := by
  induction is generalizing st with
  | nil => rw [passes]; exact ⟨rfl, Frame.refl st⟩
  | cons i is ih =>
      have hs := nodeStep_run a z u v w site i st hc
      have hi := ih ((nodeStep i).run st).1 (hc.of_frame hs.2)
      rw [hs.1] at hi
      simp only [passes, run_seq_fst]
      refine ⟨?_, hs.2.trans hi.2⟩
      simpa only [List.flatMap_cons, List.reverse_append, nodeQueries_reverse,
        List.append_assoc] using hi.1

theorem filterMap_codes (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (is : List (Fin 5)) :
    ((is.filterMap (fun i => if FieldQueryArithmetic.interpolationWeight a z i = 0 then none
      else some (PolynomialLine.point u v (a i), homogeneousIndex (le_refl 1)
        (FieldQueryArithmetic.scaleLabel (BinaryMaterializedField.coordinates t)
          (FieldQueryArithmetic.interpolationWeight a z i) w)))).map
            (fun p => address site p.1 p.2)) = is.flatMap (nodeQueries a z u v w site) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      by_cases h : FieldQueryArithmetic.interpolationWeight a z i = 0 <;>
        simp only [List.filterMap_cons, h, ↓reduceIte, List.map_cons, List.flatMap_cons,
          nodeQueries, nodeAddress, List.nil_append, List.singleton_append, ih]

theorem queryCodes_eq (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n) :
    queryCodes a z u v w site = firstAddress z u v w site ::
      (List.finRange 5).flatMap (nodeQueries a z u v w site) := by
  simp only [queryCodes, ComputableBinaryLagrangeConstraint.queries, List.map_cons,
    filterMap_codes, firstAddress]

/-- Assemble arbitrary already-proved query stages without unfolding their arithmetic code. -/
theorem assemble_queries_run (P Q : Stmt 100 40) (first : ℕ) (rest : List ℕ)
    (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (hfirst : ∀ st, Context a z u v w site st →
      (P.run st).1.lists 20 = first :: st.lists 20 ∧ Frame st (P.run st).1)
    (hpasses : ∀ st, Context a z u v w site st →
      (Q.run st).1.lists 20 = rest.reverse ++ st.lists 20 ∧ Frame st (Q.run st).1)
    (st : State 100 40) (hc : Context a z u v w site st) :
    ((Stmt.seq (.copy 7 20) (.seq P (.seq Q (.rev 20)))).run st).1.lists 20 =
      first :: rest ∧
    Frame st ((Stmt.seq (.copy 7 20) (.seq P (.seq Q (.rev 20)))).run st).1 := by
  let s := setList st 20 []
  have hsf : Frame st s := by
    have h := Frame.copy st 7 20 (by decide) (by decide) (by decide)
    simpa only [hc.empty] using h
  have hsq : s.lists 20 = [] := by simp [s]
  have hs := hfirst s (hc.of_frame hsf)
  rw [hsq] at hs
  generalize hout : (P.run s).1 = out at *
  have hp := hpasses out ((hc.of_frame hsf).of_frame hs.2)
  rw [hs.1] at hp
  generalize hpout : (Q.run out).1 = pout at *
  have hrev : Frame pout (setList pout 20 (pout.lists 20).reverse) := by
    exact frame_of_writes (.rev 20) (by simp [Stmt.regWrites])
      (by
        intro L hL
        simp only [Stmt.listWrites, List.mem_singleton] at hL
        subst L
        decide) _
  simp only [run_seq_fst, run_copy_fst, hc.empty]
  dsimp only [s] at hout
  rw [hout, hpout]
  refine ⟨?_, hsf.trans (hs.2.trans (hp.2.trans hrev))⟩
  simp only [run_rev_fst, setList_lists, Function.update_self, hp.1,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.reverse_reverse, List.singleton_append]

set_option maxRecDepth 1024 in
/-- Every returned address is computed by the actual production codec, in the exact test order. -/
theorem queries_run (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (st : State 100 40) (hc : Context a z u v w site st) :
    (queries.run st).1.lists 20 = queryCodes a z u v w site ∧
    Frame st (queries.run st).1 := by
  rw [queryCodes_eq]
  exact assemble_queries_run firstQuery (passes (List.finRange 5))
    (firstAddress z u v w site) ((List.finRange 5).flatMap (nodeQueries a z u v w site))
    a z u v w site (firstQuery_run a z u v w site)
    (passes_run a z u v w site (List.finRange 5)) st hc

end PCP.Lang.InterpolationBranch
