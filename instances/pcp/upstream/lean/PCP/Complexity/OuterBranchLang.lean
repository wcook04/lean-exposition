import PCP.Complexity.OuterBranchInner
import PCP.Complexity.OuterBranchRead

/-!
# Complete outer encoded-line branch on an exact stored sample

The primary Hadamard check, selected inner check, standard correction and final
primary read are actual programs. Their physical query sequence and Boolean
verdict agree with the named executable outer verifier.
-/

set_option maxRecDepth 1024

namespace PCP.Lang.OuterBranch

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t]

def lineOracle (k : Kind) (qs : List ℕ) (bs : List Bool)
    (uv : Point k t n × Point k t n) :
    BinaryLocalCorrection.InnerPoint (Field t) m 4 → Coefficients t 1 → ZMod 2 :=
  (k.line uv).oracle (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
    (BooleanCoefficientIndex.coefficientEquiv t 3) qs bs

omit [NeZero t] in
theorem innerOracle_eq (site : StandardCorrection.Site (Field t) n)
    (qs : List ℕ) (bs : List Bool) :
    (InterpolationBranch.oracle (m := m) site qs bs) =
      site.oracle (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
        (BooleanCoefficientIndex.coefficientEquiv t 3) qs bs := by
  funext x p
  unfold InterpolationBranch.oracle InterpolationBranch.address StandardCorrection.Site.oracle
  cases QueryTree.answersOracle qs bs _ <;> rfl

def verdict (k : Kind) (a : Fin 5 → Field t) (ζ : Field t) (s : Sample k t n m)
    (qs : List ℕ) (bs : List Bool) : Bool :=
  ComputableEncodedLineLowDegreeTest.test k.degree_pos (BinaryMaterializedField.coordinates t)
    a ζ (primaryOracle (m := m) k qs bs) (lineOracle k qs bs) s

def correctionCodes (k : Kind) (ζ : Field t) (s : Sample k t n m) : List ℕ :=
  (((k.line s.1).queries ζ (BinaryMaterializedField.coordinates t) (SetMultilinear.evaluationPoint m 4 s.2.1)
    s.2.2.1.1 s.2.2.1.2).map (fun q =>
      (ThreeColorQueryIndex.equiv (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
        (BooleanCoefficientIndex.coefficientEquiv t 3) q).val))

def primaryReadCode (k : Kind) (s : Sample k t n m) : ℕ :=
  (ThreeColorQueryIndex.equiv (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
    (BooleanCoefficientIndex.coefficientEquiv t 3)
    ((k.primary (m := m) (PolynomialLine.point s.1.1 s.1.2 s.2.1)).query
      (BooleanCoefficientArithmetic.homogeneousIndex k.degree_pos s.2.2.1.2))).val

def queryCodes (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) : List ℕ :=
  (k.queries (BinaryMaterializedField.coordinates t) a ζ s).map (fun q =>
    (ThreeColorQueryIndex.equiv (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
      (BooleanCoefficientIndex.coefficientEquiv t 3) q).val)

theorem queryCodes_parts (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) :
    queryCodes k a ζ s = primaryQueries k s ++ InnerBranch.queries a (k.line s.1) (innerSeed s) ++
      correctionCodes k ζ s ++ [primaryReadCode k s] := by
  rw [queryCodes, Kind.queries_parts]
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
  rfl

def combine : Stmt 180 80 := .seq (.assign 144 (.eq 142 143))
  (.seq (.assign 144 (.mul 140 144)) (.assign 144 (.mul 141 144)))

def program : Stmt 180 80 := .seq primaryHadamard (.seq selectedInner
  (.seq (standardAt 125) (.seq primaryRead combine)))

attribute [local irreducible] primaryHadamard selectedInner standardAt primaryRead

omit [NeZero t] in
theorem combine_run (f g : Bool) (u v : ZMod 2) (st : State 180 80)
    (hf : st.regs 140 = f.toNat) (hg : st.regs 141 = g.toNat)
    (hu : st.regs 142 = u.val) (hv : st.regs 143 = v.val) :
    (combine.run st).1.regs 144 = (f && g && decide (u = v)).toNat ∧
    (combine.run st).1.lists 49 = st.lists 49 ∧ Frame st (combine.run st).1 := by
  have he : u.val = v.val ↔ u = v := ⟨fun h => ZMod.val_injective 2 h, fun h => congrArg ZMod.val h⟩
  refine ⟨?_, run_lists_frame _ _ (by decide) st,
    frame_of_writes _ (by decide) (by decide) st⟩
  cases f <;> cases g <;> by_cases h : u = v <;>
    simp [combine, Stmt.run, Expr.eval, Function.update, hf, hg, hu, hv, he, h]

/-- Exact outer verdict and exact ordered physical trace, on arbitrary answer histories. -/
theorem program_run [NeZero m] (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) :
    (program.run st).1.regs 144 = (verdict k a ζ s qs bs).toNat ∧
    (program.run st).1.lists 49 = (queryCodes k a ζ s).reverse ++ st.lists 49 ∧
      Frame st (program.run st).1 := by
  have hp := primaryHadamard_run k a ζ s qs bs st hc
  generalize hP : (primaryHadamard.run st).1 = p at *
  have hcp := hc.of_frame hp.2.2
  have hi := selectedInner_run k a ζ s qs bs p hcp
  have hi140 := (selectedInner_reg 140 (by decide) (by decide) p).trans hp.1
  generalize hI : (selectedInner.run p).1 = i at *
  have hci := hcp.of_frame hi.2.2
  have hs := standardAt_run 125 (by decide) k a ζ s.2.1 s qs bs i hci hci.param
  have hs140 := (standardAt_reg 125 140 (by decide) (by decide) i).trans hi140
  have hs141 := (standardAt_reg 125 141 (by decide) (by decide) i).trans hi.1
  generalize hS : ((standardAt 125).run i).1 = u at *
  have hcu := hci.of_frame hs.2.2
  have hr := primaryRead_run k a ζ s qs bs u hcu
  have hr140 := (primaryRead_reg 140 (by decide) (by decide) (by decide)
    (by decide) (by decide) u).trans hs140
  have hr141 := (primaryRead_reg 141 (by decide) (by decide) (by decide)
    (by decide) (by decide) u).trans hs141
  have hr142 := (primaryRead_reg 142 (by decide) (by decide) (by decide)
    (by decide) (by decide) u).trans hs.1
  generalize hR : (primaryRead.run u).1 = v at *
  have hv := combine_run _ _ _ _ v hr140 hr141 hr142 hr.1
  simp only [program, run_seq_fst, hP, hI, hS, hR]
  refine ⟨?_, ?_, hp.2.2.trans (hi.2.2.trans (hs.2.2.trans (hr.2.2.trans hv.2.2)))⟩
  · rw [hv.1]
    simp only [verdict, ComputableEncodedLineLowDegreeTest.test,
      ComputableEncodedLineLowDegreeTest.corrected, InnerBranch.verdict,
      innerOracle_eq, lineOracle, primarySeed, innerSeed]
    congr 1
  · rw [hv.2.1, hr.2.1, hs.2.1, hi.2.1, hp.2.1, queryCodes_parts]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.append_assoc, List.singleton_append]
    rfl

end PCP.Lang.OuterBranch
