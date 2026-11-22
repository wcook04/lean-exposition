import PCP.Complexity.LocalCorrectionLang
import PCP.Algebraic.ComputableDerivedZeroOnGrid

/-!
# Certificate calls at their two actual physical table kinds

A derived-grid call is materialized in the shared outer layout using its own
sampled direction, unit parameter, inner direction and inner seed. The unused
primary Hadamard source is populated from the already sampled inner Hadamard
seed. No oracle or runtime callback is supplied as a premise.
-/

namespace PCP.Lang.LocalCorrection

open PCP.Algebraic OuterBranch BinaryFieldCode BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t] [NeZero m]

inductive Certificate
  | valid
  | proper
  deriving DecidableEq

def Certificate.outer : Certificate → OuterBranch.Kind
  | .valid => .valid
  | .proper => .proper

abbrev Certificate.Point (k : Certificate) (t n : ℕ) := k.outer.Coordinates n → Field t

abbrev Certificate.Seed (k : Certificate) (t n m : ℕ) [NeZero t] :=
  BinaryZeroOnGridCorrection.CallSeed (Field t) (k.outer.Coordinates n) m 4 t

def Certificate.sample (k : Certificate) (a : k.Point t n) (w : Fin t → ZMod 2)
    (s : k.Seed t n m) : OuterBranch.Sample k.outer t n m :=
  match k with
  | .valid => ((a, s.1), ((s.2.1 : Field t),
      ((s.2.2.1, w), (s.2.2.2.2.1.2, s.2.2.2))))
  | .proper => ((a, s.1), ((s.2.1 : Field t),
      ((s.2.2.1, w), (s.2.2.2.2.1.2, s.2.2.2))))

def Certificate.oracle (k : Certificate) (qs : List ℕ) (bs : List Bool) :
    k.Point t n → Coefficients t 1 → ZMod 2 :=
  match k with
  | .valid => primaryOracle (m := m) .valid qs bs
  | .proper => primaryOracle (m := m) .proper qs bs

def Certificate.rows (k : Certificate) (a : k.Point t n) (qs : List ℕ) (bs : List Bool) :
    k.Point t n → BinaryLocalCorrection.RowOracle (Field t) m 4 t :=
  fun b => (k.outer.line (a, b)).oracle (fieldEquiv t)
    (BooleanCoefficientIndex.coefficientEquiv t 1)
    (BooleanCoefficientIndex.coefficientEquiv t 3) qs bs

def Certificate.physical (k : Certificate) (a : k.Point t n) :
    BinaryLocalCorrection.Query (Field t) (k.outer.Coordinates n) m 4 t →
      ThreeColorVerifier.Query (Field t) n m 4 t :=
  match k with
  | .valid => fun q => ThreeColorVerifier.validGridQuery (.inr (a, q))
  | .proper => fun q => ThreeColorVerifier.properGridQuery (.inr (a, q))

omit [NeZero t] [NeZero m] in
theorem interpolation_oracle (site : StandardCorrection.Site (Field t) n)
    (qs : List ℕ) (bs : List Bool) :
    InterpolationBranch.oracle (m := m) site qs bs =
      site.oracle (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
        (BooleanCoefficientIndex.coefficientEquiv t 3) qs bs := by
  funext x L
  unfold InterpolationBranch.oracle InterpolationBranch.address StandardCorrection.Site.oracle
  cases QueryTree.answersOracle qs bs _ <;> rfl

omit [NeZero m] in
theorem result_call (k : Certificate) (nodes : Fin 5 → Field t) (ζ : Field t)
    (a : k.Point t n) (w : Fin t → ZMod 2) (s : k.Seed t n m)
    (qs : List ℕ) (bs : List Bool) :
    result k.outer nodes ζ (k.sample a w s) qs bs =
      ComputableDerivedZeroOnGrid.call (BinaryMaterializedField.coordinates t)
        nodes ζ (k.oracle (m := m) qs bs) (k.rows a qs bs) a w s := by
  cases k <;>
    simp only [result, decision, observed, corrected, Certificate.outer, Certificate.sample,
      Certificate.oracle, Certificate.rows, InnerBranch.verdict, innerSeed,
      ComputableDerivedZeroOnGrid.call, ComputableBinaryLocalCorrection.run,
      interpolation_oracle]
  all_goals rfl

omit [NeZero m] in
theorem queries_call (k : Certificate) (nodes : Fin 5 → Field t) (ζ : Field t)
    (a : k.Point t n) (w : Fin t → ZMod 2) (s : k.Seed t n m) :
    queries k.outer nodes ζ (k.sample a w s) =
      (ComputableBinaryLocalCorrection.queries (BinaryMaterializedField.coordinates t)
        nodes ζ a s.1 s.2.1 s.2.2.1 w s.2.2.2).map
          (fun q => queryCode (k.physical a q)) := by
  cases k <;>
    simp only [queries, ComputableBinaryLocalCorrection.queries, List.map_cons,
      List.map_append, List.map_map, Function.comp_def, StandardCorrection.Site.queries,
      InnerBranch.queries]
  all_goals rfl

/-- Exact execution of the original certificate call and its full ordered physical trace. -/
theorem program_call (k : Certificate) (nodes : Fin 5 → Field t) (ζ : Field t)
    (a : k.Point t n) (w : Fin t → ZMod 2) (s : k.Seed t n m)
    (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : OuterBranch.Context k.outer nodes ζ (k.sample a w s) qs bs st) :
    let value := ComputableDerivedZeroOnGrid.call (BinaryMaterializedField.coordinates t)
      nodes ζ (k.oracle (m := m) qs bs) (k.rows a qs bs) a w s
    let trace := (ComputableBinaryLocalCorrection.queries (BinaryMaterializedField.coordinates t)
      nodes ζ a s.1 s.2.1 s.2.2.1 w s.2.2.2).map (fun q => queryCode (k.physical a q))
    (program.run st).1.regs 146 = present value ∧
    (program.run st).1.regs 147 = answer value ∧
    (program.run st).1.lists 49 = trace.reverse ++ st.lists 49 ∧
    OuterBranch.Frame st (program.run st).1 := by
  have h := program_run k.outer nodes ζ (k.sample a w s) qs bs st hc
  rw [result_call, queries_call] at h
  exact h

end PCP.Lang.LocalCorrection
