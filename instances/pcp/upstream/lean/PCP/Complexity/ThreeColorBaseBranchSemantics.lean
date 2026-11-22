import PCP.Complexity.ThreeColorBaseBranchState

/-! # Exact per-branch physical query segments and answers in production order -/

namespace PCP.Lang.ThreeColorBaseBranches

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters ThreeColorFullFieldSampling
  LocalCorrection DerivedGrid

def derivedQueries (k : Certificate) (N : ℕ) (x bits : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample N bits)) : List ℕ :=
  let a := exponent N
  let s := ThreeColorBaseDerived.sample k N bits hv
  queries k (nodes a) (generator a)
    (FiniteAlphabetIndex.alphabet (BinaryFieldCode.fieldEquiv (binaryDimension a))
      (size_le_fieldCode a)) (DerivedSeed.weight k (size a) (size_le_fieldCode a) x s) s

def derivedVerdict (k : Certificate) (N : ℕ) (x bits : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample N bits)) (qs : List ℕ) (bs : List Bool) : Bool :=
  let a := exponent N
  let s := ThreeColorBaseDerived.sample k N bits hv
  decision k (nodes a) (generator a)
    (FiniteAlphabetIndex.alphabet (BinaryFieldCode.fieldEquiv (binaryDimension a))
      (size_le_fieldCode a)) (DerivedSeed.weight k (size a) (size_le_fieldCode a) x s) s qs bs

def querySegments (N : ℕ) (x bits : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample N bits)) : Fin 7 → List ℕ :=
  let a := exponent N
  ![OuterBranch.queryCodes .color (nodes a) (generator a)
      (ThreeColorBaseOuter.sample .color N bits),
    OuterBranch.queryCodes .valid (nodes a) (generator a)
      (ThreeColorBaseOuter.sample .valid N bits),
    OuterBranch.queryCodes .difference (nodes a) (generator a)
      (ThreeColorBaseOuter.sample .difference N bits),
    OuterBranch.queryCodes .proper (nodes a) (generator a)
      (ThreeColorBaseOuter.sample .proper N bits),
    derivedQueries .valid N x bits hv, derivedQueries .proper N x bits hv,
    NumericDifference.queries (size a) (ThreeColorBaseDifference.sample N bits)]

def verdicts (N : ℕ) (x bits : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample N bits)) (qs : List ℕ) (bs : List Bool) : Fin 7 → Bool :=
  let a := exponent N
  ![OuterBranch.verdict .color (nodes a) (generator a)
      (ThreeColorBaseOuter.sample .color N bits) qs bs,
    OuterBranch.verdict .valid (nodes a) (generator a)
      (ThreeColorBaseOuter.sample .valid N bits) qs bs,
    OuterBranch.verdict .difference (nodes a) (generator a)
      (ThreeColorBaseOuter.sample .difference N bits) qs bs,
    OuterBranch.verdict .proper (nodes a) (generator a)
      (ThreeColorBaseOuter.sample .proper N bits) qs bs,
    derivedVerdict .valid N x bits hv qs bs, derivedVerdict .proper N x bits hv qs bs,
    NumericDifference.verdict (size a) (ThreeColorBaseDifference.sample N bits) qs bs]

attribute [local irreducible] ThreeColorBaseOuter.program ThreeColorBaseDerived.program
  ThreeColorBaseDifference.program OuterBranch.verdict OuterBranch.queryCodes
  DerivedGrid.decision DerivedGrid.queries NumericDifference.verdict NumericDifference.queries

theorem branch_run (i : Fin 7) (x bits bs : List Bool) (qs : List ℕ)
    (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
    (st : State 400 128) (hc : Context x bits bs qs st) :
    ((branch i).run st).1.regs (resultPort i) =
      (verdicts (ThreeColorEncoding.vertexCount x) x bits hv qs bs i).toNat ∧
    ((branch i).run st).1.lists 124 =
      (querySegments (ThreeColorEncoding.vertexCount x) x bits hv i).reverse ++ st.lists 124 := by
  fin_cases i
  · exact ThreeColorBaseOuter.program_run .color _ bits qs bs st hc.ready.data
      hc.ready.cardinal
      hc.ready.seeds hc.history hc.ready.sources.answers
  · exact ThreeColorBaseOuter.program_run .valid _ bits qs bs st hc.ready.data
      hc.ready.cardinal
      hc.ready.seeds hc.history hc.ready.sources.answers
  · exact ThreeColorBaseOuter.program_run .difference _ bits qs bs st hc.ready.data
      hc.ready.cardinal
      hc.ready.seeds hc.history hc.ready.sources.answers
  · exact ThreeColorBaseOuter.program_run .proper _ bits qs bs st hc.ready.data
      hc.ready.cardinal
      hc.ready.seeds hc.history hc.ready.sources.answers
  · exact ThreeColorBaseDerived.program_run .valid _ bits x qs bs st hc.ready.data
      hc.ready.cardinal
      hc.ready.seeds hv hc.ready.sources.graph hc.history hc.ready.sources.answers
  · exact ThreeColorBaseDerived.program_run .proper _ bits x qs bs st hc.ready.data
      hc.ready.cardinal
      hc.ready.seeds hv hc.ready.sources.graph hc.history hc.ready.sources.answers
  · exact ThreeColorBaseDifference.program_run _ bits qs bs st hc.ready.data
      hc.ready.cardinal
      hc.ready.seeds hc.history hc.ready.sources.answers

end PCP.Lang.ThreeColorBaseBranches
