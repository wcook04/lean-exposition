import PCP.Complexity.AmplifiedEncodeCost
import PCP.Complexity.AmplifiedSequenceFrame
import PCP.Complexity.AmplifiedResourcePolynomial

/-!
# Concrete public protocol around a certified base callback

This compiles parsing, fixed independent repetition and result serialization to
the actual machine model. The base callback and parser premises are explicit;
the production instantiation must supply their proved concrete implementations.
-/

namespace PCP.Lang.AmplifiedProtocol

open AmplifiedStream PCP.Machine PCP.Machine.LangSymbolBridge
open PCP.Algebraic.ThreeColorAmplifiedQueryAlgorithm

/-- Standard public input state shared with the final compiled program. -/
def initial (input : List ℕ) : State 420 140 :=
  ⟨fun _ => 0, fun L => if L = 0 then input else []⟩

structure Setup (S : Stmt 420 140) : Prop where
  run : ∀ t : List Bool × List Bool × List Bool,
    Ready (S.run (initial (code (encodeTriple t)))).1
      (PCP.Algebraic.ThreeColorCanonicalVerifier.randomBudget t.1.length) t.1 t.2.1 t.2.2 ∧
    (S.run (initial (code (encodeTriple t)))).1.regs 414 = (encodeTriple t).length

/-- The finite program contains a fixed number of copies of the same callback. -/
def program (S : Stmt 420 140) (P : Stmt 400 128) (k : ℕ) (cs : List ℕ) : Prog where
  R := 420
  Q := 140
  hQ := by decide
  body := .seq S (.seq (copies P k) (encode cs))

theorem program_init (S : Stmt 420 140) (P : Stmt 400 128) (k : ℕ) (cs input : List ℕ) :
    (program S P k cs).init input = initial input := rfl

attribute [local irreducible] copies encode

theorem program_run (S : Stmt 420 140) (hS : Setup S)
    (P : Stmt 400 128) (qs : List Bool → List Bool → List ℕ)
    (fs : List Bool → List Bool → PCP.ProofOracle → Bool) (hc : Correct P qs fs)
    (C d : ℕ) (hR : PolynomialResources P qs C d) (k : ℕ)
    (cs : List ℕ) (hcs : ∀ n, PolynomialBudget.value cs n = (queryPolynomial C d).eval n)
    (t : List Bool × List Bool × List Bool) :
    (program S P k cs).run (code (encodeTriple t)) = code (encodeAnswer
      (slicedSequence (PCP.Algebraic.ThreeColorCanonicalVerifier.randomBudget t.1.length)
        (qs t.1) (fs t.1) k t.2.1 t.2.2)) := by
  let n := (encodeTriple t).length
  let st := (S.run (initial (code (encodeTriple t)))).1
  let u := ((copies P k).run st).1
  have hs := hS.run t
  change Ready st _ _ _ _ ∧ st.regs 414 = n at hs
  have hb := streamSize_bounds t
  have hbound := resources_bounded P qs C d hR n
  have ho := copies_output P qs fs hc (streamSize n) ((queryPolynomial C d).eval n)
    hbound k st _ _ _ _ hs.1 hb.1 hb.2.1
  have hframe := copies_frame P k st hs.1.empty
  have hlen : u.regs 414 = n := hframe.1.trans hs.2
  have hbudget : (queryPolynomial C d).eval n ≤ PolynomialBudget.value cs (u.regs 414) := by
    rw [hlen, hcs]
  have he := encode_run cs u ((queryPolynomial C d).eval n) ho hbudget hframe.2
  have hrun := copies_run P qs fs hc k st _ _ _ _ hs.1
  unfold Prog.run
  rw [program_init]
  change ((encode cs).run u).1.lists 1 = _
  rw [he, hrun]

/-- The explicit polynomial whose evaluation dominates the whole source cost. -/
noncomputable def costPolynomial (Cs ds C d k : ℕ) (cs : List ℕ) : Polynomial ℕ :=
  Polynomial.C Cs*(Polynomial.X+1)^ds +
    Polynomial.C ((k+1)*5000)*(sizePolynomial+queryPolynomial C d+1)^2 +
    Polynomial.C (PolynomialBudget.costConstant cs+6)*(Polynomial.X+1) +
    Polynomial.C (BinaryEncode.passConstant+25)*(Polynomial.C 2*queryPolynomial C d+3)^2+3

theorem program_cost (S : Stmt 420 140) (hS : Setup S) (Cs ds : ℕ)
    (hcostS : ∀ t : List Bool × List Bool × List Bool,
      (S.run (initial (code (encodeTriple t)))).2 ≤ Cs*((encodeTriple t).length+1)^ds)
    (P : Stmt 400 128) (qs : List Bool → List Bool → List ℕ)
    (fs : List Bool → List Bool → PCP.ProofOracle → Bool) (hc : Correct P qs fs)
    (C d : ℕ) (hR : PolynomialResources P qs C d) (k : ℕ)
    (cs : List ℕ) (hcs : ∀ n, PolynomialBudget.value cs n = (queryPolynomial C d).eval n)
    (t : List Bool × List Bool × List Bool) :
    (program S P k cs).cost (code (encodeTriple t)) ≤
      (costPolynomial Cs ds C d k cs).eval (encodeTriple t).length := by
  let n := (encodeTriple t).length
  let st := (S.run (initial (code (encodeTriple t)))).1
  let u := ((copies P k).run st).1
  have hs := hS.run t
  change Ready st _ _ _ _ ∧ st.regs 414 = n at hs
  have hb := streamSize_bounds t
  have hbound := resources_bounded P qs C d hR n
  have ho := copies_output P qs fs hc (streamSize n) ((queryPolynomial C d).eval n)
    hbound k st _ _ _ _ hs.1 hb.1 hb.2.1
  have hframe := copies_frame P k st hs.1.empty
  have hlen : u.regs 414 = n := hframe.1.trans hs.2
  have hbudget : (queryPolynomial C d).eval n ≤ PolynomialBudget.value cs (u.regs 414) := by
    rw [hlen, hcs]
  have he := encode_cost cs u ((queryPolynomial C d).eval n) ho hbudget hframe.2
  rw [hlen, hcs] at he
  have hcopy := copies_cost P qs fs hc (streamSize n) ((queryPolynomial C d).eval n)
    hbound k st _ _ _ _ hs.1 hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
  have hsetup := hcostS t
  have hsize := size_le_self n
  have he' : ((encode cs).run u).2 ≤
      (PolynomialBudget.costConstant cs+6)*(n+1)+
        (BinaryEncode.passConstant+25)*(2*(queryPolynomial C d).eval n+3)^2+1 :=
    he.trans (by gcongr)
  unfold Prog.cost
  rw [program_init]
  change (S.run (initial (code (encodeTriple t)))).2+
    (((copies P k).run st).2+((encode cs).run u).2+1)+1 ≤ _
  simp only [costPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat,
    sizePolynomial_eval]
  dsimp only [n] at he' hcopy
  omega

/-- All protocol work is realized by a concrete polynomial-time machine. -/
theorem polyTimeAlg (S : Stmt 420 140) (hS : Setup S) (Cs ds : ℕ)
    (hcostS : ∀ t : List Bool × List Bool × List Bool,
      (S.run (initial (code (encodeTriple t)))).2 ≤ Cs*((encodeTriple t).length+1)^ds)
    (P : Stmt 400 128) (qs : List Bool → List Bool → List ℕ)
    (fs : List Bool → List Bool → PCP.ProofOracle → Bool) (hc : Correct P qs fs)
    (C d : ℕ) (hR : PolynomialResources P qs C d) (k : ℕ) :
    PolyTimeAlg (fun x bits answers => slicedSequence
      (PCP.Algebraic.ThreeColorCanonicalVerifier.randomBudget x.length)
      (qs x) (fs x) k bits answers) := by
  obtain ⟨cs, hcs⟩ := PolynomialBudget.exists_coefficients (queryPolynomial C d)
  obtain ⟨C', d', hpoly⟩ := PolynomialPrefix.exists_eval_bound (costPolynomial Cs ds C d k cs)
  apply LangSymbolBridge.polyTimeAlg_of_program _ (program S P k cs) (Lang.compile _)
    (c₁ := C') (k₁ := d')
  · exact program_run S hS P qs fs hc C d hR k cs hcs
  · intro t
    exact (program_cost S hS Cs ds hcostS P qs fs hc C d hR k cs hcs t).trans (hpoly _)

end PCP.Lang.AmplifiedProtocol
