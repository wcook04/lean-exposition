
<!-- passage:front -->
# Reading the Lean PCP proof

A guide for readers new to Lean: the formal statement of the PCP theorem, the
definitions it rests on, and three results from the low-degree testing part of
the proof. It accompanies the [PCP guide](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/docs/pcp/README.md), which has the proof map
and the list of differences from the paper.

The formalization follows *A Simple Algebraic Proof of the PCP Theorem* by
Amireddy, Behera, Srinivasan, Sudan and Willumsgaard
([arXiv:2608.17429](https://arxiv.org/abs/2608.17429), to appear in SOSA 2027).
Theorem numbers are those of the paper (see [Paper version](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/docs/pcp/README.md#paper-version)).
Code is quoted verbatim from the development, with doc comments left out; each
block names its source file.

**Contents**

1. [What you have to read](#1)
2. [Reading a Lean statement](#2)
3. [The definitions](#3)
4. [The PCP theorem](#4)
5. [Checks on the definitions](#5)
6. [The explicit constants](#6)
7. [Low-degree testing statements](#7)
8. [Reading a proof](#8)
9. [Finding your way around](#9)
10. [Learning more Lean](#10)
<!-- /passage:front -->

<a id="1"></a>

## 1. What you have to read

<!-- passage:sec-1 -->

Lean checks every proof mechanically, down to the axioms. To know *what* has
been proved, you only need to read statements: the final theorem and the
definitions it mentions. You never need to read a proof to trust it.

Concretely, a reader has to check three things:

1. The definitions of NP, of a verifier, and of polynomial time
   ([Section 3](#3)) say what they should.
2. The final theorem `PCP.np_subset_pcp` ([Section 4](#4)) says
   NP ⊆ PCP(O(log n), O(1)).
3. No extra axioms were used. Running `#print axioms PCP.np_subset_pcp` lists
   nothing beyond `propext`, `Classical.choice` and `Quot.sound`, the standard
   axioms of classical mathematics in Lean. The audit script
   `scripts/pcp/axiom-audit.sh` checks this for every declaration and rejects
   `sorry` (an unproved step).

Everything else, about 26,000 declarations, is checked by Lean and can be read
for understanding rather than for trust.
<!-- /passage:sec-1 -->

<a id="2"></a>

## 2. Reading a Lean statement

<!-- passage:sec-2 -->

A theorem has the shape `theorem name (h₁ : A) (h₂ : B) : C := proof`.
Everything in parentheses before the last colon is a hypothesis, each with a
name (`h₁`, `h₂`) used later in the proof. What follows the last colon is the
conclusion. So the line reads "if A and B, then C". The table covers the
notation used in this guide.

| Lean | Meaning |
| --- | --- |
| `{F : Type*} [Field F] [Fintype F]` | Let F be a finite field. Arguments in braces and brackets are filled in by Lean automatically; brackets state structure on a type (field, finite, …). |
| `[DecidableEq F]` | Equality in F can be tested by an algorithm. No mathematical content; it lets Lean count disagreements. |
| `ℕ`, `ℚ` | Natural numbers (including 0) and rationals. Probabilities and distances are exact rationals. |
| `(c + 2 : ℚ)` | The number c + 2, read as a rational. |
| `Fin n` | The set {0, 1, …, n − 1}. |
| `σ → F`, `Fin m → F` | The spaces F<sup>σ</sup> and F<sup>m</sup>: a point is a function from coordinates to F. |
| `F × F`, `z.1`, `z.2` | Pairs, and the two coordinates of z = (z₁, z₂). |
| `fun z => e` | The function z ↦ e. |
| `f x`, `(R y).eval x` | f(x), and R<sub>y</sub>(x). Application is written by juxtaposition. |
| `A → B`, `∀ x, P x`, `∃ y, Q y` | A implies B; for all x; there exists y. Also `∧`, `∨`, `¬`, `↔` as usual. |
| `x : List Bool`, `x.length` | A bit string x ∈ {0,1}*, and its length \|x\|. |
| `Polynomial F`, `p.natDegree`, `p.eval t` | F[X], deg p (with deg 0 = 0), and p(t). |
| `MvPolynomial σ F` | Polynomials in variables X<sub>i</sub>, i ∈ σ. |
| `P.totalDegree`, `P.degreeOf j` | Total degree, and degree in the variable X<sub>j</sub>. |
| `MvPolynomial.eval x P` | P(x). |
| `![a, b]` | The vector (a, b). |
| `Fintype.card F` | \|F\|. |
| `IsPrimitiveRoot ζ (Fintype.card F - 1)` | ζ generates the multiplicative group F<sup>×</sup>. |
| `Nat.clog 2 n` | ⌈log₂ n⌉. |
| `{p : Polynomial F // p.natDegree ≤ c}` | The set of polynomials of degree at most c; `.val` is the polynomial itself. |
| `V.queries`, `V.accProb x π` | Dot notation: the field `queries` of V, or a function applied with V as its first argument. |
| `Nonempty T` | There is an object of type T (for example, a Turing machine with some property). |
| `relativeDistance f g` | Pr<sub>x</sub>[f(x) ≠ g(x)], the normalized Hamming distance (defined in this project). |
<!-- /passage:sec-2 -->

<a id="3"></a>

## 3. The definitions

<!-- passage:sec-3 -->

### Languages and NP

[PCP/Complexity/NP.lean](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Complexity/NP.lean)

```lean
def Language : Type := List Bool → Prop

structure NPCertificate (P : (List Bool → List Bool → Bool) → Prop) (L : Language) where
  witnessBound : Polynomial ℕ
  check : List Bool → List Bool → Bool
  check_polyTime : P check
  spec : ∀ x : List Bool, L x ↔
    ∃ w : List Bool, w.length ≤ witnessBound.eval x.length ∧ check x w = true

def InNP (P : (List Bool → List Bool → Bool) → Prop) (L : Language) : Prop :=
  Nonempty (NPCertificate P L)
```

A language is a predicate on bit strings. A certificate that L is in NP consists
of a polynomial bound p, a checking relation `check` that is polynomial-time in
the sense `P`, and a proof of the usual equivalence: x ∈ L if and only if some
witness w with |w| ≤ p(|x|) is accepted. The notion of polynomial time is a
parameter here. The main theorem fixes it to the concrete machine model below.

### Polynomial time

[PCP/Complexity/Machine.lean](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Complexity/Machine.lean)

```lean
def PolyTimeRel (R : List Bool → List Bool → Bool) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encodePair encodeBool (fun p => R p.1 p.2))
```

`Turing.TM2ComputableInPolyTime` is Mathlib's definition: a finite multi-stack
Turing machine computes the function, and halts within q(n) steps for a fixed
polynomial q, where n is the length of the encoded input. The input pair (x, w)
is written on the tape as x, a separator symbol, then w.

### Verifiers

[PCP/Verifier/Definition.lean](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Verifier/Definition.lean)

```lean
abbrev ProofOracle : Type := ℕ → Bool

inductive QueryTree : ℕ → Type
  | leaf {d : ℕ} (accept : Bool) : QueryTree d
  | query {d : ℕ} (addr : ℕ) (onFalse onTrue : QueryTree d) : QueryTree (d + 1)

def eval : {d : ℕ} → QueryTree d → ProofOracle → Bool
  | _, .leaf b, _ => b
  | _, .query a f t, π => if π a then (t.eval π) else (f.eval π)

def addresses : {d : ℕ} → QueryTree d → Finset ℕ
  | _, .leaf _ => ∅
  | _, .query a f t => insert a (f.addresses ∪ t.addresses)

structure Verifier where
  randomness : ℕ → ℕ
  queries : ℕ
  run : (x : List Bool) → Fin (2 ^ randomness x.length) → QueryTree queries
```

A proof is an infinite bit string π : ℕ → {0,1}. A `QueryTree d` is an adaptive
decision tree of depth at most d: each internal node reads one proof bit and
branches on it, and each leaf accepts or rejects. A verifier specifies how many
random bits it uses on inputs of length n, a bound on the number of queries, and
for each input x and each random string r ∈ {0, …, 2<sup>randomness(|x|)</sup> − 1}
the tree it runs.

```lean
variable (V : Verifier) (x : List Bool) (π : ProofOracle)

def acceptingRandomness : Finset (Fin (2 ^ V.randomness x.length)) :=
  Finset.univ.filter (fun r => (V.run x r).eval π = true)

def accProb : ℚ :=
  ((V.acceptingRandomness x π).card : ℚ) / ((2 : ℚ) ^ V.randomness x.length)

def CompleteAt : Prop := ∃ π : ProofOracle, V.accProb x π = 1

def SoundAt (s : ℚ) : Prop := ∀ π : ProofOracle, V.accProb x π ≤ s

def ReadsBelow (N : ℕ) : Prop :=
  ∀ r, ∀ a ∈ (V.run x r).addresses, a < N

def CanonicalRandomness (a b : ℕ) : Prop :=
  ∀ n : ℕ, V.randomness n = a * Nat.clog 2 (n + 2) + b
```

- `accProb` is the exact fraction of random strings on which V accepts x with
  proof π.
- `CompleteAt x`: some proof is accepted with probability 1. `SoundAt x s`:
  every proof is accepted with probability at most s.
- `ReadsBelow x N`: on input x, no tree ever queries an address ≥ N, whatever
  the random string and the answers. This is how "a proof of length N" is
  expressed.
- `CanonicalRandomness a b`: the verifier uses *exactly* a⌈log₂(n+2)⌉ + b random
  bits. An upper bound would be too weak: the randomness function is an
  arbitrary function of n, and an upper bound would let it encode an arbitrary
  (even uncomputable) predicate of the input length, which the verifier could
  read off from how many random bits it receives.

### Efficient verifiers

[PCP/Complexity/CostModel.lean](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Complexity/CostModel.lean) and
[PCP/Complexity/Machine.lean](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Complexity/Machine.lean)

```lean
abbrev VerifierAlg : Type := List Bool → List Bool → List Bool → Bool ⊕ ℕ

def ImplementedBy (V : Verifier) (alg : VerifierAlg) : Prop :=
  ∀ (x : List Bool) (r : Fin (2 ^ V.randomness x.length)),
    QueryTree.ofStep (alg x (bitsOfFin (V.randomness x.length) r)) V.queries [] = V.run x r

def PolyTimeAlg (alg : VerifierAlg) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encodeTriple encodeAnswer
    (fun t => alg t.1 t.2.1 t.2.2))
```

A `Verifier` is a mathematical object: a family of decision trees. Its
efficiency is certified separately, by an algorithm. Given the input x, the
random string r as bits, and the answers received so far, `alg` either halts
with a decision (`Bool`) or names the next proof address to query (`ℕ`).
`ImplementedBy` says that unfolding `alg` reproduces exactly the tree
`V.run x r`, for every x and r. `PolyTimeAlg` says `alg` runs in polynomial time
on Mathlib's Turing machines.
<!-- /passage:sec-3 -->

<a id="4"></a>

## 4. The PCP theorem

<!-- passage:sec-4 -->

[PCP/Theorem.lean](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Theorem.lean)

```lean
theorem np_subset_pcp (L : Language) (hL : InNP Machine.PolyTimeRel L) :
    ∃ (V : Verifier) (alg : VerifierAlg) (a b q : ℕ) (p : Polynomial ℕ),
      Machine.PolyTimeAlg alg ∧
      V.ImplementedBy alg ∧
      V.queries = q ∧
      V.CanonicalRandomness a b ∧
      (∀ x : List Bool, V.ReadsBelow x (p.eval x.length)) ∧
      (∀ x : List Bool, L x → V.CompleteAt x) ∧
      (∀ x : List Bool, ¬ L x → V.SoundAt x (1 / 2))
```

Line by line:

| Lean | Meaning |
| --- | --- |
| `(L : Language) (hL : InNP Machine.PolyTimeRel L)` | Let L ⊆ {0,1}* be a language in NP. |
| `∃ (V : Verifier) (alg : VerifierAlg) (a b q : ℕ) (p : Polynomial ℕ),` | Then there are a verifier V, an algorithm, constants a, b, q and a polynomial p, all chosen before any input x, such that: |
| `Machine.PolyTimeAlg alg ∧` | the algorithm runs in polynomial time, |
| `V.ImplementedBy alg ∧` | and it computes exactly V; |
| `V.queries = q ∧` | V reads at most q proof bits; |
| `V.CanonicalRandomness a b ∧` | on inputs of length n, V uses exactly a⌈log₂(n+2)⌉ + b random bits; |
| `(∀ x : List Bool, V.ReadsBelow x (p.eval x.length)) ∧` | on input x, V reads only the first p(\|x\|) bits of the proof; |
| `(∀ x : List Bool, L x → V.CompleteAt x) ∧` | if x ∈ L, some proof is accepted with probability 1; |
| `(∀ x : List Bool, ¬ L x → V.SoundAt x (1 / 2))` | if x ∉ L, every proof is accepted with probability at most 1/2. |

That is NP ⊆ PCP(O(log n), O(1)), with perfect completeness and a
polynomial-time verifier.
<!-- /passage:sec-4 -->

<a id="5"></a>

## 5. Checks on the definitions

<!-- passage:sec-5 -->

A formal theorem is only as good as its definitions. Two further theorems guard
against definitions that are accidentally too strong or too weak.

### NP is the textbook class

[PCP/Complexity/ReferenceNPConverse.lean](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Complexity/ReferenceNPConverse.lean)

```lean
theorem inNP_iff_mem {L : Complexity.Language} :
    PCP.InNP Machine.PolyTimeRel L ↔ L ∈ Complexity.NP
```

`Complexity.NP` comes from Complexitylib, an independent Lean library whose NP
definition is included unmodified in [vendor](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/vendor/README.md). It
defines NP = ⋃<sub>k</sub> NTIME(n<sup>k</sup>) with multi-tape nondeterministic
Turing machines, following Arora–Barak. So the class in the main theorem is the
standard one. `PCP.ReferenceNP.np_subset_pcp` states the main theorem directly
for `Complexity.NP`.

### The converse holds

[PCP/ReverseConcrete.lean](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/ReverseConcrete.lean)

```lean
theorem pcp_subset_np_concrete (L : Language) (V : Verifier) (alg : VerifierAlg) (a b : ℕ)
    (p : Polynomial ℕ) (halg : Machine.PolyTimeAlg alg) (himpl : V.ImplementedBy alg)
    (hrand : V.CanonicalRandomness a b)
    (hlen : ∀ x : List Bool, V.ReadsBelow x (p.eval x.length))
    (hcomplete : ∀ x : List Bool, L x → V.CompleteAt x)
    (hsound : ∀ x : List Bool, ¬ L x → V.SoundAt x (1 / 2)) :
    InNP Machine.PolyTimeRel L
```

Any language with a verifier of the kind produced by the main theorem is in NP.
This shows the verifier notion is not too generous: a "verifier" cannot hide
extra computing power in its definition. Together the two directions give
NP = PCP(O(log n), O(1)) for these definitions.
<!-- /passage:sec-5 -->

<a id="6"></a>

## 6. The explicit constants

<!-- passage:sec-6 -->

The proof goes through 3-COLOR. An input x is read as a graph: x = 1<sup>N</sup>0
followed by the N² adjacency bits in row-major order (missing bits are 0, so
every bit string is a graph). One run of the 3-COLOR verifier satisfies:

[PCP/Algebraic/ThreeColorCanonicalVerifier.lean](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorCanonicalVerifier.lean)

```lean
theorem verification_guarantees :
    verifier.queries = 187 ∧ verifier.CanonicalRandomness 32000000 32000000 ∧
      (∀ x, verifier.ReadsBelow x (proofBound.eval x.length)) ∧
      (∀ x, (ThreeColorEncoding.graph x).Colorable 3 → verifier.CompleteAt x) ∧
      (∀ x, ¬ (ThreeColorEncoding.graph x).Colorable 3 →
        verifier.SoundAt x (1 - ThreeColorBinaryVerifier.gap))
```

Evaluating `ThreeColorBinaryVerifier.gap` gives 1/R with
R = 1,137,847,282,503,168. The amplified verifier repeats the single run R times:

[PCP/Algebraic/ThreeColorAmplifiedVerifier.lean](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorAmplifiedVerifier.lean)

```lean
theorem verification_guarantees :
    0 < repetitions ∧ verifier.queries = repetitions * 187 ∧
      verifier.CanonicalRandomness (repetitions * 32000000) (repetitions * 32000000) ∧
      (∀ x, verifier.ReadsBelow x (ThreeColorCanonicalVerifier.proofBound.eval x.length)) ∧
      (∀ x, (ThreeColorEncoding.graph x).Colorable 3 → verifier.CompleteAt x) ∧
      (∀ x, ¬ (ThreeColorEncoding.graph x).Colorable 3 → verifier.SoundAt x (1 / 2))
```

| Quantity | Value for 3-COLOR |
| --- | --- |
| Repetitions R = ⌈1/gap⌉ | 1,137,847,282,503,168 ≈ 1.1·10¹⁵ |
| Queries 187·R | 212,777,441,828,092,416 ≈ 2.1·10¹⁷ |
| a = b = 32·10⁶·R | 36,411,113,040,101,376,000,000 ≈ 3.6·10²² |

For a general language L, the reduction maps x to a graph of length at most
p(|x|), and the randomness is padded to a = 32·10⁶·R·deg p and
b = 32·10⁶·R·(⌈log₂(p(1)+2)⌉ + 1). Nobody tried to optimize these constants;
most of the size comes from loose bookkeeping in the formal proof.
<!-- /passage:sec-6 -->

<a id="7"></a>

## 7. Low-degree testing statements

<!-- passage:sec-7 -->

Three results from the algebraic core, each with the paper's version for
comparison.

### Lemma 3.3: the generator low-degree test

[PCP/Algebraic/WeightedConstraintSoundness.lean](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/WeightedConstraintSoundness.lean),
namespace `WeightedConstraint` (here V is a vector space, not a verifier)

```lean
variable {F V I : Type*} [Field F] [AddCommGroup V] [Module F V]
variable [Fintype I]

noncomputable def predict (a w : I → F) (f : V → F) (x v : V) : F :=
  ∑ i, w i * f (x + a i • v)

variable [Fintype F] [DecidableEq F] [Fintype V]

noncomputable def rejectionRate (a w : I → F) (f : V → F) : ℚ :=
  relativeDistance (fun s : V × V => f s.1) (fun s => predict a w f s.1 s.2)
```

[PCP/Algebraic/GeneratorLowDegreeTest.lean](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/GeneratorLowDegreeTest.lean)

```lean
variable {F σ : Type*} [Field F] {c : ℕ}

def nodes (c : ℕ) (ζ : F) (i : Fin (c + 1)) : F := ζ ^ (i.val + 1)

noncomputable def weights (c : ℕ) (ζ : F) : Fin (c + 1) → F :=
  LagrangeConstraint.weight (nodes c ζ) 0

variable [Fintype F] {ζ : F}
variable [DecidableEq F] [Fintype σ] [DecidableEq σ]

noncomputable def rejectionRate (c : ℕ) (ζ : F) (f : (σ → F) → F) : ℚ :=
  WeightedConstraint.rejectionRate (nodes c ζ) (weights c ζ) f

theorem exists_close (hq : 2 * c < Fintype.card F)
    (hζ : IsPrimitiveRoot ζ (Fintype.card F - 1)) (f : (σ → F) → F)
    {δ : ℚ} (hrej : rejectionRate c ζ f ≤ δ) (hδ : δ < 1 / (2 * (c + 2 : ℚ) ^ 2)) :
    ∃ P : MvPolynomial σ F, P.totalDegree ≤ c ∧
      relativeDistance f (fun x => MvPolynomial.eval x P) ≤ 2 * δ
```

The nodes are ζ, ζ², …, ζ<sup>c+1</sup>, and `weights` are the Lagrange
coefficients η<sub>i</sub> for interpolating at 0 from those nodes, as in
Fact 2.7. The test picks u, v ∈ F<sup>σ</sup> uniformly and rejects if
f(u) ≠ Σ<sub>i</sub> η<sub>i</sub> f(u + ζ<sup>i</sup>v), which is the paper's
check Σ<sub>i=0</sub><sup>c+1</sup> η<sub>i</sub> f(u + ζ<sub>i</sub> v) ≠ 0
with η<sub>0</sub> = −1 and ζ<sub>0</sub> = 0.

*Statement.* Let F be a finite field with |F| > 2c and let ζ generate
F<sup>×</sup>. If the test rejects f with probability at most
δ < 1/(2(c+2)²), then f is within distance 2δ of a polynomial of total degree at
most c. The paper assumes instead that |F| is a power of 2 larger than Cc³.

### Theorem 2.12: the point-versus-line test

[PCP/Algebraic/PolynomialLine.lean](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/PolynomialLine.lean)

```lean
def point (u v : σ → R) (a : R) : σ → R := u + a • v
```

[PCP/Algebraic/PointLineTest.lean](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/PointLineTest.lean)

```lean
variable {F σ : Type*} [Field F] {c : ℕ}

abbrev LineTable (F σ : Type*) [Field F] (c : ℕ) :=
  ((σ → F) × (σ → F)) → {p : Polynomial F // p.natDegree ≤ c}

def check (f : (σ → F) → F) (table : LineTable F σ c)
    (u v : σ → F) (t : F) : F :=
  f (point u v t) - (table (u, v)).val.eval t

variable [Fintype F] [DecidableEq F] [Fintype σ] [DecidableEq σ]

def rejectionRate (f : (σ → F) → F) (table : LineTable F σ c) : ℚ :=
  relativeDistance
    (fun s : ((σ → F) × (σ → F)) × F => check f table s.1.1 s.1.2 s.2)
    (fun _ => 0)
```

[PCP/Algebraic/PointLineConstants.lean](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/PointLineConstants.lean)

```lean
def fieldFactor : ℕ := 1000000

def smallError : ℚ := 1 / 4000000
```

[PCP/Algebraic/PointLineSoundness.lean](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/PointLineSoundness.lean)

```lean
variable {F σ : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype σ] [DecidableEq σ] {d : ℕ}

theorem exists_close_of_small_rejection
    (hq : fieldFactor * d ^ 3 ≤ Fintype.card F) (f : (σ → F) → F)
    (table : LineTable F σ d) (hδ : rejectionRate f table ≤ smallError) :
    ∃ P : MvPolynomial σ F, P.totalDegree ≤ d ∧
      relativeDistance f (fun x => MvPolynomial.eval x P) ≤ 2 * rejectionRate f table
```

Here `point u v t` is u + t·v. The lines table assigns to every ordered pair
(u, v), including v = 0, a univariate polynomial of degree at most d; nothing
forces different parametrizations of the same line to agree. The test picks
u, v ∈ F<sup>σ</sup> and t ∈ F uniformly and rejects if f(u + tv) differs from
the table's polynomial at t.

*Statement.* If |F| ≥ 10⁶·d³ and the test rejects with probability
ρ ≤ 1/(4·10⁶), then f is within distance 2ρ of a polynomial of total degree at
most d. This is ALMSS Theorem 45 with explicit constants, and it includes d = 0.
The paper's Theorem 2.12 samples t from F<sup>×</sup> and concludes 4δ; the Lean
proof samples t from all of F, as ALMSS does.

### ALMSS Theorem 69: bivariate agreement (Arora–Safra)

[PCP/Algebraic/BivariateAgreement.lean](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/BivariateAgreement.lean)

```lean
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}

theorem exists_polynomial_of_row_column_agreement (hd : 0 < d)
    (hq : 1000 * d ^ 3 ≤ Fintype.card F)
    (f : F × F → F) (R C : F → Polynomial F)
    (hR : ∀ y, (R y).natDegree ≤ d) (hC : ∀ x, (C x).natDegree ≤ d)
    {ε : ℚ} (hrows : relativeDistance f (fun z => (R z.2).eval z.1) ≤ ε)
    (hcols : relativeDistance f (fun z => (C z.1).eval z.2) ≤ ε)
    (hε : ε ≤ 1 / 100) :
    ∃ P : MvPolynomial (Fin 2) F, (∀ j, P.degreeOf j ≤ d) ∧
      relativeDistance f (fun z => MvPolynomial.eval ![z.1, z.2] P) ≤ 4 * ε
```

*Statement.* Let d ≥ 1 and |F| ≥ 1000·d³. Suppose f : F² → F is within
ε ≤ 1/100 of the table (x, y) ↦ R<sub>y</sub>(x) and of the table
(x, y) ↦ C<sub>x</sub>(y), where every R<sub>y</sub> and C<sub>x</sub> has degree
at most d. Then f is within 4ε of a polynomial P of degree at most d in each
variable.

ALMSS states this without proof and attributes it to Arora and Safra. The row
and column polynomials here are arbitrary, not necessarily ALMSS's best-fitting
ones, so the statement is slightly more general. ALMSS's unnamed constants
become 1000 and 1/100.
<!-- /passage:sec-7 -->

<a id="8"></a>

## 8. Reading a proof

<!-- passage:sec-8 -->

Here is the complete proof of the bivariate theorem, from the same file. Most
proofs in the development look like this: a short chain of steps, each citing an
earlier result.

```lean
  have hdq := (fieldSize_bounds hd hq).2.2.2.2
  obtain ⟨a, ha⟩ := BivariateColumnSelection.exists_good_columns f R C hrows hcols hε hdq
  obtain ⟨P, hP, _, _, hclose⟩ := exists_nearby_of_close_columns hd hq a a.injective
    (fun i => C (a i)) (fun i => hC (a i)) R hR ha
  have hnear : relativeDistance f (fun z => MvPolynomial.eval ![z.1, z.2] P) ≤
      ε + 1 / 9 :=
    (relativeDistance_triangle f (fun z => (R z.2).eval z.1) _).trans
      (add_le_add hrows hclose)
  refine ⟨P, hP, BivariateAgreementBoost.distance_le_four_mul f R C hR hC P hP
    hrows hcols hnear ?_⟩
  have hqpos : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hfrac : (d : ℚ) / Fintype.card F ≤ 1 / 20 := by
    apply (div_le_iff₀ hqpos).mpr
    have h : (20 : ℚ) * d ≤ Fintype.card F := by exact_mod_cast hdq
    linarith
  linarith
```

1. `have hdq := …` records a consequence of |F| ≥ 1000d³, namely 20d ≤ |F|.
2. `obtain ⟨a, ha⟩ := …` applies an existence result and names the witness.
   Here an averaging argument gives 10d distinct points a<sub>i</sub> such that
   on each column x = a<sub>i</sub>, the row table is within 1/10 of
   C<sub>a<sub>i</sub></sub>.
3. The next `obtain` applies Arora–Safra's Lemma 5.2.1 in two variables. Since
   every row of the row table is exactly a polynomial, it gives P of degree at
   most d in each variable, within 1/9 of the row table.
4. `have hnear` uses the triangle inequality: f is within ε + 1/9 of P.
5. `refine ⟨P, hP, …⟩` offers the same P as the answer. A sharpening step turns
   ε + 1/9 into 4ε, which is the bound Theorem 69 states; Arora–Safra's lemma
   concludes only 1/9. The `?_` leaves one side condition to prove.
6. The last lines prove that side condition, d/|F| ≤ 1/20, by arithmetic.
   `linarith` is an automatic prover for linear inequalities.

The steps cited above are proved in these files, under `PCP/Algebraic/`:

| File | Content |
| --- | --- |
| `BivariateColumnSelection.lean` | Choosing the 10d good columns by averaging. |
| `BerlekampWelch.lean` | Arora–Safra Lemma 5.2.5 (Berlekamp–Welch). |
| `BerlekampWelchMatrix.lean`, `PolynomialMatrixKernel.lean`, `BerlekampWelchCertificate.lean` | Arora–Safra Lemma 5.2.7: solving the error-locator system over a polynomial ring. |
| `BivariateCleanRectangle.lean` | Arora–Safra Lemma 5.2.2: a large error-free rectangle. |
| `BivariateInterpolation.lean`, `BivariateAgreementFromRectangle.lean` | Arora–Safra Corollary 5.2.3: interpolation, giving distance 1/9. |
| `BivariateAgreementBoost.lean` | From ε + 1/9 to 4ε. |
| `PointLineCrossing.lean`, `BivariateCrossingSoundness.lean` | ALMSS Corollary 70, which uses the theorem above. |

Some other words you will meet in proofs: `exact h` (h proves the goal),
`apply h` (reduce the goal to h's hypotheses), `intro x` (to prove ∀ x or
A → B, take x or assume A), `simp` and `norm_num` (simplify), `omega`,
`linarith` and `nlinarith` (automatic arithmetic), `exact_mod_cast` (move
between ℕ and ℚ).
<!-- /passage:sec-8 -->

<a id="9"></a>

## 9. Finding your way around

<!-- passage:sec-9 -->

- [PCP/Theorem.lean](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Theorem.lean): the main theorem.
  [PCP/ReverseConcrete.lean](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/ReverseConcrete.lean): the converse.
- [PCP/Verifier/](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Verifier): verifiers, query trees, acceptance
  probability.
- [PCP/Complexity/](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Complexity): the machine model, runtime
  certificates for the verifier, and the comparison with Complexitylib's NP.
- [PCP/Reduction/](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Reduction): the reduction from NP to 3-COLOR.
- [PCP/Algebraic/](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic): the algebraic proof itself, including
  everything in Sections 6–8 of this guide.
- [vendor/](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/vendor/README.md): the unchanged Complexitylib and CSLib
  sources used for the reference definition of NP.

The [PCP guide](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/docs/pcp/README.md) has a proof map from each numbered result in the
paper to the files that prove it, and a section listing where the Lean proof
departs from the paper.

To browse the code, clone the repository and open it in VS Code with the Lean 4
extension. Hovering over any name shows its statement and doc comment;
Cmd-click (Ctrl-click) jumps to its definition; and placing the cursor inside a
`by` block shows, in the side panel, what remains to be proved at that point. In
a scratch file you can type `#check PCP.np_subset_pcp` to see a statement or
`#print axioms PCP.np_subset_pcp` to see the axioms it uses. From the repository
root, `lake build PCP` checks the whole development and
`scripts/pcp/axiom-audit.sh` runs the audit.
<!-- /passage:sec-9 -->

<a id="10"></a>

## 10. Learning more Lean

<!-- passage:sec-10 -->

- [*Mathematics in Lean*](https://leanprover-community.github.io/mathematics_in_lean/)
  (Avigad and Massot): the standard introduction for mathematicians. The first
  few chapters are enough to read statements.
- [*Theorem Proving in Lean 4*](https://lean-lang.org/theorem_proving_in_lean4/):
  the underlying logic, including implicit arguments and type classes.
- [The Natural Number Game](https://adam.math.hhu.de/): a hands-on start in a
  browser, a couple of hours.
- [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/):
  searchable; every name, such as `MvPolynomial.degreeOf`, links to its
  definition.
- [Lean Zulip](https://leanprover.zulipchat.com/): a responsive community, with
  a channel for new members.
- [Learning resources](https://leanprover-community.github.io/learn.html) on the
  Lean community site, including Kevin Buzzard's course notes
  [*Formalising Mathematics*](https://b-mehta.github.io/formalising-mathematics-notes/).
<!-- /passage:sec-10 -->

