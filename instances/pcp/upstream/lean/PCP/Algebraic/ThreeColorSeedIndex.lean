/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinarySeedEncoding
import PCP.Algebraic.BinarySeedPadding
import PCP.Algebraic.BooleanCoefficientIndex

/-!
# Structural indexing of the seven-branch sampler

The actual raw sampler is encoded by explicit products, finite function spaces
and mixed-radix expansion. Field elements use the supplied binary coordinates;
coefficient masks use their computable monomial indexing. The final cardinality
identity only casts the already constructed integer index to the previously
proved bit length. No arbitrary finite enumeration is used in this codec.

Computability is relative to the supplied field coordinates. No running-time
bound or computable construction of those coordinates is asserted here.
-/

namespace PCP.Algebraic.ThreeColorSeedIndex

open BinaryPolynomialSpace ThreeColorFullFieldSampling ThreeColorSeedSize

/-- A concrete finite enumeration together with its computed length. -/
structure Codec (A : Type*) where
  size : ℕ
  equiv : A ≃ Fin size

namespace Codec

variable {A B : Type*}

/-- The integer interval is already indexed. -/
def fin (n : ℕ) : Codec (Fin n) := ⟨n, Equiv.refl _⟩

/-- Mixed-radix encoding of an ordered pair. -/
def prod (a : Codec A) (b : Codec B) : Codec (A × B) :=
  ⟨a.size * b.size, (Equiv.prodCongr a.equiv b.equiv).trans finProdFinEquiv⟩

/-- Concatenated indexing of a tagged union. -/
def sum (a : Codec A) (b : Codec B) : Codec (A ⊕ B) :=
  ⟨a.size + b.size, (Equiv.sumCongr a.equiv b.equiv).trans finSumFinEquiv⟩

/-- A function is encoded in the explicit order supplied for its domain. -/
def function (a : Codec A) (b : Codec B) : Codec (A → B) :=
  ⟨b.size ^ a.size, (Equiv.arrowCongr a.equiv b.equiv).trans finFunctionFinEquiv⟩

/-- A heterogeneous tuple uses the explicit mixed radix of its component sizes. -/
def piFin {k : ℕ} {A : Fin k → Type*} (a : ∀ i, Codec (A i)) : Codec (∀ i, A i) :=
  ⟨∏ i, (a i).size, (Equiv.piCongrRight fun i => (a i).equiv).trans finPiFinEquiv⟩

/-- A size proof only changes the bound attached to an existing integer code. -/
def cast (a : Codec A) {n : ℕ} (h : a.size = n) : A ≃ Fin n :=
  a.equiv.trans (finCongr h)

theorem size_eq_card [Fintype A] (a : Codec A) : a.size = Fintype.card A := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr a.equiv).symm

end Codec

/-- Boolean choices use false = zero and true = one. -/
def boolCodec : Codec Bool :=
  ⟨2, BinarySeedPadding.boolEquiv.trans (ZMod.finEquiv 2).toEquiv.symm⟩

/-- A binary label uses its explicit little-endian expansion. -/
def bitsCodec (t : ℕ) : Codec (Fin t → ZMod 2) :=
  ⟨2 ^ t, (BinarySeedPadding.finSeedEquiv t).symm⟩

/-- Coefficients use the actual increasing-mask monomial indexing. -/
def coefficientCodec (t r : ℕ) : Codec (Coefficients t r) :=
  ⟨2 ^ BooleanCoefficientIndex.dimension t r, BooleanCoefficientIndex.coefficientEquiv t r⟩

/-- Every random choice in HadTest is encoded, including all loop factors. -/
def hadamardCodec (t r : ℕ) : Codec (Hadamard.TestRandomness t r) :=
  (coefficientCodec t r).prod ((coefficientCodec t r).prod
    ((coefficientCodec t 1).prod (Codec.piFin fun k : Fin (r - 1) =>
      coefficientCodec t (k.val + 1))))

section Field

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {t : ℕ}

/-- Field elements are encoded using the supplied, actual binary coordinates. -/
def fieldCodec (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) : Codec F :=
  ⟨2 ^ t, ρ.toEquiv.trans (bitsCodec t).equiv⟩

/-- The exact product seed of the binary tester, retaining both fair-choice branches. -/
def binaryLowDegreeCodec {σ : Type*} (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (σc : Codec σ) (r : ℕ) : Codec (BinaryLowDegreeTest.TestRandomness F σ t r) :=
  let p := σc.function (fieldCodec ρ)
  boolCodec.prod ((p.prod (hadamardCodec t r)).prod
    (((p.prod p).prod (fieldCodec ρ)).prod (bitsCodec t)))

/-- The inner set-multilinear point uses its ordered pair of finite coordinates. -/
def innerPointCodec (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (m c : ℕ) :
    Codec (BinaryLocalCorrection.InnerPoint F m c) :=
  ((Codec.fin c).prod (Codec.fin m)).function (fieldCodec ρ)

/-- Encode the entire inner tester seed, not just the branch it happens to read. -/
def innerCodec (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (m c : ℕ) :
    Codec (BinaryLocalCorrection.InnerSeed F m c t) :=
  binaryLowDegreeCodec ρ ((Codec.fin c).prod (Codec.fin m)) 1

/-- Encode an actual outer encoded-line tester seed. -/
def outerCodec {σ : Type*} (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (σc : Codec σ) (m c r : ℕ) : Codec (EncodedLineLowDegreeTest.Sample F σ m c t r) :=
  let p := σc.function (fieldCodec ρ)
  (p.prod p).prod ((fieldCodec ρ).prod
    (((innerPointCodec ρ m c).prod (bitsCodec t)).prod
      ((hadamardCodec t r).prod (innerCodec ρ m c))))

/-- A correction call now has a whole-field parameter, so every component has binary size. -/
def callCodec {σ : Type*} (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (σc : Codec σ) (m c : ℕ) : Codec (RawCallSeed F σ m c t) :=
  (σc.function (fieldCodec ρ)).prod ((fieldCodec ρ).prod
    ((innerPointCodec ρ m c).prod (innerCodec ρ m c)))

/-- Keep the shared homogeneous label once, and encode both independent correction calls. -/
def gridCodec (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (n m c : ℕ) :
    Codec (RawGridRandomness F n m c t) :=
  let a := callCodec ρ ((Codec.fin n).sum (Codec.fin n)) m c
  (bitsCodec t).prod (a.prod a)

/-- A derived-grid seed includes its own fresh coefficient mask. -/
def derivedCodec (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (n m c r : ℕ) :
    Codec (RawDerivedSample F n m c t r) :=
  ((Codec.fin n).function (fieldCodec ρ)).prod
    ((gridCodec ρ n m c).prod (coefficientCodec t r))

/-- Every branch uses its actual product structure and its actual coordinate order. -/
def branchCodec (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (n m c : ℕ)
    (i : Fin 7) : Codec (RawBranchSeed F n m c t i) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))) i
  · exact outerCodec ρ (Codec.fin n) m c 3
  · exact outerCodec ρ ((Codec.fin n).sum (Codec.fin n)) m c 1
  · exact outerCodec ρ ((Codec.fin n).sum (Codec.fin n)) m c 3
  · exact outerCodec ρ ((Codec.fin (n + n)).sum (Codec.fin (n + n))) m c 1
  · exact derivedCodec ρ n m c 3
  · exact derivedCodec ρ (n + n) m c 3
  · let p := (Codec.fin n).function (fieldCodec ρ)
    exact (p.prod p).prod (bitsCodec t)

/-- The complete seven-tuple is encoded by heterogeneous mixed-radix expansion. -/
def rawCodec (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (n m c : ℕ) :
    Codec (RawSample F n m c t) := Codec.piFin (branchCodec ρ n m c)

/-- Only the bound on the already constructed integer code uses the cardinality theorem. -/
theorem rawCodec_size (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (n m c : ℕ) :
    (rawCodec ρ n m c).size = 2 ^ rawBits n m c t := by
  let : Fintype F := Fintype.ofEquiv (Fin t → ZMod 2) ρ.toEquiv.symm
  exact (rawCodec ρ n m c).size_eq_card.trans
    (card_rawSample (card_field_of_coordinates ρ))

/-- Explicit integer indexing of the raw sampler, relative to the field coordinates. -/
def integerEquiv (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (n m c : ℕ) :
    RawSample F n m c t ≃ Fin (2 ^ rawBits n m c t) :=
  (rawCodec ρ n m c).cast (rawCodec_size ρ n m c)

/-- The actual raw sampler has a structural fair-bit codec of the exact stated length. -/
def equiv (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (n m c : ℕ) :
    RawSample F n m c t ≃ (Fin (rawBits n m c t) → ZMod 2) :=
  (integerEquiv ρ n m c).trans (BinarySeedPadding.finSeedEquiv (rawBits n m c t))

variable [Fintype F]

/-- Reindexing by the structural codec preserves every normalized disagreement. -/
theorem relativeDistance_equiv {B : Type*} [DecidableEq B]
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (n m c : ℕ)
    (f g : RawSample F n m c t → B) :
    relativeDistance (fun b => f ((equiv ρ n m c).symm b))
      (fun b => g ((equiv ρ n m c).symm b)) = relativeDistance f g :=
  relativeDistance_comp_equiv (equiv ρ n m c).symm f g

/-- The concrete whole-field test retains its exact rejection under this fair-bit encoding. -/
theorem rejection_equiv (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (n m c : ℕ)
    (f : RawSample F n m c t → Bool) :
    relativeDistance (fun b => f ((equiv ρ n m c).symm b)) (fun _ => true) =
      relativeDistance f (fun _ => true) :=
  relativeDistance_equiv ρ n m c f (fun _ => true)

end Field

end PCP.Algebraic.ThreeColorSeedIndex
