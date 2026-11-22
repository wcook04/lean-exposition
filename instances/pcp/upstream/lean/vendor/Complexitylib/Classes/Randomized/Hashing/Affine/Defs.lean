/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.Hashing.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Ring.BooleanRing

/-!
# Affine pairwise-independent hashing -- definitions

The seed encodes one affine linear form over the Boolean ring for each output
bit. Each row has `domainWidth` coefficients and one constant coefficient.
-/


@[expose] public section

namespace Complexity

namespace PairwiseIndependentHash

/-- Number of random bits in the affine family from `domainWidth` bits to
`rangeWidth` bits. -/
def affineSeedWidth (domainWidth rangeWidth : ℕ) : ℕ :=
  rangeWidth * (domainWidth + 1)

/-- Row-major equivalence between affine coefficient rows and the flat seed. -/
def affineSeedEquiv (domainWidth rangeWidth : ℕ) :
    (Fin rangeWidth → BitString (domainWidth + 1)) ≃
      BitString (affineSeedWidth domainWidth rangeWidth) :=
  (Equiv.curry (Fin rangeWidth) (Fin (domainWidth + 1)) Bool).symm.trans
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Bool))

/-- Coefficient rows decoded from a flat affine-family seed. -/
def affineRows {domainWidth rangeWidth : ℕ}
    (seed : BitString (affineSeedWidth domainWidth rangeWidth)) :
    Fin rangeWidth → BitString (domainWidth + 1) :=
  fun row column => seed (finProdFinEquiv (row, column))

/-- Flatten coefficient rows into the affine family's row-major seed. -/
def affineSeedOfRows {domainWidth rangeWidth : ℕ}
    (rows : Fin rangeWidth → BitString (domainWidth + 1)) :
    BitString (affineSeedWidth domainWidth rangeWidth) :=
  affineSeedEquiv domainWidth rangeWidth rows

/-- Append a constant `1` coordinate to an input. -/
def affineAugment {domainWidth : ℕ} (input : BitString domainWidth) :
    BitString (domainWidth + 1) :=
  Fin.snoc input true

/-- Evaluate the affine coefficient matrix on an augmented input. Addition in
the Boolean ring is XOR and multiplication is AND. -/
def affineEval {domainWidth rangeWidth : ℕ}
    (seed : BitString (affineSeedWidth domainWidth rangeWidth))
    (input : BitString domainWidth) : BitString rangeWidth :=
  fun row => ∑ column,
    affineRows seed row column * affineAugment input column

end PairwiseIndependentHash

end Complexity
