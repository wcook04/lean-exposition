/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.Hadamard

/-!
# Two-query self-correction of the low-degree Hadamard encoding

A §3.4: to recover the entry at `P`, sample `R` uniformly and return
`w(P + R) - w(R)`. Against an additive codeword, failure has probability at
most twice the received word's relative distance. The proof uses translation
invariance of uniform counting and the union bound expressed by Hamming distance.
No running-time certificate or robust syntactic tester is asserted here.
-/

namespace PCP.Algebraic.Hadamard

open BinaryPolynomialSpace

section Additive

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

/-- The two queries used by the correction rule, with random seed `R`. -/
def selfCorrect (w : V → W) (P R : V) : W := w (P + R) - w R

@[simp] theorem selfCorrect_addHom (E : V →+ W) (P R : V) :
    selfCorrect E P R = E P := by
  simp [selfCorrect]

/-- A two-query correction rule for any finite additive codeword. -/
theorem selfCorrect_failure_le [Fintype V] [DecidableEq W] (E : V →+ W)
    (w : V → W) (P : V) :
    relativeDistance (selfCorrect w P) (fun _ => E P) ≤ 2 * relativeDistance w E := by
  change relativeDistance (fun R : V => w (P + R) - w R) (fun _ => E P) ≤
    2 * relativeDistance w E
  have ht := relativeDistance_sub_le (fun R => w (P + R)) w (fun R => E (P + R)) E
  have he : relativeDistance (fun R => w (P + R)) (fun R => E (P + R)) =
      relativeDistance w E := relativeDistance_comp_equiv (Equiv.addLeft P) w E
  rw [he] at ht
  simpa only [map_add, add_sub_cancel_right, two_mul] using ht

end Additive

variable {t r : ℕ}

/-- A §3.4: at every requested entry, success is at least `1 - 2ε`. -/
theorem selfCorrect_success_ge (x : Fin t → ZMod 2) (w : Coefficients t r → ZMod 2)
    (P : Coefficients t r) {ε : ℚ} (hw : relativeDistance w (encode r x) ≤ ε) :
    1 - 2 * ε ≤ relativeAgreement (selfCorrect w P) (fun _ => encode r x P) := by
  have h := selfCorrect_failure_le (encode r x).toAddMonoidHom w P
  rw [relativeAgreement_eq_one_sub_relativeDistance]
  change relativeDistance (selfCorrect w P) (fun _ => encode r x P) ≤
    2 * relativeDistance w (encode r x) at h
  linarith

end PCP.Algebraic.Hadamard
