/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Reduction.FiniteDomainEncoding

/-!
# Explicit alphabet transport for finite constraint encodings

The supplied alphabet codec is fixed across the instance family. Only variable
and constraint counts grow with the input. All encoder data remains computable
relative to these explicit codecs, and the size bound retains the fixed arity.
-/

namespace PCP.Reduction.FiniteAlphabetEncoding

variable {A V C : Type*} {a v c d : ℕ}

def relation (eA : A ≃ Fin a) (R : C → (Fin d → A) → Bool) :
    C → (Fin d → Fin a) → Bool := fun e values => R e (eA.symm ∘ values)

theorem satisfiable_iff (eA : A ≃ Fin a) (R : C → (Fin d → A) → Bool)
    (s : C → Fin d → V) :
    (∃ x : V → Fin a, FiniteDomainConstraints.Holds (relation eA R) s x) ↔
      ∃ x : V → A, ∀ e, R e (fun i => x (s e i)) = true := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨eA.symm ∘ x, hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨eA ∘ x, fun e => ?_⟩
    simpa only [relation, Function.comp_def, Equiv.symm_apply_apply] using hx e

def encode (eA : A ≃ Fin a) (eV : V ≃ Fin v) (eC : C ≃ Fin c)
    (R : C → (Fin d → A) → Bool) (s : C → Fin d → V) : List Bool :=
  FiniteDomainEncoding.encode eV eC (relation eA R) s

theorem decode_colorable_iff (eA : A ≃ Fin a) (eV : V ≃ Fin v) (eC : C ≃ Fin c)
    (R : C → (Fin d → A) → Bool) (s : C → Fin d → V) :
    (Algebraic.ThreeColorEncoding.graph (encode eA eV eC R s)).Colorable 3 ↔
      ∃ x : V → A, ∀ e, R e (fun i => x (s e i)) = true :=
  (FiniteDomainEncoding.decode_colorable_iff _ _ _ _).trans (satisfiable_iff eA R s)

theorem length_encode_le_polynomial (eA : A ≃ Fin a) (eV : V ≃ Fin v) (eC : C ≃ Fin c)
    (R : C → (Fin d → A) → Bool) (s : C → Fin d → V)
    (pvars pcons : Polynomial ℕ) (n : ℕ) (hv : v ≤ pvars.eval n) (hc : c ≤ pcons.eval n) :
    (encode eA eV eC R s).length ≤ (FiniteDomainEncoding.outputPoly a d pvars pcons).eval n :=
  FiniteDomainEncoding.length_encode_le_polynomial _ _ _ _ _ _ _ hv hc

end PCP.Reduction.FiniteAlphabetEncoding
