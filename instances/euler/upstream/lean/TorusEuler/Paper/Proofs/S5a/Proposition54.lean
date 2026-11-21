import TorusEuler.Paper.S5.Statements
import TorusEuler.Paper.S34A.Statements
import TorusEuler.Paper.Proofs.S5a.Library.Seed
import TorusEuler.Paper.Proofs.S5a.Library.MeanUnique
import TorusEuler.Paper.Proofs.S5a.Library.Identity
import TorusEuler.Paper.Proofs.S5a.Library.Switch
import TorusEuler.Paper.Proofs.S5Bridge.Leading

/-!
# Proof of Proposition 5.4 from Theorem 4.2

The existence and uniqueness of the profiles are the library construction over the mean solver and
the transverse solver (`Bridge.exists_isExpansion`, `Bridge.IsExpansion.unique`), the identities are
`Lib.S5a.isExpansion_identities`, and the seed is `Lib.S5a.exists_isSeed`.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

noncomputable section

/-- Proof of **Proposition 5.4** (`cc:uf:hier:prop:identity`), following
`sections/06c_finite_hierarchy.tex:334-391` (latest numbering (5.25)-(5.30), (3.4), (3.7), (3.8)).

* `h4_2` (Theorem 4.2) enters where the TeX proof says "the mean equation has smooth solutions by
  Theorem 4.2" (line 372): the mean equation (5.11) for the parent of §5.1 is solvable with
  zero-mean label pressure (`Lib.S5a.meanSolvable_of_theorem42`, the existence and smoothness items
  of `h4_2` for the source `L = -∫_0^t (D_aX)^T f̄`, (4.11)), and its normalized solution is unique
  (`Lib.S5a.meanUnique_of_theorem42`, the uniqueness clause of the first item of `h4_2` for the
  integrated system (4.9)). Together with the transverse solve (5.15) (an ODE at each label,
  `Bridge.transverseSolvable`) they give the existence of the profiles (`Bridge.exists_isExpansion`)
  and their uniqueness (`Bridge.IsExpansion.unique`).
* The seed of §5.1 exists by the linear ODE (3.2) at each label (`Lib.S5a.exists_isSeed`).
* The identities (lines 334-367) use the leading switch `(∂_t+M)V₁ + κ∂_s𝗉₁ = χ̃'A₁` from (3.4) and
  (3.7) (`Lib.S5a.leadingSwitch`, lines 355-358), the divergence identity `𝐝̃·W = 0` (3.5), (3.6)
  and the supports (lines 376-391): `Lib.S5a.isExpansion_identities`.

The envelope exponent is `a₀ = 3`, so that `2ℓ_* < 1/2` (`Bridge.radius_fits`). -/
theorem Proof.proposition_5_4_of (h4_2 : Statement.theorem_4_2) : Statement.proposition_5_4 := by
  refine ⟨3, ?_⟩
  intro a ha T hT U X pU k D lam t₀ center d χ hP hL hO
  have hℓ : 0 < S5.radius D a := Bridge.radius_pos hP a
  have hfit := Bridge.radius_fits hP.scale_ge_two ha
  have hh := Bridge.width_pos hP
  have hh₁ := Bridge.width_le_one hP
  have hM := Lib.S5a.meanSolvable_of_theorem42 h4_2 d hP
  have hMU := Lib.S5a.meanUnique_of_theorem42 h4_2 d hP
  refine ⟨Lib.S5a.exists_isSeed d hP hL hO, fun amp hamp P hP2 => ?_⟩
  refine ⟨Bridge.exists_isExpansion d hM hP hL hamp hℓ hfit hh hh₁ χ (by omega),
    fun R S R' S' u u' hu hu' => Bridge.IsExpansion.unique d hMU hu hu', ?_⟩
  intro R S u hu
  exact Lib.S5a.isExpansion_identities d hP hL hamp hℓ hfit hh hh₁ hP2 hu
    (Lib.S5a.leadingSwitch d hL hamp hh hh₁ hu)

end

end TorusEuler.Paper
