/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.VanishingCertificate
import PCP.Algebraic.PolynomialDistance

/-!
# The algebraic zero-on-grid check

The warmup in A §6 checks `M(x,0) = 0` and `M(x,Z_H(x)) = P(x)` at a uniformly
random point. Here the oracles are evaluations of actual degree-bounded polynomials.
We prove perfect completeness and acceptance at most `d * |H| / |𝔽|` whenever
`P` does not vanish on the grid and both `P` and `M` have degree at most `d`.

This is the algebraic component, not Theorem 6.1: corrupted binary encodings,
local correction and query accounting are handled in `BinaryZeroOnGridCorrection`
and `BinaryZeroOnGridSoundness`.
-/

namespace PCP.Algebraic.GridVanishing

open Finset MvPolynomial

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {m d : ℕ}

/-- The fraction of points at which both certificate checks accept. -/
noncomputable def acceptanceRate (H : Finset 𝔽) (p : MvPolynomial (Fin m) 𝔽)
    (M : MvPolynomial (Fin m ⊕ Fin m) 𝔽) : ℚ :=
  relativeAgreement
    (fun x => (eval (Sum.elim x (fun _ => 0)) M,
      eval (Sum.elim x (fun i => eval x (coordinate H i))) M))
    (fun x => (0, eval x p))

theorem acceptanceRate_nonneg (H : Finset 𝔽) (p : MvPolynomial (Fin m) 𝔽)
    (M : MvPolynomial (Fin m ⊕ Fin m) 𝔽) : 0 ≤ acceptanceRate H p M :=
  relativeAgreement_nonneg _ _

theorem acceptanceRate_le_one (H : Finset 𝔽) (p : MvPolynomial (Fin m) 𝔽)
    (M : MvPolynomial (Fin m ⊕ Fin m) 𝔽) : acceptanceRate H p M ≤ 1 :=
  relativeAgreement_le_one _ _

theorem acceptanceRate_le_zero_agreement (H : Finset 𝔽) (p : MvPolynomial (Fin m) 𝔽)
    (M : MvPolynomial (Fin m ⊕ Fin m) 𝔽) :
    acceptanceRate H p M ≤ relativeAgreement
      (fun x => eval x (substitute (fun _ => 0) M)) 0 := by
  simpa [acceptanceRate, eval_substitute, Pi.zero_def] using relativeAgreement_le_map Prod.fst
    (fun x => (eval (Sum.elim x (fun _ => 0)) M,
      eval (Sum.elim x (fun i => eval x (coordinate H i))) M)) (fun x => (0, eval x p))

theorem acceptanceRate_le_recovery_agreement (H : Finset 𝔽) (p : MvPolynomial (Fin m) 𝔽)
    (M : MvPolynomial (Fin m ⊕ Fin m) 𝔽) :
    acceptanceRate H p M ≤ relativeAgreement
      (fun x => eval x (substitute (coordinate H) M)) (fun x => eval x p) := by
  simpa [acceptanceRate, eval_substitute] using relativeAgreement_le_map Prod.snd
    (fun x => (eval (Sum.elim x (fun _ => 0)) M,
      eval (Sum.elim x (fun i => eval x (coordinate H i))) M)) (fun x => (0, eval x p))

/-- A valid formal certificate passes both checks at every point. -/
theorem IsCertificate.acceptanceRate_eq_one {H : Finset 𝔽} {p : MvPolynomial (Fin m) 𝔽}
    {M : MvPolynomial (Fin m ⊕ Fin m) 𝔽} (hM : IsCertificate H p M) :
    acceptanceRate H p M = 1 := by
  have hzero (x : Fin m → 𝔽) : eval (Sum.elim x (fun _ => 0)) M = 0 := by
    have h := congrArg (eval x) hM.1
    simpa [eval_substitute] using h
  have hrecover (x : Fin m → 𝔽) :
      eval (Sum.elim x (fun i => eval x (coordinate H i))) M = eval x p := by
    simpa [eval_substitute] using congrArg (eval x) hM.2
  simp [acceptanceRate, hzero, hrecover]

/-- Above the degree/field-size threshold, both checks imply the formal certificate identities. -/
theorem isCertificate_of_acceptanceRate_gt (H : Finset 𝔽) (hH : H.Nonempty)
    (p : MvPolynomial (Fin m) 𝔽) (M : MvPolynomial (Fin m ⊕ Fin m) 𝔽)
    (hp : p.totalDegree ≤ d) (hM : M.totalDegree ≤ d)
    (hacc : ((d * H.card : ℕ) : ℚ) / Fintype.card 𝔽 < acceptanceRate H p M) :
    IsCertificate H p M := by
  have hd : d ≤ d * H.card := by
    exact Nat.le_mul_of_pos_right d (card_pos.mpr hH)
  constructor
  · apply eq_of_eval_agreement_gt (substitute (fun _ => 0) M) 0
      ((totalDegree_substitute_zero_le M).trans hM) (by simp)
    apply lt_of_le_of_lt _ (hacc.trans_le (acceptanceRate_le_zero_agreement H p M))
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast hd
  · apply eq_of_eval_agreement_gt (substitute (coordinate H) M) p
      ((totalDegree_substitute_coordinate_le H hH M).trans (Nat.mul_le_mul_right _ hM))
      (hp.trans hd)
    exact hacc.trans_le (acceptanceRate_le_recovery_agreement H p M)

/-- Algebraic soundness of the two-check test on degree-bounded polynomial oracles. -/
theorem acceptanceRate_le_of_not_vanishesOn (H : Finset 𝔽) (hH : H.Nonempty)
    (p : MvPolynomial (Fin m) 𝔽) (M : MvPolynomial (Fin m ⊕ Fin m) 𝔽)
    (hp : p.totalDegree ≤ d) (hM : M.totalDegree ≤ d) (hnot : ¬ VanishesOn H p) :
    acceptanceRate H p M ≤ ((d * H.card : ℕ) : ℚ) / Fintype.card 𝔽 := by
  by_contra h
  exact hnot (isCertificate_of_acceptanceRate_gt H hH p M hp hM (lt_of_not_ge h)).vanishesOn

/-- Perfect completeness, including the degree bound on the honest certificate. -/
theorem exists_acceptanceRate_eq_one (H : Finset 𝔽) (hH : H.Nonempty)
    (p : MvPolynomial (Fin m) 𝔽) (hp : VanishesOn H p) :
    ∃ M : MvPolynomial (Fin m ⊕ Fin m) 𝔽,
      M.totalDegree ≤ p.totalDegree ∧ acceptanceRate H p M = 1 := by
  obtain ⟨M, hdeg, hM⟩ := (vanishesOn_iff_exists_certificate H hH p).mp hp
  exact ⟨M, hdeg, hM.acceptanceRate_eq_one⟩

end PCP.Algebraic.GridVanishing
