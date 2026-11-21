import Breakdown.FracCell.GivenModelDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenModel

open SteadyCert CellAnalysis

namespace MixClausesInternal

variable {M : CellMesh} {N : ℕ}

theorem evalPoly_const_mul {d : ℕ} (k : ℂ) (P : CellPoly d) (r z : ℝ) :
    evalPoly (d := d) (fun j l => k * P j l) r z = k * evalPoly P r z := by
  simp only [evalPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem profile_partner {R : RowData M N} {m : ℕ} {rowMax : ℝ} (hR : IsRowData R m rowMax)
    (x : Fin N) (hx : R.harmonic x ≠ 0) (c : Fin 3) :
    R.profile (R.partner x) c =
      fun j l => (if R.positive x = true then Complex.I else -Complex.I) * R.profile x c j l := by
  funext j l
  by_cases hp : R.positive x = true
  · rw [if_pos hp, hR.partner_profile x hx hp]
  · have hp' : R.positive (R.partner x) = true := by
      rw [hR.partner_sign x hx]
      simpa using hp
    have h := hR.partner_profile (R.partner x) (by rwa [hR.partner_harmonic]) hp' c j l
    rw [hR.partner_invol] at h
    rw [if_neg hp, h]
    linear_combination (R.profile (R.partner x) c j l) * Complex.I_sq

theorem pairing_eq_zero (R : RowData M N) {a b : Fin N}
    (h : ¬ (R.cell a = R.cell b ∧ R.harmonic a = R.harmonic b)) : R.testPairing a b = 0 := by
  simp only [RowData.testPairing]
  exact if_neg h

theorem pairing_eq (R : RowData M N) {a b : Fin N} (hc : R.cell a = R.cell b)
    (hh : R.harmonic a = R.harmonic b) (h0 : R.harmonic a ≠ 0) :
    R.testPairing a b = 2 * (2 * Real.pi) * ∫ p in (M.box (R.cell a)).rect, p.1 *
      ((1 / 2 : ℝ) * ∑ c : Fin 3, (evalPoly (R.profile a c) p.1 p.2 *
        (starRingEnd ℂ) (evalPoly (R.profile b c) p.1 p.2)).re) := by
  simp only [RowData.testPairing, RowData.modePairDensity]
  rw [if_pos ⟨hc, hh⟩]
  simp only [h0, ↓reduceIte]

theorem commute_proj (R : RowData M N) (κ : Fin M.cellCount × ℕ) :
    Commute R.testPairing
      (Matrix.diagonal fun i => if (R.cell i, R.harmonic i) = κ then (1 : ℝ) else 0) := by
  unfold Commute SemiconjBy
  refine Matrix.ext fun a b => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : R.cell a = R.cell b ∧ R.harmonic a = R.harmonic b
  · rw [h.1, h.2]
    ring
  · rw [pairing_eq_zero R h]
    ring

theorem pairing_partner {R : RowData M N} {m : ℕ} {rowMax : ℝ} (hR : IsRowData R m rowMax)
    (a b : Fin N) :
    R.testPairing a (R.partner b) * (if R.harmonic (R.partner b) = 0 then 1 else R.pairSign (R.partner b)) =
      (if R.harmonic a = 0 then 1 else R.pairSign a) * R.testPairing (R.partner a) b := by
  by_cases h : R.cell a = R.cell b ∧ R.harmonic a = R.harmonic b
  · by_cases h0 : R.harmonic a = 0
    · have hb0 : R.harmonic b = 0 := h.2 ▸ h0
      rw [hR.partner_zero a h0, hR.partner_zero b hb0, if_pos hb0, if_pos h0]
      ring
    · have hb0 : R.harmonic b ≠ 0 := h.2 ▸ h0
      rw [if_neg (by rwa [hR.partner_harmonic]), if_neg h0]
      rw [pairing_eq R (by rw [hR.partner_cell]; exact h.1) (by rw [hR.partner_harmonic]; exact h.2) h0,
        pairing_eq R (by rw [hR.partner_cell]; exact h.1) (by rw [hR.partner_harmonic]; exact h.2)
          (by rwa [hR.partner_harmonic])]
      rw [hR.partner_cell]
      simp only [profile_partner hR b hb0, profile_partner hR a h0, evalPoly_const_mul]
      rw [mul_left_comm (R.pairSign a), mul_assoc (2 * (2 * Real.pi))]
      congr 1
      rw [← integral_mul_const, ← integral_const_mul]
      congr 1
      funext p
      simp only [RowData.pairSign, hR.partner_sign b hb0]
      cases R.positive a <;> cases R.positive b <;>
        simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, map_mul, map_neg,
          Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
          Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Fin.sum_univ_three] <;> ring
  · have h1 : ¬ (R.cell a = R.cell (R.partner b) ∧ R.harmonic a = R.harmonic (R.partner b)) := by
      rwa [hR.partner_cell, hR.partner_harmonic]
    have h2 : ¬ (R.cell (R.partner a) = R.cell b ∧ R.harmonic (R.partner a) = R.harmonic b) := by
      rwa [hR.partner_cell, hR.partner_harmonic]
    rw [pairing_eq_zero R h1, pairing_eq_zero R h2]
    ring

theorem commute_partner {R : RowData M N} {m : ℕ} {rowMax : ℝ} (hR : IsRowData R m rowMax) :
    Commute R.testPairing (Matrix.of fun x y : Fin N =>
      if x = R.partner y then (if R.harmonic x = 0 then (1 : ℝ) else R.pairSign x) else 0) := by
  unfold Commute SemiconjBy
  refine Matrix.ext fun a b => ?_
  have hiff : ∀ x, (a = R.partner x) ↔ (x = R.partner a) := fun x =>
    ⟨fun h => by rw [h, hR.partner_invol], fun h => by rw [h, hR.partner_invol]⟩
  simp only [Matrix.mul_apply, Matrix.of_apply, hiff, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← mul_ite, ← ite_mul]
  exact pairing_partner hR a b

theorem mix_eq (R : RowData M N) (hH : R.testPairing.IsHermitian) :
    R.mix = cfc (fun x => Real.sqrt x⁻¹) R.testPairing := by
  rw [RowData.mix, dif_pos hH, hH.cfc_eq]

end MixClausesInternal

open MixClausesInternal in
theorem mix_clauses {M : CellMesh} {N : ℕ} (R : RowData M N) (m : ℕ) (rowMax : ℝ) (hR : IsRowData R m rowMax) :
    R.mix * R.testPairing * R.mix.transpose = 1 ∧
      (∀ a b, R.mix a b ≠ 0 → R.cell a = R.cell b ∧ R.harmonic a = R.harmonic b) ∧
      ∀ a b, R.harmonic a ≠ 0 → R.mix a (R.partner b) * R.pairSign (R.partner b) = R.pairSign a * R.mix (R.partner a) b := by
  have hH : R.testPairing.IsHermitian := hR.pairing_posDef.isHermitian
  have hspec : spectrum ℝ R.testPairing = Set.range hH.eigenvalues := hH.spectrum_real_eq_range_eigenvalues
  have hfin : (spectrum ℝ R.testPairing).Finite := hspec ▸ Set.finite_range _
  have hpos : ∀ x ∈ spectrum ℝ R.testPairing, 0 < x := by
    intro x hx
    rw [hspec] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hR.pairing_posDef.eigenvalues_pos i
  have hblock : ∀ a b, R.mix a b ≠ 0 → R.cell a = R.cell b ∧ R.harmonic a = R.harmonic b := by
    intro a b h
    have hc := (commute_proj R (R.cell b, R.harmonic b)).cfc_real (fun x => Real.sqrt x⁻¹)
    rw [← mix_eq R hH] at hc
    have he := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A a b) hc.eq
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
    simp only [↓reduceIte, mul_one] at he
    by_contra hne
    have hk : ¬ ((R.cell a, R.harmonic a) = (R.cell b, R.harmonic b)) := by
      rw [Prod.mk.injEq]
      exact hne
    rw [if_neg hk, zero_mul] at he
    exact h he
  refine ⟨?_, hblock, ?_⟩
  · have hsa : IsSelfAdjoint R.mix := by
      rw [mix_eq R hH]
      exact cfc_predicate _ _
    have htr : R.mix.transpose = R.mix := by
      have h := hsa.star_eq
      rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    rw [htr, mix_eq R hH]
    have e1 : cfc (fun x => Real.sqrt x⁻¹) R.testPairing * R.testPairing =
        cfc (fun x => Real.sqrt x⁻¹ * x) R.testPairing := by
      rw [cfc_mul (fun x => Real.sqrt x⁻¹) (fun x => x) R.testPairing (hfin.continuousOn _)
        (hfin.continuousOn _), cfc_id' ℝ R.testPairing hH.isSelfAdjoint]
    have e2 : cfc (fun x => Real.sqrt x⁻¹ * x) R.testPairing * cfc (fun x => Real.sqrt x⁻¹) R.testPairing =
        cfc (fun x => Real.sqrt x⁻¹ * x * Real.sqrt x⁻¹) R.testPairing :=
      (cfc_mul _ _ R.testPairing (hfin.continuousOn _) (hfin.continuousOn _)).symm
    rw [e1, e2, ← cfc_const_one ℝ R.testPairing]
    refine cfc_congr fun x hx => ?_
    have hx0 := hpos x hx
    have hs : Real.sqrt x⁻¹ * Real.sqrt x⁻¹ = x⁻¹ := Real.mul_self_sqrt (inv_nonneg.mpr hx0.le)
    calc Real.sqrt x⁻¹ * x * Real.sqrt x⁻¹ = (Real.sqrt x⁻¹ * Real.sqrt x⁻¹) * x := by ring
      _ = 1 := by rw [hs, inv_mul_cancel₀ hx0.ne']
  · intro a b ha
    have hc := (commute_partner hR).cfc_real (fun x => Real.sqrt x⁻¹)
    rw [← mix_eq R hH] at hc
    have he := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A a b) hc.eq
    have hiff : ∀ x, (a = R.partner x) ↔ (x = R.partner a) := fun x =>
      ⟨fun h => by rw [h, hR.partner_invol], fun h => by rw [h, hR.partner_invol]⟩
    simp only [Matrix.mul_apply, Matrix.of_apply, hiff, mul_ite, ite_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at he
    rw [← mul_ite, ← ite_mul, if_neg ha] at he
    by_cases hb : R.harmonic (R.partner b) = 0
    · have h0 : R.mix a (R.partner b) = 0 := by
        by_contra hne
        exact ha ((hblock a (R.partner b) hne).2.trans hb)
      rw [if_pos hb, h0, zero_mul] at he
      rw [h0, zero_mul]
      exact he
    · rw [if_neg hb] at he
      exact he

end GivenModel

end CellCert

end Breakdown
