import Breakdown.FracCell.StEnergyProof

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellEnergy.RadialForm

open CellAnalysis CellFormula

variable {D : Type} [Fintype D] [DecidableEq D]

theorem value_add (A B : Matrix D D ℂ) (u : D → ℂ) :
    quadFormValue (A + B) u = quadFormValue A u + quadFormValue B u := by
  unfold quadFormValue
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]

theorem value_zero (u : D → ℂ) : quadFormValue (0 : Matrix D D ℂ) u = 0 := by
  unfold quadFormValue
  simp

theorem formOfRows_eq {ι : Type} [Fintype ι] (rows : ι → D → ℂ) (G : Matrix ι ι ℂ) :
    formOfRows rows G = (Matrix.of rows)ᴴ * G * Matrix.of rows := by
  ext d d'
  simp only [formOfRows, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem value_formOfRows {ι : Type} [Fintype ι] (rows : ι → D → ℂ) (G : Matrix ι ι ℂ) (u : D → ℂ) :
    quadFormValue (formOfRows rows G) u =
      (star (fun i => rowApply (rows i) u) ⬝ᵥ (G *ᵥ fun i => rowApply (rows i) u)).re := by
  have hR : (fun i => rowApply (rows i) u) = Matrix.of rows *ᵥ u := by
    ext i
    simp [rowApply, Matrix.mulVec, dotProduct]
  rw [hR, formOfRows_eq]
  unfold quadFormValue
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

section Sup

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem conj_swap (G : Matrix ι ι ℂ) (hH : G.IsHermitian) (x c : ι → ℂ) :
    star x ⬝ᵥ (G *ᵥ c) = (starRingEnd ℂ) (star c ⬝ᵥ (G *ᵥ x)) := by
  have h1 : star c ⬝ᵥ (G *ᵥ x) = star (G *ᵥ c) ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, hH.eq]
  rw [h1]
  simp only [dotProduct, map_sum, map_mul, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

theorem real_form (G : Matrix ι ι ℂ) (hH : G.IsHermitian) (c : ι → ℂ) :
    ((star c ⬝ᵥ (G *ᵥ c)).re : ℂ) = star c ⬝ᵥ (G *ᵥ c) := by
  have := conj_swap G hH c c
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im]
    have h2 := congrArg Complex.im this
    rw [Complex.conj_im] at h2
    linarith

theorem ratio_le (G : Matrix ι ι ℂ) (hH : G.IsHermitian)
    (hpos : ∀ c : ι → ℂ, 0 ≤ (star c ⬝ᵥ (G *ᵥ c)).re) (x c : ι → ℂ)
    (hc : 0 < (star c ⬝ᵥ (G *ᵥ c)).re) :
    ‖star c ⬝ᵥ (G *ᵥ x)‖ ^ 2 / (star c ⬝ᵥ (G *ᵥ c)).re ≤ (star x ⬝ᵥ (G *ᵥ x)).re := by
  set A := (star c ⬝ᵥ (G *ᵥ c)).re with hA
  set β := star c ⬝ᵥ (G *ᵥ x) with hβ
  set y : ι → ℂ := x - (β / (A : ℂ)) • c with hy
  have hAc : (A : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hxc : star x ⬝ᵥ (G *ᵥ c) = (starRingEnd ℂ) β := conj_swap G hH x c
  have hcc : star c ⬝ᵥ (G *ᵥ c) = (A : ℂ) := (real_form G hH c).symm
  have key : star y ⬝ᵥ (G *ᵥ y) = star x ⬝ᵥ (G *ᵥ x) - (β * (starRingEnd ℂ) β) / (A : ℂ) := by
    rw [hy]
    simp only [star_sub, star_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hxc, hcc, ← hβ]
    simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
    field_simp
    ring
  have h0 := hpos y
  rw [key, Complex.sub_re] at h0
  have hn : ((β * (starRingEnd ℂ) β) / (A : ℂ)).re = ‖β‖ ^ 2 / A := by
    rw [Complex.mul_conj, ← Complex.ofReal_div, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hn] at h0
  linarith

theorem sup_identity (G : Matrix ι ι ℂ) (hH : G.IsHermitian)
    (hpos : ∀ c : ι → ℂ, c ≠ 0 → 0 < (star c ⬝ᵥ (G *ᵥ c)).re) (hG : IsUnit G.det) (b : ι → ℂ) :
    sSup {t : ℝ | ∃ c : ι → ℂ, 0 < (star c ⬝ᵥ (G *ᵥ c)).re ∧
        t = ‖star c ⬝ᵥ b‖ ^ 2 / (star c ⬝ᵥ (G *ᵥ c)).re} = (star b ⬝ᵥ (G⁻¹ *ᵥ b)).re := by
  have hnn : ∀ c : ι → ℂ, 0 ≤ (star c ⬝ᵥ (G *ᵥ c)).re := by
    intro c
    by_cases h : c = 0
    · subst h; simp
    · exact (hpos c h).le
  set x := G⁻¹ *ᵥ b with hx
  have hGx : G *ᵥ x = b := by
    rw [hx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec]
  have hval : (star b ⬝ᵥ (G⁻¹ *ᵥ b)).re = (star x ⬝ᵥ (G *ᵥ x)).re := by
    rw [hGx, ← hx]
    have := conj_swap G hH x x
    rw [hGx] at this
    have h3 : star b ⬝ᵥ x = (starRingEnd ℂ) (star x ⬝ᵥ b) := by
      simp only [dotProduct, map_sum, map_mul, Pi.star_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [mul_comm]
    rw [h3, Complex.conj_re]
  rw [hval]
  by_cases hb : x = 0
  · have h0 : (star x ⬝ᵥ (G *ᵥ x)).re = 0 := by rw [hb]; simp
    rw [h0]
    have hb0 : b = 0 := by rw [← hGx, hb, Matrix.mulVec_zero]
    apply le_antisymm
    · apply Real.sSup_nonpos
      rintro t ⟨c, hc, rfl⟩
      rw [hb0]; simp
    · apply Real.sSup_nonneg
      rintro t ⟨c, hc, rfl⟩
      exact div_nonneg (sq_nonneg _) hc.le
  · have hxpos := hpos x hb
    apply IsGreatest.csSup_eq
    refine ⟨⟨x, hxpos, ?_⟩, ?_⟩
    · rw [← hGx]
      have hr := real_form G hH x
      have hn : ‖star x ⬝ᵥ (G *ᵥ x)‖ = (star x ⬝ᵥ (G *ᵥ x)).re := by
        conv_lhs => rw [← hr]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
      rw [hn]
      field_simp
    · rintro t ⟨c, hc, rfl⟩
      rw [← hGx]
      exact ratio_le G hH hnn x c hc

end Sup

end Breakdown.CellCert.CellEnergy.RadialForm
