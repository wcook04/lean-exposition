import TorusEuler.AmplitudeReferenceRows

/-! Bounds for the scaled entries of the unperturbed strain in Lemma 2.3. -/

open scoped InnerProductSpace

namespace TorusEuler.MovingAmplitude

open MovingWaveVector

private theorem entry_strain_zero {e : Fin 3 → Space} (he : Orthonormal ℝ e)
    (B : Space →L[ℝ] Space) (S σratio : ℝ) (i j : Fin 3) :
    entry e (strain e B 0 S σratio) i j =
      entry e B i j + (if i = 1 ∧ j = 0 then S * σratio else 0) := by
  simpa only [entry, zero_apply, inner_zero_right, add_zero] using entry_strain he B 0 S σratio i j

private theorem scaledEntries_strain_zero {e : Fin 3 → Space} (he : Orthonormal ℝ e)
    (B : Space →L[ℝ] Space) {S σratio : ℝ} (hS : S ≠ 0) (i j : Fin 3) :
    scaledEntries (entry e (strain e B 0 S σratio)) S i j =
      scaledEntries (entry e B) S i j + (if i = 1 ∧ j = 0 then σratio else 0) := by
  fin_cases i <;> fin_cases j <;>
    simp [scaledEntries, entry_strain_zero he, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  field_simp

private theorem referenceScaledStrainEntries_eq (ε : ℝ) (i j : Fin 3) :
    referenceScaledStrainEntries ε i j =
      referenceScaledOlderEntries ε i j + (if i = 1 ∧ j = 0 then 1 else 0) := by
  fin_cases i <;> fin_cases j <;>
    simp [referenceScaledStrainEntries, referenceScaledOlderEntries, Fin.zero_eta, Fin.mk_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- The normalized bounds on the older gradient and its two selected
couplings control every scaled older entry. -/
theorem scaledOlderEntries_sub_ref_le {b : Entries} {ε δ S : ℝ}
    (hδ : 0 ≤ δ) (hS : 1 ≤ S) (hb : ∀ i j, |b i j| ≤ δ)
    (h12 : |2 * S * b 0 1 - 1| ≤ δ) (h32 : |2 * S * b 2 1 - ε| ≤ δ) (i j : Fin 3) :
    |scaledEntries b S i j - referenceScaledOlderEntries ε i j| ≤ δ := by
  have h01 : |S * b 0 1 - (2 : ℝ)⁻¹| ≤ δ := by
    rw [← one_div, abs_le]
    rw [abs_le] at h12
    constructor <;> linarith [h12.1, h12.2]
  have h21 : |S * b 2 1 - ε / 2| ≤ δ := by
    rw [abs_le] at h32 ⊢
    constructor <;> linarith [h32.1, h32.2]
  have h10 : |b 1 0 / S| ≤ δ := by
    rw [abs_div, abs_of_nonneg (zero_le_one.trans hS)]
    exact (div_le_self (abs_nonneg _) hS).trans (hb 1 0)
  fin_cases i <;> fin_cases j <;>
    simp [scaledEntries, referenceScaledOlderEntries, Fin.zero_eta, Fin.mk_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    first | exact hb _ _ | assumption

/-- The bounds on the older gradient supply its scaled coefficient errors. -/
theorem scaledOlderStrainEntries_sub_ref_le {e : Fin 3 → Space} (he : Orthonormal ℝ e)
    (B : Space →L[ℝ] Space) {ε δ S : ℝ} (hδ : 0 ≤ δ) (hS : 1 ≤ S) (hB : ‖B‖ ≤ δ)
    (h12 : |2 * S * entry e B 0 1 - 1| ≤ δ) (h32 : |2 * S * entry e B 2 1 - ε| ≤ δ)
    (i j : Fin 3) : |scaledEntries (entry e B) S i j - referenceScaledOlderEntries ε i j| ≤ δ :=
  scaledOlderEntries_sub_ref_le hδ hS (fun i j => (coefficient_abs_le_norm he B i j).trans hB)
    h12 h32 i j

/-- The full scaled strain with the additional error omitted differs from the
older strain in one entry. Thus the reference error is at most `3*T*δ`. -/
theorem scaledStrainEntries_sub_ref_le {e : Fin 3 → Space} (he : Orthonormal ℝ e)
    (B : Space →L[ℝ] Space) {ε T δ S σratio : ℝ}
    (hδ : 0 ≤ δ) (hT : 1 ≤ T) (hS : 1 ≤ S) (hB : ‖B‖ ≤ δ)
    (h12 : |2 * S * entry e B 0 1 - 1| ≤ δ) (h32 : |2 * S * entry e B 2 1 - ε| ≤ δ)
    (hσ : |σratio - 1| ≤ 2 * T * δ) (i j : Fin 3) :
    |scaledEntries (entry e (strain e B 0 S σratio)) S i j -
      referenceScaledStrainEntries ε i j| ≤ 3 * T * δ := by
  have hS₀ : 0 < S := zero_lt_one.trans_le hS
  have h := scaledOlderStrainEntries_sub_ref_le he B hδ hS hB h12 h32 i j
  have hTδ : δ ≤ T * δ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hT hδ
  rw [scaledEntries_strain_zero he B hS₀.ne', referenceScaledStrainEntries_eq]
  by_cases h₀ : i = 1 ∧ j = 0
  · simp only [ite_eq_left h₀]
    rw [show ∀ a b : ℝ, a + σratio - (b + 1) = (a - b) + (σratio - 1) by intros; ring]
    exact (abs_add_le _ _).trans ((add_le_add h hσ).trans (by linarith))
  · simp only [ite_eq_right h₀, add_zero]
    exact h.trans (by linarith)

/-- Each of the two reference strains has every scaled entry in the unit box. -/
theorem referenceScaledEntries_abs_le_one {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (i j : Fin 3) :
    |referenceScaledOlderEntries ε i j| ≤ 1 ∧ |referenceScaledStrainEntries ε i j| ≤ 1 := by
  have h : |ε / 2| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; linarith
  fin_cases i <;> fin_cases j <;>
    norm_num [referenceScaledOlderEntries, referenceScaledStrainEntries, Fin.zero_eta,
      Fin.mk_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, h]

/-- Under the manuscript's coefficient smallness, both input strains belong
to a box of radius two in scaled entries. -/
theorem scaledEntries_abs_le_two {e : Fin 3 → Space} (he : Orthonormal ℝ e)
    (B : Space →L[ℝ] Space) {ε T δ S σratio : ℝ}
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (hδ : 0 ≤ δ) (hT : 1 ≤ T) (hS : 1 ≤ S)
    (hB : ‖B‖ ≤ δ) (h12 : |2 * S * entry e B 0 1 - 1| ≤ δ)
    (h32 : |2 * S * entry e B 2 1 - ε| ≤ δ) (hσ : |σratio - 1| ≤ 2 * T * δ)
    (hsmall : 3 * T * δ ≤ 1) (i j : Fin 3) :
    |scaledEntries (entry e B) S i j| ≤ 2 ∧
      |scaledEntries (entry e (strain e B 0 S σratio)) S i j| ≤ 2 := by
  obtain ⟨hb, hA⟩ := referenceScaledEntries_abs_le_one hε₀ hε₁ i j
  have ho := scaledOlderStrainEntries_sub_ref_le he B hδ hS hB h12 h32 i j
  have hs := scaledStrainEntries_sub_ref_le he B hδ hT hS hB h12 h32 hσ i j
  have hδ₁ : δ ≤ 1 := by
    have hTδ : δ ≤ T * δ := by simpa using mul_le_mul_of_nonneg_right hT hδ
    linarith
  have habs {a b : ℝ} (hd : |a - b| ≤ 1) (hb : |b| ≤ 1) : |a| ≤ 2 := by
    simpa only [sub_add_cancel, one_add_one_eq_two] using
      (abs_add_le (a - b) b).trans (add_le_add hd hb)
  exact ⟨habs (ho.trans hδ₁) hb, habs (hs.trans hsmall) hA⟩

end TorusEuler.MovingAmplitude
