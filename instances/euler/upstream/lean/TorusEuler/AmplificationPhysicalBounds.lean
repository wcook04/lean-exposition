import TorusEuler.AmplificationTimeRescaling

/-! The physical error (2.4) and its normalized bounds under (2.5). -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.MovingWaveVector

/-- The growth rate used to rescale time in Lemma 2.3. -/
noncomputable def amplificationGrowthRate (σ ν : ℝ) : ℝ := Real.sqrt (2 * σ * ν)

theorem amplificationGrowthRate_pos {σ ν : ℝ} (hσ : 0 < σ) (hν : 0 < ν) :
    0 < amplificationGrowthRate σ ν := by
  unfold amplificationGrowthRate
  positivity

theorem amplificationGrowthRate_sq {σ ν : ℝ} (hσ : 0 < σ) (hν : 0 < ν) :
    amplificationGrowthRate σ ν ^ 2 = 2 * σ * ν :=
  Real.sq_sqrt (by positivity)

/-- The four suprema in (2.4), evaluated on the physical time window `I`. -/
noncomputable def amplificationPhysicalError (I : Set ℝ) (e : ℝ → Fin 3 → Space)
    (B E : ℝ → Space →L[ℝ] Space) (ν η r : ℝ) : ℝ :=
  sSup ((fun t => |entry (e t) (B t) 0 1 / ν - 1|) '' I) +
  sSup ((fun t => |entry (e t) (B t) 2 1 / η - 1|) '' I) +
  sSup ((fun t => ‖B t‖) '' I) / r + sSup ((fun t => ‖E t‖) '' I) / ν

/-- The physical error supplies all four normalized coefficient bounds.
The estimates hold at each physical time in the compact window. -/
theorem normalized_rates_of_physical_error {I : Set ℝ} {t₀ σ : ℝ}
    {e : ℝ → Fin 3 → Space} {B E : ℝ → Space →L[ℝ] Space}
    (hI : IsCompact I) (ht₀ : t₀ ∈ I) (he₀ : Orthonormal ℝ (e t₀))
    (hec : ∀ i, ContinuousOn (fun t => e t i) I)
    (hBc : ContinuousOn B I) (hEc : ContinuousOn E I)
    (hσ : 0 < σ) (hν : 0 < entry (e t₀) (B t₀) 0 1) (hη : 0 < entry (e t₀) (B t₀) 2 1)
    (hε : entry (e t₀) (B t₀) 2 1 / entry (e t₀) (B t₀) 0 1 ≤ 1) :
    let ν := entry (e t₀) (B t₀) 0 1
    let η := entry (e t₀) (B t₀) 2 1
    let r := amplificationGrowthRate σ ν
    let S := σ / r
    let δ := amplificationPhysicalError I e B E ν η r
    0 ≤ δ ∧ S⁻¹ ≤ 2 * δ ∧ ∀ t ∈ I,
      ‖(1 / r) • B t‖ ≤ δ ∧ ‖(1 / r) • E t‖ ≤ δ / S ∧
      |2 * S * entry (e t) ((1 / r) • B t) 0 1 - 1| ≤ δ ∧
      |2 * S * entry (e t) ((1 / r) • B t) 2 1 - η / ν| ≤ δ := by
  let ν := entry (e t₀) (B t₀) 0 1
  let η := entry (e t₀) (B t₀) 2 1
  let r := amplificationGrowthRate σ ν
  let S := σ / r
  let δ := amplificationPhysicalError I e B E ν η r
  let f (t : ℝ) := |entry (e t) (B t) 0 1 / ν - 1|
  let g (t : ℝ) := |entry (e t) (B t) 2 1 / η - 1|
  let dν := sSup (f '' I)
  let dη := sSup (g '' I)
  let dB := sSup ((fun t => ‖B t‖) '' I)
  let dE := sSup ((fun t => ‖E t‖) '' I)
  have hδdef : δ = dν + dη + dB / r + dE / ν := rfl
  have hr : 0 < r := amplificationGrowthRate_pos hσ hν
  have hr₂ : r ^ 2 = 2 * σ * ν := amplificationGrowthRate_sq hσ hν
  have hS : 0 < S := div_pos hσ hr
  have hentryc (i j : Fin 3) : ContinuousOn (fun t => entry (e t) (B t) i j) I :=
    (hec i).inner (hBc.clm_apply (hec j))
  have hfc : ContinuousOn f I := ((hentryc 0 1).div_const ν |>.sub continuousOn_const).abs
  have hgc : ContinuousOn g I := ((hentryc 2 1).div_const η |>.sub continuousOn_const).abs
  have hf t (ht : t ∈ I) : f t ≤ dν :=
    le_csSup (hI.bddAbove_image hfc) (mem_image_of_mem _ ht)
  have hg t (ht : t ∈ I) : g t ≤ dη :=
    le_csSup (hI.bddAbove_image hgc) (mem_image_of_mem _ ht)
  have hB t (ht : t ∈ I) : ‖B t‖ ≤ dB :=
    le_csSup (hI.bddAbove_image hBc.norm) (mem_image_of_mem _ ht)
  have hE t (ht : t ∈ I) : ‖E t‖ ≤ dE :=
    le_csSup (hI.bddAbove_image hEc.norm) (mem_image_of_mem _ ht)
  have hdν : 0 ≤ dν := (abs_nonneg _).trans (hf t₀ ht₀)
  have hdη : 0 ≤ dη := (abs_nonneg _).trans (hg t₀ ht₀)
  have hdB : 0 ≤ dB / r := div_nonneg ((norm_nonneg _).trans (hB t₀ ht₀)) hr.le
  have hdE : 0 ≤ dE / ν := div_nonneg ((norm_nonneg _).trans (hE t₀ ht₀)) hν.le
  have hδ : 0 ≤ δ := by linarith only [hδdef, hdν, hdη, hdB, hdE]
  have hBn t (ht : t ∈ I) : ‖(1 / r) • B t‖ ≤ δ := by
    calc
      ‖(1 / r) • B t‖ = ‖B t‖ / r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        ring
      _ ≤ dB / r := div_le_div_of_nonneg_right (hB t ht) hr.le
      _ ≤ δ := by linarith only [hδdef, hdν, hdη, hdE]
  have hanchor : 2 * S * entry (e t₀) ((1 / r) • B t₀) 0 1 = 1 := by
    have h := normalized_coupling_entry hr hσ hν hr₂ (e t₀) (B t₀) 0 1
    change 2 * S * entry (e t₀) ((1 / r) • B t₀) 0 1 = ν / ν at h
    rwa [div_self hν.ne'] at h
  have hinv : S⁻¹ = 2 * entry (e t₀) ((1 / r) • B t₀) 0 1 := by
    rw [← one_div]
    exact (div_eq_iff hS.ne').mpr (by nlinarith only [hanchor])
  have hnormEntry : |entry (e t₀) ((1 / r) • B t₀) 0 1| ≤ ‖(1 / r) • B t₀‖ := by
    calc
      _ ≤ ‖e t₀ 0‖ * ‖((1 / r) • B t₀) (e t₀ 1)‖ := abs_real_inner_le_norm _ _
      _ ≤ _ := by
        simpa only [he₀.norm_eq_one 0, he₀.norm_eq_one 1, one_mul, mul_one] using
          (((1 / r) • B t₀).le_opNorm (e t₀ 1))
  have hSinv : S⁻¹ ≤ 2 * δ := by
    rw [hinv]
    exact mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (hnormEntry.trans (hBn t₀ ht₀))) (by norm_num)
  refine ⟨hδ, hSinv, fun t ht => ⟨hBn t ht, ?_, ?_, ?_⟩⟩
  · apply (le_div_iff₀ hS).mpr
    rw [mul_comm, normalized_shear_error_norm hr hσ hν hr₂]
    calc
      ‖E t‖ / (2 * ν) = ‖E t‖ / ν / 2 := by
        field_simp [show ν ≠ 0 from hν.ne']
      _ ≤ dE / ν / 2 := by
        exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (hE t ht) hν.le) (by norm_num)
      _ ≤ δ := by linarith only [hδdef, hdν, hdη, hdB, hdE]
  · rw [normalized_coupling_entry hr hσ hν hr₂]
    exact (hf t ht).trans (by linarith only [hδdef, hdη, hdB, hdE])
  · rw [normalized_coupling_entry hr hσ hν hr₂, show
      entry (e t) (B t) 2 1 / ν - η / ν =
        (η / ν) * (entry (e t) (B t) 2 1 / η - 1) by
          field_simp [show ν ≠ 0 from hν.ne', show η ≠ 0 from hη.ne']]
    rw [abs_mul, abs_of_nonneg (div_nonneg hη.le hν.le)]
    exact (mul_le_of_le_one_left (abs_nonneg _) hε).trans
      ((hg t ht).trans (by linarith only [hδdef, hdν, hdB, hdE]))

/-- Increasing the absolute polynomial threshold in (2.5) dominates any
fixed coefficient and exponent, uniformly in the length of the window. -/
theorem amplification_absorb_power {T ε δ C : ℝ} {p C₀ : ℕ}
    (hT : 1 ≤ T) (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hp : p ≤ C₀) (hC₀ : C ≤ C₀)
    (hsmall : (C₀ : ℝ) * T ^ C₀ * δ ≤ ε) :
    C * T ^ p * δ ≤ ε := by
  have hpow : T ^ p ≤ T ^ C₀ := pow_le_pow_right₀ hT hp
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul hC₀ hpow (by positivity) (hC.trans hC₀)) hδ).trans hsmall

theorem amplification_epsilon_le_half {ε : ℝ} {C₀ : ℕ}
    (hC₀ : 2 ≤ C₀) (hε : 0 ≤ ε) (hsmall : (C₀ : ℝ) * ε ≤ 1) :
    ε ≤ 1 / 2 := by
  have hC : (2 : ℝ) ≤ C₀ := by exact_mod_cast hC₀
  linarith only [hsmall, mul_le_mul_of_nonneg_right hC hε]

/-- An explicit threshold suffices for the wave-vector comparison, the
amplitude denominators, and the variation of the preceding strength. -/
theorem amplification_normalized_smallness {T ε δ S : ℝ} {C₀ : ℕ}
    (hT : 2 ≤ T) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hS : 0 < S) (hSinv : S⁻¹ ≤ 2 * δ)
    (hC₀ : 240 ≤ C₀) (hsmallε : (C₀ : ℝ) * ε ≤ 1)
    (hsmallδ : (C₀ : ℝ) * T ^ C₀ * δ ≤ ε) :
    ε ≤ 1 / 2 ∧ 240 * δ * T ^ 6 ≤ 1 ∧ T * δ ≤ 1 ∧ T ^ 2 ≤ S := by
  have hT₁ : 1 ≤ T := by linarith
  have he := amplification_epsilon_le_half (by omega : 2 ≤ C₀) hε hsmallε
  have h240 : (240 : ℝ) ≤ C₀ := by exact_mod_cast hC₀
  have h6 := amplification_absorb_power hT₁ hδ (by norm_num : 0 ≤ (240 : ℝ))
    (by omega : 6 ≤ C₀) h240 hsmallδ
  have h120 : 240 * δ * T ^ 6 ≤ 1 := by linarith only [h6, he]
  have hTδ := amplification_absorb_power hT₁ hδ (by norm_num : 0 ≤ (1 : ℝ))
    (by omega : 1 ≤ C₀) (show (1 : ℝ) ≤ C₀ by linarith only [h240]) hsmallδ
  have hTδ' : T * δ ≤ 1 := by
    simp only [one_mul, pow_one] at hTδ
    linarith only [hTδ, he]
  have h2δ := amplification_absorb_power hT₁ hδ (by norm_num : 0 ≤ (2 : ℝ))
    (by omega : 2 ≤ C₀) (show (2 : ℝ) ≤ C₀ by linarith only [h240]) hsmallδ
  have hquad : T ^ 2 * S⁻¹ ≤ 1 := by
    calc
      _ ≤ T ^ 2 * (2 * δ) := mul_le_mul_of_nonneg_left hSinv (sq_nonneg _)
      _ ≤ 1 := by linarith only [h2δ, he]
  have hTS : T ^ 2 ≤ S := by
    simpa only [← div_eq_mul_inv, div_le_iff₀ hS, one_mul] using hquad
  exact ⟨he, h120, hTδ', hTS⟩

end TorusEuler.MovingWaveVector
