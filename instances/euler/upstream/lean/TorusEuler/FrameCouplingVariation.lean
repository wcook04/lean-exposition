import TorusEuler.AmplificationPhysicalBounds

/-! The physical-time bound (6.6) for the comparison error of a later wave. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.MovingWaveVector

/-- Each frame-axis speed from (2.2) is at most twice the norm of the
preceding velocity gradient. -/
theorem movingFrame_axis_derivative_bound {k a : ℝ → Space} {I : Set ℝ} {t : ℝ}
    (ht : t ∈ I) (B : Space →L[ℝ] Space)
    (htrace : LinearMap.trace ℝ Space B.toLinearMap = 0)
    (hk₀ : k t ≠ 0) (ha₀ : a t ≠ 0) (hperp : ⟪k t, a t⟫_ℝ = 0)
    (hk : HasDerivWithinAt k (-(B.adjoint (k t))) I t)
    (ha : HasDerivWithinAt a
      (-(B (a t)) + (2 * ⟪k t, B (a t)⟫_ℝ / ‖k t‖ ^ 2) • k t) I t)
    (i : Fin 3) :
    ∃ v : Space, HasDerivWithinAt (fun u => frame k a u i) v I t ∧ ‖v‖ ≤ 2 * ‖B‖ := by
  let e := frame k a t
  let ν := entry e B 0 1
  let γ := entry e B 0 2
  let η := entry e B 2 1
  have he : Orthonormal ℝ e := orthonormal_movingFrame hk₀ ha₀ hperp
  have hs {c : ℝ} {j : Fin 3} (hc : |c| ≤ ‖B‖) : ‖c • e j‖ ≤ ‖B‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, he.norm_eq_one j, mul_one] using hc
  have hν : |ν| ≤ ‖B‖ := coefficient_abs_le_norm he B 0 1
  have hγ : |γ| ≤ ‖B‖ := coefficient_abs_le_norm he B 0 2
  have hη : |η| ≤ ‖B‖ := coefficient_abs_le_norm he B 2 1
  obtain ⟨h₁, h₂, h₃, _⟩ := hasDerivWithinAt_movingFrame ht B htrace hk₀ ha₀ hperp hk ha
  fin_cases i
  · refine ⟨(-ν) • e 1 - γ • e 2, h₁, (norm_sub_le _ _).trans ?_⟩
    have hneg : |-ν| ≤ ‖B‖ := by rwa [abs_neg]
    linarith only [hs (j := 1) hneg, hs (j := 2) hγ]
  · refine ⟨ν • e 0 - η • e 2, h₂, (norm_sub_le _ _).trans ?_⟩
    linarith only [hs (j := 0) hν, hs (j := 2) hη]
  · refine ⟨γ • e 0 + η • e 1, h₃, (norm_add_le _ _).trans ?_⟩
    linarith only [hs (j := 0) hγ, hs (j := 1) hη]

private theorem frame_entry_increment_le {t₀ finish t M D : ℝ}
    {e : ℝ → Fin 3 → Space} {B Bt : ℝ → Space →L[ℝ] Space}
    (ht : t ∈ Icc t₀ finish)
    (he : ∀ u ∈ Icc t₀ finish, Orthonormal ℝ (e u))
    (he' : ∀ u ∈ Icc t₀ finish, ∀ i : Fin 3, ∃ v : Space,
      HasDerivWithinAt (fun s => e s i) v (Icc t₀ finish) u ∧ ‖v‖ ≤ 2 * M)
    (hBd : ∀ u ∈ Icc t₀ finish, HasDerivWithinAt B (Bt u) (Icc t₀ finish) u)
    (hB : ∀ u ∈ Icc t₀ finish, ‖B u‖ ≤ M) (hBt : ∀ u ∈ Icc t₀ finish, ‖Bt u‖ ≤ D)
    (i j : Fin 3) :
    |entry (e t) (B t) i j - entry (e t₀) (B t₀) i j| ≤
      (4 * M ^ 2 + D) * (finish - t₀) := by
  let I := Icc t₀ finish
  have hM : 0 ≤ M := (norm_nonneg _).trans (hB t ht)
  have hD : 0 ≤ D := (norm_nonneg _).trans (hBt t ht)
  have hderiv (u : ℝ) (hu : u ∈ I) : ∃ d : ℝ,
      HasDerivWithinAt (fun s => entry (e s) (B s) i j) d I u ∧ ‖d‖ ≤ 4 * M ^ 2 + D := by
    obtain ⟨ei', hei', heiBound⟩ := he' u hu i
    obtain ⟨ej', hej', hejBound⟩ := he' u hu j
    have hi : ‖e u i‖ = 1 := (he u hu).norm_eq_one i
    have hj : ‖e u j‖ = 1 := (he u hu).norm_eq_one j
    have hBe : ‖B u (e u j)‖ ≤ M := by
      simpa only [hj, mul_one] using ((B u).le_opNorm (e u j)).trans
        (mul_le_mul_of_nonneg_right (hB u hu) (norm_nonneg _))
    have hBte : ‖Bt u (e u j)‖ ≤ D := by
      simpa only [hj, mul_one] using ((Bt u).le_opNorm (e u j)).trans
        (mul_le_mul_of_nonneg_right (hBt u hu) (norm_nonneg _))
    have hBe' : ‖B u ej'‖ ≤ 2 * M ^ 2 := by
      calc
        _ ≤ ‖B u‖ * ‖ej'‖ := (B u).le_opNorm ej'
        _ ≤ M * (2 * M) := mul_le_mul (hB u hu) hejBound (norm_nonneg _) hM
        _ = _ := by ring
    have hd := hei'.inner ℝ ((hBd u hu).clm_apply hej')
    refine ⟨⟪ei', B u (e u j)⟫_ℝ + ⟪e u i, Bt u (e u j) + B u ej'⟫_ℝ,
      hd.congr_deriv (add_comm _ _), ?_⟩
    calc
      _ ≤ ‖⟪ei', B u (e u j)⟫_ℝ‖ +
          ‖⟪e u i, Bt u (e u j) + B u ej'⟫_ℝ‖ := norm_add_le _ _
      _ ≤ ‖ei'‖ * ‖B u (e u j)‖ + ‖e u i‖ * ‖Bt u (e u j) + B u ej'‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ (2 * M) * M + (D + 2 * M ^ 2) := by
        rw [hi, one_mul]
        exact add_le_add (mul_le_mul heiBound hBe (norm_nonneg _) (by positivity))
          ((norm_add_le _ _).trans (add_le_add hBte hBe'))
      _ = _ := by ring
  choose! d hd hBound using hderiv
  have htime := norm_image_sub_le_of_norm_deriv_le_segment' hd
    (fun u hu => hBound u (Ico_subset_Icc_self hu)) t ht
  rw [Real.norm_eq_abs] at htime
  exact htime.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 _) (by positivity))

/-- The four suprema defining (2.4) obey (6.6) when the frame speeds
are bounded by twice the gradient bound. -/
theorem amplificationPhysicalError_le_of_frame_rate {t₀ finish M D Emax r : ℝ}
    {e : ℝ → Fin 3 → Space} {B Bt E : ℝ → Space →L[ℝ] Space}
    (hTime : t₀ ≤ finish) (hr : 0 < r)
    (he : ∀ u ∈ Icc t₀ finish, Orthonormal ℝ (e u))
    (he' : ∀ u ∈ Icc t₀ finish, ∀ i : Fin 3, ∃ v : Space,
      HasDerivWithinAt (fun s => e s i) v (Icc t₀ finish) u ∧ ‖v‖ ≤ 2 * M)
    (hBd : ∀ u ∈ Icc t₀ finish, HasDerivWithinAt B (Bt u) (Icc t₀ finish) u)
    (hB : ∀ u ∈ Icc t₀ finish, ‖B u‖ ≤ M) (hBt : ∀ u ∈ Icc t₀ finish, ‖Bt u‖ ≤ D)
    (hE : ∀ u ∈ Icc t₀ finish, ‖E u‖ ≤ Emax) :
    let ν := entry (e t₀) (B t₀) 0 1
    let η := entry (e t₀) (B t₀) 2 1
    0 < η → η ≤ ν →
    amplificationPhysicalError (Icc t₀ finish) e B E ν η r ≤
      8 * ((finish - t₀) * (M ^ 2 + D) / η + M / r + Emax / ν) := by
  intro ν η hη hην
  let I := Icc t₀ finish
  let d := (4 * M ^ 2 + D) * (finish - t₀)
  have ht₀ : t₀ ∈ I := left_mem_Icc.mpr hTime
  have hν : 0 < ν := hη.trans_le hην
  have hD : 0 ≤ D := (norm_nonneg _).trans (hBt t₀ ht₀)
  have hd : 0 ≤ d := by unfold d; positivity
  have hM : 0 ≤ M := (norm_nonneg _).trans (hB t₀ ht₀)
  have hEmax : 0 ≤ Emax := (norm_nonneg _).trans (hE t₀ ht₀)
  have hVar (i : Fin 3) {c : ℝ} (hc : 0 < c) (h₀ : entry (e t₀) (B t₀) i 1 = c) :
      sSup ((fun t => |entry (e t) (B t) i 1 / c - 1|) '' I) ≤ d / c := by
    apply csSup_le ⟨_, mem_image_of_mem _ ht₀⟩
    rintro _ ⟨t, ht, rfl⟩
    change |entry (e t) (B t) i 1 / c - 1| ≤ d / c
    rw [show entry (e t) (B t) i 1 / c - 1 = (entry (e t) (B t) i 1 - c) / c by
      field_simp, abs_div, abs_of_pos hc]
    have hChange := frame_entry_increment_le ht he he' hBd hB hBt i 1
    rw [h₀] at hChange
    exact div_le_div_of_nonneg_right hChange hc.le
  have hνVar := (hVar 0 hν rfl).trans (div_le_div_of_nonneg_left hd hη hην)
  have hηVar := hVar 2 hη rfl
  have hBsup : sSup ((fun t => ‖B t‖) '' I) ≤ M := by
    apply csSup_le ⟨_, mem_image_of_mem _ ht₀⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hB t ht
  have hEsup : sSup ((fun t => ‖E t‖) '' I) ≤ Emax := by
    apply csSup_le ⟨_, mem_image_of_mem _ ht₀⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hE t ht
  have htwo : 2 * (d / η) ≤ 8 * ((finish - t₀) * (M ^ 2 + D) / η) := by
    rw [← mul_div_assoc, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hη.le
    unfold d
    nlinarith only [mul_nonneg hD (sub_nonneg.mpr hTime)]
  have hBdiv := div_le_div_of_nonneg_right hBsup hr.le
  have hEdiv := div_le_div_of_nonneg_right hEsup hν.le
  change amplificationPhysicalError I e B E ν η r ≤ _
  unfold amplificationPhysicalError
  linarith only [hνVar, hηVar, hBdiv, hEdiv, htwo, div_nonneg hM hr.le, div_nonneg hEmax hν.le]

/-- Equation (6.6) for the actual moving frame of an older transverse wave.
The hypotheses are the two affine wave ODEs and bounds on the original
physical-time gradient, its time derivative and the perturbation. -/
theorem amplificationPhysicalError_le_movingFrame {t₀ finish M D Emax r : ℝ}
    {k a : ℝ → Space} {B Bt E : ℝ → Space →L[ℝ] Space}
    (hTime : t₀ ≤ finish) (hr : 0 < r)
    (hTrace : ∀ t ∈ Icc t₀ finish, LinearMap.trace ℝ Space (B t).toLinearMap = 0)
    (hPair : ∀ t ∈ Icc t₀ finish, k t ≠ 0 ∧ a t ≠ 0 ∧ ⟪k t, a t⟫_ℝ = 0)
    (hk : ∀ t ∈ Icc t₀ finish, HasDerivWithinAt k (-((B t).adjoint (k t))) (Icc t₀ finish) t)
    (ha : ∀ t ∈ Icc t₀ finish, HasDerivWithinAt a
      (-(B t (a t)) + (2 * ⟪k t, B t (a t)⟫_ℝ / ‖k t‖ ^ 2) • k t) (Icc t₀ finish) t)
    (hBd : ∀ t ∈ Icc t₀ finish, HasDerivWithinAt B (Bt t) (Icc t₀ finish) t)
    (hB : ∀ t ∈ Icc t₀ finish, ‖B t‖ ≤ M) (hBt : ∀ t ∈ Icc t₀ finish, ‖Bt t‖ ≤ D)
    (hE : ∀ t ∈ Icc t₀ finish, ‖E t‖ ≤ Emax) :
    let e := frame k a
    let ν := entry (e t₀) (B t₀) 0 1
    let η := entry (e t₀) (B t₀) 2 1
    0 < η → η ≤ ν →
    amplificationPhysicalError (Icc t₀ finish) e B E ν η r ≤
      8 * ((finish - t₀) * (M ^ 2 + D) / η + M / r + Emax / ν) := by
  intro e ν η hη hην
  refine amplificationPhysicalError_le_of_frame_rate hTime hr ?_ ?_ hBd hB hBt hE hη hην
  · intro t ht
    obtain ⟨hk₀, ha₀, hperp⟩ := hPair t ht
    exact orthonormal_movingFrame hk₀ ha₀ hperp
  · intro t ht i
    obtain ⟨hk₀, ha₀, hperp⟩ := hPair t ht
    obtain ⟨v, hv, hNorm⟩ :=
      movingFrame_axis_derivative_bound ht (B t) (hTrace t ht) hk₀ ha₀ hperp (hk t ht) (ha t ht) i
    exact ⟨v, hv, hNorm.trans (mul_le_mul_of_nonneg_left (hB t ht) (by norm_num))⟩

end TorusEuler.MovingWaveVector
