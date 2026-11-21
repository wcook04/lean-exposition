import Breakdown.Cert.CoercivePieceDensityPassageRight
import Breakdown.Cert.FreeTransportReading
import Breakdown.Cert.CoerciveBordered

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.DensityPassage

def timeCutoff (σ : ℝ) : ℝ := Real.smoothTransition (σ + 1) * (1 - Real.smoothTransition σ)

theorem contDiff_timeCutoff : ContDiff ℝ ∞ timeCutoff := by
  unfold timeCutoff
  exact (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).mul
    (contDiff_const.sub Real.smoothTransition.contDiff)

theorem timeCutoff_eq_zero {σ : ℝ} (h : σ ∉ Set.Icc (-1 : ℝ) 1) : timeCutoff σ = 0 := by
  unfold timeCutoff
  rcases not_and_or.1 h with h1 | h1
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith [not_le.1 h1]), zero_mul]
  · have h2 : Real.smoothTransition σ = 1 := Real.smoothTransition.one_of_one_le (by linarith [not_le.1 h1])
    rw [h2, sub_self, mul_zero]

theorem timeCutoff_add {σ : ℝ} (h : σ ∈ Set.Icc (0 : ℝ) 1) : timeCutoff (σ - 1) + timeCutoff σ = 1 := by
  unfold timeCutoff
  have h0 : Real.smoothTransition (σ - 1) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith [h.2])
  have h1 : Real.smoothTransition (σ + 1) = 1 := Real.smoothTransition.one_of_one_le (by linarith [h.1])
  rw [show σ - 1 + 1 = σ by ring, h0, h1]
  ring

theorem cutoff_isSpaceTimeTestField {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    IsSpaceTimeTestField (fun σ y => timeCutoff σ • ψ σ y) := by
  obtain ⟨hs, -, ⟨R, hR⟩, hdiv⟩ := hψ
  refine ⟨(contDiff_timeCutoff.comp contDiff_fst).smul hs, ?_, fun s y => ?_⟩
  · refine HasCompactSupport.intro ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod (isCompact_closedBall (0 : Space) R)) fun z hz => ?_
    simp only [Set.mem_prod, not_and_or] at hz
    rcases hz with hz | hz
    · simp only [timeCutoff_eq_zero hz, zero_smul]
    · have hy : R < ‖z.2‖ := by simpa using hz
      simp only [hR z.1 z.2 hy, smul_zero]
  · have hd : DifferentiableAt ℝ (ψ s) y :=
      ((hs.comp (contDiff_prodMk_right s)).differentiable (by simp)).differentiableAt
    have hfd : fderiv ℝ (fun y => timeCutoff s • ψ s y) y = timeCutoff s • fderiv ℝ (ψ s) y :=
      fderiv_fun_const_smul hd _
    have h0 := hdiv s y
    unfold divergenceAt at h0 ⊢
    rw [hfd]
    simp only [ContinuousLinearMap.smul_apply, PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, h0, mul_zero]

theorem matInner_integral_eq {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {φ : ℝ → Space → Space}
    (hs : ContDiff ℝ ∞ (fun z : ℝ × Space => φ z.1 z.2))
    (hc : HasCompactSupport (fun z : ℝ × Space => φ z.1 z.2)) :
    Integrable (fun z : ℝ × Space => matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) ∧
      Integrable (fun z : ℝ × Space => inner ℝ (secondDerivTrace (H z.1 z.2)) (φ z.1 z.2)) ∧
      ∫ z : ℝ × Space, matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2) =
        -∫ z : ℝ × Space, inner ℝ (secondDerivTrace (H z.1 z.2)) (φ z.1 z.2) := by
  have hcol : ∀ j : Fin 3, periodLIntegral (fun σ y => ‖G σ y (unitVector j)‖ ^ 2) < ⊤ := fun j =>
    PassageLimit.periodL2_of_le (C := 1) zero_le_one (fun σ y => by
      rw [one_mul]
      exact Finset.single_le_sum (f := fun i => ‖G σ y (unitVector i)‖ ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ j)) hv.gradient_finite
  have hcm : ∀ j : Fin 3, AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2 (unitVector j)) volume :=
    fun j => (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable
      hv.measurable_gradient
  have hint : ∀ j : Fin 3, Integrable (fun z : ℝ × Space =>
      inner ℝ (G z.1 z.2 (unitVector j)) (fderiv ℝ (φ z.1) z.2 (unitVector j))) := fun j =>
    Cert.Internal.CoerciveBordered.integrable_inner_of_periodic (F := fun σ y => G σ y (unitVector j))
      (ψ := fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2 (unitVector j)) (hcm j)
      (fun σ y => by simp only [hv.periodic_gradient σ y]) (hcol j)
      (Cert.Internal.FreePerturbation.partial_continuous hs j)
      (Cert.Internal.FreePerturbation.partial_hasCompactSupport hs hc j)
  have hfe : (fun z : ℝ × Space => matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) =
      fun z => ∑ j : Fin 3, inner ℝ (G z.1 z.2 (unitVector j)) (fderiv ℝ (φ z.1) z.2 (unitVector j)) := by
    funext z
    simp only [matInner]
  have hfi : Integrable (fun z : ℝ × Space => matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) := by
    rw [hfe]
    exact integrable_finsetSum _ fun j _ => hint j
  have htr : Integrable (fun z : ℝ × Space => inner ℝ (secondDerivTrace (H z.1 z.2)) (φ z.1 z.2)) :=
    Cert.Internal.CoerciveBordered.integrable_inner_of_periodic (F := fun σ y => secondDerivTrace (H σ y))
      (PassageLimit.continuous_secondDerivTrace.comp_aestronglyMeasurable hv.measurable_secondDeriv)
      (fun σ y => by simp only [hv.periodic_secondDeriv σ y]) hv.sumSecondPartials_finite hs.continuous hc
  refine ⟨hfi, htr, ?_⟩
  rw [Measure.volume_eq_prod] at hfi htr ⊢
  rw [integral_prod _ hfi, integral_prod _ htr, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hv.weak_secondDeriv] with σ hσ
  exact Cert.Internal.FreePerturbation.slice_byParts hσ (hs.comp (contDiff_prodMk_right σ))
    (Cert.Internal.FreePerturbation.hasCompactSupport_slice hc σ)

theorem integral_cutoff_eq {D ψ : ℝ → Space → Space} (hDp : IsTimePeriodic D) (hψp : IsTimePeriodic ψ)
    (hi : Integrable (fun z : ℝ × Space => inner ℝ (D z.1 z.2) (timeCutoff z.1 • ψ z.1 z.2))) :
    ∫ z : ℝ × Space, inner ℝ (D z.1 z.2) (timeCutoff z.1 • ψ z.1 z.2) =
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (D σ y) (ψ σ y) := by
  set h : ℝ → ℝ := fun σ => ∫ y, inner ℝ (D σ y) (ψ σ y) with hh
  have hper : ∀ σ, h (σ + 1) = h σ := fun σ => by
    simp only [hh]
    congr 1
    funext y
    rw [hDp σ y, hψp σ y]
  set k : ℝ → ℝ := fun σ => timeCutoff σ * h σ with hk
  rw [Measure.volume_eq_prod] at hi ⊢
  have hik := hi.integral_prod_left
  have ek : (fun σ => ∫ y, inner ℝ (D σ y) (timeCutoff σ • ψ σ y)) = k := by
    funext σ
    simp only [hk, hh, inner_smul_right]
    exact integral_const_mul _ _
  rw [integral_prod _ hi]
  simp only at hik ⊢
  rw [ek] at hik ⊢
  have hsupp : ∀ σ, σ ∉ Set.Ioc (-1 : ℝ) 1 → k σ = 0 := fun σ hσ => by
    by_cases h1 : σ = -1
    · simp only [hk, h1, timeCutoff, show (-1 : ℝ) + 1 = 0 by norm_num, Real.smoothTransition.zero, zero_mul]
    · have : σ ∉ Set.Icc (-1 : ℝ) 1 := fun hm => hσ ⟨lt_of_le_of_ne hm.1 (Ne.symm h1), hm.2⟩
      simp only [hk, timeCutoff_eq_zero this, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, ← intervalIntegral.integral_of_le (by norm_num),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hik.intervalIntegrable) (hik.intervalIntegrable)]
  have e1 : ∫ σ in (-1 : ℝ)..0, k σ = ∫ σ in (0 : ℝ)..1, k (σ - 1) := by
    rw [intervalIntegral.integral_comp_sub_right]
    norm_num
  have hk1 : IntervalIntegrable (fun σ => k (σ - 1)) volume 0 1 :=
    (hik.comp_sub_right 1).intervalIntegrable
  rw [e1, ← intervalIntegral.integral_add hk1 hik.intervalIntegrable,
    intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
  have hp : h (σ - 1) = h σ := by
    have := hper (σ - 1)
    rw [sub_add_cancel] at this
    exact this.symm
  simp only [hk, hp, ← add_mul, timeCutoff_add hσ, one_mul]
  rfl

theorem rightSideLimit_periodic {k : ℕ} {Γ : Set Symmetry} {P : ℝ}
    {W : ℝ → Space → Space} {act : Fin k → ℝ → Space → Space} (κ : Fin k → ℝ)
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (hWp : IsTimePeriodic W) (hactp : ∀ i, IsTimePeriodic (act i)) :
    IsTimePeriodic (rightSideLimit W act κ v G H g) := by
  intro σ y
  have eW : W (σ + 1) = W σ := funext fun x => hWp σ x
  simp only [rightSideLimit, eW, hv.periodic_derivative σ y, hv.periodic_secondDeriv σ y,
    hv.periodic_gradient σ y, hv.periodic_velocity σ y, fun i => hactp i σ y]

theorem rightSide_spaceTime {k : ℕ} {Γ : Set Symmetry} {P : ℝ}
    {W : ℝ → Space → Space} {act : Fin k → ℝ → Space → Space} (κ : Fin k → ℝ)
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWp : IsTimePeriodic W)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (hvw : periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) < ⊤)
    {F : ℝ → Space → Space} (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hFp : IsTimePeriodic F) (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤)
    (hF : IsRightSide W act κ v G g F) {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Integrable (fun z : ℝ × Space =>
        inner ℝ (F z.1 z.2 - rightSideLimit W act κ v G H g z.1 z.2) (φ z.1 z.2)) ∧
      ∫ z : ℝ × Space, inner ℝ (F z.1 z.2 - rightSideLimit W act κ v G H g z.1 z.2) (φ z.1 z.2) = 0 := by
  set R := rightSideLimit W act κ v G H g with hRdef
  obtain ⟨hRm, hR2⟩ := PassageLimit.rightSideLimit_memL2 κ hv hW hWdecay hactm hact2 hvw
  have hRp : IsTimePeriodic R := rightSideLimit_periodic κ hv hWp hactp
  have hFi : Integrable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (φ z.1 z.2)) :=
    Cert.Internal.CoerciveBordered.integrable_inner_of_periodic hFm hFp hF2
      (ψ := fun z : ℝ × Space => φ z.1 z.2) hφ.1.continuous hφ.2.1
  have hRi : Integrable (fun z : ℝ × Space => inner ℝ (R z.1 z.2) (φ z.1 z.2)) :=
    Cert.Internal.CoerciveBordered.integrable_inner_of_periodic hRm hRp hR2
      (ψ := fun z : ℝ × Space => φ z.1 z.2) hφ.1.continuous hφ.2.1
  obtain ⟨hfi, htr, hibp⟩ := matInner_integral_eq hv hφ.1 hφ.2.1
  have e : ∀ z : ℝ × Space, inner ℝ (g z.1 z.2 + G z.1 z.2 (W z.1 z.2) + fderiv ℝ (W z.1) z.2 (v z.1 z.2)
        + ∑ i, κ i • act i z.1 z.2) (φ z.1 z.2) + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)
      = (inner ℝ (R z.1 z.2) (φ z.1 z.2) + inner ℝ (secondDerivTrace (H z.1 z.2)) (φ z.1 z.2))
        + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2) := by
    intro z
    rw [← inner_add_left]
    congr 2
    simp only [hRdef, rightSideLimit]
    abel
  have hrs : ∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2) =
      ∫ z : ℝ × Space, ((inner ℝ (R z.1 z.2) (φ z.1 z.2) + inner ℝ (secondDerivTrace (H z.1 z.2)) (φ z.1 z.2))
        + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) := by
    rw [hF φ hφ]
    exact integral_congr_ae (ae_of_all _ e)
  rw [integral_add (f := fun z : ℝ × Space => inner ℝ (R z.1 z.2) (φ z.1 z.2)
      + inner ℝ (secondDerivTrace (H z.1 z.2)) (φ z.1 z.2)) (hRi.add htr) hfi, integral_add hRi htr, hibp] at hrs
  have es : (fun z : ℝ × Space => inner ℝ (F z.1 z.2 - R z.1 z.2) (φ z.1 z.2)) =
      fun z => inner ℝ (F z.1 z.2) (φ z.1 z.2) - inner ℝ (R z.1 z.2) (φ z.1 z.2) :=
    funext fun z => inner_sub_left _ _ _
  rw [es]
  refine ⟨hFi.sub hRi, ?_⟩
  rw [integral_sub hFi hRi, hrs]
  ring

theorem rightSide_orthogonal_periodic {k : ℕ} {Γ : Set Symmetry} {P : ℝ}
    {W : ℝ → Space → Space} {act : Fin k → ℝ → Space → Space} (κ : Fin k → ℝ)
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWp : IsTimePeriodic W)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (hvw : periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) < ⊤)
    {F : ℝ → Space → Space} (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hFp : IsTimePeriodic F) (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤)
    (hF : IsRightSide W act κ v G g F) (ψ : ℝ → Space → Space) (hψ : IsPeriodicTestField ψ) :
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
      inner ℝ (F σ y - rightSideLimit W act κ v G H g σ y) (ψ σ y) = 0 := by
  have hRp := rightSideLimit_periodic κ hv hWp hactp
  have hDp : IsTimePeriodic (fun σ y => F σ y - rightSideLimit W act κ v G H g σ y) := fun σ y => by
    simp only [hFp σ y, hRp σ y]
  obtain ⟨hi, h0⟩ := rightSide_spaceTime κ hv hW hWp hWdecay hactm hactp hact2 hvw hFm hFp hF2 hF
    (cutoff_isSpaceTimeTestField hψ)
  rw [← integral_cutoff_eq (D := fun σ y => F σ y - rightSideLimit W act κ v G H g σ y) hDp hψ.2.1 hi]
  exact h0

end Internal.DensityPassage

end Coercive

end Breakdown
