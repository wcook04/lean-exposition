import TorusEuler.FirstWaveDerivativeBudgets
import TorusEuler.LaterWaveHierarchyInput

/-! The initial weighted derivative budget for the later lattice-wrapped velocity and pressure. -/

open ContinuousLinearMap Set
open scoped ContDiff

namespace TorusEuler.LocalizedAmplitude.SeedOn

noncomputable section

variable {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3}
  {center : ℝ → Vec3} {t₀ T ell D C : ℝ} {w : SeedOn M κ center t₀ T ell D C}
  {r h : ℝ}

/-- The later-wave form of (5.25) for the actual wrapped profiles follows from
the raw scaled jet budgets, with only the count of admissible mixed words. -/
theorem twistedLeading_pressure_amplitudeSeminorm_le_of_scaledJetBounds
    (d : w.HierarchyRegularity r h) (k : Vec3) (n : ℕ) {freq BV BP : ℝ}
    (hfreq : 0 ≤ freq) (hBV : 0 ≤ BV) (hBP : 0 ≤ BP)
    {γ : ℝ → ℝ} (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hV : ∀ t ∈ Icc t₀ T, PhaseJetBound n (γ t * BV)
      (scaledPhaseProfile ell h (w.switchedLeading r h t)))
    (hP : ∀ t ∈ Icc t₀ T, PhaseJetBound n (γ t * BP)
      (scaledPhaseProfile ell h (fun a z => freq * w.switchedPressure r h t a z))) :
    let count : ℝ := (hierarchyAdmissibleWords (Fin 4) n).card
    HierarchyTwistedProfile.amplitudeSeminorm False ell h n d.end_pos d.nonneg_start
      d.start_lt_end.le γ hγ hpos (twistedLeading d k) ≤ count * BV ∧
    freq * HierarchyTwistedProfile.amplitudeSeminorm False ell h n d.end_pos d.nonneg_start
      d.start_lt_end.le γ hγ hpos (twistedPressure d k) ≤ count * BP := by
  let v := twistedLeading d k
  let p := twistedPressure d k
  let P : HierarchyTwistedProfile T k ℝ := freq • p
  have hVwhole := w.contDiffOn_switchedLeading d.start_lt_end d.rate_nonneg d.envelope_pos
    d.phase_pos d.phase_le_one d.amplitude_smooth
  have hPwhole := w.contDiffOn_switchedPressure d.start_lt_end d.rate_nonneg d.envelope_pos
    d.phase_pos d.phase_le_one d.strain_smooth d.covector_smooth d.covector_nonzero d.amplitude_smooth
  have hVreg (t : ℝ) (ht : t ∈ Icc t₀ T) :
      ContDiff ℝ ∞ (Function.uncurry (w.switchedLeading r h t)) := by
    apply contDiffOn_univ.mp
    exact hVwhole.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ => ⟨ht.2, mem_univ _⟩)
  have hPreg (t : ℝ) (ht : t ∈ Icc t₀ T) :
      ContDiff ℝ ∞ (Function.uncurry (fun a z => freq * w.switchedPressure r h t a z)) := by
    apply contDiff_const.mul
    apply contDiffOn_univ.mp
    exact hPwhole.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ => ⟨ht.2, mem_univ _⟩)
  have hcellV (t : ℝ) (ht : t ∈ Icc t₀ T) (a : Vec3) (ha : a ∈ centeredCell) (z : ℝ) :
      v.val.val.val (t, a, z) = w.switchedLeading r h t a z :=
    twistedLeading_cell_eval d k ⟨d.nonneg_start.trans ht.1, ht.2⟩ ha z
  have hcellP (t : ℝ) (ht : t ∈ Icc t₀ T) (a : Vec3) (ha : a ∈ centeredCell) (z : ℝ) :
      P.val.val.val (t, a, z) = freq * w.switchedPressure r h t a z := by
    change freq * p.val.val.val (t, a, z) = _
    rw [show p.val.val.val (t, a, z) = _ from
      twistedPressure_cell_eval d k ⟨d.nonneg_start.trans ht.1, ht.2⟩ ha z]
  have hWrapV (t : ℝ) (ht : t ∈ Icc t₀ T) : PhaseJetBound n (γ t * BV)
      (scaledPhaseProfile ell h (fun a z => v.val.val.val (t, a, z))) :=
    HierarchyTwistedProfile.phaseJetBound_of_centeredCell ⟨d.nonneg_start.trans ht.1, ht.2⟩
      d.envelope_pos.ne' d.phase_pos.ne' (hVreg t ht) (hcellV t ht) (hV t ht)
  have hWrapP (t : ℝ) (ht : t ∈ Icc t₀ T) : PhaseJetBound n (γ t * BP)
      (scaledPhaseProfile ell h (fun a z => P.val.val.val (t, a, z))) :=
    HierarchyTwistedProfile.phaseJetBound_of_centeredCell ⟨d.nonneg_start.trans ht.1, ht.2⟩
      d.envelope_pos.ne' d.phase_pos.ne' (hPreg t ht) (hcellP t ht) (hP t ht)
  refine ⟨HierarchyTwistedProfile.amplitudeSeminorm_le_of_scaledJetBound d.end_pos
    d.nonneg_start d.start_lt_end.le hγ hpos d.envelope_pos.ne' d.phase_pos.ne' hBV hWrapV, ?_⟩
  have hpBound := HierarchyTwistedProfile.amplitudeSeminorm_le_of_scaledJetBound (u := P)
    d.end_pos d.nonneg_start d.start_lt_end.le hγ hpos d.envelope_pos.ne' d.phase_pos.ne' hBP hWrapP
  change (HierarchyTwistedProfile.amplitudeSeminorm False ell h n d.end_pos d.nonneg_start
    d.start_lt_end.le γ hγ hpos) (freq • p) ≤ _ at hpBound
  rwa [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hfreq] at hpBound

end
end TorusEuler.LocalizedAmplitude.SeedOn
