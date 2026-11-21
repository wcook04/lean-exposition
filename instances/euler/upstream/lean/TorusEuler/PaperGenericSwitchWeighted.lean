import TorusEuler.ParentSeedJetBudgets

/-! Weighted leading-profile estimates for an arbitrary time cutoff. -/

open Set
open scoped ContDiff

namespace TorusEuler.LocalizedAmplitude

private theorem contDiff_seedSlice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {t₀ T t : ℝ} {f : ℝ → Vec3 × ℝ → E}
    (hf : ContDiffOn ℝ ∞ (fun x : ℝ × Vec3 × ℝ => f x.1 x.2) (Icc t₀ T ×ˢ univ))
    (ht : t ∈ Icc t₀ T) : ContDiff ℝ ∞ (f t) := by
  let incl (z : Vec3 × ℝ) : ℝ × Vec3 × ℝ := (t, z)
  have hIncl : ContDiffOn ℝ ∞ incl univ := (contDiff_const.prodMk contDiff_id).contDiffOn
  have hMaps : MapsTo incl univ (Icc t₀ T ×ˢ univ) := fun _ _ => ⟨ht, mem_univ _⟩
  have hSlice : ContDiffOn ℝ ∞ ((fun x : ℝ × Vec3 × ℝ => f x.1 x.2) ∘ incl) univ :=
    hf.comp hIncl hMaps
  exact contDiffOn_univ.mp hSlice

set_option maxHeartbeats 1800000 in
/-- The leading estimate depends only on the value of the cutoff at each
time. A smooth wrapped pair agreeing with the scaled seed on the centered
cell inherits the same weighted budget for every cutoff bounded by one. -/
theorem exists_parent_seed_genericSwitch_ampSeminorm_le (W : ℕ → ℝ) (hW : ∀ m, 0 ≤ W m) :
    ∃ A : ℕ, 30 ≤ A ∧ ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T t₀ D ℓ Cseed freq r : ℝ}
        {k : Vec3} {center : ℝ → Vec3},
      T ≤ 1 → 2 ≤ D → 0 < ℓ → ℓ ≤ (D ^ A)⁻¹ →
      ∀ (hf : 1 ≤ freq), ‖labelWaveVector X 0 0 k t₀‖ = freq →
      IsLabelFlowOn U X (Icc 0 T) →
      ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
      (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
      (∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
        ‖iteratedFDeriv ℝ j (U t) x‖ ≤ W n * D ^ j) →
      let M (t : ℝ) (a : Vec3) := fderiv ℝ (U t) (X 0 t a)
      let κ (t : ℝ) (a : Vec3) := labelWaveVector X 0 a k t
      ∀ (hc : CenterWaveOn (fun t => M t 0) (fun t => κ t 0) center t₀ T D)
        (w : SeedOn M κ center t₀ T ℓ D Cseed),
      let h := freq ^ (-1 / 2 : ℝ)
      ∀ (d : w.HierarchyRegularity r h),
      let γ (t : ℝ) := freq ^ (3 / 4 : ℝ) * ‖center t‖
      let hγ : ContinuousOn γ (Icc t₀ T) :=
        (HasDerivWithinAt.continuousOn hc.amplitude).norm.const_mul _
      let hpos (t : ℝ) (ht : t ∈ Icc t₀ T) : 0 < γ t :=
        mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hf) _)
          (norm_pos_iff.mpr (hc.nonzero t ht).2.1)
      ∀ (c : ℝ → ℝ) (v : HierarchyTwistedProfile T k Vec3) (p : HierarchyTwistedProfile T k ℝ),
      (∀ t ∈ Icc t₀ T, |c t| ≤ 1) →
      (∀ t ∈ Icc t₀ T, ∀ a ∈ centeredCell, ∀ z,
        v.val.val.val (t, a, z) = c t • w.leading h t a z) →
      (∀ t ∈ Icc t₀ T, ∀ a ∈ centeredCell, ∀ z,
        p.val.val.val (t, a, z) = c t * w.leadingPressure h t a z) →
      HierarchyTwistedProfile.amplitudeSeminorm False ℓ h n d.end_pos d.nonneg_start
          d.start_lt_end.le γ hγ hpos v +
        freq * HierarchyTwistedProfile.amplitudeSeminorm False ℓ h n d.end_pos d.nonneg_start
          d.start_lt_end.le γ hγ hpos p ≤ C * D ^ 20 * freq ^ (-5 / 4 : ℝ) := by
  obtain ⟨A, hA, hRawAll⟩ := exists_parent_seed_leadingScaledJetBounds W hW
  refine ⟨A, hA, fun n => ?_⟩
  obtain ⟨C₀, hC₀, hRaw⟩ := hRawAll n
  let count : ℝ := (hierarchyAdmissibleWords (Fin 4) n).card
  let C := 2 * count * C₀
  have hC₀' := zero_le_one.trans hC₀
  refine ⟨C, mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) hC₀', ?_⟩
  intro U X T t₀ D ℓ Cseed freq r k center hT hD hℓ hℓA hf hfreq
    hX hU hper hF hG hUjets M κ hc w h d γ hγ hpos c v p hc₁ hv hp
  let B := C₀ * D ^ 20 * freq ^ (-5 / 4 : ℝ)
  have hD₀ : 0 ≤ D := by linarith
  have hf₀ := zero_le_one.trans hf
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let P : HierarchyTwistedProfile T k ℝ := freq • p
  have hVwhole := w.contDiffOn_leading d.envelope_pos d.phase_pos d.phase_le_one d.amplitude_smooth
  have hPwhole := w.contDiffOn_leadingPressure d.envelope_pos d.phase_pos d.phase_le_one
    d.strain_smooth d.covector_smooth d.covector_nonzero d.amplitude_smooth
  have hWrap (t : ℝ) (ht : t ∈ Icc t₀ T) :
      PhaseJetBound n (γ t * B) (scaledPhaseProfile ℓ h (fun a z => v.val.val.val (t, a, z))) ∧
      PhaseJetBound n (γ t * B) (scaledPhaseProfile ℓ h (fun a z => P.val.val.val (t, a, z))) := by
    have hVraw : ContDiff ℝ ∞ (fun z : Vec3 × ℝ => w.leading h t z.1 z.2) :=
      contDiff_seedSlice (f := fun t z => w.leading h t z.1 z.2) hVwhole ht
    have hPraw : ContDiff ℝ ∞ (fun z : Vec3 × ℝ => w.leadingPressure h t z.1 z.2) :=
      contDiff_seedSlice (f := fun t z => w.leadingPressure h t z.1 z.2) hPwhole ht
    have hVr : ContDiff ℝ ∞ (Function.uncurry (fun a z => c t • w.leading h t a z)) := by
      rw [show Function.uncurry (fun a z => c t • w.leading h t a z) =
        (fun z : Vec3 × ℝ => c t • w.leading h t z.1 z.2) from funext fun ⟨_, _⟩ => rfl]
      exact hVraw.const_smul (c t)
    have hPr : ContDiff ℝ ∞ (Function.uncurry (fun a z => freq * (c t * w.leadingPressure h t a z))) := by
      rw [show Function.uncurry (fun a z => freq * (c t * w.leadingPressure h t a z)) =
        (fun z : Vec3 × ℝ => freq * (c t * w.leadingPressure h t z.1 z.2)) from funext fun ⟨_, _⟩ => rfl]
      exact (contDiff_const (c := freq)).mul ((contDiff_const (c := c t)).mul hPraw)
    have hPcell (a : Vec3) (ha : a ∈ centeredCell) (z : ℝ) :
        P.val.val.val (t, a, z) = freq * (c t * w.leadingPressure h t a z) :=
      congrArg (fun x : ℝ => freq * x) (hp t ht a ha z)
    have ht' : t ∈ Icc 0 T := ⟨d.nonneg_start.trans ht.1, ht.2⟩
    obtain ⟨hVjet, hPjet⟩ := hRaw d.nonneg_start d.start_lt_end hT hD hℓ hℓA hf hfreq
      hX hU hper hF hG hUjets hc w (hc₁ t ht) t ht
    exact ⟨HierarchyTwistedProfile.phaseJetBound_of_centeredCell ht' hℓ.ne' d.phase_pos.ne'
      hVr (hv t ht) hVjet,
      HierarchyTwistedProfile.phaseJetBound_of_centeredCell ht' hℓ.ne' d.phase_pos.ne'
        hPr hPcell hPjet⟩
  let NV : Seminorm ℝ (HierarchyTwistedProfile T k Vec3) :=
    HierarchyTwistedProfile.amplitudeSeminorm False ℓ h n d.end_pos d.nonneg_start
      d.start_lt_end.le γ hγ hpos
  let NP : Seminorm ℝ (HierarchyTwistedProfile T k ℝ) :=
    HierarchyTwistedProfile.amplitudeSeminorm False ℓ h n d.end_pos d.nonneg_start
      d.start_lt_end.le γ hγ hpos
  have hvBound : NV v ≤ count * B :=
    HierarchyTwistedProfile.amplitudeSeminorm_le_of_scaledJetBound d.end_pos
      d.nonneg_start d.start_lt_end.le hγ hpos hℓ.ne' d.phase_pos.ne' hB fun t ht => (hWrap t ht).1
  have hpBound : NP P ≤ count * B :=
    HierarchyTwistedProfile.amplitudeSeminorm_le_of_scaledJetBound d.end_pos
      d.nonneg_start d.start_lt_end.le hγ hpos hℓ.ne' d.phase_pos.ne' hB fun t ht => (hWrap t ht).2
  change NP (freq • p) ≤ _ at hpBound
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hf₀] at hpBound
  calc
    _ ≤ count * B + count * B := add_le_add hvBound hpBound
    _ = _ := by dsimp only [B, C]; ring

end TorusEuler.LocalizedAmplitude
