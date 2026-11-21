import TorusEuler.HierarchyTwistedCompletion
import TorusEuler.HierarchyConcreteTransverse
import TorusEuler.HierarchySupportPropagation
import TorusEuler.LocalizedSeedRegularity

/-! The actual later-wave leading input in the skew-periodic hierarchy,
including both terms of the activation residual. -/

open ContinuousLinearMap Filter Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

noncomputable section

private theorem deriv_waveSwitch_zero_before {t₀ r t : ℝ} (hr : 0 ≤ r) (ht : t ≤ t₀) :
    deriv (waveSwitch t₀ r) t = 0 := by
  have h := ((contDiff_waveSwitch t₀ r).differentiable (by simp) t).hasDerivAt
  have h0 : HasDerivWithinAt (waveSwitch t₀ r) 0 (Iic t₀) t := by
    refine (hasDerivWithinAt_const t (Iic t₀) (0 : ℝ)).congr ?_ ?_
    · exact fun u hu => waveSwitch_eq_zero_of_le hr hu
    · exact waveSwitch_eq_zero_of_le hr ht
  have hI := uniqueDiffOn_Iic t₀ t ht
  exact (h.hasDerivWithinAt.derivWithin hI).symm.trans (h0.derivWithin hI)

private theorem contDiff_deriv_waveSwitch (t₀ r : ℝ) :
    ContDiff ℝ ∞ (deriv (waveSwitch t₀ r)) := by
  apply ContDiff.deriv'
  simpa using (contDiff_waveSwitch t₀ r)

namespace HierarchyTwistedProfile

variable {T : ℝ} {k : Vec3}

private def wrapOnSlab {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → Vec3 → ℝ → E}
    (hf : ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint =>
      phaseTwistedPeriodizeCentered k f x.1 x.2.1 x.2.2) (hierarchyProfileSlab T))
    (hper : ∀ t a, Function.Periodic (f t a) 1) : HierarchyTwistedProfile T k E :=
  ofSmooth (fun x => phaseTwistedPeriodizeCentered k f x.1 x.2.1 x.2.2) hf
    (fun x => by
      rcases x with ⟨t, a, s⟩
      simpa only [hierarchyPhasePeriod, Prod.mk_add_mk, add_zero] using
        (phaseTwistedPeriodizeCentered_phase_periodic (k := k) (hper t) a s))
    (fun n x => by
      rw [add_hierarchyLatticeShift]
      exact phaseTwistedPeriodizeCentered_translate k f x.1 x.2.1 x.2.2 n)

private theorem wrapOnSlab_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → Vec3 → ℝ → E}
    (hf : ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint =>
      phaseTwistedPeriodizeCentered k f x.1 x.2.1 x.2.2) (hierarchyProfileSlab T))
    (hper : ∀ t a, Function.Periodic (f t a) 1) {t : ℝ} (ht : t ∈ Icc 0 T)
    (a : Vec3) (s : ℝ) :
    (wrapOnSlab hf hper).val.val.val (t, a, s) = phaseTwistedPeriodizeCentered k f t a s :=
  ofSmooth_eval _ _ _ ⟨ht, mem_univ _⟩

private theorem all_on_centeredCell {Q : HierarchyProfilePoint → Prop}
    (hShift : ∀ (t : ℝ) (a : Vec3) (s : ℝ) (n : Fin 3 → ℤ),
      Q (t, a, s) → Q (t, a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ))
    (hCell : ∀ t ∈ Icc 0 T, ∀ a ∈ centeredCell, ∀ s, Q (t, a, s)) :
    ∀ x ∈ hierarchyProfileSlab T, Q x := by
  rintro ⟨t, a, s⟩ ht
  obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell a
  have hz := hShift t (a - latticeVector n) (s - ⟪k, latticeVector n⟫_ℝ) n
    (hCell t ht.1 _ hn _)
  simpa only [sub_add_cancel] using hz

private theorem eq_of_centeredCell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : HierarchyTwistedProfile T k E}
    (hEq : ∀ t ∈ Icc 0 T, ∀ a ∈ centeredCell, ∀ s, f.val.val.val (t, a, s) = g.val.val.val (t, a, s)) :
    f = g := by
  apply HierarchyTwistedProfile.ext
  refine all_on_centeredCell (k := k) (T := T)
    (Q := fun x => f.val.val.val x = g.val.val.val x) ?_ hEq
  intro t a s n h
  rw [twistedSlice f, twistedSlice g]
  exact h

end HierarchyTwistedProfile

namespace LocalizedAmplitude.SeedOn

variable {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3}
  {center : ℝ → Vec3} {t₀ T ell D C r h : ℝ}

private theorem deriv_switchedPressure_raw (w : SeedOn M κ center t₀ T ell D C)
    (hh : 0 < h) (hh₁ : h ≤ 1) (t : ℝ) (a : Vec3) (s : ℝ) :
    deriv (w.switchedPressure r h t a) s =
      (waveSwitch t₀ r t * (radialEnvelope ell a * waveProfile h s)) *
        oscillatoryPressureSlope (M t a) (κ t a) 0 (w.amplitude t a) := by
  have hd := (((hasDerivAt_wavePressurePrimitive hh hh₁ s).const_mul
    (-wavePressureCoefficient (radialEnvelope ell a) (κ t a) (w.amplitude t a) (M t a))).const_mul
      (waveSwitch t₀ r t)).deriv
  change deriv (w.switchedPressure r h t a) s = _ at hd
  rw [hd]
  simp only [wavePressureCoefficient, oscillatoryPressureSlope, inner_zero_right, zero_sub, div_eq_mul_inv]
  ring

private theorem hasDerivWithinAt_switchedLeading_zero_left (w : SeedOn M κ center t₀ T ell D C)
    (hr : 0 ≤ r) {t : ℝ} (ht : t ≤ t₀) (a : Vec3) (s : ℝ) :
    HasDerivWithinAt (fun u => w.switchedLeading r h u a s) 0 (Iic t₀) t :=
  (hasDerivWithinAt_const t (Iic t₀) (0 : Vec3)).congr
    (fun _ hu => w.switchedLeading_eq_zero_before_activation hr hu a s)
    (w.switchedLeading_eq_zero_before_activation hr ht a s)

private theorem hasDerivWithinAt_switchedLeading_momentum_active
    (w : SeedOn M κ center t₀ T ell D C) (hh : 0 < h) (hh₁ : h ≤ 1)
    {t : ℝ} (ht : t ∈ Icc t₀ T) (a : Vec3) (s : ℝ) :
    HasDerivWithinAt (fun u => w.switchedLeading r h u a s)
      (deriv (waveSwitch t₀ r) t • w.leading h t a s - M t a (w.switchedLeading r h t a s) -
        deriv (w.switchedPressure r h t a) s • κ t a) (Icc t₀ T) t := by
  let b := radialEnvelope ell a * waveProfile h s
  have hAmp := (w.equation a t ht).const_smul b
  have hχ := ((contDiff_waveSwitch t₀ r).differentiable (by simp) t).hasDerivAt.hasDerivWithinAt
    (s := Icc t₀ T)
  have hD := hχ.smul hAmp
  change HasDerivWithinAt (fun u => w.switchedLeading r h u a s) _ (Icc t₀ T) t at hD
  have hOp := affineWaveAmplitudeOperator_add_transverseProjection (M t a) (κ t a) 0 (w.amplitude t a)
  simp only [map_zero, add_zero, zero_sub] at hOp
  refine hD.congr_deriv ?_
  rw [hOp, deriv_switchedPressure_raw w hh hh₁]
  simp only [b, SeedOn.switchedLeading, SeedOn.leading, Pi.smul_apply, map_smul,
    smul_sub, smul_neg, smul_smul, mul_assoc]
  abel

/-- Before activation the switch forcing, velocity and phase pressure all vanish. -/
theorem switchedLeading_momentum_terms_eq_zero_before
    (w : SeedOn M κ center t₀ T ell D C) (hr : 0 ≤ r) {t : ℝ} (ht : t ≤ t₀)
    (a : Vec3) (s : ℝ) :
    deriv (waveSwitch t₀ r) t • w.leading h t a s = 0 ∧
      w.switchedLeading r h t a s = 0 ∧ deriv (w.switchedPressure r h t a) s = 0 := by
  refine ⟨by rw [deriv_waveSwitch_zero_before hr ht, zero_smul],
    w.switchedLeading_eq_zero_before_activation hr ht a s, ?_⟩
  have hz : w.switchedPressure r h t a = fun _ => 0 := by
    funext q
    rw [SeedOn.switchedPressure, waveSwitch_eq_zero_of_le hr ht, zero_mul]
  rw [hz, deriv_const]

/-- The raw switched seed solves the lifted momentum equation with only the
switch velocity forcing, including at the activation seam. -/
theorem hasDerivWithinAt_switchedLeading_momentum
    (w : SeedOn M κ center t₀ T ell D C) (hr : 0 ≤ r) (hh : 0 < h) (hh₁ : h ≤ 1)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    HasDerivWithinAt (fun u => w.switchedLeading r h u a s)
      (deriv (waveSwitch t₀ r) t • w.leading h t a s - M t a (w.switchedLeading r h t a s) -
        deriv (w.switchedPressure r h t a) s • κ t a) (Icc 0 T) t := by
  rcases lt_trichotomy t t₀ with hlt | rfl | hgt
  · obtain ⟨hf, hv, hp⟩ := switchedLeading_momentum_terms_eq_zero_before (h := h) w hr hlt.le a s
    simp only [hf, hv, hp, map_zero, zero_smul, sub_zero]
    exact ((hasDerivWithinAt_switchedLeading_zero_left (h := h) w hr hlt.le a s).hasDerivAt
      (Iic_mem_nhds hlt)).hasDerivWithinAt
  · obtain ⟨hf, hv, hp⟩ := switchedLeading_momentum_terms_eq_zero_before (h := h) w hr (le_refl t) a s
    have hright := hasDerivWithinAt_switchedLeading_momentum_active (r := r) w hh hh₁
      ⟨le_rfl, ht.2⟩ a s
    simp only [hf, hv, hp, map_zero, zero_smul, sub_zero] at hright ⊢
    refine ((hasDerivWithinAt_switchedLeading_zero_left (h := h) w hr (le_refl t) a s).union hright).mono ?_
    intro u hu
    by_cases h : u ≤ t
    · exact Or.inl h
    · exact Or.inr ⟨le_of_not_ge h, hu.2⟩
  · apply (hasDerivWithinAt_inter (Ici_mem_nhds hgt)).mp
    exact (hasDerivWithinAt_switchedLeading_momentum_active (r := r) w hh hh₁
      ⟨hgt.le, ht.2⟩ a s).mono (fun _ hu => ⟨hu.2, hu.1.2⟩)

/-- The pointwise momentum identity written with the actual slab and phase
derivatives. -/
theorem switchedLeading_momentum (w : SeedOn M κ center t₀ T ell D C)
    (hT : 0 < T) (hr : 0 ≤ r) (hh : 0 < h) (hh₁ : h ≤ 1)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    derivWithin (fun u => w.switchedLeading r h u a s) (Icc 0 T) t +
      M t a (w.switchedLeading r h t a s) + deriv (w.switchedPressure r h t a) s • κ t a =
        deriv (waveSwitch t₀ r) t • w.leading h t a s := by
  rw [(hasDerivWithinAt_switchedLeading_momentum w hr hh hh₁ ht a s).derivWithin
    (uniqueDiffOn_Icc hT t ht)]
  abel

end LocalizedAmplitude.SeedOn

namespace LocalizedAmplitude.SeedOn

variable {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3}
  {center : ℝ → Vec3} {t₀ T ell D C : ℝ}
  (w : SeedOn M κ center t₀ T ell D C)

/-- The local smooth seed data required by the flat, cell-supported
profiles. The carrier frequency and coefficient identities are used
separately when selecting the hierarchy operators. -/
structure HierarchyRegularity (r h : ℝ) : Prop where
  nonneg_start : 0 ≤ t₀
  start_lt_end : t₀ < T
  rate_nonneg : 0 ≤ r
  envelope_pos : 0 < ell
  envelope_fits : 2 * ell < 1 / 2
  phase_pos : 0 < h
  phase_le_one : h ≤ 1
  strain_smooth : ContDiffOn ℝ ∞ (Function.uncurry M) (Icc t₀ T ×ˢ (univ : Set Vec3))
  covector_smooth : ContDiffOn ℝ ∞ (Function.uncurry κ) (Icc t₀ T ×ˢ (univ : Set Vec3))
  covector_nonzero : ∀ t ∈ Icc t₀ T, ∀ a, κ t a ≠ 0
  amplitude_smooth : ContDiffOn ℝ ∞ (Function.uncurry w.amplitude) (Icc t₀ T ×ˢ (univ : Set Vec3))

variable {w} {r h : ℝ}

theorem HierarchyRegularity.end_pos (d : w.HierarchyRegularity r h) : 0 < T :=
  d.nonneg_start.trans_lt d.start_lt_end

/-- The velocity part of the activation residual, before wrapping the label cell. -/
def leadingSwitchProfile (w : SeedOn M κ center t₀ T ell D C) (r h : ℝ)
    (t : ℝ) (a : Vec3) (s : ℝ) : Vec3 :=
  deriv (waveSwitch t₀ r) t • w.leading h t a s

private theorem leadingBare_smooth (d : w.HierarchyRegularity r h) :
    ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint => waveProfile h x.2.2 • w.amplitude x.1 x.2.1)
      (Icc t₀ T ×ˢ univ) := by
  have hA := d.amplitude_smooth.comp (contDiff_fst.prodMk contDiff_snd.fst).contDiffOn
    (fun x (hx : x ∈ Icc t₀ T ×ˢ (univ : Set (Vec3 × ℝ))) => ⟨hx.1, mem_univ _⟩)
  exact ((contDiff_waveProfile d.phase_pos d.phase_le_one).comp contDiff_snd.snd).contDiffOn.smul hA

private def barePressure (w : SeedOn M κ center t₀ T ell D C) (h : ℝ)
    (t : ℝ) (a : Vec3) (s : ℝ) : ℝ :=
  -wavePressureCoefficient 1 (κ t a) (w.amplitude t a) (M t a) * wavePressurePrimitive h s

private theorem leadingPressure_eq_envelope (w : SeedOn M κ center t₀ T ell D C)
    (h t : ℝ) (a : Vec3) (s : ℝ) :
    w.leadingPressure h t a s = radialEnvelope ell a * w.barePressure h t a s := by
  simp only [SeedOn.leadingPressure, barePressure, wavePressureCoefficient, div_eq_mul_inv]
  ring

set_option maxHeartbeats 450000 in
private theorem barePressure_smooth (d : w.HierarchyRegularity r h) :
    ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint => w.barePressure h x.1 x.2.1 x.2.2)
      (Icc t₀ T ×ˢ univ) := by
  let I : Set HierarchyProfilePoint := Icc t₀ T ×ˢ univ
  let L (x : HierarchyProfilePoint) := (x.1, x.2.1)
  have hL : ContDiffOn ℝ ∞ L I := (contDiff_fst.prodMk contDiff_snd.fst).contDiffOn
  have hmaps : MapsTo L I (Icc t₀ T ×ˢ (univ : Set Vec3)) := fun _ hx => ⟨hx.1, mem_univ _⟩
  have hK := d.covector_smooth.comp hL hmaps
  have hA := d.amplitude_smooth.comp hL hmaps
  have hM := d.strain_smooth.comp hL hmaps
  have hn (x : HierarchyProfilePoint) (hx : x ∈ I) : ‖κ x.1 x.2.1‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (d.covector_nonzero x.1 hx.1 x.2.1))
  have hCoef := (contDiffOn_const (c := (2 : ℝ))).mul (hK.inner ℝ (hM.clm_apply hA))
  have hC := (hCoef.div (ContDiffOn.norm_sq ℝ hK) hn).neg
  simpa only [barePressure, wavePressureCoefficient, mul_one, Function.comp_apply,
    Function.uncurry_apply_pair, Pi.div_apply, L, I] using
    hC.mul (((contDiff_wavePressurePrimitive d.phase_pos d.phase_le_one).comp contDiff_snd.snd).contDiffOn)

private theorem switchedPressure_periodic (w : SeedOn M κ center t₀ T ell D C)
    (d : w.HierarchyRegularity r h) (t : ℝ) (a : Vec3) :
    Function.Periodic (w.switchedPressure r h t a) 1 := by
  intro s
  simp only [SeedOn.switchedPressure, SeedOn.leadingPressure,
    periodic_wavePressurePrimitive d.phase_pos d.phase_le_one s]

private theorem leadingSwitch_periodic (w : SeedOn M κ center t₀ T ell D C)
    (d : w.HierarchyRegularity r h) (t : ℝ) (a : Vec3) :
    Function.Periodic (w.leadingSwitchProfile r h t a) 1 := by
  intro s
  simp only [leadingSwitchProfile, SeedOn.leading, periodic_waveProfile d.phase_pos d.phase_le_one s]

private theorem twistedLeading_smooth (d : w.HierarchyRegularity r h) (k : Vec3) :
    ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint =>
      phaseTwistedPeriodizeCentered k (w.switchedLeading r h) x.1 x.2.1 x.2.2)
      (hierarchyProfileSlab T) :=
  (w.contDiffOn_twistedSwitchedLeading k d.start_lt_end d.rate_nonneg d.envelope_pos
    d.envelope_fits d.phase_pos d.phase_le_one d.amplitude_smooth).mono
    (fun _ hx => ⟨hx.1.2, mem_univ _⟩)

private theorem twistedPressure_smooth (d : w.HierarchyRegularity r h) (k : Vec3) :
    ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint =>
      phaseTwistedPeriodizeCentered k (w.switchedPressure r h) x.1 x.2.1 x.2.2)
      (hierarchyProfileSlab T) := by
  have hEq : w.switchedPressure r h = fun t a s =>
      waveSwitch t₀ r t • (radialEnvelope ell a • w.barePressure h t a s) := by
    funext t a s
    rw [SeedOn.switchedPressure, leadingPressure_eq_envelope]
    rfl
  rw [hEq]
  exact (contDiffOn_phaseTwistedPeriodizeCentered_flatActivation (k := k) d.start_lt_end
    d.envelope_pos d.envelope_fits (contDiff_waveSwitch t₀ r)
    (fun _ ht => waveSwitch_eq_zero_of_le d.rate_nonneg ht) (barePressure_smooth d)).mono
      (fun _ hx => ⟨hx.1.2, mem_univ _⟩)

private theorem twistedLeadingSwitch_smooth (d : w.HierarchyRegularity r h) (k : Vec3) :
    ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint =>
      phaseTwistedPeriodizeCentered k (w.leadingSwitchProfile r h) x.1 x.2.1 x.2.2)
      (hierarchyProfileSlab T) := by
  have hEq : w.leadingSwitchProfile r h = fun t a s =>
      deriv (waveSwitch t₀ r) t • (radialEnvelope ell a • (waveProfile h s • w.amplitude t a)) := by
    funext t a s
    simp only [leadingSwitchProfile, SeedOn.leading, smul_smul]
  rw [hEq]
  exact (contDiffOn_phaseTwistedPeriodizeCentered_flatActivation (k := k) d.start_lt_end
    d.envelope_pos d.envelope_fits (contDiff_deriv_waveSwitch t₀ r)
    (fun _ ht => deriv_waveSwitch_zero_before d.rate_nonneg ht) (leadingBare_smooth d)).mono
      (fun _ hx => ⟨hx.1.2, mem_univ _⟩)

/-- The actual switched later-wave velocity in the twisted hierarchy. -/
def twistedLeading (d : w.HierarchyRegularity r h) (k : Vec3) : HierarchyTwistedProfile T k Vec3 :=
  HierarchyTwistedProfile.wrapOnSlab (twistedLeading_smooth d k)
    (fun _ a => w.switchedLeading_periodic_phase d.phase_pos d.phase_le_one a)

/-- The actual switched later-wave pressure in the twisted hierarchy. -/
def twistedPressure (d : w.HierarchyRegularity r h) (k : Vec3) : HierarchyTwistedProfile T k ℝ :=
  HierarchyTwistedProfile.wrapOnSlab (twistedPressure_smooth d k) (switchedPressure_periodic w d)

/-- The actual flat activation source entering the leading transverse equation. -/
def twistedLeadingSwitch (d : w.HierarchyRegularity r h) (k : Vec3) : HierarchyTwistedProfile T k Vec3 :=
  HierarchyTwistedProfile.wrapOnSlab (twistedLeadingSwitch_smooth d k) (leadingSwitch_periodic w d)

theorem twistedLeading_eval (d : w.HierarchyRegularity r h) (k : Vec3) {t : ℝ}
    (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (twistedLeading d k).val.val.val (t, a, s) =
      phaseTwistedPeriodizeCentered k (w.switchedLeading r h) t a s :=
  HierarchyTwistedProfile.wrapOnSlab_eval _ _ ht a s

theorem twistedPressure_eval (d : w.HierarchyRegularity r h) (k : Vec3) {t : ℝ}
    (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (twistedPressure d k).val.val.val (t, a, s) =
      phaseTwistedPeriodizeCentered k (w.switchedPressure r h) t a s :=
  HierarchyTwistedProfile.wrapOnSlab_eval _ _ ht a s

theorem twistedLeadingSwitch_eval (d : w.HierarchyRegularity r h) (k : Vec3) {t : ℝ}
    (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (twistedLeadingSwitch d k).val.val.val (t, a, s) =
      phaseTwistedPeriodizeCentered k (w.leadingSwitchProfile r h) t a s :=
  HierarchyTwistedProfile.wrapOnSlab_eval _ _ ht a s

private theorem wrapped_eq_on_cell_of_radial_zero {E : Type*} [Zero E]
    {f : ℝ → Vec3 → ℝ → E} (k : Vec3) {t : ℝ} {a : Vec3}
    (ha : a ∈ centeredCell) (s : ℝ) (hfit : 2 * ell < 1 / 2)
    (hzero : ∀ b, 2 * ell ≤ ‖b‖ → ∀ q, f t b q = 0) :
    phaseTwistedPeriodizeCentered k f t a s = f t a s := by
  refine phaseTwistedPeriodizeCentered_eq_on_centeredCell (sub_pos.mpr hfit) ?_ ha s
  intro b hb q
  obtain ⟨i, hi⟩ := hb
  have hbi : |b i| ≤ ‖b‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le b i
  exact hzero b (by linarith) q

theorem twistedLeading_cell_eval (d : w.HierarchyRegularity r h) (k : Vec3) {t : ℝ}
    (ht : t ∈ Icc 0 T) {a : Vec3} (ha : a ∈ centeredCell) (s : ℝ) :
    (twistedLeading d k).val.val.val (t, a, s) = w.switchedLeading r h t a s := by
  rw [twistedLeading_eval d k ht]
  exact wrapped_eq_on_cell_of_radial_zero k ha s d.envelope_fits
    (fun b hb q => w.switchedLeading_eq_zero_outside_envelope d.envelope_pos hb q)

theorem twistedPressure_cell_eval (d : w.HierarchyRegularity r h) (k : Vec3) {t : ℝ}
    (ht : t ∈ Icc 0 T) {a : Vec3} (ha : a ∈ centeredCell) (s : ℝ) :
    (twistedPressure d k).val.val.val (t, a, s) = w.switchedPressure r h t a s := by
  rw [twistedPressure_eval d k ht]
  refine wrapped_eq_on_cell_of_radial_zero k ha s d.envelope_fits (fun b hb q => ?_)
  simp only [SeedOn.switchedPressure, leadingPressure_eq_envelope,
    radialEnvelope_eq_zero d.envelope_pos hb, zero_mul, mul_zero]

theorem twistedLeadingSwitch_cell_eval (d : w.HierarchyRegularity r h) (k : Vec3) {t : ℝ}
    (ht : t ∈ Icc 0 T) {a : Vec3} (ha : a ∈ centeredCell) (s : ℝ) :
    (twistedLeadingSwitch d k).val.val.val (t, a, s) = w.leadingSwitchProfile r h t a s := by
  rw [twistedLeadingSwitch_eval d k ht]
  refine wrapped_eq_on_cell_of_radial_zero k ha s d.envelope_fits (fun b hb q => ?_)
  simp only [leadingSwitchProfile, SeedOn.leading, radialEnvelope_eq_zero d.envelope_pos hb,
    zero_mul, zero_smul, smul_zero]

theorem twistedLeading_before_activation (d : w.HierarchyRegularity r h) (k : Vec3) {t : ℝ}
    (ht : t ∈ Icc 0 T) (ht₀ : t ≤ t₀) (a : Vec3) (s : ℝ) :
    (twistedLeading d k).val.val.val (t, a, s) = 0 := by
  rw [twistedLeading_eval d k ht, phaseTwistedPeriodizeCentered]
  exact w.switchedLeading_eq_zero_before_activation d.rate_nonneg ht₀ _ _

theorem twistedPressure_before_activation (d : w.HierarchyRegularity r h) (k : Vec3) {t : ℝ}
    (ht : t ∈ Icc 0 T) (ht₀ : t ≤ t₀) (a : Vec3) (s : ℝ) :
    (twistedPressure d k).val.val.val (t, a, s) = 0 := by
  rw [twistedPressure_eval d k ht, phaseTwistedPeriodizeCentered]
  simp only [SeedOn.switchedPressure, waveSwitch_eq_zero_of_le d.rate_nonneg ht₀, zero_mul]

theorem twistedLeadingSwitch_before_activation (d : w.HierarchyRegularity r h) (k : Vec3) {t : ℝ}
    (ht : t ∈ Icc 0 T) (ht₀ : t ≤ t₀) (a : Vec3) (s : ℝ) :
    (twistedLeadingSwitch d k).val.val.val (t, a, s) = 0 := by
  rw [twistedLeadingSwitch_eval d k ht, phaseTwistedPeriodizeCentered]
  simp only [leadingSwitchProfile, deriv_waveSwitch_zero_before d.rate_nonneg ht₀, zero_smul]

/-- The three wrapped leading profiles retain the original envelope support. -/
theorem twistedLeading_support (d : w.HierarchyRegularity r h) (k : Vec3) {t : ℝ}
    (ht : t ∈ Icc 0 T) {a : Vec3} (ha : 2 * ell ≤ ‖centeredLabel a‖) (s : ℝ) :
    (twistedLeading d k).val.val.val (t, a, s) = 0 ∧
      (twistedPressure d k).val.val.val (t, a, s) = 0 ∧
      (twistedLeadingSwitch d k).val.val.val (t, a, s) = 0 := by
  rw [twistedLeading_eval d k ht, twistedPressure_eval d k ht, twistedLeadingSwitch_eval d k ht]
  simp only [phaseTwistedPeriodizeCentered, SeedOn.switchedLeading, SeedOn.switchedPressure,
    SeedOn.leading, leadingPressure_eq_envelope, leadingSwitchProfile,
    radialEnvelope_eq_zero d.envelope_pos ha, zero_mul, mul_zero, zero_smul, smul_zero, and_self]

private theorem phaseMean_mul_waveProfile_smul (d : w.HierarchyRegularity r h)
    (c : ℝ) (v : Vec3) : phaseMean (fun s => (c * waveProfile h s) • v) = 0 := by
  let L := toSpanSingleton ℝ (c • v)
  have he : (fun s => (c * waveProfile h s) • v) = fun s => L (waveProfile h s) := by
    funext s
    change (c * waveProfile h s) • v = waveProfile h s • (c • v)
    rw [smul_smul, mul_comm]
  rw [he, phaseMean, L.intervalIntegral_comp_comm
    ((contDiff_waveProfile d.phase_pos d.phase_le_one).continuous.intervalIntegrable 0 1),
    ← phaseMean, phaseMean_waveProfile d.phase_pos d.phase_le_one, map_zero]

private theorem phaseMean_wrapped_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → Vec3 → ℝ → E} {t : ℝ} (k a : Vec3)
    (hper : ∀ b, Function.Periodic (f t b) 1) (hMean : ∀ b, phaseMean (f t b) = 0) :
    phaseMean (phaseTwistedPeriodizeCentered k f t a) = 0 := by
  let b := centeredLabel a
  let c := -⟪k, a⟫_ℝ + ⟪k, b⟫_ℝ
  have he : phaseTwistedPeriodizeCentered k f t a = fun s => f t b (s + c) := by
    funext s
    unfold phaseTwistedPeriodizeCentered
    congr 1
    dsimp [c, b]
    ring
  rw [he, phaseMean, intervalIntegral.integral_comp_add_right]
  have hc := (hper b).intervalIntegral_add_eq c 0
  simp only [zero_add] at hc
  rw [zero_add, add_comm (1 : ℝ) c, hc]
  exact hMean b

theorem twistedLeading_average_zero (d : w.HierarchyRegularity r h) (k : Vec3) :
    HierarchyTwistedProfile.profilePhaseAverage d.end_pos (twistedLeading d k) = 0 := by
  apply HierarchyTwistedProfile.ext
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  change (HierarchySmoothProfile.profilePhaseAverage d.end_pos (twistedLeading d k).val.val).val
    (t, a, s) = 0
  rw [HierarchySmoothProfile.profilePhaseAverage_apply _ _ hx]
  simp_rw [twistedLeading_eval d k ht]
  apply phaseMean_wrapped_shift k a (fun b => w.switchedLeading_periodic_phase d.phase_pos d.phase_le_one b)
  intro b
  change phaseMean (fun s => w.switchedLeading r h t b s) = 0
  simpa only [SeedOn.switchedLeading, SeedOn.leading, smul_smul, mul_assoc] using
    phaseMean_mul_waveProfile_smul d (waveSwitch t₀ r t * radialEnvelope ell b) (w.amplitude t b)

/-- The selected pressure uses the zero-phase-mean gauge. -/
theorem twistedPressure_phaseMean_zero (d : w.HierarchyRegularity r h) (k : Vec3)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) :
    phaseMean (fun s => (twistedPressure d k).val.val.val (t, a, s)) = 0 := by
  simp_rw [twistedPressure_eval d k ht]
  apply phaseMean_wrapped_shift k a (switchedPressure_periodic w d t)
  intro b
  let c := -wavePressureCoefficient (radialEnvelope ell b) (κ t b) (w.amplitude t b) (M t b)
  have hf : w.switchedPressure r h t b =
      fun q => ((waveSwitch t₀ r t) * c) * wavePressurePrimitive h q := by
    funext q
    exact (mul_assoc _ _ _).symm
  rw [hf, phaseMean, intervalIntegral.integral_const_mul, ← phaseMean,
    phaseMean_wavePressurePrimitive d.phase_pos d.phase_le_one, mul_zero]

theorem twistedLeadingSwitch_average_zero (d : w.HierarchyRegularity r h) (k : Vec3) :
    HierarchyTwistedProfile.profilePhaseAverage d.end_pos (twistedLeadingSwitch d k) = 0 := by
  apply HierarchyTwistedProfile.ext
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  change (HierarchySmoothProfile.profilePhaseAverage d.end_pos (twistedLeadingSwitch d k).val.val).val
    (t, a, s) = 0
  rw [HierarchySmoothProfile.profilePhaseAverage_apply _ _ hx]
  simp_rw [twistedLeadingSwitch_eval d k ht]
  apply phaseMean_wrapped_shift k a (leadingSwitch_periodic w d t)
  intro b
  change phaseMean (fun s => w.leadingSwitchProfile r h t b s) = 0
  simpa only [leadingSwitchProfile, SeedOn.leading, smul_smul, mul_assoc] using
    phaseMean_mul_waveProfile_smul d (deriv (waveSwitch t₀ r) t * radialEnvelope ell b) (w.amplitude t b)

variable {k : Vec3}

/-- The selected switched wave has the transverse type required at
level one. Its transversality uses the actual covector at each label. -/
def twistedLeadingOutput (d : w.HierarchyRegularity r h)
    (G M₀ : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3))
    (κ₀ : HierarchyTwistedProfile T k Vec3)
    (hκ : ∀ x ∈ hierarchyProfileSlab T, κ₀.val.val.val x = κ x.1 x.2.1) :
    HierarchyTransverseOutput (HierarchyTwistedProfile.twistedHierarchyOperators d.end_pos G M₀ κ₀) where
  V := twistedLeading d k
  p := twistedPressure d k
  average_V := twistedLeading_average_zero d k
  phaseAdv_V := by
    intro v
    apply HierarchyTwistedProfile.phaseAdv_eq_zero_of_transverse
    refine HierarchyTwistedProfile.all_on_centeredCell (k := k) (T := T)
      (Q := fun x => ⟪κ₀.val.val.val x, (twistedLeading d k).val.val.val x⟫_ℝ = 0) ?_ ?_
    · intro t a s n hz
      simpa only [HierarchyTwistedProfile.twistedSlice] using hz
    · intro t ht a ha s
      rw [hκ _ ⟨ht, mem_univ _⟩, twistedLeading_cell_eval d k ht ha]
      by_cases h : t ≤ t₀
      · rw [w.switchedLeading_eq_zero_before_activation d.rate_nonneg h, inner_zero_right]
      · simp only [SeedOn.switchedLeading, SeedOn.leading, real_inner_smul_right,
          w.transverse a t ⟨le_of_not_ge h, ht.2⟩, mul_zero]

set_option maxHeartbeats 750000 in
/-- The concrete leading momentum has exactly the flat activation
source on the entire twisted profile space. The raw equation is
checked on the closed label cell and translated by the skew shift. -/
theorem twistedLeadingOutput_momentum (d : w.HierarchyRegularity r h)
    (G M₀ : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3))
    (κ₀ : HierarchyTwistedProfile T k Vec3)
    (hM : ∀ x ∈ hierarchyProfileSlab T, M₀.val.val.val x = M x.1 x.2.1)
    (hκ : ∀ x ∈ hierarchyProfileSlab T, κ₀.val.val.val x = κ x.1 x.2.1) :
    let O := HierarchyTwistedProfile.twistedHierarchyOperators d.end_pos G M₀ κ₀
    let o := twistedLeadingOutput d G M₀ κ₀ hκ
    O.material o.V + O.phaseGrad o.p = twistedLeadingSwitch d k := by
  let O := HierarchyTwistedProfile.twistedHierarchyOperators d.end_pos G M₀ κ₀
  let V := twistedLeading d k
  let p := twistedPressure d k
  change O.material V + O.phaseGrad p = _
  apply HierarchyTwistedProfile.eq_of_centeredCell
  intro t ht a ha s
  have hz : (t, a, s) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have htD := HierarchySmoothProfile.hasDerivWithinAt_profileTime V.val.val ht a s
  have hD := htD.congr (fun u hu => (twistedLeading_cell_eval d k hu ha s).symm)
    (twistedLeading_cell_eval d k ht ha s).symm
  have hv := (hD.derivWithin (uniqueDiffOn_Icc d.end_pos t ht)).symm
  have hqp := (HierarchySmoothProfile.hasDerivAt_profilePhase p.val.val ht a s).deriv.symm
  have hpFun : (fun q => p.val.val.val (t, a, q)) = w.switchedPressure r h t a :=
    funext (twistedPressure_cell_eval d k ht ha)
  rw [hpFun] at hqp
  let O₀ := HierarchySmoothProfile.hierarchyConcreteOperators d.end_pos G.val.val M₀.val.val κ₀.val.val
  change (O₀.material V.val.val).val (t, a, s) +
      (O₀.phaseGrad p.val.val).val (t, a, s) =
      (twistedLeadingSwitch d k).val.val.val (t, a, s)
  rw [HierarchySmoothProfile.hierarchyConcreteOperators_material_apply d.end_pos
      G.val.val M₀.val.val κ₀.val.val V.val.val hz]
  change _ + (HierarchySmoothProfile.phaseGradient d.end_pos κ₀.val.val p.val.val).val (t, a, s) = _
  rw [HierarchySmoothProfile.phaseGradient_apply d.end_pos κ₀.val.val p.val.val hz,
    hM _ hz, hκ _ hz, hv, hqp, twistedLeading_cell_eval d k ht ha, twistedLeadingSwitch_cell_eval d k ht ha]
  exact w.switchedLeading_momentum d.end_pos d.rate_nonneg d.phase_pos d.phase_le_one ht a s

/-- The completion part of the activation residual is formed by applying
the exact curl completion to the derivative cutoff times the unswitched
velocity. This keeps the time splice smooth at activation. -/
def twistedCompletionSwitch (d : w.HierarchyRegularity r h)
    (G : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3))
    (κ₀ : HierarchyTwistedProfile T k Vec3)
    (hPhase : HierarchyPeriodicProfile.PhaseIndependent κ₀.val.val)
    (hκ₀ : ∀ t ∈ Icc 0 T, ∀ a, κ₀.val.val.val (t, a, 0) ≠ 0) : HierarchyTwistedProfile T k Vec3 :=
  HierarchyTwistedProfile.complete d.end_pos G κ₀ hPhase hκ₀ (twistedLeadingSwitch d k)

private theorem wavePotential_time_smul (K : Vec3) (c : ℝ) (V : ℝ → Vec3) (s : ℝ) :
    wavePotential K (fun q => c • V q) s = c • wavePotential K V s := by
  have he : (fun q => (-(‖K‖ ^ 2)⁻¹) • cross3 K (c • V q)) =
      fun q => c • ((-(‖K‖ ^ 2)⁻¹) • cross3 K (V q)) := by
    funext q
    change (-(‖K‖ ^ 2)⁻¹) • cross3Left K (c • V q) =
      c • ((-(‖K‖ ^ 2)⁻¹) • cross3Left K (V q))
    rw [map_smul]
    exact smul_comm _ _ _
  unfold wavePotential
  rw [he]
  simp only [phasePrimitive, phaseOscillation, intervalIntegral.integral_smul,
    phaseMean_const_smul, smul_sub]

/-- The unswitched leading curl at a fixed label and phase. Only a
spatial derivative is taken, so the unswitched profile need not extend
smoothly across the activation time. -/
def wrappedUnswitchedCompletion
    (G : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3))
    (t : ℝ) (a : Vec3) (s : ℝ) : Vec3 :=
  curlOfDerivative ((fderiv ℝ (fun b =>
    wavePotential (κ t b) (phaseTwistedPeriodizeCentered k (w.leading h) t b) s) a).comp
      (G.val.val.val (t, a, s)))

theorem twistedCompletionSwitch_eval (d : w.HierarchyRegularity r h)
    (G : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3))
    (κ₀ : HierarchyTwistedProfile T k Vec3)
    (hPhase : HierarchyPeriodicProfile.PhaseIndependent κ₀.val.val)
    (hκ₀ : ∀ t ∈ Icc 0 T, ∀ a, κ₀.val.val.val (t, a, 0) ≠ 0)
    (hκ : ∀ x ∈ hierarchyProfileSlab T, κ₀.val.val.val x = κ x.1 x.2.1)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (twistedCompletionSwitch d G κ₀ hPhase hκ₀).val.val.val (t, a, s) =
      deriv (waveSwitch t₀ r) t • wrappedUnswitchedCompletion (w := w) (h := h) G t a s := by
  let Z := twistedLeadingSwitch d k
  let Q := HierarchySmoothProfile.profileWavePotential d.end_pos κ₀.val.val hκ₀ Z.val.val
  let j := deriv (waveSwitch t₀ r) t
  change (HierarchyTwistedProfile.complete d.end_pos G κ₀ hPhase hκ₀ Z).val.val.val (t, a, s) = _
  rw [HierarchyTwistedProfile.complete_val_val_of_phaseMean_zero d.end_pos G κ₀ hPhase hκ₀ Z
    (twistedLeadingSwitch_average_zero d k)]
  change (HierarchySmoothProfile.profileSlowCurl d.end_pos G.val.val Q).val (t, a, s) = _
  rw [HierarchySmoothProfile.profileSlowCurl_apply d.end_pos G.val.val Q ht]
  let P (b : Vec3) := wavePotential (κ t b) (phaseTwistedPeriodizeCentered k (w.leading h) t b) s
  have hQ : (fun b => Q.val (t, b, s)) = j • P := by
    funext b
    rw [HierarchySmoothProfile.profileWavePotential_apply d.end_pos κ₀.val.val hκ₀ Z.val.val ht,
      hκ _ (show (t, b, (0 : ℝ)) ∈ hierarchyProfileSlab T from ⟨ht, mem_univ _⟩)]
    have hZ : (fun r => Z.val.val.val (t, b, r)) =
        fun r => j • phaseTwistedPeriodizeCentered k (w.leading h) t b r := by
      funext q
      rw [twistedLeadingSwitch_eval d k ht]
      rfl
    rw [hZ, wavePotential_time_smul]
    rfl
  rw [hQ, fderiv_const_smul_field, Pi.smul_apply, smul_comp, curlOfDerivative_smul]
  rfl

theorem twistedCompletionSwitch_before_activation (d : w.HierarchyRegularity r h)
    (G : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3))
    (κ₀ : HierarchyTwistedProfile T k Vec3)
    (hPhase : HierarchyPeriodicProfile.PhaseIndependent κ₀.val.val)
    (hκ₀ : ∀ t ∈ Icc 0 T, ∀ a, κ₀.val.val.val (t, a, 0) ≠ 0)
    (hκ : ∀ x ∈ hierarchyProfileSlab T, κ₀.val.val.val x = κ x.1 x.2.1)
    {t : ℝ} (ht : t ∈ Icc 0 T) (ht₀ : t ≤ t₀) (a : Vec3) (s : ℝ) :
    (twistedCompletionSwitch d G κ₀ hPhase hκ₀).val.val.val (t, a, s) = 0 := by
  rw [twistedCompletionSwitch_eval d G κ₀ hPhase hκ₀ hκ ht,
    deriv_waveSwitch_zero_before d.rate_nonneg ht₀, zero_smul]

/-- On the interior label cell the completion switch is `χ' C[A₁]`
with the unwrapped seed and its original coframe. -/
theorem twistedCompletionSwitch_cell_eval (d : w.HierarchyRegularity r h)
    (G : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3))
    (κ₀ : HierarchyTwistedProfile T k Vec3)
    (hPhase : HierarchyPeriodicProfile.PhaseIndependent κ₀.val.val)
    (hκ₀ : ∀ t ∈ Icc 0 T, ∀ a, κ₀.val.val.val (t, a, 0) ≠ 0)
    (hκ : ∀ x ∈ hierarchyProfileSlab T, κ₀.val.val.val x = κ x.1 x.2.1)
    {t : ℝ} (ht : t ∈ Icc 0 T) {a : Vec3} (ha : a ∈ interior centeredCell) (s : ℝ) :
    (twistedCompletionSwitch d G κ₀ hPhase hκ₀).val.val.val (t, a, s) =
      deriv (waveSwitch t₀ r) t •
        curlOfDerivative ((fderiv ℝ (fun b => wavePotential (κ t b) (w.leading h t b) s) a).comp
          (G.val.val.val (t, a, s))) := by
  rw [twistedCompletionSwitch_eval d G κ₀ hPhase hκ₀ hκ ht, wrappedUnswitchedCompletion]
  have he : (fun b => wavePotential (κ t b) (phaseTwistedPeriodizeCentered k (w.leading h) t b) s)
      =ᶠ[𝓝 a] fun b => wavePotential (κ t b) (w.leading h t b) s := by
    filter_upwards [interior_mem_nhds.mp (isOpen_interior.mem_nhds ha)] with b hb
    apply congrArg (fun f => wavePotential (κ t b) f s)
    funext q
    exact wrapped_eq_on_cell_of_radial_zero k hb q d.envelope_fits (fun v hv z => by
      simp only [SeedOn.leading, radialEnvelope_eq_zero d.envelope_pos hv, zero_mul, zero_smul])
  rw [he.fderiv_eq]

private theorem uniqueDiffOn_centeredLabelCell : UniqueDiffOn ℝ centeredCell := by
  apply uniqueDiffOn_convex
  · have heq : centeredCell = ⋂ i : Fin 3, (fun x : Vec3 => x i) ⁻¹' Icc (-(1 / 2 : ℝ)) (1 / 2) := by
      ext x
      simp [centeredCell]
    rw [heq]
    exact convex_iInter fun i => (convex_Icc _ _).linear_preimage
      (EuclideanSpace.proj (𝕜 := ℝ) i).toLinearMap
  · refine ⟨0, mem_interior_iff_mem_nhds.mpr ?_⟩
    refine mem_of_superset (Metric.ball_mem_nhds (0 : Vec3) (show 0 < 1 / 2 by norm_num)) ?_
    intro x hx i
    have hnorm : ‖x‖ < (1 : ℝ) / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact abs_le.mp ((PiLp.norm_apply_le x i).trans hnorm.le)

set_option maxHeartbeats 650000 in
/-- The evaluated completion agrees with the unwrapped curl up to the
closed cell boundary. Both derivative fields are determined by their
common restriction to that cell. -/
theorem twistedCompletionSwitch_closedCell_eval (d : w.HierarchyRegularity r h)
    (G : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3))
    (κ₀ : HierarchyTwistedProfile T k Vec3)
    (hPhase : HierarchyPeriodicProfile.PhaseIndependent κ₀.val.val)
    (hκ₀ : ∀ t ∈ Icc 0 T, ∀ a, κ₀.val.val.val (t, a, 0) ≠ 0)
    (hκ : ∀ x ∈ hierarchyProfileSlab T, κ₀.val.val.val x = κ x.1 x.2.1)
    {t : ℝ} (ht : t ∈ Icc 0 T) {a : Vec3} (ha : a ∈ centeredCell) (s : ℝ) :
    (twistedCompletionSwitch d G κ₀ hPhase hκ₀).val.val.val (t, a, s) =
      deriv (waveSwitch t₀ r) t •
        curlOfDerivative ((fderiv ℝ (fun b => wavePotential (κ t b) (w.leading h t b) s) a).comp
          (G.val.val.val (t, a, s))) := by
  let j := deriv (waveSwitch t₀ r) t
  let Z := twistedLeadingSwitch d k
  have hBare : ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint => w.leading h x.1 x.2.1 x.2.2)
      (Icc t₀ T ×ˢ univ) := by
    refine (((contDiff_radialEnvelope d.envelope_pos).comp contDiff_snd.fst).contDiffOn.smul
      (leadingBare_smooth d)).congr ?_
    intro x _
    change (radialEnvelope ell x.2.1 * waveProfile h x.2.2) • w.amplitude x.1 x.2.1 =
      radialEnvelope ell x.2.1 • (waveProfile h x.2.2 • w.amplitude x.1 x.2.1)
    exact (smul_smul _ _ _).symm
  have hRaw : ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint =>
      w.leadingSwitchProfile r h x.1 x.2.1 x.2.2) (hierarchyProfileSlab T) :=
    (contDiffOn_flatActivation_smul d.start_lt_end (contDiff_deriv_waveSwitch t₀ r)
      (fun _ ht => deriv_waveSwitch_zero_before d.rate_nonneg ht) hBare).mono
        (fun _ hx => ⟨hx.1.2, mem_univ _⟩)
  let Zraw := HierarchySmoothProfile.ofSmooth _ hRaw
  let Q := HierarchySmoothProfile.profileWavePotential d.end_pos κ₀.val.val hκ₀ Z.val.val
  let Qraw := HierarchySmoothProfile.profileWavePotential d.end_pos κ₀.val.val hκ₀ Zraw
  have hRawEval (b : Vec3) : (fun q => Zraw.val (t, b, q)) = w.leadingSwitchProfile r h t b :=
    funext fun q => HierarchySmoothProfile.ofSmooth_apply hRaw ⟨ht, mem_univ _⟩
  have he : EqOn (fun b => Q.val (t, b, s)) (fun b => Qraw.val (t, b, s)) centeredCell := by
    intro b hb
    change Q.val (t, b, s) = Qraw.val (t, b, s)
    rw [HierarchySmoothProfile.profileWavePotential_apply d.end_pos κ₀.val.val hκ₀ Z.val.val ht,
      HierarchySmoothProfile.profileWavePotential_apply d.end_pos κ₀.val.val hκ₀ Zraw ht, hRawEval b]
    exact congrArg (fun f => wavePotential (κ₀.val.val.val (t, b, 0)) f s)
      (funext (twistedLeadingSwitch_cell_eval d k ht hb))
  have hSlice (F : HierarchySmoothProfile T Vec3) : Differentiable ℝ (fun b => F.val (t, b, s)) := by
    have hIncl : ContDiff ℝ ∞ (fun b : Vec3 => (t, b, s)) :=
      contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)
    exact (contDiffOn_univ.mp ((HierarchySmoothProfile.smooth F).comp hIncl.contDiffOn
      (fun _ _ => ⟨ht, mem_univ _⟩))).differentiable (by simp)
  have ha' := uniqueDiffOn_centeredLabelCell a ha
  have hDiff : fderiv ℝ (fun b => Q.val (t, b, s)) a = fderiv ℝ (fun b => Qraw.val (t, b, s)) a := by
    rw [← fderivWithin_eq_fderiv ha' (hSlice Q a), ← fderivWithin_eq_fderiv ha' (hSlice Qraw a)]
    exact fderivWithin_congr' he ha
  have hQraw : (fun b => Qraw.val (t, b, s)) = j • (fun b => wavePotential (κ t b) (w.leading h t b) s) := by
    funext b
    rw [HierarchySmoothProfile.profileWavePotential_apply d.end_pos κ₀.val.val hκ₀ Zraw ht,
      hκ _ (show (t, b, (0 : ℝ)) ∈ hierarchyProfileSlab T from ⟨ht, mem_univ _⟩), hRawEval b]
    exact wavePotential_time_smul _ _ _ _
  rw [twistedCompletionSwitch, HierarchyTwistedProfile.complete_val_val_of_phaseMean_zero
      d.end_pos G κ₀ hPhase hκ₀ Z (twistedLeadingSwitch_average_zero d k)]
  change (HierarchySmoothProfile.profileSlowCurl d.end_pos G.val.val Q).val (t, a, s) = _
  rw [HierarchySmoothProfile.profileSlowCurl_apply d.end_pos G.val.val Q ht, hDiff, hQraw,
    fderiv_const_smul_field, Pi.smul_apply, smul_comp, curlOfDerivative_smul]

private theorem reflect_of_onSlab {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : HierarchyTwistedProfile T k E} {sign : ℝ}
    (hf : ∀ x ∈ hierarchyProfileSlab T,
      f.val.val.val (hierarchyProfileReflection x) = sign • f.val.val.val x) :
    HierarchyProfileReflectionParity sign f.val.val.val := by
  intro x
  by_cases hx : x ∈ hierarchyProfileSlab T
  · exact hf x hx
  · rw [HierarchySmoothProfile.eq_zero_outside f.val.val
      (fun h => hx (hierarchyProfileReflection_mem_slab.mp h)),
      HierarchySmoothProfile.eq_zero_outside f.val.val hx, smul_zero]

private theorem leadingPressurePrimitive_even (d : w.HierarchyRegularity r h) :
    Function.Even (wavePressurePrimitive h) := by
  intro s
  have he : (∫ q in (0 : ℝ)..(-s), waveProfile h q) = ∫ q in (0 : ℝ)..s, waveProfile h q := by
    have hOdd : (fun q => waveProfile h (-q)) = fun q => -waveProfile h q :=
      funext (odd_waveProfile d.phase_pos d.phase_le_one)
    have ht := intervalIntegral.integral_comp_neg (f := waveProfile h) (a := (0 : ℝ)) (b := s)
    rw [hOdd, intervalIntegral.integral_neg, neg_zero] at ht
    calc
      _ = -(∫ q in (-s)..(0 : ℝ), waveProfile h q) := intervalIntegral.integral_symm (-s) 0
      _ = _ := by rw [← ht, neg_neg]
  simp only [wavePressurePrimitive, phasePrimitive, phaseOscillation, he]

theorem twistedLeading_reflectionOdd (d : w.HierarchyRegularity r h) (k : Vec3)
    (hEven : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t)) :
    HierarchyProfileReflectionParity (-1) (twistedLeading d k).val.val.val := by
  apply reflect_of_onSlab
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  simp only [hierarchyProfileReflection_apply, twistedLeading_eval d k ht, neg_one_smul]
  exact (w.twistedSwitchedLeading_agreement_and_reflection k d.rate_nonneg d.envelope_pos
    d.envelope_fits d.phase_pos d.phase_le_one hEven).2 t ht.2 a s

theorem twistedPressure_reflectionEven (d : w.HierarchyRegularity r h) (k : Vec3)
    (hEven : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t))
    (hM : ∀ t ∈ Icc t₀ T, Function.Even (M t))
    (hκ : ∀ t ∈ Icc t₀ T, Function.Even (κ t)) :
    HierarchyProfileReflectionParity 1 (twistedPressure d k).val.val.val := by
  apply reflect_of_onSlab
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  simp only [hierarchyProfileReflection_apply, twistedPressure_eval d k ht, one_smul]
  apply phaseTwistedPeriodizeCentered_neg_equivariant (L := id) rfl _ _ a s
  · intro b q
    by_cases he : t ≤ t₀
    · simp only [SeedOn.switchedPressure, waveSwitch_eq_zero_of_le d.rate_nonneg he,
        zero_mul, id_eq]
    · have ha : t ∈ Icc t₀ T := ⟨le_of_not_ge he, ht.2⟩
      simp only [SeedOn.switchedPressure, SeedOn.leadingPressure, radialEnvelope_neg,
        hκ t ha b, hEven t ha b, hM t ha b, leadingPressurePrimitive_even d q, id_eq]
  · intro b hb q
    obtain ⟨i, hi⟩ := hb
    have hb' : |b i| ≤ ‖b‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le b i
    rw [hi, abs_neg, abs_of_nonneg (by norm_num)] at hb'
    simp only [SeedOn.switchedPressure, leadingPressure_eq_envelope,
      radialEnvelope_eq_zero d.envelope_pos (d.envelope_fits.le.trans hb'), zero_mul, mul_zero]

theorem twistedLeadingSwitch_reflectionOdd (d : w.HierarchyRegularity r h) (k : Vec3)
    (hEven : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t)) :
    HierarchyProfileReflectionParity (-1) (twistedLeadingSwitch d k).val.val.val := by
  apply reflect_of_onSlab
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  simp only [hierarchyProfileReflection_apply, twistedLeadingSwitch_eval d k ht, neg_one_smul]
  apply phaseTwistedPeriodizeCentered_neg_equivariant (L := Neg.neg) (neg_zero) _ _ a s
  · intro b q
    by_cases he : t ≤ t₀
    · simp only [leadingSwitchProfile, deriv_waveSwitch_zero_before d.rate_nonneg he, zero_smul, neg_zero]
    · have ha : t ∈ Icc t₀ T := ⟨le_of_not_ge he, ht.2⟩
      simp only [leadingSwitchProfile, SeedOn.leading, radialEnvelope_neg,
        odd_waveProfile d.phase_pos d.phase_le_one q, hEven t ha b, mul_neg, neg_smul, smul_neg]
  · intro b hb q
    obtain ⟨i, hi⟩ := hb
    have hb' : |b i| ≤ ‖b‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le b i
    rw [hi, abs_neg, abs_of_nonneg (by norm_num)] at hb'
    simp only [leadingSwitchProfile, SeedOn.leading,
      radialEnvelope_eq_zero d.envelope_pos (d.envelope_fits.le.trans hb'), zero_mul, zero_smul, smul_zero]

theorem twistedCompletionSwitch_reflectionOdd (d : w.HierarchyRegularity r h)
    (G : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3))
    (κ₀ : HierarchyTwistedProfile T k Vec3)
    (hPhase : HierarchyPeriodicProfile.PhaseIndependent κ₀.val.val)
    (hκ₀ : ∀ t ∈ Icc 0 T, ∀ a, κ₀.val.val.val (t, a, 0) ≠ 0)
    (hGeven : HierarchyProfileReflectionParity 1 G.val.val.val)
    (hκeven : HierarchyProfileReflectionParity 1 κ₀.val.val.val)
    (hEven : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t)) :
    HierarchyProfileReflectionParity (-1) (twistedCompletionSwitch d G κ₀ hPhase hκ₀).val.val.val :=
  HierarchyTwistedProfile.complete_reflectionOdd_of_phaseMean_zero d.end_pos G κ₀ hPhase hκ₀
    (twistedLeadingSwitch d k) hGeven hκeven (twistedLeadingSwitch_reflectionOdd d k hEven)
    (twistedLeadingSwitch_average_zero d k)

/-- The parent flow supplies all regularity and joint-reflection data for the
later-wave leading velocity, pressure, and velocity switch. -/
theorem hierarchyRegularity_of_parent
    {U : Velocity} {X : ℝ → Velocity} {center : ℝ → Vec3} {k : Vec3}
    {t₀ T ell D C r h : ℝ} (ht₀ : 0 ≤ t₀) (ht₀T : t₀ < T)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (hodd : ∀ t ∈ Icc 0 T, Function.Odd (U t)) (hk : k ≠ 0)
    (w : SeedOn (fun t a => fderiv ℝ (U t) (X 0 t a))
      (fun t a => labelWaveVector X 0 a k t) center t₀ T ell D C)
    (hr : 0 ≤ r) (hEll : 0 < ell) (hfit : 2 * ell < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) :
    w.HierarchyRegularity r h ∧
      (∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t)) ∧
      (∀ t ∈ Icc t₀ T, Function.Even (fun a => fderiv ℝ (U t) (X 0 t a))) ∧
      (∀ t ∈ Icc t₀ T, Function.Even (fun a => labelWaveVector X 0 a k t)) := by
  obtain ⟨hSmooth, hEven⟩ := SeedOn.regularity_of_parent ht₀ ht₀T hX hU hper hodd hk w
  have hT : 0 < T := ht₀.trans_lt ht₀T
  have hsub : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc_left ht₀
  have hsubS : (Icc t₀ T ×ˢ (univ : Set Vec3)) ⊆ Icc 0 T ×ˢ univ :=
    fun _ hx => ⟨hsub hx.1, hx.2⟩
  have hM := (hX.contDiffOn_materialGradient hT hU hper).mono hsubS
  have hK := (hX.contDiffOn_transportedCovector hT hU hper k).mono hsubS
  have hU₁ : ContDiffOn ℝ 1 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hU.of_le (by simp)
  obtain ⟨L, hL⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT hU₁ hper
  have hParity (t : ℝ) (ht : t ∈ Icc t₀ T) := hX.even_materialGradient_and_labelWaveVector hL hodd
    (left_mem_Icc.mpr hT.le) (hsub ht) k
  exact ⟨⟨ht₀, ht₀T, hr, hEll, hfit, hh, hh₁, hM, hK,
    fun t ht => transportedCovector_ne_zero_of_parent hT hX hU hper hk t (hsub ht), hSmooth⟩,
    hEven, fun t ht => (hParity t ht).1, fun t ht => (hParity t ht).2⟩

/-- Both switch sources and the leading pair vanish on the support region
required by the finite hierarchy, for any closed set containing the
support of the wrapped envelope. -/
theorem twistedLeading_inactive (d : w.HierarchyRegularity r h)
    (G : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3))
    (κ₀ : HierarchyTwistedProfile T k Vec3)
    (hPhase : HierarchyPeriodicProfile.PhaseIndependent κ₀.val.val)
    (hκ₀ : ∀ t ∈ Icc 0 T, ∀ a, κ₀.val.val.val (t, a, 0) ≠ 0)
    {S : Set Vec3} (hS : IsClosed S) (henv : Function.support (periodizeCentered (radialEnvelope ell)) ⊆ S) :
    let I := hierarchyInactiveRegion T t₀ S
    EqOn (twistedLeading d k).val.val.val 0 I ∧
      EqOn (twistedPressure d k).val.val.val 0 I ∧
      EqOn (twistedLeadingSwitch d k).val.val.val 0 I ∧
      EqOn (twistedCompletionSwitch d G κ₀ hPhase hκ₀).val.val.val 0 I := by
  let I := hierarchyInactiveRegion T t₀ S
  have hLeading {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ)
      (ha : t < t₀ ∨ a ∉ S) :
      (twistedLeading d k).val.val.val (t, a, s) = 0 ∧
      (twistedPressure d k).val.val.val (t, a, s) = 0 ∧
      (twistedLeadingSwitch d k).val.val.val (t, a, s) = 0 := by
    rcases ha with hpre | hout
    · exact ⟨twistedLeading_before_activation d k ht hpre.le a s,
        twistedPressure_before_activation d k ht hpre.le a s,
        twistedLeadingSwitch_before_activation d k ht hpre.le a s⟩
    · have hz : radialEnvelope ell (centeredLabel a) = 0 :=
        Function.notMem_support.mp fun hv => hout (henv hv)
      rw [twistedLeading_eval d k ht, twistedPressure_eval d k ht, twistedLeadingSwitch_eval d k ht]
      simp only [phaseTwistedPeriodizeCentered, SeedOn.switchedLeading, SeedOn.switchedPressure,
        SeedOn.leading, leadingPressure_eq_envelope, leadingSwitchProfile, hz, zero_mul, mul_zero,
        zero_smul, smul_zero, and_self]
  have hZ : EqOn (twistedLeadingSwitch d k).val.val.val 0 I := by
    rintro ⟨t, a, s⟩ hx
    exact (hLeading hx.1.1 a s hx.2).2.2
  refine ⟨?_, ?_, hZ, ?_⟩
  · rintro ⟨t, a, s⟩ hx
    exact (hLeading hx.1.1 a s hx.2).1
  · rintro ⟨t, a, s⟩ hx
    exact (hLeading hx.1.1 a s hx.2).2.1
  · rw [twistedCompletionSwitch, HierarchyTwistedProfile.complete_val_val_of_phaseMean_zero
      d.end_pos G κ₀ hPhase hκ₀ (twistedLeadingSwitch d k) (twistedLeadingSwitch_average_zero d k)]
    exact HierarchySmoothProfile.profileCompletion_eq_zero_on_inactive d.end_pos hS
      G.val.val κ₀.val.val (twistedLeadingSwitch d k).val.val hκ₀ hZ

end LocalizedAmplitude.SeedOn

end
end TorusEuler
