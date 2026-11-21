import TorusEuler.HierarchyPhysicalApproximation
import TorusEuler.HierarchySelectedLinearEstimates
import TorusEuler.LaterWaveHierarchyInput
import TorusEuler.PaperHierarchyLeadingEquation
import TorusEuler.TerminalSeeleyExtension

/-! The leading wave and its activation residual with the cutoff of §3. -/

open ContinuousLinearMap Filter Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

set_option maxHeartbeats 900000

noncomputable section

/-- A smooth cutoff on the closed time slab, including the unswitched first wave. -/
structure PaperWaveCutoff (t₀ T : ℝ) where
  value : ℝ → ℝ
  smooth : ContDiffOn ℝ ∞ value (Icc 0 T)
  range : ∀ t ∈ Icc 0 T, 0 ≤ value t ∧ value t ≤ 1
  zero_before : ∀ t ∈ Icc 0 T, t < t₀ → value t = 0

namespace PaperWaveCutoff

variable {t₀ T : ℝ}

/-- At the initial time the first wave uses the constant cutoff. -/
def first (T : ℝ) : PaperWaveCutoff 0 T where
  value := fun _ => 1
  smooth := contDiffOn_const
  range := fun _ _ => ⟨zero_le_one, le_rfl⟩
  zero_before := fun _ ht h => (not_lt_of_ge ht.1 h).elim

/-- The cutoff derivative on the same closed slab as the Euler equation. -/
def derivative (χ : PaperWaveCutoff t₀ T) : ℝ → ℝ :=
  derivWithin χ.value (Icc 0 T)

theorem abs_le_one (χ : PaperWaveCutoff t₀ T) {t : ℝ} (ht : t ∈ Icc 0 T) : |χ.value t| ≤ 1 := by
  rw [abs_of_nonneg (χ.range t ht).1]
  exact (χ.range t ht).2

theorem derivative_first (T : ℝ) (t : ℝ) : (first T).derivative t = 0 := by
  change derivWithin (Function.const ℝ (1 : ℝ)) (Icc 0 T) t = 0
  rw [derivWithin_const]
  rfl

theorem derivative_smooth (χ : PaperWaveCutoff t₀ T) (hT : 0 < T) :
    ContDiffOn ℝ ∞ χ.derivative (Icc 0 T) :=
  χ.smooth.derivWithin (uniqueDiffOn_Icc hT) (by simp)

private theorem hasDerivWithinAt_eq_zero_before
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hzero : ∀ u ∈ Icc 0 T, u < t₀ → f u = 0) {t : ℝ}
    (ht : t ∈ Icc 0 T) (hpre : t < t₀) : HasDerivWithinAt f 0 (Icc 0 T) t := by
  apply (hasDerivWithinAt_inter (Iio_mem_nhds hpre)).mp
  exact (hasDerivWithinAt_const t (Icc 0 T ∩ Iio t₀) (0 : E)).congr
    (fun _ hu => hzero _ hu.1 hu.2) (hzero _ ht hpre)

theorem derivative_zero_before (χ : PaperWaveCutoff t₀ T) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (hpre : t < t₀) : χ.derivative t = 0 :=
  (hasDerivWithinAt_eq_zero_before χ.zero_before ht hpre).derivWithin (uniqueDiffOn_Icc hT t ht)

theorem hasDerivWithinAt (χ : PaperWaveCutoff t₀ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt χ.value (χ.derivative t) (Icc 0 T) t :=
  ((χ.smooth.differentiableOn (by simp)) t ht).hasDerivWithinAt

end PaperWaveCutoff

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
  {w : SeedOn M κ center t₀ T ell D C}

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


/-- A smooth active multiplier times a smooth active profile is jointly smooth on
the complete slab. The extension is used only to verify regularity. -/
private theorem contDiffOn_slab_multiplier {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {c : ℝ → ℝ} {f : HierarchyProfilePoint → E}
    (hEnd : t₀ < T) (hc : ContDiffOn ℝ ∞ c (Icc 0 T))
    (hzero : ∀ t ∈ Icc 0 T, t < t₀ → c t = 0)
    (hf : ContDiffOn ℝ ∞ f (Icc t₀ T ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint => c x.1 • f x) (hierarchyProfileSlab T) := by
  obtain ⟨g, hg, hAgree⟩ := exists_smoothExtensionOfClosedTimeSlab hEnd isOpen_univ hf
  have hC : ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint => c x.1) (hierarchyProfileSlab T) :=
    hc.comp contDiff_fst.contDiffOn (fun _ hx => hx.1)
  refine (hC.smul (hg.mono fun _ _ => ⟨mem_univ _, mem_univ _⟩)).congr ?_
  intro x hx
  change c x.1 • f x = c x.1 • g x
  by_cases hpre : x.1 < t₀
  · rw [hzero _ hx.1 hpre, zero_smul, zero_smul]
  · rw [hAgree (show x ∈ Icc t₀ T ×ˢ univ from ⟨⟨le_of_not_gt hpre, hx.1.2⟩, mem_univ _⟩)]

private theorem contDiffOn_waves_raw (reg : w.HierarchyRegularity r h) {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ ∞ c (Icc 0 T)) (hzero : ∀ t ∈ Icc 0 T, t < t₀ → c t = 0) :
    ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint =>
      c x.1 • w.leading h x.1 x.2.1 x.2.2) (hierarchyProfileSlab T) := by
  exact contDiffOn_slab_multiplier reg.start_lt_end hc hzero
    (w.contDiffOn_leading reg.envelope_pos reg.phase_pos reg.phase_le_one reg.amplitude_smooth)

private def velocityMultiple (reg : w.HierarchyRegularity r h) (k : Vec3) (c : ℝ → ℝ)
    (hc : ContDiffOn ℝ ∞ c (Icc 0 T)) (hzero : ∀ t ∈ Icc 0 T, t < t₀ → c t = 0) :
    HierarchyTwistedProfile T k Vec3 :=
  HierarchyTwistedProfile.wrapOnSlab
    (f := fun t a s => c t • w.leading h t a s)
    (by
      simpa only [SeedOn.leading, smul_smul, mul_left_comm, hierarchyProfileSlab] using
        contDiffOn_phaseTwistedPeriodizeCentered_radialEnvelope (k := k)
          (f := fun t a s => c t • (waveProfile h s • w.amplitude t a)) (I := Icc 0 T)
          reg.envelope_pos reg.envelope_fits
          (contDiffOn_slab_multiplier reg.start_lt_end hc hzero (leadingBare_smooth reg)))
    (fun _ _ s => by simp only [SeedOn.leading, periodic_waveProfile reg.phase_pos reg.phase_le_one s])

private def pressureMultiple (reg : w.HierarchyRegularity r h) (k : Vec3) (c : ℝ → ℝ)
    (hc : ContDiffOn ℝ ∞ c (Icc 0 T)) (hzero : ∀ t ∈ Icc 0 T, t < t₀ → c t = 0) :
    HierarchyTwistedProfile T k ℝ :=
  HierarchyTwistedProfile.wrapOnSlab
    (f := fun t a s => c t * w.leadingPressure h t a s)
    (by
      simpa only [leadingPressure_eq_envelope, smul_eq_mul, mul_left_comm, hierarchyProfileSlab] using
        contDiffOn_phaseTwistedPeriodizeCentered_radialEnvelope (k := k)
          (f := fun t a s => c t • w.barePressure h t a s) (I := Icc 0 T)
          reg.envelope_pos reg.envelope_fits
          (contDiffOn_slab_multiplier reg.start_lt_end hc hzero (barePressure_smooth reg)))
    (fun _ _ s => by
      simp only [SeedOn.leadingPressure, periodic_wavePressurePrimitive reg.phase_pos reg.phase_le_one s])

/-- The leading velocity `χ A₁`, wrapped in the parent label cell. -/
def genericLeading (reg : w.HierarchyRegularity r h) (k : Vec3) (χ : PaperWaveCutoff t₀ T) :
    HierarchyTwistedProfile T k Vec3 :=
  velocityMultiple reg k χ.value χ.smooth χ.zero_before

/-- The normalized leading phase pressure `χ p[A₁]`. -/
def genericPressure (reg : w.HierarchyRegularity r h) (k : Vec3) (χ : PaperWaveCutoff t₀ T) :
    HierarchyTwistedProfile T k ℝ :=
  pressureMultiple reg k χ.value χ.smooth χ.zero_before

/-- The leading part of the switch residual `χ' A₁`. -/
def genericLeadingSwitch (reg : w.HierarchyRegularity r h) (k : Vec3)
    (χ : PaperWaveCutoff t₀ T) : HierarchyTwistedProfile T k Vec3 :=
  velocityMultiple reg k χ.derivative (χ.derivative_smooth reg.end_pos)
    (fun _ ht hpre => χ.derivative_zero_before reg.end_pos ht hpre)

private theorem velocityMultiple_eval (reg : w.HierarchyRegularity r h) (k : Vec3) {c : ℝ → ℝ}
    {hc : ContDiffOn ℝ ∞ c (Icc 0 T)} {hzero : ∀ t ∈ Icc 0 T, t < t₀ → c t = 0}
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (velocityMultiple reg k c hc hzero).val.val.val (t, a, s) =
      c t • phaseTwistedPeriodizeCentered k (w.leading h) t a s :=
  HierarchyTwistedProfile.wrapOnSlab_eval _ _ ht a s

private theorem pressureMultiple_eval (reg : w.HierarchyRegularity r h) (k : Vec3) {c : ℝ → ℝ}
    {hc : ContDiffOn ℝ ∞ c (Icc 0 T)} {hzero : ∀ t ∈ Icc 0 T, t < t₀ → c t = 0}
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (pressureMultiple reg k c hc hzero).val.val.val (t, a, s) =
      c t * phaseTwistedPeriodizeCentered k (w.leadingPressure h) t a s :=
  HierarchyTwistedProfile.wrapOnSlab_eval _ _ ht a s

theorem genericLeading_eval (reg : w.HierarchyRegularity r h) (k : Vec3)
    (χ : PaperWaveCutoff t₀ T) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (genericLeading reg k χ).val.val.val (t, a, s) =
      χ.value t • phaseTwistedPeriodizeCentered k (w.leading h) t a s :=
  velocityMultiple_eval reg k ht a s

theorem genericPressure_eval (reg : w.HierarchyRegularity r h) (k : Vec3)
    (χ : PaperWaveCutoff t₀ T) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (genericPressure reg k χ).val.val.val (t, a, s) =
      χ.value t * phaseTwistedPeriodizeCentered k (w.leadingPressure h) t a s :=
  pressureMultiple_eval reg k ht a s

theorem genericLeadingSwitch_eval (reg : w.HierarchyRegularity r h) (k : Vec3)
    (χ : PaperWaveCutoff t₀ T) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (genericLeadingSwitch reg k χ).val.val.val (t, a, s) =
      χ.derivative t • phaseTwistedPeriodizeCentered k (w.leading h) t a s :=
  velocityMultiple_eval reg k ht a s

private theorem wrapped_eq_on_cell_of_radial_zero {E : Type*} [Zero E]
    {ell : ℝ} {f : ℝ → Vec3 → ℝ → E} (k : Vec3) {t : ℝ} {a : Vec3}
    (ha : a ∈ centeredCell) (s : ℝ) (hfit : 2 * ell < 1 / 2)
    (hzero : ∀ b, 2 * ell ≤ ‖b‖ → ∀ q, f t b q = 0) :
    phaseTwistedPeriodizeCentered k f t a s = f t a s := by
  refine phaseTwistedPeriodizeCentered_eq_on_centeredCell (sub_pos.mpr hfit) ?_ ha s
  intro b hb q
  obtain ⟨i, hi⟩ := hb
  have hbi : |b i| ≤ ‖b‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le b i
  exact hzero b (by linarith) q

private theorem leading_zero_outside (reg : w.HierarchyRegularity r h)
    (t : ℝ) {a : Vec3} (ha : 2 * ell ≤ ‖a‖) (s : ℝ) : w.leading h t a s = 0 := by
  simp only [SeedOn.leading, radialEnvelope_eq_zero reg.envelope_pos ha, zero_mul, zero_smul]

private theorem pressure_zero_outside (reg : w.HierarchyRegularity r h)
    (t : ℝ) {a : Vec3} (ha : 2 * ell ≤ ‖a‖) (s : ℝ) : w.leadingPressure h t a s = 0 := by
  simp only [leadingPressure_eq_envelope, radialEnvelope_eq_zero reg.envelope_pos ha, zero_mul]

theorem genericLeading_cell_eval (reg : w.HierarchyRegularity r h) (k : Vec3)
    (χ : PaperWaveCutoff t₀ T) {t : ℝ} (ht : t ∈ Icc 0 T) {a : Vec3}
    (ha : a ∈ centeredCell) (s : ℝ) :
    (genericLeading reg k χ).val.val.val (t, a, s) = χ.value t • w.leading h t a s := by
  rw [genericLeading_eval reg k χ ht, wrapped_eq_on_cell_of_radial_zero k ha s reg.envelope_fits
    (fun _ hz q => leading_zero_outside reg t hz q)]

theorem genericPressure_cell_eval (reg : w.HierarchyRegularity r h) (k : Vec3)
    (χ : PaperWaveCutoff t₀ T) {t : ℝ} (ht : t ∈ Icc 0 T) {a : Vec3}
    (ha : a ∈ centeredCell) (s : ℝ) :
    (genericPressure reg k χ).val.val.val (t, a, s) = χ.value t * w.leadingPressure h t a s := by
  rw [genericPressure_eval reg k χ ht, wrapped_eq_on_cell_of_radial_zero k ha s reg.envelope_fits
    (fun _ hz q => pressure_zero_outside reg t hz q)]

theorem genericLeadingSwitch_cell_eval (reg : w.HierarchyRegularity r h) (k : Vec3)
    (χ : PaperWaveCutoff t₀ T) {t : ℝ} (ht : t ∈ Icc 0 T) {a : Vec3}
    (ha : a ∈ centeredCell) (s : ℝ) :
    (genericLeadingSwitch reg k χ).val.val.val (t, a, s) = χ.derivative t • w.leading h t a s := by
  rw [genericLeadingSwitch_eval reg k χ ht, wrapped_eq_on_cell_of_radial_zero k ha s reg.envelope_fits
    (fun _ hz q => leading_zero_outside reg t hz q)]

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

variable {k : Vec3}

private theorem velocityMultiple_average_zero (reg : w.HierarchyRegularity r h)
    {c : ℝ → ℝ} (hc : ContDiffOn ℝ ∞ c (Icc 0 T))
    (hzero : ∀ t ∈ Icc 0 T, t < t₀ → c t = 0) :
    HierarchyTwistedProfile.profilePhaseAverage reg.end_pos (velocityMultiple reg k c hc hzero) = 0 := by
  apply HierarchyTwistedProfile.ext
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  change (HierarchySmoothProfile.profilePhaseAverage reg.end_pos
    (velocityMultiple reg k c hc hzero).val.val).val (t, a, s) = 0
  rw [HierarchySmoothProfile.profilePhaseAverage_apply _ _ hx]
  simp_rw [velocityMultiple_eval reg k ht, phaseMean_const_smul]
  by_cases hpre : t < t₀
  · rw [hzero _ ht hpre, zero_smul]
  · have hact : t ∈ Icc t₀ T := ⟨le_of_not_gt hpre, ht.2⟩
    rw [phaseMean_wrapped_shift k a ?_ ?_, smul_zero]
    · intro b q
      simp only [SeedOn.leading, periodic_waveProfile reg.phase_pos reg.phase_le_one q]
    · intro b
      exact (w.paper_hierarchy_leading_homogeneous reg.start_lt_end reg.phase_pos reg.phase_le_one
        hact b 0).2.2.1

theorem genericLeadingSwitch_average_zero (reg : w.HierarchyRegularity r h)
    (χ : PaperWaveCutoff t₀ T) :
    HierarchyTwistedProfile.profilePhaseAverage reg.end_pos (genericLeadingSwitch reg k χ) = 0 :=
  velocityMultiple_average_zero reg (χ.derivative_smooth reg.end_pos)
    (fun _ ht hpre => χ.derivative_zero_before reg.end_pos ht hpre)

/-- The normalized pressure has zero phase average with the arbitrary cutoff. -/
theorem genericPressure_phaseMean_zero (reg : w.HierarchyRegularity r h)
    (χ : PaperWaveCutoff t₀ T) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) :
    phaseMean (fun s => (genericPressure reg k χ).val.val.val (t, a, s)) = 0 := by
  simp_rw [genericPressure_eval reg k χ ht]
  change phaseMean (fun s => χ.value t • phaseTwistedPeriodizeCentered k (w.leadingPressure h) t a s) = 0
  rw [phaseMean_const_smul]
  by_cases hpre : t < t₀
  · rw [χ.zero_before _ ht hpre, zero_smul]
  · have hact : t ∈ Icc t₀ T := ⟨le_of_not_gt hpre, ht.2⟩
    rw [phaseMean_wrapped_shift k a ?_ ?_, smul_zero]
    · intro b q
      simp only [SeedOn.leadingPressure, periodic_wavePressurePrimitive reg.phase_pos reg.phase_le_one q]
    · intro b
      exact (w.paper_hierarchy_leading_homogeneous reg.start_lt_end reg.phase_pos reg.phase_le_one
        hact b 0).2.2.2

private theorem velocityMultiple_transverse (reg : w.HierarchyRegularity r h)
    (κ₀ : HierarchyTwistedProfile T k Vec3)
    (hκ : ∀ x ∈ hierarchyProfileSlab T, κ₀.val.val.val x = κ x.1 x.2.1)
    {c : ℝ → ℝ} (hc : ContDiffOn ℝ ∞ c (Icc 0 T))
    (hzero : ∀ t ∈ Icc 0 T, t < t₀ → c t = 0) :
    ∀ x ∈ hierarchyProfileSlab T,
      ⟪κ₀.val.val.val x, (velocityMultiple reg k c hc hzero).val.val.val x⟫_ℝ = 0 := by
  refine HierarchyTwistedProfile.all_on_centeredCell (k := k) (T := T)
    (Q := fun x => ⟪κ₀.val.val.val x, (velocityMultiple reg k c hc hzero).val.val.val x⟫_ℝ = 0) ?_ ?_
  · intro t a s n hz
    simpa only [HierarchyTwistedProfile.twistedSlice] using hz
  · intro t ht a ha s
    rw [hκ _ ⟨ht, mem_univ _⟩, velocityMultiple_eval reg k ht, wrapped_eq_on_cell_of_radial_zero k ha s
      reg.envelope_fits (fun _ hz q => leading_zero_outside reg t hz q)]
    by_cases hpre : t < t₀
    · rw [hzero _ ht hpre, zero_smul, inner_zero_right]
    · have hact : t ∈ Icc t₀ T := ⟨le_of_not_gt hpre, ht.2⟩
      rw [real_inner_smul_right, (w.paper_hierarchy_leading_homogeneous reg.start_lt_end
        reg.phase_pos reg.phase_le_one hact a s).2.1, mul_zero]

theorem genericLeadingSwitch_transverse (reg : w.HierarchyRegularity r h)
    (χ : PaperWaveCutoff t₀ T) (κ₀ : HierarchyTwistedProfile T k Vec3)
    (hκ : ∀ x ∈ hierarchyProfileSlab T, κ₀.val.val.val x = κ x.1 x.2.1) :
    ∀ x ∈ hierarchyProfileSlab T, ⟪κ₀.val.val.val x, (genericLeadingSwitch reg k χ).val.val.val x⟫_ℝ = 0 :=
  velocityMultiple_transverse reg κ₀ hκ (χ.derivative_smooth reg.end_pos)
    (fun _ ht hpre => χ.derivative_zero_before reg.end_pos ht hpre)

/-- The leading pair belongs to the transverse profile space of the parent. -/
def genericLeadingOutput (reg : w.HierarchyRegularity r h) (χ : PaperWaveCutoff t₀ T)
    (G M₀ : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3))
    (κ₀ : HierarchyTwistedProfile T k Vec3)
    (hκ : ∀ x ∈ hierarchyProfileSlab T, κ₀.val.val.val x = κ x.1 x.2.1) :
    HierarchyTransverseOutput (HierarchyTwistedProfile.twistedHierarchyOperators reg.end_pos G M₀ κ₀) where
  V := genericLeading reg k χ
  p := genericPressure reg k χ
  average_V := velocityMultiple_average_zero reg χ.smooth χ.zero_before
  phaseAdv_V := fun v =>
    HierarchyTwistedProfile.phaseAdv_eq_zero_of_transverse reg.end_pos G M₀ κ₀
      (genericLeading reg k χ) v (velocityMultiple_transverse reg κ₀ hκ χ.smooth χ.zero_before)

private theorem raw_momentum (reg : w.HierarchyRegularity r h) (χ : PaperWaveCutoff t₀ T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    derivWithin (fun u => χ.value u • w.leading h u a s) (Icc 0 T) t +
      M t a (χ.value t • w.leading h t a s) +
        deriv (fun q => χ.value t * w.leadingPressure h t a q) s • κ t a =
      χ.derivative t • w.leading h t a s := by
  have hp : deriv (fun q => χ.value t * w.leadingPressure h t a q) s =
      χ.value t * deriv (w.leadingPressure h t a) s := by
    have hpd := ((hasDerivAt_wavePressurePrimitive reg.phase_pos reg.phase_le_one s).const_mul
      (-wavePressureCoefficient (radialEnvelope ell a) (κ t a) (w.amplitude t a) (M t a)))
    exact (hpd.const_mul (χ.value t)).deriv.trans (congrArg _ hpd.deriv.symm)
  rw [hp]
  by_cases hpre : t < t₀
  · have hD := PaperWaveCutoff.hasDerivWithinAt_eq_zero_before
      (f := fun u => χ.value u • w.leading h u a s)
      (fun u hu hv => by rw [χ.zero_before u hu hv, zero_smul]) ht hpre
    rw [hD.derivWithin (uniqueDiffOn_Icc reg.end_pos t ht), χ.zero_before _ ht hpre,
      χ.derivative_zero_before reg.end_pos ht hpre, zero_smul, map_zero, zero_mul,
      zero_smul, add_zero, add_zero]
  · have hact : t ∈ Icc t₀ T := ⟨le_of_not_gt hpre, ht.2⟩
    have hsub := Icc_subset_Icc_left reg.nonneg_start (b := T)
    have hD := ((χ.hasDerivWithinAt ht).mono hsub).smul
      (w.hasDerivWithinAt_leading_homogeneous_momentum reg.phase_pos reg.phase_le_one hact a s)
    have hIncl : ContDiff ℝ ∞ (fun u : ℝ => (u, a, s)) := contDiff_id.prodMk contDiff_const
    have hMaps : MapsTo (fun u : ℝ => (u, a, s)) (Icc 0 T) (hierarchyProfileSlab T) :=
      fun _ hu => ⟨hu, mem_univ _⟩
    have hslice : ContDiffOn ℝ ∞ (fun u => χ.value u • w.leading h u a s) (Icc 0 T) :=
      (contDiffOn_waves_raw reg χ.smooth χ.zero_before).comp hIncl.contDiffOn hMaps
    have hFull := ((hslice.differentiableOn (by simp)) t ht).hasDerivWithinAt
    have hEq := ((hFull.mono hsub).derivWithin (uniqueDiffOn_Icc reg.start_lt_end t hact)).symm.trans
      (hD.derivWithin (uniqueDiffOn_Icc reg.start_lt_end t hact))
    rw [hEq]
    simp only [map_smul, smul_sub, smul_neg, smul_smul]
    abel

set_option maxHeartbeats 750000 in
/-- The concrete leading momentum has exactly the flat activation
source on the entire twisted profile space. The raw equation is
checked on the closed label cell and translated by the skew shift. -/
theorem genericLeadingOutput_momentum (d : w.HierarchyRegularity r h) (χ : PaperWaveCutoff t₀ T)
    (G M₀ : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3))
    (κ₀ : HierarchyTwistedProfile T k Vec3)
    (hM : ∀ x ∈ hierarchyProfileSlab T, M₀.val.val.val x = M x.1 x.2.1)
    (hκ : ∀ x ∈ hierarchyProfileSlab T, κ₀.val.val.val x = κ x.1 x.2.1) :
    let O := HierarchyTwistedProfile.twistedHierarchyOperators d.end_pos G M₀ κ₀
    let o := genericLeadingOutput d χ G M₀ κ₀ hκ
    O.material o.V + O.phaseGrad o.p = genericLeadingSwitch d k χ := by
  let O := HierarchyTwistedProfile.twistedHierarchyOperators d.end_pos G M₀ κ₀
  let V := genericLeading d k χ
  let p := genericPressure d k χ
  change O.material V + O.phaseGrad p = _
  apply HierarchyTwistedProfile.eq_of_centeredCell
  intro t ht a ha s
  have hz : (t, a, s) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have htD := HierarchySmoothProfile.hasDerivWithinAt_profileTime V.val.val ht a s
  have hD := htD.congr (fun u hu => (genericLeading_cell_eval d k χ hu ha s).symm)
    (genericLeading_cell_eval d k χ ht ha s).symm
  have hv := (hD.derivWithin (uniqueDiffOn_Icc d.end_pos t ht)).symm
  have hqp := (HierarchySmoothProfile.hasDerivAt_profilePhase p.val.val ht a s).deriv.symm
  have hpFun : (fun q => p.val.val.val (t, a, q)) = (fun q => χ.value t * w.leadingPressure h t a q) :=
    funext (genericPressure_cell_eval d k χ ht ha)
  rw [hpFun] at hqp
  let O₀ := HierarchySmoothProfile.hierarchyConcreteOperators d.end_pos G.val.val M₀.val.val κ₀.val.val
  change (O₀.material V.val.val).val (t, a, s) +
      (O₀.phaseGrad p.val.val).val (t, a, s) =
      (genericLeadingSwitch d k χ).val.val.val (t, a, s)
  rw [HierarchySmoothProfile.hierarchyConcreteOperators_material_apply d.end_pos
      G.val.val M₀.val.val κ₀.val.val V.val.val hz]
  change _ + (HierarchySmoothProfile.phaseGradient d.end_pos κ₀.val.val p.val.val).val (t, a, s) = _
  rw [HierarchySmoothProfile.phaseGradient_apply d.end_pos κ₀.val.val p.val.val hz,
    hM _ hz, hκ _ hz, hv, hqp, genericLeading_cell_eval d k χ ht ha, genericLeadingSwitch_cell_eval d k χ ht ha]
  exact raw_momentum d χ ht a s

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

private theorem velocityMultiple_reflectionOdd (reg : w.HierarchyRegularity r h)
    {c : ℝ → ℝ} (hc : ContDiffOn ℝ ∞ c (Icc 0 T))
    (hzero : ∀ t ∈ Icc 0 T, t < t₀ → c t = 0)
    (hEven : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t)) :
    HierarchyProfileReflectionParity (-1) (velocityMultiple reg k c hc hzero).val.val.val := by
  apply reflect_of_onSlab
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  simp only [hierarchyProfileReflection_apply, velocityMultiple_eval reg k ht, neg_one_smul]
  by_cases hpre : t < t₀
  · simp only [hzero t ht hpre, zero_smul, neg_zero]
  · have hact : t ∈ Icc t₀ T := ⟨le_of_not_gt hpre, ht.2⟩
    have hNeg := phaseTwistedPeriodizeCentered_neg_equivariant (k := k) (f := w.leading h)
      (t := t) (L := Neg.neg) (neg_zero : -(0 : Vec3) = 0) ?_ ?_ a s
    · rw [hNeg, smul_neg]
    · intro b q
      simp only [SeedOn.leading, radialEnvelope_neg, odd_waveProfile reg.phase_pos reg.phase_le_one q,
        hEven t hact b, mul_neg, neg_smul]
    · intro b hb q
      obtain ⟨i, hi⟩ := hb
      have hz : |b i| ≤ ‖b‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le b i
      rw [hi, abs_neg, abs_of_nonneg (by norm_num)] at hz
      exact leading_zero_outside reg t (reg.envelope_fits.le.trans hz) q

theorem genericLeading_reflectionOdd (reg : w.HierarchyRegularity r h)
    (χ : PaperWaveCutoff t₀ T) (hEven : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t)) :
    HierarchyProfileReflectionParity (-1) (genericLeading reg k χ).val.val.val :=
  velocityMultiple_reflectionOdd reg χ.smooth χ.zero_before hEven

theorem genericLeadingSwitch_reflectionOdd (reg : w.HierarchyRegularity r h)
    (χ : PaperWaveCutoff t₀ T) (hEven : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t)) :
    HierarchyProfileReflectionParity (-1) (genericLeadingSwitch reg k χ).val.val.val :=
  velocityMultiple_reflectionOdd reg (χ.derivative_smooth reg.end_pos)
    (fun _ ht hpre => χ.derivative_zero_before reg.end_pos ht hpre) hEven

theorem genericPressure_reflectionEven (reg : w.HierarchyRegularity r h) (χ : PaperWaveCutoff t₀ T)
    (hEven : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t))
    (hM : ∀ t ∈ Icc t₀ T, Function.Even (M t))
    (hκ : ∀ t ∈ Icc t₀ T, Function.Even (κ t)) :
    HierarchyProfileReflectionParity 1 (genericPressure reg k χ).val.val.val := by
  apply reflect_of_onSlab
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  simp only [hierarchyProfileReflection_apply, genericPressure_eval reg k χ ht, one_smul]
  by_cases hpre : t < t₀
  · simp only [χ.zero_before t ht hpre, zero_mul]
  · have hact : t ∈ Icc t₀ T := ⟨le_of_not_gt hpre, ht.2⟩
    congr 1
    apply phaseTwistedPeriodizeCentered_neg_equivariant (L := id) rfl _ _ a s
    · intro b q
      simp only [SeedOn.leadingPressure, radialEnvelope_neg, hκ t hact b, hEven t hact b, hM t hact b,
        leadingPressurePrimitive_even reg q, id_eq]
    · intro b hb q
      obtain ⟨i, hi⟩ := hb
      have hz : |b i| ≤ ‖b‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le b i
      rw [hi, abs_neg, abs_of_nonneg (by norm_num)] at hz
      exact pressure_zero_outside reg t (reg.envelope_fits.le.trans hz) q

end LocalizedAmplitude.SeedOn

namespace HierarchyTwistedProfile.PhysicalLeadingInput

open LocalizedAmplitude LocalizedAmplitude.SeedOn

variable {T t₀ ell D C r h : ℝ} {hT : 0 < T}
  {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {center : ℝ → Vec3}

local notation "I" => Icc (0 : ℝ) T
local notation "J" => Set.prod I (univ : Set Vec3)
local notation "M" => (fun t a => fderiv ℝ (U t) (X 0 t a))
local notation "K" => (fun t a => labelWaveVector X 0 a k t)

private theorem label_even_of_profile_even
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : HierarchyTwistedProfile T k E} {f : ℝ → Vec3 → E}
    (hval : ∀ z ∈ hierarchyProfileSlab T, F.val.val.val z = f z.1 z.2.1)
    (hF : HierarchyProfileReflectionParity 1 F.val.val.val)
    {t : ℝ} (ht : t ∈ I) : Function.Even (f t) := by
  intro a
  have he := hF (t, a, 0)
  simp only [hierarchyProfileReflection_apply, neg_zero, one_smul] at he
  rw [hval _ ⟨ht, mem_univ _⟩, hval _ ⟨ht, mem_univ _⟩] at he
  exact he

/-- The actual leading pair and both activation pieces for an arbitrary paper cutoff. -/
def ofPaperCutoff (g : ParentGeometry hT U X k) (w : SeedOn M K center t₀ T ell D C)
    (reg : w.HierarchyRegularity r h) (χ : PaperWaveCutoff t₀ T)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hodd : ∀ t ∈ I, Function.Odd (U t))
    (hAmp : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t)) : PhysicalLeadingInput g :=
  have hpar := g.reflection hX hU hper hodd
  have hsub : Icc t₀ T ⊆ I := Icc_subset_Icc_left reg.nonneg_start
  { output := genericLeadingOutput reg χ g.inverse g.strain g.covector g.covector_value
    leadingSwitch := genericLeadingSwitch reg k χ
    completionSwitch := complete hT g.inverse g.covector g.oscillation.covector_independent
      g.oscillation.covector_ne_zero (genericLeadingSwitch reg k χ)
    momentum := genericLeadingOutput_momentum reg χ g.inverse g.strain g.covector
      g.strain_value g.covector_value
    velocity_odd := genericLeading_reflectionOdd reg χ hAmp
    pressure_even := genericPressure_reflectionEven reg χ hAmp
      (fun _ ht => label_even_of_profile_even (f := M) g.strain_value hpar.2.1 (hsub ht))
      (fun _ ht => label_even_of_profile_even (f := K) g.covector_value hpar.2.2.1 (hsub ht))
    completionSwitch_odd := complete_reflectionOdd_of_phaseMean_zero hT g.inverse g.covector
      g.oscillation.covector_independent g.oscillation.covector_ne_zero (genericLeadingSwitch reg k χ)
      hpar.1 hpar.2.2.1 (genericLeadingSwitch_reflectionOdd reg χ hAmp)
      (genericLeadingSwitch_average_zero reg χ) }

/-- The four profiles vanish before activation and outside the supported label set. -/
theorem ofPaperCutoff_inactive (g : ParentGeometry hT U X k) (w : SeedOn M K center t₀ T ell D C)
    (reg : w.HierarchyRegularity r h) (χ : PaperWaveCutoff t₀ T)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hodd : ∀ t ∈ I, Function.Odd (U t))
    (hAmp : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t))
    {S : Set Vec3} (hS : IsClosed S) (henv : Function.support (periodizeCentered (radialEnvelope ell)) ⊆ S) :
    (ofPaperCutoff g w reg χ hX hU hper hodd hAmp).Inactive t₀ S := by
  let R := hierarchyInactiveRegion T t₀ S
  have hvalues {t : ℝ} (ht : t ∈ I) (a : Vec3) (s : ℝ) (ha : t < t₀ ∨ a ∉ S) :
      (genericLeading reg k χ).val.val.val (t,a,s) = 0 ∧
      (genericPressure reg k χ).val.val.val (t,a,s) = 0 ∧
      (genericLeadingSwitch reg k χ).val.val.val (t,a,s) = 0 := by
    rw [genericLeading_eval reg k χ ht, genericPressure_eval reg k χ ht,
      genericLeadingSwitch_eval reg k χ ht]
    rcases ha with hpre | hout
    · simp only [χ.zero_before _ ht hpre, χ.derivative_zero_before hT ht hpre,
        zero_smul, zero_mul, and_self]
    · have hz : radialEnvelope ell (centeredLabel a) = 0 :=
        Function.notMem_support.mp fun hv => hout (henv hv)
      simp only [phaseTwistedPeriodizeCentered, SeedOn.leading, SeedOn.leadingPressure,
        wavePressureCoefficient, hz, mul_zero, zero_mul, zero_div, neg_zero, zero_smul, smul_zero, and_self]
  have hF : EqOn (genericLeadingSwitch reg k χ).val.val.val 0 R := by
    rintro ⟨t, a, s⟩ hx
    exact (hvalues hx.1.1 a s hx.2).2.2
  refine ⟨?_, ?_, hF, ?_⟩
  · rintro ⟨t, a, s⟩ hx
    exact (hvalues hx.1.1 a s hx.2).1
  · rintro ⟨t, a, s⟩ hx
    exact (hvalues hx.1.1 a s hx.2).2.1
  · change EqOn (complete hT g.inverse g.covector g.oscillation.covector_independent
      g.oscillation.covector_ne_zero (genericLeadingSwitch reg k χ)).val.val.val 0 R
    rw [complete_val_val_of_phaseMean_zero hT g.inverse g.covector g.oscillation.covector_independent
      g.oscillation.covector_ne_zero (genericLeadingSwitch reg k χ) (genericLeadingSwitch_average_zero reg χ)]
    exact HierarchySmoothProfile.profileCompletion_eq_zero_on_inactive hT hS g.inverse.val.val g.covector.val.val
      (genericLeadingSwitch reg k χ).val.val g.oscillation.covector_ne_zero hF

/-- The switched leading input supplies the phase mean, transversality, and exact completed switch. -/
theorem ofPaperCutoff_relay (g : ParentGeometry hT U X k) (w : SeedOn M K center t₀ T ell D C)
    (reg : w.HierarchyRegularity r h) (χ : PaperWaveCutoff t₀ T)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hodd : ∀ t ∈ I, Function.Odd (U t))
    (hAmp : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t))
    {p : Pressure} {depth : ℕ} (b : PhysicalApproximationData g p depth)
    (hLeading : b.leading = ofPaperCutoff g w reg χ hX hU hper hodd hAmp) :
    b.LeadingRelayData := by
  constructor
  · intro t ht x
    rw [hLeading]
    exact genericPressure_phaseMean_zero reg χ ht x
  · change profilePhaseAverage hT b.leading.leadingSwitch = 0
    rw [hLeading]
    exact genericLeadingSwitch_average_zero reg χ
  · intro t ht x s
    rw [hLeading]
    have hw := genericLeadingSwitch_transverse reg χ g.covector g.covector_value (t,x,s)
      ⟨ht,mem_univ _⟩
    have he := g.oscillation.covector_independent (t,x,0) ⟨ht,mem_univ _⟩ s
    change g.covector.val.val.val (t,x,s) = g.covector.val.val.val (t,x,0) at he
    rw [he] at hw
    exact hw
  · rw [hLeading]
    rfl

end HierarchyTwistedProfile.PhysicalLeadingInput

end
end TorusEuler
