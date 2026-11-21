import TorusEuler.Paper.Proofs.S5Bridge.Hierarchy
import TorusEuler.Paper.Proofs.S5Bridge.Library.Wrap
import TorusEuler.TerminalSeeleyExtension
import TorusEuler.WavePressureCenter
import TorusEuler.ActivationProfiles
import TorusEuler.WaveProfile

/-!
# S5 bridge: the leading pair `(χ̃A₁, χ̃𝗉[A₁])` and the activation term `χ̃'A₁`

From an `S5.IsSeed` the leading oscillation `A₁ = g𝐚F_h` and its pressure `𝗉[A₁]` of (3.3),
multiplied by a smooth time factor `c` vanishing before `t₀` (the cutoff `χ̃` or its
derivative `χ̃'`), are wrapped into lattice-twisted profiles whose values on the label
cell are the raw fields (`leadingVelocityProfile`, `leadingPressureProfile`). With
`c = χ̃` the pair is a transverse output of the operators `S5.ops d`
(`leadingOutput`: zero phase mean and `κ·V = 0`), and with `c = χ̃'` it is the
activation term `S = χ̃'A₁`. Together with the abstract mean solver this gives an
expansion (`exists_isExpansion`).

Only the defining properties of the seed (transversality and smoothness) and of the
profile (`F_h` periodic with zero mean, `P_h` periodic, both smooth) are used; the
leading momentum identity (3.4) is not used. The wrapping and smoothness lemmas used here
are the copies of private library lemmas of `TorusEuler/PaperGenericWaveSwitch.lean` in
`Library/Wrap.lean` (namespace `TorusEuler.Paper.Lib.S5Bridge`: `contDiffOn_slab_multiplier`,
`wrapProfile`, `wrapProfile_eval`, `forall_of_centeredCell`, `wrapped_eq_on_cell`,
`phaseMean_wrapped_shift`, `leadingBare_smooth`, `pressureBare_smooth`); this file only
supplies their hypotheses for the Section 5 seed and parent.
-/

open Set ContinuousLinearMap
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Bridge

open HierarchyTwistedProfile Lib.S5Bridge

noncomputable section


/-! ## The leading fields of a seed -/

section Leading

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {t₀ : ℝ} {center : ℝ → Vec3}
  {pU : Pressure} {D lam : ℝ}

/-- `c(t) F_h(s) 𝐚(t,a)`: the leading velocity without its envelope, times a time factor. -/
def leadingCore (h : ℝ) (amp : ℝ → Vec3 → Vec3) (c : ℝ → ℝ) (t : ℝ) (a : Vec3) (s : ℝ) : Vec3 :=
  c t • (waveProfile h s • amp t a)

/-- `c(t) (-p_w|_{g=1}) P_h(s)`: the leading pressure without its envelope, times a time
factor. -/
def pressureCore (U : Velocity) (X : ℝ → Velocity) (k : Vec3) (h : ℝ) (amp : ℝ → Vec3 → Vec3)
    (c : ℝ → ℝ) (t : ℝ) (a : Vec3) (s : ℝ) : ℝ :=
  c t • (-wavePressureCoefficient 1 (S5.waveVector X k t a) (amp t a) (S5.strainField U X t a) *
    wavePressurePrimitive h s)

/-- `g · c F_h 𝐚 = c A₁`. -/
theorem envelope_leadingCore (ℓ h : ℝ) (amp : ℝ → Vec3 → Vec3) (c : ℝ → ℝ) (t : ℝ) (a : Vec3)
    (s : ℝ) : radialEnvelope ℓ a • leadingCore h amp c t a s = c t • S5.leading ℓ h amp t a s := by
  simp only [leadingCore, S5.leading, smul_smul]
  congr 1
  ring

/-- `g · c (-p_w|_{g=1}) P_h = c 𝗉[A₁]`. -/
theorem envelope_pressureCore (ℓ h : ℝ) (amp : ℝ → Vec3 → Vec3) (c : ℝ → ℝ) (t : ℝ) (a : Vec3)
    (s : ℝ) : radialEnvelope ℓ a • pressureCore U X k h amp c t a s =
      c t * S5.leadingPressure U X k ℓ h amp t a s := by
  simp only [pressureCore, S5.leadingPressure, wavePressureCoefficient, smul_eq_mul]
  ring

/-- The leading core is smooth on the slab (the library copies `leadingBare_smooth` and
`contDiffOn_slab_multiplier`, with the smoothness of the seed). -/
theorem leadingCore_smooth (hL : S5.Launch T X k lam t₀) {amp : ℝ → Vec3 → Vec3}
    (hamp : S5.IsSeed U X k t₀ T center amp) {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ ∞ c (Icc 0 T)) (hzero : ∀ t ∈ Icc 0 T, t < t₀ → c t = 0) :
    ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint => leadingCore h amp c x.1 x.2.1 x.2.2)
      (Icc 0 T ×ˢ univ) :=
  contDiffOn_slab_multiplier hL.start_lt hc hzero (leadingBare_smooth hamp.smooth hh hh₁)

/-- The pressure core is smooth on the slab (the library copies `pressureBare_smooth` and
`contDiffOn_slab_multiplier`, with the smoothness of `M`, `κ` and of the seed and
`κ ≠ 0` on the active slab). -/
theorem pressureCore_smooth (hP : S5.Parent T U X pU D lam) (hL : S5.Launch T X k lam t₀)
    {amp : ℝ → Vec3 → Vec3} (hamp : S5.IsSeed U X k t₀ T center amp) {h : ℝ} (hh : 0 < h)
    (hh₁ : h ≤ 1) {c : ℝ → ℝ} (hc : ContDiffOn ℝ ∞ c (Icc 0 T))
    (hzero : ∀ t ∈ Icc 0 T, t < t₀ → c t = 0) :
    ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint => pressureCore U X k h amp c x.1 x.2.1 x.2.2)
      (Icc 0 T ×ˢ univ) := by
  have hT := Launch.end_pos hL
  have hsub : Icc t₀ T ×ˢ (univ : Set Vec3) ⊆ Icc 0 T ×ˢ univ :=
    prod_mono (Launch.active_subset hL) subset_rfl
  exact contDiffOn_slab_multiplier hL.start_lt hc hzero
    (pressureBare_smooth ((Parent.strainField_smooth hT hP).mono hsub)
      ((Parent.waveVector_smooth (k := k) hT hP).mono hsub)
      (fun t ht a => Parent.waveVector_ne_zero hT hP hL.carrier_ne_zero
        (Launch.active_subset hL ht) a)
      hamp.smooth hh hh₁)

/-- The twisted profile of `c A₁` (`A₁ = g𝐚F_h` with `g = radialEnvelope ℓ`), for a smooth
time factor `c` vanishing before `t₀`. -/
def leadingVelocityProfile (hL : S5.Launch T X k lam t₀) {amp : ℝ → Vec3 → Vec3}
    (hamp : S5.IsSeed U X k t₀ T center amp) {ℓ : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (c : ℝ → ℝ) (hc : ContDiffOn ℝ ∞ c (Icc 0 T))
    (hzero : ∀ t ∈ Icc 0 T, t < t₀ → c t = 0) : HierarchyTwistedProfile T k Vec3 :=
  wrapProfile k (f := fun t a s => radialEnvelope ℓ a • leadingCore h amp c t a s)
    (contDiffOn_phaseTwistedPeriodizeCentered_radialEnvelope (k := k) (f := leadingCore h amp c)
      (I := Icc 0 T) hℓ hfit (leadingCore_smooth hL hamp hh hh₁ hc hzero))
    (fun t a s => by simp only [leadingCore, periodic_waveProfile hh hh₁ s])

/-- The twisted profile of `c 𝗉[A₁]`. -/
def leadingPressureProfile (hP : S5.Parent T U X pU D lam) (hL : S5.Launch T X k lam t₀)
    {amp : ℝ → Vec3 → Vec3} (hamp : S5.IsSeed U X k t₀ T center amp) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hfit : 2 * ℓ < 1 / 2) {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (c : ℝ → ℝ)
    (hc : ContDiffOn ℝ ∞ c (Icc 0 T)) (hzero : ∀ t ∈ Icc 0 T, t < t₀ → c t = 0) :
    HierarchyTwistedProfile T k ℝ :=
  wrapProfile k (f := fun t a s => radialEnvelope ℓ a • pressureCore U X k h amp c t a s)
    (contDiffOn_phaseTwistedPeriodizeCentered_radialEnvelope (k := k)
      (f := pressureCore U X k h amp c) (I := Icc 0 T) hℓ hfit
      (pressureCore_smooth hP hL hamp hh hh₁ hc hzero))
    (fun t a s => by simp only [pressureCore, periodic_wavePressurePrimitive hh hh₁ s])

/-- Values of `leadingVelocityProfile` on the slab: the twisted extension of `c A₁`. -/
theorem leadingVelocityProfile_eval (hL : S5.Launch T X k lam t₀) {amp : ℝ → Vec3 → Vec3}
    (hamp : S5.IsSeed U X k t₀ T center amp) {ℓ : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (c : ℝ → ℝ) (hc : ContDiffOn ℝ ∞ c (Icc 0 T))
    (hzero : ∀ t ∈ Icc 0 T, t < t₀ → c t = 0) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (leadingVelocityProfile hL hamp hℓ hfit hh hh₁ c hc hzero).val.val.val (t, a, s) =
      phaseTwistedPeriodizeCentered k
        (fun t a s => radialEnvelope ℓ a • leadingCore h amp c t a s) t a s :=
  wrapProfile_eval k _ _ ht a s

/-- Values of `leadingPressureProfile` on the slab: the twisted extension of `c 𝗉[A₁]`. -/
theorem leadingPressureProfile_eval (hP : S5.Parent T U X pU D lam)
    (hL : S5.Launch T X k lam t₀) {amp : ℝ → Vec3 → Vec3} (hamp : S5.IsSeed U X k t₀ T center amp)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (c : ℝ → ℝ)
    (hc : ContDiffOn ℝ ∞ c (Icc 0 T)) (hzero : ∀ t ∈ Icc 0 T, t < t₀ → c t = 0) {t : ℝ}
    (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (leadingPressureProfile hP hL hamp hℓ hfit hh hh₁ c hc hzero).val.val.val (t, a, s) =
      phaseTwistedPeriodizeCentered k
        (fun t a s => radialEnvelope ℓ a • pressureCore U X k h amp c t a s) t a s :=
  wrapProfile_eval k _ _ ht a s

/-- On the label cell, `leadingVelocityProfile` is `c A₁`. -/
theorem leadingVelocityProfile_cell_eval (hL : S5.Launch T X k lam t₀) {amp : ℝ → Vec3 → Vec3}
    (hamp : S5.IsSeed U X k t₀ T center amp) {ℓ : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (c : ℝ → ℝ) (hc : ContDiffOn ℝ ∞ c (Icc 0 T))
    (hzero : ∀ t ∈ Icc 0 T, t < t₀ → c t = 0) {t : ℝ} (ht : t ∈ Icc 0 T) {a : Vec3}
    (ha : a ∈ centeredCell) (s : ℝ) :
    (leadingVelocityProfile hL hamp hℓ hfit hh hh₁ c hc hzero).val.val.val (t, a, s) =
      c t • S5.leading ℓ h amp t a s := by
  rw [leadingVelocityProfile_eval hL hamp hℓ hfit hh hh₁ c hc hzero ht, wrapped_eq_on_cell k ha s hfit
    (fun b hb q => by simp only [radialEnvelope_eq_zero hℓ hb, zero_smul])]
  exact envelope_leadingCore ℓ h amp c t a s

/-- On the label cell, `leadingPressureProfile` is `c 𝗉[A₁]`. -/
theorem leadingPressureProfile_cell_eval (hP : S5.Parent T U X pU D lam)
    (hL : S5.Launch T X k lam t₀) {amp : ℝ → Vec3 → Vec3} (hamp : S5.IsSeed U X k t₀ T center amp)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (c : ℝ → ℝ)
    (hc : ContDiffOn ℝ ∞ c (Icc 0 T)) (hzero : ∀ t ∈ Icc 0 T, t < t₀ → c t = 0) {t : ℝ}
    (ht : t ∈ Icc 0 T) {a : Vec3} (ha : a ∈ centeredCell) (s : ℝ) :
    (leadingPressureProfile hP hL hamp hℓ hfit hh hh₁ c hc hzero).val.val.val (t, a, s) =
      c t * S5.leadingPressure U X k ℓ h amp t a s := by
  rw [leadingPressureProfile_eval hP hL hamp hℓ hfit hh hh₁ c hc hzero ht, wrapped_eq_on_cell k ha s hfit
    (fun b hb q => by simp only [radialEnvelope_eq_zero hℓ hb, zero_smul])]
  exact envelope_pressureCore ℓ h amp c t a s

/-- `c A₁` has zero phase mean (`F_h` has zero mean). -/
theorem leadingVelocityProfile_average {hT : 0 < T} (d : ParentGeometry hT U X k)
    (hL : S5.Launch T X k lam t₀) {amp : ℝ → Vec3 → Vec3} (hamp : S5.IsSeed U X k t₀ T center amp)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (c : ℝ → ℝ)
    (hc : ContDiffOn ℝ ∞ c (Icc 0 T)) (hzero : ∀ t ∈ Icc 0 T, t < t₀ → c t = 0) :
    (S5.ops d).average (leadingVelocityProfile hL hamp hℓ hfit hh hh₁ c hc hzero) = 0 := by
  apply HierarchyTwistedProfile.ext
  intro x hx
  rw [ops_average_eval d _ hx]
  have hfun : (fun z => (leadingVelocityProfile hL hamp hℓ hfit hh hh₁ c hc hzero).val.val.val
      (x.1, x.2.1, z)) = phaseTwistedPeriodizeCentered k
        (fun t a s => radialEnvelope ℓ a • leadingCore h amp c t a s) x.1 x.2.1 :=
    funext fun z => leadingVelocityProfile_eval hL hamp hℓ hfit hh hh₁ c hc hzero hx.1 _ _
  rw [hfun]
  refine phaseMean_wrapped_shift k x.2.1 (fun b q => ?_) (fun b => ?_)
  · simp only [leadingCore, periodic_waveProfile hh hh₁ q]
  · have he : (fun q => radialEnvelope ℓ b • leadingCore h amp c x.1 b q) =
        fun q => (radialEnvelope ℓ b * c x.1) • toSpanSingleton ℝ (amp x.1 b) (waveProfile h q) := by
      funext q
      simp only [leadingCore, toSpanSingleton_apply, smul_smul, mul_assoc]
    rw [he, phaseMean_const_smul, phaseMean,
      (toSpanSingleton ℝ (amp x.1 b)).intervalIntegral_comp_comm
        ((contDiff_waveProfile hh hh₁).continuous.intervalIntegrable 0 1),
      ← phaseMean, phaseMean_waveProfile hh hh₁, map_zero, smul_zero]

/-- `κ·(c A₁) = 0` on the slab (the seed is transverse). -/
theorem leadingVelocityProfile_transverse {hT : 0 < T} (d : ParentGeometry hT U X k)
    (hL : S5.Launch T X k lam t₀) {amp : ℝ → Vec3 → Vec3} (hamp : S5.IsSeed U X k t₀ T center amp)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (c : ℝ → ℝ)
    (hc : ContDiffOn ℝ ∞ c (Icc 0 T)) (hzero : ∀ t ∈ Icc 0 T, t < t₀ → c t = 0) :
    ∀ t ∈ Icc 0 T, ∀ a s, ⟪S5.waveVector X k t a,
      (leadingVelocityProfile hL hamp hℓ hfit hh hh₁ c hc hzero).val.val.val (t, a, s)⟫_ℝ = 0 := by
  let V := leadingVelocityProfile hL hamp hℓ hfit hh hh₁ c hc hzero
  have hall := forall_of_centeredCell (T := T) k
    (Q := fun x => ⟪d.covector.val.val.val x, V.val.val.val x⟫_ℝ = 0)
    (fun t a s n hq => by simpa only [HierarchyTwistedProfile.twistedSlice] using hq)
    (fun t ht a ha s => by
      have hκ : d.covector.val.val.val (t, a, s) = S5.waveVector X k t a :=
        d.covector_value (t, a, s) ⟨ht, mem_univ _⟩
      change ⟪d.covector.val.val.val (t, a, s), V.val.val.val (t, a, s)⟫_ℝ = 0
      rw [hκ, leadingVelocityProfile_cell_eval hL hamp hℓ hfit hh hh₁ c hc hzero ht ha s]
      by_cases hpre : t < t₀
      · rw [hzero _ ht hpre, zero_smul, inner_zero_right]
      · have hact : t ∈ Icc t₀ T := ⟨le_of_not_gt hpre, ht.2⟩
        simp only [S5.leading, real_inner_smul_right, hamp.transverse a t hact, mul_zero])
  intro t ht a s
  have h := hall (t, a, s) ⟨ht, mem_univ _⟩
  have hκ : d.covector.val.val.val (t, a, s) = S5.waveVector X k t a :=
    d.covector_value (t, a, s) ⟨ht, mem_univ _⟩
  change ⟪d.covector.val.val.val (t, a, s), V.val.val.val (t, a, s)⟫_ℝ = 0 at h
  rw [hκ] at h
  exact h

/-- The leading pair `(χ̃A₁, χ̃𝗉[A₁])` as a transverse output of the operators `S5.ops d`. -/
def leadingOutput {hT : 0 < T} (d : ParentGeometry hT U X k) (hP : S5.Parent T U X pU D lam)
    (hL : S5.Launch T X k lam t₀) {amp : ℝ → Vec3 → Vec3} (hamp : S5.IsSeed U X k t₀ T center amp)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (χ : PaperWaveCutoff t₀ T) : HierarchyTransverseOutput (S5.ops d) where
  V := leadingVelocityProfile hL hamp hℓ hfit hh hh₁ χ.value χ.smooth χ.zero_before
  p := leadingPressureProfile hP hL hamp hℓ hfit hh hh₁ χ.value χ.smooth χ.zero_before
  average_V := leadingVelocityProfile_average d hL hamp hℓ hfit hh hh₁ χ.value χ.smooth χ.zero_before
  phaseAdv_V := fun v => ops_phaseAdv_of_transverse d
    (leadingVelocityProfile_transverse d hL hamp hℓ hfit hh hh₁ χ.value χ.smooth χ.zero_before) v

/-- The activation term `S = χ̃'A₁` of (3.8) as a twisted profile. -/
def activationProfile (hL : S5.Launch T X k lam t₀) {amp : ℝ → Vec3 → Vec3}
    (hamp : S5.IsSeed U X k t₀ T center amp) {ℓ : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (χ : PaperWaveCutoff t₀ T) : HierarchyTwistedProfile T k Vec3 :=
  leadingVelocityProfile hL hamp hℓ hfit hh hh₁ χ.derivative
    (χ.derivative_smooth (Launch.end_pos hL))
    (fun _ ht hpre => χ.derivative_zero_before (Launch.end_pos hL) ht hpre)

/-- Existence of an expansion: for an abstract mean solver, the library construction over
`solvers d hM (transverseSolvable d)`, started from the leading pair of the seed, with the
activation term `χ̃'A₁` and the parent residual `R_U∘X`, is an expansion of every depth
`P ≥ 1`. -/
theorem exists_isExpansion {hT : 0 < T} (d : ParentGeometry hT U X k) (hM : MeanSolvable d)
    (hP : S5.Parent T U X pU D lam) (hL : S5.Launch T X k lam t₀) {amp : ℝ → Vec3 → Vec3}
    (hamp : S5.IsSeed U X k t₀ T center amp) {ℓ : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (χ : PaperWaveCutoff t₀ T) {P : ℕ} (hP1 : 1 ≤ P) :
    ∃ (R S : HierarchyTwistedProfile T k Vec3)
      (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)),
      S5.IsExpansion d pU χ ℓ h amp P R S u := by
  obtain ⟨R, hRavg, hR⟩ := exists_residualProfile d hP
  have hS : ∀ t ∈ Icc 0 T, ∀ a ∈ centeredCell, ∀ s,
      (activationProfile hL hamp hℓ hfit hh hh₁ χ).val.val.val (t, a, s) =
        χ.derivative t • S5.leading ℓ h amp t a s := fun t ht a ha s =>
    leadingVelocityProfile_cell_eval hL hamp hℓ hfit hh hh₁ χ.derivative
      (χ.derivative_smooth (Launch.end_pos hL))
      (fun _ ht hpre => χ.derivative_zero_before (Launch.end_pos hL) ht hpre) ht ha s
  have hV : ∀ t ∈ Icc 0 T, ∀ a ∈ centeredCell, ∀ s,
      (leadingOutput d hP hL hamp hℓ hfit hh hh₁ χ).V.val.val.val (t, a, s) =
        χ.value t • S5.leading ℓ h amp t a s := fun t ht a ha s =>
    leadingVelocityProfile_cell_eval hL hamp hℓ hfit hh hh₁ χ.value χ.smooth χ.zero_before ht ha s
  have hp : ∀ t ∈ Icc 0 T, ∀ a ∈ centeredCell, ∀ s,
      (leadingOutput d hP hL hamp hℓ hfit hh hh₁ χ).p.val.val.val (t, a, s) =
        χ.value t * S5.leadingPressure U X k ℓ h amp t a s := fun t ht a ha s =>
    leadingPressureProfile_cell_eval hP hL hamp hℓ hfit hh hh₁ χ.value χ.smooth χ.zero_before
      ht ha s
  exact ⟨R, activationProfile hL hamp hℓ hfit hh hh₁ χ, _,
    construct_isExpansion d hM (transverseSolvable d) χ ℓ h amp hP1
      (leadingOutput d hP hL hamp hℓ hfit hh hh₁ χ) R (activationProfile hL hamp hℓ hfit hh hh₁ χ)
      hRavg hR hS hV hp⟩

end Leading

end

end TorusEuler.Paper.Bridge
