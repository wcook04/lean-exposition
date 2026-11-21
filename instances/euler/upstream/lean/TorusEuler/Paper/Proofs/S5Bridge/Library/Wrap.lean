import TorusEuler.HierarchyTwistedProfiles
import TorusEuler.LocalizedSeedRegularity
import TorusEuler.TerminalSeeleyExtension
import TorusEuler.PeriodicLift
import TorusEuler.PhaseCalculus
import TorusEuler.WaveProfile
import TorusEuler.WavePressureCenter

/-!
# Library copies for the S5 bridge

Copies of private glue lemmas of the library (`TorusEuler/PaperGenericWaveSwitch.lean`),
made public under new names in namespace `TorusEuler.Paper.Lib.S5Bridge`. Each copy has the
statement of its original up to the changes listed below; the proofs are those of the
originals except where the table says otherwise. None of them is the content lemma of a
ledger row.

| original (private, `PaperGenericWaveSwitch.lean`) | copy | change |
|---|---|---|
| `HierarchyTwistedProfile.eq_of_centeredCell` (:109) | `eq_of_centeredCell` | same statement; proof rewritten (direct lattice reduction with `exists_sub_latticeVector_mem_centeredCell` instead of `all_on_centeredCell`) |
| `HierarchyTwistedProfile.all_on_centeredCell` (:98) | `forall_of_centeredCell` | carrier `k` explicit |
| `SeedOn.contDiffOn_slab_multiplier` (:167) | `contDiffOn_slab_multiplier` | variables made explicit |
| `HierarchyTwistedProfile.wrapOnSlab` (:75) | `wrapProfile` | carrier `k` explicit |
| `HierarchyTwistedProfile.wrapOnSlab_eval` (:89) | `wrapProfile_eval` | carrier `k` explicit |
| `SeedOn.wrapped_eq_on_cell_of_radial_zero` (:265) | `wrapped_eq_on_cell` | none |
| `SeedOn.phaseMean_wrapped_shift` (:305) | `phaseMean_wrapped_shift` | none |
| `SeedOn.leadingBare_smooth` (:128) | `leadingBare_smooth` | stated for any amplitude `amp`; the fields `amplitude_smooth`, `phase_pos`, `phase_le_one` of `HierarchyRegularity` become hypotheses; same proof |
| `SeedOn.barePressure_smooth` (:146) | `pressureBare_smooth` | stated for any coefficients `M`, `κ` and amplitude `amp`, with the private `barePressure` unfolded; the fields `strain_smooth`, `covector_smooth`, `covector_nonzero`, `amplitude_smooth`, `phase_pos`, `phase_le_one` of `HierarchyRegularity` become hypotheses; same proof |
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5Bridge

open HierarchyTwistedProfile

noncomputable section

/-! ## Profiles fixed by their values on the label cell -/

section Cell

variable {T : ℝ} {k : Vec3}

/-- A twisted profile is determined by its values on `[0,T] × [-1/2,1/2]³ × ℝ`. -/
theorem eq_of_centeredCell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : HierarchyTwistedProfile T k E}
    (hEq : ∀ t ∈ Icc 0 T, ∀ a ∈ centeredCell, ∀ s,
      f.val.val.val (t, a, s) = g.val.val.val (t, a, s)) : f = g := by
  apply HierarchyTwistedProfile.ext
  rintro ⟨t, a, s⟩ hx
  obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell a
  have h := hEq t hx.1 (a - latticeVector n) hn (s - ⟪k, latticeVector n⟫_ℝ)
  rw [← twistedSlice f t (a - latticeVector n) (s - ⟪k, latticeVector n⟫_ℝ) n,
    ← twistedSlice g t (a - latticeVector n) (s - ⟪k, latticeVector n⟫_ℝ) n] at h
  simpa only [sub_add_cancel] using h

end Cell

/-! ## Wrapping a field supported near the lattice into a twisted profile -/

section Wrap

variable {T : ℝ} {k : Vec3}

/-- A smooth multiplier vanishing before `t₀` times a field that is smooth on the active
slab `[t₀,T]` is smooth on the whole slab (copy of the private library lemma
`contDiffOn_slab_multiplier`, `PaperGenericWaveSwitch.lean:167`). -/
theorem contDiffOn_slab_multiplier {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {t₀ : ℝ} {c : ℝ → ℝ} {f : HierarchyProfilePoint → E}
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

/-- The twisted profile of a field `f(t,a,s)` periodic in the phase, extended from the
label cell by the twisted lattice translations (copy of the private library definition
`wrapOnSlab`, `PaperGenericWaveSwitch.lean:75`). -/
def wrapProfile {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : Vec3)
    {f : ℝ → Vec3 → ℝ → E}
    (hf : ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint =>
      phaseTwistedPeriodizeCentered k f x.1 x.2.1 x.2.2) (hierarchyProfileSlab T))
    (hper : ∀ t a, Function.Periodic (f t a) 1) : HierarchyTwistedProfile T k E :=
  HierarchyTwistedProfile.ofSmooth (fun x => phaseTwistedPeriodizeCentered k f x.1 x.2.1 x.2.2) hf
    (fun x => by
      rcases x with ⟨t, a, s⟩
      simpa only [hierarchyPhasePeriod, Prod.mk_add_mk, add_zero] using
        (phaseTwistedPeriodizeCentered_phase_periodic (k := k) (hper t) a s))
    (fun n x => by
      rw [add_hierarchyLatticeShift]
      exact phaseTwistedPeriodizeCentered_translate k f x.1 x.2.1 x.2.2 n)

/-- Values of `wrapProfile` on the slab. -/
theorem wrapProfile_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : Vec3)
    {f : ℝ → Vec3 → ℝ → E}
    (hf : ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint =>
      phaseTwistedPeriodizeCentered k f x.1 x.2.1 x.2.2) (hierarchyProfileSlab T))
    (hper : ∀ t a, Function.Periodic (f t a) 1) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (wrapProfile (T := T) k hf hper).val.val.val (t, a, s) = phaseTwistedPeriodizeCentered k f t a s :=
  HierarchyTwistedProfile.ofSmooth_eval _ _ _ ⟨ht, mem_univ _⟩

/-- A property of slab points that is invariant under the twisted lattice translations
holds on the slab once it holds on the label cell (copy of the private library lemma
`all_on_centeredCell`). -/
theorem forall_of_centeredCell (k : Vec3) {Q : HierarchyProfilePoint → Prop}
    (hShift : ∀ (t : ℝ) (a : Vec3) (s : ℝ) (n : Fin 3 → ℤ),
      Q (t, a, s) → Q (t, a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ))
    (hCell : ∀ t ∈ Icc 0 T, ∀ a ∈ centeredCell, ∀ s, Q (t, a, s)) :
    ∀ x ∈ hierarchyProfileSlab T, Q x := by
  rintro ⟨t, a, s⟩ ht
  obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell a
  have hz := hShift t (a - latticeVector n) (s - ⟪k, latticeVector n⟫_ℝ) n
    (hCell t ht.1 _ hn _)
  simpa only [sub_add_cancel] using hz

/-- On the label cell the twisted extension of a field vanishing for `|a| ≥ 2ℓ`
(`2ℓ < 1/2`) is the field itself (copy of the private library lemma
`wrapped_eq_on_cell_of_radial_zero`). -/
theorem wrapped_eq_on_cell {E : Type*} [Zero E] {ell : ℝ} {f : ℝ → Vec3 → ℝ → E} (k : Vec3)
    {t : ℝ} {a : Vec3} (ha : a ∈ centeredCell) (s : ℝ) (hfit : 2 * ell < 1 / 2)
    (hzero : ∀ b, 2 * ell ≤ ‖b‖ → ∀ q, f t b q = 0) :
    phaseTwistedPeriodizeCentered k f t a s = f t a s := by
  refine phaseTwistedPeriodizeCentered_eq_on_centeredCell (sub_pos.mpr hfit) ?_ ha s
  intro b hb q
  obtain ⟨i, hi⟩ := hb
  have hbi : |b i| ≤ ‖b‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le b i
  exact hzero b (by linarith) q

/-- The twisted extension of a field with zero phase mean at every label has zero phase
mean (copy of the private library lemma `phaseMean_wrapped_shift`). -/
theorem phaseMean_wrapped_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

end Wrap

/-! ## Smoothness of the bare leading fields -/

section Bare

variable {t₀ T h : ℝ}

/-- `F_h(s) 𝐚(t,a)` is jointly smooth on the active slab `[t₀,T] × ℝ³ × ℝ` (copy of the
private library lemma `SeedOn.leadingBare_smooth`, `PaperGenericWaveSwitch.lean:128`, for
any amplitude `amp`, with the regularity fields used by its proof as hypotheses). -/
theorem leadingBare_smooth {amp : ℝ → Vec3 → Vec3}
    (hamp : ContDiffOn ℝ ∞ (Function.uncurry amp) (Icc t₀ T ×ˢ (univ : Set Vec3)))
    (hh : 0 < h) (hh₁ : h ≤ 1) :
    ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint => waveProfile h x.2.2 • amp x.1 x.2.1)
      (Icc t₀ T ×ˢ univ) := by
  have hA := hamp.comp (contDiff_fst.prodMk contDiff_snd.fst).contDiffOn
    (fun x (hx : x ∈ Icc t₀ T ×ˢ (univ : Set (Vec3 × ℝ))) => ⟨hx.1, mem_univ _⟩)
  exact ((contDiff_waveProfile hh hh₁).comp contDiff_snd.snd).contDiffOn.smul hA

set_option maxHeartbeats 1000000 in
/-- The leading pressure without its envelope, `-(2⟨κ, M𝐚⟩/|κ|²) P_h(s)`, is jointly
smooth on the active slab (copy of the private library lemma `SeedOn.barePressure_smooth`,
`PaperGenericWaveSwitch.lean:146`, for any coefficients `M`, `κ` and amplitude `amp`, with
the private `barePressure` unfolded and the regularity fields used by its proof as
hypotheses). -/
theorem pressureBare_smooth {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ amp : ℝ → Vec3 → Vec3}
    (hMs : ContDiffOn ℝ ∞ (Function.uncurry M) (Icc t₀ T ×ˢ (univ : Set Vec3)))
    (hκs : ContDiffOn ℝ ∞ (Function.uncurry κ) (Icc t₀ T ×ˢ (univ : Set Vec3)))
    (hκ : ∀ t ∈ Icc t₀ T, ∀ a, κ t a ≠ 0)
    (hamp : ContDiffOn ℝ ∞ (Function.uncurry amp) (Icc t₀ T ×ˢ (univ : Set Vec3)))
    (hh : 0 < h) (hh₁ : h ≤ 1) :
    ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint =>
      -wavePressureCoefficient 1 (κ x.1 x.2.1) (amp x.1 x.2.1) (M x.1 x.2.1) *
        wavePressurePrimitive h x.2.2) (Icc t₀ T ×ˢ univ) := by
  let I : Set HierarchyProfilePoint := Icc t₀ T ×ˢ univ
  let L (x : HierarchyProfilePoint) := (x.1, x.2.1)
  have hL : ContDiffOn ℝ ∞ L I := (contDiff_fst.prodMk contDiff_snd.fst).contDiffOn
  have hmaps : MapsTo L I (Icc t₀ T ×ˢ (univ : Set Vec3)) := fun _ hx => ⟨hx.1, mem_univ _⟩
  have hK := hκs.comp hL hmaps
  have hA := hamp.comp hL hmaps
  have hM := hMs.comp hL hmaps
  have hn (x : HierarchyProfilePoint) (hx : x ∈ I) : ‖κ x.1 x.2.1‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (hκ x.1 hx.1 x.2.1))
  have hCoef := (contDiffOn_const (c := (2 : ℝ))).mul (hK.inner ℝ (hM.clm_apply hA))
  have hC := (hCoef.div (ContDiffOn.norm_sq ℝ hK) hn).neg
  simpa only [wavePressureCoefficient, mul_one, Function.comp_apply,
    Function.uncurry_apply_pair, Pi.div_apply, L, I] using
    hC.mul (((contDiff_wavePressurePrimitive hh hh₁).comp contDiff_snd.snd).contDiffOn)

end Bare

end

end TorusEuler.Paper.Lib.S5Bridge
