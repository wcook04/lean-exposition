import TorusEuler.Paper.S5.Vocabulary
import TorusEuler.Paper.Proofs.S5Bridge.Parent
import TorusEuler.PaperHierarchyUnswitchedRelay

/-!
# S5a library: the leading oscillation `A₁` on `[t₀,T]` as twisted profiles

For the last clause of Lemma 5.5 ("for the leading oscillation `V = A₁` on `[t₀,T]` the
source is `f = 0`", `sections/06c_finite_hierarchy.tex:412-413`), the fields
`A₁ = g𝐚F_h` and `𝗉[A₁]` of a seed (any `S5.IsSeed`) are represented by smooth twisted
profiles on `[0,T]` (a smooth extension in time of the seed, then the lattice-twisted
periodization of the envelope), and the leading equation (3.4)
`(∂_t + M)A₁ + κ∂_s𝗉[A₁] = 0` with `κ·A₁ = 0` holds on `[t₀,T]`.

Copies (all over `S5.IsSeed` instead of the library seed type `SeedOn`):

| original | copy | change |
|---|---|---|
| `envelopeWrapped_smooth`, `envelopeWrapped`, `envelopeWrapped_eval`, `envelopeWrapped_phaseMean`, `envelopeWrapped_average` (private, `TorusEuler/PaperHierarchyUnswitchedRelay.lean:19-88`) | same names in `Lib.S5a` | none |
| `exists_unswitched_wrapped_representatives` (`PaperHierarchyUnswitchedRelay.lean:91`) | `exists_leading_representatives` | the seed is an `S5.IsSeed`; the regularity fields of `HierarchyRegularity` are supplied by `S5.Parent`, `S5.Launch` and `S5.IsSeed.smooth` |
| `wrapped_eq_on_centeredCell_of_radius` (private, `PaperHierarchyUnswitchedRelay.lean:138`) | `wrapped_eq_on_cell` | none |
| `SeedOn.paper_hierarchy_leading_homogeneous` and its private helpers (`TorusEuler/PaperHierarchyLeadingEquation.lean:13-78`, content of row 5.5) | `leading_homogeneous` | stated for an `S5.IsSeed` (only `equation` and `transverse` of the seed are read) |
-/

open Set Function
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5a

noncomputable section

open HierarchyTwistedProfile LocalizedAmplitude

section Wrapped

variable {T ℓ : ℝ} {k : Vec3}

/-- Copy of the private `envelopeWrapped_smooth` (`PaperHierarchyUnswitchedRelay.lean:19`). -/
theorem envelopeWrapped_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ × Vec3 → E} {z : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hz : ContDiff ℝ ∞ z)
    (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) :
    ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint =>
      phaseTwistedPeriodizeCentered k (fun t a s => radialEnvelope ℓ a • (z s • u (t,a)))
        x.1 x.2.1 x.2.2) (hierarchyProfileSlab T) :=
  contDiffOn_phaseTwistedPeriodizeCentered_radialEnvelope hℓ hfit
    (((hz.comp contDiff_snd.snd).smul (hu.comp (contDiff_fst.prodMk contDiff_snd.fst))).contDiffOn)

/-- Copy of the private `envelopeWrapped` (`PaperHierarchyUnswitchedRelay.lean:29`): the
twisted profile of `g(a) z(s) u(t,a)`. -/
def envelopeWrapped {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ × Vec3 → E} {z : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hz : ContDiff ℝ ∞ z)
    (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) (hper : Periodic z 1) :
    HierarchyTwistedProfile T k E :=
  ofSmooth (fun x => phaseTwistedPeriodizeCentered k (fun t a s => radialEnvelope ℓ a • (z s • u (t,a)))
    x.1 x.2.1 x.2.2) (envelopeWrapped_smooth hu hz hℓ hfit)
    (fun x => by
      rcases x with ⟨t,a,s⟩
      simpa only [hierarchyPhasePeriod, Prod.mk_add_mk, add_zero] using
        (phaseTwistedPeriodizeCentered_phase_periodic (k := k)
          (f := fun t a s => radialEnvelope ℓ a • (z s • u (t,a)))
          (fun a q => by
            change radialEnvelope ℓ a • (z (q + 1) • u (t,a)) = _
            rw [hper q]) a s))
    (fun n x => by
      rw [add_hierarchyLatticeShift]
      exact phaseTwistedPeriodizeCentered_translate k _ x.1 x.2.1 x.2.2 n)

/-- Copy of the private `envelopeWrapped_eval` (`PaperHierarchyUnswitchedRelay.lean:46`). -/
theorem envelopeWrapped_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ × Vec3 → E} {z : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hz : ContDiff ℝ ∞ z)
    (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) (hper : Periodic z 1) {t : ℝ}
    (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (envelopeWrapped (T := T) (k := k) hu hz hℓ hfit hper).val.val.val (t,a,s) =
      phaseTwistedPeriodizeCentered k (fun t a s => radialEnvelope ℓ a • (z s • u (t,a))) t a s :=
  ofSmooth_eval _ _ _ ⟨ht, mem_univ _⟩

/-- Copy of the private `envelopeWrapped_phaseMean` (`PaperHierarchyUnswitchedRelay.lean:54`). -/
theorem envelopeWrapped_phaseMean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {u : ℝ × Vec3 → E} {z : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hz : ContDiff ℝ ∞ z)
    (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) (hper : Periodic z 1) (hMean : phaseMean z = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) :
    phaseMean (fun s => (envelopeWrapped (T := T) (k := k) hu hz hℓ hfit hper).val.val.val (t,a,s)) = 0 := by
  simp_rw [envelopeWrapped_eval hu hz hℓ hfit hper ht]
  let b := centeredLabel a
  let c := -⟪k,a⟫_ℝ + ⟪k,b⟫_ℝ
  have he : (fun s => phaseTwistedPeriodizeCentered k
      (fun t a s => radialEnvelope ℓ a • (z s • u (t,a))) t a s) =
      fun s => radialEnvelope ℓ b • (z (s + c) • u (t,b)) := by
    funext s
    simp only [phaseTwistedPeriodizeCentered, b, c, sub_eq_add_neg, add_assoc]
  rw [he, phaseMean_const_smul, phaseMean, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_comp_add_right, zero_add]
  have hc := hper.intervalIntegral_add_eq c 0
  simp only [zero_add] at hc
  rw [add_comm (1 : ℝ) c, hc, ← phaseMean, hMean, zero_smul, smul_zero]

/-- Copy of the private `envelopeWrapped_average` (`PaperHierarchyUnswitchedRelay.lean:76`). -/
theorem envelopeWrapped_average
    (hT : 0 < T) {u : ℝ × Vec3 → Vec3} {z : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hz : ContDiff ℝ ∞ z)
    (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) (hper : Periodic z 1) (hMean : phaseMean z = 0) :
    profilePhaseAverage hT (envelopeWrapped (T := T) (k := k) hu hz hℓ hfit hper) = 0 := by
  apply HierarchyTwistedProfile.ext
  rintro ⟨t,a,s⟩ hx
  change (HierarchySmoothProfile.profilePhaseAverage hT
    (envelopeWrapped (T := T) (k := k) hu hz hℓ hfit hper).val.val).val (t,a,s) = 0
  rw [HierarchySmoothProfile.profilePhaseAverage_apply hT _ hx]
  exact envelopeWrapped_phaseMean (k := k) hu hz hℓ hfit hper hMean hx.1 a

/-- Copy of the private `wrapped_eq_on_centeredCell_of_radius`
(`PaperHierarchyUnswitchedRelay.lean:138`): on the label cell the twisted periodization of a
field supported in `|a| < 2ℓ` is the field itself. -/
theorem wrapped_eq_on_cell {E : Type*} [Zero E]
    {f : ℝ → Vec3 → ℝ → E} {t : ℝ} {a : Vec3}
    (ha : a ∈ centeredCell) (s : ℝ) (hfit : 2 * ℓ < 1 / 2)
    (hf : ∀ b, 2 * ℓ ≤ ‖b‖ → ∀ q, f t b q = 0) :
    phaseTwistedPeriodizeCentered k f t a s = f t a s := by
  refine phaseTwistedPeriodizeCentered_eq_on_centeredCell (sub_pos.mpr hfit) ?_ ha s
  rintro b ⟨i, hi⟩ q
  have hb : |b i| ≤ ‖b‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le b i
  exact hf b (by linarith) q

end Wrapped

section Leading

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3} {D lam t₀ : ℝ}
  {center : ℝ → Vec3} {amp : ℝ → Vec3 → Vec3}

set_option maxHeartbeats 1500000 in
/-- Copy of `exists_unswitched_wrapped_representatives` (`PaperHierarchyUnswitchedRelay.lean:91`)
for a seed `amp` in predicate form: smooth twisted profiles `V`, `p` on `[0,T]` with zero
phase average (resp. zero phase mean) whose values on `[t₀,T]` are the twisted
periodizations of `A₁ = g𝐚F_h` and `𝗉[A₁]`. The regularity of the coefficients comes from
the parent, that of the seed from `S5.IsSeed.smooth`. -/
theorem exists_leading_representatives (hP : S5.Parent T U X pU D lam)
    (hL : S5.Launch T X k lam t₀) (hamp : S5.IsSeed U X k t₀ T center amp)
    {ℓ h : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) :
    ∃ (V : HierarchyTwistedProfile T k Vec3) (p : HierarchyTwistedProfile T k ℝ),
      profilePhaseAverage (Bridge.Launch.end_pos hL) V = 0 ∧
      (∀ t ∈ Icc 0 T, ∀ a, phaseMean (fun s => p.val.val.val (t,a,s)) = 0) ∧
      ∀ t ∈ Icc t₀ T, ∀ a s,
        V.val.val.val (t,a,s) = phaseTwistedPeriodizeCentered k (S5.leading ℓ h amp) t a s ∧
        p.val.val.val (t,a,s) =
          phaseTwistedPeriodizeCentered k (S5.leadingPressure U X k ℓ h amp) t a s := by
  have hT := Bridge.Launch.end_pos hL
  have hI : Icc t₀ T ⊆ Icc 0 T := Bridge.Launch.active_subset hL
  have hκs := (Bridge.Parent.waveVector_smooth (k := k) hT hP).mono (prod_mono hI subset_rfl)
  have hMs := (Bridge.Parent.strainField_smooth hT hP).mono (prod_mono hI subset_rfl)
  let b (z : ℝ × Vec3) := -wavePressureCoefficient 1 (S5.waveVector X k z.1 z.2) (amp z.1 z.2)
    (S5.strainField U X z.1 z.2)
  have hb : ContDiffOn ℝ ∞ b (Icc t₀ T ×ˢ (univ : Set Vec3)) := by
    have hb₀ := (contDiffOn_const (c := (2 : ℝ))).mul
      (hκs.inner ℝ (hMs.clm_apply hamp.smooth))
    have hn (z : ℝ × Vec3) (hz : z ∈ Icc t₀ T ×ˢ (univ : Set Vec3)) :
        ‖S5.waveVector X k z.1 z.2‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr
        (Bridge.Parent.waveVector_ne_zero hT hP hL.carrier_ne_zero (hI hz.1) z.2))
    have hb₁ := (hb₀.div (ContDiffOn.norm_sq ℝ hκs) hn).neg
    simpa only [b, wavePressureCoefficient, mul_one, Function.uncurry, Pi.div_apply] using hb₁
  obtain ⟨Ue, hU, hUeq⟩ := exists_smoothExtensionOfClosedTimeSlab hL.start_lt isOpen_univ hamp.smooth
  obtain ⟨Q, hQ, hQeq⟩ := exists_smoothExtensionOfClosedTimeSlab hL.start_lt isOpen_univ hb
  have hUs : ContDiff ℝ ∞ Ue := contDiffOn_univ.mp (by simpa only [univ_prod_univ] using hU)
  have hQs : ContDiff ℝ ∞ Q := contDiffOn_univ.mp (by simpa only [univ_prod_univ] using hQ)
  have hv := contDiff_waveProfile hh hh₁
  have hq := contDiff_wavePressurePrimitive hh hh₁
  have hvper := periodic_waveProfile hh hh₁
  have hqper := periodic_wavePressurePrimitive hh hh₁
  let V : HierarchyTwistedProfile T k Vec3 := envelopeWrapped hUs hv hℓ hfit hvper
  let p : HierarchyTwistedProfile T k ℝ := envelopeWrapped hQs hq hℓ hfit hqper
  refine ⟨V, p, envelopeWrapped_average hT hUs hv hℓ hfit hvper
    (phaseMean_waveProfile hh hh₁), ?_, ?_⟩
  · intro t ht a
    exact envelopeWrapped_phaseMean hQs hq hℓ hfit hqper
      (phaseMean_wavePressurePrimitive hh hh₁) ht a
  · intro t ht a s
    have hFull : t ∈ Icc 0 T := hI ht
    constructor
    · rw [show V.val.val.val (t,a,s) = _ from envelopeWrapped_eval hUs hv hℓ hfit hvper hFull a s]
      simp only [phaseTwistedPeriodizeCentered]
      rw [hUeq (show (t,centeredLabel a) ∈ Icc t₀ T ×ˢ (univ : Set Vec3) from ⟨ht,mem_univ _⟩)]
      simp only [S5.leading, Function.uncurry_apply_pair, smul_smul]
    · rw [show p.val.val.val (t,a,s) = _ from envelopeWrapped_eval hQs hq hℓ hfit hqper hFull a s]
      simp only [phaseTwistedPeriodizeCentered]
      rw [hQeq (show (t,centeredLabel a) ∈ Icc t₀ T ×ˢ (univ : Set Vec3) from ⟨ht,mem_univ _⟩)]
      simp only [b, S5.leadingPressure, wavePressureCoefficient, mul_one, smul_eq_mul, div_eq_mul_inv]
      ring

/-- The phase derivative of `𝗉[A₁]` (copy of the private `deriv_leadingPressure`,
`PaperHierarchyLeadingEquation.lean:13`, for a seed in predicate form). -/
theorem deriv_leadingPressure {ℓ h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (t : ℝ) (a : Vec3) (s : ℝ) :
    deriv (S5.leadingPressure U X k ℓ h amp t a) s =
      (radialEnvelope ℓ a * waveProfile h s) *
        oscillatoryPressureSlope (S5.strainField U X t a) (S5.waveVector X k t a) 0 (amp t a) := by
  have hd := ((hasDerivAt_wavePressurePrimitive hh hh₁ s).const_mul
    (-wavePressureCoefficient (radialEnvelope ℓ a) (S5.waveVector X k t a) (amp t a)
      (S5.strainField U X t a))).deriv
  change deriv (S5.leadingPressure U X k ℓ h amp t a) s = _ at hd
  rw [hd]
  simp only [wavePressureCoefficient, oscillatoryPressureSlope, inner_zero_right, zero_sub,
    div_eq_mul_inv]
  ring

/-- **The leading equation (3.4)** for a seed in predicate form: copy of
`SeedOn.paper_hierarchy_leading_homogeneous` (`PaperHierarchyLeadingEquation.lean:42`, content
of row 5.5) and of `hasDerivWithinAt_leading_homogeneous_momentum` (:27), reading only the
seed equation (3.2) and the transversality of `S5.IsSeed`: on `[t₀,T]`,
`∂_tA₁ + MA₁ + ∂_s𝗉[A₁] κ = 0`, `κ·A₁ = 0`, and `A₁`, `𝗉[A₁]` have zero phase mean. -/
theorem leading_homogeneous (hamp : S5.IsSeed U X k t₀ T center amp) (hI : t₀ < T)
    {ℓ h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) {t : ℝ} (ht : t ∈ Icc t₀ T) (a : Vec3) (s : ℝ) :
    (derivWithin (fun u => S5.leading ℓ h amp u a s) (Icc t₀ T) t +
      S5.strainField U X t a (S5.leading ℓ h amp t a s) +
        deriv (S5.leadingPressure U X k ℓ h amp t a) s • S5.waveVector X k t a = 0) ∧
      ⟪S5.waveVector X k t a, S5.leading ℓ h amp t a s⟫_ℝ = 0 ∧
      phaseMean (S5.leading ℓ h amp t a) = 0 ∧
      phaseMean (S5.leadingPressure U X k ℓ h amp t a) = 0 := by
  have hmom : HasDerivWithinAt (fun u => S5.leading ℓ h amp u a s)
      (-S5.strainField U X t a (S5.leading ℓ h amp t a s) -
        deriv (S5.leadingPressure U X k ℓ h amp t a) s • S5.waveVector X k t a) (Icc t₀ T) t := by
    let c := radialEnvelope ℓ a * waveProfile h s
    have hAmp := (hamp.equation a t ht).const_smul c
    have hOp := affineWaveAmplitudeOperator_add_transverseProjection (S5.strainField U X t a)
      (S5.waveVector X k t a) 0 (amp t a)
    simp only [map_zero, add_zero, zero_sub] at hOp
    apply hAmp.congr_deriv
    rw [hOp, deriv_leadingPressure hh hh₁]
    simp only [c, S5.leading, map_smul, smul_sub, smul_neg, smul_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hmom.derivWithin (uniqueDiffOn_Icc hI t ht)]
    abel
  · simp only [S5.leading, real_inner_smul_right, hamp.transverse a t ht, mul_zero]
  · let L := ContinuousLinearMap.toSpanSingleton ℝ (radialEnvelope ℓ a • amp t a)
    have hL : S5.leading ℓ h amp t a = fun s => L (waveProfile h s) := by
      funext s
      change (radialEnvelope ℓ a * waveProfile h s) • amp t a =
        waveProfile h s • (radialEnvelope ℓ a • amp t a)
      rw [smul_smul, mul_comm]
    rw [hL, phaseMean, L.intervalIntegral_comp_comm
      ((contDiff_waveProfile hh hh₁).continuous.intervalIntegrable 0 1), ← phaseMean,
      phaseMean_waveProfile hh hh₁, map_zero]
  · change phaseMean (fun s =>
      (-wavePressureCoefficient (radialEnvelope ℓ a) (S5.waveVector X k t a) (amp t a)
        (S5.strainField U X t a)) • wavePressurePrimitive h s) = 0
    rw [phaseMean_const_smul, phaseMean_wavePressurePrimitive hh hh₁, smul_zero]

end Leading

end

end TorusEuler.Paper.Lib.S5a
