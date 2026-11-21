import TorusEuler.Paper.Proofs.S5b.Lemma58OddA
import TorusEuler.Paper.Proofs.S5b.Lemma58C2
import TorusEuler.Paper.Proofs.S5Bridge.Seed
import TorusEuler.Paper.Proofs.S5Bridge.Leading
import TorusEuler.FirstWaveLocalized
import TorusEuler.LocalizedSeedRegularity
import TorusEuler.PeriodicLift
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Lemma 5.8, oddness of `W^♮` (part 2): the reflected expansion is an expansion

For an odd parent, the reflection `ϱ` of `Lemma58OddA` (velocity profiles `f ↦ -f(t,-a,-s)`,
pressure profiles `f ↦ f(t,-a,-s)`) maps every expansion of §5.5 to an expansion with the same
data (`isExpansion_reflFamily`). Ingredients, all from the oddness of `U` and `R_U`:

* the coefficient profiles `(D_aX)⁻¹`, `M`, `κ` are even (`evenGeometry`, library
  `ParentGeometry.reflection`), `X(t,·)` is odd and `D_aX` is even;
* the seed is even in the label (`seed_even`: `𝐚(t,-a)` is again a seed, and seeds are unique,
  `Bridge.IsSeed.eqOn`), so `A₁ = g𝐚F_h` is odd and `𝗉[A₁]` is even in `(a,s)` (`F_h` odd,
  `P_h` even, `g` radial);
* the mean equation (5.11) and the transverse equation (5.15) are preserved
  (`meanSolution_vrefl`, `transverseSolution_vrefl`), and so are the sources (5.25)–(5.28)
  (`levelSource_vrefl`, `oscSource_vrefl`, `suppSource_vrefl`, `meanSource_vrefl`).
-/

open Set MeasureTheory
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.S5b

open HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {pU : Pressure} {D lam t₀ : ℝ}
  {center : ℝ → Vec3}

/-! ## Symmetry of the label cell and of the phase mean (copies of private library glue) -/

/-- The label cell is symmetric (copy of the private
`endpointParity_neg_preimage_centeredCell`, `TorusEuler/EndpointPhysicalMeanParity.lean:289`). -/
theorem neg_preimage_centeredCell : (fun x : Vec3 => -x) ⁻¹' centeredCell = centeredCell := by
  ext x
  change (∀ i, (-x) i ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) ↔
    (∀ i, x i ∈ Icc (-(1 / 2 : ℝ)) (1 / 2))
  simp only [PiLp.neg_apply, mem_Icc, ← abs_le, abs_neg]

/-- `-a` lies in the label cell with `a`. -/
theorem neg_mem_centeredCell {a : Vec3} (ha : a ∈ centeredCell) : -a ∈ centeredCell := by
  have h : a ∈ (fun x : Vec3 => -x) ⁻¹' centeredCell := by rw [neg_preimage_centeredCell]; exact ha
  exact h

/-- The cell integral is invariant under `a ↦ -a` (copy of the private
`endpointParity_integral_reflect_centeredCell`, `TorusEuler/EndpointPhysicalMeanParity.lean:296`). -/
theorem integral_centeredCell_neg (p : Vec3 → ℝ) :
    (∫ x in centeredCell, p (-x)) = ∫ x in centeredCell, p x := by
  have hMeasure := (Measure.measurePreserving_neg (volume : Measure Vec3)).restrict_preimage
    isCompact_centeredCell.measurableSet
  rw [neg_preimage_centeredCell] at hMeasure
  exact hMeasure.integral_comp (Homeomorph.neg Vec3).measurableEmbedding p

/-- The phase mean of a `1`-periodic function is invariant under `s ↦ -s` (copy of the private
`HierarchyTwistedProfile.phaseMean_reflect`, `TorusEuler/HierarchyTwistedProfiles.lean:717`, for
any normed space). -/
theorem phaseMean_comp_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : Function.Periodic f 1) : phaseMean (fun s => f (-s)) = phaseMean f := by
  unfold phaseMean
  rw [intervalIntegral.integral_comp_neg, neg_zero]
  simpa only [neg_add_cancel, zero_add] using hf.intervalIntegral_add_eq (-1) 0

/-! ## Parities of an odd parent -/

section Parent

variable (hT : 0 < T) (hP : S5.Parent T U X pU D lam)
include hT hP

/-- `X(t,·)` (from time `0` to `t`) is odd. -/
theorem flow_odd {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) : X 0 t (-a) = -X 0 t a := by
  obtain ⟨K, hK⟩ := Bridge.Parent.exists_lipschitz hT hP
  exact hP.flow.odd hK hP.velocity_odd (left_mem_Icc.mpr hT.le) ht a

/-- `D_aX(t,·)` is even. -/
theorem deformation_even {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) :
    fderiv ℝ (X 0 t) (-a) = fderiv ℝ (X 0 t) a := by
  obtain ⟨K, hK⟩ := Bridge.Parent.exists_lipschitz hT hP
  exact even_fderiv_of_odd (hP.flow.odd hK hP.velocity_odd (left_mem_Icc.mpr hT.le) ht) a

/-- `κ(t,·)` is even. -/
theorem waveVector_neg {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) :
    S5.waveVector X k t (-a) = S5.waveVector X k t a := by
  obtain ⟨K, hK⟩ := Bridge.Parent.exists_lipschitz hT hP
  exact (hP.flow.even_materialGradient_and_labelWaveVector hK hP.velocity_odd
    (left_mem_Icc.mpr hT.le) ht k).2 a

/-- `M(t,·)` is even. -/
theorem strainField_neg {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) :
    S5.strainField U X t (-a) = S5.strainField U X t a := by
  obtain ⟨K, hK⟩ := Bridge.Parent.exists_lipschitz hT hP
  exact (hP.flow.even_materialGradient_and_labelWaveVector hK hP.velocity_odd
    (left_mem_Icc.mpr hT.le) ht (0 : Vec3)).1 a

/-- The coefficient profiles of an odd parent are even (library `ParentGeometry.reflection`). -/
theorem evenGeometry (d : ParentGeometry hT U X k) : EvenGeometry d :=
  let h := d.reflection hP.flow hP.velocity_smooth hP.velocity_periodic hP.velocity_odd
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- **The seed is even in the label**: `𝐚(t,-a) = 𝐚(t,a)` on `[t₀,T]`, since `𝐚(t,-a)` solves
(3.2) with (5.4) (the coefficients `M`, `κ` are even) and the seed is unique. -/
theorem seed_even (hL : S5.Launch T X k lam t₀) {amp : ℝ → Vec3 → Vec3}
    (hamp : S5.IsSeed U X k t₀ T center amp) : ∀ t ∈ Icc t₀ T, ∀ a, amp t (-a) = amp t a := by
  have hR : S5.IsSeed U X k t₀ T center (fun t a => amp t (-a)) :=
    { at_origin := fun t ht => by
        show amp t (-0) = center t
        rw [neg_zero]
        exact hamp.at_origin t ht
      start := fun a => by
        show amp t₀ (-a) = _
        rw [hamp.start (-a), waveVector_neg hT hP (Bridge.Launch.start_mem hL) a]
      equation := fun a t ht => by
        have h := hamp.equation (-a) t ht
        rwa [strainField_neg hT hP (Bridge.Launch.active_subset hL ht) a,
          waveVector_neg hT hP (Bridge.Launch.active_subset hL ht) a] at h
      transverse := fun a t ht => by
        show ⟪S5.waveVector X k t a, amp t (-a)⟫_ℝ = 0
        rw [← waveVector_neg hT hP (Bridge.Launch.active_subset hL ht) a]
        exact hamp.transverse (-a) t ht
      smooth := hamp.smooth.comp (contDiffOn_fst.prodMk contDiffOn_snd.neg)
        (fun z hz => ⟨hz.1, mem_univ _⟩) }
  exact Bridge.IsSeed.eqOn hP hL hR hamp

/-- `A₁ = g𝐚F_h` is odd in `(a,s)` on `[t₀,T]`. -/
theorem leading_neg (hL : S5.Launch T X k lam t₀) {amp : ℝ → Vec3 → Vec3}
    (hamp : S5.IsSeed U X k t₀ T center amp) {ℓ h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) {t : ℝ}
    (ht : t ∈ Icc t₀ T) (a : Vec3) (s : ℝ) :
    S5.leading ℓ h amp t (-a) (-s) = -S5.leading ℓ h amp t a s := by
  simp only [S5.leading]
  rw [radialEnvelope_neg, odd_waveProfile hh hh₁ s, seed_even hT hP hL hamp t ht a, mul_neg,
    neg_smul]

/-- `𝗉[A₁] = -p_w g P_h` is even in `(a,s)` on `[t₀,T]`. -/
theorem leadingPressure_neg (hL : S5.Launch T X k lam t₀) {amp : ℝ → Vec3 → Vec3}
    (hamp : S5.IsSeed U X k t₀ T center amp) {ℓ h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) {t : ℝ}
    (ht : t ∈ Icc t₀ T) (a : Vec3) (s : ℝ) :
    S5.leadingPressure U X k ℓ h amp t (-a) (-s) = S5.leadingPressure U X k ℓ h amp t a s := by
  have ht' := Bridge.Launch.active_subset hL ht
  simp only [S5.leadingPressure]
  rw [radialEnvelope_neg, waveVector_neg hT hP ht' a, seed_even hT hP hL hamp t ht a,
    strainField_neg hT hP ht' a, even_wavePressurePrimitive hh hh₁ s]

end Parent

/-! ## The mean and transverse equations are preserved -/

section Solutions

variable {hT : 0 < T} {d : ParentGeometry hT U X k}

set_option maxHeartbeats 1000000 in
/-- **(5.11) is preserved**: if `(B, q̄)` solves the mean equation with source `f̄`, then
`(ϱB, q̄ ∘ reflection)` solves it with source `ϱf̄` (displacement `-z(t,-a)`, velocity `-v(t,-a)`). -/
theorem meanSolution_vrefl (hP : S5.Parent T U X pU D lam) (hd : EvenGeometry d)
    {f B : HierarchyTwistedProfile T k Vec3} {q : HierarchyTwistedProfile T k ℝ}
    (h : S5.MeanSolution d f B q) :
    S5.MeanSolution d (vrefl f) (vrefl B) (reflection q) where
  momentum := by rw [material_vrefl hd, labelGrad_reflection hd, ← map_add vrefl, h.momentum]
  phase_independent := by rw [average_vrefl, h.phase_independent]
  pressure_phase_independent := by
    rw [phaseGrad_reflection hd, h.pressure_phase_independent, map_zero]
  endpoint := by
    obtain ⟨v, z, hv, hz, hper, hz0, hzT, hder, hdiv, hB⟩ := h.endpoint
    have hneg : ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 => (p.1, -p.2)) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
      contDiffOn_fst.prodMk contDiffOn_snd.neg
    have hmaps : MapsTo (fun p : ℝ × Vec3 => (p.1, -p.2)) (Icc 0 T ×ˢ (univ : Set Vec3))
        (Icc 0 T ×ˢ (univ : Set Vec3)) := fun p hp => ⟨hp.1, mem_univ _⟩
    have hperneg {w : Vec3 → Vec3} (hw : SpatiallyPeriodic w) :
        SpatiallyPeriodic (fun a => -w (-a)) := by
      intro n x
      change -w (-(x + latticeVector n)) = -w (-x)
      rw [← hw n (-(x + latticeVector n))]
      congr 2
      abel
    refine ⟨fun t a => -v t (-a), fun t a => -z t (-a), (hv.comp hneg hmaps).neg,
      (hz.comp hneg hmaps).neg, fun t ht => ⟨hperneg (hper t ht).1, hperneg (hper t ht).2⟩, ?_, ?_,
      fun t ht a => (hder t ht (-a)).neg, fun t ht a => ?_, fun t ht a s => ?_⟩
    · funext a
      simp [hz0]
    · funext a
      simp [hzT]
    · have hfd : fderiv ℝ (fun b => -v t (-b)) a = fderiv ℝ (v t) (-a) := by
        rw [fderiv_fun_neg, fderiv_comp_neg' (v t) a, neg_neg]
      unfold divergence
      rw [hfd]
      exact hdiv t ht (-a)
    · rw [vrefl_eval]
      simp only [hierarchyProfileReflection_apply]
      rw [hB t ht (-a) (-s), deformation_even hT hP ht a, map_neg]

set_option maxHeartbeats 1000000 in
/-- **(5.15) is preserved**: if `(V, 𝗉)` solves the transverse equation from zero with source `f`,
then `(ϱV, 𝗉 ∘ reflection)` solves it with source `ϱf`. -/
theorem transverseSolution_vrefl (hP : S5.Parent T U X pU D lam) (hd : EvenGeometry d)
    {f V : HierarchyTwistedProfile T k Vec3} {q : HierarchyTwistedProfile T k ℝ}
    (h : S5.TransverseSolution d f V q) :
    S5.TransverseSolution d (vrefl f) (vrefl V) (reflection q) where
  momentum := by rw [material_vrefl hd, phaseGrad_reflection hd, ← map_add vrefl, h.momentum]
  transverse := fun t ht a s => by
    rw [vrefl_eval]
    simp only [hierarchyProfileReflection_apply]
    rw [inner_neg_right, ← waveVector_neg hT hP ht a, h.transverse t ht (-a) (-s), neg_zero]
  mean_zero := by rw [average_vrefl, h.mean_zero, map_zero]
  initial := fun a s => by
    rw [vrefl_eval]
    simp only [hierarchyProfileReflection_apply]
    rw [h.initial, neg_zero]
  pressure_mean_zero := fun t ht a => by
    simp only [reflection_eval, hierarchyProfileReflection_apply]
    rw [phaseMean_comp_neg (f := fun s => q.val.val.val (t, -a, s))
      (HierarchyPeriodicProfile.phasePeriodic q.val t (-a))]
    exact h.pressure_mean_zero t ht (-a)

end Solutions

/-! ## The reflected family and its sources -/

section Family

/-- The reflected family: `ϱV_p`, `ϱC_p`, `ϱB_p`, `𝗉_p ∘ reflection`, `q̄_p ∘ reflection`. -/
def reflFamily
    (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)) :
    HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ) where
  V i := vrefl (u.V i)
  C i := vrefl (u.C i)
  B i := vrefl (u.B i)
  p i := reflection (u.p i)
  q i := reflection (u.q i)

variable (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ))

/-- The `V` component of the reflected family. -/
@[simp] theorem reflFamily_V (i : ℕ) : (reflFamily u).V i = vrefl (u.V i) := rfl
@[simp] theorem reflFamily_B (i : ℕ) : (reflFamily u).B i = vrefl (u.B i) := rfl
@[simp] theorem reflFamily_p (i : ℕ) : (reflFamily u).p i = reflection (u.p i) := rfl
@[simp] theorem reflFamily_q (i : ℕ) : (reflFamily u).q i = reflection (u.q i) := rfl

theorem Cd_reflFamily (i : ℕ) : S5.Cd (reflFamily u) i = vrefl (S5.Cd u i) := rfl

/-- `Yd` commutes with the reflection of a family. -/
theorem Yd_reflFamily (i : ℕ) : S5.Yd (reflFamily u) i = vrefl (S5.Yd u i) := by
  simp only [S5.Yd, Cd_reflFamily, reflFamily_V, map_add]

/-- `Zd` commutes with the reflection of a family. -/
theorem Zd_reflFamily (i : ℕ) : S5.Zd (reflFamily u) i = vrefl (S5.Zd u i) := by
  simp only [S5.Zd, Yd_reflFamily, reflFamily_B, map_add]

variable {hT : 0 < T} {d : ParentGeometry hT U X k}

set_option maxHeartbeats 4000000 in
/-- `H_p` of the reflected family is the reflection of `H_p`, (5.25)–(5.26). -/
theorem levelSource_vrefl (hd : EvenGeometry d) (cS : HierarchyTwistedProfile T k Vec3) (p : ℕ) :
    S5.levelSource (S5.ops d) (reflFamily u) (vrefl cS) p =
      vrefl (S5.levelSource (S5.ops d) u cS p) := by
  have hite : (if p = 2 then vrefl cS else 0) = vrefl (if p = 2 then cS else 0) := by
    split_ifs <;> simp
  simp only [S5.levelSource, Cd_reflFamily, Zd_reflFamily, Yd_reflFamily, reflFamily_p,
    material_vrefl hd, labelGrad_reflection hd, labelAdv_vrefl hd, phaseAdv_vrefl hd, hite,
    map_add, map_sub, map_sum]

set_option maxHeartbeats 1000000 in
/-- `f_p` of the reflected family is the reflection of `f_p`, (5.27). -/
theorem oscSource_vrefl (hd : EvenGeometry d) (cS : HierarchyTwistedProfile T k Vec3) (p : ℕ) :
    S5.oscSource (S5.ops d) (reflFamily u) (vrefl cS) p =
      vrefl (S5.oscSource (S5.ops d) u cS p) := by
  simp only [S5.oscSource, levelSource_vrefl u hd, average_vrefl, map_sub, map_neg]

set_option maxHeartbeats 1000000 in
/-- `f_p^S` of the reflected family is the reflection of `f_p^S`, (5.28). -/
theorem suppSource_vrefl (hd : EvenGeometry d) (p : ℕ) :
    S5.suppSource (S5.ops d) (reflFamily u) p = vrefl (S5.suppSource (S5.ops d) u p) := by
  simp only [S5.suppSource, Yd_reflFamily, reflFamily_B, phaseAdv_vrefl hd, map_neg, map_sum]

set_option maxHeartbeats 1000000 in
/-- `f̄_p` of the reflected family (with `ϱR_U∘X`) is the reflection of `f̄_p`, (5.27). -/
theorem meanSource_vrefl (hd : EvenGeometry d) (cS R : HierarchyTwistedProfile T k Vec3) (p : ℕ) :
    S5.meanSource (S5.ops d) (reflFamily u) (vrefl cS) (vrefl R) p =
      vrefl (S5.meanSource (S5.ops d) u cS R p) := by
  have hite : (if p = 2 then vrefl R else 0) = vrefl (if p = 2 then R else 0) := by
    split_ifs <;> simp
  simp only [S5.meanSource, levelSource_vrefl u hd, average_vrefl, hite, map_sub, map_neg]

end Family

/-! ## The reflected expansion -/

section Expansion

variable {hT : 0 < T} {d : ParentGeometry hT U X k}

/-- `⟨V₁⟩ = 0`: `V₁` agrees on the cell with the bridge profile of `χ̃A₁`
(`Bridge.leadingVelocityProfile`), whose phase average vanishes. -/
theorem average_first (hL : S5.Launch T X k lam t₀) {amp : ℝ → Vec3 → Vec3}
    (hamp : S5.IsSeed U X k t₀ T center amp) {χ : PaperWaveCutoff t₀ T} {ℓ h : ℝ} (hℓ : 0 < ℓ)
    (hfit : 2 * ℓ < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) {P : ℕ}
    {R S : HierarchyTwistedProfile T k Vec3}
    {u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)}
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) : (S5.ops d).average (u.V 1) = 0 := by
  have heq : u.V 1 =
      Bridge.leadingVelocityProfile hL hamp hℓ hfit hh hh₁ χ.value χ.smooth χ.zero_before :=
    Lib.S5Bridge.eq_of_centeredCell fun t ht a ha s => by
      rw [hu.leading_velocity t ht a ha s, Bridge.leadingVelocityProfile_cell_eval hL hamp hℓ
        hfit hh hh₁ χ.value χ.smooth χ.zero_before ht ha s]
  rw [heq]
  exact Bridge.leadingVelocityProfile_average d hL hamp hℓ hfit hh hh₁ χ.value χ.smooth
    χ.zero_before

set_option maxHeartbeats 2000000 in
/-- **The reflected family is an expansion with the same data** (`R ↦ ϱR`, `S ↦ ϱS`): every
clause of `S5.IsExpansion` is preserved by the symmetry `(a,s) ↦ (-a,-s)`. -/
theorem isExpansion_reflFamily (hP : S5.Parent T U X pU D lam) (hL : S5.Launch T X k lam t₀)
    {amp : ℝ → Vec3 → Vec3} (hamp : S5.IsSeed U X k t₀ T center amp)
    {χ : PaperWaveCutoff t₀ T} {ℓ h : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) (hh : 0 < h)
    (hh₁ : h ≤ 1) {P : ℕ} {R S : HierarchyTwistedProfile T k Vec3}
    {u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)}
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) :
    S5.IsExpansion d pU χ ℓ h amp P (vrefl R) (vrefl S) (reflFamily u) := by
  have hd := evenGeometry hT hP d
  have hS := activation_average d hℓ hfit hh hh₁ hu
  have hcS : S5.curlCorrection d (vrefl S) = vrefl (S5.curlCorrection d S) :=
    curlCorrection_vrefl hd S hS
  have hact (t : ℝ) (ht : t ∈ Icc 0 T) (htt : ¬t < t₀) : t ∈ Icc t₀ T := ⟨not_lt.mp htt, ht.2⟩
  refine
    { residual := fun z hz => ?_
      activation := fun t ht a ha s => ?_
      leading_velocity := fun t ht a ha s => ?_
      leading_pressure := fun t ht a ha s => ?_
      first_correction := ?_
      first_mean := ?_
      correction := fun p hp => ?_
      mean := fun p hp => ?_
      transverse := fun p hp => ?_
      top := ?_ }
  · obtain ⟨t, a, s⟩ := z
    have ht : t ∈ Icc 0 T := hz.1
    rw [vrefl_eval]
    simp only [hierarchyProfileReflection_apply]
    rw [hu.residual (t, -a, -s) ⟨ht, mem_univ _⟩]
    simp only
    rw [flow_odd hT hP ht a, hP.residual_odd t ht, neg_neg]
  · rw [vrefl_eval]
    simp only [hierarchyProfileReflection_apply]
    rw [hu.activation t ht (-a) (neg_mem_centeredCell ha) (-s)]
    by_cases htt : t < t₀
    · rw [χ.derivative_zero_before hT ht htt, zero_smul, zero_smul, neg_zero]
    · rw [leading_neg hT hP hL hamp hh hh₁ (hact t ht htt) a s, smul_neg, neg_neg]
  · rw [reflFamily_V, vrefl_eval]
    simp only [hierarchyProfileReflection_apply]
    rw [hu.leading_velocity t ht (-a) (neg_mem_centeredCell ha) (-s)]
    by_cases htt : t < t₀
    · rw [χ.zero_before t ht htt, zero_smul, zero_smul, neg_zero]
    · rw [leading_neg hT hP hL hamp hh hh₁ (hact t ht htt) a s, smul_neg, neg_neg]
  · rw [reflFamily_p, reflection_eval]
    simp only [hierarchyProfileReflection_apply]
    rw [hu.leading_pressure t ht (-a) (neg_mem_centeredCell ha) (-s)]
    by_cases htt : t < t₀
    · rw [χ.zero_before t ht htt, zero_mul, zero_mul]
    · rw [leadingPressure_neg hT hP hL hamp hh hh₁ (hact t ht htt) a s]
  · rw [Cd_reflFamily, hu.first_correction, map_zero]
  · exact ⟨by rw [reflFamily_B, hu.first_mean.1, map_zero],
      by rw [reflFamily_q, hu.first_mean.2, map_zero]⟩
  · have hmean : (S5.ops d).average (u.V p) = 0 := by
      rcases Nat.lt_or_ge p 2 with hp1 | hp2
      · have h1 : p = 1 := by simp only [Finset.mem_Icc] at hp; omega
        rw [h1]
        exact average_first hL hamp hℓ hfit hh hh₁ hu
      · exact (hu.transverse p (Finset.mem_Icc.mpr ⟨hp2, (Finset.mem_Icc.mp hp).2⟩)).mean_zero
    rw [Cd_reflFamily, hu.correction p hp, reflFamily_V, curlCorrection_vrefl hd _ hmean]
  · obtain ⟨hm, hn⟩ := hu.mean p hp
    refine ⟨?_, fun t ht => ?_⟩
    · rw [hcS, meanSource_vrefl u hd, reflFamily_B, reflFamily_q]
      exact meanSolution_vrefl hP hd hm
    · rw [reflFamily_q]
      simp only [reflection_eval, hierarchyProfileReflection_apply, neg_zero]
      rw [integral_centeredCell_neg (fun a => (u.q p).val.val.val (t, a, 0))]
      exact hn t ht
  · rw [hcS, oscSource_vrefl u hd, suppSource_vrefl u hd, ← map_add vrefl, reflFamily_V,
      reflFamily_p]
    exact transverseSolution_vrefl hP hd (hu.transverse p hp)
  · exact ⟨by rw [reflFamily_V, hu.top.1, map_zero], by rw [reflFamily_B, hu.top.2, map_zero]⟩

end Expansion

end

end TorusEuler.Paper.S5b
