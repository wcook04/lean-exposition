import TorusEuler.HierarchyPhysicalSolvers
import TorusEuler.HierarchyLinearRelayBounds

/-! The actual projected equations for the transverse time estimates. -/

open Set ContinuousLinearMap
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)
local notation "SP" => HierarchyTwistedProfile T k ℝ
local notation "LP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] ℝ)
local notation "I" => Icc (0 : ℝ) T
local notation "J" => Set.prod I (univ : Set Vec3)

/-- A phase-independent coefficient is bundled from its periodic label slices. -/
def ofSmoothPeriodicLabelSlices {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → Vec3 → E) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (f t)) : HierarchyTwistedProfile T k E := by
  let q : HierarchySmoothProfile T E := HierarchySmoothProfile.ofSmooth (fun x => f x.1 x.2.1)
    (hf.comp (contDiff_fst.prodMk contDiff_snd.fst).contDiffOn
      (fun x hx => ⟨hx.1, mem_univ x.2.1⟩))
  have hq (t : ℝ) (ht : t ∈ I) (a : Vec3) (s : ℝ) : q.val (t,a,s) = f t a :=
    HierarchySmoothProfile.ofSmooth_apply _ ⟨ht, mem_univ _⟩
  let p := HierarchyPeriodicProfile.ofPeriodicSlices q (fun t ht a s => by
    change q.val (t,a,s + 1) = q.val (t,a,s)
    rw [hq t ht a (s + 1), hq t ht a s])
  exact ofTwistedSlices p (fun t ht a s m => by
    change q.val (t,a + latticeVector m,s + ⟪k, latticeVector m⟫_ℝ) = q.val (t,a,s)
    rw [hq t ht, hq t ht]
    exact hper t ht m a)

@[simp] theorem ofSmoothPeriodicLabelSlices_eval {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → Vec3 → E) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (f t)) (t : ℝ) (ht : t ∈ I) (a : Vec3) (s : ℝ) :
    (ofSmoothPeriodicLabelSlices (k := k) f hf hper).val.val.val (t, a, s) = f t a := by
  have hs : ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint => f x.1 x.2.1) (hierarchyProfileSlab T) :=
    hf.comp (contDiff_fst.prodMk contDiff_snd.fst).contDiffOn
      (fun x hx => ⟨hx.1, mem_univ x.2.1⟩)
  exact HierarchySmoothProfile.ofSmooth_apply hs ⟨ht, mem_univ _⟩

/-- The four label coefficients in the selected projected velocity and normalized
phase pressure equations. Only the latter two use carrier normalization. -/
structure TransverseTimeCoefficients {M : MP} {κ : VP}
    (d : TransverseCoefficients M κ) (freq : ℝ) where
  velocity : MP
  source : MP
  pressureVelocity : LP
  pressureSource : LP
  velocity_value : ∀ t ∈ I, ∀ a s, velocity.val.val.val (t,a,s) =
    affineWaveAmplitudeOperator (d.strain t a) (d.covector t a)
  source_value : ∀ t ∈ I, ∀ a s, source.val.val.val (t,a,s) =
    oscillatoryTransverseProjection (d.covector t a)
  pressureVelocity_value : ∀ t ∈ I, ∀ a s, pressureVelocity.val.val.val (t,a,s) =
    hierarchyRelayPressureAmplitudeCoefficient (d.strain t a) (freq⁻¹ • d.covector t a)
  pressureSource_value : ∀ t ∈ I, ∀ a s, pressureSource.val.val.val (t,a,s) =
    hierarchyRelayPressureSourceCoefficient (freq⁻¹ • d.covector t a)

/-- The exact affine generator, projection, and normalized pressure
coefficients are jointly smooth on the entire parent slab. -/
theorem contDiffOn_transverseTimeCoefficients {M : MP} {κ : VP}
    (d : TransverseCoefficients M κ) (freq : ℝ) (hfreq : freq ≠ 0) :
    ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => affineWaveAmplitudeOperator (d.strain q.1 q.2)
      (d.covector q.1 q.2)) J ∧
    ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => oscillatoryTransverseProjection (d.covector q.1 q.2)) J ∧
    ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => hierarchyRelayPressureAmplitudeCoefficient
      (d.strain q.1 q.2) (freq⁻¹ • d.covector q.1 q.2)) J ∧
    ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => hierarchyRelayPressureSourceCoefficient
      (freq⁻¹ • d.covector q.1 q.2)) J := by
  let v (q : ℝ × Vec3) := d.covector q.1 q.2
  let w (q : ℝ × Vec3) := freq⁻¹ • v q
  have hv : ContDiffOn ℝ ∞ v J := d.covector_smooth
  have hw : ContDiffOn ℝ ∞ w J := hv.const_smul _
  have hM := d.strain_smooth
  have hvne (q : ℝ × Vec3) (hq : q ∈ J) : v q ≠ 0 := by
    have hk := d.covector_ne_zero q.1 hq.1 q.2
    rwa [d.covector_value _ ⟨hq.1, mem_univ _⟩] at hk
  let L := (innerSL ℝ : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ)
  have hL : ContDiffOn ℝ ∞ (fun q => L (v q)) J := L.contDiff.comp_contDiffOn hv
  have hRank : ContDiffOn ℝ ∞ (fun q => InnerProductSpace.rankOne ℝ (v q) (v q)) J :=
    (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := Vec3) (F := Vec3)).contDiff.comp_contDiffOn
      (hL.prodMk hv)
  have hvnorm : ContDiffOn ℝ ∞ (fun q => ‖v q‖ ^ 2) J := hv.norm_sq ℝ
  have hwnorm : ContDiffOn ℝ ∞ (fun q => (‖w q‖ ^ 2)⁻¹) J :=
    (hw.norm_sq ℝ).inv fun q hq => pow_ne_zero _ (norm_ne_zero_iff.mpr
      (smul_ne_zero (inv_ne_zero hfreq) (hvne q hq)))
  have hvN (q : ℝ × Vec3) (hq : q ∈ J) : ‖v q‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (hvne q hq))
  have hwL : ContDiffOn ℝ ∞ (fun q => L (w q)) J := L.contDiff.comp_contDiffOn hw
  refine ⟨hM.neg.add (((contDiffOn_const (c := (2 : ℝ))).div hvnorm hvN).smul
    (hRank.clm_comp hM)), contDiffOn_const.sub ((hvnorm.inv hvN).smul hRank), ?_, ?_⟩
  · exact (((contDiffOn_const (c := (-2 : ℝ))).mul hwnorm).smul (hwL.clm_comp hM))
  · exact hwnorm.smul hwL

/-- The time estimate uses the coefficients of the actual selected solve. -/
def TransverseCoefficients.timeCoefficients {M : MP} {κ : VP}
    (d : TransverseCoefficients M κ) (freq : ℝ) (hfreq : freq ≠ 0) :
    TransverseTimeCoefficients d freq := by
  obtain ⟨hA, hB, hC, hD⟩ := contDiffOn_transverseTimeCoefficients d freq hfreq
  let A (t : ℝ) (a : Vec3) := affineWaveAmplitudeOperator (d.strain t a) (d.covector t a)
  let B (t : ℝ) (a : Vec3) := oscillatoryTransverseProjection (d.covector t a)
  let C (t : ℝ) (a : Vec3) := hierarchyRelayPressureAmplitudeCoefficient
    (d.strain t a) (freq⁻¹ • d.covector t a)
  let D (t : ℝ) (a : Vec3) := hierarchyRelayPressureSourceCoefficient (freq⁻¹ • d.covector t a)
  have hAp : ∀ t ∈ I, SpatiallyPeriodic (A t) := fun t ht n a => by
    simp only [A, d.strain_periodic t ht n a, d.covector_periodic t ht n a]
  have hBp : ∀ t ∈ I, SpatiallyPeriodic (B t) := fun t ht n a => by
    simp only [B, d.covector_periodic t ht n a]
  have hCp : ∀ t ∈ I, SpatiallyPeriodic (C t) := fun t ht n a => by
    simp only [C, d.strain_periodic t ht n a, d.covector_periodic t ht n a]
  have hDp : ∀ t ∈ I, SpatiallyPeriodic (D t) := fun t ht n a => by
    simp only [D, d.covector_periodic t ht n a]
  exact ⟨ofSmoothPeriodicLabelSlices A hA hAp, ofSmoothPeriodicLabelSlices B hB hBp,
    ofSmoothPeriodicLabelSlices C hC hCp, ofSmoothPeriodicLabelSlices D hD hDp,
    ofSmoothPeriodicLabelSlices_eval A hA hAp, ofSmoothPeriodicLabelSlices_eval B hB hBp,
    ofSmoothPeriodicLabelSlices_eval C hC hCp, ofSmoothPeriodicLabelSlices_eval D hD hDp⟩

private theorem oscillatoryPressureSlope_at_normalized_covector {freq : ℝ} (hf : 0 < freq)
    (M : Vec3 →L[ℝ] Vec3) (κ f v : Vec3) :
    oscillatoryPressureSlope M (freq⁻¹ • κ) f v = freq * oscillatoryPressureSlope M κ f v := by
  simp only [oscillatoryPressureSlope, real_inner_smul_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hf)]
  by_cases hκ : ‖κ‖ = 0
  · simp [hκ]
  · field_simp [hf.ne', hκ]

/-- The pressure has been eliminated using the exact normalized slope of the
same selected transverse solution. -/
theorem TransverseResult.velocity_projectedEquation {hT : 0 < T} {G M : MP} {κ F : VP}
    (r : TransverseResult hT G M κ F) {d : TransverseCoefficients M κ} {freq : ℝ}
    (c : TransverseTimeCoefficients d freq) (t : ℝ) (ht : t ∈ I) (a : Vec3) (s : ℝ) :
    HasDerivWithinAt (fun u => r.output.V.val.val.val (u,a,s))
      (c.velocity.val.val.val (t,a,s) (r.output.V.val.val.val (t,a,s)) +
        c.source.val.val.val (t,a,s) (F.val.val.val (t,a,s))) I t := by
  have h := r.velocity_equation t ht a s
  rw [(r.pressure_slope t ht a s).deriv, d.strain_value (t,a,0) ⟨ht, mem_univ _⟩,
    d.covector_value (t,a,0) ⟨ht, mem_univ _⟩] at h
  rw [c.velocity_value t ht a s, c.source_value t ht a s,
    affineWaveAmplitudeOperator_add_transverseProjection]
  exact h

/-- Normalizing by the central carrier leaves phase-independent coefficient maps
of the existing strain and normalized covector. -/
theorem TransverseResult.pressure_normalized_slope {hT : 0 < T} {G M : MP} {κ F : VP}
    (r : TransverseResult hT G M κ F) {d : TransverseCoefficients M κ} {freq : ℝ}
    (hf : 0 < freq) (c : TransverseTimeCoefficients d freq)
    (t : ℝ) (ht : t ∈ I) (a : Vec3) (s : ℝ) :
    HasDerivAt (fun z => freq • r.output.p.val.val.val (t,a,z))
      (c.pressureVelocity.val.val.val (t,a,s) (r.output.V.val.val.val (t,a,s)) +
        c.pressureSource.val.val.val (t,a,s) (F.val.val.val (t,a,s))) s := by
  have hs := (r.pressure_slope t ht a s).const_smul freq
  rw [d.strain_value (t,a,0) ⟨ht, mem_univ _⟩, d.covector_value (t,a,0) ⟨ht, mem_univ _⟩] at hs
  rw [c.pressureVelocity_value t ht a s, c.pressureSource_value t ht a s,
    ← oscillatoryPressureSlope_eq_coefficients, oscillatoryPressureSlope_at_normalized_covector hf]
  exact hs

end

end TorusEuler.HierarchyTwistedProfile
