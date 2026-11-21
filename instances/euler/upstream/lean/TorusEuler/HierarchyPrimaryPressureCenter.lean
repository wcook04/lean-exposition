import TorusEuler.HierarchyPhysicalGraph
import TorusEuler.InductionChildEstimates
import TorusEuler.LaterWaveHierarchyInput
import TorusEuler.SeedDerivativeBudgets

/-! The physical pressure and central derivative of the actual later leading wave. -/

open ContinuousLinearMap Filter InnerProductSpace Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.LocalizedAmplitude.SeedOn

noncomputable section

variable {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3}
  {center : ℝ → Vec3} {t₀ T ell D C r h : ℝ}
  {w : SeedOn M κ center t₀ T ell D C}

local notation "Hess[" f "]" => fderiv ℝ (gradient f)

private theorem slice_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → Vec3 → E} {I : Set ℝ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (I ×ˢ (univ : Set Vec3)))
    {t : ℝ} (ht : t ∈ I) : ContDiff ℝ ∞ (f t) :=
  hf.comp_contDiff (f := fun a : Vec3 => (t, a)) (contDiff_const.prodMk contDiff_id)
    (fun a => ⟨ht, mem_univ a⟩)

/-- The selected leading velocity has the original localized Eulerian
readout on the entire lift. -/
theorem twistedLeading_graph_eq_localized (d : w.HierarchyRegularity r h)
    (A : Velocity) (k : Vec3) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HierarchyTwistedProfile.graphRead A (twistedLeading d k) t =
      localizedTransportedProfile A k (w.switchedLeading r h) t := by
  funext x
  change (twistedLeading d k).val.val.val (t, A t x, ⟪k, A t x⟫_ℝ) = _
  rw [twistedLeading_eval d k ht, phaseTwistedPeriodizeCentered_on_graph]

/-- Reading the same selected seed at the origin gives exactly the
switched rank-one derivative from the clipped center amplitude. -/
theorem hasFDerivAt_twistedLeading_graph_origin (d : w.HierarchyRegularity r h)
    {A : Velocity} {k : Vec3} {Ax : Vec3 →L[ℝ] Vec3} {t : ℝ} (ht : t ∈ Icc 0 T)
    (hA : HasFDerivAt (A t) Ax 0) (hA₀ : A t 0 = 0)
    (hκ : Ax.adjoint k = κ t 0) :
    HasFDerivAt (HierarchyTwistedProfile.graphRead A (twistedLeading d k) t)
      (waveSwitch t₀ r t • rankOne ℝ (center t) (κ t 0)) 0 := by
  rw [twistedLeading_graph_eq_localized d A k ht]
  by_cases hactive : t₀ ≤ t
  · have ha := slice_smooth d.amplitude_smooth ⟨hactive, ht.2⟩
    have hLeading : w.switchedLeading r h = fun u a s =>
        (waveSwitch t₀ r u * radialEnvelope ell a * waveProfile h s) • w.amplitude u a := by
      funext u a s
      simp only [SeedOn.switchedLeading, SeedOn.leading, smul_smul, mul_assoc]
    rw [hLeading, ← w.at_center ⟨hactive, ht.2⟩, ← hκ]
    exact hasFDerivAt_inductionPrimaryWave_origin d.phase_pos d.phase_le_one
      d.envelope_pos d.envelope_fits hA hA₀ (ha.differentiable (by simp) 0)
  · have hpre : t ≤ t₀ := (lt_of_not_ge hactive).le
    have hz : localizedTransportedProfile A k (w.switchedLeading r h) t = fun _ => 0 := by
      funext x
      exact w.switchedLeading_eq_zero_before_activation d.rate_nonneg hpre
        (centeredLabel (A t x)) ⟪k, centeredLabel (A t x)⟫_ℝ
    rw [hz, waveSwitch_eq_zero_of_le d.rate_nonneg hpre, zero_smul]
    exact hasFDerivAt_const _ _

/-- The selected leading pressure has the original localized Eulerian
readout on the entire lift. -/
theorem twistedPressure_graph_eq_localized (d : w.HierarchyRegularity r h)
    (A : Velocity) (k : Vec3) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HierarchyTwistedProfile.graphRead A (twistedPressure d k) t =
      localizedTransportedProfile A k (w.switchedPressure r h) t := by
  funext x
  change (twistedPressure d k).val.val.val (t, A t x, ⟪k, A t x⟫_ℝ) = _
  rw [twistedPressure_eval d k ht, phaseTwistedPeriodizeCentered_on_graph]

/-- The coefficient of the primary pressure on the inverse label graph,
with the actual time switch and radial envelope included. -/
def primaryPressureCoefficient (w : SeedOn M κ center t₀ T ell D C) (A : Velocity)
    (r t : ℝ) (x : Vec3) : ℝ :=
  let a := A t x
  wavePressureCoefficient (waveSwitch t₀ r t * radialEnvelope ell a)
    (κ t a) (w.amplitude t a) (M t a)

/-- The unwrapped transported pressure has the frozen phase-product form. -/
theorem transported_switchedPressure_eq (w : SeedOn M κ center t₀ T ell D C)
    (A : Velocity) (k : Vec3) (r h t : ℝ) :
    transportedProfile A k (w.switchedPressure r h) t = fun x =>
      -(w.primaryPressureCoefficient A r t x * wavePressurePrimitive h ⟪k, A t x⟫_ℝ) := by
  funext x
  simp only [transportedProfile, SeedOn.switchedPressure, SeedOn.leadingPressure,
    primaryPressureCoefficient, wavePressureCoefficient, div_eq_mul_inv]
  ring

private theorem contDiff_primaryPressureCoefficient (d : w.HierarchyRegularity r h)
    {A : Velocity} {t : ℝ} (ht : t ∈ Icc t₀ T) (hA : ContDiff ℝ ∞ (A t)) :
    ContDiff ℝ ∞ (w.primaryPressureCoefficient A r t) := by
  have hK := (slice_smooth d.covector_smooth ht).comp hA
  have hM := (slice_smooth d.strain_smooth ht).comp hA
  have ha := (slice_smooth d.amplitude_smooth ht).comp hA
  have hcut := (contDiff_const (c := waveSwitch t₀ r t)).mul
    ((contDiff_radialEnvelope d.envelope_pos).comp hA)
  have hi := hK.inner ℝ (hM.clm_apply ha)
  exact (((contDiff_const (c := (2 : ℝ))).mul hcut).mul hi).div (hK.norm_sq ℝ)
    (fun x => pow_ne_zero 2 (norm_ne_zero_iff.mpr (d.covector_nonzero t ht _)))

private theorem closure_interior_centeredCell : closure (interior centeredCell) = centeredCell := by
  have hconv : Convex ℝ centeredCell := by
    have heq : centeredCell = ⋂ i : Fin 3, (fun x : Vec3 => x i) ⁻¹' Icc (-(1 / 2 : ℝ)) (1 / 2) := by
      ext x
      simp [centeredCell]
    rw [heq]
    exact convex_iInter fun i => (convex_Icc _ _).linear_preimage
      (EuclideanSpace.proj (𝕜 := ℝ) i).toLinearMap
  have hz : (0 : Vec3) ∈ interior centeredCell := by
    apply mem_interior_iff_mem_nhds.mpr
    apply mem_of_superset (Metric.ball_mem_nhds (0 : Vec3) (show 0 < 1 / 2 by norm_num))
    intro x hx i
    have hnorm : ‖x‖ < (1 : ℝ) / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact abs_le.mp ((PiLp.norm_apply_le x i).trans hnorm.le)
  rw [hconv.closure_interior_eq_closure_of_nonempty_interior ⟨0, hz⟩,
    isCompact_centeredCell.isClosed.closure_eq]

private theorem smooth_gradient {p : Vec3 → ℝ} (hp : ContDiff ℝ ∞ p) :
    ContDiff ℝ ∞ (gradient p) :=
  (InnerProductSpace.toDual ℝ Vec3).symm.toContinuousLinearEquiv.contDiff.comp
    (hp.fderiv_right (m := ∞) (by simp))

/-- Smooth pressures agreeing on the closed inverse-label cell also have equal Hessians there. -/
theorem pressureHessian_eq_of_labelCell
    {A : Vec3 → Vec3} {X : Vec3 → Vec3} {p q : Vec3 → ℝ}
    (hA : Continuous A) (hX : Continuous X) (hLeft : Function.LeftInverse X A)
    (hRight : Function.LeftInverse A X) (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q)
    (he : EqOn p q (A ⁻¹' centeredCell)) {x : Vec3} (hx : A x ∈ centeredCell) :
    Hess[p] x = Hess[q] x := by
  let S : Set Vec3 := {x | Hess[p] x = Hess[q] x}
  have hS : IsClosed S := isClosed_eq ((smooth_gradient hp).continuous_fderiv (by simp))
    ((smooth_gradient hq).continuous_fderiv (by simp))
  have hInterior : X '' interior centeredCell ⊆ S := by
    rintro _ ⟨a, ha, rfl⟩
    have hAin : A (X a) ∈ interior centeredCell := by rwa [hRight]
    have hloc : p =ᶠ[𝓝 (X a)] q := by
      filter_upwards [hA.continuousAt.eventually (isOpen_interior.mem_nhds hAin)] with y hy
      exact he ((interior_subset : interior centeredCell ⊆ centeredCell) hy)
    exact hloc.gradient.fderiv_eq
  have hnear : A x ∈ closure (interior centeredCell) := by rwa [closure_interior_centeredCell]
  have hImage := image_closure_subset_closure_image hX (mem_image_of_mem X hnear)
  rw [hLeft] at hImage
  exact closure_minimal hInterior hS hImage

/-- Every Hessian of the actual periodic pressure is the Hessian of the
unwrapped seed at a translated point in the closed label cell. -/
theorem twistedPressure_graph_hessian_translate (d : w.HierarchyRegularity r h)
    {A : Velocity} {X : Vec3 → Vec3} {k : Vec3} {t : ℝ} (ht : t ∈ Icc 0 T)
    (hA : ContDiff ℝ ∞ (A t)) (hX : Continuous X)
    (hLeft : Function.LeftInverse X (A t)) (hRight : Function.LeftInverse (A t) X)
    (hAper : ∀ (n : Fin 3 → ℤ) x, A t (x + latticeVector n) = A t x + latticeVector n)
    (x : Vec3) : ∃ n : Fin 3 → ℤ, A t (x - latticeVector n) ∈ centeredCell ∧
      Hess[HierarchyTwistedProfile.graphRead A (twistedPressure d k) t] x =
      Hess[transportedProfile A k (w.switchedPressure r h) t] (x - latticeVector n) := by
  let p := HierarchyTwistedProfile.graphRead A (twistedPressure d k) t
  let q := transportedProfile A k (w.switchedPressure r h) t
  let phase (x : Vec3) := ⟪k, A t x⟫_ℝ
  have hphase : ContDiff ℝ ∞ phase := (innerSL ℝ k).contDiff.comp hA
  have hp : ContDiff ℝ ∞ p :=
    (HierarchySmoothProfile.contDiff_labelPhase_slice (twistedPressure d k).val.val ht).comp
      (hA.prodMk hphase)
  have hq : ContDiff ℝ ∞ q :=
    (w.contDiffOn_switchedPressure d.start_lt_end d.rate_nonneg d.envelope_pos d.phase_pos
      d.phase_le_one d.strain_smooth d.covector_smooth d.covector_nonzero d.amplitude_smooth).comp_contDiff
        (f := fun y : Vec3 => (t, A t y, phase y)) (contDiff_const.prodMk (hA.prodMk hphase))
        (fun y => ⟨ht.2, mem_univ _⟩)
  have hEq : EqOn p q ((A t) ⁻¹' centeredCell) := by
    intro y hy
    exact twistedPressure_cell_eval d k ht hy _
  have hpper : SpatiallyPeriodic p := HierarchyTwistedProfile.spatiallyPeriodic_graphRead A
    (twistedPressure d k) t hAper
  have hessPer := (hpper.gradient (hp.differentiable (by simp))).fderiv
    ((smooth_gradient hp).differentiable (by simp))
  obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell (A t x)
  have hArep : A t (x - latticeVector n) = A t x - latticeVector n := by
    have heq := hAper n (x - latticeVector n)
    rw [sub_add_cancel] at heq
    rw [heq, add_sub_cancel_right]
  have hrep : A t (x - latticeVector n) ∈ centeredCell := hArep ▸ hn
  refine ⟨n, hrep, ?_⟩
  have hper := hessPer n (x - latticeVector n)
  rw [sub_add_cancel] at hper
  exact hper.trans (pressureHessian_eq_of_labelCell hA.continuous hX hLeft hRight hp hq hEq hrep)

/-- Slow coefficient bounds for a fixed Eulerian time slice of the
primary pressure. `B` controls the coframe and strain and `K` the spatial
jets of the complete switch-envelope coefficient through order two. -/
structure PrimaryPressureBudget (w : SeedOn M κ center t₀ T ell D C)
    (A : Velocity) (k : Vec3) (r h t freq B K : ℝ) : Prop where
  frequency_ge_one : 1 ≤ freq
  coframe_ge_one : 1 ≤ B
  coefficient_constant_nonneg : 0 ≤ K
  phase_width : h = freq ^ (-1 / 2 : ℝ)
  center_cap : t₀ ≤ t → ‖center t‖ ≤ freq ^ (-3 / 4 : ℝ)
  strain : ∀ a, ‖M t a‖ ≤ B
  covector : ∀ a, ‖κ t a‖ ≤ B ^ 2 * freq
  phase_gradient : ∀ x, gradient (fun y => ⟪k, A t y⟫_ℝ) x = κ t (A t x)
  phase_hessian : ∀ x, ‖Hess[fun y => ⟪k, A t y⟫_ℝ] x‖ ≤ B ^ 2 * freq
  coefficient_jets : t₀ ≤ t → ∀ x,
    ‖w.primaryPressureCoefficient A r t x‖ ≤ K * freq ^ (-7 / 4 : ℝ) ∧
    ‖gradient (w.primaryPressureCoefficient A r t) x‖ ≤ K * freq ^ (-7 / 4 : ℝ) ∧
    ‖Hess[w.primaryPressureCoefficient A r t] x‖ ≤ K * freq ^ (-7 / 4 : ℝ)

set_option maxHeartbeats 1500000 in
/-- The signed primary pressure bound of Lemma 5.9 for the raw inverse-label
readout. The leading sign uses positivity from the same clipped seed. -/
theorem transported_switchedPressure_hessian_upper (d : w.HierarchyRegularity r h)
    {A : Velocity} {k : Vec3} {t freq B K : ℝ} (ht : t ∈ Icc 0 T)
    (hA : ContDiff ℝ ∞ (A t)) (bud : w.PrimaryPressureBudget A k r h t freq B K)
    (x v : Vec3) :
    ⟪v, Hess[transportedProfile A k (w.switchedPressure r h) t] x v⟫_ℝ ≤
      ((2 * B ^ 3 + (3 * B ^ 4 + B ^ 2) * K) * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2 := by
  have hf : 0 < freq := zero_lt_one.trans_le bud.frequency_ge_one
  have hB : 0 ≤ B := zero_le_one.trans bud.coframe_ge_one
  have hK := bud.coefficient_constant_nonneg
  have hb : 0 ≤ (3 * B ^ 4 + B ^ 2) * K := by positivity
  by_cases hactive : t₀ ≤ t
  · let phase (y : Vec3) := ⟪k, A t y⟫_ℝ
    let c := w.primaryPressureCoefficient A r t
    let L := (-(c x * waveSlope h (phase x))) • rankOne ℝ (gradient phase x) (gradient phase x)
    let G := -(waveProfile h (phase x) •
      (rankOne ℝ (gradient c x) (gradient phase x) + rankOne ℝ (gradient phase x) (gradient c x) +
        c x • Hess[phase] x)) - wavePressurePrimitive h (phase x) • Hess[c] x
    let Q := K * freq ^ (-9 / 4 : ℝ)
    have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
    have hact : t ∈ Icc t₀ T := ⟨hactive, ht.2⟩
    have hc : ContDiff ℝ 2 c := (contDiff_primaryPressureCoefficient d hact hA).of_le (by simp)
    have hph : ContDiff ℝ 2 phase := (innerSL ℝ k).contDiff.comp (hA.of_le (by simp))
    have hGrad : gradient phase x = κ t (A t x) := bud.phase_gradient x
    have hWidth := bud.phase_width
    have hLead (u : Vec3) : ⟪u, L u⟫_ℝ ≤ (2 * B ^ 3 * freq ^ (-1 / 4 : ℝ)) * ‖u‖ ^ 2 := by
      let a := A t x
      by_cases hNear : ‖a‖ ≤ 2 * ell
      · have hχ : waveSwitch t₀ r t ∈ Icc (0 : ℝ) 1 :=
          ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
        have he := radialEnvelope_mem_Icc ell a
        have hcut : waveSwitch t₀ r t * radialEnvelope ell a ∈ Icc (0 : ℝ) 1 :=
          ⟨mul_nonneg hχ.1 he.1, mul_le_one₀ hχ.2 he.1 he.2⟩
        have hSeed := w.near a hNear t hact
        have hCap : ‖w.amplitude t a‖ ≤ 2 * freq ^ (-3 / 4 : ℝ) :=
          hSeed.2.1.2.trans (mul_le_mul_of_nonneg_left (bud.center_cap hactive) (by norm_num))
        have h := wavePrimaryPressure_leading_upper_of_scale bud.frequency_ge_one
          (d.covector_nonzero t hact a) hcut hSeed.2.2.2.1.le
          (bud.covector a) (bud.strain a) hCap (phase x) u
        simpa only [L, c, primaryPressureCoefficient, hGrad, hWidth, a] using h
      · have hz : c x = 0 := by
          change wavePressureCoefficient (waveSwitch t₀ r t * radialEnvelope ell a)
            (κ t a) (w.amplitude t a) (M t a) = 0
          simp only [radialEnvelope_eq_zero d.envelope_pos (le_of_not_ge hNear), mul_zero,
            wavePressureCoefficient, zero_mul, zero_div]
        simp only [L, hz, zero_mul, neg_zero, zero_smul, zero_apply, inner_zero_right]
        positivity
    have hW : h * (K * freq ^ (-7 / 4 : ℝ)) = Q := by
      dsimp only [Q]
      rw [hWidth, show (-9 / 4 : ℝ) = -1 / 2 + -7 / 4 by norm_num, Real.rpow_add hf]
      ring
    have hF : ‖waveProfile h (phase x)‖ ≤ h :=
      (norm_waveProfile_le d.phase_pos d.phase_le_one _).trans (by linarith [d.phase_pos])
    have hP : ‖wavePressurePrimitive h (phase x)‖ ≤ h := by
      have hp := norm_phasePrimitive_le (contDiff_waveProfile d.phase_pos d.phase_le_one).continuous
        (periodic_waveProfile d.phase_pos d.phase_le_one) (phaseMean_waveProfile d.phase_pos d.phase_le_one)
        (fun s _ => norm_waveProfile_le d.phase_pos d.phase_le_one s) (phase x)
      change ‖wavePressurePrimitive h (phase x)‖ ≤ 2 * (h / 2) at hp
      linarith
    have hfactor : 1 ≤ B ^ 2 := one_le_pow₀ bud.coframe_ge_one
    have hroot : 1 ≤ Real.sqrt freq := by simpa using Real.sqrt_le_sqrt bud.frequency_ge_one
    have hstretch : Q ≤ B ^ 2 * Real.sqrt freq * Q := by
      have hmul := one_le_mul_of_one_le_of_one_le hfactor hroot
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hmul hQ
    have hstretch' : Q ≤ B ^ 2 * Q := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor hQ
    obtain ⟨hC, hC1, hC2⟩ := bud.coefficient_jets hactive x
    have hF0 : ‖waveProfile h (phase x)‖ * ‖c x‖ ≤ B ^ 2 * Real.sqrt freq * Q :=
      ((mul_le_mul hF hC (norm_nonneg _) d.phase_pos.le).trans_eq hW).trans hstretch
    have hF1 : ‖waveProfile h (phase x)‖ * ‖gradient c x‖ ≤ B ^ 2 * Real.sqrt freq * Q :=
      ((mul_le_mul hF hC1 (norm_nonneg _) d.phase_pos.le).trans_eq hW).trans hstretch
    have hP2 : ‖wavePressurePrimitive h (phase x) • Hess[c] x‖ ≤ B ^ 2 * Q := by
      rw [norm_smul]
      exact ((mul_le_mul hP hC2 (norm_nonneg _) d.phase_pos.le).trans_eq hW).trans hstretch'
    have hGeo : ‖G‖ ≤ ((3 * B ^ 4 + B ^ 2) * K) * freq ^ (-3 / 4 : ℝ) := by
      rw [show B ^ 4 = (B ^ 2) ^ 2 by ring]
      exact norm_wavePrimaryPressure_geometricRemainder_le_at_hierarchy_scale
        bud.frequency_ge_one hQ (sq_nonneg B) le_rfl (waveProfile h (phase x))
        (wavePressurePrimitive h (phase x)) (c x) (gradient phase x) (gradient c x)
        (Hess[phase] x) (Hess[c] x) (hGrad ▸ bud.covector (A t x)) (bud.phase_hessian x) hF1 hF0 hP2
    have hH : Hess[transportedProfile A k (w.switchedPressure r h) t] x = L + G + 0 + 0 := by
      rw [transported_switchedPressure_eq, wavePrimaryPressure_hessian d.phase_pos d.phase_le_one hc hph x]
      dsimp only [L, G]
      abel
    simpa only [add_zero] using wavePressure_hessian_upper_of_scales bud.frequency_ge_one hb
      (le_refl (0 : ℝ)) (le_refl (0 : ℝ)) hH hLead hGeo (by simp) (by simp) v
  · have hzero : transportedProfile A k (w.switchedPressure r h) t = (0 : Vec3 → ℝ) := by
      funext y
      simp only [transportedProfile, SeedOn.switchedPressure,
        waveSwitch_eq_zero_of_le d.rate_nonneg (le_of_not_ge hactive), zero_mul, Pi.zero_apply]
    have hg : gradient (0 : Vec3 → ℝ) = (0 : Vec3 → Vec3) := by
      funext y
      simp [gradient]
    rw [hzero, hg, fderiv_zero, Pi.zero_apply, zero_apply, inner_zero_right]
    positivity

/-- The primary Hessian estimate holds for the actual wrapped selected
pressure on the full spatial lift, including translated cell faces. -/
theorem twistedPressure_graph_hessian_upper (d : w.HierarchyRegularity r h)
    {A : Velocity} {X : Vec3 → Vec3} {k : Vec3} {t freq B K : ℝ} (ht : t ∈ Icc 0 T)
    (hA : ContDiff ℝ ∞ (A t)) (hX : Continuous X)
    (hLeft : Function.LeftInverse X (A t)) (hRight : Function.LeftInverse (A t) X)
    (hAper : ∀ (n : Fin 3 → ℤ) x, A t (x + latticeVector n) = A t x + latticeVector n)
    (bud : w.PrimaryPressureBudget A k r h t freq B K) (x v : Vec3) :
    ⟪v, Hess[HierarchyTwistedProfile.graphRead A (twistedPressure d k) t] x v⟫_ℝ ≤
      ((2 * B ^ 3 + (3 * B ^ 4 + B ^ 2) * K) * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2 := by
  obtain ⟨n, _, hn⟩ := twistedPressure_graph_hessian_translate d ht hA hX hLeft hRight hAper x
  rw [hn]
  exact transported_switchedPressure_hessian_upper d ht hA bud (x - latticeVector n) v

/-- The Riesz identification preserves the operator norm of the scalar Hessian. -/
theorem norm_pressureHessian_eq_iteratedFDeriv (c : Vec3 → ℝ) (x : Vec3) :
    ‖fderiv ℝ (gradient c) x‖ = ‖iteratedFDeriv ℝ 2 c x‖ := by
  let L := (toDual ℝ Vec3).symm
  calc
    _ = ‖iteratedFDeriv ℝ 1 (L ∘ fderiv ℝ c) x‖ := (norm_iteratedFDeriv_one _).symm
    _ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ c) x‖ := L.norm_iteratedFDeriv_comp_left _ _ _
    _ = _ := norm_iteratedFDeriv_fderiv

/-- The normalized label jet bound for the complete slow coefficient gives
the actual Eulerian coefficient, gradient, and Hessian rows. `J` bounds
the first two derivative orders of the radius-scaled inverse chart. -/
theorem primaryPressureCoefficient_jets_of_scaledLabelJets
    (d : w.HierarchyRegularity r h) {A : Velocity} {t freq C₀ J : ℝ}
    (ht : t ∈ Icc t₀ T) (hf : 0 < freq) (hJ : 1 ≤ J) (hC₀ : 0 ≤ C₀)
    (hA : ContDiff ℝ ∞ (A t))
    (hlabel : PhaseJetBound 2 (C₀ * freq ^ (-3 / 4 : ℝ))
      (fun a => freq * w.primaryPressureCoefficient (fun _ => id) r t (ell • a)))
    (hInv : ∀ j : ℕ, 1 ≤ j → j ≤ 2 → ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => ell⁻¹ • A t y) x‖ ≤ J ^ j) (x : Vec3) :
    let Q := 2 * C₀ * J ^ 2 * freq ^ (-7 / 4 : ℝ)
    ‖w.primaryPressureCoefficient A r t x‖ ≤ Q ∧
      ‖gradient (w.primaryPressureCoefficient A r t) x‖ ≤ Q ∧
      ‖fderiv ℝ (gradient (w.primaryPressureCoefficient A r t)) x‖ ≤ Q := by
  let F (a : Vec3) := freq * w.primaryPressureCoefficient (fun _ => id) r t (ell • a)
  let R (y : Vec3) := ell⁻¹ • A t y
  have hraw := contDiff_primaryPressureCoefficient (A := fun _ => id) d ht contDiff_id
  have hsF : ContDiff ℝ ∞ F := contDiff_const.mul (hraw.comp (contDiff_id.const_smul ell))
  have hsR : ContDiff ℝ ∞ R := hA.const_smul _
  have hComp : PhaseJetBound 2 (2 * C₀ * J ^ 2 * freq ^ (-3 / 4 : ℝ)) (F ∘ R) := by
    intro j hj y
    have hfct : (j.factorial : ℝ) ≤ 2 := by
      exact_mod_cast Nat.factorial_le (m := j) (n := 2) hj
    have hpow : J ^ j ≤ J ^ 2 := pow_le_pow_right₀ hJ hj
    calc
      _ ≤ (j.factorial : ℝ) * (C₀ * freq ^ (-3 / 4 : ℝ)) * J ^ j :=
        norm_iteratedFDeriv_comp_le hsF hsR (by simp) y
          (fun i hi => hlabel i (hi.trans hj) (R y)) (fun i hi hij => hInv i hi (hij.trans hj) y)
      _ ≤ 2 * (C₀ * freq ^ (-3 / 4 : ℝ)) * J ^ 2 := by
        gcongr
      _ = _ := by ring
  have he : freq⁻¹ • (F ∘ R) = w.primaryPressureCoefficient A r t := by
    funext y
    change freq⁻¹ * (freq * w.primaryPressureCoefficient (fun _ => id) r t (ell • (ell⁻¹ • A t y))) = _
    rw [smul_smul, mul_inv_cancel₀ d.envelope_pos.ne', one_smul, ← mul_assoc, inv_mul_cancel₀ hf.ne', one_mul]
    rfl
  have hScale : freq⁻¹ * (2 * C₀ * J ^ 2 * freq ^ (-3 / 4 : ℝ)) =
      2 * C₀ * J ^ 2 * freq ^ (-7 / 4 : ℝ) := by
    rw [show (-7 / 4 : ℝ) = -1 + (-3 / 4) by norm_num, Real.rpow_add hf, Real.rpow_neg_one]
    ring
  have hj : PhaseJetBound 2 (2 * C₀ * J ^ 2 * freq ^ (-7 / 4 : ℝ))
      (w.primaryPressureCoefficient A r t) := by
    intro j hj y
    rw [← he, iteratedFDeriv_const_smul_apply ((hsF.comp hsR).contDiffAt.of_le (by simp)),
      norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hf.le), ← hScale]
    exact mul_le_mul_of_nonneg_left (hComp j hj y) (inv_nonneg.mpr hf.le)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [norm_iteratedFDeriv_zero] using hj 0 (by norm_num) x
  · have hOne := hj 1 (by norm_num) x
    rw [norm_iteratedFDeriv_one] at hOne
    exact ((toDual ℝ Vec3).symm.norm_map _).trans_le hOne
  · rw [norm_pressureHessian_eq_iteratedFDeriv]
    exact hj 2 le_rfl x

/-- The radius-normalized actual slow pressure coefficient follows from
jet bounds on the enveloped seed and normalized pressure operator. -/
theorem primaryPressureCoefficient_scaledLabelJets_of_slowJets
    (d : w.HierarchyRegularity r h) {t freq B₀ P₀ : ℝ} (ht : t ∈ Icc t₀ T)
    (hf : 0 < freq) (hB₀ : 0 ≤ B₀) (hP₀ : 0 ≤ P₀)
    (hCap : ‖center t‖ ≤ freq ^ (-3 / 4 : ℝ))
    (hamp : PhaseJetBound 2 (B₀ * ‖center t‖)
      (fun a => radialEnvelope ell (ell • a) • w.amplitude t (ell • a)))
    (hP_smooth : ContDiff ℝ ∞ (fun a : Vec3 =>
      hierarchyRelayPressureAmplitudeCoefficient (M t (ell • a)) (freq⁻¹ • κ t (ell • a))))
    (hP : PhaseJetBound 2 P₀ (fun a : Vec3 =>
      hierarchyRelayPressureAmplitudeCoefficient (M t (ell • a)) (freq⁻¹ • κ t (ell • a)))) :
    PhaseJetBound 2 ((4 * P₀ * B₀) * freq ^ (-3 / 4 : ℝ))
      (fun a => freq * w.primaryPressureCoefficient (fun _ => id) r t (ell • a)) := by
  let P (a : Vec3) := hierarchyRelayPressureAmplitudeCoefficient (M t (ell • a)) (freq⁻¹ • κ t (ell • a))
  let E (a : Vec3) := radialEnvelope ell (ell • a) • w.amplitude t (ell • a)
  let χ := waveSwitch t₀ r t
  have hs : ContDiff ℝ ∞ (w.amplitude t) :=
    d.amplitude_smooth.comp_contDiff (f := fun a : Vec3 => (t, a))
      (contDiff_const.prodMk contDiff_id) (fun _ => ⟨ht, mem_univ _⟩)
  have hsE : ContDiff ℝ ∞ E := ((contDiff_radialEnvelope d.envelope_pos).comp (contDiff_id.const_smul ell)).smul
    (hs.comp (contDiff_id.const_smul ell))
  have hχ : χ ∈ Icc (0 : ℝ) 1 := ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hE : PhaseJetBound 2 (B₀ * ‖center t‖) (χ • E) := by
    intro j hj a
    rw [iteratedFDeriv_const_smul_apply (hsE.contDiffAt.of_le (by simp)), norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (by
      simpa only [Real.norm_of_nonneg hχ.1] using hχ.2)).trans (hamp j hj a)
  let L : (Vec3 →L[ℝ] ℝ) →L[ℝ] Vec3 →L[ℝ] ℝ := (ContinuousLinearMap.apply ℝ ℝ).flip
  have hL : ‖L‖ ≤ 1 := by
    simp only [L, ContinuousLinearMap.opNorm_flip, ContinuousLinearMap.apply]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => ?_
    simp only [ContinuousLinearMap.coe_id', id, one_mul]
    rfl
  have hPE : PhaseJetBound 2 ((2 : ℝ) ^ 2 * (P₀ * (B₀ * ‖center t‖)))
      (fun a => P a ((χ • E) a)) :=
    phaseJetBound_bilinear_product L hL hP_smooth (hsE.const_smul χ) hP₀
      (mul_nonneg hB₀ (norm_nonneg _)) hP hE
  have he : (fun a => P a ((χ • E) a)) =
      -(fun a => freq * w.primaryPressureCoefficient (fun _ => id) r t (ell • a)) := by
    funext a
    change P a (χ • (radialEnvelope ell (ell • a) • w.amplitude t (ell • a))) = _
    rw [smul_smul]
    simpa only [P, χ, primaryPressureCoefficient, id_eq, Pi.neg_apply, mul_neg] using
      normalizedPressureAmplitudeCoefficient_apply_leading hf (M t (ell • a))
        (κ t (ell • a)) (w.amplitude t (ell • a)) (χ * radialEnvelope ell (ell • a))
  intro j hj a
  have h' := hPE j hj a
  rw [he, iteratedFDeriv_neg_apply, norm_neg] at h'
  exact h'.trans (by
    calc
      _ ≤ (2 : ℝ) ^ 2 * (P₀ * (B₀ * freq ^ (-3 / 4 : ℝ))) := by gcongr
      _ = _ := by ring)

set_option maxHeartbeats 750000 in
/-- First-order label jets of the inverse coframe give the two Eulerian
inverse-map jets and the transported phase gradient used by the primary pressure. -/
theorem _root_.TorusEuler.IsLabelFlowOn.primaryPressure_geometry {T ell B L : ℝ} {U : Velocity}
    {X : ℝ → Velocity} {k : Vec3} (hT : 0 < T) (hell : 0 < ell) (hL : 1 ≤ L)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) {t : ℝ} (ht : t ∈ Icc 0 T)
    (hG : ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ B)
    (hG₁ : ∀ a, ‖fderiv ℝ (fun b => fderiv ℝ (X t 0) (X 0 t b)) a‖ ≤ L) :
    (∀ x, gradient (fun y => ⟪k, X t 0 y⟫_ℝ) x = labelWaveVector X 0 (X t 0 x) k t) ∧
    (∀ x, ‖fderiv ℝ (gradient (fun y => ⟪k, X t 0 y⟫_ℝ)) x‖ ≤ ‖k‖ * (L * B)) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ 2 → ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => ell⁻¹ • X t 0 y) x‖ ≤ (max 1 (ell⁻¹ * (L * B))) ^ j) := by
  let A := X t 0
  let G (a : Vec3) := fderiv ℝ (X t 0) (X 0 t a)
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hU₂ := hU.of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)
  obtain ⟨K, hLip⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
  have hInv (x : Vec3) : X 0 t (X t 0 x) = x := (hX.inverse hLip ht h₀).1 x
  have hA : ContDiff ℝ ∞ A :=
    (hX.contDiffOn_inverseLabelFlow hT hU hper).comp_contDiff (f := fun x : Vec3 => (t,x))
      (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht, mem_univ x⟩)
  have hGs : ContDiff ℝ ∞ G :=
    (hX.contDiffOn_inverseLabelDerivative hT hU hper).comp_contDiff (f := fun x : Vec3 => (t,x))
      (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht, mem_univ x⟩)
  have he : fderiv ℝ A = G ∘ A := by
    funext x
    change fderiv ℝ A x = fderiv ℝ A (X 0 t (X t 0 x))
    rw [hInv]
  have hD₁ (x : Vec3) : ‖fderiv ℝ A x‖ ≤ B := by
    rw [he]
    exact hG (A x)
  have hD₂ (x : Vec3) : ‖iteratedFDeriv ℝ 2 A x‖ ≤ L * B := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one, he,
      fderiv_comp x ((hGs.differentiable (by simp)) (A x)) (hA.differentiable (by simp) x)]
    exact (opNorm_comp_le _ _).trans (mul_le_mul (hG₁ (A x)) (hD₁ x) (norm_nonneg _) (zero_le_one.trans hL))
  have hB : 0 ≤ B := (norm_nonneg _).trans (hD₁ 0)
  constructor
  · intro x
    have hg := (hX.hasGradientAt_labelPhase hT hU₂ hper h₀ ht (X t 0 x) k).gradient
    rwa [hInv] at hg
  · constructor
    · intro x
      let ℒ := innerSL ℝ k
      let q := ℒ ∘ A
      change ‖fderiv ℝ (gradient q) x‖ ≤ ‖k‖ * (L * B)
      rw [norm_pressureHessian_eq_iteratedFDeriv]
      have hnorm : ‖ℒ‖ = ‖k‖ := innerSL_apply_norm ℝ k
      exact (ℒ.norm_iteratedFDeriv_comp_left hA.contDiffAt (by simp)).trans
        (mul_le_mul hnorm.le (hD₂ x) (norm_nonneg _) (norm_nonneg _))
    · intro j hj hj₂ x
      let J := max 1 (ell⁻¹ * (L * B))
      have hJ : 1 ≤ J := le_max_left _ _
      have hD (i : ℕ) (hi : 1 ≤ i) (hi₂ : i ≤ 2) : ‖iteratedFDeriv ℝ i A x‖ ≤ L * B := by
        interval_cases i
        · rw [norm_iteratedFDeriv_one]
          exact (hD₁ x).trans (le_mul_of_one_le_left hB hL)
        · exact hD₂ x
      change ‖iteratedFDeriv ℝ j (ell⁻¹ • A) x‖ ≤ J ^ j
      rw [iteratedFDeriv_const_smul_apply (hA.contDiffAt.of_le (by simp)), norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hell.le)]
      calc
        _ ≤ ell⁻¹ * (L * B) := mul_le_mul_of_nonneg_left (hD j hj hj₂) (inv_nonneg.mpr hell.le)
        _ ≤ J := le_max_right _ _
        _ ≤ J ^ j := by simpa only [pow_one] using pow_le_pow_right₀ hJ hj

section Parent

variable {U : Velocity} {X : ℝ → Velocity} {k : Vec3}
  {seed : SeedOn (fun t a => fderiv ℝ (U t) (X 0 t a))
    (fun t a => labelWaveVector X 0 a k t) center t₀ T ell D C}

/-- The actual inverse parent chart gives the signed central derivative
of the same leading wave used by the physical hierarchy. -/
theorem hasFDerivAt_twistedLeading_parentGraph_origin (d : seed.HierarchyRegularity r h)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) (hodd : ∀ t ∈ Icc 0 T, Function.Odd (U t))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasFDerivAt (HierarchyTwistedProfile.graphRead (fun u => X u 0) (twistedLeading d k) t)
      (waveSwitch t₀ r t • rankOne ℝ (center t) (labelWaveVector X 0 0 k t)) 0 := by
  have ht0 : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr d.end_pos.le
  obtain ⟨K, hLip⟩ := exists_lipschitzWith_of_contDiffOn_periodic d.end_pos (hU.of_le (by simp)) hper
  have hA := slice_smooth (f := fun u => X u 0) (hX.contDiffOn_inverseLabelFlow d.end_pos hU hper) ht
  have hneg : X t 0 0 = -X t 0 0 := by
    simpa only [neg_zero] using hX.odd hLip hodd ht ht0 (0 : Vec3)
  have hA0 : X t 0 0 = 0 := by
    have h2 : (2 : ℝ) • X t 0 0 = 0 := calc
      _ = X t 0 0 + X t 0 0 := two_smul ℝ _
      _ = X t 0 0 + -X t 0 0 := congrArg (X t 0 0 + ·) hneg
      _ = 0 := by simp
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  have hInv := (hX.inverse hLip ht0 ht).2 (0 : Vec3)
  change X 0 t (X t 0 0) = 0 at hInv
  rw [hA0] at hInv
  exact hasFDerivAt_twistedLeading_graph_origin d ht
    ((hA.differentiable (by simp) 0).hasFDerivAt) hA0 (by simp only [labelWaveVector, hInv])

set_option maxHeartbeats 750000 in
/-- The global signed pressure estimate for the actual inverse parent
chart. The remaining inputs are the measured leading coefficient jets. -/
theorem twistedPressure_parentGraph_hessian_upper (d : seed.HierarchyRegularity r h)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) {t freq B K : ℝ} (ht : t ∈ Icc 0 T)
    (bud : seed.PrimaryPressureBudget (fun u => X u 0) k r h t freq B K) (x v : Vec3) :
    ⟪v, Hess[HierarchyTwistedProfile.graphRead (fun u => X u 0) (twistedPressure d k) t] x v⟫_ℝ ≤
      ((2 * B ^ 3 + (3 * B ^ 4 + B ^ 2) * K) * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2 := by
  have ht0 : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr d.end_pos.le
  obtain ⟨L, hLip⟩ := exists_lipschitzWith_of_contDiffOn_periodic d.end_pos (hU.of_le (by simp)) hper
  have hA := slice_smooth (f := fun u => X u 0) (hX.contDiffOn_inverseLabelFlow d.end_pos hU hper) ht
  have hForward := slice_smooth (f := fun u => X 0 u) (hX.contDiffOn_forwardLabelFlow d.end_pos hU hper) ht
  obtain ⟨hLeft, hRight⟩ := hX.inverse hLip ht ht0
  exact twistedPressure_graph_hessian_upper (A := fun u => X u 0) (X := X 0 t) d ht
    hA hForward.continuous hLeft hRight (hX.add_latticeVector hLip hper ht ht0) bud x v

set_option maxHeartbeats 1500000 in
/-- Parent coframe jets and radius-normalized label pressure coefficient
jets supply the physical pressure budget used in the signed Hessian estimate. -/
theorem primaryPressureBudget_of_parent_labelJets (d : seed.HierarchyRegularity r h)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) {t freq B L C₀ : ℝ} (ht : t ∈ Icc 0 T)
    (hf : 1 ≤ freq) (hB : 1 ≤ B) (hL : 1 ≤ L) (hC₀ : 0 ≤ C₀) (hh : h = freq ^ (-1 / 2 : ℝ))
    (hCap : t₀ ≤ t → ‖center t‖ ≤ freq ^ (-3 / 4 : ℝ))
    (hCarrier : ‖k‖ ≤ B * freq) (hM : ∀ x, ‖fderiv ℝ (U t) x‖ ≤ B)
    (hG : ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ B)
    (hG₁ : ∀ a, ‖fderiv ℝ (fun b => fderiv ℝ (X t 0) (X 0 t b)) a‖ ≤ L)
    (hlabel : t₀ ≤ t → PhaseJetBound 2 (C₀ * freq ^ (-3 / 4 : ℝ))
      (fun a => freq * seed.primaryPressureCoefficient (fun _ => id) r t (ell • a))) :
    seed.PrimaryPressureBudget (fun u => X u 0) k r h t freq (L * B)
      (2 * C₀ * (max 1 (ell⁻¹ * (L * B))) ^ 2) := by
  have hA := slice_smooth (f := fun u => X u 0) (hX.contDiffOn_inverseLabelFlow d.end_pos hU hper) ht
  have hGeo := hX.primaryPressure_geometry (k := k) d.end_pos d.envelope_pos hL hU hper ht hG hG₁
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  have hLB : B ≤ L * B := le_mul_of_one_le_left hB₀ hL
  have hLB₀ : 0 ≤ L * B := hB₀.trans hLB
  have hf₀ : 0 ≤ freq := zero_le_one.trans hf
  have hCar : ‖k‖ ≤ (L * B) * freq := hCarrier.trans (mul_le_mul_of_nonneg_right hLB hf₀)
  refine ⟨hf, hB.trans hLB, by positivity, hh, hCap, (fun a => (hM (X 0 t a)).trans hLB),
    ?_, hGeo.1, ?_, ?_⟩
  · intro a
    change ‖(fderiv ℝ (X t 0) (X 0 t a)).adjoint k‖ ≤ (L * B) ^ 2 * freq
    calc
      _ ≤ ‖(fderiv ℝ (X t 0) (X 0 t a)).adjoint‖ * ‖k‖ :=
        ((fderiv ℝ (X t 0) (X 0 t a)).adjoint).le_opNorm k
      _ = ‖fderiv ℝ (X t 0) (X 0 t a)‖ * ‖k‖ := by rw [adjoint.norm_map]
      _ ≤ (L * B) * ((L * B) * freq) := mul_le_mul ((hG a).trans hLB) hCar (norm_nonneg _) hLB₀
      _ = _ := by ring
  · intro x
    calc
      _ ≤ ‖k‖ * (L * B) := hGeo.2.1 x
      _ ≤ ((L * B) * freq) * (L * B) := mul_le_mul_of_nonneg_right hCar hLB₀
      _ = _ := by ring
  · intro hactive x
    exact primaryPressureCoefficient_jets_of_scaledLabelJets (A := fun u => X u 0) d
      ⟨hactive, ht.2⟩ (zero_lt_one.trans_le hf) (le_max_left _ _) hC₀ hA (hlabel hactive) hGeo.2.2 x

set_option maxHeartbeats 900000 in
/-- The signed pressure budget is supplied by the parent coframe, the
scaled enveloped seed jets and the normalized slow pressure operator. -/
theorem primaryPressureBudget_of_parent_seedJets (d : seed.HierarchyRegularity r h)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) {t freq B L B₀ P₀ : ℝ} (ht : t ∈ Icc 0 T)
    (hf : 1 ≤ freq) (hB : 1 ≤ B) (hL : 1 ≤ L) (hB₀ : 0 ≤ B₀) (hP₀ : 0 ≤ P₀)
    (hh : h = freq ^ (-1 / 2 : ℝ)) (hCap : t₀ ≤ t → ‖center t‖ ≤ freq ^ (-3 / 4 : ℝ))
    (hCarrier : ‖k‖ ≤ B * freq) (hM : ∀ x, ‖fderiv ℝ (U t) x‖ ≤ B)
    (hG : ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ B)
    (hG₁ : ∀ a, ‖fderiv ℝ (fun b => fderiv ℝ (X t 0) (X 0 t b)) a‖ ≤ L)
    (hamp : t₀ ≤ t → PhaseJetBound 2 (B₀ * ‖center t‖)
      (fun a => radialEnvelope ell (ell • a) • seed.amplitude t (ell • a)))
    (hP : t₀ ≤ t →
      let P (a : Vec3) := hierarchyRelayPressureAmplitudeCoefficient (fderiv ℝ (U t) (X 0 t (ell • a)))
        (freq⁻¹ • labelWaveVector X 0 (ell • a) k t)
      ContDiff ℝ ∞ P ∧ PhaseJetBound 2 P₀ P) :
    seed.PrimaryPressureBudget (fun u => X u 0) k r h t freq (L * B)
      (2 * (4 * P₀ * B₀) * (max 1 (ell⁻¹ * (L * B))) ^ 2) := by
  refine primaryPressureBudget_of_parent_labelJets d hX hU hper ht hf hB hL (by positivity)
    hh hCap hCarrier hM hG hG₁ ?_
  intro hactive
  exact primaryPressureCoefficient_scaledLabelJets_of_slowJets d ⟨hactive, ht.2⟩
    (zero_lt_one.trans_le hf) hB₀ hP₀ (hCap hactive) (hamp hactive) (hP hactive).1 (hP hactive).2

end Parent

end
end TorusEuler.LocalizedAmplitude.SeedOn
