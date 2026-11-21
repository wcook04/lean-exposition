import TorusEuler.Paper.Proofs.S5Bridge.Norms
import TorusEuler.PaperPhysicalParentInputs
import TorusEuler.LocalizedAmplitudeComparison
import TorusEuler.LocalizedSeedRegularity

/-!
# S5 bridge: the standing hypotheses of §5.1

Glue between the standing hypotheses of the Section 5 statements (`S5.Parent`,
`S5.Launch`, `S5.Origin`, and an arbitrary coefficient carrier
`d : ParentGeometry hT U X k`) and the library inputs of the hierarchy
(`ParentGeometry`, `TruncatedHierarchyParent`, `CenterWaveOn`).

* Two parent geometries of the same parent have the same coefficient profiles,
  hence the same operators `S5.ops`, the same `S5.curlCorrection` and
  `S5.totalDivergence`, and the same solutions and expansions
  (`MeanSolution`, `TransverseSolution`, `IsExpansion`).
* `S5.Parent` gives a parent geometry `d'` with `TruncatedHierarchyParent d' pU D lam`
  (`exists_truncatedHierarchyParent`); conversely a `TruncatedHierarchyParent` with the
  remaining data of §5.1 gives `S5.Parent` (`parent_of_truncatedHierarchyParent`).
  `TruncatedHierarchyParent` has no field that is absent from `S5.Parent`: its bounds
  `d.mean.inverse_bound ≤ 𝖣`, `d.mean.strain_bound ≤ 𝖣` concern the chosen carrier and
  hold for the carrier built here. The library data that is **not** in the S5
  predicates are the velocity jets `|∇^j U| ≤ C_j 𝖣^j` (Bernstein, Lemma B.1 / the
  proof of Proposition 5.1) and the coefficient jets (D.6) of Proposition 5.1, which
  many library lemmas take as hypotheses: row proofs take them from their cited
  statements.
* The flow fixes the origin (`flow_origin`), so the central data of `S5.Origin` are
  `CenterWaveOn` at `∇U(t,0)` (`Origin.centerWaveOn_gradient`), and the launch
  covector of the library seed constructions is `k_*` (`Launch.carrier_eq`).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Bridge

open HierarchyTwistedProfile LocalizedAmplitude

noncomputable section

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {k : Vec3}

/-! ## Two carriers of the same parent -/

/-- Two parent geometries of the same parent have the same profile `(D_aX)⁻¹`. -/
theorem geometry_inverse_eq (d d' : ParentGeometry hT U X k) : d.inverse = d'.inverse :=
  HierarchyTwistedProfile.ext fun x hx => (d.inverse_value x hx).trans (d'.inverse_value x hx).symm

/-- Two parent geometries of the same parent have the same profile `M`. -/
theorem geometry_strain_eq (d d' : ParentGeometry hT U X k) : d.strain = d'.strain :=
  HierarchyTwistedProfile.ext fun x hx => (d.strain_value x hx).trans (d'.strain_value x hx).symm

/-- Two parent geometries of the same parent have the same profile `κ`. -/
theorem geometry_covector_eq (d d' : ParentGeometry hT U X k) : d.covector = d'.covector :=
  HierarchyTwistedProfile.ext fun x hx =>
    (d.covector_value x hx).trans (d'.covector_value x hx).symm

/-- Two parent geometries of the same parent have the same operators `S5.ops`. -/
theorem ops_eq (d d' : ParentGeometry hT U X k) : S5.ops d = S5.ops d' := by
  unfold S5.ops
  rw [geometry_inverse_eq d d', geometry_strain_eq d d', geometry_covector_eq d d']

/-- The library completion `C[·]` only depends on the coefficient profiles. -/
theorem complete_congr {G G' : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)}
    {κ κ' : HierarchyTwistedProfile T k Vec3} (hG : G = G') (hκ : κ = κ')
    (h₁ : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (h₂ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    (h₁' : HierarchyPeriodicProfile.PhaseIndependent κ'.val.val)
    (h₂' : ∀ t ∈ Icc 0 T, ∀ a, κ'.val.val.val (t, a, 0) ≠ 0)
    (V : HierarchyTwistedProfile T k Vec3) :
    complete hT G κ h₁ h₂ V = complete hT G' κ' h₁' h₂' V := by
  subst hG
  subst hκ
  rfl

/-- Two parent geometries of the same parent have the same `C[·]` (`S5.curlCorrection`). -/
theorem curlCorrection_eq (d d' : ParentGeometry hT U X k) :
    S5.curlCorrection d = S5.curlCorrection d' :=
  funext fun V => complete_congr (geometry_inverse_eq d d') (geometry_covector_eq d d') _ _ _ _ V

/-- Two parent geometries of the same parent have the same `𝐝̃·` (`S5.totalDivergence`). -/
theorem totalDivergence_eq (d d' : ParentGeometry hT U X k) :
    S5.totalDivergence d = S5.totalDivergence d' := by
  funext W
  unfold S5.totalDivergence
  rw [geometry_inverse_eq d d', geometry_covector_eq d d']

/-- A solution of the mean equation (5.11) for one carrier is one for any other carrier
of the same parent. -/
theorem meanSolution_transport (d d' : ParentGeometry hT U X k)
    {f B : HierarchyTwistedProfile T k Vec3} {q : HierarchyTwistedProfile T k ℝ}
    (h : S5.MeanSolution d f B q) : S5.MeanSolution d' f B q := by
  have hops := ops_eq d d'
  exact ⟨hops ▸ h.momentum, hops ▸ h.phase_independent, hops ▸ h.pressure_phase_independent,
    h.endpoint⟩

/-- A solution of the transverse equation (5.15) for one carrier is one for any other
carrier of the same parent. -/
theorem transverseSolution_transport (d d' : ParentGeometry hT U X k)
    {f V : HierarchyTwistedProfile T k Vec3} {q : HierarchyTwistedProfile T k ℝ}
    (h : S5.TransverseSolution d f V q) : S5.TransverseSolution d' f V q := by
  have hops := ops_eq d d'
  exact ⟨hops ▸ h.momentum, h.transverse, hops ▸ h.mean_zero, h.initial, h.pressure_mean_zero⟩

/-- An expansion (`S5.IsExpansion`) for one carrier is an expansion for any other carrier
of the same parent: all objects are built from the coefficient profiles. -/
theorem isExpansion_transport (d d' : ParentGeometry hT U X k) {pU : Pressure} {t₀ : ℝ}
    {χ : PaperWaveCutoff t₀ T} {ℓ h : ℝ} {amp : ℝ → Vec3 → Vec3} {P : ℕ}
    {R S : HierarchyTwistedProfile T k Vec3}
    {u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)}
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) : S5.IsExpansion d' pU χ ℓ h amp P R S u := by
  have hops := ops_eq d d'
  have hcc := curlCorrection_eq d d'
  refine ⟨hu.residual, hu.activation, hu.leading_velocity, hu.leading_pressure,
    hu.first_correction, hu.first_mean, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, hu.top⟩
  · rw [← hcc]
    exact hu.correction p hp
  · obtain ⟨hm, hq⟩ := hu.mean p hp
    refine ⟨meanSolution_transport d d' ?_, hq⟩
    rw [← hops, ← hcc]
    exact hm
  · refine transverseSolution_transport d d' ?_
    rw [← hops, ← hcc]
    exact hu.transverse p hp

/-! ## `S5.Parent` and `TruncatedHierarchyParent` -/

/-- The standing hypotheses `S5.Parent` give a parent geometry `d` (coefficient profiles
of the parent) with the library hypotheses `TruncatedHierarchyParent d pU 𝖣 λ`; by
`isExpansion_transport` and its companions, every statement about one carrier transfers
to it. -/
theorem exists_truncatedHierarchyParent (hT : 0 < T) {pU : Pressure} {D lam : ℝ}
    (hP : S5.Parent T U X pU D lam) (hk : k ≠ 0) :
    ∃ d : ParentGeometry hT U X k, Nonempty (TruncatedHierarchyParent d pU D lam) := by
  obtain ⟨v, hv⟩ := hP.velocity_band
  obtain ⟨r, hr⟩ := hP.residual_band
  exact TruncatedHierarchyParent.exists_of_torus_bands_and_coercivity hT hP.time_le_one
    hP.scale_ge_two hP.frequency_ge_one hk hP.flow hP.velocity_smooth hP.pressure_smooth
    hP.velocity_periodic hP.deformation_le hP.inverse_deformation_le hP.gradient_le hP.coercive
    v r (fun t ht => funext fun x => (hv t ht).1 x) (fun t ht x => (hr t ht).1 x)
    (fun t ht => (hv t ht).2) (fun t ht => (hr t ht).2.1) (fun t ht => (hr t ht).2.2)

/-- Conversely, the library hypotheses `TruncatedHierarchyParent` together with the
remaining assumptions of §5.1 that it does not record (oddness and incompressibility of
`U`, smoothness and periodicity of the pressure, oddness of the residual, and the
coercivity (5.2)) give `S5.Parent`. -/
theorem parent_of_truncatedHierarchyParent {pU : Pressure} {D lam : ℝ}
    {d : ParentGeometry hT U X k} (data : TruncatedHierarchyParent d pU D lam)
    (hodd : ∀ t ∈ Icc 0 T, Function.Odd (U t))
    (hdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (U t) x = 0)
    (hp : ContDiffOn ℝ ∞ (Function.uncurry pU) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hpper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (pU t))
    (hRodd : ∀ t ∈ Icc 0 T, Function.Odd (momentumResidual (Icc 0 T) U pU t))
    (hcoer : ∀ t ∈ Icc 0 T, ∀ x v : Vec3,
      ⟪(fderiv ℝ (gradient (pU t)) x - fderiv ℝ (momentumResidual (Icc 0 T) U pU t) x) v, v⟫_ℝ ≤
        ‖v‖ ^ 2) :
    S5.Parent T U X pU D lam where
  time_le_one := data.time_le_one
  scale_ge_two := data.scale_ge_two
  frequency_ge_one := data.frequency_ge_one
  flow := data.flow
  velocity_smooth := data.velocity_smooth
  velocity_periodic := data.velocity_periodic
  velocity_odd := hodd
  divergence_free := hdiv
  velocity_band := ⟨data.torusVelocity, fun t ht =>
    ⟨fun x => congrFun (data.velocity_lift t ht) x, data.velocity_band t ht⟩⟩
  gradient_le := data.velocity_gradient_le
  deformation_le := data.deformation_le
  inverse_deformation_le := data.inverse_deformation_le
  pressure_smooth := hp
  pressure_periodic := hpper
  residual_odd := hRodd
  residual_band := ⟨data.torusResidual, fun t ht =>
    ⟨data.residual_lift t ht, data.residual_band t ht, data.residual_size t ht⟩⟩
  coercive := hcoer

/-! ## Elementary consequences of the standing hypotheses -/

section Standing

variable {pU : Pressure} {D lam t₀ : ℝ}

/-- `𝖣 ≥ 1`. -/
theorem Parent.scale_ge_one (hP : S5.Parent T U X pU D lam) : 1 ≤ D :=
  one_le_two.trans hP.scale_ge_two

/-- `λ > 0`. -/
theorem Parent.frequency_pos (hP : S5.Parent T U X pU D lam) : 0 < lam :=
  zero_lt_one.trans_le hP.frequency_ge_one

/-- The activation time lies in `[0,T]`. -/
theorem Launch.start_mem (hL : S5.Launch T X k lam t₀) : t₀ ∈ Icc 0 T :=
  ⟨hL.start_nonneg, hL.start_lt.le⟩

/-- `[t₀,T] ⊆ [0,T]`. -/
theorem Launch.active_subset (hL : S5.Launch T X k lam t₀) : Icc t₀ T ⊆ Icc 0 T :=
  Icc_subset_Icc_left hL.start_nonneg

/-- The time `T` is positive. -/
theorem Launch.end_pos (hL : S5.Launch T X k lam t₀) : 0 < T :=
  hL.start_nonneg.trans_lt hL.start_lt

/-- The velocity is Lipschitz in space, uniformly on `[0,T]`. -/
theorem Parent.exists_lipschitz (hT : 0 < T) (hP : S5.Parent T U X pU D lam) :
    ∃ K : NNReal, ∀ t ∈ Icc 0 T, LipschitzWith K (U t) :=
  exists_lipschitzWith_of_contDiffOn_periodic hT (hP.velocity_smooth.of_le (by simp))
    hP.velocity_periodic

/-- The odd parent flow fixes the origin: `X(t,0) = 0`. -/
theorem Parent.flow_origin (hT : 0 < T) (hP : S5.Parent T U X pU D lam) {t : ℝ}
    (ht : t ∈ Icc 0 T) : X 0 t 0 = 0 := by
  obtain ⟨Lp, hLp⟩ := Parent.exists_lipschitz hT hP
  have he := hP.flow.odd hLp hP.velocity_odd (left_mem_Icc.mpr hT.le) ht (0 : Vec3)
  rw [neg_zero] at he
  ext i
  have hi := congrArg (fun y : Vec3 => y i) he
  simp only [PiLp.neg_apply] at hi
  simpa only [PiLp.zero_apply] using (show (X 0 t 0) i = 0 by linarith)

/-- At the origin `M(t,0) = ∇U(t,0)`. -/
theorem Parent.strainField_origin (hT : 0 < T) (hP : S5.Parent T U X pU D lam) {t : ℝ}
    (ht : t ∈ Icc 0 T) : S5.strainField U X t 0 = fderiv ℝ (U t) 0 := by
  unfold S5.strainField
  rw [Parent.flow_origin hT hP ht]

/-- The central data of `S5.Origin` in the form used by the library seed lemmas:
`CenterWaveOn` at the parent gradient `∇U(t,0)`. -/
theorem Origin.centerWaveOn_gradient {center : ℝ → Vec3} (hP : S5.Parent T U X pU D lam)
    (hL : S5.Launch T X k lam t₀) (hO : S5.Origin T U X k D lam t₀ center) :
    CenterWaveOn (fun t => fderiv ℝ (U t) 0) (fun t => S5.waveVector X k t 0) center t₀ T D :=
  hO.wave.congr_gradient fun _ ht =>
    Parent.strainField_origin (Launch.end_pos hL) hP (Launch.active_subset hL ht)

/-- The launch covector recovered from the central covector at `t₀`,
`(D_aX(t₀,0))^T κ(t₀,0)`, is `k_*` (as in the library seed constructions). -/
theorem Launch.carrier_eq (hP : S5.Parent T U X pU D lam) (hL : S5.Launch T X k lam t₀) :
    (fderiv ℝ (X 0 t₀) (0 : Vec3)).adjoint (S5.waveVector X k t₀ 0) = k := by
  have hT := Launch.end_pos hL
  have hinv : (fderiv ℝ (X t₀ 0) (X 0 t₀ 0)).comp (fderiv ℝ (X 0 t₀) (0 : Vec3)) =
      ContinuousLinearMap.id ℝ Vec3 :=
    (hP.flow.labelDerivative_inverse hT (hP.velocity_smooth.of_le (by simp))
      hP.velocity_periodic (left_mem_Icc.mpr hT.le) (Launch.start_mem hL) (0 : Vec3)).1
  have h := congrArg (fun A : Vec3 →L[ℝ] Vec3 => A.adjoint k) hinv
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
  exact h

/-- The transported wave vector `κ(t,a)` is jointly smooth on `[0,T] × ℝ³`. -/
theorem Parent.waveVector_smooth (hT : 0 < T) (hP : S5.Parent T U X pU D lam) :
    ContDiffOn ℝ ∞ (Function.uncurry (S5.waveVector X k)) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
  hP.flow.contDiffOn_transportedCovector hT hP.velocity_smooth hP.velocity_periodic k

/-- The matrix `M(t,a)` is jointly smooth on `[0,T] × ℝ³`. -/
theorem Parent.strainField_smooth (hT : 0 < T) (hP : S5.Parent T U X pU D lam) :
    ContDiffOn ℝ ∞ (Function.uncurry (S5.strainField U X)) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
  hP.flow.contDiffOn_materialGradient hT hP.velocity_smooth hP.velocity_periodic

/-- `κ(t,a) ≠ 0` on `[0,T]` when `k_* ≠ 0`. -/
theorem Parent.waveVector_ne_zero (hT : 0 < T) (hP : S5.Parent T U X pU D lam) (hk : k ≠ 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) : S5.waveVector X k t a ≠ 0 :=
  transportedCovector_ne_zero_of_parent hT hP.flow hP.velocity_smooth hP.velocity_periodic hk t ht a

/-- The weight `γ(t) = λ^{3/4}|𝐚(t,0)|` is positive on `[t₀,T]`. -/
theorem Origin.weight_pos {center : ℝ → Vec3} (hP : S5.Parent T U X pU D lam)
    (hO : S5.Origin T U X k D lam t₀ center) :
    ∀ t ∈ Icc t₀ T, 0 < S5.weight lam center t := fun t ht =>
  mul_pos (Real.rpow_pos_of_pos (Parent.frequency_pos hP) _) (norm_pos_iff.mpr (hO.wave.nonzero t ht).2.1)

/-- The weight `γ(t) = λ^{3/4}|𝐚(t,0)|` is continuous on `[t₀,T]`. -/
theorem Origin.weight_continuousOn {center : ℝ → Vec3} (hO : S5.Origin T U X k D lam t₀ center) :
    ContinuousOn (S5.weight lam center) (Icc t₀ T) := by
  have hc : ContinuousOn center (Icc t₀ T) := fun t ht =>
    (hO.wave.amplitude t ht).continuousWithinAt
  exact continuousOn_const.mul hc.norm

/-- The weight `γ ≤ 1` on `[t₀,T]` (the normalization of §5.1). -/
theorem Origin.weight_le_one {center : ℝ → Vec3} (hO : S5.Origin T U X k D lam t₀ center) :
    ∀ t ∈ Icc t₀ T, S5.weight lam center t ≤ 1 :=
  hO.normalized

/-- The inverse weight `γ⁻¹` is bounded on `[t₀,T]`, as needed for the seminorm
properties of `S5.wNorm` (`wNorm_nonneg`, `wNorm_add_le`, ...). -/
theorem Origin.exists_inverse_weight_bound {center : ℝ → Vec3} (hP : S5.Parent T U X pU D lam)
    (hL : S5.Launch T X k lam t₀) (hO : S5.Origin T U X k D lam t₀ center) :
    ∃ B : ℝ, ∀ t ∈ Icc t₀ T, ‖(S5.weight lam center t)⁻¹‖ ≤ B :=
  inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr hL.start_lt.le)
    (Origin.weight_continuousOn hO) (Origin.weight_pos hP hO)

/-- `ℓ_* = 𝖣^{-a}` is positive. -/
theorem radius_pos (hP : S5.Parent T U X pU D lam) (a : ℕ) : 0 < S5.radius D a :=
  inv_pos.mpr (pow_pos (zero_lt_one.trans_le (Parent.scale_ge_one hP)) a)

/-- `h = λ^{-1/2}` is positive. -/
theorem width_pos (hP : S5.Parent T U X pU D lam) : 0 < S5.width lam :=
  Real.rpow_pos_of_pos (Parent.frequency_pos hP) _

/-- `h = λ^{-1/2} ≤ 1`. -/
theorem width_le_one (hP : S5.Parent T U X pU D lam) : S5.width lam ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hP.frequency_ge_one (by norm_num)

end Standing

end

end TorusEuler.Paper.Bridge
