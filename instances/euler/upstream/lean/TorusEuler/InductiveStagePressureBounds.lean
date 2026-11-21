import TorusEuler.HierarchyPhysicalPressureBounds
import TorusEuler.InductiveParentGeometry
import TorusEuler.InductiveStageVelocityJetBounds
import TorusEuler.ParentCoframeEstimates

/-! Fixed-order pressure estimates for the actual inductive approximation. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.InductiveEulerStage

open HierarchyTwistedProfile

noncomputable section

local notation "Time(" T ")" => Icc (0 : ℝ) T
local notation "Slab(" T ")" => (Set.prod (Time(T)) (univ : Set Vec3))
local notation "Scale(" P "," n ")" => (InductiveEulerParameters.frequency P n ^ (9 : ℕ))
local notation "Radius(" P "," n "," a ")" => ((Scale(P,n) ^ a)⁻¹)
local notation "Width(" freq ")" => (freq ^ (-1 / 2 : ℝ))

private theorem stagePressure_slice_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T t : ℝ} {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) Slab(T)) (ht : t ∈ Time(T)) : ContDiff ℝ ∞ (f t) :=
  contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

variable {P : InductiveEulerParameters} {n : ℕ} {activation T : ℝ}
  {s : InductiveEulerStage P n activation} {hT : 0 < T} {k : Vec3}

/-- Fixed-order geometric inputs to the pressure estimates on the actual parent slab. -/
structure StagePressureGeometryCaps (d : s.OnSlab hT k) (a : ℕ) (freq K Kparent : ℝ) : Prop where
  constant_ge_one : 1 ≤ K
  parent_constant_nonneg : 0 ≤ Kparent
  carrier : ‖k‖ ≤ Scale(P,n) * freq
  coframe_two : ∀ t ∈ Time(T), ∀ j ≤ 2, ∀ x,
    Radius(P,n,a) ^ j * ‖iteratedFDeriv ℝ j (fun y => d.geometry.inverse.val.val.val (t,y,0)) x‖ ≤
      K * Scale(P,n)
  coframe_one : ∀ t ∈ Time(T), ∀ j ≤ 1, ∀ x,
    Radius(P,n,a) ^ j * ‖iteratedFDeriv ℝ j (fun y => d.geometry.inverse.val.val.val (t,y,0)) x‖ ≤
      K * Scale(P,n) ^ (24 : ℕ)
  adjoint_one : ∀ t ∈ Time(T), ∀ j ≤ 1, ∀ x,
    Radius(P,n,a) ^ j * ‖iteratedFDeriv ℝ j
      (fun y => (d.geometry.inverse.val.val.val (t,y,0)).adjoint) x‖ ≤ K * Scale(P,n) ^ (24 : ℕ)
  strain_one : ∀ t ∈ Time(T), ∀ j ≤ 1, ∀ x,
    Radius(P,n,a) ^ j * ‖iteratedFDeriv ℝ j (fun y => d.geometry.strain.val.val.val (t,y,0)) x‖ ≤
      K * Scale(P,n) ^ (24 : ℕ)
  projection_one : ∀ t ∈ Time(T), ∀ j ≤ 1, ∀ x,
    Radius(P,n,a) ^ j * ‖iteratedFDeriv ℝ j
      (fun y => hierarchyLongitudinalProjection (d.geometry.covector.val.val.val (t,y,0))) x‖ ≤
      K * Scale(P,n) ^ (24 : ℕ)
  parent_gradient : ∀ t ∈ Time(T), SpatialHolderHalf 0 (fderiv ℝ (s.velocity t)) ∧
    spatialHolderHalfNorm 0 (fderiv ℝ (s.velocity t)) ≤ Kparent * Scale(P,n) ^ (2 : ℕ)

/-- The parent gradient estimate follows from the first and second Eulerian
jets. No conversion of the stage to a torus Fourier lift is needed here. -/
private theorem stageParentGradient_halfHolder_of_jets {u : Vec3 → Vec3} {R D : ℝ}
    (hU : ContDiff ℝ ∞ u) (hR : 0 ≤ R) (hD : 1 ≤ D)
    (hjet : ∀ j : ℕ, 1 ≤ j → j ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ j u x‖ ≤ R * D ^ j) :
    SpatialHolderHalf 0 (fderiv ℝ u) ∧ spatialHolderHalfNorm 0 (fderiv ℝ u) ≤ 3 * R * D ^ 2 := by
  have hs : ContDiff ℝ ∞ (fderiv ℝ u) := hU.fderiv_right (m := ∞) (by simp)
  have hj (j : ℕ) (hj : j ≤ 0 + 1) (x : Vec3) :
      ‖iteratedFDeriv ℝ j (fderiv ℝ u) x‖ ≤ R * D ^ 2 := by
    rw [norm_iteratedFDeriv_fderiv]
    exact (hjet (j + 1) (by omega) (by omega) x).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) hR)
  obtain ⟨hHolder, hNorm⟩ := spatialHolderHalfNorm_le_of_uniformJets (m := 0) hs (by positivity) hj
  refine ⟨hHolder, hNorm.trans_eq ?_⟩
  norm_num
  ring

set_option maxHeartbeats 2300000 in
/-- The pressure geometry constants are uniform over stages and use only the
fixed derivative orders one and two of the actual parent. -/
theorem exists_stagePressureGeometryCaps :
    ∃ K Kparent : ℝ, 1 ≤ K ∧ 0 ≤ Kparent ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {activation T : ℝ}
        {s : InductiveEulerStage P n activation} {hT : 0 < T} {k : Vec3}
        (d : s.OnSlab hT k), T ≤ 1 → 1 ≤ P.frequency n →
        ∀ {freq t₀ : ℝ}, 0 < freq → t₀ ∈ Time(T) → ‖labelWaveVector s.flow 0 0 k t₀‖ = freq →
        ∀ a : ℕ, 7 ≤ a → StagePressureGeometryCaps d a freq K Kparent := by
  obtain ⟨R, hR, hVel⟩ := exists_velocity_jet_bounds
  obtain ⟨C, hC, hParent⟩ := exists_parent_coefficientJetBounds R hR
  let K := 1 + ∑ j ∈ Finset.range 3, C j
  have hK : 1 ≤ K := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hC j)
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hCj (j : ℕ) (hj : j ≤ 2) : C j ≤ K :=
    (Finset.single_le_sum (fun x _ => hC x) (Finset.mem_range.mpr (by omega : j < 3))).trans
      (le_add_of_nonneg_left zero_le_one)
  have hR₂ := mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (hR 2)
  refine ⟨K, 3 * R 2, hK, hR₂, ?_⟩
  intro P n activation T s hT k d hT₁ hμ freq t₀ hfreq ht₀ hcenter a ha
  let D := Scale(P,n)
  let ell := Radius(P,n,a)
  have hD : 1 ≤ D := one_le_pow₀ hμ
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hEll : 0 < ell := inv_pos.mpr (pow_pos hDpos _)
  have hEll₁ : ell ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hD)
  have hScale : ell * D ^ (7 : ℕ) ≤ 1 := by
    calc
      _ ≤ ell * D ^ a := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD ha) hEll.le
      _ = 1 := inv_mul_cancel₀ (pow_pos hDpos _).ne'
  have hμD : P.frequency n ≤ D := by
    simpa only [pow_one] using pow_le_pow_right₀ hμ (show (1 : ℕ) ≤ 9 by decide)
  let hX := d.deformationOn.flow
  have hper (t : ℝ) (_ : t ∈ Time(T)) := s.periodic_velocity t
  have hF (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) : ‖fderiv ℝ (s.flow 0 t) x‖ ≤ D :=
    (((d.deformationOn.bounds t ht).2.1 x).2).trans hμD
  have hG (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) : ‖fderiv ℝ (s.flow t 0) (s.flow 0 t x)‖ ≤ D :=
    (((d.deformationOn.bounds t ht).2.2 (s.flow 0 t x)).2).trans hμD
  have hUjet (m j : ℕ) (hj : 1 ≤ j) (hm : j ≤ m) (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) :=
    hVel s hμ m j hj hm t (d.subset ht) x
  have hJets := hParent hT hT₁ hD hX d.smooth_velocity hper hF hG hUjet k hfreq ht₀ hcenter
  have hCarrier : ‖k‖ ≤ D * freq := (div_le_iff₀ hfreq).mp
    (hX.norm_normalizedLabelWaveVector_bounds hT (d.smooth_velocity.of_le (by simp)) hper
      ht₀ ht₀ 0 k hD hfreq hcenter (hF t₀ ht₀ 0) (hG t₀ ht₀ 0) (hF t₀ ht₀ 0) (hG t₀ ht₀ 0)).1
  have hGval (t : ℝ) (ht : t ∈ Time(T)) :
      (fun x => d.geometry.inverse.val.val.val (t,x,0)) =
        fun x => fderiv ℝ (s.flow t 0) (s.flow 0 t x) :=
    funext fun x => d.geometry.inverse_value (t,x,0) ⟨ht, mem_univ _⟩
  have hMval (t : ℝ) (ht : t ∈ Time(T)) :
      (fun x => d.geometry.strain.val.val.val (t,x,0)) =
        fun x => fderiv ℝ (s.velocity t) (s.flow 0 t x) :=
    funext fun x => d.geometry.strain_value (t,x,0) ⟨ht, mem_univ _⟩
  have hκval (t : ℝ) (ht : t ∈ Time(T)) :
      (fun x => d.geometry.covector.val.val.val (t,x,0)) = fun x => labelWaveVector s.flow 0 x k t :=
    funext fun x => d.geometry.covector_value (t,x,0) ⟨ht, mem_univ _⟩
  have hUp {u : ℝ} {j q : ℕ} (hj : j ≤ 1) (hq : q ≤ 24) (hu : 0 ≤ u)
      (h : u ≤ C j * D ^ q) : ell ^ j * u ≤ K * D ^ (24 : ℕ) :=
    (mul_le_of_le_one_left hu (pow_le_one₀ hEll.le hEll₁)).trans
      (h.trans (mul_le_mul (hCj j (by omega)) (pow_le_pow_right₀ hD hq) (pow_nonneg hD₀ _) hK₀))
  refine ⟨hK, hR₂, hCarrier, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    refine scaledCoframe_jet_bound hEll.le hD hK₀ hScale ?_
    intro j hj x
    rw [hGval t ht]
    exact (hJets j t ht x).2.1.trans
      (mul_le_mul_of_nonneg_right (hCj j hj) (pow_nonneg hD₀ _))
  · intro t ht j hj x
    rw [hGval t ht]
    exact hUp hj (by omega) (norm_nonneg _) (hJets j t ht x).2.1
  · intro t ht j hj x
    rw [show (fun y => (d.geometry.inverse.val.val.val (t,y,0)).adjoint) =
      fun y => (fderiv ℝ (s.flow t 0) (s.flow 0 t y)).adjoint from
      congrArg (fun f : Vec3 → Vec3 →L[ℝ] Vec3 => fun y => (f y).adjoint) (hGval t ht)]
    exact hUp hj (by omega) (norm_nonneg _) (hJets j t ht x).2.2.1
  · intro t ht j hj x
    rw [hMval t ht]
    exact hUp hj (by omega) (norm_nonneg _) (hJets j t ht x).2.2.2.1
  · intro t ht j hj x
    rw [show (fun y => hierarchyLongitudinalProjection (d.geometry.covector.val.val.val (t,y,0))) =
      fun y => hierarchyLongitudinalProjection (labelWaveVector s.flow 0 y k t) from
      congrArg (fun f : Vec3 → Vec3 => hierarchyLongitudinalProjection ∘ f) (hκval t ht)]
    exact hUp hj (by omega) (norm_nonneg _) (hJets j t ht x).2.2.2.2.2.2
  · intro t ht
    exact stageParentGradient_halfHolder_of_jets (stagePressure_slice_smooth d.smooth_velocity ht)
      (hR 2) hD (fun j hj hj₂ x => hUjet 2 j hj hj₂ t ht x)

/-- Keep the fixed coframe coefficient in the scalar graph factor, outside
all powers of the parent scale. -/
theorem stageMeanPressure_graphCap_eq {a r : ℕ} {D freq L count Clevel : ℝ} :
    13824 * (L * D ^ (a + 1)) ^ 2 *
        (count * Clevel * D ^ (6 * r) * freq ^ (-5 / 2 : ℝ)) =
      (13824 * L ^ 2 * count * Clevel) * D ^ (6 * r + 2 * (a + 1)) * freq ^ (-5 / 2 : ℝ) := by
  rw [mul_pow, ← pow_mul, pow_add D (6 * r), Nat.mul_comm 2 (a + 1)]
  ring

/-- Fixed-order factor for the mean pressure estimate with the exact graph
Hölder budgets of its mean velocity and forcing. -/
noncomputable def stageMeanPressureCost (L count Clevel Cparent : ℝ) : ℝ :=
  48 * ‖pressureHessianMultiplier‖ * (13824 * L ^ 2 * count * Clevel) * (1 + Cparent)

/-- The closed-slab Hessian estimate and the graph budgets give a pointwise
operator-norm estimate with the same fixed-order constant. -/
theorem norm_meanPressureHessian_at_stage_of_graphCaps
    {T D freq L count Clevel Cparent : ℝ} {a r : ℕ} {q : Pressure}
    (hD : 1 ≤ D) (hfreq : 0 < freq) (hcount : 0 ≤ count)
    (hClevel : 0 ≤ Clevel) (hCparent : 0 ≤ Cparent) :
    let Q := L * D ^ (a + 1)
    let M := 13824 * Q ^ 2 * (count * Clevel * D ^ (6 * r) * freq ^ (-5 / 2 : ℝ))
    (∀ t ∈ Icc 0 T, SpatialHolderHalf 0 (fderiv ℝ (gradient (q t))) ∧
      spatialHolderHalfNorm 0 (fderiv ℝ (gradient (q t))) ≤
        (48 * ‖pressureHessianMultiplier‖) * (M + (Cparent * D ^ 2) * M)) →
    ∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (gradient (q t)) x‖ ≤
      stageMeanPressureCost L count Clevel Cparent * D ^ (6 * r + 2 * (a + 1) + 2) *
        freq ^ (-5 / 2 : ℝ) := by
  intro Q M hH t ht x
  let H := fderiv ℝ (gradient (q t))
  let Cmean := 13824 * L ^ 2 * count * Clevel
  have hCmean : 0 ≤ Cmean := by dsimp only [Cmean]; positivity
  have he : M = Cmean * D ^ (6 * r + 2 * (a + 1)) * freq ^ (-5 / 2 : ℝ) :=
    stageMeanPressure_graphCap_eq
  have hM : 0 ≤ M := he ▸ (by dsimp only [Cmean]; positivity)
  have hRate := meanPressureHessian_rate_absorption (b := 6 * r + 2 * (a + 1))
    hD hfreq hCparent hCmean hM le_rfl he.le he.le
  obtain ⟨hholder, hNorm⟩ := hH t ht
  obtain ⟨_, hSup, hQuot⟩ := (spatialHolderHalf_zero_iff H).mp hholder
  have hSig : 0 ≤ spatialHolderHalfSeminorm H := by
    have h := le_ciSup hQuot ((0 : Vec3), (0 : Vec3))
    have h0 : spatialHolderHalfQuotient H (0, 0) = 0 := by simp [spatialHolderHalfQuotient]
    rw [h0] at h
    exact h
  have hPoint : ‖H x‖ ≤ spatialHolderHalfNorm 0 H := by
    rw [spatialHolderHalfNorm_zero_eq]
    exact (norm_le_spatialSupNorm hSup x).trans (le_add_of_nonneg_right hSig)
  exact hPoint.trans (hNorm.trans hRate)

private theorem stagePressure_sum_is_mean {H : ℕ}
    (d : s.OnSlab hT k) (b : PhysicalApproximationData d.geometry s.pressure H)
    (f : ℕ → HierarchyTwistedProfile T k Vec3)
    (hf : ∀ i ∈ Finset.Icc 2 H, b.operators.average (f i) = f i) :
    HierarchyPeriodicProfile.PhaseIndependent (∑ i ∈ Finset.Icc 2 H, f i).val.val := by
  have h : b.operators.average (∑ i ∈ Finset.Icc 2 H, f i) = ∑ i ∈ Finset.Icc 2 H, f i := by
    rw [map_sum]
    exact Finset.sum_congr rfl hf
  exact HierarchyPeriodicProfile.phaseIndependent_of_profilePhaseAverage_eq_self hT _
    (congrArg Subtype.val h)

set_option maxHeartbeats 1800000 in
/-- The exact stage mean Hessian from order-two measured levels. The coframe
constant is fixed at order two and does not enter a parent exponent. -/
theorem norm_stageMeanPressureHessian_of_levels {H a r : ℕ}
    (d : s.OnSlab hT k) (b : PhysicalApproximationData d.geometry s.pressure H) (hH : 1 ≤ H)
    {freq K Kparent Clevel : ℝ} (cap : StagePressureGeometryCaps d a freq K Kparent)
    (hμ : 1 ≤ P.frequency n) (hfreq : 1 ≤ freq) (hClevel : 0 ≤ Clevel)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hLevel : ∀ i ∈ Finset.Icc 2 H, HierarchyLevelBound
      (actualMeasuredLevels b.operators b.profiles H b.leading.completionSwitch b.parentResidual freq
        (zero_le_one.trans hfreq) Radius(P,n,a) Width(freq) hT ht₀ htT γ hγ hpos)
      freq (Scale(P,n) ^ r) Clevel 2 i) :
    ∀ t ∈ Time(T), ∀ x, ‖fderiv ℝ (gradient (b.meanPressure t)) x‖ ≤
      stageMeanPressureCost K (Finset.Icc 2 H).card Clevel Kparent *
        Scale(P,n) ^ (6 * r + 2 * (a + 1) + 2) * freq ^ (-5 / 2 : ℝ) := by
  let D := Scale(P,n)
  let ell := Radius(P,n,a)
  let h := Width(freq)
  let Q := K * D ^ (a + 1)
  let S := Finset.Icc 2 H
  let M₀ := (S.card : ℝ) * Clevel * D ^ (6 * r) * freq ^ (-5 / 2 : ℝ)
  let M := 13824 * Q ^ 2 * M₀
  let A : Velocity := fun t => s.flow t 0
  let W := ∑ i ∈ S, b.profiles.B i
  let F := ∑ i ∈ S, b.meanForceAt i
  have hD : 1 ≤ D := one_le_pow₀ hμ
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hEll : 0 < ell := inv_pos.mpr (pow_pos (zero_lt_one.trans_le hD) _)
  have hK := zero_le_one.trans cap.constant_ge_one
  have hQ : 1 ≤ Q := one_le_mul_of_one_le_of_one_le cap.constant_ge_one (one_le_pow₀ hD)
  have hQD : ell⁻¹ * (K * D) ≤ Q := by
    change ((D ^ a)⁻¹)⁻¹ * (K * D) ≤ K * D ^ (a + 1)
    rw [inv_inv, pow_succ]
    exact le_of_eq (by ring)
  let hX := d.deformationOn.flow
  have hper (t : ℝ) (_ : t ∈ Time(T)) := s.periodic_velocity t
  have hDiv (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) := s.divergence_free t (d.subset ht) x
  have hA : ContDiffOn ℝ ∞ (Function.uncurry A) Slab(T) :=
    hX.contDiffOn_inverseLabelFlow hT d.smooth_velocity hper
  have hEqW : b.meanCorrection = graphRead A W := b.meanCorrection_eq_correctionGraphSum hH
  have hWi := stagePressure_sum_is_mean d b b.profiles.B (fun i _ => b.solvers.construct_average_B H
    b.leading.completionSwitch b.parentResidual b.parentResidual_average b.leading.output i)
  have hFi := stagePressure_sum_is_mean d b b.meanForceAt b.average_meanForceAt
  have hProfiles := b.meanProfileSums_le_of_actualLevels hfreq (one_le_pow₀ hD) hClevel
    ht₀ htT γ hγ hpos hLevel
  have hAbsorb := meanOrderTwoBudget_le_parentPower (P := H) (r := r) (D := D) (K := 1) (loss := D ^ r)
    (zero_le_one.trans hfreq) hClevel (pow_nonneg hD₀ _) (by simp)
  have hProfile (f : HierarchyTwistedProfile T k Vec3)
      (hf : unweightedSeminorm False ell h 2 hT f ≤
        (S.card : ℝ) * (Clevel * (D ^ r) ^ 6 * freq ^ (-5 / 2 : ℝ))) :
      unweightedSeminorm False ell h 2 hT f ≤ M₀ := by
    exact hf.trans (by simpa only [S, M₀, one_pow, mul_one] using hAbsorb)
  have hGraph (f : HierarchyTwistedProfile T k Vec3)
      (hi : HierarchyPeriodicProfile.PhaseIndependent f.val.val)
      (hf : unweightedSeminorm False ell h 2 hT f ≤ M₀) (t : ℝ) (ht : t ∈ Time(T)) :
      SpatialHolderHalf 1 (graphRead A f t) ∧ spatialHolderHalfNorm 1 (graphRead A f t) ≤ M := by
    let B (x : Vec3) := d.geometry.inverse.val.val.val (t,x,0)
    have hB : ∀ x, B (A t x) = fderiv ℝ (A t) x :=
      fun x => ((d.geometry.inverseGraph_values hX d.smooth_velocity hper).2 t ht x 0).1
    have hBreg : ContDiff ℝ ∞ B :=
      (HierarchySmoothProfile.contDiff_labelPhase_slice d.geometry.inverse.val.val ht).comp
        (contDiff_id.prodMk contDiff_const)
    obtain ⟨hh, hn⟩ := spatialHolderHalf_graphRead_independent_le_unweighted hT ht hEll
      (mul_nonneg hK hD₀) hQ hQD
      (stagePressure_slice_smooth hA ht) hB hBreg (cap.coframe_two t ht) f hi
    exact ⟨hh, hn.trans (mul_le_mul_of_nonneg_left hf (by positivity))⟩
  have hVreg : ContDiffOn ℝ ∞ (Function.uncurry b.meanCorrection) Slab(T) :=
    HierarchySmoothProfile.contDiffOn_graphRead k _ hA
  have hQreg : ContDiffOn ℝ ∞ (Function.uncurry b.meanPressure) Slab(T) :=
    HierarchySmoothProfile.contDiffOn_graphRead k _ hA
  have hVper : ∀ t ∈ Time(T), SpatiallyPeriodic (b.meanCorrection t) :=
    fun t ht => spatiallyPeriodic_inverseParentGraphRead hT hX d.smooth_velocity hper _ ht
  have hFper : ∀ t ∈ Time(T), SpatiallyPeriodic (b.meanForce t) :=
    fun t ht => spatiallyPeriodic_inverseParentGraphRead hT hX d.smooth_velocity hper _ ht
  have hQper : ∀ t ∈ Time(T), SpatiallyPeriodic (b.meanPressure t) :=
    fun t ht => spatiallyPeriodic_inverseParentGraphRead hT hX d.smooth_velocity hper _ ht
  have hMean := meanPressureHessian_closedSlab_bound (MV := M) (Mf := M) hT
    (d.smooth_velocity.of_le (by simp)) (hVreg.of_le (by simp))
    (fun _ ht => stagePressure_slice_smooth hQreg ht) hQper hper hVper hFper hDiv
    (b.meanCorrection_divergence_eq_zero hH hX d.smooth_velocity hper hDiv)
    (fun _ ht x => b.meanCorrection_linearizedMomentum hH hX d.smooth_velocity hper ht x)
    cap.parent_gradient (by
      rw [hEqW]
      exact hGraph W hWi (hProfile W hProfiles.1))
    (hGraph F hFi (hProfile F hProfiles.2))
  exact norm_meanPressureHessian_at_stage_of_graphCaps (a := a) (r := r)
    (L := K) (count := (Finset.Icc 2 H).card) (Clevel := Clevel) (q := b.meanPressure)
    hD (zero_lt_one.trans_le hfreq) (Nat.cast_nonneg _) hClevel cap.parent_constant_nonneg hMean.1

/-- The fixed-order coefficient of the higher oscillatory Hessian. -/
def stageHigherPressureCost (K count Clevel : ℝ) : ℝ :=
  12 * count * Clevel * K ^ 2 * (8 + 32 * (K + 1))

/-- A single parent exponent covers all three pressure contributions. -/
def stagePressureExponent (a r leadingPower : ℕ) : ℕ :=
  max leadingPower (max (max a 1 + 48 + (max 24 a + r)) (6 * r + 2 * (a + 1) + 2))

/-- The scalar to include in the schedule's step entry at the selected depth.
The leading coefficient and the recurrence's level constant can be read
from that same depth table. -/
def stagePressureCost (depth : ℕ) (K Kparent Clevel Clead : ℝ) : ℝ :=
  Clead + stageHigherPressureCost K (Finset.Icc 2 depth).card Clevel +
    stageMeanPressureCost K (Finset.Icc 2 depth).card Clevel Kparent

theorem stagePressureCost_nonneg (depth : ℕ) {K Kparent Clevel Clead : ℝ}
    (hK : 0 ≤ K) (hKparent : 0 ≤ Kparent) (hClevel : 0 ≤ Clevel) (hClead : 0 ≤ Clead) :
    0 ≤ stagePressureCost depth K Kparent Clevel Clead := by
  unfold stagePressureCost stageHigherPressureCost stageMeanPressureCost
  positivity

/-- At the induction's radius and loss, the mean pressure power covers the
higher pressure power and any leading power below the same cap. -/
theorem stagePressureExponent_eq_mean_of_le {a r leadingPower : ℕ}
    (ha : 24 ≤ a) (hr : 9 ≤ r) (hLead : leadingPower ≤ 6 * r + 2 * (a + 1) + 2) :
    stagePressureExponent a r leadingPower = 6 * r + 2 * (a + 1) + 2 := by
  have hHigher : max a 1 + 48 + (max 24 a + r) ≤ 6 * r + 2 * (a + 1) + 2 := by
    rw [max_eq_left (by omega : 1 ≤ a), max_eq_right ha]
    omega
  unfold stagePressureExponent
  rw [max_eq_right hHigher, max_eq_right hLead]

set_option maxHeartbeats 1300000 in
/-- The higher-pressure graph estimate with its fixed stage coefficient.
Support gives the same estimate before the amplitude is positive. -/
theorem norm_stageHigherPressureHessian_of_levels {H a r : ℕ}
    (d : s.OnSlab hT k) (b : PhysicalApproximationData d.geometry s.pressure H) (hH : 1 ≤ H)
    {freq K Kparent Clevel : ℝ} (cap : StagePressureGeometryCaps d a freq K Kparent)
    (hμ : 1 ≤ P.frequency n) (hfreq : 1 ≤ freq) (hClevel : 0 ≤ Clevel)
    {t₀ : ℝ} {S : Set Vec3} (hS : IsClosed S) (hInactive : b.leading.Inactive t₀ S)
    (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγ₁ : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hLevel : ∀ m ∈ Finset.Icc 1 2, ∀ i ∈ Finset.Icc 2 H, HierarchyLevelBound
      (actualMeasuredLevels b.operators b.profiles H b.leading.completionSwitch b.parentResidual freq
        (zero_le_one.trans hfreq) Radius(P,n,a) Width(freq) hT ht₀ htT γ hγ hpos)
      freq (Scale(P,n) ^ r) Clevel m i) :
    ∀ t ∈ Time(T), ∀ x, ‖fderiv ℝ (gradient (b.higherOscillatoryPressure t)) x‖ ≤
      stageHigherPressureCost K (Finset.Icc 2 H).card Clevel *
        Scale(P,n) ^ (max a 1 + 48 + (max 24 a + r)) * freq ^ (-5 / 12 : ℝ) := by
  let D := Scale(P,n)
  let ell := Radius(P,n,a)
  let h := Width(freq)
  have hD : 1 ≤ D := one_le_pow₀ hμ
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hEll : 0 < ell := inv_pos.mpr (pow_pos (zero_lt_one.trans_le hD) _)
  have hElt : ell⁻¹ = D ^ a := inv_inv _
  have hK := zero_le_one.trans cap.constant_ge_one
  have hJet : 0 ≤ K * D ^ (24 : ℕ) := by positivity
  have hA : 0 ≤ D ^ a := by positivity
  have hL : 0 ≤ D ^ r := by positivity
  have hh := b.norm_higherOscillatoryPressure_hessian_le_of_actualLevels hH
    d.deformationOn.flow d.smooth_velocity (fun t _ => s.periodic_velocity t) hS hInactive
    hfreq hEll (h := h) rfl hElt.le cap.carrier hClevel hL hJet ht₀ htT γ hγ hpos hγ₁
    cap.coframe_one cap.adjoint_one cap.strain_one cap.projection_one hLevel
  have hPower := higherPressure_prefactor_le_parentPower (P := H) (a := a) (b := r) (c := 1)
    (D := D) (B := K) (L := 1) (Kwave := D) (Aell := D ^ a)
    hD hJet hD₀ hA hL hClevel le_rfl (by simp) le_rfl (by simp) (le_rfl (a := Clevel))
  intro t ht x
  refine (hh t ht x).trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (zero_le_one.trans hfreq) _))
  simpa only [PhysicalApproximationData.higherOscillatoryHessianPrefactor, stageHigherPressureCost, mul_one]
    using hPower

set_option maxHeartbeats 1800000 in
/-- The pressure slot of the common stage installer. The three profiles are
from the same selected approximation, and all powers are absolute once the
radius, recurrence loss, and signed leading estimate have been fixed. -/
theorem potential_hessian_upper_of_actualStageLevels {H a r leadingPower stepPower : ℕ}
    (d : s.OnSlab hT k) (b : PhysicalApproximationData d.geometry s.pressure H)
    (props : PhysicalApproximationProperties b) (hH : 1 ≤ H)
    {freq K Kparent Clevel Clead Γ : ℝ} (cap : StagePressureGeometryCaps d a freq K Kparent)
    (hμ : 1 ≤ P.frequency n) (hfreq : 1 ≤ freq) (hClevel : 0 ≤ Clevel) (hClead : 0 ≤ Clead)
    {t₀ : ℝ} {S : Set Vec3} (hS : IsClosed S) (hInactive : b.leading.Inactive t₀ S)
    (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγ₁ : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hLevel : ∀ m ∈ Finset.Icc 1 2, ∀ i ∈ Finset.Icc 2 H, HierarchyLevelBound
      (actualMeasuredLevels b.operators b.profiles H b.leading.completionSwitch b.parentResidual freq
        (zero_le_one.trans hfreq) Radius(P,n,a) Width(freq) hT ht₀ htT γ hγ hpos)
      freq (Scale(P,n) ^ r) Clevel m i)
    (hLead : ∀ t ∈ Time(T), ∀ x v,
      ⟪v, fderiv ℝ (gradient (b.leadingPressure t)) x v⟫_ℝ ≤
        (Clead * Scale(P,n) ^ leadingPower * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2)
    (hPower : stagePressureExponent a r leadingPower ≤ stepPower)
    (hCost : stagePressureCost H K Kparent Clevel Clead ≤ Γ) :
    ∀ t ∈ Time(T), ∀ x v,
      ⟪v, fderiv ℝ (gradient (b.potential props t).lift) x v⟫_ℝ ≤
        ⟪v, fderiv ℝ (gradient (s.pressure t)) x v⟫_ℝ +
          ((Γ * Scale(P,n) ^ stepPower) * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2 := by
  let D := Scale(P,n)
  let count : ℝ := (Finset.Icc 2 H).card
  let C₂ := stageMeanPressureCost K count Clevel Kparent
  let C₁ := stageHigherPressureCost K count Clevel
  let e₂ := 6 * r + 2 * (a + 1) + 2
  let e₁ := max a 1 + 48 + (max 24 a + r)
  have hD : 1 ≤ D := one_le_pow₀ hμ
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hK := zero_le_one.trans cap.constant_ge_one
  have hKp := cap.parent_constant_nonneg
  have hCount : 0 ≤ count := Nat.cast_nonneg _
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁, stageHigherPressureCost]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp only [C₂, stageMeanPressureCost]; positivity
  have heLead : leadingPower ≤ stepPower := (le_max_left _ _).trans hPower
  have he₁ : e₁ ≤ stepPower := ((le_max_left e₁ e₂).trans (le_max_right leadingPower _)).trans hPower
  have he₂ : e₂ ≤ stepPower := ((le_max_right e₁ e₂).trans (le_max_right leadingPower _)).trans hPower
  have hStage : Clead * D ^ leadingPower + C₁ * D ^ e₁ + C₂ * D ^ e₂ ≤ Γ * D ^ stepPower := by
    set B := D ^ stepPower
    have hB : 0 ≤ B := pow_nonneg hD₀ _
    calc
      _ ≤ Clead * B + C₁ * B + C₂ * B :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD heLead) hClead)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD he₁) hC₁))
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD he₂) hC₂)
      _ = stagePressureCost H K Kparent Clevel Clead * B := by
        change _ = (Clead + C₁ + C₂) * B
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCost hB
  have hMean := norm_stageMeanPressureHessian_of_levels d b hH (r := r) cap hμ hfreq hClevel
    ht₀ htT γ hγ hpos (hLevel 2 (by decide))
  have hHigher := norm_stageHigherPressureHessian_of_levels d b hH (r := r) cap hμ hfreq hClevel
    hS hInactive ht₀ htT γ hγ hpos hγ₁ hLevel
  exact b.potential_hessian_upper_at_stepScale hH d.deformationOn.flow d.smooth_velocity
    (fun t _ => s.periodic_velocity t) props
    (fun _ ht => (stagePressure_slice_smooth d.smooth_pressure ht).of_le (by simp))
    hfreq (mul_nonneg hC₁ (pow_nonneg hD₀ _)) (mul_nonneg hC₂ (pow_nonneg hD₀ _))
    hStage hLead hHigher hMean

end

end TorusEuler.InductiveEulerStage
