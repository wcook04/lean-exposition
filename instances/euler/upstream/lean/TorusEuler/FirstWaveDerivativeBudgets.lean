import TorusEuler.FirstWaveLocalized
import TorusEuler.WavePressureCenter
import TorusEuler.FirstWaveHierarchyInput
import TorusEuler.LocalizedAmplitudeComparison
import TorusEuler.CoframeDerivativeBounds
import TorusEuler.HierarchyActualNorms

/-! The initial weighted velocity and pressure derivative budgets for the actual first wave. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

private theorem norm_iteratedFDeriv_rightSlice_le
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : P × Vec3 → E}
    (hf : ContDiff ℝ ∞ f) (p : P) (a : Vec3) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun x => f (p, x)) a‖ ≤
      ‖iteratedFDeriv ℝ m f (p, a)‖ := by
  let L := LinearIsometry.inr (𝕜 := ℝ) (E := P) (F := Vec3)
  let g (z : P × Vec3) := f (z + (p, 0))
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have he : g ∘ L.toContinuousLinearMap = fun x => f (p, x) := by
    funext x
    simp [g, L]
  rw [← he, L.toContinuousLinearMap.iteratedFDeriv_comp_right hg a (by simp)]
  have hjet : iteratedFDeriv ℝ m g (L.toContinuousLinearMap a) = iteratedFDeriv ℝ m f (p, a) := by
    rw [show iteratedFDeriv ℝ m g (L.toContinuousLinearMap a) =
      iteratedFDeriv ℝ m f (L.toContinuousLinearMap a + (p, 0)) from
      iteratedFDeriv_comp_add_right m (p, 0) (L.toContinuousLinearMap a)]
    simp [L]
  rw [hjet]
  exact (iteratedFDeriv ℝ m f (p, a)).norm_compContinuous_linearIsometry_le (fun _ => L)

/-- Smooth families of periodic fields have uniform joint Fréchet derivative
bounds over compact parameter sets. The same constants bound all spatial
derivatives of each member of the family. -/
theorem exists_uniformJetBounds_of_contDiff_periodic
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set P}
    (hK : IsCompact K) {f : P × Vec3 → E} (hf : ContDiff ℝ ∞ f)
    (hper : ∀ p, SpatiallyPeriodic (fun x => f (p, x))) :
    ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧ ∀ m p, p ∈ K → ∀ a,
      ‖iteratedFDeriv ℝ m f (p, a)‖ ≤ B m ∧
      ‖iteratedFDeriv ℝ m (fun x => f (p, x)) a‖ ≤ B m := by
  have hBound (m : ℕ) := (hK.prod isCompact_centeredCell).exists_bound_of_continuousOn
    (hf.continuous_iteratedFDeriv (m := m) (by simp)).continuousOn
  choose C hC using hBound
  refine ⟨fun m => max 0 (C m), fun m => le_max_left _ _, ?_⟩
  intro m p hp a
  obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell a
  let z : P × Vec3 := (p, a - latticeVector n)
  let δ : P × Vec3 := (0, latticeVector n)
  have hz : z + δ = (p, a) := by simp [z, δ]
  have hshift : (fun x : P × Vec3 => f (x + δ)) = f := by
    funext x
    change f (x.1 + 0, x.2 + latticeVector n) = f x
    rw [add_zero]
    exact hper x.1 n x.2
  have hjet := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) m δ z
  rw [hshift, hz] at hjet
  have hb : ‖iteratedFDeriv ℝ m f (p, a)‖ ≤ max 0 (C m) := by
    rw [← hjet]
    exact (hC m z ⟨hp, hn⟩).trans (le_max_right _ _)
  exact ⟨hb, (norm_iteratedFDeriv_rightSlice_le hf p a m).trans hb⟩

private theorem spatiallyPeriodic_firstWaveCos :
    SpatiallyPeriodic (fun a : Vec3 => Real.cos (2 * Real.pi * a 1)) := by
  intro n a
  change Real.cos (2 * Real.pi * (a 1 + (n 1 : ℝ))) = _
  rw [mul_add, mul_comm (2 * Real.pi) (n 1 : ℝ)]
  exact Real.cos_periodic.int_mul (n 1) (2 * Real.pi * a 1)

private theorem spatiallyPeriodic_firstWaveSweep (t : ℝ) : SpatiallyPeriodic (firstWaveSweep t) := by
  intro n a
  exact congrArg (fun x : ℝ => t * (2 * Real.pi * x)) (spatiallyPeriodic_firstWaveCos n a)

theorem spatiallyPeriodic_firstWaveSmoothSeed (s c t : ℝ) :
    SpatiallyPeriodic (firstWaveSmoothSeed s c t) := by
  intro n a
  unfold firstWaveSmoothSeed
  rw [spatiallyPeriodic_firstWaveSweep t n a]

/-- The exact seed is linear in its initial amplitude scale. -/
theorem firstWaveSmoothSeed_scale (s c t : ℝ) (a : Vec3) :
    firstWaveSmoothSeed s c t a = c • firstWaveSmoothSeed s 1 t a := by
  let z := firstWaveSweep t a
  let e (i : Fin 3) : Vec3 := EuclideanSpace.single i 1
  change (c * z / (1 + z ^ 2)) • e 0 + (c / (1 + z ^ 2)) • e 1 +
    (-s * c * Real.arctan z) • e 2 =
    c • ((1 * z / (1 + z ^ 2)) • e 0 + (1 / (1 + z ^ 2)) • e 1 +
      (-s * 1 * Real.arctan z) • e 2)
  rw [show c * z / (1 + z ^ 2) = c * (1 * z / (1 + z ^ 2)) by ring,
    show c / (1 + z ^ 2) = c * (1 / (1 + z ^ 2)) by ring,
    show -s * c * Real.arctan z = c * (-s * 1 * Real.arctan z) by ring]
  simp only [smul_add, smul_smul]

/-- The unit-scale first seed is smooth jointly in the shear ratio, time and
label. This supplies constants uniform over bounded ratios. -/
theorem contDiff_firstWaveSmoothSeed_unit_joint :
    ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × Vec3 => firstWaveSmoothSeed q.1.1 1 q.1.2 q.2) := by
  let z (q : (ℝ × ℝ) × Vec3) := firstWaveSweep q.1.2 q.2
  let e (i : Fin 3) : Vec3 := EuclideanSpace.single i 1
  have hz : ContDiff ℝ ∞ z :=
    contDiff_firstWaveSweep.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
  have hs : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × Vec3 => q.1.1) := contDiff_fst.comp contDiff_fst
  have hd : ContDiff ℝ ∞ (fun q => 1 + z q ^ 2) := contDiff_const.add (hz.pow 2)
  have hn (q : (ℝ × ℝ) × Vec3) : 1 + z q ^ 2 ≠ 0 := by positivity
  change ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × Vec3 =>
    (1 * z q / (1 + z q ^ 2)) • e 0 + (1 / (1 + z q ^ 2)) • e 1 +
      (-q.1.1 * 1 * Real.arctan (z q)) • e 2)
  simp only [one_mul, mul_one]
  exact (((hz.div hd hn).smul contDiff_const).add
    ((contDiff_const.div hd hn).smul contDiff_const)).add
    ((hs.neg.mul (Real.contDiff_arctan.comp hz)).smul contDiff_const)

/-- On the first-wave slab the exact spatial seed jets are bounded by the
initial amplitude scale, uniformly over bounded shear ratios and all labels. -/
theorem exists_firstWaveSmoothSeedJetBounds :
    ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧ ∀ m s c t a,
      |s| ≤ 1 → t ∈ Icc (0 : ℝ) 1 →
      ‖iteratedFDeriv ℝ m (firstWaveSmoothSeed s c t) a‖ ≤ B m * |c| := by
  let K := Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let f (q : (ℝ × ℝ) × Vec3) := firstWaveSmoothSeed q.1.1 1 q.1.2 q.2
  obtain ⟨B, hB, hJet⟩ := exists_uniformJetBounds_of_contDiff_periodic
    (K := K) (f := f) (isCompact_Icc.prod isCompact_Icc) contDiff_firstWaveSmoothSeed_unit_joint
    (fun p => spatiallyPeriodic_firstWaveSmoothSeed p.1 1 p.2)
  refine ⟨B, hB, ?_⟩
  intro m s c t a hs ht
  have hK : (s, t) ∈ K := ⟨abs_le.mp hs, ht⟩
  have hF : ContDiff ℝ ∞ (firstWaveSmoothSeed s 1 t) := by
    change ContDiff ℝ ∞ (f ∘ fun x => ((s, t), x))
    exact contDiff_firstWaveSmoothSeed_unit_joint.comp (contDiff_const.prodMk contDiff_id)
  rw [show firstWaveSmoothSeed s c t = fun x => c • firstWaveSmoothSeed s 1 t x from
      funext (firstWaveSmoothSeed_scale s c t),
    iteratedFDeriv_const_smul_apply' ((hF.of_le (by simp)).contDiffAt), norm_smul, Real.norm_eq_abs,
    mul_comm (|c|)]
  exact mul_le_mul_of_nonneg_right (hJet m (s, t) hK a).2 (abs_nonneg _)


theorem firstWaveSmoothSeed_second_apply (s c t : ℝ) (a : Vec3) :
    firstWaveSmoothSeed s c t a 1 = c / (1 + firstWaveSweep t a ^ 2) := by
  let ξ := firstWaveSweep t a
  let e (i : Fin 3) : Vec3 := EuclideanSpace.single i 1
  change ((c * ξ / (1 + ξ ^ 2)) • e 0 + (c / (1 + ξ ^ 2)) • e 1 +
    (-s * c * Real.arctan ξ) • e 2) 1 = c / (1 + ξ ^ 2)
  norm_num [e, EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply,
    show (1 : Fin 3) ≠ 2 by decide]

/-- On a bounded first-wave slab the center amplitude controls the
initial amplitude scale without assuming that scale is nonzero. -/
theorem firstWaveSmoothSeed_scale_abs_le_centerAmplitude (s c t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |c| ≤ (1 + (2 * Real.pi) ^ 2) * ‖firstWaveSmoothSeed s c t 0‖ := by
  let z := firstWaveSweep t (0 : Vec3)
  have hz : z = t * (2 * Real.pi) := by
    simp [z, firstWaveSweep, firstWaveShearRate]
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  have hle : z ≤ 2 * Real.pi := by
    rw [hz]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 hπ
  have hz₀ : 0 ≤ z := by rw [hz]; exact mul_nonneg ht.1 hπ
  have hzsq := pow_le_pow_left₀ hz₀ hle 2
  have hd : 0 < 1 + z ^ 2 := by positivity
  have hcoord : |c| / (1 + z ^ 2) ≤ ‖firstWaveSmoothSeed s c t 0‖ := by
    have hc := PiLp.norm_apply_le (firstWaveSmoothSeed s c t 0) (1 : Fin 3)
    rw [firstWaveSmoothSeed_second_apply, Real.norm_eq_abs, abs_div] at hc
    change |c| / |1 + z ^ 2| ≤ _ at hc
    rw [abs_of_pos hd] at hc
    exact hc
  calc
    _ ≤ ‖firstWaveSmoothSeed s c t 0‖ * (1 + z ^ 2) := (div_le_iff₀ hd).mp hcoord
    _ ≤ ‖firstWaveSmoothSeed s c t 0‖ * (1 + (2 * Real.pi) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hzsq) (norm_nonneg _)
    _ = _ := mul_comm _ _

/-- The normalization scale is controlled by the actual central seed weight. -/
theorem FirstWaveOrigin.scale_le_centerAmplitude {s T freq t : ℝ}
    (w : FirstWaveOrigin s T freq) (hf : freq ≠ 0) (ht : t ∈ Icc 0 T) (ht₁ : t ≤ 1) :
    w.scale ≤ (1 + (2 * Real.pi) ^ 2) * ‖w.amplitude t‖ := by
  rw [w.amplitude_eq_smoothSeed (ht.1.trans ht.2) hf ht]
  simpa only [abs_of_pos w.scale_pos] using
    firstWaveSmoothSeed_scale_abs_le_centerAmplitude s w.scale t ⟨ht.1, ht₁⟩

/-- All spatial seed jets obey the center-amplitude weight of the first-wave
hierarchy at every time on the first slab. -/
theorem exists_firstWaveOrigin_spatialJetBounds :
    ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧ ∀ {s T freq : ℝ} (w : FirstWaveOrigin s T freq),
      |s| ≤ 1 → T ≤ 1 → freq ≠ 0 → ∀ m t, t ∈ Icc 0 T → ∀ a,
        ‖iteratedFDeriv ℝ m (firstWaveSmoothSeed s w.scale t) a‖ ≤ B m * ‖w.amplitude t‖ := by
  obtain ⟨B, hB, hjet⟩ := exists_firstWaveSmoothSeedJetBounds
  let D := 1 + (2 * Real.pi) ^ 2
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨fun m => B m * D, fun m => mul_nonneg (hB _) hD, ?_⟩
  intro s T freq w hs hT hf m t ht a
  have h₀ := hjet m s w.scale t a hs ⟨ht.1, ht.2.trans hT⟩
  rw [abs_of_pos w.scale_pos] at h₀
  exact h₀.trans ((mul_le_mul_of_nonneg_left (w.scale_le_centerAmplitude hf ht (ht.2.trans hT))
    (hB m)).trans_eq (mul_assoc _ _ _).symm)

private def normalizedFirstWavePressureCoefficient (t : ℝ) (a : Vec3) : ℝ :=
  2 * firstWaveShearRate a / (1 + firstWaveSweep t a ^ 2) ^ 2

/-- The pressure coefficient of the explicit first seed is independent of the
shear ratio after the amplitude and wave-number factors have been removed. -/
theorem wavePressureCoefficient_firstWave_eq (s c freq t : ℝ) (a : Vec3) (hf : freq ≠ 0) :
    wavePressureCoefficient 1 (firstWaveTransportedCovector s freq t a) (firstWaveSmoothSeed s c t a)
      (Real.cos (2 * Real.pi * a 1) • stationaryShearGradient s) =
        (c / freq) * normalizedFirstWavePressureCoefficient t a := by
  let ξ := firstWaveSweep t a
  let e (i : Fin 3) : Vec3 := EuclideanSpace.single i 1
  let b := firstWaveSmoothSeed s c t a
  let M := Real.cos (2 * Real.pi * a 1) • stationaryShearGradient s
  have hb : b 1 = c / (1 + ξ ^ 2) := firstWaveSmoothSeed_second_apply s c t a
  have hMa : M b = (firstWaveShearRate a * b 1) • (e 0 + s • e 2) := by
    dsimp only [M, firstWaveShearRate]
    rw [smul_apply, stationaryShearGradient_apply, smul_smul]
    congr 1
    ring
  have hMa0 : (M b) 0 = firstWaveShearRate a * (c / (1 + ξ ^ 2)) := by
    rw [hMa, hb]
    norm_num [e, EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply,
      show (1 : Fin 3) ≠ 2 by decide, show (0 : Fin 3) ≠ 2 by decide]
  have hMa1 : (M b) 1 = 0 := by
    rw [hMa]
    norm_num [e, EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply,
      show (1 : Fin 3) ≠ 2 by decide, show (0 : Fin 3) ≠ 2 by decide]
  change wavePressureCoefficient 1 (firstWaveTransportedCovector s freq t a) b M = _
  rw [wavePressureCoefficient, mul_one, inner_firstWaveTransportedCovector, hMa0, hMa1,
    mul_zero, sub_zero, norm_sq_firstWaveTransportedCovector]
  change (2 * (freq * (firstWaveShearRate a * (c / (1 + ξ ^ 2))))) /
      (freq ^ 2 * (1 + ξ ^ 2)) = (c / freq) * (2 * firstWaveShearRate a / (1 + ξ ^ 2) ^ 2)
  have hξ : 1 + ξ ^ 2 ≠ 0 := by positivity
  field_simp [hf, hξ]

private theorem contDiff_normalizedFirstWavePressureCoefficient :
    ContDiff ℝ ∞ (Function.uncurry normalizedFirstWavePressureCoefficient) := by
  have hCos : ContDiff ℝ ∞ (fun q : ℝ × Vec3 => q.2 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).contDiff.comp contDiff_snd
  have hRate : ContDiff ℝ ∞ (fun q : ℝ × Vec3 => firstWaveShearRate q.2) := by
    unfold firstWaveShearRate
    exact contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul hCos))
  have hDen : ContDiff ℝ ∞ (fun q : ℝ × Vec3 => (1 + firstWaveSweep q.1 q.2 ^ 2) ^ 2) :=
    (contDiff_const.add (contDiff_firstWaveSweep.pow 2)).pow 2
  exact (contDiff_const.mul hRate).div hDen (fun q => by positivity)

private theorem spatiallyPeriodic_normalizedFirstWavePressureCoefficient (t : ℝ) :
    SpatiallyPeriodic (normalizedFirstWavePressureCoefficient t) := by
  intro n a
  unfold normalizedFirstWavePressureCoefficient
  rw [spatiallyPeriodic_firstWaveSweep t n a]
  exact congrArg (fun x : ℝ => 2 * (2 * Real.pi * x) / (1 + firstWaveSweep t a ^ 2) ^ 2)
    (spatiallyPeriodic_firstWaveCos n a)

/-- The leading pressure coefficient has uniform spatial derivative bounds of
every order with the factor |c| / |freq|. -/
theorem exists_firstWavePressureCoefficientJetBounds :
    ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧ ∀ m s c freq t a,
      freq ≠ 0 → t ∈ Icc (0 : ℝ) 1 →
      ‖iteratedFDeriv ℝ m (fun x =>
        wavePressureCoefficient 1 (firstWaveTransportedCovector s freq t x)
          (firstWaveSmoothSeed s c t x)
          (Real.cos (2 * Real.pi * x 1) • stationaryShearGradient s)) a‖ ≤
        B m * (|c| / |freq|) := by
  obtain ⟨B, hB, hJet⟩ := exists_uniformJetBounds_of_contDiff_periodic
    (K := Icc (0 : ℝ) 1) isCompact_Icc contDiff_normalizedFirstWavePressureCoefficient
    spatiallyPeriodic_normalizedFirstWavePressureCoefficient
  refine ⟨B, hB, ?_⟩
  intro m s c freq t a hf ht
  have hF : ContDiff ℝ ∞ (normalizedFirstWavePressureCoefficient t) := by
    change ContDiff ℝ ∞ ((Function.uncurry normalizedFirstWavePressureCoefficient) ∘ fun x => (t, x))
    exact contDiff_normalizedFirstWavePressureCoefficient.comp (contDiff_const.prodMk contDiff_id)
  have heq : (fun x => wavePressureCoefficient 1 (firstWaveTransportedCovector s freq t x)
      (firstWaveSmoothSeed s c t x)
      (Real.cos (2 * Real.pi * x 1) • stationaryShearGradient s)) =
      fun x => (c / freq) • normalizedFirstWavePressureCoefficient t x :=
    funext fun x => wavePressureCoefficient_firstWave_eq s c freq t x hf
  rw [heq, iteratedFDeriv_const_smul_apply' ((hF.of_le (by simp)).contDiffAt),
    norm_smul, Real.norm_eq_abs, abs_div, mul_comm (|c| / |freq|)]
  exact mul_le_mul_of_nonneg_right (hJet m t ht a).2 (div_nonneg (abs_nonneg _) (abs_nonneg _))

end
end TorusEuler

open ContinuousLinearMap Filter Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

noncomputable section

private theorem exists_unitRadialEnvelope_phaseJetBound (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ PhaseJetBound n C (radialEnvelope 1) := by
  have hSmooth := contDiff_radialEnvelope (ℓ := 1) (by norm_num)
  have hCap (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a,
      ‖iteratedFDeriv ℝ j (radialEnvelope 1) a‖ ≤ C := by
    let B := Metric.closedBall (0 : Vec3) 2
    have hB : IsCompact B := isCompact_closedBall _ _
    obtain ⟨C, hC⟩ := hB.exists_bound_of_continuousOn
      (hSmooth.continuous_iteratedFDeriv (m := j) (by simp)).continuousOn
    refine ⟨max 0 C, le_max_left _ _, fun a => ?_⟩
    by_cases ha : a ∈ B
    · exact (hC a ha).trans (le_max_right _ _)
    · have hzero : iteratedFDeriv ℝ j (radialEnvelope 1) a = 0 := by
        apply Function.notMem_support.mp
        intro hx
        have h := tsupport_radialEnvelope_subset (show 0 < (1 : ℝ) by norm_num)
          (support_iteratedFDeriv_subset j hx)
        change ‖a‖ ≤ 2 * (1 : ℝ) at h
        exact ha (by simpa only [B, Metric.mem_closedBall, dist_zero_right, mul_one] using h)
      simpa only [hzero, norm_zero] using (le_max_left (0 : ℝ) C)
  choose B hB hjet using hCap
  let C := 1 + ∑ j ∈ Finset.range (n + 1), B j
  refine ⟨C, le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hB j), ?_⟩
  intro j hj x
  exact (hjet j x).trans
    ((Finset.single_le_sum (f := B) (fun i _ => hB i)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).trans (le_add_of_nonneg_left zero_le_one))

private theorem phaseJetBound_comp_contraction {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} (hf : ContDiff ℝ ∞ f) (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    {n : ℕ} {A : ℝ} (hA : PhaseJetBound n A f) : PhaseJetBound n A (f ∘ L) := by
  intro j hj x
  rw [L.iteratedFDeriv_comp_right hf x (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ * ‖L‖ ^ j := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ j f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
    _ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ :=
      mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)
    _ ≤ A := hA j hj _

/-- Incorporating the actual envelope preserves the rescaled slow-factor
budget, with a constant depending only on the derivative order. -/
theorem exists_radial_scaledPhaseSlowFactor_jetBounds (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : Vec3 → E} {r A : ℝ}, 0 < r → r ≤ 1 → 0 ≤ A → ContDiff ℝ ∞ f →
      PhaseJetBound n A f →
      let V (p : Vec3 × ℝ) := radialEnvelope r (r • p.1) • f (r • p.1)
      ContDiff ℝ ∞ V ∧ PhaseJetBound n (C * A) V := by
  obtain ⟨B, hB, henv⟩ := exists_unitRadialEnvelope_phaseJetBound n
  let C := (2 : ℝ) ^ n * B
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hB
  refine ⟨C, hC, ?_⟩
  intro E _ _ f r A hr hr₁ hA hf hjet V
  let S : (Vec3 × ℝ) →L[ℝ] Vec3 := r • ContinuousLinearMap.fst ℝ Vec3 ℝ
  let F : (Vec3 × ℝ) →L[ℝ] Vec3 := ContinuousLinearMap.fst ℝ Vec3 ℝ
  let u := radialEnvelope 1 ∘ F
  let v := f ∘ S
  have hS : ‖S‖ ≤ 1 := by
    rw [show S = r • F from rfl, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_of_le_one_right hr.le (ContinuousLinearMap.norm_fst_le ..)).trans hr₁
  have hF : ‖F‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ..
  have huS := contDiff_radialEnvelope (ℓ := 1) (by norm_num)
  have hu : ContDiff ℝ ∞ u := huS.comp F.contDiff
  have hv : ContDiff ℝ ∞ v := hf.comp S.contDiff
  have hU := phaseJetBound_comp_contraction huS F hF henv
  have hV := phaseJetBound_comp_contraction hf S hS hjet
  have heq : V = fun p => u p • v p := by
    funext p
    have hEq : radialEnvelope r (r • p.1) = radialEnvelope 1 p.1 := by
      unfold radialEnvelope
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_comm r, mul_div_cancel_right₀ _ hr.ne', div_one]
    change radialEnvelope r (r • p.1) • f (r • p.1) =
      radialEnvelope 1 p.1 • f (r • p.1)
    rw [hEq]
  rw [heq]
  refine ⟨hu.smul hv, ?_⟩
  intro j hj x
  have hb := norm_iteratedFDeriv_bilinear_scaled_le (lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
    opNorm_lsmul_le (n := j) (p := 0) (q := 0) (r := 0) (D := 1)
    (hu.of_le (by simp)) (hv.of_le (by simp)) x
    (fun i hi => by simpa only [one_pow, mul_one] using hU i (hi.trans hj) x)
    (fun i hi => by simpa only [one_pow, mul_one] using hV i (hi.trans hj) x)
  calc
    _ ≤ (2 : ℝ) ^ j * (B * A) := by simpa only [lsmul_apply, one_pow, mul_one] using hb
    _ ≤ (2 : ℝ) ^ n * (B * A) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj)
        (mul_nonneg (zero_le_one.trans hB) hA)
    _ = C * A := by dsimp only [C]; ring

private theorem contDiff_first_wave_raw_pressure_coefficient (s c freq t : ℝ) (hf : freq ≠ 0) :
    ContDiff ℝ ∞ (fun x => wavePressureCoefficient 1 (firstWaveTransportedCovector s freq t x)
      (firstWaveSmoothSeed s c t x) (firstWaveMaterialGradient s x)) := by
  have hEq : (fun x => wavePressureCoefficient 1 (firstWaveTransportedCovector s freq t x)
      (firstWaveSmoothSeed s c t x) (firstWaveMaterialGradient s x)) =
      fun x => (c / freq) * (2 * firstWaveShearRate x / (1 + firstWaveSweep t x ^ 2) ^ 2) :=
    funext fun x => wavePressureCoefficient_firstWave_eq s c freq t x hf
  rw [hEq]
  have ht : ContDiff ℝ ∞ (firstWaveSweep t) :=
    contDiff_firstWaveSweep.comp (contDiff_const.prodMk contDiff_id)
  have hr : ContDiff ℝ ∞ firstWaveShearRate := by
    unfold firstWaveShearRate
    exact contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul
      (EuclideanSpace.proj (1 : Fin 3) : Vec3 →L[ℝ] ℝ).contDiff))
  exact contDiff_const.mul ((contDiff_const.mul hr).div
    ((contDiff_const.add (ht.pow 2)).pow 2) (fun _ => by positivity))

set_option maxHeartbeats 1200000 in
/-- The first leading velocity and carrier-normalized pressure have the
scaled pointwise jet estimate of (5.25), with constants independent of the
stationary shear ratio, radius, interval, and carrier. -/
theorem exists_firstWaveLeadingProfile_scaledJetBounds (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s T freq r : ℝ} (w : FirstWaveOrigin s T freq),
      |s| ≤ 1 → T ≤ 1 → 1 ≤ freq → 0 < r → r ≤ 1 → ∀ t ∈ Icc 0 T,
      let h := freq ^ (-1 / 2 : ℝ)
      let γ := freq ^ (3 / 4 : ℝ) * ‖w.amplitude t‖
      PhaseJetBound n (γ * (C * freq ^ (-5 / 4 : ℝ)))
        (scaledPhaseProfile r h (firstWaveLeadingProfile s w.scale r h t)) ∧
      PhaseJetBound n (γ * (C * freq ^ (-5 / 4 : ℝ)))
        (scaledPhaseProfile r h (fun x z => freq * firstWaveLeadingPressureProfile s w.scale freq r h t x z)) := by
  obtain ⟨J, hJ, hSeed⟩ := exists_firstWaveOrigin_spatialJetBounds
  obtain ⟨L, hL, hPress⟩ := exists_firstWavePressureCoefficientJetBounds
  obtain ⟨E, hE, hslow⟩ := exists_radial_scaledPhaseSlowFactor_jetBounds n
  obtain ⟨K, hK, hlead⟩ := exists_switchedLeadingProfile_scaledJetBounds n
  let D := 1 + (2 * Real.pi) ^ 2
  let U := ∑ j ∈ Finset.range (n + 1), J j
  let Q := (∑ j ∈ Finset.range (n + 1), L j) * D
  let C := K * E * (U + Q)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hU : 0 ≤ U := Finset.sum_nonneg fun j _ => hJ j
  have hQ : 0 ≤ Q := mul_nonneg (Finset.sum_nonneg fun j _ => hL j) hD
  have hE₀ : 0 ≤ E := zero_le_one.trans hE
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  refine ⟨C, mul_nonneg (mul_nonneg hK₀ hE₀) (add_nonneg hU hQ), ?_⟩
  intro s T freq r w hs hT hf hr hr₁ t ht h γ
  have hp : 0 < freq := zero_lt_one.trans_le hf
  let A := ‖w.amplitude t‖
  let a := firstWaveSmoothSeed s w.scale t
  let κ := firstWaveTransportedCovector s freq t
  let M := firstWaveMaterialGradient s
  let pc (x : Vec3) := wavePressureCoefficient 1 (κ x) (a x) (M x)
  let q : Vec3 → ℝ := fun x => (-freq) • pc x
  have ha : ContDiff ℝ ∞ a :=
    (contDiff_firstWaveSmoothSeed s w.scale).comp (contDiff_const.prodMk contDiff_id)
  have hpreg : ContDiff ℝ ∞ pc := contDiff_first_wave_raw_pressure_coefficient s w.scale freq t hp.ne'
  have hq : ContDiff ℝ ∞ q := hpreg.const_smul (-freq)
  have hajet : PhaseJetBound n (U * A) a := by
    intro j hj x
    have hjU : J j ≤ U :=
      Finset.single_le_sum (f := J) (fun i _ => hJ i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    exact (hSeed w hs hT hp.ne' j t ht x).trans (mul_le_mul_of_nonneg_right hjU (norm_nonneg _))
  have hqjet : PhaseJetBound n (Q * A) q := by
    intro j hj x
    have hjQ : L j * D ≤ Q :=
      mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := L) (fun i _ => hL i)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))) hD
    have hb := hPress j s w.scale freq t x hp.ne' ⟨ht.1, ht.2.trans hT⟩
    rw [abs_of_pos w.scale_pos, abs_of_pos hp] at hb
    change ‖iteratedFDeriv ℝ j pc x‖ ≤ L j * (w.scale / freq) at hb
    change ‖iteratedFDeriv ℝ j (fun y => (-freq) • pc y) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' ((hpreg.of_le (by simp)).contDiffAt),
      norm_smul, norm_neg, Real.norm_of_nonneg hp.le]
    calc
      _ ≤ freq * (L j * (w.scale / freq)) := mul_le_mul_of_nonneg_left hb hp.le
      _ = L j * w.scale := by field_simp
      _ ≤ L j * (D * A) :=
        mul_le_mul_of_nonneg_left (w.scale_le_centerAmplitude hp.ne' ht (ht.2.trans hT)) (hL j)
      _ = (L j * D) * A := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hjQ (norm_nonneg _)
  obtain ⟨hFs, hFj⟩ := hslow hr hr₁ (mul_nonneg hU (norm_nonneg _)) ha hajet
  obtain ⟨hPs, hPj⟩ := hslow hr hr₁ (mul_nonneg hQ (norm_nonneg _)) hq hqjet
  have hA : γ * freq ^ (-3 / 4 : ℝ) = A := by
    dsimp only [γ, A]
    rw [mul_right_comm, ← Real.rpow_add hp,
      show (3 / 4 : ℝ) + (-3 / 4) = 0 by norm_num, Real.rpow_zero, one_mul]
  have hFj' : PhaseJetBound n ((E * U) * γ * freq ^ (-3 / 4 : ℝ))
      (fun p : Vec3 × ℝ => (1 * radialEnvelope r (r • p.1)) • a (r • p.1)) := by
    rw [mul_assoc, hA]
    simpa only [one_mul, mul_assoc] using hFj
  have hPeq : (fun p : Vec3 × ℝ => freq * -wavePressureCoefficient (1 * radialEnvelope r (r • p.1))
      (κ (r • p.1)) (a (r • p.1)) (M (r • p.1))) =
        fun p => radialEnvelope r (r • p.1) • q (r • p.1) := by
    funext p
    simp only [q, pc, smul_eq_mul, wavePressureCoefficient, one_mul]
    ring
  have hPj' : PhaseJetBound n ((E * Q) * γ * freq ^ (-3 / 4 : ℝ))
      (fun p : Vec3 × ℝ => freq * -wavePressureCoefficient (1 * radialEnvelope r (r • p.1))
        (κ (r • p.1)) (a (r • p.1)) (M (r • p.1))) := by
    rw [hPeq, mul_assoc, hA]
    simpa only [mul_assoc] using hPj
  have hγ : 0 ≤ γ := mul_nonneg (Real.rpow_nonneg hp.le _) (norm_nonneg _)
  obtain ⟨hVelocity, hPressure⟩ := hlead (freq := freq) (ell := r) (χ := 1) (γ := γ)
    (U := E * U) (Q := E * Q) (a := a) (κ := κ) (M := M) hf hγ
    (mul_nonneg hE₀ hU) (mul_nonneg hE₀ hQ)
    (by simpa only [one_mul] using hFs) (by rw [hPeq]; exact hPs) hFj' hPj'
  have hVeq : (fun x z => ((1 * radialEnvelope r x) * waveProfile h z) • a x) =
      firstWaveLeadingProfile s w.scale r h t := by
    funext x z
    simp only [one_mul, firstWaveLeadingProfile, a]
  have hQeq : (fun x z => freq * oscillatoryPhasePressure (M x) (κ x) (fun _ => 0)
      (fun p => ((1 * radialEnvelope r x) * waveProfile h p) • a x) z) =
      fun x z => freq * firstWaveLeadingPressureProfile s w.scale freq r h t x z := by
    funext x z
    rw [congrFun (firstWaveLeadingPressureProfile_eq_phasePressure s w.scale freq r h t x) z]
    exact congrArg (fun g => freq * oscillatoryPhasePressure (M x) (κ x) (fun _ => 0) g z)
      (congrFun hVeq x)
  rw [hVeq] at hVelocity
  rw [hQeq] at hPressure
  have hCvel : K * (E * U) ≤ C := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hQ) (mul_nonneg hK₀ hE₀)
  have hCpress : K * (E * Q) ≤ C := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hU) (mul_nonneg hK₀ hE₀)
  have hmono {B : ℝ} (hb : B ≤ C) :
      γ * (B * freq ^ (-5 / 4 : ℝ)) ≤ γ * (C * freq ^ (-5 / 4 : ℝ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hp.le _)) hγ
  exact ⟨fun j hj p => (hVelocity j hj p).trans (hmono hCvel),
    fun j hj p => (hPressure j hj p).trans (hmono hCpress)⟩


private theorem uniqueDiffOn_centeredCell_firstWave : UniqueDiffOn ℝ centeredCell := by
  have hconv : Convex ℝ centeredCell := by
    have heq : centeredCell = ⋂ i : Fin 3, (fun x : Vec3 => x i) ⁻¹' Icc (-(1 / 2 : ℝ)) (1 / 2) := by
      ext x
      simp [centeredCell]
    rw [heq]
    exact convex_iInter fun i => (convex_Icc _ _).linear_preimage
      (EuclideanSpace.proj (𝕜 := ℝ) i).toLinearMap
  refine uniqueDiffOn_convex hconv ⟨0, mem_interior_iff_mem_nhds.mpr ?_⟩
  apply mem_of_superset (Metric.ball_mem_nhds (0 : Vec3) (show 0 < 1 / 2 by norm_num))
  intro x hx i
  have hnorm : ‖x‖ < (1 : ℝ) / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  exact abs_le.mp ((PiLp.norm_apply_le x i).trans hnorm.le)

/-- The lattice extension of a smooth profile preserves its scaled derivative
budget exactly when its values agree on the whole centered cell. -/
theorem HierarchyTwistedProfile.phaseJetBound_of_centeredCell
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {k : Vec3} {u : HierarchyTwistedProfile T k E}
    {f : Vec3 → ℝ → E} {t r h B : ℝ} {n : ℕ}
    (ht : t ∈ Icc 0 T) (hr : r ≠ 0) (hh : h ≠ 0)
    (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hcell : ∀ a ∈ centeredCell, ∀ s, u.val.val.val (t, a, s) = f a s)
    (hjet : PhaseJetBound n B (scaledPhaseProfile r h f)) :
    PhaseJetBound n B (scaledPhaseProfile r h (fun a s => u.val.val.val (t, a, s))) := by
  let g : Vec3 × ℝ → E := fun x => u.val.val.val (t, x)
  let S := labelPhaseScale r h
  have hg : ContDiff ℝ ∞ g :=
    contDiffOn_univ.mp ((HierarchySmoothProfile.smooth u.val.val).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨ht, mem_univ _⟩))
  have hC : UniqueDiffOn ℝ (centeredCell ×ˢ (univ : Set ℝ)) :=
    uniqueDiffOn_centeredCell_firstWave.prod uniqueDiffOn_univ
  have hEq : EqOn g (Function.uncurry f) (centeredCell ×ˢ (univ : Set ℝ)) := by
    rintro ⟨a, s⟩ hx
    exact hcell a hx.1 s
  intro j hj p
  change ‖iteratedFDeriv ℝ j (g ∘ S) p‖ ≤ B
  let y := S p
  obtain ⟨m, hm⟩ := exists_sub_latticeVector_mem_centeredCell y.1
  let δ : Vec3 × ℝ := (latticeVector m, ⟪k, latticeVector m⟫_ℝ)
  let x := y - δ
  have hx : x ∈ centeredCell ×ˢ (univ : Set ℝ) := ⟨hm, mem_univ _⟩
  have htrans : (fun z : Vec3 × ℝ => g (z + δ)) = g := by
    funext z
    exact HierarchyTwistedProfile.twistedSlice u t z.1 z.2 m
  have hshift := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := g) j δ x
  rw [htrans, show x + δ = y from sub_add_cancel y δ] at hshift
  have hderiv : iteratedFDeriv ℝ j g x = iteratedFDeriv ℝ j (Function.uncurry f) x := by
    have h := iteratedFDerivWithin_congr (𝕜 := ℝ) hEq hx j
    rwa [iteratedFDerivWithin_eq_iteratedFDeriv hC ((hg.of_le (by simp)).contDiffAt) hx,
      iteratedFDerivWithin_eq_iteratedFDeriv hC ((hf.of_le (by simp)).contDiffAt) hx] at h
  let q : Vec3 × ℝ := (r⁻¹ • x.1, h⁻¹ * x.2)
  have hq : S q = x := by
    rw [show S = labelPhaseScale r h from rfl, labelPhaseScale_apply]
    apply Prod.ext
    · change r • (r⁻¹ • x.1) = x.1
      rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
    · change h * (h⁻¹ * x.2) = x.2
      rw [← mul_assoc, mul_inv_cancel₀ hh, one_mul]
  have hqjet := hjet j hj q
  change ‖iteratedFDeriv ℝ j (Function.uncurry f ∘ S) q‖ ≤ B at hqjet
  rw [S.iteratedFDeriv_comp_right hf q (by simp), hq] at hqjet
  rw [S.iteratedFDeriv_comp_right hg p (by simp)]
  change ‖(iteratedFDeriv ℝ j g y).compContinuousLinearMap (fun _ => S)‖ ≤ B
  rw [← hshift, hderiv]
  exact hqjet


private theorem phaseOperatorWord_constant_eq_iteratedFDeriv_firstWave
    {I U E : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : I → U) {f : U → E} (hf : ContDiff ℝ ∞ f) (w : List I) (x : U) :
    phaseOperatorWord (fun i _ => d i) w f x =
      iteratedFDeriv ℝ w.length f x (fun i => d (w.get i)) := by
  induction w generalizing x with
  | nil => simp [phaseOperatorWord]
  | cons i w ih =>
    have hw : phaseOperatorWord (fun j _ => d j) w f =
        fun y => iteratedFDeriv ℝ w.length f y (fun j => d (w.get j)) :=
      funext ih
    change fderiv ℝ (phaseOperatorWord (fun j _ => d j) w f) x (d i) =
      iteratedFDeriv ℝ (w.length + 1) f x (fun j => d ((i :: w).get j))
    rw [hw]
    have hd := hf.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top w.length) x
    rw [hd.iteratedFDeriv_succ_apply_left']
    rfl

/-- A scaled Fréchet jet budget controls each mixed coordinate word,
with no additional constant for one word. -/
theorem norm_hierarchyMixedWord_le_of_scaledJetBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec3 × ℝ → E} (hf : ContDiff ℝ ∞ f)
    {r h M : ℝ} (hr : r ≠ 0) (hh : h ≠ 0) {n : ℕ}
    (hjet : PhaseJetBound n M (f ∘ labelPhaseScale r h))
    (w : List (Fin 4)) (hw : w.length ≤ n) (x : Vec3 × ℝ) :
    ‖phaseOperatorWord (hierarchyMixedDirection r h) w f x‖ ≤ M := by
  let d : Fin 4 → Vec3 × ℝ := Fin.lastCases (phaseCoordinateDirection (.inr ()))
    (fun j => phaseCoordinateDirection (.inl j))
  let S := labelPhaseScale r h
  let q : Vec3 × ℝ := (r⁻¹ • x.1, h⁻¹ * x.2)
  have hq : S q = x := by
    rw [show S = labelPhaseScale r h from rfl, labelPhaseScale_apply]
    apply Prod.ext
    · change r • (r⁻¹ • x.1) = x.1
      rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
    · change h * (h⁻¹ * x.2) = x.2
      rw [← mul_assoc, mul_inv_cancel₀ hh, one_mul]
  have hd (i : Fin 4) : S (d i) = hierarchyMixedDirection r h i 0 := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [S, d, Fin.lastCases_last, hierarchyMixedDirection,
        labelPhaseScale_phaseCoordinateDirection, phaseCoordinateWeight]
    · simp only [S, d, Fin.lastCases_castSucc, hierarchyMixedDirection,
        labelPhaseScale_phaseCoordinateDirection, phaseCoordinateWeight]
  have hdn (i : Fin 4) : ‖d i‖ = 1 := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [d, Fin.lastCases_last]
      simp [phaseCoordinateDirection, Prod.norm_def]
    · simp [d, phaseCoordinateDirection, Prod.norm_def, coordinateDirection, EuclideanSpace.single]
  have heval : phaseOperatorWord (hierarchyMixedDirection r h) w f x =
      iteratedFDeriv ℝ w.length (f ∘ S) q (fun i => d (w.get i)) := by
    rw [S.iteratedFDeriv_comp_right hf q (by simp), hq]
    change phaseOperatorWord (fun j _ => hierarchyMixedDirection r h j 0) w f x =
      iteratedFDeriv ℝ w.length f x (fun i => S (d (w.get i)))
    rw [phaseOperatorWord_constant_eq_iteratedFDeriv_firstWave _ hf]
    simp_rw [hd]
  rw [heval]
  have hdir : ‖iteratedFDeriv ℝ w.length (f ∘ S) q (fun i => d (w.get i))‖ ≤
      ‖iteratedFDeriv ℝ w.length (f ∘ S) q‖ := by
    simpa only [hdn, Finset.prod_const_one, mul_one] using
      (iteratedFDeriv ℝ w.length (f ∘ S) q).le_opNorm (fun i => d (w.get i))
  exact hdir.trans (hjet w.length hw q)

/-- The exact mixed-word amplitude seminorm of a twisted profile follows
from a uniform scaled Fréchet derivative bound on its time slices. -/
theorem HierarchyTwistedProfile.amplitudeSeminorm_le_of_scaledJetBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T t₀ : ℝ} {k : Vec3} (hT : 0 < T) (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T)
    {u : HierarchyTwistedProfile T k E} {γ : ℝ → ℝ}
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    {r h B : ℝ} (hr : r ≠ 0) (hh : h ≠ 0) {n : ℕ} (hB : 0 ≤ B)
    (hjet : ∀ t ∈ Icc t₀ T, PhaseJetBound n (γ t * B)
      (scaledPhaseProfile r h (fun a s => u.val.val.val (t, a, s)))) :
    amplitudeSeminorm False r h n hT ht₀ htT γ hγ hpos u ≤
      (hierarchyAdmissibleWords (Fin 4) n).card * B := by
  let A := Icc t₀ T
  let f := weightedSlices A (fun t => (γ t)⁻¹) u
  let D := hierarchyMixedDirection r h
  have hterm (w : List (Fin 4)) (hw : w ∈ hierarchyAdmissibleWords (Fin 4) n) :
      sSup (hierarchyJetValues False D w f) ≤ B := by
    apply csSup_le (show (hierarchyJetValues False D w f).Nonempty from ⟨0, Or.inl rfl⟩)
    rintro y (rfl | ⟨t, x, rfl⟩ | ⟨hfalse, _⟩)
    · exact hB
    · let g : Vec3 × ℝ → E := fun x => u.val.val.val (t.val, x)
      have hg : ContDiff ℝ ∞ g :=
        contDiffOn_univ.mp ((HierarchySmoothProfile.smooth u.val.val).comp
          (contDiff_const.prodMk contDiff_id).contDiffOn
          (fun _ _ => ⟨⟨ht₀.trans t.property.1, t.property.2⟩, mem_univ _⟩))
      have hEq : phaseOperatorWord D w (f t) x =
          (γ t.val)⁻¹ • phaseOperatorWord D w g x :=
        phaseOperatorWord_const_smul (fun _ => contDiff_const) hg _ w x
      rw [hEq, norm_smul, Real.norm_of_nonneg (inv_pos.mpr (hpos _ t.property)).le]
      calc
        _ ≤ (γ t.val)⁻¹ * (γ t.val * B) :=
          mul_le_mul_of_nonneg_left
            (norm_hierarchyMixedWord_le_of_scaledJetBound hg hr hh (hjet _ t.property)
              w ((mem_hierarchyAdmissibleWords.mp hw).1) x) (inv_nonneg.mpr (hpos _ t.property).le)
        _ = B := by rw [← mul_assoc, inv_mul_cancel₀ (hpos _ t.property).ne', one_mul]
    · exact hfalse.elim
  rw [amplitudeSeminorm_apply]
  change (∑ w ∈ hierarchyAdmissibleWords (Fin 4) n, sSup (hierarchyJetValues False D w f)) ≤ _
  calc
    _ ≤ ∑ _w ∈ hierarchyAdmissibleWords (Fin 4) n, B := Finset.sum_le_sum hterm
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]


set_option maxHeartbeats 1250000 in
/-- The wrapped first-wave velocity and pressure satisfy the exact mixed-word
version of (5.25), with the first-wave amplitude weight. -/
theorem exists_firstWaveHierarchyLeading_ampSeminorm_le (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s T freq r : ℝ} (w : FirstWaveOrigin s T freq),
      |s| ≤ 1 → ∀ (hT : 0 < T), T ≤ 1 → ∀ (hf : 1 ≤ freq)
        (hr : 0 < r) (hcell : 2 * r < 1 / 2),
      let h := freq ^ (-1 / 2 : ℝ)
      let hh : 0 < h := (profileWidth_and_seedScale hf).1.1
      let hh₁ : h ≤ 1 := (profileWidth_and_seedScale hf).1.2
      let hfreq : 0 < freq := zero_lt_one.trans_le hf
      let γ (t : ℝ) := freq ^ (3 / 4 : ℝ) * ‖w.amplitude t‖
      let hγ : ContinuousOn γ (Icc 0 T) := (HasDerivWithinAt.continuousOn w.amplitude_equation).norm.const_mul _
      let hpos (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < γ t :=
        mul_pos (Real.rpow_pos_of_pos hfreq _) (norm_pos_iff.mpr (w.transverse t ht).2.1)
      let av := HierarchyTwistedProfile.amplitudeSeminorm (k := firstWaveLaunchCovector freq)
        (E := Vec3) False r h n hT le_rfl hT.le γ hγ hpos
      let ap := HierarchyTwistedProfile.amplitudeSeminorm (k := firstWaveLaunchCovector freq)
        (E := ℝ) False r h n hT le_rfl hT.le γ hγ hpos
      let v := firstWaveHierarchyLeadingVelocity (T := T) s w.scale freq hr hcell hh hh₁
      let p := firstWaveHierarchyLeadingPressure (T := T) s w.scale hfreq.ne' hr hcell hh hh₁
      av v + freq * ap p ≤ C * freq ^ (-5 / 4 : ℝ) := by
  obtain ⟨K, hK, hRaw⟩ := exists_firstWaveLeadingProfile_scaledJetBounds n
  let count : ℝ := (hierarchyAdmissibleWords (Fin 4) n).card
  refine ⟨2 * count * K, mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) hK, ?_⟩
  intro s T freq r w hs hT hT₁ hf hr hcell h hh hh₁ hfreq γ hγ hpos av ap v p
  have hr₁ : r ≤ 1 := by linarith [hcell]
  let B := K * freq ^ (-5 / 4 : ℝ)
  have hB : 0 ≤ B := mul_nonneg hK (Real.rpow_nonneg hfreq.le _)
  let δ := (1 / 2 : ℝ) - 2 * r
  have hδ : 0 < δ := sub_pos.mpr hcell
  have hOut {a : Vec3} (ha : ∃ i : Fin 3, 1 / 2 - δ < |a i|) : 2 * r ≤ ‖a‖ := by
    obtain ⟨i, hi⟩ := ha
    have hn := PiLp.norm_apply_le a i
    rw [Real.norm_eq_abs] at hn
    dsimp only [δ] at hi
    linarith
  have hEnv : ContDiff ℝ ∞ (fun x : Vec3 × ℝ => radialEnvelope r x.1) :=
    (contDiff_radialEnvelope hr).comp contDiff_fst
  have hVraw (t : ℝ) : ContDiff ℝ ∞ (Function.uncurry (firstWaveLeadingProfile s w.scale r h t)) := by
    have hSeed : ContDiff ℝ ∞ (firstWaveSmoothSeed s w.scale t) :=
      (contDiff_firstWaveSmoothSeed s w.scale).comp (contDiff_const.prodMk contDiff_id)
    exact (hEnv.mul ((contDiff_waveProfile hh hh₁).comp contDiff_snd)).smul (hSeed.comp contDiff_fst)
  have hPraw (t : ℝ) : ContDiff ℝ ∞
      (Function.uncurry (fun a z => freq * firstWaveLeadingPressureProfile s w.scale freq r h t a z)) := by
    have hc := (contDiff_first_wave_raw_pressure_coefficient s w.scale freq t hfreq.ne').comp
      (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Vec3 × ℝ → Vec3))
    exact contDiff_const.mul (hEnv.mul (hc.neg.mul ((contDiff_wavePressurePrimitive hh hh₁).comp contDiff_snd)))
  have hVcell (t : ℝ) (ht : t ∈ Icc 0 T) (a : Vec3) (ha : a ∈ centeredCell) (z : ℝ) :
      v.val.val.val (t, a, z) = firstWaveLeadingProfile s w.scale r h t a z := by
    rw [show v.val.val.val (t, a, z) = _ from firstWaveHierarchyLeadingVelocity_eval
      s w.scale freq hr hcell hh hh₁ (p := (t, a, z)) ⟨ht, mem_univ _⟩]
    refine phaseTwistedPeriodizeCentered_eq_on_centeredCell hδ (fun a ha z => ?_) ha z
    rw [firstWaveLeadingProfile, radialEnvelope_eq_zero hr (hOut ha), zero_mul, zero_smul]
  let P : HierarchyTwistedProfile T (firstWaveLaunchCovector freq) ℝ := freq • p
  have hPcell (t : ℝ) (ht : t ∈ Icc 0 T) (a : Vec3) (ha : a ∈ centeredCell) (z : ℝ) :
      P.val.val.val (t, a, z) = freq * firstWaveLeadingPressureProfile s w.scale freq r h t a z := by
    change freq * p.val.val.val (t, a, z) = _
    rw [show p.val.val.val (t, a, z) = _ from firstWaveHierarchyLeadingPressure_eval
      s w.scale hfreq.ne' hr hcell hh hh₁ (p := (t, a, z)) ⟨ht, mem_univ _⟩]
    apply congrArg (freq * ·)
    refine phaseTwistedPeriodizeCentered_eq_on_centeredCell hδ (fun a ha z => ?_) ha z
    unfold firstWaveLeadingPressureProfile
    rw [radialEnvelope_eq_zero hr (hOut ha), zero_mul]
  have hv : av v ≤ count * B :=
    HierarchyTwistedProfile.amplitudeSeminorm_le_of_scaledJetBound hT le_rfl hT.le hγ hpos
      hr.ne' hh.ne' hB (fun t ht => HierarchyTwistedProfile.phaseJetBound_of_centeredCell ht
        hr.ne' hh.ne' (hVraw t) (hVcell t ht) (hRaw w hs hT₁ hf hr hr₁ t ht).1)
  have hp : freq * ap p ≤ count * B := by
    have hP := HierarchyTwistedProfile.amplitudeSeminorm_le_of_scaledJetBound (u := P)
      hT le_rfl hT.le hγ hpos hr.ne' hh.ne' hB
      (fun t ht => HierarchyTwistedProfile.phaseJetBound_of_centeredCell ht hr.ne' hh.ne'
        (hPraw t) (hPcell t ht) (hRaw w hs hT₁ hf hr hr₁ t ht).2)
    change ap (freq • p) ≤ _ at hP
    rwa [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hfreq] at hP
  calc
    _ ≤ count * B + count * B := add_le_add hv hp
    _ = _ := by dsimp only [B]; ring

end
end TorusEuler
