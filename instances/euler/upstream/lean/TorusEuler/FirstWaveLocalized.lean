import TorusEuler.BaseParentData
import TorusEuler.FirstWaveInitialization
import TorusEuler.TerminalIntegrals
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! The jointly smooth first wave over the frozen paper's stationary shear.
This file constructs the affine seed in Section 6.1 and realizes the curl
completion (3.5) on the torus using the actual inverse shear flow. -/

open Filter Set ContinuousLinearMap
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

private abbrev basisAxis (i : Fin 3) : Vec3 := EuclideanSpace.single i 1

private theorem basisAxis_apply (i j : Fin 3) :
    basisAxis i j = if j = i then 1 else 0 := by
  simp [basisAxis, EuclideanSpace.single, PiLp.single_apply]

private theorem firstAxisSimp :
    basisAxis 0 0 = 1 ∧ basisAxis 0 1 = 0 ∧ basisAxis 0 2 = 0 := by
  norm_num [basisAxis_apply, show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide]

private theorem secondAxisSimp :
    basisAxis 1 0 = 0 ∧ basisAxis 1 1 = 1 ∧ basisAxis 1 2 = 0 := by
  norm_num [basisAxis_apply, show (0 : Fin 3) ≠ 1 by decide, show (2 : Fin 3) ≠ 1 by decide]

private theorem thirdAxisSimp :
    basisAxis 2 0 = 0 ∧ basisAxis 2 1 = 0 ∧ basisAxis 2 2 = 1 := by
  norm_num [basisAxis_apply, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide]

/-- The scalar shear rate seen by the particle with label `a`. -/
def firstWaveShearRate (a : Vec3) : ℝ := 2 * Real.pi * Real.cos (2 * Real.pi * a 1)

/-- The amount of shear accumulated along a stationary-shear trajectory. -/
def firstWaveSweep (t : ℝ) (a : Vec3) : ℝ := t * firstWaveShearRate a

private def firstWaveSeedAtSweep (s c z : ℝ) : Vec3 :=
  (c * z / (1 + z ^ 2)) • basisAxis 0 +
    (c / (1 + z ^ 2)) • basisAxis 1 + (-s * c * Real.arctan z) • basisAxis 2

/-- The explicit first-wave amplitude over the stationary shear. The
denominator never vanishes, including on labels of zero local shear. -/
def firstWaveSmoothSeed (s c t : ℝ) (a : Vec3) : Vec3 :=
  firstWaveSeedAtSweep s c (firstWaveSweep t a)

theorem firstWaveSmoothSeed_zero (s c : ℝ) (a : Vec3) :
    firstWaveSmoothSeed s c 0 a = c • EuclideanSpace.single 1 1 := by
  simp [firstWaveSmoothSeed, firstWaveSeedAtSweep, firstWaveSweep]

theorem contDiff_firstWaveSweep : ContDiff ℝ ∞ (fun p : ℝ × Vec3 => firstWaveSweep p.1 p.2) := by
  have hproj : ContDiff ℝ ∞ (fun p : ℝ × Vec3 => p.2 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).contDiff.comp contDiff_snd
  unfold firstWaveSweep firstWaveShearRate
  fun_prop

theorem contDiff_firstWaveSmoothSeed (s c : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (firstWaveSmoothSeed s c)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × Vec3 =>
    firstWaveSeedAtSweep s c (firstWaveSweep p.1 p.2))
  have hSeed : ContDiff ℝ ∞ (firstWaveSeedAtSweep s c) := by
    unfold firstWaveSeedAtSweep
    have hd : ContDiff ℝ ∞ (fun z : ℝ => 1 + z ^ 2) := by fun_prop
    have hd₀ (z : ℝ) : 1 + z ^ 2 ≠ 0 := by positivity
    have h₀ : ContDiff ℝ ∞ (fun z : ℝ => c * z) := by fun_prop
    have h₁ : ContDiff ℝ ∞ (fun _ : ℝ => c) := contDiff_const
    have h₂ : ContDiff ℝ ∞ (fun z : ℝ => -s * c * Real.arctan z) :=
      contDiff_const.mul Real.contDiff_arctan
    exact (((h₀.div hd hd₀).smul contDiff_const).add
      ((h₁.div hd hd₀).smul contDiff_const)).add (h₂.smul contDiff_const)
  exact hSeed.comp contDiff_firstWaveSweep

private theorem firstWaveSeedAtSweep_components (s c z : ℝ) :
    firstWaveSeedAtSweep s c z 0 = c * z / (1 + z ^ 2) ∧
      firstWaveSeedAtSweep s c z 1 = c / (1 + z ^ 2) ∧
      firstWaveSeedAtSweep s c z 2 = -s * c * Real.arctan z := by
  simp only [firstWaveSeedAtSweep, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    firstAxisSimp.1, firstAxisSimp.2.1, firstAxisSimp.2.2, secondAxisSimp.1,
    secondAxisSimp.2.1, secondAxisSimp.2.2, thirdAxisSimp.1, thirdAxisSimp.2.1,
    thirdAxisSimp.2.2, mul_zero, mul_one, add_zero, zero_add, and_self]

private theorem hasDerivAt_firstWaveSeedAtSweep (s c z : ℝ) :
    HasDerivAt (firstWaveSeedAtSweep s c)
      ((c * (1 - z ^ 2) / (1 + z ^ 2) ^ 2) • basisAxis 0 +
        (-2 * z * c / (1 + z ^ 2) ^ 2) • basisAxis 1 +
        (-s * c / (1 + z ^ 2)) • basisAxis 2) z := by
  have hz := hasDerivAt_id z
  have hd : HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * z) z := by
    have hp : (id ^ 2 : ℝ → ℝ) = (fun u : ℝ => u ^ 2) := rfl
    simpa only [hp, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using
      (hz.pow 2).const_add 1
  have h₀ : HasDerivAt (fun u : ℝ => c * u / (1 + u ^ 2))
      (c * (1 - z ^ 2) / (1 + z ^ 2) ^ 2) z := by
    refine ((hz.const_mul c).div hd (by positivity)).congr_deriv ?_
    simp only [id_eq, mul_one]
    ring
  have h₁ : HasDerivAt (fun u : ℝ => c / (1 + u ^ 2))
      (-2 * z * c / (1 + z ^ 2) ^ 2) z := by
    refine ((hasDerivAt_const z c).div hd (by positivity)).congr_deriv ?_
    simp only [zero_mul, zero_sub]
    ring
  have h₂ : HasDerivAt (fun u : ℝ => -s * c * Real.arctan u)
      (-s * c / (1 + z ^ 2)) z := by
    simpa only [mul_one_div] using (Real.hasDerivAt_arctan z).const_mul (-s * c)
  exact ((h₀.smul_const (basisAxis 0)).add (h₁.smul_const (basisAxis 1))).add
    (h₂.smul_const (basisAxis 2))

theorem stationaryShearGradient_apply (s : ℝ) (v : Vec3) :
    stationaryShearGradient s v = (2 * Real.pi * v 1) • (basisAxis 0 + s • basisAxis 2) := by
  change (2 * Real.pi : ℝ) • (⟪basisAxis 1, v⟫_ℝ • (basisAxis 0 + s • basisAxis 2)) = _
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, smul_smul]

theorem stationaryShearGradient_adjoint_firstAxis (s c : ℝ) :
    (stationaryShearGradient s).adjoint (c • basisAxis 0) = (2 * Real.pi * c) • basisAxis 1 := by
  apply ext_inner_left ℝ
  intro v
  rw [adjoint_inner_right, stationaryShearGradient_apply]
  have h00 : ⟪basisAxis 0, basisAxis 0⟫_ℝ = 1 := by
    simp [basisAxis]
  have h20 : ⟪basisAxis 2, basisAxis 0⟫_ℝ = 0 := by
    norm_num [basisAxis, EuclideanSpace.inner_single_left, PiLp.single_apply]
    decide
  have hv : ⟪v, basisAxis 1⟫_ℝ = v 1 := by
    calc
      ⟪v, basisAxis 1⟫_ℝ = ⟪basisAxis 1, v⟫_ℝ := real_inner_comm _ _
      _ = v 1 := by simp [basisAxis, EuclideanSpace.inner_single_left]
  simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left,
    h00, h20, hv, mul_one, mul_zero, add_zero]
  ring

theorem firstWaveTransportedCovector_eq (s freq t : ℝ) (a : Vec3) :
    firstWaveTransportedCovector s freq t a =
      freq • basisAxis 0 + (-(freq * firstWaveSweep t a)) • basisAxis 1 := by
  let k₀ : Vec3 := freq • basisAxis 0
  let γ : ℝ := t * Real.cos (2 * Real.pi * a 1)
  change (ContinuousLinearMap.id ℝ Vec3 - γ • stationaryShearGradient s).adjoint k₀ = _
  have h : (ContinuousLinearMap.id ℝ Vec3 - γ • stationaryShearGradient s).adjoint k₀ =
      k₀ - γ • (stationaryShearGradient s).adjoint k₀ := by
    simp only [map_sub, map_smul, sub_apply, smul_apply, adjoint_id, id_apply]
  rw [h]
  change freq • basisAxis 0 - γ • (stationaryShearGradient s).adjoint (freq • basisAxis 0) = _
  rw [stationaryShearGradient_adjoint_firstAxis, sub_eq_add_neg, smul_smul, ← neg_smul]
  rw [show γ * (2 * Real.pi * freq) = freq * firstWaveSweep t a by
    dsimp [γ, firstWaveSweep, firstWaveShearRate]
    ring]

theorem inner_firstWaveTransportedCovector (s freq t : ℝ) (a v : Vec3) :
    ⟪firstWaveTransportedCovector s freq t a, v⟫_ℝ =
      freq * v 0 - freq * firstWaveSweep t a * v 1 := by
  rw [firstWaveTransportedCovector_eq]
  simp only [inner_add_left, real_inner_smul_left, basisAxis,
    EuclideanSpace.inner_single_left, map_one, one_mul]
  ring

theorem norm_sq_firstWaveTransportedCovector (s freq t : ℝ) (a : Vec3) :
    ‖firstWaveTransportedCovector s freq t a‖ ^ 2 = freq ^ 2 * (1 + firstWaveSweep t a ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, inner_firstWaveTransportedCovector,
    firstWaveTransportedCovector_eq]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, basisAxis, PiLp.single_apply,
    show (0 : Fin 3) ≠ 1 by decide, show (1 : Fin 3) ≠ 0 by decide,
    ite_false, ite_true, mul_one, mul_zero, zero_add, add_zero]
  ring

theorem contDiff_firstWaveTransportedCovector (s freq : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (firstWaveTransportedCovector s freq)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × Vec3 => firstWaveTransportedCovector s freq p.1 p.2)
  simp only [firstWaveTransportedCovector_eq]
  have h : ContDiff ℝ ∞ (fun p : ℝ × Vec3 => -(freq * firstWaveSweep p.1 p.2)) :=
    (contDiff_const.mul contDiff_firstWaveSweep).neg
  exact contDiff_const.add (h.smul_const (basisAxis 1))

private theorem contDiff_cross3_of_contDiff {f g : ℝ × Vec3 → Vec3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun p => cross3 (f p) (g p)) := by
  have hp (i : Fin 3) : ContDiff ℝ ∞ (fun v : Vec3 => v i) := contDiff_piLp_apply 2
  have hf' (i : Fin 3) : ContDiff ℝ ∞ (fun p => f p i) := (hp i).comp hf
  have hg' (i : Fin 3) : ContDiff ℝ ∞ (fun p => g p i) := (hp i).comp hg
  apply contDiff_piLp' 2
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun p => f p 1 * g p 2 - f p 2 * g p 1)
    exact ((hf' 1).mul (hg' 2)).sub ((hf' 2).mul (hg' 1))
  · change ContDiff ℝ ∞ (fun p => f p 2 * g p 0 - f p 0 * g p 2)
    exact ((hf' 2).mul (hg' 0)).sub ((hf' 0).mul (hg' 2))
  · change ContDiff ℝ ∞ (fun p => f p 0 * g p 1 - f p 1 * g p 0)
    exact ((hf' 0).mul (hg' 1)).sub ((hf' 1).mul (hg' 0))

theorem contDiff_firstWavePotentialCoefficient {s freq : ℝ} (hf : freq ≠ 0)
    {U : ℝ → Vec3 → Vec3} (hU : ContDiff ℝ ∞ (Function.uncurry U)) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec3 =>
      (-(‖firstWaveTransportedCovector s freq p.1 p.2‖ ^ 2)⁻¹) •
        cross3 (firstWaveTransportedCovector s freq p.1 p.2) (U p.1 p.2)) := by
  have hk := contDiff_firstWaveTransportedCovector s freq
  have hnorm : ContDiff ℝ ∞ (fun p : ℝ × Vec3 =>
      ‖firstWaveTransportedCovector s freq p.1 p.2‖ ^ 2) := by
    simp only [norm_sq_firstWaveTransportedCovector]
    exact contDiff_const.mul (contDiff_const.add (contDiff_firstWaveSweep.pow 2))
  have hne (p : ℝ × Vec3) : ‖firstWaveTransportedCovector s freq p.1 p.2‖ ^ 2 ≠ 0 := by
    rw [norm_sq_firstWaveTransportedCovector]
    exact mul_ne_zero (pow_ne_zero 2 hf) (by positivity)
  exact (hnorm.inv hne).neg.smul (contDiff_cross3_of_contDiff hk hU)

/-- The explicit label-dependent seed satisfies the affine amplitude equation at
every time. Its strain is the actual stationary-shear gradient along the label. -/
theorem hasDerivAt_firstWaveSmoothSeed (s c freq t : ℝ) (a : Vec3) (hf : freq ≠ 0) :
    HasDerivAt (fun u => firstWaveSmoothSeed s c u a)
      (affineWaveAmplitudeOperator
        (Real.cos (2 * Real.pi * a 1) • stationaryShearGradient s)
        (firstWaveTransportedCovector s freq t a) (firstWaveSmoothSeed s c t a)) t := by
  let B := Real.cos (2 * Real.pi * a 1) • stationaryShearGradient s
  let z := firstWaveSweep t a
  let ξ := firstWaveShearRate a
  let k := firstWaveTransportedCovector s freq t a
  let u := firstWaveSmoothSeed s c t a
  have hw : HasDerivAt (fun v => firstWaveSweep v a) ξ t := by
    simpa only [firstWaveSweep, ξ, id_eq, one_mul] using
      (hasDerivAt_id t).mul_const ξ
  have hdu : B u = (ξ * (c / (1 + z ^ 2))) • (basisAxis 0 + s • basisAxis 2) := by
    dsimp only [B]
    rw [smul_apply, stationaryShearGradient_apply, smul_smul]
    change (Real.cos (2 * Real.pi * a 1) * (2 * Real.pi * firstWaveSeedAtSweep s c z 1)) •
      (basisAxis 0 + s • basisAxis 2) = _
    rw [(firstWaveSeedAtSweep_components s c z).2.1]
    congr 1
    dsimp only [ξ, firstWaveShearRate]
    ring
  have hdot : ⟪k, B u⟫_ℝ = freq * (ξ * (c / (1 + z ^ 2))) := by
    rw [hdu, show k = firstWaveTransportedCovector s freq t a by rfl,
      inner_firstWaveTransportedCovector]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, firstAxisSimp.1,
      firstAxisSimp.2.1, thirdAxisSimp.1, thirdAxisSimp.2.1, mul_zero, mul_one,
      add_zero, sub_zero]
  have hn : ‖k‖ ^ 2 = freq ^ 2 * (1 + z ^ 2) :=
    norm_sq_firstWaveTransportedCovector s freq t a
  have hk : k = freq • basisAxis 0 + (-(freq * z)) • basisAxis 1 :=
    firstWaveTransportedCovector_eq s freq t a
  change HasDerivAt (fun v => firstWaveSeedAtSweep s c (firstWaveSweep v a))
    (affineWaveAmplitudeOperator B k u) t
  refine ((hasDerivAt_firstWaveSeedAtSweep s c z).scomp t hw).congr_deriv ?_
  rw [affineWaveAmplitudeOperator_apply, hdot, hn, hdu, hk]
  have hd : 1 + z ^ 2 ≠ 0 := by positivity
  apply PiLp.ext
  intro i
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul, basisAxis_apply]
  fin_cases i <;> simp (config := { decide := true }) <;> field_simp [hf, hd]
  all_goals ring

theorem firstWaveTransportedCovector_ne_zero (s freq t : ℝ) (a : Vec3) (hf : freq ≠ 0) :
    firstWaveTransportedCovector s freq t a ≠ 0 := by
  intro hk
  have hn := norm_sq_firstWaveTransportedCovector s freq t a
  rw [hk, norm_zero, zero_pow (by decide)] at hn
  exact (mul_ne_zero (pow_ne_zero 2 hf) (by positivity)) hn.symm

theorem firstWaveSmoothSeed_ne_zero (s c t : ℝ) (a : Vec3) (hc : c ≠ 0) :
    firstWaveSmoothSeed s c t a ≠ 0 := by
  intro hu
  have h := (firstWaveSeedAtSweep_components s c (firstWaveSweep t a)).2.1
  change firstWaveSmoothSeed s c t a 1 = _ at h
  rw [hu, PiLp.zero_apply] at h
  exact (div_ne_zero hc (by positivity)) h.symm

theorem inner_firstWaveTransportedCovector_smoothSeed (s c freq t : ℝ) (a : Vec3) :
    ⟪firstWaveTransportedCovector s freq t a, firstWaveSmoothSeed s c t a⟫_ℝ = 0 := by
  rw [inner_firstWaveTransportedCovector]
  unfold firstWaveSmoothSeed
  rw [(firstWaveSeedAtSweep_components s c _).1, (firstWaveSeedAtSweep_components s c _).2.1]
  ring

/-- The jointly smooth seed restricts at the origin to the affine solution
with the manuscript's attained peak normalization. -/
theorem FirstWaveOrigin.amplitude_eq_smoothSeed {s T freq : ℝ} (w : FirstWaveOrigin s T freq)
    (hT : 0 ≤ T) (hf : freq ≠ 0) :
    EqOn w.amplitude (fun t => firstWaveSmoothSeed s w.scale t 0) (Icc 0 T) := by
  apply linearODE_unique_of_mem
    (A := fun t => affineWaveAmplitudeOperator (stationaryShearGradient s) (w.covector t))
    ordConnected_Icc (left_mem_Icc.mpr hT)
  · exact continuousOn_affineWaveAmplitudeOperator continuousOn_const
      (HasDerivWithinAt.continuousOn w.covector_equation)
      (fun t ht => (w.transverse t ht).1)
  · exact w.amplitude_equation
  · intro t ht
    rw [w.covector_eq_transported hT ht]
    simpa only [PiLp.zero_apply, mul_zero, Real.cos_zero, one_smul] using
      (hasDerivAt_firstWaveSmoothSeed s w.scale freq t 0 hf).hasDerivWithinAt (s := Icc 0 T)
  · rw [w.amplitude_initial, firstWaveSmoothSeed_zero]

/-- The collar envelope makes the periodic extension smooth jointly with
respect to every smooth profile parameter. -/
theorem contDiff_joint_periodizeCentered_radialEnvelope
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℝ}
    {H : P × Vec3 → E} (hr : 0 < r) (hcell : 2 * r < 1 / 2)
    (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun p : P × Vec3 =>
      periodizeCentered (fun a => radialEnvelope r a • H (p.1, a)) p.2) := by
  let R : ℝ := (2 * r + 1 / 2) / 2
  let δ : ℝ := 1 / 2 - R
  have hRin : 2 * r < R := by dsimp only [R]; linarith
  have hRout : R < 1 / 2 := by dsimp only [R]; linarith
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hδ' : δ ≤ 1 / 2 := by dsimp only [δ]; linarith
  let b : ContDiffBump (0 : Vec3) := ⟨2 * r, R, by positivity, hRin⟩
  let g := periodizeCentered (radialEnvelope r)
  let proxy := periodizeCentered (fun a => b a • a)
  have hcollar (a : Vec3) (ha : ∃ i : Fin 3, 1 / 2 - δ < |a i|) :
      R < ‖a‖ := by
    obtain ⟨i, hi⟩ := ha
    have hi' : |a i| ≤ ‖a‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le a i
    dsimp only [δ] at hi
    linarith
  have hgc : ContDiff ℝ ∞ g := contDiff_periodizeCentered hδ hδ'
    (contDiff_radialEnvelope hr)
    (fun a ha => radialEnvelope_eq_zero hr (hRin.le.trans (hcollar a ha).le))
  have hpc : ContDiff ℝ ∞ proxy :=
    contDiff_periodizeCentered hδ hδ' (b.contDiff.smul contDiff_id) (fun a ha => by
      have hb : b a = 0 := b.zero_of_le_dist (by
        simpa only [dist_zero_right, b] using (hcollar a ha).le)
      rw [hb, zero_smul])
  have heq (p : P × Vec3) :
      periodizeCentered (fun a => radialEnvelope r a • H (p.1, a)) p.2 =
        g p.2 • H (p.1, proxy p.2) := by
    let a := centeredLabel p.2
    change radialEnvelope r a • H (p.1, a) = radialEnvelope r a • H (p.1, b a • a)
    by_cases ha : 2 * r ≤ ‖a‖
    · rw [radialEnvelope_eq_zero hr ha, zero_smul, zero_smul]
    · have hb : b a = 1 := b.one_of_mem_closedBall
        (by simpa only [Metric.mem_closedBall, dist_zero_right, b] using (le_of_not_ge ha))
      rw [hb, one_smul]
  rw [funext heq]
  exact (hgc.comp contDiff_snd).smul (hH.comp (contDiff_fst.prodMk (hpc.comp contDiff_snd)))

/-- The spatial differential of a jointly smooth potential varies smoothly in both parameters. -/
theorem contDiff_joint_fderiv_right {P X E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : P × X → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : P × X => fderiv ℝ (fun x => F (p.1, x)) p.2) := by
  let J : ((P × X) →L[ℝ] E) →L[ℝ] X →L[ℝ] E :=
    (ContinuousLinearMap.compL ℝ X (P × X) E).flip (ContinuousLinearMap.inr ℝ P X)
  have hd : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have heq (p : P × X) : fderiv ℝ (fun x => F (p.1, x)) p.2 = J (fderiv ℝ F p) := by
    exact ((hF.differentiable (by simp) p).hasFDerivAt.comp p.2
      (hasFDerivAt_prodMk_right p.1 p.2)).fderiv
  rw [funext heq]
  exact J.contDiff.comp hd

/-- Taking curl in the spatial variable preserves joint smoothness. -/
theorem contDiff_joint_curl {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : P × Vec3 → Vec3} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : P × Vec3 => curl (fun x => F (p.1, x)) p.2) :=
  curlOfDerivativeCLM.contDiff.comp (contDiff_joint_fderiv_right hF)

theorem contDiff_stationaryShearFlow_inverse (s : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec3 => stationaryShearFlow s (-p.1) p.2) := by
  have hx : ContDiff ℝ ∞ (fun p : ℝ × Vec3 => p.2 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).contDiff.comp contDiff_snd
  have hsin : ContDiff ℝ ∞ (fun p : ℝ × Vec3 => Real.sin (2 * Real.pi * p.2 1)) :=
    (contDiff_const.mul hx).sin
  unfold stationaryShearFlow stationaryShear
  exact contDiff_snd.add (contDiff_fst.neg.smul (hsin.smul contDiff_const))

/-- The centered periodic extension preserves reflection symmetries when the
profile vanishes on the walls where the half-open cell breaks reflection symmetry. -/
theorem periodizeCentered_neg_equivariant {F : Type*} [Zero F]
    {f : Vec3 → F} {L : F → F} (hL : L 0 = 0)
    (hf : ∀ a, f (-a) = L (f a))
    (hwall : ∀ a, (∃ i : Fin 3, a i = -(1 / 2 : ℝ)) → f a = 0)
    (x : Vec3) : periodizeCentered f (-x) = L (periodizeCentered f x) := by
  have hneg (i : Fin 3) :
      Int.fract ((-x) i + 1 / 2) = Int.fract (-(x i + 1 / 2)) := by
    calc
      _ = Int.fract (-(x i + 1 / 2) + (1 : ℤ)) := by
        congr 1
        simp [PiLp.neg_apply]
        ring
      _ = _ := Int.fract_add_intCast _ _
  change f (centeredLabel (-x)) = L (f (centeredLabel x))
  by_cases h : ∃ i : Fin 3, Int.fract (x i + 1 / 2) = 0
  · obtain ⟨i, hi⟩ := h
    have hxi : centeredLabel x i = -(1 / 2 : ℝ) := by
      change Int.fract (x i + 1 / 2) - 1 / 2 = _
      rw [hi, zero_sub]
    have hni : centeredLabel (-x) i = -(1 / 2 : ℝ) := by
      change Int.fract ((-x) i + 1 / 2) - 1 / 2 = _
      rw [hneg i, Int.fract_neg_eq_zero.mpr hi, zero_sub]
    rw [hwall _ ⟨i, hxi⟩, hwall _ ⟨i, hni⟩, hL]
  · have heq : centeredLabel (-x) = -centeredLabel x := by
      apply PiLp.ext
      intro i
      change Int.fract ((-x) i + 1 / 2) - 1 / 2 = -(Int.fract (x i + 1 / 2) - 1 / 2)
      rw [hneg i, Int.fract_neg (fun hi => h ⟨i, hi⟩)]
      ring
    rw [heq, hf]

/-- Pulling a periodized even phase potential back by an odd label map preserves its parity. -/
theorem even_localizedTransportedProfile_radialEnvelope {A : Velocity} {k : Vec3} {t r : ℝ}
    {F : ℝ → ℝ} {U : Vec3 → Vec3} (hA : Function.Odd (A t))
    (hr : 0 < r) (hcell : 2 * r ≤ 1 / 2) (hF : Function.Even F) (hU : Function.Even U) :
    Function.Even (localizedTransportedProfile A k
      (fun _ a u => (radialEnvelope r a * F u) • U a) t) := by
  let f : Vec3 → Vec3 := fun a => (radialEnvelope r a * F ⟪k, a⟫_ℝ) • U a
  change Function.Even ((periodizeCentered f) ∘ A t)
  apply Function.Even.comp_odd _ hA
  refine periodizeCentered_neg_equivariant (L := id) rfl ?_ ?_
  · intro a
    simp only [f, radialEnvelope_neg, inner_neg_right, hF _, hU _, id_eq]
  · intro a ha
    obtain ⟨i, hi⟩ := ha
    have hn := PiLp.norm_apply_le a i
    rw [hi, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by norm_num)] at hn
    simp [f, radialEnvelope_eq_zero hr (hcell.trans hn)]

/-- The zero-mean primitive of the odd wave profile is even. -/
theorem even_wavePressurePrimitive {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) :
    Function.Even (wavePressurePrimitive h) := by
  intro s
  unfold wavePressurePrimitive phasePrimitive phaseOscillation
  have hneg := intervalIntegral.integral_comp_neg (f := waveProfile h) (a := 0) (b := s)
  simp only [odd_waveProfile hh hle _, intervalIntegral.integral_neg, neg_zero] at hneg
  congr 1
  calc
    _ = -(∫ x in -s..0, waveProfile h x) := intervalIntegral.integral_symm _ _
    _ = _ := by rw [← hneg, neg_neg]

/-- Spatial curl sends even differentiable potentials to odd velocity fields. -/
theorem odd_curl_of_even {Q : Vec3 → Vec3} (hQ : Function.Even Q)
    (hreg : Differentiable ℝ Q) : Function.Odd (curl Q) := by
  intro x
  have hneg : HasFDerivAt (fun y : Vec3 => -y) (-(ContinuousLinearMap.id ℝ Vec3)) x :=
    (hasFDerivAt_id x).neg
  have hD := ((hreg (-x)).hasFDerivAt.comp x hneg).fderiv
  change fderiv ℝ (fun y => Q (-y)) x = _ at hD
  have hcomp : (fderiv ℝ Q (-x)).comp (-(ContinuousLinearMap.id ℝ Vec3)) =
      - fderiv ℝ Q (-x) := by
    ext y i
    simp
  rw [funext hQ, hcomp] at hD
  have hD' : fderiv ℝ Q (-x) = - fderiv ℝ Q x := by rw [hD, neg_neg]
  change curlOfDerivative (fderiv ℝ Q (-x)) = -curlOfDerivative (fderiv ℝ Q x)
  rw [hD', ← neg_one_smul ℝ (fderiv ℝ Q x), curlOfDerivative_smul, neg_one_smul]

theorem even_firstWaveSweep (t : ℝ) : Function.Even (firstWaveSweep t) := by
  intro a
  simp only [firstWaveSweep, firstWaveShearRate, PiLp.neg_apply, mul_neg, Real.cos_neg]

theorem even_firstWaveSmoothSeed (s c t : ℝ) : Function.Even (firstWaveSmoothSeed s c t) := by
  intro a
  simp only [firstWaveSmoothSeed, even_firstWaveSweep t a]

theorem even_firstWaveTransportedCovector (s freq t : ℝ) :
    Function.Even (firstWaveTransportedCovector s freq t) := by
  intro a
  simp only [firstWaveTransportedCovector_eq, even_firstWaveSweep t a]

/-- Coefficient of the phase primitive in the fast curl inverse. -/
def firstWavePotentialCoefficient (s c freq t : ℝ) (a : Vec3) : Vec3 :=
  let κ := firstWaveTransportedCovector s freq t a
  (-(‖κ‖ ^ 2)⁻¹) • cross3 κ (firstWaveSmoothSeed s c t a)

/-- The first leading oscillation in label and phase coordinates. -/
def firstWaveLeadingProfile (s c r h t : ℝ) (a : Vec3) (φ : ℝ) : Vec3 :=
  (radialEnvelope r a * waveProfile h φ) • firstWaveSmoothSeed s c t a

/-- The vector potential as a function of material label and the independent phase. -/
def firstWavePotentialProfile (s c freq r h t : ℝ) (a : Vec3) (φ : ℝ) : Vec3 :=
  (radialEnvelope r a * wavePressurePrimitive h φ) • firstWavePotentialCoefficient s c freq t a

/-- Pull back the centered periodic extension of the vector potential
by the exact inverse stationary shear flow. -/
def firstWaveLocalizedPotential (s c freq r h : ℝ) : Velocity :=
  localizedTransportedProfile (fun t => stationaryShearFlow s (-t)) (freq • basisAxis 0)
    (firstWavePotentialProfile s c freq r h)

/-- The periodic solenoidal completion of the actual first oscillation. -/
def firstWaveLocalizedVelocity (s c freq r h : ℝ) (t : ℝ) : Vec3 → Vec3 :=
  curl (firstWaveLocalizedPotential s c freq r h t)

theorem contDiff_firstWaveLocalizedPotential {s c freq r h : ℝ} (hf : freq ≠ 0)
    (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) :
    ContDiff ℝ ∞ (Function.uncurry (firstWaveLocalizedPotential s c freq r h)) := by
  let S : ℝ × Vec3 → ℝ × Vec3 := fun p => (p.1, stationaryShearFlow s (-p.1) p.2)
  let H : ℝ × Vec3 → Vec3 := fun p =>
    wavePressurePrimitive h ⟪freq • basisAxis 0, p.2⟫_ℝ •
      firstWavePotentialCoefficient s c freq p.1 p.2
  have hH : ContDiff ℝ ∞ H := by
    have hφ := (innerSL ℝ (freq • basisAxis 0)).contDiff.comp
      (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × Vec3 → Vec3))
    exact ((contDiff_wavePressurePrimitive hh hh₁).comp hφ).smul
      (contDiff_firstWavePotentialCoefficient hf (contDiff_firstWaveSmoothSeed s c))
  have hS : ContDiff ℝ ∞ S := contDiff_fst.prodMk (contDiff_stationaryShearFlow_inverse s)
  have hc := (contDiff_joint_periodizeCentered_radialEnvelope hr hcell hH).comp hS
  have heq : Function.uncurry (firstWaveLocalizedPotential s c freq r h) =
      (fun p : ℝ × Vec3 => periodizeCentered (fun a => radialEnvelope r a • H (p.1, a)) p.2) ∘ S := by
    funext p
    rcases p with ⟨t, x⟩
    simp only [firstWaveLocalizedPotential, localizedTransportedProfile, periodizeCentered,
      Function.uncurry_apply_pair, Function.comp_apply, firstWavePotentialProfile, H, S, smul_smul]
  rw [heq]
  exact hc

theorem contDiff_firstWaveLocalizedVelocity {s c freq r h : ℝ} (hf : freq ≠ 0)
    (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) :
    ContDiff ℝ ∞ (Function.uncurry (firstWaveLocalizedVelocity s c freq r h)) :=
  contDiff_joint_curl (contDiff_firstWaveLocalizedPotential hf hr hcell hh hh₁)

theorem spatiallyPeriodic_firstWaveLocalizedVelocity (s c freq r h t : ℝ) :
    SpatiallyPeriodic (firstWaveLocalizedVelocity s c freq r h t) :=
  spatiallyPeriodic_curl (spatiallyPeriodic_localizedTransportedProfile
    (A := fun τ => stationaryShearFlow s (-τ)) (t := t)
    (stationaryShearFlow_lattice_equiv s (-t)) (freq • basisAxis 0)
    (firstWavePotentialProfile s c freq r h))

private theorem contDiff_firstWaveLocalizedPotential_slice {s c freq r h : ℝ}
    (hf : freq ≠ 0) (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) (t : ℝ) :
    ContDiff ℝ ∞ (firstWaveLocalizedPotential s c freq r h t) := by
  have hpair : ContDiff ℝ ∞ (fun x : Vec3 => (t, x)) := contDiff_const.prodMk contDiff_id
  change ContDiff ℝ ∞ (Function.uncurry (firstWaveLocalizedPotential s c freq r h) ∘
    fun x : Vec3 => (t, x))
  have hF := contDiff_firstWaveLocalizedPotential (s := s) (c := c) hf hr hcell hh hh₁
  exact hF.comp hpair

theorem divergence_firstWaveLocalizedVelocity {s c freq r h : ℝ} (hf : freq ≠ 0)
    (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) (t : ℝ) (x : Vec3) :
    divergence (firstWaveLocalizedVelocity s c freq r h t) x = 0 :=
  divergence_curl ((contDiff_firstWaveLocalizedPotential_slice hf hr hcell hh hh₁ t).of_le
    (by simp)).contDiffAt

theorem odd_firstWaveLocalizedVelocity {s c freq r h : ℝ} (hf : freq ≠ 0)
    (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) (t : ℝ) :
    Function.Odd (firstWaveLocalizedVelocity s c freq r h t) := by
  apply odd_curl_of_even _ ((contDiff_firstWaveLocalizedPotential_slice hf hr hcell hh hh₁ t).differentiable
    (by simp))
  apply even_localizedTransportedProfile_radialEnvelope
    (odd_stationaryShearFlow s (-t)) hr hcell.le (even_wavePressurePrimitive hh hh₁)
  intro a
  simp only [firstWavePotentialCoefficient, even_firstWaveTransportedCovector s freq t a,
    even_firstWaveSmoothSeed s c t a]

/-- The explicit primitive is exactly the mean-zero potential prescribed by
the fast curl inverse. -/
theorem wavePotential_firstWaveLeadingProfile {s c freq r h t : ℝ} (a : Vec3)
    (hh : 0 < h) (hh₁ : h ≤ 1) :
    wavePotential (firstWaveTransportedCovector s freq t a)
      (firstWaveLeadingProfile s c r h t a) = firstWavePotentialProfile s c freq r h t a := by
  let κ := firstWaveTransportedCovector s freq t a
  let g := radialEnvelope r a
  let U := firstWaveSmoothSeed s c t a
  let C := firstWavePotentialCoefficient s c freq t a
  have hcross (z : ℝ) : cross3 κ (z • U) = z • cross3 κ U := by
    apply WithLp.ofLp_injective
    simp only [cross3, WithLp.ofLp_smul, WithLp.ofLp_toLp, map_smul]
  have hfac (φ : ℝ) : (-(‖κ‖ ^ 2)⁻¹) • cross3 κ (firstWaveLeadingProfile s c r h t a φ) =
      (g * waveProfile h φ) • C := by
    change (-(‖κ‖ ^ 2)⁻¹) • cross3 κ ((g * waveProfile h φ) • U) =
      (g * waveProfile h φ) • ((-(‖κ‖ ^ 2)⁻¹) • cross3 κ U)
    rw [hcross, smul_comm]
  have hderiv (φ : ℝ) : HasDerivAt (firstWavePotentialProfile s c freq r h t a)
      ((g * waveProfile h φ) • C) φ :=
    ((hasDerivAt_wavePressurePrimitive hh hh₁ φ).const_mul g).smul_const C
  have hmean : phaseMean (firstWavePotentialProfile s c freq r h t a) = 0 := by
    change (∫ φ in (0 : ℝ)..1, (g * wavePressurePrimitive h φ) • C) = 0
    rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_const_mul,
      ← phaseMean, phaseMean_wavePressurePrimitive hh hh₁, mul_zero, zero_smul]
  have hcont : Continuous (fun φ => (g * waveProfile h φ) • C) :=
    (continuous_const.mul (contDiff_waveProfile hh hh₁).continuous).smul continuous_const
  change phasePrimitive (fun φ => (-(‖κ‖ ^ 2)⁻¹) •
    cross3 κ (firstWaveLeadingProfile s c r h t a φ)) = _
  rw [funext hfac, phasePrimitive_deriv hderiv hcont]
  funext φ
  simp only [phaseOscillation, hmean, sub_zero]

private theorem contDiff_firstWavePotentialProfile {s c freq r h : ℝ} (hf : freq ≠ 0)
    (hr : 0 < r) (hh : 0 < h) (hh₁ : h ≤ 1) (t : ℝ) :
    ContDiff ℝ ∞ (fun p : Vec3 × ℝ => firstWavePotentialProfile s c freq r h t p.1 p.2) := by
  let H : Vec3 × ℝ → ℝ × Vec3 := fun p => (t, p.1)
  have hH : ContDiff ℝ ∞ H := contDiff_const.prodMk contDiff_fst
  have hC₀ : ContDiff ℝ ∞ (fun p : ℝ × Vec3 => firstWavePotentialCoefficient s c freq p.1 p.2) :=
    contDiff_firstWavePotentialCoefficient hf (contDiff_firstWaveSmoothSeed s c)
  have hC : ContDiff ℝ ∞ (fun p : Vec3 × ℝ => firstWavePotentialCoefficient s c freq t p.1) := by
    change ContDiff ℝ ∞ ((fun p : ℝ × Vec3 => firstWavePotentialCoefficient s c freq p.1 p.2) ∘ H)
    exact hC₀.comp hH
  exact (((contDiff_radialEnvelope hr).comp contDiff_fst).mul
    ((contDiff_wavePressurePrimitive hh hh₁).comp contDiff_snd)).smul hC

/-- On the interior of the transported cell the localized wave agrees with
the leading oscillation plus the slow curl at frozen phase. -/
theorem firstWaveLocalizedVelocity_eq_add_slowCurl {s c freq r h t : ℝ} {x : Vec3}
    (hf : freq ≠ 0) (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hx : stationaryShearFlow s (-t) x ∈ interior centeredCell) :
    let A (u : ℝ) := stationaryShearFlow s (-u)
    let k := freq • EuclideanSpace.single 0 1
    let φ := ⟪k, A t x⟫_ℝ
    firstWaveLocalizedVelocity s c freq r h t x =
      transportedProfile A k (firstWaveLeadingProfile s c r h) t x +
        curl (fun y => firstWavePotentialProfile s c freq r h t (A t y) φ) x := by
  let A : Velocity := fun u => stationaryShearFlow s (-u)
  let k : Vec3 := freq • basisAxis 0
  let Q := firstWavePotentialProfile s c freq r h
  let V := firstWaveLeadingProfile s c r h
  let a := A t x
  let φ := ⟪k, a⟫_ℝ
  let δ := 1 / 2 - 2 * r
  let Ax := ContinuousLinearMap.id ℝ Vec3 -
    (t * Real.cos (2 * Real.pi * x 1)) • stationaryShearGradient s
  have hAx : ContinuousLinearMap.id ℝ Vec3 +
      ((-t) * Real.cos (2 * Real.pi * x 1)) • stationaryShearGradient s = Ax := by
    apply ContinuousLinearMap.ext
    intro y
    change y + ((-t) * Real.cos (2 * Real.pi * x 1)) • stationaryShearGradient s y =
      y - (t * Real.cos (2 * Real.pi * x 1)) • stationaryShearGradient s y
    rw [sub_eq_add_neg, neg_mul, _root_.neg_smul]
  have hA : HasFDerivAt (A t) Ax x := by
    rw [← hAx]
    exact hasFDerivAt_stationaryShearFlow s (-t) x
  have hκ : firstWaveTransportedCovector s freq t a = Ax.adjoint k := by
    dsimp only [firstWaveTransportedCovector, a, A, Ax, k, basisAxis]
    rw [stationaryShearFlow_second]
  have hzero (b : Vec3) (hb : ∃ i : Fin 3, 1 / 2 - δ < |b i|) : Q t b ⟪k, b⟫_ℝ = 0 := by
    obtain ⟨i, hi⟩ := hb
    have hnorm : |b i| ≤ ‖b‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le b i
    have hb' : 2 * r ≤ ‖b‖ := by dsimp only [δ] at hi; linarith
    simp only [Q, firstWavePotentialProfile, radialEnvelope_eq_zero hr hb', zero_mul, zero_smul]
  have hnear := localizedTransportedProfile_eventuallyEq (A := A) (k := k) (f := Q)
    hA.continuousAt hx (by dsimp only [δ]; linarith) hzero
  have hloc : firstWaveLocalizedVelocity s c freq r h t x = curl (transportedProfile A k Q t) x :=
    congrArg curlOfDerivative hnear.fderiv_eq
  have hV : Continuous (V t a) :=
    (continuous_const.mul (contDiff_waveProfile hh hh₁).continuous).smul continuous_const
  have htrans (u : ℝ) : ⟪firstWaveTransportedCovector s freq t a, V t a u⟫_ℝ = 0 := by
    simp only [V, firstWaveLeadingProfile, real_inner_smul_right,
      inner_firstWaveTransportedCovector_smoothSeed, mul_zero]
  have hQeq : (fun τ b => wavePotential (firstWaveTransportedCovector s freq τ b) (V τ b)) = Q := by
    funext τ b
    exact wavePotential_firstWaveLeadingProfile b hh hh₁
  have hQ : DifferentiableAt ℝ
      (fun p : Vec3 × ℝ => wavePotential (firstWaveTransportedCovector s freq t p.1) (V t p.1) p.2)
      (a, φ) := by
    simp only [congrFun (congrFun hQeq t) _]
    exact ((contDiff_firstWavePotentialProfile (s := s) (c := c) hf hr hh hh₁ t).differentiable
      (by simp)).differentiableAt
  have hsplit := curl_transportedWavePotential_eq_add_slowCurl (k := k) (V := V)
    hA hκ (firstWaveTransportedCovector_ne_zero s freq t a hf) hV htrans hQ
  change firstWaveLocalizedVelocity s c freq r h t x =
    transportedProfile A k V t x + curl (fun y => Q t (A t y) φ) x
  rw [hloc]
  dsimp only at hsplit
  simpa only [hQeq, congrFun (congrFun hQeq t) _] using hsplit

/-- The completed wave has the exact prescribed rank-one central gradient
at activation. At other times the slow curl is part of the gradient. -/
theorem hasFDerivAt_firstWaveLocalizedVelocity_initial {s c freq r h : ℝ}
    (hf : freq ≠ 0) (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) :
    HasFDerivAt (firstWaveLocalizedVelocity s c freq r h 0)
      ((innerSL ℝ (freq • EuclideanSpace.single 0 1)).smulRight
        (c • EuclideanSpace.single 1 1)) 0 := by
  let k := freq • basisAxis 0
  let b := c • basisAxis 1
  have hk : k ≠ 0 := by
    simpa only [firstWaveTransportedCovector_zero, k, basisAxis] using
      firstWaveTransportedCovector_ne_zero s freq 0 (0 : Vec3) hf
  have hb : ⟪k, b⟫_ℝ = 0 := by
    simpa only [firstWaveTransportedCovector_zero, firstWaveSmoothSeed_zero, k, b, basisAxis] using
      inner_firstWaveTransportedCovector_smoothSeed s c freq 0 0
  have hgrad := (initialLocalizedCompletedWave_properties hr hcell hh hh₁ hk hb).2.2.2.2
  have heq : firstWaveLocalizedVelocity s c freq r h 0 =
      curl (periodizeCentered (fun a =>
        (radialEnvelope r a * wavePressurePrimitive h ⟪k, a⟫_ℝ) •
          ((-(‖k‖ ^ 2)⁻¹) • cross3 k b))) := by
    unfold firstWaveLocalizedVelocity
    congr 1
    funext x
    simp only [firstWaveLocalizedPotential, localizedTransportedProfile, Function.comp_apply,
      stationaryShearFlow, neg_zero, zero_smul, add_zero, firstWavePotentialProfile,
      firstWavePotentialCoefficient, firstWaveTransportedCovector_zero, firstWaveSmoothSeed_zero,
      k, b, basisAxis]
  rw [heq]
  exact hgrad

/-- With the phase slope one at the origin, the leading oscillation has
the transported rank-one central gradient on the entire first-wave slab. -/
theorem hasFDerivAt_firstWaveLeadingProfile_origin {s c freq r h t : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hh₁ : h ≤ 1) :
    HasFDerivAt
      (transportedProfile (fun τ => stationaryShearFlow s (-τ))
        (freq • EuclideanSpace.single 0 1) (firstWaveLeadingProfile s c r h) t)
      ((innerSL ℝ (firstWaveTransportedCovector s freq t 0)).smulRight
        (firstWaveSmoothSeed s c t 0)) 0 := by
  let A : Vec3 → Vec3 := stationaryShearFlow s (-t)
  let k := freq • basisAxis 0
  let κ := firstWaveTransportedCovector s freq t 0
  let φ : Vec3 → ℝ := fun x => ⟪k, A x⟫_ℝ
  let B : Vec3 → Vec3 := fun x => radialEnvelope r (A x) • firstWaveSmoothSeed s c t (A x)
  have hφ₀ : φ 0 = 0 := by simp only [φ, A, stationaryShearFlow_origin, inner_zero_right]
  have hφ : HasFDerivAt φ (innerSL ℝ κ) 0 := by
    have hd := (hasGradientAt_firstWaveTransportedPhase s freq t 0).hasFDerivAt
    rw [stationaryShearFlow_origin] at hd
    exact hd
  have hF : HasFDerivAt (waveProfile h ∘ φ) (innerSL ℝ κ) 0 := by
    simpa only [one_smul] using
      (hasDerivAt_waveProfile_zero hh hh₁).comp_hasFDerivAt_of_eq 0 hφ hφ₀.symm
  let H : Vec3 → ℝ × Vec3 := fun x => (t, x)
  have hH : ContDiff ℝ ∞ H := contDiff_const.prodMk contDiff_id
  have hA : ContDiff ℝ ∞ A := by
    change ContDiff ℝ ∞ ((fun p : ℝ × Vec3 => stationaryShearFlow s (-p.1) p.2) ∘ H)
    exact (contDiff_stationaryShearFlow_inverse s).comp hH
  have hU : ContDiff ℝ ∞ (fun x => firstWaveSmoothSeed s c t x) := by
    change ContDiff ℝ ∞ (Function.uncurry (firstWaveSmoothSeed s c) ∘ H)
    exact (contDiff_firstWaveSmoothSeed s c).comp hH
  have hB : DifferentiableAt ℝ B 0 :=
    ((((contDiff_radialEnvelope hr).comp hA).smul (hU.comp hA)).differentiable (by simp)) 0
  have hB₀ : B 0 = firstWaveSmoothSeed s c t 0 := by
    simp only [B, A, stationaryShearFlow_origin, radialEnvelope_eq_one (a := (0 : Vec3)) hr
      (by simpa only [norm_zero] using hr.le), one_smul]
  have hD := hF.smul hB.hasFDerivAt
  rw [Function.comp_apply, hφ₀, waveProfile_zero, zero_smul, zero_add, hB₀] at hD
  refine hD.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  change transportedProfile (fun τ => stationaryShearFlow s (-τ)) k
    (firstWaveLeadingProfile s c r h) t x = waveProfile h (φ x) • B x
  simp only [transportedProfile, firstWaveLeadingProfile, φ, A, B, smul_smul, mul_comm]

end
end TorusEuler
