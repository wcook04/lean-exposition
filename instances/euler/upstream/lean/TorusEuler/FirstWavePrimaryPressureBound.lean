import TorusEuler.FirstWaveDerivativeBudgets
import TorusEuler.HierarchyPrimaryPressureCenter
import TorusEuler.HierarchyPhysicalPressureBounds
import TorusEuler.InductiveFirstWaveSelection

/-! The leading pressure Hessian for the actual selected stationary first wave. -/

open ContinuousLinearMap Filter InnerProductSpace Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

noncomputable section

local notation "Hess[" f "]" => fderiv ℝ (gradient f)

private def firstLabelPressureCoefficient (s c freq r t : ℝ) (a : Vec3) : ℝ :=
  wavePressureCoefficient (radialEnvelope r a) (firstWaveTransportedCovector s freq t a)
    (firstWaveSmoothSeed s c t a) (firstWaveMaterialGradient s a)

private theorem firstLabelPressureCoefficient_eq (s c freq r t : ℝ) (a : Vec3) :
    firstLabelPressureCoefficient s c freq r t a = radialEnvelope r a *
      wavePressureCoefficient 1 (firstWaveTransportedCovector s freq t a)
        (firstWaveSmoothSeed s c t a) (firstWaveMaterialGradient s a) := by
  unfold firstLabelPressureCoefficient wavePressureCoefficient
  ring

private theorem firstLabelPressureCoefficient_nonneg {s c freq r t : ℝ} (a : Vec3)
    (hc : 0 ≤ c) (hf : 0 < freq) (hr : 0 < r) (hfit : 2 * r ≤ 1 / 4) :
    0 ≤ firstLabelPressureCoefficient s c freq r t a := by
  have h := wavePressureCoefficient_firstWave_eq s c freq t a hf.ne'
  change wavePressureCoefficient 1 (firstWaveTransportedCovector s freq t a)
    (firstWaveSmoothSeed s c t a) (firstWaveMaterialGradient s a) =
    (c / freq) * (2 * firstWaveShearRate a / (1 + firstWaveSweep t a ^ 2) ^ 2) at h
  rw [firstLabelPressureCoefficient_eq, h]
  by_cases hout : 2 * r ≤ ‖a‖
  · rw [radialEnvelope_eq_zero hr hout, zero_mul]
  · have hcoord : |a 1| ≤ 1 / 4 := by
      have hh := PiLp.norm_apply_le a (1 : Fin 3)
      rw [Real.norm_eq_abs] at hh
      exact hh.trans ((lt_of_not_ge hout).le.trans hfit)
    have hpos : 0 ≤ Real.cos (2 * Real.pi * a 1) := by
      obtain ⟨hlo, hhi⟩ := abs_le.mp hcoord
      exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    exact mul_nonneg (radialEnvelope_mem_Icc r a).1 (mul_nonneg (div_nonneg hc hf.le)
      (div_nonneg (mul_nonneg (by norm_num) (show 0 ≤ firstWaveShearRate a by
        unfold firstWaveShearRate; positivity)) (sq_nonneg _)))

private theorem firstWaveLeadingPressureProfile_eq_product (s c freq r h t : ℝ) (a : Vec3) :
    firstWaveLeadingPressureProfile s c freq r h t a =
      fun z => -(firstLabelPressureCoefficient s c freq r t a * wavePressurePrimitive h z) := by
  rw [firstWaveLeadingPressureProfile_eq_phasePressure]
  rw [show firstWaveLeadingProfile s c r h t a =
    (fun z => (radialEnvelope r a * waveProfile h z) • firstWaveSmoothSeed s c t a) from rfl]
  rw [oscillatoryPhasePressure_primary_eq]
  funext z
  exact neg_mul _ _

private theorem contDiff_rawFirstWavePressureCoefficient (s c freq t : ℝ) (hf : freq ≠ 0) :
    ContDiff ℝ ∞ (fun x => wavePressureCoefficient 1 (firstWaveTransportedCovector s freq t x)
      (firstWaveSmoothSeed s c t x) (firstWaveMaterialGradient s x)) := by
  have heq : (fun x => wavePressureCoefficient 1 (firstWaveTransportedCovector s freq t x)
      (firstWaveSmoothSeed s c t x) (firstWaveMaterialGradient s x)) =
      fun x => (c / freq) * (2 * firstWaveShearRate x / (1 + firstWaveSweep t x ^ 2) ^ 2) :=
    funext fun x => wavePressureCoefficient_firstWave_eq s c freq t x hf
  rw [heq]
  have ht : ContDiff ℝ ∞ (firstWaveSweep t) :=
    contDiff_firstWaveSweep.comp (contDiff_const.prodMk contDiff_id)
  have hr : ContDiff ℝ ∞ firstWaveShearRate := by
    unfold firstWaveShearRate
    exact contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul
      (EuclideanSpace.proj (1 : Fin 3) : Vec3 →L[ℝ] ℝ).contDiff))
  exact contDiff_const.mul ((contDiff_const.mul hr).div
    ((contDiff_const.add (ht.pow 2)).pow 2) (fun _ => by positivity))

private theorem contDiff_firstLabelPressureCoefficient (s c freq r t : ℝ)
    (hf : freq ≠ 0) (hr : 0 < r) : ContDiff ℝ ∞ (firstLabelPressureCoefficient s c freq r t) := by
  simp_rw [show firstLabelPressureCoefficient s c freq r t = _ from
    funext (firstLabelPressureCoefficient_eq s c freq r t)]
  exact (contDiff_radialEnvelope hr).mul (contDiff_rawFirstWavePressureCoefficient s c freq t hf)

set_option maxHeartbeats 1000000 in
private theorem exists_firstLabelPressureCoefficient_jetBound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {s T freq r : ℝ} (w : FirstWaveOrigin s T freq),
      T ≤ 1 → 0 < freq → 0 < r → r ≤ 1 → ∀ {t : ℝ}, t ∈ Icc 0 T →
      PhaseJetBound 2 (K * freq ^ (-7 / 4 : ℝ))
        (fun a => firstLabelPressureCoefficient s w.scale freq r t (r • a)) := by
  obtain ⟨J, hJ, hjet⟩ := exists_firstWavePressureCoefficientJetBounds
  obtain ⟨R, hR, hRad⟩ := exists_phaseJetBound_scaledRadialEnvelope 2
  let L := J 0 + J 1 + J 2
  let B : ℝ := 1 + (2 * Real.pi) ^ 2
  let K := 4 * R * (L * B)
  have hL : 0 ≤ L := add_nonneg (add_nonneg (hJ 0) (hJ 1)) (hJ 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro s T freq r w hT hf hr hr₁ t ht
  let p (a : Vec3) := wavePressureCoefficient 1 (firstWaveTransportedCovector s freq t a)
    (firstWaveSmoothSeed s w.scale t a) (firstWaveMaterialGradient s a)
  let g (a : Vec3) := radialEnvelope r (r • a)
  let z (a : Vec3) := p (r • a)
  have hp : ContDiff ℝ ∞ p := contDiff_rawFirstWavePressureCoefficient s w.scale freq t hf.ne'
  have hg : ContDiff ℝ ∞ g := (contDiff_radialEnvelope hr).comp (contDiff_id.const_smul r)
  have hz : ContDiff ℝ ∞ z := hp.comp (contDiff_id.const_smul r)
  have hScale : w.scale / freq ≤ B * freq ^ (-7 / 4 : ℝ) := by
    have hpeak : ‖w.amplitude t‖ ≤ freq ^ (-3 / 4 : ℝ) := by
      simpa only [show (-(3 / 4) : ℝ) = -3 / 4 by norm_num] using w.norm_le_peak t ht
    have h := (w.scale_le_centerAmplitude hf.ne' ht (ht.2.trans hT)).trans
      (mul_le_mul_of_nonneg_left hpeak hB)
    calc
      _ ≤ (B * freq ^ (-3 / 4 : ℝ)) / freq := div_le_div_of_nonneg_right h hf.le
      _ = _ := by
        rw [show (-7 / 4 : ℝ) = (-3 / 4) + (-1) by norm_num, Real.rpow_add hf,
          Real.rpow_neg_one, div_eq_mul_inv]; ring
  have hZ : PhaseJetBound 2 ((L * B) * freq ^ (-7 / 4 : ℝ)) z := by
    intro j hj a
    have hJL : J j ≤ L := by
      interval_cases j
      all_goals dsimp only [L]; linarith [hJ 0, hJ 1, hJ 2]
    have hj' := hjet j s w.scale freq t (r • a) hf.ne' ⟨ht.1, ht.2.trans hT⟩
    rw [abs_of_pos w.scale_pos, abs_of_pos hf] at hj'
    have hb : ‖iteratedFDeriv ℝ j p (r • a)‖ ≤ (L * B) * freq ^ (-7 / 4 : ℝ) := by
      refine hj'.trans ?_
      rw [mul_assoc]
      exact mul_le_mul hJL hScale (div_nonneg w.scale_pos.le hf.le) hL
    exact (norm_iteratedFDeriv_scaledLabel_le hp hr.le j a).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hr.le hr₁)).trans hb)
  have hProd := phaseJetBound_bilinear_product (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
    opNorm_lsmul_le hg hz (zero_le_one.trans hR) (by positivity) (hRad hr) hZ
  have heq : (fun a => firstLabelPressureCoefficient s w.scale freq r t (r • a)) =
      fun a => lsmul ℝ ℝ (g a) (z a) := by
    funext a
    exact firstLabelPressureCoefficient_eq s w.scale freq r t (r • a)
  rw [heq]
  have hBound : (2 : ℝ) ^ 2 * (R * ((L * B) * freq ^ (-7 / 4 : ℝ))) =
      K * freq ^ (-7 / 4 : ℝ) := by dsimp only [K]; ring
  rw [hBound] at hProd
  exact hProd

private def firstPressureCoframeBound : ℝ := (1 + 8 * Real.pi ^ 2) * (1 + 4 * Real.pi)

private theorem one_le_firstPressureCoframeBound : 1 ≤ firstPressureCoframeBound := by
  unfold firstPressureCoframeBound
  exact one_le_mul_of_one_le_of_one_le (by linarith [sq_nonneg Real.pi]) (by linarith [Real.pi_pos])

private theorem firstPressureCoframe_firstJet {s t : ℝ} (hs : |s| ≤ 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (a : Vec3) :
    ‖fderiv ℝ (fun y => fderiv ℝ (stationaryShearFlow s (-t)) (stationaryShearFlow s t y)) a‖ ≤
      1 + 8 * Real.pi ^ 2 := by
  let B := stationaryShearGradient s
  let P : Vec3 →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)
  let L := (2 * Real.pi) • P
  have hP : ‖P‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro v
    change ‖v 1‖ ≤ 1 * ‖v‖
    simpa only [one_mul] using (PiLp.norm_apply_le v (1 : Fin 3))
  have hL : ‖L‖ ≤ 2 * Real.pi := by
    dsimp only [L]
    rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    exact mul_le_of_le_one_right (by positivity) hP
  let j (y : Vec3) := t * Real.cos (L y)
  have hEq : (fun y => fderiv ℝ (stationaryShearFlow s (-t)) (stationaryShearFlow s t y)) =
      fun y => ContinuousLinearMap.id ℝ Vec3 - j y • B :=
    funext fun y => (stationaryShearFlow_jacobians_eq s t y).2
  let J : Vec3 →L[ℝ] ℝ := t • (-Real.sin (L a)) • L
  have hcos : HasFDerivAt (fun y => Real.cos (L y)) ((-Real.sin (L a)) • L) a :=
    (Real.hasDerivAt_cos (L a)).comp_hasFDerivAt a L.hasFDerivAt
  have hj : HasFDerivAt j J a := hcos.const_smul t
  have hD : HasFDerivAt (fun y => ContinuousLinearMap.id ℝ Vec3 - j y • B)
      (-(J.smulRight B)) a := by
    refine ((hj.smul_const B).neg.const_add (ContinuousLinearMap.id ℝ Vec3)).congr_of_eventuallyEq
      (Eventually.of_forall fun y => ?_)
    exact sub_eq_add_neg _ _
  have hJ : ‖J‖ ≤ 2 * Real.pi := by
    have hsin : |Real.sin (L a)| ≤ 1 := Real.abs_sin_le_one _
    calc
      ‖J‖ = t * |Real.sin (L a)| * ‖L‖ := by
        dsimp only [J]
        rw [norm_smul, norm_smul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht.1]
        ring
      _ ≤ 1 * 1 * (2 * Real.pi) := by gcongr; exact ht.2
      _ = _ := by ring
  have hBn : ‖B‖ ≤ 4 * Real.pi := norm_stationaryShearGradient_le hs
  rw [hEq, hD.fderiv]
  calc
    _ = ‖J‖ * ‖B‖ := (norm_neg _).trans (J.norm_smulRight_apply B)
    _ ≤ (2 * Real.pi) * (4 * Real.pi) :=
      mul_le_mul hJ hBn (norm_nonneg _) (by positivity)
    _ ≤ _ := by nlinarith

set_option maxHeartbeats 1000000 in
private theorem firstPressure_geometry {s t T freq r : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1)
    (hs : |s| ≤ 1) (ht : t ∈ Icc 0 T) (hf : 0 < freq) (hr : 0 < r) (hr₁ : r ≤ 1) :
    let A := stationaryShearFlow s (-t)
    let k := firstWaveLaunchCovector freq
    let B := firstPressureCoframeBound
    let phase (x : Vec3) := ⟪k, A x⟫_ℝ
    (∀ x, ‖gradient phase x‖ ≤ B * freq) ∧
      (∀ x, ‖Hess[phase] x‖ ≤ B * freq) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ 2 → ∀ x,
        ‖iteratedFDeriv ℝ j (fun y => r⁻¹ • A y) x‖ ≤ (r⁻¹ * B) ^ j) := by
  dsimp only
  let U : Velocity := fun _ => stationaryShear s
  let X (u v : ℝ) := stationaryShearFlow s (v - u)
  let L : ℝ := 1 + 8 * Real.pi ^ 2
  let B₀ : ℝ := 1 + 4 * Real.pi
  let B := firstPressureCoframeBound
  let k := firstWaveLaunchCovector freq
  let A := stationaryShearFlow s (-t)
  have hXt : X t 0 = A := by simp only [X, A, zero_sub]
  have hX₀ : X 0 t = stationaryShearFlow s t := by simp only [X, sub_zero]
  have ht₁ : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hT₁⟩
  have hUs : ContDiff ℝ ∞ (stationaryShear s) := by
    unfold stationaryShear
    exact (Real.contDiff_sin.comp (contDiff_const.mul
      (EuclideanSpace.proj (1 : Fin 3) : Vec3 →L[ℝ] ℝ).contDiff)).smul_const _
  have hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    (hUs.comp contDiff_snd).contDiffOn
  have hG (a : Vec3) : ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ B₀ := by
    rw [hXt, hX₀]
    exact (stationaryShearFlow_jacobian_norms hs ht₁ a).2
  have hG₁ (a : Vec3) : ‖fderiv ℝ (fun y => fderiv ℝ (X t 0) (X 0 t y)) a‖ ≤ L := by
    simp_rw [hXt, hX₀]
    exact firstPressureCoframe_firstJet hs ht₁ a
  have hL : 1 ≤ L := by dsimp only [L]; linarith [sq_nonneg Real.pi]
  have hGeo := (stationaryShear_isLabelFlowOn s (Icc 0 T)).primaryPressure_geometry
    (k := k) hT hr hL hU (fun _ _ => spatiallyPeriodic_stationaryShear s) ht hG hG₁
  have hk : ‖k‖ = freq := by
    simp [k, firstWaveLaunchCovector, norm_smul, EuclideanSpace.single, PiLp.norm_single,
      Real.norm_eq_abs, abs_of_pos hf]
  have hB₀ : 0 ≤ B₀ := by dsimp only [B₀]; positivity
  have hBB : B₀ ≤ B := le_mul_of_one_le_left hB₀ hL
  have hInvB : 1 ≤ r⁻¹ * B := one_le_mul_of_one_le_of_one_le
    (by simpa using one_le_inv₀ hr |>.mpr hr₁) one_le_firstPressureCoframeBound
  have hMax : max 1 (r⁻¹ * B) = r⁻¹ * B := max_eq_right hInvB
  refine ⟨?_, ?_, ?_⟩
  · intro x
    change ‖gradient (fun y => ⟪k, A y⟫_ℝ) x‖ ≤ B * freq
    have hGx : gradient (fun y => ⟪k, A y⟫_ℝ) x = labelWaveVector X 0 (X t 0 x) k t := by
      simpa only [X, A, zero_sub] using hGeo.1 x
    rw [hGx, labelWaveVector]
    have h := ((fderiv ℝ (X t 0) (X 0 t (X t 0 x))).adjoint).le_opNorm k
    rw [adjoint.norm_map, hk] at h
    exact h.trans (mul_le_mul_of_nonneg_right ((hG (X t 0 x)).trans hBB) hf.le)
  · intro x
    have h := hGeo.2.1 x
    rw [hk, mul_comm freq, show L * B₀ = B from rfl] at h
    simpa only [zero_sub, k] using h
  · intro j hj hj₂ x
    have h := hGeo.2.2 j hj hj₂ x
    rw [show L * B₀ = B from rfl, hMax] at h
    simpa only [zero_sub] using h

set_option maxHeartbeats 750000 in
private theorem firstPressure_eulerianCoefficientJets {p : Vec3 → ℝ} {A : Vec3 → Vec3}
    {r K B freq : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hB : 1 ≤ B) (hK : 0 ≤ K) (hf : 0 < freq)
    (hp : ContDiff ℝ ∞ p) (hA : ContDiff ℝ ∞ A)
    (hLabel : PhaseJetBound 2 (K * freq ^ (-7 / 4 : ℝ)) (fun y => p (r • y)))
    (hInv : ∀ j : ℕ, 1 ≤ j → j ≤ 2 → ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => r⁻¹ • A y) x‖ ≤ (r⁻¹ * B) ^ j) (x : Vec3) :
    let Q := 2 * K * B ^ 2 * r⁻¹ ^ 2 * freq ^ (-7 / 4 : ℝ)
    ‖p (A x)‖ ≤ Q ∧ ‖gradient (p ∘ A) x‖ ≤ Q ∧ ‖Hess[p ∘ A] x‖ ≤ Q := by
  let J := r⁻¹ * B
  let F (y : Vec3) := p (r • y)
  let R (y : Vec3) := r⁻¹ • A y
  have hJ : 1 ≤ J := one_le_mul_of_one_le_of_one_le ((one_le_inv₀ hr).mpr hr₁) hB
  have hsF : ContDiff ℝ ∞ F := hp.comp (contDiff_id.const_smul r)
  have hsR : ContDiff ℝ ∞ R := hA.const_smul _
  have he : F ∘ R = p ∘ A := by
    funext y
    change p (r • (r⁻¹ • A y)) = p (A y)
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hComp : PhaseJetBound 2 (2 * K * B ^ 2 * r⁻¹ ^ 2 * freq ^ (-7 / 4 : ℝ)) (p ∘ A) := by
    rw [← he]
    intro j hj y
    have hfct : (j.factorial : ℝ) ≤ 2 := by
      exact_mod_cast Nat.factorial_le (m := j) (n := 2) hj
    have hpow : J ^ j ≤ J ^ 2 := pow_le_pow_right₀ hJ hj
    calc
      _ ≤ (j.factorial : ℝ) * (K * freq ^ (-7 / 4 : ℝ)) * J ^ j :=
        norm_iteratedFDeriv_comp_le hsF hsR (by simp) y
          (fun i hi => hLabel i (hi.trans hj) (R y)) (fun i hi hij => hInv i hi (hij.trans hj) y)
      _ ≤ 2 * (K * freq ^ (-7 / 4 : ℝ)) * J ^ 2 := by gcongr
      _ = _ := by dsimp only [J]; ring
  refine ⟨?_, ?_, ?_⟩
  · simpa only [norm_iteratedFDeriv_zero, Function.comp_apply] using hComp 0 (by norm_num) x
  · have hOne := hComp 1 (by norm_num) x
    rw [norm_iteratedFDeriv_one] at hOne
    exact ((toDual ℝ Vec3).symm.norm_map _).trans_le hOne
  · rw [LocalizedAmplitude.SeedOn.norm_pressureHessian_eq_iteratedFDeriv]
    exact hComp 2 le_rfl x

set_option maxHeartbeats 1500000 in
private theorem stationaryPrimaryPressure_product_hessian_upper
    {freq B K : ℝ} (hf : 1 ≤ freq) (hB : 1 ≤ B) (hK : 0 ≤ K)
    {c phase : Vec3 → ℝ} (hc : ContDiff ℝ 2 c) (hphase : ContDiff ℝ 2 phase)
    (x v : Vec3) (hc₀ : 0 ≤ c x) (hκ : ‖gradient phase x‖ ≤ B * freq)
    (hφ : ‖Hess[phase] x‖ ≤ B * freq)
    (hCoeff : ‖c x‖ ≤ K * freq ^ (-7 / 4 : ℝ) ∧
      ‖gradient c x‖ ≤ K * freq ^ (-7 / 4 : ℝ) ∧
      ‖Hess[c] x‖ ≤ K * freq ^ (-7 / 4 : ℝ)) :
    let h := freq ^ (-1 / 2 : ℝ)
    ⟪v, Hess[fun y => -(c y * wavePressurePrimitive h (phase y))] x v⟫_ℝ ≤
      ((B ^ 2 / 2 + (3 * B ^ 2 + B)) * K * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2 := by
  let h := freq ^ (-1 / 2 : ℝ)
  let κ := gradient phase x
  let L := (-(c x * waveSlope h (phase x))) • rankOne ℝ κ κ
  let G := -(waveProfile h (phase x) •
    (rankOne ℝ (gradient c x) κ + rankOne ℝ κ (gradient c x) + c x • Hess[phase] x)) -
    wavePressurePrimitive h (phase x) • Hess[c] x
  let Q := K * freq ^ (-9 / 4 : ℝ)
  have hf₀ : 0 < freq := zero_lt_one.trans_le hf
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hh : 0 < h := Real.rpow_pos_of_pos hf₀ _
  have hh₁ : h ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hf (by norm_num)
  obtain ⟨hC, hC1, hC2⟩ := hCoeff
  have hLead (u : Vec3) : ⟪u, L u⟫_ℝ ≤ ((B ^ 2 / 2 * K) * freq ^ (-1 / 4 : ℝ)) * ‖u‖ ^ 2 := by
    have hcx : c x ≤ K * freq ^ (-7 / 4 : ℝ) := by
      simpa only [Real.norm_of_nonneg hc₀] using hC
    have hSq : ‖κ‖ ^ 2 ≤ (B * freq) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hκ 2
    refine (wavePrimaryPressure_leading_upper hh hh₁ hc₀ (phase x) κ u).trans ?_
    have hMajor : h / 2 * c x * ‖κ‖ ^ 2 ≤ h / 2 * (K * freq ^ (-7 / 4 : ℝ)) * (B * freq) ^ 2 := by
      gcongr
    refine (mul_le_mul_of_nonneg_right hMajor (sq_nonneg _)).trans_eq ?_
    rw [show (-1 / 4 : ℝ) = (-1 / 2) + (-7 / 4) + 2 by norm_num,
      Real.rpow_add hf₀, Real.rpow_add hf₀, Real.rpow_two]
    dsimp only [h]
    ring
  have hW : h * (K * freq ^ (-7 / 4 : ℝ)) = Q := by
    dsimp only [h, Q]
    rw [show (-9 / 4 : ℝ) = -1 / 2 + -7 / 4 by norm_num, Real.rpow_add hf₀]
    ring
  have hF : ‖waveProfile h (phase x)‖ ≤ h :=
    (norm_waveProfile_le hh hh₁ _).trans (by linarith)
  have hP : ‖wavePressurePrimitive h (phase x)‖ ≤ h := by
    have hp := norm_phasePrimitive_le (contDiff_waveProfile hh hh₁).continuous
      (periodic_waveProfile hh hh₁) (phaseMean_waveProfile hh hh₁)
      (fun s _ => norm_waveProfile_le hh hh₁ s) (phase x)
    change ‖wavePressurePrimitive h (phase x)‖ ≤ 2 * (h / 2) at hp
    linarith
  have hroot : 1 ≤ Real.sqrt freq := by simpa using Real.sqrt_le_sqrt hf
  have hstretch : Q ≤ B * Real.sqrt freq * Q := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_mul_of_one_le_of_one_le hB hroot) hQ
  have hstretch' : Q ≤ B * Q := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hB hQ
  have hF0 : ‖waveProfile h (phase x)‖ * ‖c x‖ ≤ B * Real.sqrt freq * Q :=
    ((mul_le_mul hF hC (norm_nonneg _) hh.le).trans_eq hW).trans hstretch
  have hF1 : ‖waveProfile h (phase x)‖ * ‖gradient c x‖ ≤ B * Real.sqrt freq * Q :=
    ((mul_le_mul hF hC1 (norm_nonneg _) hh.le).trans_eq hW).trans hstretch
  have hP2 : ‖wavePressurePrimitive h (phase x) • Hess[c] x‖ ≤ B * Q := by
    rw [norm_smul]
    exact ((mul_le_mul hP hC2 (norm_nonneg _) hh.le).trans_eq hW).trans hstretch'
  have hGeo : ‖G‖ ≤ ((3 * B ^ 2 + B) * K) * freq ^ (-3 / 4 : ℝ) :=
    norm_wavePrimaryPressure_geometricRemainder_le_at_hierarchy_scale hf hQ hB₀ le_rfl
      (waveProfile h (phase x)) (wavePressurePrimitive h (phase x)) (c x) κ (gradient c x)
      (Hess[phase] x) (Hess[c] x) hκ hφ hF1 hF0 hP2
  have hH : Hess[fun y => -(c y * wavePressurePrimitive h (phase y))] x = L + G + 0 + 0 := by
    rw [wavePrimaryPressure_hessian hh hh₁ hc hphase x]
    dsimp only [L, G, κ]
    abel
  have hTotal := wavePressure_hessian_upper_of_scales hf (show 0 ≤ (3 * B ^ 2 + B) * K by positivity)
    (le_refl (0 : ℝ)) (le_refl (0 : ℝ)) hH hLead hGeo (by simp) (by simp) v
  dsimp only [h]
  have hAdd : B ^ 2 / 2 * K + (3 * B ^ 2 + B) * K + 0 + 0 =
      (B ^ 2 / 2 + (3 * B ^ 2 + B)) * K := by ring
  rw [hAdd] at hTotal
  exact hTotal

private theorem firstWaveLeadingPressure_graph_eq_localized {T s c freq r h t : ℝ}
    (A : Velocity) (hf : freq ≠ 0) (hr : 0 < r) (hcell : 2 * r < 1 / 2)
    (hh : 0 < h) (hh₁ : h ≤ 1) (ht : t ∈ Icc 0 T) :
    HierarchyTwistedProfile.graphRead A (firstWaveHierarchyLeadingPressure (T := T) s c hf hr hcell hh hh₁) t =
      localizedTransportedProfile A (firstWaveLaunchCovector freq)
        (firstWaveLeadingPressureProfile s c freq r h) t := by
  funext y
  let k := firstWaveLaunchCovector freq
  change (firstWaveHierarchyLeadingPressure (T := T) s c hf hr hcell hh hh₁).val.val.val
    (t, A t y, ⟪k, A t y⟫_ℝ) = _
  rw [firstWaveHierarchyLeadingPressure_eval s c hf hr hcell hh hh₁ ⟨ht, mem_univ _⟩]
  exact phaseTwistedPeriodizeCentered_on_graph A k _ t y

set_option maxHeartbeats 2000000 in
/-- The signed first-wave pressure Hessian on the entire periodic lift.
The only radius loss is the two slow spatial derivatives of the envelope. -/
theorem exists_firstWavePrimaryPressure_hessian_upper :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {s T freq r : ℝ} (w : FirstWaveOrigin s T freq),
      0 < T → T ≤ 1 → |s| ≤ 1 → 1 ≤ freq → 0 < r → 2 * r ≤ 1 / 4 →
      ∀ t ∈ Icc 0 T, ∀ x v : Vec3,
      let h := freq ^ (-1 / 2 : ℝ)
      let A : Velocity := fun u => stationaryShearFlow s (-u)
      let k := firstWaveLaunchCovector freq
      let p := localizedTransportedProfile A k (firstWaveLeadingPressureProfile s w.scale freq r h) t
      ⟪v, Hess[p] x v⟫_ℝ ≤ (K * r⁻¹ ^ 2 * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2 := by
  obtain ⟨K, hK, hJet⟩ := exists_firstLabelPressureCoefficient_jetBound
  let B := firstPressureCoframeBound
  have hB : 1 ≤ B := one_le_firstPressureCoframeBound
  have hB₀ := zero_le_one.trans hB
  let C := (B ^ 2 / 2 + (3 * B ^ 2 + B)) * (2 * K * B ^ 2)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro s T freq r w hT hT₁ hs hf hr hfit t ht x v
  let h := freq ^ (-1 / 2 : ℝ)
  let A : Velocity := fun u => stationaryShearFlow s (-u)
  let X := stationaryShearFlow s t
  let k := firstWaveLaunchCovector freq
  have hf₀ : 0 < freq := zero_lt_one.trans_le hf
  have hh : 0 < h := Real.rpow_pos_of_pos hf₀ _
  have hh₁ : h ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hf (by norm_num)
  have hr₁ : r ≤ 1 := by linarith
  have hcell : 2 * r < 1 / 2 := by linarith
  let P := firstWaveHierarchyLeadingPressure (T := T) s w.scale hf₀.ne' hr hcell hh hh₁
  let p := HierarchyTwistedProfile.graphRead A P t
  let c := firstLabelPressureCoefficient s w.scale freq r t ∘ A t
  let phase (x : Vec3) := ⟪k, A t x⟫_ℝ
  let q (x : Vec3) := -(c x * wavePressurePrimitive h (phase x))
  have hpEq : p = localizedTransportedProfile A k (firstWaveLeadingPressureProfile s w.scale freq r h) t :=
    firstWaveLeadingPressure_graph_eq_localized A hf₀.ne' hr hcell hh hh₁ ht
  have hA : ContDiff ℝ ∞ (A t) :=
    (contDiff_stationaryShearFlow_inverse s).comp (contDiff_const.prodMk contDiff_id)
  have hX : ContDiff ℝ ∞ X := by
    have hX' := (contDiff_stationaryShearFlow_inverse s).comp
      (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun a : Vec3 => (-t, a)))
    change ContDiff ℝ ∞ (fun a => stationaryShearFlow s (-(-t)) a) at hX'
    simpa only [X, neg_neg] using hX'
  have hphase : ContDiff ℝ ∞ phase := (innerSL ℝ k).contDiff.comp hA
  have hlabel := contDiff_firstLabelPressureCoefficient s w.scale freq r t hf₀.ne' hr
  have hc : ContDiff ℝ ∞ c := hlabel.comp hA
  have hp : ContDiff ℝ ∞ p :=
    (HierarchySmoothProfile.contDiff_labelPhase_slice P.val.val ht).comp (hA.prodMk hphase)
  have hq : ContDiff ℝ ∞ q := (hc.mul ((contDiff_wavePressurePrimitive hh hh₁).comp hphase)).neg
  have hLeft : Function.LeftInverse X (A t) := by
    intro a
    simpa only [X, A, neg_neg] using stationaryShearFlow_inverse s (-t) a
  have hRight : Function.LeftInverse (A t) X := stationaryShearFlow_inverse s t
  have hEq : EqOn p q ((A t) ⁻¹' centeredCell) := by
    intro y hy
    have hay : A t y ∈ centeredCell := hy
    change P.val.val.val (t, A t y, phase y) = _
    rw [firstWaveHierarchyLeadingPressure_eval s w.scale hf₀.ne' hr hcell hh hh₁
      ⟨ht, mem_univ _⟩]
    have hPhase : phaseTwistedPeriodizeCentered k (firstWaveLeadingPressureProfile s w.scale freq r h)
        t (A t y) (phase y) = firstWaveLeadingPressureProfile s w.scale freq r h t (A t y) (phase y) := by
      apply phaseTwistedPeriodizeCentered_eq_on_centeredCell (δ := 1 / 2 - 2 * r)
        (sub_pos.mpr hcell) _ hay
      intro a ha z
      obtain ⟨i, hi⟩ := ha
      have hnorm : |a i| ≤ ‖a‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le a i
      have hrad : 2 * r ≤ ‖a‖ := by linarith
      simp only [firstWaveLeadingPressureProfile, radialEnvelope_eq_zero hr hrad, zero_mul]
    rw [hPhase, firstWaveLeadingPressureProfile_eq_product]
    rfl
  have hAPer : ∀ n : Fin 3 → ℤ, ∀ a, A t (a + latticeVector n) = A t a + latticeVector n :=
    stationaryShearFlow_lattice_equiv s (-t)
  have hPP := HierarchyTwistedProfile.spatiallyPeriodic_graphRead A P t hAPer
  have hGradient : ContDiff ℝ ∞ (gradient p) :=
    (toDual ℝ Vec3).symm.contDiff.comp (hp.fderiv_right (m := ∞) (by simp))
  have hHPer := (hPP.gradient (hp.differentiable (by simp))).fderiv (hGradient.differentiable (by simp))
  obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell (A t x)
  let y := x - latticeVector n
  have hArep : A t y = A t x - latticeVector n := by
    have h := hAPer n y
    rw [show y + latticeVector n = x from sub_add_cancel _ _] at h
    rw [h, add_sub_cancel_right]
  have hy : A t y ∈ centeredCell := hArep ▸ hn
  have hH := hHPer n y
  rw [show y + latticeVector n = x from sub_add_cancel _ _] at hH
  have hRawHessian : Hess[p] y = Hess[q] y :=
    LocalizedAmplitude.SeedOn.pressureHessian_eq_of_labelCell hA.continuous hX.continuous
      hLeft hRight hp hq hEq hy
  have hGeom := firstPressure_geometry hT hT₁ hs ht hf₀ hr hr₁
  have hCoeff := firstPressure_eulerianCoefficientJets hr hr₁ hB hK hf₀ hlabel hA
    (hJet w hT₁ hf₀ hr hr₁ ht) hGeom.2.2 y
  let Q := 2 * K * B ^ 2 * r⁻¹ ^ 2
  have hBound := stationaryPrimaryPressure_product_hessian_upper hf hB (K := Q) (by dsimp only [Q]; positivity)
    (hc.of_le (by simp)) (hphase.of_le (by simp)) y v
    (firstLabelPressureCoefficient_nonneg (A t y) w.scale_pos.le hf₀ hr hfit)
    (hGeom.1 y) (hGeom.2.1 y) hCoeff
  change ⟪v, Hess[localizedTransportedProfile A k (firstWaveLeadingPressureProfile s w.scale freq r h) t] x v⟫_ℝ ≤ _
  rw [← hpEq, hH, hRawHessian]
  have hFinal : (B ^ 2 / 2 + (3 * B ^ 2 + B)) * Q = C * r⁻¹ ^ 2 := by dsimp only [Q, C]; ring
  simpa only [hFinal, q, h] using hBound

namespace InductiveFirstWaveSelection

/-- The selected first pressure in the actual finite approximation has
its uniform one-sided Hessian bound with the scheduled parent scale. -/
theorem exists_leading_pressure_hessian_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : InductiveEulerParameters) (a : ℕ)
      (d : InductiveFirstWaveSelection P a) (t : ℝ), t ∈ Icc 0 (P.slab 1 0) → ∀ x v : Vec3,
      ⟪v, Hess[d.approximation.leadingPressure t] x v⟫_ℝ ≤
        (K * (P.frequency 0 ^ 9) ^ (2 * a) * P.frequency 1 ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2 := by
  obtain ⟨K, hK, hBound⟩ := exists_firstWavePrimaryPressure_hessian_upper
  refine ⟨K, hK, ?_⟩
  intro P a d t ht x v
  have hD : 4 ≤ P.frequency 0 ^ 9 := d.frequency_base_ge_four.trans
    (le_self_pow₀ ((by norm_num : (1 : ℝ) ≤ 4).trans d.frequency_base_ge_four)
      (by decide : (9 : ℕ) ≠ 0))
  have hR : radius P a ≤ ((4 : ℝ) ^ 2)⁻¹ :=
    (d.radius_le_inverse_power (j := 2) (by have ha := d.exponent_ge; omega)).trans
      (inv_anti₀ (by norm_num) (pow_le_pow_left₀ (by norm_num) hD 2))
  have hfit : 2 * radius P a ≤ 1 / 4 := by norm_num at hR; linarith
  have h := hBound d.origin d.time_pos d.time_le_one d.tilt_small d.frequency_ge_one d.radius_pos
    hfit t ht x v
  have hA : (fun u => d.parent.flow u 0) = fun u => stationaryShearFlow P.firstWaveTilt (-u) := by
    funext u
    simp only [d.parent_flow, zero_sub]
  have hRead : d.approximation.leadingPressure t =
      localizedTransportedProfile (fun u => stationaryShearFlow P.firstWaveTilt (-u))
        (firstWaveLaunchCovector (P.frequency 1))
        (firstWaveLeadingPressureProfile P.firstWaveTilt d.origin.scale (P.frequency 1)
          (radius P a) (width P)) t := by
    let Q := firstWaveHierarchyLeadingPressure (T := P.slab 1 0) P.firstWaveTilt d.origin.scale
      d.frequency_pos.ne' d.radius_pos d.radius_cell d.width_pos d.width_le_one
    change HierarchyTwistedProfile.graphRead (fun u => d.parent.flow u 0) Q t = _
    rw [hA]
    exact firstWaveLeadingPressure_graph_eq_localized _ d.frequency_pos.ne' d.radius_pos d.radius_cell
      d.width_pos d.width_le_one ht
  rw [hRead]
  have hRpow : (radius P a)⁻¹ ^ 2 = (P.frequency 0 ^ 9) ^ (2 * a) := by
    rw [radius, inv_inv, ← pow_mul, Nat.mul_comm a 2]
  simpa only [hRpow, width] using h

end InductiveFirstWaveSelection

end
end TorusEuler
