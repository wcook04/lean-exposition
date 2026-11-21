import TorusEuler.ActivationProfiles
import TorusEuler.ChildFlowDeformation
import TorusEuler.PhysicalAmplificationCrossing
import TorusEuler.PhysicalCutoffEstimates
import TorusEuler.TruncatedParentResidual
import TorusEuler.WaveProfile

/-! The child estimates in items 5 and 6 of the proof of frozen Theorem 7.1. -/

open ContinuousLinearMap InnerProductSpace Set Filter
open scoped ContDiff InnerProductSpace NNReal Topology

namespace TorusEuler

open ChildFlow (DeformationOn)

noncomputable section

private theorem scheduledChildFrequency_lower {μ : ℝ} {b q : ℕ}
    (hμ : 1 ≤ μ) (hb : 1 ≤ b) {n : ℕ} (hn : n ≤ 320) :
    μ ^ n ≤ μ ^ frequencyExponent b q := by
  have hK : 320 ≤ frequencyExponent b q := by
    change 320 * 1 * 1 ≤ 320 * b * (q + 1)
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 320 hb) (Nat.succ_pos _)
  exact pow_le_pow_right₀ hμ (hn.trans hK)

private theorem scheduledChildFrequencies {μ : ℝ} {b q qNext : ℕ} (hμ : 2 ≤ μ) (hb : 1 ≤ b) :
    let freq := μ ^ frequencyExponent b q
    let next := freq ^ frequencyExponent b qNext
    2 * μ ≤ freq ∧ (2 : ℝ) ^ (12 : ℕ) ≤ freq ∧ freq ≤ next := by
  let freq := μ ^ frequencyExponent b q
  have hμ₁ : 1 ≤ μ := by linarith
  have hFreq : 2 * μ ≤ freq :=
    (show 2 * μ ≤ μ ^ (2 : ℕ) by nlinarith).trans
      (scheduledChildFrequency_lower hμ₁ hb (by decide))
  have hFreq₁ : 1 ≤ freq := by nlinarith
  exact ⟨hFreq,
    (pow_le_pow_left₀ zero_le_two hμ 12).trans
      (scheduledChildFrequency_lower hμ₁ hb (by decide)),
    (pow_one freq).symm.le.trans
      (scheduledChildFrequency_lower hFreq₁ hb (by decide))⟩

/-- The oscillatory size and the child deformation are valid at the
inductive frequency once the step constant has been absorbed. -/
theorem induction_child_oscillation_and_deformation_budget {freq Cstep : ℝ}
    (hfreq : 1 ≤ freq) (hCstep : Cstep ≤ freq ^ (1 / 32 : ℝ)) :
    Cstep * freq ^ (-5 / 4 : ℝ) ≤ freq⁻¹ ∧
      Cstep * freq ^ (1 / 4 : ℝ) ≤ freq := by
  have hf : 0 < freq := zero_lt_one.trans_le hfreq
  constructor
  · calc
      _ ≤ freq ^ (1 / 32 : ℝ) * freq ^ (-5 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hCstep (by positivity)
      _ = freq ^ (-39 / 32 : ℝ) := by rw [← Real.rpow_add hf]; norm_num
      _ ≤ freq⁻¹ := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le hfreq (by norm_num)
  · apply child_flow_deformation_scale_le_frequency hfreq
    calc
      _ ≤ freq ^ (1 / 32 : ℝ) * freq ^ (-1 / 12 : ℝ) :=
        mul_le_mul_of_nonneg_right hCstep (by positivity)
      _ = freq ^ (-5 / 96 : ℝ) := by rw [← Real.rpow_add hf]; norm_num
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hfreq (by norm_num)

/-- The cutoff perturbation fits the smallness hypothesis in Lemma 5.10. -/
theorem induction_child_flow_tail_budget {freq next : ℝ} (hfreq : 1 ≤ freq)
    (hnext : freq ≤ next) : next ^ (-5 : ℝ) ≤ freq ^ (-5 / 2 : ℝ) :=
  (Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hfreq) hnext (by norm_num)).trans
    (Real.rpow_le_rpow_of_exponent_le hfreq (by norm_num))

/-- Both contributions to the nonoscillatory part of (7.4) fit in one
inverse power of the child frequency. -/
theorem induction_child_increment_budget {freq next : ℝ} (hfreq : 4 ≤ freq)
    (hnext : freq ≤ next) : freq ^ (-3 / 2 : ℝ) + next ^ (-4 : ℝ) ≤ freq⁻¹ := by
  have hf : 0 < freq := by linarith
  have hf₁ : 1 ≤ freq := by linarith
  have hroot : 2 ≤ freq ^ (1 / 2 : ℝ) := by
    have h := Real.rpow_le_rpow (show 0 ≤ (4 : ℝ) by norm_num) hfreq
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    norm_num at h
    exact h
  have hmean : 2 * freq ^ (-3 / 2 : ℝ) ≤ freq⁻¹ := calc
    _ ≤ freq ^ (1 / 2 : ℝ) * freq ^ (-3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right hroot (by positivity)
    _ = _ := by rw [← Real.rpow_add hf, ← Real.rpow_neg_one]; norm_num
  have htail : next ^ (-4 : ℝ) ≤ freq ^ (-3 / 2 : ℝ) :=
    (Real.rpow_le_rpow_of_nonpos hf hnext (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le hf₁ (by norm_num))
  linarith only [hmean, htail]

/-- The cutoff gradient adds only a fifth inverse power of the next
frequency to the central error of (5.50). -/
theorem induction_child_center_error_budget {freq next : ℝ}
    (hfreq : (2 : ℝ) ^ (12 : ℕ) ≤ freq) (hnext : freq ≤ next) :
    freq ^ (-1 / 3 : ℝ) + next ^ (-5 : ℝ) ≤ freq ^ (-1 / 4 : ℝ) := by
  have hf : 0 < freq := by linarith [(by norm_num : (0 : ℝ) < 2 ^ (12 : ℕ))]
  have hf₁ : 1 ≤ freq := (by norm_num : (1 : ℝ) ≤ 2 ^ (12 : ℕ)).trans hfreq
  have hroot : 2 ≤ freq ^ (1 / 12 : ℝ) := by
    have h := Real.rpow_le_rpow (show 0 ≤ (2 : ℝ) ^ (12 : ℕ) by positivity) hfreq
      (show (0 : ℝ) ≤ 1 / 12 by norm_num)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ (2 : ℝ) by norm_num)] at h
    norm_num at h
    exact h
  have hpre : 2 * freq ^ (-1 / 3 : ℝ) ≤ freq ^ (-1 / 4 : ℝ) := calc
    _ ≤ freq ^ (1 / 12 : ℝ) * freq ^ (-1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hroot (by positivity)
    _ = _ := by rw [← Real.rpow_add hf]; norm_num
  have htail : next ^ (-5 : ℝ) ≤ freq ^ (-1 / 3 : ℝ) :=
    (Real.rpow_le_rpow_of_nonpos hf hnext (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le hf₁ (by norm_num))
  linarith only [hpre, htail]

/-- The pressure upper bound from (5.57) fits the increment in (T3). -/
theorem frequencySchedule_child_pressure_budget
    {μ Cstep C : ℝ} {b q qNext : ℕ} (hμ : 2 ≤ μ) (hb : 1 ≤ b) (hC : 0 ≤ C)
    (hCstep : Cstep ≤ (μ ^ frequencyExponent b q) ^ (1 / 32 : ℝ))
    (hlarge : max 2 ((2 * C) ^ (2 : ℕ)) ≤ (μ ^ frequencyExponent b q) ^ frequencyExponent b qNext) :
    let freq := μ ^ frequencyExponent b q
    let next := freq ^ frequencyExponent b qNext
    Cstep * freq ^ (-1 / 4 : ℝ) + (C * next ^ (-7 / 2 : ℝ) + next ^ (-5 : ℝ)) ≤ μ⁻¹ := by
  let freq := μ ^ frequencyExponent b q
  let next := freq ^ frequencyExponent b qNext
  obtain ⟨hFreq, _, hnext⟩ := scheduledChildFrequencies (q := q) (qNext := qNext) hμ hb
  change 2 * μ ≤ freq at hFreq
  change freq ≤ next at hnext
  have hf : 0 < freq := by linarith
  have hμ₀ : 0 < μ := by linarith
  have hμ₁ : 1 ≤ μ := by linarith
  have hμFreq : μ ≤ next := (by linarith : μ ≤ freq).trans hnext
  have hFreqTen : μ ^ (10 : ℕ) ≤ freq :=
    scheduledChildFrequency_lower hμ₁ hb (by decide)
  have hleading : Cstep * freq ^ (-1 / 4 : ℝ) ≤ μ ^ (-2 : ℝ) := calc
    _ ≤ freq ^ (1 / 32 : ℝ) * freq ^ (-1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right hCstep (by positivity)
    _ = freq ^ (-7 / 32 : ℝ) := by rw [← Real.rpow_add hf]; norm_num
    _ ≤ (μ ^ (10 : ℕ)) ^ (-7 / 32 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hFreqTen (by norm_num)
    _ = μ ^ (-35 / 16 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hμ₀.le]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hμ₁ (by norm_num)
  have htail : C * next ^ (-7 / 2 : ℝ) + next ^ (-5 : ℝ) ≤ μ ^ (-2 : ℝ) :=
    (truncatedParent_residual_rate hC hlarge).trans
      ((Real.rpow_le_rpow_of_nonpos hμ₀ hμFreq (by norm_num)).trans
        (Real.rpow_le_rpow_of_exponent_le hμ₁ (by norm_num)))
  have htwo : 2 * μ ^ (-2 : ℝ) ≤ μ⁻¹ := by
    rw [Real.rpow_neg hμ₀.le, Real.rpow_two]
    have hdiv : 2 / (μ ^ (2 : ℕ)) ≤ 1 / μ :=
      (div_le_div_iff₀ (pow_pos hμ₀ 2) hμ₀).2 (by nlinarith)
    simpa only [div_eq_mul_inv, one_mul] using hdiv
  exact (add_le_add hleading htail).trans (by linarith only [htwo])

/-- A physical crossing occurs after the switching interval. The cutoff has
already reached one at the crossing itself and remains one afterward. -/
theorem MovingWaveVector.PhysicalAmplification.GrowingCrossing.waveSwitch_eq_one_after
    {I : Set ℝ} {t₀ : ℝ} {w : MovingWaveVector.PhysicalAmplification I t₀}
    {T scale Ustar next : ℝ} (d : w.GrowingCrossing T scale Ustar next)
    {t : ℝ} (ht : d.crossing ≤ t) : waveSwitch t₀ w.rate t = 1 := by
  apply waveSwitch_eq_one_of_activation w.rate_pos
  have h := d.delay_bounds.1
  linarith only [h, ht]

/-- The pre-cutoff oscillation's support shrinks to the origin, with the
lattice translates made explicit on the lift. -/
theorem induction_child_oscillation_lattice_support
    {μ ell : ℝ} {D : ℝ≥0} {U : Velocity} {Y : ℝ → Velocity} {T t : ℝ}
    {k : Vec3} {W : ℝ → Vec3 → ℝ → Vec3}
    (hμ : 2 ≤ μ) (hD : μ ≤ (D : ℝ)) (hell : ell ≤ ((D : ℝ) ^ (3 : ℕ))⁻¹)
    (hY : DeformationOn U Y T (D : ℝ)) (ht : t ∈ Icc 0 T)
    (hT : 0 < T) (hU : ContDiffOn ℝ 1 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hUPeriodic : ∀ s ∈ Icc 0 T, SpatiallyPeriodic (U s))
    (hUOdd : ∀ s ∈ Icc 0 T, Function.Odd (U s))
    (hW : ∀ a, 2 * ell < ‖a‖ → W t a ⟪k, a⟫_ℝ = 0)
    (x : Vec3) (hx : localizedTransportedProfile (fun s => Y s 0) k W t x ≠ 0) :
    ∃ n : Fin 3 → ℤ, dist (latticeVector n) x ≤ μ⁻¹ := by
  by_contra hno
  have hsep (n : Fin 3 → ℤ) : μ⁻¹ < dist x (latticeVector n) :=
    not_le.mp (fun hn => hno ⟨n, by simpa only [dist_comm] using hn⟩)
  apply hx
  have hD₀ : 0 < (D : ℝ) := by linarith
  have hμ₀ : 0 < μ := by linarith
  have hrad : (D : ℝ) * (2 * ell) ≤ μ⁻¹ := calc
    _ ≤ (D : ℝ) * (2 * ((D : ℝ) ^ (3 : ℕ))⁻¹) := by gcongr
    _ = 2 / (D : ℝ) ^ (2 : ℕ) := by field_simp
    _ ≤ _ := by
      rw [← one_div μ]
      apply (div_le_div_iff₀ (pow_pos hD₀ _) hμ₀).2
      nlinarith [mul_le_mul_of_nonneg_left hD (show 0 ≤ μ by linarith),
        mul_le_mul_of_nonneg_right hD (show 0 ≤ (D : ℝ) by positivity)]
  obtain ⟨⟨_, hInv⟩, hF, _⟩ := hY.bounds t ht
  have hLip : LipschitzWith D (Y 0 t) :=
    lipschitzWith_of_nnnorm_fderiv_le (fun a => (hF a).1)
      (fun a => by exact_mod_cast (hF a).2)
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  obtain ⟨K, hULip⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT hU hUPeriodic
  have hfix : Y 0 t 0 = 0 := by
    have h := (hY.flow.odd hULip hUOdd h0 ht) (0 : Vec3)
    rw [neg_zero] at h
    apply PiLp.ext
    intro i
    have hi := congrArg (fun z : Vec3 => z i) h
    simp only [PiLp.neg_apply] at hi
    rw [PiLp.zero_apply]
    linarith
  exact localizedTransportedProfile_eq_zero_of_lattice_separation
    (A := fun s => Y s 0) (t := t) (k := k) (f := W) hInv (hY.lattice 0 h0 t ht) hfix hLip hW x
    (fun n => hrad.trans_lt (hsep n))

/-- A vanishing label oscillation stays zero under periodization and
transport, including at the activation time with zero higher-profile data. -/
theorem induction_child_oscillation_zero_through_activation
    {A a : Velocity} {k : Vec3} {h ell t₀ r : ℝ}
    {C : ℝ → Vec3 → ℝ → Vec3}
    (hr : 0 ≤ r) (hC : ∀ t ≤ t₀, ∀ y s, C t y s = 0)
    {t : ℝ} (ht : t ≤ t₀) (x : Vec3) :
    localizedTransportedProfile A k
      (fun s y q => (waveSwitch t₀ r s * radialEnvelope ell y * waveProfile h q) • a s y +
        C s y q) t x = 0 := by
  simp [localizedTransportedProfile, periodizeCentered, waveSwitch_eq_zero_of_le hr ht, hC t ht]

/-- The leading transported and periodized primary wave has the rank-one
gradient in (5.50). The vanishing profile at phase zero eliminates all
derivatives of the coefficient. -/
theorem hasFDerivAt_inductionPrimaryWave_origin
    {A a : Velocity} {k : Vec3} {Ax : Vec3 →L[ℝ] Vec3} {chi : ℝ → ℝ}
    {h ell t : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (hell : 0 < ell) (hellLarge : 2 * ell < 1 / 2)
    (hA : HasFDerivAt (A t) Ax 0) (hA₀ : A t 0 = 0) (ha : DifferentiableAt ℝ (a t) 0) :
    let V₁ := fun s y q => (chi s * radialEnvelope ell y * waveProfile h q) • a s y
    HasFDerivAt (localizedTransportedProfile A k V₁ t)
      (chi t • rankOne ℝ (a t 0) (Ax.adjoint k)) 0 := by
  let V₁ := fun s y q => (chi s * radialEnvelope ell y * waveProfile h q) • a s y
  let phase : Vec3 → ℝ := fun x => ⟪k, A t x⟫_ℝ
  let B : Vec3 → Vec3 := fun x => (chi t * radialEnvelope ell (A t x)) • a t (A t x)
  have hphase₀ : phase 0 = 0 := by simp [phase, hA₀]
  have hphase : HasFDerivAt phase (innerSL ℝ (Ax.adjoint k)) 0 :=
    (hasGradientAt_transportedPhase hA).hasFDerivAt
  have hF : HasFDerivAt (waveProfile h ∘ phase) (innerSL ℝ (Ax.adjoint k)) 0 := by
    simpa only [one_smul] using
      (hasDerivAt_waveProfile_zero hh hh₁).comp_hasFDerivAt_of_eq 0 hphase hphase₀.symm
  have haA : DifferentiableAt ℝ (a t) (A t 0) := by simpa only [hA₀] using ha
  have hB : DifferentiableAt ℝ B 0 := by
    have hchi : DifferentiableAt ℝ (fun _ : Vec3 => chi t) 0 := differentiableAt_const _
    exact (hchi.mul (((contDiff_radialEnvelope hell).differentiable (by simp) (A t 0)).comp 0
      hA.differentiableAt)).smul (haA.comp 0 hA.differentiableAt)
  have hB₀ : B 0 = chi t • a t 0 := by
    simp [B, hA₀, radialEnvelope_eq_one hell (show ‖(0 : Vec3)‖ ≤ ell by simpa using hell.le)]
  have hd := hF.smul hB.hasFDerivAt
  rw [Function.comp_apply, hphase₀, waveProfile_zero, zero_smul, zero_add, hB₀] at hd
  have hTransport : HasFDerivAt (transportedProfile A k V₁ t)
      (chi t • rankOne ℝ (a t 0) (Ax.adjoint k)) 0 := by
    refine (hd.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
    · ext v
      simp [rankOne_apply, smul_smul, mul_comm]
    · simp [transportedProfile, V₁, phase, B, smul_smul, mul_comm]
  apply hTransport.congr_of_eventuallyEq
  have hz : (0 : Vec3) ∈ interior centeredCell := by
    apply mem_interior_iff_mem_nhds.mpr
    apply mem_of_superset (Metric.ball_mem_nhds (0 : Vec3) (show 0 < 1 / 2 by norm_num))
    intro x hx i
    have hnorm : ‖x‖ < (1 : ℝ) / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact abs_le.mp ((PiLp.norm_apply_le x i).trans hnorm.le)
  let delta := (1 / 2 : ℝ) - 2 * ell
  apply localizedTransportedProfile_eventuallyEq hA.continuousAt (hA₀.symm ▸ hz)
    (δ := delta) (by dsimp [delta]; linarith)
  intro y hy
  obtain ⟨i, hi⟩ := hy
  have hyr : 2 * ell ≤ ‖y‖ := by
    have h := hi.trans_le (PiLp.norm_apply_le y i)
    dsimp [delta] at h
    linarith
  simp [radialEnvelope_eq_zero hell hyr]

/-- Adding the cutoff correction to the center splitting of the
approximate child gives the central error in (T4). -/
theorem induction_child_center_split
    {V parent child tail : Velocity} {chi : ℝ → ℝ} {a k : ℝ → Vec3}
    {E : ℝ → (Vec3 →L[ℝ] Vec3)} {t start finish freq next : ℝ}
    (ht : t ∈ Icc start finish) (hfreq : (2 : ℝ) ^ (12 : ℕ) ≤ freq) (hnext : freq ≤ next)
    (hchild : child t = V t + tail t)
    (hV : DifferentiableAt ℝ (V t) 0) (hTail : DifferentiableAt ℝ (tail t) 0)
    (hcentral : ∀ s ∈ Icc start finish, fderiv ℝ (V s) 0 =
      fderiv ℝ (parent s) 0 + chi s • rankOne ℝ (a s) (k s) + E s)
    (hpre : ‖E t‖ ≤ freq ^ (-1 / 3 : ℝ))
    (htail : ‖fderiv ℝ (tail t) 0‖ ≤ next ^ (-5 : ℝ)) :
    let Ec := E t + fderiv ℝ (tail t) 0
    fderiv ℝ (child t) 0 = fderiv ℝ (parent t) 0 +
      chi t • rankOne ℝ (a t) (k t) + Ec ∧ ‖Ec‖ ≤ freq ^ (-1 / 4 : ℝ) := by
  dsimp only
  constructor
  · rw [hchild, (hV.hasFDerivAt.add hTail.hasFDerivAt).fderiv, hcentral t ht, add_assoc]
  · exact (norm_add_le _ _).trans
      ((add_le_add hpre htail).trans (induction_child_center_error_budget hfreq hnext))

theorem spatialHolderHalf_add_exact {f g : Vec3 → Vec3} {m : ℕ}
    (hf : SpatialHolderHalf m f) (hg : SpatialHolderHalf m g) :
    SpatialHolderHalf m (f + g) ∧
      spatialHolderHalfNorm m (f + g) ≤
        spatialHolderHalfNorm m f + spatialHolderHalfNorm m g := by
  have hjets (j : ℕ) (hj : j ≤ m) : iteratedFDeriv ℝ j (f + g) =
      iteratedFDeriv ℝ j f + iteratedFDeriv ℝ j g :=
    iteratedFDeriv_add (hf.1.of_le (by exact_mod_cast hj)) (hg.1.of_le (by exact_mod_cast hj))
  have hpoint (j : ℕ) (hj : j ≤ m) (x : Vec3) :
      ‖iteratedFDeriv ℝ j (f + g) x‖ ≤
        spatialSupNorm (iteratedFDeriv ℝ j f) + spatialSupNorm (iteratedFDeriv ℝ j g) := by
    rw [hjets j hj, Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add
      (norm_le_spatialSupNorm (hf.2 j hj).1 x) (norm_le_spatialSupNorm (hg.2 j hj).1 x))
  have hquot (j : ℕ) (hj : j ≤ m) (p : Vec3 × Vec3) :
      spatialHolderHalfQuotient (iteratedFDeriv ℝ j (f + g)) p ≤
        spatialHolderHalfSeminorm (iteratedFDeriv ℝ j f) +
          spatialHolderHalfSeminorm (iteratedFDeriv ℝ j g) := by
    have hdiff : iteratedFDeriv ℝ j (f + g) (p.1 + p.2) - iteratedFDeriv ℝ j (f + g) p.1 =
        (iteratedFDeriv ℝ j f (p.1 + p.2) - iteratedFDeriv ℝ j f p.1) +
          (iteratedFDeriv ℝ j g (p.1 + p.2) - iteratedFDeriv ℝ j g p.1) := by
      rw [hjets j hj]
      simp only [Pi.add_apply]
      abel
    unfold spatialHolderHalfQuotient
    rw [hdiff]
    refine (div_le_div_of_nonneg_right (norm_add_le _ _) (Real.sqrt_nonneg _)).trans ?_
    rw [add_div]
    exact add_le_add (le_ciSup (hf.2 j hj).2 p) (le_ciSup (hg.2 j hj).2 p)
  refine ⟨⟨hf.1.add hg.1, fun j hj =>
    ⟨⟨_, forall_mem_range.mpr (hpoint j hj)⟩, ⟨_, forall_mem_range.mpr (hquot j hj)⟩⟩⟩, ?_⟩
  unfold spatialHolderHalfNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have hj' : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hs := add_le_add (ciSup_le (hpoint j hj')) (ciSup_le (hquot j hj'))
  exact hs.trans_eq (by abel)

/-- The spatial half-Hölder norm controls each pointwise derivative
through its defining order. -/
theorem norm_iteratedFDeriv_le_spatialHolderHalfNorm {m j : ℕ} {f : Vec3 → Vec3}
    (hf : SpatialHolderHalf m f) (hj : j ≤ m) (x : Vec3) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ spatialHolderHalfNorm m f := by
  have hsemi (i : ℕ) (hi : i ≤ m) : 0 ≤ spatialHolderHalfSeminorm (iteratedFDeriv ℝ i f) := by
    have h := le_ciSup (hf.2 i hi).2 ((0 : Vec3), (0 : Vec3))
    rw [show spatialHolderHalfQuotient (iteratedFDeriv ℝ i f) (0, 0) = 0 by
      simp [spatialHolderHalfQuotient]] at h
    exact h
  have hlevel : spatialSupNorm (iteratedFDeriv ℝ j f) + spatialHolderHalfSeminorm
      (iteratedFDeriv ℝ j f) ≤ spatialHolderHalfNorm m f := by
    unfold spatialHolderHalfNorm
    apply Finset.single_le_sum _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    intro i hi
    have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    exact add_nonneg ((norm_nonneg _).trans (norm_le_spatialSupNorm (hf.2 i hi').1 0))
      (hsemi i hi')
  exact (norm_le_spatialSupNorm (hf.2 j hj).1 x).trans
    ((le_add_of_nonneg_right (hsemi j hj)).trans hlevel)

/-- The two Eulerian remainder parts in (7.4), with the frozen scale
and derivative order at the current and following wave. -/
theorem frequencySchedule_child_velocity_increment
    {μ Cmean : ℝ} {b q qNext m : ℕ} {child parent V osc mean tail : Vec3 → Vec3}
    (hμ : 2 ≤ μ) (hb : 1 ≤ b) (hm : m ≤ q) (hq : q ≤ qNext) (hCmean : Cmean ≤ μ)
    (hChild : child = V + tail) (hV : V = parent + osc + mean)
    (hMean : SpatialHolderHalf m mean) (hTail : SpatialHolderHalf m tail)
    (hMeanSize : spatialHolderHalfNorm m mean ≤ Cmean * (μ ^ 9) ^ (b * (m + 2)) *
      (μ ^ frequencyExponent b q) ^ (-5 / 2 : ℝ))
    (hTailSize : let freq := μ ^ frequencyExponent b q
      let next := freq ^ frequencyExponent b qNext
      spatialHolderHalfNorm m tail ≤ freq ^ (5 * m) * next ^ (-5 : ℝ)) :
    SpatialHolderHalf m (child - parent - osc) ∧
      spatialHolderHalfNorm m (child - parent - osc) ≤ (μ ^ frequencyExponent b q)⁻¹ := by
  let freq := μ ^ frequencyExponent b q
  let next := freq ^ frequencyExponent b qNext
  obtain ⟨hμfreq, _, hnext⟩ := scheduledChildFrequencies (q := q) (qNext := qNext) hμ hb
  change 2 * μ ≤ freq at hμfreq
  change freq ≤ next at hnext
  have hfreq : 4 ≤ freq := by linarith
  have hmean : spatialHolderHalfNorm m mean ≤ freq ^ (-3 / 2 : ℝ) := calc
    _ ≤ Cmean * (μ ^ 9) ^ (b * (m + 2)) * freq ^ (-5 / 2 : ℝ) := hMeanSize
    _ ≤ freq ^ (1 / 16 : ℝ) * freq ^ (-5 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right (frequencySchedule_lowOrder_mean_budget
        (q := q) (by linarith) hCmean hb hm) (by positivity)
    _ = freq ^ (-39 / 16 : ℝ) := by rw [← Real.rpow_add (by linarith : 0 < freq)]; norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have htail : spatialHolderHalfNorm m tail ≤ next ^ (-4 : ℝ) :=
    hTailSize.trans (frequencySchedule_lowOrder_tail_budget (qNext := qNext)
      (by linarith : 1 ≤ freq) hb hm hq)
  have hSplit : child - parent - osc = mean + tail := by
    rw [hChild, hV]
    abel
  rw [hSplit]
  obtain ⟨hsmooth, hsum⟩ := spatialHolderHalf_add_exact hMean hTail
  exact ⟨hsmooth, hsum.trans ((add_le_add hmean htail).trans
    (induction_child_increment_budget hfreq hnext))⟩

/-- A primary oscillation with the sharp amplitude bound and the small
nonoscillatory increment give the velocity part of (T2). -/
theorem induction_child_velocity_bound
    {μ freq : ℝ} {child parent osc : Vec3 → Vec3}
    (hμ : 2 ≤ μ) (hfreq : 2 * μ ≤ freq)
    (hParent : ∀ x, ‖parent x‖ ≤ μ) (hOsc : ∀ x, ‖osc x‖ ≤ freq⁻¹)
    (hRest : SpatialHolderHalf 0 (child - parent - osc))
    (hInc : spatialHolderHalfNorm 0 (child - parent - osc) ≤ freq⁻¹) (x : Vec3) :
    ‖child x‖ ≤ freq := by
  have hfreq₀ : 0 < freq := by linarith
  have hpt := (norm_iteratedFDeriv_le_spatialHolderHalfNorm hRest le_rfl x).trans hInc
  rw [norm_iteratedFDeriv_zero] at hpt
  have heq : child x = parent x + osc x + (child - parent - osc) x := by
    simp only [Pi.sub_apply]
    abel
  have hsmall : freq⁻¹ ≤ 1 := (inv_le_one₀ hfreq₀).mpr (by linarith)
  conv_lhs => rw [heq]
  calc
    _ ≤ ‖parent x‖ + ‖osc x‖ + ‖(child - parent - osc) x‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ μ + freq⁻¹ + freq⁻¹ := add_le_add (add_le_add (hParent x) (hOsc x)) hpt
    _ ≤ freq := by linarith

/-- The norms supplied by the physical step and by the truncation give all
three bounds in (T2) on the child's closed time interval. -/
theorem frequencySchedule_child_T2
    {μ Cstep C : ℝ} {b q qNext : ℕ} {T : ℝ}
    {parent child osc residual : Velocity} {Y : ℝ → Velocity}
    (hμ : 2 ≤ μ) (hb : 1 ≤ b) (hC : 0 ≤ C)
    (hCstep : Cstep ≤ (μ ^ frequencyExponent b q) ^ (1 / 32 : ℝ))
    (hlarge : max 2 ((2 * C) ^ (2 : ℕ)) ≤ (μ ^ frequencyExponent b q) ^ frequencyExponent b qNext)
    (hFlow : DeformationOn child Y T (Cstep * (μ ^ frequencyExponent b q) ^ (1 / 4 : ℝ)))
    (hParent : ∀ t ∈ Icc 0 T, ∀ x, ‖parent t x‖ ≤ μ)
    (hOsc : ∀ t ∈ Icc 0 T, ∀ x, ‖osc t x‖ ≤ Cstep * (μ ^ frequencyExponent b q) ^ (-5 / 4 : ℝ))
    (hInc : ∀ t ∈ Icc 0 T, SpatialHolderHalf 0 (child t - parent t - osc t) ∧
      spatialHolderHalfNorm 0 (child t - parent t - osc t) ≤ (μ ^ frequencyExponent b q)⁻¹)
    (hResidual : let next := (μ ^ frequencyExponent b q) ^ frequencyExponent b qNext
      ∀ t ∈ Icc 0 T, ∀ x, ‖residual t x‖ ≤ C * next ^ (-7 / 2 : ℝ) + next ^ (-5 : ℝ)) :
    let freq := μ ^ frequencyExponent b q
    let next := freq ^ frequencyExponent b qNext
    (∀ t ∈ Icc 0 T, ∀ x, ‖child t x‖ ≤ freq) ∧
      DeformationOn child Y T freq ∧
      (∀ t ∈ Icc 0 T, ∀ x, ‖residual t x‖ ≤ next ^ (-3 : ℝ)) := by
  let freq := μ ^ frequencyExponent b q
  obtain ⟨hμfreq, _, _⟩ := scheduledChildFrequencies (q := q) (qNext := qNext) hμ hb
  change 2 * μ ≤ freq at hμfreq
  obtain ⟨hOscBudget, hFlowBudget⟩ :=
    induction_child_oscillation_and_deformation_budget (by linarith : 1 ≤ freq) hCstep
  refine ⟨fun t ht x => induction_child_velocity_bound hμ hμfreq (hParent t ht)
    (fun y => (hOsc t ht y).trans hOscBudget) (hInc t ht).1 (hInc t ht).2 x, ?_, ?_⟩
  · refine ⟨hFlow.flow, hFlow.lattice, fun t ht => ?_⟩
    obtain ⟨hInv, hF, hG⟩ := hFlow.bounds t ht
    exact ⟨hInv, fun x => ⟨(hF x).1, (hF x).2.trans hFlowBudget⟩,
      fun x => ⟨(hG x).1, (hG x).2.trans hFlowBudget⟩⟩
  · intro t ht x
    exact (hResidual t ht x).trans (truncatedParent_residual_rate hC hlarge)

/-- The parent pressure budget on the larger slab passes to the next
stage after adding exactly the preceding frequency's inverse. -/
theorem frequencySchedule_child_T3
    {freq : ℕ → ℝ} {Cstep C Sparent Schild : ℝ} {b q qNext j : ℕ}
    {pParent pChild : Pressure}
    (hμ : 2 ≤ freq j) (hb : 1 ≤ b) (hC : 0 ≤ C) (hS : Schild ≤ Sparent)
    (hCstep : Cstep ≤ ((freq j) ^ frequencyExponent b q) ^ (1 / 32 : ℝ))
    (hlarge : max 2 ((2 * C) ^ (2 : ℕ)) ≤ ((freq j) ^ frequencyExponent b q) ^ frequencyExponent b qNext)
    (hParent : ∀ t ∈ Icc 0 Sparent, ∀ x v : Vec3,
      ⟪v, fderiv ℝ (gradient (pParent t)) x v⟫_ℝ ≤
        (∑ i ∈ Finset.range j, (freq i)⁻¹) * ‖v‖ ^ 2)
    (hIncrement : let f := (freq j) ^ frequencyExponent b q
      let next := f ^ frequencyExponent b qNext
      ∀ t ∈ Icc 0 Schild, ∀ x v : Vec3,
        ⟪v, fderiv ℝ (gradient (pChild t)) x v⟫_ℝ ≤
          ⟪v, fderiv ℝ (gradient (pParent t)) x v⟫_ℝ +
            (Cstep * f ^ (-1 / 4 : ℝ) + (C * next ^ (-7 / 2 : ℝ) + next ^ (-5 : ℝ))) * ‖v‖ ^ 2) :
    ∀ t ∈ Icc 0 Schild, ∀ x v : Vec3,
      ⟪v, fderiv ℝ (gradient (pChild t)) x v⟫_ℝ ≤
        (∑ i ∈ Finset.range (j + 1), (freq i)⁻¹) * ‖v‖ ^ 2 := by
  intro t ht x v
  have hprev := hParent t ⟨ht.1, ht.2.trans hS⟩ x v
  have hB := frequencySchedule_child_pressure_budget (C := C) (qNext := qNext) hμ hb hC hCstep hlarge
  refine (hIncrement t ht x v).trans ?_
  calc
    _ ≤ (∑ i ∈ Finset.range j, (freq i)⁻¹) * ‖v‖ ^ 2 + (freq j)⁻¹ * ‖v‖ ^ 2 :=
      add_le_add hprev (mul_le_mul_of_nonneg_right hB (sq_nonneg ‖v‖))
    _ = _ := by rw [Finset.sum_range_succ, add_mul]

/-- The full-depth Fourier-tail estimate yields precisely the weaker
low-order tail input needed in (7.4), including orders zero and one. -/
theorem induction_child_cutoffTail_budget {freq next μ K size tail : ℝ} {m P : ℕ}
    (hfreq : 1 ≤ freq) (hμ : 0 ≤ μ) (hsize : 0 ≤ size) (hK : K ≤ μ)
    (hTail : tail ≤ K * (freq ^ (5 : ℕ)) ^ ((m : ℤ) - P) * size)
    (hEpsilon : μ * ((freq ^ (5 : ℕ)) ^ ((2 : ℤ) - P) * (1 + size) ^ (2 : ℕ)) ≤
      next ^ (-5 : ℝ)) :
    tail ≤ freq ^ (5 * m) * next ^ (-5 : ℝ) := by
  let cutoff := freq ^ (5 : ℕ)
  have hcutoff : 1 ≤ cutoff := one_le_pow₀ hfreq
  have hcutoff₀ : 0 < cutoff := zero_lt_one.trans_le hcutoff
  have hpow : cutoff ^ ((m : ℤ) - P) ≤ cutoff ^ m * cutoff ^ ((2 : ℤ) - P) := by
    rw [← zpow_natCast, ← zpow_add₀ hcutoff₀.ne']
    exact zpow_le_zpow_right₀ hcutoff (by omega)
  have hsize' : size ≤ (1 + size) ^ (2 : ℕ) := by nlinarith
  calc
    _ ≤ K * cutoff ^ ((m : ℤ) - P) * size := hTail
    _ ≤ μ * cutoff ^ ((m : ℤ) - P) * size := by gcongr
    _ ≤ μ * (cutoff ^ m * cutoff ^ ((2 : ℤ) - P)) * (1 + size) ^ (2 : ℕ) := by gcongr
    _ = cutoff ^ m * (μ * (cutoff ^ ((2 : ℤ) - P) * (1 + size) ^ (2 : ℕ))) := by ring
    _ ≤ cutoff ^ m * next ^ (-5 : ℝ) := mul_le_mul_of_nonneg_left hEpsilon (by positivity)
    _ = _ := by rw [← pow_mul]

/-- The central error of the approximate child is the derivative of the
remaining oscillatory profiles and the mean field. -/
theorem induction_approximate_child_center_split
    {parent primary oscRemainder mean V : Vec3 → Vec3} {A K : Vec3}
    {freq Cstep chi : ℝ}
    (hfreq : 1 ≤ freq) (hCstep : Cstep ≤ freq ^ (1 / 32 : ℝ))
    (hV : V = parent + primary + oscRemainder + mean)
    (hParent : DifferentiableAt ℝ parent 0)
    (hPrimary : HasFDerivAt primary (chi • rankOne ℝ A K) 0)
    (hOsc : DifferentiableAt ℝ oscRemainder 0) (hMean : DifferentiableAt ℝ mean 0)
    (hBound : ‖fderiv ℝ oscRemainder 0‖ + ‖fderiv ℝ mean 0‖ ≤
      Cstep * freq ^ (-5 / 12 : ℝ)) :
    let E := fderiv ℝ oscRemainder 0 + fderiv ℝ mean 0
    fderiv ℝ V 0 = fderiv ℝ parent 0 + chi • rankOne ℝ A K + E ∧
      ‖E‖ ≤ freq ^ (-1 / 3 : ℝ) := by
  dsimp only
  constructor
  · rw [hV, (((hParent.hasFDerivAt.add hPrimary).add hOsc.hasFDerivAt).add
      hMean.hasFDerivAt).fderiv, add_assoc]
  · calc
      _ ≤ ‖fderiv ℝ oscRemainder 0‖ + ‖fderiv ℝ mean 0‖ := norm_add_le _ _
      _ ≤ Cstep * freq ^ (-5 / 12 : ℝ) := hBound
      _ ≤ freq ^ (1 / 12 : ℝ) * freq ^ (-5 / 12 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact hCstep.trans (Real.rpow_le_rpow_of_exponent_le hfreq (by norm_num))
      _ = _ := by rw [← Real.rpow_add (zero_lt_one.trans_le hfreq)]; norm_num

/-- The central statement in (T4) on both active slabs and at the
physical crossing, with the cutoff gradient controlled by the actual tail norm. -/
theorem frequencySchedule_child_T4_center
    {I : Set ℝ} {t₀ μ T Ustar ratio half : ℝ}
    {w : MovingWaveVector.PhysicalAmplification I t₀} {b q qNext : ℕ}
    {parent V child tail : Velocity} {E : ℝ → Vec3 →L[ℝ] Vec3}
    (d : w.GrowingCrossing T (μ ^ frequencyExponent b q) Ustar ratio)
    (hμ : 2 ≤ μ) (hb : 1 ≤ b) (hhalf : d.crossing - t₀ ≤ half)
    (hChild : ∀ t ∈ w.activeSlab T, child t = V t + tail t)
    (hV : ∀ t ∈ w.activeSlab T, DifferentiableAt ℝ (V t) 0)
    (hTail : let next := (μ ^ frequencyExponent b q) ^ frequencyExponent b qNext
      ∀ t ∈ w.activeSlab T, SpatialHolderHalf 2 (tail t) ∧
        spatialHolderHalfNorm 2 (tail t) ≤ next ^ (-5 : ℝ))
    (hPre : ∀ t ∈ w.activeSlab T,
      fderiv ℝ (V t) 0 = fderiv ℝ (parent t) 0 +
        waveSwitch t₀ w.rate t • rankOne ℝ (d.amplitude t) (d.waveVector t) + E t ∧
      ‖E t‖ ≤ (μ ^ frequencyExponent b q) ^ (-1 / 3 : ℝ)) :
    let freq := μ ^ frequencyExponent b q
    let centerError := fun t => E t + fderiv ℝ (tail t) 0
    (∀ t ∈ w.activeSlab T,
      fderiv ℝ (child t) 0 = fderiv ℝ (parent t) 0 +
        waveSwitch t₀ w.rate t • rankOne ℝ (d.amplitude t) (d.waveVector t) + centerError t ∧
      ‖centerError t‖ ≤ freq ^ (-1 / 4 : ℝ)) ∧
    (∀ t ∈ Icc d.crossing (w.clock T), waveSwitch t₀ w.rate t = 1 ∧
      fderiv ℝ (child t) 0 = fderiv ℝ (parent t) 0 +
        rankOne ℝ (d.amplitude t) (d.waveVector t) + centerError t) ∧
    0 ≤ d.crossing - t₀ ∧ d.crossing - t₀ ≤ half ∧
    w.physicalEta d.waveVector d.amplitude d.crossing /
      w.physicalNu d.waveVector d.amplitude d.crossing = ratio := by
  let freq := μ ^ frequencyExponent b q
  let centerError := fun t => E t + fderiv ℝ (tail t) 0
  obtain ⟨_, hfreq, hnext⟩ := scheduledChildFrequencies (q := q) (qNext := qNext) hμ hb
  have hstage (t : ℝ) (ht : t ∈ w.activeSlab T) :
      fderiv ℝ (child t) 0 = fderiv ℝ (parent t) 0 +
        waveSwitch t₀ w.rate t • rankOne ℝ (d.amplitude t) (d.waveVector t) + centerError t ∧
      ‖centerError t‖ ≤ freq ^ (-1 / 4 : ℝ) := by
    obtain ⟨hTailReg, hTailSize⟩ := hTail t ht
    have hTailDiff : DifferentiableAt ℝ (tail t) 0 :=
      (hTailReg.1.differentiable (by norm_num)) 0
    have hTailJet := norm_iteratedFDeriv_le_spatialHolderHalfNorm hTailReg (by decide : 1 ≤ 2) 0
    rw [norm_iteratedFDeriv_one] at hTailJet
    exact induction_child_center_split ht hfreq hnext (hChild t ht) (hV t ht) hTailDiff
      (fun s hs => (hPre s hs).1) (hPre t ht).2 (hTailJet.trans hTailSize)
  have hcross : t₀ ≤ d.crossing := d.crossing_in_slab.1
  refine ⟨hstage, ?_, sub_nonneg.mpr hcross, hhalf, d.crossing_ratio⟩
  intro t ht
  have hone := d.waveSwitch_eq_one_after ht.1
  refine ⟨hone, ?_⟩
  simpa only [hone, one_smul] using (hstage t ⟨hcross.trans ht.1, ht.2⟩).1

end

end TorusEuler
