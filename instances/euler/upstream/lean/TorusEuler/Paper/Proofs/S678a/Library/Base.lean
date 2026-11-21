import TorusEuler.Paper.Proofs.S678a.Library.StepBuild
import TorusEuler.Paper.Proofs.S678a.Library.LaterWaveTip
import TorusEuler.FirstWaveHierarchyInput
import TorusEuler.InductionChildEstimates

/-! # The base of the construction of Theorem 7.1 (package S678a)

Items 1-2 of the proof (sections/08b_induction.tex:252-256 for the base, :285-290 for the first wave, Subsection 6.1): the stationary shear
`U_0` at `ρ = ε_1`, the first wave of Lemma 6.1 (from `h6_1`: `FirstWaveOrigin` and the
conditions (5.5) of `Lemma61Conclusions`), the expansion of Subsection 5.5 over `U_0` with the
cutoff `χ̃_1 = 1` (`h5_4`), and the first child `U_1` from Lemmas 5.8-5.10 and Proposition 5.11
(`exists_child_of_section5` at the parent index `0`). -/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler HierarchyTwistedProfile LocalizedAmplitude
open TorusEuler.MovingWaveVector (frame entry)

noncomputable section

/-- The two conditions (5.5) from the conclusions of Lemma 6.1: the first wave is a central wave
of the stationary parent for every `D ≥ 2` (sections/03a_exact_base.tex:38, Lemma 6.1). -/
theorem centerWaveOn_of_lemma61 {s T freq D : ℝ} (w : FirstWaveOrigin s T freq)
    (hc : Lemma61Conclusions w) (hf : 0 < freq) (hD : 2 ≤ D) :
    CenterWaveOn (fun _ => stationaryShearGradient s) w.covector w.amplitude 0 T D := by
  refine ⟨w.covector_equation, w.transverse, w.amplitude_equation, ?_, ?_⟩
  · intro z hz hperp u v hu hv huv
    have h := hc.propagation D hD z hz hperp u v hu hv huv
    have hfp : 0 < freq ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hf _
    have hav : 0 < ‖w.amplitude v‖ := norm_pos_iff.mpr (w.transverse v hv).2.1
    have hau : 0 < ‖w.amplitude u‖ := norm_pos_iff.mpr (w.transverse u hu).2.1
    calc ‖z v‖ / ‖w.amplitude v‖ = freq ^ (3 / 4 : ℝ) * (‖z v‖ / (freq ^ (3 / 4 : ℝ) * ‖w.amplitude v‖)) := by
          field_simp
      _ ≤ freq ^ (3 / 4 : ℝ) * (D * (‖z u‖ / (freq ^ (3 / 4 : ℝ) * ‖w.amplitude u‖))) :=
          mul_le_mul_of_nonneg_left h hfp.le
      _ = D * (‖z u‖ / ‖w.amplitude u‖) := by field_simp
  · intro t ht
    have h := hc.coupling D hD t ht
    have hk : 0 < ‖w.covector t‖ := norm_pos_iff.mpr (w.transverse t ht).1
    have ha : 0 < ‖w.amplitude t‖ := norm_pos_iff.mpr (w.transverse t ht).2.1
    have he : entry (frame w.covector w.amplitude t) (stationaryShearGradient s) 0 1 =
        ‖w.covector t‖⁻¹ * (‖w.amplitude t‖⁻¹ *
          ⟪w.covector t, stationaryShearGradient s (w.amplitude t)⟫_ℝ) := by
      simp only [entry, frame, Matrix.cons_val_zero, Matrix.cons_val_one, NormedSpace.normalize,
        map_smul, real_inner_smul_left, real_inner_smul_right]
      ring
    rw [he] at h
    have h2 := mul_le_mul_of_nonneg_left h (mul_pos hk ha).le
    calc D⁻¹ * (‖w.covector t‖ * ‖w.amplitude t‖) = (‖w.covector t‖ * ‖w.amplitude t‖) * D⁻¹ := by ring
      _ ≤ (‖w.covector t‖ * ‖w.amplitude t‖) * (‖w.covector t‖⁻¹ * (‖w.amplitude t‖⁻¹ *
          ⟪w.covector t, stationaryShearGradient s (w.amplitude t)⟫_ℝ)) := h2
      _ = ⟪w.covector t, stationaryShearGradient s (w.amplitude t)⟫_ℝ := by field_simp


/-- The central gradient of the first child (item 6 of the proof, sections/08b_induction.tex:473-479): from (5.50) for `V`, the
second-order tail of the cutoff child, and `child = V + tail`, the gradient of the child at the
origin is `∇U + 𝐚 ⊗ κ + E` with `|E| ≤ λ_1^{-1/4}`
(`induction_child_center_split`, as `FirstWaveOrigin.child_T4_center` does for the library hierarchy). -/
theorem base_gradient_split {U V C Sv : Velocity} {κ a : ℝ → Vec3} {T freq next : ℝ}
    (hv : C = Sv)
    (hVslice : ∀ r ∈ Icc 0 T, DifferentiableAt ℝ (V r) 0)
    (hTailReg : ∀ r ∈ Icc 0 T, SpatialHolderHalf 2 (Sv r - V r))
    (hTailSize : ∀ r ∈ Icc 0 T, spatialHolderHalfNorm 2 (Sv r - V r) ≤ next ^ (-5 : ℝ))
    (h550 : ∀ r ∈ Icc 0 T, ‖fderiv ℝ (V r) 0 - fderiv ℝ (U r) 0 -
      (1 : ℝ) • InnerProductSpace.rankOne ℝ (a r) (κ r)‖ ≤ freq ^ (-1 / 3 : ℝ))
    (hfreq : (2 : ℝ) ^ (12 : ℕ) ≤ freq) (hnext : freq ≤ next) :
    ∀ r ∈ Icc 0 T, fderiv ℝ (C r) 0 = fderiv ℝ (U r) 0 +
        (1 : ℝ) • InnerProductSpace.rankOne ℝ (a r) (κ r) +
        ((fderiv ℝ (V r) 0 - fderiv ℝ (U r) 0 - (1 : ℝ) • InnerProductSpace.rankOne ℝ (a r) (κ r)) +
          fderiv ℝ (Sv r - V r) 0) ∧
      ‖(fderiv ℝ (V r) 0 - fderiv ℝ (U r) 0 - (1 : ℝ) • InnerProductSpace.rankOne ℝ (a r) (κ r)) +
          fderiv ℝ (Sv r - V r) 0‖ ≤ freq ^ (-1 / 4 : ℝ) := by
  intro r hr
  have hTailDiff : DifferentiableAt ℝ (Sv r - V r) 0 := ((hTailReg r hr).1.differentiable (by norm_num)) 0
  have hTailJet := norm_iteratedFDeriv_le_spatialHolderHalfNorm (hTailReg r hr) (by decide : 1 ≤ 2) 0
  rw [norm_iteratedFDeriv_one] at hTailJet
  exact induction_child_center_split (V := V) (parent := U) (child := C) (tail := fun r => Sv r - V r)
    (chi := fun _ => (1 : ℝ)) (a := a) (k := κ) (start := 0) (finish := T)
    (E := fun r => fderiv ℝ (V r) 0 - fderiv ℝ (U r) 0 - (1 : ℝ) • InnerProductSpace.rankOne ℝ (a r) (κ r))
    hr hfreq hnext (by
      rw [hv]
      funext x
      show Sv r x = V r x + (Sv r x - V r x)
      abel)
    (hVslice r hr) hTailDiff (fun r _ => by abel) (h550 r hr)
    (hTailJet.trans (hTailSize r hr))

set_option maxHeartbeats 6400000 in
/-- **The base of the induction from Section 5** (the base, sections/08b_induction.tex:252-256, and item 2 for `j = 1`, :285-291, of the proof of Theorem 7.1;
the central gradient is item 6, :473-479): the stationary base, the first child and the first wave carry
the local data of `Theorem71StepData` (step `j = 1`), the base velocity is the shear (6.1) at the
scheduled tilt and the first cutoff is `1`. Uses `h6_1` (first wave, (5.5), strength),
`h5_4`, `h5_8`-`h5_11` (through `exists_child_of_section5`). -/
theorem exists_base_of_section5 {P : InductiveEulerParameters} (hLife : P.LifetimeBounds)
    (h6_1 : Statement.lemma_6_1)
    {ψ : Vec3 → ℝ} {a : ℕ} {Γ : ℕ → ℝ} {K58 : ℕ → ℕ → ℝ} {C11 Cc : ℝ} {K11 Ct Cj : ℕ → ℝ}
    {Cstep Cmean : ℝ}
    (h54 : Body54 a) (h58 : Body58 a P.exponentParameter Γ K58)
    (h59 : Body59 a P.exponentParameter Γ) (h510 : Body510 a P.exponentParameter Γ)
    (h511 : Body511 ψ a P.exponentParameter Γ C11 K11)
    (hTail : TailBounds ψ Ct)
    (hParent : ∀ {m : ℕ} {act T : ℝ} (s : InductiveEulerStage P m act), 0 < T →
      T ≤ P.slab m act → T ≤ 1 →
      S5.Parent T s.velocity s.flow s.pressure (P.frequency m ^ 9) (P.frequency (m + 1)))
    (hJets : ∀ {m : ℕ} {act : ℝ} (s : InductiveEulerStage P m act), 1 ≤ P.frequency m → ∀ N : ℕ,
      ∀ t ∈ Icc 0 (P.slab m act),
        PhaseJetBound (N + 1) (Cj N * P.frequency m ^ (5 * (N + 1) + 1)) (s.velocity t))
    (ha : 3 ≤ a) (hN : (64 * Real.pi) ^ (16 : ℕ) ≤ P.frequency 0) (hExp : Real.exp 1 ≤ P.frequency 0)
    (hC11 : C11 ≤ Cc)
    (hNum : StepNumbers P 0 Γ K58 Cc K11 Ct
      (Cj (6 * frequencyExponent P.exponentParameter (P.order 2))) Cstep Cmean) :
    ∃ b : InductiveEulerBase P, LocalStep b.stationary b.first b.wave a ψ ∧
      b.stationary.velocity =
        (fun _ => stationaryShear (couplingRatioOfGain (4 * Real.log (P.frequency 3)))) ∧
      b.wave.cutoff = fun _ => 1 := by
  classical
  have hπ : 3 < Real.pi := Real.pi_gt_three
  have h64 : 1 ≤ 64 * Real.pi := by linarith
  have hBase : 1 + 4 * Real.pi ≤ P.frequency 0 :=
    (by linarith : 1 + 4 * Real.pi ≤ 64 * Real.pi).trans
      ((le_self_pow₀ h64 (by norm_num : (16 : ℕ) ≠ 0)).trans hN)
  have hInitial : 2 ≤ P.frequency 0 := by linarith
  have hMono := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge (by linarith) P.frequency_step
  have hGain : 1 ≤ 4 * Real.log (P.frequency 3) := by
    have hg := Real.log_le_log (Real.exp_pos 1) (hExp.trans (hMono (Nat.zero_le 3)))
    rw [Real.log_exp] at hg
    linarith
  have hTilt : |couplingRatioOfGain (4 * Real.log (P.frequency 3))| ≤ 1 := by
    rw [couplingRatioOfGain, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    exact (inv_le_one₀ (sq_pos_of_pos (zero_lt_one.trans_le hGain))).2 (one_le_pow₀ hGain)
  have hTiltPos : 0 < couplingRatioOfGain (4 * Real.log (P.frequency 3)) :=
    inv_pos.mpr (sq_pos_of_pos (zero_lt_one.trans_le hGain))
  have hTime : P.slab 1 0 = 2 * inductionHalfLength P.frequency 0 := by
    rw [P.slab_succ, zero_add]
  have hT : 0 < P.slab 1 0 := by
    rw [hTime]
    exact mul_pos zero_lt_two (hLife.step 0).1
  have hT₁ : P.slab 1 0 ≤ 1 := by
    rw [hTime]
    linarith only [hLife.first]
  have hSmall := firstWave_stationaryShear_window_small hTilt hT.le hTime.le (hLife.step 0).2.1 hN
  have hf1 : 1 ≤ P.frequency 1 := (by linarith : (1 : ℝ) ≤ P.frequency 0).trans (hMono (Nat.zero_le 1))
  have hfpos : 0 < P.frequency 1 := zero_lt_one.trans_le hf1
  let parent : InductiveEulerStage P 0 0 := stationaryInductiveEulerStage P hTilt hBase
  have hPv : parent.velocity = fun _ => stationaryShear (couplingRatioOfGain (4 * Real.log (P.frequency 3))) :=
    funext fun t => funext fun x => stationaryInductiveEulerStage_velocity P hTilt hBase t x
  obtain ⟨⟨w⟩, hall⟩ := h6_1 (couplingRatioOfGain (4 * Real.log (P.frequency 3))) (P.slab 1 0)
    (P.frequency 1) hTiltPos (abs_le.mp hTilt).2 hf1 hT hSmall
  have hc := hall w
  have hpar := hParent parent hT (by rw [P.slab_zero]; exact hT₁) hT₁
  have ht₀ : (0 : ℝ) ∈ Icc 0 (P.slab 1 0) := ⟨le_rfl, hT.le⟩
  have hκ : ∀ t ∈ Icc 0 (P.slab 1 0), HasDerivWithinAt w.covector
      (-((fderiv ℝ (parent.velocity t) (0 : Vec3)).adjoint (w.covector t))) (Icc 0 (P.slab 1 0)) t := by
    intro t ht
    have := w.covector_equation t ht
    simpa only [hPv, stationaryShearGradient_origin] using this
  obtain ⟨hkne, hkv⟩ := Bridge.waveVector_origin_eq_of_covector (X := parent.flow) hT hpar ht₀ hκ
  have hk : (fderiv ℝ (parent.flow 0 0) (0 : Vec3)).adjoint (w.covector 0) ≠ 0 :=
    hkne (w.transverse 0 ht₀).1
  have hl : S5.Launch (P.slab 1 0) parent.flow ((fderiv ℝ (parent.flow 0 0) (0 : Vec3)).adjoint (w.covector 0))
      (P.frequency 1) 0 :=
    Bridge.launch_of_carrier le_rfl hT hk (by
      rw [hkv 0 ht₀, w.covector_initial]
      simp [EuclideanSpace.single, norm_smul, PiLp.norm_single, abs_of_pos hfpos])
  have hcw : CenterWaveOn (fun _ => fderiv ℝ (stationaryShear (couplingRatioOfGain
      (4 * Real.log (P.frequency 3)))) 0) w.covector w.amplitude 0 (P.slab 1 0) (P.frequency 0 ^ 9) :=
    (centerWaveOn_of_lemma61 w hc hfpos (by
      have : (2 : ℝ) ≤ P.frequency 0 ^ 9 :=
        hInitial.trans (le_self_pow₀ (one_le_two.trans hInitial) (by norm_num))
      exact this)).congr_gradient (fun _ _ => (stationaryShearGradient_origin _).symm)
  have hcwU : CenterWaveOn (fun t => fderiv ℝ (parent.velocity t) 0) w.covector w.amplitude 0
      (P.slab 1 0) (P.frequency 0 ^ 9) := by
    rw [hPv]
    exact hcw
  have hnorm : ∀ t ∈ Icc 0 (P.slab 1 0), P.frequency 1 ^ (3 / 4 : ℝ) * ‖w.amplitude t‖ ≤ 1 := by
    intro t ht
    calc P.frequency 1 ^ (3 / 4 : ℝ) * ‖w.amplitude t‖
        ≤ P.frequency 1 ^ (3 / 4 : ℝ) * P.frequency 1 ^ (-(3 / 4) : ℝ) :=
          mul_le_mul_of_nonneg_left (w.norm_le_peak t ht) (Real.rpow_nonneg hfpos.le _)
      _ = 1 := by
        rw [← Real.rpow_add hfpos]
        norm_num
  have ho : S5.Origin (P.slab 1 0) parent.velocity parent.flow
      ((fderiv ℝ (parent.flow 0 0) (0 : Vec3)).adjoint (w.covector 0)) (P.frequency 0 ^ 9)
      (P.frequency 1) 0 w.amplitude :=
    Bridge.origin_of_centerWaveOn hpar hl hcwU (fun t ht => hkv t ht) hnorm
  obtain ⟨dg, -⟩ := Bridge.exists_truncatedHierarchyParent hT hpar hk
  let χ : PaperWaveCutoff 0 (P.slab 1 0) := PaperWaveCutoff.first (P.slab 1 0)
  obtain ⟨hμ2, -, hDepth⟩ := physicalWave_schedule (P := P) (n := 0) hInitial
  have hdep2 : 2 ≤ 6 * frequencyExponent P.exponentParameter (P.order 2) :=
    (le_max_left _ _).trans hDepth
  obtain ⟨⟨amp, hamp⟩, h4a⟩ := h54 hT dg χ hpar hl ho
  obtain ⟨⟨R, S, u, hu⟩, -, hid⟩ := h4a amp hamp
    (6 * frequencyExponent P.exponentParameter (P.order 2)) hdep2
  obtain ⟨-, -, -, hsum, hsupp, -, hvan, -⟩ := hid R S u hu
  have hds : χ.derivativeSize (S5.weight (P.frequency 1) w.amplitude) = 0 := by
    have : Nonempty (Icc (0 : ℝ) (P.slab 1 0)) := ⟨⟨0, ht₀⟩⟩
    unfold PaperWaveCutoff.derivativeSize
    simp [χ, PaperWaveCutoff.derivative_first]
  have hRVn := hNum.residual (χ.derivativeSize (S5.weight (P.frequency 1) w.amplitude)) (by
    rw [hds]
    have h0 : 0 ≤ P.frequency 0 := by linarith
    have h2 : 0 ≤ P.frequency 2 := by linarith [hMono (Nat.zero_le 2)]
    positivity)
  obtain ⟨s, child, hv, hp, hosc, hcorr, happ, htr, hT1, hT2, hT3, h550⟩ :=
    exists_child_of_section5 (parent := parent) h58 h59 h510 h511 hTail hT dg χ hpar hl ho
      hamp hu ha hInitial (by rw [P.slab_zero]; exact hT₁) hNum.flow_small hRVn hNum.ct_nonneg
      hNum.ct_le hC11 hNum.cc_nonneg hNum.k11_le hNum.large
      (fun t ht => hJets parent (by linarith) _ t ⟨ht.1, ht.2.trans hT₁⟩) hNum.jets_le
      hNum.parent_nonneg hNum.osc_le hNum.step0 hNum.stepΓ hNum.step32 hNum.mean_le hNum.mean_mu
  -- the oscillation and the center
  have hSupport : ∀ t ∈ Icc 0 (P.slab 1 0), ∀ x, graphRead (fun r => parent.flow r 0)
      (S5.expansion u (6 * frequencyExponent P.exponentParameter (P.order 2)) -
        (S5.ops dg).average (S5.expansion u (6 * frequencyExponent P.exponentParameter
          (P.order 2)))) t x ≠ 0 →
      ∃ z : Fin 3 → ℤ, dist (latticeVector z) x ≤ (P.frequency 0)⁻¹ := by
    have hD : 1 ≤ P.frequency 0 ^ 9 := one_le_pow₀ (by linarith)
    exact osc_support parent hT (by rw [P.slab_zero]; exact hT₁)
      (inv_pos.mpr (pow_pos (zero_lt_one.trans_le hD) a)) hμ2
      (inv_anti₀ (pow_pos (zero_lt_one.trans_le hD) 3) (pow_le_pow_right₀ hD ha)) _ hsupp
  have hExponent : 12 ≤ frequencyExponent P.exponentParameter (P.order 1) := by
    rw [P.initial_order]
    unfold frequencyExponent
    have h := Nat.mul_le_mul_left 320 P.exponentParameter_ge
    omega
  have hFreq : (2 : ℝ) ^ (12 : ℕ) ≤ P.frequency 1 := by
    rw [P.frequency_step 0]
    exact (pow_le_pow_left₀ zero_le_two hInitial _).trans
      (pow_le_pow_right₀ (one_le_two.trans hInitial) hExponent)
  have hnext : P.frequency 1 ≤ P.frequency 2 := hMono (by decide)
  have hVsm := happ.1.1
  have hVslice : ∀ r ∈ Icc 0 (P.slab 1 0), DifferentiableAt ℝ
      ((parent.velocity + graphRead (fun t => parent.flow t 0)
        (S5.expansion u (6 * frequencyExponent P.exponentParameter (P.order 2)))) r) 0 := by
    intro r hr
    have hs := hVsm.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x (_ : x ∈ (univ : Set Vec3)) => mem_prod.mpr ⟨hr, mem_univ x⟩)
    exact ((contDiffOn_univ.mp hs).differentiable (by simp)) 0
  have hgs := base_gradient_split (U := parent.velocity) (C := child.velocity) (Sv := s.velocity)
    (V := parent.velocity + graphRead (fun t => parent.flow t 0)
      (S5.expansion u (6 * frequencyExponent P.exponentParameter (P.order 2))))
    (κ := w.covector) (a := w.amplitude) (T := P.slab 1 0) (freq := P.frequency 1)
    (next := P.frequency 2) hv hVslice (fun r hr => (hT1 2 hdep2 r hr).1)
    (fun r hr => (hT2 r hr).trans (hT3 r hr))
    (fun r hr => by
      have h := h550 r hr
      rw [hkv r hr] at h
      exact h) hFreq hnext
  have hν : entry (frame w.covector w.amplitude 0) (fderiv ℝ (parent.velocity 0) 0) 0 1 = 2 * Real.pi := by
    rw [hPv, stationaryShearGradient_origin]
    exact (w.initial_couplings hfpos).1
  have hη : entry (frame w.covector w.amplitude 0) (fderiv ℝ (parent.velocity 0) 0) 2 1 =
      2 * Real.pi * couplingRatioOfGain (4 * Real.log (P.frequency 3)) := by
    rw [hPv, stationaryShearGradient_origin]
    exact (w.initial_couplings hfpos).2
  have hStr := hc.initial_strength
  have hL1 : (1 : ℝ) ≤ (4 * Real.log (P.frequency 3)) ^ 2 := one_le_pow₀ hGain
  have hf14 : 0 ≤ P.frequency 1 ^ (1 / 4 : ℝ) := Real.rpow_nonneg hfpos.le _
  have hC2 := P.strengthConstant_ge
  have hS1 : P.strengthConstant⁻¹ * P.frequency 1 ^ (1 / 4 : ℝ) ≤ ‖w.covector 0‖ * ‖w.amplitude 0‖ := by
    have hh : P.strengthConstant⁻¹ ≤ 1 / 2 := by
      rw [one_div]
      exact inv_anti₀ (by norm_num) hC2
    calc P.strengthConstant⁻¹ * P.frequency 1 ^ (1 / 4 : ℝ)
        ≤ (1 / 2) * P.frequency 1 ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_right hh hf14
      _ = P.frequency 1 ^ (1 / 4 : ℝ) / 2 := by ring
      _ ≤ ‖w.amplitude 0‖ * ‖w.covector 0‖ := hStr.1
      _ = ‖w.covector 0‖ * ‖w.amplitude 0‖ := mul_comm _ _
  have hS2 : ‖w.covector 0‖ * ‖w.amplitude 0‖ ≤ P.strengthConstant * P.frequency 1 ^ (1 / 4 : ℝ) *
      (4 * Real.log (P.frequency 3)) ^ 2 := by
    have h1 : (1 : ℝ) ≤ P.strengthConstant * (4 * Real.log (P.frequency 3)) ^ 2 :=
      one_le_mul_of_one_le_of_one_le (by linarith) hL1
    calc ‖w.covector 0‖ * ‖w.amplitude 0‖ = ‖w.amplitude 0‖ * ‖w.covector 0‖ := mul_comm _ _
      _ ≤ P.frequency 1 ^ (1 / 4 : ℝ) := hStr.2
      _ = 1 * P.frequency 1 ^ (1 / 4 : ℝ) := (one_mul _).symm
      _ ≤ (P.strengthConstant * (4 * Real.log (P.frequency 3)) ^ 2) * P.frequency 1 ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right h1 hf14
      _ = _ := by ring
  refine ⟨{
    stationary := parent
    first := child
    wave := {
      oscillation := graphRead (fun r => parent.flow r 0)
        (S5.expansion u (6 * frequencyExponent P.exponentParameter (P.order 2)) -
          (S5.ops dg).average (S5.expansion u (6 * frequencyExponent P.exponentParameter
            (P.order 2))))
      waveVector := w.covector
      amplitude := w.amplitude
      cutoff := fun _ => 1
      error := fun r => (fderiv ℝ ((parent.velocity + graphRead (fun t => parent.flow t 0)
            (S5.expansion u (6 * frequencyExponent P.exponentParameter (P.order 2)))) r) 0 -
          fderiv ℝ (parent.velocity r) 0 -
          (1 : ℝ) • InnerProductSpace.rankOne ℝ (w.amplitude r) (w.covector r)) +
          fderiv ℝ (s.velocity r - (parent.velocity + graphRead (fun t => parent.flow t 0)
            (S5.expansion u (6 * frequencyExponent P.exponentParameter (P.order 2)))) r) 0
      center := hcwU
      activation_step := ⟨by norm_num, by
        have := (hLife.step 0).1.le
        norm_num
        exact this⟩
      oscillation_bound := hosc
      correction_bound := hcorr
      oscillation_vanishes := fun hnone => absurd hnone (by omega)
      oscillation_support := hSupport
      gradient_split := fun r hr => by
        have := (hgs r hr).1
        simpa only [InnerProductSpace.rankOne_def, one_smul] using this
      error_bound := fun r hr => (hgs r hr).2
      cutoff_complete := fun _ _ => rfl
      strength_at_crossing := ⟨hS1, hS2⟩
      coupling_at_crossing := by
        dsimp only
        rw [hν]
        exact ⟨by linarith, by linarith⟩
      ratio_at_crossing := by
        dsimp only
        rw [hν, hη, mul_div_cancel_left₀ _ (by positivity)] }
    initial_coupling := hν }, ?_, hPv, rfl⟩
  exact ⟨hT, _, w.amplitude, amp, dg, χ, R, S, u, hpar, hl, ho, fun r _ => rfl, hamp,
    fun r _ => rfl, hu, happ, htr, fun r _ => rfl⟩

end

end TorusEuler.Paper.Lib.S678a
