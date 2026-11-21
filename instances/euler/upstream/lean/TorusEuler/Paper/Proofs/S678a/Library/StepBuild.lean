import TorusEuler.Paper.Proofs.S678a.Library.StepChild
import TorusEuler.Paper.Proofs.S678a.Library.StepOsc
import TorusEuler.Paper.Proofs.S678a.Library.StepNumbers
import TorusEuler.Paper.Proofs.S678a.Library.StepCutoff
import TorusEuler.Paper.Proofs.S5Bridge.Construction
import TorusEuler.Paper.Proofs.S5Bridge.Parent
import TorusEuler.Paper.Proofs.S678a.Library.WaveSelection
import TorusEuler.InductiveLaterWaveSelection

/-! # One step of the construction of Theorem 7.1 (package S678a)

Items 2 and 4 of the proof (sections/08b_induction.tex:284-328 and :376-461): for a certified
prefix `tip`, the later wave `d` selected over the actual parent (item 2) is launched at `t_j`
with the carrier `k_*` of its seed; the parent, launch and origin hypotheses of Subsection 5.1
hold (`hParent`, the center data of `d`), the seed and the expansion exist (Proposition 5.4), the
cutoff of the expansion is `waveSwitch t_j r_j`, and the conversion `exists_child_of_section5`
(Lemmas 5.8-5.10, Proposition 5.11) gives the child; the step is built with
`InductiveEulerStep.ofPhysicalHierarchyCutoff'`. -/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler HierarchyTwistedProfile MovingWaveVector MovingWaveVector.PhysicalAmplification

noncomputable section

set_option maxHeartbeats 6400000 in
/-- **One step of the induction from Section 5** (items 2 and 4 of the proof of Theorem 7.1): for
the selected wave `d` over a certified prefix, there is a step of the construction whose
parent, child and wave carry the local data of `Theorem71StepData`. Uses `h5_4` (seed, expansion,
vanishing and support, through `h54`), `h5_8`-`h5_11` (through `exists_child_of_section5`) and
the parent hypotheses of Subsection 5.1 (`hParent`). -/
theorem exists_step_of_section5
    {P : InductiveEulerParameters} {hLife : P.LifetimeBounds} {n : ℕ} {tip : InductiveEulerTip P n}
    (pre : InductiveEulerPrefix P hLife n tip)
    (w : tip.LaterWindow) (d : tip.LaterSelection w)
    {ψ : Vec3 → ℝ} {a : ℕ} {Γ : ℕ → ℝ} {K58 : ℕ → ℕ → ℝ} {C11 Cc : ℝ} {K11 Ct : ℕ → ℝ}
    {Cparent Cstep Cmean : ℝ}
    (h54 : Body54 a) (h58 : Body58 a P.exponentParameter Γ K58)
    (h59 : Body59 a P.exponentParameter Γ) (h510 : Body510 a P.exponentParameter Γ)
    (h511 : Body511 ψ a P.exponentParameter Γ C11 K11)
    (hTail : TailBounds ψ Ct)
    (hParent : ∀ {m : ℕ} {act T : ℝ} (s : InductiveEulerStage P m act), 0 < T →
      T ≤ P.slab m act → T ≤ 1 →
      S5.Parent T s.velocity s.flow s.pressure (P.frequency m ^ 9) (P.frequency (m + 1)))
    (ha : 3 ≤ a) (hLarge : Real.exp 4 ≤ P.frequency 0) (hConst : 18 * Real.exp 3 ≤ P.strengthConstant)
    (hC11 : C11 ≤ Cc)
    (hNum : StepNumbers P (n + 1) Γ K58 Cc K11 Ct Cparent Cstep Cmean)
    (hJets : ∀ t ∈ Icc 0 (P.slab (n + 1 + 1) tip.nextActivation),
      PhaseJetBound (6 * frequencyExponent P.exponentParameter (P.order (n + 1 + 2)) + 1)
        (Cparent * P.frequency (n + 1) ^ (5 * (6 * frequencyExponent P.exponentParameter
          (P.order (n + 1 + 2)) + 1) + 1)) (tip.parent.velocity t))
    (hSwitch : ∀ t, |deriv (waveSwitch tip.nextActivation w.physical.rate) t| *
      |S5.weight (P.frequency (n + 1 + 1)) d.crossing.amplitude t| ≤
        P.frequency (n + 1) * P.frequency (n + 1 + 2) ^ (-4 : ℝ)) :
    ∃ step : InductiveEulerStep tip, LocalStep tip.parent step.child step.wave a ψ ∧
      step.wave.cutoff = waveSwitch tip.nextActivation step.physical.rate := by
  classical
  have h2e : (2 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hInitial : 2 ≤ P.frequency 0 := h2e.trans hLarge
  have hMono := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge (one_le_two.trans hInitial) P.frequency_step
  obtain ⟨hμ2, -, hDepth⟩ := physicalWave_schedule (P := P) (n := n + 1) hInitial
  have hdep2 : 2 ≤ 6 * frequencyExponent P.exponentParameter (P.order (n + 1 + 2)) :=
    (le_max_left _ _).trans hDepth
  have hT : 0 < P.slab (n + 1 + 1) tip.nextActivation := tip.next_slab_pos hLife
  have hTold : P.slab (n + 1 + 1) tip.nextActivation ≤ P.slab (n + 1) tip.activation :=
    (tip.next_slab_lt hLife).le
  have hT₁ : P.slab (n + 1 + 1) tip.nextActivation ≤ 1 := hTold.trans pre.tip_parent_slab_le_one
  have ht₀ : 0 ≤ tip.nextActivation := tip.next_activation_nonnegative
  have ht₀T : tip.nextActivation < P.slab (n + 1 + 1) tip.nextActivation := by
    change tip.nextActivation < tip.nextActivation + 2 * inductionHalfLength P.frequency (n + 1)
    linarith only [(hLife.step (n + 1)).1]
  have hpar := hParent tip.parent hT hTold hT₁
  have hsub : Icc 0 (P.slab (n + 1 + 1) tip.nextActivation) ⊆ Icc 0 (P.slab (n + 1) tip.activation) :=
    Icc_subset_Icc_right hTold
  have hX : IsLabelFlowOn tip.parent.velocity tip.parent.flow (Icc 0 (P.slab (n + 1 + 1) tip.nextActivation)) :=
    tip.parent.deformation.flow.mono hsub
  have hU : ContDiffOn ℝ ∞ (Function.uncurry tip.parent.velocity)
      (Icc 0 (P.slab (n + 1 + 1) tip.nextActivation) ×ˢ (univ : Set Vec3)) :=
    tip.parent.smooth_velocity.mono (prod_mono_left hsub)
  have hper (t : ℝ) (_ : t ∈ Icc 0 (P.slab (n + 1 + 1) tip.nextActivation)) :
      SpatiallyPeriodic (tip.parent.velocity t) := tip.parent.periodic_velocity t
  have hodd (t : ℝ) (ht : t ∈ Icc 0 (P.slab (n + 1 + 1) tip.nextActivation)) :
      Function.Odd (tip.parent.velocity t) := tip.parent.odd_velocity t (hsub ht)
  have hfp : 0 < P.frequency (n + 1 + 1) :=
    zero_lt_one.trans_le ((one_le_two.trans hInitial).trans (hMono (Nat.zero_le _)))
  have hLaunch := d.crossing.launch_geometry hfp
  have hKexpr : tip.laterCarrier d = P.frequency (n + 1 + 1) •
      (fderiv ℝ (tip.parent.flow 0 tip.nextActivation) (0 : Vec3)).adjoint
        (w.physical.basis tip.nextActivation 2) := by
    simp only [InductiveEulerTip.laterCarrier, hLaunch.1, map_smul]
  have hTransport := d.crossing.transport_launch_covector hX hT (hU.of_le (by simp)) hper hodd
    ⟨ht₀, ht₀T.le⟩ d.clock_eq w.parent_gradient_eq
  dsimp only at hTransport
  rw [← hKexpr] at hTransport
  obtain ⟨hk, hTr⟩ := hTransport
  have hl : S5.Launch (P.slab (n + 1 + 1) tip.nextActivation) tip.parent.flow (tip.laterCarrier d)
      (P.frequency (n + 1 + 1)) tip.nextActivation :=
    Bridge.launch_of_carrier ht₀ ht₀T hk (by
      show ‖labelWaveVector tip.parent.flow 0 0 (tip.laterCarrier d) tip.nextActivation‖ = _
      rw [hTr ⟨le_rfl, ht₀T.le⟩]
      exact hLaunch.2.1)
  have hActive : w.physical.activeSlab d.window = Icc tip.nextActivation
      (P.slab (n + 1 + 1) tip.nextActivation) := by
    unfold PhysicalAmplification.activeSlab
    rw [d.clock_eq]
  have hnorm : ∀ t ∈ Icc tip.nextActivation (P.slab (n + 1 + 1) tip.nextActivation),
      P.frequency (n + 1 + 1) ^ (3 / 4 : ℝ) * ‖d.crossing.amplitude t‖ ≤ 1 := by
    intro t ht
    have hp := d.crossing.peak.2 (mem_image_of_mem _ (hActive ▸ ht))
    calc P.frequency (n + 1 + 1) ^ (3 / 4 : ℝ) * ‖d.crossing.amplitude t‖
        ≤ P.frequency (n + 1 + 1) ^ (3 / 4 : ℝ) * P.frequency (n + 1 + 1) ^ (-3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hfp.le _)
      _ = 1 := by
        rw [← Real.rpow_add hfp]
        norm_num
  have ho : S5.Origin (P.slab (n + 1 + 1) tip.nextActivation) tip.parent.velocity tip.parent.flow
      (tip.laterCarrier d) (P.frequency (n + 1) ^ 9) (P.frequency (n + 1 + 1)) tip.nextActivation
      d.crossing.amplitude :=
    Bridge.origin_of_centerWaveOn hpar hl d.center (fun t ht => hTr ht) hnorm
  obtain ⟨dg, -⟩ := Bridge.exists_truncatedHierarchyParent hT hpar hk
  have hrate : 0 < w.physical.rate := w.physical.rate_pos
  let χ : PaperWaveCutoff tip.nextActivation (P.slab (n + 1 + 1) tip.nextActivation) :=
    paperCutoffOfWaveSwitch tip.nextActivation w.physical.rate _ hrate.le
  have hχ : χ.value tip.nextActivation = 0 := waveSwitch_eq_zero_of_le hrate.le le_rfl
  obtain ⟨⟨amp, hamp⟩, h4a⟩ := h54 hT dg χ hpar hl ho
  obtain ⟨⟨R, S, u, hu⟩, -, hid⟩ := h4a amp hamp
    (6 * frequencyExponent P.exponentParameter (P.order (n + 1 + 2))) hdep2
  obtain ⟨-, -, -, hsum, hsupp, -, hvan, -⟩ := hid R S u hu
  -- the derivative of the cutoff
  have hdS : χ.derivativeSize (S5.weight (P.frequency (n + 1 + 1)) d.crossing.amplitude) ≤
      P.frequency (n + 1) * P.frequency (n + 1 + 2) ^ (-4 : ℝ) :=
    derivativeSize_paperCutoffOfWaveSwitch_le hrate.le hT ht₀ ht₀T.le _
      (fun t _ => mul_nonneg (Real.rpow_nonneg hfp.le _) (norm_nonneg _)) hSwitch
  have hRVn := hNum.residual _ hdS
  -- the child
  obtain ⟨s, child, hv, hp, hosc, hcorr, happ, htr, hT1, hT2, hT3, h550⟩ :=
    exists_child_of_section5 (parent := tip.parent) h58 h59 h510 h511 hTail hT dg χ hpar hl ho
      hamp hu ha hInitial hTold hNum.flow_small hRVn hNum.ct_nonneg hNum.ct_le hC11 hNum.cc_nonneg
      hNum.k11_le hNum.large hJets hNum.jets_le hNum.parent_nonneg hNum.osc_le hNum.step0
      hNum.stepΓ hNum.step32 hNum.mean_le hNum.mean_mu
  -- vanishing and support of the oscillation
  have hVanish : ∀ t ∈ Icc 0 tip.nextActivation, graphRead (fun r => tip.parent.flow r 0)
      (S5.expansion u (6 * frequencyExponent P.exponentParameter (P.order (n + 1 + 2))) -
        (S5.ops dg).average (S5.expansion u (6 * frequencyExponent P.exponentParameter
          (P.order (n + 1 + 2))))) t = 0 := by
    intro t ht
    have hz := osc_profile_vanishes (d := dg) (χ := χ) ht₀ ht₀T.le hχ hu hsum
      (fun i hi t ht hlt x s => ((hvan t ht hlt x s).1 i hi).1) t ht
    funext x
    exact hz _ _
  have hSupport : ∀ t ∈ Icc 0 (P.slab (n + 1 + 1) tip.nextActivation), ∀ x,
      graphRead (fun r => tip.parent.flow r 0)
        (S5.expansion u (6 * frequencyExponent P.exponentParameter (P.order (n + 1 + 2))) -
          (S5.ops dg).average (S5.expansion u (6 * frequencyExponent P.exponentParameter
            (P.order (n + 1 + 2))))) t x ≠ 0 →
      ∃ z : Fin 3 → ℤ, dist (latticeVector z) x ≤ (P.frequency (n + 1))⁻¹ := by
    have hD : 1 ≤ P.frequency (n + 1) ^ 9 :=
      one_le_pow₀ (one_le_two.trans (hμ2))
    exact osc_support tip.parent hT hTold
      (inv_pos.mpr (pow_pos (zero_lt_one.trans_le hD) a)) hμ2
      (inv_anti₀ (pow_pos (zero_lt_one.trans_le hD) 3) (pow_le_pow_right₀ hD ha)) _ hsupp
  have hApprox : ∀ t ∈ Icc tip.nextActivation (P.slab (n + 1 + 1) tip.nextActivation),
      fderiv ℝ ((tip.parent.velocity + graphRead (fun r => tip.parent.flow r 0)
        (S5.expansion u (6 * frequencyExponent P.exponentParameter (P.order (n + 1 + 2))))) t) 0 =
        fderiv ℝ (tip.parent.velocity t) 0 +
          waveSwitch tip.nextActivation w.physical.rate t •
            InnerProductSpace.rankOne ℝ (d.crossing.amplitude t) (d.crossing.waveVector t) +
          (fderiv ℝ ((tip.parent.velocity + graphRead (fun r => tip.parent.flow r 0)
            (S5.expansion u (6 * frequencyExponent P.exponentParameter (P.order (n + 1 + 2))))) t) 0 -
            fderiv ℝ (tip.parent.velocity t) 0 -
            waveSwitch tip.nextActivation w.physical.rate t •
              InnerProductSpace.rankOne ℝ (d.crossing.amplitude t) (d.crossing.waveVector t)) ∧
        ‖fderiv ℝ ((tip.parent.velocity + graphRead (fun r => tip.parent.flow r 0)
            (S5.expansion u (6 * frequencyExponent P.exponentParameter (P.order (n + 1 + 2))))) t) 0 -
            fderiv ℝ (tip.parent.velocity t) 0 -
            waveSwitch tip.nextActivation w.physical.rate t •
              InnerProductSpace.rankOne ℝ (d.crossing.amplitude t) (d.crossing.waveVector t)‖ ≤
          P.frequency (n + 1 + 1) ^ (-1 / 3 : ℝ) := by
    intro t ht
    refine ⟨by abel, ?_⟩
    have h := h550 t ht
    have hw : S5.waveVector tip.parent.flow (tip.laterCarrier d) t 0 = d.crossing.waveVector t :=
      hTr ht
    rw [hw] at h
    exact h
  refine ⟨InductiveEulerStep.ofPhysicalHierarchyCutoff' pre w d s child hv hLarge hConst hosc hcorr
    (fun t ht => hVanish t ht) hSupport hT1 hT2 hdep2 hT3 happ.1.1 hApprox, ?_, rfl⟩
  exact ⟨hT, tip.laterCarrier d, d.crossing.amplitude, amp, dg, χ, R, S, u, hpar, hl, ho,
      fun r _ => rfl, hamp, fun r _ => rfl, hu, happ, htr, fun r _ => rfl⟩

end

end TorusEuler.Paper.Lib.S678a
