import TorusEuler.Paper.Proofs.S678a.Library.Bernstein
import TorusEuler.HierarchyPhysicalVelocityBounds
import TorusEuler.InductionChildEstimates
import TorusEuler.PhysicalHierarchyProfileBounds

/-! # Approximation bounds of the step from Lemma 5.8 (package S678a)

Own glue of row 7.1 (items 4-5 of the proof, sections/08b_induction.tex:376-381, :415-421): the
fields of the library `PhysicalWaveApproximationBounds` (without its pressure bound, see `StepApproxBounds`) that the step reads from the conclusions of
Lemma 5.8 (5.47, 5.48): the full-depth velocity size, the oscillation and the mean, and
NOT the pressure: the Hessian bound of the child pressure is read from (5.57) of Proposition 5.11
(`scheduled_bounds_of_5_11`). The residual size (7.11) (which needs (7.10), from (6.8)) is a separate field supplied by the caller. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler

noncomputable section

/-- Copy of the private `velocityDepth_from_holder` (`HierarchyPhysicalVelocityBounds.lean:656`):
the arithmetic of (7.8) at the full depth: `V = U + O + M` with the parent bound
`C_p μ^{5(P+1)+1}`, the oscillation bound (5.48) and the mean bound (5.48) at the scale
`D = μ^9`, `λ = μ^K`, gives `1 + ‖V‖_{P,1/2} ≤ 3 λ^{2(P+1)}`. Same proof (pure arithmetic of the
schedule; it reaches no content lemma). -/
theorem velocityDepth_from_holder {U V O M : Vec3 → Vec3}
    {μ Cparent Cosc Cmean : ℝ} {P b q : ℕ}
    (hμ : 2 ≤ μ) (hb : 1 ≤ b)
    (hCp : Cparent ≤ μ) (hCo : Cosc ≤ μ) (hCm : Cmean ≤ μ)
    (hSplit : V = U + O + M)
    (hU : SpatialHolderHalf P U) (hO : SpatialHolderHalf P O) (hM : SpatialHolderHalf P M)
    (hParent : spatialHolderHalfNorm P U ≤ Cparent * μ ^ (5 * (P + 1) + 1))
    (hOsc : spatialHolderHalfNorm P O ≤
      Cosc * (μ ^ 9) ^ (b * (P + 2)) *
        (μ ^ frequencyExponent b q) ^ ((3 : ℝ) * (P + 1) / 2 - 5 / 4))
    (hMean : spatialHolderHalfNorm P M ≤
      Cmean * (μ ^ 9) ^ (b * (P + 2)) * (μ ^ frequencyExponent b q) ^ (-5 / 2 : ℝ)) :
    1 + spatialHolderHalfNorm P V ≤ 3 * (μ ^ frequencyExponent b q) ^ (2 * (P + 1)) := by
  let freq := μ ^ frequencyExponent b q
  let E : ℝ := (3 : ℝ) * (P + 1) / 2 - 5 / 4 + ((P : ℝ) + 2) / 32
  have hμ1 : 1 ≤ μ := one_le_two.trans hμ
  have hExp : frequencyExponent b q ≠ 0 := by
    unfold frequencyExponent
    exact Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos (by decide) hb) (Nat.succ_pos _))
  have hf₂ : 2 ≤ freq := hμ.trans (le_self_pow₀ hμ1 hExp)
  have hf : 1 ≤ freq := one_le_two.trans hf₂
  have hfpos : 0 < freq := zero_lt_one.trans_le hf
  have hPar' : spatialHolderHalfNorm P U ≤ freq ^ (2 * (P + 1)) :=
    hParent.trans ((frequencySchedule_fullOrder_parent_budget hμ1 hCp hb).trans
      (pow_le_pow_right₀ hf (by omega)))
  have hO' : spatialHolderHalfNorm P O ≤ freq ^ E := by
    refine hOsc.trans ((mul_le_mul_of_nonneg_right
      (frequencySchedule_fullOrder_wave_budget (q := q) hμ1 hCo hb) (by positivity)).trans_eq ?_)
    change freq ^ (((P : ℝ) + 2) / 32) * freq ^ ((3 : ℝ) * (P + 1) / 2 - 5 / 4) = _
    rw [← Real.rpow_add hfpos]
    congr 1
    dsimp only [E]
    ring
  have hM' : spatialHolderHalfNorm P M ≤ freq ^ E := by
    refine hMean.trans ((mul_le_mul_of_nonneg_right
      (frequencySchedule_fullOrder_wave_budget (q := q) hμ1 hCm hb) (by positivity)).trans ?_)
    change freq ^ (((P : ℝ) + 2) / 32) * freq ^ (-5 / 2 : ℝ) ≤ _
    rw [← Real.rpow_add hfpos]
    apply Real.rpow_le_rpow_of_exponent_le hf
    dsimp only [E]
    linarith [(show 0 ≤ (P : ℝ) from by positivity)]
  have hWave : spatialHolderHalfNorm P O + spatialHolderHalfNorm P M ≤ freq ^ (2 * (P + 1)) := by
    calc
      _ ≤ freq ^ E + freq ^ E := add_le_add hO' hM'
      _ = 2 * freq ^ E := by ring
      _ ≤ freq * freq ^ E := mul_le_mul_of_nonneg_right hf₂ (Real.rpow_nonneg hfpos.le _)
      _ = freq ^ (1 + E) := by
        simpa only [Real.rpow_one] using (Real.rpow_add hfpos 1 E).symm
      _ ≤ freq ^ (2 * (P + 1)) := by
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le hf
        push_cast
        dsimp only [E]
        linarith [(show 0 ≤ (P : ℝ) from by positivity)]
  obtain ⟨hUO, hUOnorm⟩ := spatialHolderHalf_add_exact hU hO
  obtain ⟨_, hVnorm⟩ := spatialHolderHalf_add_exact hUO hM
  rw [hSplit]
  have hOne : 1 ≤ freq ^ (2 * (P + 1)) := one_le_pow₀ hf
  linarith only [hOne, hVnorm, hUOnorm, hPar', hWave]

section Step

variable {P : InductiveEulerParameters} {n : ℕ} {activationOld activation : ℝ}

/-- The Eulerian estimates of the finite hierarchy before the Fourier cutoff that the step reads from
Lemma 5.8 (the fields of the library `PhysicalWaveApproximationBounds` other than the pressure
bound, which here comes from (5.57) of Proposition 5.11). -/
structure StepApproxBounds (P : InductiveEulerParameters) (n : ℕ) (activation : ℝ)
    (V RV oscillation mean : Velocity) (Cstep Cmean : ℝ) : Prop where
  velocity_size : ∀ t ∈ Icc 0 (P.slab (n + 1) activation),
    1 + spatialHolderHalfNorm (6 * frequencyExponent P.exponentParameter (P.order (n + 2))) (V t) ≤
      3 * P.frequency (n + 1) ^
        (2 * (6 * frequencyExponent P.exponentParameter (P.order (n + 2)) + 1))
  residual_size : ∀ t ∈ Icc 0 (P.slab (n + 1) activation),
    spatialHolderHalfNorm 1 (RV t) ≤ P.frequency (n + 2) ^ (-7 / 2 : ℝ)
  oscillation_size : ∀ t ∈ Icc 0 (P.slab (n + 1) activation), ∀ x,
    ‖oscillation t x‖ ≤ Cstep * P.frequency (n + 1) ^ (-5 / 4 : ℝ)
  mean_size : ∀ m ≤ P.order (n + 1), ∀ t ∈ Icc 0 (P.slab (n + 1) activation),
    SpatialHolderHalf m (mean t) ∧
      spatialHolderHalfNorm m (mean t) ≤
        Cmean * (P.frequency n ^ 9) ^ (P.exponentParameter * (m + 2)) *
          P.frequency (n + 1) ^ (-5 / 2 : ℝ)

/-- **The fields of `StepApproxBounds` read from Lemma 5.8** (item 4 of the
proof of Theorem 7.1, sections/08b_induction.tex:376-381; (5.47), (5.48) of the latest
manuscript), for the approximate velocity `V = U + W_osc + W̄` of the step from the stage `n`
(`D = λ_n^9`, `λ = λ_{n+1}`, depth `P = 6K_{n+2}`): the size of `V` in `C^{P,1/2}` from the parent's
Bernstein jets and (5.48) (arithmetic of `velocityDepth_from_holder`), the oscillation (5.47), the
mean (5.48). The pressure increment is not read here (it comes from (5.57), `scheduled_bounds_of_5_11`). The residual size, which needs
(6.8), is the hypothesis `hRes`. -/
theorem physicalWaveApproximationBounds_of_5_8
    (parent : InductiveEulerStage P n activationOld)
    {V RV osc mean : Velocity} {Kosc0 Cparent Cstep Cmean : ℝ} {Kosc Kmean : ℕ → ℝ}
    (hμ : 2 ≤ P.frequency n)
    (hSlab : P.slab (n + 1) activation ≤ P.slab n activationOld)
    (hJets : ∀ t ∈ Icc 0 (P.slab (n + 1) activation),
      PhaseJetBound (6 * frequencyExponent P.exponentParameter (P.order (n + 2)) + 1)
        (Cparent * P.frequency n ^ (5 * (6 * frequencyExponent P.exponentParameter
          (P.order (n + 2)) + 1) + 1)) (parent.velocity t))
    (hCp : (3 * (((6 * frequencyExponent P.exponentParameter (P.order (n + 2)) : ℕ) : ℝ) + 1)) *
      Cparent ≤ P.frequency n)
    (hCparent : 0 ≤ Cparent)
    (hSplit : ∀ t ∈ Icc 0 (P.slab (n + 1) activation), V t = parent.velocity t + osc t + mean t)
    (hOscH : ∀ m : ℕ, ∀ t ∈ Icc 0 (P.slab (n + 1) activation),
      SpatialHolderHalf m (osc t) ∧ spatialHolderHalfNorm m (osc t) ≤
        Kosc m * ((P.frequency n) ^ 9) ^ (P.exponentParameter * (m + 2)) *
          P.frequency (n + 1) ^ ((3 : ℝ) * ((m : ℝ) + 1) / 2 - 5 / 4))
    (hOscSup : ∀ t ∈ Icc 0 (P.slab (n + 1) activation), ∀ x,
      ‖osc t x‖ ≤ Kosc0 * ((P.frequency n) ^ 9) ^ P.exponentParameter *
        P.frequency (n + 1) ^ (-5 / 4 : ℝ))
    (hMeanH : ∀ m : ℕ, ∀ t ∈ Icc 0 (P.slab (n + 1) activation),
      SpatialHolderHalf m (mean t) ∧ spatialHolderHalfNorm m (mean t) ≤
        Kmean m * ((P.frequency n) ^ 9) ^ (P.exponentParameter * (m + 2)) *
          P.frequency (n + 1) ^ (-5 / 2 : ℝ))
    (hCosc : Kosc (6 * frequencyExponent P.exponentParameter (P.order (n + 2))) ≤ P.frequency n)
    (hCmeanDepth : Kmean (6 * frequencyExponent P.exponentParameter (P.order (n + 2))) ≤
      P.frequency n)
    (hCstep : Kosc0 * ((P.frequency n) ^ 9) ^ P.exponentParameter ≤ Cstep)
    (hKmean : ∀ m ≤ P.order (n + 1), Kmean m ≤ Cmean)
    (hRes : ∀ t ∈ Icc 0 (P.slab (n + 1) activation),
      spatialHolderHalfNorm 1 (RV t) ≤ P.frequency (n + 2) ^ (-7 / 2 : ℝ)) :
    StepApproxBounds P n activation V RV osc mean Cstep Cmean := by
  have hb := P.exponentParameter_ge
  have hfreq : P.frequency (n + 1) = P.frequency n ^
      frequencyExponent P.exponentParameter (P.order (n + 1)) := P.frequency_step n
  have hf0 : 0 ≤ P.frequency (n + 1) := by
    rw [hfreq]; exact pow_nonneg (by linarith) _
  refine ⟨fun t ht => ?_, hRes, fun t ht x => ?_, fun m hm t ht => ?_⟩
  · have hUsmooth : ContDiff ℝ ∞ (parent.velocity t) :=
      contDiff_slice' parent.smooth_velocity ⟨ht.1, ht.2.trans hSlab⟩
    obtain ⟨hUreg, hUnorm⟩ := spatialHolderHalfNorm_le_of_uniformJets hUsmooth
      (mul_nonneg hCparent (by positivity)) (hJets t ht)
    rw [hfreq]
    refine velocityDepth_from_holder (Cparent := (3 * (((6 * frequencyExponent P.exponentParameter
      (P.order (n + 2)) : ℕ) : ℝ) + 1)) * Cparent) (Cosc := Kosc (6 * frequencyExponent
      P.exponentParameter (P.order (n + 2)))) (Cmean := Kmean (6 * frequencyExponent
      P.exponentParameter (P.order (n + 2)))) hμ hb hCp hCosc hCmeanDepth (hSplit t ht) hUreg
      (hOscH _ t ht).1 (hMeanH _ t ht).1 ?_ ?_ ?_
    · refine hUnorm.trans (le_of_eq ?_)
      push_cast
      ring
    · simpa only [hfreq] using (hOscH _ t ht).2
    · simpa only [hfreq] using (hMeanH _ t ht).2
  · refine (hOscSup t ht x).trans ?_
    exact mul_le_mul_of_nonneg_right hCstep (Real.rpow_nonneg hf0 _)
  · refine ⟨(hMeanH m t ht).1, (hMeanH m t ht).2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hKmean m hm)
      (by positivity)) (Real.rpow_nonneg hf0 _)

end Step

end

end TorusEuler.Paper.Lib.S678a
