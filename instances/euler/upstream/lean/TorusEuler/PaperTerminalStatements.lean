import TorusEuler.Theorem11FromInductiveStages
import TorusEuler.PeriodicEulerUniqueness

/-! Proposition 8.1, Proposition 8.2, Corollary 8.3, and Proposition 8.4
of the frozen torus manuscript. -/

open Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace TorusEuler

/-- The limit in Proposition 8.1 and its agreement with any maximal
smooth periodic solution from the same datum. -/
structure PaperLimitAgreement (s : InductiveEulerStages) (T : ℝ) (u : Velocity) (p : Pressure) : Prop where
  euler : IsEulerSolution T u p
  odd : ∀ t ∈ Ico 0 T, Function.Odd (u t)
  initial_smooth : ContDiff ℝ ∞ (u 0)
  initial_odd : Function.Odd (u 0)
  initial_divergence_free : ∀ x, divergence (u 0) x = 0
  initial_convergence : ∀ m : ℕ, Tendsto
    (fun j => spatialHolderHalfNorm m (s.velocity j 0 - u 0)) atTop (𝓝 0)
  continuousToTerminal : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3))
  closed_velocity_limit : TendstoUniformlyOn (fun j => Function.uncurry (s.velocity j))
    (Function.uncurry u) atTop (Icc 0 T ×ˢ (univ : Set Vec3))
  prefix_convergence : ∀ S < T, ∀ m : ℕ, TendstoUniformlyOn
    (fun j t => spatialHolderHalfNorm m (s.velocity j t - u t)) (fun _ => 0) atTop (Icc 0 S)
  maximal_agreement : ∀ {T₁ : ℝ} {v : Velocity} {q : Pressure},
    IsMaximalEulerSolution T₁ v q → v 0 = u 0 → T ≤ T₁ ∧ EqOn v u (Ico 0 T)

/-- The bounded velocity and the full terminal central-curl limit of Proposition 8.2. -/
def PaperTerminalVelocityCurl (T : ℝ) (u : Velocity) : Prop :=
  (∃ C : ℝ, ∀ t ∈ Ico 0 T, torusLInf (u t) ≤ ENNReal.ofReal C) ∧
    Tendsto (fun t => ‖curl (u t) 0‖) (𝓝[Ico 0 T] T) atTop

/-- The maximal lifespan and both integral conclusions of Corollary 8.3.
The endpoint is the same `T` as the limit of the activation times. -/
def PaperTerminalTime (T : ℝ) (u : Velocity) (p : Pressure) : Prop :=
  IsMaximalEulerSolution T u p ∧
    (∫⁻ t in Ico 0 T, torusLInf (curl (u t))) = ⊤ ∧
    (∫⁻ t in Ico 0 T, torusLInf (fderiv ℝ (u t))) = ⊤

/-- Both off-origin spatial limits in Proposition 8.4. -/
def PaperTerminalOffOrigin (T : ℝ) (u : Velocity) : Prop :=
  HasOffOriginLimits T u ∧ HasOffOriginLimits T (timeDerivative T u)

namespace InductiveEulerStages

private theorem frequency_square_for_terminal (s : InductiveEulerStages) (hInit : 2 ≤ s.frequency 0) :
    ∀ j, s.frequency j ^ 2 ≤ s.frequency (j + 1) := by
  have hMono := frequencySchedule_frequency_mono s.exponentParameter s.order s.frequency
    s.exponentParameter_ge (one_le_two.trans hInit) s.frequency_step
  intro j
  rw [s.frequency_step]
  apply pow_le_pow_right₀ (one_le_two.trans (hInit.trans (hMono (Nat.zero_le j))))
  unfold frequencyExponent
  have h := s.exponentParameter_ge
  nlinarith

/-- Proposition 8.1 for the compatible stage data on its common terminal
slab. The maximal-solution comparison uses periodic Euler uniqueness. -/
theorem paper_proposition_8_1 (s : InductiveEulerStages) {T : ℝ} (hT : 0 < T)
    (hSlab : ∀ j, T ≤ s.slab j) (hInit : 2 ≤ s.frequency 0)
    (hActivation : Tendsto s.activation atTop (𝓝 T)) :
    ∃ (u : Velocity) (p : Pressure), PaperLimitAgreement s T u p := by
  have hMono := frequencySchedule_frequency_mono s.exponentParameter s.order s.frequency
    s.exponentParameter_ge (one_le_two.trans hInit) s.frequency_step
  have hFreq := frequencySchedule_frequency_tendsto_atTop s.exponentParameter s.order s.frequency
    s.exponentParameter_ge (one_lt_two.trans_le hInit) s.frequency_step
  have hOrder := frequencySchedule_order_tendsto_atTop s.threshold s.frequency s.order
    s.initial_order s.initial_threshold hMono hFreq s.order_maximum
  have hCorrection (j m : ℕ) (hm : m ≤ s.order (j + 1)) (t : ℝ)
      (ht : t ∈ Icc 0 (s.slab (j + 1))) (x : Vec3) :
      ‖iteratedFDeriv ℝ m (s.velocity (j + 1) t - s.velocity j t - s.oscillation (j + 1) t) x‖
        ≤ (s.frequency (j + 1))⁻¹ := by
    have h := s.correction_bound j m hm t ht
    exact (norm_iteratedFDeriv_le_spatialHolderHalfNorm h.1 le_rfl x).trans h.2
  obtain ⟨u, p, hEuler, hOdd, hContinuous, hLimit, hJets⟩ :=
    exists_inductive_periodicEulerSolution (U := s.velocity) hT hSlab hInit
      (s.frequency_square_for_terminal hInit) hOrder hActivation s.smooth
      (fun j t _ => s.periodic_velocity j t) s.odd s.divergence_free
      s.oscillation_vanishes s.oscillation_bound hCorrection s.projected_residual s.residual_bound
  have hAt0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
  have hPrefix (S : ℝ) (hST : S < T) (m : ℕ) : TendstoUniformlyOn
      (fun j t => spatialHolderHalfNorm m (s.velocity j t - u t))
      (fun _ => 0) atTop (Icc 0 S) := by
    obtain ⟨S', hSS', hS'T⟩ := exists_between (max_lt hST hT)
    exact ((hJets S' ((le_max_right _ _).trans_lt hSS') hS'T m).2).mono
      (Icc_subset_Icc_right ((le_max_left _ _).trans hSS'.le))
  refine ⟨u, p, hEuler, hOdd, hEuler.contDiff_velocity_slice hAt0, hOdd 0 hAt0,
    hEuler.incompressible 0 hAt0, ?_, hContinuous, hLimit, hPrefix, ?_⟩
  · intro m
    exact (hPrefix 0 hT m).tendsto_at (x := 0) ⟨le_rfl, le_rfl⟩
  · intro T₁ v q hMax h0
    have hEq := hMax.1.velocity_eq_on_common_interval hEuler h0
    have hLe : T ≤ T₁ := by
      by_contra! hSmall
      apply hMax.2 T hSmall
      refine ⟨u, p, hEuler, fun t ht => ?_⟩
      exact (hEq t (by simpa only [min_eq_left hSmall.le] using ht)).symm
    exact ⟨hLe, fun _ ht => hEq _ (by simpa only [min_eq_right hLe] using ht)⟩

end InductiveEulerStages

/-- Proposition 8.2, Corollary 8.3, and Proposition 8.4 for one and
the same limit in Proposition 8.1. -/
theorem paper_section_8_of_inductiveEulerStages :
    ∃ N₀ : ℝ, ∀ (s : InductiveEulerStages) (_w : InductiveEulerCentralWaves s),
      N₀ ≤ s.frequency 0 →
      ∃ (T : ℝ) (u : Velocity) (p : Pressure),
        0 < T ∧ (∀ j, T < s.slab j) ∧ Tendsto s.activation atTop (𝓝 T) ∧
        PaperLimitAgreement s T u p ∧ PaperTerminalVelocityCurl T u ∧
        PaperTerminalTime T u p ∧ PaperTerminalOffOrigin T u := by
  obtain ⟨N, hN⟩ := exists_theorem11Witness_of_inductiveEulerStages
  refine ⟨N, fun s w hLarge => ?_⟩
  obtain ⟨hInit, T, u, p, hT, hSlab, hActivation, hWitness, hLimit⟩ := hN s w hLarge
  obtain ⟨v, q, hAgreement⟩ := s.paper_proposition_8_1 hT (fun j => (hSlab j).le) hInit hActivation
  have hEq (t : ℝ) (ht : t ∈ Icc 0 T) : u t = v t := by
    funext x
    exact tendsto_nhds_unique (hLimit.tendsto_at (x := (t, x)) ⟨ht, mem_univ x⟩)
      (hAgreement.closed_velocity_limit.tendsto_at (x := (t, x)) ⟨ht, mem_univ x⟩)
  have h0 : u 0 = v 0 := hEq 0 ⟨le_rfl, hT.le⟩
  rcases hWitness with
    ⟨hu0, _, hOdd0, hDiv0, hMax, _, hOdd, hGradient, hCurl, hBound, hCentral, hOff, hOffDt⟩
  refine ⟨T, u, p, hT, hSlab, hActivation, ?_, ⟨hBound, hCentral⟩, ⟨hMax, hCurl, hGradient⟩,
    ⟨hOff, hOffDt⟩⟩
  refine ⟨hMax.1, hOdd, hu0, hOdd0, hDiv0, ?_, ?_, hLimit, ?_, ?_⟩
  · simpa only [h0] using hAgreement.initial_convergence
  · exact hAgreement.continuousToTerminal.congr fun z hz => congrFun (hEq z.1 hz.1) z.2
  · intro S hST m
    exact (hAgreement.prefix_convergence S hST m).congr (Eventually.of_forall fun j t ht => by
      change spatialHolderHalfNorm m (s.velocity j t - v t) =
        spatialHolderHalfNorm m (s.velocity j t - u t)
      rw [hEq t ⟨ht.1, ht.2.trans hST.le⟩])
  · intro T₁ U P hMax₁ hInitial
    obtain ⟨hLe, hAgree⟩ := hAgreement.maximal_agreement hMax₁ (hInitial.trans h0)
    exact ⟨hLe, fun t ht => (hAgree ht).trans (hEq t (Ico_subset_Icc_self ht)).symm⟩

end TorusEuler
