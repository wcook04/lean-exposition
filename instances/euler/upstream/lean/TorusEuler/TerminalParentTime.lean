import TorusEuler.TerminalTimeCutoffCommutation
import TorusEuler.TerminalParentTimeBand
import TorusEuler.TerminalTimeAdvection
import TorusEuler.TerminalLeraySup

/-! The exact projected Euler recurrence and parent time estimates for the
terminal smoothness note. -/

open Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

namespace InductiveEulerStage

section StageEquations

variable {P : InductiveEulerParameters} {n : ℕ} {activation : ℝ}

local notation "S" => P.slab n activation

theorem smooth_stage_residual (s : InductiveEulerStage P n activation) (hS : 0 < S) :
    ContDiffOn ℝ ∞ (Function.uncurry s.residual) (Icc 0 S ×ˢ (univ : Set Vec3)) :=
  contDiffOn_closedSlab_momentumResidual (u := s.velocity) hS s.smooth_velocity s.smooth_pressure

/-- The zeroth time-order estimates follow from the actual stage bounds. -/
theorem slabTimeJet_zero_stage_bounds (s : InductiveEulerStage P n activation)
    (hμ : 1 ≤ P.frequency n) {t : ℝ} (ht : t ∈ Icc 0 S) (x : Vec3) :
    ‖slabTimeJet 0 S 0 s.velocity t x‖ ≤ P.frequency n ∧
    ‖slabTimeJet 0 S 0 s.residual t x‖ ≤ P.frequency (n + 1) ^ (-(5 / 2) : ℝ) := by
  let ν := P.frequency (n + 1)
  have hν : 1 ≤ ν := by
    dsimp only [ν]
    rw [P.frequency_step n]
    exact one_le_pow₀ hμ
  simp only [slabTimeJet, iteratedDerivWithin_zero]
  refine ⟨((s.torusVelocity t).norm_coe_le_norm (toUnitTorus x)).trans (s.velocity_bound t ht), ?_⟩
  refine (s.residual_bound t ht x).trans ?_
  have hν₀ : 0 ≤ ν := zero_le_one.trans hν
  have heq : ν⁻¹ ^ (3 : ℕ) = ν ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg hν₀, inv_pow]
    norm_num only [Real.rpow_ofNat]
  change ν⁻¹ ^ (3 : ℕ) ≤ ν ^ (-(5 / 2) : ℝ)
  rw [heq]
  exact Real.rpow_le_rpow_of_exponent_le hν (by norm_num)

/-- The first within-slab derivative satisfies the exact Leray equation. -/
theorem slabTimeJet_one_stage_eq (s : InductiveEulerStage P n activation) (hS : 0 < S)
    {t : ℝ} (ht : t ∈ Icc 0 S) (x : Vec3) :
    slabTimeJet 0 S 1 s.velocity t x =
      s.residual t x - periodicLerayHolderLift (slabAdvection s.velocity s.velocity t) x := by
  have hAd := momentumTensorDivergence_self_eq_advection
    ((terminal_contDiff_spaceSlice (f := s.velocity) s.smooth_velocity ht).differentiable (by simp))
    (s.divergence_free t ht)
  have hEq := hasDerivWithinAt_of_closedSlabLerayMomentum hS
    (u := s.velocity) (R := s.residual) s.smooth_velocity (fun r _ => s.periodic_velocity r)
    s.divergence_free (fun r hr => (s.projected_eq r hr).symm) ht x
  rw [hAd] at hEq
  rw [slabTimeJet_succ, slabTimeJet_zero]
  exact hEq.derivWithin (uniqueDiffOn_Icc hS t ht)

/-- The differentiated stage momentum equation uses only the residual jet
one order below the resulting velocity derivative. -/
theorem slabTimeJet_succ_stage_eq (s : InductiveEulerStage P n activation) (hS : 0 < S)
    (q : ℕ) {t : ℝ} (ht : t ∈ Icc 0 S) (x : Vec3) :
    slabTimeJet 0 S (q + 1) s.velocity t x = slabTimeJet 0 S q s.residual t x -
      periodicLerayHolderLift (slabTimeJet 0 S q (slabAdvection s.velocity s.velocity) t) x := by
  let adv := slabAdvection s.velocity s.velocity
  have hAdv := smooth_slabAdvection hS (v := s.velocity) (w := s.velocity) s.smooth_velocity s.smooth_velocity
  have hPer (r : ℝ) (hr : r ∈ Icc 0 S) : SpatiallyPeriodic (adv r) :=
    slabAdvection_periodic
      ((terminal_contDiff_spaceSlice (f := s.velocity) s.smooth_velocity hr).differentiable (by simp))
      (s.periodic_velocity r) (s.periodic_velocity r)
  have hProj (r : ℝ) (hr : r ∈ Icc 0 S) :
      periodicLerayHolderLift (adv r) x = s.residual r x - slabTimeJet 0 S 1 s.velocity r x := by
    rw [s.slabTimeJet_one_stage_eq hS hr x]
    abel
  have hR := terminal_contDiffOn_timeSlice (s.smooth_stage_residual hS) x
  have hU := terminal_contDiffOn_timeSlice (slabTimeJet_smooth hS (f := s.velocity) s.smooth_velocity 1) x
  have hJetEq (r : ℝ) :
      iteratedDerivWithin q (fun v => slabTimeJet 0 S 1 s.velocity v x) (Icc 0 S) r =
        slabTimeJet 0 S (q + 1) s.velocity r x := by
    change iteratedDerivWithin q (fun v => iteratedDerivWithin 1 (fun z => s.velocity z x) (Icc 0 S) v)
      (Icc 0 S) r = iteratedDerivWithin (q + 1) (fun z => s.velocity z x) (Icc 0 S) r
    simp only [iteratedDerivWithin_one]
    exact (congrFun (iteratedDerivWithin_succ' (n := q) (f := fun z => s.velocity z x)
      (s := Icc 0 S)) r).symm
  have h := slabTimeJet_periodicLerayHolderLift hS hAdv hPer q ht x
  change iteratedDerivWithin q (fun r => periodicLerayHolderLift (adv r) x) (Icc 0 S) t = _ at h
  rw [iteratedDerivWithin_congr hProj ht,
    ← Pi.sub_def, iteratedDerivWithin_sub ht (uniqueDiffOn_Icc hS)
      ((hR.of_le (by simp)) t ht) ((hU.of_le (by simp)) t ht), hJetEq] at h
  rw [← h]
  abel

/-- The projected recurrence with its nonlinearity written as the exact
binomial sum of lower velocity time jets. -/
theorem slabTimeJet_succ_stage_eq_binomial (s : InductiveEulerStage P n activation) (hS : 0 < S)
    (q : ℕ) {t : ℝ} (ht : t ∈ Icc 0 S) (x : Vec3) :
    slabTimeJet 0 S (q + 1) s.velocity t x = slabTimeJet 0 S q s.residual t x -
      periodicLerayHolderLift (fun y => ∑ i ∈ Finset.range (q + 1), q.choose i •
        slabAdvection (slabTimeJet 0 S i s.velocity) (slabTimeJet 0 S (q - i) s.velocity) t y) x := by
  have hAdv := funext (slabTimeJet_slabAdvection (v := s.velocity) (w := s.velocity)
    hS s.smooth_velocity s.smooth_velocity q ht)
  rw [s.slabTimeJet_succ_stage_eq hS q ht x, hAdv]

end StageEquations

/-- A pointwise parent bound through time order `q`, together with the
residual through order `q`, bounds velocity through order `q+1` by
one absolute power of the old frequency. -/
theorem exists_slabTimeJet_succ_velocity_bound (q A : ℕ) :
    ∃ A' : ℕ, A ≤ A' ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {activation : ℝ}
        (s : InductiveEulerStage P n activation), 0 < P.slab n activation → 2 ≤ P.frequency n →
        (∀ i ≤ q, ∀ t ∈ Icc 0 (P.slab n activation), ∀ x,
          ‖slabTimeJet 0 (P.slab n activation) i s.velocity t x‖ ≤ P.frequency n ^ A) →
        (∀ t ∈ Icc 0 (P.slab n activation), ∀ x,
          ‖slabTimeJet 0 (P.slab n activation) q s.residual t x‖ ≤ 1) →
        ∀ i ≤ q + 1, ∀ t ∈ Icc 0 (P.slab n activation), ∀ x,
          ‖slabTimeJet 0 (P.slab n activation) i s.velocity t x‖ ≤ P.frequency n ^ A' := by
  obtain ⟨K, hK, hBernstein⟩ := exists_slabTimeJet_bernsteinBounds
  let L := Real.sqrt 2 * ‖endpointStrongSpatialLeray‖
  let C := L * (2 ^ q * (3 * K 1 + (K 1 * K 1 + K 2))) + 1
  obtain ⟨e, he⟩ := pow_unbounded_of_one_lt C (show (1 : ℝ) < 2 by norm_num)
  let A' := (2 * A + 10) + e
  refine ⟨A', by dsimp only [A']; omega, ?_⟩
  intro P n activation s hS hμ hU hR i hi t ht x
  let S := P.slab n activation
  let μ := P.frequency n
  have hμ₁ : 1 ≤ μ := one_le_two.trans hμ
  have hμp : 0 < μ := zero_lt_one.trans_le hμ₁
  by_cases hiq : i ≤ q
  · exact (hU i hiq t ht x).trans (pow_le_pow_right₀ hμ₁ (by dsimp only [A']; omega))
  have hiEq : i = q + 1 := by omega
  subst i
  let W := μ ^ A
  let W₁ := K 1 * μ ^ (A + 5)
  let W₂ := K 2 * μ ^ (A + 10)
  have hW : 0 ≤ W := pow_nonneg hμp.le _
  have hW₁ : 0 ≤ W₁ := mul_nonneg (hK 1) (pow_nonneg hμp.le _)
  have hW₂ : 0 ≤ W₂ := mul_nonneg (hK 2) (pow_nonneg hμp.le _)
  have hDeriv (j : ℕ) (hj : j ≤ q) (m : ℕ) (y : Vec3) :
      ‖iteratedFDeriv ℝ m (slabTimeJet 0 S j s.velocity t) y‖ ≤ K m * μ ^ (A + 5 * m) := by
    have h := (hBernstein s hS hμp j W 0 hW le_rfl).1 (hU j hj) m t ht y
    simpa only [W, pow_add, pow_mul, mul_assoc] using h
  have hD (j : ℕ) (hj : j ≤ q) (y : Vec3) :
      ‖fderiv ℝ (slabTimeJet 0 S j s.velocity t) y‖ ≤ W₁ := by
    simpa only [norm_iteratedFDeriv_one, Nat.mul_one, W₁] using hDeriv j hj 1 y
  have hD₂ (j : ℕ) (hj : j ≤ q) (y : Vec3) :
      ‖iteratedFDeriv ℝ 2 (slabTimeJet 0 S j s.velocity t) y‖ ≤ W₂ :=
    hDeriv j hj 2 y
  let adv := slabAdvection s.velocity s.velocity
  let f := slabTimeJet 0 S q adv t
  have hAd := smooth_slabAdvection hS (v := s.velocity) (w := s.velocity) s.smooth_velocity s.smooth_velocity
  have hSmooth := slabTimeJet_slice_smooth hS hAd q ht
  have hPer := slabTimeJet_periodic (f := adv) (fun r hr => slabAdvection_periodic
    ((terminal_contDiff_spaceSlice (f := s.velocity) s.smooth_velocity hr).differentiable (by simp))
    (s.periodic_velocity r) (s.periodic_velocity r)) q ht
  let amp := 2 ^ q * (W₁ * W)
  let grad := 2 ^ q * (W₁ * W₁ + W₂ * W)
  have hF (y : Vec3) : ‖f y‖ ≤ amp ∧ ‖fderiv ℝ f y‖ ≤ grad :=
    norm_slabTimeJet_slabAdvection_and_fderiv_le (u := s.velocity) hS s.smooth_velocity q ht
      hW₁ hW₂ (fun j hj => hU j hj t ht) hD hD₂ y
  have hL (y : Vec3) : ‖periodicLerayHolderLift f y‖ ≤ L * (3 * amp + grad) :=
    norm_periodicLerayHolderLift_le_sup_and_fderiv (hSmooth.differentiable (by simp)) hPer
      (fun y => (hF y).1) (fun y => (hF y).2) y
  have hExpo : μ ^ (2 * A + 5) ≤ μ ^ (2 * A + 10) :=
    pow_le_pow_right₀ hμ₁ (by omega)
  have hAmp : amp ≤ (2 ^ q * K 1) * μ ^ (2 * A + 10) := by
    have heq : amp = (2 ^ q * K 1) * μ ^ (2 * A + 5) := by
      dsimp only [amp, W, W₁]
      simp only [pow_add, two_mul]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hExpo
      (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) (hK 1))
  have hGrad : grad = (2 ^ q * (K 1 * K 1 + K 2)) * μ ^ (2 * A + 10) := by
    dsimp only [grad, W, W₁, W₂]
    simp only [pow_add, two_mul]
    rw [show μ ^ (10 : ℕ) = μ ^ (5 : ℕ) * μ ^ (5 : ℕ) by rw [← pow_add]]
    ring
  have hProj : ‖periodicLerayHolderLift f x‖ ≤ (C - 1) * μ ^ (2 * A + 10) := by
    refine (hL x).trans ?_
    calc
      _ ≤ L * (3 * ((2 ^ q * K 1) * μ ^ (2 * A + 10)) +
        (2 ^ q * (K 1 * K 1 + K 2)) * μ ^ (2 * A + 10)) := by
          rw [hGrad]
          gcongr
      _ = _ := by dsimp only [C]; ring
  have hOne : 1 ≤ μ ^ (2 * A + 10) := one_le_pow₀ hμ₁
  have hCe : C ≤ μ ^ e := he.le.trans (pow_le_pow_left₀ zero_le_two hμ e)
  rw [s.slabTimeJet_succ_stage_eq hS q ht x]
  change ‖slabTimeJet 0 S q s.residual t x - periodicLerayHolderLift f x‖ ≤ _
  calc
    _ ≤ 1 + (C - 1) * μ ^ (2 * A + 10) :=
      (norm_sub_le _ _).trans (add_le_add (hR t ht x) hProj)
    _ ≤ μ ^ (2 * A + 10) + (C - 1) * μ ^ (2 * A + 10) :=
      add_le_add hOne le_rfl
    _ = C * μ ^ (2 * A + 10) := by ring
    _ ≤ μ ^ e * μ ^ (2 * A + 10) := mul_le_mul_of_nonneg_right hCe (pow_nonneg hμp.le _)
    _ = μ ^ A' := by
      dsimp only [A']
      rw [mul_comm, ← pow_add]

/-- The old parent's mixed spatial estimates are uniform in the spatial
order apart from its Bernstein factor. The highest velocity time
derivative uses the residual only one order lower. -/
theorem exists_terminalParentTime_bounds (q A : ℕ) :
    ∃ A' : ℕ, ∃ K : ℕ → ℝ, A ≤ A' ∧ (∀ m, 0 ≤ K m) ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {activation : ℝ}
        (s : InductiveEulerStage P n activation), 0 < P.slab n activation → 2 ≤ P.frequency n →
        (∀ i ≤ q, ∀ t ∈ Icc 0 (P.slab n activation), ∀ x,
          ‖slabTimeJet 0 (P.slab n activation) i s.velocity t x‖ ≤ P.frequency n ^ A) →
        (∀ i ≤ q, ∀ t ∈ Icc 0 (P.slab n activation), ∀ x,
          ‖slabTimeJet 0 (P.slab n activation) i s.residual t x‖ ≤ P.frequency (n + 1) ^ (-(5 / 2) : ℝ)) →
        (∀ i ≤ q + 1, ∀ t ∈ Icc 0 (P.slab n activation), ∀ x,
          ‖slabTimeJet 0 (P.slab n activation) i s.velocity t x‖ ≤ P.frequency n ^ A') ∧
        (∀ i ≤ q + 1, ∀ m, ∀ t ∈ Icc 0 (P.slab n activation), ∀ x,
          ‖iteratedFDeriv ℝ m (slabTimeJet 0 (P.slab n activation) i s.velocity t) x‖ ≤
            K m * P.frequency n ^ (A' + 5 * m)) ∧
        (∀ i ≤ q, ∀ m, ∀ t ∈ Icc 0 (P.slab n activation), ∀ x,
          ‖iteratedFDeriv ℝ m (slabTimeJet 0 (P.slab n activation) i s.residual t) x‖ ≤
            K m * P.frequency n ^ (5 * m) * P.frequency (n + 1) ^ (-(5 / 2) : ℝ)) := by
  obtain ⟨A', hA', hStep⟩ := exists_slabTimeJet_succ_velocity_bound q A
  obtain ⟨K, hK, hBernstein⟩ := exists_slabTimeJet_bernsteinBounds
  refine ⟨A', K, hA', hK, ?_⟩
  intro P n activation s hS hμ hU hR
  let μ := P.frequency n
  let ν := P.frequency (n + 1)
  have hμ₁ : 1 ≤ μ := one_le_two.trans hμ
  have hμp : 0 < μ := zero_lt_one.trans_le hμ₁
  have hν : 1 ≤ ν := by
    dsimp only [ν]
    rw [P.frequency_step n]
    exact one_le_pow₀ hμ₁
  have hνp : 0 < ν := zero_lt_one.trans_le hν
  have hUp := hStep s hS hμ hU (fun t ht x => (hR q le_rfl t ht x).trans
    (Real.rpow_le_one_of_one_le_of_nonpos hν (by norm_num)))
  refine ⟨hUp, ?_, ?_⟩
  · intro i hi m t ht x
    have h := (hBernstein s hS hμp i (μ ^ A') 0 (pow_nonneg hμp.le _) le_rfl).1
      (hUp i hi) m t ht x
    simpa only [pow_add, pow_mul, mul_assoc] using h
  · intro i hi m t ht x
    have h := (hBernstein s hS hμp i 0 (ν ^ (-(5 / 2) : ℝ)) le_rfl (Real.rpow_nonneg hνp.le _)).2
      (hR i hi) m t ht x
    simpa only [pow_mul, mul_right_comm] using h

end InductiveEulerStage

end

end TorusEuler
