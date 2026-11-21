import TorusEuler.TerminalTimeCutoffResidual
import TorusEuler.TerminalTimeVelocityCutoff

/-! Closed-slab time bounds for the differentiated child velocity and residual. -/

open Set UnitAddTorus
open scoped ContDiff

namespace TorusEuler

noncomputable section

set_option maxHeartbeats 2400000

local notation "Labels" => UnitAddTorus (Fin 3)
local notation "Slab(" T ")" => Set.prod (Icc (0 : ℝ) T) (univ : Set Vec3)

private theorem terminal_spatialHolderHalf_zero (m : ℕ) :
    SpatialHolderHalf m (0 : Vec3 → Vec3) ∧ spatialHolderHalfNorm m (0 : Vec3 → Vec3) = 0 := by
  have hS : SpatiallyPeriodic (0 : Vec3 → Vec3) := fun _ _ => rfl
  refine ⟨spatialHolderHalf_of_contDiff_periodic (show ContDiff ℝ ∞ (fun _ : Vec3 => (0 : Vec3)) from
    contDiff_const) hS m, ?_⟩
  simp [spatialHolderHalfNorm, spatialHolderHalfSeminorm, spatialHolderHalfQuotient, spatialSupNorm]

private theorem terminal_spatialHolderHalf_nsmul {f : Vec3 → Vec3} {m : ℕ}
    (hf : SpatialHolderHalf m f) (n : ℕ) :
    SpatialHolderHalf m (n • f) ∧ spatialHolderHalfNorm m (n • f) ≤ (n : ℝ) * spatialHolderHalfNorm m f := by
  induction n with
  | zero =>
    obtain ⟨h, hn⟩ := terminal_spatialHolderHalf_zero m
    simpa only [zero_nsmul, Nat.cast_zero, zero_mul] using And.intro h hn.le
  | succ n ih =>
    rw [succ_nsmul, Nat.cast_succ, add_mul, one_mul]
    obtain ⟨h, hb⟩ := spatialHolderHalf_add_exact ih.1 hf
    exact ⟨h, hb.trans (add_le_add ih.2 le_rfl)⟩

private theorem terminal_spatialHolderHalf_sum {ι : Type*} (s : Finset ι) {m : ℕ} {f : ι → Vec3 → Vec3}
    (hf : ∀ j ∈ s, SpatialHolderHalf m (f j)) :
    SpatialHolderHalf m (∑ j ∈ s, f j) ∧
      spatialHolderHalfNorm m (∑ j ∈ s, f j) ≤ ∑ j ∈ s, spatialHolderHalfNorm m (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨h, hn⟩ := terminal_spatialHolderHalf_zero m
    simpa only [Finset.sum_empty] using And.intro h hn.le
  | @insert a s hs ih =>
    rw [Finset.sum_insert hs, Finset.sum_insert hs]
    obtain ⟨h, hN⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    obtain ⟨h', hN'⟩ := spatialHolderHalf_add_exact (hf a (Finset.mem_insert_self a s)) h
    exact ⟨h', hN'.trans (add_le_add le_rfl hN)⟩

private theorem terminalCutoffStress_differentiable (ψ : Vec3 → ℝ) (Λ : ℝ) (g h : C(Labels, Vec3)) :
    Differentiable ℝ (terminalCutoffStress ψ Λ g h) := by
  have h₁ := contDiff_lift_realVectorFourierCutoff ψ Λ g
  have h₂ := contDiff_lift_realVectorFourierCutoff ψ Λ h
  have h₃ := contDiff_lift_momentumTensorFourierCutoff ψ Λ (cutoffMomentumTensor g h)
  exact (((momentumTensor.contDiff.comp h₁).clm_apply h₂).sub h₃).differentiable (by simp)

private theorem terminalCutoffStress_periodic (ψ : Vec3 → ℝ) (Λ : ℝ) (g h : C(Labels, Vec3)) :
    SpatiallyPeriodic (terminalCutoffStress ψ Λ g h) := fun n x => by
  simp only [terminalCutoffStress, terminalCutoffVector, (toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩]

private theorem terminalCutoffStress_div_sum (ψ : Vec3 → ℝ) (Λ : ℝ) (U : ℕ → C(Labels, Vec3)) (q : ℕ) :
    (momentumTensorDivergence ∘ fderiv ℝ
      (∑ j ∈ Finset.range (q + 1), q.choose j • terminalCutoffStress ψ Λ (U j) (U (q - j)))) =
      ∑ j ∈ Finset.range (q + 1), q.choose j •
        (momentumTensorDivergence ∘ fderiv ℝ (terminalCutoffStress ψ Λ (U j) (U (q - j)))) := by
  funext x
  have hD j : DifferentiableAt ℝ
      ((q.choose j : ℝ) • terminalCutoffStress ψ Λ (U j) (U (q - j))) x :=
    ((terminalCutoffStress_differentiable ψ Λ (U j) (U (q - j))) x).const_smul _
  have hB :
      fderiv ℝ (∑ j ∈ Finset.range (q + 1), q.choose j • terminalCutoffStress ψ Λ (U j) (U (q - j))) x =
        ∑ j ∈ Finset.range (q + 1), q.choose j • fderiv ℝ (terminalCutoffStress ψ Λ (U j) (U (q - j))) x := by
    simp_rw [← Nat.cast_smul_eq_nsmul ℝ]
    rw [fderiv_sum (fun j _ => hD j)]
    apply Finset.sum_congr rfl
    intro j _
    exact fderiv_const_smul ((terminalCutoffStress_differentiable ψ Λ (U j) (U (q - j))) x) _
  simp only [Function.comp_apply, hB, map_sum, map_nsmul, Finset.sum_apply, Pi.smul_apply]

/-- The paper's dyadic cutoff has one depth-independent coefficient for the
input residual and a fixed cost for each time order and cutoff depth. -/
theorem exists_terminalTimeCutoffResidualBudget :
    ∃ (Cr : ℝ) (Ct : ℕ → ℕ → ℝ), 0 ≤ Cr ∧ (∀ q depth, 0 ≤ Ct q depth) ∧
      ∀ {T Λ : ℝ} {V RV : Velocity}
        (s : TruncatedChildStage T Λ dyadicMultiplierCutoff V RV), 0 < T → 0 < Λ →
        ContDiffOn ℝ ∞ (Function.uncurry V) (Slab(T)) →
        ContDiffOn ℝ ∞ (Function.uncurry RV) (Slab(T)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (V t)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (RV t)) → ∀
        (q i depth : ℕ), i ≤ q → 2 ≤ depth → ∀ t ∈ Icc 0 T, ∀ M : ℝ,
        (∀ j ≤ i, spatialHolderHalfNorm depth (slabTimeJet 0 T j V t) ≤ M) →
        SpatialHolderHalf 1 (slabTimeJet 0 T i s.residual t) ∧
          spatialHolderHalfNorm 1 (slabTimeJet 0 T i s.residual t) ≤
            Cr * spatialHolderHalfNorm 1 (slabTimeJet 0 T i RV t) + Ct q depth * (Λ ^ ((2 : ℤ) - depth) * M^2) := by
  classical
  let ψ := dyadicMultiplierCutoff
  have hp : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0 := fun ξ hξ => dyadicMultiplierCutoff_zero ξ hξ.le
  choose A hA hStress using fun d : {d : ℕ // 2 ≤ d} =>
    exists_terminalCutoffStress_holder hp dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit d.val d.property
  let Ac (d : ℕ) := if hd : 2 ≤ d then A ⟨d,hd⟩ else 0
  have hAc d : 0 ≤ Ac d := by
    unfold Ac
    split
    · exact hA _
    · exact le_rfl
  let Cproj := 2 * Real.sqrt 2 * ‖endpointStrongSpatialLeray‖
  let Cr := Cproj * (1 + terminalCutoffTailCost 1)
  let Ct (q depth : ℕ) := Cproj * (2 : ℝ)^q * Ac depth
  have hCproj : 0 ≤ Cproj := by dsimp [Cproj]; positivity
  have hC1 : 0 ≤ 1 + terminalCutoffTailCost 1 := add_nonneg zero_le_one (terminalCutoffTailCost_nonneg 1)
  refine ⟨Cr, Ct, mul_nonneg hCproj hC1, fun q d => mul_nonneg (mul_nonneg hCproj (by positivity)) (hAc d), ?_⟩
  intro T Λ V RV s hT hΛ hV hRV hVper hRVper q i depth hi hd t ht M hVrate
  obtain ⟨g, hg⟩ := exists_continuousTorusTimeJets hT hV hVper
  obtain ⟨gR, hgR⟩ := exists_continuousTorusTimeJets hT hRV hRVper
  have hRrep : (fun x => gR i t (toUnitTorus x)) = slabTimeJet 0 T i RV t := funext (hgR i t ht)
  have hVrep j : (fun x => g j t (toUnitTorus x)) = slabTimeJet 0 T j V t := funext (hg j t ht)
  have hG j : SpatialHolderHalf depth (fun x => g j t (toUnitTorus x)) := by
    rw [hVrep]
    exact spatialHolderHalf_of_contDiff_periodic (slabTimeJet_slice_smooth hT hV j ht) (slabTimeJet_periodic hVper j ht) _
  have hGR : SpatialHolderHalf 1 (fun x => gR i t (toUnitTorus x)) := by
    rw [hRrep]
    exact spatialHolderHalf_of_contDiff_periodic (slabTimeJet_slice_smooth hT hRV i ht) (slabTimeJet_periodic hRVper i ht) _
  let Z j := momentumTensorDivergence ∘ fderiv ℝ (terminalCutoffStress ψ Λ (g j t) (g (i - j) t))
  let L := terminalCutoffVector ψ Λ (gR i t)
  let τ := Λ ^ ((2 : ℤ) - depth)
  let input : Vec3 → Vec3 := L + ∑ j ∈ Finset.range (i + 1), i.choose j • Z j
  have hL := terminalCutoffVector_holder hp dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit hΛ (gR i t) hGR
  have hZ j : SpatialHolderHalf 1 (Z j) ∧
      spatialHolderHalfNorm 1 (Z j) ≤ Ac depth * τ *
        spatialHolderHalfNorm depth (slabTimeJet 0 T j V t) *
        spatialHolderHalfNorm depth (slabTimeJet 0 T (i - j) V t) := by
    simpa only [Z, Ac, dite_eq_left hd, τ, hVrep] using
      hStress ⟨depth,hd⟩ hΛ (g j t) (g (i - j) t) (hG j) (hG (i - j))
  have hZrate (j : ℕ) (hj : j ≤ i) : spatialHolderHalfNorm 1 (Z j) ≤ Ac depth * τ * M * M := by
    have h₁ : 0 ≤ spatialHolderHalfNorm depth (slabTimeJet 0 T j V t) := by
      rw [← hVrep j]
      exact (norm_nonneg _).trans (norm_iteratedFDeriv_le_spatialHolderHalfNorm (hG j) (Nat.zero_le _) 0)
    have h₂ : 0 ≤ spatialHolderHalfNorm depth (slabTimeJet 0 T (i-j) V t) := by
      rw [← hVrep (i-j)]
      exact (norm_nonneg _).trans (norm_iteratedFDeriv_le_spatialHolderHalfNorm (hG (i-j)) (Nat.zero_le _) 0)
    have hM := h₁.trans (hVrate j hj)
    have hF : 0 ≤ Ac depth * τ := mul_nonneg (hAc depth) (zpow_nonneg hΛ.le _)
    exact (hZ j).2.trans (mul_le_mul (mul_le_mul_of_nonneg_left (hVrate j hj) hF)
      (hVrate (i-j) (Nat.sub_le _ _)) h₂ (mul_nonneg hF hM))
  have hZsum := terminal_spatialHolderHalf_sum (Finset.range (i + 1))
    (f := fun j => i.choose j • Z j) (fun j _ => (terminal_spatialHolderHalf_nsmul (hZ j).1 (i.choose j)).1)
  have hZsumN : spatialHolderHalfNorm 1 (∑ j ∈ Finset.range (i + 1), i.choose j • Z j) ≤
      (2 : ℝ)^q * Ac depth * (τ * M^2) := by
    refine hZsum.2.trans ?_
    calc
      _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (Ac depth * τ * M * M) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (terminal_spatialHolderHalf_nsmul (hZ j).1 (i.choose j)).2.trans
          (mul_le_mul_of_nonneg_left (hZrate j (Finset.mem_range_succ_iff.mp hj)) (by positivity))
      _ = (2 : ℝ)^i * (Ac depth * τ * M * M) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose i
      _ ≤ (2 : ℝ)^q * (Ac depth * τ * M * M) := by
        apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi)
        have hF : 0 ≤ Ac depth * τ := mul_nonneg (hAc depth) (zpow_nonneg hΛ.le _)
        rw [mul_assoc (Ac depth * τ), ← sq]
        exact mul_nonneg hF (sq_nonneg _)
      _ = _ := by ring
  have hP : SpatiallyPeriodic input := by
    intro n x
    have hx : toUnitTorus (x + latticeVector n) = toUnitTorus x := (toUnitTorus_eq_iff _ _).mpr ⟨n,rfl⟩
    have hZj j : Z j (x + latticeVector n) = Z j x := by
      unfold Z Function.comp
      rw [(terminalCutoffStress_periodic ψ Λ _ _).fderiv (terminalCutoffStress_differentiable ψ Λ _ _) n x]
    simp only [input, L, terminalCutoffVector, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, hx, hZj]
  have hInput := spatialHolderHalf_add_exact hL.1 hZsum.1
  have hRes : slabTimeJet 0 T i s.residual t = periodicLerayHolderLift input := by
    rw [s.slabTimeJet_residual_eq hT hV hRV g gR hg hgR i ht, terminalCutoffStress_div_sum]
  rw [hRes]
  obtain ⟨hS, hN⟩ := periodicLerayHolderLift_holder_one input hP hInput.1
  refine ⟨hS, hN.trans ?_⟩
  change Cproj * spatialHolderHalfNorm 1 input ≤ _
  have hLN : spatialHolderHalfNorm 1 L ≤ (1 + terminalCutoffTailCost 1) *
      spatialHolderHalfNorm 1 (slabTimeJet 0 T i RV t) := by
    simpa only [L, terminalCutoffTailCost, hRrep] using hL.2
  exact (mul_le_mul_of_nonneg_left (hInput.2.trans (add_le_add hLN hZsumN)) hCproj).trans_eq
    (by dsimp only [Cr, Ct]; ring)

/-- Cutoff of the low-order uncut velocity jet has the exponent in
the auxiliary time-bounds lemma. -/
theorem TruncatedChildStage.slabTimeJet_cutoffVelocity_rate {T freq : ℝ} {V RV : Velocity}
    (s : TruncatedChildStage T (freq ^ (5 : ℕ)) dyadicMultiplierCutoff V RV) (hT : 0 < T)
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Slab(T)))
    (hVper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (V t))
    {i : ℕ} {t exponent : ℝ} (ht : t ∈ Icc 0 T) (hf : 2 ≤ freq)
    (hCost : 1 + terminalCutoffTailCost 0 ≤ freq)
    (hSize : spatialHolderHalfNorm 0 (slabTimeJet 0 T i V t) ≤ freq ^ (2 + exponent)) (x : Vec3) :
    ‖slabTimeJet 0 T i s.velocity t x‖ ≤ freq ^ (exponent + 3) := by
  obtain ⟨g, hg⟩ := exists_continuousTorusTimeJets hT hV hVper
  have hrep : (fun x => g i t (toUnitTorus x)) = slabTimeJet 0 T i V t := funext (hg i t ht)
  have hG : SpatialHolderHalf 0 (fun x => g i t (toUnitTorus x)) := by
    rw [hrep]
    exact spatialHolderHalf_of_contDiff_periodic (slabTimeJet_slice_smooth hT hV i ht)
      (slabTimeJet_periodic hVper i ht) _
  have hp := terminalCutoffVector_holder (fun ξ hξ => dyadicMultiplierCutoff_zero ξ hξ.le)
    dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit (pow_pos (zero_lt_two.trans_le hf) (5 : ℕ)) (g i t) hG
  rw [s.slabTimeJet_velocity hT hV g hg i ht x]
  have hn := norm_apply_le_spatialHolderHalfNorm_zero hp.1 x
  have hcut : spatialHolderHalfNorm 0 (terminalCutoffVector dyadicMultiplierCutoff (freq ^ (5 : ℕ)) (g i t)) ≤
      (1 + terminalCutoffTailCost 0) * spatialHolderHalfNorm 0 (slabTimeJet 0 T i V t) := by
    simpa only [terminalCutoffTailCost, hrep] using hp.2
  exact (hn.trans hcut).trans
    ((mul_le_mul_of_nonneg_left hSize (add_nonneg zero_le_one (terminalCutoffTailCost_nonneg 0))).trans
      (terminalTime_cutoff_velocity_rate hf hCost))

/-- The raw differentiated spatial residual estimate, at the exact
scheduled depth and radius, implies the required pointwise rate. -/
theorem slabTimeJet_cutoffResidual_rate {T freq next Cr Ct exponent : ℝ} {k i : ℕ} {RV R : Velocity}
    {t : ℝ} (hf : 2 ≤ freq) (hExp : 0 ≤ exponent) (hNext : next = freq ^ k)
    (hk : 16 + 2 * exponent ≤ (k : ℝ))
    (hCr : 0 ≤ Cr) (hCrF : Cr ≤ freq) (hCtF : Ct ≤ freq)
    (hApprox : spatialHolderHalfNorm 1 (slabTimeJet 0 T i RV t) ≤ freq ^ exponent * next ^ (-4 : ℝ))
    (hR : SpatialHolderHalf 1 (slabTimeJet 0 T i R t) ∧
      spatialHolderHalfNorm 1 (slabTimeJet 0 T i R t) ≤
        Cr * spatialHolderHalfNorm 1 (slabTimeJet 0 T i RV t) +
          Ct * ((freq ^ (5 : ℕ)) ^ ((2 : ℤ) - (6 * k : ℕ)) *
            (freq ^ (2 * (((6 * k : ℕ) : ℝ) + 1) + exponent)) ^ (2 : ℕ)))
    (x : Vec3) : ‖slabTimeJet 0 T i R t x‖ ≤ next ^ (-5 / 2 : ℝ) := by
  have hn := norm_iteratedFDeriv_le_spatialHolderHalfNorm hR.1 (show (0 : ℕ) ≤ 1 by decide) x
  rw [norm_iteratedFDeriv_zero] at hn
  exact (hn.trans hR.2).trans
    ((add_le_add (mul_le_mul_of_nonneg_left hApprox hCr) le_rfl).trans
      (terminalTime_cutoff_residual_rate hf hExp hCtF hCrF hNext hk))

end

end TorusEuler
