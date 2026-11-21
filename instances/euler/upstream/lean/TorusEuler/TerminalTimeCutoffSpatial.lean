import TorusEuler.TruncatedChildStage

/-! Spatial cutoff and stress estimates for the independently differentiated factors. -/

open Set UnitAddTorus
open scoped ContDiff SchwartzMap

namespace TorusEuler

noncomputable section

set_option maxHeartbeats 1600000

local notation "Labels" => UnitAddTorus (Fin 3)

def terminalCutoffVector (ψ : Vec3 → ℝ) (Λ : ℝ) (g : C(Labels, Vec3)) : Vec3 → Vec3 :=
  fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)

def cutoffMomentumTensor (g h : C(Labels, Vec3)) : C(Labels, MomentumTensor) :=
  ⟨fun z => momentumTensor (g z) (h z), (momentumTensor.continuous.comp g.continuous).clm_apply h.continuous⟩

/-- The unprojected quadratic cutoff stress with independent left and right inputs. -/
def terminalCutoffStress (ψ : Vec3 → ℝ) (Λ : ℝ) (g h : C(Labels, Vec3)) : Vec3 → MomentumTensor :=
  fun x => momentumTensor (terminalCutoffVector ψ Λ g x) (terminalCutoffVector ψ Λ h x) -
    momentumTensorFourierCutoff ψ Λ (cutoffMomentumTensor g h) (toUnitTorus x)

private theorem cutoffHolderConstant_nonneg {K : 𝓢(Vec3, ℂ)} (m : ℕ) :
    0 ≤ cutoffHolderTailUniformConstant K m := by
  unfold cutoffHolderTailUniformConstant cutoffKernelAbsoluteMoment
  positivity

private theorem cutoffHolder_mono {V : Vec3 → Vec3} {m depth : ℕ}
    (hV : SpatialHolderHalf depth V) (hm : m ≤ depth) :
    SpatialHolderHalf m V ∧ spatialHolderHalfNorm m V ≤ spatialHolderHalfNorm depth V := by
  refine ⟨⟨hV.1.of_le (by exact_mod_cast hm), fun j hj => hV.2 j (hj.trans hm)⟩, ?_⟩
  unfold spatialHolderHalfNorm
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hm))
  intro j hj _
  have hd : j ≤ depth := Finset.mem_range_succ_iff.mp hj
  have hS := (norm_nonneg _).trans (norm_le_spatialSupNorm (hV.2 j hd).1 0)
  have hQ := le_ciSup (hV.2 j hd).2 ((0 : Vec3),(0 : Vec3))
  have : 0 ≤ spatialHolderHalfSeminorm (iteratedFDeriv ℝ j V) := by
    rw [show spatialHolderHalfQuotient (iteratedFDeriv ℝ j V) (0,0) = 0 by simp [spatialHolderHalfQuotient]] at hQ
    exact hQ
  exact add_nonneg hS this

theorem terminalCutoffVector_holder {ψ : Vec3 → ℝ}
    (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 0 < Λ)
    (g : C(Labels, Vec3)) {m : ℕ} (hg : SpatialHolderHalf m (fun x => g (toUnitTorus x))) :
    SpatialHolderHalf m (terminalCutoffVector ψ Λ g) ∧
      spatialHolderHalfNorm m (terminalCutoffVector ψ Λ g) ≤
        (1 + cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) m) *
          spatialHolderHalfNorm m (fun x => g (toUnitTorus x)) := by
  have htail := spatialHolderHalfNorm_cutoffVelocityDifference hψ hs hunit hΛ g le_rfl hg
  dsimp only at htail
  rw [sub_self, zpow_zero, mul_one] at htail
  have hsum := spatialHolderHalf_add_exact htail.1 hg
  rw [sub_add_cancel] at hsum
  refine ⟨hsum.1, hsum.2.trans ((add_le_add htail.2 le_rfl).trans_eq ?_)⟩
  ring

/-- The two-frequency input estimate for each Leibniz term of the differentiated cutoff stress. -/
theorem exists_terminalCutoffStress_holder {ψ : Vec3 → ℝ}
    (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) (depth : ℕ) (hd : 2 ≤ depth) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Λ : ℝ}, 0 < Λ → ∀ g h : C(Labels, Vec3),
      SpatialHolderHalf depth (fun x => g (toUnitTorus x)) →
      SpatialHolderHalf depth (fun x => h (toUnitTorus x)) →
      let d := momentumTensorDivergence ∘ fderiv ℝ (terminalCutoffStress ψ Λ g h)
      SpatialHolderHalf 1 d ∧ spatialHolderHalfNorm 1 d ≤
        A * Λ ^ ((2 : ℤ) - depth) * spatialHolderHalfNorm depth (fun x => g (toUnitTorus x)) *
          spatialHolderHalfNorm depth (fun x => h (toUnitTorus x)) := by
  let C m := cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) m
  let B := momentumTensor
  let D := momentumTensorDivergence
  let J : MomentumTensor →L[ℝ] (Fin 3 → ComplexEuclideanVec3) :=
    ContinuousLinearMap.piMap fun _ => periodicComplexifyVector
  let R : (Fin 3 → ComplexEuclideanVec3) →L[ℝ] MomentumTensor :=
    ContinuousLinearMap.piMap fun _ => periodicRealPartVector
  let c m := 3 * ((m : ℕ) + 1 : ℝ) * ‖B‖ * (2 : ℝ)^m
  let A := ‖D‖ * 36 * (c 2 * C depth * (1 + C 2) + c 2 * C depth + ‖R‖ * ‖J‖ * C depth * c depth)
  have hC m : 0 ≤ C m := cutoffHolderConstant_nonneg m
  have hc m : 0 ≤ c m := by dsimp only [c]; positivity
  have hC2 : 0 ≤ 1 + C 2 := add_nonneg zero_le_one (hC 2)
  refine ⟨A, ?_, ?_⟩
  · dsimp only [A]
    have hterm₁ := mul_nonneg (mul_nonneg (hc 2) (hC depth)) hC2
    have hterm₂ := mul_nonneg (hc 2) (hC depth)
    have hterm₃ := mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg R) (norm_nonneg J)) (hC depth)) (hc depth)
    exact mul_nonneg (by positivity : 0 ≤ ‖D‖ * (36 : ℝ)) (add_nonneg (add_nonneg hterm₁ hterm₂) hterm₃)
  intro Λ hΛ g h hg hh d
  let V := fun x => g (toUnitTorus x)
  let W := fun x => h (toUnitTorus x)
  let SV := terminalCutoffVector ψ Λ g
  let SW := terminalCutoffVector ψ Λ h
  let τ := Λ ^ ((2 : ℤ) - depth)
  let M := spatialHolderHalfNorm depth V
  let N := spatialHolderHalfNorm depth W
  let gVW := cutoffMomentumTensor g h
  let a := fun x => B ((SV - V) x) (SW x)
  let b := fun x => B (V x) ((SW - W) x)
  let e := (fun x => gVW (toUnitTorus x)) - (fun x => momentumTensorFourierCutoff ψ Λ gVW (toUnitTorus x))
  have hStress : terminalCutoffStress ψ Λ g h = a + b + e := by
    funext x
    simp only [terminalCutoffStress, a, b, e, V, W, SV, SW, gVW, B, Pi.add_apply, Pi.sub_apply,
      cutoffMomentumTensor, ContinuousMap.coe_mk, map_sub, sub_apply]
    abel
  have hv := spatialHolderHalfNorm_cutoffVelocityDifference hψ hs hunit hΛ g hd hg
  have hw := spatialHolderHalfNorm_cutoffVelocityDifference hψ hs hunit hΛ h hd hh
  have hV₂ := cutoffHolder_mono hg hd
  have hW₂ := cutoffHolder_mono hh hd
  have hSW := terminalCutoffVector_holder hψ hs hunit hΛ h hW₂.1
  have hSWN := hSW.2.trans (mul_le_mul_of_nonneg_left hW₂.2 hC2)
  have hProduct := spatialHolderHalf_bilinear B hg hh
  have hRJ (q : MomentumTensor) : R (J q) = q :=
    funext fun k => periodicRealPartVector_complexifyVector (q k)
  have he := spatialHolderHalfNorm_realTensorCutoffTail J R hRJ hψ hs hunit hΛ gVW hd hProduct.1
  have ha := spatialHolderHalf_bilinear B hv.1 hSW.1
  have hb := spatialHolderHalf_bilinear B hV₂.1 hw.1
  change SpatialHolderHalf 2 a ∧ _ at ha
  change SpatialHolderHalf 2 b ∧ _ at hb
  change SpatialHolderHalf 2 e ∧ _ at he
  have hM : 0 ≤ M := (norm_nonneg _).trans (norm_iteratedFDeriv_le_spatialHolderHalfNorm hg (Nat.zero_le _) 0)
  have hN : 0 ≤ N := (norm_nonneg _).trans (norm_iteratedFDeriv_le_spatialHolderHalfNorm hh (Nat.zero_le _) 0)
  have hτ : 0 ≤ τ := zpow_nonneg hΛ.le _
  have hvN : spatialHolderHalfNorm 2 (SV - V) ≤ C depth * τ * M := by
    change spatialHolderHalfNorm 2 ((fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)) - V) ≤ _
    simpa only [Nat.cast_ofNat] using hv.2
  have hwN : spatialHolderHalfNorm 2 (SW - W) ≤ C depth * τ * N := by
    change spatialHolderHalfNorm 2 ((fun x => realVectorFourierCutoff ψ Λ h (toUnitTorus x)) - W) ≤ _
    simpa only [Nat.cast_ofNat] using hw.2
  have hA₂ : spatialHolderHalfNorm 2 a ≤ c 2 * (C depth * τ * M) * ((1 + C 2) * N) := by
    refine ha.2.trans ?_
    have hS₀ : 0 ≤ spatialHolderHalfNorm 2 SW :=
      (norm_nonneg _).trans (norm_iteratedFDeriv_le_spatialHolderHalfNorm hSW.1 (Nat.zero_le _) 0)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hvN (hc 2)) hSWN hS₀
      (mul_nonneg (hc 2) (mul_nonneg (mul_nonneg (hC depth) hτ) hM))
  have hB₂ : spatialHolderHalfNorm 2 b ≤ c 2 * M * (C depth * τ * N) := by
    refine hb.2.trans ?_
    have hW₀ : 0 ≤ spatialHolderHalfNorm 2 (SW - W) :=
      (norm_nonneg _).trans (norm_iteratedFDeriv_le_spatialHolderHalfNorm hw.1 (Nat.zero_le _) 0)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hV₂.2 (hc 2)) hwN hW₀ (mul_nonneg (hc 2) hM)
  have hFactor : 0 ≤ ‖R‖ * ‖J‖ * C depth * τ :=
    mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg R) (norm_nonneg J)) (hC depth)) hτ
  have hE₂ : spatialHolderHalfNorm 2 e ≤ ‖R‖ * ‖J‖ * C depth * τ * (c depth * M * N) :=
    (by simpa only [Nat.cast_ofNat, e, momentumTensorFourierCutoff, J, R, C, τ] using he.2 : spatialHolderHalfNorm 2 e ≤
      ‖R‖ * ‖J‖ * C depth * τ * spatialHolderHalfNorm depth (fun x => gVW (toUnitTorus x))).trans
        (mul_le_mul_of_nonneg_left hProduct.2 hFactor)
  have hAB := spatialHolderHalf_add ha.1 hb.1
  have hABE := spatialHolderHalf_add hAB.1 he.1
  norm_num at hAB hABE
  have hd' := spatialHolderHalf_contraction_fderiv D hABE.1
  dsimp only [d]
  rw [hStress]
  refine ⟨hd'.1, hd'.2.trans ?_⟩
  change ‖D‖ * spatialHolderHalfNorm 2 (a + b + e) ≤ A * τ * M * N
  have hVec : spatialHolderHalfNorm 2 (a + b + e) ≤
      36 * (c 2 * C depth * (1 + C 2) + c 2 * C depth + ‖R‖ * ‖J‖ * C depth * c depth) * τ * M * N := by
    refine hABE.2.trans ?_
    have h₁ := add_le_add (hAB.2.trans (mul_le_mul_of_nonneg_left (add_le_add hA₂ hB₂) (by norm_num))) hE₂
    refine (mul_le_mul_of_nonneg_left h₁ (by norm_num)).trans ?_
    have hnE : 0 ≤ ‖R‖ * ‖J‖ * C depth * τ * (c depth * M * N) :=
      mul_nonneg hFactor (mul_nonneg (mul_nonneg (hc depth) hM) hN)
    -- Every stress component is bounded with the largest triangle constant.
    have hsix : (6 : ℝ) * (‖R‖ * ‖J‖ * C depth * τ * (c depth * M * N)) ≤
        36 * (‖R‖ * ‖J‖ * C depth * τ * (c depth * M * N)) := by
      exact mul_le_mul_of_nonneg_right (by norm_num) hnE
    let shared := 36 * (c 2 * (C depth * τ * M) * ((1 + C 2) * N) + c 2 * M * (C depth * τ * N))
    convert add_le_add (le_refl shared) hsix using 1 <;> dsimp only [shared, τ, M, N] <;> ring
  exact (mul_le_mul_of_nonneg_left hVec (norm_nonneg D)).trans_eq (by dsimp only [A]; ring)

end

end TorusEuler
