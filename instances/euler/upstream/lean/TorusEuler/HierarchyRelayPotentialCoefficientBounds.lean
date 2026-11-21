import TorusEuler.HierarchyLinearRelayBounds
import TorusEuler.WaveCompletionBounds

/-! The normalized potential and pressure coefficients in the wave relay
have finite label–phase word budgets with one fixed parent exponent. -/

open ContinuousLinearMap
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

universe u

def relayCrossMap : Vec3 →L[ℝ] (Vec3 →L[ℝ] Vec3) := by
  let L : Vec3 →ₗ[ℝ] (Vec3 →L[ℝ] Vec3) :=
    { toFun := cross3Left
      map_add' := by
        intro v w
        ext x : 1
        apply WithLp.ofLp_injective
        simp only [_root_.add_apply, cross3Left_apply, cross3, WithLp.ofLp_add,
          WithLp.ofLp_toLp, map_add, LinearMap.add_apply]
      map_smul' := by
        intro c v
        ext x : 1
        apply WithLp.ofLp_injective
        simp only [RingHom.id_apply, _root_.smul_apply, cross3Left_apply, cross3,
          WithLp.ofLp_smul, WithLp.ofLp_toLp, map_smul, LinearMap.smul_apply] }
  exact L.mkContinuous 1 fun v => by
    rw [one_mul]
    exact opNorm_le_bound _ (norm_nonneg v) (norm_cross3_le v)

theorem relayCrossMap_apply (v : Vec3) : relayCrossMap v = cross3Left v := rfl

private theorem norm_relayCrossMap_le : ‖relayCrossMap‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  rw [relayCrossMap_apply, one_mul]
  exact opNorm_le_bound _ (norm_nonneg v) (norm_cross3_le v)

private theorem norm_evalRelayMap_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ‖(ContinuousLinearMap.apply ℝ F : E →L[ℝ] (E →L[ℝ] F) →L[ℝ] F).flip‖ ≤ 1 := by
  simp only [ContinuousLinearMap.opNorm_flip, ContinuousLinearMap.apply]
  apply opNorm_le_bound _ zero_le_one
  intro v
  simp only [ContinuousLinearMap.coe_id', id, one_mul]
  rfl

private structure RelayLabelJets {X : Type u} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : ℝ) (n p : ℕ) (C : ℝ) (f : X → Vec3 → E) : Prop where
  smooth : ∀ t, ContDiff ℝ ∞ (f t)
  nonneg : 0 ≤ C
  le : ∀ t j, j ≤ n → ∀ a, ‖iteratedFDeriv ℝ j (f t) a‖ ≤ C * D ^ (16 * j + p)

namespace RelayLabelJets

variable {X : Type u} {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {D C B : ℝ} {n p q : ℕ} {f : X → Vec3 → E} {g : X → Vec3 → F}

protected theorem map (hf : RelayLabelJets D n p C f) (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) :
    RelayLabelJets D n p C (fun t a => L (f t a)) := by
  refine ⟨fun t => L.contDiff.comp (hf.smooth t), hf.nonneg, ?_⟩
  intro t j hj a
  exact (L.norm_iteratedFDeriv_comp_left (hf.smooth t).contDiffAt (by simp)).trans
    ((mul_le_of_le_one_left (norm_nonneg _) hL).trans (hf.le t j hj a))

protected theorem bilinear (hf : RelayLabelJets D n p C f) (hg : RelayLabelJets D n q B g)
    (L : E →L[ℝ] F →L[ℝ] G) (hL : ‖L‖ ≤ 1) (hD : 1 ≤ D) :
    RelayLabelJets D n (p + q) ((2 : ℝ) ^ n * (C * B)) (fun t a => L (f t a) (g t a)) := by
  refine ⟨fun t => (L.contDiff.comp (hf.smooth t)).clm_apply (hg.smooth t),
    mul_nonneg (by positivity) (mul_nonneg hf.nonneg hg.nonneg), ?_⟩
  intro t j hj a
  have hb := norm_iteratedFDeriv_bilinear_scaled_le L hL
    ((hf.smooth t).of_le (by simp : (j : ℕ∞ω) ≤ ∞))
    ((hg.smooth t).of_le (by simp : (j : ℕ∞ω) ≤ ∞)) a
    (p := 16) (fun i hi => hf.le t i (hi.trans hj) a) (fun i hi => hg.le t i (hi.trans hj) a)
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
  refine hb.trans ?_
  rw [add_assoc]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpow (mul_nonneg hf.nonneg hg.nonneg))
    (pow_nonneg (zero_le_one.trans hD) _)

protected theorem add (hf : RelayLabelJets D n p C f) {g : X → Vec3 → E}
    (hg : RelayLabelJets D n p B g) :
    RelayLabelJets D n p (C + B) (fun t a => f t a + g t a) := by
  refine ⟨fun t => (hf.smooth t).add (hg.smooth t), add_nonneg hf.nonneg hg.nonneg, ?_⟩
  intro t j hj a
  rw [fun_iteratedFDeriv_add_apply ((hf.smooth t).contDiffAt.of_le (by simp))
    ((hg.smooth t).contDiffAt.of_le (by simp))]
  exact (norm_add_le _ _).trans <| by simpa only [add_mul] using add_le_add (hf.le t j hj a) (hg.le t j hj a)

protected theorem sub (hf : RelayLabelJets D n p C f) {g : X → Vec3 → E}
    (hg : RelayLabelJets D n p B g) :
    RelayLabelJets D n p (C + B) (fun t a => f t a - g t a) := by
  refine ⟨fun t => (hf.smooth t).sub (hg.smooth t), add_nonneg hf.nonneg hg.nonneg, ?_⟩
  intro t j hj a
  rw [fun_iteratedFDeriv_sub_apply ((hf.smooth t).contDiffAt.of_le (by simp))
    ((hg.smooth t).contDiffAt.of_le (by simp))]
  exact (norm_sub_le _ _).trans <| by simpa only [add_mul] using add_le_add (hf.le t j hj a) (hg.le t j hj a)

protected theorem const_smul (hf : RelayLabelJets D n p C f) (s : ℝ) :
    RelayLabelJets D n p (‖s‖ * C) (fun t a => s • f t a) := by
  let L : E →L[ℝ] E := s • ContinuousLinearMap.id ℝ E
  refine ⟨fun t => (hf.smooth t).const_smul s, mul_nonneg (norm_nonneg _) hf.nonneg, ?_⟩
  intro t j hj a
  have hL : ‖L‖ ≤ ‖s‖ := by
    change ‖s • ContinuousLinearMap.id ℝ E‖ ≤ ‖s‖
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_id_le (𝕜 := ℝ) (E := E))
  calc
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ j (f t) a‖ :=
      L.norm_iteratedFDeriv_comp_left (hf.smooth t).contDiffAt (by simp)
    _ ≤ ‖s‖ * (C * D ^ (16 * j + p)) :=
      mul_le_mul hL (hf.le t j hj a) (norm_nonneg _) (norm_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

protected theorem mono_power (hf : RelayLabelJets D n p C f) (hD : 1 ≤ D) (hpq : p ≤ q) :
    RelayLabelJets D n q C f := by
  refine ⟨hf.smooth, hf.nonneg, fun t j hj a => (hf.le t j hj a).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) hf.nonneg

protected theorem coefficients (hf : RelayLabelJets D n p C f)
    {ℓ h K : ℝ} (hℓ : 0 ≤ ℓ) (hD : 1 ≤ D) (hscale : ℓ * D ^ (16 : ℕ) ≤ 1)
    (hK : C ≤ K) :
    HierarchyRelayCoefficientJets ℓ h n (K * D ^ p) f := by
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  refine ⟨fun t => (hf.smooth t).comp contDiff_fst,
    hierarchyRelayWordBound_of_phaseIndependent hℓ
      (mul_nonneg (hf.nonneg.trans hK) (pow_nonneg hD₀ _)) hf.smooth ?_⟩
  intro t j hj a
  calc
    _ ≤ ℓ ^ j * (C * D ^ (16 * j + p)) :=
      mul_le_mul_of_nonneg_left (hf.le t j hj a) (pow_nonneg hℓ _)
    _ = (ℓ * D ^ (16 : ℕ)) ^ j * (C * D ^ p) := by rw [mul_pow, ← pow_mul, pow_add]; ring
    _ ≤ C * D ^ p := mul_le_of_le_one_left (mul_nonneg hf.nonneg (pow_nonneg hD₀ _))
      (pow_le_one₀ (mul_nonneg hℓ (pow_nonneg hD₀ _)) hscale)
    _ ≤ _ := mul_le_mul_of_nonneg_right hK (pow_nonneg hD₀ _)

end RelayLabelJets

set_option maxHeartbeats 3000000 in
/-- The four normalized potential and pressure coefficients have a common
finite mixed-derivative budget. The exponent fifteen is independent of
the derivative order and of the time set. -/
theorem exists_hierarchyRelayPotentialCoefficientBounds
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) :
    ∃ K : ℕ → ℝ, (∀ n, 0 ≤ K n) ∧
      ∀ {X : Type u} {ℓ h D : ℝ}, 0 ≤ ℓ → 1 ≤ D → ℓ * D ^ (16 : ℕ) ≤ 1 →
        ∀ (n : ℕ) (M : X → Vec3 → (Vec3 →L[ℝ] Vec3)) (κ : X → Vec3 → Vec3),
          (∀ t, ContDiff ℝ ∞ (M t)) → (∀ t, ContDiff ℝ ∞ (κ t)) →
          (∀ t a, κ t a ≠ 0) →
          (∀ t j, j ≤ n → ∀ a, ‖iteratedFDeriv ℝ j (M t) a‖ ≤ C j * D ^ (6 * j + 1)) →
          (∀ t j, j ≤ n → ∀ a, ‖iteratedFDeriv ℝ j (κ t) a‖ ≤ C j * D ^ (7 * j + 2)) →
          (∀ t j, j ≤ n → ∀ a,
            ‖iteratedFDeriv ℝ j (fun b => (‖κ t b‖ ^ 2)⁻¹) a‖ ≤ C j * D ^ (16 * j + 4)) →
          HierarchyRelayCoefficientJets ℓ h n (K n * D ^ 15)
            (fun t a => hierarchyRelayPotentialCoefficient (κ t a)) ∧
          HierarchyRelayCoefficientJets ℓ h n (K n * D ^ 15)
            (fun t a => hierarchyRelayTimeAmplitudeCoefficient (M t a) (κ t a)) ∧
          HierarchyRelayCoefficientJets ℓ h n (K n * D ^ 15)
            (fun t a => hierarchyRelayPressureAmplitudeCoefficient (M t a) (κ t a)) ∧
          HierarchyRelayCoefficientJets ℓ h n (K n * D ^ 15)
            (fun t a => hierarchyRelayPressureSourceCoefficient (κ t a)) := by
  let S (n : ℕ) := ∑ j ∈ Finset.range (n + 1), C j
  let L (n : ℕ) : ℝ := 2 ^ n
  let K (n : ℕ) := 2 * L n * S n ^ 2 + 4 * L n ^ 2 * S n ^ 3 + 2 * L n ^ 5 * S n ^ 6
  have hS (n : ℕ) : 0 ≤ S n := Finset.sum_nonneg fun j _ => hC j
  have hL (n : ℕ) : 0 ≤ L n := by dsimp only [L]; positivity
  have hSK (n j : ℕ) (hj : j ≤ n) : C j ≤ S n :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_range.mpr (by omega))
  refine ⟨K, fun n => by have := hS n; have := hL n; dsimp only [K]; positivity, ?_⟩
  intro X ℓ h D hℓ hD hscale n M κ hMs hκs hκnz hM hκ hInv
  let V := Vec3 →L[ℝ] Vec3
  let W := Vec3 →L[ℝ] ℝ
  let T : V →L[ℝ] V :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)).toContinuousLinearEquiv.toContinuousLinearMap
  let I : Vec3 →L[ℝ] W := innerSL ℝ
  let evV : V →L[ℝ] Vec3 →L[ℝ] Vec3 := (ContinuousLinearMap.apply ℝ Vec3).flip
  let evW : W →L[ℝ] Vec3 →L[ℝ] ℝ := (ContinuousLinearMap.apply ℝ ℝ).flip
  let invSquare (t : X) (a : Vec3) := (‖κ t a‖ ^ 2)⁻¹
  let A := S n
  let B := L n
  have hA : 0 ≤ A := hS n
  have hB : 0 ≤ B := hL n
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hT : ‖T‖ ≤ 1 := by
    refine opNorm_le_bound _ zero_le_one fun v => ?_
    rw [one_mul]
    exact le_of_eq (ContinuousLinearMap.adjoint.norm_map v)
  have hI : ‖I‖ ≤ 1 := norm_innerSL_le ℝ
  have hMJets : RelayLabelJets D n 1 A M := by
    refine ⟨hMs, hA, fun t j hj a => (hM t j hj a).trans ?_⟩
    exact mul_le_mul (hSK n j hj) (pow_le_pow_right₀ hD (by omega))
      (pow_nonneg hD₀ _) hA
  have hκJets : RelayLabelJets D n 2 A κ := by
    refine ⟨hκs, hA, fun t j hj a => (hκ t j hj a).trans ?_⟩
    exact mul_le_mul (hSK n j hj) (pow_le_pow_right₀ hD (by omega))
      (pow_nonneg hD₀ _) hA
  have hInvJets : RelayLabelJets D n 4 A invSquare := by
    refine ⟨fun t => ?_, hA, fun t j hj a => (hInv t j hj a).trans ?_⟩
    · change ContDiff ℝ ∞ (fun a => (‖κ t a‖ ^ 2)⁻¹)
      exact ((hκs t).norm_sq ℝ).inv
        (fun a => pow_ne_zero _ (norm_ne_zero_iff.mpr (hκnz t a)))
    · exact mul_le_mul_of_nonneg_right (hSK n j hj) (pow_nonneg hD₀ _)
  have hCross := hκJets.map relayCrossMap norm_relayCrossMap_le
  have hDot := hκJets.map I hI
  have hAdj := hMJets.map T hT
  have hκM := hMJets.bilinear hκJets evV norm_evalRelayMap_le hD
  have hκAdj := hAdj.bilinear hκJets evV norm_evalRelayMap_le hD
  have hFirst := hκAdj.map relayCrossMap norm_relayCrossMap_le
  have hSecond := hCross.bilinear hMJets (compL ℝ Vec3 Vec3 Vec3) (norm_compL_le _ _ _ _) hD
  have hCrossSum := hFirst.add hSecond
  have hTimeLinear := hInvJets.bilinear hCrossSum (lsmul ℝ ℝ) opNorm_lsmul_le hD
  have hDotM := hDot.bilinear hκM evW norm_evalRelayMap_le hD
  have hInvTwice := hInvJets.bilinear hInvJets (lsmul ℝ ℝ) opNorm_lsmul_le hD
  have hTimeScalar := hInvTwice.bilinear hDotM (lsmul ℝ ℝ) opNorm_lsmul_le hD
  have hTimeCubic := (hTimeScalar.bilinear hCross (lsmul ℝ ℝ) opNorm_lsmul_le hD).const_smul 2
  have hPressureLin := hDot.bilinear hMJets (compL ℝ Vec3 Vec3 ℝ) (norm_compL_le _ _ _ _) hD
  have hPot := (hInvJets.bilinear hCross (lsmul ℝ ℝ) opNorm_lsmul_le hD).const_smul (-1)
  have hPressureAmp := (hInvJets.bilinear hPressureLin (lsmul ℝ ℝ) opNorm_lsmul_le hD).const_smul (-2)
  have hPressureSrc := hInvJets.bilinear hDot (lsmul ℝ ℝ) opNorm_lsmul_le hD
  have hTime := ((hTimeLinear.mono_power (q := 15) hD (by decide)).sub hTimeCubic)
  have hPot' : RelayLabelJets D n 15 (B * A ^ 2) (fun t a => hierarchyRelayPotentialCoefficient (κ t a)) := by
    have h := hPot.mono_power (q := 15) hD (by decide)
    convert h using 1
    · dsimp only [B, L]; rw [Real.norm_eq_abs, abs_neg, abs_one]; ring
    · funext t a
      simp [hierarchyRelayPotentialCoefficient, invSquare, relayCrossMap_apply, smul_smul]
  have hTime' : RelayLabelJets D n 15 (2 * B ^ 2 * A ^ 3 + 2 * B ^ 5 * A ^ 6)
      (fun t a => hierarchyRelayTimeAmplitudeCoefficient (M t a) (κ t a)) := by
    convert hTime using 1
    · dsimp only [B, L]; rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; ring
    · funext t a
      simp only [hierarchyRelayTimeAmplitudeCoefficient, invSquare, relayCrossMap_apply,
        lsmul_apply, compL_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply,
        T, I, evV, evW, LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
        smul_smul, smul_eq_mul]
      congr 2
      change 2 * ⟪κ t a, M t a (κ t a)⟫_ℝ / (‖κ t a‖ ^ 2) ^ 2 =
        2 * ((‖κ t a‖ ^ 2)⁻¹ * (‖κ t a‖ ^ 2)⁻¹ * ⟪κ t a, M t a (κ t a)⟫_ℝ)
      rw [div_eq_mul_inv, ← inv_pow, pow_two]
      ring
  have hPressureAmp' : RelayLabelJets D n 15 (2 * B ^ 2 * A ^ 3)
      (fun t a => hierarchyRelayPressureAmplitudeCoefficient (M t a) (κ t a)) := by
    have h := hPressureAmp.mono_power (q := 15) hD (by decide)
    convert h using 1
    · dsimp only [B, L]; rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; ring
    · funext t a
      simp [hierarchyRelayPressureAmplitudeCoefficient, invSquare, I, smul_smul]
      rfl
  have hPressureSrc' : RelayLabelJets D n 15 (B * A ^ 2)
      (fun t a => hierarchyRelayPressureSourceCoefficient (κ t a)) := by
    have h := hPressureSrc.mono_power (q := 15) hD (by decide)
    convert h using 1
    · dsimp only [B, L]; ring
    · funext t a
      rfl
  have hP₁ : 0 ≤ B * A ^ 2 := by positivity
  have hP₂ : 0 ≤ 2 * B ^ 2 * A ^ 3 := by positivity
  have hP₃ : 0 ≤ 2 * B ^ 5 * A ^ 6 := by positivity
  have hPotK : B * A ^ 2 ≤ K n := by
    change B * A ^ 2 ≤ 2 * B * A ^ 2 + 4 * B ^ 2 * A ^ 3 + 2 * B ^ 5 * A ^ 6
    nlinarith only [hP₁, hP₂, hP₃]
  have hTimeK : 2 * B ^ 2 * A ^ 3 + 2 * B ^ 5 * A ^ 6 ≤ K n := by
    change _ ≤ 2 * B * A ^ 2 + 4 * B ^ 2 * A ^ 3 + 2 * B ^ 5 * A ^ 6
    nlinarith only [hP₁, hP₂]
  have hPressK : 2 * B ^ 2 * A ^ 3 ≤ K n := by
    change _ ≤ 2 * B * A ^ 2 + 4 * B ^ 2 * A ^ 3 + 2 * B ^ 5 * A ^ 6
    nlinarith only [hP₁, hP₂, hP₃]
  exact ⟨hPot'.coefficients hℓ hD hscale hPotK, hTime'.coefficients hℓ hD hscale hTimeK,
    hPressureAmp'.coefficients hℓ hD hscale hPressK, hPressureSrc'.coefficients hℓ hD hscale hPotK⟩

end

end TorusEuler
