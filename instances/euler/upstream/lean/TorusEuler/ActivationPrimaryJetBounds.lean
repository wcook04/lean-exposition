import TorusEuler.ParentSeedJetBudgets
import TorusEuler.SeedDerivativeBudgets
import TorusEuler.HierarchyLinearRelayBounds
import TorusEuler.HierarchyPhysicalVelocityBounds
import TorusEuler.FirstWaveDerivativeBudgets

/-! Weighted spatial derivatives of the actual later activation primary. -/

open ContinuousLinearMap Set
open scoped ContDiff BigOperators

namespace TorusEuler

noncomputable section

private def potentialCrossLinear : Vec3 →L[ℝ] (Vec3 →L[ℝ] Vec3) := by
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

private theorem norm_potentialCrossLinear_le : ‖potentialCrossLinear‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun v => ?_
  change ‖cross3Left v‖ ≤ 1 * ‖v‖
  rw [one_mul]
  exact opNorm_le_bound _ (norm_nonneg v) (norm_cross3_le v)

/-- The raw potential coefficient is smooth on a smooth nonvanishing covector field. -/
theorem contDiff_hierarchyRelayPotentialCoefficient
    {κ : Vec3 → Vec3} (hκ : ContDiff ℝ ∞ κ) (hκ₀ : ∀ a, κ a ≠ 0) :
    ContDiff ℝ ∞ (fun a => hierarchyRelayPotentialCoefficient (κ a)) := by
  change ContDiff ℝ ∞ (fun a => (-(‖κ a‖ ^ 2)⁻¹) • potentialCrossLinear (κ a))
  exact ((hκ.norm_sq ℝ).inv (fun a => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hκ₀ a)))).neg.smul
    (potentialCrossLinear.contDiff.comp hκ)

/-- The potential's coefficient has degree minus one in the covector. -/
theorem hierarchyRelayPotentialCoefficient_frequency_scale {freq : ℝ} (hf : 0 < freq)
    (k : Vec3) :
    hierarchyRelayPotentialCoefficient (freq • k) =
      freq⁻¹ • hierarchyRelayPotentialCoefficient k := by
  have hi : (‖freq • k‖ ^ 2)⁻¹ = freq⁻¹ ^ 2 * (‖k‖ ^ 2)⁻¹ := by
    simpa only [inv_inv, div_eq_mul_inv] using inv_sq_norm_inv_smul freq⁻¹ k
  have hc : cross3Left (freq • k) = freq • cross3Left k :=
    potentialCrossLinear.map_smul freq k
  rw [hierarchyRelayPotentialCoefficient, hierarchyRelayPotentialCoefficient, hi, hc,
    smul_smul, smul_smul]
  congr 1
  field_simp [hf.ne']

/-- The unnormalized potential operator retains one inverse frequency
after all radius-scaled derivatives in label and phase. -/
theorem phaseJetBound_scaledPhasePotentialCoefficient
    (N : ℕ) {κ : Vec3 → Vec3} {freq ℓ D C : ℝ}
    (hf : 0 < freq) (hℓ : 0 ≤ ℓ) (hD : 1 ≤ D) (hR : ℓ * D ^ 16 ≤ 1) (hC : 0 ≤ C)
    (hκ : ContDiff ℝ ∞ κ) (hκ₀ : ∀ a, κ a ≠ 0)
    (hK : ∀ m ≤ N, ∀ a, ‖iteratedFDeriv ℝ m (fun b => freq⁻¹ • κ b) a‖ ≤
      C * D ^ (7 * m + 2))
    (hQ : ∀ m ≤ N, ∀ a, ‖iteratedFDeriv ℝ m (fun b => freq ^ 2 / ‖κ b‖ ^ 2) a‖ ≤
      C * D ^ (16 * m + 4)) :
    ContDiff ℝ ∞ (scaledPhaseCoefficient ℓ (fun a => hierarchyRelayPotentialCoefficient (κ a))) ∧
    PhaseJetBound N (((2 : ℝ) ^ N * C ^ 2 * D ^ 6) / freq)
      (scaledPhaseCoefficient ℓ (fun a => hierarchyRelayPotentialCoefficient (κ a))) := by
  let k (a : Vec3) := freq⁻¹ • κ a
  let q (a : Vec3) := freq ^ 2 / ‖κ a‖ ^ 2
  let ks (a : Vec3) := k (ℓ • a)
  let qs (a : Vec3) := (-freq⁻¹ : ℝ) • q (ℓ • a)
  let cross (a : Vec3) := potentialCrossLinear (ks a)
  let A (a : Vec3) := qs a • cross a
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hS : ContDiff ℝ ∞ (fun a : Vec3 => ℓ • a) := contDiff_id.const_smul _
  have hk : ContDiff ℝ ∞ k := hκ.const_smul _
  have hq : ContDiff ℝ ∞ q :=
    contDiff_const.div (hκ.norm_sq ℝ) fun a => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hκ₀ a))
  have hks : ContDiff ℝ ∞ ks := hk.comp hS
  have hqs : ContDiff ℝ ∞ qs := (hq.comp hS).const_smul _
  have hCross : ContDiff ℝ ∞ cross := potentialCrossLinear.contDiff.comp hks
  have hAs : ContDiff ℝ ∞ A := hqs.smul hCross
  have hRk : ℓ * D ^ 7 ≤ 1 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by decide)) hℓ).trans hR
  have hksj : PhaseJetBound N (C * D ^ 2) ks := fun m hm a =>
    (norm_iteratedFDeriv_scaledLabel_power_le hk hD hℓ hRk hC m a (hK m hm (ℓ • a))).1
  have hqsj : PhaseJetBound N (freq⁻¹ * (C * D ^ 4)) qs := by
    intro m hm a
    change ‖iteratedFDeriv ℝ m (fun b => (-freq⁻¹ : ℝ) • q (ℓ • b)) a‖ ≤ _
    have hqscaled : ContDiffAt ℝ m (fun b => q (ℓ • b)) a :=
      ((hq.comp hS).of_le (by simp)).contDiffAt
    rw [iteratedFDeriv_const_smul_apply' hqscaled,
      norm_smul, norm_neg, Real.norm_of_nonneg (inv_nonneg.mpr hf.le)]
    exact mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_scaledLabel_power_le hq hD hℓ hR hC m a (hQ m hm (ℓ • a))).1
      (inv_nonneg.mpr hf.le)
  have hCrossj : PhaseJetBound N (C * D ^ 2) cross := by
    intro m hm a
    exact (potentialCrossLinear.norm_iteratedFDeriv_comp_left hks.contDiffAt (by simp)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) norm_potentialCrossLinear_le).trans (hksj m hm a))
  have hAj : PhaseJetBound N (((2 : ℝ) ^ N * C ^ 2 * D ^ 6) / freq) A := by
    intro m hm a
    have hb := phaseJetBound_bilinear_product (lsmul ℝ ℝ) opNorm_lsmul_le
      hqs hCross (by positivity : 0 ≤ freq⁻¹ * (C * D ^ 4)) (by positivity : 0 ≤ C * D ^ 2)
      hqsj hCrossj m hm a
    refine hb.trans_eq ?_
    rw [show (4 : ℕ) = 2 + 2 by decide, show (6 : ℕ) = 2 + 2 + 2 by decide, pow_add, pow_add, pow_add]
    ring
  let fst := ContinuousLinearMap.fst ℝ Vec3 ℝ
  have hEq : scaledPhaseCoefficient ℓ (fun a => hierarchyRelayPotentialCoefficient (κ a)) =
      A ∘ fst := by
    funext p
    let v := κ (ℓ • p.1)
    change hierarchyRelayPotentialCoefficient v = ((-freq⁻¹ : ℝ) • (freq ^ 2 / ‖v‖ ^ 2)) •
      cross3Left (freq⁻¹ • v)
    calc
      _ = hierarchyRelayPotentialCoefficient (freq • (freq⁻¹ • v)) := by
        rw [smul_smul, mul_inv_cancel₀ hf.ne', one_smul]
      _ = _ := by
        rw [hierarchyRelayPotentialCoefficient_frequency_scale hf, hierarchyRelayPotentialCoefficient,
          inv_sq_norm_inv_smul, smul_smul, smul_eq_mul]
        congr 1
        ring
  rw [hEq]
  refine ⟨hAs.comp fst.contDiff, fun m hm p => ?_⟩
  rw [fst.iteratedFDeriv_comp_right hAs p (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ m A (fst p)‖ * ‖fst‖ ^ m := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ m A (fst p)).norm_compContinuousLinearMap_le (fun _ => fst)
    _ ≤ ‖iteratedFDeriv ℝ m A (fst p)‖ :=
      mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _)
        (ContinuousLinearMap.norm_fst_le ..))
    _ ≤ _ := hAj m hm (fst p)

set_option maxHeartbeats 950000 in
/-- The actual parent wave potential operators have one inverse-frequency
factor at every fixed jet order on the closed slab. -/
theorem exists_parent_scaledPhasePotentialCoefficientJetBounds
    (W : ℕ → ℝ) (hW : ∀ n, 0 ≤ W n) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T D ℓ : ℝ},
      0 < T → T ≤ 1 → 1 ≤ D → 0 ≤ ℓ → ℓ * D ^ 16 ≤ 1 →
      IsLabelFlowOn U X (Icc 0 T) →
      ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
      (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
      (∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
        ‖iteratedFDeriv ℝ j (U t) x‖ ≤ W n * D ^ j) →
      ∀ (k : Vec3) {freq t₀ : ℝ}, 0 < freq → t₀ ∈ Icc 0 T →
        ‖labelWaveVector X 0 0 k t₀‖ = freq →
        ∀ n : ℕ, ∀ t ∈ Icc 0 T,
          let P := scaledPhaseCoefficient ℓ
            (fun a => hierarchyRelayPotentialCoefficient (labelWaveVector X 0 a k t))
          ContDiff ℝ ∞ P ∧ PhaseJetBound n ((C n * D ^ 6) / freq) P := by
  obtain ⟨K, hK, hJets⟩ := exists_parent_coefficientJetBounds W hW
  let A (n : ℕ) := ∑ i ∈ Finset.range (n + 1), K i
  let C (n : ℕ) : ℝ := (2 : ℝ) ^ n * (A n) ^ 2
  have hA (n : ℕ) : 0 ≤ A n := Finset.sum_nonneg (fun i _ => hK i)
  have hKA {i n : ℕ} (hi : i ≤ n) : K i ≤ A n :=
    Finset.single_le_sum (fun i _ => hK i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  refine ⟨C, fun n => mul_nonneg (by positivity) (sq_nonneg _), ?_⟩
  intro U X T D ℓ hT hT₁ hD hℓ hsmall hX hU hper hF hG hUJet k freq t₀ hf ht₀ hcenter n t ht
  dsimp only
  have hk : k ≠ 0 := by
    intro hzero
    simp only [hzero, labelWaveVector, map_zero, norm_zero] at hcenter
    exact hf.ne' hcenter.symm
  have hκs :
      ContDiff ℝ ∞ (fun a => labelWaveVector X 0 a k t) :=
    contDiff_slice_on_closedSlab (u := fun r a => labelWaveVector X 0 a k r)
      (hX.contDiffOn_transportedCovector hT hU hper k) ht
  have hκ₀ (a : Vec3) : labelWaveVector X 0 a k t ≠ 0 :=
    LocalizedAmplitude.transportedCovector_ne_zero_of_parent hT hX hU hper hk t ht a
  have hj (m : ℕ) (a : Vec3) :=
    hJets hT hT₁ hD hX hU hper hF hG hUJet k hf ht₀ hcenter m t ht a
  have hle (m : ℕ) (hm : m ≤ n) (p : ℕ) : K m * D ^ p ≤ A n * D ^ p :=
    mul_le_mul_of_nonneg_right (hKA hm) (pow_nonneg (zero_le_one.trans hD) _)
  exact phaseJetBound_scaledPhasePotentialCoefficient n hf hℓ hD hsmall (hA n) hκs hκ₀
    (fun m hm a => (hj m a).2.2.2.2.1.trans (hle m hm _))
    (fun m hm a => (hj m a).2.2.2.2.2.1.trans (hle m hm _))


end

end TorusEuler

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

private def labelRestriction :
    ((Vec3 × ℝ) →L[ℝ] Vec3) →L[ℝ] (Vec3 →L[ℝ] Vec3) :=
  (compL ℝ Vec3 (Vec3 × ℝ) Vec3).flip (inl ℝ Vec3 ℝ)

private theorem norm_labelRestriction_le : ‖labelRestriction‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro L
  change ‖L.comp (inl ℝ Vec3 ℝ)‖ ≤ 1 * ‖L‖
  have hI : ‖inl ℝ Vec3 ℝ‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro v
    simp only [inl_apply, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _), one_mul, le_refl]
  exact (L.opNorm_comp_le _).trans (by
    rw [one_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hI)

private theorem scaledLabelJet_formula {Q : Vec3 → ℝ → Vec3} {ℓ h : ℝ}
    (hℓ : ℓ ≠ 0) (hQ : ContDiff ℝ ∞ (Function.uncurry Q)) (x : Vec3 × ℝ) :
    fderiv ℝ (fun b => Q b (h * x.2)) (ℓ • x.1) =
      ℓ⁻¹ • labelRestriction (fderiv ℝ (scaledPhaseProfile ℓ h Q) x) := by
  rcases x with ⟨a, s⟩
  let q := scaledPhaseProfile ℓ h Q
  have hq : ContDiff ℝ ∞ q := hQ.comp (labelPhaseScale ℓ h).contDiff
  have hD : HasFDerivAt (fun b => q (b, s))
      ((fderiv ℝ q (a,s)).comp (inl ℝ Vec3 ℝ)) a := by
    have hd : HasFDerivAt q (fderiv ℝ q (a,s)) (a,s) :=
      (hq.differentiable (by simp) (a,s)).hasFDerivAt
    exact hd.comp (f := fun b : Vec3 => (b, s)) a (hasFDerivAt_prodMk_left a s)
  have hslice : ContDiff ℝ ∞ (fun b => Q b (h * s)) :=
    hQ.comp (contDiff_id.prodMk contDiff_const)
  have hS : HasFDerivAt (fun b => q (b, s))
      ((fderiv ℝ (fun b => Q b (h * s)) (ℓ • a)).comp (ℓ • ContinuousLinearMap.id ℝ Vec3)) a :=
    (hslice.differentiable (by simp) (ℓ • a)).hasFDerivAt.comp a
      (ℓ • ContinuousLinearMap.id ℝ Vec3).hasFDerivAt
  have hd := hD.unique hS
  ext v : 1
  change fderiv ℝ (fun b => Q b (h * s)) (ℓ • a) v =
    ℓ⁻¹ • ((fderiv ℝ q (a,s)).comp (inl ℝ Vec3 ℝ)) v
  rw [hd]
  simp only [comp_apply, smul_apply, id_apply, map_smul, smul_smul, inv_mul_cancel₀ hℓ, one_smul]

/-- The slow curl costs one scaled label derivative and one inverse coframe.
The constant is explicit in the two operator norms. -/
theorem phaseJetBound_scaled_slowCurl
    {Q : Vec3 → ℝ → Vec3} {B : Vec3 → Vec3 →L[ℝ] Vec3}
    {ℓ h BP BG : ℝ} (n : ℕ) (hℓ : 0 < ℓ)
    (hQ : ContDiff ℝ ∞ (Function.uncurry Q)) (hB : ContDiff ℝ ∞ B)
    (hBP : 0 ≤ BP) (hBG : 0 ≤ BG)
    (hpotential : PhaseJetBound (n + 1) BP (scaledPhaseProfile ℓ h Q))
    (hcoframe : ∀ j ≤ n, ∀ a, ℓ ^ j * ‖iteratedFDeriv ℝ j B a‖ ≤ BG) :
    let curl (a : Vec3) (s : ℝ) :=
      curlOfDerivative ((fderiv ℝ (fun b => Q b s) a).comp (B a))
    ContDiff ℝ ∞ (scaledPhaseProfile ℓ h curl) ∧
      PhaseJetBound n (‖curlOfDerivativeCLM‖ * ℓ⁻¹ * ((2 : ℝ) ^ n * (BP * BG)))
        (scaledPhaseProfile ℓ h curl) := by
  let P := scaledPhaseProfile ℓ h Q
  let J := labelRestriction ∘ fderiv ℝ P
  let G := scaledPhaseCoefficient ℓ B
  let W (z : Vec3 × ℝ) := (J z).comp (G z)
  let C := ℓ⁻¹ • curlOfDerivativeCLM
  have hP : ContDiff ℝ ∞ P := hQ.comp (labelPhaseScale ℓ h).contDiff
  have hD : ContDiff ℝ ∞ (fderiv ℝ P) := hP.fderiv_right (by simp)
  have hJ : ContDiff ℝ ∞ J := labelRestriction.contDiff.comp hD
  have hG : ContDiff ℝ ∞ G := contDiff_scaledPhaseCoefficient hB ℓ
  have hW : ContDiff ℝ ∞ W := by
    change ContDiff ℝ ∞ (fun z => compL ℝ Vec3 Vec3 Vec3 (J z) (G z))
    exact ((compL ℝ Vec3 Vec3 Vec3).contDiff.comp hJ).clm_apply hG
  have hJjet : PhaseJetBound n BP J := by
    intro j hj z
    refine (labelRestriction.norm_iteratedFDeriv_comp_left hD.contDiffAt (by simp)).trans ?_
    rw [norm_iteratedFDeriv_fderiv]
    exact (mul_le_of_le_one_left (norm_nonneg _) norm_labelRestriction_le).trans
      (hpotential (j + 1) (Nat.succ_le_succ hj) z)
  have hWjet : PhaseJetBound n ((2 : ℝ) ^ n * (BP * BG)) W :=
    phaseJetBound_bilinear_product (compL ℝ Vec3 Vec3 Vec3) (norm_compL_le ℝ Vec3 Vec3 Vec3)
      hJ hG hBP hBG hJjet (scaledPhaseCoefficient_jetBound hB hℓ.le hcoframe)
  have hEq :
      scaledPhaseProfile ℓ h (fun a s =>
        curlOfDerivative ((fderiv ℝ (fun b => Q b s) a).comp (B a))) = C ∘ W := by
    funext x
    change curlOfDerivative ((fderiv ℝ (fun b => Q b (h * x.2)) (ℓ • x.1)).comp
      (B (ℓ • x.1))) = ℓ⁻¹ • curlOfDerivative ((J x).comp (G x))
    rw [scaledLabelJet_formula hℓ.ne' hQ, smul_comp, curlOfDerivative_smul]
    rfl
  dsimp only
  rw [hEq]
  refine ⟨C.contDiff.comp hW, ?_⟩
  intro j hj x
  refine (C.norm_iteratedFDeriv_comp_left hW.contDiffAt (by simp)).trans ?_
  have hC : ‖C‖ ≤ ‖curlOfDerivativeCLM‖ * ℓ⁻¹ := by
    apply opNorm_le_bound _ (by positivity)
    intro D
    change ‖ℓ⁻¹ • curlOfDerivativeCLM D‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le), mul_comm ‖curlOfDerivativeCLM‖, mul_assoc]
    exact mul_le_mul_of_nonneg_left (curlOfDerivativeCLM.le_opNorm D) (inv_nonneg.mpr hℓ.le)
  exact mul_le_mul hC (hWjet j hj x) (norm_nonneg _) (by positivity)

namespace HierarchyTwistedProfile.PhysicalApproximationData

open LocalizedAmplitude

variable {T : ℝ} {k : Vec3} {U : Velocity} {X : ℝ → Velocity}
  {hT : 0 < T} {g : ParentGeometry hT U X k}

local notation "M" => (fun t a => fderiv ℝ (U t) (X 0 t a))
local notation "K" => (fun t a => labelWaveVector X 0 a k t)

/-- The exactly wrapped uncut primary inherits its two-jet bound from the
actual wrapped velocity, three potential jets and two coframe jets. -/
theorem activationPrimary_phaseJetBound
    {t₀ ℓ D C h : ℝ} {center : ℝ → Vec3}
    (w : SeedOn M K center t₀ T ℓ D C) {t : ℝ} (ht : t ∈ Icc 0 T)
    {BV BP BG : ℝ} (hℓ : 0 < ℓ) (hBP : 0 ≤ BP) (hBG : 0 ≤ BG)
    (hB : ContDiff ℝ ∞ (fun a => fderiv ℝ (X t 0) (X 0 t a)))
    (hcoframe : ∀ j ≤ (2 : ℕ), ∀ a, ℓ ^ j *
      ‖iteratedFDeriv ℝ j (fun b => fderiv ℝ (X t 0) (X 0 t b)) a‖ ≤ BG)
    (hV : ContDiff ℝ ∞ (Function.uncurry (phaseTwistedPeriodizeCentered k (w.leading h) t)))
    (hvelocity : PhaseJetBound 2 BV
      (scaledPhaseProfile ℓ h (phaseTwistedPeriodizeCentered k (w.leading h) t)))
    (hP : ContDiff ℝ ∞ (Function.uncurry (fun a s => wavePotential (K t a)
      (phaseTwistedPeriodizeCentered k (w.leading h) t a) s)))
    (hpotential : PhaseJetBound 3 BP (scaledPhaseProfile ℓ h (fun a s => wavePotential (K t a)
      (phaseTwistedPeriodizeCentered k (w.leading h) t a) s))) :
    PhaseJetBound 2 (BV + ‖curlOfDerivativeCLM‖ * ℓ⁻¹ * ((2 : ℝ) ^ (2 : ℕ) * (BP * BG)))
      (scaledPhaseProfile ℓ h (activationPrimary (h := h) w g.inverse t)) := by
  let V := phaseTwistedPeriodizeCentered k (w.leading h) t
  let B (a : Vec3) := fderiv ℝ (X t 0) (X 0 t a)
  let P (a : Vec3) (s : ℝ) := wavePotential (K t a) (V a) s
  let Q (a : Vec3) (s : ℝ) := curlOfDerivative ((fderiv ℝ (fun b => P b s) a).comp (B a))
  have heq : activationPrimary (h := h) w g.inverse t = fun a s => V a s + Q a s := by
    funext a s
    change V a s + curlOfDerivative ((fderiv ℝ (fun b => P b s) a).comp
      (g.inverse.val.val.val (t, a, s))) = _
    rw [g.inverse_value _ ⟨ht, mem_univ _⟩]
  have hVr : ContDiff ℝ ∞ (scaledPhaseProfile ℓ h V) := hV.comp (labelPhaseScale ℓ h).contDiff
  obtain ⟨hQr, hQjet⟩ :=
    phaseJetBound_scaled_slowCurl 2 hℓ hP hB hBP hBG hpotential hcoframe
  rw [heq]
  intro j hj x
  change ‖iteratedFDeriv ℝ j (scaledPhaseProfile ℓ h V + scaledPhaseProfile ℓ h Q) x‖ ≤ _
  rw [iteratedFDeriv_add (hVr.of_le (by simp)) (hQr.of_le (by simp))]
  exact (norm_add_le _ _).trans (add_le_add (hvelocity j hj x) (hQjet j hj x))

end HierarchyTwistedProfile.PhysicalApproximationData
end
end TorusEuler


namespace TorusEuler

noncomputable section

open scoped Interval

private theorem phaseMean_translate_forActivation {f : ℝ → Vec3}
    (hper : Function.Periodic f 1) (b : ℝ) :
    phaseMean (fun s => f (b + s)) = phaseMean f := by
  unfold phaseMean
  simp_rw [add_comm b]
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm (1 : ℝ) b] using hper.intervalIntegral_add_eq b 0

private theorem phasePrimitive_translate_forActivation {f : ℝ → Vec3} (hf : Continuous f)
    (hper : Function.Periodic f 1) (hzero : phaseMean f = 0) (b : ℝ) :
    phasePrimitive (fun s => f (b + s)) 0 = phasePrimitive f b := by
  have hd (s : ℝ) : HasDerivAt (fun u => phasePrimitive f (b + u)) (f (b + s)) s :=
    (hasDerivAt_phasePrimitive hf (b + s)).scomp s ((hasDerivAt_id s).const_add b)
      |>.congr_deriv (by simp)
  have h := phasePrimitive_deriv hd (hf.comp (continuous_const.add continuous_id))
  have hm : phaseMean (fun s => phasePrimitive f (b + s)) = 0 :=
    (phaseMean_translate_forActivation (periodic_phasePrimitive hf hper hzero) b).trans
      (phaseMean_phasePrimitive hf)
  rw [h]
  change phasePrimitive f (b + 0) - phaseMean (fun s => phasePrimitive f (b + s)) = _
  rw [add_zero, hm, sub_zero]

/-- The periodic zero-mean phase primitive preserves every scaled jet order
with factor two. Derivatives may act on both labels and the evaluation phase. -/
theorem phaseJetBound_scaled_periodicPrimitive
    {f : Vec3 → ℝ → Vec3} {n : ℕ} {ℓ h B : ℝ} (hh : h ≠ 0)
    (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hper : ∀ a, Function.Periodic (f a) 1)
    (hzero : ∀ a, phaseMean (f a) = 0)
    (hjet : PhaseJetBound n B (scaledPhaseProfile ℓ h f)) :
    PhaseJetBound n (2 * B) (scaledPhaseProfile ℓ h (fun a => phasePrimitive (f a))) := by
  let F := scaledPhaseProfile ℓ h f
  let g (x : Vec3 × ℝ) (s : ℝ) := f (ℓ • x.1) (h * x.2 + s)
  have hg : ContDiff ℝ ∞ (Function.uncurry g) :=
    hf.comp ((contDiff_fst.fst.const_smul ℓ).prodMk
      (((contDiff_const (c := h)).mul contDiff_fst.snd).add contDiff_snd))
  have hgper (x : Vec3 × ℝ) : Function.Periodic (g x) 1 := by
    intro s
    simpa only [g, add_assoc] using hper (ℓ • x.1) (h * x.2 + s)
  have hgzero (x : Vec3 × ℝ) : phaseMean (g x) = 0 :=
    (phaseMean_translate_forActivation (hper (ℓ • x.1)) _).trans (hzero (ℓ • x.1))
  have hprim : (fun x => phasePrimitive (g x) 0) =
      scaledPhaseProfile ℓ h (fun a => phasePrimitive (f a)) := by
    funext x
    have hcont : Continuous (f (ℓ • x.1)) :=
      hf.continuous.comp (continuous_const.prodMk continuous_id)
    exact phasePrimitive_translate_forActivation hcont (hper _) (hzero _) (h * x.2)
  intro j hj x
  let L := ContinuousLinearMap.id ℝ ((Vec3 × ℝ) [×j]→L[ℝ] Vec3)
  have hD (s : ℝ) : ‖L (mixedPhaseJet g j 0 x s)‖ ≤ B := by
    have heq : (fun y => g y s) = fun y => F (y + (0, s / h)) := by
      funext y
      have hcancel : h * (s / h) = s := by field_simp
      change f (ℓ • y.1) (h * y.2 + s) = f (ℓ • (y.1 + 0)) (h * (y.2 + s / h))
      rw [add_zero, mul_add, hcancel]
    simp only [L, id_apply, mixedPhaseJet, iteratedDeriv_zero, heq, iteratedFDeriv_comp_add_right]
    exact hjet j hj (x + (0, s / h))
  have h := (norm_map_mixedPhaseJet_phaseOps_le hg hgper j 0 x 0 L hD).2.2 hgzero
  simpa only [L, id_apply, mixedPhaseJet, iteratedDeriv_zero, hprim] using h

/-- Applying the covector coefficient and taking the normalized primitive
bounds the exact potential with two finite Leibniz factors. -/
theorem phaseJetBound_scaled_wavePotential
    {f : Vec3 → ℝ → Vec3} {κ : Vec3 → Vec3} {n : ℕ} {ℓ h BV BK : ℝ} (hh : h ≠ 0)
    (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hper : ∀ a, Function.Periodic (f a) 1)
    (hzero : ∀ a, phaseMean (f a) = 0)
    (hκ : ContDiff ℝ ∞ (fun a => hierarchyRelayPotentialCoefficient (κ a)))
    (hBV : 0 ≤ BV) (hBK : 0 ≤ BK)
    (hV : PhaseJetBound n BV (scaledPhaseProfile ℓ h f))
    (hK : PhaseJetBound n BK
      (scaledPhaseCoefficient ℓ (fun a => hierarchyRelayPotentialCoefficient (κ a)))) :
    ContDiff ℝ ∞ (Function.uncurry (fun a => wavePotential (κ a) (f a))) ∧
    PhaseJetBound n (2 * ((2 : ℝ) ^ n * (BK * BV)))
      (scaledPhaseProfile ℓ h (fun a => wavePotential (κ a) (f a))) := by
  let K := fun a => hierarchyRelayPotentialCoefficient (κ a)
  let u (a : Vec3) (s : ℝ) := K a (f a s)
  have hu : ContDiff ℝ ∞ (Function.uncurry u) := (hκ.comp contDiff_fst).clm_apply hf
  have huper (a : Vec3) : Function.Periodic (u a) 1 := fun s => congrArg (K a) (hper a s)
  have huzero (a : Vec3) : phaseMean (u a) = 0 := by
    have hcont : Continuous (f a) := hf.continuous.comp (continuous_const.prodMk continuous_id)
    change (∫ s in (0 : ℝ)..1, K a (f a s)) = 0
    rw [(K a).intervalIntegral_comp_comm (hcont.intervalIntegrable 0 1)]
    change K a (phaseMean (f a)) = 0
    rw [hzero, map_zero]
  let L : (Vec3 →L[ℝ] Vec3) →L[ℝ] Vec3 →L[ℝ] Vec3 :=
    (ContinuousLinearMap.apply ℝ Vec3).flip
  have hL : ‖L‖ ≤ 1 := by
    simp only [L, ContinuousLinearMap.opNorm_flip, ContinuousLinearMap.apply]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => ?_
    simp only [ContinuousLinearMap.coe_id', id, one_mul]
    rfl
  have hU : PhaseJetBound n ((2 : ℝ) ^ n * (BK * BV)) (scaledPhaseProfile ℓ h u) :=
    phaseJetBound_bilinear_product L hL (contDiff_scaledPhaseCoefficient hκ ℓ)
      (hf.comp (labelPhaseScale ℓ h).contDiff) hBK hBV hK hV
  have heq : (fun a => wavePotential (κ a) (f a)) = fun a => phasePrimitive (u a) := by
    funext a s
    rfl
  rw [heq]
  refine ⟨?_, phaseJetBound_scaled_periodicPrimitive hh hu huper huzero hU⟩
  apply contDiffOn_univ.mp
  rw [← univ_prod_univ]
  exact contDiffOn_phasePrimitive convex_univ uniqueDiffOn_univ hu.contDiffOn

end
end TorusEuler


namespace TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData

open LocalizedAmplitude

noncomputable section

variable {T : ℝ} {k : Vec3} {U : Velocity} {X : ℝ → Velocity}
  {hT : 0 < T} {g : ParentGeometry hT U X k}

local notation "M" => (fun t a => fderiv ℝ (U t) (X 0 t a))
local notation "K" => (fun t a => labelWaveVector X 0 a k t)

private theorem wrappedUnswitchedLeading_bounds
    {t₀ ℓ D C r h : ℝ} {center : ℝ → Vec3}
    (w : SeedOn M K center t₀ T ℓ D C) (reg : w.HierarchyRegularity r h)
    {t : ℝ} (ht : t ∈ Icc t₀ T) {n : ℕ} {BV : ℝ}
    (hvelocity : PhaseJetBound n BV (scaledPhaseProfile ℓ h (w.leading h t))) :
    let V := phaseTwistedPeriodizeCentered k (w.leading h) t
    ContDiff ℝ ∞ (Function.uncurry V) ∧ (∀ a, Function.Periodic (V a) 1) ∧
      (∀ a, phaseMean (V a) = 0) ∧ PhaseJetBound n BV (scaledPhaseProfile ℓ h V) := by
  let A := w.amplitude t
  let F (_ : ℝ) (a : Vec3) (s : ℝ) := waveProfile h s • A a
  let f (u : ℝ) (a : Vec3) (s : ℝ) := radialEnvelope ℓ a • F u a s
  let v (p : HierarchyProfilePoint) := phaseTwistedPeriodizeCentered k f p.1 p.2.1 p.2.2
  let V := phaseTwistedPeriodizeCentered k (w.leading h) t
  have htI : t ∈ Icc 0 T := ⟨reg.nonneg_start.trans ht.1, ht.2⟩
  have hA : ContDiff ℝ ∞ A :=
    reg.amplitude_smooth.comp_contDiff (f := fun a : Vec3 => (t, a))
      (contDiff_const.prodMk contDiff_id) (fun a => ⟨ht, mem_univ a⟩)
  have hw := contDiff_waveProfile reg.phase_pos reg.phase_le_one
  have hF : ContDiff ℝ ∞ (fun p : HierarchyProfilePoint => F p.1 p.2.1 p.2.2) :=
    (hw.comp contDiff_snd.snd).smul (hA.comp contDiff_snd.fst)
  have hv : ContDiffOn ℝ ∞ v (hierarchyProfileSlab T) :=
    contDiffOn_phaseTwistedPeriodizeCentered_radialEnvelope reg.envelope_pos reg.envelope_fits hF.contDiffOn
  have hraw (u : ℝ) : f u = w.leading h t := by
    funext a s
    simp only [f, F, A, SeedOn.leading, smul_smul]
  have hper (u : ℝ) (a : Vec3) : Function.Periodic (f u a) 1 := by
    intro s
    simp only [f, F, periodic_waveProfile reg.phase_pos reg.phase_le_one s]
  have hVper (a : Vec3) : Function.Periodic (V a) 1 := by
    change Function.Periodic (phaseTwistedPeriodizeCentered k (w.leading h) t a) 1
    apply phaseTwistedPeriodizeCentered_phase_periodic
    rw [← hraw t]
    exact hper t
  let p : HierarchyTwistedProfile T k Vec3 :=
    HierarchyTwistedProfile.ofSmooth v hv
      (fun x => by
        rcases x with ⟨u, a, s⟩
        simpa only [v, hierarchyPhasePeriod, Prod.mk_add_mk, add_zero] using
          phaseTwistedPeriodizeCentered_phase_periodic (k := k) (hper u) a s)
      (fun m x => by
        rw [add_hierarchyLatticeShift]
        exact phaseTwistedPeriodizeCentered_translate k f x.1 x.2.1 x.2.2 m)
  have hp (a : Vec3) (s : ℝ) : p.val.val.val (t, a, s) = V a s := by
    have hx : (t, a, s) ∈ hierarchyProfileSlab T := ⟨htI, mem_univ _⟩
    have hEval : p.val.val.val (t, a, s) = v (t, a, s) :=
      HierarchyTwistedProfile.ofSmooth_eval (f := v) hv _ _ hx
    rw [hEval]
    change phaseTwistedPeriodizeCentered k f t a s = V a s
    change f t (centeredLabel a) _ = w.leading h t (centeredLabel a) _
    rw [hraw t]
  have hVs : ContDiff ℝ ∞ (Function.uncurry V) := by
    have hpS := HierarchySmoothProfile.contDiff_labelPhase_slice p.val.val htI
    have hpEq : (fun q : Vec3 × ℝ => p.val.val.val (t, q)) = Function.uncurry V :=
      funext fun q => hp q.1 q.2
    rwa [hpEq] at hpS
  have hVzero (a : Vec3) : phaseMean (V a) = 0 := by
    let b := centeredLabel a
    let c : ℝ := -⟪k, a⟫_ℝ + ⟪k, b⟫_ℝ
    have heq : V a = fun s => f t b (c + s) := by
      funext s
      change w.leading h t b (s - ⟪k, a⟫_ℝ + ⟪k, b⟫_ℝ) = f t b (c + s)
      rw [hraw t]
      congr 1
      dsimp only [c]
      ring
    rw [heq, phaseMean_translate_forActivation (hper t b) c]
    let E : ℝ →L[ℝ] Vec3 :=
      radialEnvelope ℓ b • (ContinuousLinearMap.id ℝ ℝ).smulRight (A b)
    change (∫ s in (0 : ℝ)..1, E (waveProfile h s)) = 0
    rw [E.intervalIntegral_comp_comm (hw.continuous.intervalIntegrable 0 1)]
    change E (phaseMean (waveProfile h)) = 0
    rw [phaseMean_waveProfile reg.phase_pos reg.phase_le_one, map_zero]
  have hRaw : ContDiff ℝ ∞ (Function.uncurry (w.leading h t)) := by
    have hFu : ContDiff ℝ ∞ (Function.uncurry (F t)) :=
      (hw.comp contDiff_snd).smul (hA.comp contDiff_fst)
    rw [← hraw t]
    exact ((contDiff_radialEnvelope reg.envelope_pos).comp contDiff_fst).smul hFu
  have hcell (a : Vec3) (ha : a ∈ centeredCell) (s : ℝ) :
      p.val.val.val (t, a, s) = w.leading h t a s := by
    rw [hp]
    have h := phaseTwistedPeriodizeCentered_radialEnvelope_eq_on_centeredCell (k := k)
      (f := F) (t := t) reg.envelope_pos reg.envelope_fits ha s
    change phaseTwistedPeriodizeCentered k f t a s = f t a s at h
    simpa only [V, phaseTwistedPeriodizeCentered, hraw] using h
  have hJ := HierarchyTwistedProfile.phaseJetBound_of_centeredCell htI reg.envelope_pos.ne'
    reg.phase_pos.ne' hRaw hcell hvelocity
  have hEq : (fun a s => p.val.val.val (t, a, s)) = V := funext fun a => funext (hp a)
  rw [hEq] at hJ
  exact ⟨hVs, hVper, hVzero, hJ⟩

/-- The actual later-wave primary, including the skew wrapping and exact curl,
uses three scaled unwrapped seed jets, three potential coefficient jets and
two inverse coframe jets. -/
theorem activationPrimary_phaseJetBound_of_leading
    {t₀ ℓ D C r h : ℝ} {center : ℝ → Vec3}
    (w : SeedOn M K center t₀ T ℓ D C) (reg : w.HierarchyRegularity r h)
    {t : ℝ} (ht : t ∈ Icc t₀ T) {BV BK BG : ℝ} (hBV : 0 ≤ BV) (hBK : 0 ≤ BK) (hBG : 0 ≤ BG)
    (hB : ContDiff ℝ ∞ (fun a => fderiv ℝ (X t 0) (X 0 t a)))
    (hcoframe : ∀ j ≤ (2 : ℕ), ∀ a, ℓ ^ j *
      ‖iteratedFDeriv ℝ j (fun b => fderiv ℝ (X t 0) (X 0 t b)) a‖ ≤ BG)
    (hpotentialCoefficient :
      ContDiff ℝ ∞ (fun a => hierarchyRelayPotentialCoefficient (K t a)))
    (hK : PhaseJetBound 3 BK (scaledPhaseCoefficient ℓ
      (fun a => hierarchyRelayPotentialCoefficient (K t a))))
    (hvelocity : PhaseJetBound 3 BV (scaledPhaseProfile ℓ h (w.leading h t))) :
    PhaseJetBound 2
      (BV + ‖curlOfDerivativeCLM‖ * ℓ⁻¹ * ((2 : ℝ) ^ (2 : ℕ) *
        ((2 * ((2 : ℝ) ^ (3 : ℕ) * (BK * BV))) * BG)))
      (scaledPhaseProfile ℓ h (activationPrimary (h := h) w g.inverse t)) := by
  obtain ⟨hVs, hVper, hVzero, hVjet⟩ := wrappedUnswitchedLeading_bounds (k := k) w reg ht hvelocity
  obtain ⟨hPs, hPjet⟩ :=
    phaseJetBound_scaled_wavePotential reg.phase_pos.ne' hVs hVper hVzero
      hpotentialCoefficient hBV hBK hVjet hK
  exact activationPrimary_phaseJetBound w ⟨reg.nonneg_start.trans ht.1, ht.2⟩
    reg.envelope_pos (by positivity) hBG hB hcoframe hVs
    (hVjet.mono_order (by decide)) hPs hPjet

end
end TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData

namespace TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData

open LocalizedAmplitude

noncomputable section

set_option maxHeartbeats 1700000 in
/-- The actual uncut primary on the activation slab has the two-jet cap
required by the scheduled residual. The slow curl contributes one inverse
label radius and retains the inverse carrier in its potential. -/
theorem exists_parent_activationPrimary_phaseJetBound (W : ℕ → ℝ) (hW : ∀ j, 0 ≤ W j) :
    ∃ (A : ℕ) (C : ℝ), 30 ≤ A ∧ 0 ≤ C ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T t₀ D ℓ Cseed freq r : ℝ} {a : ℕ}
        {k : Vec3} {center : ℝ → Vec3} {hT : 0 < T} {g : ParentGeometry hT U X k},
      T ≤ 1 → 2 ≤ D → ℓ ≤ (D ^ A)⁻¹ → ℓ⁻¹ ≤ D ^ a →
      1 ≤ freq → ‖labelWaveVector X 0 0 k t₀‖ = freq →
      IsLabelFlowOn U X (Icc 0 T) →
      ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
      (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
      (∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (X 0 t) x‖ ≤ D) →
      (∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (X t 0) (X 0 t x)‖ ≤ D) →
      (∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
        ‖iteratedFDeriv ℝ j (U t) x‖ ≤ W n * D ^ j) →
      let M (t : ℝ) (x : Vec3) := fderiv ℝ (U t) (X 0 t x)
      let κ (t : ℝ) (x : Vec3) := labelWaveVector X 0 x k t
      CenterWaveOn (fun t => M t 0) (fun t => κ t 0) center t₀ T D →
      ∀ (w : SeedOn M κ center t₀ T ℓ D Cseed),
      let h := freq ^ (-1 / 2 : ℝ)
      w.HierarchyRegularity r h →
      ∀ t ∈ Icc t₀ T,
        let γ := freq ^ (3 / 4 : ℝ) * ‖center t‖
        PhaseJetBound 2 (γ * (C * D ^ (a + 27) * freq ^ (-5 / 4 : ℝ)))
          (scaledPhaseProfile ℓ h (activationPrimary (h := h) w g.inverse t)) := by
  obtain ⟨A, hA, hRawAll⟩ := exists_parent_seed_leadingScaledJetBounds W hW
  obtain ⟨L, hL, hRaw⟩ := hRawAll 3
  obtain ⟨P, hP, hPot⟩ := exists_parent_scaledPhasePotentialCoefficientJetBounds W hW
  obtain ⟨G, hG, hJets⟩ := exists_parent_coefficientJetBounds W hW
  let S : ℝ := 1 + ∑ j ∈ Finset.range 3, G j
  let C := L * (1 + 64 * ‖curlOfDerivativeCLM‖ * P 3 * S)
  have hL₀ := zero_le_one.trans hL
  have hP₀ := hP 3
  have hS : 0 ≤ S := add_nonneg zero_le_one (Finset.sum_nonneg fun i _ => hG i)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨A, C, hA, hC, ?_⟩
  intro U X T t₀ D ℓ Cseed freq r a k center hT g hT₁ hD hℓA hℓinv hf hfreq
    hX hU hper hFbound hGbound hUjet M κ hc w h reg t ht γ
  have hf₀ : 0 < freq := zero_lt_one.trans_le hf
  have hD₁ : 1 ≤ D := one_le_two.trans hD
  have hD₀ : 0 < D := zero_lt_one.trans_le hD₁
  have ht₀ : t₀ ∈ Icc 0 T := ⟨reg.nonneg_start, reg.start_lt_end.le⟩
  have ht' : t ∈ Icc 0 T := ⟨reg.nonneg_start.trans ht.1, ht.2⟩
  have hℓ := reg.envelope_pos
  have hℓpow : ℓ * D ^ A ≤ 1 :=
    (le_div_iff₀ (pow_pos hD₀ A)).mp (by simpa only [one_div] using hℓA)
  have hsmall (p : ℕ) (hp : p ≤ 30) : ℓ * D ^ p ≤ 1 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD₁ (hp.trans hA)) hℓ.le).trans hℓpow
  let B (x : Vec3) := fderiv ℝ (X t 0) (X 0 t x)
  let BV := γ * (L * D ^ 20 * freq ^ (-5 / 4 : ℝ))
  let BK := (P 3 * D ^ 6) / freq
  let BG := S * D
  have hγ : 0 ≤ γ := by dsimp only [γ]; positivity
  have hBV : 0 ≤ BV := by dsimp only [BV]; positivity
  have hBK : 0 ≤ BK := by dsimp only [BK]; positivity
  have hBG : 0 ≤ BG := by dsimp only [BG]; positivity
  have hBs : ContDiff ℝ ∞ B :=
    contDiff_slice_on_closedSlab (u := fun u x => fderiv ℝ (X u 0) (X 0 u x))
      (hX.contDiffOn_inverseLabelDerivative hT hU hper) ht'
  have hBGjet (j : ℕ) (hj : j ≤ 2) (x : Vec3) :
      ℓ ^ j * ‖iteratedFDeriv ℝ j B x‖ ≤ BG := by
    have hGbase := (hJets hT hT₁ hD₁ hX hU hper hFbound hGbound hUjet
      k hf₀ ht₀ hfreq j t ht' x).2.1
    have hGS : G j ≤ S := (Finset.single_le_sum (fun i _ => hG i)
      (Finset.mem_range.mpr (show j < 3 by omega))).trans (le_add_of_nonneg_left zero_le_one)
    calc
      _ ≤ ℓ ^ j * (S * D ^ (7 * j + 1)) := mul_le_mul_of_nonneg_left
        (hGbase.trans (mul_le_mul_of_nonneg_right hGS (pow_nonneg hD₀.le _))) (pow_nonneg hℓ.le _)
      _ = (ℓ * D ^ 7) ^ j * BG := by dsimp only [BG]; rw [mul_pow, ← pow_mul, pow_add]; ring
      _ ≤ BG := mul_le_of_le_one_left hBG (pow_le_one₀ (by positivity) (hsmall 7 (by decide)))
  obtain ⟨_, hKjet⟩ := hPot hT hT₁ hD₁ hℓ.le (hsmall 16 (by decide)) hX hU hper
    hFbound hGbound hUjet k hf₀ ht₀ hfreq 3 t ht'
  have hk : k ≠ 0 := by
    intro hz
    simp only [hz, labelWaveVector, map_zero, norm_zero] at hfreq
    exact hf₀.ne' hfreq.symm
  have hκs : ContDiff ℝ ∞ (κ t) := contDiff_slice_on_closedSlab (u := κ)
    (hX.contDiffOn_transportedCovector hT hU hper k) ht'
  have hKsmooth : ContDiff ℝ ∞ (fun x => hierarchyRelayPotentialCoefficient (κ t x)) :=
    contDiff_hierarchyRelayPotentialCoefficient hκs fun x =>
      transportedCovector_ne_zero_of_parent hT hX hU hper hk t ht' x
  have hVjet : PhaseJetBound 3 BV (scaledPhaseProfile ℓ h (w.leading h t)) := by
    have hv := (hRaw reg.nonneg_start reg.start_lt_end hT₁ hD hℓ hℓA hf hfreq
      hX hU hper hFbound hGbound hUjet hc w (χ := 1) (by norm_num) t ht).1
    simpa only [one_smul] using hv
  have hJ := activationPrimary_phaseJetBound_of_leading (g := g) w reg ht
    hBV hBK hBG hBs hBGjet hKsmooth hKjet hVjet
  have hBKle : BK ≤ P 3 * D ^ 6 := by
    dsimp only [BK]
    exact div_le_self (by positivity) hf
  intro j hj x
  refine (hJ j hj x).trans ?_
  have hPow : D ^ 20 ≤ D ^ (a + 27) := pow_le_pow_right₀ hD₁ (by omega)
  have hPerf : 0 ≤ freq ^ (-5 / 4 : ℝ) := Real.rpow_nonneg hf₀.le _
  calc
    _ ≤ BV + ‖curlOfDerivativeCLM‖ * D ^ a * (4 * ((2 * (8 * (P 3 * D ^ 6 * BV))) * BG)) := by
      rw [show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num, show (2 : ℝ) ^ (3 : ℕ) = 8 by norm_num]
      gcongr
    _ = γ * (L * D ^ 20 * freq ^ (-5 / 4 : ℝ)) +
        γ * ((L * (64 * ‖curlOfDerivativeCLM‖ * P 3 * S)) * D ^ (a + 27) * freq ^ (-5 / 4 : ℝ)) := by
      dsimp only [BV, BG]
      rw [pow_add]
      ring
    _ ≤ γ * (L * D ^ (a + 27) * freq ^ (-5 / 4 : ℝ)) +
        γ * ((L * (64 * ‖curlOfDerivativeCLM‖ * P 3 * S)) * D ^ (a + 27) * freq ^ (-5 / 4 : ℝ)) := by
      gcongr
    _ = _ := by dsimp only [C]; ring

end
end TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData
