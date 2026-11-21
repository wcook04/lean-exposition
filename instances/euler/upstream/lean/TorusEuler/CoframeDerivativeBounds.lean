import TorusEuler.FreezingOperatorBounds
import TorusEuler.LabelFlowGeometry

open scoped InnerProductSpace

/-!
Quantitative bounds for the inverse deformation and the transported covector
in Proposition 5.1, given bounds for the derivatives of the forward flow.
-/

open ContinuousLinearMap Set

namespace TorusEuler

section InverseCoefficient

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A] [CompleteSpace A]

/-- If the positive-order jets of a coefficient cost `D ^ (p * i + 1)`
and the inverse has norm at most `D`, then its order-`n` inverse jet costs
`D ^ ((p + 2) * n + 1)`. The constant depends on a single upper bound
for the forward-jet constants through order `n`. -/
theorem norm_iteratedFDeriv_inverse_coefficient_le {c : E → A} {x : E} {n p : ℕ}
    (hc : ContDiff ℝ n c) (hunit : ∀ y, IsUnit (c y)) {D C : ℝ}
    (hD : 1 ≤ D) (hC : 1 ≤ C) (hInv : ‖Ring.inverse (c x)‖ ≤ D)
    (hJets : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i c x‖ ≤ C * D ^ (p * i + 1)) :
    ‖iteratedFDeriv ℝ n (Ring.inverse ∘ c) x‖ ≤
      (n.factorial : ℝ) ^ 2 * C ^ n * D ^ ((p + 2) * n + 1) := by
  have hinput (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i c x‖ ≤ (C * D ^ (p + 1)) ^ i := by
    have hiPow : p * i + 1 ≤ (p + 1) * i := by rw [Nat.add_mul, one_mul]; omega
    calc
      _ ≤ C * D ^ (p * i + 1) := hJets i hi hin
      _ ≤ C ^ i * D ^ ((p + 1) * i) := by
        gcongr
        exact le_self_pow₀ hC (by omega)
      _ = _ := by rw [mul_pow, pow_mul]
  have h := norm_iteratedFDeriv_ringInverse_comp_le isOpen_univ (mem_univ x)
    hc.contDiffOn (fun y _ => hunit y) hD hInv hinput
  calc
    _ ≤ (n.factorial : ℝ) ^ 2 * D ^ (n + 1) * (C * D ^ (p + 1)) ^ n := by
      simpa only [norm_one, max_self, mul_one] using h
    _ = _ := by
      rw [mul_pow, ← pow_mul]
      rw [show (p + 2) * n + 1 = (n + 1) + (p + 1) * n by
        simp only [Nat.add_mul]; omega, pow_add]
      ring

end InverseCoefficient

section Deformation

variable {U : Velocity} {X : ℝ → Velocity} {l r s t : ℝ}

private theorem IsLabelFlowOn.inverseLabelDerivative_eq_ringInverse
    (hX : IsLabelFlowOn U X (Icc l r)) (hlr : l < r)
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hper : ∀ u ∈ Icc l r, SpatiallyPeriodic (U u))
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) (a : Vec3) :
    IsUnit (fderiv ℝ (X s t) a) ∧
      Ring.inverse (fderiv ℝ (X s t) a) = fderiv ℝ (X t s) (X s t a) := by
  let F := fderiv ℝ (X s t) a
  let G := fderiv ℝ (X t s) (X s t a)
  obtain ⟨hGF, hFG⟩ := hX.labelDerivative_inverse hlr hU hper hs ht a
  let u : (Vec3 →L[ℝ] Vec3)ˣ := ⟨F, G, hFG, hGF⟩
  exact ⟨u.isUnit, Ring.inverse_unit u⟩

/-- At a fixed pair of times, one spatial derivative of the forward flow
gives the spatial regularity of the inverse Jacobian in labels. -/
theorem IsLabelFlowOn.contDiff_inverseLabelDerivative
    (hX : IsLabelFlowOn U X (Icc l r)) (hlr : l < r)
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hper : ∀ u ∈ Icc l r, SpatiallyPeriodic (U u))
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) {n : ℕ}
    (hFlow : ContDiff ℝ (n + 1 : ℕ) (X s t)) :
    ContDiff ℝ n fun b => fderiv ℝ (X t s) (X s t b) := by
  refine contDiff_iff_contDiffAt.mpr fun a => ?_
  obtain ⟨u, hu⟩ := (hX.inverseLabelDerivative_eq_ringInverse hlr hU hper hs ht a).1
  have hF : ContDiff ℝ (n : ℕ) (fderiv ℝ (X s t)) := hFlow.fderiv_right (by simp)
  have hI : ContDiffAt ℝ n Ring.inverse (fderiv ℝ (X s t) a) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  refine (hI.comp a hF.contDiffAt).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun b => ?_)
  exact (hX.inverseLabelDerivative_eq_ringInverse hlr hU hper hs ht b).2.symm

/-- At a fixed pair of times, forward label-flow jets bound the jets of the
inverse Jacobian evaluated along the forward flow. -/
theorem IsLabelFlowOn.norm_iteratedFDeriv_inverseLabelDerivative_le
    (hX : IsLabelFlowOn U X (Icc l r)) (hlr : l < r)
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hper : ∀ u ∈ Icc l r, SpatiallyPeriodic (U u))
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) {n : ℕ}
    (hFlow : ContDiff ℝ (n + 1 : ℕ) (X s t)) (a : Vec3) {D C : ℝ}
    (hD : 1 ≤ D) (hC : 1 ≤ C)
    (hInv : ‖fderiv ℝ (X t s) (X s t a)‖ ≤ D)
    (hJets : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ (i + 1) (X s t) a‖ ≤ C * D ^ (5 * i + 1)) :
    ‖iteratedFDeriv ℝ n (fun b => fderiv ℝ (X t s) (X s t b)) a‖ ≤
      (n.factorial : ℝ) ^ 2 * C ^ n * D ^ (7 * n + 1) := by
  have hinv (b : Vec3) := hX.inverseLabelDerivative_eq_ringInverse hlr hU hper hs ht b
  have hEq : (Ring.inverse ∘ fderiv ℝ (X s t)) = fun b => fderiv ℝ (X t s) (X s t b) :=
    funext fun b => (hinv b).2
  rw [← hEq]
  have hF : ContDiff ℝ (n : ℕ) (fderiv ℝ (X s t)) :=
    hFlow.fderiv_right (by simp)
  exact norm_iteratedFDeriv_inverse_coefficient_le (p := 5) hF
    (fun b => (hinv b).1) hD hC (by rw [(hinv a).2]; exact hInv)
    (fun i hi hin => by rw [norm_iteratedFDeriv_fderiv]; exact hJets i hi hin)

/-- The label derivatives of the transported covector inherit the coframe
bounds with a single factor of the launch covector's length. -/
theorem IsLabelFlowOn.norm_iteratedFDeriv_labelWaveVector_le
    (hX : IsLabelFlowOn U X (Icc l r)) (hlr : l < r)
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hper : ∀ u ∈ Icc l r, SpatiallyPeriodic (U u))
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) {n : ℕ}
    (hFlow : ContDiff ℝ (n + 1 : ℕ) (X s t)) (a k : Vec3) {D C : ℝ}
    (hD : 1 ≤ D) (hC : 1 ≤ C)
    (hInv : ‖fderiv ℝ (X t s) (X s t a)‖ ≤ D)
    (hJets : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ (i + 1) (X s t) a‖ ≤ C * D ^ (5 * i + 1)) :
    ‖iteratedFDeriv ℝ n (fun b => labelWaveVector X s b k t) a‖ ≤
      ‖k‖ * ((n.factorial : ℝ) ^ 2 * C ^ n * D ^ (7 * n + 1)) := by
  let G (b : Vec3) := fderiv ℝ (X t s) (X s t b)
  let J := ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)
  have hG : ContDiffAt ℝ n G a :=
    (hX.contDiff_inverseLabelDerivative hlr hU hper hs ht hFlow).contDiffAt
  have hJG : ContDiffAt ℝ n (J ∘ G) a :=
    (J.toContinuousLinearEquiv.contDiff.contDiffAt).comp a hG
  calc
    _ ≤ ‖k‖ * ‖iteratedFDeriv ℝ n (J ∘ G) a‖ :=
      norm_iteratedFDeriv_clm_apply_const hJG le_rfl
    _ = ‖k‖ * ‖iteratedFDeriv ℝ n G a‖ := by
      rw [J.norm_iteratedFDeriv_comp_left G a n]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hX.norm_iteratedFDeriv_inverseLabelDerivative_le hlr hU hper hs ht hFlow a hD hC hInv hJets)
      (norm_nonneg _)

/-- Zeroth-order bounds for the deformation and its inverse control the
ratio of the transported covector's length to that of its launch value. -/
theorem IsLabelFlowOn.norm_labelWaveVector_bounds
    (hX : IsLabelFlowOn U X (Icc l r)) (hlr : l < r)
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hper : ∀ u ∈ Icc l r, SpatiallyPeriodic (U u))
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) (a k : Vec3) {D : ℝ}
    (hD : 0 < D) (hF : ‖fderiv ℝ (X s t) a‖ ≤ D)
    (hG : ‖fderiv ℝ (X t s) (X s t a)‖ ≤ D) :
    ‖k‖ / D ≤ ‖labelWaveVector X s a k t‖ ∧
      ‖labelWaveVector X s a k t‖ ≤ D * ‖k‖ := by
  let F := fderiv ℝ (X s t) a
  let G := fderiv ℝ (X t s) (X s t a)
  change ‖k‖ / D ≤ ‖G.adjoint k‖ ∧ ‖G.adjoint k‖ ≤ D * ‖k‖
  have hGF : G.comp F = .id ℝ Vec3 := (hX.labelDerivative_inverse hlr hU hper hs ht a).1
  have hAdj : F.adjoint.comp G.adjoint = .id ℝ Vec3 := by
    simpa only [adjoint_comp, adjoint_id] using congrArg
      (fun L : Vec3 →L[ℝ] Vec3 => L.adjoint) hGF
  have hRec : F.adjoint (G.adjoint k) = k :=
    congrArg (fun L : Vec3 →L[ℝ] Vec3 => L k) hAdj
  constructor
  · rw [div_le_iff₀ hD, mul_comm]
    conv_lhs => rw [← hRec]
    exact (F.adjoint.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((adjoint.norm_map F).trans_le hF) (norm_nonneg _))
  · exact (G.adjoint.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((adjoint.norm_map G).trans_le hG) (norm_nonneg _))

end Deformation

section ParentComposition

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The composition bound in (5.7) for supplied forward flow jets. Both
constants here can be finite upper bounds for the order-dependent constants
through order `n`. -/
theorem norm_iteratedFDeriv_parentComposition_le {f : F → G} {Y : E → F} {n : ℕ}
    (hf : ContDiff ℝ n f) (hY : ContDiff ℝ n Y) (x : E) {D Cₓ C_f A_f : ℝ}
    (hD : 1 ≤ D) (hCₓ : 1 ≤ Cₓ) (hC_f : 0 ≤ C_f) (hA_f : 0 ≤ A_f)
    (hYJets : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i Y x‖ ≤ Cₓ * D ^ (5 * i))
    (hfJets : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f (Y x)‖ ≤ C_f * A_f * D ^ i) :
    ‖iteratedFDeriv ℝ n (f ∘ Y) x‖ ≤
      (n.factorial : ℝ) * C_f * Cₓ ^ n * A_f * D ^ (6 * n) := by
  have hOuter (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i f (Y x)‖ ≤ C_f * A_f * D ^ n :=
    (hfJets i hi).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hi)
      (mul_nonneg hC_f hA_f))
  have hInner (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i Y x‖ ≤ (Cₓ * D ^ 5) ^ i := by
    refine (hYJets i hi hin).trans ?_
    rw [mul_pow, ← pow_mul]
    exact mul_le_mul_of_nonneg_right (le_self_pow₀ hCₓ (by omega)) (by positivity)
  calc
    _ ≤ (n.factorial : ℝ) * (C_f * A_f * D ^ n) * (Cₓ * D ^ 5) ^ n :=
      norm_iteratedFDeriv_comp_le hf hY le_rfl x hOuter hInner
    _ = _ := by
      rw [mul_pow, ← pow_mul, show 6 * n = n + 5 * n by omega, pow_add]
      ring

end ParentComposition

section WaveCoefficients

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Leibniz's bound preserves a common linear slope in the derivative order,
adding the zeroth-order scale exponents. -/
theorem norm_iteratedFDeriv_bilinear_scaled_le
    (B : F →L[ℝ] G →L[ℝ] H) (hB : ‖B‖ ≤ 1) {f : E → F} {g : E → G}
    {n p q r : ℕ} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (x : E)
    {D C₁ C₂ : ℝ}
    (h₁ : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ C₁ * D ^ (p * i + q))
    (h₂ : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ C₂ * D ^ (p * i + r)) :
    ‖iteratedFDeriv ℝ n (fun y => B (f y) (g y)) x‖ ≤
      (2 : ℝ) ^ n * (C₁ * C₂) * D ^ (p * n + q + r) := by
  let M := (C₁ * C₂) * D ^ (p * n + q + r)
  have hterm (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ ≤ M := by
    have hin : i ≤ n := by simpa using Finset.mem_range.mp hi
    have heq : (p * i + q) + (p * (n - i) + r) = p * n + q + r := by
      have hadd : p * i + p * (n - i) = p * n := by rw [← Nat.mul_add, Nat.add_sub_of_le hin]
      omega
    calc
      _ ≤ (C₁ * D ^ (p * i + q)) * (C₂ * D ^ (p * (n - i) + r)) :=
        mul_le_mul (h₁ i hin) (h₂ (n - i) (Nat.sub_le _ _)) (norm_nonneg _)
          ((norm_nonneg _).trans (h₁ i hin))
      _ = M := by
        dsimp only [M]
        rw [← heq, pow_add]
        ring
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ :=
      B.norm_iteratedFDeriv_le_of_bilinear_of_le_one hf hg x le_rfl hB
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * M := by
      refine Finset.sum_le_sum fun i hi => ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hterm i hi) (Nat.cast_nonneg _)
    _ = _ := by
      have hChoose : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
        exact_mod_cast Nat.sum_range_choose n
      rw [← Finset.sum_mul, hChoose]
      dsimp only [M]
      ring

set_option maxHeartbeats 500000 in
set_option maxSynthPendingDepth 4 in
/-- The reciprocal squared length and wave-direction projection have polynomial
jet bounds in the parent scale. The input is the normalized wave vector
with the coframe jet bound and the reciprocal zeroth-order bound from (5.3). -/
theorem norm_iteratedFDeriv_waveCoefficients_le {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {κ : E → V} {n : ℕ}
    (hκ : ContDiff ℝ n κ) (hnz : ∀ y, κ y ≠ 0) (x : E) {D C : ℝ}
    (hD : 1 ≤ D) (hC : 1 ≤ C) (hInv : (‖κ x‖ ^ 2)⁻¹ ≤ D ^ 4)
    (hJets : ∀ i ≤ n, ‖iteratedFDeriv ℝ i κ x‖ ≤ C * D ^ (7 * i + 2)) :
    let B : ℝ := 2 ^ n * (C * C)
    let R : ℝ := (n.factorial : ℝ) ^ 2 * B ^ n
    ‖iteratedFDeriv ℝ n (fun y => (‖κ y‖ ^ 2)⁻¹) x‖ ≤ R * D ^ (16 * n + 4) ∧
      ‖iteratedFDeriv ℝ n
        (fun y => (‖κ y‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ (κ y) (κ y)) x‖ ≤
        2 ^ n * (R * B) * D ^ (16 * n + 8) := by
  let B : ℝ := 2 ^ n * (C * C)
  let R : ℝ := (n.factorial : ℝ) ^ 2 * B ^ n
  let q (y : E) : ℝ := ‖κ y‖ ^ 2
  let P (y : E) : V →L[ℝ] V := InnerProductSpace.rankOne ℝ (κ y) (κ y)
  let I : V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ
  let A : V →L[ℝ] (V →L[ℝ] (V →L[ℝ] V)) := InnerProductSpace.rankOne ℝ
  have hqEq : (fun y => I (κ y) (κ y)) = q :=
    funext fun y => real_inner_self_eq_norm_sq (κ y)
  have hA : ‖A‖ ≤ 1 := by
    refine opNorm_le_bound _ zero_le_one fun u => ?_
    rw [one_mul]
    exact opNorm_le_bound _ (norm_nonneg u) fun v =>
      (InnerProductSpace.norm_rankOne (𝕜 := ℝ) u v).le
  have hq : ContDiff ℝ n q := by
    rw [← hqEq]
    exact (I.contDiff.comp hκ).clm_apply hκ
  have hP : ContDiff ℝ n P := by
    change ContDiff ℝ n (fun y => A (κ y) (κ y))
    exact (A.contDiff.comp hκ).clm_apply hκ
  have hB : 1 ≤ B := by
    dsimp only [B]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (by norm_num)) (one_le_mul_of_one_le_of_one_le hC hC)
  have hB' (i : ℕ) (hi : i ≤ n) : (2 : ℝ) ^ i * (C * C) ≤ B := by
    dsimp only [B]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) (mul_self_nonneg C)
  have hqJets (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i q x‖ ≤ B * D ^ (7 * i + 4) := by
    rw [← hqEq]
    have hκ' : ContDiff ℝ i κ := hκ.of_le (by exact_mod_cast hi)
    exact (norm_iteratedFDeriv_bilinear_scaled_le I (norm_innerSL_le ℝ) hκ' hκ' x
      (fun j hj => hJets j (hj.trans hi)) (fun j hj => hJets j (hj.trans hi))).trans
        (mul_le_mul_of_nonneg_right (hB' i hi) (by positivity))
  have hqPos (y : E) : 0 < q y := sq_pos_of_pos (norm_pos_iff.mpr (hnz y))
  have hqInv : ContDiff ℝ n fun y => (q y)⁻¹ := hq.inv fun y => (hqPos y).ne'
  have hInvJets (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fun y => (q y)⁻¹) x‖ ≤ R * D ^ (16 * i + 4) := by
    have hJ (j : ℕ) (_hj : 1 ≤ j) (hji : j ≤ i) :
        ‖iteratedFDeriv ℝ j q x‖ ≤ B * (D ^ 4) ^ (2 * j + 1) := by
      refine (hqJets j (hji.trans hi)).trans ?_
      rw [← pow_mul]
      gcongr
      omega
    have hz : ‖Ring.inverse (q x)‖ ≤ D ^ 4 := by
      rw [Ring.inverse_eq_inv', Real.norm_of_nonneg (inv_nonneg.mpr (hqPos x).le)]
      exact hInv
    have h := norm_iteratedFDeriv_inverse_coefficient_le (p := 2)
      (hq.of_le (by exact_mod_cast hi)) (fun y => isUnit_iff_ne_zero.mpr (hqPos y).ne')
      (one_le_pow₀ hD) hB hz hJ
    simp only [Function.comp_def, Ring.inverse_eq_inv'] at h
    refine h.trans ?_
    rw [← pow_mul, show 4 * ((2 + 2) * i + 1) = 16 * i + 4 by omega]
    dsimp only [R]
    gcongr
  have hPJets (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i P x‖ ≤ B * D ^ (16 * i + 4) := by
    have hκ' : ContDiff ℝ i κ := hκ.of_le (by exact_mod_cast hi)
    refine (norm_iteratedFDeriv_bilinear_scaled_le A hA hκ' hκ' x
      (fun j hj => hJets j (hj.trans hi)) (fun j hj => hJets j (hj.trans hi))).trans ?_
    exact mul_le_mul (hB' i hi) (pow_le_pow_right₀ hD (by omega))
      (by positivity) (zero_le_one.trans hB)
  exact ⟨hInvJets n le_rfl,
    norm_iteratedFDeriv_bilinear_scaled_le (lsmul ℝ ℝ) opNorm_lsmul_le hqInv hP x
      hInvJets hPJets⟩

end WaveCoefficients

end TorusEuler
