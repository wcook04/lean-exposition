import TorusEuler.EndpointPhysicalJetEstimates
import TorusEuler.EndpointMixedProjectionUniform

/-! Duration-uniform polynomial caps for the physical endpoint inverse. -/

open Filter MeasureTheory Set
open scoped InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal
local notation "μt" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "Paths(" T ")" => Lp Vec3 2 (μt T)
local notation "MixedCoefficient(" T ")" => HalfHolder A (Paths(T) →L[ℝ] Paths(T))
local notation "P[" T "]" => endpointStrongMixedLeray T
local notation "W[" T "]" => freezingFixedSpace (endpointStrongMixedLeray T)

local instance physicalInverseCapSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance physicalInverseCapSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

private theorem dist_inverseCapTorus_le_one (a b : A) : dist a b ≤ 1 := by
  apply (dist_pi_le_iff zero_le_one).mpr
  intro i
  rw [dist_eq_norm]
  exact (AddCircle.norm_le_half_period (1 : ℝ) (x := a i - b i) (by norm_num : (1 : ℝ) ≠ 0)).trans
    (by norm_num)

/-- Pointwise zeroth- and first-order bounds on the lift control the actual
coefficient's torus half-Hölder norm and Lipschitz constant. -/
theorem endpointHalfHolderCaps_of_lift_gradient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (K : ℝ → HalfHolder A E) (k : ℝ → Vec3 → E)
    (hEval : ∀ t ∈ Icc 0 T, ∀ x, HalfHolder.eval (toUnitTorus x) (K t) = k t x)
    (hDifferentiable : ∀ t ∈ Icc 0 T, Differentiable ℝ (k t))
    (hValue : ∀ t ∈ Icc 0 T, ∀ x, ‖k t x‖ ≤ C)
    (hGradient : ∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (k t) x‖ ≤ L) :
    (∀ t ∈ Icc 0 T, ‖K t‖ ≤ C + 2 * L) ∧
      ∀ t ∈ Icc 0 T, ∀ a b : A, ‖HalfHolder.eval a (K t) - HalfHolder.eval b (K t)‖ ≤ 2 * L * dist a b := by
  have hL₀ := mul_nonneg zero_le_two hL
  have hLip (t : ℝ) (ht : t ∈ Icc 0 T) (a b : A) :
      ‖HalfHolder.eval a (K t) - HalfHolder.eval b (K t)‖ ≤ 2 * L * dist a b := by
    obtain ⟨x, y, hx, hy, hxy⟩ := holderBridge_exists_close_lifts a b
    have hx' : HalfHolder.eval a (K t) = k t x := hx ▸ hEval t ht x
    have hy' : HalfHolder.eval b (K t) = k t y := hy ▸ hEval t ht y
    rw [hx', hy']
    calc
      _ ≤ L * ‖x - y‖ := Convex.norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => hDifferentiable t ht z) (fun z _ => hGradient t ht z)
        (convex_univ : Convex ℝ (univ : Set Vec3)) (mem_univ y) (mem_univ x)
      _ ≤ L * (2 * dist a b) := mul_le_mul_of_nonneg_left hxy hL
      _ = _ := by ring
  refine ⟨fun t ht => (HalfHolder.norm_le_iff (add_nonneg hC hL₀)).2 ⟨?_, ?_⟩, hLip⟩
  · intro a
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    change ‖HalfHolder.eval (toUnitTorus x) (K t)‖ ≤ _
    rw [hEval t ht x]
    exact (hValue t ht x).trans (le_add_of_nonneg_right hL₀)
  · intro a b
    change ‖HalfHolder.eval a (K t) - HalfHolder.eval b (K t)‖ ≤ _
    have hd : dist a b ≤ Real.sqrt (dist a b) := by
      apply Real.le_sqrt_of_sq_le
      rw [pow_two]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (dist_inverseCapTorus_le_one a b) dist_nonneg
    exact (hLip t ht a b).trans (mul_le_mul (le_add_of_nonneg_left hC) hd dist_nonneg (add_nonneg hC hL₀))

/-- Label Lipschitz control of the strong coefficient transfers to the actual
mixed time-path operator through its almost-everywhere action. -/
theorem norm_endpointMixedCoefficient_sub_le_of_timeSlices {T L : ℝ} (hL : 0 ≤ L)
    (Kmix : MixedCoefficient(T)) (K : ℝ → K½)
    (hLip : ∀ t ∈ Icc 0 T, ∀ a b : A,
      ‖HalfHolder.eval a (K t) - HalfHolder.eval b (K t)‖ ≤ L * dist a b)
    (hMix : ∀ (a : A) (v : Paths(T)), (fun t => HalfHolder.eval a Kmix v t) =ᵐ[μt T]
      fun t => HalfHolder.eval a (K t) (v t)) (a b : A) :
    ‖HalfHolder.eval a Kmix - HalfHolder.eval b Kmix‖ ≤ L * dist a b := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hL dist_nonneg)
  intro v
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hMix a v, hMix b v, ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := 0) (b := T)),
    Lp.coeFn_sub (HalfHolder.eval a Kmix v) (HalfHolder.eval b Kmix v)] with t ha hb ht hsub
  change HalfHolder.eval a Kmix v t = _ at ha
  change HalfHolder.eval b Kmix v t = _ at hb
  rw [_root_.sub_apply, hsub, Pi.sub_apply, ha, hb, ← _root_.sub_apply]
  exact (HalfHolder.eval a (K t) - HalfHolder.eval b (K t)).le_of_opNorm_le
    (hLip t (Ioc_subset_Icc_self ht) a b) (v t)

set_option maxHeartbeats 5000000 in
/-- Uniform inverse caps for the actual physical time-slice and mixed
compressions. The constants are independent of the slab duration. -/
theorem exists_endpointPhysicalInverseCaps (a : ℕ) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {T D μ μmix CK CΩ LK LΩ : ℝ} (hT : 0 < T), T ≤ 1 → 1 ≤ D →
      ∀ (Kmix Ωmix : MixedCoefficient(T)) (K Ω : ℝ → K½),
      ContinuousOn K (Icc 0 T) → ContinuousOn Ω (Icc 0 T) →
      (∀ (b : A) (v : Paths(T)), (fun t => HalfHolder.eval b Kmix v t) =ᵐ[μt T]
        fun t => HalfHolder.eval b (K t) (v t)) →
      (∀ (b : A) (v : Paths(T)), (fun t => HalfHolder.eval b Ωmix v t) =ᵐ[μt T]
        fun t => HalfHolder.eval b (Ω t) (v t)) →
      0 ≤ CK → 0 ≤ CΩ → 0 ≤ LK → 0 ≤ LΩ →
      (∀ t ∈ Icc 0 T, ‖K t‖ ≤ CK) → (∀ t ∈ Icc 0 T, ‖Ω t‖ ≤ CΩ) →
      (∀ t ∈ Icc 0 T, ∀ b c : A,
        ‖HalfHolder.eval b (K t) - HalfHolder.eval c (K t)‖ ≤ LK * dist b c) →
      (∀ t ∈ Icc 0 T, ∀ b c : A,
        ‖HalfHolder.eval b (Ω t) - HalfHolder.eval c (Ω t)‖ ≤ LΩ * dist b c) →
      0 < μ → 0 < μmix →
      (∀ t ∈ Icc 0 T, ∀ b v, μ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval b (K t) v, v⟫_ℝ) →
      (∀ b (v : Paths(T)), endpointIntegral T v = 0 → μmix * ‖v‖ ^ 2 ≤
        ⟪HalfHolder.eval b (endpointMixedPathCoefficient hT.le Kmix Ωmix) v, v⟫_ℝ) →
      4 + μ⁻¹ + μmix⁻¹ + CK + CΩ + LK + LΩ ≤ C₀ * D ^ a →
      ∃ (eS : ℝ → S ≃L[ℝ] S) (eM : W[T] ≃L[ℝ] W[T]) (As Am : ℝ),
        (∀ t ∈ Icc 0 T, ∀ v : S,
          eS t v = endpointStrongSpatialProjection ((K t).coefficientMul v.val)) ∧
        (∀ t ∈ Icc 0 T, ‖((eS t).symm : S →L[ℝ] S)‖ ≤ As) ∧
        (eM : W[T] →L[ℝ] W[T]) = freezingCompression P[T]
          (endpointMixedPathCoefficient hT.le Kmix Ωmix).coefficientMul
          (endpointStrongMixedLeray_idempotent hT) ∧
        ‖(eM.symm : W[T] →L[ℝ] W[T])‖ ≤ Am ∧
        endpointPhysicalInverseBudget hT.le Kmix Ωmix As Am ≤ C * D ^ (291 * a) := by
  classical
  obtain ⟨Cs, hCs, hSpatial⟩ := exists_endpointSpatialSolenoidalInverse
  obtain ⟨Cm, hCm, hMixed⟩ := exists_endpointMixedLerayInverse_uniform
  obtain ⟨Pm, hPm, hpMixed⟩ := exists_norm_endpointStrongMixedLeray_le
  let Ps := ‖endpointStrongSpatialProjection‖
  have hPs : 0 ≤ Ps := endpointStrongSpatialProjection.opNorm_nonneg
  let C := (Cs * Ps * (2 + 6 * Cm * Pm)) * C₀ ^ 291
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (mul_nonneg hCs hPs) (add_nonneg zero_le_two
      (mul_nonneg (mul_nonneg (by norm_num) hCm) hPm))) (pow_nonneg (zero_le_one.trans hC₀) _)
  refine ⟨C, hC, ?_⟩
  intro T D μ μmix CK CΩ LK LΩ hT hT₁ hD Kmix Ωmix K Ω hK hΩ hKa hΩa hCK hCΩ hLK hLΩ
    hKBound hΩBound hKLip hΩLip hμ hμmix hKPos hBPos hInput
  let Q := C₀ * D ^ a
  have hQ : 1 ≤ Q := one_le_mul_of_one_le_of_one_le hC₀ (one_le_pow₀ hD)
  have hQ₀ : 0 ≤ Q := zero_le_one.trans hQ
  have hμ₀ : 0 ≤ μ⁻¹ := inv_nonneg.mpr hμ.le
  have hμmix₀ : 0 ≤ μmix⁻¹ := inv_nonneg.mpr hμmix.le
  have hKsup (t : ℝ) (ht : t ∈ Icc 0 T) : ‖(K t).val.1‖ ≤ CK := by
    apply (BoundedContinuousFunction.norm_le hCK).mpr
    exact ((HalfHolder.norm_le_iff hCK).mp (hKBound t ht)).1
  let As := Cs * Q ^ 145
  let Am := Cm * Q ^ 145
  have hAs₀ : 0 ≤ As := mul_nonneg hCs (pow_nonneg hQ₀ _)
  have hAm₀ : 0 ≤ Am := mul_nonneg hCm (pow_nonneg hQ₀ _)
  have hSpatialData (t : Icc (0 : ℝ) T) : ∃ e : S ≃L[ℝ] S,
      (∀ v : S, e v = endpointStrongSpatialProjection ((K t).coefficientMul v.val)) ∧
      ‖(e.symm : S →L[ℝ] S)‖ ≤ As := by
    obtain ⟨e, he, hBound⟩ := hSpatial (K t) hμ hLK (hKLip t t.property) (hKPos t t.property)
    refine ⟨e, he, hBound.trans ?_⟩
    have hScale : 4 + μ⁻¹ + ‖(K t).val.1‖ + LK ≤ Q := by
      change 4 + μ⁻¹ + ‖(K t).val.1‖ + LK ≤ C₀ * D ^ a
      linarith only [hKsup t t.property, hInput, hμmix₀, hCΩ, hLΩ]
    have hScale₀ : 0 ≤ 4 + μ⁻¹ + ‖(K t).val.1‖ + LK :=
      add_nonneg (add_nonneg (add_nonneg (by norm_num) hμ₀) (norm_nonneg _)) hLK
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hScale₀ hScale 145) hCs
  choose e hForward hSpatialCap using hSpatialData
  let eS (t : ℝ) := if ht : t ∈ Icc 0 T then e ⟨t, ht⟩ else ContinuousLinearEquiv.refl ℝ S
  have heS (t : ℝ) (ht : t ∈ Icc 0 T) (v : S) :
      eS t v = endpointStrongSpatialProjection ((K t).coefficientMul v.val) := by
    simpa only [eS, dite_eq_left ht] using hForward ⟨t, ht⟩ v
  have hAs (t : ℝ) (ht : t ∈ Icc 0 T) : ‖((eS t).symm : S →L[ℝ] S)‖ ≤ As := by
    simpa only [eS, dite_eq_left ht] using hSpatialCap ⟨t, ht⟩
  let B := endpointMixedPathCoefficient hT.le Kmix Ωmix
  let Lmix := LK + T * LΩ
  have hLmix : 0 ≤ Lmix := add_nonneg hLK (mul_nonneg hT.le hLΩ)
  have hBLip (b c : A) : ‖HalfHolder.eval b B - HalfHolder.eval c B‖ ≤ Lmix * dist b c :=
    norm_endpointMixedPathCoefficient_sub_le hT.le Kmix Ωmix
      (norm_endpointMixedCoefficient_sub_le_of_timeSlices hLK Kmix K hKLip hKa)
      (norm_endpointMixedCoefficient_sub_le_of_timeSlices hLΩ Ωmix Ω hΩLip hΩa) b c
  have hKmix := norm_endpointMixedCoefficient_le_of_timeSlices hCK Kmix K hK hKBound
    (Eventually.of_forall hKa)
  have hΩmix := norm_endpointMixedCoefficient_le_of_timeSlices hCΩ Ωmix Ω hΩ hΩBound
    (Eventually.of_forall hΩa)
  have hBsup : ‖B.val.1‖ ≤ CK + T * CΩ := norm_endpointMixedPathCoefficient_sup_le hT.le
    Kmix Ωmix hCK hCΩ ((HalfHolder.norm_le_iff hCK).mp hKmix).1 ((HalfHolder.norm_le_iff hCΩ).mp hΩmix).1
  obtain ⟨eM, heM, hInverse⟩ := hMixed hT B hμmix hLmix hBLip hBPos
  have hMixedScale : 4 + μmix⁻¹ + ‖B.val.1‖ + Lmix ≤ Q := by
    have hΩT := mul_le_of_le_one_left hCΩ hT₁
    have hLΩT := mul_le_of_le_one_left hLΩ hT₁
    dsimp only [Lmix, Q]
    linarith only [hBsup, hΩT, hLΩT, hμ₀, hInput]
  have hMixedScale₀ : 0 ≤ 4 + μmix⁻¹ + ‖B.val.1‖ + Lmix :=
    add_nonneg (add_nonneg (add_nonneg (by norm_num) hμmix₀) (norm_nonneg _)) hLmix
  have hAm : ‖(eM.symm : W[T] →L[ℝ] W[T])‖ ≤ Am :=
    hInverse.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMixedScale₀ hMixedScale 145) hCm)
  refine ⟨eS, eM, As, Am, heS, hAs, heM, hAm, ?_⟩
  have hKn := endpointClosedTimeNorm_le hT.le hKBound
  have hΩn := endpointClosedTimeNorm_le hT.le hΩBound
  have hKQ : endpointClosedTimeNorm T K ≤ Q := by
    change endpointClosedTimeNorm T K ≤ C₀ * D ^ a
    linarith only [hKn, hInput, hμ₀, hμmix₀, hCΩ, hLK, hLΩ]
  have hΩQ : endpointClosedTimeNorm T Ω ≤ Q := by
    change endpointClosedTimeNorm T Ω ≤ C₀ * D ^ a
    linarith only [hΩn, hInput, hμ₀, hμmix₀, hCK, hLK, hLΩ]
  let cost := 2 * endpointClosedTimeNorm T K + 4 * T * endpointClosedTimeNorm T Ω
  have hCost₀ : 0 ≤ cost := add_nonneg
    (mul_nonneg zero_le_two (endpointClosedTimeNorm_nonneg hT.le K))
    (mul_nonneg (mul_nonneg (by norm_num) hT.le) (endpointClosedTimeNorm_nonneg hT.le Ω))
  have hCost : cost ≤ 6 * Q := by
    have h := mul_le_of_le_one_left (endpointClosedTimeNorm_nonneg hT.le Ω) hT₁
    dsimp only [cost]
    linarith only [hKQ, hΩQ, h]
  have hCap := endpointPhysicalInverseBudget_le_of_timeSlices hT.le hAs₀ hAm₀ Kmix Ωmix K Ω hK hΩ
    (Eventually.of_forall hKa) (Eventually.of_forall hΩa)
  refine hCap.trans ((endpointRecoveryBudget_scalar_le_power hQ hCs hCm hPs hAm₀ hPs
    (P[T]).opNorm_nonneg hCost₀ (le_refl As) (le_refl Am) (le_refl Ps) (hpMixed T hT) hCost).trans_eq ?_)
  dsimp only [Q, C]
  rw [mul_pow, ← pow_mul, Nat.mul_comm a 291]
  simp only [mul_assoc]

/-- A fixed nonnegative prefactor can be absorbed into a fixed power at a
base parameter at least two. -/
theorem exists_endpointPower_absorb_prefactor (C : ℝ) (a : ℕ) :
    ∃ b : ℕ, ∀ D : ℝ, 2 ≤ D → C * D ^ a ≤ D ^ b := by
  obtain ⟨n, _, hn⟩ := exists_nat_pow_near (x := max 1 C) (y := (2 : ℝ))
    (le_max_left _ _) (by norm_num)
  refine ⟨n + 1 + a, fun D hD => ?_⟩
  have h₀ : 0 ≤ D := (by norm_num : (0 : ℝ) ≤ 2).trans hD
  have hC : C ≤ D ^ (n + 1) :=
    ((le_max_right 1 C).trans hn.le).trans (pow_le_pow_left₀ (by norm_num) hD _)
  rw [pow_add]
  exact mul_le_mul_of_nonneg_right hC (pow_nonneg h₀ _)

/-- The physical parent powers at orders zero and one fit a common ninth
power, including both coercivity costs. -/
theorem endpointInverseCommonScale_le_power_nine {D M CK CΩ LK LΩ : ℝ}
    (hD : 1 ≤ D) (hM : 0 ≤ M) (hMD : M ≤ D)
    (hCK : 0 ≤ CK) (hCΩ : 0 ≤ CΩ) (hLK : 0 ≤ LK) (_hLΩ : 0 ≤ LΩ) :
    4 + ((D ^ 2)⁻¹)⁻¹ + (1 / (2 * D ^ 2 * (1 + M) ^ 2))⁻¹ +
        (CK * D ^ 2 + 2 * LK * D ^ 7) + (CΩ * D ^ 3 + 2 * LΩ * D ^ 9) +
        2 * LK * D ^ 7 + 2 * LΩ * D ^ 9 ≤
      (13 + CK + CΩ + 4 * LK + 4 * LΩ) * D ^ 9 := by
  have hSum : 1 + M ≤ 2 * D := by linarith only [hD, hMD]
  have hMix : 2 * D ^ 2 * (1 + M) ^ 2 ≤ 8 * D ^ 9 := by
    calc
      _ ≤ 2 * D ^ 2 * (2 * D) ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith only [hM]) hSum 2) (mul_nonneg zero_le_two (sq_nonneg D))
      _ = 8 * D ^ 4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by decide)) (by norm_num)
  have hPow₂ : D ^ 2 ≤ D ^ 9 := pow_le_pow_right₀ hD (by decide)
  have hPow₃ : D ^ 3 ≤ D ^ 9 := pow_le_pow_right₀ hD (by decide)
  have hPow₇ : D ^ 7 ≤ D ^ 9 := pow_le_pow_right₀ hD (by decide)
  have h4 : (4 : ℝ) ≤ 4 * D ^ 9 := le_mul_of_one_le_right (by norm_num) (one_le_pow₀ hD)
  have hK := mul_le_mul_of_nonneg_left hPow₂ hCK
  have hΩ := mul_le_mul_of_nonneg_left hPow₃ hCΩ
  have hL := mul_le_mul_of_nonneg_left hPow₇ hLK
  simp only [one_div, inv_inv]
  nlinarith only [hMix, hPow₂, h4, hK, hΩ, hL]

end

end TorusEuler
