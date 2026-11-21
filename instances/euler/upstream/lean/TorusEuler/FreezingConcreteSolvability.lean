import TorusEuler.FreezingConcreteMultipliers
import TorusEuler.FreezingSolvability

/-! Concrete frozen Fourier multipliers supply the uniform estimates for the
projected half-Hölder inverse in Appendix A.2. -/

open ContinuousLinearMap Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler

universe u v

private theorem freezingRadius_bounds {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) :
    let R := 1 + 16 * C * L
    let r := (R⁻¹) ^ 2
    1 ≤ R ∧ 0 < r ∧ r ≤ 1 ∧ 8 * C * L * Real.sqrt r ≤ 1 / 2 := by
  intro R r
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hC) hL]
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hRinv : 0 < R⁻¹ := inv_pos.mpr hRpos
  have hr : r ≤ 1 := by
    dsimp [r]
    simpa only [one_pow] using pow_le_pow_left₀ hRinv.le ((inv_le_one₀ hRpos).mpr hR) 2
  refine ⟨hR, pow_pos hRinv _, hr, ?_⟩
  rw [show Real.sqrt r = R⁻¹ from Real.sqrt_sq hRinv.le, ← div_eq_mul_inv]
  apply (div_le_iff₀ hRpos).mpr
  dsimp [R]
  linarith

private theorem freezingLowerOrder_polynomial {C K L M Q : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hQ : 1 ≤ Q) (hLQ : L ≤ Q) (hMQ : 1 + M ≤ Q) :
    let R := 1 + 16 * (C * Q ^ 11) * L
    let r := (R⁻¹) ^ 2
    let D := K * Q ^ 11 / r
    let J := 1 + 2 * K * (1 + 16 * C) ^ 2 + 4 * (1 + 16 * C)
    freezingLowerOrder r (2 * D * (1 + M)) ≤ J * Q ^ 36 := by
  intro R r D J
  have hQ₀ : 0 ≤ Q := zero_le_one.trans hQ
  have hR : 1 ≤ R := (freezingRadius_bounds (mul_nonneg hC (pow_nonneg hQ₀ _)) hL).1
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hr : r ≤ 1 := (freezingRadius_bounds (mul_nonneg hC (pow_nonneg hQ₀ _)) hL).2.2.1
  have hRinv : 0 < R⁻¹ := inv_pos.mpr hRpos
  have hsqrt : Real.sqrt (r / 4) = R⁻¹ / 2 := by
    rw [show r / 4 = (R⁻¹ / 2) ^ 2 by dsimp [r]; ring]
    exact Real.sqrt_sq (by positivity)
  have hsqrt₁ : Real.sqrt (r / 4) ≤ 1 := by
    rw [hsqrt]
    linarith [(inv_le_one₀ hRpos).mpr hR]
  have hRbd : R ≤ (1 + 16 * C) * Q ^ 12 := calc
    R ≤ Q ^ 12 + 16 * (C * Q ^ 11) * Q := by
      dsimp [R]
      gcongr
      exact one_le_pow₀ hQ
    _ = _ := by ring
  have hDbd : D ≤ K * (1 + 16 * C) ^ 2 * Q ^ 35 := calc
    D = K * Q ^ 11 * R ^ 2 := by
      dsimp [D, r]
      rw [div_eq_mul_inv, ← inv_pow, inv_inv]
    _ ≤ K * Q ^ 11 * ((1 + 16 * C) * Q ^ 12) ^ 2 := by gcongr
    _ = _ := by ring
  have hfar : 2 * D * (1 + M) * Real.sqrt (r / 4) ≤
      (2 * K * (1 + 16 * C) ^ 2) * Q ^ 36 := calc
    _ ≤ 2 * (K * (1 + 16 * C) ^ 2 * Q ^ 35) * Q * 1 := by
      have hD₀ : 0 ≤ D := by dsimp [D, r]; positivity
      gcongr
    _ = _ := by ring
  have hdistant : 2 / Real.sqrt (r / 4) ≤ (4 * (1 + 16 * C)) * Q ^ 36 := calc
    _ = 4 * R := by
      rw [hsqrt]
      field_simp
      ring
    _ ≤ 4 * ((1 + 16 * C) * Q ^ 12) := mul_le_mul_of_nonneg_left hRbd (by norm_num)
    _ = (4 * (1 + 16 * C)) * Q ^ 12 := by ring
    _ ≤ _ := by
      gcongr
      norm_num
  have hJ₁ : 1 ≤ J := by
    dsimp [J]
    have hA : 0 ≤ 2 * K * (1 + 16 * C) ^ 2 := by positivity
    have hB : 0 ≤ 4 * (1 + 16 * C) := by positivity
    linarith
  have hJA : 2 * K * (1 + 16 * C) ^ 2 ≤ J := by
    dsimp [J]
    have hB : 0 ≤ 4 * (1 + 16 * C) := by positivity
    linarith
  have hJB : 4 * (1 + 16 * C) ≤ J := by
    dsimp [J]
    have hA : 0 ≤ 2 * K * (1 + 16 * C) ^ 2 := by positivity
    linarith
  unfold freezingLowerOrder
  apply max_le
  · calc
      1 ≤ 1 * Q ^ 36 := by simpa only [one_mul] using one_le_pow₀ hQ
      _ ≤ _ := mul_le_mul_of_nonneg_right hJ₁ (pow_nonneg hQ₀ _)
  · exact max_le
      (hfar.trans (mul_le_mul_of_nonneg_right hJA (pow_nonneg hQ₀ _)))
      (hdistant.trans (mul_le_mul_of_nonneg_right hJB (pow_nonneg hQ₀ _)))

private theorem freezingInverse_polynomial {C J J₀ νinv Q : ℝ}
    (hC : 0 ≤ C) (hJ : 0 ≤ J) (hJ₀ : 0 ≤ J₀) (hνinv : 0 ≤ νinv)
    (hQ : 1 ≤ Q) (hJQ : J ≤ J₀ * Q ^ 36) (hνQ : νinv ≤ Q) :
    4 * (C * Q ^ 11 + J * (4 * J) ^ 3 * νinv) ≤
      4 * (C + 64 * J₀ ^ 4) * Q ^ 145 := by
  calc
    _ ≤ 4 * (C * Q ^ 145 + (J₀ * Q ^ 36) * (4 * (J₀ * Q ^ 36)) ^ 3 * Q) := by
      gcongr
      norm_num
    _ = _ := by ring

section Torus

variable {H Hc : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Hc] [NormedSpace ℂ Hc] [CompleteSpace Hc]

local notation "Labels" => UnitAddTorus (Fin 3)
local notation "W" => HalfHolder Labels H
local notation "M" => HalfHolder Labels (H →L[ℝ] H)
local notation "Punctured" => ({0}ᶜ : Set Vec3)

omit [CompleteSpace H] in
private theorem freezingCoefficientLine_range_coercive (B : M) {s μ : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (a : Labels) (v : H)
    (hB : μ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a B v, v⟫_ℝ) :
    min 1 μ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a (freezingCoefficientLine B s) v, v⟫_ℝ := by
  calc
    _ = (1 - s) * (min 1 μ * ‖v‖ ^ 2) + s * (min 1 μ * ‖v‖ ^ 2) := by ring
    _ ≤ (1 - s) * ‖v‖ ^ 2 + s * ⟪HalfHolder.eval a B v, v⟫_ℝ :=
      add_le_add (mul_le_mul_of_nonneg_left
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_left 1 μ) (sq_nonneg ‖v‖))
        (sub_nonneg.mpr hs.2))
        (mul_le_mul_of_nonneg_left
          ((mul_le_mul_of_nonneg_right (min_le_right 1 μ) (sq_nonneg ‖v‖)).trans hB) hs.1)
    _ = _ := by
      simp only [freezingCoefficientLine_eval, _root_.add_apply, _root_.smul_apply,
        one_apply_eq_self, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]

set_option maxHeartbeats 1000000 in
/-- A single polynomial inverse prefactor works for every Hilbert target with
the same annular projection jet bound. -/
theorem exists_uniform_concrete_freezingCompressionEquiv {J : ℝ} (hJ : 1 ≤ J) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {H : Type u} {Hc : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [NormedAddCommGroup Hc] [NormedSpace ℂ Hc] [CompleteSpace Hc]
        (X : EndpointComplexification H Hc)
        (P : Vec3 → H →L[ℝ] H) (_hP : ContDiffOn ℝ ∞ P Punctured)
        (_hhom : ∀ c : ℝ, 0 < c → ∀ ξ : Vec3, ξ ≠ 0 → P (c • ξ) = P ξ)
        (_hProj : ∀ ξ, (P ξ : H →ₗ[ℝ] H).IsSymmetricProjection) (_hP₀ : ‖P 0‖ ≤ 1)
        (_hjets : ∀ i : ℕ, i ≤ 5 → ∀ ξ : Vec3, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 →
          ‖iteratedFDeriv ℝ i P ξ‖ ≤ J ^ i)
        (Pstrong : HalfHolder Labels H →L[ℝ] HalfHolder Labels H) (hPstrong : ∀ v, Pstrong (Pstrong v) = Pstrong v)
        (_hFourier : ∀ (w : HalfHolder Labels H) k, complexifiedHalfHolderFourierCoeff X (Pstrong w) k =
          X.extendOperator (P (latticeVector k)) (complexifiedHalfHolderFourierCoeff X w k))
        (_hpair : ∀ w (v : freezingFixedSpace Pstrong),
          ⟪freezingHaarEmbedding (Pstrong w), freezingHaarEmbedding v.val⟫_ℝ =
            ⟪freezingHaarEmbedding w, freezingHaarEmbedding v.val⟫_ℝ)
        (B : HalfHolder Labels (H →L[ℝ] H)) {μ L : ℝ}, 0 < μ → 0 ≤ L →
      (∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ L * dist a b) →
      (∀ a ξ v, P ξ v = v → μ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a B v, v⟫_ℝ) →
      (∀ (v : freezingFixedSpace Pstrong) a, μ * ‖HalfHolder.eval a v.val‖ ^ 2 ≤
        ⟪HalfHolder.eval a B (HalfHolder.eval a v.val), HalfHolder.eval a v.val⟫_ℝ) →
      ∃ e : freezingFixedSpace Pstrong ≃L[ℝ] freezingFixedSpace Pstrong,
        (e : freezingFixedSpace Pstrong →L[ℝ] freezingFixedSpace Pstrong) =
          freezingCompression Pstrong B.coefficientMul hPstrong ∧
        ‖(e.symm : freezingFixedSpace Pstrong →L[ℝ] freezingFixedSpace Pstrong)‖ ≤
          C * (4 + μ⁻¹ + ‖B.val.1‖ + L) ^ 145 := by
  obtain ⟨C₀, K₀, hC₀, hK₀, hEstimateAll⟩ :=
    exists_uniform_freezingHalfHolderMultipliers_bounds.{u, v} hJ
  let J₀ := 1 + 2 * K₀ * (1 + 16 * C₀) ^ 2 + 4 * (1 + 16 * C₀)
  have hJ₀ : 0 ≤ J₀ := by dsimp [J₀]; positivity
  refine ⟨4 * (C₀ + 64 * J₀ ^ 4), by positivity, ?_⟩
  intro H Hc _ _ _ _ _ _ X P hP hhom hProj hP₀ hjets Pstrong hPstrong hFourier hpair
    B μ L hμ hL hBlip hB hcoercive
  have hEstimate := hEstimateAll X P hP hProj hP₀ hjets
  let ν := min 1 μ
  have hν : 0 < ν := lt_min zero_lt_one hμ
  have hνinv : ν⁻¹ ≤ 1 + μ⁻¹ := by
    rcases le_total μ 1 with h | h
    · rw [show ν = μ from min_eq_right h]
      linarith
    · rw [show ν = 1 from min_eq_left h, inv_one]
      linarith [inv_nonneg.mpr hμ.le]
  let Q := 4 + μ⁻¹ + ‖B.val.1‖ + L
  have hQ : 1 ≤ Q := by dsimp [Q]; linarith [inv_nonneg.mpr hμ.le, norm_nonneg B.val.1]
  have hLQ : L ≤ Q := by dsimp [Q]; linarith [inv_nonneg.mpr hμ.le, norm_nonneg B.val.1]
  have hBQ : 1 + ‖B.val.1‖ ≤ Q := by dsimp [Q]; linarith [inv_nonneg.mpr hμ.le]
  have hνQ : ν⁻¹ ≤ Q := by dsimp [Q]; linarith [norm_nonneg B.val.1]
  let C := C₀ * Q ^ 11
  have hC : 0 ≤ C := mul_nonneg hC₀ (pow_nonneg (zero_le_one.trans hQ) _)
  let R := 1 + 16 * C * L
  let r := (R⁻¹) ^ 2
  let D := K₀ * Q ^ 11 / r
  obtain ⟨-, hr, hr₁, hsmall⟩ := freezingRadius_bounds hC hL
  have hD : 0 ≤ D := div_nonneg (mul_nonneg hK₀ (pow_nonneg (zero_le_one.trans hQ) _)) hr.le
  let Bf (s : ℝ) (a : Labels) := HalfHolder.eval a (freezingCoefficientLine B s)
  have hLine (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (a : Labels) (ξ : Vec3) (v : H)
      (hv : P ξ v = v) : ν * ‖v‖ ^ 2 ≤ ⟪Bf s a v, v⟫_ℝ :=
    freezingCoefficientLine_range_coercive B hs a v (hB a ξ v hv)
  have hMQ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (a : Labels) :
      2 + ν⁻¹ + ‖Bf s a‖ ≤ Q := by
    have hb := ((freezingCoefficientLine B s).val.1.norm_coe_le_norm a).trans
      (freezingCoefficientLine_sup_le B hs)
    change ‖Bf s a‖ ≤ 1 + ‖B.val.1‖ at hb
    dsimp [Q]
    linarith
  have hUnit (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (a : Labels) :
      ∀ ξ ∈ Punctured, IsUnit (frozenSymbol (P ξ) (Bf s a)) :=
    fun ξ _ => frozenSymbol_isUnit (hProj ξ) hν (hLine s hs a ξ)
  let F (s : ℝ) (a : Labels) : HalfHolder Labels H →L[ℝ] HalfHolder Labels H :=
    if hs : s ∈ Icc (0 : ℝ) 1 then freezingInverseHalfHolderMultiplier X hP (hUnit s hs a) else 0
  let G (s : ℝ) (a : Labels) : HalfHolder Labels H →L[ℝ] HalfHolder Labels H :=
    if hs : s ∈ Icc (0 : ℝ) 1 then freezingProjectedInverseHalfHolderMultiplier X hP (hUnit s hs a)
      else 0
  have hQpow (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (a : Labels) :
      (2 + ν⁻¹ + ‖Bf s a‖) ^ 11 ≤ Q ^ 11 :=
    pow_le_pow_left₀ (by positivity) (hMQ s hs a) _
  have hF (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (a : Labels) : ‖F s a‖ ≤ C := by
    dsimp only [F]
    rw [dite_eq_left hs]
    exact (hEstimate (Bf s a) hν (hLine s hs a)).1.trans
      (mul_le_mul_of_nonneg_left (hQpow s hs a) hC₀)
  have hG (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (a : Labels) : ‖G s a‖ ≤ C := by
    dsimp only [G]
    rw [dite_eq_left hs]
    exact (hEstimate (Bf s a) hν (hLine s hs a)).2.1.trans
      (mul_le_mul_of_nonneg_left (hQpow s hs a) hC₀)
  have hfreeze (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (v : freezingFixedSpace Pstrong) (a : Labels)
      (w : HalfHolder Labels H) (hw : ∀ x, HalfHolder.eval x w =
        (HalfHolder.eval a (freezingCoefficientLine B s) - HalfHolder.eval x
          (freezingCoefficientLine B s)) (HalfHolder.eval x v.val)) :
      v.val = F s a (Pstrong ((freezingCoefficientLine B s).coefficientMul v.val)) + G s a w := by
    let u := (freezingCoefficientLine B s).coefficientMul v.val
    have hwEq : w = HalfHolder.map (Bf s a) v.val - u := by
      apply HalfHolder.ext
      intro x
      rw [hw x, map_sub, HalfHolder.eval_coefficientMul]
      simp only [_root_.sub_apply]
      rfl
    have hvFix := (mem_freezingFixedSpace Pstrong _).mp v.property
    dsimp only [F, G]
    rw [dite_eq_left hs, dite_eq_left hs]
    refine freezingHalfHolderMultipliers_identity X hP (hUnit s hs a) hhom hProj hν
      (hLine s hs a) v.val (Pstrong u) w u ?_ (hFourier u) ?_
    · intro k
      rw [← hFourier, hvFix]
    · intro k
      rw [hwEq, complexifiedHalfHolderFourierCoeff_sub, complexifiedHalfHolderFourierCoeff_map]
  have hoff (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (a : Labels) (w : HalfHolder Labels H)
      (hw : ∀ x, dist x a ≤ r → HalfHolder.eval x w = 0)
      (b : Labels) (hb : dist a b ≤ r / 4) :
      ‖HalfHolder.eval a (G s a w) - HalfHolder.eval b (G s a w)‖ ≤
        D * ‖w.val.1‖ * dist a b := by
    dsimp only [G]
    rw [dite_eq_left hs]
    obtain h := (hEstimate (Bf s a) hν (hLine s hs a)).2.2 w hr hw
      (by simpa only [dist_comm] using hb : dist b a ≤ r / 4)
    refine h.trans ?_
    rw [dist_comm b a]
    dsimp only [D]
    gcongr
    exact hMQ s hs a
  obtain ⟨e, he, hbound⟩ :=
    exists_freezingCompressionEquiv Pstrong hPstrong B F G hr hr₁ hC hD hL hμ
      hBlip hsmall hpair hcoercive hF hG hfreeze hoff
  let K := freezingLowerOrder r (2 * D * (1 + ‖B.val.1‖))
  have hK : 0 ≤ K := zero_le_one.trans (one_le_freezingLowerOrder _ _)
  have hKbd : K ≤ J₀ * Q ^ 36 :=
    freezingLowerOrder_polynomial hC₀ hK₀ hL (norm_nonneg B.val.1) hQ hLQ hBQ
  exact ⟨e, he, hbound.trans (freezingInverse_polynomial hC₀ hK hJ₀ (inv_nonneg.mpr hν.le) hQ hKbd hνQ)⟩

/-- The polynomial inverse bound for a fixed Hilbert target and projection. -/
theorem exists_concrete_freezingCompressionEquiv (X : EndpointComplexification H Hc)
    (P : Vec3 → H →L[ℝ] H) (hP : ContDiffOn ℝ ∞ P Punctured)
    (hhom : ∀ c : ℝ, 0 < c → ∀ ξ : Vec3, ξ ≠ 0 → P (c • ξ) = P ξ)
    (hProj : ∀ ξ, (P ξ : H →ₗ[ℝ] H).IsSymmetricProjection) (hP₀ : ‖P 0‖ ≤ 1)
    {J : ℝ} (hJ : 1 ≤ J)
    (hjets : ∀ i : ℕ, i ≤ 5 → ∀ ξ : Vec3, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 →
      ‖iteratedFDeriv ℝ i P ξ‖ ≤ J ^ i)
    (Pstrong : W →L[ℝ] W) (hPstrong : ∀ v, Pstrong (Pstrong v) = Pstrong v)
    (hFourier : ∀ (w : W) k, complexifiedHalfHolderFourierCoeff X (Pstrong w) k =
      X.extendOperator (P (latticeVector k)) (complexifiedHalfHolderFourierCoeff X w k))
    (hpair : ∀ w (v : freezingFixedSpace Pstrong),
      ⟪freezingHaarEmbedding (Pstrong w), freezingHaarEmbedding v.val⟫_ℝ =
        ⟪freezingHaarEmbedding w, freezingHaarEmbedding v.val⟫_ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : M) {μ L : ℝ}, 0 < μ → 0 ≤ L →
      (∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ L * dist a b) →
      (∀ a ξ v, P ξ v = v → μ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a B v, v⟫_ℝ) →
      (∀ (v : freezingFixedSpace Pstrong) a, μ * ‖HalfHolder.eval a v.val‖ ^ 2 ≤
        ⟪HalfHolder.eval a B (HalfHolder.eval a v.val), HalfHolder.eval a v.val⟫_ℝ) →
      ∃ e : freezingFixedSpace Pstrong ≃L[ℝ] freezingFixedSpace Pstrong,
        (e : freezingFixedSpace Pstrong →L[ℝ] freezingFixedSpace Pstrong) =
          freezingCompression Pstrong B.coefficientMul hPstrong ∧
        ‖(e.symm : freezingFixedSpace Pstrong →L[ℝ] freezingFixedSpace Pstrong)‖ ≤
          C * (4 + μ⁻¹ + ‖B.val.1‖ + L) ^ 145 := by
  obtain ⟨C, hC, hSolve⟩ := exists_uniform_concrete_freezingCompressionEquiv hJ
  exact ⟨C, hC, hSolve X P hP hhom hProj hP₀ hjets Pstrong hPstrong hFourier hpair⟩

end Torus

end TorusEuler
