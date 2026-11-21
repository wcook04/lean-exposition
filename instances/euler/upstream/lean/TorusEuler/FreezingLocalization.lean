import TorusEuler.FreezingInterpolation
import TorusEuler.HalfHolderSpace

/-! Localization and absorption of the lower-order term in Lemma A.2. -/

open Set
open scoped NNReal

namespace TorusEuler

private theorem HalfHolder.ofBound_norm_le {X H : Type*} [MetricSpace X] [NormedAddCommGroup H]
    [NormedSpace ℝ H] (v : C(X, H)) {M : ℝ} (hM : 0 ≤ M)
    (hvalue : ∀ a, ‖v a‖ ≤ M) (hquot : ∀ a b, ‖v a - v b‖ ≤ M * Real.sqrt (dist a b)) :
    ‖HalfHolder.ofBound v hvalue hquot‖ ≤ M := by
  apply (HalfHolder.norm_le_iff hM).mpr
  exact ⟨hvalue, hquot⟩

section Localization

variable {X : Type*} [MetricSpace X]

/-- A Lipschitz cutoff for freezing about a point, equal to one through radius
`r` and zero from radius `2*r`. Smoothness is not needed to localize the source
in (A.7), since only the cutoff's Lipschitz bound and support are used. -/
noncomputable def freezingCutoff (a : X) (r : ℝ) (x : X) : ℝ :=
  max 0 (min 1 (2 - dist x a / r))

theorem freezingCutoff_mem_Icc (a : X) (r : ℝ) (x : X) :
    freezingCutoff a r x ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem freezingCutoff_eq_one {a x : X} {r : ℝ} (hr : 0 < r) (hx : dist x a ≤ r) :
    freezingCutoff a r x = 1 := by
  unfold freezingCutoff
  have h := (div_le_one₀ hr).mpr hx
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem freezingCutoff_eq_zero {a x : X} {r : ℝ} (hr : 0 < r) (hx : 2 * r ≤ dist x a) :
    freezingCutoff a r x = 0 := by
  unfold freezingCutoff
  have h := (le_div_iff₀ hr).mpr hx
  have h' : 2 - dist x a / r ≤ 0 := by linarith
  rw [min_eq_right (h'.trans zero_le_one), max_eq_left h']

theorem freezingCutoff_lipschitz (a : X) {r : ℝ} (hr : 0 < r) (x y : X) :
    ‖freezingCutoff a r x - freezingCutoff a r y‖ ≤ r⁻¹ * dist x y := by
  let K : ℝ≥0 := ⟨r⁻¹, inv_nonneg.mpr hr.le⟩
  have hdist : LipschitzWith K (fun x : X => 2 - dist x a / r) := by
    refine lipschitzWith_iff_dist_le_mul.mpr fun x y => ?_
    have h := dist_dist_dist_le_left x y a
    rw [Real.dist_eq, show 2 - dist x a / r - (2 - dist y a / r) =
      (dist y a - dist x a) * r⁻¹ by simp only [div_eq_mul_inv]; ring,
      abs_mul, abs_of_nonneg (inv_nonneg.mpr hr.le)]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.dist_eq, abs_sub_comm] using h)
      (inv_nonneg.mpr hr.le)
  have hclip : LipschitzWith K (freezingCutoff a r) := by
    change LipschitzWith K (fun x => max 0 (min 1 (2 - dist x a / r)))
    simpa only [min_comm] using (hdist.min_const 1).const_max 0
  have h := hclip.dist_le_mul x y
  change dist (freezingCutoff a r x) (freezingCutoff a r y) ≤ r⁻¹ * dist x y at h
  simpa only [dist_eq_norm] using h

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Pointwise application of an operator-valued half-Hölder field has the usual
product bound in the maximum of the supremum and Hölder seminorms. -/
theorem HalfHolder.exists_applyField (B : HalfHolder X (H →L[ℝ] H)) (v : HalfHolder X H) :
    ∃ w : HalfHolder X H,
      (∀ a, HalfHolder.eval a w = HalfHolder.eval a B (HalfHolder.eval a v)) ∧
      ‖w‖ ≤ 2 * ‖B‖ * ‖v‖ := by
  let F : C(X, H) :=
    ⟨fun a => B.val.1 a (v.val.1 a), B.val.1.continuous.clm_apply v.val.1.continuous⟩
  obtain ⟨hB, hBdiff⟩ := (HalfHolder.norm_le_iff (norm_nonneg B)).mp (le_refl _)
  obtain ⟨hv, hvdiff⟩ := (HalfHolder.norm_le_iff (norm_nonneg v)).mp (le_refl _)
  have hval : ∀ a, ‖F a‖ ≤ 2 * ‖B‖ * ‖v‖ := fun a => by
    change ‖B.val.1 a (v.val.1 a)‖ ≤ _
    calc
      _ ≤ ‖B.val.1 a‖ * ‖v.val.1 a‖ := (B.val.1 a).le_opNorm _
      _ ≤ ‖B‖ * ‖v‖ := mul_le_mul (hB a) (hv a) (norm_nonneg _) (norm_nonneg _)
      _ ≤ _ := by linarith only [mul_nonneg (norm_nonneg B) (norm_nonneg v)]
  have hquot : ∀ a b, ‖F a - F b‖ ≤ (2 * ‖B‖ * ‖v‖) * Real.sqrt (dist a b) := by
    intro a b
    change ‖B.val.1 a (v.val.1 a) - B.val.1 b (v.val.1 b)‖ ≤ _
    rw [show B.val.1 a (v.val.1 a) - B.val.1 b (v.val.1 b) =
        B.val.1 a (v.val.1 a - v.val.1 b) + (B.val.1 a - B.val.1 b) (v.val.1 b) by
      rw [map_sub, _root_.sub_apply]
      abel]
    calc
      _ ≤ ‖B.val.1 a (v.val.1 a - v.val.1 b)‖ + ‖(B.val.1 a - B.val.1 b) (v.val.1 b)‖ :=
        norm_add_le _ _
      _ ≤ ‖B.val.1 a‖ * ‖v.val.1 a - v.val.1 b‖ + ‖B.val.1 a - B.val.1 b‖ * ‖v.val.1 b‖ :=
        add_le_add ((B.val.1 a).le_opNorm _) ((B.val.1 a - B.val.1 b).le_opNorm _)
      _ ≤ ‖B‖ * (‖v‖ * Real.sqrt (dist a b)) + (‖B‖ * Real.sqrt (dist a b)) * ‖v‖ :=
        add_le_add (mul_le_mul (hB a) (hvdiff a b) (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul (hBdiff a b) (hv b) (norm_nonneg _) (by positivity))
      _ = _ := by ring
  refine ⟨HalfHolder.ofBound F hval hquot, ?_, HalfHolder.ofBound_norm_le F (by positivity) hval hquot⟩
  intro a
  rfl

/-- The near source in (A.7) has a small half-Hölder norm before application of
the frozen multiplier. -/
theorem exists_freezing_near_source (a : X) (B : C(X, H →L[ℝ] H)) (v : HalfHolder X H)
    {r L : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hL : 0 ≤ L)
    (hBlip : ∀ x y, ‖B x - B y‖ ≤ L * dist x y) :
    ∃ w : HalfHolder X H,
      (∀ x, HalfHolder.eval x w = freezingCutoff a r x • ((B a - B x) (HalfHolder.eval x v))) ∧
      ‖w‖ ≤ 8 * L * Real.sqrt r * ‖v‖ := by
  have hc := localizedCoefficient_holderHalf a (freezingCutoff a r) B hr zero_le_one hL
    (freezingCutoff_mem_Icc a r) (fun _ hx => freezingCutoff_eq_zero hr hx.le)
    (fun x y => by simpa only [one_div] using freezingCutoff_lipschitz a hr x y) hBlip
  let F : C(X, H →L[ℝ] H) :=
    ⟨fun x => freezingCutoff a r x • (B a - B x), by
      have hχ : Continuous (freezingCutoff a r) := by unfold freezingCutoff; fun_prop
      exact hχ.smul (continuous_const.sub B.continuous)⟩
  have hval : ∀ x, ‖F x‖ ≤ 4 * L * Real.sqrt r := by
    intro x
    have hr' : r ≤ Real.sqrt r := by
      apply (Real.le_sqrt hr.le hr.le).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hr₁ hr.le]
    refine (hc.1 x).trans ?_
    nlinarith only [mul_le_mul_of_nonneg_right hr' hL,
      mul_nonneg hL (Real.sqrt_nonneg r)]
  have hquot : ∀ x y, ‖F x - F y‖ ≤ (4 * L * Real.sqrt r) * Real.sqrt (dist x y) := by
    intro x y
    change ‖freezingCutoff a r x • (B a - B x) - freezingCutoff a r y • (B a - B y)‖ ≤ _
    simpa only [show max (4 : ℝ) (1 + 2 * 1) = 4 by norm_num] using hc.2.2 x y
  let D := HalfHolder.ofBound F hval hquot
  obtain ⟨w, hw, hnorm⟩ := HalfHolder.exists_applyField D v
  refine ⟨w, fun x => ?_, hnorm.trans ?_⟩
  · rw [hw, HalfHolder.eval_ofBound]
    rfl
  · have hd := HalfHolder.ofBound_norm_le F (by positivity) hval hquot
    nlinarith only [mul_le_mul_of_nonneg_right hd (norm_nonneg v)]

/-- The cutoff decomposition in (A.7) gives a small near source and a far
source that vanishes through radius `r`. Its supremum norm is bounded by the
supremum norms of the coefficient and the unknown. -/
theorem exists_freezing_split_sources (a : X) (B : HalfHolder X (H →L[ℝ] H))
    (v : HalfHolder X H) {r L : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hL : 0 ≤ L)
    (hBlip : ∀ x y, ‖HalfHolder.eval x B - HalfHolder.eval y B‖ ≤ L * dist x y) :
    ∃ near far : HalfHolder X H,
      (∀ x, HalfHolder.eval x (near + far) =
        (HalfHolder.eval a B - HalfHolder.eval x B) (HalfHolder.eval x v)) ∧
      ‖near‖ ≤ 8 * L * Real.sqrt r * ‖v‖ ∧
      (∀ x, dist x a ≤ r → HalfHolder.eval x far = 0) ∧
      ‖far.val.1‖ ≤ 2 * ‖B.val.1‖ * ‖v.val.1‖ := by
  let C₀ : C(X, H →L[ℝ] H) := ContinuousMap.const X (HalfHolder.eval a B)
  let B₀ := HalfHolder.ofBound C₀
    (fun _ => le_refl ‖HalfHolder.eval a B‖)
    (fun _ _ => by change ‖HalfHolder.eval a B - HalfHolder.eval a B‖ ≤ _; simp; positivity)
  obtain ⟨source, hsource, _⟩ := HalfHolder.exists_applyField (B₀ - B) v
  obtain ⟨near, hnear, hNearBound⟩ :=
    exists_freezing_near_source a B.val.1.toContinuousMap v hr hr₁ hL hBlip
  let far := source - near
  have hEval (x : X) : HalfHolder.eval x source =
      (HalfHolder.eval a B - HalfHolder.eval x B) (HalfHolder.eval x v) := by
    rw [hsource, map_sub]
    rfl
  have hfull (x : X) : HalfHolder.eval x (near + far) =
      (HalfHolder.eval a B - HalfHolder.eval x B) (HalfHolder.eval x v) := by
    rw [show near + far = source by dsimp only [far]; abel, hEval]
  have hFar (x : X) : HalfHolder.eval x far =
      (1 - freezingCutoff a r x) • ((HalfHolder.eval a B - HalfHolder.eval x B) (HalfHolder.eval x v)) := by
    rw [show far = source - near from rfl, map_sub, hEval, hnear, sub_smul, one_smul]
    rfl
  refine ⟨near, far, hfull, hNearBound, fun x hx => ?_, ?_⟩
  · rw [hFar, freezingCutoff_eq_one hr hx, sub_self, zero_smul]
  · apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    change ‖HalfHolder.eval x far‖ ≤ _
    have hχ (x : X) : ‖1 - freezingCutoff a r x‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (sub_nonneg.mpr (freezingCutoff_mem_Icc a r x).2)]
      linarith [(freezingCutoff_mem_Icc a r x).1]
    have hcoeff : ‖HalfHolder.eval a B - HalfHolder.eval x B‖ ≤ 2 * ‖B.val.1‖ := by
      calc
        _ ≤ ‖HalfHolder.eval a B‖ + ‖HalfHolder.eval x B‖ := norm_sub_le _ _
        _ ≤ _ := by
          change ‖B.val.1 a‖ + ‖B.val.1 x‖ ≤ _
          linarith only [B.val.1.norm_coe_le_norm a, B.val.1.norm_coe_le_norm x]
    rw [hFar, norm_smul]
    calc
      _ ≤ 1 * (‖HalfHolder.eval a B - HalfHolder.eval x B‖ * ‖HalfHolder.eval x v‖) :=
        mul_le_mul (hχ x) ((HalfHolder.eval a B - HalfHolder.eval x B).le_opNorm _)
          (norm_nonneg _) zero_le_one
      _ ≤ _ := by
        rw [one_mul]
        exact mul_le_mul hcoeff (v.val.1.norm_coe_le_norm x) (norm_nonneg _) (by positivity)

/-- A single coefficient for the supremum, local far-source, and distant-pair
terms in the freezing estimate. The constant `D` bounds the derivative of the
far-source contribution per unit supremum norm of the unknown field. -/
noncomputable def freezingLowerOrder (r D : ℝ) : ℝ :=
  max 1 (max (D * Real.sqrt (r / 4)) (2 / Real.sqrt (r / 4)))

theorem one_le_freezingLowerOrder (r D : ℝ) : 1 ≤ freezingLowerOrder r D :=
  le_max_left _ _

/-- Centering the splitting at one point of each nearby pair, then absorbing
the small near-source term, gives a global half-Hölder estimate. The hypothesis
on the far contribution is the off-support multiplier estimate, prior to
dividing by the square root of the pair's distance. -/
theorem halfHolder_norm_le_of_freezing_split (f v : HalfHolder X H)
    {r C D θ : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hD : 0 ≤ D) (hθ : 0 ≤ θ)
    (hθhalf : θ ≤ 1 / 2)
    (hlocal : ∀ a, ∃ g near far : HalfHolder X H, v = g + near + far ∧
      ‖g‖ ≤ C * ‖f‖ ∧ ‖near‖ ≤ θ * ‖v‖ ∧
      ∀ b, dist a b ≤ r / 4 →
        ‖HalfHolder.eval a far - HalfHolder.eval b far‖ ≤ D * ‖v.val.1‖ * dist a b) :
    ‖v‖ ≤ 2 * (C * ‖f‖ + freezingLowerOrder r D * ‖v.val.1‖) := by
  let K := freezingLowerOrder r D
  have hK : 1 ≤ K := one_le_freezingLowerOrder r D
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hKd : D * Real.sqrt (r / 4) ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKr : 2 / Real.sqrt (r / 4) ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hr₀ : 0 < Real.sqrt (r / 4) := Real.sqrt_pos.2 (by linarith)
  let A := C * ‖f‖ + θ * ‖v‖ + K * ‖v.val.1‖
  have hbase : ‖v.val.1‖ ≤ A := by
    have h := mul_le_mul_of_nonneg_right hK (norm_nonneg v.val.1)
    dsimp only [A]
    linarith only [h, mul_nonneg hC (norm_nonneg f), mul_nonneg hθ (norm_nonneg v)]
  have hbound : ‖v‖ ≤ A := by
    apply (HalfHolder.norm_le_iff (by dsimp only [A]; positivity)).mpr
    refine ⟨fun a => (v.val.1.norm_coe_le_norm a).trans hbase, ?_⟩
    intro a b
    by_cases hab : dist a b ≤ r / 4
    · obtain ⟨g, near, far, hsplit, hg, hn, hfar⟩ := hlocal a
      have hgi := ((HalfHolder.norm_le_iff (mul_nonneg hC (norm_nonneg f))).mp hg).2 a b
      have hni := ((HalfHolder.norm_le_iff (mul_nonneg hθ (norm_nonneg v))).mp hn).2 a b
      have hfari : ‖HalfHolder.eval a far - HalfHolder.eval b far‖ ≤
          K * ‖v.val.1‖ * Real.sqrt (dist a b) := by
        have hsq : dist a b ≤ Real.sqrt (r / 4) * Real.sqrt (dist a b) := by
          calc
            dist a b = Real.sqrt (dist a b) * Real.sqrt (dist a b) :=
              (Real.mul_self_sqrt dist_nonneg).symm
            _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hab) (Real.sqrt_nonneg _)
        calc
          _ ≤ D * ‖v.val.1‖ * dist a b := hfar b hab
          _ ≤ D * ‖v.val.1‖ * (Real.sqrt (r / 4) * Real.sqrt (dist a b)) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = (D * Real.sqrt (r / 4)) * (‖v.val.1‖ * Real.sqrt (dist a b)) := by ring
          _ ≤ _ := (mul_le_mul_of_nonneg_right hKd (by positivity)).trans_eq (by ring)
      change ‖HalfHolder.eval a v - HalfHolder.eval b v‖ ≤ _
      rw [show HalfHolder.eval a v - HalfHolder.eval b v =
        (HalfHolder.eval a g - HalfHolder.eval b g) +
        (HalfHolder.eval a near - HalfHolder.eval b near) +
        (HalfHolder.eval a far - HalfHolder.eval b far) by rw [hsplit]; simp only [map_add]; abel]
      calc
        _ ≤ ‖HalfHolder.eval a g - HalfHolder.eval b g‖ +
            ‖HalfHolder.eval a near - HalfHolder.eval b near‖ +
            ‖HalfHolder.eval a far - HalfHolder.eval b far‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ _ := (add_le_add (add_le_add hgi hni) hfari).trans_eq (by dsimp only [A]; ring)
    · have hsqrt : Real.sqrt (r / 4) ≤ Real.sqrt (dist a b) :=
        Real.sqrt_le_sqrt (le_of_lt (lt_of_not_ge hab))
      have hprod : 2 ≤ K * Real.sqrt (dist a b) := by
        calc
          2 ≤ K * Real.sqrt (r / 4) := (div_le_iff₀ hr₀).mp hKr
          _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt hK₀
      calc
        _ ≤ ‖v.val.1 a‖ + ‖v.val.1 b‖ := norm_sub_le _ _
        _ ≤ 2 * ‖v.val.1‖ := by
          nlinarith only [v.val.1.norm_coe_le_norm a, v.val.1.norm_coe_le_norm b]
        _ ≤ (K * Real.sqrt (dist a b)) * ‖v.val.1‖ :=
          mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
        _ = (K * ‖v.val.1‖) * Real.sqrt (dist a b) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by
          dsimp only [A]
          linarith only [mul_nonneg hC (norm_nonneg f), mul_nonneg hθ (norm_nonneg v)])
          (Real.sqrt_nonneg _)
  dsimp only [A] at hbound
  linarith only [hbound, mul_le_mul_of_nonneg_right hθhalf (norm_nonneg v)]

/-- The local frozen identity and the off-support increment estimate imply
the global freezing bound. The term involving `D` uses the supremum norm
of the far source and the support created by the cutoff. -/
theorem halfHolder_norm_le_of_frozen_operator
    (B : HalfHolder X (H →L[ℝ] H)) (f v : HalfHolder X H)
    (F G : X → HalfHolder X H →L[ℝ] HalfHolder X H) {r C D L : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hBlip : ∀ x y, ‖HalfHolder.eval x B - HalfHolder.eval y B‖ ≤ L * dist x y)
    (hF : ∀ a, ‖F a‖ ≤ C) (hG : ∀ a, ‖G a‖ ≤ C)
    (hsmall : 8 * C * L * Real.sqrt r ≤ 1 / 2)
    (hfreeze : ∀ a s, (∀ x, HalfHolder.eval x s =
      (HalfHolder.eval a B - HalfHolder.eval x B) (HalfHolder.eval x v)) →
      v = F a f + G a s)
    (hoff : ∀ a s, (∀ x, dist x a ≤ r → HalfHolder.eval x s = 0) →
      ∀ b, dist a b ≤ r / 4 → ‖HalfHolder.eval a (G a s) - HalfHolder.eval b (G a s)‖ ≤
        D * ‖s.val.1‖ * dist a b) :
    ‖v‖ ≤ 2 * (C * ‖f‖ + freezingLowerOrder r (2 * D * ‖B.val.1‖) * ‖v.val.1‖) := by
  refine halfHolder_norm_le_of_freezing_split f v hr hC (by positivity) (by positivity) hsmall ?_
  intro a
  obtain ⟨near, far, hsplit, hnear, hsupp, hfar⟩ :=
    exists_freezing_split_sources a B v hr hr₁ hL hBlip
  refine ⟨F a f, G a near, G a far, ?_, (F a).le_of_opNorm_le (hF a) f, ?_, ?_⟩
  · rw [add_assoc, ← map_add, hfreeze a (near + far) hsplit]
  · calc
      _ ≤ C * ‖near‖ := (G a).le_of_opNorm_le (hG a) near
      _ ≤ C * (8 * L * Real.sqrt r * ‖v‖) := mul_le_mul_of_nonneg_left hnear hC
      _ = _ := by ring
  · intro b hb
    exact (hoff a far hsupp b hb).trans <|
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfar hD) dist_nonneg).trans_eq
        (by ring)

end Localization

local notation "Labels" => UnitAddTorus (Fin 3)

open MeasureTheory

/-- The torus interpolation step absorbs the supremum norm from the global
freezing estimate. The (L^2) hypothesis is the inequality obtained by
testing the projected equation against the unknown. -/
theorem freezing_torus_absorb_supremum {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f v : HalfHolder Labels H) {C K μ : ℝ}
    (hK : 1 ≤ K)
    (hprior : ‖v‖ ≤ 2 * (C * ‖f‖ + K * ‖v.val.1‖))
    (hcoercive : Real.sqrt (∫ x, ‖HalfHolder.eval x v‖ ^ 2 ∂unitTorusMeasure) ≤ μ⁻¹ * ‖f‖) :
    ‖v‖ ≤ 4 * (C + K * (4 * K) ^ 3 * μ⁻¹) * ‖f‖ := by
  let ε : ℝ := (4 * K)⁻¹
  let V : C(Labels, H) := v.val.1.toContinuousMap
  have hK₀ : 0 < K := zero_lt_one.trans_le hK
  have hε : 0 < ε := inv_pos.2 (by positivity)
  have hε₁ : ε ≤ 1 := (inv_le_one₀ (by positivity)).mpr (by linarith)
  have hv := (HalfHolder.norm_le_iff (norm_nonneg v)).mp (le_refl _)
  have hV : ‖v.val.1‖ ≤ ‖V‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg V)).mpr
    exact fun a => ContinuousMap.norm_coe_le_norm V a
  have hinterp := unitTorus_sup_le_holderHalf_add_l2 V hε hε₁ (norm_nonneg v) hv.2
  have hsup : ‖v.val.1‖ ≤ ε * ‖v‖ + (4 * K) ^ 3 * (μ⁻¹ * ‖f‖) := by
    apply (hV.trans hinterp).trans
    dsimp only [ε]
    simp only [inv_inv]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hcoercive (by positivity))
  have hmul : 2 * K * ε = 1 / 2 := by
    dsimp only [ε]
    field_simp
    norm_num
  have h := hprior.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsup hK₀.le)) (by norm_num))
  nlinarith only [h, congrArg (fun c : ℝ => c * ‖v‖) hmul]

end TorusEuler
