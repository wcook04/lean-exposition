import TorusEuler.CoframeDerivativeBounds
import TorusEuler.HierarchyLinearRelayBounds
import TorusEuler.HierarchySourceBounds
import TorusEuler.MeanDerivativeLifting

/-! The finite coefficient bounds and derivative calculus of Appendix D. -/

open Set
open scoped ContDiff

namespace TorusEuler

section CoefficientPowers

variable {I A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The derivative powers (D.6), using ambient derivative norms on a fixed
three-dimensional label space. The constants are uniform in the time index. -/
def FiniteCoefficientPower (D : ℝ) (a : ℕ) (c : I → Vec3 → A) : Prop :=
  (∀ t, ContDiff ℝ ∞ (c t)) ∧ ∃ C : ℕ → ℝ, (∀ m, 1 ≤ C m) ∧
    ∀ m t x, ‖iteratedFDeriv ℝ m (c t) x‖ ≤ C m * D ^ (a * (m + 1))

private theorem max_initialCoefficientCosts_ge {C : ℕ → ℝ} (hC : ∀ m, 1 ≤ C m) (n : ℕ) :
    1 ≤ 1 + ∑ i ∈ Finset.range (n + 1), C i :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => zero_le_one.trans (hC i))

private theorem coefficientCost_le_max_initial {C : ℕ → ℝ} (hC : ∀ m, 1 ≤ C m)
    {n i : ℕ} (hi : i ≤ n) : C i ≤ 1 + ∑ j ∈ Finset.range (n + 1), C j :=
  (Finset.single_le_sum (fun j _ => zero_le_one.trans (hC j))
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))).trans (by linarith only)

omit [CompleteSpace A] in
theorem FiniteCoefficientPower.mono {D : ℝ} {a b : ℕ} {c : I → Vec3 → A}
    (h : FiniteCoefficientPower D a c) (hD : 1 ≤ D) (hab : a ≤ b) :
    FiniteCoefficientPower D b c := by
  obtain ⟨hs, C, hC, h⟩ := h
  exact ⟨hs, C, hC, fun m t x => (h m t x).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (Nat.mul_le_mul_right _ hab))
      (zero_le_one.trans (hC m)))⟩

omit [CompleteSpace A] in
/-- Lemma D.2(a). Products preserve one absolute linear slope in the number of label derivatives. -/
theorem paperLemmaD2_mul {D : ℝ} {a : ℕ} (hD : 1 ≤ D) {c d : I → Vec3 → A}
    (hc : FiniteCoefficientPower D a c) (hd : FiniteCoefficientPower D a d) :
    FiniteCoefficientPower D (2 * a) (fun t x => c t x * d t x) := by
  obtain ⟨hc', C, hC, hc⟩ := hc
  obtain ⟨hd', J, hJ, hd⟩ := hd
  let B (n : ℕ) := 1 + ∑ i ∈ Finset.range (n + 1), C i
  let L (n : ℕ) := 1 + ∑ i ∈ Finset.range (n + 1), J i
  have hB (n : ℕ) : 1 ≤ B n := max_initialCoefficientCosts_ge hC n
  have hL (n : ℕ) : 1 ≤ L n := max_initialCoefficientCosts_ge hJ n
  refine ⟨fun t => (hc' t).mul (hd' t), fun n => 2 ^ n * (B n * L n), ?_, ?_⟩
  · intro n
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two)
      (one_le_mul_of_one_le_of_one_le (hB n) (hL n))
  · intro n t x
    have h := norm_iteratedFDeriv_bilinear_scaled_le
      (ContinuousLinearMap.mul ℝ A) (ContinuousLinearMap.opNorm_mul_le ℝ A)
      (n := n) (p := a) (q := a) (r := a) ((hc' t).of_le (by simp)) ((hd' t).of_le (by simp)) x
      (C₁ := B n) (C₂ := L n)
      (fun i hi => (hc i t x).trans (by
        rw [Nat.mul_succ]
        exact mul_le_mul_of_nonneg_right (coefficientCost_le_max_initial hC hi) (by positivity)))
      (fun i hi => (hd i t x).trans (by
        rw [Nat.mul_succ]
        exact mul_le_mul_of_nonneg_right (coefficientCost_le_max_initial hJ hi) (by positivity)))
    have he : a * n + a + a ≤ (2 * a) * (n + 1) := by
      rw [Nat.mul_succ, Nat.mul_assoc, two_mul, two_mul]
      omega
    refine h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD he) ?_)
    exact zero_le_one.trans
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two)
        (one_le_mul_of_one_le_of_one_le (hB n) (hL n)))

/-- Lemma D.2(b). An inverse with a fixed zeroth-order power has powers
at all orders with the absolute exponent (3a). -/
theorem paperLemmaD2_inverse {D : ℝ} {a : ℕ} (hD : 1 ≤ D) {c : I → Vec3 → A}
    (hc : FiniteCoefficientPower D a c) (hUnit : ∀ t x, IsUnit (c t x))
    (hInv : ∀ t x, ‖Ring.inverse (c t x)‖ ≤ D ^ a) :
    FiniteCoefficientPower D (3 * a) (fun t x => Ring.inverse (c t x)) := by
  obtain ⟨hs, C, hC, hc⟩ := hc
  let B (n : ℕ) := 1 + ∑ i ∈ Finset.range (n + 1), C i
  have hB (n : ℕ) : 1 ≤ B n := max_initialCoefficientCosts_ge hC n
  have hOne : 1 ≤ D ^ a := one_le_pow₀ hD
  refine ⟨?_, fun n => (n.factorial : ℝ) ^ 2 * max 1 ‖(1 : A)‖ * (B n) ^ n, ?_, ?_⟩
  · intro t
    apply contDiff_iff_contDiffAt.mpr
    intro x
    obtain ⟨u, hu⟩ := hUnit t x
    exact ((hu ▸ contDiffAt_ringInverse ℝ u).comp x (hs t).contDiffAt)
  · intro n
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (by exact_mod_cast Nat.factorial_pos n)) (le_max_left _ _))
      (one_le_pow₀ (hB n))
  · intro n t x
    have hJet (i : ℕ) (hi₁ : 1 ≤ i) (hi₂ : i ≤ n) :
        ‖iteratedFDeriv ℝ i (c t) x‖ ≤ (B n * D ^ (2 * a)) ^ i := by
      refine (hc i t x).trans ?_
      rw [mul_pow, ← pow_mul]
      have hCpow : C i ≤ (B n) ^ i := by
        refine (coefficientCost_le_max_initial hC hi₂).trans ?_
        exact le_self_pow₀ (hB n) (by omega)
      have hPow : a * (i + 1) ≤ (2 * a) * i := by
        calc
          _ ≤ a * (2 * i) := Nat.mul_le_mul_left _ (by omega)
          _ = _ := by ac_rfl
      exact mul_le_mul hCpow (pow_le_pow_right₀ hD hPow) (by positivity)
        (zero_le_one.trans (one_le_pow₀ (hB n)))
    have h := norm_iteratedFDeriv_ringInverse_comp_le (s := (univ : Set Vec3)) isOpen_univ
      (mem_univ x) ((hs t).of_le (by simp : (n : ℕ∞ω) ≤ ∞)).contDiffOn
      (fun y _ => hUnit t y) hOne (hInv t x) hJet
    have hPow : a * (n + 1) + (2 * a) * n ≤ (3 * a) * (n + 1) := by
      rw [Nat.mul_succ, Nat.mul_assoc, Nat.mul_succ, two_mul, show 3 * a = a + a + a by omega]
      rw [add_mul, add_mul]
      omega
    simp only [Function.comp_def, mul_pow, ← pow_mul] at h
    refine h.trans ?_
    calc
      _ = ((n.factorial : ℝ) ^ 2 * max 1 ‖(1 : A)‖ * (B n) ^ n) *
            D ^ (a * (n + 1) + (2 * a) * n) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hPow)
        (mul_nonneg (mul_nonneg (sq_nonneg _) (zero_le_one.trans (le_max_left _ _)))
          (pow_nonneg (zero_le_one.trans (hB n)) _))

omit [CompleteSpace A] in
/-- Lemma D.2(c), including the extra positive-order radius gain. -/
theorem paperLemmaD2_weighted {D ℓ : ℝ} {a : ℕ} (hD : 1 ≤ D)
    (hℓ : 0 ≤ ℓ) (hscale : ℓ * D ^ a ≤ 1) {c : I → Vec3 → A}
    (hc : FiniteCoefficientPower D a c) :
    ∃ C : ℕ → ℝ,
      (∀ m t x, ℓ ^ m * ‖iteratedFDeriv ℝ m (c t) x‖ ≤ C m * D ^ a) ∧
      (∀ m ≥ 1, ∀ t x, ℓ ^ m * ‖iteratedFDeriv ℝ m (c t) x‖ ≤ C m * D ^ (2 * a) * ℓ) ∧
      ∀ n, hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) n c ≤
        (∑ w ∈ hierarchyAdmissibleWords (Fin 3) n, C w.length) * D ^ a := by
  obtain ⟨hs, C, hC, hc⟩ := hc
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hmain (m : ℕ) (t : I) (x : Vec3) :
      ℓ ^ m * ‖iteratedFDeriv ℝ m (c t) x‖ ≤ C m * D ^ a := by
    calc
      _ ≤ ℓ ^ m * (C m * D ^ (a * (m + 1))) :=
        mul_le_mul_of_nonneg_left (hc m t x) (pow_nonneg hℓ _)
      _ = (ℓ * D ^ a) ^ m * (C m * D ^ a) := by
        rw [mul_pow, ← pow_mul, Nat.mul_succ, pow_add]
        ring
      _ ≤ _ := mul_le_of_le_one_left (mul_nonneg (zero_le_one.trans (hC m)) (pow_nonneg hD₀ _))
        (pow_le_one₀ (mul_nonneg hℓ (pow_nonneg hD₀ _)) hscale)
  refine ⟨C, hmain, fun m hm t x => hierarchy_weighted_coefficient_le hD hℓ
    (zero_le_one.trans (hC m)) hscale hm (hc m t x), ?_⟩
  intro n
  unfold hierarchyFiniteWordNorm
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro w _
  apply csSup_le (s := hierarchyJetValues False (hierarchyLabelDirection ℓ) w c) ⟨0, Or.inl rfl⟩
  rintro r (rfl | ⟨t, x, rfl⟩ | ⟨h, _⟩)
  · exact mul_nonneg (zero_le_one.trans (hC _)) (pow_nonneg hD₀ _)
  · rw [show hierarchyLabelDirection ℓ = fun i _ => ℓ • coordinateDirection i from rfl,
      phaseOperatorWord_constant_eq_iteratedFDeriv _ (hs t)]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have hsphere (i : Fin w.length) : ‖ℓ • coordinateDirection (w.get i)‖ = ℓ := by
      simp [coordinateDirection, norm_smul, Real.norm_of_nonneg hℓ]
    simp_rw [hsphere]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]
    exact hmain _ t x
  · exact h.elim

end CoefficientPowers

end TorusEuler
