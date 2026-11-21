import TorusEuler.ParentCoframeEstimates
import TorusEuler.FourierHolderTail

/-! The uniform parent coefficient and composition bounds of Proposition 5.1. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

/-- An order-`m` label jet estimate of the form in (D.5). -/
def ParentLabelJetBound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T D : ℝ) (f : ℝ → Vec3 → E) (C : ℕ → ℝ) (p c : ℕ) : Prop :=
  ∀ m t, t ∈ Icc 0 T → ∀ x, ‖iteratedFDeriv ℝ m (f t) x‖ ≤ C m * D ^ (p * m + c)

/-- Summing the radius-weighted suprema removes the order-dependent power
from a coefficient jet, leaving its zeroth-order power. -/
theorem ParentLabelJetBound.weighted_sum_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T D ℓ : ℝ} {f : ℝ → Vec3 → E} {C : ℕ → ℝ} {p c : ℕ}
    (hf : ParentLabelJetBound T D f C p c) (hC : ∀ j, 0 ≤ C j)
    (hD : 1 ≤ D) (hℓ : 0 ≤ ℓ) (hscale : ℓ * D ^ p ≤ 1) {t : ℝ} (ht : t ∈ Icc 0 T) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (f t))) ≤
      (∑ j ∈ Finset.range (n + 1), C j) * D ^ c := by
  apply sum_weighted_labelJets_le_of_power (show 0 ≤ D ^ c by positivity)
    (zero_le_one.trans hD) hℓ hscale (fun j _ => hC j)
  intro j _
  rw [mul_assoc, ← pow_add, add_comm c]
  exact ciSup_le (hf j t ht)

/-- The actual forward and inverse coframes, strain, normalized covector,
inverse covector length, and projection have a common absolute slope and
zeroth-order exponent, as in Proposition 5.1. -/
theorem paperProposition51_parentCoefficients (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T D : ℝ}, 0 < T → T ≤ 1 → 1 ≤ D →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        (∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
          ‖iteratedFDeriv ℝ j (U t) x‖ ≤ R n * D ^ j) →
        ∀ (k : Vec3) {freq t₀ : ℝ}, 0 < freq → t₀ ∈ Icc 0 T →
          ‖labelWaveVector X 0 0 k t₀‖ = freq →
          let F := fun t => fderiv ℝ (X 0 t)
          let G := fun t a => fderiv ℝ (X t 0) (X 0 t a)
          let M := fun t a => fderiv ℝ (U t) (X 0 t a)
          let κ := fun t a => labelWaveVector X 0 a k t
          ParentLabelJetBound T D F C 16 16 ∧ ParentLabelJetBound T D G C 16 16 ∧
          ParentLabelJetBound T D M C 16 16 ∧ ParentLabelJetBound T D (fun t a => freq⁻¹ • κ t a) C 16 16 ∧
          ParentLabelJetBound T D (fun t a => freq ^ 2 / ‖κ t a‖ ^ 2) C 16 16 ∧
          ParentLabelJetBound T D
            (fun t a => (‖κ t a‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ (κ t a) (κ t a)) C 16 16 := by
  obtain ⟨C, hC, hBound⟩ := exists_parent_coefficientJetBounds R hR
  refine ⟨C, hC, ?_⟩
  intro U X T D hT hT₁ hD hX hU hPer hF hG hUjet k freq t₀ hfreq ht₀ hκ
  have h (m : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) :=
    hBound hT hT₁ hD hX hU hPer hF hG hUjet k hfreq ht₀ hκ m t ht x
  have widen (m : ℕ) {p : ℕ} (hp : p ≤ 16 * m + 16) :
      C m * D ^ p ≤ C m * D ^ (16 * m + 16) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hp) (hC m)
  exact ⟨fun m t ht x => (h m t ht x).1.trans (widen m (by omega)),
    fun m t ht x => (h m t ht x).2.1.trans (widen m (by omega)),
    fun m t ht x => (h m t ht x).2.2.2.1.trans (widen m (by omega)),
    fun m t ht x => (h m t ht x).2.2.2.2.1.trans (widen m (by omega)),
    fun m t ht x => (h m t ht x).2.2.2.2.2.1.trans (widen m (by omega)),
    fun m t ht x => (h m t ht x).2.2.2.2.2.2.trans (widen m (by omega))⟩

/-- The composition estimate of Proposition 5.1 holds for every field
with Bernstein-scale spatial jets, with constants chosen before the field
and the parent. The weighted consequence uses the same order budget. -/
theorem paperProposition51_parentComposition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R C' : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) (hC' : ∀ n, 0 ≤ C' n) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T D : ℝ}, 0 < T → T ≤ 1 → 1 ≤ D →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        (∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
          ‖iteratedFDeriv ℝ j (U t) x‖ ≤ R n * D ^ j) →
        ∀ (f : ℝ → Vec3 → E) {A : ℝ}, 0 ≤ A →
          (∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (f t)) →
          ParentLabelJetBound T D f (fun j => C' j * A) 1 0 →
          ParentLabelJetBound T D (fun t => f t ∘ X 0 t) (fun j => C j * A) 6 0 := by
  obtain ⟨Cf, hCf, hFlow⟩ := exists_forward_flowJetBounds R hR
  let B (m : ℕ) := 1 + ∑ j ∈ Finset.range (m + 1), Cf j
  let K (m : ℕ) := ∑ j ∈ Finset.range (m + 1), C' j
  have hB (m : ℕ) : 1 ≤ B m :=
    le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hCf j)
  have hK (m : ℕ) : 0 ≤ K m := Finset.sum_nonneg fun j _ => hC' j
  let C (m : ℕ) := (m.factorial : ℝ) * K m * B m ^ m
  refine ⟨C, fun m => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hK m))
    (pow_nonneg (zero_le_one.trans (hB m)) _), ?_⟩
  intro U X T D hT hT₁ hD hX hU hPer hF hG hUjets f A hA hf hJets m t ht x
  have hXreg := (hX.labelJets_evolve m hT hU hPer).1 t ht
  have hCcomp := norm_iteratedFDeriv_parentComposition_le ((hf t ht).of_le (by simp)) hXreg x hD
    (hB m) (hK m) hA (fun i hi him => ?_) (fun i him => ?_)
  · simpa only [C, add_zero] using hCcomp
  · have hCi : Cf i ≤ B m :=
      (Finset.single_le_sum (fun j _ => hCf j) (Finset.mem_range.mpr (Nat.lt_succ_of_le him))).trans
        (le_add_of_nonneg_left zero_le_one)
    have hjet := hFlow hT hT₁ hD hX hU hPer hF hG
      (fun n _ j hj hjn => hUjets n j ((by decide : 1 ≤ 2).trans hj) hjn) i hi t ht x
    exact hjet.trans (mul_le_mul hCi (pow_le_pow_right₀ hD (Nat.sub_le _ _))
      (by positivity) (zero_le_one.trans (hB m)))
  · have hCi : C' i ≤ K m :=
      Finset.single_le_sum (fun j _ => hC' j) (Finset.mem_range.mpr (Nat.lt_succ_of_le him))
    refine (hJets i t ht (X 0 t x)).trans ?_
    simp only [one_mul, add_zero]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCi hA) (by positivity)

/-- Weighted composition bound (5.12), with the amplitude retained outside
the finite sum of the pure-order constants. -/
theorem paperProposition51_weightedComposition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T D ℓ A : ℝ} {f : ℝ → Vec3 → E} {C : ℕ → ℝ}
    (hD : 1 ≤ D) (hℓ : 0 ≤ ℓ) (hA : 0 ≤ A) (hscale : ℓ * D ^ (6 : ℕ) ≤ 1)
    (hC : ∀ n, 0 ≤ C n) (hf : ParentLabelJetBound T D f (fun j => C j * A) 6 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (f t))) ≤
      (∑ j ∈ Finset.range (n + 1), C j) * A := by
  apply sum_weighted_labelJets_le_of_power hA (zero_le_one.trans hD) hℓ hscale (fun j _ => hC j)
  intro j _
  apply ciSup_le
  simpa only [add_zero] using hf j t ht

end TorusEuler
