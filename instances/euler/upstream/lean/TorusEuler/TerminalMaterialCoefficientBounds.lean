import TorusEuler.TerminalCoefficientTimeProduct

/-! Parent-field material jets and their polynomial bound in label coordinates. -/

open Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The amplitude of `j` material derivatives is bounded by a degree-`j`
polynomial built from the parent velocity amplitude and the derivative scale. -/
theorem exists_terminalMaterialIterateCost (Cᵤ C₀ : ℕ → ℝ)
    (hCᵤ : ∀ n, 0 ≤ Cᵤ n) (hC₀ : ∀ n, 0 ≤ C₀ n) (j q : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ ∀ {a b D A Aᵤ : ℝ} {p : ℕ}
      {U : Velocity} {f : ℝ → Vec3 → E}, a < b →
      0 ≤ D → 0 ≤ A → 0 ≤ Aᵤ →
      ContDiffOn ℝ ∞ (Function.uncurry U) (Icc a b ×ˢ (univ : Set Vec3)) →
      ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set Vec3)) →
      TerminalMixedJetBound a b (q+j) p D Aᵤ Cᵤ U →
      TerminalMixedJetBound a b (q+j) p D A C₀ f →
      TerminalMixedJetBound a b q p D (A * (1 + D ^ p * Aᵤ) ^ j) C
        (terminalMaterialIterate a b U j f) := by
  induction j generalizing q with
  | zero =>
    refine ⟨C₀, hC₀, ?_⟩
    intro a b D A Aᵤ p U f _ _ _ _ _ _ _ hf
    simpa only [Nat.add_zero, pow_zero, mul_one, terminalMaterialIterate_zero] using hf
  | succ j ih =>
    obtain ⟨C, hC, hB⟩ := ih (q+1)
    let B : (Vec3 →L[ℝ] E) →L[ℝ] Vec3 →L[ℝ] E := (ContinuousLinearMap.apply ℝ E).flip
    let Cnew (n : ℕ) := C n + terminalMixedProductCost q B (fun k => C (k+1)) Cᵤ n
    have hCnew (n : ℕ) : 0 ≤ Cnew n :=
      add_nonneg (hC n) (terminalMixedProductCost_nonneg q B (fun k => hC (k+1)) hCᵤ n)
    refine ⟨Cnew, hCnew, ?_⟩
    intro a b D A Aᵤ p U f hab hD hA hAᵤ hUreg hfreg hU hf
    have hq : q + 1 + j = q + (j + 1) := by omega
    have hprev := hB hab hD hA hAᵤ hUreg hfreg (hq.symm ▸ hU) (hq.symm ▸ hf)
    have hPrevReg := terminal_contDiffOn_materialIterate hab hUreg hfreg j
    have hAmp : 0 ≤ A * (1 + D ^ p * Aᵤ) ^ j := by positivity
    simpa only [Cnew, B, terminalMaterialIterate_succ, pow_succ, mul_assoc] using
      hprev.materialStep hab hD hAmp hAᵤ hC hCᵤ
        (hU.mono_order (by omega : q ≤ q + (j + 1))) hPrevReg hUreg

private theorem one_le_orderCap (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n) (n : ℕ) :
    1 ≤ 1 + ∑ j ∈ Finset.range (n + 1), C j :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hC j)

private theorem le_orderCap (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n) {n j : ℕ} (hj : j ≤ n) :
    C j ≤ 1 + ∑ r ∈ Finset.range (n + 1), C r :=
  (Finset.single_le_sum (fun r _ => hC r) (Finset.mem_range.2 (Nat.lt_succ_iff.2 hj))).trans
    (le_add_of_nonneg_left zero_le_one)

set_option maxHeartbeats 1000000 in
/-- The label pullback of a smooth parent quantity inherits every controlled
time jet. The spatial derivative slope is six and does not depend on the
number of time derivatives. -/
theorem exists_terminalMaterialPullbackCost (Cᵤ C₀ Cₓ : ℕ → ℝ)
    (hCᵤ : ∀ n, 0 ≤ Cᵤ n) (hC₀ : ∀ n, 0 ≤ C₀ n) (hCₓ : ∀ n, 0 ≤ Cₓ n) (q : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ ∀ {T D A Aᵤ : ℝ}
      {U : Velocity} {X : ℝ → Velocity} {f : ℝ → Vec3 → E}, 0 < T →
      1 ≤ D → 0 ≤ A → 0 ≤ Aᵤ → IsLabelFlowOn U X (Icc 0 T) →
      ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
      ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3)) →
      (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
      TerminalMixedJetBound 0 T q 1 D Aᵤ Cᵤ U →
      TerminalMixedJetBound 0 T q 1 D A C₀ f →
      (∀ j, 1 ≤ j → ∀ t ∈ Icc 0 T, ∀ x,
        ‖iteratedFDeriv ℝ j (X 0 t) x‖ ≤ Cₓ j * D ^ (5 * j)) →
      TerminalMixedJetBound 0 T q 6 D (A * (1 + D * Aᵤ) ^ q) C
        (fun t x => f t (X 0 t x)) := by
  have hAll (i : ℕ) := exists_terminalMaterialIterateCost (E := E) Cᵤ C₀ hCᵤ hC₀ i 0
  choose L hL hBound using hAll
  let Cflow (n : ℕ) := 1 + ∑ j ∈ Finset.range (n + 1), Cₓ j
  let Cout (n : ℕ) := 1 + ∑ i ∈ Finset.range (q+1), ∑ j ∈ Finset.range (n+1), L i j
  let C (n : ℕ) := (n.factorial : ℝ) * Cout n * Cflow n ^ n
  have hFlow (n : ℕ) : 1 ≤ Cflow n := one_le_orderCap Cₓ hCₓ n
  have hOut (n : ℕ) : 1 ≤ Cout n := one_le_orderCap
    (fun i => ∑ j ∈ Finset.range (n+1), L i j) (fun i => Finset.sum_nonneg fun j _ => hL i j) q
  have hC (n : ℕ) : 0 ≤ C n := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (hOut n)))
    (pow_nonneg (zero_le_one.trans (hFlow n)) _)
  refine ⟨C, hC, ?_⟩
  intro T D A Aᵤ U X f hT hD hA hAᵤ hX hUreg hfreg hper hU hf hXjets
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hG : 1 ≤ 1 + D * Aᵤ := le_add_of_nonneg_right (mul_nonneg hD₀ hAᵤ)
  have ht₀ : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  intro i hi n t ht x
  let g := terminalMaterialIterate 0 T U i f
  have hg : ContDiffOn ℝ ∞ (Function.uncurry g) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    terminal_contDiffOn_materialIterate hT hUreg hfreg i
  have heq : slabTimeJet 0 T i (fun r y => f r (X 0 r y)) t = g t ∘ X 0 t :=
    funext (hX.terminal_iteratedDerivWithin_pullback hT hUreg hfreg ht₀ i ht)
  rw [heq]
  have hgin := hBound i hT hD₀ hA hAᵤ hUreg hfreg
    (hU.mono_order (by simpa using hi)) (hf.mono_order (by simpa using hi))
  have hg₀ : ∀ j y, ‖iteratedFDeriv ℝ j (g t) y‖ ≤ L i j * (A * (1 + D * Aᵤ)^i) * D^j := by
    intro j y
    simpa only [slabTimeJet_zero, pow_one, one_mul] using hgin 0 le_rfl j t ht y
  have hCout (j : ℕ) (hj : j ≤ n) : L i j ≤ Cout n := by
    refine (Finset.single_le_sum (fun r _ => hL i r) (Finset.mem_range.2 (Nat.lt_succ_iff.2 hj))).trans ?_
    exact le_orderCap (fun k => ∑ r ∈ Finset.range (n+1), L k r)
      (fun k => Finset.sum_nonneg fun r _ => hL k r) hi
  have hgCap (j : ℕ) (hj : j ≤ n) :
      ‖iteratedFDeriv ℝ j (g t) (X 0 t x)‖ ≤ Cout n * (A * (1 + D * Aᵤ)^q) * D^j := by
    exact (hg₀ j _).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (hCout j hj) (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hG hi) hA)
        (by positivity) (zero_le_one.trans (hOut n))) (pow_nonneg hD₀ _))
  have hXreg := terminal_contDiff_spaceSlice (hX.contDiffOn_forwardLabelFlow hT hUreg hper) ht
  exact norm_iteratedFDeriv_parentComposition_le
    ((terminal_contDiff_spaceSlice hg ht).of_le (by simp)) (hXreg.of_le (by simp)) x hD (hFlow n)
    (zero_le_one.trans (hOut n)) (by positivity)
    (fun j hj hjn => (hXjets j hj t ht x).trans
      (mul_le_mul_of_nonneg_right (le_orderCap Cₓ hCₓ hjn) (pow_nonneg hD₀ _))) hgCap

end

end TorusEuler
