import TorusEuler.TerminalCoefficientTimeBase
import TorusEuler.TerminalTimeGraphCalculus
import Mathlib.Data.Nat.Choose.Sum

/-! Bilinear operations and material differentiation preserve the mixed
spatial power slope. -/

open Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The cost of distributing time and spatial orders over a bilinear product. -/
def terminalMixedProductCost (q : ℕ) (B : E →L[ℝ] F →L[ℝ] G)
    (C C' : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 ^ q * ‖B‖ * ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * C j * C' (n - j)

theorem terminalMixedProductCost_nonneg (q : ℕ) (B : E →L[ℝ] F →L[ℝ] G)
    {C C' : ℕ → ℝ} (hC : ∀ n, 0 ≤ C n) (hC' : ∀ n, 0 ≤ C' n) (n : ℕ) :
    0 ≤ terminalMixedProductCost q B C C' n :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC j)) (hC' (n - j)))

namespace TerminalMixedJetBound

variable {a b D A A' : ℝ} {p q : ℕ} {C C' : ℕ → ℝ} {f : ℝ → Vec3 → E} {g : ℝ → Vec3 → F}

local notation "I" => Icc a b
local notation "J" => Set.prod (Icc a b) (univ : Set Vec3)

set_option maxHeartbeats 500000 in
/-- Bilinear multiplication distributes fixed time and spatial orders over the
two factors, adding the two order-independent amplitudes. -/
theorem bilinear (B : E →L[ℝ] F →L[ℝ] G) (hab : a < b)
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hC : ∀ n, 0 ≤ C n) (hC' : ∀ n, 0 ≤ C' n)
    (hf : TerminalMixedJetBound a b q p D A C f)
    (hg : TerminalMixedJetBound a b q p D A' C' g)
    (hfreg : ContDiffOn ℝ ∞ (Function.uncurry f) J)
    (hgreg : ContDiffOn ℝ ∞ (Function.uncurry g) J) :
    TerminalMixedJetBound a b q p D (A * A') (terminalMixedProductCost q B C C')
      (fun t x => B (f t x) (g t x)) := by
  intro i hi n t ht x
  let term (j : ℕ) (y : Vec3) := B (slabTimeJet a b j f t y) (slabTimeJet a b (i - j) g t y)
  let L := ‖B‖ * ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * C k * C' (n - k)
  let M := A * A' * D ^ (p * n)
  have hL : 0 ≤ L := by
    exact mul_nonneg (norm_nonneg B) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC k)) (hC' _))
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg hA hA') (pow_nonneg hD _)
  have hsum : slabTimeJet a b i (fun r y => B (f r y) (g r y)) t =
      fun y => ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) • term j y := by
    funext y
    simp only [term, Nat.cast_smul_eq_nsmul]
    exact iteratedDerivWithin_bilinear B (uniqueDiffOn_Icc hab) ht
      (terminal_contDiffOn_timeSlice hfreg y) (terminal_contDiffOn_timeSlice hgreg y) i
  have hreg (j : ℕ) : ContDiff ℝ ∞ (term j) :=
    (B.contDiff.comp (slabTimeJet_slice_smooth hab hfreg j ht)).clm_apply
      (slabTimeJet_slice_smooth hab hgreg (i-j) ht)
  have hnorm (j : ℕ) (hj : j ∈ Finset.range (i + 1)) :
      ‖iteratedFDeriv ℝ n (term j) x‖ ≤ L * M := by
    have hji : j ≤ i := by simpa using hj
    refine (B.norm_iteratedFDeriv_le_of_bilinear (slabTimeJet_slice_smooth hab hfreg j ht)
      (slabTimeJet_slice_smooth hab hgreg (i-j) ht) x (n := n) (by simp)).trans ?_
    dsimp only [L]
    rw [mul_assoc, Finset.sum_mul]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_) (norm_nonneg B)
    have hkn : k ≤ n := by simpa using hk
    have hs : p * k + p * (n - k) = p * n := by rw [← Nat.mul_add, Nat.add_sub_of_le hkn]
    calc
      _ ≤ (n.choose k : ℝ) * (C k * A * D ^ (p * k)) * (C' (n-k) * A' * D ^ (p * (n-k))) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left (hf j (hji.trans hi) k t ht x) (Nat.cast_nonneg _))
          (hg (i-j) ((Nat.sub_le _ _).trans hi) (n-k) t ht x) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (hC k) hA) (pow_nonneg hD _)))
      _ = _ := by dsimp only [M]; rw [← hs, pow_add]; ring
  rw [hsum, iteratedFDeriv_fun_sum_apply fun j _ =>
    ((hreg j).const_smul _).contDiffAt.of_le (by simp)]
  calc
    _ ≤ ∑ j ∈ Finset.range (i + 1),
        ‖iteratedFDeriv ℝ n (fun y => (i.choose j : ℝ) • term j y) x‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (L * M) := by
      refine Finset.sum_le_sum fun j hj => ?_
      rw [iteratedFDeriv_const_smul_apply' ((hreg j).contDiffAt.of_le (by simp)),
        norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hnorm j hj) (Nat.cast_nonneg _)
    _ = (2 : ℝ) ^ i * (L * M) := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose i
    _ ≤ (2 : ℝ) ^ q * (L * M) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) (mul_nonneg hL hM)
    _ = _ := by dsimp only [terminalMixedProductCost, L, M]; ring

/-- One material derivative spends one time order, and advances the
order-independent amplitude by a factor bounded by a parent polynomial. -/
theorem materialStep {A₀ : ℝ} {C₀ : ℕ → ℝ} {U : Velocity}
    (hab : a < b) (hD : 0 ≤ D) (hA : 0 ≤ A) (hA₀ : 0 ≤ A₀)
    (hC : ∀ n, 0 ≤ C n) (hC₀ : ∀ n, 0 ≤ C₀ n)
    (hf : TerminalMixedJetBound a b (q+1) p D A C f)
    (hU : TerminalMixedJetBound a b q p D A₀ C₀ U)
    (hfreg : ContDiffOn ℝ ∞ (Function.uncurry f) J)
    (hUreg : ContDiffOn ℝ ∞ (Function.uncurry U) J) :
    TerminalMixedJetBound a b q p D (A * (1 + D ^ p * A₀))
      (fun n => C n + terminalMixedProductCost q ((ContinuousLinearMap.apply ℝ E : Vec3 →L[ℝ] (Vec3 →L[ℝ] E) →L[ℝ] E).flip)
        (fun k => C (k+1)) C₀ n)
      (terminalMaterialStep a b U f) := by
  let B : (Vec3 →L[ℝ] E) →L[ℝ] Vec3 →L[ℝ] E := (ContinuousLinearMap.apply ℝ E).flip
  let Anew := A * (1 + D ^ p * A₀)
  have hDpow : 0 ≤ D ^ p := pow_nonneg hD _
  have hg := (hf.spaceDerivative hab hfreg).mono_order (Nat.le_succ q)
  have hAdv := bilinear B hab hD (mul_nonneg hA hDpow) hA₀ (fun n => hC (n+1)) hC₀
    hg hU (terminal_contDiffOn_spaceDerivative hab hfreg) hUreg
  have hA₁ : A ≤ Anew := by
    dsimp only [Anew]
    nlinarith only [mul_nonneg (mul_nonneg hA hDpow) hA₀]
  have hA₂ : A * D ^ p * A₀ ≤ Anew := by
    dsimp only [Anew]
    linarith only [hA, show A * (1 + D ^ p * A₀) = A + A * D ^ p * A₀ by ring]
  exact ((hf.timeDerivative).mono_amplitude hD hC hA₁).add
    (hAdv.mono_amplitude hD (terminalMixedProductCost_nonneg q B (fun n => hC (n+1)) hC₀) hA₂)
    hab (contDiffOn_sliceTimeDerivWithin_Icc hab hfreg)
    ((terminal_contDiffOn_spaceDerivative hab hfreg).clm_apply hUreg)

end TerminalMixedJetBound

end

end TorusEuler
