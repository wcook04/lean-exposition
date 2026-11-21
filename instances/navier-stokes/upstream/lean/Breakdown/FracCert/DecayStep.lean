import Breakdown.FracCert.StDecay
import Breakdown.FracCert.WeakRegular

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

namespace DecayStep.Internal

def pairMap : Space →L[ℝ] Space →L[ℝ] (Fin 3 → Fin 3 → ℝ) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun (v w : Space) (i k : Fin 3) => v i * w k)
      (fun v₁ v₂ w => by ext i k; simp [add_mul])
      (fun c v w => by ext i k; simp [mul_assoc])
      (fun v w₁ w₂ => by ext i k; simp [mul_add])
      (fun c v w => by ext i k; simp [mul_left_comm]))
    1 (fun v w => by
      rw [one_mul]
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
      simp only [LinearMap.mk₂_apply]
      rw [norm_mul]
      exact mul_le_mul (PiLp.norm_apply_le v i) (PiLp.norm_apply_le w k) (norm_nonneg _)
        (norm_nonneg _))

theorem norm_pairMap_le : ‖pairMap‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

theorem tensorSq_eq (V : Space → Space) : tensorSq V = fun y => pairMap (V y) (V y) := by
  funext y
  rfl

theorem prod_weight {w e₁ e₂ c x₁ x₂ G₁ G₂ : ℝ} (hw : 1 ≤ w) (he : c ≤ e₁ + e₂) (hx₁ : 0 ≤ x₁)
    (hx₂ : 0 ≤ x₂) (h₁ : w ^ e₁ * x₁ ≤ G₁) (h₂ : w ^ e₂ * x₂ ≤ G₂) :
    w ^ c * (x₁ * x₂) ≤ G₁ * G₂ := by
  have hw0 : 0 < w := by linarith
  have hc : w ^ c ≤ w ^ e₁ * w ^ e₂ := by
    rw [← Real.rpow_add hw0]
    exact Real.rpow_le_rpow_of_exponent_le hw he
  have hG₁ : 0 ≤ G₁ := le_trans (by positivity) h₁
  calc w ^ c * (x₁ * x₂) ≤ w ^ e₁ * w ^ e₂ * (x₁ * x₂) := by gcongr
    _ = (w ^ e₁ * x₁) * (w ^ e₂ * x₂) := by ring
    _ ≤ G₁ * G₂ := mul_le_mul h₁ h₂ (by positivity) hG₁

theorem weight_of {w e x C : ℝ} (hw : 0 < w) (h : x ≤ C * w ^ (-e)) : w ^ e * x ≤ C := by
  have hp : 0 < w ^ e := Real.rpow_pos_of_pos hw e
  calc w ^ e * x ≤ w ^ e * (C * w ^ (-e)) := by gcongr
    _ = C := by
      rw [Real.rpow_neg hw.le]
      field_simp

theorem unweight_of {w e x K : ℝ} (hw : 0 < w) (h : w ^ e * x ≤ K) : x ≤ K * w ^ (-e) := by
  have hp : 0 < w ^ e := Real.rpow_pos_of_pos hw e
  rw [Real.rpow_neg hw.le, ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
  exact h

theorem decay_core (h2 : FarFieldBoundStatement) {α a : ℝ} (hα : 1 < α) (hα2 : α < 5 / 4)
    {V : Space → Space} (hV : ContDiff ℝ ∞ V)
    (hbd : ∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ k V y‖ ≤ C)
    (hfix : V = farFieldOp α a (tensorSq V)) (j : ℕ) (hj : 1 ≤ j) (E : ℕ → ℝ)
    (hE : ∀ i < j, ∀ y, (1 + ‖y‖) ^ (2 * α - 1 + i) * ‖iteratedFDeriv ℝ i V y‖ ≤ E i) :
    ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ j V y‖ ≤ C * (1 + ‖y‖) ^ (-(2 * α - 1 + j)) := by
  have hFsm : ContDiff ℝ j (tensorSq V) := by
    rw [tensorSq_eq]
    exact (ContDiff.clm_apply (pairMap.contDiff.comp hV) hV).of_le (by exact_mod_cast le_top)
  have hB : ∀ y, (1 + ‖y‖) ^ (2 * (2 * α - 1)) * ‖tensorSq V y‖ ≤ E 0 * E 0 := by
    intro y
    have h0 := hE 0 (by omega) y
    simp only [Nat.cast_zero, add_zero, norm_iteratedFDeriv_zero] at h0
    have hn : ‖tensorSq V y‖ ≤ ‖V y‖ * ‖V y‖ := by
      rw [tensorSq_eq]
      refine (pairMap.le_opNorm₂ (V y) (V y)).trans ?_
      nlinarith [norm_pairMap_le, norm_nonneg (V y), mul_nonneg (norm_nonneg (V y)) (norm_nonneg (V y))]
    have hw : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
    calc (1 + ‖y‖) ^ (2 * (2 * α - 1)) * ‖tensorSq V y‖
        ≤ (1 + ‖y‖) ^ (2 * (2 * α - 1)) * (‖V y‖ * ‖V y‖) := by gcongr
      _ ≤ E 0 * E 0 := prod_weight hw (by linarith) (norm_nonneg _) (norm_nonneg _) h0 h0
  have step : ∀ n : ℕ, n ≤ j + 1 → ∀ K : ℝ,
      (∀ y, (1 + ‖y‖) ^ (n : ℝ) * ‖iteratedFDeriv ℝ j V y‖ ≤ K) →
      ∃ K' : ℝ, ∀ y, (1 + ‖y‖) ^ (min ((n : ℝ) + 1) (2 * α - 1 + j)) *
        ‖iteratedFDeriv ℝ j V y‖ ≤ K' := by
    intro n hn K hK
    have hne : (n : ℝ) + 1 ≠ 2 * α - 1 + j := by
      intro h
      have h1 : (j : ℝ) < n := by linarith
      have h2 : j < n := by exact_mod_cast h1
      have h3 : (j : ℝ) + 1 ≤ n := by exact_mod_cast h2
      linarith
    have hnR : (n : ℝ) ≤ j + 1 := by exact_mod_cast hn
    obtain ⟨C, hC⟩ := h2 α hα hα2 a (2 * (2 * α - 1)) ((n : ℝ) + 1) j (by linarith) (by linarith)
      (by positivity) (by linarith) hne
    let G : ℕ → ℝ := fun i => if i < j then E i else K
    let e : ℕ → ℝ := fun i => if i < j then 2 * α - 1 + i else n
    have hG : ∀ i ≤ j, ∀ y, (1 + ‖y‖) ^ e i * ‖iteratedFDeriv ℝ i V y‖ ≤ G i := by
      intro i hi y
      by_cases h : i < j
      · simp only [e, G, if_pos h]
        exact hE i h y
      · have hij : i = j := by omega
        subst hij
        simp only [e, G, if_neg h]
        exact hK y
    have hsum : ∀ i ≤ j, (n : ℝ) + 1 ≤ e i + e (j - i) := by
      intro i hi
      simp only [e]
      by_cases h : i < j
      · by_cases h' : j - i < j
        · rw [if_pos h, if_pos h', Nat.cast_sub hi]
          linarith
        · have hi0 : i = 0 := by omega
          subst hi0
          rw [if_pos h, if_neg h']
          simp only [Nat.cast_zero]
          linarith
      · have hij : i = j := by omega
        subst hij
        rw [if_neg h, Nat.sub_self, if_pos (by omega)]
        simp only [Nat.cast_zero]
        linarith
    let A : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (G i * G (j - i))
    have hA : ∀ y, (1 + ‖y‖) ^ ((n : ℝ) + 1) * ‖iteratedFDeriv ℝ j (tensorSq V) y‖ ≤ A := by
      intro y
      have hw : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
      have hd := pairMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one hV hV y
        (n := j) (by exact_mod_cast le_top) norm_pairMap_le
      rw [← tensorSq_eq] at hd
      calc (1 + ‖y‖) ^ ((n : ℝ) + 1) * ‖iteratedFDeriv ℝ j (tensorSq V) y‖
          ≤ (1 + ‖y‖) ^ ((n : ℝ) + 1) * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i V y‖ * ‖iteratedFDeriv ℝ (j - i) V y‖ := by gcongr
        _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ((1 + ‖y‖) ^ ((n : ℝ) + 1) *
            (‖iteratedFDeriv ℝ i V y‖ * ‖iteratedFDeriv ℝ (j - i) V y‖)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        _ ≤ A := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          exact mul_le_mul_of_nonneg_left (prod_weight hw (hsum i hi') (norm_nonneg _)
            (norm_nonneg _) (hG i hi' y) (hG (j - i) (Nat.sub_le j i) y)) (by positivity)
    obtain ⟨_, hC2⟩ := hC (tensorSq V) A (E 0 * E 0) hFsm hA hB
    refine ⟨C * (A + E 0 * E 0), fun y => ?_⟩
    have hD : iteratedFDeriv ℝ j V y = iteratedFDeriv ℝ j (farFieldOp α a (tensorSq V)) y := by
      rw [← hfix]
    rw [hD]
    exact hC2 y
  have iter : ∀ n : ℕ, n ≤ j + 1 → ∃ K : ℝ,
      ∀ y, (1 + ‖y‖) ^ (n : ℝ) * ‖iteratedFDeriv ℝ j V y‖ ≤ K := by
    intro n
    induction n with
    | zero =>
      intro _
      obtain ⟨C, hC⟩ := hbd j
      exact ⟨C, fun y => by simpa using hC y⟩
    | succ m ih =>
      intro hm
      obtain ⟨K, hK⟩ := ih (by omega)
      obtain ⟨K', hK'⟩ := step m (by omega) K hK
      refine ⟨K', fun y => ?_⟩
      have hmin : min ((m : ℝ) + 1) (2 * α - 1 + j) = ((m + 1 : ℕ) : ℝ) := by
        push_cast
        have : (m : ℝ) + 1 ≤ j + 1 := by exact_mod_cast hm
        exact min_eq_left (by linarith)
      rw [← hmin]
      exact hK' y
  obtain ⟨K, hK⟩ := iter (j + 1) le_rfl
  obtain ⟨K', hK'⟩ := step (j + 1) le_rfl K hK
  have hmin : min (((j + 1 : ℕ) : ℝ) + 1) (2 * α - 1 + j) = 2 * α - 1 + j := by
    push_cast
    exact min_eq_right (by linarith)
  refine ⟨K', fun y => ?_⟩
  have hw0 : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
  have := hK' y
  rw [hmin] at this
  exact unweight_of hw0 this

end DecayStep.Internal

open DecayStep.Internal

theorem profileDecayStep_of (h1 : ProfileFixedPointStatement) (h2 : FarFieldBoundStatement)
    (h3 : SymbolL1OfMomentsStatement) (h4 : FieldSmoothOfMomentsStatement)
    (h5 : ProfileDecayBaseStatement) : ProfileDecayStepStatement := by
  intro α hα hα2 a U hU hM j hj
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · obtain ⟨C, hC⟩ := h5 α hα hα2 a U hU hM
    refine ⟨C, fun y => ?_⟩
    rw [norm_iteratedFDeriv_zero]
    simpa using hC y
  · have hwm := (h3 U hM).1
    have hsm := h4 _ (WeakRegularInternal.moments_clean U hwm) (WeakRegularInternal.cleanSymbol_conjSym _)
    rw [WeakRegularInternal.physField_clean U] at hsm
    have hE : ∀ i, ∃ C : ℝ, i < j → ∀ y, (1 + ‖y‖) ^ (2 * α - 1 + i) *
        ‖iteratedFDeriv ℝ i (profileField U) y‖ ≤ C := by
      intro i
      by_cases hi : i < j
      · obtain ⟨C, hC⟩ := hj i hi
        exact ⟨C, fun _ y => weight_of (by linarith [norm_nonneg y]) (hC y)⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose E hE using hE
    exact decay_core h2 hα hα2 hsm.1 hsm.2 (funext (h1 α hα hα2 a U hU hM)) j hjpos E
      (fun i hi => hE i hi)

end Breakdown.FracCert
