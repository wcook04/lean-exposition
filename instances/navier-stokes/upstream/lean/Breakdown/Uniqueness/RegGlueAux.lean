import Breakdown.Uniqueness.RegLocal
import Breakdown.Uniqueness.RegPersist
import Breakdown.Uniqueness.RegConcat
import Breakdown.Uniqueness.RegApriori

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

def IsSymbolFlow (m : ℕ) (F : ℝ → Space → CSpace) (F₀ : Space → CSpace) (s : ℝ) : Prop :=
  IsHsCurve m F 0 s ∧ IsVarConstSymbol F 0 s ∧ (∀ t ∈ Icc 0 s, IsSolenoidalSymbol (F t)) ∧
    F 0 = F₀

theorem homNormSq_one_le_hsNormSq (f : Space → CSpace) : homNormSq 1 f ≤ hsNormSq 1 f := by
  unfold homNormSq hsNormSq hsWeight
  refine lintegral_mono fun ξ => ?_
  gcongr
  simp only [mul_one, pow_one]
  linarith

private theorem isSymbolFlow_const {m : ℕ} {F₀ : Space → CSpace}
    (hm : AEStronglyMeasurable F₀ volume) (hs : IsSolenoidalSymbol F₀) (hf : hsNormSq m F₀ < ⊤) :
    IsSymbolFlow m (fun _ => F₀) F₀ 0 := by
  refine ⟨⟨fun _ _ => ⟨hm, hf⟩, fun t₀ _ => ?_⟩, ?_, fun _ _ => hs, rfl⟩
  · have h0 : hsNormSq m (F₀ - F₀) = 0 := by simp [hsNormSq]
    simp only [h0]
    exact tendsto_const_nhds
  · intro t ht ξ
    have h : t = 0 := le_antisymm ht.2 ht.1
    subst h
    simp [heatSymbol]

theorem isHsCurve_of_flow {F : ℝ → Space → CSpace} {F₀ : Space → CSpace} {s : ℝ}
    (hF : IsSymbolFlow 3 F F₀ s) (h0 : ∀ m, hsNormSq m F₀ < ⊤) (m : ℕ) :
    IsHsCurve m F 0 s := by
  rcases le_or_gt 3 m with hm | hm
  · exact isHsCurve_of_persist hm hF.1 hF.2.1 hF.2.2.1 (by rw [hF.2.2.2]; exact h0 m)
  · exact isHsCurve_mono hm.le hF.1

theorem exists_symbolFlow_of_homBound {F₀ : Space → CSpace}
    (hm0 : AEStronglyMeasurable F₀ volume) (hs0 : IsSolenoidalSymbol F₀)
    (hf0 : hsNormSq 3 F₀ < ⊤) {T M : ℝ} (hT : 0 < T)
    (hH : ∀ s ∈ Icc 0 T, ∀ F, IsSymbolFlow 3 F F₀ s → ∀ t ∈ Icc 0 s,
      homNormSq 1 (F t) ≤ ENNReal.ofReal M) :
    ∃ F, IsSymbolFlow 3 F F₀ T := by
  obtain ⟨B, hB⟩ := hsNormSq_apriori 3 le_rfl M T (hsNormSq 3 F₀).toReal
  obtain ⟨δ, hδ, hloc⟩ := exists_local_varConst 3 le_rfl B
  have hstep : ∀ k : ℕ, ∃ F, IsSymbolFlow 3 F F₀ (min (k * δ) T) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun _ => F₀, ?_⟩
      have h : min ((0 : ℕ) * δ) T = 0 := by simp [hT.le]
      rw [h]
      exact isSymbolFlow_const hm0 hs0 hf0
    | succ k ih =>
      obtain ⟨F, hF⟩ := ih
      rcases eq_or_lt_of_le (min_le_right ((k : ℝ) * δ) T) with hsT | hsT
      · have h1 : T ≤ (k : ℝ) * δ := min_eq_right_iff.mp hsT
        have h2 : min (((k + 1 : ℕ) : ℝ) * δ) T = T := by
          apply min_eq_right
          push_cast
          nlinarith
        rw [h2]
        rw [hsT] at hF
        exact ⟨F, hF⟩
      · have hk : (k : ℝ) * δ < T := by
          by_contra hc
          rw [min_eq_right (not_lt.mp hc)] at hsT
          exact lt_irrefl _ hsT
        rw [min_eq_left hk.le] at hF
        have hs0 : 0 ≤ (k : ℝ) * δ := by positivity
        have hsI : (k : ℝ) * δ ∈ Icc 0 T := ⟨hs0, hk.le⟩
        have hsI' : (k : ℝ) * δ ∈ Icc 0 ((k : ℝ) * δ) := ⟨hs0, le_rfl⟩
        have hbd : hsNormSq 3 (F ((k : ℝ) * δ)) ≤ ENNReal.ofReal B :=
          hB _ hsI F hF.1 hF.2.1 hF.2.2.1 (by rw [hF.2.2.2, ENNReal.ofReal_toReal hf0.ne])
            (hH _ hsI F hF) _ hsI'
        obtain ⟨G, hG0, hGc, hGd, hGs⟩ :=
          hloc _ (F ((k : ℝ) * δ)) (hF.1.1 _ hsI').1 (hF.2.2.1 _ hsI') hbd
        have hss' : min (((k + 1 : ℕ) : ℝ) * δ) T ≤ (k : ℝ) * δ + δ := by
          refine (min_le_left _ _).trans ?_
          push_cast
          linarith
        refine ⟨fun t => if t ≤ (k : ℝ) * δ then F t else G t, ?_, ?_, ?_, ?_⟩
        · exact isHsCurve_restrict le_rfl hss'
            (isHsCurve_concat hs0 (by linarith) hF.1 hGc hG0)
        · exact isVarConstSymbol_restrict hss'
            (isVarConstSymbol_concat hs0 (by linarith) hF.1 hGc hF.2.1 hGd hG0)
        · intro t ht
          by_cases h : t ≤ (k : ℝ) * δ
          · simp only [h, if_true]
            exact hF.2.2.1 t ⟨ht.1, h⟩
          · simp only [h, if_false]
            exact hGs t ⟨(not_le.mp h).le, ht.2.trans hss'⟩
        · simp only [hs0, if_true]
          exact hF.2.2.2
  obtain ⟨k, hk⟩ := exists_nat_ge (T / δ)
  obtain ⟨F, hF⟩ := hstep k
  have h : min ((k : ℝ) * δ) T = T := by
    rw [min_eq_right]
    rw [div_le_iff₀ hδ] at hk
    linarith
  rw [h] at hF
  exact ⟨F, hF⟩

end Breakdown.SmoothFlow
