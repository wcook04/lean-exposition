import Breakdown.Frac.StSpaceReg
import Breakdown.Uniqueness.RegConcat

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow.PowerInternal

open Breakdown.Freq
open Breakdown.SmoothFlow

theorem flow_const {α : ℝ} {m : ℕ} {F₀ : Space → CSpace}
    (hm : AEStronglyMeasurable F₀ volume) (hs : IsSolenoidalSymbol F₀) (hf : hsNormSq m F₀ < ⊤) :
    IsPowerSymbolFlow α m (fun _ => F₀) F₀ 0 := by
  refine ⟨⟨fun _ _ => ⟨hm, hf⟩, fun t₀ _ => ?_⟩, ?_, fun _ _ => hs, rfl⟩
  · have h0 : hsNormSq m (F₀ - F₀) = 0 := by simp [hsNormSq]
    simp only [h0]
    exact tendsto_const_nhds
  · intro t ht ξ
    have h : t = 0 := le_antisymm ht.2 ht.1
    subst h
    simp [powerHeatSymbol]

theorem flow_regular {α : ℝ} (h3 : PowerPersistStatement α) {F : ℝ → Space → CSpace}
    {F₀ : Space → CSpace} {s : ℝ}
    (hF : IsPowerSymbolFlow α 3 F F₀ s) (h0 : ∀ m, hsNormSq m F₀ < ⊤) (m : ℕ) :
    IsHsCurve m F 0 s := by
  rcases le_or_gt 3 m with hm | hm
  · exact h3 m hm F 0 s hF.1 hF.2.1 hF.2.2.1 (by rw [hF.2.2.2]; exact h0 m)
  · exact isHsCurve_mono hm.le hF.1

theorem flow_exists {α : ℝ} (h1 : PowerLocalStatement α) (h2 : PowerConcatStatement α)
    (h4 : PowerAprioriStatement α) {F₀ : Space → CSpace}
    (hm0 : AEStronglyMeasurable F₀ volume) (hs0 : IsSolenoidalSymbol F₀)
    (hf0 : hsNormSq 3 F₀ < ⊤) {T M : ℝ} (hT : 0 < T)
    (hH : ∀ s ∈ Icc 0 T, ∀ F, IsPowerSymbolFlow α 3 F F₀ s → ∀ t ∈ Icc 0 s,
      homNormSq 1 (F t) ≤ ENNReal.ofReal M) :
    ∃ F, IsPowerSymbolFlow α 3 F F₀ T := by
  obtain ⟨B, hB⟩ := h4 3 le_rfl M T (hsNormSq 3 F₀).toReal
  obtain ⟨δ, hδ, hloc⟩ := h1 3 le_rfl B
  have hstep : ∀ k : ℕ, ∃ F, IsPowerSymbolFlow α 3 F F₀ (min (k * δ) T) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun _ => F₀, ?_⟩
      have h : min ((0 : ℕ) * δ) T = 0 := by simp [hT.le]
      rw [h]
      exact flow_const hm0 hs0 hf0
    | succ k ih =>
      obtain ⟨F, hF⟩ := ih
      rcases eq_or_lt_of_le (min_le_right ((k : ℝ) * δ) T) with hsT | hsT
      · have h1' : T ≤ (k : ℝ) * δ := min_eq_right_iff.mp hsT
        have h2' : min (((k + 1 : ℕ) : ℝ) * δ) T = T := by
          apply min_eq_right
          push_cast
          nlinarith
        rw [h2']
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
        · exact h2.2 _ _ _ _ hss'
            (h2.1 F G 0 _ _ hs0 (by linarith) hF.1 hGc hF.2.1 hGd hG0)
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

end Breakdown.SmoothFlow.PowerInternal

namespace Breakdown.SmoothFlow

theorem powerFlow_of (α : ℝ) (hα : 1 < α) (h1 : PowerLocalStatement α)
    (h2 : PowerConcatStatement α) (h3 : PowerPersistStatement α) (h4 : PowerAprioriStatement α) :
    PowerFlowStatement α :=
  ⟨fun _ _ _ hF h0 m => PowerInternal.flow_regular h3 hF h0 m,
    fun _ hm0 hs0 hf0 _ _ hT hH => PowerInternal.flow_exists h1 h2 h4 hm0 hs0 hf0 hT hH⟩

end Breakdown.SmoothFlow
