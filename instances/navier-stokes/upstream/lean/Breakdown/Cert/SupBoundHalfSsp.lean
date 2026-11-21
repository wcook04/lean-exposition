import Breakdown.Cert.SupBoundTestField
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Cert

namespace Internal.SupBoundHalfSsp

open Breakdown.Freq Breakdown.Freq.Internal.Heat
  Breakdown.Freq.Internal.MildOfWeak

theorem inner_eq_integral (f g : X) :
    inner ℝ f g = ∫ ξ, inner ℝ ((f : L2C) ξ) ((g : L2C) ξ) := by
  rw [Submodule.coe_inner, L2.inner_def]

theorem inner_eq_norm_sq {χ ψ κ : X} (hl : IsSspOf χ ψ) (hh : IsHalfSspOf χ κ) :
    inner ℝ χ ψ = ‖κ‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_integral, inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hl, hh] with ξ a b
  rw [a, b, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right]
  unfold sspFactor
  ring

theorem isHalfSspOf_heat {x k : X} (h : IsHalfSspOf x k) (τ : ℝ) :
    IsHalfSspOf (heatX τ x) (heatX τ k) := by
  unfold IsHalfSspOf at h ⊢
  rw [heat_holds.2.2.2.2.2 τ x, heat_holds.2.2.2.2.2 τ k]
  filter_upwards [h, heat_ae fieldOpRealized_holds τ (x : L2C),
    heat_ae fieldOpRealized_holds τ (k : L2C)] with ξ a b c
  rw [b, c, a, smul_comm]

theorem sq_le_test {φ : Space → Space} (hφ : IsTestField φ) (y : Space) :
    ‖φ y‖ ^ 2 ≤ (1 / (2 * π)) * ‖embedX φ‖ *
      Real.sqrt (inner ℝ (embedX φ) (embedX (negSsp φ))) := by
  have hd := isDecayField_of_isTestField hφ
  have hn := isTestField_negSsp hφ
  have e1 : ‖embedX φ‖ = Real.sqrt (∫ y, ∑ i : Fin 3, ‖fderiv ℝ φ y (unitVector i)‖ ^ 2) := by
    rw [← embedNormLinear_holds.1 φ hd, Real.sqrt_sq (norm_nonneg _)]
  have e2 : inner ℝ (embedX φ) (embedX (negSsp φ)) = ∫ y, ‖sumSecondPartialsAt φ y‖ ^ 2 := by
    rw [real_inner_comm, pairingEmbed embedNormLinear_holds.1 embedNormLinear_holds.2 _ _
      (isDecayField_of_isTestField hn) hd, pairingByParts _ _ (isDecayField_of_isTestField hn) hφ]
    unfold fieldPairing negSsp
    simp_rw [inner_neg_left, inner_neg_right, neg_neg, real_inner_self_eq_norm_sq]
  rw [e1, e2]
  exact supBound_test_field φ hφ.1 hφ.2.1 y

theorem exists_test_near {x k : X} (h : IsHalfSspOf x k) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ, IsTestField φ ∧ ‖embedX φ - x‖ < ε ∧
      inner ℝ (embedX φ) (embedX (negSsp φ)) < ‖k‖ ^ 2 + ε := by
  have hc : ContinuousWithinAt (fun t => heatX t x) (Ici 0) 0 :=
    heat_holds.2.2.2.1 x 0 (mem_Ici.2 le_rfl)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 hc (ε / 2) (half_pos hε)
  have hτ : (0 : ℝ) < δ / 2 := half_pos hδ
  have hτx : ‖heatX (δ / 2) x - x‖ < ε / 2 := by
    have := hδ' (x := δ / 2) (mem_Ici.2 hτ.le) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hτ]
      linarith)
    rwa [heat_holds.1, ContinuousLinearMap.id_apply, dist_eq_norm] at this
  obtain ⟨χ, hχ⟩ : ∃ χ, χ = heatX (δ / 2) x := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = sspHeatX (δ / 2) x := ⟨_, rfl⟩
  rw [← hχ] at hτx
  have hl : IsSspOf χ ψ := by
    rw [hχ, hψ]
    exact isSspOf_heat fieldOpRealized_holds heat_holds hτ x
  have hI : inner ℝ χ ψ ≤ ‖k‖ ^ 2 := by
    rw [inner_eq_norm_sq hl (hχ ▸ isHalfSspOf_heat h (δ / 2))]
    have hk : ‖heatX (δ / 2) k‖ ≤ ‖k‖ :=
      ((heatX (δ / 2)).le_opNorm k).trans
        (mul_le_of_le_one_left (norm_nonneg _) (heat_holds.2.2.1 _ hτ.le))
    exact pow_le_pow_left₀ (norm_nonneg _) hk 2
  have hcont : ContinuousAt (fun p : X × X => inner ℝ p.1 p.2) (χ, ψ) :=
    continuous_inner.continuousAt
  obtain ⟨η, hη, hη'⟩ := Metric.continuousAt_iff.1 hcont (ε / 2) (half_pos hε)
  obtain ⟨φ, hφ, h1, h2⟩ := testDense_holds.1 χ ψ hl (min η (ε / 2)) (lt_min hη (half_pos hε))
  refine ⟨φ, hφ, ?_, ?_⟩
  · calc ‖embedX φ - x‖ ≤ ‖embedX φ - χ‖ + ‖χ - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (h1.trans_le (min_le_right _ _)) hτx
      _ = ε := add_halves ε
  · have := hη' (x := (embedX φ, embedX (negSsp φ))) (by
      rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]
      exact ⟨h1.trans_le (min_le_left _ _), h2.trans_le (min_le_left _ _)⟩)
    rw [Real.dist_eq] at this
    have := (abs_lt.1 this).2
    simp only at this
    linarith

end Internal.SupBoundHalfSsp

open Breakdown.Freq Internal.SupBoundHalfSsp in
theorem sq_le_of_halfSsp (x k : Freq.X) (h : Freq.IsHalfSspOf x k) :
    ∀ᵐ y ∂volume, ‖(Freq.velocity x : Space → Space) y‖ ^ 2 ≤ (1 / (2 * Real.pi)) * ‖x‖ * ‖k‖ := by
  choose φ hφ hx hI using fun n : ℕ =>
    exists_test_near h (Nat.one_div_pos_of_nat (α := ℝ) (n := n))
  have hr : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hxt : Tendsto (fun n => embedX (φ n)) atTop (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hx n).le) hr
  have hvt : Tendsto (fun n => velocity (embedX (φ n))) atTop (𝓝 (velocity x)) :=
    (velocity.continuous.tendsto x).comp hxt
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hvt).exists_seq_tendsto_ae
  have hall : ∀ᵐ y ∂volume, ∀ n, (velocity (embedX (φ n)) : Space → Space) y = φ n y :=
    ae_all_iff.2 fun n => velocityDecay_holds _ (isDecayField_of_isTestField (hφ n))
  filter_upwards [hae, hall] with y hy hy'
  have hlim : Tendsto (fun i => ‖φ (ns i) y‖ ^ 2) atTop
      (𝓝 (‖(velocity x : Space → Space) y‖ ^ 2)) := by
    have := ((continuous_norm.tendsto _).comp hy).pow 2
    simp only [Function.comp_def, hy'] at this
    exact this
  have hns' : Tendsto ns atTop atTop := hns.tendsto_atTop
  have hub : Tendsto (fun i => (1 / (2 * π)) * ‖embedX (φ (ns i))‖ *
      Real.sqrt (‖k‖ ^ 2 + 1 / ((ns i : ℝ) + 1))) atTop
      (𝓝 ((1 / (2 * π)) * ‖x‖ * Real.sqrt (‖k‖ ^ 2 + 0))) := by
    refine ((tendsto_const_nhds.mul ((continuous_norm.tendsto _).comp (hxt.comp hns'))).mul
      ((Real.continuous_sqrt.tendsto _).comp (tendsto_const_nhds.add (hr.comp hns'))))
  rw [add_zero, Real.sqrt_sq (norm_nonneg _)] at hub
  refine le_of_tendsto_of_tendsto' hlim hub fun i => ?_
  refine (sq_le_test (hφ (ns i)) y).trans ?_
  gcongr
  exact (hI (ns i)).le

end Breakdown.Cert
