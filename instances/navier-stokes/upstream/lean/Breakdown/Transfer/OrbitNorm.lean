import Breakdown.Transfer.StatementsFrame
import Breakdown.Transfer.StatementsLocal

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

namespace OrbitNormInternal

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

theorem norm_periodic {F : MildFramework X} {ρ : X ≃ₗᵢ[ℝ] X} {w : ℝ → X} {P : ℝ}
    (hw : F.IsOrbit ρ w P) : Function.Periodic (fun s => ‖w s‖) P := by
  intro s
  simp only [hw.periodic s, LinearIsometryEquiv.norm_map]

theorem norm_add_nat_mul {F : MildFramework X} {ρ : X ≃ₗᵢ[ℝ] X} {w : ℝ → X} {P : ℝ}
    (hw : F.IsOrbit ρ w P) (s : ℝ) (n : ℕ) : ‖w (s + n * P)‖ = ‖w s‖ :=
  (norm_periodic hw).nat_mul n s

theorem decay {F : MildFramework X} {w : ℝ → X} {s' : ℝ} {u : ℝ → X}
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, u t = F.selfSimilar w s' t) (B : ℝ)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖u t‖ ≤ B) (σ : ℝ) (hσ : 0 ≤ σ) :
    ‖w (s' + σ)‖ ≤ Real.exp (-σ) ^ (1 / 4 : ℝ) * B := by
  have he : 0 < Real.exp (-σ) := Real.exp_pos _
  have he1 : Real.exp (-σ) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have ht : 1 - Real.exp (-σ) ∈ Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have h1 : 1 - (1 - Real.exp (-σ)) = Real.exp (-σ) := by ring
  have key : F.D (Real.exp (-σ)) (u (1 - Real.exp (-σ))) = w (s' + σ) := by
    rw [hu _ ht, MildFramework.selfSimilar, h1, Real.log_exp, sub_neg_eq_add,
      ← ContinuousLinearMap.comp_apply, ← F.D_mul _ _ he (inv_pos.mpr he),
      mul_inv_cancel₀ he.ne', F.D_one, ContinuousLinearMap.id_apply]
  rw [← key, F.D_norm _ he]
  exact mul_le_mul_of_nonneg_left (hB _ (Ico_subset_Icc_self ht))
    (Real.rpow_nonneg he.le _)

theorem exp_quarter_small {P : ℝ} (hP : 0 < P) :
    ∃ n : ℕ, 2 * Real.exp (-(n * P)) ^ (1 / 4 : ℝ) < 1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (4 / P)
  refine ⟨n, ?_⟩
  have hnP : 4 < n * P := by
    rwa [div_lt_iff₀ hP] at hn
  rw [← Real.exp_mul]
  have h2 : Real.exp (-(n * P) * (1 / 4 : ℝ)) < Real.exp (-1) :=
    Real.exp_lt_exp.mpr (by linarith)
  have h3 : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero
    linarith
  have h4 : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-1)]

end OrbitNormInternal

open OrbitNormInternal

theorem orbitBound : OrbitBoundStatement := by
  intro X _ _ _ F ρ w P hw
  have hb := (norm_periodic hw).isBounded_of_continuous hw.pos.ne' (continuous_norm.comp hw.cont)
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  refine ⟨C, fun s => ?_⟩
  have := hC _ (mem_range_self s)
  simpa only [Real.norm_eq_abs, abs_norm] using this

theorem orbitNorm_of (h1 : OrbitPhysicalStatement) (h2 : UniqueStatement)
    (h3 : SmallDataStatement) : OrbitNormStatement := by
  intro X _ _ _ F ρ _ w P hw
  obtain ⟨c, hc, hsmall⟩ := h3 X F.toHeatBilinear
  refine ⟨c, hc, ?_⟩
  have hdec : ∀ s', ‖w s'‖ ≤ c → ∀ σ, 0 ≤ σ →
      ‖w (s' + σ)‖ ≤ Real.exp (-σ) ^ (1 / 4 : ℝ) * (2 * ‖w s'‖) := by
    intro s' hs' σ hσ
    obtain ⟨u, hu0, hum, hub⟩ := hsmall (w s') hs'
    have hss : F.IsMildOn (F.selfSimilar w s') 0 1 := h1 X F w hw.cont hw.flow s'
    have hss0 : F.selfSimilar w s' 0 = w s' := by
      simp [MildFramework.selfSimilar, F.D_one]
    have huIco : F.toHeatBilinear.IsMildOn u 0 1 :=
      ⟨hum.1.mono Ico_subset_Icc_self, fun t ht => hum.2 t (Ico_subset_Icc_self ht)⟩
    have heq := (h2 X F.toHeatBilinear u (F.selfSimilar w s') 0 1).1 huIco hss
      (by rw [hu0, hss0])
    exact decay heq _ hub σ hσ
  have hzero : ∀ s', ‖w s'‖ ≤ c → w s' = 0 := by
    intro s' hs'
    obtain ⟨n, hn⟩ := exp_quarter_small hw.pos
    have hb := hdec s' hs' (n * P) (mul_nonneg (Nat.cast_nonneg _) hw.pos.le)
    rw [norm_add_nat_mul hw] at hb
    have hnn := norm_nonneg (w s')
    have : ‖w s'‖ ≤ 0 := by nlinarith
    exact norm_le_zero_iff.mp this
  intro s
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨s₁, hs₁⟩ := hw.nonzero
  have hs0 := hzero s hlt.le
  obtain ⟨n, hn⟩ := exists_nat_gt ((s - s₁) / P)
  have hσ : 0 ≤ s₁ + n * P - s := by
    rw [div_lt_iff₀ hw.pos] at hn
    linarith
  have hb := hdec s hlt.le _ hσ
  rw [hs0, norm_zero, mul_zero, mul_zero, add_sub_cancel, norm_add_nat_mul hw] at hb
  exact hs₁ (norm_le_zero_iff.mp hb)

end Breakdown
