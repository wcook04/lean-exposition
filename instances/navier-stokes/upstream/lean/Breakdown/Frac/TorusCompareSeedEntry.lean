import Breakdown.Frac.StTorusStepCompare
import Breakdown.Torus.CompareSeedEntry

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

open CompareSeedEntry.Internal

private theorem frac_r3_slot {G D : ℝ → Freq.X →L[ℝ] Freq.X}
    (hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → G (a + b) = (G a).comp (G b))
    (hDG : ∀ μ t : ℝ, 0 < μ → 0 ≤ t → (D μ).comp (G (μ * t)) = (G t).comp (D μ))
    {lam μ s : ℝ} (hl1 : lam < 1) (hμ : 0 < μ) (hμl : μ ≤ lam) (hs : 0 ≤ s) (x : Freq.X) {w : Freq.X}
    (hw : w = G (1 - lam) x) :
    D μ (G (μ * s + lam - μ) w) = G (s + μ⁻¹ - 1) (D μ x) := by
  subst hw
  have ha : 0 ≤ μ * s + lam - μ := by nlinarith
  have ht : 0 ≤ s + μ⁻¹ - 1 := by
    have := (one_le_inv₀ hμ).2 (hμl.trans hl1.le)
    linarith
  have heq : μ * s + lam - μ + (1 - lam) = μ * (s + μ⁻¹ - 1) := by
    rw [mul_sub, mul_add, mul_inv_cancel₀ hμ.ne']
    ring
  have h1 : G (μ * s + lam - μ) (G (1 - lam) x) = G (μ * (s + μ⁻¹ - 1)) x := by
    rw [← heq, hadd _ _ ha (by linarith), ContinuousLinearMap.comp_apply]
  have h2 : D μ (G (μ * (s + μ⁻¹ - 1)) x) = G (s + μ⁻¹ - 1) (D μ x) := by
    rw [← ContinuousLinearMap.comp_apply (D μ) (G (μ * (s + μ⁻¹ - 1))), hDG μ _ hμ ht,
      ContinuousLinearMap.comp_apply]
  exact (congrArg (D μ) h1).trans h2

private theorem frac_torus_slot (α : ℝ) {T lam μ s : ℝ} (hT : 0 < T) (hl1 : lam < 1) (hμl : μ ≤ lam)
    (hμ : 0 ≤ μ) (hs : 0 ≤ s) (x : V) :
    fracTorusHeat α (T * (μ * s + lam - μ)) (fracTorusHeat α (T * (1 - lam)) x) =
      fracTorusHeat α (T * (μ * s + 1 - μ)) x := by
  have ha : 0 ≤ T * (μ * s + lam - μ) := mul_nonneg hT.le (by nlinarith)
  have hb : 0 ≤ T * (1 - lam) := mul_nonneg hT.le (by linarith)
  rw [← ContinuousLinearMap.comp_apply (fracTorusHeat α _), ← (fracTorusHeatAlgebra α).2.2.1 _ _ ha hb,
    show T * (μ * s + lam - μ) + T * (1 - lam) = T * (μ * s + 1 - μ) by ring]

theorem fracR3SeedEntry (α : ℝ) (hα : 1 < α) (hN : InvSeriesEntry) (hS : SeqOpSpec)
    (hCh : FracR3ChainFormula α) (hO : FracOperatorNormBounds α hα) (hP : PieceOperatorStatement) :
    FracR3SeedEntry α := by
  intro F hG hD P k θ E _ _ J hPk hk hθ hθ1 e n s
  obtain ⟨C, -, -, -, -, -, hr3, -⟩ := hO
  have hl : 0 < Real.exp (-(P / k)) := Real.exp_pos _
  have hPk' : 0 < P / k := div_pos hPk (Nat.cast_pos.2 hk)
  have hl1 : Real.exp (-(P / k)) < 1 := Real.exp_lt_one_iff.2 (neg_lt_zero.2 hPk')
  have hθ0 : 0 < θ := lt_trans (Real.rpow_pos_of_pos hl _) hθ
  have hnorm : ‖fracR3Shift F P k θ‖ < 1 :=
    lt_of_le_of_lt (hr3 F P k θ hPk hk hθ0) ((div_lt_one hθ0).2 hθ)
  have hL : 0 < MildFramework.stepLength P k := sub_pos.2 hl1
  have hfree : ∀ (x : Freq.X) (t : Icc (0 : ℝ) (MildFramework.stepLength P k)),
      F.stepFree P k x t = Freq.fracHeatX α t x := fun x t =>
    ((hP Freq.X F.toHeatBilinear _ hL).2.2.1 x t).trans
      (congrArg (fun G : ℝ → Freq.X →L[ℝ] Freq.X => G t x) hG)
  have hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      Freq.fracHeatX α (a + b) = (Freq.fracHeatX α a).comp (Freq.fracHeatX α b) := by
    rewrite [← hG]
    exact F.G_add
  have hDG : ∀ μ t : ℝ, 0 < μ → 0 ≤ t →
      (Freq.fracDilX α μ).comp (Freq.fracHeatX α (μ * t)) =
        (Freq.fracHeatX α t).comp (Freq.fracDilX α μ) := by
    rewrite [← hG, ← hD]
    exact F.D_G
  have hD1 : Freq.fracDilX α 1 = ContinuousLinearMap.id ℝ Freq.X := by
    rewrite [← hD]
    exact F.D_one
  have key : (Ring.inverse (1 - fracR3Shift F P k θ) (fracR3Seed F P k J e)) n =
      shiftChain (fracR3Step F P k θ) 0 n (F.stepFree P k (J e)) :=
    inverse_seed hN hS (fracR3Step F P k θ) ‖fracR3Step F P k θ 0‖ (fun _ => le_rfl) (norm_nonneg _)
      hnorm ((F.stepFree P k).comp J) e n
  refine Eq.trans (congrArg (fun f : Piece Freq.X (MildFramework.stepLength P k) => f s) key) ?_
  rcases n with _ | j
  · refine (DFunLike.congr_fun (DFunLike.congr_fun (shiftChain_zero_zero (fracR3Step F P k θ)) _) s).trans
      ((hfree (J e) s).trans ?_)
    simp only [pow_zero, inv_one, one_smul, add_sub_cancel_right, hD1, ContinuousLinearMap.id_apply]
  · have hend : pieceEnd (MildFramework.stepLength P k) (F.stepFree P k (J e)) =
        Freq.fracHeatX α (1 - Real.exp (-(P / k))) (J e) :=
      (pieceEnd_eval hL.le _).trans (hfree (J e) _)
    have hc := hCh F hG hD P k θ hPk hk (F.stepFree P k (J e)) 0 j s
    refine (DFunLike.congr_fun (DFunLike.congr_fun (shiftChain_zero_add (fracR3Step F P k θ) j) _) s).trans
      (hc.trans ?_)
    exact congrArg (HSMul.hSMul ((θ⁻¹) ^ (j + 1))) (frac_r3_slot hadd hDG hl1 (pow_pos hl (j + 1))
      (pow_le_of_le_one hl.le hl1.le (Nat.succ_ne_zero j)) s.2.1 (J e) hend)

theorem fracTorusSeedEntry (α : ℝ) (hα : 1 < α) (hN : InvSeriesEntry) (hS : SeqOpSpec)
    (hCh : FracTorusChainFormula α hα) (hO : FracOperatorNormBounds α hα) (hP : PieceOperatorStatement) :
    FracTorusSeedEntry α hα := by
  intro T lam θ hT hT1 hl hl1 E _ _ Jt hlt hθ hθ1 e n s
  obtain ⟨C, -, -, -, -, -, -, htor⟩ := hO
  have hθ0 : 0 < θ := lt_trans (Real.rpow_pos_of_pos hl _) hθ
  have hnorm : ‖fracTorusShift α hα T lam θ hT hT1 hl hl1‖ < 1 :=
    lt_of_le_of_lt (htor T lam θ hT hT1 hl hl1 hθ0) ((div_lt_one hθ0).2 hθ)
  have hL : 0 < 1 - lam := sub_pos.2 hlt
  have hB : ∀ i, ‖fracTorusStep α hα T lam θ hT hT1 hl hl1 i‖ ≤ ‖lam ^ dilExponent α / θ‖ := fun i => by
    unfold fracTorusStep
    refine (norm_smul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) ?_)
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_one₀ (norm_pieceFree_le _ _) (norm_nonneg _)
        (norm_pieceEnd_le _))
  have key : (Ring.inverse (1 - fracTorusShift α hα T lam θ hT hT1 hl hl1)
      (fracTorusSeed α hα T lam hT hT1 hl hl1 Jt e)) n =
      shiftChain (fracTorusStep α hα T lam θ hT hT1 hl hl1) 0 n
        ((fracStepFrame α hα (stepScale T lam 0) (stepScale_pos hT hl 0)
          (stepScale_le_one hT1 hl hl1 0)).pieceFree (1 - lam) (Jt e)) :=
    inverse_seed hN hS (fracTorusStep α hα T lam θ hT hT1 hl hl1) _ hB (norm_nonneg _) hnorm _ e n
  have hfree : ∀ t : Icc (0 : ℝ) (1 - lam),
      (fracStepFrame α hα (stepScale T lam 0) (stepScale_pos hT hl 0)
        (stepScale_le_one hT1 hl hl1 0)).pieceFree (1 - lam) (Jt e) t = fracTorusHeat α (T * t) (Jt e) :=
    fun t => by
      refine ((hP V _ (1 - lam) hL).2.2.1 (Jt e) t).trans ?_
      show fracTorusHeat α (stepScale T lam 0 * t) (Jt e) = _
      rw [stepScale, pow_zero, mul_one]
  rw [key]
  rcases n with _ | j
  · rw [shiftChain_zero_zero, ContinuousLinearMap.id_apply, hfree]
    simp only [pow_zero, one_smul, one_mul, add_sub_cancel_right]
  · have hc := hCh T lam θ hT hT1 hl hl1 hlt
      ((fracStepFrame α hα (stepScale T lam 0) (stepScale_pos hT hl 0)
        (stepScale_le_one hT1 hl hl1 0)).pieceFree (1 - lam) (Jt e)) 0 j s
    rw [zero_add] at hc
    rw [hc, pieceEnd_eval hL.le, hfree, stepScale, pow_zero, mul_one]
    exact congrArg _ (frac_torus_slot α hT hlt (pow_le_of_le_one hl.le hl1 (Nat.succ_ne_zero j))
      (pow_nonneg hl.le _) s.2.1 (Jt e))

end Breakdown.Periodic
