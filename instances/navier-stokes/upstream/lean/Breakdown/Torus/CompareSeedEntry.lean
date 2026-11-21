import Breakdown.Torus.CompareStatements
import Breakdown.Transfer.StatementsLocal

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

namespace CompareSeedEntry.Internal

theorem norm_pieceFree_le {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (H : HeatBilinear Y) (T : ℝ) : ‖H.pieceFree T‖ ≤ 1 := by
  unfold HeatBilinear.pieceFree
  split_ifs with h
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    refine (ContinuousMap.norm_le _ (norm_nonneg x)).2 fun t => ?_
    rw [h.choose_spec x t]
    simpa using (H.G t).le_of_opNorm_le (H.G_norm t t.2.1) x
  · simp

theorem norm_pieceEnd_le {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : ℝ) :
    ‖(pieceEnd T : Piece Y T →L[ℝ] Y)‖ ≤ 1 := by
  unfold pieceEnd
  split_ifs with h
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    rw [one_mul]
    exact ContinuousMap.norm_coe_le_norm f _
  · simp

theorem seqSeed_apply (hS : SeqOpSpec) {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (A : E →L[ℝ] X) (e : E) (n : ℕ) :
    seqSeed A e n = if n = 0 then A e else 0 := by
  have h0 : ∀ k : ℕ, ‖(fun _ : ℕ => (0 : X →L[ℝ] X)) k‖ ≤ 0 := fun _ => by simp
  have hid := ((hS X X (fun _ => 0) 0 h0 le_rfl).2.2.2 (ContinuousLinearMap.id ℝ X)).1
  have hex : ∃ T : E →L[ℝ] lp (fun _ : ℕ => X) ∞, ∀ e n, T e n = if n = 0 then A e else 0 :=
    ⟨(seqSeed (ContinuousLinearMap.id ℝ X)).comp A, fun e n => by
      rw [ContinuousLinearMap.comp_apply, hid]
      rfl⟩
  unfold seqSeed
  rw [dif_pos hex]
  exact hex.choose_spec e n

theorem seqShift_apply (hS : SeqOpSpec) {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (B : ℕ → X →L[ℝ] X) (C : ℝ) (hB : ∀ n, ‖B n‖ ≤ C) (hC : 0 ≤ C) :
    ∀ g n, seqShift B g n = if n = 0 then 0 else B (n - 1) (g (n - 1)) :=
  ((hS X X (fun _ => 0) C (fun _ => by simpa using hC) hC).2.2.1 B hB).1

theorem inverse_seed (hN : InvSeriesEntry) (hS : SeqOpSpec) {E X : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (B : ℕ → X →L[ℝ] X) (C : ℝ) (hB : ∀ n, ‖B n‖ ≤ C) (hC : 0 ≤ C) (hlt : ‖seqShift B‖ < 1)
    (A : E →L[ℝ] X) (e : E) (n : ℕ) :
    (Ring.inverse (1 - seqShift B) (seqSeed A e)) n = shiftChain B 0 n (A e) := by
  rw [hN X B hlt (seqShift_apply hS B C hB hC) (seqSeed A e) n, Finset.sum_eq_single 0]
  · rw [seqSeed_apply hS, if_pos rfl]
  · intro m _ hm
    rw [seqSeed_apply hS, if_neg hm, map_zero]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos n)) h

theorem shiftChain_zero_zero {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : ℕ → X →L[ℝ] X) : shiftChain B 0 0 = ContinuousLinearMap.id ℝ X := by
  simp [shiftChain]

theorem shiftChain_zero_add {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : ℕ → X →L[ℝ] X) (j : ℕ) : shiftChain B 0 (j + 1) = shiftChain B 0 (0 + j + 1) := by
  rw [Nat.zero_add]

theorem pieceEnd_eval {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {L : ℝ} (hL : 0 ≤ L)
    (z : Piece X L) : pieceEnd L z = z ⟨L, hL, le_rfl⟩ := by
  unfold pieceEnd
  rw [dif_pos hL]
  rfl

theorem r3_slot
    (hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → Freq.heatX (a + b) = (Freq.heatX a).comp (Freq.heatX b))
    (hDG : ∀ μ t : ℝ, 0 < μ → 0 ≤ t →
      (Freq.dilX μ).comp (Freq.heatX (μ * t)) = (Freq.heatX t).comp (Freq.dilX μ))
    {lam μ s : ℝ} (hl1 : lam < 1) (hμ : 0 < μ) (hμl : μ ≤ lam) (hs : 0 ≤ s) (x : Freq.X) {w : Freq.X}
    (hw : w = Freq.heatX (1 - lam) x) :
    Freq.dilX μ (Freq.heatX (μ * s + lam - μ) w) = Freq.heatX (s + μ⁻¹ - 1) (Freq.dilX μ x) := by
  subst hw
  have ha : 0 ≤ μ * s + lam - μ := by nlinarith
  have ht : 0 ≤ s + μ⁻¹ - 1 := by
    have := (one_le_inv₀ hμ).2 (hμl.trans hl1.le)
    linarith
  have heq : μ * s + lam - μ + (1 - lam) = μ * (s + μ⁻¹ - 1) := by
    rw [mul_sub, mul_add, mul_inv_cancel₀ hμ.ne']
    ring
  have h1 : Freq.heatX (μ * s + lam - μ) (Freq.heatX (1 - lam) x) =
      Freq.heatX (μ * (s + μ⁻¹ - 1)) x := by
    rw [← heq, hadd _ _ ha (by linarith), ContinuousLinearMap.comp_apply]
  have h2 : Freq.dilX μ (Freq.heatX (μ * (s + μ⁻¹ - 1)) x) =
      Freq.heatX (s + μ⁻¹ - 1) (Freq.dilX μ x) := by
    rw [← ContinuousLinearMap.comp_apply (Freq.dilX μ) (Freq.heatX (μ * (s + μ⁻¹ - 1))), hDG μ _ hμ ht,
      ContinuousLinearMap.comp_apply]
  exact (congrArg (Freq.dilX μ) h1).trans h2

theorem torus_slot {T lam μ s : ℝ} (hT : 0 < T) (hl1 : lam < 1) (hμl : μ ≤ lam) (hμ : 0 ≤ μ)
    (hs : 0 ≤ s) (x : V) :
    heat (T * (μ * s + lam - μ)) (heat (T * (1 - lam)) x) = heat (T * (μ * s + 1 - μ)) x := by
  have ha : 0 ≤ T * (μ * s + lam - μ) := mul_nonneg hT.le (by nlinarith)
  have hb : 0 ≤ T * (1 - lam) := mul_nonneg hT.le (by linarith)
  rw [← ContinuousLinearMap.comp_apply (heat _), ← heat_add _ _ ha hb,
    show T * (μ * s + lam - μ) + T * (1 - lam) = T * (μ * s + 1 - μ) by ring]

end CompareSeedEntry.Internal

open CompareSeedEntry.Internal

theorem r3SeedEntry (hN : InvSeriesEntry) (hS : SeqOpSpec) (hCh : R3ChainFormula)
    (hO : OperatorNormBounds) (hP : PieceOperatorStatement) : R3SeedEntry := by
  intro F hG hD P k θ E _ _ J hPk hk hθ hθ1 e n s
  obtain ⟨C, -, -, -, -, -, hr3, -⟩ := hO
  have hl : 0 < Real.exp (-(P / k)) := Real.exp_pos _
  have hPk' : 0 < P / k := div_pos hPk (Nat.cast_pos.2 hk)
  have hl1 : Real.exp (-(P / k)) < 1 := Real.exp_lt_one_iff.2 (neg_lt_zero.2 hPk')
  have hθ0 : 0 < θ := lt_trans (Real.rpow_pos_of_pos hl _) hθ
  have hnorm : ‖r3Shift F P k θ‖ < 1 :=
    lt_of_le_of_lt (hr3 F P k θ hPk hk hθ0) ((div_lt_one hθ0).2 hθ)
  have hL : 0 < MildFramework.stepLength P k := sub_pos.2 hl1
  have hfree : ∀ (x : Freq.X) (t : Icc (0 : ℝ) (MildFramework.stepLength P k)),
      F.stepFree P k x t = Freq.heatX t x := fun x t =>
    ((hP Freq.X F.toHeatBilinear _ hL).2.2.1 x t).trans
      (congrArg (fun G : ℝ → Freq.X →L[ℝ] Freq.X => G t x) hG)
  have hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      Freq.heatX (a + b) = (Freq.heatX a).comp (Freq.heatX b) := by
    rewrite [← hG]
    exact F.G_add
  have hDG : ∀ μ t : ℝ, 0 < μ → 0 ≤ t →
      (Freq.dilX μ).comp (Freq.heatX (μ * t)) = (Freq.heatX t).comp (Freq.dilX μ) := by
    rewrite [← hG, ← hD]
    exact F.D_G
  have hD1 : Freq.dilX 1 = ContinuousLinearMap.id ℝ Freq.X := by
    rewrite [← hD]
    exact F.D_one
  have key : (Ring.inverse (1 - r3Shift F P k θ) (r3Seed F P k J e)) n =
      shiftChain (r3Step F P k θ) 0 n (F.stepFree P k (J e)) :=
    inverse_seed hN hS (r3Step F P k θ) ‖r3Step F P k θ 0‖ (fun _ => le_rfl) (norm_nonneg _) hnorm
      ((F.stepFree P k).comp J) e n
  refine Eq.trans (congrArg (fun f : Piece Freq.X (MildFramework.stepLength P k) => f s) key) ?_
  rcases n with _ | j
  · refine (DFunLike.congr_fun (DFunLike.congr_fun (shiftChain_zero_zero (r3Step F P k θ)) _) s).trans
      ((hfree (J e) s).trans ?_)
    simp only [pow_zero, inv_one, one_smul, add_sub_cancel_right, hD1, ContinuousLinearMap.id_apply]
  · have hend : pieceEnd (MildFramework.stepLength P k) (F.stepFree P k (J e)) =
        Freq.heatX (1 - Real.exp (-(P / k))) (J e) :=
      (pieceEnd_eval hL.le _).trans (hfree (J e) _)
    have hc := hCh F hG hD P k θ hPk hk (F.stepFree P k (J e)) 0 j s
    refine (DFunLike.congr_fun (DFunLike.congr_fun (shiftChain_zero_add (r3Step F P k θ) j) _) s).trans
      (hc.trans ?_)
    exact congrArg (HSMul.hSMul ((θ⁻¹) ^ (j + 1))) (r3_slot hadd hDG hl1 (pow_pos hl (j + 1))
      (pow_le_of_le_one hl.le hl1.le (Nat.succ_ne_zero j)) s.2.1 (J e) hend)

theorem torusSeedEntry (hN : InvSeriesEntry) (hS : SeqOpSpec) (hCh : TorusChainFormula)
    (hO : OperatorNormBounds) (hP : PieceOperatorStatement) : TorusSeedEntry := by
  intro hK T lam θ hT hT1 hl hl1 E _ _ Jt hlt hθ hθ1 e n s
  obtain ⟨C, -, -, -, -, -, -, htor⟩ := hO
  have hθ0 : 0 < θ := lt_trans (Real.rpow_pos_of_pos hl _) hθ
  have hnorm : ‖torusShift hK T lam θ hT hT1 hl hl1‖ < 1 :=
    lt_of_le_of_lt (htor hK T lam θ hT hT1 hl hl1 hθ0) ((div_lt_one hθ0).2 hθ)
  have hL : 0 < 1 - lam := sub_pos.2 hlt
  have hB : ∀ i, ‖torusStep hK T lam θ hT hT1 hl hl1 i‖ ≤ ‖lam ^ (1 / 4 : ℝ) / θ‖ := fun i => by
    unfold torusStep
    refine (norm_smul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) ?_)
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_one₀ (norm_pieceFree_le _ _) (norm_nonneg _)
        (norm_pieceEnd_le _))
  have key : (Ring.inverse (1 - torusShift hK T lam θ hT hT1 hl hl1)
      (torusSeed hK T lam hT hT1 hl hl1 Jt e)) n =
      shiftChain (torusStep hK T lam θ hT hT1 hl hl1) 0 n
        ((stepFrame hK (stepScale T lam 0) (stepScale_pos hT hl 0)
          (stepScale_le_one hT1 hl hl1 0)).pieceFree (1 - lam) (Jt e)) :=
    inverse_seed hN hS (torusStep hK T lam θ hT hT1 hl hl1) _ hB (norm_nonneg _) hnorm _ e n
  have hfree : ∀ t : Icc (0 : ℝ) (1 - lam),
      (stepFrame hK (stepScale T lam 0) (stepScale_pos hT hl 0)
        (stepScale_le_one hT1 hl hl1 0)).pieceFree (1 - lam) (Jt e) t = heat (T * t) (Jt e) :=
    fun t => by
      refine ((hP V _ (1 - lam) hL).2.2.1 (Jt e) t).trans ?_
      show heat (stepScale T lam 0 * t) (Jt e) = _
      rw [stepScale, pow_zero, mul_one]
  rw [key]
  rcases n with _ | j
  · rw [shiftChain_zero_zero, ContinuousLinearMap.id_apply, hfree]
    simp only [pow_zero, one_smul, one_mul, add_sub_cancel_right]
  · have hc := hCh hK T lam θ hT hT1 hl hl1 hlt
      ((stepFrame hK (stepScale T lam 0) (stepScale_pos hT hl 0)
        (stepScale_le_one hT1 hl hl1 0)).pieceFree (1 - lam) (Jt e)) 0 j s
    rw [zero_add] at hc
    rw [hc, pieceEnd_eval hL.le, hfree, stepScale, pow_zero, mul_one]
    exact congrArg _ (torus_slot hT hlt (pow_le_of_le_one hl.le hl1 (Nat.succ_ne_zero j))
      (pow_nonneg hl.le _) s.2.1 (Jt e))

end Breakdown.Periodic
