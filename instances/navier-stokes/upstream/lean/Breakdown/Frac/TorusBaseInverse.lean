import Breakdown.Frac.StTorusInverse
import Breakdown.Frac.ScaledStatements

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

namespace FracBaseInverseInternal

theorem exponent_pos {α : ℝ} (hα : 1 < α) : 0 < dilExponent α := by
  unfold dilExponent
  have h4 : (0 : ℝ) < 4 * α := by linarith
  rw [sub_pos, div_lt_one h4]
  linarith

theorem seqChain_comp_eq_id {W Y : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Sh Op : lp (fun _ : ℕ => Y) ∞ →L[ℝ] lp (fun _ : ℕ => Y) ∞)
    (Sd : W →L[ℝ] lp (fun _ : ℕ => Y) ∞)
    (R : lp (fun _ : ℕ => Y) ∞ →L[ℝ] W × lp (fun _ : ℕ => Y) ∞)
    (A : ℕ → Y →L[ℝ] Y) (B : Y →L[ℝ] Y) (G : W →L[ℝ] Y)
    (hOp : ∀ g n, Op g n = A n (g n))
    (hSh : ∀ g n, Sh g n = if n = 0 then 0 else B (g (n - 1)))
    (hSd : ∀ e n, Sd e n = if n = 0 then G e else 0)
    (hR : ∀ g n, (R g).2 n - A n ((R g).2 n) -
      (if n = 0 then G (R g).1 else B ((R g).2 (n - 1))) = g n) :
    ContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ W (lp (fun _ : ℕ => Y) ∞) -
      Sh.comp (ContinuousLinearMap.snd ℝ W (lp (fun _ : ℕ => Y) ∞)) -
      Sd.comp (ContinuousLinearMap.fst ℝ W (lp (fun _ : ℕ => Y) ∞)) -
      Op.comp (ContinuousLinearMap.snd ℝ W (lp (fun _ : ℕ => Y) ∞))) R =
      ContinuousLinearMap.id ℝ _ := by
  refine ContinuousLinearMap.ext fun g => lp.ext (funext fun n => ?_)
  have h := hR g n
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, sub_apply,
    lp.coeFn_sub, Pi.sub_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst',
    hOp, hSh, hSd]
  rw [← h]
  by_cases hn : n = 0
  · simp only [hn, if_true]
    abel
  · simp only [hn, if_false]
    abel

end FracBaseInverseInternal

theorem fracBaseInverse (α : ℝ) (hα : 1 < α) (hStep : ScaledStepDataStatement) (hS : SeqOpSpec) :
    FracBaseInverse α := by
  intro F ρ hρ w P hw C' hC' t₀ ht₀
  have hκ₀ : (0 : ℝ) < 1 / (4 * α) := one_div_pos.2 (by linarith)
  have h0 := hStep Freq.X (dilExponent α) (FracBaseInverseInternal.exponent_pos hα) F ρ hρ w P hw C' hC' t₀ ht₀
    (1 / (4 * α)) hκ₀
  obtain ⟨k, θ, hk, hL, hθ, hθ₀, hθ1, hop, h1⟩ := h0
  obtain ⟨Vs, J, R, hfd, h3⟩ := h1
  obtain ⟨hJ, hRV, hR⟩ := h3
  let R₁ : R3Seq (MildFramework.stepLength P k) →L[ℝ] Vs :=
    ((ContinuousLinearMap.fst ℝ _ _).comp R).codRestrict Vs hRV
  let R' : R3Seq (MildFramework.stepLength P k) →L[ℝ] Vs × R3Seq (MildFramework.stepLength P k) :=
    R₁.prod ((ContinuousLinearMap.snd ℝ _ _).comp R)
  refine ⟨k, θ, Vs, J, R', hk, hL, hθ, hθ₀, hθ1, hfd, hJ, ?_⟩
  have hA := (hS (Piece Freq.X (MildFramework.stepLength P k)) (Piece Freq.X (MildFramework.stepLength P k))
    (fun n => (2 : ℝ) • F.toHeatBilinear.pieceBil (MildFramework.stepLength P k) (F.profilePiece w P k n))
    (1 / 4) (fun n => hop n) (by norm_num)).1
  have hB := ((hS (Piece Freq.X (MildFramework.stepLength P k)) (Piece Freq.X (MildFramework.stepLength P k))
    (fun _ => 0) ‖θ⁻¹ • (F.stepFree P k).comp (F.stepEnd P k)‖ (fun _ => by simp) (norm_nonneg _)).2.2.1
    (fun _ => θ⁻¹ • (F.stepFree P k).comp (F.stepEnd P k)) (fun _ => le_rfl)).1
  have hC := ((hS Vs (Piece Freq.X (MildFramework.stepLength P k)) (fun _ => 0) 0 (fun _ => by simp)
    le_rfl).2.2.2 ((F.stepFree P k).comp (J.comp Vs.subtypeL : Vs →L[ℝ] Freq.X))).1
  exact FracBaseInverseInternal.seqChain_comp_eq_id (fracR3Shift F P k θ)
    (seqOp fun n => (2 : ℝ) • F.toHeatBilinear.pieceBil (MildFramework.stepLength P k) (F.profilePiece w P k n))
    (fracR3Seed F P k (J.comp Vs.subtypeL : Vs →L[ℝ] Freq.X)) R'
    (fun n => (2 : ℝ) • F.toHeatBilinear.pieceBil (MildFramework.stepLength P k) (F.profilePiece w P k n))
    (θ⁻¹ • (F.stepFree P k).comp (F.stepEnd P k))
    ((F.stepFree P k).comp (J.comp Vs.subtypeL : Vs →L[ℝ] Freq.X)) hA hB hC (fun g n => hR g n)

end Breakdown.Periodic
