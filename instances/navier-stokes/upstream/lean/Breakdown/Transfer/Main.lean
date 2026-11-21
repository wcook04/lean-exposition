import Breakdown.Transfer.StatementsLocal
import Breakdown.Transfer.StatementsFrame
import Breakdown.Transfer.StatementsAbstract

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Breakdown

namespace TransferAssemblyInternal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem extendPiece_add {T : ℝ} (f g : Piece X T) (t : ℝ) :
    extendPiece (f + g) t = extendPiece f t + extendPiece g t := by
  unfold extendPiece
  split_ifs with h
  · rfl
  · simp

theorem extendPiece_of_mem {T : ℝ} (f : Piece X T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    extendPiece f t = f ⟨t, ht⟩ := by
  have h : (0 : ℝ) ≤ T := ht.1.trans ht.2
  simp only [extendPiece, h, dite_true]
  exact Set.IccExtend_of_mem h f ht

theorem extendPiece_end {T : ℝ} (h : 0 ≤ T) (f : Piece X T) :
    extendPiece f T = pieceEnd T f := by
  rw [extendPiece_of_mem f ⟨h, le_rfl⟩]
  simp [pieceEnd, h]

theorem norm_extendPiece_le {T : ℝ} (f : Piece X T) (t : ℝ) : ‖extendPiece f t‖ ≤ ‖f‖ := by
  unfold extendPiece
  split_ifs with h
  · exact ContinuousMap.norm_coe_le_norm f _
  · simp

theorem add_sub_left_eq (a b : X) : a + b - a = b := by abel

end TransferAssemblyInternal

open TransferAssemblyInternal

theorem transferHolds_of (h1 : StepDataStatement) (h2 : ContractionStatement)
    (h3 : PiecePerturbationStatement) (h4 : ProfilePieceStatement) (h5 : GlueStatement) :
    TransferHolds := by
  intro X _ _ _ F ρ hc w P ho C' hC' ε hε
  obtain ⟨k, θ, hk, hL, hθ0, hθ1, -, V, J, R, -, hJ, -, hR⟩ :=
    h1 X F ρ hc w P ho C' hC' (1 / 2) (by norm_num)
  have hPk : 0 < P / k := div_pos ho.pos (Nat.cast_pos.mpr hk)
  have hμ0 : 0 < Real.exp (-(P / k)) := Real.exp_pos _
  have hμ1 : Real.exp (-(P / k)) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_lt_zero.mpr hPk)
  have hLpos : 0 < MildFramework.stepLength P k := by
    simp only [MildFramework.stepLength]
    linarith
  have hL1 : MildFramework.stepLength P k ≤ 1 := by linarith
  have hθpos : 0 < θ := lt_of_le_of_lt (Real.rpow_nonneg hμ0.le _) hθ0
  obtain ⟨ϱ₀, hϱ₀, C₁, hcon⟩ := h2 X (Piece X (MildFramework.stepLength P k)) (F.stepOp w P k)
    (F.stepFree P k) (F.stepEnd P k) J (F.toHeatBilinear.pieceBil (MildFramework.stepLength P k))
    θ R hθpos hθ1.le hR
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 1 + ‖J‖ * (|C₁| + 1) := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by
    have := norm_nonneg J
    have := abs_nonneg C₁
    rw [hMdef]
    nlinarith
  obtain ⟨f₀, hf₀, hdist⟩ := hC'.exists_dist_lt (w 0)
    (lt_min hϱ₀ (div_pos hε (by linarith)) : 0 < min ϱ₀ (ε / M))
  have hξ : ‖f₀ - w 0‖ < min ϱ₀ (ε / M) := by
    rw [← dist_eq_norm, dist_comm]
    exact hdist
  obtain ⟨e, z, he, hz⟩ := hcon (f₀ - w 0) (hξ.le.trans (min_le_left _ _))
  obtain ⟨v, hvdef⟩ : ∃ v : ℕ → Piece X (MildFramework.stepLength P k), ∀ n, v n = θ ^ n • z n :=
    ⟨fun n => θ ^ n • z n, fun n => rfl⟩
  obtain ⟨x, hx0, hxs⟩ : ∃ x : ℕ → X, x 0 = J e + (f₀ - w 0) ∧
      ∀ m, x (m + 1) = F.stepEnd P k (v m) :=
    ⟨fun n => Nat.rec (J e + (f₀ - w 0)) (fun m _ => F.stepEnd P k (v m)) n, rfl, fun m => rfl⟩
  have hv : ∀ n, v n = F.toHeatBilinear.pieceFree (MildFramework.stepLength P k) (x n) +
      (2 : ℝ) • F.toHeatBilinear.pieceBil (MildFramework.stepLength P k) (F.profilePiece w P k n) (v n) +
      F.toHeatBilinear.pieceBil (MildFramework.stepLength P k) (v n) (v n) := by
    intro n
    have hcfree : θ ^ n • (if n = 0 then F.stepFree P k (J e + (f₀ - w 0))
        else θ⁻¹ • F.stepFree P k (F.stepEnd P k (z (n - 1)))) =
        F.toHeatBilinear.pieceFree (MildFramework.stepLength P k) (x n) := by
      rcases n with _ | m
      · rw [if_pos rfl, pow_zero, one_smul, hx0]
        rfl
      · rw [if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel, smul_smul, pow_succ, mul_assoc,
          mul_inv_cancel₀ hθpos.ne', mul_one, hxs, hvdef, map_smul, map_smul]
        rfl
    have h := hz n
    have h' : z n = (if n = 0 then F.stepFree P k (J e + (f₀ - w 0))
        else θ⁻¹ • F.stepFree P k (F.stepEnd P k (z (n - 1)))) + F.stepOp w P k n (z n) +
        θ ^ n • F.toHeatBilinear.pieceBil (MildFramework.stepLength P k) (z n) (z n) := by
      rw [← h]
      abel
    have hop : ∀ y, F.stepOp w P k n y =
        (2 : ℝ) • F.toHeatBilinear.pieceBil (MildFramework.stepLength P k) (F.profilePiece w P k n) y :=
      fun y => rfl
    rw [hvdef, ← hcfree]
    refine (congrArg (fun y => θ ^ n • y) h').trans ?_
    simp only [hop, smul_add, map_smul, smul_apply, smul_smul]
    rw [mul_comm (θ ^ n) 2]
  have hpert : ∀ n, extendPiece (v n) 0 = x n ∧
      F.IsMildOnIcc (extendPiece (F.profilePiece w P k n + v n)) 0 (MildFramework.stepLength P k) :=
    fun n => h3 X F.toHeatBilinear _ (F.profilePiece w P k n) (v n) (x n) hLpos hL1
      ((h4 X F ρ hc w P ho k hk n).2.1) (hv n)
  have hglue := h5 X F (Real.exp (-(P / k))) (fun n => F.profilePiece w P k n + v n) hμ0 hμ1
    (fun n => (hpert n).2) (by
      intro n
      show extendPiece (F.profilePiece w P k (n + 1) + v (n + 1)) 0 =
        F.D (Real.exp (-(P / k))) (extendPiece (F.profilePiece w P k n + v n) (MildFramework.stepLength P k))
      rw [extendPiece_add, extendPiece_add, (hpert (n + 1)).1, hxs n,
        ← (h4 X F ρ hc w P ho k hk n).2.2.1, extendPiece_end hLpos.le, extendPiece_end hLpos.le,
        map_add]
      rfl)
  have hmem0 : (0 : ℝ) ∈ Icc 0 (MildFramework.stepLength P k) := ⟨le_rfl, hLpos.le⟩
  have hU0 : F.gluePieces (Real.exp (-(P / k))) (fun n => F.profilePiece w P k n + v n) 0 =
      w 0 + (J e + (f₀ - w 0)) := by
    have hidx : MildFramework.stepIndex (Real.exp (-(P / k))) 0 = 0 := by
      simp [MildFramework.stepIndex]
    simp only [MildFramework.gluePieces, hidx, pow_zero, inv_one, F.D_one, sub_self,
      div_one, ContinuousLinearMap.id_apply]
    show extendPiece (F.profilePiece w P k 0 + v 0) 0 = _
    rw [extendPiece_add, (hpert 0).1, hx0, extendPiece_of_mem _ hmem0,
      (h4 X F ρ hc w P ho k hk 0).1 ⟨0, hmem0⟩]
    simp [MildFramework.selfSimilar, F.D_one]
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = Real.log θ / Real.log (Real.exp (-(P / k))) := ⟨_, rfl⟩
  have hlogμ : Real.log (Real.exp (-(P / k))) < 0 := by
    rw [Real.log_exp]
    exact neg_lt_zero.mpr hPk
  have hκpos : 0 < κ := by
    rw [hκdef]
    exact div_pos_of_neg_of_neg (Real.log_neg hθpos hθ1) hlogμ
  refine ⟨F.gluePieces (Real.exp (-(P / k))) (fun n => F.profilePiece w P k n + v n), ?_, ?_,
    hglue.1, θ⁻¹ * ‖z‖, κ, hκpos, ?_⟩
  · rw [hU0]
    have : w 0 + (J e + (f₀ - w 0)) = J e + f₀ := by abel
    rw [this]
    exact C'.add_mem (hJ e) hf₀
  · rw [hU0, add_sub_left_eq]
    have ha : ‖f₀ - w 0‖ < ε / M := hξ.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by linarith)] at ha
    have hJe : ‖J e‖ ≤ ‖J‖ * ‖e‖ := J.le_opNorm e
    have he' : ‖e‖ ≤ |C₁| * ‖f₀ - w 0‖ :=
      he.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
    have hJe' : ‖J‖ * ‖e‖ ≤ ‖J‖ * ((|C₁| + 1) * ‖f₀ - w 0‖) :=
      mul_le_mul_of_nonneg_left (he'.trans (mul_le_mul_of_nonneg_right (by linarith)
        (norm_nonneg _))) (norm_nonneg _)
    calc ‖J e + (f₀ - w 0)‖ ≤ ‖J e‖ + ‖f₀ - w 0‖ := norm_add_le _ _
      _ ≤ ‖f₀ - w 0‖ * M := by rw [hMdef]; nlinarith
      _ < ε := ha
  · intro t ht
    obtain ⟨n, s, hs, h1t, hD⟩ := hglue.2 t ht
    have hs2 : s < 1 - Real.exp (-(P / k)) := hs.2
    have hs1 : 0 < 1 - s := by linarith
    have hsI : s ∈ Icc (0 : ℝ) (MildFramework.stepLength P k) := ⟨hs.1, hs.2.le⟩
    have hlog : -Real.log (1 - t) = n * (P / k) - Real.log (1 - s) := by
      rw [h1t, Real.log_mul (pow_ne_zero _ hμ0.ne') hs1.ne', Real.log_pow, Real.log_exp]
      ring
    have hself : F.D (1 - s) (F.selfSimilar w (n * (P / k)) s) = w (-Real.log (1 - t)) := by
      rw [MildFramework.selfSimilar, hlog, ← ContinuousLinearMap.comp_apply,
        ← F.D_mul _ _ hs1 (inv_pos.mpr hs1), mul_inv_cancel₀ hs1.ne', F.D_one,
        ContinuousLinearMap.id_apply]
    rw [hD]
    show ‖F.D (1 - s) (extendPiece (F.profilePiece w P k n + v n) s) - w (-Real.log (1 - t))‖ ≤ _
    rw [extendPiece_add, map_add, extendPiece_of_mem _ hsI,
      (h4 X F ρ hc w P ho k hk n).1 ⟨s, hsI⟩]
    rw [show ((⟨s, hsI⟩ : Icc (0 : ℝ) (MildFramework.stepLength P k)) : ℝ) = s from rfl, hself,
      add_sub_left_eq, F.D_norm _ hs1]
    have hlt : Real.exp (-(P / k)) ^ (n + 1) ≤ 1 - t := by
      rw [h1t, pow_succ]
      exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hμ0.le _)
    have hpowκ : (Real.exp (-(P / k)) ^ (n + 1)) ^ κ = θ ^ (n + 1) := by
      rw [Real.rpow_def_of_pos (pow_pos hμ0 _), Real.log_pow,
        ← Real.exp_log (pow_pos hθpos (n + 1)), Real.log_pow, hκdef]
      congr 1
      field_simp
      exact mul_div_cancel_left₀ _ hlogμ.ne
    have hθn : θ ^ n ≤ θ⁻¹ * (1 - t) ^ κ := by
      have h2 : θ ^ (n + 1) ≤ (1 - t) ^ κ := by
        rw [← hpowκ]
        exact Real.rpow_le_rpow (pow_nonneg hμ0.le _) hlt hκpos.le
      rw [pow_succ] at h2
      calc θ ^ n = θ⁻¹ * (θ ^ n * θ) := by field_simp
        _ ≤ θ⁻¹ * (1 - t) ^ κ := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hθpos.le)
    have hr : (1 - s) ^ (1 / 4 : ℝ) ≤ 1 :=
      Real.rpow_le_one hs1.le (by linarith [hs.1]) (by norm_num)
    have hy : ‖extendPiece (v n) s‖ ≤ θ ^ n * ‖z‖ := by
      refine (norm_extendPiece_le _ _).trans ?_
      rw [hvdef, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hθpos n)]
      exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm ENNReal.top_ne_zero z n)
        (pow_nonneg hθpos.le n)
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    have hfin := mul_le_mul_of_nonneg_right hθn hz0
    calc (1 - s) ^ (1 / 4 : ℝ) * ‖extendPiece (v n) s‖ ≤ 1 * (θ ^ n * ‖z‖) :=
          mul_le_mul hr hy (norm_nonneg _) zero_le_one
      _ ≤ θ⁻¹ * ‖z‖ * (1 - t) ^ κ := by linarith

end Breakdown
