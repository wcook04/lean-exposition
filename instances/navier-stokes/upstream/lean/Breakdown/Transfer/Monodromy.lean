import Breakdown.Transfer.StatementsFrame
import Breakdown.Transfer.StatementsLocal

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

private def liftPiece (T : ℝ) (e : X ≃ₗᵢ[ℝ] X) : Piece X T →L[ℝ] Piece X T :=
  ContinuousLinearMap.compLeftContinuous ℝ (Icc (0 : ℝ) T) (e.toContinuousLinearEquiv : X →L[ℝ] X)

private theorem liftPiece_apply (T : ℝ) (e : X ≃ₗᵢ[ℝ] X) (f : Piece X T) (t : Icc (0 : ℝ) T) :
    liftPiece T e f t = e (f t) := rfl

private theorem extendPiece_liftPiece {T : ℝ} (hT : 0 ≤ T) (e : X ≃ₗᵢ[ℝ] X) (f : Piece X T) (s : ℝ) :
    extendPiece (liftPiece T e f) s = e (extendPiece f s) := by
  unfold extendPiece
  rw [dif_pos hT, dif_pos hT, Set.IccExtend_apply, Set.IccExtend_apply]
  rfl

private theorem pieceEnd_apply {T : ℝ} (hT : 0 ≤ T) (f : Piece X T) :
    pieceEnd T f = f ⟨T, hT, le_rfl⟩ := by
  unfold pieceEnd
  rw [dif_pos hT]
  rfl

private theorem liftPiece_mul_symm (T : ℝ) (e : X ≃ₗᵢ[ℝ] X) :
    liftPiece T e * liftPiece T e.symm = 1 := by
  ext f t
  simp [liftPiece_apply]

private theorem liftPiece_symm_mul (T : ℝ) (e : X ≃ₗᵢ[ℝ] X) :
    liftPiece T e.symm * liftPiece T e = 1 := by
  ext f t
  simp [liftPiece_apply]

private theorem norm_inverse_one_sub_le {R : Type*} [NormedRing R] (h1 : ‖(1 : R)‖ ≤ 1) {x : R}
    (hu : IsUnit (1 - x)) (hx : ‖x‖ ≤ 1 / 4) : ‖Ring.inverse (1 - x)‖ ≤ 4 / 3 := by
  have hy : (1 - x) * Ring.inverse (1 - x) = 1 := Ring.mul_inverse_cancel _ hu
  rw [sub_mul, one_mul] at hy
  have hy' := sub_eq_iff_eq_add.mp hy
  have hle : ‖Ring.inverse (1 - x)‖ ≤ 1 + ‖x‖ * ‖Ring.inverse (1 - x)‖ := by
    calc ‖Ring.inverse (1 - x)‖ = ‖1 + x * Ring.inverse (1 - x)‖ := by rw [← hy']
      _ ≤ ‖(1 : R)‖ + ‖x * Ring.inverse (1 - x)‖ := norm_add_le _ _
      _ ≤ 1 + ‖x‖ * ‖Ring.inverse (1 - x)‖ := add_le_add h1 (norm_mul_le _ _)
  have h0 := norm_nonneg (Ring.inverse (1 - x))
  nlinarith

private theorem inverse_eq_of_mul_eq_one {R : Type*} [MonoidWithZero R] {c b : R} (hc : IsUnit c)
    (hcb : c * b = 1) : Ring.inverse c = b := by
  calc Ring.inverse c = Ring.inverse c * (c * b) := by rw [hcb, mul_one]
    _ = b := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hc, one_mul]

private theorem inverse_conj {R : Type*} [Ring R] (u v B : R) (huv : u * v = 1) (hvu : v * u = 1)
    (hB : IsUnit B) (hc : IsUnit (u * B * v)) :
    Ring.inverse (u * B * v) = u * Ring.inverse B * v := by
  apply inverse_eq_of_mul_eq_one hc
  have : u * B * v * (u * Ring.inverse B * v) = u * (B * (v * u) * Ring.inverse B) * v := by
    simp only [mul_assoc]
  rw [this, hvu, mul_one, Ring.mul_inverse_cancel _ hB, mul_one, huv]

private theorem iterProd_sub_pow_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : ℕ → E →L[ℝ] E) (T₀ : E →L[ℝ] E) (hS : ∀ n, IsCompactOperator ⇑(S n - T₀)) :
    ∀ m, IsCompactOperator ⇑(iterProd S m - T₀ ^ m)
  | 0 => by
    simp only [iterProd, pow_zero, sub_self]
    exact isCompactOperator_zero
  | m + 1 => by
    have hm := iterProd_sub_pow_compact S T₀ hS m
    have heq : iterProd S (m + 1) - T₀ ^ (m + 1) =
        (S m - T₀) * iterProd S m + T₀ * (iterProd S m - T₀ ^ m) := by
      rw [iterProd, pow_succ', sub_mul, mul_sub]
      abel
    rw [heq, FunLike.coe_add, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
    exact ((hS m).comp_clm _).add (hm.clm_comp _)

theorem monodromy_of (h1 : PieceOperatorStatement) (h2 : CompactPieceStatement)
    (h3 : ProfilePieceStatement) : MonodromyStatement := by
  intro X _ _ _ F ρ hc w P ho k hk hA
  have hP := ho.pos
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hPk : 0 < P / k := div_pos hP hkpos
  set μ := Real.exp (-(P / k)) with hμdef
  have hμ0 : 0 < μ := Real.exp_pos _
  have hμ1 : μ < 1 := by rw [hμdef]; exact Real.exp_lt_one_iff.mpr (by linarith)
  set L := MildFramework.stepLength P k with hLdef
  have hL : 0 < L := by simp only [hLdef, MildFramework.stepLength]; linarith
  have hL0 : 0 ≤ L := hL.le
  have hL1 : L ≤ 1 := by simp only [hLdef, MildFramework.stepLength]; linarith
  obtain ⟨hbil, -, hfree, -⟩ := h1 X F.toHeatBilinear L hL
  have hU : ∀ n, IsUnit (1 - F.stepOp w P k n) := fun n =>
    isUnit_one_sub_of_norm_lt_one (lt_of_le_of_lt (hA n) (by norm_num))
  have hone : ‖(1 : Piece X L →L[ℝ] Piece X L)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp)
  have hΓ : ∀ x (t : Icc (0 : ℝ) L), F.stepFree P k x t = F.G t x := fun x t => hfree x t
  have hE : ∀ f : Piece X L, F.stepEnd P k f = F.D μ (f ⟨L, hL0, le_rfl⟩) := by
    intro f
    simp only [MildFramework.stepEnd, ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [pieceEnd_apply hL0]
  set T₀ := (F.D μ).comp (F.G L) with hT₀
  refine ⟨hU, fun n => norm_inverse_one_sub_le hone (hU n) (hA n), ?_, ?_, ?_⟩
  · intro n
    set ρP := liftPiece L ρ
    set σP := liftPiece L ρ.symm
    have hpp : F.profilePiece w P k (n + k) = ρP (F.profilePiece w P k n) := by
      ext t
      rw [liftPiece_apply]
      exact (h3 X F ρ hc w P ho k hk n).2.2.2.1 t
    have hAk : F.stepOp w P k (n + k) = ρP * F.stepOp w P k n * σP := by
      ext g t
      simp only [MildFramework.stepOp, mul_apply_eq_comp,
        smul_apply, ContinuousMap.smul_apply]
      rw [liftPiece_apply, ContinuousMap.smul_apply, LinearIsometryEquiv.map_smul]
      congr 1
      have hcomm : ∀ (f : ℝ → X) (a b : ℝ), ρ (∫ s in a..b, f s) = ∫ s in a..b, ρ (f s) :=
        fun f a b => (ρ.toLinearIsometry.intervalIntegral_comp_comm f).symm
      rw [hbil, hbil, hcomm]
      congr 1
      funext s
      rw [hpp, extendPiece_liftPiece hL0, extendPiece_liftPiece hL0]
      show F.K _ _ _ = ρ (F.K _ _ _)
      rw [hc.comm_K, ρ.apply_symm_apply]
    have hc1 : 1 - F.stepOp w P k (n + k) = ρP * (1 - F.stepOp w P k n) * σP := by
      rw [hAk, mul_sub, sub_mul, mul_one, liftPiece_mul_symm]
    have hinv : Ring.inverse (1 - F.stepOp w P k (n + k)) =
        ρP * Ring.inverse (1 - F.stepOp w P k n) * σP := by
      rw [hc1]
      refine inverse_conj _ _ _ (liftPiece_mul_symm L ρ) (liftPiece_symm_mul L ρ) (hU n) ?_
      rw [← hc1]
      exact hU (n + k)
    have hΓσ : ∀ x, σP (F.stepFree P k x) = F.stepFree P k (ρ.symm x) := by
      intro x
      ext t
      rw [liftPiece_apply, hΓ, hΓ]
      apply ρ.injective
      rw [ρ.apply_symm_apply, hc.comm_G, ρ.apply_symm_apply]
    have hEρ : ∀ f, F.stepEnd P k (ρP f) = ρ (F.stepEnd P k f) := by
      intro f
      rw [hE, hE, liftPiece_apply, hc.comm_D]
    ext x
    simp only [stepMap, mul_apply_eq_comp, ContinuousLinearMap.coe_comp,
      Function.comp_apply, hinv, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [hΓσ, hEρ]
  · have hEΓ : (F.stepEnd P k).comp (F.stepFree P k) = T₀ := by
      ext x
      rw [ContinuousLinearMap.comp_apply, hE, hΓ, hT₀, ContinuousLinearMap.comp_apply]
    have hEA : ∀ n, IsCompactOperator ⇑((F.stepEnd P k).comp (F.stepOp w P k n)) := by
      intro n
      have key := ((h2 X F.toHeatBilinear L hL hL1 F.hasCompactKernel
        (F.profilePiece w P k n)).clm_comp (F.D μ)).smul (2 : ℝ)
      have hfun : ⇑((F.stepEnd P k).comp (F.stepOp w P k n)) = (2 : ℝ) • (⇑(F.D μ) ∘
          ⇑((pieceEnd L).comp (F.toHeatBilinear.pieceBil L (F.profilePiece w P k n)))) := by
        funext g
        simp only [MildFramework.stepEnd, MildFramework.stepOp, ContinuousLinearMap.comp_apply,
          Function.comp_apply, smul_apply, Pi.smul_apply, map_smul]
        rfl
      rw [hfun]
      exact key
    have hS : ∀ n, IsCompactOperator
        ⇑(stepMap (F.stepOp w P k) (F.stepFree P k) (F.stepEnd P k) n - T₀) := by
      intro n
      have hR : Ring.inverse (1 - F.stepOp w P k n) =
          1 + F.stepOp w P k n * Ring.inverse (1 - F.stepOp w P k n) := by
        have hy : (1 - F.stepOp w P k n) * Ring.inverse (1 - F.stepOp w P k n) = 1 :=
          Ring.mul_inverse_cancel _ (hU n)
        rw [sub_mul, one_mul] at hy
        exact sub_eq_iff_eq_add.mp hy
      have heq : stepMap (F.stepOp w P k) (F.stepFree P k) (F.stepEnd P k) n - T₀ =
          ((F.stepEnd P k).comp (F.stepOp w P k n)).comp
            ((Ring.inverse (1 - F.stepOp w P k n)).comp (F.stepFree P k)) := by
        rw [← hEΓ]
        ext x
        simp only [stepMap, sub_apply, ContinuousLinearMap.coe_comp,
          Function.comp_apply]
        conv_lhs => rw [hR]
        simp only [add_apply, one_apply_eq_self,
          mul_apply_eq_comp, map_add]
        abel
      rw [heq, ContinuousLinearMap.coe_comp]
      exact (hEA n).comp_clm _
    have hprod := iterProd_sub_pow_compact _ T₀ hS k
    rw [← mul_sub, ContinuousLinearMap.mul_def, ContinuousLinearMap.coe_comp]
    exact hprod.clm_comp _
  · have hD : ‖F.D μ‖ ≤ μ ^ (1 / 4 : ℝ) :=
      ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg hμ0.le _)
        (fun u => (F.D_norm μ hμ0 u).le)
    have hT : ‖T₀‖ ≤ μ ^ (1 / 4 : ℝ) := by
      calc ‖T₀‖ ≤ ‖F.D μ‖ * ‖F.G L‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ μ ^ (1 / 4 : ℝ) * 1 :=
          mul_le_mul hD (F.G_norm L hL0) (norm_nonneg _) (Real.rpow_nonneg hμ0.le _)
        _ = μ ^ (1 / 4 : ℝ) := mul_one _
    have hρs : ‖(ρ.symm.toContinuousLinearEquiv : X →L[ℝ] X)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp)
    have hval : (μ ^ (1 / 4 : ℝ)) ^ k = Real.exp (-(P / 4)) := by
      rw [hμdef, ← Real.exp_mul, ← Real.exp_nat_mul]
      congr 1
      field_simp
    calc ‖(ρ.symm.toContinuousLinearEquiv : X →L[ℝ] X) * T₀ ^ k‖
        ≤ ‖(ρ.symm.toContinuousLinearEquiv : X →L[ℝ] X)‖ * ‖T₀ ^ k‖ := norm_mul_le _ _
      _ ≤ 1 * ‖T₀‖ ^ k :=
          mul_le_mul hρs (norm_pow_le' _ hk) (norm_nonneg _) zero_le_one
      _ ≤ 1 * (μ ^ (1 / 4 : ℝ)) ^ k := by
          gcongr
      _ = Real.exp (-(P / 4)) := by rw [one_mul, hval]

end Breakdown
