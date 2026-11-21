import Breakdown.Transfer.StatementsFrame
import Breakdown.Transfer.StatementsLocal
import Breakdown.Transfer.StatementsAbstract

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

noncomputable section

namespace Breakdown

namespace StepDataInternal

theorem exists_step_count (P CK M t₀ : ℝ) (ht₀ : 0 < t₀) :
    ∃ k : ℕ, 0 < k ∧ 1 - Real.exp (-(P / k)) < t₀ ∧
      2 * (4 * CK * (1 - Real.exp (-(P / k))) ^ (1 / 4 : ℝ) * (Real.exp (P / k / 4) * M)) < 1 / 4 := by
  set g : ℝ → ℝ := fun x => 2 * (4 * CK * (1 - Real.exp (-x)) ^ (1 / 4 : ℝ) * (Real.exp (x / 4) * M))
    with hg
  set h : ℝ → ℝ := fun x => 1 - Real.exp (-x) with hh
  have hgc : Continuous g := by
    have h1 : Continuous fun x : ℝ => (1 - Real.exp (-x)) ^ (1 / 4 : ℝ) :=
      (Real.continuous_rpow_const (by norm_num)).comp
        (continuous_const.sub (Real.continuous_exp.comp continuous_neg))
    rw [hg]
    exact continuous_const.mul ((continuous_const.mul h1).mul
      ((Real.continuous_exp.comp (continuous_id.div_const 4)).mul continuous_const))
  have hhc : Continuous h := continuous_const.sub (Real.continuous_exp.comp continuous_neg)
  have hg0 : g 0 = 0 := by
    simp [hg]
  have hh0 : h 0 = 0 := by simp [hh]
  have ht : Tendsto (fun k : ℕ => P / (k : ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat P
  have tg : Tendsto (fun k : ℕ => g (P / k)) atTop (𝓝 0) := by
    have := (hgc.tendsto 0).comp ht
    rw [hg0] at this
    exact this
  have th : Tendsto (fun k : ℕ => h (P / k)) atTop (𝓝 0) := by
    have := (hhc.tendsto 0).comp ht
    rw [hh0] at this
    exact this
  have e1 := tg.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4)
  have e2 := th.eventually_lt_const ht₀
  obtain ⟨k, hk1, hk2, hk3⟩ := ((eventually_ge_atTop 1).and (e2.and e1)).exists
  exact ⟨k, hk1, hk2, hk3⟩

end StepDataInternal

open StepDataInternal in
theorem stepData_of (h1 : MonodromyStatement) (h2 : ProfilePieceStatement)
    (h3 : OrbitBoundStatement) (h4 : PieceOperatorStatement) (h5 : PeriodicInverseStatement)
    (h6 : SectionStatement) (h7 : DichotomyHolds) : StepDataStatement := by
  intro X _ _ _ F ρ hcomm w P horb C' hdense t₀ ht₀
  obtain ⟨M, hM⟩ := h3 X F ρ w P horb
  have hP : 0 < P := horb.pos
  obtain ⟨k, hk, hLt, hsmall⟩ := exists_step_count P F.CK M t₀ ht₀
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hPk : 0 < P / k := div_pos hP hkpos
  have hLpos : 0 < MildFramework.stepLength P k := by
    show 0 < 1 - Real.exp (-(P / k))
    have : Real.exp (-(P / k)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hL1 : MildFramework.stepLength P k ≤ 1 := by
    show 1 - Real.exp (-(P / k)) ≤ 1
    have := Real.exp_pos (-(P / k))
    linarith
  have hstep : ∀ n, ‖F.stepOp w P k n‖ ≤ 1 / 4 := by
    intro n
    have hB : ‖F.toHeatBilinear.pieceBil (MildFramework.stepLength P k)‖ ≤
        4 * F.CK * (MildFramework.stepLength P k) ^ (1 / 4 : ℝ) :=
      (h4 X F.toHeatBilinear _ hLpos).2.1 hL1
    have hpp : ‖F.profilePiece w P k n‖ ≤ Real.exp (P / k / 4) * M :=
      ((h2 X F ρ hcomm w P horb k hk n).2.2.2.2) M hM
    have hle : ‖F.stepOp w P k n‖ ≤
        2 * (‖F.toHeatBilinear.pieceBil (MildFramework.stepLength P k)‖ *
          ‖F.profilePiece w P k n‖) := by
      unfold MildFramework.stepOp
      rw [norm_smul]
      have := ContinuousLinearMap.le_opNorm
        (F.toHeatBilinear.pieceBil (MildFramework.stepLength P k)) (F.profilePiece w P k n)
      have h2n : ‖(2 : ℝ)‖ = 2 := by norm_num
      rw [h2n]
      linarith
    have hprod : ‖F.toHeatBilinear.pieceBil (MildFramework.stepLength P k)‖ *
          ‖F.profilePiece w P k n‖ ≤
        (4 * F.CK * (MildFramework.stepLength P k) ^ (1 / 4 : ℝ)) *
          (Real.exp (P / k / 4) * M) :=
      mul_le_mul hB hpp (norm_nonneg _) ((norm_nonneg _).trans hB)
    have : 2 * ((4 * F.CK * (MildFramework.stepLength P k) ^ (1 / 4 : ℝ)) *
          (Real.exp (P / k / 4) * M)) < 1 / 4 := by
      have e : 2 * ((4 * F.CK * (MildFramework.stepLength P k) ^ (1 / 4 : ℝ)) *
          (Real.exp (P / k / 4) * M)) =
          2 * (4 * F.CK * (1 - Real.exp (-(P / k))) ^ (1 / 4 : ℝ) * (Real.exp (P / k / 4) * M)) :=
        rfl
      rw [e]
      exact hsmall
    linarith
  obtain ⟨hunit, hinv, hper, hcpt, hT0⟩ := h1 X F ρ hcomm w P horb k hk hstep
  set Mono : X →L[ℝ] X := (ρ.symm.toContinuousLinearEquiv : X →L[ℝ] X) *
    iterProd (stepMap (F.stepOp w P k) (F.stepFree P k) (F.stepEnd P k)) k with hMono
  set T₀ : X →L[ℝ] X := (ρ.symm.toContinuousLinearEquiv : X →L[ℝ] X) *
    ((F.D (Real.exp (-(P / k)))).comp (F.G (MildFramework.stepLength P k))) ^ k with hT₀
  have hb0 : 0 ≤ Real.exp (-(P / 4)) := (Real.exp_pos _).le
  have hb1 : Real.exp (-(P / 4)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  obtain ⟨r₁, r₂, K, Pu, hbr₁, hr₁₂, hr₂1, hK, hPP, hPc, hfd, hdec, hgrow, hsurj⟩ :=
    h7 X T₀ (Mono - T₀) (Real.exp (-(P / 4))) (Real.exp (-(P / 4))) 1 hb0 le_rfl hb1 hT0 hcpt
  have hsum : T₀ + (Mono - T₀) = Mono := add_sub_cancel T₀ Mono
  rw [hsum] at hPc hdec hgrow hsurj
  obtain ⟨J, hPJ, hJC⟩ := h6 X Pu C' hPP hfd hdense
  set Θ : ℝ := (r₁ + r₂) / 2 with hΘ
  have hr₁pos : 0 < r₁ := (Real.exp_pos _).trans hbr₁
  have hΘpos : 0 < Θ := by rw [hΘ]; linarith
  have hr₁Θ : r₁ < Θ := by rw [hΘ]; linarith
  have hΘr₂ : Θ < r₂ := by rw [hΘ]; linarith
  set θ : ℝ := Θ ^ ((k : ℝ)⁻¹) with hθ
  have hθpos : 0 < θ := Real.rpow_pos_of_pos hΘpos _
  have hk0 : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
  have hθk : θ ^ k = Θ := Real.rpow_inv_natCast_pow hΘpos.le hk0
  have hθ1 : θ < 1 := by
    have : θ ^ k < 1 := by rw [hθk]; linarith
    exact (pow_lt_one_iff_of_nonneg hθpos.le hk0).mp this
  have hbθ : Real.exp (-(P / k)) ^ (1 / 4 : ℝ) < θ := by
    have ha : Real.exp (-(P / k)) ^ (1 / 4 : ℝ) = Real.exp (-(P / k) * (1 / 4)) :=
      (Real.exp_mul _ _).symm
    have hak : (Real.exp (-(P / k)) ^ (1 / 4 : ℝ)) ^ k = Real.exp (-(P / 4)) := by
      rw [ha, ← Real.exp_nat_mul]
      congr 1
      field_simp
    apply lt_of_pow_lt_pow_left₀ k hθpos.le
    rw [hak, hθk]
    linarith
  obtain ⟨R, hR1, hR2⟩ := h5 X (Piece X (MildFramework.stepLength P k)) k ρ (F.stepOp w P k)
    (F.stepFree P k) (F.stepEnd P k) J Pu K r₁ r₂ θ (4 / 3) hk hθpos hunit hinv hper hPP hPc
    hr₁pos.le (by rw [hθk]; exact hr₁Θ) (by rw [hθk]; exact hΘr₂) hdec hgrow hsurj hPJ
  exact ⟨k, θ, hk, hLt.le, hbθ, hθ1, hstep, LinearMap.range (Pu : X →ₗ[ℝ] X), J, R, hfd, hJC,
    hR1, hR2⟩

end Breakdown
