import TorusEuler.TerminalMixedDerivatives
import TorusEuler.TerminalTimeGraphCalculus
import Mathlib.Data.Nat.Choose.Sum

/-! The differentiated Euler advection and its first spatial derivative. -/

open Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

/-- Eulerian advection, with the differentiated vector field first. -/
abbrev slabAdvection (v w : Velocity) : Velocity := fun t x => fderiv ℝ (v t) x (w t x)

theorem smooth_slabAdvection {T : ℝ} {v w : Velocity} (hT : 0 < T)
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hw : ContDiffOn ℝ ∞ (Function.uncurry w) (Icc 0 T ×ˢ (univ : Set Vec3))) :
    ContDiffOn ℝ ∞ (Function.uncurry (slabAdvection v w)) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
  (terminal_contDiffOn_spaceDerivative hT hv).clm_apply hw

theorem slabAdvection_periodic {v w : Vec3 → Vec3} (hv : Differentiable ℝ v)
    (hpv : SpatiallyPeriodic v) (hpw : SpatiallyPeriodic w) :
    SpatiallyPeriodic (fun x => fderiv ℝ v x (w x)) := by
  intro k x
  change (fderiv ℝ v (x + latticeVector k)) (w (x + latticeVector k)) = (fderiv ℝ v x) (w x)
  rw [hpv.fderiv hv k x, hpw k x]

/-- The exact binomial rule for differentiation of advection at a fixed point. -/
theorem slabTimeJet_slabAdvection {T : ℝ} {v w : Velocity} (hT : 0 < T)
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hw : ContDiffOn ℝ ∞ (Function.uncurry w) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (q : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) :
    slabTimeJet 0 T q (slabAdvection v w) t x =
      ∑ i ∈ Finset.range (q + 1), q.choose i •
        slabAdvection (slabTimeJet 0 T i v) (slabTimeJet 0 T (q - i) w) t x := by
  let B : (Vec3 →L[ℝ] Vec3) →L[ℝ] Vec3 →L[ℝ] Vec3 :=
    (ContinuousLinearMap.apply ℝ Vec3).flip
  have hGrad : ContDiffOn ℝ ∞ (fun r => fderiv ℝ (v r) x) (Icc 0 T) :=
    terminal_contDiffOn_timeSlice (f := fun r y => fderiv ℝ (v r) y)
      (terminal_contDiffOn_spaceDerivative hT hv) x
  have hW := terminal_contDiffOn_timeSlice hw x
  have hh := iteratedDerivWithin_bilinear B (uniqueDiffOn_Icc hT) ht hGrad hW q
  change slabTimeJet 0 T q (slabAdvection v w) t x = ∑ i ∈ Finset.range (q + 1),
    q.choose i • (slabTimeJet 0 T i (fun r y => fderiv ℝ (v r) y) t x)
      (slabTimeJet 0 T (q - i) w t x) at hh
  simpa only [terminal_iteratedDerivWithin_fderiv_comm hT hv _ ht, slabAdvection] using hh

/-- One spatial derivative of an advective term costs either one derivative
on each factor or a second derivative of the differentiated factor. -/
theorem norm_fderiv_slabAdvection_le {v w : Vec3 → Vec3}
    (hv : ContDiff ℝ 2 v) (hw : Differentiable ℝ w) (x : Vec3) :
    ‖fderiv ℝ (fun y => fderiv ℝ v y (w y)) x‖ ≤
      ‖fderiv ℝ v x‖ * ‖fderiv ℝ w x‖ + ‖iteratedFDeriv ℝ 2 v x‖ * ‖w x‖ := by
  have hd := ((hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt
  let M := fderiv ℝ v x
  let W := fderiv ℝ w x
  let G := fderiv ℝ (fderiv ℝ v) x
  have hG : ‖G‖ = ‖iteratedFDeriv ℝ 2 v x‖ := by
    simpa only [G, norm_iteratedFDeriv_one] using
      (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := v) (x := x) (n := 1))
  rw [(hd.clm_apply (hw x).hasFDerivAt).fderiv, ← hG]
  change ‖M.comp W + G.flip (w x)‖ ≤ ‖M‖ * ‖W‖ + ‖G‖ * ‖w x‖
  exact (norm_add_le _ _).trans (add_le_add (M.opNorm_comp_le W)
    (by simpa only [ContinuousLinearMap.opNorm_flip] using G.flip.le_opNorm (w x)))

private theorem sum_choose_mul_real (q : ℕ) (A : ℝ) :
    ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * A = 2 ^ q * A := by
  rw [← Finset.sum_mul]
  rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]

/-- A time derivative of the self-advection needs only time jets through the
same order and spatial jets through order two. -/
theorem norm_slabTimeJet_slabAdvection_and_fderiv_le {T : ℝ} {u : Velocity} (hT : 0 < T)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (q : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) {A B C : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hU : ∀ i ≤ q, ∀ x, ‖slabTimeJet 0 T i u t x‖ ≤ A)
    (hD : ∀ i ≤ q, ∀ x, ‖fderiv ℝ (slabTimeJet 0 T i u t) x‖ ≤ B)
    (hD₂ : ∀ i ≤ q, ∀ x, ‖iteratedFDeriv ℝ 2 (slabTimeJet 0 T i u t) x‖ ≤ C)
    (x : Vec3) :
    ‖slabTimeJet 0 T q (slabAdvection u u) t x‖ ≤ 2 ^ q * (B * A) ∧
    ‖fderiv ℝ (slabTimeJet 0 T q (slabAdvection u u) t) x‖ ≤ 2 ^ q * (B * B + C * A) := by
  let ujet (i : ℕ) := slabTimeJet 0 T i u t
  let term (i : ℕ) (y : Vec3) := fderiv ℝ (ujet i) y (ujet (q - i) y)
  let sum (y : Vec3) := ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) • term i y
  have hSum : slabTimeJet 0 T q (slabAdvection u u) t = sum := by
    funext y
    simp only [sum, term, ujet, Nat.cast_smul_eq_nsmul]
    exact slabTimeJet_slabAdvection hT hu hu q ht y
  have hTermSmooth (i : ℕ) : ContDiff ℝ ∞ (term i) := by
    have hi := slabTimeJet_slice_smooth hT hu i ht
    have hj := slabTimeJet_slice_smooth hT hu (q - i) ht
    exact (hi.fderiv_right (m := ∞) (by simp)).clm_apply hj
  have hTerm (i : ℕ) (hi : i ∈ Finset.range (q + 1)) : ‖term i x‖ ≤ B * A := by
    have hiq : i ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact ((fderiv ℝ (ujet i) x).le_opNorm _).trans
      (mul_le_mul (hD i hiq x) (hU (q - i) (Nat.sub_le _ _) x) (norm_nonneg _) hB)
  have hTermD (i : ℕ) (hi : i ∈ Finset.range (q + 1)) :
      ‖fderiv ℝ (term i) x‖ ≤ B * B + C * A := by
    have hiq : i ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hiS := slabTimeJet_slice_smooth hT hu i ht
    have hjS := slabTimeJet_slice_smooth hT hu (q - i) ht
    refine (norm_fderiv_slabAdvection_le (hiS.of_le (by simp)) (hjS.differentiable (by simp)) x).trans ?_
    exact add_le_add
      (mul_le_mul (hD i hiq x) (hD (q - i) (Nat.sub_le _ _) x) (norm_nonneg _) hB)
      (mul_le_mul (hD₂ i hiq x) (hU (q - i) (Nat.sub_le _ _) x) (norm_nonneg _) hC)
  constructor
  · rw [hSum]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i hi => ?_).trans_eq (sum_choose_mul_real q _)
    rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hTerm i hi) (Nat.cast_nonneg _)
  · rw [hSum]
    have hd (i : ℕ) (_ : i ∈ Finset.range (q + 1)) :
        DifferentiableAt ℝ (fun y => (q.choose i : ℝ) • term i y) x := by
      change DifferentiableAt ℝ ((q.choose i : ℝ) • term i) x
      exact ((hTermSmooth i).differentiable (by simp) x).const_smul _
    change ‖fderiv ℝ (fun y => ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) • term i y) x‖ ≤ _
    rw [fderiv_fun_sum hd]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i hi => ?_).trans_eq (sum_choose_mul_real q _)
    change ‖fderiv ℝ ((q.choose i : ℝ) • term i) x‖ ≤ _
    rw [fderiv_const_smul ((hTermSmooth i).differentiable (by simp) x),
      norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hTermD i hi) (Nat.cast_nonneg _)

end

end TorusEuler
