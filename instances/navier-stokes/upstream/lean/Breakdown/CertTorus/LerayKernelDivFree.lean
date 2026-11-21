import Breakdown.CertTorus.KernelStatements

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.FarField.Internal.LerayDivFree

open Breakdown Breakdown.FarField

def kd (a b : Fin 3) : ℝ := if a = b then 1 else 0

def secondPartial (j k : Fin 3) (ρ : ℝ) (x : Space) : ℝ :=
  (x j * x k / (4 * ρ ^ 2) - kd j k / (2 * ρ)) * heatKernel ρ x

def secondPartialTime (j k : Fin 3) (ρ : ℝ) (x : Space) : ℝ :=
  (-(x j * x k) / (2 * ρ ^ 3) + kd j k / (2 * ρ ^ 2)) * heatKernel ρ x +
    (x j * x k / (4 * ρ ^ 2) - kd j k / (2 * ρ)) *
      ((-3 / (2 * ρ) + ‖x‖ ^ 2 / (4 * ρ ^ 2)) * heatKernel ρ x)

theorem heatKernel_hasDerivAt_time (x : Space) {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (fun r => heatKernel r x)
      ((-3 / (2 * ρ) + ‖x‖ ^ 2 / (4 * ρ ^ 2)) * heatKernel ρ x) ρ := by
  have hpos : 0 < 4 * π * ρ := by positivity
  have h1 : HasDerivAt (fun r : ℝ => 4 * π * r) (4 * π) ρ := by
    simpa using (hasDerivAt_id ρ).const_mul (4 * π)
  have h2 := h1.rpow_const (p := -(3 / 2 : ℝ)) (Or.inl hpos.ne')
  have h3 : HasDerivAt (fun r : ℝ => -(‖x‖ ^ 2) / (4 * r)) (‖x‖ ^ 2 / (4 * ρ ^ 2)) ρ := by
    have h := (((hasDerivAt_id ρ).const_mul 4).inv (by simp; positivity)).const_mul (-(‖x‖ ^ 2))
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)).congr_deriv ?_
    · simp [div_eq_mul_inv]
    · simp only [id]; field_simp
  have h4 := h2.mul h3.exp
  refine (h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)).congr_deriv ?_
  · simp [heatKernel]
  · rw [Real.rpow_sub_one hpos.ne']
    simp only [heatKernel]
    field_simp

theorem secondPartial_hasDerivAt (j k : Fin 3) (x : Space) {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (fun r => secondPartial j k r x) (secondPartialTime j k ρ x) ρ := by
  have hc : HasDerivAt (fun r : ℝ => x j * x k / (4 * r ^ 2) - kd j k / (2 * r))
      (-(x j * x k) / (2 * ρ ^ 3) + kd j k / (2 * ρ ^ 2)) ρ := by
    have ha := (((hasDerivAt_pow 2 ρ).const_mul 4).inv (by positivity)).const_mul (x j * x k)
    have hb := (((hasDerivAt_id ρ).const_mul 2).inv (by simp; positivity)).const_mul (kd j k)
    refine ((ha.sub hb).congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)).congr_deriv ?_
    · simp [div_eq_mul_inv]
    · simp only [id]; norm_num; field_simp; ring
  exact hc.mul (heatKernel_hasDerivAt_time x hρ)

theorem heatKernel_nonneg {ρ : ℝ} (hρ : 0 < ρ) (x : Space) : 0 ≤ heatKernel ρ x := by
  unfold heatKernel
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le


theorem secondPartial_tendsto (j k : Fin 3) (x : Space) :
    Tendsto (fun r => secondPartial j k r x) atTop (𝓝 0) := by
  have hc : Tendsto (fun r : ℝ => x j * x k / (4 * r ^ 2) - kd j k / (2 * r)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => 4 * r ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).const_mul_atTop (by norm_num)
    have h2 : Tendsto (fun r : ℝ => 2 * r) atTop atTop := tendsto_id.const_mul_atTop (by norm_num)
    simpa using (tendsto_const_nhds.div_atTop h1).sub (tendsto_const_nhds.div_atTop h2)
  have hG : Tendsto (fun r => heatKernel r x) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => (4 * π * r) ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp (tendsto_id.const_mul_atTop (by positivity))
    have h2 : Tendsto (fun r : ℝ => rexp (-(‖x‖ ^ 2) / (4 * r))) atTop (𝓝 1) := by
      have : Tendsto (fun r : ℝ => -(‖x‖ ^ 2) / (4 * r)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by norm_num))
      have h3 := (Real.continuous_exp.tendsto 0).comp this
      simpa [Function.comp_def] using h3
    simpa [heatKernel] using h1.mul h2
  simpa [secondPartial] using hc.mul hG

theorem heatKernel_le {τ ρ : ℝ} (hτ : 0 < τ) (hρ : τ ≤ ρ) (y : Space) :
    heatKernel ρ y ≤ (4 * π * τ) ^ (-(3 / 2 : ℝ)) := by
  unfold heatKernel
  have he : rexp (-(‖y‖ ^ 2) / (4 * ρ)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div]
    have h4 : 0 < 4 * ρ := by linarith
    exact neg_nonpos.mpr (div_nonneg (sq_nonneg _) h4.le)
  have hr : (4 * π * ρ) ^ (-(3 / 2 : ℝ)) ≤ (4 * π * τ) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos (by positivity) hτ) (by gcongr) (by norm_num)
  calc (4 * π * ρ) ^ (-(3 / 2 : ℝ)) * rexp (-(‖y‖ ^ 2) / (4 * ρ))
      ≤ (4 * π * ρ) ^ (-(3 / 2 : ℝ)) * 1 := by
        gcongr
        exact Real.rpow_nonneg (mul_pos (by positivity) (hτ.trans_le hρ)).le _
    _ ≤ (4 * π * τ) ^ (-(3 / 2 : ℝ)) := by rw [mul_one]; exact hr

def gammaLine (ρ : ℝ) (y e : Space) : ℝ :=
  ∑ m : Fin 3, (-(y m / (2 * ρ)) * heatKernel ρ y) * e m

def thirdLine (i j k : Fin 3) (ρ : ℝ) (y e : Space) : ℝ :=
  ((if j = k then e i else 0) + (if i = k then e j else 0) + (if i = j then e k else 0)) /
      (4 * ρ ^ 2) * heatKernel ρ y
    + ((if j = k then y i else 0) + (if i = k then y j else 0) + (if i = j then y k else 0)) /
      (4 * ρ ^ 2) * gammaLine ρ y e
    - ((e i * y j + y i * e j) * y k + y i * y j * e k) / (8 * ρ ^ 3) * heatKernel ρ y
    - y i * y j * y k / (8 * ρ ^ 3) * gammaLine ρ y e

theorem coord_line (x e : Space) (m : Fin 3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (x + s • e) m) (e m) t := by
  have h := ((hasDerivAt_id t).mul_const (e m)).const_add (x m)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)).congr_deriv ?_ <;> simp

theorem ite_line (p : Prop) [Decidable p] {f : ℝ → ℝ} {f' t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => if p then f s else 0) (if p then f' else 0) t := by
  by_cases hp : p
  · simpa [hp] using h
  · simpa [hp] using hasDerivAt_const t (0 : ℝ)

theorem heatKernel_line (hHP : HeatKernelPartials) {ρ : ℝ} (hρ : 0 < ρ) (x e : Space) (t : ℝ) :
    HasDerivAt (fun s : ℝ => heatKernel ρ (x + s • e)) (gammaLine ρ (x + t • e) e) t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add x
  have h := (hHP ρ hρ (x + t • e)).1.comp_hasDerivAt t hl
  refine h.congr_deriv ?_
  simp [gammaLine]

theorem third_line (hHP : HeatKernelPartials) {ρ : ℝ} (hρ : 0 < ρ) (i j k : Fin 3) (x e : Space)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => heatKernelThird i j k ρ (x + s • e)) (thirdLine i j k ρ (x + t • e) e) t := by
  have hS := ((ite_line (j = k) (coord_line x e i t)).add (ite_line (i = k) (coord_line x e j t))).add
    (ite_line (i = j) (coord_line x e k t))
  have hP := ((coord_line x e i t).mul (coord_line x e j t)).mul (coord_line x e k t)
  have hG := heatKernel_line hHP hρ x e t
  have h := ((hS.div_const (4 * ρ ^ 2)).mul hG).sub ((hP.div_const (8 * ρ ^ 3)).mul hG)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)).congr_deriv ?_
  · rfl
  · simp only [thirdLine, Pi.add_apply, Pi.mul_apply]; ring

def heatSup (τ : ℝ) : ℝ := (4 * π * τ) ^ (-(3 / 2 : ℝ))

def lineSup (τ R : ℝ) : ℝ := 3 * (R / (2 * τ) * heatSup τ)

theorem ite_abs_le (p : Prop) [Decidable p] {a B : ℝ} (h : |a| ≤ B) (hB : 0 ≤ B) :
    |if p then a else 0| ≤ B := by
  split_ifs <;> simp [h, hB]

theorem abs_mul_le' {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

theorem abs_add_le' {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a + b| ≤ A + B := by
  have h1 := abs_le.mp ha; have h2 := abs_le.mp hb
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_sub_le' {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a - b| ≤ A + B := by
  have h1 := abs_le.mp ha; have h2 := abs_le.mp hb
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_div_le' {a A c : ℝ} (ha : |a| ≤ A) (hc : 0 < c) : |a / c| ≤ A / c := by
  rw [abs_div, abs_of_pos hc]; exact div_le_div_of_nonneg_right ha hc.le

theorem cube_le {τ ρ A : ℝ} (hτ : 0 < τ) (hρ : τ ≤ ρ) (hA : 0 ≤ A) :
    A / (8 * ρ ^ 3) ≤ A / (8 * τ) / ρ ^ 2 := by
  have hρ0 : 0 < ρ := hτ.trans_le hρ
  rw [div_div]
  apply div_le_div_of_nonneg_left hA (by positivity)
  have : τ * ρ ^ 2 ≤ ρ * ρ ^ 2 := mul_le_mul_of_nonneg_right hρ (sq_nonneg _)
  nlinarith

theorem gammaLine_bound {τ ρ R : ℝ} (hτ : 0 < τ) (hρ : τ ≤ ρ) {y e : Space}
    (hy : ∀ m, |y m| ≤ R) (he : ∀ m, |e m| ≤ 1) :
    |gammaLine ρ y e| ≤ lineSup τ R := by
  have hρ0 : 0 < ρ := hτ.trans_le hρ
  have hR : 0 ≤ R := (abs_nonneg _).trans (hy 0)
  have hG0 := heatKernel_nonneg hρ0 y
  have hG1 := heatKernel_le hτ hρ y
  have term : ∀ m, |(-(y m / (2 * ρ)) * heatKernel ρ y) * e m| ≤ R / (2 * τ) * heatSup τ := by
    intro m
    have h1 : |-(y m / (2 * ρ))| ≤ R / (2 * τ) := by
      rw [abs_neg]
      calc |y m / (2 * ρ)| ≤ R / (2 * ρ) := abs_div_le' (hy m) (by linarith)
        _ ≤ R / (2 * τ) := div_le_div_of_nonneg_left hR (by linarith) (by linarith)
    have h2 : |heatKernel ρ y| ≤ heatSup τ := by rw [abs_of_nonneg hG0]; exact hG1
    simpa using abs_mul_le' (abs_mul_le' h1 h2) (he m)
  unfold gammaLine lineSup
  rw [Fin.sum_univ_three]
  have := abs_add_le' (abs_add_le' (term 0) (term 1)) (term 2)
  linarith

theorem thirdLine_bound {τ ρ R : ℝ} (hτ : 0 < τ) (hρ : τ ≤ ρ) (i j k : Fin 3) {y e : Space}
    (hy : ∀ m, |y m| ≤ R) (he : ∀ m, |e m| ≤ 1) :
    |thirdLine i j k ρ y e| ≤
      (3 * heatSup τ / 4 + 3 * R * lineSup τ R / 4 + 3 * R ^ 2 * heatSup τ / (8 * τ) +
        R ^ 3 * lineSup τ R / (8 * τ)) / ρ ^ 2 := by
  have hρ0 : 0 < ρ := hτ.trans_le hρ
  have hR : 0 ≤ R := (abs_nonneg _).trans (hy 0)
  have hG0 := heatKernel_nonneg hρ0 y
  have hG : |heatKernel ρ y| ≤ heatSup τ := by rw [abs_of_nonneg hG0]; exact heatKernel_le hτ hρ y
  have hS0 : 0 ≤ heatSup τ := (abs_nonneg _).trans hG
  have hL := gammaLine_bound hτ hρ hy he
  have hL0 : 0 ≤ lineSup τ R := (abs_nonneg _).trans hL
  have hSe : |(if j = k then e i else 0) + (if i = k then e j else 0) + (if i = j then e k else 0)| ≤
      1 + 1 + 1 :=
    abs_add_le' (abs_add_le' (ite_abs_le _ (he i) zero_le_one) (ite_abs_le _ (he j) zero_le_one))
      (ite_abs_le _ (he k) zero_le_one)
  have hSy : |(if j = k then y i else 0) + (if i = k then y j else 0) + (if i = j then y k else 0)| ≤
      R + R + R :=
    abs_add_le' (abs_add_le' (ite_abs_le _ (hy i) hR) (ite_abs_le _ (hy j) hR)) (ite_abs_le _ (hy k) hR)
  have hPe : |(e i * y j + y i * e j) * y k + y i * y j * e k| ≤ (1 * R + R * 1) * R + R * R * 1 :=
    abs_add_le' (abs_mul_le' (abs_add_le' (abs_mul_le' (he i) (hy j)) (abs_mul_le' (hy i) (he j))) (hy k))
      (abs_mul_le' (abs_mul_le' (hy i) (hy j)) (he k))
  have hPy : |y i * y j * y k| ≤ R * R * R := abs_mul_le' (abs_mul_le' (hy i) (hy j)) (hy k)
  have h4 : (0 : ℝ) < 4 * ρ ^ 2 := by positivity
  have h8 : (0 : ℝ) < 8 * ρ ^ 3 := by positivity
  have t1 := abs_mul_le' (abs_div_le' hSe h4) hG
  have t2 := abs_mul_le' (abs_div_le' hSy h4) hL
  have t3 := abs_mul_le' (abs_div_le' hPe h8) hG
  have t4 := abs_mul_le' (abs_div_le' hPy h8) hL
  have c3 := cube_le hτ hρ (by positivity : (0 : ℝ) ≤ (1 * R + R * 1) * R + R * R * 1)
  have c4 := cube_le hτ hρ (by positivity : (0 : ℝ) ≤ R * R * R)
  have t3' : |((e i * y j + y i * e j) * y k + y i * y j * e k) / (8 * ρ ^ 3) * heatKernel ρ y| ≤
      ((1 * R + R * 1) * R + R * R * 1) / (8 * τ) / ρ ^ 2 * heatSup τ :=
    t3.trans (mul_le_mul_of_nonneg_right c3 hS0)
  have t4' : |y i * y j * y k / (8 * ρ ^ 3) * gammaLine ρ y e| ≤
      R * R * R / (8 * τ) / ρ ^ 2 * lineSup τ R :=
    t4.trans (mul_le_mul_of_nonneg_right c4 hL0)
  have hsum := abs_sub_le' (abs_sub_le' (abs_add_le' t1 t2) t3') t4'
  unfold thirdLine
  refine hsum.trans (le_of_eq ?_)
  field_simp
  ring

theorem third_bound {τ ρ R : ℝ} (hτ : 0 < τ) (hρ : τ ≤ ρ) (i j k : Fin 3) {y : Space}
    (hy : ∀ m, |y m| ≤ R) :
    |heatKernelThird i j k ρ y| ≤ (3 * R * heatSup τ / 4 + R ^ 3 * heatSup τ / (8 * τ)) / ρ ^ 2 := by
  have hρ0 : 0 < ρ := hτ.trans_le hρ
  have hR : 0 ≤ R := (abs_nonneg _).trans (hy 0)
  have hG0 := heatKernel_nonneg hρ0 y
  have hG : |heatKernel ρ y| ≤ heatSup τ := by rw [abs_of_nonneg hG0]; exact heatKernel_le hτ hρ y
  have hS0 : 0 ≤ heatSup τ := (abs_nonneg _).trans hG
  have hSy : |(if j = k then y i else 0) + (if i = k then y j else 0) + (if i = j then y k else 0)| ≤
      R + R + R :=
    abs_add_le' (abs_add_le' (ite_abs_le _ (hy i) hR) (ite_abs_le _ (hy j) hR)) (ite_abs_le _ (hy k) hR)
  have hPy : |y i * y j * y k| ≤ R * R * R := abs_mul_le' (abs_mul_le' (hy i) (hy j)) (hy k)
  have h4 : (0 : ℝ) < 4 * ρ ^ 2 := by positivity
  have h8 : (0 : ℝ) < 8 * ρ ^ 3 := by positivity
  have t1 := abs_mul_le' (abs_div_le' hSy h4) hG
  have t2 := abs_mul_le' (abs_div_le' hPy h8) hG
  have c2 := cube_le hτ hρ (by positivity : (0 : ℝ) ≤ R * R * R)
  have t2' : |y i * y j * y k / (8 * ρ ^ 3) * heatKernel ρ y| ≤ R * R * R / (8 * τ) / ρ ^ 2 * heatSup τ :=
    t2.trans (mul_le_mul_of_nonneg_right c2 hS0)
  have hsum := abs_sub_le' t1 t2'
  unfold heatKernelThird
  refine hsum.trans (le_of_eq ?_)
  field_simp
  ring

theorem sum_thirdLine (j k : Fin 3) (ρ : ℝ) (hρ : 0 < ρ) (x : Space) :
    ∑ i : Fin 3, thirdLine i j k ρ x (unitVector i) = secondPartialTime j k ρ x := by
  have hn : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]; simp
  simp only [thirdLine, gammaLine, secondPartialTime, kd, Fin.sum_univ_three, unitVector,
    PiLp.single_apply, hn]
  fin_cases j <;> fin_cases k <;> simp <;> field_simp <;> ring

def aLine (i j k : Fin 3) (τ : ℝ) (y e : Space) : ℝ :=
  if i = j then -(e k / (2 * τ)) * heatKernel τ y + -(y k / (2 * τ)) * gammaLine τ y e else 0

theorem first_line (hHP : HeatKernelPartials) {τ : ℝ} (hτ : 0 < τ) (i j k : Fin 3) (x e : Space)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => if i = j then -((x + s • e) k / (2 * τ)) * heatKernel τ (x + s • e) else 0)
      (aLine i j k τ (x + t • e) e) t := by
  have h := ite_line (i = j) (((coord_line x e k t).div_const (2 * τ)).neg.mul (heatKernel_line hHP hτ x e t))
  refine h.congr_deriv ?_
  simp only [aLine, Pi.neg_apply]

theorem sum_aLine (j k : Fin 3) (τ : ℝ) (hτ : 0 < τ) (x : Space) :
    ∑ i : Fin 3, aLine i j k τ x (unitVector i) = secondPartial j k τ x := by
  simp only [aLine, gammaLine, secondPartial, kd, Fin.sum_univ_three, unitVector,
    PiLp.single_apply]
  fin_cases j <;> fin_cases k <;> simp <;> field_simp <;> ring

theorem third_meas (i j k : Fin 3) (y : Space) : Measurable (fun ρ => heatKernelThird i j k ρ y) := by
  unfold heatKernelThird heatKernel; fun_prop

theorem thirdLine_meas (i j k : Fin 3) (y e : Space) : Measurable (fun ρ => thirdLine i j k ρ y e) := by
  unfold thirdLine gammaLine heatKernel; fun_prop

theorem coord_le (y : Space) (m : Fin 3) : |y m| ≤ ‖y‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y m

theorem line_deriv (hHP : HeatKernelPartials) (hC1 : LerayKernelC1) {τ : ℝ} (hτ : 0 < τ)
    (i j k : Fin 3) (x e : Space) (he : ‖e‖ ≤ 1) :
    Integrable (fun ρ => thirdLine i j k ρ x e) (volume.restrict (Ioi τ)) ∧
      fderiv ℝ (lerayKernel i j k τ) x e = aLine i j k τ x e + ∫ ρ in Ioi τ, thirdLine i j k ρ x e := by
  set R := ‖x‖ + 1 with hR
  have hcoord : ∀ t ∈ Metric.ball (0 : ℝ) 1, ∀ m, |(x + t • e) m| ≤ R := by
    intro t ht m
    have ht' : |t| < 1 := by simpa [Real.dist_eq] using ht
    calc |(x + t • e) m| ≤ ‖x + t • e‖ := coord_le _ m
      _ ≤ ‖x‖ + ‖t • e‖ := norm_add_le _ _
      _ ≤ R := by
        rw [norm_smul, Real.norm_eq_abs, hR]
        nlinarith [abs_nonneg t, norm_nonneg e]
  have he' : ∀ m, |e m| ≤ 1 := fun m => (coord_le e m).trans he
  have hpow : ∀ ρ ∈ Ioi τ, ∀ c : ℝ, c / ρ ^ 2 = c * ρ ^ (-2 : ℝ) := by
    intro ρ hρ c
    rw [Real.rpow_neg (hτ.trans hρ).le, Real.rpow_two, div_eq_mul_inv]
  have hint : ∀ c : ℝ, Integrable (fun ρ : ℝ => c * ρ ^ (-2 : ℝ)) (volume.restrict (Ioi τ)) :=
    fun c => (integrableOn_Ioi_rpow_of_lt (by norm_num) hτ).const_mul c
  have hF0 : Integrable (fun ρ => heatKernelThird i j k ρ (x + (0 : ℝ) • e)) (volume.restrict (Ioi τ)) := by
    refine (hint (3 * R * heatSup τ / 4 + R ^ 3 * heatSup τ / (8 * τ))).mono'
      (third_meas i j k _).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun ρ hρ => ?_)
    rw [Real.norm_eq_abs, ← hpow ρ hρ]
    exact third_bound hτ (le_of_lt hρ) i j k (hcoord 0 (Metric.mem_ball_self one_pos))
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi τ))
    (F := fun t ρ => heatKernelThird i j k ρ (x + t • e))
    (F' := fun t ρ => thirdLine i j k ρ (x + t • e) e) (x₀ := 0)
    (bound := fun ρ => (3 * heatSup τ / 4 + 3 * R * lineSup τ R / 4 + 3 * R ^ 2 * heatSup τ / (8 * τ) +
        R ^ 3 * lineSup τ R / (8 * τ)) * ρ ^ (-2 : ℝ))
    (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun t => (third_meas i j k _).aestronglyMeasurable) hF0
    (thirdLine_meas i j k _ e).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun ρ hρ t ht => by
      rw [Real.norm_eq_abs, ← hpow ρ hρ]
      exact thirdLine_bound hτ (le_of_lt hρ) i j k (hcoord t ht) he'))
    (hint _)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun ρ hρ t _ =>
      third_line hHP (hτ.trans hρ) i j k x e t))
  obtain ⟨hI, hD⟩ := hmain
  simp only [zero_smul, add_zero] at hI hD
  refine ⟨hI, ?_⟩
  have hA := first_line hHP hτ i j k x e 0
  simp only [zero_smul, add_zero] at hA
  have hd : DifferentiableAt ℝ (lerayKernel i j k τ) (x + (0 : ℝ) • e) := by
    simpa using ((hC1 i j k τ hτ).differentiable one_ne_zero) x
  have hl : HasDerivAt (fun s : ℝ => x + s • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
  have hL := hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
  simp only [zero_smul, add_zero] at hL
  exact hL.unique (hA.add hD)

end Breakdown.FarField.Internal.LerayDivFree

namespace Breakdown.FarField

open Internal.LerayDivFree

theorem lerayKernelDivFree_of_c1 :
    HeatKernelBounds → HeatKernelPartials → LerayKernelC1 → LerayKernelDivFree := by
  intro _ hHP hC1 j k τ hτ x
  have hl := fun i => line_deriv hHP hC1 hτ i j k x (unitVector i) (by simp [unitVector])
  rw [Finset.sum_congr rfl (fun i _ => (hl i).2), Finset.sum_add_distrib, sum_aLine j k τ hτ x,
    ← integral_finsetSum _ (fun i _ => (hl i).1)]
  have hsum : (fun ρ => ∑ i : Fin 3, thirdLine i j k ρ x (unitVector i)) =ᵐ[volume.restrict (Ioi τ)]
      fun ρ => secondPartialTime j k ρ x :=
    (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun ρ hρ => sum_thirdLine j k ρ (hτ.trans hρ) x)
  rw [integral_congr_ae hsum]
  have hint : IntegrableOn (fun ρ => secondPartialTime j k ρ x) (Ioi τ) :=
    (integrable_finsetSum _ (fun i _ => (hl i).1)).congr hsum
  rw [integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun ρ hρ => secondPartial_hasDerivAt j k x (hτ.trans_le hρ)) hint (secondPartial_tendsto j k x)]
  ring

end Breakdown.FarField

