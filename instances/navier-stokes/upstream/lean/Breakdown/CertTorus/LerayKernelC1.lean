import Breakdown.CertTorus.KernelStatements

open MeasureTheory Set Real Filter
open scoped ContDiff Topology

noncomputable section

namespace Breakdown.FarField

namespace Internal.LerayKernelSmooth

def linPart (i j k : Fin 3) (ρ : ℝ) (x : Space) : ℝ :=
  ((if j = k then x i else 0) + (if i = k then x j else 0) + (if i = j then x k else 0)) /
    (4 * ρ ^ 2)

def linPartDeriv (i j k : Fin 3) (ρ : ℝ) : Space →L[ℝ] ℝ :=
  (4 * ρ ^ 2)⁻¹ • ((if j = k then (EuclideanSpace.proj i : Space →L[ℝ] ℝ) else 0) +
    (if i = k then (EuclideanSpace.proj j : Space →L[ℝ] ℝ) else 0) +
    (if i = j then (EuclideanSpace.proj k : Space →L[ℝ] ℝ) else 0))

def cubicPart (i j k : Fin 3) (ρ : ℝ) (x : Space) : ℝ :=
  x i * x j * x k / (8 * ρ ^ 3)

def cubicPartDeriv (i j k : Fin 3) (ρ : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (8 * ρ ^ 3)⁻¹ • ((x j * x k) • (EuclideanSpace.proj i : Space →L[ℝ] ℝ) +
    (x i * x k) • (EuclideanSpace.proj j : Space →L[ℝ] ℝ) +
    (x i * x j) • (EuclideanSpace.proj k : Space →L[ℝ] ℝ))

def heatGrad (ρ : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  ∑ l : Fin 3, (-(x l / (2 * ρ)) * heatKernel ρ x) • (EuclideanSpace.proj l : Space →L[ℝ] ℝ)

def thirdDeriv (i j k : Fin 3) (ρ : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  linPart i j k ρ x • heatGrad ρ x + heatKernel ρ x • linPartDeriv i j k ρ -
    (cubicPart i j k ρ x • heatGrad ρ x + heatKernel ρ x • cubicPartDeriv i j k ρ x)

theorem heatKernelThird_eq (i j k : Fin 3) (ρ : ℝ) :
    heatKernelThird i j k ρ =
      fun x => linPart i j k ρ x * heatKernel ρ x - cubicPart i j k ρ x * heatKernel ρ x :=
  rfl

theorem contDiff_heatKernel {n : WithTop ℕ∞} (ρ : ℝ) : ContDiff ℝ n (heatKernel ρ) := by
  unfold heatKernel
  exact contDiff_const.mul (((contDiff_norm_sq ℝ).neg.div_const _).exp)

theorem hasFDerivAt_ite_coord (a b c : Fin 3) (x : Space) :
    HasFDerivAt (fun z : Space => if a = b then z c else 0)
      (if a = b then (EuclideanSpace.proj c : Space →L[ℝ] ℝ) else 0) x := by
  split_ifs
  · exact (EuclideanSpace.proj c : Space →L[ℝ] ℝ).hasFDerivAt
  · exact hasFDerivAt_const 0 x

theorem hasFDerivAt_linPart (i j k : Fin 3) (ρ : ℝ) (x : Space) :
    HasFDerivAt (linPart i j k ρ) (linPartDeriv i j k ρ) x := by
  have h := (((hasFDerivAt_ite_coord j k i x).add (hasFDerivAt_ite_coord i k j x)).add
    (hasFDerivAt_ite_coord i j k x)).mul_const (4 * ρ ^ 2)⁻¹
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  simp only [linPart, div_eq_mul_inv]
  rfl

theorem hasFDerivAt_cubicPart (i j k : Fin 3) (ρ : ℝ) (x : Space) :
    HasFDerivAt (cubicPart i j k ρ) (cubicPartDeriv i j k ρ x) x := by
  have hi := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hj := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hk := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h := ((hi.mul hj).mul hk).mul_const (8 * ρ ^ 3)⁻¹
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  · refine ContinuousLinearMap.ext fun v => ?_
    simp [cubicPartDeriv]
    ring
  · simp [cubicPart, div_eq_mul_inv]

theorem hasFDerivAt_heatKernelThird (hP : HeatKernelPartials) (i j k : Fin 3) {ρ : ℝ}
    (hρ : 0 < ρ) (x : Space) :
    HasFDerivAt (heatKernelThird i j k ρ) (thirdDeriv i j k ρ x) x := by
  have hΓ : HasFDerivAt (heatKernel ρ) (heatGrad ρ x) x := (hP ρ hρ x).1
  rw [heatKernelThird_eq]
  exact ((hasFDerivAt_linPart i j k ρ x).mul hΓ).sub ((hasFDerivAt_cubicPart i j k ρ x).mul hΓ)

theorem abs_coord_le (x : Space) (a : Fin 3) : |x a| ≤ ‖x‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x a

theorem abs_ite_coord_le (a b c : Fin 3) (x : Space) : |(if a = b then x c else 0)| ≤ ‖x‖ := by
  split_ifs
  · exact abs_coord_le x c
  · simp

theorem ite_proj_apply (a b c : Fin 3) (v : Space) :
    (if a = b then (EuclideanSpace.proj c : Space →L[ℝ] ℝ) else 0) v = if a = b then v c else 0 := by
  split_ifs <;> rfl

theorem abs_linForm_le (i j k : Fin 3) {ρ : ℝ} (hρ : 0 < ρ) (y : Space) :
    |((if j = k then y i else 0) + (if i = k then y j else 0) + (if i = j then y k else 0)) /
      (4 * ρ ^ 2)| ≤ 3 * ‖y‖ / (4 * ρ ^ 2) := by
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * ρ ^ 2)]
  gcongr
  calc _ ≤ |(if j = k then y i else 0) + (if i = k then y j else 0)| + |(if i = j then y k else 0)| :=
        abs_add_le _ _
    _ ≤ |(if j = k then y i else 0)| + |(if i = k then y j else 0)| + |(if i = j then y k else 0)| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ ‖y‖ + ‖y‖ + ‖y‖ :=
        add_le_add_three (abs_ite_coord_le _ _ _ y) (abs_ite_coord_le _ _ _ y) (abs_ite_coord_le _ _ _ y)
    _ = 3 * ‖y‖ := by ring

theorem abs_triple_le (x y : Space) (a b c : Fin 3) : |x a * x b * y c| ≤ ‖x‖ * ‖x‖ * ‖y‖ := by
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (abs_coord_le x a) (abs_coord_le x b) (abs_nonneg _) (norm_nonneg _))
    (abs_coord_le y c) (abs_nonneg _) (by positivity)

theorem norm_thirdDeriv_le (i j k : Fin 3) {ρ : ℝ} (hρ : 0 < ρ) (x : Space) :
    ‖thirdDeriv i j k ρ x‖ ≤ 13 * (4 * π * ρ) ^ (-(3 / 2 : ℝ)) / ρ ^ 2 := by
  obtain ⟨c, hc_eq⟩ : ∃ c : ℝ, c = (4 * π * ρ) ^ (-(3 / 2 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨E, hE_eq⟩ : ∃ E : ℝ, E = Real.exp (-(‖x‖ ^ 2) / (4 * ρ)) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hc_eq]; exact Real.rpow_pos_of_pos (by positivity) _
  have hE : 0 < E := by rw [hE_eq]; exact Real.exp_pos _
  have hΓ : heatKernel ρ x = c * E := by rw [hc_eq, hE_eq]; rfl
  obtain ⟨t, ht_eq⟩ : ∃ t : ℝ, t = ‖x‖ ^ 2 / (4 * ρ) := ⟨_, rfl⟩
  have ht : 0 ≤ t := by rw [ht_eq]; positivity
  have hEt : E * Real.exp t = 1 := by
    rw [hE_eq, ← Real.exp_add, ht_eq]
    rw [show -(‖x‖ ^ 2) / (4 * ρ) + ‖x‖ ^ 2 / (4 * ρ) = 0 by ring]
    exact Real.exp_zero
  have h1 : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have h2 : t ^ 2 / 2 ≤ Real.exp t := by simpa using Real.pow_div_factorial_le_exp (hx := ht) (n := 2)
  have hE1 : E ≤ 1 := by
    rw [hE_eq, Real.exp_le_one_iff, neg_div]
    have : 0 ≤ ‖x‖ ^ 2 / (4 * ρ) := by positivity
    linarith
  have hx2 : ‖x‖ ^ 2 = 4 * ρ * t := by rw [ht_eq]; field_simp
  have hEr2 : E * ‖x‖ ^ 2 ≤ 4 * ρ := by
    have h3 : E * t ≤ 1 := by
      calc E * t ≤ E * Real.exp t := mul_le_mul_of_nonneg_left h1 hE.le
        _ = 1 := hEt
    calc E * ‖x‖ ^ 2 = 4 * ρ * (E * t) := by rw [hx2]; ring
      _ ≤ 4 * ρ * 1 := by gcongr
      _ = 4 * ρ := by ring
  have hEr4 : E * ‖x‖ ^ 4 ≤ 32 * ρ ^ 2 := by
    have h3 : E * (t ^ 2 / 2) ≤ 1 := by
      calc E * (t ^ 2 / 2) ≤ E * Real.exp t := mul_le_mul_of_nonneg_left h2 hE.le
        _ = 1 := hEt
    calc E * ‖x‖ ^ 4 = 32 * ρ ^ 2 * (E * (t ^ 2 / 2)) := by
          rw [show ‖x‖ ^ 4 = (‖x‖ ^ 2) ^ 2 by ring, hx2]; ring
      _ ≤ 32 * ρ ^ 2 * 1 := by gcongr
      _ = 32 * ρ ^ 2 := by ring
  rw [← hc_eq]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hcE : 0 ≤ c * E := by positivity
  have hG : |heatGrad ρ x v| ≤ 3 * (‖x‖ * ‖v‖ / (2 * ρ)) * (c * E) := by
    have hterm : ∀ l : Fin 3, |(-(x l / (2 * ρ)) * (c * E)) * v l| ≤
        ‖x‖ * ‖v‖ / (2 * ρ) * (c * E) := by
      intro l
      rw [show (-(x l / (2 * ρ)) * (c * E)) * v l = -((x l * v l) * (c * E / (2 * ρ))) by ring,
        abs_neg, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ c * E / (2 * ρ))]
      calc |x l| * |v l| * (c * E / (2 * ρ)) ≤ ‖x‖ * ‖v‖ * (c * E / (2 * ρ)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul (abs_coord_le x l) (abs_coord_le v l) (abs_nonneg _) (norm_nonneg _))
              (by positivity)
        _ = ‖x‖ * ‖v‖ / (2 * ρ) * (c * E) := by ring
    have happ : heatGrad ρ x v = ∑ l : Fin 3, (-(x l / (2 * ρ)) * (c * E)) * v l := by
      simp [heatGrad, hΓ]
    rw [happ, Fin.sum_univ_three]
    calc _ ≤ |(-(x 0 / (2 * ρ)) * (c * E)) * v 0 + (-(x 1 / (2 * ρ)) * (c * E)) * v 1| +
          |(-(x 2 / (2 * ρ)) * (c * E)) * v 2| := abs_add_le _ _
      _ ≤ |(-(x 0 / (2 * ρ)) * (c * E)) * v 0| + |(-(x 1 / (2 * ρ)) * (c * E)) * v 1| +
          |(-(x 2 / (2 * ρ)) * (c * E)) * v 2| := by gcongr; exact abs_add_le _ _
      _ ≤ ‖x‖ * ‖v‖ / (2 * ρ) * (c * E) + ‖x‖ * ‖v‖ / (2 * ρ) * (c * E) +
          ‖x‖ * ‖v‖ / (2 * ρ) * (c * E) := add_le_add_three (hterm 0) (hterm 1) (hterm 2)
      _ = 3 * (‖x‖ * ‖v‖ / (2 * ρ)) * (c * E) := by ring
  have hP : |linPart i j k ρ x| ≤ 3 * ‖x‖ / (4 * ρ ^ 2) := abs_linForm_le i j k hρ x
  have hP' : |linPartDeriv i j k ρ v| ≤ 3 * ‖v‖ / (4 * ρ ^ 2) := by
    have happ : linPartDeriv i j k ρ v = ((if j = k then v i else 0) + (if i = k then v j else 0) +
        (if i = j then v k else 0)) / (4 * ρ ^ 2) := by
      simp only [linPartDeriv, smul_apply, add_apply,
        ite_proj_apply, smul_eq_mul]
      ring
    rw [happ]
    exact abs_linForm_le i j k hρ v
  have hQ : |cubicPart i j k ρ x| ≤ ‖x‖ ^ 3 / (8 * ρ ^ 3) := by
    unfold cubicPart
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 8 * ρ ^ 3)]
    gcongr
    calc |x i * x j * x k| ≤ ‖x‖ * ‖x‖ * ‖x‖ := abs_triple_le x x i j k
      _ = ‖x‖ ^ 3 := by ring
  have hQ' : |cubicPartDeriv i j k ρ x v| ≤ 3 * ‖x‖ ^ 2 * ‖v‖ / (8 * ρ ^ 3) := by
    have happ : cubicPartDeriv i j k ρ x v =
        (x j * x k * v i + x i * x k * v j + x i * x j * v k) / (8 * ρ ^ 3) := by
      simp only [cubicPartDeriv, smul_apply, add_apply,
        smul_eq_mul, EuclideanSpace.coe_proj]
      ring
    rw [happ, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 8 * ρ ^ 3)]
    gcongr
    calc _ ≤ |x j * x k * v i + x i * x k * v j| + |x i * x j * v k| := abs_add_le _ _
      _ ≤ |x j * x k * v i| + |x i * x k * v j| + |x i * x j * v k| := by
          gcongr; exact abs_add_le _ _
      _ ≤ ‖x‖ * ‖x‖ * ‖v‖ + ‖x‖ * ‖x‖ * ‖v‖ + ‖x‖ * ‖x‖ * ‖v‖ :=
          add_le_add_three (abs_triple_le x v j k i) (abs_triple_le x v i k j)
            (abs_triple_le x v i j k)
      _ = 3 * ‖x‖ ^ 2 * ‖v‖ := by ring
  have happ : thirdDeriv i j k ρ x v =
      linPart i j k ρ x * heatGrad ρ x v + c * E * linPartDeriv i j k ρ v -
        (cubicPart i j k ρ x * heatGrad ρ x v + c * E * cubicPartDeriv i j k ρ x v) := by
    simp only [thirdDeriv, sub_apply, add_apply,
      smul_apply, smul_eq_mul, hΓ]
  rw [Real.norm_eq_abs, happ]
  have hA1 : |linPart i j k ρ x * heatGrad ρ x v + c * E * linPartDeriv i j k ρ v| ≤
      3 * ‖x‖ / (4 * ρ ^ 2) * (3 * (‖x‖ * ‖v‖ / (2 * ρ)) * (c * E)) +
        c * E * (3 * ‖v‖ / (4 * ρ ^ 2)) := by
    calc _ ≤ |linPart i j k ρ x * heatGrad ρ x v| + |c * E * linPartDeriv i j k ρ v| :=
          abs_add_le _ _
      _ = |linPart i j k ρ x| * |heatGrad ρ x v| + c * E * |linPartDeriv i j k ρ v| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hcE]
      _ ≤ _ := by
          gcongr
  have hA2 : |cubicPart i j k ρ x * heatGrad ρ x v + c * E * cubicPartDeriv i j k ρ x v| ≤
      ‖x‖ ^ 3 / (8 * ρ ^ 3) * (3 * (‖x‖ * ‖v‖ / (2 * ρ)) * (c * E)) +
        c * E * (3 * ‖x‖ ^ 2 * ‖v‖ / (8 * ρ ^ 3)) := by
    calc _ ≤ |cubicPart i j k ρ x * heatGrad ρ x v| + |c * E * cubicPartDeriv i j k ρ x v| :=
          abs_add_le _ _
      _ = |cubicPart i j k ρ x| * |heatGrad ρ x v| + c * E * |cubicPartDeriv i j k ρ x v| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hcE]
      _ ≤ _ := by
          gcongr
  have hinner : 3 / 4 * E + 3 / 2 * (E * ‖x‖ ^ 2) / ρ + 3 / 16 * (E * ‖x‖ ^ 4) / ρ ^ 2 ≤ 13 := by
    have a1 : 3 / 2 * (E * ‖x‖ ^ 2) / ρ ≤ 6 := by
      rw [div_le_iff₀ hρ]; linarith
    have a2 : 3 / 16 * (E * ‖x‖ ^ 4) / ρ ^ 2 ≤ 6 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  calc _ ≤ _ := abs_sub _ _
    _ ≤ _ := add_le_add hA1 hA2
    _ = ‖v‖ * (c / ρ ^ 2) *
          (3 / 4 * E + 3 / 2 * (E * ‖x‖ ^ 2) / ρ + 3 / 16 * (E * ‖x‖ ^ 4) / ρ ^ 2) := by
        field_simp
        ring
    _ ≤ ‖v‖ * (c / ρ ^ 2) * 13 := by gcongr
    _ = 13 * c / ρ ^ 2 * ‖v‖ := by ring

theorem integrableOn_inv_pow (n : ℕ) (hn : 2 ≤ n) {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun ρ : ℝ => (ρ ^ n)⁻¹) (Ioi τ) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h := integrableOn_Ioi_rpow_of_lt (a := -(n : ℝ)) (by linarith) hτ
  refine h.congr_fun (fun ρ hρ => ?_) measurableSet_Ioi
  show ρ ^ (-(n : ℝ)) = (ρ ^ n)⁻¹
  rw [Real.rpow_neg (le_of_lt (hτ.trans hρ)), Real.rpow_natCast]

theorem continuous_thirdDeriv (i j k : Fin 3) (ρ : ℝ) : Continuous (thirdDeriv i j k ρ) := by
  have hΓ : Continuous (heatKernel ρ) := (contDiff_heatKernel (n := 0) ρ).continuous
  have hL : Continuous (linPart i j k ρ) :=
    continuous_iff_continuousAt.2 fun x => (hasFDerivAt_linPart i j k ρ x).continuousAt
  have hC : Continuous (cubicPart i j k ρ) :=
    continuous_iff_continuousAt.2 fun x => (hasFDerivAt_cubicPart i j k ρ x).continuousAt
  have hcoord : ∀ l : Fin 3, Continuous fun x : Space => x l :=
    fun l => (EuclideanSpace.proj l : Space →L[ℝ] ℝ).continuous
  have hcst : ∀ L : Space →L[ℝ] ℝ, Continuous fun _ : Space => L := fun L => continuous_const
  have hG : Continuous (heatGrad ρ) := by
    unfold heatGrad
    refine continuous_finsetSum _ fun l _ => ?_
    exact (((hcoord l).div_const _).neg.mul hΓ).smul (hcst _)
  have hQ' : Continuous (cubicPartDeriv i j k ρ) := by
    unfold cubicPartDeriv
    exact ((((((hcoord j).mul (hcoord k)).smul (hcst _)).add
      (((hcoord i).mul (hcoord k)).smul (hcst _))).add
      (((hcoord i).mul (hcoord j)).smul (hcst _)))).const_smul ((8 * ρ ^ 3)⁻¹ : ℝ)
  unfold thirdDeriv
  exact ((hL.smul hG).add (hΓ.smul (hcst _))).sub ((hC.smul hG).add (hΓ.smul hQ'))

theorem measurable_heatKernel_time (x : Space) : Measurable fun ρ : ℝ => heatKernel ρ x := by
  unfold heatKernel
  fun_prop

theorem measurable_heatKernelThird_time (i j k : Fin 3) (x : Space) :
    Measurable fun ρ : ℝ => heatKernelThird i j k ρ x := by
  have := measurable_heatKernel_time x
  unfold heatKernelThird
  fun_prop

theorem aestronglyMeasurable_thirdDeriv (i j k : Fin 3) (x : Space) (μ : Measure ℝ) :
    AEStronglyMeasurable (fun ρ : ℝ => thirdDeriv i j k ρ x) μ := by
  have := measurable_heatKernel_time x
  unfold thirdDeriv linPart linPartDeriv cubicPart cubicPartDeriv heatGrad
  fun_prop

theorem contDiff_integral_third (hB : HeatKernelBounds) (hP : HeatKernelPartials) (i j k : Fin 3)
    {τ : ℝ} (hτ : 0 < τ) :
    ContDiff ℝ 1 (fun x : Space => ∫ ρ in Ioi τ, heatKernelThird i j k ρ x) := by
  obtain ⟨C, hC⟩ := hB
  have hC0 : 0 ≤ C := by
    have h := (hC 1 one_pos 0).1
    have hpos : 0 < heatKernel 1 0 := by unfold heatKernel; positivity
    have hd : 0 < (‖(0 : Space)‖ + Real.sqrt 1) ^ 3 := by simp
    by_contra hneg
    replace hneg := not_le.mp hneg
    have : C / (‖(0 : Space)‖ + Real.sqrt 1) ^ 3 < 0 := div_neg_of_neg_of_pos hneg hd
    linarith
  have hint : ∀ x : Space,
      Integrable (fun ρ => heatKernelThird i j k ρ x) (volume.restrict (Ioi τ)) := by
    intro x
    refine Integrable.mono' ((integrableOn_inv_pow 3 (by norm_num) hτ).const_mul C)
      (measurable_heatKernelThird_time i j k x).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ρ hρ => ?_)
    have hρ0 : 0 < ρ := hτ.trans hρ
    have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ0
    rw [Real.norm_eq_abs]
    calc |heatKernelThird i j k ρ x| ≤ C / (‖x‖ + Real.sqrt ρ) ^ 6 := (hC ρ hρ0 x).2.2 i j k
      _ ≤ C / Real.sqrt ρ ^ 6 :=
          div_le_div_of_nonneg_left hC0 (pow_pos hs 6)
            (pow_le_pow_left₀ hs.le (by linarith [norm_nonneg x]) 6)
      _ = C * (ρ ^ 3)⁻¹ := by
          rw [show Real.sqrt ρ ^ 6 = (Real.sqrt ρ ^ 2) ^ 3 by ring, Real.sq_sqrt hρ0.le,
            div_eq_mul_inv]
  have hM : Integrable (fun ρ : ℝ => 13 * (4 * π * τ) ^ (-(3 / 2 : ℝ)) * (ρ ^ 2)⁻¹)
      (volume.restrict (Ioi τ)) :=
    (integrableOn_inv_pow 2 le_rfl hτ).const_mul _
  have hbound : ∀ x : Space, ∀ ρ ∈ Ioi τ,
      ‖thirdDeriv i j k ρ x‖ ≤ 13 * (4 * π * τ) ^ (-(3 / 2 : ℝ)) * (ρ ^ 2)⁻¹ := by
    intro x ρ hρ
    have hρ0 : 0 < ρ := hτ.trans hρ
    have hmono : (4 * π * ρ) ^ (-(3 / 2 : ℝ)) ≤ (4 * π * τ) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity)
        (mul_le_mul_of_nonneg_left (le_of_lt hρ) (by positivity)) (by norm_num)
    calc _ ≤ 13 * (4 * π * ρ) ^ (-(3 / 2 : ℝ)) / ρ ^ 2 := norm_thirdDeriv_le i j k hρ0 x
      _ ≤ 13 * (4 * π * τ) ^ (-(3 / 2 : ℝ)) / ρ ^ 2 := by gcongr
      _ = _ := by rw [div_eq_mul_inv]
  have hmeas : ∀ x : Space,
      AEStronglyMeasurable (fun ρ => heatKernelThird i j k ρ x) (volume.restrict (Ioi τ)) :=
    fun x => (measurable_heatKernelThird_time i j k x).aestronglyMeasurable
  have hmeas' : ∀ x : Space,
      AEStronglyMeasurable (fun ρ => thirdDeriv i j k ρ x) (volume.restrict (Ioi τ)) :=
    fun x => aestronglyMeasurable_thirdDeriv i j k x _
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨fun x => ∫ ρ in Ioi τ, thirdDeriv i j k ρ x, ?_, fun x => ?_⟩
  · exact continuous_of_dominated hmeas'
      (fun x => (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (hbound x))) hM
      (Eventually.of_forall fun ρ => continuous_thirdDeriv i j k ρ)
  · exact hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) univ_mem
      (Eventually.of_forall hmeas) (hint x) (hmeas' x)
      ((ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun ρ hρ y _ => hbound y ρ hρ)) hM
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ρ hρ y _ =>
        hasFDerivAt_heatKernelThird hP i j k (hτ.trans hρ) y))

end Internal.LerayKernelSmooth

open Internal.LerayKernelSmooth in
theorem lerayKernelC1_of_heat : HeatKernelBounds → HeatKernelPartials → LerayKernelC1 := by
  intro hB hP i j k τ hτ
  have h1 : ContDiff ℝ 1
      (fun x : Space => if i = j then -(x k / (2 * τ)) * heatKernel τ x else 0) := by
    split_ifs
    · exact (((EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.div_const _).neg).mul
        (contDiff_heatKernel τ)
    · exact contDiff_const
  exact h1.add (contDiff_integral_third hB hP i j k hτ)

end Breakdown.FarField
