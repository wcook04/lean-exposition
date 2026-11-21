import Breakdown.FracCell.GivenProfileDefs
import Breakdown.FracCell.FieldJointSmooth
import Breakdown.FracCell.GivenProfileBoundsField
import Breakdown.FracCell.GivenProfileDriftLocal

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

namespace FieldDriftInternal

open FracInternal.FieldJoint

theorem grad_continuous_main (P : ChartParams) (hP : IsChartParams P) (F : FieldData) :
    ∀ᵐ y ∂(volume : Measure Space), Continuous (fun β : ℝ => fderiv ℝ (fieldOf P F β) y) := by
  let lt : List ℝ := F.modes.toList.flatMap (fun n => (F.amp n).radialAmp.mesh.tBreaks ++
    (F.amp n).polarAmp.mesh.tBreaks ++ (F.amp n).streamAmp.mesh.tBreaks ++ (F.amp n).swirlAmp.mesh.tBreaks)
  let lx : List ℝ := F.modes.toList.flatMap (fun n => (F.amp n).radialAmp.mesh.xBreaks ++
    (F.amp n).polarAmp.mesh.xBreaks ++ (F.amp n).streamAmp.mesh.xBreaks ++ (F.amp n).swirlAmp.mesh.xBreaks)
  filter_upwards [FracInternal.ae_generic P hP.L0_pos lt lx] with y hy
  obtain ⟨h0, h1, h2, ht, hx⟩ := hy
  have hy0 : y ≠ 0 := fun h => h0 (by simp [h])
  have hx0 : heightRatio y ≠ 0 := div_ne_zero h2 (norm_ne_zero_iff.2 hy0)
  have hgen : ∀ n ∈ F.modes, ∀ S ∈ [(F.amp n).radialAmp, (F.amp n).polarAmp, (F.amp n).streamAmp,
      (F.amp n).swirlAmp], chartT P y ∉ S.mesh.tBreaks ∧ |heightRatio y| ∉ S.mesh.xBreaks := by
    intro n hn S hS
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    refine ⟨fun h => ht (List.mem_flatMap.2 ⟨n, Finset.mem_toList.2 hn, ?_⟩),
      fun h => hx (List.mem_flatMap.2 ⟨n, Finset.mem_toList.2 hn, ?_⟩)⟩
    · rcases hS with rfl | rfl | rfl | rfl <;> simp [h]
    · rcases hS with rfl | rfl | rfl | rfl <;> simp [h]
  refine continuous_iff_continuousAt.2 fun β0 => ?_
  have key : ContDiffAt ℝ ∞ (Function.uncurry (fun β z => fieldOf P F β z)) (β0, y) :=
    joint_fieldOf P hP F hy0 h1 hx0 hgen β0
  exact (ContDiffAt.fderiv (f := fun β z => fieldOf P F β z) (g := fun _ => y) (m := 0) key contDiffAt_const
    (by simp)).continuousAt


theorem le_of_ae_le_continuous {f g : Space → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ᵐ y ∂(volume : Measure Space), f y ≤ g y) (y : Space) : f y ≤ g y := by
  by_contra hy
  replace hy := not_le.1 hy
  have ho : IsOpen {z | g z < f z} := isOpen_lt hg hf
  have hpos := ho.measure_pos (volume : Measure Space) ⟨y, hy⟩
  have h0 : (volume : Measure Space) {z | g z < f z} = 0 := by
    rw [ae_iff] at h
    simpa using h
  exact hpos.ne' h0

theorem drift_continuous {α a : ℝ} {v : Space → Space} (hv : ContDiff ℝ 1 v) :
    Continuous (fun y => driftField α a v (fun z => fderiv ℝ v z) y) := by
  have hG : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by norm_num)
  have hJ : Continuous axialTurn := by
    let L : Space →ₗ[ℝ] Space :=
      { toFun := axialTurn
        map_add' := fun x y => by ext i; fin_cases i <;> simp [axialTurn] <;> ring
        map_smul' := fun c x => by ext i; fin_cases i <;> simp [axialTurn] }
    exact L.continuous_of_finiteDimensional
  have hvc := hv.continuous
  unfold driftField
  fun_prop

theorem norm_ofComponents_le (w : Fin 3 → ℝ) : ‖ofComponents w‖ ≤ |w 0| + |w 1| + |w 2| := by
  unfold ofComponents
  refine (norm_add₃_le).trans (le_of_eq ?_)
  simp [Real.norm_eq_abs]

theorem coord_div_norm_le (y : Space) (j : Fin 3) : |y j| / ‖y‖ ≤ 1 := by
  rcases eq_or_ne y 0 with h | h
  · simp [h]
  · rw [div_le_one (norm_pos_iff.2 h)]
    have := PiLp.norm_apply_le y j
    rwa [Real.norm_eq_abs] at this

theorem frame_bounds (y : Space) (i : Fin 3) :
    |radialVec y i| ≤ 1 ∧ |polarVecQ y i| ≤ 1 ∧ |azimVecQ y i| ≤ 1 := by
  have hh : |heightRatio y| ≤ 1 := by
    unfold heightRatio
    rw [abs_div, abs_norm]
    exact coord_div_norm_le y 2
  have hh2 : heightRatio y ^ 2 ≤ 1 := by
    have := sq_abs (heightRatio y)
    nlinarith [abs_nonneg (heightRatio y)]
  refine ⟨?_, ?_, ?_⟩
  · unfold radialVec
    rw [abs_div, abs_norm]
    exact coord_div_norm_le y i
  · fin_cases i
    · show |heightRatio y * y 0 / ‖y‖| ≤ 1
      rw [mul_div_assoc, abs_mul, abs_div, abs_norm]
      exact mul_le_one₀ hh (by positivity) (coord_div_norm_le y 0)
    · show |heightRatio y * y 1 / ‖y‖| ≤ 1
      rw [mul_div_assoc, abs_mul, abs_div, abs_norm]
      exact mul_le_one₀ hh (by positivity) (coord_div_norm_le y 1)
    · show |-(qOf y)| ≤ 1
      unfold qOf
      rw [abs_neg, abs_le]
      constructor <;> nlinarith [sq_nonneg (heightRatio y)]
  · fin_cases i
    · show |-(y 1) / ‖y‖| ≤ 1
      rw [abs_div, abs_neg, abs_norm]
      exact coord_div_norm_le y 1
    · show |y 0 / ‖y‖| ≤ 1
      rw [abs_div, abs_norm]
      exact coord_div_norm_le y 0
    · show |(0 : ℝ)| ≤ 1
      simp

theorem fieldOf_drift_generic (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (α a : ℝ) (hα : α = 1 + P.eps) :
    ∃ C : ℝ, ∀ y : Space, y 0 ≠ 0 → y 1 ≠ 0 → y 2 ≠ 0 →
      (∀ n ∈ F.modes, ∀ S ∈ [(F.amp n).radialAmp, (F.amp n).polarAmp, (F.amp n).streamAmp,
        (F.amp n).swirlAmp], chartT P y ∉ S.mesh.tBreaks ∧ |heightRatio y| ∉ S.mesh.xBreaks) →
      ‖driftField α a (fieldOf P F (-(2 * α * (P.m : ℝ) * a)))
        (fun z => fderiv ℝ (fieldOf P F (-(2 * α * (P.m : ℝ) * a))) z) y‖ ≤
          C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  set β : ℝ := -(2 * α * (P.m : ℝ) * a) with hβ
  have hαpos : 0 < α := by rw [hα]; linarith [hP.eps_pos]
  obtain ⟨C, hC⟩ := flowTerm_bound P hP F hF (max |β| |2 * α * a|)
  set M : ℝ := max P.L0 1 with hM
  set K : ℝ := 3 * ((F.modes.card : ℝ) * (3 * (|C| * M ^ 2))) with hK
  refine ⟨K / (2 * α), fun y h0 h1 h2 hgen => ?_⟩
  have hy0 : y ≠ 0 := fun h => h0 (by simp [h])
  have hL := hP.L0_pos
  have hn0 : 0 ≤ ‖y‖ := norm_nonneg y
  have hden : 0 < ‖y‖ + P.L0 := by linarith
  have ht0 : 0 ≤ chartT P y := div_nonneg hn0 hden.le
  have ht1 : chartT P y < 1 := by
    unfold chartT
    rw [div_lt_one hden]
    linarith
  have hx1 : |heightRatio y| ≤ 1 := by
    unfold heightRatio
    rw [abs_div, abs_norm]
    exact coord_div_norm_le y 2
  have hx0 : heightRatio y ≠ 0 := div_ne_zero h2 (norm_ne_zero_iff.2 hy0)
  set t := chartT P y with ht
  have hW : ∀ n ∈ F.modes, ∀ k : Fin 3,
      ‖flowTerm P F n β (2 * α * a) t (heightRatio y) k‖ ≤ |C| * (1 - t) ^ 2 := fun n hn k =>
    (hC β (2 * α * a) (le_max_left _ _) (le_max_right _ _) n hn k t (heightRatio y) ht0 ht1 hx1 hx0
      (hgen n hn)).trans (by gcongr; exact le_abs_self C)
  have hdec : ‖(decayFactor P y : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    unfold decayFactor chartS
    have hs0 : 0 ≤ 1 - t := by linarith
    rw [abs_of_nonneg (Real.rpow_nonneg hs0 _)]
    exact Real.rpow_le_one hs0 (by linarith) (by linarith [hP.eps_pos])
  have hcomp : ∀ i : Fin 3, |((decayFactor P y : ℂ) * ∑ n ∈ F.modes, modePhase P n β y *
      (flowTerm P F n β (2 * α * a) t (heightRatio y) 0 * radialVec y i +
        flowTerm P F n β (2 * α * a) t (heightRatio y) 1 * polarVecQ y i +
          flowTerm P F n β (2 * α * a) t (heightRatio y) 2 * azimVecQ y i)).re| ≤
        (F.modes.card : ℝ) * (3 * (|C| * (1 - t) ^ 2)) := by
    intro i
    obtain ⟨fr, fp, fa⟩ := frame_bounds y i
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) hdec).trans ?_
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [norm_mul]
    have hph : ‖modePhase P n β y‖ = 1 := by
      unfold modePhase
      exact Complex.norm_exp_I_mul_ofReal _
    rw [hph, one_mul]
    have e : ∀ (k : Fin 3) (r : ℝ), |r| ≤ 1 →
        ‖flowTerm P F n β (2 * α * a) t (heightRatio y) k * (r : ℂ)‖ ≤ |C| * (1 - t) ^ 2 := by
      intro k r hr
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) hr |>.trans (hW n hn k)
    calc _ ≤ _ := norm_add₃_le
      _ ≤ |C| * (1 - t) ^ 2 + |C| * (1 - t) ^ 2 + |C| * (1 - t) ^ 2 :=
          add_le_add (add_le_add (e 0 _ fr) (e 1 _ fp)) (e 2 _ fa)
      _ = 3 * (|C| * (1 - t) ^ 2) := by ring
  have hform := drift_flow_formula P hP F α a hα y h0 h1 h2 hgen
  have hmain : ‖(2 * α) • driftField α a (fieldOf P F β) (fun z => fderiv ℝ (fieldOf P F β) z) y‖ ≤
      3 * ((F.modes.card : ℝ) * (3 * (|C| * (1 - t) ^ 2))) := by
    rw [hform]
    refine (norm_ofComponents_le _).trans ?_
    have := hcomp 0
    have := hcomp 1
    have := hcomp 2
    linarith
  have hs : (1 - t) ^ 2 ≤ M ^ 2 * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
    have e1 : 1 - t = P.L0 / (‖y‖ + P.L0) := by
      rw [ht]
      unfold chartT
      field_simp
      ring
    have hM1 : 1 ≤ M := le_max_right _ _
    have hML : P.L0 ≤ M := le_max_left _ _
    have e2 : P.L0 / (‖y‖ + P.L0) ≤ M / (1 + ‖y‖) := by
      rw [div_le_div_iff₀ hden (by linarith)]
      nlinarith
    have e3 : (1 + ‖y‖) ^ (-(2 : ℝ)) = ((1 + ‖y‖) ^ 2)⁻¹ := by
      rw [Real.rpow_neg (by linarith), Real.rpow_two]
    rw [e1, e3, ← div_eq_mul_inv, ← div_pow]
    exact pow_le_pow_left₀ (by positivity) e2 2
  have h2α : 0 < 2 * α := by linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos h2α] at hmain
  have hcard : 0 ≤ (F.modes.card : ℝ) := by positivity
  have hC0 : 0 ≤ |C| := abs_nonneg C
  have hfin : 2 * α * ‖driftField α a (fieldOf P F β) (fun z => fderiv ℝ (fieldOf P F β) z) y‖ ≤
      2 * α * (K / (2 * α) * (1 + ‖y‖) ^ (-(2 : ℝ))) := by
    calc _ ≤ 3 * ((F.modes.card : ℝ) * (3 * (|C| * (1 - t) ^ 2))) := hmain
      _ ≤ 3 * ((F.modes.card : ℝ) * (3 * (|C| * (M ^ 2 * (1 + ‖y‖) ^ (-(2 : ℝ)))))) := by gcongr
      _ = 2 * α * (K / (2 * α) * (1 + ‖y‖) ^ (-(2 : ℝ))) := by
        rw [hK]
        field_simp
  exact le_of_mul_le_mul_left hfin h2α

theorem drift_bound_main (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (α a : ℝ) (hα : α = 1 + P.eps) :
    ∃ C : ℝ, ∀ y : Space, ‖driftField α a (fieldOf P F (-(2 * α * (P.m : ℝ) * a)))
      (fun z => fderiv ℝ (fieldOf P F (-(2 * α * (P.m : ℝ) * a))) z) y‖ ≤
        C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  set β : ℝ := -(2 * α * (P.m : ℝ) * a) with hβ
  obtain ⟨C, hC⟩ := fieldOf_drift_generic P hP F hF α a hα
  obtain ⟨_, hD⟩ := FracCellInternal.fieldOf_decay P hP F hF |β|
  have hC1 : ContDiff ℝ 1 (fieldOf P F β) := (hD β le_rfl).1
  refine ⟨C, le_of_ae_le_continuous (f := fun y => ‖driftField α a (fieldOf P F β)
    (fun z => fderiv ℝ (fieldOf P F β) z) y‖) (drift_continuous hC1).norm ?_ ?_⟩
  · exact continuous_const.mul ((continuous_const.add continuous_norm).rpow_const
      fun y => Or.inl (by have := norm_nonneg y; exact (show (0 : ℝ) < 1 + ‖y‖ by linarith).ne'))
  · let lt : List ℝ := F.modes.toList.flatMap (fun n => (F.amp n).radialAmp.mesh.tBreaks ++
      (F.amp n).polarAmp.mesh.tBreaks ++ (F.amp n).streamAmp.mesh.tBreaks ++ (F.amp n).swirlAmp.mesh.tBreaks)
    let lx : List ℝ := F.modes.toList.flatMap (fun n => (F.amp n).radialAmp.mesh.xBreaks ++
      (F.amp n).polarAmp.mesh.xBreaks ++ (F.amp n).streamAmp.mesh.xBreaks ++ (F.amp n).swirlAmp.mesh.xBreaks)
    filter_upwards [FracInternal.ae_generic P hP.L0_pos lt lx] with y hy
    obtain ⟨h0, h1, h2, ht, hx⟩ := hy
    refine hC y h0 h1 h2 fun n hn S hS => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    refine ⟨fun h => ht (List.mem_flatMap.2 ⟨n, Finset.mem_toList.2 hn, ?_⟩),
      fun h => hx (List.mem_flatMap.2 ⟨n, Finset.mem_toList.2 hn, ?_⟩)⟩
    · rcases hS with rfl | rfl | rfl | rfl <;> simp [h]
    · rcases hS with rfl | rfl | rfl | rfl <;> simp [h]

theorem fieldOf_differentiable (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (β : ℝ) : Differentiable ℝ (fieldOf P F β) := by
  obtain ⟨_, h⟩ := FracCellInternal.fieldOf_decay P hP F hF |β|
  exact (h β le_rfl).1.differentiable (by norm_num)

theorem fieldOf_grad_bound (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (B : ℝ) :
    ∃ C : ℝ, ∀ β : ℝ, |β| ≤ B → ∀ y : Space,
      ‖fderiv ℝ (fieldOf P F β) y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  obtain ⟨C, h⟩ := FracCellInternal.fieldOf_decay P hP F hF B
  exact ⟨C, fun β hβ y => ((h β hβ).2 y).2.1⟩

theorem fieldOf_grad_continuous (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) :
    ∀ᵐ y ∂(volume : Measure Space), Continuous (fun β : ℝ => fderiv ℝ (fieldOf P F β) y) := by
  exact grad_continuous_main P hP F

theorem fieldOf_drift_bound (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (α a : ℝ) (hα : α = 1 + P.eps) :
    ∃ C : ℝ, ∀ y : Space, ‖driftField α a (fieldOf P F (-(2 * α * (P.m : ℝ) * a)))
      (fun z => fderiv ℝ (fieldOf P F (-(2 * α * (P.m : ℝ) * a))) z) y‖ ≤
        C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  exact drift_bound_main P hP F hF α a hα

end FieldDriftInternal

end GivenFields

end CellCert

end Breakdown
