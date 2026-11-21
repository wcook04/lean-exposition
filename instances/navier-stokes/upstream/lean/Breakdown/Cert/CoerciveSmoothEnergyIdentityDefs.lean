import Breakdown.Cert.CoerciveSmoothEnergyIdentityCutoff
import Breakdown.Cert.CoerciveEnergyIdentityStretch

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEnergyIdentityInternal

open EnergyIdentityInternal

def timePair (v : ℝ → Space → Space) (σ : ℝ) (y : Space) : ℝ :=
  ∑ j : Fin 3, inner ℝ (fderiv ℝ (fun x => deriv (fun s => v s x) σ) y (unitVector j))
    (fderiv ℝ (v σ) y (unitVector j))

def advectionPart (W v : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  fderiv ℝ (v σ) y (W σ y) + fderiv ℝ (W σ) y (v σ y)

structure SliceBounds (P : ℝ) (v : ℝ → Space → Space) (σ : ℝ) : Prop where
  weighted : Integrable (fun y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)
  first : Integrable (fun y => ‖fderiv ℝ (v σ) y‖ ^ 2)
  second : Integrable (fun y => ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ ^ 2)
  transport : Integrable (fun y => ‖transportPart P v σ y‖ ^ 2)
  transport_first : Integrable (fun y => ‖fderiv ℝ (transportPart P v σ) y‖ ^ 2)
  time_first : Integrable (fun y => ‖fderiv ℝ (fun x => deriv (fun s => v s x) σ) y‖ ^ 2)

theorem smoothRight_split (P : ℝ) (W v : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    inner ℝ (smoothRight P W v σ y) (-secondDerivTrace (secondDerivField v σ y)) =
      inner ℝ (transportPart P v σ y) (-secondDerivTrace (secondDerivField v σ y))
      + inner ℝ (-secondDerivTrace (secondDerivField v σ y)) (-secondDerivTrace (secondDerivField v σ y))
      + inner ℝ (advectionPart W v σ y) (-secondDerivTrace (secondDerivField v σ y)) := by
  have h : smoothRight P W v σ y = transportPart P v σ y + (-secondDerivTrace (secondDerivField v σ y))
      + advectionPart W v σ y := by
    simp only [smoothRight, transportPart, advectionPart]
    abel
  rw [h, inner_add_left, inner_add_left]


theorem unitVector_norm (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem coord_abs_le (w : Space) (i : Fin 3) : |w i| ≤ ‖w‖ := by
  have := PiLp.norm_apply_le w i
  rwa [Real.norm_eq_abs] at this

theorem clm_unit_sq_le (G : Space →L[ℝ] Space) (i : Fin 3) : ‖G (unitVector i)‖ ^ 2 ≤ ‖G‖ ^ 2 := by
  have h := G.le_opNorm (unitVector i)
  rw [unitVector_norm, mul_one] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem matSq_le (G : Space →L[ℝ] Space) : matSq G ≤ 3 * ‖G‖ ^ 2 := by
  simp only [matSq, Fin.sum_univ_three]
  linarith [clm_unit_sq_le G 0, clm_unit_sq_le G 1, clm_unit_sq_le G 2]

theorem matSq_nonneg (G : Space →L[ℝ] Space) : 0 ≤ matSq G := by
  simp only [matSq]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem curl_sq_cross (G : Space →L[ℝ] Space) :
    ‖curlVec G‖ ^ 2 = matSq G - ∑ i : Fin 3, G (G (unitVector i)) i := by
  rw [curl_sq]
  simp only [Fin.sum_univ_three]
  rw [apply_self G (G (unitVector 0)) 0, apply_self G (G (unitVector 1)) 1,
    apply_self G (G (unitVector 2)) 2]
  simp only [matSq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  ring

theorem cross_term_zero (u : Space → Space) (hu : ContDiff ℝ 2 u) (hd : ∀ y, divergenceAt u y = 0)
    (h1 : Integrable (fun y => ‖fderiv ℝ u y‖ ^ 2))
    (h0 : Integrable (fun y => ‖u y‖ ^ 2 / (1 + ‖y‖) ^ 2)) (i : Fin 3) :
    Integrable (fun y => fderiv ℝ u y (fderiv ℝ u y (unitVector i)) i) ∧
      ∫ y, fderiv ℝ u y (fderiv ℝ u y (unitVector i)) i = 0 := by
  have hdu : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hdd : Differentiable ℝ (fun x => fderiv ℝ u x) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have cu : Continuous u := hu.continuous
  have cdu : Continuous (fun y => fderiv ℝ u y) := hu.continuous_fderiv (by norm_num)
  have ha : ContDiff ℝ 1 (fun x => fderiv ℝ u x (unitVector i)) :=
    (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hg : ContDiff ℝ 1 (fun x => u x i) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp (hu.of_le (by norm_num))
  have e1 : ∀ y, fderiv ℝ (fun x => u x i) y (fderiv ℝ u y (unitVector i)) =
      fderiv ℝ u y (fderiv ℝ u y (unitVector i)) i := fun y => fderiv_component u (hdu y) i _
  have ediv : ∀ y, divergenceAt (fun x => fderiv ℝ u x (unitVector i)) y = 0 := by
    intro y
    have ea : ∀ w, fderiv ℝ (fun x => fderiv ℝ u x (unitVector i)) y w =
        fderiv ℝ (fun x => fderiv ℝ u x) y w (unitVector i) := by
      intro w
      have := fderiv_clm_left (ContinuousLinearMap.apply ℝ Space (unitVector i)) (hdd y)
      rw [show (fun x => fderiv ℝ u x (unitVector i)) =
        fun x => (ContinuousLinearMap.apply ℝ Space (unitVector i)) (fderiv ℝ u x) from rfl, this]
      rfl
    simp only [divergenceAt, ea, d2_symm_two u hu y _ (unitVector i)]
    exact div_deriv_zero_two u hu hd y i
  have hbound : ∀ y, |fderiv ℝ u y (fderiv ℝ u y (unitVector i)) i| ≤ ‖fderiv ℝ u y‖ ^ 2 := by
    intro y
    refine (coord_abs_le _ i).trans ?_
    refine ((fderiv ℝ u y).le_opNorm _).trans ?_
    have h2 := (fderiv ℝ u y).le_opNorm (unitVector i)
    rw [unitVector_norm, mul_one] at h2
    rw [sq]
    exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  have cX : Continuous (fun y => fderiv ℝ u y (fderiv ℝ u y (unitVector i)) i) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp
      (cdu.clm_apply (cdu.clm_apply continuous_const))
  have iX : Integrable (fun y => fderiv ℝ u y (fderiv ℝ u y (unitVector i)) i) :=
    h1.mono' cX.aestronglyMeasurable (Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs]; exact hbound y))
  refine ⟨iX, ?_⟩
  have h3 : Integrable (fun y => ‖fderiv ℝ u y (unitVector i)‖ * |u y i| / (1 + ‖y‖)) := by
    refine ((h1.add h0).div_const 2).mono' ?_ (Eventually.of_forall (fun y => ?_))
    · exact (((cdu.clm_apply continuous_const).norm.mul
        ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp cu).abs).div
        (continuous_const.add continuous_norm) (fun y => (by positivity : (0 : ℝ) < 1 + ‖y‖).ne')).aestronglyMeasurable
    · have hp : 0 < 1 + ‖y‖ := by positivity
      have ha' : ‖fderiv ℝ u y (unitVector i)‖ ≤ ‖fderiv ℝ u y‖ := by
        have h2 := (fderiv ℝ u y).le_opNorm (unitVector i)
        rwa [unitVector_norm, mul_one] at h2
      have hb' := coord_abs_le (u y) i
      set A := ‖fderiv ℝ u y‖
      set B := ‖u y‖ / (1 + ‖y‖)
      have hB : ‖u y‖ ^ 2 / (1 + ‖y‖) ^ 2 = B ^ 2 := by rw [div_pow]
      have hA0 : 0 ≤ ‖fderiv ℝ u y (unitVector i)‖ := norm_nonneg _
      have hB0 : 0 ≤ |u y i| := abs_nonneg _
      have key : ‖fderiv ℝ u y (unitVector i)‖ * |u y i| / (1 + ‖y‖) ≤ A * B := by
        rw [div_le_iff₀ hp]
        have : A * B * (1 + ‖y‖) = A * ‖u y‖ := by
          simp only [B]; field_simp
        rw [this]
        exact mul_le_mul ha' hb' hB0 (norm_nonneg _)
      have hnn : 0 ≤ ‖fderiv ℝ u y (unitVector i)‖ * |u y i| / (1 + ‖y‖) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn, Pi.add_apply, hB]
      nlinarith [sq_nonneg (A - B)]
  have hz : (fun y => divergenceAt (fun x => fderiv ℝ u x (unitVector i)) y * u y i) = fun _ => 0 := by
    funext y; rw [ediv y, zero_mul]
  have w := weighted_ibp (fun x => fderiv ℝ u x (unitVector i)) (fun x => u x i) ha hg
    (by simp_rw [e1]; exact iX) (by rw [hz]; exact integrable_zero _ _ _) h3
  simp_rw [e1] at w
  rw [w, hz, integral_zero, neg_zero]

theorem curl_energy (u : Space → Space) (hu : ContDiff ℝ 2 u) (hd : ∀ y, divergenceAt u y = 0)
    (h1 : Integrable (fun y => ‖fderiv ℝ u y‖ ^ 2))
    (h0 : Integrable (fun y => ‖u y‖ ^ 2 / (1 + ‖y‖) ^ 2)) :
    ∫ y, ‖curlVec (fderiv ℝ u y)‖ ^ 2 = ∫ y, matSq (fderiv ℝ u y) := by
  have cdu : Continuous (fun y => fderiv ℝ u y) := hu.continuous_fderiv (by norm_num)
  have iF : Integrable (fun y => matSq (fderiv ℝ u y)) := by
    refine (h1.const_mul 3).mono' ?_ (Eventually.of_forall (fun y => ?_))
    · unfold matSq; fun_prop
    · rw [Real.norm_eq_abs, abs_of_nonneg (matSq_nonneg _)]; exact matSq_le _
  have cz := fun i => cross_term_zero u hu hd h1 h0 i
  simp_rw [curl_sq_cross]
  rw [integral_sub iF (integrable_finsetSum _ (fun i _ => (cz i).1)),
    integral_finsetSum _ (fun i _ => (cz i).1)]
  simp [fun i => (cz i).2]

end SmoothEnergyIdentityInternal

end Coercive

end Breakdown
