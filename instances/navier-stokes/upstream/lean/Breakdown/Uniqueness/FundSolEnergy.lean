import Breakdown.Uniqueness.FundSolByParts
import Breakdown.Uniqueness.FundSolDecay
import Breakdown.Uniqueness.FundSolEnergyAux

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FundSol

open Internal

private theorem integral_sq_dirDeriv_two {θ : Space → ℝ} (hθ : ContDiff ℝ ∞ θ) {C : ℝ}
    (hC : ∀ k ≤ 3, ∀ x : Space, ‖iteratedFDeriv ℝ k θ x‖ ≤ C * (1 + ‖x‖)⁻¹ ^ (k + 1))
    (i j : Fin 3) :
    ∫ x, dirDeriv (unitVector i) (dirDeriv (unitVector j) θ) x ^ 2 =
      ∫ x, dirDeriv (unitVector i) (dirDeriv (unitVector i) θ) x *
        dirDeriv (unitVector j) (dirDeriv (unitVector j) θ) x := by
  have hu : ContDiff ℝ ∞ (dirDeriv (unitVector j) θ) := contDiff_dirDeriv hθ _
  have hw : ContDiff ℝ ∞ (dirDeriv (unitVector i) (dirDeriv (unitVector j) θ)) :=
    contDiff_dirDeriv hu _
  have hb : ContDiff ℝ ∞ (dirDeriv (unitVector i) (dirDeriv (unitVector i) θ)) :=
    contDiff_dirDeriv (contDiff_dirDeriv hθ _) _
  have hsw : dirDeriv (unitVector i) (dirDeriv (unitVector i) (dirDeriv (unitVector j) θ)) =
      dirDeriv (unitVector j) (dirDeriv (unitVector i) (dirDeriv (unitVector i) θ)) := by
    rw [dirDeriv_comm hθ (unitVector i) (unitVector j),
      dirDeriv_comm (contDiff_dirDeriv hθ _) (unitVector i) (unitVector j)]
  have bu : ∀ x, |dirDeriv (unitVector j) θ x| ≤ C * (1 + ‖x‖)⁻¹ ^ 2 := fun x =>
    (abs_dirDeriv_le hθ j x).trans (hC 1 (by norm_num) x)
  have bw : ∀ x, |dirDeriv (unitVector i) (dirDeriv (unitVector j) θ) x| ≤
      C * (1 + ‖x‖)⁻¹ ^ 3 := fun x =>
    (abs_dirDeriv_two_le hθ i j x).trans (hC 2 (by norm_num) x)
  have bb : ∀ x, |dirDeriv (unitVector i) (dirDeriv (unitVector i) θ) x| ≤
      C * (1 + ‖x‖)⁻¹ ^ 3 := fun x =>
    (abs_dirDeriv_two_le hθ i i x).trans (hC 2 (by norm_num) x)
  have bdu : ∀ x, |dirDeriv (unitVector j) (dirDeriv (unitVector j) θ) x| ≤
      C * (1 + ‖x‖)⁻¹ ^ 3 := fun x =>
    (abs_dirDeriv_two_le hθ j j x).trans (hC 2 (by norm_num) x)
  have bdw : ∀ x, |dirDeriv (unitVector i) (dirDeriv (unitVector i)
      (dirDeriv (unitVector j) θ)) x| ≤ C * (1 + ‖x‖)⁻¹ ^ 4 := fun x =>
    (abs_dirDeriv_three_le hθ i i j x).trans (hC 3 le_rfl x)
  have bdb : ∀ x, |dirDeriv (unitVector j) (dirDeriv (unitVector i)
      (dirDeriv (unitVector i) θ)) x| ≤ C * (1 + ‖x‖)⁻¹ ^ 4 := by
    rw [← hsw]; exact bdw
  have cu := hu.continuous
  have cw := hw.continuous
  have cb := hb.continuous
  have cdu := (contDiff_dirDeriv hu (unitVector j)).continuous
  have cdw := (contDiff_dirDeriv hw (unitVector i)).continuous
  have cdb := (contDiff_dirDeriv hb (unitVector j)).continuous
  have e1 : ∫ x, dirDeriv (unitVector j) θ x *
        dirDeriv (unitVector i) (dirDeriv (unitVector i) (dirDeriv (unitVector j) θ)) x =
      - ∫ x, dirDeriv (unitVector i) (dirDeriv (unitVector j) θ) x *
        dirDeriv (unitVector i) (dirDeriv (unitVector j) θ) x :=
    integral_mul_dirDeriv hu hw (unitVector i)
      (integrable_mul_of_decay cw cw (by norm_num) bw bw)
      (integrable_mul_of_decay cu cdw (by norm_num) bu bdw)
      (integrable_mul_of_decay cu cw (by norm_num) bu bw)
  have e2 : ∫ x, dirDeriv (unitVector j) θ x *
        dirDeriv (unitVector j) (dirDeriv (unitVector i) (dirDeriv (unitVector i) θ)) x =
      - ∫ x, dirDeriv (unitVector j) (dirDeriv (unitVector j) θ) x *
        dirDeriv (unitVector i) (dirDeriv (unitVector i) θ) x :=
    integral_mul_dirDeriv hu hb (unitVector j)
      (integrable_mul_of_decay cdu cb (by norm_num) bdu bb)
      (integrable_mul_of_decay cu cdb (by norm_num) bu bdb)
      (integrable_mul_of_decay cu cb (by norm_num) bu bb)
  rw [hsw] at e1
  have e3 : ∫ x, dirDeriv (unitVector i) (dirDeriv (unitVector j) θ) x ^ 2 =
      ∫ x, dirDeriv (unitVector i) (dirDeriv (unitVector j) θ) x *
        dirDeriv (unitVector i) (dirDeriv (unitVector j) θ) x := by
    simp only [sq]
  have e4 : ∫ x, dirDeriv (unitVector i) (dirDeriv (unitVector i) θ) x *
        dirDeriv (unitVector j) (dirDeriv (unitVector j) θ) x =
      ∫ x, dirDeriv (unitVector j) (dirDeriv (unitVector j) θ) x *
        dirDeriv (unitVector i) (dirDeriv (unitVector i) θ) x := by
    simp only [mul_comm]
  rw [e3, e4]
  linarith

private theorem integrable_sq_dirDeriv_two {θ : Space → ℝ} (hθ : ContDiff ℝ ∞ θ) {C : ℝ}
    (hC : ∀ k ≤ 3, ∀ x : Space, ‖iteratedFDeriv ℝ k θ x‖ ≤ C * (1 + ‖x‖)⁻¹ ^ (k + 1))
    (i j k l : Fin 3) :
    Integrable (fun x => dirDeriv (unitVector i) (dirDeriv (unitVector j) θ) x *
      dirDeriv (unitVector k) (dirDeriv (unitVector l) θ) x) :=
  integrable_mul_of_decay (contDiff_dirDeriv (contDiff_dirDeriv hθ _) _).continuous
    (contDiff_dirDeriv (contDiff_dirDeriv hθ _) _).continuous (by norm_num : 4 ≤ 3 + 3)
    (fun x => (abs_dirDeriv_two_le hθ i j x).trans (hC 2 (by norm_num) x))
    (fun x => (abs_dirDeriv_two_le hθ k l x).trans (hC 2 (by norm_num) x))

theorem integrable_sum_sq_secondPartial {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) :
    Integrable (fun x => ∑ i, ∑ j, secondPartial (potential g) i j x ^ 2) := by
  obtain ⟨C, hC⟩ := potential_decay hg hc
  have hθ := contDiff_potential hg hc
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  have h := integrable_sq_dirDeriv_two hθ hC i j i j
  simp only [← sq] at h
  simpa only [secondPartial_eq_dirDeriv hθ] using h

theorem integral_sum_sq_secondPartial {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) :
    ∫ x, ∑ i, ∑ j, secondPartial (potential g) i j x ^ 2 = ∫ x, g x ^ 2 := by
  obtain ⟨C, hC⟩ := potential_decay hg hc
  have hθ := contDiff_potential hg hc
  have hint : ∀ i j, Integrable (fun x =>
      dirDeriv (unitVector i) (dirDeriv (unitVector j) (potential g)) x ^ 2) := by
    intro i j
    have h := integrable_sq_dirDeriv_two hθ hC i j i j
    simpa only [← sq] using h
  have hssp : ∀ x, ∑ i, dirDeriv (unitVector i) (dirDeriv (unitVector i) (potential g)) x =
      g x := by
    intro x
    rw [← scalarSumSecondPartials_potential hg hc x, scalarSumSecondPartials]
    simp only [secondPartial_eq_dirDeriv hθ]
  calc ∫ x, ∑ i, ∑ j, secondPartial (potential g) i j x ^ 2
        = ∫ x, ∑ i, ∑ j, dirDeriv (unitVector i) (dirDeriv (unitVector j) (potential g)) x ^ 2 := by
          simp only [secondPartial_eq_dirDeriv hθ]
    _ = ∑ i, ∑ j, ∫ x, dirDeriv (unitVector i) (dirDeriv (unitVector j) (potential g)) x ^ 2 := by
          rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finsetSum _ fun j _ => hint i j]
    _ = ∑ i, ∑ j, ∫ x, dirDeriv (unitVector i) (dirDeriv (unitVector i) (potential g)) x *
          dirDeriv (unitVector j) (dirDeriv (unitVector j) (potential g)) x := by
          simp only [integral_sq_dirDeriv_two hθ hC]
    _ = ∫ x, ∑ i, ∑ j, dirDeriv (unitVector i) (dirDeriv (unitVector i) (potential g)) x *
          dirDeriv (unitVector j) (dirDeriv (unitVector j) (potential g)) x := by
          rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
            integrable_sq_dirDeriv_two hθ hC i i j j]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finsetSum _ fun j _ => integrable_sq_dirDeriv_two hθ hC i i j j]
    _ = ∫ x, g x ^ 2 := by
          congr 1
          funext x
          rw [← Finset.sum_mul_sum, hssp x, sq]

private theorem norm_sq_gradientAt (θ : Space → ℝ) (x : Space) :
    ‖gradientAt θ x‖ ^ 2 = ∑ i, dirDeriv (unitVector i) θ x ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [gradientAt, unitVector, dirDeriv, Pi.single_apply]

private theorem norm_sq_eq_sum (v : Space) : ‖v‖ ^ 2 = ∑ j, v j ^ 2 :=
  EuclideanSpace.real_norm_sq_eq v

private theorem gradient_energy_bound {θ : Space → ℝ} {ϕ : Space → Space}
    (hθ : ContDiff ℝ ∞ θ) (hϕ : ∀ j, ContDiff ℝ ∞ (fun y => ϕ y j))
    (hc : ∀ j, HasCompactSupport (fun y => ϕ y j)) {C K : ℝ}
    (hC : ∀ k ≤ 3, ∀ x : Space, ‖iteratedFDeriv ℝ k θ x‖ ≤ C * (1 + ‖x‖)⁻¹ ^ (k + 1))
    (hK : ∀ x, |θ x| ≤ K * (1 + ‖x‖)⁻¹ ^ 2)
    (hssp : ∀ x, ∑ i, dirDeriv (unitVector i) (dirDeriv (unitVector i) θ) x =
      ∑ j, dirDeriv (unitVector j) (fun y => ϕ y j) x) :
    Integrable (fun x => ‖gradientAt θ x‖ ^ 2) ∧
    ∫ x, ‖gradientAt θ x‖ ^ 2 ≤ ∫ x, ‖ϕ x‖ ^ 2 := by
  have cθ := hθ.continuous
  have cD : ∀ i, Continuous (dirDeriv (unitVector i) θ) := fun i =>
    (contDiff_dirDeriv hθ _).continuous
  have cDD : ∀ i, Continuous (dirDeriv (unitVector i) (dirDeriv (unitVector i) θ)) := fun i =>
    (contDiff_dirDeriv (contDiff_dirDeriv hθ _) _).continuous
  have bD : ∀ i x, |dirDeriv (unitVector i) θ x| ≤ C * (1 + ‖x‖)⁻¹ ^ 2 := fun i x =>
    (abs_dirDeriv_le hθ i x).trans (hC 1 (by norm_num) x)
  have bDD : ∀ i x, |dirDeriv (unitVector i) (dirDeriv (unitVector i) θ) x| ≤
      C * (1 + ‖x‖)⁻¹ ^ 3 := fun i x =>
    (abs_dirDeriv_two_le hθ i i x).trans (hC 2 (by norm_num) x)
  have iDD : ∀ i, Integrable (fun x => dirDeriv (unitVector i) θ x *
      dirDeriv (unitVector i) θ x) := fun i =>
    integrable_mul_of_decay (cD i) (cD i) (by norm_num) (bD i) (bD i)
  have iθDD : ∀ i, Integrable (fun x => θ x *
      dirDeriv (unitVector i) (dirDeriv (unitVector i) θ) x) := fun i =>
    integrable_mul_of_decay cθ (cDD i) (by norm_num) hK (bDD i)
  have iSq : ∀ i, Integrable (fun x => dirDeriv (unitVector i) θ x ^ 2) := fun i => by
    simpa only [sq] using iDD i
  have cϕj : ∀ j, Continuous (fun y => ϕ y j) := fun j => (hϕ j).continuous
  have cDϕ : ∀ j, Continuous (dirDeriv (unitVector j) (fun y => ϕ y j)) := fun j =>
    (contDiff_dirDeriv (hϕ j) _).continuous
  have sDϕ : ∀ j, HasCompactSupport (dirDeriv (unitVector j) (fun y => ϕ y j)) := fun j =>
    (hc j).fderiv_apply (𝕜 := ℝ) (unitVector j)
  have iθDϕ : ∀ j, Integrable (fun x => θ x * dirDeriv (unitVector j) (fun y => ϕ y j) x) :=
    fun j => (cθ.mul (cDϕ j)).integrable_of_hasCompactSupport (sDϕ j).mul_left
  have iDθϕ : ∀ j, Integrable (fun x => dirDeriv (unitVector j) θ x * ϕ x j) :=
    fun j => ((cD j).mul (cϕj j)).integrable_of_hasCompactSupport (hc j).mul_left
  have iθϕ : ∀ j, Integrable (fun x => θ x * ϕ x j) :=
    fun j => (cθ.mul (cϕj j)).integrable_of_hasCompactSupport (hc j).mul_left
  have hA : ∀ i, ∫ x, dirDeriv (unitVector i) θ x ^ 2 =
      - ∫ x, θ x * dirDeriv (unitVector i) (dirDeriv (unitVector i) θ) x := by
    intro i
    have e := integral_mul_dirDeriv hθ (contDiff_dirDeriv hθ (unitVector i)) (unitVector i)
      (iDD i) (iθDD i) (integrable_mul_of_decay cθ (cD i) (by norm_num) hK (bD i))
    rw [e, neg_neg]
    simp only [sq]
  have hD : ∀ j, ∫ x, θ x * dirDeriv (unitVector j) (fun y => ϕ y j) x =
      - ∫ x, dirDeriv (unitVector j) θ x * ϕ x j := fun j =>
    integral_mul_dirDeriv hθ (hϕ j) (unitVector j) (iDθϕ j) (iθDϕ j) (iθϕ j)
  have hG : (fun x => ‖gradientAt θ x‖ ^ 2) = fun x => ∑ i, dirDeriv (unitVector i) θ x ^ 2 := by
    funext x
    exact norm_sq_gradientAt θ x
  have iG : Integrable (fun x => ‖gradientAt θ x‖ ^ 2) := by
    rw [hG]
    exact integrable_finsetSum _ fun i _ => iSq i
  have hX : ∫ x, ‖gradientAt θ x‖ ^ 2 = ∑ j, ∫ x, dirDeriv (unitVector j) θ x * ϕ x j := by
    rw [hG, integral_finsetSum _ fun i _ => iSq i]
    simp only [hA, Finset.sum_neg_distrib]
    rw [← integral_finsetSum _ fun i _ => iθDD i]
    have hm : ∀ x, ∑ i, θ x * dirDeriv (unitVector i) (dirDeriv (unitVector i) θ) x =
        ∑ j, θ x * dirDeriv (unitVector j) (fun y => ϕ y j) x := by
      intro x
      rw [← Finset.mul_sum, hssp, Finset.mul_sum]
    simp only [hm]
    rw [integral_finsetSum _ fun j _ => iθDϕ j]
    simp only [hD, Finset.sum_neg_distrib, neg_neg]
  have iPhi : Integrable (fun x => ‖ϕ x‖ ^ 2) := by
    simp only [norm_sq_eq_sum]
    refine integrable_finsetSum _ fun j _ => ?_
    have h : Integrable (fun x => ϕ x j * ϕ x j) :=
      ((cϕj j).mul (cϕj j)).integrable_of_hasCompactSupport (hc j).mul_left
    simpa only [sq] using h
  have hZ : ∑ j, ∫ x, dirDeriv (unitVector j) θ x * ϕ x j ≤
      ∫ x, ((1 / 2 : ℝ) * ‖gradientAt θ x‖ ^ 2 + (1 / 2 : ℝ) * ‖ϕ x‖ ^ 2) := by
    rw [← integral_finsetSum _ fun j _ => iDθϕ j]
    refine integral_mono (integrable_finsetSum _ fun j _ => iDθϕ j)
      ((iG.const_mul _).add (iPhi.const_mul _)) fun x => ?_
    rw [norm_sq_gradientAt, norm_sq_eq_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    nlinarith [sq_nonneg (dirDeriv (unitVector j) θ x - ϕ x j)]
  rw [integral_add (iG.const_mul _) (iPhi.const_mul _), integral_const_mul, integral_const_mul,
    ← hX] at hZ
  exact ⟨iG, by linarith⟩

private theorem fderiv_component {ϕ : Space → Space} (hϕ : ContDiff ℝ ∞ ϕ) (j : Fin 3)
    (x v : Space) : fderiv ℝ (fun y => ϕ y j) x v = (fderiv ℝ ϕ x v) j := by
  have hd : DifferentiableAt ℝ ϕ x := hϕ.differentiable (by simp) x
  have h := ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  have e : (fun y => ϕ y j) = ⇑(EuclideanSpace.proj j : Space →L[ℝ] ℝ) ∘ ϕ := by
    funext y
    simp
  rw [e, h]
  simp

private theorem potential_sum_three {F : Fin 3 → Space → ℝ} (hF : ∀ j, ContDiff ℝ ∞ (F j))
    (hc : ∀ j, HasCompactSupport (F j)) (x : Space) :
    potential (fun y => ∑ j, F j y) x = ∑ j, potential (F j) x := by
  have e : (fun y => ∑ j, F j y) = (F 0 + F 1) + F 2 := by
    funext y
    simp [Fin.sum_univ_three]
  rw [e, potential_add (g := F 0 + F 1) (h := F 2) ((hF 0).add (hF 1)) ((hc 0).add (hc 1)) (hF 2) (hc 2),
    potential_add (hF 0) (hc 0) (hF 1) (hc 1)]
  simp [Fin.sum_univ_three]

theorem integral_sq_gradient_potential_div_le {ϕ : Space → Space} (hϕ : ContDiff ℝ ∞ ϕ)
    (hc : HasCompactSupport ϕ) :
    Integrable (fun x => ‖gradientAt (potential (divergenceAt ϕ)) x‖ ^ 2) ∧
    ∫ x, ‖gradientAt (potential (divergenceAt ϕ)) x‖ ^ 2 ≤ ∫ x, ‖ϕ x‖ ^ 2 := by
  have hϕc : ∀ j, ContDiff ℝ ∞ (fun y => ϕ y j) := fun j =>
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp hϕ
  have hcc : ∀ j, HasCompactSupport (fun y => ϕ y j) := fun j =>
    hc.comp_left (g := fun v : Space => v j) (by simp)
  have hdiv : divergenceAt ϕ = fun x => ∑ j, dirDeriv (unitVector j) (fun y => ϕ y j) x := by
    funext x
    simp only [divergenceAt, dirDeriv, fderiv_component hϕ]
  have hdS : ContDiff ℝ ∞ (divergenceAt ϕ) := by
    rw [hdiv]
    exact ContDiff.sum fun j _ => contDiff_dirDeriv (hϕc j) _
  have hdC : HasCompactSupport (divergenceAt ϕ) :=
    (hc.fderiv (𝕜 := ℝ)).comp_left
      (g := fun L : Space →L[ℝ] Space => ∑ i : Fin 3, (L (unitVector i)) i) (by simp)
  have hθ := contDiff_potential hdS hdC
  obtain ⟨C, hC⟩ := potential_decay hdS hdC
  have hdec : ∀ j, ∃ c : ℝ, ∀ k ≤ 3, ∀ x : Space,
      ‖iteratedFDeriv ℝ k (potential (fun y => ϕ y j)) x‖ ≤ c * (1 + ‖x‖)⁻¹ ^ (k + 1) :=
    fun j => potential_decay (hϕc j) (hcc j)
  choose c hcj using hdec
  have hrep : ∀ x, potential (divergenceAt ϕ) x =
      ∑ j, dirDeriv (unitVector j) (potential (fun y => ϕ y j)) x := by
    intro x
    rw [hdiv, potential_sum_three (fun j => contDiff_dirDeriv (hϕc j) _)
      (fun j => (hcc j).fderiv_apply (𝕜 := ℝ) (unitVector j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (fderiv_potential (hϕc j) (hcc j) x (unitVector j)).symm
  have hK : ∀ x, |potential (divergenceAt ϕ) x| ≤ (∑ j, c j) * (1 + ‖x‖)⁻¹ ^ 2 := by
    intro x
    rw [hrep, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    exact (abs_dirDeriv_le (contDiff_potential (hϕc j) (hcc j)) j x).trans
      (hcj j 1 (by norm_num) x)
  have hssp : ∀ x, ∑ i, dirDeriv (unitVector i) (dirDeriv (unitVector i)
      (potential (divergenceAt ϕ))) x = ∑ j, dirDeriv (unitVector j) (fun y => ϕ y j) x := by
    intro x
    have h := scalarSumSecondPartials_potential hdS hdC x
    rw [scalarSumSecondPartials] at h
    simp only [secondPartial_eq_dirDeriv hθ] at h
    rw [h, hdiv]
  exact gradient_energy_bound hθ hϕc hcc hC hK hssp

end Breakdown.FundSol
