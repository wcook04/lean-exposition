import Breakdown.Torus.StatementsCutoff

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace Cutoff.Internal

theorem cross_apply_zero (a b : Space) : cross a b 0 = a 1 * b 2 - a 2 * b 1 := rfl

theorem cross_apply_one (a b : Space) : cross a b 1 = a 2 * b 0 - a 0 * b 2 := rfl

theorem cross_apply_two (a b : Space) : cross a b 2 = a 0 * b 1 - a 1 * b 0 := rfl

theorem unitVector_apply (i j : Fin 3) : unitVector i j = if j = i then 1 else 0 := by
  simp [unitVector]

def crossLinear : Space →ₗ[ℝ] Space →ₗ[ℝ] Space :=
  LinearMap.mk₂ ℝ cross
    (fun a b c => by ext i; fin_cases i <;> simp [cross_apply_zero, cross_apply_one, cross_apply_two] <;> ring)
    (fun r a b => by ext i; fin_cases i <;> simp [cross_apply_zero, cross_apply_one, cross_apply_two] <;> ring)
    (fun a b c => by ext i; fin_cases i <;> simp [cross_apply_zero, cross_apply_one, cross_apply_two] <;> ring)
    (fun r a b => by ext i; fin_cases i <;> simp [cross_apply_zero, cross_apply_one, cross_apply_two] <;> ring)

def crossBilinear : Space →L[ℝ] Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ crossLinear)

theorem crossBilinear_apply (a b : Space) : crossBilinear a b = cross a b := rfl

theorem contDiff_cross {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}
    {u v : E → Space} (hu : ContDiff ℝ n u) (hv : ContDiff ℝ n v) :
    ContDiff ℝ n (fun y => cross (u y) (v y)) :=
  (crossBilinear.contDiff.comp hu).clm_apply hv

theorem hasFDerivAt_cross {u v : Space → Space} {u' v' : Space →L[ℝ] Space} {x : Space}
    (hu : HasFDerivAt u u' x) (hv : HasFDerivAt v v' x) :
    HasFDerivAt (fun y => cross (u y) (v y))
      ((crossBilinear (u x)).comp v' + (crossBilinear.comp u').flip (v x)) x :=
  (crossBilinear.hasFDerivAt.comp x hu).clm_apply hv

theorem hasFDerivAt_cross_apply {u v : Space → Space} {u' v' : Space →L[ℝ] Space} {x : Space}
    (w : Space) : ((crossBilinear (u x)).comp v' + (crossBilinear.comp u').flip (v x)) w =
      cross (u x) (v' w) + cross (u' w) (v x) := rfl

theorem apply_expand (L : Space →L[ℝ] Space) (v : Space) (c : Fin 3) :
    L v c = v 0 * L (unitVector 0) c + v 1 * L (unitVector 1) c + v 2 * L (unitVector 2) c := by
  have hv : v = v 0 • unitVector 0 + v 1 • unitVector 1 + v 2 • unitVector 2 := by
    ext i; fin_cases i <;> simp [unitVector_apply]
  conv_lhs => rw [hv]
  simp

variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

def partialSecond (F : ℝ × Space → G) (s : ℝ) (x : Space) : Space →L[ℝ] G :=
  (fderiv ℝ F (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space)

theorem hasFDerivAt_partialSecond (F : ℝ × Space → G) (hF : ContDiff ℝ 1 F) (s : ℝ) (x : Space) :
    HasFDerivAt (fun y => F (s, y)) (partialSecond F s x) x :=
  ((hF.differentiable one_ne_zero) (s, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)

theorem continuous_partialSecond (F : ℝ × Space → G) (hF : ContDiff ℝ 1 F) :
    Continuous (fun z : ℝ × Space => partialSecond F z.1 z.2) :=
  (hF.continuous_fderiv one_ne_zero).clm_comp continuous_const

theorem hasFDerivAt_integral_unit (F : ℝ × Space → G) (hF : ContDiff ℝ 1 F) (x : Space) :
    HasFDerivAt (fun y => ∫ s in (0 : ℝ)..1, F (s, y))
      (∫ s in (0 : ℝ)..1, partialSecond F s x) x := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall x 1)).exists_bound_of_continuousOn
    (continuous_partialSecond F hF).continuousOn
  have hcont : ∀ y : Space, Continuous (fun s : ℝ => F (s, y)) := fun y =>
    hF.continuous.comp (continuous_id.prodMk continuous_const)
  have hcont' : Continuous (fun s : ℝ => partialSecond F s x) :=
    (continuous_partialSecond F hF).comp (continuous_id.prodMk continuous_const)
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (F' := fun y s => partialSecond F s y) (Metric.ball_mem_nhds x one_pos)
    (Eventually.of_forall fun y => (hcont y).aestronglyMeasurable)
    ((hcont x).intervalIntegrable 0 1) hcont'.aestronglyMeasurable
    (Eventually.of_forall fun s hs y hy => hC (s, y)
      ⟨Ioc_subset_Icc_self (by rwa [uIoc_of_le zero_le_one] at hs), Metric.ball_subset_closedBall hy⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun s _ y _ => hasFDerivAt_partialSecond F hF s y)

theorem contDiff_integral_unit (n : ℕ) : ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (F : ℝ × Space → G), ContDiff ℝ ∞ F →
      ContDiff ℝ n (fun y => ∫ s in (0 : ℝ)..1, F (s, y)) := by
  induction n with
  | zero =>
    intro G _ _ _ F hF
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun y =>
      (hasFDerivAt_integral_unit F (hF.of_le (by simp)) y).continuousAt)
  | succ n ih =>
    intro G _ _ _ F hF
    have h1 : ContDiff ℝ 1 F := hF.of_le (by simp)
    have hfd : fderiv ℝ (fun y => ∫ s in (0 : ℝ)..1, F (s, y)) =
        fun y => ∫ s in (0 : ℝ)..1, partialSecond F s y :=
      funext fun y => (hasFDerivAt_integral_unit F h1 y).fderiv
    rw [Nat.cast_succ]
    refine contDiff_succ_iff_fderiv.2
      ⟨fun y => (hasFDerivAt_integral_unit F h1 y).differentiableAt, by simp, ?_⟩
    rw [hfd]
    exact ih (fun z => partialSecond F z.1 z.2)
      ((contDiff_infty_iff_fderiv.1 hF).2.clm_comp contDiff_const)

theorem contDiff_integral_unit_infty (F : ℝ × Space → G) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun y => ∫ s in (0 : ℝ)..1, F (s, y)) :=
  contDiff_infty.2 fun n => contDiff_integral_unit n F hF


def potentialIntegrand (x₀ : Space) (g : Space → Space) (z : ℝ × Space) : Space :=
  z.1 • cross (g (x₀ + z.1 • (z.2 - x₀))) (z.2 - x₀)

def potentialDerivative (x₀ x : Space) (g : Space → Space) (s : ℝ) : Space :=
  s ^ 2 • fderiv ℝ g (x₀ + s • (x - x₀)) (x - x₀) + (2 * s) • g (x₀ + s • (x - x₀))

section Potential

variable {x₀ : Space} {g : Space → Space}

theorem contDiff_potentialIntegrand (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (potentialIntegrand x₀ g) :=
  contDiff_fst.smul (contDiff_cross
    (hg.comp (contDiff_const.add (contDiff_fst.smul (contDiff_snd.sub contDiff_const))))
    (contDiff_snd.sub contDiff_const))

theorem homotopyPotential_eq :
    homotopyPotential x₀ g = fun y => ∫ s in (0 : ℝ)..1, potentialIntegrand x₀ g (s, y) := rfl

theorem partialSecond_potential_apply (hg : ContDiff ℝ ∞ g) (s : ℝ) (x v : Space) :
    partialSecond (potentialIntegrand x₀ g) s x v =
      s • (cross (g (x₀ + s • (x - x₀))) v + cross (fderiv ℝ g (x₀ + s • (x - x₀)) (s • v)) (x - x₀)) := by
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hin : HasFDerivAt (fun y : Space => x₀ + s • (y - x₀)) (s • ContinuousLinearMap.id ℝ Space) x :=
    (((hasFDerivAt_id (𝕜 := ℝ) x).sub_const x₀).const_smul s).const_add x₀
  have hg' := (hgd (x₀ + s • (x - x₀))).hasFDerivAt.comp x hin
  have hsub : HasFDerivAt (fun y : Space => y - x₀) (ContinuousLinearMap.id ℝ Space) x :=
    (hasFDerivAt_id (𝕜 := ℝ) x).sub_const x₀
  have hc := (hasFDerivAt_cross hg' hsub).const_smul s
  have h1 : ContDiff ℝ 1 (potentialIntegrand x₀ g) := (contDiff_potentialIntegrand hg).of_le (by simp)
  rw [(hasFDerivAt_partialSecond _ h1 s x).unique hc]
  rfl

theorem continuous_partialSecond_potential (hg : ContDiff ℝ ∞ g) (x v : Space) :
    Continuous (fun s => partialSecond (potentialIntegrand x₀ g) s x v) := by
  have h1 : ContDiff ℝ 1 (potentialIntegrand x₀ g) := (contDiff_potentialIntegrand hg).of_le (by simp)
  exact ((continuous_partialSecond _ h1).comp (continuous_id.prodMk continuous_const)).clm_apply
    continuous_const

theorem partialAt_potential (hg : ContDiff ℝ ∞ g) (i j : Fin 3) (x : Space) :
    partialAt (homotopyPotential x₀ g) i j x =
      ∫ s in (0 : ℝ)..1, partialSecond (potentialIntegrand x₀ g) s x (unitVector i) j := by
  have h1 : ContDiff ℝ 1 (potentialIntegrand x₀ g) := (contDiff_potentialIntegrand hg).of_le (by simp)
  have hint : IntervalIntegrable (fun s => partialSecond (potentialIntegrand x₀ g) s x) volume 0 1 :=
    ((continuous_partialSecond _ h1).comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
  unfold partialAt
  rw [homotopyPotential_eq, (hasFDerivAt_integral_unit _ h1 x).fderiv,
    ContinuousLinearMap.intervalIntegral_apply hint]
  exact ((EuclideanSpace.proj j).intervalIntegral_comp_comm (μ := volume)
    ((continuous_partialSecond_potential hg x (unitVector i)).intervalIntegrable 0 1)).symm

theorem integral_potentialDerivative (hg : ContDiff ℝ ∞ g) (x : Space) :
    ∫ s in (0 : ℝ)..1, potentialDerivative x₀ x g s = g x := by
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hgc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  have hgc0 : Continuous g := hg.continuous
  have hcont : Continuous (potentialDerivative x₀ x g) := by
    unfold potentialDerivative
    fun_prop
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => s ^ 2 • g (x₀ + s • (x - x₀)))
      (potentialDerivative x₀ x g s) s := by
    intro s _
    have hl : HasDerivAt (fun s : ℝ => x₀ + s • (x - x₀)) (x - x₀) s := by
      simpa using ((hasDerivAt_id s).smul_const (x - x₀)).const_add x₀
    have := (hasDerivAt_pow 2 s).smul ((hgd _).hasFDerivAt.comp_hasDerivAt s hl)
    exact this.congr_deriv (by simp [potentialDerivative])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable 0 1)]
  simp

theorem potential_pointwise (hg : ContDiff ℝ ∞ g) (hdiv : ∀ x, divergenceAt g x = 0) (x : Space)
    (a b c : Fin 3) (habc : (a = 1 ∧ b = 2 ∧ c = 0) ∨ (a = 2 ∧ b = 0 ∧ c = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 2))
    (s : ℝ) :
    partialSecond (potentialIntegrand x₀ g) s x (unitVector a) b -
      partialSecond (potentialIntegrand x₀ g) s x (unitVector b) a = potentialDerivative x₀ x g s c := by
  have hexp := apply_expand (fderiv ℝ g (x₀ + s • (x - x₀))) (x - x₀) c
  have hd := hdiv (x₀ + s • (x - x₀))
  rw [partialSecond_potential_apply hg, partialSecond_potential_apply hg]
  unfold potentialDerivative
  rcases habc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · simp [divergenceAt, Fin.sum_univ_three, cross_apply_one, cross_apply_two,
      unitVector_apply] at hd hexp ⊢
    linear_combination (-(s ^ 2)) * hexp + (-(s ^ 2) * (x 0 - x₀ 0)) * hd
  · simp [divergenceAt, Fin.sum_univ_three, cross_apply_zero, cross_apply_two,
      unitVector_apply] at hd hexp ⊢
    linear_combination (-(s ^ 2)) * hexp + (-(s ^ 2) * (x 1 - x₀ 1)) * hd
  · simp [divergenceAt, Fin.sum_univ_three, cross_apply_zero, cross_apply_one,
      unitVector_apply] at hd hexp ⊢
    linear_combination (-(s ^ 2)) * hexp + (-(s ^ 2) * (x 2 - x₀ 2)) * hd

theorem curl_potential_component (hg : ContDiff ℝ ∞ g) (hdiv : ∀ x, divergenceAt g x = 0) (x : Space)
    (a b c : Fin 3) (habc : (a = 1 ∧ b = 2 ∧ c = 0) ∨ (a = 2 ∧ b = 0 ∧ c = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 2)) :
    partialAt (homotopyPotential x₀ g) a b x - partialAt (homotopyPotential x₀ g) b a x = g x c := by
  have hcd : Continuous (potentialDerivative x₀ x g) := by
    have hgc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
    have hgc0 : Continuous g := hg.continuous
    unfold potentialDerivative
    fun_prop
  have hi : ∀ i j : Fin 3, IntervalIntegrable
      (fun s => partialSecond (potentialIntegrand x₀ g) s x (unitVector i) j) volume 0 1 :=
    fun i j => ((EuclideanSpace.proj j).continuous.comp
      (continuous_partialSecond_potential hg x (unitVector i))).intervalIntegrable 0 1
  rw [partialAt_potential hg, partialAt_potential hg,
    ← intervalIntegral.integral_sub (hi a b) (hi b a)]
  simp_rw [potential_pointwise hg hdiv x a b c habc]
  exact ((EuclideanSpace.proj c).intervalIntegral_comp_comm (μ := volume)
    (hcd.intervalIntegrable 0 1)).trans (congrArg (fun v : Space => v c) (integral_potentialDerivative hg x))

end Potential

end Cutoff.Internal

open Cutoff.Internal

theorem homotopyCurl : HomotopyCurl := by
  intro x₀ g hg hdiv
  refine ⟨contDiff_integral_unit_infty _ (contDiff_potentialIntegrand hg), fun x => ?_⟩
  ext c
  fin_cases c
  · exact curl_potential_component hg hdiv x 1 2 0 (Or.inl ⟨rfl, rfl, rfl⟩)
  · exact curl_potential_component hg hdiv x 2 0 1 (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  · exact curl_potential_component hg hdiv x 0 1 2 (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))

namespace Cutoff.Internal

theorem contDiff_gradientAt {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (gradientAt χ) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ χ) := (contDiff_infty_iff_fderiv.1 hχ).2
  unfold gradientAt
  exact ContDiff.sum fun i _ => (hfd.clm_apply contDiff_const).smul contDiff_const

theorem hasFDerivAt_gradientAt {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (x : Space) :
    HasFDerivAt (gradientAt χ) (∑ i : Fin 3, (((fderiv ℝ χ x).comp (0 : Space →L[ℝ] Space) +
      (fderiv ℝ (fderiv ℝ χ) x).flip (unitVector i)).smulRight (unitVector i))) x := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ χ) := (contDiff_infty_iff_fderiv.1 hχ).2
  have hH2 : HasFDerivAt (fderiv ℝ χ) (fderiv ℝ (fderiv ℝ χ) x) x :=
    (hfd.differentiable (by simp) x).hasFDerivAt
  exact HasFDerivAt.fun_sum fun i _ =>
    (hH2.clm_apply (hasFDerivAt_const (unitVector i) x)).smul_const (unitVector i)

end Cutoff.Internal

open Cutoff.Internal

theorem cutoffDivergenceFree (hH : HomotopyCurl) : CutoffDivergenceFree := by
  intro χ x₀ g hχ hg hdiv
  obtain ⟨hΨ, hcurl⟩ := hH x₀ g hg hdiv
  refine ⟨(hχ.smul hg).add (contDiff_cross (contDiff_gradientAt hχ) hΨ), fun x => ?_⟩
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hΨd : Differentiable ℝ (homotopyPotential x₀ g) := hΨ.differentiable (by simp)
  have hcut : HasFDerivAt (cutoffField χ x₀ g) _ x :=
    ((hχd x).hasFDerivAt.smul (hgd x).hasFDerivAt).add
      (hasFDerivAt_cross (hasFDerivAt_gradientAt hχ x) (hΨd x).hasFDerivAt)
  have hsym : IsSymmSndFDerivAt ℝ χ x := hχ.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  have hs01 := hsym (unitVector 0) (unitVector 1)
  have hs20 := hsym (unitVector 2) (unitVector 0)
  have hs12 := hsym (unitVector 1) (unitVector 2)
  have hd := hdiv x
  have h0 := congrArg (fun v : Space => v 0) (hcurl x)
  have h1 := congrArg (fun v : Space => v 1) (hcurl x)
  have h2 := congrArg (fun v : Space => v 2) (hcurl x)
  simp only [curlAt, partialAt] at h0 h1 h2
  unfold divergenceAt
  rw [hcut.fderiv]
  simp [divergenceAt, Fin.sum_univ_three, gradientAt, cross_apply_zero, cross_apply_one,
    cross_apply_two, unitVector_apply, crossBilinear_apply] at hd h0 h1 h2 ⊢
  linear_combination (χ x) * hd + (-(fderiv ℝ χ x (unitVector 0))) * h0
    + (-(fderiv ℝ χ x (unitVector 1))) * h1 + (-(fderiv ℝ χ x (unitVector 2))) * h2
    + (homotopyPotential x₀ g x 2) * hs01 + (homotopyPotential x₀ g x 1) * hs20
    + (homotopyPotential x₀ g x 0) * hs12

end Breakdown.Periodic
