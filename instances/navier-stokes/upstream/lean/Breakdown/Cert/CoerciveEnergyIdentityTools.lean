import Breakdown.Cert.CoerciveNodes

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace EnergyIdentityInternal

theorem slice_smooth {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) (σ : ℝ) :
    ContDiff ℝ ∞ (v σ) :=
  hv.1.comp (contDiff_const.prodMk contDiff_id)

theorem slice_vanish {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) :
    ∃ R, ∀ σ y, R < ‖y‖ → v σ y = 0 :=
  hv.2.2.1

theorem compact_of_vanish {E : Type*} [NormedAddCommGroup E] (f : Space → E) (R : ℝ)
    (h : ∀ y, R < ‖y‖ → f y = 0) : HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_closedBall 0 R) (fun y hy => h y (by
    simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy))


theorem vanish_open {E : Type*} [NormedAddCommGroup E] (f : Space → E) (R : ℝ)
    (h : ∀ y, R < ‖y‖ → f y = 0) (y : Space) (hy : R < ‖y‖) : f =ᶠ[nhds y] fun _ => 0 := by
  have ho : IsOpen {x : Space | R < ‖x‖} := isOpen_lt continuous_const continuous_norm
  filter_upwards [ho.mem_nhds hy] with x hx using h x hx

theorem fderiv_vanish {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Space → E) (R : ℝ)
    (h : ∀ y, R < ‖y‖ → f y = 0) : ∀ y, R < ‖y‖ → fderiv ℝ f y = 0 := by
  intro y hy
  rw [(vanish_open f R h y hy).fderiv_eq]
  simp

theorem fderiv_clm_left {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) {g : Space → E} {y : Space} (h : DifferentiableAt ℝ g y) :
    fderiv ℝ (fun x => L (g x)) y = L.comp (fderiv ℝ g y) :=
  (L.hasFDerivAt.comp y h.hasFDerivAt).fderiv

theorem fderiv_component (u : Space → Space) {y : Space} (hu : DifferentiableAt ℝ u y) (i : Fin 3)
    (w : Space) : fderiv ℝ (fun x => u x i) y w = fderiv ℝ u y w i := by
  have := fderiv_clm_left (EuclideanSpace.proj i : Space →L[ℝ] ℝ) hu
  change fderiv ℝ (fun x => (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (u x)) y w = _
  rw [this]
  rfl

theorem fderiv_second_component (u : Space → Space) (hu : ContDiff ℝ 2 u) (y : Space) (i j k : Fin 3) :
    fderiv ℝ (fun x => fderiv ℝ (fun z => u z i) x (unitVector j)) y (unitVector k) =
      fderiv ℝ (fun x => fderiv ℝ u x) y (unitVector k) (unitVector j) i := by
  have hd : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hdd : Differentiable ℝ (fun x => fderiv ℝ u x) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have e : (fun x => fderiv ℝ (fun z => u z i) x (unitVector j)) =
      fun x => ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp
        (ContinuousLinearMap.apply ℝ Space (unitVector j))) (fderiv ℝ u x) := by
    funext x
    rw [fderiv_component u (hd x)]
    rfl
  rw [e, fderiv_clm_left _ (hdd y)]
  rfl

theorem ibp (f g : Space → ℝ) (j : Fin 3) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport f) :
    ∫ y, f y * fderiv ℝ g y (unitVector j) = -∫ y, fderiv ℝ f y (unitVector j) * g y := by
  have cf := hf.continuous
  have cg := hg.continuous
  have cf' : Continuous fun y => fderiv ℝ f y (unitVector j) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have cg' : Continuous fun y => fderiv ℝ g y (unitVector j) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (cf'.mul cg).integrable_of_hasCompactSupport ((hc.fderiv_apply (𝕜 := ℝ) _).mul_right)
  · exact (cf.mul cg').integrable_of_hasCompactSupport hc.mul_right
  · exact (cf.mul cg).integrable_of_hasCompactSupport hc.mul_right
  · exact fun x _ => (hf.differentiable (by norm_num)) x
  · exact fun x _ => (hg.differentiable (by norm_num)) x

theorem curlVec_add (G K : Space →L[ℝ] Space) : curlVec (G + K) = curlVec G + curlVec K := by
  simp only [curlVec, ContinuousLinearMap.add_apply, PiLp.add_apply, mul_add, Finset.sum_add_distrib,
    add_smul]

theorem curlVec_smul (c : ℝ) (G : Space →L[ℝ] Space) : curlVec (c • G) = c • curlVec G := by
  simp only [curlVec, ContinuousLinearMap.smul_apply, PiLp.smul_apply, smul_eq_mul, Finset.smul_sum,
    smul_smul, Finset.mul_sum]
  congr 1; funext i; congr 1; congr 1; funext j; congr 1; funext l; ring

def curlLinear : (Space →L[ℝ] Space) →ₗ[ℝ] Space where
  toFun := curlVec
  map_add' := curlVec_add
  map_smul' := curlVec_smul

def curlCLM : (Space →L[ℝ] Space) →L[ℝ] Space := LinearMap.toContinuousLinearMap curlLinear

theorem curlCLM_apply (G : Space →L[ℝ] Space) : curlCLM G = curlVec G := rfl

theorem slice_facts_of {v : ℝ → Space → Space} {R : ℝ} (hR : ∀ σ y, R < ‖y‖ → v σ y = 0) (σ : ℝ) :
    (∀ y, R < ‖y‖ → v σ y = 0) ∧ (∀ y, R < ‖y‖ → fderiv ℝ (v σ) y = 0) ∧
      (∀ y, R < ‖y‖ → fderiv ℝ (fun x => fderiv ℝ (v σ) x) y = 0) ∧
      (∀ y, R < ‖y‖ → fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y = 0) := by
  have h1 := fderiv_vanish (v σ) R (hR σ)
  refine ⟨hR σ, h1, fderiv_vanish _ R h1, fderiv_vanish _ R ?_⟩
  intro y hy
  rw [h1 y hy, ← curlCLM_apply, map_zero]

theorem slice_continuous {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) (σ : ℝ) :
    Continuous (v σ) ∧ Continuous (fun y => fderiv ℝ (v σ) y) ∧
      Continuous (fun y => fderiv ℝ (fun x => fderiv ℝ (v σ) x) y) ∧
      Continuous (fun y => fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y) := by
  have hs := slice_smooth hv σ
  have h1 : ContDiff ℝ ∞ (fun y => fderiv ℝ (v σ) y) := hs.fderiv_right (by simp)
  have h2 : ContDiff ℝ ∞ (fun y => curlCLM (fderiv ℝ (v σ) y)) := curlCLM.contDiff.comp h1
  refine ⟨hs.continuous, h1.continuous, h1.continuous_fderiv (by simp), ?_⟩
  exact h2.continuous_fderiv (by simp)

theorem sigma_integrable (f : ℝ × Space → ℝ) (hf : Continuous f) (R : ℝ)
    (h : ∀ σ y, R < ‖y‖ → f (σ, y) = 0) :
    IntegrableOn (fun σ => ∫ y, f (σ, y)) (Set.Icc 0 1) := by
  have hK : IntegrableOn f (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) (volume.prod volume) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall 0 R))
  have hB : Function.support f ⊆ Set.univ ×ˢ Metric.closedBall (0 : Space) R := by
    intro z hz
    refine ⟨trivial, ?_⟩
    by_contra hc
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hc
    exact hz (h z.1 z.2 hc)
  have hm : (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space) =
      (volume.prod volume).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hint : Integrable f ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    rw [hm, ← integrableOn_iff_integrable_of_support_subset hB, IntegrableOn,
      Measure.restrict_restrict (MeasurableSet.univ.prod Metric.isClosed_closedBall.measurableSet)]
    have e : Set.univ ×ˢ Metric.closedBall (0 : Space) R ∩ Set.Icc (0 : ℝ) 1 ×ˢ Set.univ =
        Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R := by
      ext z
      simp [and_comm]
    rw [e]
    exact hK
  exact hint.integral_prod_left

theorem space_fderiv_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → Space → E)
    (hF : Differentiable ℝ (fun z : ℝ × Space => F z.1 z.2)) (σ : ℝ) (y : Space) :
    fderiv ℝ (F σ) y =
      (fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) (σ, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space) :=
  ((hF (σ, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right σ y)).fderiv

theorem joint_partial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → Space → E)
    {m n : WithTop ℕ∞} (hF : ContDiff ℝ m (fun z : ℝ × Space => F z.1 z.2)) (hmn : n + 1 ≤ m)
    (h1 : m ≠ 0) : ContDiff ℝ n (fun z : ℝ × Space => fderiv ℝ (F z.1) z.2) := by
  have hd := hF.differentiable h1
  have e : (fun z : ℝ × Space => fderiv ℝ (F z.1) z.2) = fun z =>
      (fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) z).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
    funext z
    exact space_fderiv_eq F hd z.1 z.2
  rw [e]
  exact (hF.fderiv_right hmn).clm_comp contDiff_const

theorem time_deriv_eq (v : ℝ → Space → Space) (hF : Differentiable ℝ (fun z : ℝ × Space => v z.1 z.2))
    (σ : ℝ) (y : Space) :
    deriv (fun s => v s y) σ = fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (σ, y) (1, 0) :=
  by
  have h := (hF (σ, y)).hasFDerivAt.comp_hasDerivAt σ ((hasDerivAt_id σ).prodMk (hasDerivAt_const σ y))
  simp only [Function.comp_def, id] at h
  exact h.deriv

theorem joint_continuous {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) :
    Continuous (fun z : ℝ × Space => v z.1 z.2) ∧
    Continuous (fun z : ℝ × Space => deriv (fun s => v s z.2) z.1) ∧
    Continuous (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) ∧
    Continuous (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (v z.1) x) z.2) ∧
    Continuous (fun z : ℝ × Space => fderiv ℝ (fun x => curlVec (fderiv ℝ (v z.1) x)) z.2) := by
  have h0 := hv.1
  have hd : Differentiable ℝ (fun z : ℝ × Space => v z.1 z.2) := h0.differentiable (by simp)
  have h1 : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    joint_partial v h0 (by simp) (by simp)
  have h2 : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (v z.1) x) z.2) :=
    joint_partial (fun σ x => fderiv ℝ (v σ) x) h1 (by simp) (by simp)
  have h3 : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (fun x => curlCLM (fderiv ℝ (v z.1) x)) z.2) :=
    joint_partial (fun σ x => curlCLM (fderiv ℝ (v σ) x)) (curlCLM.contDiff.comp h1) (by simp) (by simp)
  refine ⟨h0.continuous, ?_, h1.continuous, h2.continuous, h3.continuous⟩
  have e : (fun z : ℝ × Space => deriv (fun s => v s z.2) z.1) =
      fun z => fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) z (1, 0) := by
    funext z
    exact time_deriv_eq v hd z.1 z.2
  rw [e]
  exact (h0.continuous_fderiv (by simp)).clm_apply continuous_const

theorem joint_continuous_weight {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => W z.1 z.2) ∧
    Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) ∧
    Continuous (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (W z.1) x) z.2) := by
  have h1 : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
    joint_partial W hW (by norm_num) (by simp)
  have h2 : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (W z.1) x) z.2) :=
    joint_partial (fun σ x => fderiv ℝ (W σ) x) h1 (by norm_num) (by simp)
  exact ⟨hW.continuous, h1.continuous, h2.continuous⟩

theorem d1_smooth (u : Space → Space) (hu : ContDiff ℝ ∞ u) (j i : Fin 3) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ u x (unitVector j) i) := by
  have h := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp
    ((hu.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const (c := unitVector j)))
  exact h

theorem d1_support (u : Space → Space) (hc : HasCompactSupport u) (j i : Fin 3) :
    HasCompactSupport (fun x => fderiv ℝ u x (unitVector j) i) := by
  have h := (hc.fderiv_apply (𝕜 := ℝ) (unitVector j)).comp_left (g := fun w : Space => w i) (by simp)
  exact h

theorem comp_smooth (u : Space → Space) (hu : ContDiff ℝ ∞ u) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x => u x i) := by
  have h := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hu
  exact h

theorem comp_support (u : Space → Space) (hc : HasCompactSupport u) (i : Fin 3) :
    HasCompactSupport (fun x => u x i) := by
  have h := hc.comp_left (g := fun w : Space => w i) (by simp)
  exact h

theorem d2_eq (u : Space → Space) (hu : ContDiff ℝ ∞ u) (y : Space) (i j k : Fin 3) :
    fderiv ℝ (fun x => fderiv ℝ u x (unitVector j) i) y (unitVector k) =
      fderiv ℝ (fun x => fderiv ℝ u x) y (unitVector k) (unitVector j) i := by
  have hdd : Differentiable ℝ (fun x => fderiv ℝ u x) :=
    (hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have h := fderiv_clm_left ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp
    (ContinuousLinearMap.apply ℝ Space (unitVector j))) (hdd y)
  change fderiv ℝ (fun x => ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp
    (ContinuousLinearMap.apply ℝ Space (unitVector j))) (fderiv ℝ u x)) y (unitVector k) = _
  rw [h]
  rfl

theorem d2_symm (u : Space → Space) (hu : ContDiff ℝ ∞ u) (y a b : Space) :
    fderiv ℝ (fun x => fderiv ℝ u x) y a b = fderiv ℝ (fun x => fderiv ℝ u x) y b a :=
  (hu.contDiffAt.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.mpr le_top)) a b

theorem div_deriv_zero (u : Space → Space) (hu : ContDiff ℝ ∞ u) (hd : ∀ y, divergenceAt u y = 0)
    (y : Space) (j : Fin 3) :
    ∑ i : Fin 3, fderiv ℝ (fun x => fderiv ℝ u x) y (unitVector j) (unitVector i) i = 0 := by
  have hdd : Differentiable ℝ (fun x => fderiv ℝ u x) :=
    (hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have e : (fun x => ∑ i : Fin 3, fderiv ℝ u x (unitVector i) i) = fun _ => 0 := by
    funext x
    exact hd x
  have h1 : ∀ i : Fin 3, DifferentiableAt ℝ (fun x => fderiv ℝ u x (unitVector i) i) y :=
    fun i => ((d1_smooth u hu i i).differentiable (by simp)) y
  have h2 : fderiv ℝ (fun x => ∑ i : Fin 3, fderiv ℝ u x (unitVector i) i) y (unitVector j) =
      ∑ i : Fin 3, fderiv ℝ (fun x => fderiv ℝ u x (unitVector i) i) y (unitVector j) := by
    rw [fderiv_fun_sum (fun i _ => h1 i)]
    simp
  rw [e] at h2
  simp only [d2_eq u hu y] at h2
  rw [← h2]
  simp

theorem cont_intg (f : Space → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) : Integrable f :=
  hf.integrable_of_hasCompactSupport hc

theorem one_le_inf : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top

theorem cross_zero (u : Space → Space) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hd : ∀ y, divergenceAt u y = 0) :
    ∫ y, ∑ j : Fin 3, ∑ i : Fin 3, fderiv ℝ u y (unitVector j) i * fderiv ℝ u y (unitVector i) j = 0 := by
  have hcont : ∀ j i : Fin 3, Continuous (fun x => fderiv ℝ u x (unitVector j) i) :=
    fun j i => (d1_smooth u hu j i).continuous
  have hint : ∀ j i : Fin 3,
      Integrable (fun y => fderiv ℝ u y (unitVector j) i * fderiv ℝ u y (unitVector i) j) :=
    fun j i => cont_intg _ ((hcont j i).mul (hcont i j)) (d1_support u hc j i).mul_right
  have c2 : Continuous (fun y => fderiv ℝ (fun x => fderiv ℝ u x) y) :=
    (hu.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)
  have c0 : Continuous u := hu.continuous
  have hint2 : ∀ j i : Fin 3,
      Integrable (fun y => fderiv ℝ (fun x => fderiv ℝ u x) y (unitVector j) (unitVector i) i * u y j) := by
    intro j i
    refine cont_intg _ (by fun_prop) (comp_support u hc j).mul_left
  have step : ∀ j i : Fin 3, ∫ y, fderiv ℝ u y (unitVector j) i * fderiv ℝ u y (unitVector i) j =
      -∫ y, fderiv ℝ (fun x => fderiv ℝ u x) y (unitVector j) (unitVector i) i * u y j := by
    intro j i
    have e : ∀ y, fderiv ℝ u y (unitVector i) j = fderiv ℝ (fun x => u x j) y (unitVector i) :=
      fun y => (fderiv_component u ((hu.differentiable (by simp)) y) j _).symm
    simp_rw [e]
    rw [ibp _ _ i ((d1_smooth u hu j i).of_le one_le_inf) ((comp_smooth u hu j).of_le one_le_inf)
      (d1_support u hc j i)]
    simp_rw [d2_eq u hu, d2_symm u hu _ (unitVector i) (unitVector j)]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => hint j i))]
  apply Finset.sum_eq_zero
  intro j _
  rw [integral_finsetSum _ (fun i _ => hint j i)]
  simp_rw [step]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hint2 j i)]
  simp_rw [← Finset.sum_mul, div_deriv_zero u hu hd]
  simp

theorem sd1_smooth (a : Space → ℝ) (ha : ContDiff ℝ ∞ a) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ a x (unitVector j)) :=
  (ha.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem s_symm (a : Space → ℝ) (ha : ContDiff ℝ ∞ a) (y : Space) (j k : Fin 3) :
    fderiv ℝ (fun x => fderiv ℝ a x (unitVector k)) y (unitVector j) =
      fderiv ℝ (fun x => fderiv ℝ a x (unitVector j)) y (unitVector k) := by
  have hdd : Differentiable ℝ (fun x => fderiv ℝ a x) :=
    (ha.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have h1 := fderiv_clm_left (ContinuousLinearMap.apply ℝ ℝ (unitVector k)) (hdd y)
  have h2 := fderiv_clm_left (ContinuousLinearMap.apply ℝ ℝ (unitVector j)) (hdd y)
  change fderiv ℝ (fun x => (ContinuousLinearMap.apply ℝ ℝ (unitVector k)) (fderiv ℝ a x)) y (unitVector j) =
    fderiv ℝ (fun x => (ContinuousLinearMap.apply ℝ ℝ (unitVector j)) (fderiv ℝ a x)) y (unitVector k)
  rw [h1, h2]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  exact (ha.contDiffAt.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.mpr le_top)) _ _

theorem coord_mul_deriv (g : Space → ℝ) (hg : Differentiable ℝ g) (k j : Fin 3) (y : Space) :
    fderiv ℝ (fun x => x k * g x) y (unitVector j) =
      (unitVector j) k * g y + y k * fderiv ℝ g y (unitVector j) := by
  have hp : HasFDerivAt (fun x : Space => x k) (EuclideanSpace.proj k : Space →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt
  rw [show (fun x : Space => x k * g x) = (fun x : Space => x k) * g from rfl,
    (hp.mul (hg y).hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  change y k * fderiv ℝ g y (unitVector j) + g y * (unitVector j) k = _
  ring

theorem radial_term (g : Space → ℝ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (k : Fin 3) :
    ∫ y, (y k * g y) * fderiv ℝ g y (unitVector k) = -(1 / 2 : ℝ) * ∫ y, g y ^ 2 := by
  have hpc : ContDiff ℝ ∞ (fun x : Space => x k) := by
    have h := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff (n := ∞)
    exact h
  have hf : ContDiff ℝ ∞ (fun x : Space => x k * g x) := hpc.mul hg
  have hfc : HasCompactSupport (fun x : Space => x k * g x) := hc.mul_left
  have hI := ibp (fun x => x k * g x) g k (hf.of_le one_le_inf) (hg.of_le one_le_inf) hfc
  simp_rw [coord_mul_deriv g (hg.differentiable (by simp)) k k] at hI
  have ukk : (unitVector k) k = 1 := by simp [unitVector]
  simp_rw [ukk, one_mul, add_mul] at hI
  have cg : Continuous (fun y => fderiv ℝ g y (unitVector k)) := (sd1_smooth g hg k).continuous
  have i1 : Integrable (fun y => g y * g y) := cont_intg _ (hg.continuous.mul hg.continuous) hc.mul_left
  have i2 : Integrable (fun y => y k * fderiv ℝ g y (unitVector k) * g y) :=
    cont_intg _ ((hpc.continuous.mul cg).mul hg.continuous) hc.mul_left
  rw [integral_add i1 i2] at hI
  have e : ∫ y, y k * fderiv ℝ g y (unitVector k) * g y = ∫ y, (y k * g y) * fderiv ℝ g y (unitVector k) := by
    congr 1; funext y; ring
  have e2 : ∫ y, g y ^ 2 = ∫ y, g y * g y := by congr 1; funext y; ring
  rw [e] at hI
  rw [e2]
  linarith

theorem scalar_transport (a : Space → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (j : Fin 3) :
    ∫ y, ((1 / 2 : ℝ) * a y + (1 / 2 : ℝ) * ∑ k : Fin 3, y k * fderiv ℝ a y (unitVector k)) *
      fderiv ℝ (fun x => fderiv ℝ a x (unitVector j)) y (unitVector j) =
    -(1 / 4 : ℝ) * ∫ y, fderiv ℝ a y (unitVector j) ^ 2 := by
  have hds : ∀ k, ContDiff ℝ ∞ (fun x => fderiv ℝ a x (unitVector k)) := sd1_smooth a ha
  have hdc : ∀ k, HasCompactSupport (fun x => fderiv ℝ a x (unitVector k)) :=
    fun k => hc.fderiv_apply (𝕜 := ℝ) _
  have hpc : ∀ k : Fin 3, ContDiff ℝ ∞ (fun x : Space => x k) := fun k => by
    have h := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff (n := ∞)
    exact h
  have c1 : ∀ k, Continuous (fun x => fderiv ℝ a x (unitVector k)) := fun k => (hds k).continuous
  have c2 : ∀ k l, Continuous (fun y => fderiv ℝ (fun x => fderiv ℝ a x (unitVector k)) y (unitVector l)) :=
    fun k l => (sd1_smooth _ (hds k) l).continuous
  have cp : ∀ k : Fin 3, Continuous (fun x : Space => x k) := fun k => (hpc k).continuous
  have A : ∫ y, a y * fderiv ℝ (fun x => fderiv ℝ a x (unitVector j)) y (unitVector j) =
      -∫ y, fderiv ℝ a y (unitVector j) * fderiv ℝ a y (unitVector j) :=
    ibp a _ j (ha.of_le one_le_inf) ((hds j).of_le one_le_inf) hc
  have B : ∀ k : Fin 3, ∫ y, (y k * fderiv ℝ a y (unitVector k)) *
        fderiv ℝ (fun x => fderiv ℝ a x (unitVector j)) y (unitVector j) =
      -((unitVector j) k * ∫ y, fderiv ℝ a y (unitVector k) * fderiv ℝ a y (unitVector j))
        + (1 / 2 : ℝ) * ∫ y, fderiv ℝ a y (unitVector j) ^ 2 := by
    intro k
    have hI := ibp (fun x => x k * fderiv ℝ a x (unitVector k)) _ j
      (((hpc k).mul (hds k)).of_le one_le_inf) ((hds j).of_le one_le_inf) (hdc k).mul_left
    have e1 : ∀ y, fderiv ℝ (fun x => x k * fderiv ℝ a x (unitVector k)) y (unitVector j) *
        fderiv ℝ a y (unitVector j) =
        (unitVector j) k * (fderiv ℝ a y (unitVector k) * fderiv ℝ a y (unitVector j)) +
          (y k * fderiv ℝ a y (unitVector j)) *
            fderiv ℝ (fun x => fderiv ℝ a x (unitVector j)) y (unitVector k) := by
      intro y
      rw [coord_mul_deriv _ ((hds k).differentiable (by simp)) k j, s_symm a ha y j k]
      ring
    simp_rw [e1] at hI
    have i1 : Integrable (fun y => (unitVector j) k *
        (fderiv ℝ a y (unitVector k) * fderiv ℝ a y (unitVector j))) := by
      have := c1 k; have := c1 j
      exact cont_intg _ (by fun_prop) ((hdc k).mul_right.mul_left)
    have i2 : Integrable (fun y => (y k * fderiv ℝ a y (unitVector j)) *
        fderiv ℝ (fun x => fderiv ℝ a x (unitVector j)) y (unitVector k)) := by
      have := c1 j; have := c2 j k; have := cp k
      exact cont_intg _ (by fun_prop) ((hdc j).mul_left.mul_right)
    rw [integral_add i1 i2, integral_const_mul, radial_term _ (hds j) (hdc j) k] at hI
    rw [hI]
    ring
  have i3 : Integrable (fun y => a y * fderiv ℝ (fun x => fderiv ℝ a x (unitVector j)) y (unitVector j)) := by
    have := c2 j j
    exact cont_intg _ (by fun_prop) hc.mul_right
  have i4 : ∀ k : Fin 3, Integrable (fun y => (y k * fderiv ℝ a y (unitVector k)) *
      fderiv ℝ (fun x => fderiv ℝ a x (unitVector j)) y (unitVector j)) := by
    intro k
    have := c2 j j; have := c1 k; have := cp k
    exact cont_intg _ (by fun_prop) ((hdc k).mul_left.mul_right)
  have e : ∀ y, ((1 / 2 : ℝ) * a y + (1 / 2 : ℝ) * ∑ k : Fin 3, y k * fderiv ℝ a y (unitVector k)) *
      fderiv ℝ (fun x => fderiv ℝ a x (unitVector j)) y (unitVector j) =
      (1 / 2 : ℝ) * (a y * fderiv ℝ (fun x => fderiv ℝ a x (unitVector j)) y (unitVector j)) +
      (1 / 2 : ℝ) * ∑ k : Fin 3, (y k * fderiv ℝ a y (unitVector k)) *
        fderiv ℝ (fun x => fderiv ℝ a x (unitVector j)) y (unitVector j) := by
    intro y
    rw [← Finset.sum_mul]
    ring
  simp_rw [e]
  rw [integral_add (i3.const_mul _) ((integrable_finsetSum _ (fun k _ => i4 k)).const_mul _),
    integral_const_mul, integral_const_mul, integral_finsetSum _ (fun k _ => i4 k), A]
  simp_rw [B]
  have hsum : ∑ k : Fin 3, (unitVector j) k * ∫ y, fderiv ℝ a y (unitVector k) * fderiv ℝ a y (unitVector j) =
      ∫ y, fderiv ℝ a y (unitVector j) ^ 2 := by
    simp [unitVector, sq]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hsum]
  have e2 : ∫ y, fderiv ℝ a y (unitVector j) * fderiv ℝ a y (unitVector j) =
      ∫ y, fderiv ℝ a y (unitVector j) ^ 2 := by
    congr 1; funext y; ring
  rw [e2]
  simp
  ring

theorem curl_sq (G : Space →L[ℝ] Space) :
    ‖curlVec G‖ ^ 2 = ∑ i : Fin 3, ∑ j : Fin 3, (G (unitVector j) i) ^ 2 -
      ∑ j : Fin 3, ∑ i : Fin 3, G (unitVector j) i * G (unitVector i) j := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [curlVec, alternatingSymbol, Fin.sum_univ_three, unitVector]
  ring

theorem inner_coord (a b : Space) : inner ℝ a b = ∑ i : Fin 3, a i * b i := by
  simp [PiLp.inner_apply, mul_comm]

theorem apply_self (L : Space →L[ℝ] Space) (y : Space) (i : Fin 3) :
    L y i = ∑ k : Fin 3, y k * L (unitVector k) i := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr y]
  simp [unitVector, map_sum, map_smul]

theorem swap_ibp (b c : Space → ℝ) (hb : ContDiff ℝ ∞ b) (hc' : ContDiff ℝ ∞ c)
    (hcc : HasCompactSupport c) (j k : Fin 3) :
    ∫ y, fderiv ℝ b y (unitVector j) * fderiv ℝ c y (unitVector k) =
      ∫ y, fderiv ℝ b y (unitVector k) * fderiv ℝ c y (unitVector j) := by
  have h1 := ibp (fun x => fderiv ℝ c x (unitVector k)) b j ((sd1_smooth c hc' k).of_le one_le_inf)
    (hb.of_le one_le_inf) (hcc.fderiv_apply (𝕜 := ℝ) _)
  have h2 := ibp (fun x => fderiv ℝ c x (unitVector j)) b k ((sd1_smooth c hc' j).of_le one_le_inf)
    (hb.of_le one_le_inf) (hcc.fderiv_apply (𝕜 := ℝ) _)
  simp_rw [s_symm c hc' _ j k] at h1
  have e1 : ∫ y, fderiv ℝ b y (unitVector j) * fderiv ℝ c y (unitVector k) =
      ∫ y, fderiv ℝ c y (unitVector k) * fderiv ℝ b y (unitVector j) := by
    congr 1; funext y; ring
  have e2 : ∫ y, fderiv ℝ b y (unitVector k) * fderiv ℝ c y (unitVector j) =
      ∫ y, fderiv ℝ c y (unitVector j) * fderiv ℝ b y (unitVector k) := by
    congr 1; funext y; ring
  rw [e1, e2, h1, h2]

theorem sumSecondPartials_scalar (a : Space → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) :
    ∫ y, (∑ j : Fin 3, fderiv ℝ (fun x => fderiv ℝ a x (unitVector j)) y (unitVector j)) ^ 2 =
      ∑ j : Fin 3, ∑ k : Fin 3, ∫ y, fderiv ℝ (fun x => fderiv ℝ a x (unitVector j)) y (unitVector k) ^ 2 := by
  have hds : ∀ k, ContDiff ℝ ∞ (fun x => fderiv ℝ a x (unitVector k)) := sd1_smooth a ha
  have hdc : ∀ k, HasCompactSupport (fun x => fderiv ℝ a x (unitVector k)) :=
    fun k => hc.fderiv_apply (𝕜 := ℝ) _
  have c2 : ∀ k l, Continuous (fun y => fderiv ℝ (fun x => fderiv ℝ a x (unitVector k)) y (unitVector l)) :=
    fun k l => (sd1_smooth _ (hds k) l).continuous
  have s2 : ∀ k l, HasCompactSupport (fun y => fderiv ℝ (fun x => fderiv ℝ a x (unitVector k)) y (unitVector l)) :=
    fun k l => (hdc k).fderiv_apply (𝕜 := ℝ) _
  have hI : ∀ j k : Fin 3, Integrable (fun y => fderiv ℝ (fun x => fderiv ℝ a x (unitVector j)) y (unitVector j) *
      fderiv ℝ (fun x => fderiv ℝ a x (unitVector k)) y (unitVector k)) :=
    fun j k => cont_intg _ ((c2 j j).mul (c2 k k)) (s2 j j).mul_right
  have e : ∀ y, (∑ j : Fin 3, fderiv ℝ (fun x => fderiv ℝ a x (unitVector j)) y (unitVector j)) ^ 2 =
      ∑ j : Fin 3, ∑ k : Fin 3, fderiv ℝ (fun x => fderiv ℝ a x (unitVector j)) y (unitVector j) *
        fderiv ℝ (fun x => fderiv ℝ a x (unitVector k)) y (unitVector k) := by
    intro y
    rw [sq, Finset.sum_mul_sum]
  simp_rw [e]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hI j k))]
  simp_rw [integral_finsetSum _ (fun k _ => hI _ k)]
  congr 1; funext j; congr 1; funext k
  rw [swap_ibp _ _ (hds j) (hds k) (hdc k) j k]
  congr 1; funext y
  rw [s_symm a ha y j k]
  ring

theorem time_hasDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → Space → E)
    (hF : Differentiable ℝ (fun z : ℝ × Space => F z.1 z.2)) (σ : ℝ) (y : Space) :
    HasDerivAt (fun s => F s y) (fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) (σ, y) (1, 0)) σ := by
  have h := (hF (σ, y)).hasFDerivAt.comp_hasDerivAt σ ((hasDerivAt_id σ).prodMk (hasDerivAt_const σ y))
  simp only [Function.comp_def, id] at h
  exact h

theorem mixed_partial (F : ℝ → Space → ℝ) (hF : ContDiff ℝ ∞ (fun z : ℝ × Space => F z.1 z.2))
    (σ : ℝ) (y : Space) (j : Fin 3) :
    fderiv ℝ (fun x => deriv (fun s => F s x) σ) y (unitVector j) =
      deriv (fun s => fderiv ℝ (F s) y (unitVector j)) σ := by
  have hd : Differentiable ℝ (fun z : ℝ × Space => F z.1 z.2) := hF.differentiable (by simp)
  have h1 : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) z) :=
    hF.fderiv_right (by simp)
  have hdd : Differentiable ℝ (fun z : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) z) :=
    h1.differentiable (by simp)
  have eL : (fun x => deriv (fun s => F s x) σ) = fun x =>
      (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : Space)))
        (fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) (σ, x)) := by
    funext x
    exact (time_hasDeriv F hd σ x).deriv
  have eR : (fun s => fderiv ℝ (F s) y (unitVector j)) = fun s =>
      (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), unitVector j))
        (fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) (s, y)) := by
    funext s
    rw [space_fderiv_eq F hd s y]
    rfl
  rw [eL, eR]
  have hx : DifferentiableAt ℝ (fun x => fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) (σ, x)) y :=
    (hdd.comp (differentiable_const σ |>.prodMk differentiable_id)) y
  rw [fderiv_clm_left _ hx]
  have hs := time_hasDeriv (fun s x => fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) (s, x)) hdd σ y
  have h3 := (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), unitVector j)).hasFDerivAt.comp_hasDerivAt σ hs
  simp only [Function.comp_def] at h3
  rw [h3.deriv]
  rw [space_fderiv_eq (fun s x => fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) (s, x)) hdd σ y]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, ContinuousLinearMap.inr_apply]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.mpr le_top)) _ _

theorem prod_integrable (f : ℝ × Space → ℝ) (hf : Continuous f) (R : ℝ)
    (h : ∀ σ y, R < ‖y‖ → f (σ, y) = 0) :
    Integrable f ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  have hK : IntegrableOn f (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) (volume.prod volume) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall 0 R))
  have hB : Function.support f ⊆ Set.univ ×ˢ Metric.closedBall (0 : Space) R := by
    intro z hz
    refine ⟨trivial, ?_⟩
    by_contra hc
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hc
    exact hz (h z.1 z.2 hc)
  have hm : (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space) =
      (volume.prod volume).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hm, ← integrableOn_iff_integrable_of_support_subset hB, IntegrableOn,
    Measure.restrict_restrict (MeasurableSet.univ.prod Metric.isClosed_closedBall.measurableSet)]
  have e : Set.univ ×ˢ Metric.closedBall (0 : Space) R ∩ Set.Icc (0 : ℝ) 1 ×ˢ Set.univ =
      Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R := by
    ext z
    simp [and_comm]
  rw [e]
  exact hK

theorem period_term (G : ℝ → Space → ℝ) (hG : ContDiff ℝ ∞ (fun z : ℝ × Space => G z.1 z.2))
    (hp : IsTimePeriodic G) (R : ℝ) (hR : ∀ σ y, R < ‖y‖ → G σ y = 0) :
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, deriv (fun s => G s y) σ * G σ y = 0 := by
  have hd : Differentiable ℝ (fun z : ℝ × Space => G z.1 z.2) := hG.differentiable (by simp)
  have ed : ∀ σ y, deriv (fun s => G s y) σ =
      fderiv ℝ (fun z : ℝ × Space => G z.1 z.2) (σ, y) (1, 0) :=
    fun σ y => (time_hasDeriv G hd σ y).deriv
  have hc : Continuous (fun z : ℝ × Space => deriv (fun s => G s z.2) z.1 * G z.1 z.2) := by
    simp only [ed]
    exact ((hG.continuous_fderiv (by simp)).clm_apply continuous_const).mul hG.continuous
  have hint := prod_integrable _ hc R (fun σ y hy => by simp [hR σ y hy])
  rw [integral_integral_swap hint]
  have h0 : ∀ y, ∫ σ in Set.Icc (0 : ℝ) 1, deriv (fun s => G s y) σ * G σ y = 0 := by
    intro y
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    have hder : ∀ σ ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s => G s y * G s y / 2) (deriv (fun s => G s y) σ * G σ y) σ := by
      intro σ _
      have h := time_hasDeriv G hd σ y
      rw [← h.deriv] at h
      exact ((h.mul h).div_const 2).congr_deriv (by ring)
    have hci : Continuous (fun σ => deriv (fun s => G s y) σ * G σ y) :=
      hc.comp (continuous_id.prodMk continuous_const)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hci.intervalIntegrable 0 1)]
    have e1 : G 1 y = G 0 y := by
      have := hp 0 y
      simpa using this
    simp [e1]
  simp [h0]

theorem transport_zero (W₀ : Space → Space) (hW : ContDiff ℝ 1 W₀) (hWd : ∀ y, divergenceAt W₀ y = 0)
    (h : Space → ℝ) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    ∫ y, ∑ k : Fin 3, (W₀ y k * h y) * fderiv ℝ h y (unitVector k) = 0 := by
  have hWk : ∀ k : Fin 3, ContDiff ℝ 1 (fun x => W₀ x k) := fun k => by
    have e := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp hW
    exact e
  have hdW : Differentiable ℝ W₀ := hW.differentiable (by simp)
  have cW : ∀ k : Fin 3, Continuous (fun x => fderiv ℝ (fun x => W₀ x k) x (unitVector k)) :=
    fun k => ((hWk k).continuous_fderiv (by simp)).clm_apply continuous_const
  have chk : ∀ k : Fin 3, Continuous (fun x => fderiv ℝ h x (unitVector k)) :=
    fun k => (sd1_smooth h hh k).continuous
  have i1 : ∀ k : Fin 3, Integrable (fun y => (W₀ y k * h y) * fderiv ℝ h y (unitVector k)) :=
    fun k => cont_intg _ (((hWk k).continuous.mul hh.continuous).mul (chk k)) hc.mul_left.mul_right
  have i2 : ∀ k : Fin 3, Integrable (fun y => fderiv ℝ (fun x => W₀ x k) y (unitVector k) * h y * h y) :=
    fun k => cont_intg _ (((cW k).mul hh.continuous).mul hh.continuous) hc.mul_left.mul_right
  have step : ∀ k : Fin 3, ∫ y, (W₀ y k * h y) * fderiv ℝ h y (unitVector k) =
      -(1 / 2 : ℝ) * ∫ y, fderiv ℝ (fun x => W₀ x k) y (unitVector k) * h y * h y := by
    intro k
    have hf : ContDiff ℝ 1 (fun x => W₀ x k * h x) := (hWk k).mul (hh.of_le one_le_inf)
    have hI := ibp (fun x => W₀ x k * h x) h k hf (hh.of_le one_le_inf) hc.mul_left
    have e : ∀ y, fderiv ℝ (fun x => W₀ x k * h x) y (unitVector k) * h y =
        fderiv ℝ (fun x => W₀ x k) y (unitVector k) * h y * h y +
          (W₀ y k * h y) * fderiv ℝ h y (unitVector k) := by
      intro y
      have hm := ((hWk k).differentiable (by simp) y).hasFDerivAt.mul
        ((hh.differentiable (by simp)) y).hasFDerivAt
      rw [show (fun x => W₀ x k * h x) = (fun x => W₀ x k) * h from rfl, hm.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    simp_rw [e] at hI
    rw [integral_add (i2 k) (i1 k)] at hI
    linarith
  rw [integral_finsetSum _ (fun k _ => i1 k)]
  simp_rw [step]
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun k _ => i2 k)]
  have e2 : ∀ y, ∑ k : Fin 3, fderiv ℝ (fun x => W₀ x k) y (unitVector k) * h y * h y = 0 := by
    intro y
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    have := hWd y
    simp only [divergenceAt] at this
    simp only [fderiv_component W₀ (hdW y)]
    rw [this]
    ring
  simp [e2]

theorem slice_transport (u : Space → Space) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hd : ∀ y, divergenceAt u y = 0) :
    ∫ y, inner ℝ ((1 / 2 : ℝ) • u y + (1 / 2 : ℝ) • fderiv ℝ u y y)
        (-secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ u x) y)) =
      ∫ y, (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ u y)‖ ^ 2 := by
  have h2 : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hdu : Differentiable ℝ u := hu.differentiable (by simp)
  have pt : ∀ y, inner ℝ ((1 / 2 : ℝ) • u y + (1 / 2 : ℝ) • fderiv ℝ u y y)
      (-secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ u x) y)) =
      -∑ i : Fin 3, ∑ j : Fin 3, ((1 / 2 : ℝ) * u y i + (1 / 2 : ℝ) * ∑ k : Fin 3,
        y k * fderiv ℝ (fun x => u x i) y (unitVector k)) *
          fderiv ℝ (fun x => fderiv ℝ (fun z => u z i) x (unitVector j)) y (unitVector j) := by
    intro y
    simp only [fderiv_second_component u h2, fderiv_component u (hdu y)]
    rw [inner_coord]
    simp [secondDerivTrace, Fin.sum_univ_three, apply_self (fderiv ℝ u y) y]
    ring
  simp_rw [pt]
  have hF : ∀ i j : Fin 3, Integrable (fun y => ((1 / 2 : ℝ) * u y i + (1 / 2 : ℝ) * ∑ k : Fin 3,
        y k * fderiv ℝ (fun x => u x i) y (unitVector k)) *
          fderiv ℝ (fun x => fderiv ℝ (fun z => u z i) x (unitVector j)) y (unitVector j)) := by
    intro i j
    have ha := comp_smooth u hu i
    have c1 : ∀ k, Continuous (fun x => fderiv ℝ (fun z => u z i) x (unitVector k)) :=
      fun k => (sd1_smooth _ ha k).continuous
    have c2 := (sd1_smooth _ (sd1_smooth _ ha j) j).continuous
    have c0 := ha.continuous
    have cp : ∀ k : Fin 3, Continuous (fun x : Space => x k) := fun k => by
      have h := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous
      exact h
    have := c1 0; have := c1 1; have := c1 2; have := cp 0; have := cp 1; have := cp 2
    refine cont_intg _ (by fun_prop) ?_
    exact (((comp_support u hc i).fderiv_apply (𝕜 := ℝ) (unitVector j)).fderiv_apply (𝕜 := ℝ)
      (unitVector j)).mul_left
  rw [integral_neg, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hF i j))]
  have hS : ∀ i j : Fin 3, ∫ y, ((1 / 2 : ℝ) * u y i + (1 / 2 : ℝ) * ∑ k : Fin 3,
        y k * fderiv ℝ (fun x => u x i) y (unitVector k)) *
          fderiv ℝ (fun x => fderiv ℝ (fun z => u z i) x (unitVector j)) y (unitVector j) =
      -(1 / 4 : ℝ) * ∫ y, fderiv ℝ u y (unitVector j) i ^ 2 := by
    intro i j
    have h := scalar_transport (fun x => u x i) (comp_smooth u hu i) (comp_support u hc i) j
    simp only [fderiv_component u (hdu _)] at h ⊢
    exact h
  simp_rw [integral_finsetSum _ (fun j _ => hF _ j), hS]
  have hG : ∀ i j : Fin 3, Integrable (fun y => fderiv ℝ u y (unitVector j) i ^ 2) := by
    intro i j
    have cc := (d1_smooth u hu j i).continuous
    simp only [sq]
    exact cont_intg _ (cc.mul cc) (d1_support u hc j i).mul_right
  have hX : Integrable (fun y => ∑ j : Fin 3, ∑ i : Fin 3,
      fderiv ℝ u y (unitVector j) i * fderiv ℝ u y (unitVector i) j) := by
    refine integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => ?_))
    exact cont_intg _ ((d1_smooth u hu j i).continuous.mul (d1_smooth u hu i j).continuous)
      (d1_support u hc j i).mul_right
  simp_rw [curl_sq]
  rw [integral_const_mul, integral_sub (integrable_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => hG i j))) hX, cross_zero u hu hc hd,
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hG i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hG _ j)]
  simp only [Finset.mul_sum, sub_zero]
  simp only [neg_mul, Finset.sum_neg_distrib, neg_neg]

theorem slice_sumSecondPartials (u : Space → Space) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hd : ∀ y, divergenceAt u y = 0) :
    ∫ y, inner ℝ (-secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ u x) y))
        (-secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ u x) y)) =
      ∫ y, matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ u x)) y) := by
  have h2 : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hdd : Differentiable ℝ (fun x => fderiv ℝ u x) :=
    (hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have pt : ∀ y, inner ℝ (-secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ u x) y))
      (-secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ u x) y)) =
      ∑ i : Fin 3, (∑ j : Fin 3, fderiv ℝ (fun x => fderiv ℝ (fun z => u z i) x (unitVector j)) y
        (unitVector j)) ^ 2 := by
    intro y
    simp only [fderiv_second_component u h2]
    rw [inner_coord]
    simp [secondDerivTrace, Fin.sum_univ_three]
    ring
  simp_rw [pt]
  have hL : ∀ i : Fin 3, Integrable (fun y => (∑ j : Fin 3, fderiv ℝ (fun x => fderiv ℝ (fun z => u z i) x
      (unitVector j)) y (unitVector j)) ^ 2) := by
    intro i
    have ha := comp_smooth u hu i
    have s := fun j => ((comp_support u hc i).fderiv_apply (𝕜 := ℝ) (unitVector j)).fderiv_apply (𝕜 := ℝ)
      (unitVector j)
    have cc := fun j => (sd1_smooth _ (sd1_smooth _ ha j) j).continuous
    simp only [Fin.sum_univ_three, sq]
    exact cont_intg _ ((((cc 0).add (cc 1)).add (cc 2)).mul (((cc 0).add (cc 1)).add (cc 2)))
      (((s 0).add (s 1)).add (s 2)).mul_right
  rw [integral_finsetSum _ (fun i _ => hL i)]
  simp_rw [sumSecondPartials_scalar _ (comp_smooth u hu _) (comp_support u hc _)]
  have hB : ∀ (m : Fin 3) y, fderiv ℝ (fun x => fderiv ℝ u x (unitVector m)) y =
      (ContinuousLinearMap.apply ℝ Space (unitVector m)).comp (fderiv ℝ (fun x => fderiv ℝ u x) y) :=
    fun m y => fderiv_clm_left (ContinuousLinearMap.apply ℝ Space (unitVector m)) (hdd y)
  have pt2 : ∀ y, matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ u x)) y) =
      ∑ m : Fin 3, ‖curlVec (fderiv ℝ (fun x => fderiv ℝ u x (unitVector m)) y)‖ ^ 2 := by
    intro y
    have hA : fderiv ℝ (fun x => curlVec (fderiv ℝ u x)) y =
        curlCLM.comp (fderiv ℝ (fun x => fderiv ℝ u x) y) :=
      fderiv_clm_left curlCLM (hdd y)
    simp only [matSq, hA, hB]
    congr 1; funext m
    rw [ContinuousLinearMap.comp_apply, curlCLM_apply]
    congr 3
    refine ContinuousLinearMap.ext (fun w => ?_)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    exact d2_symm u hu y _ _
  simp_rw [pt2, curl_sq]
  have wsm : ∀ m : Fin 3, ContDiff ℝ ∞ (fun x => fderiv ℝ u x (unitVector m)) :=
    fun m => (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have wsp : ∀ m : Fin 3, HasCompactSupport (fun x => fderiv ℝ u x (unitVector m)) :=
    fun m => hc.fderiv_apply (𝕜 := ℝ) _
  have wdv : ∀ (m : Fin 3) y, divergenceAt (fun x => fderiv ℝ u x (unitVector m)) y = 0 := by
    intro m y
    simp only [divergenceAt, hB, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    simp_rw [d2_symm u hu y _ (unitVector m)]
    exact div_deriv_zero u hu hd y m
  have hG : ∀ (m i j : Fin 3), Integrable (fun y => fderiv ℝ (fun x => fderiv ℝ u x (unitVector m)) y
      (unitVector j) i ^ 2) := by
    intro m i j
    have cc := (d1_smooth _ (wsm m) j i).continuous
    simp only [sq]
    exact cont_intg _ (cc.mul cc) (d1_support _ (wsp m) j i).mul_right
  have hX : ∀ m : Fin 3, Integrable (fun y => ∑ j : Fin 3, ∑ i : Fin 3,
      fderiv ℝ (fun x => fderiv ℝ u x (unitVector m)) y (unitVector j) i *
        fderiv ℝ (fun x => fderiv ℝ u x (unitVector m)) y (unitVector i) j) := by
    intro m
    refine integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => ?_))
    exact cont_intg _ ((d1_smooth _ (wsm m) j i).continuous.mul (d1_smooth _ (wsm m) i j).continuous)
      (d1_support _ (wsp m) j i).mul_right
  have hR : ∀ m : Fin 3, Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ (fun x => fderiv ℝ u x (unitVector m)) y (unitVector j) i ^ 2 -
      ∑ j : Fin 3, ∑ i : Fin 3, fderiv ℝ (fun x => fderiv ℝ u x (unitVector m)) y (unitVector j) i *
        fderiv ℝ (fun x => fderiv ℝ u x (unitVector m)) y (unitVector i) j) :=
    fun m => (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hG m i j))).sub (hX m)
  rw [integral_finsetSum _ (fun m _ => hR m)]
  simp_rw [integral_sub (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hG _ i j)))
    (hX _), cross_zero _ (wsm _) (wsp _) (wdv _), sub_zero]
  simp_rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hG _ i j)),
    integral_finsetSum _ (fun j _ => hG _ _ j)]
  simp_rw [fderiv_second_component u h2, hB, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply]
  simp only [Fin.sum_univ_three]
  ring

end EnergyIdentityInternal

end Coercive

end Breakdown
