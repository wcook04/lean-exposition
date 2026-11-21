import Breakdown.FracCell.GivenAuxAdjointCore

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

namespace AdjointInternal

open AdjointCoreInternal

theorem turn_zero (m : ℕ) : turnStep m 0 = 0 := by
  ext i
  fin_cases i <;> simp [turnStep]

theorem mirror_zero' : mirror 0 = 0 := by
  ext i
  fin_cases i <;> simp [mirror]

theorem turn_add (m : ℕ) (a b : Space) : turnStep m (a + b) = turnStep m a + turnStep m b := by
  ext i
  fin_cases i <;> simp [turnStep] <;> ring

theorem mirror_add' (a b : Space) : mirror (a + b) = mirror a + mirror b := by
  ext i
  fin_cases i <;> simp [mirror]
  ring

theorem turn_smul (m : ℕ) (r : ℝ) (a : Space) : turnStep m (r • a) = r • turnStep m a := by
  ext i
  fin_cases i <;> simp [turnStep] <;> ring

theorem mirror_smul' (r : ℝ) (a : Space) : mirror (r • a) = r • mirror a := by
  ext i
  fin_cases i <;> simp [mirror]

theorem loc_two {E : Type} [NormedAddCommGroup E] {f : Space → E} (h : MemLp f 2 volume) :
    LocallyIntegrable f volume :=
  h.locallyIntegrable (by norm_num)

theorem test_deriv_cont {φ : Space → ℝ} (hφ : IsTestScalar φ) (j : Fin 3) :
    Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
  (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const

theorem test_deriv_supp {φ : Space → ℝ} (hφ : IsTestScalar φ) (j : Fin 3) :
    HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
  hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector j)

theorem grad_cont {φ : Space → ℝ} (hφ : IsTestScalar φ) : Continuous (fun y => gradientAt φ y) := by
  unfold gradientAt
  exact continuous_finsetSum _ fun i _ => (test_deriv_cont hφ i).smul continuous_const

theorem grad_supp {φ : Space → ℝ} (hφ : IsTestScalar φ) : HasCompactSupport (fun y => gradientAt φ y) := by
  have h : (fun y => gradientAt φ y) =
      (fun L : Space →L[ℝ] ℝ => ∑ i : Fin 3, L (unitVector i) • unitVector i) ∘ fderiv ℝ φ := by
    funext y
    rfl
  rw [h]
  exact (hφ.2.fderiv (𝕜 := ℝ)).comp_left (by simp)

theorem inner_integrable {g : Space → Space} (hg : MemLp g 2 volume) {φ : Space → ℝ} (hφ : IsTestScalar φ) :
    Integrable (fun y => inner ℝ (g y) (gradientAt φ y)) := by
  have hloc : LocallyIntegrable (fun y => ‖g y‖) volume := loc_two hg.norm
  have hb : Integrable (fun y => ‖gradientAt φ y‖ • ‖g y‖) :=
    hloc.integrable_smul_left_of_hasCompactSupport (grad_cont hφ).norm (grad_supp hφ).norm
  refine hb.mono' (hg.1.inner (grad_cont hφ).aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_)
  rw [smul_eq_mul, Real.norm_eq_abs, mul_comm]
  exact abs_real_inner_le_norm _ _

theorem weak_of_C1 {v : Space → Space} (hv : ContDiff ℝ 1 v) : IsWeakGradientOf v (fun y => fderiv ℝ v y) := by
  intro φ hφ j
  obtain ⟨hs, hc⟩ := hφ
  have hφ1 : Differentiable ℝ φ := hs.differentiable (by simp)
  have hv1 : Differentiable ℝ v := hv.differentiable one_ne_zero
  have cφ' : Continuous fun y => fderiv ℝ φ y (unitVector j) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  have cv' : Continuous fun y => fderiv ℝ v y (unitVector j) :=
    (hv.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • v y) :=
    (cφ'.smul hv.continuous).integrable_of_hasCompactSupport
      ((hc.fderiv_apply (𝕜 := ℝ) (unitVector j)).smul_right)
  have i2 : Integrable (fun y => φ y • fderiv ℝ v y (unitVector j)) :=
    (hs.continuous.smul cv').integrable_of_hasCompactSupport hc.smul_right
  have i3 : Integrable (fun y => φ y • v y) :=
    (hs.continuous.smul hv.continuous).integrable_of_hasCompactSupport hc.smul_right
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable i1 i2 i3
    (fun y _ => hφ1 y) (fun y _ => hv1 y)
  rw [h, neg_neg]

theorem sol_of_div {g : Space → Space} (hc : ContDiff ℝ 1 g) (hdiv : ∀ y, divergenceAt g y = 0) :
    ∀ φ : Space → ℝ, IsTestScalar φ → ∫ y, inner ℝ (g y) (gradientAt φ y) = 0 := by
  intro φ hφ
  have hw := weak_of_C1 hc φ hφ
  have cD : ∀ i, Continuous (fun y => fderiv ℝ g y (unitVector i)) := fun i =>
    (hc.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have ii : ∀ i, Integrable (fun y => fderiv ℝ φ y (unitVector i) • g y) := fun i =>
    ((test_deriv_cont hφ i).smul hc.continuous).integrable_of_hasCompactSupport (test_deriv_supp hφ i).smul_right
  have jj : ∀ i, Integrable (fun y => φ y • fderiv ℝ g y (unitVector i)) := fun i =>
    (hφ.1.continuous.smul (cD i)).integrable_of_hasCompactSupport hφ.2.smul_right
  have e : (fun y => inner ℝ (g y) (gradientAt φ y)) =
      fun y => ∑ i : Fin 3, inner ℝ (unitVector i) (fderiv ℝ φ y (unitVector i) • g y) := by
    funext y
    simp only [gradientAt, inner_sum, inner_smul_right, real_inner_comm]
  have e2 : ∀ y, ∑ i : Fin 3, inner ℝ (unitVector i) (φ y • fderiv ℝ g y (unitVector i)) =
      φ y * divergenceAt g y := by
    intro y
    simp [divergenceAt, unitVector, inner_smul_right, Finset.mul_sum, EuclideanSpace.inner_single_left]
  calc ∫ y, inner ℝ (g y) (gradientAt φ y)
      = ∑ i : Fin 3, ∫ y, inner ℝ (unitVector i) (fderiv ℝ φ y (unitVector i) • g y) := by
        rw [e, integral_finset_sum]
        exact fun i _ => Integrable.const_inner (𝕜 := ℝ) (unitVector i) (ii i)
    _ = ∑ i : Fin 3, inner ℝ (unitVector i) (∫ y, fderiv ℝ φ y (unitVector i) • g y) :=
        Finset.sum_congr rfl fun i _ => integral_inner (ii i) _
    _ = ∑ i : Fin 3, -∫ y, inner ℝ (unitVector i) (φ y • fderiv ℝ g y (unitVector i)) :=
        Finset.sum_congr rfl fun i _ => by rw [hw i, inner_neg_right, integral_inner (jj i)]
    _ = -∫ y, ∑ i : Fin 3, inner ℝ (unitVector i) (φ y • fderiv ℝ g y (unitVector i)) := by
        rw [integral_finset_sum, Finset.sum_neg_distrib]
        exact fun i _ => Integrable.const_inner (𝕜 := ℝ) (unitVector i) (jj i)
    _ = 0 := by simp [e2, hdiv]

theorem weak_of_slope {g : Space → Space} {K : NNReal} (hg : LipschitzWith K g) {φ : Space → ℝ}
    (hφ : IsTestScalar φ) (v : Space) :
    ∫ y, fderiv ℝ φ y v • g y = -∫ y, φ y • fderiv ℝ g y v := by
  obtain ⟨Kφ, hφL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφ.2 hφ.1 (by simp)
  have hφd : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have hgd : ∀ᵐ y ∂volume, DifferentiableAt ℝ g y := hg.ae_differentiableAt
  have hI1 : Integrable (fun y => fderiv ℝ φ y v • g y) :=
    (((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const).smul hg.continuous).integrable_of_hasCompactSupport
      (hφ.2.fderiv_apply (𝕜 := ℝ) v).smul_right
  have hb : MemLp (fun y => fderiv ℝ g y v) ⊤ volume := by
    refine memLp_top_of_bound (measurable_fderiv_apply_const ℝ g v).aestronglyMeasurable (K * ‖v‖)
      (Filter.Eventually.of_forall fun y => ?_)
    exact (fderiv ℝ g y).le_of_opNorm_le (norm_fderiv_le_of_lipschitz ℝ hg) v
  have hI2 : Integrable (fun y => φ y • fderiv ℝ g y v) :=
    (hb.locallyIntegrable le_top).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
  have key : ∀ c : Fin 3, ∫ y, fderiv ℝ φ y v * g y c = -∫ y, φ y * fderiv ℝ g y v c := by
    intro c
    have hgc : LipschitzWith _ (fun y => (EuclideanSpace.proj c : Space →L[ℝ] ℝ) (g y)) :=
      (EuclideanSpace.proj c : Space →L[ℝ] ℝ).lipschitz.comp hg
    have R := hgc.integral_lineDeriv_mul_eq (μ := volume) hφL hφ.2 v
    have h1 : (fun x => lineDeriv ℝ φ x (-v) * (EuclideanSpace.proj c : Space →L[ℝ] ℝ) (g x)) =
        fun x => -(fderiv ℝ φ x v * g x c) := by
      funext x
      rw [lineDeriv_neg, (hφd x).lineDeriv_eq_fderiv]
      simp
    have h2 : (fun x => lineDeriv ℝ (fun y => (EuclideanSpace.proj c : Space →L[ℝ] ℝ) (g y)) x v * φ x) =ᵐ[volume]
        fun x => φ x * fderiv ℝ g x v c := by
      filter_upwards [hgd] with x hx
      have hd : HasFDerivAt (fun y => (EuclideanSpace.proj c : Space →L[ℝ] ℝ) (g y))
          ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).comp (fderiv ℝ g x)) x :=
        (EuclideanSpace.proj c : Space →L[ℝ] ℝ).hasFDerivAt.comp x hx.hasFDerivAt
      rw [(hd.hasLineDerivAt v).lineDeriv, mul_comm]
      simp
    rw [h1, integral_congr_ae h2, integral_neg] at R
    rw [R, neg_neg]
  ext c
  have e1 := (EuclideanSpace.proj c : Space →L[ℝ] ℝ).integral_comp_comm hI1
  have e2 := (EuclideanSpace.proj c : Space →L[ℝ] ℝ).integral_comp_comm hI2
  simp only [EuclideanSpace.proj] at e1 e2
  simp at e1 e2 ⊢
  rw [← e1, ← e2]
  simpa [smul_eq_mul] using key c

theorem weakSecond_of_slope {G : Space → (Space →L[ℝ] Space)} {K : NNReal} (hG : LipschitzWith K G) :
    IsWeakSecondDerivOf G (fderiv ℝ G) := by
  intro φ hφ i j
  have hGd : ∀ᵐ y ∂volume, DifferentiableAt ℝ G y := hG.ae_differentiableAt
  have hl : LipschitzWith _ (fun y => (ContinuousLinearMap.apply ℝ Space (unitVector i)) (G y)) :=
    (ContinuousLinearMap.apply ℝ Space (unitVector i)).lipschitz.comp hG
  have h := weak_of_slope hl hφ (unitVector j)
  simp only [ContinuousLinearMap.apply_apply] at h
  rw [h]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hGd] with y hy
  have hd := (ContinuousLinearMap.apply ℝ Space (unitVector i)).hasFDerivAt.comp y hy.hasFDerivAt
  have e : fderiv ℝ (fun y => (G y) (unitVector i)) y =
      (ContinuousLinearMap.apply ℝ Space (unitVector i)).comp (fderiv ℝ G y) := hd.fderiv
  rw [e]
  simp

theorem memLp_of_decay {E : Type} [NormedAddCommGroup E] {f : Space → E} (hf : AEStronglyMeasurable f volume)
    {C a : ℝ} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (ha : 3 < a * p.toReal)
    (hb : ∀ᵐ y ∂volume, ‖f y‖ ≤ C * (1 + ‖y‖) ^ (-a)) : MemLp f p volume := by
  rw [← integrable_norm_rpow_iff hf hp0 hpt]
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hi : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(a * p.toReal))) volume :=
    integrable_one_add_norm (by simpa [finrank_euclideanSpace] using ha)
  refine (hi.const_mul (|C| ^ p.toReal)).mono' (hf.norm.aemeasurable.pow_const _).aestronglyMeasurable ?_
  filter_upwards [hb] with y hy
  have h1 : 0 < 1 + ‖y‖ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  calc ‖f y‖ ^ p.toReal ≤ (|C| * (1 + ‖y‖) ^ (-a)) ^ p.toReal := by
        refine Real.rpow_le_rpow (norm_nonneg _) (hy.trans ?_) hq.le
        exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg h1.le _)
    _ = |C| ^ p.toReal * (1 + ‖y‖) ^ (-(a * p.toReal)) := by
        rw [Real.mul_rpow (abs_nonneg C) (Real.rpow_nonneg h1.le _), ← Real.rpow_mul h1.le, neg_mul]

theorem weight_le (y : Space) (k : ℕ) (a : ℝ) :
    ‖y‖ ^ k * (1 + ‖y‖) ^ (-a) ≤ (1 + ‖y‖) ^ (-(a - k)) := by
  have h1 : 0 < 1 + ‖y‖ := by positivity
  calc ‖y‖ ^ k * (1 + ‖y‖) ^ (-a) ≤ (1 + ‖y‖) ^ k * (1 + ‖y‖) ^ (-a) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg h1.le _)
        exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) k
    _ = (1 + ‖y‖) ^ (-(a - k)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add h1]
        ring_nf

theorem unit_norm (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

structure GoodField (m : ℕ) (g : Space → Space) : Prop where
  cd : ContDiff ℝ 1 g
  d2 : ∀ᵐ y ∂volume, DifferentiableAt ℝ (fderiv ℝ g) y
  l2 : MemLp g 2 volume
  l3 : MemLp g 3 volume
  w1 : MemLp (fun y => ‖y‖ • g y) 2 volume
  g2 : ∀ i, MemLp (fun y => fderiv ℝ g y (unitVector i)) 2 volume
  gw : ∀ i, MemLp (fun y => ‖y‖ ^ 2 • fderiv ℝ g y (unitVector i)) 2 volume
  h2 : ∀ a b, MemLp (fun y => fderiv ℝ (fderiv ℝ g) y (unitVector a) (unitVector b)) 2 volume
  ws : IsWeakSecondDerivOf (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g))
  sol : ∀ φ : Space → ℝ, IsTestScalar φ → ∫ y, inner ℝ (g y) (gradientAt φ y) = 0
  cls : ∀ y, g (turnStep m y) = turnStep m (g y) ∧ g (mirror y) = mirror (g y)

theorem good_zero (m : ℕ) : GoodField m (0 : Space → Space) := by
  have hF : fderiv ℝ (0 : Space → Space) = 0 := fderiv_zero
  have hH : fderiv ℝ (fderiv ℝ (0 : Space → Space)) = 0 := by rw [hF]; exact fderiv_zero
  refine ⟨contDiff_const, Filter.Eventually.of_forall fun y => ?_, MemLp.zero, MemLp.zero, ?_, fun i => ?_,
    fun i => ?_, fun a b => ?_, ?_, ?_, fun y => ?_⟩
  · rw [hF]; exact differentiableAt_const _
  · simpa using (MemLp.zero : MemLp (0 : Space → Space) 2 volume)
  · simpa [hF] using (MemLp.zero : MemLp (0 : Space → Space) 2 volume)
  · simpa [hF] using (MemLp.zero : MemLp (0 : Space → Space) 2 volume)
  · simpa [hH] using (MemLp.zero : MemLp (0 : Space → Space) 2 volume)
  · intro φ hφ i j
    simp [hF, hH]
  · intro φ hφ
    simp
  · simp [turn_zero, mirror_zero']

theorem good_add {m : ℕ} {g h : Space → Space} (hg : GoodField m g) (hh : GoodField m h) :
    GoodField m (g + h) := by
  have hdg : ∀ y, DifferentiableAt ℝ g y := fun y => hg.cd.differentiable one_ne_zero y
  have hdh : ∀ y, DifferentiableAt ℝ h y := fun y => hh.cd.differentiable one_ne_zero y
  have hF : fderiv ℝ (g + h) = fderiv ℝ g + fderiv ℝ h := by
    funext y
    show fderiv ℝ (fun z => g z + h z) y = _
    exact fderiv_add (hdg y) (hdh y)
  have hHae : fderiv ℝ (fderiv ℝ (g + h)) =ᵐ[volume] fderiv ℝ (fderiv ℝ g) + fderiv ℝ (fderiv ℝ h) := by
    filter_upwards [hg.d2, hh.d2] with y h1 h2
    rw [hF]
    show fderiv ℝ (fun z => fderiv ℝ g z + fderiv ℝ h z) y = _
    exact fderiv_add h1 h2
  have cg : ∀ i, Continuous (fun y => fderiv ℝ g y (unitVector i)) := fun i =>
    (hg.cd.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have ch : ∀ i, Continuous (fun y => fderiv ℝ h y (unitVector i)) := fun i =>
    (hh.cd.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine ⟨hg.cd.add hh.cd, ?_, hg.l2.add hh.l2, hg.l3.add hh.l3, ?_, fun i => ?_, fun i => ?_, fun a b => ?_, ?_, ?_,
    fun y => ?_⟩
  · rw [hF]
    filter_upwards [hg.d2, hh.d2] with y h1 h2
    exact h1.add h2
  · exact (hg.w1.add hh.w1).ae_eq (Filter.Eventually.of_forall fun y => by simp [smul_add])
  · exact ((hg.g2 i).add (hh.g2 i)).ae_eq (Filter.Eventually.of_forall fun y => by simp [hF])
  · exact ((hg.gw i).add (hh.gw i)).ae_eq (Filter.Eventually.of_forall fun y => by simp [hF, smul_add])
  · refine ((hg.h2 a b).add (hh.h2 a b)).ae_eq ?_
    filter_upwards [hHae] with y hy
    simp [hy]
  · intro φ hφ i j
    have e1 : (fun y => fderiv ℝ φ y (unitVector j) • fderiv ℝ (g + h) y (unitVector i)) =
        fun y => fderiv ℝ φ y (unitVector j) • fderiv ℝ g y (unitVector i) +
          fderiv ℝ φ y (unitVector j) • fderiv ℝ h y (unitVector i) := by
      funext y
      simp [hF, smul_add]
    have e2 : (fun y => φ y • fderiv ℝ (fderiv ℝ (g + h)) y (unitVector j) (unitVector i)) =ᵐ[volume]
        fun y => φ y • fderiv ℝ (fderiv ℝ g) y (unitVector j) (unitVector i) +
          φ y • fderiv ℝ (fderiv ℝ h) y (unitVector j) (unitVector i) := by
      filter_upwards [hHae] with y hy
      simp [hy, smul_add]
    have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • fderiv ℝ g y (unitVector i)) :=
      ((test_deriv_cont hφ j).smul (cg i)).integrable_of_hasCompactSupport (test_deriv_supp hφ j).smul_right
    have i2 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • fderiv ℝ h y (unitVector i)) :=
      ((test_deriv_cont hφ j).smul (ch i)).integrable_of_hasCompactSupport (test_deriv_supp hφ j).smul_right
    have i3 : Integrable (fun y => φ y • fderiv ℝ (fderiv ℝ g) y (unitVector j) (unitVector i)) :=
      (loc_two (hg.h2 j i)).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    have i4 : Integrable (fun y => φ y • fderiv ℝ (fderiv ℝ h) y (unitVector j) (unitVector i)) :=
      (loc_two (hh.h2 j i)).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    rw [e1, integral_congr_ae e2, integral_add i1 i2, integral_add i3 i4, hg.ws φ hφ i j, hh.ws φ hφ i j, neg_add]
  · intro φ hφ
    have e : (fun y => inner ℝ ((g + h) y) (gradientAt φ y)) =
        fun y => inner ℝ (g y) (gradientAt φ y) + inner ℝ (h y) (gradientAt φ y) := by
      funext y
      simp [inner_add_left]
    rw [e, integral_add (inner_integrable hg.l2 hφ) (inner_integrable hh.l2 hφ), hg.sol φ hφ, hh.sol φ hφ, add_zero]
  · simp [(hg.cls y).1, (hh.cls y).1, (hg.cls y).2, (hh.cls y).2, turn_add, mirror_add']

theorem good_smul {m : ℕ} (c : ℝ) {g : Space → Space} (hg : GoodField m g) : GoodField m (c • g) := by
  have hdg : ∀ y, DifferentiableAt ℝ g y := fun y => hg.cd.differentiable one_ne_zero y
  have hF : fderiv ℝ (c • g) = c • fderiv ℝ g := by
    funext y
    show fderiv ℝ (fun z => c • g z) y = _
    exact fderiv_const_smul (hdg y) c
  have hHae : fderiv ℝ (fderiv ℝ (c • g)) =ᵐ[volume] c • fderiv ℝ (fderiv ℝ g) := by
    filter_upwards [hg.d2] with y h1
    rw [hF]
    show fderiv ℝ (fun z => c • fderiv ℝ g z) y = _
    exact fderiv_const_smul h1 c
  refine ⟨hg.cd.const_smul c, ?_, hg.l2.const_smul c, hg.l3.const_smul c, ?_, fun i => ?_, fun i => ?_,
    fun a b => ?_, ?_, ?_, fun y => ?_⟩
  · rw [hF]
    filter_upwards [hg.d2] with y h1
    exact h1.const_smul c
  · exact (hg.w1.const_smul c).ae_eq (Filter.Eventually.of_forall fun y => by simp [smul_comm c])
  · exact ((hg.g2 i).const_smul c).ae_eq (Filter.Eventually.of_forall fun y => by simp [hF])
  · exact ((hg.gw i).const_smul c).ae_eq (Filter.Eventually.of_forall fun y => by simp [hF, smul_comm c])
  · refine ((hg.h2 a b).const_smul c).ae_eq ?_
    filter_upwards [hHae] with y hy
    simp [hy]
  · intro φ hφ i j
    have e1 : (fun y => fderiv ℝ φ y (unitVector j) • fderiv ℝ (c • g) y (unitVector i)) =
        fun y => c • (fderiv ℝ φ y (unitVector j) • fderiv ℝ g y (unitVector i)) := by
      funext y
      simp [hF, smul_comm c]
    have e2 : (fun y => φ y • fderiv ℝ (fderiv ℝ (c • g)) y (unitVector j) (unitVector i)) =ᵐ[volume]
        fun y => c • (φ y • fderiv ℝ (fderiv ℝ g) y (unitVector j) (unitVector i)) := by
      filter_upwards [hHae] with y hy
      simp [hy, smul_comm c]
    rw [e1, integral_congr_ae e2, integral_smul, integral_smul, hg.ws φ hφ i j, smul_neg]
  · intro φ hφ
    have e : (fun y => inner ℝ ((c • g) y) (gradientAt φ y)) =
        fun y => c * inner ℝ (g y) (gradientAt φ y) := by
      funext y
      simp [real_inner_smul_left]
    rw [e, integral_const_mul, hg.sol φ hφ, mul_zero]
  · simp [(hg.cls y).1, (hg.cls y).2, turn_smul, mirror_smul']

theorem good_field (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D) (β : ℝ) :
    GoodField P.m (fieldOf P D β) := by
  have hc := field_contDiff P hP D hD β
  obtain ⟨C0, h0⟩ := field_decay P hP D hD β
  obtain ⟨C1, h1⟩ := field_gradDecay P hP D hD β
  obtain ⟨C2, h2⟩ := field_secondDecay P hP D hD β
  have hm : AEStronglyMeasurable (fieldOf P D β) volume := hc.continuous.aestronglyMeasurable
  have hcol : ∀ i, AEStronglyMeasurable (fun y => fderiv ℝ (fieldOf P D β) y (unitVector i)) volume := fun i =>
    (measurable_fderiv_apply_const ℝ _ _).aestronglyMeasurable
  have hcb : ∀ i y, ‖fderiv ℝ (fieldOf P D β) y (unitVector i)‖ ≤ C1 * (1 + ‖y‖) ^ (-(4 : ℝ)) := fun i y => by
    have := (fderiv ℝ (fieldOf P D β) y).le_opNorm (unitVector i)
    rw [unit_norm, mul_one] at this
    exact this.trans (h1 y)
  have hC1 : 0 ≤ C1 := by
    have := (norm_nonneg _).trans (h1 0)
    simpa using this
  refine ⟨hc, (field_gradSlope P hP D hD β).choose_spec.ae_differentiableAt, ?_, ?_, ?_, fun i => ?_, fun i => ?_,
    fun a b => ?_, weakSecond_of_slope (field_gradSlope P hP D hD β).choose_spec,
    sol_of_div hc (field_divergence P hP D hD β), field_class P hP D hD β⟩
  · exact memLp_of_decay hm (by norm_num) (by norm_num) (by norm_num) (Filter.Eventually.of_forall h0)
  · exact memLp_of_decay hm (by norm_num) (by norm_num) (by norm_num) (Filter.Eventually.of_forall h0)
  · have hC0 : 0 ≤ C0 := by
      have := (norm_nonneg _).trans (h0 0)
      simpa using this
    refine memLp_of_decay (f := fun y => ‖y‖ • fieldOf P D β y) (a := 2) (C := C0)
      (continuous_norm.smul hc.continuous).aestronglyMeasurable
      (by norm_num) (by norm_num) (by norm_num) (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_smul, norm_norm]
    calc ‖y‖ * ‖fieldOf P D β y‖ ≤ ‖y‖ * (C0 * (1 + ‖y‖) ^ (-(3 : ℝ))) :=
          mul_le_mul_of_nonneg_left (h0 y) (norm_nonneg _)
      _ = C0 * (‖y‖ ^ 1 * (1 + ‖y‖) ^ (-(3 : ℝ))) := by ring
      _ ≤ C0 * (1 + ‖y‖) ^ (-((3 : ℝ) - (1 : ℕ))) := mul_le_mul_of_nonneg_left (weight_le y 1 3) hC0
      _ = C0 * (1 + ‖y‖) ^ (-(2 : ℝ)) := by norm_num
  · exact memLp_of_decay (hcol i) (by norm_num) (by norm_num) (by norm_num) (Filter.Eventually.of_forall (hcb i))
  · have hw : AEStronglyMeasurable (fun y => ‖y‖ ^ 2 • fderiv ℝ (fieldOf P D β) y (unitVector i)) volume :=
      ((continuous_norm.pow 2).measurable.smul (measurable_fderiv_apply_const ℝ _ _)).aestronglyMeasurable
    refine memLp_of_decay (f := fun y => ‖y‖ ^ 2 • fderiv ℝ (fieldOf P D β) y (unitVector i)) (a := 2) (C := C1) hw
      (by norm_num) (by norm_num) (by norm_num) (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_smul, norm_pow, norm_norm]
    calc ‖y‖ ^ 2 * ‖fderiv ℝ (fieldOf P D β) y (unitVector i)‖ ≤ ‖y‖ ^ 2 * (C1 * (1 + ‖y‖) ^ (-(4 : ℝ))) :=
          mul_le_mul_of_nonneg_left (hcb i y) (by positivity)
      _ = C1 * (‖y‖ ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ))) := by ring
      _ ≤ C1 * (1 + ‖y‖) ^ (-((4 : ℝ) - (2 : ℕ))) := mul_le_mul_of_nonneg_left (weight_le y 2 4) hC1
      _ = C1 * (1 + ‖y‖) ^ (-(2 : ℝ)) := by norm_num
  · have hsm : AEStronglyMeasurable
        (fun y => fderiv ℝ (fderiv ℝ (fieldOf P D β)) y (unitVector a) (unitVector b)) volume :=
      ((ContinuousLinearMap.apply ℝ Space (unitVector b)).continuous.measurable.comp
        (measurable_fderiv_apply_const ℝ (fderiv ℝ (fieldOf P D β)) (unitVector a))).aestronglyMeasurable
    refine memLp_of_decay (a := 5) (C := C2) hsm (by norm_num) (by norm_num) (by norm_num) ?_
    filter_upwards [h2] with y hy
    have := (fderiv ℝ (fderiv ℝ (fieldOf P D β)) y).le_opNorm₂ (unitVector a) (unitVector b)
    rw [unit_norm, unit_norm, mul_one, mul_one] at this
    exact this.trans hy

theorem atom_two (P : ChartParams) (hP : IsChartParams P) (X : AtomData) (hX : IsAtomData P X) (β : ℝ) :
    MemLp (atomOf P X β) 2 volume := by
  obtain ⟨hm, C, hC⟩ := atom_bound P hP X hX β
  exact memLp_of_decay hm (by norm_num) (by norm_num) (by norm_num) (Filter.Eventually.of_forall hC)

theorem good_adjoint (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (j : Fin k) (p : Fin k → ℝ) : GoodField P.m (A.adjointField P j p) := by
  have h : A.adjointField P j p = ∑ γ ∈ (A.adjointFamily j).indices,
      multiPow γ p • fieldOf P ((A.adjointFamily j).coef γ) (A.phase p) := by
    funext y
    simp [AuxData.adjointField, FieldFamily.eval, Finset.sum_apply]
  rw [h]
  exact Finset.sum_induction _ (GoodField P.m) (fun a b ha hb => good_add ha hb) (good_zero P.m)
    (fun γ hγ => good_smul _ (good_field P hP _ (hA.adjoint_shape j γ hγ) _))

theorem regular_of_good {m : ℕ} {g : Space → Space} (hg : GoodField m g) :
    Reduction.IsAdjointRegular g (fun y => fderiv ℝ g y) (fun y => fderiv ℝ (fun z => fderiv ℝ g z) y) := by
  refine ⟨hg.l2, hg.l3, hg.w1, (measurable_fderiv ℝ g).aestronglyMeasurable, weak_of_C1 hg.cd, ?_, ?_,
    (measurable_fderiv ℝ _).aestronglyMeasurable, hg.ws, ?_⟩
  · simp only [entrySq]
    exact integrable_finsetSum _ fun i _ => (memLp_two_iff_integrable_sq_norm (hg.g2 i).1).mp (hg.g2 i)
  · have e : (fun y => ‖y‖ ^ 4 * entrySq (fderiv ℝ g y)) =
        fun y => ∑ i : Fin 3, ‖‖y‖ ^ 2 • fderiv ℝ g y (unitVector i)‖ ^ 2 := by
      funext y
      simp only [entrySq]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_smul, norm_pow, norm_norm]
      ring
    rw [e]
    exact integrable_finsetSum _ fun i _ => (memLp_two_iff_integrable_sq_norm (hg.gw i).1).mp (hg.gw i)
  · simp only [fullSecondSq]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      (memLp_two_iff_integrable_sq_norm (hg.h2 a b).1).mp (hg.h2 a b)

structure GoodScalar (q : Space → ℝ) : Prop where
  l2 : MemLp q 2 volume
  d : ∀ᵐ y ∂volume, DifferentiableAt ℝ q y
  li : LocallyIntegrable (fun y => gradientAt q y) volume
  wg : Reduction.IsWeakScalarGradientOf q (fun y => gradientAt q y)
  w : MemLp (fun y => ‖y‖ • gradientAt q y) 2 volume
  b : ∃ C : ℝ, ∀ᵐ y ∂volume, ‖gradientAt q y‖ ≤ C * min (‖y‖⁻¹) (‖y‖ ^ (-(3 : ℝ)))

theorem min_nonneg' (y : Space) : 0 ≤ min (‖y‖⁻¹) (‖y‖ ^ (-(3 : ℝ))) :=
  le_min (inv_nonneg.mpr (norm_nonneg _)) (Real.rpow_nonneg (norm_nonneg _) _)

theorem gradientAt_add {q r : Space → ℝ} {y : Space} (hq : DifferentiableAt ℝ q y) (hr : DifferentiableAt ℝ r y) :
    gradientAt (q + r) y = gradientAt q y + gradientAt r y := by
  unfold gradientAt
  have : fderiv ℝ (q + r) y = fderiv ℝ q y + fderiv ℝ r y := by
    show fderiv ℝ (fun z => q z + r z) y = _
    exact fderiv_add hq hr
  rw [this, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [add_smul]

theorem gradientAt_smul {q : Space → ℝ} {y : Space} (c : ℝ) (hq : DifferentiableAt ℝ q y) :
    gradientAt (c • q) y = c • gradientAt q y := by
  unfold gradientAt
  have : fderiv ℝ (c • q) y = c • fderiv ℝ q y := by
    show fderiv ℝ (fun z => c • q z) y = _
    exact fderiv_const_smul hq c
  rw [this, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [smul_smul]

theorem scalar_zero : GoodScalar (0 : Space → ℝ) := by
  have hG : ∀ y, gradientAt (0 : Space → ℝ) y = 0 := fun y => by simp [gradientAt, fderiv_zero]
  refine ⟨MemLp.zero, Filter.Eventually.of_forall fun y => differentiableAt_const _, ?_, ?_, ?_, ⟨0, ?_⟩⟩
  · simp only [hG]
    exact locallyIntegrable_const 0
  · intro φ hφ j
    simp [hG]
  · simpa [hG] using (MemLp.zero : MemLp (0 : Space → Space) 2 volume)
  · exact Filter.Eventually.of_forall fun y => by simp [hG]

theorem scalar_add {q r : Space → ℝ} (hq : GoodScalar q) (hr : GoodScalar r) : GoodScalar (q + r) := by
  have hGae : (fun y => gradientAt (q + r) y) =ᵐ[volume] fun y => gradientAt q y + gradientAt r y := by
    filter_upwards [hq.d, hr.d] with y h1 h2
    exact gradientAt_add h1 h2
  obtain ⟨C1, hC1⟩ := hq.b
  obtain ⟨C2, hC2⟩ := hr.b
  refine ⟨hq.l2.add hr.l2, ?_, ?_, ?_, ?_, ⟨C1 + C2, ?_⟩⟩
  · filter_upwards [hq.d, hr.d] with y h1 h2
    exact h1.add h2
  · exact (hq.li.add hr.li).congr hGae.symm
  · intro φ hφ j
    have e1 : (fun y => fderiv ℝ φ y (unitVector j) * (q + r) y) =
        fun y => fderiv ℝ φ y (unitVector j) * q y + fderiv ℝ φ y (unitVector j) * r y := by
      funext y
      simp [mul_add]
    have e2 : (fun y => φ y * inner ℝ (gradientAt (q + r) y) (unitVector j)) =ᵐ[volume]
        fun y => φ y * inner ℝ (gradientAt q y) (unitVector j) + φ y * inner ℝ (gradientAt r y) (unitVector j) := by
      filter_upwards [hGae] with y hy
      simp [hy, inner_add_left, mul_add]
    have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) * q y) :=
      (loc_two hq.l2).integrable_smul_left_of_hasCompactSupport
        (test_deriv_cont hφ j) (test_deriv_supp hφ j)
    have i2 : Integrable (fun y => fderiv ℝ φ y (unitVector j) * r y) :=
      (loc_two hr.l2).integrable_smul_left_of_hasCompactSupport
        (test_deriv_cont hφ j) (test_deriv_supp hφ j)
    have i3 : Integrable (fun y => φ y * inner ℝ (gradientAt q y) (unitVector j)) := by
      have := ((hq.li.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2).inner_const (𝕜 := ℝ) (unitVector j))
      simpa [real_inner_smul_left] using this
    have i4 : Integrable (fun y => φ y * inner ℝ (gradientAt r y) (unitVector j)) := by
      have := ((hr.li.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2).inner_const (𝕜 := ℝ) (unitVector j))
      simpa [real_inner_smul_left] using this
    rw [e1, integral_congr_ae e2, integral_add i1 i2, integral_add i3 i4, hq.wg φ hφ j, hr.wg φ hφ j, neg_add]
  · refine (hq.w.add hr.w).ae_eq ?_
    filter_upwards [hGae] with y hy
    simp [hy, smul_add]
  · filter_upwards [hGae, hC1, hC2] with y hy h1 h2
    rw [hy]
    calc ‖gradientAt q y + gradientAt r y‖ ≤ ‖gradientAt q y‖ + ‖gradientAt r y‖ := norm_add_le _ _
      _ ≤ C1 * min (‖y‖⁻¹) (‖y‖ ^ (-(3 : ℝ))) + C2 * min (‖y‖⁻¹) (‖y‖ ^ (-(3 : ℝ))) := add_le_add h1 h2
      _ = (C1 + C2) * min (‖y‖⁻¹) (‖y‖ ^ (-(3 : ℝ))) := by ring

theorem scalar_smul (c : ℝ) {q : Space → ℝ} (hq : GoodScalar q) : GoodScalar (c • q) := by
  have hGae : (fun y => gradientAt (c • q) y) =ᵐ[volume] fun y => c • gradientAt q y := by
    filter_upwards [hq.d] with y h1
    exact gradientAt_smul c h1
  obtain ⟨C, hC⟩ := hq.b
  refine ⟨hq.l2.const_smul c, ?_, ?_, ?_, ?_, ⟨|c| * C, ?_⟩⟩
  · filter_upwards [hq.d] with y h1
    exact h1.const_smul c
  · exact (hq.li.smul c).congr hGae.symm
  · intro φ hφ j
    have e1 : (fun y => fderiv ℝ φ y (unitVector j) * (c • q) y) =
        fun y => c * (fderiv ℝ φ y (unitVector j) * q y) := by
      funext y
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have e2 : (fun y => φ y * inner ℝ (gradientAt (c • q) y) (unitVector j)) =ᵐ[volume]
        fun y => c * (φ y * inner ℝ (gradientAt q y) (unitVector j)) := by
      filter_upwards [hGae] with y hy
      rw [hy, real_inner_smul_left]
      ring
    rw [e1, integral_congr_ae e2, integral_const_mul, integral_const_mul, hq.wg φ hφ j, mul_neg]
  · refine (hq.w.const_smul c).ae_eq ?_
    filter_upwards [hGae] with y hy
    simp [hy, smul_comm c]
  · filter_upwards [hGae, hC] with y hy h1
    rw [hy, norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg c)

theorem weight_min (y : Space) :
    ‖y‖ * min (‖y‖⁻¹) (‖y‖ ^ (-(3 : ℝ))) ≤ 4 * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  have r0 : 0 ≤ ‖y‖ := norm_nonneg _
  have e2 : (1 + ‖y‖) ^ (-(2 : ℝ)) = ((1 + ‖y‖) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
  have e3 : ‖y‖ ^ (-(3 : ℝ)) = (‖y‖ ^ 3)⁻¹ := by
    rw [Real.rpow_neg r0]
    norm_cast
  rw [e2, e3]
  rcases le_or_gt ‖y‖ 1 with h | h
  · calc ‖y‖ * min (‖y‖⁻¹) ((‖y‖ ^ 3)⁻¹) ≤ ‖y‖ * ‖y‖⁻¹ := mul_le_mul_of_nonneg_left (min_le_left _ _) r0
      _ ≤ 1 := by
        rcases eq_or_lt_of_le r0 with h0 | h0
        · rw [← h0]
          simp
        · rw [mul_inv_cancel₀ h0.ne']
      _ ≤ 4 * ((1 + ‖y‖) ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, one_le_div (by positivity)]
        nlinarith
  · have hpos : 0 < ‖y‖ := by linarith
    calc ‖y‖ * min (‖y‖⁻¹) ((‖y‖ ^ 3)⁻¹) ≤ ‖y‖ * (‖y‖ ^ 3)⁻¹ := mul_le_mul_of_nonneg_left (min_le_right _ _) r0
      _ = (‖y‖ ^ 2)⁻¹ := by
        field_simp
      _ ≤ 4 * ((1 + ‖y‖) ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith

theorem good_pressureOf (P : ChartParams) (hP : IsChartParams P) (D : PressureData) (hD : IsPressureData P D)
    (β : ℝ) : GoodScalar (pressureOf P D β) := by
  obtain ⟨hm, ⟨C0, h0⟩, hd, wg, ⟨C, hC⟩⟩ := pressure_core P hP D hD β
  have hgm : Measurable (fun y => gradientAt (pressureOf P D β) y) := by
    unfold gradientAt
    exact Finset.measurable_sum _ fun i _ => (measurable_fderiv_apply_const ℝ _ _).smul_const _
  have li : LocallyIntegrable (fun y => gradientAt (pressureOf P D β) y) volume := by
    refine locallyIntegrable_of_norm_le_rpow (α := 1) (C := |C|) (by simp) (by simp) ?_ hgm.aestronglyMeasurable
    filter_upwards [hC] with y hy
    rw [Real.rpow_neg_one]
    calc ‖gradientAt (pressureOf P D β) y‖ ≤ C * min (‖y‖⁻¹) (‖y‖ ^ (-(3 : ℝ))) := hy
      _ ≤ |C| * min (‖y‖⁻¹) (‖y‖ ^ (-(3 : ℝ))) := mul_le_mul_of_nonneg_right (le_abs_self C) (min_nonneg' y)
      _ ≤ |C| * ‖y‖⁻¹ := mul_le_mul_of_nonneg_left (min_le_left _ _) (abs_nonneg C)
  refine ⟨memLp_of_decay (a := 2) (C := C0) hm (by norm_num) (by norm_num) (by norm_num)
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact h0 y), hd, li, wg, ?_, ⟨C, hC⟩⟩
  refine memLp_of_decay (f := fun y => ‖y‖ • gradientAt (pressureOf P D β) y) (a := 2) (C := |C| * 4)
    (continuous_norm.measurable.smul hgm).aestronglyMeasurable (by norm_num) (by norm_num) (by norm_num) ?_
  filter_upwards [hC] with y hy
  rw [norm_smul, norm_norm]
  have hmin := min_nonneg' y
  calc ‖y‖ * ‖gradientAt (pressureOf P D β) y‖ ≤ ‖y‖ * (C * min (‖y‖⁻¹) (‖y‖ ^ (-(3 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hy (norm_nonneg _)
    _ ≤ ‖y‖ * (|C| * min (‖y‖⁻¹) (‖y‖ ^ (-(3 : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self C) hmin) (norm_nonneg _)
    _ = |C| * (‖y‖ * min (‖y‖⁻¹) (‖y‖ ^ (-(3 : ℝ)))) := by ring
    _ ≤ |C| * (4 * (1 + ‖y‖) ^ (-(2 : ℝ))) := mul_le_mul_of_nonneg_left (weight_min y) (abs_nonneg C)
    _ = |C| * 4 * (1 + ‖y‖) ^ (-(2 : ℝ)) := by ring

theorem good_pressure (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (j : Fin k) (p : Fin k → ℝ) : GoodScalar (A.adjointPressureField P j p) := by
  have h : A.adjointPressureField P j p = ∑ γ ∈ (A.adjointFamily j).indices,
      multiPow γ p • pressureOf P (A.adjointPressure j γ) (A.phase p) := by
    funext y
    simp [AuxData.adjointPressureField, Finset.sum_apply]
  rw [h]
  refine Finset.sum_induction _ GoodScalar (fun a b ha hb => scalar_add ha hb) scalar_zero (fun γ hγ => ?_)
  obtain ⟨hD, -⟩ := hA.pressure_shape j γ hγ
  exact scalar_smul _ (good_pressureOf P hP _ hD _)

end AdjointInternal

open AdjointInternal AdjointCoreInternal

theorem adjointSolenoidal_of_given (P : ChartParams) (hP : IsChartParams P) {k N : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (d : FracCertData k N) (hm : d.order = P.m)
    (hadj : ∀ j p, d.adjoint j p = A.adjointField P j p)
    (hsharp : ∀ j p, d.adjointSharp j p = A.sharpField P d.splitVisc j p) :
    ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, IsSolenoidalL2 (d.adjoint j p) ∧
      IsClassField d.order (d.adjoint j p) ∧ MemLp (d.adjointSharp j p) 2 volume := by
  intro j _ p _
  have hg := good_adjoint P hP A hA j p
  rw [hadj, hsharp, hm]
  refine ⟨⟨hg.l2, hg.sol⟩, ⟨Filter.Eventually.of_forall fun y => (hg.cls y).1,
    Filter.Eventually.of_forall fun y => (hg.cls y).2⟩, ?_⟩
  have hS : MemLp (fun y => (A.sharpSum j).eval P A.phase p y) 2 volume := by
    simp only [AtomFamily.eval]
    exact memLp_finsetSum _ fun γ hγ =>
      (atom_two P hP _ (hA.sharp_shape j γ hγ) (A.phase p)).const_smul (multiPow γ p)
  exact ((hg.l2.const_smul (A.sharpLead j)).sub hS).sub (hg.l2.const_smul d.splitVisc)

theorem adjointRegular_of_given (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (j : Fin k) (p : Fin k → ℝ) :
    CellCert.Reduction.IsAdjointRegular (A.adjointField P j p) (fun y => fderiv ℝ (A.adjointField P j p) y)
      (fun y => fderiv ℝ (fun z => fderiv ℝ (A.adjointField P j p) z) y) :=
  regular_of_good (good_adjoint P hP A hA j p)

theorem adjointPressure_of_given (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (j : Fin k) (p : Fin k → ℝ) :
    MemLp (A.adjointPressureField P j p) 2 volume ∧
      CellCert.Reduction.IsWeakScalarGradientOf (A.adjointPressureField P j p)
        (fun y => gradientAt (A.adjointPressureField P j p) y) ∧
      MemLp (fun y => ‖y‖ • gradientAt (A.adjointPressureField P j p) y) 2 volume ∧
      ∃ C : ℝ, ∀ᵐ y ∂volume, ‖gradientAt (A.adjointPressureField P j p) y‖ ≤ C * min (‖y‖⁻¹) (‖y‖ ^ (-(3 : ℝ))) := by
  have hg := good_pressure P hP A hA j p
  exact ⟨hg.l2, hg.wg, hg.w, hg.b⟩

end GivenFields

end CellCert

end Breakdown
