import Breakdown.CellReduction.InstanceStatements
import Breakdown.CertCell.CellLayerClosed
import Breakdown.CellReduction.InstScalarGradient
import Breakdown.CellReduction.InstBallAgreement
import Breakdown.CellReduction.InstStepPhase
import Breakdown.CellReduction.InstPressureRegular

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown
namespace CellReduction
namespace Instantiation

open CertCell CertCell.GivenShape

namespace Internal
namespace OffsetBall

section Algebra

variable {k : ℕ}

def QuadExpands {E : Type*} [AddCommGroup E] [Module ℝ E] (q : Fin k → ℝ) (X c : E) (a : Fin k → E)
    (b : Fin k → Fin k → E) : Prop :=
  X = c + ∑ i, q i • a i + ∑ i, ∑ m, (q i * q m) • b i m

variable {E F G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] (q : Fin k → ℝ)

theorem quadExpands_add {X c X' c' : E} {a a' : Fin k → E} {b b' : Fin k → Fin k → E}
    (h : QuadExpands q X c a b) (h' : QuadExpands q X' c' a' b') :
    QuadExpands q (X + X') (c + c') (fun i => a i + a' i) (fun i m => b i m + b' i m) := by
  unfold QuadExpands at *
  rw [h, h']
  simp only [smul_add, Finset.sum_add_distrib]
  abel

theorem quadExpands_sub {X c X' c' : E} {a a' : Fin k → E} {b b' : Fin k → Fin k → E}
    (h : QuadExpands q X c a b) (h' : QuadExpands q X' c' a' b') :
    QuadExpands q (X - X') (c - c') (fun i => a i - a' i) (fun i m => b i m - b' i m) := by
  unfold QuadExpands at *
  rw [h, h']
  simp only [smul_sub, Finset.sum_sub_distrib]
  abel

theorem quadExpands_linear (c : E) (a : Fin k → E) :
    QuadExpands q (c + ∑ i, q i • a i) c a (fun _ _ => 0) := by
  simp [QuadExpands]

theorem quadExpands_map (f : E →ₗ[ℝ] F) {X c : E} {a : Fin k → E} {b : Fin k → Fin k → E}
    (h : QuadExpands q X c a b) :
    QuadExpands q (f X) (f c) (fun i => f (a i)) (fun i m => f (b i m)) := by
  unfold QuadExpands at *
  rw [h]
  simp only [map_add, map_sum, map_smul]

theorem quadExpands_bilin (B : E →ₗ[ℝ] F →ₗ[ℝ] G) (u : E) (us : Fin k → E) (v : F) (vs : Fin k → F) :
    QuadExpands q (B (u + ∑ i, q i • us i) (v + ∑ i, q i • vs i)) (B u v)
      (fun i => B u (vs i) + B (us i) v) (fun i m => B (us i) (vs m)) := by
  unfold QuadExpands
  simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
  have h2 : ∑ x, ∑ y, (q x * q y) • B (us y) (vs x) = ∑ x, ∑ y, (q x * q y) • B (us x) (vs y) := by
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [h2]
  abel

theorem sum_square_triangle (f : Fin k → Fin k → E) :
    ∑ i, ∑ m, (q i * q m) • f i m =
      ∑ i, ∑ m ∈ Finset.Ici i, (q i * q m) • (if i = m then f i i else f i m + f m i) := by
  have hsplit : ∀ i : Fin k, ∑ m, (q i * q m) • f i m =
      ∑ m ∈ Finset.Ici i, (q i * q m) • f i m + ∑ m ∈ Finset.Iio i, (q i * q m) • f i m := by
    intro i
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => i ≤ m)]
    congr 1
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext m; simp
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext m; simp
  have hswap : ∑ i : Fin k, ∑ m ∈ Finset.Iio i, (q i * q m) • f i m =
      ∑ i : Fin k, ∑ m ∈ Finset.Ioi i, (q m * q i) • f m i := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun m => Finset.Ioi m)]
    intro x y
    simp
  have hdiag : ∀ i : Fin k, ∑ m ∈ Finset.Ici i, (q i * q m) • (if i = m then f i i else f i m + f m i) =
      (q i * q i) • f i i + ∑ m ∈ Finset.Ioi i, (q i * q m) • (f i m + f m i) := by
    intro i
    rw [← Finset.Ioi_insert, Finset.sum_insert (by simp), if_pos rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    rw [if_neg (ne_of_lt (Finset.mem_Ioi.mp hm))]
  have hdiag' : ∀ i : Fin k, ∑ m ∈ Finset.Ici i, (q i * q m) • f i m =
      (q i * q i) • f i i + ∑ m ∈ Finset.Ioi i, (q i * q m) • f i m := by
    intro i
    rw [← Finset.Ioi_insert, Finset.sum_insert (by simp)]
  simp only [hsplit, Finset.sum_add_distrib, hswap, hdiag, hdiag', smul_add, mul_comm (q _) (q _)]
  abel

end Algebra

section Calculus

variable {k : ℕ} (q : Fin k → ℝ)

theorem quadExpands_fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {X c : E → F} {a : Fin k → E → F} {b : Fin k → Fin k → E → F} {y : E}
    (h : ∀ y', QuadExpands q (X y') (c y') (fun i => a i y') (fun i m => b i m y'))
    (hc : DifferentiableAt ℝ c y) (ha : ∀ i, DifferentiableAt ℝ (a i) y)
    (hb : ∀ i m, DifferentiableAt ℝ (b i m) y) :
    QuadExpands q (fderiv ℝ X y) (fderiv ℝ c y) (fun i => fderiv ℝ (a i) y) (fun i m => fderiv ℝ (b i m) y) := by
  have hX : X = fun y' => c y' + ∑ i, q i • a i y' + ∑ i, ∑ m, (q i * q m) • b i m y' := funext h
  have H : HasFDerivAt (fun y' => c y' + ∑ i, q i • a i y' + ∑ i, ∑ m, (q i * q m) • b i m y')
      (fderiv ℝ c y + ∑ i, q i • fderiv ℝ (a i) y + ∑ i, ∑ m, (q i * q m) • fderiv ℝ (b i m) y) y :=
    (hc.hasFDerivAt.fun_add (HasFDerivAt.fun_sum fun i _ => (ha i).hasFDerivAt.fun_const_smul (q i))).fun_add
      (HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun m _ =>
        (hb i m).hasFDerivAt.fun_const_smul (q i * q m))
  rw [hX, H.fderiv]
  rfl

def gradMap : (Space →L[ℝ] ℝ) →ₗ[ℝ] Space where
  toFun A := (InnerProductSpace.toDual ℝ Space).symm A
  map_add' A B := map_add _ A B
  map_smul' c A := by simp

theorem quadExpands_gradient {X c : Space → ℝ} {a : Fin k → Space → ℝ} {b : Fin k → Fin k → Space → ℝ}
    {y : Space}
    (h : ∀ y', QuadExpands q (X y') (c y') (fun i => a i y') (fun i m => b i m y'))
    (hc : DifferentiableAt ℝ c y) (ha : ∀ i, DifferentiableAt ℝ (a i) y)
    (hb : ∀ i m, DifferentiableAt ℝ (b i m) y) :
    QuadExpands q (gradient X y) (gradient c y) (fun i => gradient (a i) y) (fun i m => gradient (b i m) y) :=
  quadExpands_map q gradMap (quadExpands_fderiv q h hc ha hb)

theorem quadExpands_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {X c : ℝ → F}
    {a : Fin k → ℝ → F} {b : Fin k → Fin k → ℝ → F} {s : ℝ}
    (h : ∀ s', QuadExpands q (X s') (c s') (fun i => a i s') (fun i m => b i m s'))
    (hc : DifferentiableAt ℝ c s) (ha : ∀ i, DifferentiableAt ℝ (a i) s)
    (hb : ∀ i m, DifferentiableAt ℝ (b i m) s) :
    QuadExpands q (deriv X s) (deriv c s) (fun i => deriv (a i) s) (fun i m => deriv (b i m) s) :=
  quadExpands_map q (ContinuousLinearMap.apply ℝ F (1 : ℝ)).toLinearMap (quadExpands_fderiv q h hc ha hb)

theorem gradient_sub_of {f g : Space → ℝ} {y : Space} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) : gradient (fun y' => f y' - g y') y = gradient f y - gradient g y := by
  unfold gradient
  rw [(hf.hasFDerivAt.fun_sub hg.hasFDerivAt).fderiv, map_sub]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem joint_slice_hasFDerivAt {Φ : ℝ → Space → E} (hΦ : ContDiff ℝ 1 (fun z : ℝ × Space => Φ z.1 z.2))
    (σ : ℝ) (y : Space) :
    HasFDerivAt (Φ σ) ((fderiv ℝ (fun z : ℝ × Space => Φ z.1 z.2) (σ, y)).comp
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space))) y := by
  have h1 : HasFDerivAt (fun y' : Space => ((σ, y') : ℝ × Space))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y :=
    (hasFDerivAt_const σ y).prodMk (hasFDerivAt_id y)
  have h2 := ((hΦ.differentiable one_ne_zero) (σ, y)).hasFDerivAt
  exact h2.comp y h1

theorem joint_time_hasDerivAt {Φ : ℝ → Space → E} (hΦ : ContDiff ℝ 1 (fun z : ℝ × Space => Φ z.1 z.2))
    (σ : ℝ) (y : Space) :
    HasDerivAt (fun s => Φ s y) (fderiv ℝ (fun z : ℝ × Space => Φ z.1 z.2) (σ, y) ((1 : ℝ), (0 : Space))) σ := by
  have h1 : HasDerivAt (fun s : ℝ => ((s, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) σ :=
    (hasDerivAt_id σ).prodMk (hasDerivAt_const σ y)
  have h2 := ((hΦ.differentiable one_ne_zero) (σ, y)).hasFDerivAt
  exact h2.comp_hasDerivAt σ h1

theorem joint_fderiv_continuous {Φ : ℝ → Space → E} (hΦ : ContDiff ℝ 1 (fun z : ℝ × Space => Φ z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (Φ z.1) z.2) := by
  have e : (fun z : ℝ × Space => fderiv ℝ (Φ z.1) z.2) = fun z =>
      (fderiv ℝ (fun z : ℝ × Space => Φ z.1 z.2) z).comp
        ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) :=
    funext fun z => (joint_slice_hasFDerivAt hΦ z.1 z.2).fderiv
  rw [e]
  exact (hΦ.continuous_fderiv one_ne_zero).clm_comp continuous_const

theorem joint_time_continuous {Φ : ℝ → Space → E} (hΦ : ContDiff ℝ 1 (fun z : ℝ × Space => Φ z.1 z.2)) :
    Continuous (fun z : ℝ × Space => deriv (fun s => Φ s z.2) z.1) := by
  have e : (fun z : ℝ × Space => deriv (fun s => Φ s z.2) z.1) = fun z =>
      fderiv ℝ (fun z : ℝ × Space => Φ z.1 z.2) z ((1 : ℝ), (0 : Space)) :=
    funext fun z => (joint_time_hasDerivAt hΦ z.1 z.2).deriv
  rw [e]
  exact (hΦ.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem joint_gradient_continuous {Φ : ℝ → Space → ℝ} (hΦ : ContDiff ℝ 1 (fun z : ℝ × Space => Φ z.1 z.2)) :
    Continuous (fun z : ℝ × Space => gradient (Φ z.1) z.2) :=
  (InnerProductSpace.toDual ℝ Space).symm.continuous.comp (joint_fderiv_continuous hΦ)

theorem joint_differentiableAt {Φ : ℝ → Space → E} (hΦ : ContDiff ℝ 1 (fun z : ℝ × Space => Φ z.1 z.2))
    (σ : ℝ) (y : Space) : DifferentiableAt ℝ (Φ σ) y :=
  (joint_slice_hasFDerivAt hΦ σ y).differentiableAt

theorem joint_time_differentiableAt {Φ : ℝ → Space → E}
    (hΦ : ContDiff ℝ 1 (fun z : ℝ × Space => Φ z.1 z.2)) (σ : ℝ) (y : Space) :
    DifferentiableAt ℝ (fun s => Φ s y) σ :=
  (joint_time_hasDerivAt hΦ σ y).differentiableAt

end Calculus

section Pairing

def boxMeasure (r : ℝ) : Measure (ℝ × Space) :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Metric.closedBall (0 : Space) r))

theorem boxMeasure_eq (r : ℝ) :
    boxMeasure r = volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) r) := by
  rw [boxMeasure, Measure.prod_restrict]
  rfl

theorem boxMeasure_finite (r : ℝ) : IsFiniteMeasure (boxMeasure r) := by
  rw [boxMeasure_eq]
  exact isFiniteMeasure_restrict.2 (isCompact_Icc.prod (isCompact_closedBall (0 : Space) r)).measure_lt_top.ne

structure Tame {E : Type*} [NormedAddCommGroup E] (r : ℝ) (F : ℝ → Space → E) : Prop where
  meas : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) (boxMeasure r)
  bound : ∃ C, ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Metric.closedBall (0 : Space) r, ‖F σ y‖ ≤ C

variable {r : ℝ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E']

theorem tame_of_volume {F : ℝ → Space → E}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hb : ∃ C, ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Metric.closedBall (0 : Space) r, ‖F σ y‖ ≤ C) :
    Tame r F :=
  ⟨by rw [boxMeasure_eq]; exact hm.restrict, hb⟩

theorem tame_of_continuous {F : ℝ → Space → E} (h : Continuous (fun z : ℝ × Space => F z.1 z.2)) :
    Tame r F := by
  refine ⟨h.aestronglyMeasurable, ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : Space) r)).exists_bound_of_continuousOn
    h.continuousOn
  exact ⟨C, fun σ hσ y hy => hC (σ, y) ⟨hσ, hy⟩⟩

theorem tame_add {F G : ℝ → Space → E} (hF : Tame r F) (hG : Tame r G) :
    Tame r (fun σ y => F σ y + G σ y) := by
  obtain ⟨C₁, h₁⟩ := hF.bound
  obtain ⟨C₂, h₂⟩ := hG.bound
  exact ⟨hF.meas.add hG.meas, C₁ + C₂, fun σ hσ y hy =>
    (norm_add_le _ _).trans (add_le_add (h₁ σ hσ y hy) (h₂ σ hσ y hy))⟩

theorem tame_sub {F G : ℝ → Space → E} (hF : Tame r F) (hG : Tame r G) :
    Tame r (fun σ y => F σ y - G σ y) := by
  obtain ⟨C₁, h₁⟩ := hF.bound
  obtain ⟨C₂, h₂⟩ := hG.bound
  exact ⟨hF.meas.sub hG.meas, C₁ + C₂, fun σ hσ y hy =>
    (norm_sub_le _ _).trans (add_le_add (h₁ σ hσ y hy) (h₂ σ hσ y hy))⟩

theorem tame_smul (c : ℝ) {F : ℝ → Space → E} (hF : Tame r F) : Tame r (fun σ y => c • F σ y) := by
  obtain ⟨C, h⟩ := hF.bound
  refine ⟨hF.meas.const_smul c, |c| * C, fun σ hσ y hy => ?_⟩
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (h σ hσ y hy) (abs_nonneg c)

theorem tame_zero : Tame r (fun (_ : ℝ) (_ : Space) => (0 : E)) :=
  tame_of_continuous continuous_const

theorem tame_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → Space → E} (h : ∀ i ∈ s, Tame r (F i)) :
    Tame r (fun σ y => ∑ i ∈ s, F i σ y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (tame_zero : Tame r (fun (_ : ℝ) (_ : Space) => (0 : E)))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact tame_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem tame_clm (T : E →L[ℝ] E') {F : ℝ → Space → E} (hF : Tame r F) : Tame r (fun σ y => T (F σ y)) := by
  obtain ⟨C, h⟩ := hF.bound
  refine ⟨T.continuous.comp_aestronglyMeasurable hF.meas, ‖T‖ * C, fun σ hσ y hy => ?_⟩
  exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h σ hσ y hy) (norm_nonneg T))

theorem tame_inner {F G : ℝ → Space → Space} (hF : Tame r F) (hG : Tame r G) :
    Tame r (fun σ y => inner ℝ (F σ y) (G σ y)) := by
  obtain ⟨C₁, h₁⟩ := hF.bound
  obtain ⟨C₂, h₂⟩ := hG.bound
  refine ⟨hF.meas.inner hG.meas, C₁ * C₂, fun σ hσ y hy => ?_⟩
  rw [Real.norm_eq_abs]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (h₁ σ hσ y hy) (h₂ σ hσ y hy) (norm_nonneg _)
    ((norm_nonneg _).trans (h₁ σ hσ y hy)))

theorem pairing_integrable {F G : ℝ → Space → Space} (hF : Tame r F) (hG : Tame r G) :
    Integrable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (G z.1 z.2)) (boxMeasure r) := by
  have := boxMeasure_finite r
  obtain ⟨C, hC⟩ := (tame_inner hF hG).bound
  refine Integrable.of_bound (tame_inner hF hG).meas C ?_
  rw [boxMeasure_eq]
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod Metric.isClosed_closedBall.measurableSet)] with z hz
  exact hC z.1 hz.1 z.2 hz.2

theorem pairing_eq_integral {F G : ℝ → Space → Space} (hF : Tame r F) (hG : Tame r G) :
    ballPairing r F G = ∫ z, inner ℝ (F z.1 z.2) (G z.1 z.2) ∂(boxMeasure r) := by
  rw [boxMeasure, integral_prod _ (pairing_integrable hF hG)]
  rfl

theorem pairing_add {F G Z : ℝ → Space → Space} (hF : Tame r F) (hG : Tame r G) (hZ : Tame r Z) :
    ballPairing r (fun σ y => F σ y + G σ y) Z = ballPairing r F Z + ballPairing r G Z := by
  rw [pairing_eq_integral (tame_add hF hG) hZ, pairing_eq_integral hF hZ, pairing_eq_integral hG hZ,
    ← integral_add (pairing_integrable hF hZ) (pairing_integrable hG hZ)]
  congr 1
  funext z
  exact inner_add_left _ _ _

theorem pairing_smul (c : ℝ) (F Z : ℝ → Space → Space) :
    ballPairing r (fun σ y => c • F σ y) Z = c * ballPairing r F Z := by
  unfold ballPairing
  simp only [real_inner_smul_left, integral_const_mul]

theorem pairing_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → Space → Space} {Z : ℝ → Space → Space}
    (h : ∀ i ∈ s, Tame r (F i)) (hZ : Tame r Z) :
    ballPairing r (fun σ y => ∑ i ∈ s, F i σ y) Z = ∑ i ∈ s, ballPairing r (F i) Z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ballPairing]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [pairing_add (h a (Finset.mem_insert_self a s))
      (tame_sum s fun i hi => h i (Finset.mem_insert_of_mem hi)) hZ,
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem pairing_congr {F G Z : ℝ → Space → Space}
    (h : ∀ σ, ∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : Space) r)), F σ y = G σ y) :
    ballPairing r F Z = ballPairing r G Z := by
  unfold ballPairing
  congr 1
  funext σ
  apply integral_congr_ae
  filter_upwards [h σ] with y hy
  rw [hy]

theorem pairing_expand {k : ℕ} (q : Fin k → ℝ) {C Z : ℝ → Space → Space} {L : Fin k → ℝ → Space → Space}
    {Q : Fin k → Fin k → ℝ → Space → Space} (hC : Tame r C) (hL : ∀ i, Tame r (L i))
    (hQ : ∀ i m, Tame r (Q i m)) (hZ : Tame r Z) :
    ballPairing r (fun σ y => C σ y + ∑ i, q i • L i σ y + ∑ i, ∑ m ∈ Finset.Ici i, (q i * q m) • Q i m σ y) Z =
      ballPairing r C Z + (∑ i, q i * ballPairing r (L i) Z)
        + (∑ i, ∑ m ∈ Finset.Ici i, q i * q m * ballPairing r (Q i m) Z) := by
  have tL : Tame r (fun σ y => ∑ i, q i • L i σ y) := tame_sum _ fun i _ => tame_smul (q i) (hL i)
  have tQi : ∀ i, Tame r (fun σ y => ∑ m ∈ Finset.Ici i, (q i * q m) • Q i m σ y) :=
    fun i => tame_sum _ fun m _ => tame_smul (q i * q m) (hQ i m)
  have tQ : Tame r (fun σ y => ∑ i, ∑ m ∈ Finset.Ici i, (q i * q m) • Q i m σ y) :=
    tame_sum _ fun i _ => tQi i
  rw [pairing_add (tame_add hC tL) tQ hZ, pairing_add hC tL hZ,
    pairing_sum _ (fun i _ => tame_smul (q i) (hL i)) hZ, pairing_sum _ (fun i _ => tQi i) hZ]
  simp only [pairing_sum _ (fun m _ => tame_smul _ (hQ _ m)) hZ, pairing_smul]

end Pairing

section Coefficients

variable {r : ℝ}

def traceMap : (Space →L[ℝ] Space →L[ℝ] Space) →L[ℝ] Space :=
  ∑ j : Fin 3, (ContinuousLinearMap.apply ℝ Space (unitVector j)).comp
    (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector j))

theorem traceMap_apply (H : Space →L[ℝ] Space →L[ℝ] Space) : traceMap H = secondDerivTrace H := by
  simp [traceMap, secondDerivTrace]

theorem tame_field {Φ : ℝ → Space → Space} (hΦ : ContDiff ℝ 1 (fun z : ℝ × Space => Φ z.1 z.2)) :
    Tame r Φ :=
  tame_of_continuous hΦ.continuous

theorem tame_time {Φ : ℝ → Space → Space} (hΦ : ContDiff ℝ 1 (fun z : ℝ × Space => Φ z.1 z.2)) :
    Tame r (timeDeriv Φ) :=
  tame_of_continuous (joint_time_continuous hΦ)

theorem tame_fderiv_apply {Φ V : ℝ → Space → Space} (hΦ : ContDiff ℝ 1 (fun z : ℝ × Space => Φ z.1 z.2))
    (hV : Continuous (fun z : ℝ × Space => V z.1 z.2)) :
    Tame r (fun σ y => fderiv ℝ (Φ σ) y (V σ y)) :=
  tame_of_continuous ((joint_fderiv_continuous hΦ).clm_apply hV)

theorem tame_fderiv_self {Φ : ℝ → Space → Space} (hΦ : ContDiff ℝ 1 (fun z : ℝ × Space => Φ z.1 z.2)) :
    Tame r (fun σ y => fderiv ℝ (Φ σ) y y) :=
  tame_fderiv_apply (V := fun _ y => y) hΦ continuous_snd

theorem tame_gradient_smooth {Φ : ℝ → Space → ℝ} (hΦ : ContDiff ℝ 1 (fun z : ℝ × Space => Φ z.1 z.2)) :
    Tame r (fun σ y => gradient (Φ σ) y) :=
  tame_of_continuous (joint_gradient_continuous hΦ)

theorem tame_secondDerivTrace (P : ShapeParams) (D : TimeFieldData) (hP : IsShapeParams P) (hD : IsTimeFieldData D) :
    Tame r (fun σ y => secondDerivTrace (shapeHess P D σ y)) := by
  obtain ⟨B, hB⟩ := shapeParts_closed.field_decay P D hP hD
  have t : Tame r (shapeHess P D) := by
    refine tame_of_volume (shapeParts_closed.field_smooth P D hP hD).2.2.1 ⟨|B|, fun σ _ y _ => ?_⟩
    have hpos : (0 : ℝ) < (1 + ‖y‖) ^ 3 := by positivity
    have h1 : (1 : ℝ) ≤ (1 + ‖y‖) ^ 3 := one_le_pow₀ (by linarith [norm_nonneg y])
    calc ‖shapeHess P D σ y‖ ≤ B / (1 + ‖y‖) ^ 3 := (hB σ y).2.2
      _ ≤ |B| / (1 + ‖y‖) ^ 3 := div_le_div_of_nonneg_right (le_abs_self B) hpos.le
      _ ≤ |B| := div_le_self (abs_nonneg B) h1
  have := tame_clm traceMap t
  simpa only [traceMap_apply] using this

theorem tame_pressure (hPress : PressureFieldRegularHolds) (P : ShapeParams) (E : PressureFieldData)
    (hP : IsShapeParams P) (hE : IsPressureFieldData E) :
    Tame r (fun σ y => gradient (shapePressure P E σ) y) := by
  obtain ⟨hc, -, hl⟩ := hPress P E hP hE
  have hm := (scalarGradientOrthogonal_holds (shapePressure P E) hc fun σ ρ =>
    (hl ρ).elim fun L hL => ⟨L, hL σ⟩).1
  refine tame_of_volume hm ?_
  obtain ⟨L, hL⟩ := hl (|r| + 1)
  refine ⟨L, fun σ _ y hy => ?_⟩
  have hy' : ‖y‖ < |r| + 1 := by
    have := mem_closedBall_zero_iff.1 hy
    linarith [le_abs_self r]
  have hn : Metric.closedBall (0 : Space) (|r| + 1) ∈ 𝓝 y :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hy')) Metric.ball_subset_closedBall
  have := norm_fderiv_le_of_lipschitzOn ℝ hn (hL σ)
  unfold gradient
  rw [LinearIsometryEquiv.norm_map]
  exact this

end Coefficients

section Pointwise

variable {k : ℕ}

def cField (R : ProfileShapeEntry k) : ℝ → Space → Space :=
  shapeInfoField (withOrigin R.params R.centreOrigin) R.centre

def tField (R : ProfileShapeEntry k) (i : Fin k) : ℝ → Space → Space :=
  shapeInfoField (withOrigin R.params (R.tangentOrigin i)) (R.tangent i)

def baseField (R : ProfileShapeEntry k) (q : Fin k → ℝ) (σ : ℝ) (y : Space) : Space :=
  cField R σ y + ∑ i, q i • tField R i σ y

structure BaseSmooth (R : ProfileShapeEntry k) : Prop where
  centre : ContDiff ℝ 1 (fun z : ℝ × Space => cField R z.1 z.2)
  tangent : ∀ i, ContDiff ℝ 1 (fun z : ℝ × Space => tField R i z.1 z.2)

def applyRight : Space →ₗ[ℝ] (Space →L[ℝ] Space) →ₗ[ℝ] Space :=
  LinearMap.mk₂ ℝ (fun w A => A w) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp)

def halfInner : Space →ₗ[ℝ] Space →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun a b => inner ℝ a b / 2) (fun _ _ _ => by simp [inner_add_left, add_div])
    (fun _ _ _ => by simp [real_inner_smul_left, mul_div_assoc]) (fun _ _ _ => by simp [inner_add_right, add_div])
    (fun _ _ _ => by simp [real_inner_smul_right, mul_div_assoc])

theorem quadExpands_of_eq {E : Type*} [AddCommGroup E] [Module ℝ E] {q : Fin k → ℝ} {X c X' c' : E}
    {a a' : Fin k → E} {b b' : Fin k → Fin k → E} (h : QuadExpands q X c a b) (hX : X = X') (hc : c = c')
    (ha : ∀ i, a i = a' i) (hb : ∀ i m, b i m = b' i m) : QuadExpands q X' c' a' b' := by
  subst hX hc
  rw [show a = a' from funext ha, show b = b' from funext fun i => funext fun m => hb i m] at h
  exact h

theorem gradient_zero_fun (y : Space) : gradient (fun _ : Space => (0 : ℝ)) y = 0 := by
  simp [gradient]

variable (R : ProfileShapeEntry k) (q : Fin k → ℝ)

theorem baseField_fderiv (hs : BaseSmooth R) (σ : ℝ) (y : Space) :
    fderiv ℝ (baseField R q σ) y = fderiv ℝ (cField R σ) y + ∑ i, q i • fderiv ℝ (tField R i σ) y := by
  have H : HasFDerivAt (fun y' => cField R σ y' + ∑ i, q i • tField R i σ y')
      (fderiv ℝ (cField R σ) y + ∑ i, q i • fderiv ℝ (tField R i σ) y) y :=
    (joint_differentiableAt hs.centre σ y).hasFDerivAt.fun_add
      (HasFDerivAt.fun_sum fun i _ => (joint_differentiableAt (hs.tangent i) σ y).hasFDerivAt.fun_const_smul (q i))
  exact H.fderiv

theorem baseField_differentiableAt (hs : BaseSmooth R) (σ : ℝ) (y : Space) :
    DifferentiableAt ℝ (baseField R q σ) y :=
  ((joint_differentiableAt hs.centre σ y).hasFDerivAt.fun_add
      (HasFDerivAt.fun_sum fun i _ =>
        (joint_differentiableAt (hs.tangent i) σ y).hasFDerivAt.fun_const_smul (q i))).differentiableAt

theorem time_expands (hs : BaseSmooth R) (w0 : ℝ) (w : Fin k → ℝ) (σ : ℝ) (y : Space) :
    QuadExpands q ((w0 + ∑ i, q i * w i) • deriv (fun s => baseField R q s y) σ)
      (w0 • timeDeriv (cField R) σ y)
      (fun i => w0 • timeDeriv (tField R i) σ y + w i • timeDeriv (cField R) σ y)
      (fun i m => w i • timeDeriv (tField R m) σ y) := by
  have hd : deriv (fun s => baseField R q s y) σ =
      timeDeriv (cField R) σ y + ∑ i, q i • timeDeriv (tField R i) σ y := by
    have H : HasDerivAt (fun s => cField R s y + ∑ i, q i • tField R i s y)
        (timeDeriv (cField R) σ y + ∑ i, q i • timeDeriv (tField R i) σ y) σ :=
      (joint_time_differentiableAt hs.centre σ y).hasDerivAt.add
        (HasDerivAt.fun_sum fun i _ =>
          HasDerivAt.const_smul (q i) (joint_time_differentiableAt (hs.tangent i) σ y).hasDerivAt)
    exact H.deriv
  have := quadExpands_bilin q (LinearMap.lsmul ℝ Space) w0 w (timeDeriv (cField R) σ y)
    (fun i => timeDeriv (tField R i) σ y)
  refine quadExpands_of_eq this ?_ ?_ ?_ ?_
  · rw [hd]
    simp only [LinearMap.lsmul_apply, smul_eq_mul]
  · simp
  · intro i
    simp
  · intro i m
    simp

theorem half_expands (σ : ℝ) (y : Space) :
    QuadExpands q ((1 / 2 : ℝ) • baseField R q σ y) ((1 / 2 : ℝ) • cField R σ y)
      (fun i => (1 / 2 : ℝ) • tField R i σ y) (fun _ _ => 0) := by
  refine quadExpands_of_eq (quadExpands_map q (LinearMap.lsmul ℝ Space (1 / 2 : ℝ))
    (quadExpands_linear q (cField R σ y) (fun i => tField R i σ y))) ?_ ?_ ?_ ?_
  · simp [baseField]
  · simp
  · intro i
    simp
  · intro i m
    simp

theorem halfDeriv_expands (hs : BaseSmooth R) (σ : ℝ) (y : Space) :
    QuadExpands q ((1 / 2 : ℝ) • fderiv ℝ (baseField R q σ) y y) ((1 / 2 : ℝ) • fderiv ℝ (cField R σ) y y)
      (fun i => (1 / 2 : ℝ) • fderiv ℝ (tField R i σ) y y) (fun _ _ => 0) := by
  refine quadExpands_of_eq (quadExpands_map q
    ((LinearMap.lsmul ℝ Space (1 / 2 : ℝ)).comp (ContinuousLinearMap.apply ℝ Space y).toLinearMap)
    (quadExpands_linear q (fderiv ℝ (cField R σ) y) (fun i => fderiv ℝ (tField R i σ) y))) ?_ ?_ ?_ ?_
  · rw [baseField_fderiv R q hs σ y]
    simp
  · simp
  · intro i
    simp
  · intro i m
    simp

theorem trace_expands (H₀ : Space →L[ℝ] Space →L[ℝ] Space) (H : Fin k → Space →L[ℝ] Space →L[ℝ] Space) :
    QuadExpands q (secondDerivTrace (H₀ + ∑ i, q i • H i)) (secondDerivTrace H₀) (fun i => secondDerivTrace (H i))
      (fun _ _ => 0) := by
  refine quadExpands_of_eq (quadExpands_map q traceMap.toLinearMap (quadExpands_linear q H₀ H)) ?_ ?_ ?_ ?_
  · simp [traceMap_apply]
  · simp [traceMap_apply]
  · intro i
    simp [traceMap_apply]
  · intro i m
    simp

theorem advection_expands (hs : BaseSmooth R) (σ : ℝ) (y : Space) :
    QuadExpands q (advectionAt (baseField R q σ) y) (advectionAt (cField R σ) y)
      (fun i => fderiv ℝ (tField R i σ) y (cField R σ y) + fderiv ℝ (cField R σ) y (tField R i σ y))
      (fun i m => fderiv ℝ (tField R m σ) y (tField R i σ y)) := by
  refine quadExpands_of_eq (quadExpands_bilin q applyRight (cField R σ y) (fun i => tField R i σ y)
    (fderiv ℝ (cField R σ) y) (fun i => fderiv ℝ (tField R i σ) y)) ?_ ?_ ?_ ?_
  · rw [advectionAt, baseField_fderiv R q hs σ y]
    simp only [applyRight, LinearMap.mk₂_apply, baseField]
  · simp [applyRight, advectionAt]
  · intro i
    simp [applyRight]
  · intro i m
    simp [applyRight]

theorem actuator_expands (mc : Fin k → ℝ) (mt : Fin k → Fin k → ℝ) (b : Fin k → Space) :
    QuadExpands q (∑ l, (mc l + ∑ i, q i * mt i l) • b l) (∑ l, mc l • b l) (fun i => ∑ l, mt i l • b l)
      (fun _ _ => 0) := by
  unfold QuadExpands
  simp only [add_smul, Finset.sum_add_distrib, Finset.sum_smul, mul_smul, Finset.smul_sum, smul_zero,
    Finset.sum_const_zero, add_zero]
  rw [Finset.sum_comm]

theorem differentiableAt_half {f : Space → ℝ} {y : Space} (h : DifferentiableAt ℝ f y) :
    DifferentiableAt ℝ (fun y' => f y' / 2) y := by
  simpa only [div_eq_mul_inv] using h.mul_const (2⁻¹ : ℝ)

theorem pressure_expands (hs : BaseSmooth R) (cP : ℝ → Space → ℝ) (tP : Fin k → ℝ → Space → ℝ) (σ : ℝ)
    (y : Space) (hpc : DifferentiableAt ℝ (cP σ) y) (hpt : ∀ i, DifferentiableAt ℝ (tP i σ) y) :
    QuadExpands q (gradient (fun y' => (cP σ y' + ∑ i, q i * tP i σ y') - ‖baseField R q σ y'‖ ^ 2 / 2) y)
      (gradient (cP σ) y - gradient (fun y' => ‖cField R σ y'‖ ^ 2 / 2) y)
      (fun i => gradient (tP i σ) y - gradient (fun y' => inner ℝ (cField R σ y') (tField R i σ y')) y)
      (fun i m => gradient (fun _ : Space => (0 : ℝ)) y -
        gradient (fun y' => inner ℝ (tField R i σ y') (tField R m σ y') / 2) y) := by
  have hc := joint_differentiableAt hs.centre σ y
  have ht := fun i => joint_differentiableAt (hs.tangent i) σ y
  have hP : ∀ y', QuadExpands q (cP σ y' + ∑ i, q i * tP i σ y') (cP σ y') (fun i => tP i σ y')
      (fun _ _ => (0 : ℝ)) := fun y' => by
    unfold QuadExpands
    simp
  have hN : ∀ y', QuadExpands q (‖baseField R q σ y'‖ ^ 2 / 2) (‖cField R σ y'‖ ^ 2 / 2)
      (fun i => inner ℝ (cField R σ y') (tField R i σ y'))
      (fun i m => inner ℝ (tField R i σ y') (tField R m σ y') / 2) := fun y' =>
    quadExpands_of_eq (quadExpands_bilin q halfInner (cField R σ y') (fun i => tField R i σ y')
      (cField R σ y') (fun i => tField R i σ y'))
      (by simp only [halfInner, LinearMap.mk₂_apply, baseField, real_inner_self_eq_norm_sq])
      (by simp only [halfInner, LinearMap.mk₂_apply, real_inner_self_eq_norm_sq])
      (fun i => by
        simp only [halfInner, LinearMap.mk₂_apply]
        rw [real_inner_comm (cField R σ y') (tField R i σ y')]
        ring)
      (fun i m => by simp only [halfInner, LinearMap.mk₂_apply])
  have g1 := quadExpands_gradient q hP hpc hpt (fun _ _ => differentiableAt_const _)
  have g2 := quadExpands_gradient q hN (differentiableAt_half (hc.norm_sq ℝ)) (fun i => hc.inner ℝ (ht i))
    (fun i m => by
      exact differentiableAt_half ((ht i).inner ℝ (ht m)))
  have hPd : DifferentiableAt ℝ (fun y' => cP σ y' + ∑ i, q i * tP i σ y') y := by fun_prop
  have hNd : DifferentiableAt ℝ (fun y' => ‖baseField R q σ y'‖ ^ 2 / 2) y := by
    exact differentiableAt_half ((baseField_differentiableAt R q hs σ y).norm_sq ℝ)
  refine quadExpands_of_eq (quadExpands_sub q g1 g2) ?_ rfl (fun i => rfl) (fun i m => rfl)
  exact (gradient_sub_of hPd hNd).symm

end Pointwise

section Main

variable {k : ℕ} {C : Type} {nE nM : ℕ}

theorem originParams_valid {P : ShapeParams} {g : OriginProfile} (hP : IsShapeParams P)
    (hg : IsOriginProfile g) : IsShapeParams (withOrigin P g) :=
  ⟨hP.chartLength_pos, hP.azimuthOrder_pos, hP.phase, hg⟩

theorem baseSmooth_of {D : CellLayerData k C nE nM} {R : ProfileShapeEntry k}
    (hR : IsProfileShapeEntry D R) : BaseSmooth R :=
  ⟨(shapeParts_closed.field_smooth _ _ (originParams_valid hR.params_valid hR.centreOrigin_valid)
      hR.centre_valid).1,
    fun i => (shapeParts_closed.field_smooth _ _ (originParams_valid hR.params_valid (hR.tangentOrigin_valid i))
      (hR.tangent_valid i)).1⟩

theorem defect_expands (hBall : BallAgreementHolds) (hStep : StepPhaseHolds)
    (D : CellLayerData k C nE nM) (R : ProfileShapeEntry k) (Pr : PressureShapeEntry k)
    (O : OffsetExpansionEntry k) (hR : IsProfileShapeEntry D R) (hPr : IsPressureShapeEntry D R Pr)
    (hper : ∀ q ∈ D.cert.params, 1 / D.cert.period q = O.freqCentre + ∑ i, q i * O.freqTangent i)
    (hmul : ∀ q ∈ D.cert.params, ∀ l, D.cert.multiplier q l = O.multCentre l + ∑ i, q i * O.multTangent i l)
    (q : Fin k → ℝ) (hq : q ∈ D.cert.params) (σ : ℝ) (y : Space) (hy : ‖y‖ < R.matchRadius)
    (hpc : DifferentiableAt ℝ (shapePressure R.params Pr.centre σ) y)
    (hpt : ∀ i, DifferentiableAt ℝ (shapePressure R.params (Pr.tangent i) σ) y) :
    QuadExpands q (D.cert.defect q σ y) (O.centreCoefficient D R Pr σ y)
      (fun i => O.linearCoefficient D R Pr i σ y) (fun i m => O.orderedQuadratic R i m σ y) := by
  have hs := baseSmooth_of hR
  have hPv := hR.params_valid
  obtain ⟨hrad, hzero⟩ := hStep R.params.chartLength R.stepEdge R.step hPv.chartLength_pos hR.step_valid
  have agree : ∀ (g : OriginProfile) (T : TimeFieldData), IsOriginProfile g → IsTimeFieldData T →
      ∀ σ' y', ‖y'‖ < R.matchRadius →
      shapeInfoField (withOrigin (R.paramsAt q) g) T σ' y' = shapeInfoField (withOrigin R.params g) T σ' y' ∧
      shapeHess (withOrigin (R.paramsAt q) g) T σ' y' = shapeHess (withOrigin R.params g) T σ' y' := by
    intro g T hg hT σ' y' hy'
    have h := hBall (withOrigin R.params g) R.moving (phaseRate R.rate q) R.matchRadius T Pr.centre
      (originParams_valid hPv hg) hrad hzero hT hPr.centre_valid σ' y' hy'
    exact ⟨h.1, h.2.2.1⟩
  have agreeP : ∀ (E : PressureFieldData), IsPressureFieldData E → ∀ σ' y', ‖y'‖ < R.matchRadius →
      shapePressure (R.paramsAt q) E σ' y' = shapePressure R.params E σ' y' := fun E hE σ' y' hy' =>
    (hBall R.params R.moving (phaseRate R.rate q) R.matchRadius R.centre E hPv hrad hzero hR.centre_valid hE
      σ' y' hy').2.2.2.1
  have hW : ∀ σ' y', ‖y'‖ < R.matchRadius → D.cert.profile q σ' y' = baseField R q σ' y' := by
    intro σ' y' hy'
    rw [hR.profile_eq]
    show shapeInfoField (withOrigin (R.paramsAt q) R.centreOrigin) R.centre σ' y' +
      ∑ i, q i • shapeInfoField (withOrigin (R.paramsAt q) (R.tangentOrigin i)) (R.tangent i) σ' y' =
        cField R σ' y' + ∑ i, q i • tField R i σ' y'
    rw [(agree _ _ hR.centreOrigin_valid hR.centre_valid σ' y' hy').1]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(agree _ _ (hR.tangentOrigin_valid i) (hR.tangent_valid i) σ' y' hy').1]
    rfl
  have hH : D.cert.profileSecondDeriv q σ y = shapeHess (withOrigin R.params R.centreOrigin) R.centre σ y +
      ∑ i, q i • shapeHess (withOrigin R.params (R.tangentOrigin i)) (R.tangent i) σ y := by
    rw [hR.profileSecondDeriv_eq]
    show shapeHess (withOrigin (R.paramsAt q) R.centreOrigin) R.centre σ y +
      ∑ i, q i • shapeHess (withOrigin (R.paramsAt q) (R.tangentOrigin i)) (R.tangent i) σ y = _
    rw [(agree _ _ hR.centreOrigin_valid hR.centre_valid σ y hy).2]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(agree _ _ (hR.tangentOrigin_valid i) (hR.tangent_valid i) σ y hy).2]
  have hnb : D.cert.profile q σ =ᶠ[𝓝 y] baseField R q σ := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hy)] with y' hy'
    exact hW σ y' (mem_ball_zero_iff.1 hy')
  have hfd : fderiv ℝ (D.cert.profile q σ) y = fderiv ℝ (baseField R q σ) y := hnb.fderiv_eq
  have hval : D.cert.profile q σ y = baseField R q σ y := hW σ y hy
  have htime : (fun s => D.cert.profile q s y) = fun s => baseField R q s y := funext fun s => hW s y hy
  have hadv : advectionAt (D.cert.profile q σ) y = advectionAt (baseField R q σ) y := by
    unfold advectionAt
    rw [hfd, hval]
  have hpress : D.cert.pressureGrad q σ y = gradient (fun y' => (shapePressure R.params Pr.centre σ y' +
      ∑ i, q i * shapePressure R.params (Pr.tangent i) σ y') - ‖baseField R q σ y'‖ ^ 2 / 2) y := by
    rw [hPr.pressureGrad_eq]
    unfold gradient
    congr 1
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hy)] with y' hy'
    have hy'' := mem_ball_zero_iff.1 hy'
    simp only [PressureShapeEntry.pressure]
    rw [agreeP _ hPr.centre_valid σ y' hy'', hW σ y' hy'']
    congr 2
    exact Finset.sum_congr rfl fun i _ => by rw [agreeP _ (hPr.tangent_valid i) σ y' hy'']
  have E := quadExpands_add q (quadExpands_add q (quadExpands_add q (quadExpands_sub q
    (quadExpands_add q (quadExpands_add q (time_expands R q hs O.freqCentre O.freqTangent σ y)
      (half_expands R q σ y)) (halfDeriv_expands R q hs σ y))
    (trace_expands q (shapeHess (withOrigin R.params R.centreOrigin) R.centre σ y)
      (fun i => shapeHess (withOrigin R.params (R.tangentOrigin i)) (R.tangent i) σ y)))
    (advection_expands R q hs σ y))
    (actuator_expands q O.multCentre O.multTangent (fun l => D.cert.actuator l σ y)))
    (pressure_expands R q hs (shapePressure R.params Pr.centre) (fun i => shapePressure R.params (Pr.tangent i))
      σ y hpc hpt)
  refine quadExpands_of_eq E ?_ ?_ ?_ ?_
  · symm
    simp only [ExtendedCertificateData.defect, weakDefectField]
    rw [htime, hadv, hfd, hval, hH, hpress, hper q hq]
    simp only [hmul q hq]
  · simp only [OffsetExpansionEntry.centreCoefficient, centreDefect, cField]
    abel
  · intro i
    simp only [OffsetExpansionEntry.linearCoefficient, linearDefect, cField, tField]
    abel
  · intro i m
    simp only [OffsetExpansionEntry.orderedQuadratic, quadraticDefect, tField, gradient_zero_fun]
    abel

end Main

section Conclusion

variable {k : ℕ} {C : Type} {nE nM : ℕ}

theorem quadCoeff_apply (R : ProfileShapeEntry k) (O : OffsetExpansionEntry k) (i m : Fin k) (σ : ℝ)
    (y : Space) : O.quadraticCoefficient R i m σ y =
      if i = m then O.orderedQuadratic R i i σ y else O.orderedQuadratic R i m σ y + O.orderedQuadratic R m i σ y := by
  unfold OffsetExpansionEntry.quadraticCoefficient
  split_ifs <;> rfl

end Conclusion

end OffsetBall
end Internal

open Internal.OffsetBall in
theorem offsetBallIdentity_of (hBall : BallAgreementHolds) (hStep : StepPhaseHolds)
    (hPress : PressureFieldRegularHolds) : OffsetBallIdentityHolds := by
  intro k C nE nM D X F R Pr Z O hF hI hO j hj q hq
  obtain ⟨hR, hPr, hZ⟩ := hI
  have hs := baseSmooth_of hR
  have hPv := hR.params_valid
  rw [hZ.adjoint_eq j hj q]
  have tZ : Tame R.matchRadius (shapeInfoField Z.params (Z.field j)) :=
    tame_field (shapeParts_closed.field_smooth _ _ hZ.params_valid (hZ.field_valid j hj)).1
  have tAct : ∀ l, Tame R.matchRadius (D.cert.actuator l) := fun l => by
    rw [hF.actuator_eq l]
    exact tame_field (shapeParts_closed.field_smooth _ _ (hF.actuatorParams_valid l) (hF.actuators_valid l).field).1
  have tC : Tame R.matchRadius (O.centreCoefficient D R Pr) :=
    tame_sub (tame_add (tame_add (tame_add (tame_sub (tame_add (tame_add
      (tame_smul _ (tame_time hs.centre)) (tame_smul _ (tame_field hs.centre)))
      (tame_smul _ (tame_fderiv_self hs.centre)))
      (tame_secondDerivTrace _ _ (originParams_valid hPv hR.centreOrigin_valid) hR.centre_valid))
      (tame_fderiv_apply hs.centre hs.centre.continuous))
      (tame_sum _ fun l _ => tame_smul _ (tAct l)))
      (tame_pressure hPress _ _ hPv hPr.centre_valid))
      (tame_gradient_smooth ((hs.centre.norm_sq ℝ).div_const (2 : ℝ)))
  have tL : ∀ i, Tame R.matchRadius (O.linearCoefficient D R Pr i) := fun i =>
    tame_sub (tame_add (tame_add (tame_add (tame_add (tame_sub (tame_add (tame_add (tame_add
      (tame_smul _ (tame_time (hs.tangent i))) (tame_smul _ (tame_time hs.centre)))
      (tame_smul _ (tame_field (hs.tangent i))))
      (tame_smul _ (tame_fderiv_self (hs.tangent i))))
      (tame_secondDerivTrace _ _ (originParams_valid hPv (hR.tangentOrigin_valid i)) (hR.tangent_valid i)))
      (tame_fderiv_apply hs.centre (hs.tangent i).continuous))
      (tame_fderiv_apply (hs.tangent i) hs.centre.continuous))
      (tame_sum _ fun l _ => tame_smul _ (tAct l)))
      (tame_pressure hPress _ _ hPv (hPr.tangent_valid i)))
      (tame_gradient_smooth (hs.centre.inner ℝ (hs.tangent i)))
  have tO : ∀ i m, Tame R.matchRadius (O.orderedQuadratic R i m) := fun i m =>
    tame_sub (tame_add (tame_smul _ (tame_time (hs.tangent m)))
      (tame_fderiv_apply (hs.tangent m) (hs.tangent i).continuous))
      (tame_gradient_smooth (((hs.tangent i).inner ℝ (hs.tangent m)).div_const (2 : ℝ)))
  have tQ : ∀ i m, Tame R.matchRadius (O.quadraticCoefficient R i m) := fun i m => by
    unfold OffsetExpansionEntry.quadraticCoefficient
    split_ifs
    · exact tO i i
    · exact tame_add (tO i m) (tO m i)
  have hae : ∀ σ, ∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : Space) R.matchRadius)),
      D.cert.defect q σ y = O.centreCoefficient D R Pr σ y + ∑ i, q i • O.linearCoefficient D R Pr i σ y +
        ∑ i, ∑ m ∈ Finset.Ici i, (q i * q m) • O.quadraticCoefficient R i m σ y := by
    intro σ
    obtain ⟨-, -, hlc⟩ := hPress R.params Pr.centre hPv hPr.centre_valid
    obtain ⟨Lc, hLc⟩ := hlc R.matchRadius
    have hlt : ∀ i, ∃ L : NNReal, ∀ σ', LipschitzOnWith L (shapePressure R.params (Pr.tangent i) σ')
        (Metric.closedBall (0 : Space) R.matchRadius) := fun i =>
      (hPress R.params (Pr.tangent i) hPv (hPr.tangent_valid i)).2.2 R.matchRadius
    choose Lt hLt using hlt
    have h1 := (hLc σ).ae_differentiableWithinAt_of_mem (μ := (volume : Measure Space))
    have h2 : ∀ᵐ y ∂(volume : Measure Space), ∀ i, y ∈ Metric.closedBall (0 : Space) R.matchRadius →
        DifferentiableWithinAt ℝ (shapePressure R.params (Pr.tangent i) σ)
          (Metric.closedBall (0 : Space) R.matchRadius) y :=
      ae_all_iff.2 fun i => (hLt i σ).ae_differentiableWithinAt_of_mem
    have h3 : ∀ᵐ y ∂(volume : Measure Space), y ∉ Metric.sphere (0 : Space) R.matchRadius :=
      measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_sphere volume 0 R.matchRadius)
    rw [ae_restrict_iff' Metric.isClosed_closedBall.measurableSet]
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3 hyB
    have hy : ‖y‖ < R.matchRadius := lt_of_le_of_ne (mem_closedBall_zero_iff.1 hyB)
      (fun h => hy3 (mem_sphere_zero_iff_norm.2 h))
    have hn : Metric.closedBall (0 : Space) R.matchRadius ∈ 𝓝 y :=
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hy)) Metric.ball_subset_closedBall
    have E := defect_expands hBall hStep D R Pr O hR hPr hO.period_eq hO.multiplier_eq q hq σ y hy
      ((hy1 hyB).differentiableAt hn) (fun i => (hy2 i hyB).differentiableAt hn)
    unfold QuadExpands at E
    rw [E, sum_square_triangle q]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
    rw [quadCoeff_apply]
  rw [pairing_congr (Z := shapeInfoField Z.params (Z.field j)) hae, pairing_expand q tC tL tQ tZ]

theorem offsetBallIdentity_holds : OffsetBallIdentityHolds :=
  offsetBallIdentity_of ballAgreement_holds stepPhase_holds pressureFieldRegular_holds

end Instantiation
end CellReduction
end Breakdown
