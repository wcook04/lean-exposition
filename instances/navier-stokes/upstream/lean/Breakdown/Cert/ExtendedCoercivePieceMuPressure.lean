import Breakdown.Cert.ExtendedCoercivePairingSplit
import Breakdown.Cert.CoerciveSmoothPressure
import Breakdown.Cert.CoerciveSmoothPieceMuSeminorm
import Breakdown.Cert.CoerciveFieldModes
import Breakdown.Cert.ExtendedCoerciveSecondDerivSymm

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.WeakPieceMuPressure

open Coercive

variable {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D P : ℝ}

private theorem tensor_coord {u w : Space → Space} {y : Space} (du : DifferentiableAt ℝ u y)
    (dw : DifferentiableAt ℝ w y) (i j : Fin 3) :
    fderiv ℝ (fun x => w x j * u x i - u x j * w x i) y (unitVector j)
      = w y j * fderiv ℝ u y (unitVector j) i + u y i * fderiv ℝ w y (unitVector j) j
        - (u y j * fderiv ℝ w y (unitVector j) i + w y i * fderiv ℝ u y (unitVector j) j) := by
  have hc : ∀ (f : Space → Space) (k : Fin 3), DifferentiableAt ℝ f y →
      HasFDerivAt (fun x => f x k) ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).comp (fderiv ℝ f y)) y :=
    fun f k hf => (EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt.comp y hf.hasFDerivAt
  have hd : HasFDerivAt (fun x => w x j * u x i - u x j * w x i) _ y :=
    ((hc w j dw).mul (hc u i du)).sub ((hc u j du).mul (hc w i dw))
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  rfl

private theorem apply_coord (L : Space →L[ℝ] Space) (a : Space) (i : Fin 3) :
    L a i = ∑ j : Fin 3, a j * L (unitVector j) i := by
  rw [Coercive.Internal.SmoothPieceMuDivergence.clm_expand L a, Coercive.Internal.SmoothPieceMuDivergence.coord_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Coercive.Internal.SmoothPieceMuDivergence.coord_smul]

theorem tensor_orthogonal {u w : Space → Space} (hu : ContDiff ℝ 1 u) (hw : ContDiff ℝ 1 w)
    (hdu : ∀ x, divergenceAt u x = 0) (hdw : ∀ x, divergenceAt w x = 0)
    {p : Space → ℝ} (hp : ContDiff ℝ ∞ p) {R : ℝ} (hR : ∀ y, R < ‖y‖ → p y = 0) :
    ∫ y, inner ℝ (fderiv ℝ u y (w y) - fderiv ℝ w y (u y)) (gradientAt p y) = 0 := by
  have hLu : ∀ k : Fin 3, ContDiff ℝ 1 (fun x => u x k) := fun k =>
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp hu
  have hLw : ∀ k : Fin 3, ContDiff ℝ 1 (fun x => w x k) := fun k =>
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp hw
  have du : Differentiable ℝ u := hu.differentiable (by norm_num)
  have dw : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hF : ∀ i j : Fin 3, ContDiff ℝ 1 (fun x => w x j * u x i - u x j * w x i) := fun i j =>
    ((hLw j).mul (hLu i)).sub ((hLu j).mul (hLw i))
  have hDp : ContDiff ℝ ∞ (fderiv ℝ p) := hp.fderiv_right (m := ∞) (by simp)
  have hG : ∀ i : Fin 3, ContDiff ℝ ∞ (fun x => fderiv ℝ p x (unitVector i)) := fun i =>
    hDp.clm_apply contDiff_const
  have hpR : ∀ y, R < ‖y‖ → fderiv ℝ p y = 0 := fun y hy => PairingSplitInternal.fderiv_eq_zero_far hR hy
  have hGR : ∀ i : Fin 3, ∀ y, R < ‖y‖ → fderiv ℝ p y (unitVector i) = 0 := fun i y hy => by
    rw [hpR y hy]; rfl
  have hGR' : ∀ i : Fin 3, ∀ y, R < ‖y‖ → fderiv ℝ (fun x => fderiv ℝ p x (unitVector i)) y = 0 :=
    fun i y hy => PairingSplitInternal.fderiv_eq_zero_far (hGR i) hy
  have I1 : ∀ i j : Fin 3, Integrable (fun x => (w x j * u x i - u x j * w x i)
      * fderiv ℝ (fun x' => fderiv ℝ p x' (unitVector i)) x (unitVector j)) := fun i j =>
    Coercive.Internal.SmoothPairingClass.integrable_of_far
      ((hF i j).continuous.mul (((hG i).continuous_fderiv (by simp)).clm_apply continuous_const))
      fun y hy => by rw [hGR' i y hy]; simp
  have I2 : ∀ i j : Fin 3, Integrable (fun x => fderiv ℝ (fun x' => w x' j * u x' i - u x' j * w x' i) x (unitVector j)
      * fderiv ℝ p x (unitVector i)) := fun i j =>
    Coercive.Internal.SmoothPairingClass.integrable_of_far
      ((((hF i j).continuous_fderiv (by norm_num)).clm_apply continuous_const).mul (hG i).continuous)
      fun y hy => by rw [hGR i y hy]; simp
  have I3 : ∀ i j : Fin 3, Integrable (fun x => (w x j * u x i - u x j * w x i) * fderiv ℝ p x (unitVector i)) :=
    fun i j => Coercive.Internal.SmoothPairingClass.integrable_of_far ((hF i j).continuous.mul (hG i).continuous)
      fun y hy => by rw [hGR i y hy]; simp
  have step : ∀ i j : Fin 3, ∫ x, (w x j * u x i - u x j * w x i)
      * fderiv ℝ (fun x' => fderiv ℝ p x' (unitVector i)) x (unitVector j)
      = -∫ x, fderiv ℝ (fun x' => w x' j * u x' i - u x' j * w x' i) x (unitVector j)
        * fderiv ℝ p x (unitVector i) := fun i j =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (I2 i j) (I1 i j) (I3 i j)
      (fun x _ => ((hF i j).differentiable (by norm_num)) x) (fun x _ => ((hG i).differentiable (by simp)) x)
  have hpt : ∀ y, inner ℝ (fderiv ℝ u y (w y) - fderiv ℝ w y (u y)) (gradientAt p y)
      = ∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ (fun x' => w x' j * u x' i - u x' j * w x' i) y (unitVector j)
        * fderiv ℝ p y (unitVector i) := by
    intro y
    rw [Coercive.Internal.SmoothPairingClass.inner_gradientAt]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    simp only [tensor_coord (du y) (dw y) i]
    have ew : ∑ j : Fin 3, fderiv ℝ w y (unitVector j) j = 0 := hdw y
    have eu : ∑ j : Fin 3, fderiv ℝ u y (unitVector j) j = 0 := hdu y
    rw [PiLp.sub_apply, apply_coord (fderiv ℝ u y) (w y) i, apply_coord (fderiv ℝ w y) (u y) i]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ew, eu]
    ring
  have hsym : ∀ y, ∑ i : Fin 3, ∑ j : Fin 3, (w y j * u y i - u y j * w y i)
      * fderiv ℝ (fun x' => fderiv ℝ p x' (unitVector i)) y (unitVector j) = 0 := by
    intro y
    have hs := (hp.contDiffAt (x := y)).isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.mpr le_top)
    simp only [Internal.SecondDerivSymm.fderiv_fderiv_apply hp]
    have e := Finset.sum_comm (s := (Finset.univ : Finset (Fin 3))) (t := Finset.univ)
      (f := fun i j => (w y j * u y i - u y j * w y i) * fderiv ℝ (fderiv ℝ p) y (unitVector j) (unitVector i))
    have e2 : ∑ j : Fin 3, ∑ i : Fin 3, (w y j * u y i - u y j * w y i)
        * fderiv ℝ (fderiv ℝ p) y (unitVector j) (unitVector i)
        = -∑ i : Fin 3, ∑ j : Fin 3, (w y j * u y i - u y j * w y i)
          * fderiv ℝ (fderiv ℝ p) y (unitVector j) (unitVector i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hs (unitVector j) (unitVector i)]
      ring
    linarith
  calc ∫ y, inner ℝ (fderiv ℝ u y (w y) - fderiv ℝ w y (u y)) (gradientAt p y)
      = ∫ y, ∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ (fun x' => w x' j * u x' i - u x' j * w x' i) y (unitVector j)
        * fderiv ℝ p y (unitVector i) := integral_congr_ae (ae_of_all _ hpt)
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ y, fderiv ℝ (fun x' => w x' j * u x' i - u x' j * w x' i) y (unitVector j)
        * fderiv ℝ p y (unitVector i) := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => I2 i j]
        exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => I2 i j
    _ = ∑ i : Fin 3, ∑ j : Fin 3, -∫ x, (w x j * u x i - u x j * w x i)
        * fderiv ℝ (fun x' => fderiv ℝ p x' (unitVector i)) x (unitVector j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [step i j, neg_neg]
    _ = -∫ y, ∑ i : Fin 3, ∑ j : Fin 3, (w y j * u y i - u y j * w y i)
        * fderiv ℝ (fun x' => fderiv ℝ p x' (unitVector i)) y (unitVector j) := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => I1 i j, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => I1 i j, ← Finset.sum_neg_distrib]
    _ = 0 := by simp only [hsym, integral_zero, neg_zero]

theorem transport_orthogonal (hW : IsWeakSecondDerivState W HW D) {v : ℝ → Space → Space}
    (hv : IsSmoothPerturbation P v) (q : ℝ → Space → ℝ) (hq : IsPeriodicTestPotential q) :
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y) - fderiv ℝ (W σ) y (v σ y))
      (gradientAt (q σ) y) = 0 := by
  obtain ⟨hqs, -, R, hR⟩ := hq
  set Z : ℝ → Space → Space := fun _ _ => 0 with hZdef
  have hZ : ContDiff ℝ 2 (fun z : ℝ × Space => Z z.1 z.2) := contDiff_const
  have hZd : ∀ σ y, fderiv ℝ (Z σ) y = 0 := fun σ y => by simp [hZdef]
  have hZdiv : ∀ σ y, divergenceAt (Z σ) y = 0 := fun σ y => by
    unfold divergenceAt
    simp [hZd]
  have c6 : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (Z z.1) z.2 (v z.1 z.2)) :=
    (PairingSplitInternal.contDiff_slice (V := Z) hZ (by norm_num)).clm_apply (hv.smooth.of_le (by norm_cast))
  have hS : ContDiff ℝ 1 (fun z : ℝ × Space => smoothRight P Z v z.1 z.2 - fderiv ℝ (Z z.1) z.2 (v z.1 z.2) - fderiv ℝ (Z z.1) z.2 (v z.1 z.2)) :=
    ((Coercive.Internal.SmoothPairingClass.smoothRight_contDiff' hZ hv).sub c6).sub c6
  have e : ∀ σ, ∫ y, inner ℝ (smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y) - fderiv ℝ (W σ) y (v σ y))
      (gradientAt (q σ) y) = 0 := by
    intro σ
    have hqσ : ContDiff ℝ ∞ (q σ) := Coercive.Internal.SmoothPairingClass.slice_of_joint hqs σ
    have hSσ := Coercive.Internal.SmoothPairingClass.slice_of_joint
        (V := fun s x => smoothRight P Z v s x - fderiv ℝ (Z s) x (v s x) - fderiv ℝ (Z s) x (v s x)) hS σ
    have e1 := Coercive.Internal.SmoothPieceMuDivergence.orthogonal_of_div_zero hSσ
      (fun x => Coercive.Internal.SmoothPieceMuDivergence.innerPart_sub_div_zero P Z hZ hZdiv v hv σ x)
      hqσ (fun y hy => hR σ y hy)
    have hu : ContDiff ℝ 1 (v σ) :=
      (Coercive.Internal.SmoothPairingClass.slice_of_joint hv.smooth σ).of_le (by norm_cast)
    have hw : ContDiff ℝ 1 (W σ) := Coercive.Internal.SmoothPairingClass.slice_of_joint hW.smooth σ
    have e2 := tensor_orthogonal hu hw (hv.divergence_free σ) (hW.divergence_free σ) hqσ (fun y hy => hR σ y hy)
    have hpR : ∀ y, R < ‖y‖ → gradientAt (q σ) y = 0 := fun y hy => by
      unfold gradientAt
      rw [PairingSplitInternal.fderiv_eq_zero_far (fun x hx => hR σ x hx) hy]
      simp
    have hgc : Continuous (fun y => gradientAt (q σ) y) := by
      unfold gradientAt
      exact continuous_finsetSum _ fun i _ =>
        ((hqσ.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const
    have I1 : Integrable (fun y => inner ℝ (smoothRight P Z v σ y - fderiv ℝ (Z σ) y (v σ y) - fderiv ℝ (Z σ) y (v σ y))
        (gradientAt (q σ) y)) :=
      Coercive.Internal.SmoothPairingClass.integrable_of_far (hSσ.continuous.inner hgc)
        fun y hy => by rw [hpR y hy, inner_zero_right]
    have hc2 : Continuous (fun y => fderiv ℝ (v σ) y (W σ y) - fderiv ℝ (W σ) y (v σ y)) :=
      ((hu.continuous_fderiv (by norm_num)).clm_apply hw.continuous).sub
        ((hw.continuous_fderiv (by norm_num)).clm_apply hu.continuous)
    have I2 : Integrable (fun y => inner ℝ (fderiv ℝ (v σ) y (W σ y) - fderiv ℝ (W σ) y (v σ y))
        (gradientAt (q σ) y)) :=
      Coercive.Internal.SmoothPairingClass.integrable_of_far (hc2.inner hgc)
        fun y hy => by rw [hpR y hy, inner_zero_right]
    have hpt : ∀ y, inner ℝ (smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y) - fderiv ℝ (W σ) y (v σ y))
        (gradientAt (q σ) y) = inner ℝ (smoothRight P Z v σ y - fderiv ℝ (Z σ) y (v σ y) - fderiv ℝ (Z σ) y (v σ y))
          (gradientAt (q σ) y) + inner ℝ (fderiv ℝ (v σ) y (W σ y) - fderiv ℝ (W σ) y (v σ y))
          (gradientAt (q σ) y) := by
      intro y
      rw [← inner_add_left]
      congr 1
      have h0 : fderiv ℝ (fun _ : Space => (0 : Space)) y = 0 := by simp
      unfold smoothRight
      simp only [hZdef, h0, ContinuousLinearMap.zero_apply, map_zero]
      abel
    rw [integral_congr_ae (ae_of_all _ hpt), integral_add I1 I2, e1, e2, add_zero]
  simp only [e, integral_zero]

theorem solenoidal_split (hSolenoidal : SolenoidalModeHolds) (hW : IsWeakSecondDerivState W HW D)
    {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    (Q : ℝ → Space → Space) (hQ : IsSolenoidalPartOf (smoothRight P W v) Q) :
    AEStronglyMeasurable (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (v z.1 z.2)) volume ∧
      IsTimePeriodic (fun σ y => fderiv ℝ (W σ) y (v σ y)) ∧
      periodLIntegral (fun σ y => ‖fderiv ℝ (W σ) y (v σ y)‖ ^ 2) < ⊤ ∧
      AEStronglyMeasurable (fun z : ℝ × Space => smoothRight P W v z.1 z.2 - fderiv ℝ (W z.1) z.2 (v z.1 z.2)) volume ∧
      IsTimePeriodic (fun σ y => smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y)) ∧
      periodLIntegral (fun σ y => ‖smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y)‖ ^ 2) < ⊤ ∧
      ∃ Q', IsSolenoidalPartOf (fun σ y => fderiv ℝ (W σ) y (v σ y)) Q' ∧ ∀ᵐ z : ℝ × Space, Q z.1 z.2 =
        (smoothRight P W v z.1 z.2 - fderiv ℝ (W z.1) z.2 (v z.1 z.2))
          + ((2 : ℝ) • Q' z.1 z.2 - fderiv ℝ (W z.1) z.2 (v z.1 z.2)) := by
  have hD0 := Internal.WeakPairingSplit.decay_const_nonneg hW
  have dW : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
    PairingSplitInternal.contDiff_slice (V := W) hW.smooth (by norm_num)
  have cF : Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (v z.1 z.2)) :=
    dW.continuous.clm_apply hv.smooth.continuous
  have pF : IsTimePeriodic (fun σ y => fderiv ℝ (W σ) y (v σ y)) := by
    intro σ y
    have ev : v (σ + 1) = v σ := funext fun x => hv.periodic σ x
    have eW : W (σ + 1) = W σ := funext fun x => hW.periodic σ x
    show fderiv ℝ (W (σ + 1)) y (v (σ + 1) y) = _
    rw [ev, eW]
  have bF : ∀ σ y, ‖fderiv ℝ (W σ) y (v σ y)‖ ≤ D * (‖v σ y‖ / (1 + ‖y‖)) := by
    intro σ y
    have h1 : ‖fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖) ^ 2 := (hW.decay σ y).2.1
    exact ((fderiv ℝ (W σ) y).le_opNorm _).trans ((mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans
      (Coercive.Internal.SmoothPairingClass.div_pow_le_div hD0 (norm_nonneg _) (norm_nonneg y) (by norm_num)))
  have mF := Coercive.Internal.SmoothPairingClass.memLp_of_bound (h := fun σ y => ‖fderiv ℝ (W σ) y (v σ y)‖)
    (g := fun σ y => D * (‖v σ y‖ / (1 + ‖y‖))) cF.norm
    ((Coercive.Internal.SmoothPairingClass.memLp_weighted hv).const_mul D)
    (fun σ y => by rw [abs_norm]; exact bF σ y)
  have lF : periodLIntegral (fun σ y => ‖fderiv ℝ (W σ) y (v σ y)‖ ^ 2) < ⊤ :=
    Coercive.Internal.SmoothPairingClass.lt_top_of_memLp_real mF
  have sR := Internal.WeakPairingSplit.smoothRight_square hW hv
  have sF : ModeL2Internal.IsSquareField (fun σ y => fderiv ℝ (W σ) y (v σ y)) := ⟨cF.aestronglyMeasurable, pF, lF⟩
  have sS0 := PairingSplitInternal.square_lin sR sF 1 (-1)
  have eS : (fun σ y => (1 : ℝ) • smoothRight P W v σ y + (-1 : ℝ) • fderiv ℝ (W σ) y (v σ y))
      = fun σ y => smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y) := by
    funext σ y
    rw [one_smul, neg_one_smul, ← sub_eq_add_neg]
  rw [eS] at sS0
  have sD0 := PairingSplitInternal.square_lin sS0 sF 1 (-1)
  have eD : (fun σ y => (1 : ℝ) • (smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y)) + (-1 : ℝ) • fderiv ℝ (W σ) y (v σ y))
      = fun σ y => smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y) - fderiv ℝ (W σ) y (v σ y) := by
    funext σ y
    rw [one_smul, neg_one_smul, ← sub_eq_add_neg]
  rw [eD] at sD0
  refine ⟨sF.1, sF.2.1, sF.2.2, sS0.1, sS0.2.1, sS0.2.2, ?_⟩
  obtain ⟨Q', hQ', -, -, -, -⟩ := hSolenoidal _ sF.1 sF.2.1 sF.2.2
  refine ⟨Q', hQ', ?_⟩
  have hDD : IsSolenoidalPartOf (fun σ y => smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y) - fderiv ℝ (W σ) y (v σ y))
      (fun σ y => smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y) - fderiv ℝ (W σ) y (v σ y)) :=
    ⟨sD0.1, sD0.2.1, sD0.2.2, fun q hq => transport_orthogonal hW hv q hq, fun _ _ => rfl⟩
  have hFF := PairingSplitInternal.solenoidal_add sF sF hQ' hQ'
  have hsum := PairingSplitInternal.solenoidal_add sD0 (PairingSplitInternal.square_add sF sF) hDD hFF
  have hsum' : IsSolenoidalPartOf (smoothRight P W v)
      (fun σ y => (smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y) - fderiv ℝ (W σ) y (v σ y)) + (Q' σ y + Q' σ y)) := by
    convert hsum using 1
    funext σ y
    abel
  obtain ⟨Q₀, -, -, -, huniq, -⟩ := hSolenoidal _ sR.1 sR.2.1 sR.2.2
  filter_upwards [huniq Q hQ, huniq _ hsum'] with z h1 h2
  rw [h1, ← h2, two_smul]
  abel

end Internal.WeakPieceMuPressure

end CoerciveWeak

end Breakdown
