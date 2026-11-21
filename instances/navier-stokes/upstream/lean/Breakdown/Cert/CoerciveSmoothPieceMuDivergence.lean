import Breakdown.Cert.CoerciveSmoothPairingSplitClass
import Breakdown.Cert.CoerciveEnergyIdentityStretch
import Breakdown.Cert.CoerciveModeRotation

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceMuDivergence

theorem coord_sum (a : Fin 3 → Space) (i : Fin 3) : (∑ j, a j) i = ∑ j, a j i := by
  rw [← PairingSplitInternal.proj_apply, map_sum]
  rfl

theorem coord_smul (c : ℝ) (a : Space) (i : Fin 3) : (c • a) i = c * a i := by
  rw [← PairingSplitInternal.proj_apply, map_smul]
  rfl

theorem clm_expand (L : Space →L[ℝ] Space) (u : Space) : L u = ∑ k : Fin 3, u k • L (unitVector k) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr u]
  simp [unitVector, map_sum, map_smul]

theorem trace_comp_comm (M N : Space →L[ℝ] Space) :
    ∑ i : Fin 3, M (N (unitVector i)) i = ∑ i : Fin 3, N (M (unitVector i)) i := by
  have h1 : ∀ i, M (N (unitVector i)) i = ∑ j : Fin 3, N (unitVector i) j * M (unitVector j) i := fun i => by
    rw [clm_expand M, coord_sum]
    simp only [coord_smul]
  have h2 : ∀ i, N (M (unitVector i)) i = ∑ j : Fin 3, M (unitVector i) j * N (unitVector j) i := fun i => by
    rw [clm_expand N, coord_sum]
    simp only [coord_smul]
  simp only [h1, h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem second_trace_zero {u : Space → Space} {n : WithTop ℕ∞} (hu : ContDiff ℝ n u) (hn : 2 ≤ n)
    (hd : ∀ y, divergenceAt u y = 0) (y a : Space) :
    ∑ i : Fin 3, fderiv ℝ (fun x => fderiv ℝ u x) y a (unitVector i) i = 0 := by
  have hD : Differentiable ℝ (fun x => fderiv ℝ u x) :=
    (hu.fderiv_right (m := 1) (le_trans (by norm_num) hn)).differentiable (by norm_num)
  have hi : ∀ i : Fin 3, HasFDerivAt (fun x => (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (fderiv ℝ u x (unitVector i)))
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp ((fderiv ℝ (fun x => fderiv ℝ u x) y).flip (unitVector i))) y := by
    intro i
    have h1 : HasFDerivAt (fun x => fderiv ℝ u x (unitVector i))
        ((fderiv ℝ (fun x => fderiv ℝ u x) y).flip (unitVector i)) y := by
      have := (hD y).hasFDerivAt.clm_apply (hasFDerivAt_const (unitVector i) y)
      simpa using this
    exact (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y h1
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => hi i
  have hz : (fun x => ∑ i : Fin 3, (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (fderiv ℝ u x (unitVector i)))
      = fun _ => 0 := funext fun x => hd x
  rw [hz] at hs
  have := congrArg (fun L : Space →L[ℝ] ℝ => L a) (hs.unique (hasFDerivAt_const (0 : ℝ) y))
  simpa using this

theorem time_deriv_trace_zero {v : ℝ → Space → Space} (hv : ContDiff ℝ ∞ (fun z : ℝ × Space => v z.1 z.2))
    (hdiv : ∀ σ y, divergenceAt (v σ) y = 0) (σ : ℝ) (y : Space) :
    ∑ i : Fin 3, fderiv ℝ (fun x => deriv (fun s => v s x) σ) y (unitVector i) i = 0 := by
  set F : ℝ × Space → Space := fun z => v z.1 z.2 with hFdef
  have hF : ContDiff ℝ ∞ F := hv
  have dF : Differentiable ℝ F := hF.differentiable (by simp)
  have dG : Differentiable ℝ (fderiv ℝ F) := (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have t1 : (fun x => deriv (fun s => v s x) σ) = fun x => fderiv ℝ F (σ, x) ((1 : ℝ), (0 : Space)) := by
    funext x
    have h1 : HasDerivAt (fun s : ℝ => ((s, x) : ℝ × Space)) ((1 : ℝ), (0 : Space)) σ :=
      (hasDerivAt_id σ).prodMk (hasDerivAt_const σ x)
    exact ((dF (σ, x)).hasFDerivAt.comp_hasDerivAt σ h1).deriv
  have t2 : ∀ s x e, fderiv ℝ (v s) x e = fderiv ℝ F (s, x) ((0 : ℝ), e) := by
    intro s x e
    have h1 : HasFDerivAt (fun x' : Space => ((s, x') : ℝ × Space))
        ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) x :=
      (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
    have h2 : HasFDerivAt (v s) ((fderiv ℝ F (s, x)).comp
        ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space))) x :=
      (dF (s, x)).hasFDerivAt.comp x h1
    rw [h2.fderiv]
    simp
  have h1y : HasFDerivAt (fun x' : Space => ((σ, x') : ℝ × Space))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y :=
    (hasFDerivAt_const σ y).prodMk (hasFDerivAt_id y)
  have hc : HasFDerivAt (fun x => fderiv ℝ F (σ, x)) ((fderiv ℝ (fderiv ℝ F) (σ, y)).comp
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space))) y :=
    (dG (σ, y)).hasFDerivAt.comp y h1y
  have hφ := hc.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : Space)) y)
  have key : ∀ e, fderiv ℝ (fun x => fderiv ℝ F (σ, x) ((1 : ℝ), (0 : Space))) y e
      = fderiv ℝ (fderiv ℝ F) (σ, y) ((0 : ℝ), e) ((1 : ℝ), (0 : Space)) := by
    intro e
    rw [hφ.fderiv]
    simp
  have hct : HasDerivAt (fun s => fderiv ℝ F (s, y)) (fderiv ℝ (fderiv ℝ F) (σ, y) ((1 : ℝ), (0 : Space))) σ :=
    (dG (σ, y)).hasFDerivAt.comp_hasDerivAt σ ((hasDerivAt_id σ).prodMk (hasDerivAt_const σ y))
  have hLi : ∀ i : Fin 3, HasDerivAt (fun s => ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ Space ((0 : ℝ), unitVector i))) (fderiv ℝ F (s, y)))
      (((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ Space ((0 : ℝ), unitVector i))) (fderiv ℝ (fderiv ℝ F) (σ, y) ((1 : ℝ), (0 : Space)))) σ :=
    fun i => ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ Space ((0 : ℝ), unitVector i))).hasFDerivAt.comp_hasDerivAt σ hct
  have hψ := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hLi i
  have hz : (fun s => ∑ i ∈ Finset.univ, ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ Space ((0 : ℝ), unitVector i))) (fderiv ℝ F (s, y))) = fun _ => 0 := by
    funext s
    have h := hdiv s y
    unfold divergenceAt at h
    simp only [t2] at h
    simpa using h
  rw [hz] at hψ
  have hu := hψ.unique (hasDerivAt_const σ (0 : ℝ))
  have hsym : ∀ e, fderiv ℝ (fderiv ℝ F) (σ, y) ((0 : ℝ), e) ((1 : ℝ), (0 : Space))
      = fderiv ℝ (fderiv ℝ F) (σ, y) ((1 : ℝ), (0 : Space)) ((0 : ℝ), e) := fun e =>
    (hF.contDiffAt.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.mpr le_top)) _ _
  rw [t1]
  simp only [key, hsym]
  simpa using hu

theorem innerPart_sub_div_zero (P : ℝ) (W : ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (σ : ℝ) (y : Space) :
    divergenceAt (fun x => smoothRight P W v σ x - fderiv ℝ (W σ) x (v σ x) - fderiv ℝ (W σ) x (v σ x)) y = 0 := by
  have hu : ContDiff ℝ ∞ (v σ) := Internal.SmoothPairingClass.slice_of_joint hv.smooth σ
  have hw : ContDiff ℝ 2 (W σ) := Internal.SmoothPairingClass.slice_of_joint hW σ
  have hτ : ContDiff ℝ ∞ (fun x => deriv (fun s => v s x) σ) :=
    Internal.SmoothPairingClass.slice_of_joint (V := fun s x => deriv (fun s' => v s' x) s)
      (Internal.SmoothPairingClass.time_contDiff hv.smooth) σ
  have dU : Differentiable ℝ (fderiv ℝ (v σ)) :=
    (hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have dW : Differentiable ℝ (fderiv ℝ (W σ)) :=
    (hw.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have dH : Differentiable ℝ (fun x => secondDerivTrace (secondDerivField v σ x)) := by
    have e : (fun x => secondDerivTrace (secondDerivField v σ x)) = fun x =>
        Internal.SmoothPairingClass.traceCLM (fderiv ℝ (fderiv ℝ (v σ)) x) :=
      funext fun x => (Internal.SmoothPairingClass.traceCLM_apply _).symm
    rw [e]
    exact Internal.SmoothPairingClass.traceCLM.differentiable.comp
      (((hu.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).differentiable (by simp))
  have h1 := ((hτ.differentiable (by simp)) y).hasFDerivAt
  have h2 := ((hu.differentiable (by simp)) y).hasFDerivAt
  have h3 := (dU y).hasFDerivAt.clm_apply (hasFDerivAt_id y)
  have h4 := (dH y).hasFDerivAt
  have h5 := (dU y).hasFDerivAt.clm_apply ((hw.differentiable (by norm_num)) y).hasFDerivAt
  have h6 := (dW y).hasFDerivAt.clm_apply ((hu.differentiable (by simp)) y).hasFDerivAt
  have hf : HasFDerivAt (fun x => smoothRight P W v σ x - fderiv ℝ (W σ) x (v σ x) - fderiv ℝ (W σ) x (v σ x))
      _ y := ((((((((h1.const_smul (1 / P)).add (h2.const_smul (1 / 2 : ℝ))).add (h3.const_smul (1 / 2 : ℝ))).sub h4).add
        h5).add h6).sub h6).sub h6)
  have sτ := time_deriv_trace_zero hv.smooth hv.divergence_free σ y
  have su : ∑ i : Fin 3, fderiv ℝ (v σ) y (unitVector i) i = 0 := hv.divergence_free σ y
  have sX : ∑ i : Fin 3, fderiv ℝ (fderiv ℝ (v σ)) y (unitVector i) y i = 0 := by
    have h := second_trace_zero hu (WithTop.coe_le_coe.mpr le_top) (hv.divergence_free σ) y y
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [EnergyIdentityInternal.d2_symm (v σ) hu y]
  have sA : ∑ i : Fin 3, fderiv ℝ (fderiv ℝ (v σ)) y (unitVector i) (W σ y) i = 0 := by
    have h := second_trace_zero hu (WithTop.coe_le_coe.mpr le_top) (hv.divergence_free σ) y (W σ y)
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [EnergyIdentityInternal.d2_symm (v σ) hu y]
  have sB : ∑ i : Fin 3, fderiv ℝ (fderiv ℝ (W σ)) y (unitVector i) (v σ y) i = 0 := by
    have h := second_trace_zero hw le_rfl (hWdiv σ) y (v σ y)
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [EnergyIdentityInternal.d2_symm_two (W σ) hw y]
  have sH : ∑ i : Fin 3, fderiv ℝ (fun x => secondDerivTrace (secondDerivField v σ x)) y (unitVector i) i = 0 := by
    have h := Internal.SmoothPairingClass.divergence_negSsp hu (hv.divergence_free σ) y
    unfold divergenceAt at h
    rw [fderiv_fun_neg] at h
    simp only [ContinuousLinearMap.neg_apply, PiLp.neg_apply, Finset.sum_neg_distrib, neg_eq_zero] at h
    exact h
  have sC := trace_comp_comm (fderiv ℝ (v σ) y) (fderiv ℝ (W σ) y)
  unfold divergenceAt
  rw [hf.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, id_eq,
    PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  linear_combination (1 / P) * sτ + (1 / 2 : ℝ) * su + (1 / 2 : ℝ) * (su + sX) - sH + sA - sB + sC

theorem orthogonal_of_div_zero {f : Space → Space} (hf : ContDiff ℝ 1 f) (hdiv : ∀ x, divergenceAt f x = 0)
    {p : Space → ℝ} (hp : ContDiff ℝ ∞ p) {R : ℝ} (hR : ∀ y, R < ‖y‖ → p y = 0) :
    ∫ y, inner ℝ (f y) (gradientAt p y) = 0 := by
  have hLi : ∀ i : Fin 3, ContDiff ℝ 1 (fun x => f x i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hf
  have dL : Differentiable ℝ f := hf.differentiable (by norm_num)
  have dLi : ∀ i : Fin 3, Differentiable ℝ (fun x => f x i) := fun i => (hLi i).differentiable (by norm_num)
  have dp : Differentiable ℝ p := hp.differentiable (by simp)
  have cDp : Continuous (fun x => fderiv ℝ p x) := hp.continuous_fderiv (by simp)
  have cDLi : ∀ i : Fin 3, Continuous (fun x => fderiv ℝ (fun x' => f x' i) x) := fun i =>
    (hLi i).continuous_fderiv (by norm_num)
  have hpR : ∀ y, R < ‖y‖ → fderiv ℝ p y = 0 := fun y hy => PairingSplitInternal.fderiv_eq_zero_far hR hy
  have I1 : ∀ i : Fin 3, Integrable (fun x => f x i * fderiv ℝ p x (unitVector i)) := fun i =>
    Internal.SmoothPairingClass.integrable_of_far (((hLi i).continuous).mul (cDp.clm_apply continuous_const))
      fun y hy => by rw [hpR y hy]; simp
  have I2 : ∀ i : Fin 3, Integrable (fun x => fderiv ℝ (fun x' => f x' i) x (unitVector i) * p x) := fun i =>
    Internal.SmoothPairingClass.integrable_of_far (((cDLi i).clm_apply continuous_const).mul hp.continuous)
      fun y hy => by rw [hR y hy]; simp
  have I3 : ∀ i : Fin 3, Integrable (fun x => f x i * p x) := fun i =>
    Internal.SmoothPairingClass.integrable_of_far ((hLi i).continuous.mul hp.continuous)
      fun y hy => by rw [hR y hy]; simp
  have step : ∀ i : Fin 3, ∫ x, f x i * fderiv ℝ p x (unitVector i)
      = -∫ x, fderiv ℝ (fun x' => f x' i) x (unitVector i) * p x := fun i =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (I2 i) (I1 i) (I3 i) (fun x _ => dLi i x)
      (fun x _ => dp x)
  have hdivL : ∀ x, ∑ i : Fin 3, fderiv ℝ (fun x' => f x' i) x (unitVector i) = 0 := fun x => by
    have h := hdiv x
    unfold divergenceAt at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact PairingSplitInternal.fderiv_component (dL x) i (unitVector i)
  calc ∫ y, inner ℝ (f y) (gradientAt p y) = ∫ y, ∑ i : Fin 3, f y i * fderiv ℝ p y (unitVector i) := by
        congr 1; funext y; exact Internal.SmoothPairingClass.inner_gradientAt _ _ _
    _ = ∑ i : Fin 3, ∫ y, f y i * fderiv ℝ p y (unitVector i) :=
        integral_finsetSum _ fun i _ => I1 i
    _ = ∑ i : Fin 3, -∫ y, fderiv ℝ (fun x' => f x' i) y (unitVector i) * p y :=
        Finset.sum_congr rfl fun i _ => step i
    _ = -∫ y, ∑ i : Fin 3, fderiv ℝ (fun x' => f x' i) y (unitVector i) * p y := by
        rw [Finset.sum_neg_distrib, integral_finsetSum _ fun i _ => I2 i]
    _ = 0 := by
        have e : (fun y => ∑ i : Fin 3, fderiv ℝ (fun x' => f x' i) y (unitVector i) * p y) = fun _ => 0 :=
          funext fun y => by rw [← Finset.sum_mul, hdivL y, zero_mul]
        rw [e]; simp

theorem modeVel_neg (ι : ℤ × ℤ) (X : ℝ → Space → Space) (σ : ℝ) (y : Space) (i : Fin 3) :
    modeVel (-ι) X σ y i = (starRingEnd ℂ) (modeVel ι X σ y i) := by
  unfold modeVel modeAverage
  simp only [map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal, Prod.fst_neg, Prod.snd_neg,
    Int.cast_neg]
  rw [← intervalIntegral.intervalIntegral_conj]
  refine congrArg (fun t => (1 / (2 * (Real.pi : ℂ))) * t) (intervalIntegral.integral_congr fun τ _ => ?_)
  rw [← intervalIntegral.intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun φ _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem modeVel_shiftRot (ι : ℤ × ℤ) (X : ℝ → Space → Space) (hX : IsTimePeriodic X) (τ₀ φ₀ σ : ℝ)
    (y : Space) (i : Fin 3) :
    modeVel ι (fun s x => axialRot (-φ₀) (X (s + τ₀) (axialRot φ₀ x))) σ y i
      = Complex.exp (((2 * Real.pi * ι.1 * τ₀ + ι.2 * φ₀ : ℝ) : ℂ) * Complex.I) * modeVel ι X σ y i := by
  have hRot := axialRotationHolds_proof
  obtain ⟨r, hr⟩ : ∃ r : ℝ → ℝ → ℂ, r = fun t p => ((axialRot (-p) (X (σ + t) (axialRot p y)) i : ℝ) : ℂ) :=
    ⟨_, rfl⟩
  have hrp : ∀ t, Function.Periodic (r t) (2 * Real.pi) := by
    intro t p
    rw [hr]
    simp only
    rw [hRot.2.2.2.1 p y, show -(p + 2 * Real.pi) = -p - 2 * Real.pi by ring,
      Internal.ModeRotation.axialRot_sub_period hRot]
  have hrt : ∀ t p, r (t + 1) p = r t p := by
    intro t p
    rw [hr]
    simp only
    rw [show σ + (t + 1) = (σ + t) + 1 by ring, hX]
  have step0 : ∀ τ φ, ((axialRot (-φ) (X (σ + τ) (axialRot φ y)) i : ℝ) : ℂ) = r τ φ := by
    intro τ φ
    rw [hr]
  have step1 : ∀ τ φ, ((axialRot (-φ) (axialRot (-φ₀) (X (σ + τ + τ₀) (axialRot φ₀ (axialRot φ y)))) i : ℝ) : ℂ)
      = r (τ + τ₀) (φ + φ₀) := by
    intro τ φ
    rw [hr]
    simp only
    rw [← hRot.2.1, ← hRot.2.1, show -φ + -φ₀ = -(φ + φ₀) by ring, show φ₀ + φ = φ + φ₀ by ring,
      show σ + τ + τ₀ = σ + (τ + τ₀) by ring]
  have inner : ∀ τ, ∫ φ in (0 : ℝ)..(2 * Real.pi), Internal.ModeRotation.expFactor ι τ φ * r (τ + τ₀) (φ + φ₀)
      = Complex.exp (((ι.2 * φ₀ : ℝ) : ℂ) * Complex.I)
        * ∫ φ in (0 : ℝ)..(2 * Real.pi), Internal.ModeRotation.expFactor ι τ φ * r (τ + τ₀) φ :=
    fun τ => Internal.ModeRotation.integral_shift ι τ φ₀ (r (τ + τ₀)) (hrp _)
  have efac : ∀ τ φ, Internal.ModeRotation.expFactor ι τ φ
      = Complex.exp (((2 * Real.pi * ι.1 * τ₀ : ℝ) : ℂ) * Complex.I) * Internal.ModeRotation.expFactor ι (τ + τ₀) φ := by
    intro τ φ
    unfold Internal.ModeRotation.expFactor
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have eper : ∀ t φ, Internal.ModeRotation.expFactor ι (t + 1) φ = Internal.ModeRotation.expFactor ι t φ := by
    intro t φ
    unfold Internal.ModeRotation.expFactor
    have h : -(((2 * Real.pi * ι.1 * (t + 1) + ι.2 * φ : ℝ) : ℂ) * Complex.I) =
        -(((2 * Real.pi * ι.1 * t + ι.2 * φ : ℝ) : ℂ) * Complex.I) + ((-ι.1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      ring
    rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  obtain ⟨H, hH⟩ : ∃ H : ℝ → ℂ, H = fun t => ∫ φ in (0 : ℝ)..(2 * Real.pi), Internal.ModeRotation.expFactor ι t φ * r t φ :=
    ⟨_, rfl⟩
  have hHp : Function.Periodic H 1 := by
    intro t
    rw [hH]
    simp only [eper, hrt]
  have outer : ∀ τ, ∫ φ in (0 : ℝ)..(2 * Real.pi), Internal.ModeRotation.expFactor ι τ φ * r (τ + τ₀) φ
      = Complex.exp (((2 * Real.pi * ι.1 * τ₀ : ℝ) : ℂ) * Complex.I) * H (τ + τ₀) := by
    intro τ
    rw [hH]
    simp only [efac τ, mul_assoc, intervalIntegral.integral_const_mul]
  have hshift : ∫ τ in (0 : ℝ)..1, H (τ + τ₀) = ∫ τ in (0 : ℝ)..1, H τ := by
    rw [intervalIntegral.integral_comp_add_right H τ₀, zero_add, add_comm (1 : ℝ) τ₀,
      hHp.intervalIntegral_add_eq τ₀ 0, zero_add]
  have hexp : Complex.exp (((2 * Real.pi * ι.1 * τ₀ + ι.2 * φ₀ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((ι.2 * φ₀ : ℝ) : ℂ) * Complex.I) * Complex.exp (((2 * Real.pi * ι.1 * τ₀ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold modeVel
  rw [Internal.ModeRotation.modeAverage_eq, Internal.ModeRotation.modeAverage_eq]
  simp only [step0, step1, inner, outer, intervalIntegral.integral_const_mul, hshift]
  rw [hH, hexp]
  ring

end Internal.SmoothPieceMuDivergence

end Coercive

end Breakdown
