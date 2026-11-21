import Breakdown.Cert.CoerciveSmoothPieceEpsCompression

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceEpsCore

open Internal.PieceAbsorb

private theorem frame_alg (a b : Fin 3 → Fin 3 → ℝ) (ha : a 0 0 + a 1 1 + a 2 2 = 0)
    (hb : b 0 0 + b 1 1 + b 2 2 = 0) (i : Fin 3) :
    ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l *
        (∑ k : Fin 3, b j k * a k l + ∑ k : Fin 3, a j k * b k l)
      = -(∑ k : Fin 3, (∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol k j l * a j l) * b k i)
        - ∑ k : Fin 3, (∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol k j l * b j l) * a k i := by
  fin_cases i <;> simp [Fin.sum_univ_three, alternatingSymbol]
  · linear_combination (b 1 2 - b 2 1) * ha + (a 1 2 - a 2 1) * hb
  · linear_combination (b 2 0 - b 0 2) * ha + (a 2 0 - a 0 2) * hb
  · linear_combination (b 0 1 - b 1 0) * ha + (a 0 1 - a 1 0) * hb

private theorem apply_expand (A : Space →L[ℝ] Space) (x : Space) (i : Fin 3) :
    A x i = ∑ k : Fin 3, x k * A (unitVector k) i := by
  have hx : x = ∑ k : Fin 3, x k • unitVector k := by
    ext m
    fin_cases m <;> simp [unitVector, Fin.sum_univ_three]
  conv_lhs => rw [hx]
  simp only [map_sum, map_smul]
  simp [Fin.sum_univ_three]

private theorem curl_comp_pair (A B : Space →L[ℝ] Space) (hA : ∑ i : Fin 3, A (unitVector i) i = 0)
    (hB : ∑ i : Fin 3, B (unitVector i) i = 0) :
    curlVec (A.comp B) + curlVec (B.comp A) = -(B (curlVec A)) - A (curlVec B) := by
  have e := fun i => frame_alg (fun j l => A (unitVector j) l) (fun j l => B (unitVector j) l)
    (by simpa [Fin.sum_univ_three] using hA) (by simpa [Fin.sum_univ_three] using hB) i
  ext i
  have ei := e i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply]
  rw [apply_expand B (curlVec A) i, apply_expand A (curlVec B) i]
  simp only [StretchInternal.curlVec_apply, ContinuousLinearMap.comp_apply]
  have hAB : ∀ j l, A (B (unitVector j)) l = ∑ k : Fin 3, B (unitVector j) k * A (unitVector k) l :=
    fun j l => apply_expand A _ l
  have hBA : ∀ j l, B (A (unitVector j)) l = ∑ k : Fin 3, A (unitVector j) k * B (unitVector k) l :=
    fun j l => apply_expand B _ l
  simp only [hAB, hBA]
  simp only [Fin.sum_univ_three] at ei ⊢
  linear_combination ei

private theorem hasDerivAt_curlVec {G : ℝ → Space →L[ℝ] Space} {G' : Space →L[ℝ] Space} {σ : ℝ}
    (h : ∀ u, HasDerivAt (fun s => G s u) (G' u) σ) :
    HasDerivAt (fun s => curlVec (G s)) (curlVec G') σ := by
  have hc : ∀ i j l : Fin 3, HasDerivAt (fun s => G s (unitVector j) l) (G' (unitVector j) l) σ := by
    intro i j l
    have h1 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) l).hasFDerivAt.comp_hasDerivAt σ (h (unitVector j))
    exact h1
  have hs : ∀ i : Fin 3, HasDerivAt
      (fun s => (∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * G s (unitVector j) l) • unitVector i)
      ((∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * G' (unitVector j) l) • unitVector i) σ := by
    intro i
    have h2 : HasDerivAt (fun s => ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * G s (unitVector j) l)
        (∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * G' (unitVector j) l) σ :=
      HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun l _ => (hc i j l).const_mul _
    exact h2.smul_const (unitVector i)
  unfold curlVec
  exact HasDerivAt.fun_sum fun i _ => hs i

private theorem flip_eq_of_symm {f : Space → Space} {y : Space} (hf : IsSymmSndFDerivAt ℝ f y) (u : Space) :
    (fderiv ℝ (fderiv ℝ f) y).flip u = fderiv ℝ (fderiv ℝ f) y u := by
  ext w : 1
  rw [ContinuousLinearMap.flip_apply]
  exact hf w u

theorem vortField_identity {P a : ℝ} {W v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0) (σ : ℝ)
    (y : Space) :
    vortField (smoothRight P W v) σ y - vortField (negSumSecondPartials v) σ y
      = (1 / P) • deriv (fun s => vortField v s y) σ + vortField v σ y
        + a • (fderiv ℝ (vortField v σ) y (axialPerp y) - axialPerp (vortField v σ y)) + frameRest a W v σ y := by
  have hvs : ContDiff ℝ ∞ (v σ) := hv.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hWs : ContDiff ℝ 2 (W σ) := slice_contDiff hW σ
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 2
  have hvd : Differentiable ℝ (v σ) := hvs.differentiable (by simp)
  have hWd : Differentiable ℝ (W σ) := hWs.differentiable (by norm_num)
  have hD1 : ContDiff ℝ ∞ (fderiv ℝ (v σ)) := hvs.fderiv_right (m := ∞) (by simp)
  have hD : Differentiable ℝ (fderiv ℝ (v σ)) := hD1.differentiable (by simp)
  have hDD : Differentiable ℝ (fderiv ℝ (fderiv ℝ (v σ))) :=
    (hD1.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hE : Differentiable ℝ (fderiv ℝ (W σ)) :=
    (hWs.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hTs : ContDiff ℝ ∞ (fun x => deriv (fun s => v s x) σ) :=
    (Internal.SmoothPieceEpsFrequency.timeDeriv_smooth hv.smooth).comp (contDiff_const.prodMk contDiff_id)
  have hTd : Differentiable ℝ (fun x => deriv (fun s => v s x) σ) := hTs.differentiable (by simp)
  have hHc : ContDiff ℝ ∞ (fun x => secondDerivTrace (secondDerivField v σ x)) := by
    unfold secondDerivTrace secondDerivField
    exact ContDiff.sum fun j _ =>
      ((hD1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).clm_apply contDiff_const
  have hHd : Differentiable ℝ (fun x => secondDerivTrace (secondDerivField v σ x)) := hHc.differentiable (by simp)
  have hsv : IsSymmSndFDerivAt ℝ (v σ) y :=
    hvs.contDiffAt.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  have hsW : IsSymmSndFDerivAt ℝ (W σ) y :=
    hWs.contDiffAt.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])
  set D := fderiv ℝ (v σ) y with hDdef
  set E := fderiv ℝ (W σ) y with hEdef
  set D2 := fderiv ℝ (fderiv ℝ (v σ)) y with hD2def
  set E2 := fderiv ℝ (fderiv ℝ (W σ)) y with hE2def
  set T' := fderiv ℝ (fun x => deriv (fun s => v s x) σ) y with hT'def
  set H' := fderiv ℝ (fun x => secondDerivTrace (secondDerivField v σ x)) y with hH'def
  have hR : HasFDerivAt (fun x => (1 / P) • deriv (fun s => v s x) σ + (1 / 2 : ℝ) • v σ x
      + (1 / 2 : ℝ) • fderiv ℝ (v σ) x x + fderiv ℝ (v σ) x (W σ x) + fderiv ℝ (W σ) x (v σ x))
      ((1 / P) • T' + (1 / 2 : ℝ) • D + (1 / 2 : ℝ) • (D.comp (ContinuousLinearMap.id ℝ Space) + D2.flip y)
        + (D.comp E + D2.flip (W σ y)) + (E.comp D + E2.flip (v σ y))) y := by
    have h1 := (hTd y).hasFDerivAt.const_smul (1 / P)
    have h2 := (hvd y).hasFDerivAt.const_smul (1 / 2 : ℝ)
    have h3 := ((hD y).hasFDerivAt.clm_apply (hasFDerivAt_id y)).const_smul (1 / 2 : ℝ)
    have h4 := (hD y).hasFDerivAt.clm_apply (hWd y).hasFDerivAt
    have h5 := (hE y).hasFDerivAt.clm_apply (hvd y).hasFDerivAt
    exact (((h1.add h2).add h3).add h4).add h5
  have eS : smoothRight P W v σ = fun x => -secondDerivTrace (secondDerivField v σ x)
      + ((1 / P) • deriv (fun s => v s x) σ + (1 / 2 : ℝ) • v σ x
      + (1 / 2 : ℝ) • fderiv ℝ (v σ) x x + fderiv ℝ (v σ) x (W σ x) + fderiv ℝ (W σ) x (v σ x)) := by
    funext x
    show smoothRight P W v σ x = _
    unfold smoothRight secondDerivField
    abel
  have eN : negSumSecondPartials v σ = fun x => -secondDerivTrace (secondDerivField v σ x) := rfl
  have hS : HasFDerivAt (fun x => -secondDerivTrace (secondDerivField v σ x)
      + ((1 / P) • deriv (fun s => v s x) σ + (1 / 2 : ℝ) • v σ x
      + (1 / 2 : ℝ) • fderiv ℝ (v σ) x x + fderiv ℝ (v σ) x (W σ x) + fderiv ℝ (W σ) x (v σ x)))
      (-H' + ((1 / P) • T' + (1 / 2 : ℝ) • D + (1 / 2 : ℝ) • (D.comp (ContinuousLinearMap.id ℝ Space) + D2.flip y)
        + (D.comp E + D2.flip (W σ y)) + (E.comp D + E2.flip (v σ y)))) y :=
    (hHd y).hasFDerivAt.neg.add hR
  have hN : HasFDerivAt (fun x => -secondDerivTrace (secondDerivField v σ x)) (-H') y := (hHd y).hasFDerivAt.neg
  have lhs : vortField (smoothRight P W v) σ y - vortField (negSumSecondPartials v) σ y
      = Internal.SmoothPieceEps.curlLinear ((1 / P) • T' + (1 / 2 : ℝ) • D
        + (1 / 2 : ℝ) • (D.comp (ContinuousLinearMap.id ℝ Space) + D2.flip y)
        + (D.comp E + D2.flip (W σ y)) + (E.comp D + E2.flip (v σ y))) := by
    show curlVec (fderiv ℝ (smoothRight P W v σ) y) - curlVec (fderiv ℝ (negSumSecondPartials v σ) y) = _
    rw [eS, eN, hS.fderiv, hN.fderiv, ← Internal.SmoothPieceEps.curlLinear_apply,
      ← Internal.SmoothPieceEps.curlLinear_apply, map_add]
    abel
  have ht : deriv (fun s => vortField v s y) σ = Internal.SmoothPieceEps.curlLinear T' :=
    (hasDerivAt_curlVec fun u => Internal.SmoothPieceEpsFrequency.hasDerivAt_gradField_time hv.smooth σ y u).deriv
  have hgv : fderiv ℝ (vortField v σ) y = Internal.SmoothPieceEps.curlLinear.comp D2 := vortGrad_eq hv2 σ y
  have hgW : fderiv ℝ (vortField W σ) y = Internal.SmoothPieceEps.curlLinear.comp E2 := vortGrad_eq hW σ y
  have hvv : vortField v σ y = Internal.SmoothPieceEps.curlLinear D := rfl
  have hvW : vortField W σ y = Internal.SmoothPieceEps.curlLinear E := rfl
  have hpair : Internal.SmoothPieceEps.curlLinear (D.comp E)
      = -(E (Internal.SmoothPieceEps.curlLinear D)) - D (Internal.SmoothPieceEps.curlLinear E)
        - Internal.SmoothPieceEps.curlLinear (E.comp D) := by
    have hA : ∑ i : Fin 3, D (unitVector i) i = 0 := hv.divergence_free σ y
    have hB : ∑ i : Fin 3, E (unitVector i) i = 0 := hWdiv σ y
    have := curl_comp_pair D E hA hB
    rw [Internal.SmoothPieceEps.curlLinear_apply, Internal.SmoothPieceEps.curlLinear_apply,
      Internal.SmoothPieceEps.curlLinear_apply, Internal.SmoothPieceEps.curlLinear_apply, ← this]
    abel
  rw [lhs, ht]
  unfold frameRest
  rw [hgv, hgW, hvv, hvW, flip_eq_of_symm hsv, flip_eq_of_symm hsv, flip_eq_of_symm hsW,
    ContinuousLinearMap.comp_id]
  simp only [ContinuousLinearMap.comp_apply, map_add, map_sub, map_smul]
  rw [hpair]
  module

theorem modeVel_time_vort {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) :
    modeVel ι (fun s x => deriv (fun r => vortField v r x) s) σ y
      = fun i => (((2 * Real.pi * ι.1 : ℝ) : ℂ) * Complex.I) * modeVel ι (vortField v) σ y i := by
  have hVs := vortField_smooth hv.smooth
  set U := vortField v
  have cU : Continuous (fun z : ℝ × Space => U z.1 z.2) := hVs.continuous
  have cU' : Continuous (fun z : ℝ × Space => deriv (fun r => U r z.2) z.1) :=
    (Internal.SmoothPieceEpsFrequency.timeDeriv_smooth hVs).continuous
  have hdiff : ∀ x : Space, Differentiable ℝ (fun r => U r x) := fun x =>
    (hVs.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
  have hper : ∀ s, U (s + 1) = U s := by
    intro s
    have e : v (s + 1) = v s := funext (hv.periodic s)
    show vortField v (s + 1) = vortField v s
    unfold vortField
    rw [e]
  funext i
  unfold modeVel
  refine Internal.SmoothPieceEpsFrequency.modeAverage_time_deriv ι
    (fun τ φ i => axialRot (-φ) (U (σ + τ) (axialRot φ y)) i)
    (fun τ φ i => axialRot (-φ) (deriv (fun r => U r (axialRot φ y)) (σ + τ)) i) i
    (Internal.Field.mode_integrand_continuous cU σ y i)
    (Internal.Field.mode_integrand_continuous (X := fun s x => deriv (fun r => U r x) s) cU' σ y i) ?_ ?_
  · intro τ φ
    have h0 := ((hdiff (axialRot φ y)) (σ + τ)).hasDerivAt
    have h1 := h0.scomp τ ((hasDerivAt_id' τ).const_add σ)
    rw [one_smul] at h1
    exact Internal.SmoothPieceEpsFrequency.hasDerivAt_rot_coord (-φ) i h1
  · intro φ
    simp only [add_zero]
    rw [hper σ]

theorem hasDerivAt_angle_phase (n k τ φ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-(((2 * Real.pi * n * τ + k * t : ℝ) : ℂ) * Complex.I)))
      (Complex.exp (-(((2 * Real.pi * n * τ + k * φ : ℝ) : ℂ) * Complex.I)) * (-((k : ℂ) * Complex.I))) φ := by
  have h1 : HasDerivAt (fun t : ℝ => ((2 * Real.pi * n * τ + k * t : ℝ) : ℂ)) (k : ℂ) φ := by
    have := (((hasDerivAt_id φ).const_mul k).const_add (2 * Real.pi * n * τ)).ofReal_comp
    simpa using this
  exact ((h1.mul_const Complex.I).neg).cexp

theorem angle_phase_period (n : ℝ) (k : ℤ) (τ : ℝ) :
    Complex.exp (-(((2 * Real.pi * n * τ + k * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (-(((2 * Real.pi * n * τ + k * 0 : ℝ) : ℂ) * Complex.I)) := by
  have : (-(((2 * Real.pi * n * τ + k * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)) =
      (-(((2 * Real.pi * n * τ + k * 0 : ℝ) : ℂ) * Complex.I)) + ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem modeAverage_angle_deriv {β : Type*} (ι : ℤ × ℤ) (F F' : ℝ → ℝ → β → ℝ) (b : β)
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2 b)) (hF' : Continuous (fun p : ℝ × ℝ => F' p.1 p.2 b))
    (hd : ∀ τ φ, HasDerivAt (fun t => F τ t b) (F' τ φ b) φ) (hp : ∀ τ, F τ (2 * Real.pi) b = F τ 0 b) :
    modeAverage ι F' b = (((ι.2 : ℝ) : ℂ) * Complex.I) * modeAverage ι F b := by
  unfold modeAverage
  set E : ℝ → ℝ → ℂ := fun τ φ => Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
    with hE
  have hEc : Continuous (fun p : ℝ × ℝ => E p.1 p.2) := by
    simp only [hE]
    fun_prop
  have key : ∀ τ, (∫ φ in (0 : ℝ)..(2 * Real.pi), E τ φ * ((F' τ φ b : ℝ) : ℂ)) =
      (((ι.2 : ℝ) : ℂ) * Complex.I) * ∫ φ in (0 : ℝ)..(2 * Real.pi), E τ φ * ((F τ φ b : ℝ) : ℂ) := by
    intro τ
    have hu : ∀ φ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), HasDerivAt (fun t => E τ t)
        (E τ φ * (-(((ι.2 : ℝ) : ℂ) * Complex.I))) φ := fun φ _ =>
      hasDerivAt_angle_phase (ι.1 : ℝ) (ι.2 : ℝ) τ φ
    have hv : ∀ φ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), HasDerivAt (fun t => ((F τ t b : ℝ) : ℂ))
        ((F' τ φ b : ℝ) : ℂ) φ := fun φ _ => (hd τ φ).ofReal_comp
    have cu : Continuous (fun φ => E τ φ * (-(((ι.2 : ℝ) : ℂ) * Complex.I))) :=
      (hEc.comp (Continuous.prodMk_right τ)).mul continuous_const
    have cv : Continuous (fun φ => ((F' τ φ b : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hF'.comp (Continuous.prodMk_right τ))
    have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv (cu.intervalIntegrable _ _)
      (cv.intervalIntegrable _ _)
    rw [ibp]
    have e1 : E τ (2 * Real.pi) = E τ 0 := by simp only [hE]; exact angle_phase_period (ι.1 : ℝ) ι.2 τ
    rw [e1, hp τ, sub_self, zero_sub, ← intervalIntegral.integral_neg]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun φ _ => ?_
    ring
  have key' : (fun τ => ∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((F' τ φ b : ℝ) : ℂ))
      = fun τ => (((ι.2 : ℝ) : ℂ) * Complex.I) * ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((F τ φ b : ℝ) : ℂ) :=
    funext key
  rw [key', intervalIntegral.integral_const_mul]
  ring

theorem rot_coord0 (ψ : ℝ) (u : Space) : axialRot ψ u 0 = Real.cos ψ * u 0 - Real.sin ψ * u 1 := by
  simp [axialRot, unitVector]

theorem rot_coord1 (ψ : ℝ) (u : Space) : axialRot ψ u 1 = Real.sin ψ * u 0 + Real.cos ψ * u 1 := by
  simp [axialRot, unitVector]

theorem rot_coord2 (ψ : ℝ) (u : Space) : axialRot ψ u 2 = u 2 := by
  simp [axialRot, unitVector]

theorem perp_coord0 (u : Space) : axialPerp u 0 = -u 1 := by simp [axialPerp, unitVector]

theorem perp_coord1 (u : Space) : axialPerp u 1 = u 0 := by simp [axialPerp, unitVector]

theorem perp_coord2 (u : Space) : axialPerp u 2 = 0 := by simp [axialPerp, unitVector]

theorem hasDerivAt_rot_angle (y : Space) (φ : ℝ) :
    HasDerivAt (fun t => axialRot t y) (axialPerp (axialRot φ y)) φ := by
  have e : (fun t => axialRot t y) = fun t => (Real.cos t * y 0 - Real.sin t * y 1) • unitVector 0
      + (Real.sin t * y 0 + Real.cos t * y 1) • unitVector 1 + y 2 • unitVector 2 := rfl
  rw [e]
  have hd : axialPerp (axialRot φ y) = (-Real.sin φ * y 0 - Real.cos φ * y 1) • unitVector 0
      + (Real.cos φ * y 0 + -Real.sin φ * y 1) • unitVector 1 + (0 : ℝ) • unitVector 2 := by
    refine PiLp.ext fun j => ?_
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
    · rw [perp_coord0, rot_coord1]; simp [unitVector]; ring
    · rw [perp_coord1, rot_coord0]; simp [unitVector]; ring
    · rw [perp_coord2]; simp [unitVector]
  rw [hd]
  exact (((((Real.hasDerivAt_cos φ).mul_const (y 0)).sub ((Real.hasDerivAt_sin φ).mul_const (y 1))).smul_const
    (unitVector 0)).add ((((Real.hasDerivAt_sin φ).mul_const (y 0)).add
      ((Real.hasDerivAt_cos φ).mul_const (y 1))).smul_const (unitVector 1))).add
    ((hasDerivAt_const φ (y 2)).smul_const (unitVector 2))

theorem hasDerivAt_coord {g : ℝ → Space} {g' : Space} {φ : ℝ} (hg : HasDerivAt g g' φ) (j : Fin 3) :
    HasDerivAt (fun t => g t j) (g' j) φ :=
  (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt φ hg

theorem hasDerivAt_rot_field {U : Space → Space} (hU : Differentiable ℝ U) (y : Space) (φ : ℝ) (i : Fin 3) :
    HasDerivAt (fun t => axialRot (-t) (U (axialRot t y)) i)
      (axialRot (-φ) (fderiv ℝ U (axialRot φ y) (axialPerp (axialRot φ y)) - axialPerp (U (axialRot φ y))) i) φ := by
  have hg : HasDerivAt (fun t => U (axialRot t y)) (fderiv ℝ U (axialRot φ y) (axialPerp (axialRot φ y))) φ :=
    (hU (axialRot φ y)).hasFDerivAt.comp_hasDerivAt φ (hasDerivAt_rot_angle y φ)
  have g0 := hasDerivAt_coord hg 0
  have g1 := hasDerivAt_coord hg 1
  have g2 := hasDerivAt_coord hg 2
  have hc : HasDerivAt (fun t => Real.cos (-t)) (-Real.sin φ) φ :=
    ((Real.hasDerivAt_cos (-φ)).comp φ (hasDerivAt_neg φ)).congr_deriv (by rw [Real.sin_neg]; ring)
  have hs : HasDerivAt (fun t => Real.sin (-t)) (-Real.cos φ) φ :=
    ((Real.hasDerivAt_sin (-φ)).comp φ (hasDerivAt_neg φ)).congr_deriv (by rw [Real.cos_neg]; ring)
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  · have e : (fun t => axialRot (-t) (U (axialRot t y)) 0)
        = fun t => Real.cos (-t) * U (axialRot t y) 0 - Real.sin (-t) * U (axialRot t y) 1 :=
      funext fun t => rot_coord0 _ _
    rw [e, rot_coord0]
    refine ((hc.mul g0).sub (hs.mul g1)).congr_deriv ?_
    simp only [WithLp.ofLp_sub, Pi.sub_apply, perp_coord0, perp_coord1, Real.cos_neg, Real.sin_neg]
    ring
  · have e : (fun t => axialRot (-t) (U (axialRot t y)) 1)
        = fun t => Real.sin (-t) * U (axialRot t y) 0 + Real.cos (-t) * U (axialRot t y) 1 :=
      funext fun t => rot_coord1 _ _
    rw [e, rot_coord1]
    refine ((hs.mul g0).add (hc.mul g1)).congr_deriv ?_
    simp only [WithLp.ofLp_sub, Pi.sub_apply, perp_coord0, perp_coord1, Real.cos_neg, Real.sin_neg]
    ring
  · have e : (fun t => axialRot (-t) (U (axialRot t y)) 2) = fun t => U (axialRot t y) 2 :=
      funext fun t => rot_coord2 _ _
    rw [e, rot_coord2]
    refine g2.congr_deriv ?_
    simp only [WithLp.ofLp_sub, Pi.sub_apply, perp_coord2, sub_zero]

theorem modeVel_angular_vort {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) :
    modeVel ι (fun s x => fderiv ℝ (vortField v s) x (axialPerp x) - axialPerp (vortField v s x)) σ y
      = fun i => (((ι.2 : ℝ) : ℂ) * Complex.I) * modeVel ι (vortField v) σ y i := by
  have hVs := vortField_smooth hv.smooth
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 2
  set U := vortField v
  have cU : Continuous (fun z : ℝ × Space => U z.1 z.2) := hVs.continuous
  have cG : Continuous (fun z : ℝ × Space =>
      fderiv ℝ (U z.1) z.2 (axialPerp z.2) - axialPerp (U z.1 z.2)) :=
    ((vortGrad_continuous hv2).clm_apply (axialPerp_continuous.comp continuous_snd)).sub
      (axialPerp_continuous.comp cU)
  have hdiff : ∀ s, Differentiable ℝ (U s) := fun s =>
    (hVs.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hR := axialRotationHolds_proof
  have r0 : ∀ u : Space, axialRot 0 u = u := hR.2.2.1
  have r2 : ∀ u : Space, axialRot (2 * Real.pi) u = u := fun u => by
    have := hR.2.2.2.1 0 u
    rw [zero_add, r0] at this
    exact this
  have rm2 : ∀ u : Space, axialRot (-(2 * Real.pi)) u = u := fun u => by
    have := hR.2.2.2.1 (-(2 * Real.pi)) u
    rw [neg_add_cancel, r0] at this
    exact this.symm
  funext i
  unfold modeVel
  refine modeAverage_angle_deriv ι
    (fun τ φ i => axialRot (-φ) (U (σ + τ) (axialRot φ y)) i)
    (fun τ φ i => axialRot (-φ) (fderiv ℝ (U (σ + τ)) (axialRot φ y) (axialPerp (axialRot φ y))
      - axialPerp (U (σ + τ) (axialRot φ y))) i) i
    (Internal.Field.mode_integrand_continuous cU σ y i)
    (Internal.Field.mode_integrand_continuous
      (X := fun s x => fderiv ℝ (U s) x (axialPerp x) - axialPerp (U s x)) cG σ y i) ?_ ?_
  · intro τ φ
    exact hasDerivAt_rot_field (hdiff (σ + τ)) y φ i
  · intro τ
    simp only [neg_zero, r0, r2, rm2]

theorem mode_identity {P a : ℝ} {W v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    ∀ i, vortMode (smoothRight P W v) ι σ y i - vortMode (negSumSecondPartials v) ι σ y i
      = ((PieceWeights.frameFreq P a ι : ℂ) * Complex.I) * vortMode v ι σ y i
        + vortMode v ι σ y i + modeVel ι (frameRest a W v) σ y i := by
  have hv3 : ContDiff ℝ 3 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 3
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 2
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 1
  have hSR : ContDiff ℝ 1 (fun z : ℝ × Space => smoothRight P W v z.1 z.2) :=
    SmoothEpsInternal.contDiff_smoothRight hv3 hW
  have hH := SmoothEpsInternal.contDiff_secondDerivField_one hv3
  have hNL : ContDiff ℝ 1 (fun z : ℝ × Space => negSumSecondPartials v z.1 z.2) := by
    unfold negSumSecondPartials secondDerivTrace secondDerivField
    exact (ContDiff.sum fun j _ => (hH.clm_apply contDiff_const).clm_apply contDiff_const).neg
  have cA : Continuous (fun z : ℝ × Space => vortField (smoothRight P W v) z.1 z.2) :=
    Internal.SmoothPieceEps.curlLinear.continuous.comp (fderiv_slice_continuous hSR)
  have cB : Continuous (fun z : ℝ × Space => vortField (negSumSecondPartials v) z.1 z.2) :=
    Internal.SmoothPieceEps.curlLinear.continuous.comp (fderiv_slice_continuous hNL)
  have hVs := vortField_smooth hv.smooth
  have c1' : Continuous (fun z : ℝ × Space => deriv (fun r => vortField v r z.2) z.1) :=
    (Internal.SmoothPieceEpsFrequency.timeDeriv_smooth hVs).continuous
  have c1 : Continuous (fun z : ℝ × Space => ((1 / P : ℝ) • fun s x => deriv (fun r => vortField v r x) s) z.1 z.2) :=
    c1'.const_smul (1 / P)
  have c2 : Continuous (fun z : ℝ × Space => vortField v z.1 z.2) := vortField_continuous hv2
  have c3' : Continuous (fun z : ℝ × Space =>
      fderiv ℝ (vortField v z.1) z.2 (axialPerp z.2) - axialPerp (vortField v z.1 z.2)) :=
    ((vortGrad_continuous hv2).clm_apply (axialPerp_continuous.comp continuous_snd)).sub
      (axialPerp_continuous.comp c2)
  have c3 : Continuous (fun z : ℝ × Space => (a • fun s x =>
      fderiv ℝ (vortField v s) x (axialPerp x) - axialPerp (vortField v s x)) z.1 z.2) := c3'.const_smul a
  have c4 : Continuous (fun z : ℝ × Space => frameRest a W v z.1 z.2) := frameRest_continuous hv2 hW
  have e : vortField (smoothRight P W v) - vortField (negSumSecondPartials v)
      = ((1 / P : ℝ) • fun s x => deriv (fun r => vortField v r x) s) + vortField v
        + (a • fun s x => fderiv ℝ (vortField v s) x (axialPerp x) - axialPerp (vortField v s x))
        + frameRest a W v := by
    funext s x
    exact vortField_identity hv hW hWdiv s x
  have c12 : Continuous (fun z : ℝ × Space => (((1 / P : ℝ) • fun s x => deriv (fun r => vortField v r x) s)
      + vortField v) z.1 z.2) := c1.add c2
  have c123 : Continuous (fun z : ℝ × Space => (((1 / P : ℝ) • fun s x => deriv (fun r => vortField v r x) s)
      + vortField v + (a • fun s x => fderiv ℝ (vortField v s) x (axialPerp x) - axialPerp (vortField v s x)))
      z.1 z.2) := c12.add c3
  have key := congrFun (modeVel_sub' cA cB ι σ y).symm
  intro i
  rw [vortMode_eq_modeVel hSR, vortMode_eq_modeVel hNL, vortMode_eq_modeVel hv1]
  have k2 := key i
  simp only [Pi.sub_apply] at k2
  rw [k2, e, Internal.Field.modeVel_add c123 c4, Internal.Field.modeVel_add c12 c3,
    Internal.Field.modeVel_add c1 c2, Internal.Field.modeVel_smul, Internal.Field.modeVel_smul,
    modeVel_time_vort hv, modeVel_angular_vort hv]
  simp only [Pi.add_apply]
  unfold PieceWeights.frameFreq
  push_cast
  ring
theorem rot_perp (ψ : ℝ) (a : ℝ) (w : Space) :
    axialRot ψ (a • axialPerp w) 0 = (-a) * axialRot ψ w 1 ∧ axialRot ψ (a • axialPerp w) 1 = a * axialRot ψ w 0 ∧
      axialRot ψ (a • axialPerp w) 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [rot_coord0, rot_coord1]
    simp only [PiLp.smul_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, perp_coord0, perp_coord1]
    ring
  · rw [rot_coord1, rot_coord0]
    simp only [PiLp.smul_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, perp_coord0, perp_coord1]
    ring
  · rw [rot_coord2]
    simp only [PiLp.smul_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, perp_coord2, mul_zero]

theorem modeAverage_congr_mul {β : Type*} (ι : ℤ × ℤ) (f g : ℝ → ℝ → β → ℝ) (b b' : β) (c : ℝ)
    (h : ∀ τ φ, f τ φ b = c * g τ φ b') : modeAverage ι f b = (c : ℂ) * modeAverage ι g b' := by
  unfold modeAverage
  simp only [h]
  simp_rw [Complex.ofReal_mul, mul_left_comm _ (c : ℂ), intervalIntegral.integral_const_mul]
  ring

theorem modeVel_rotationRest (a : ℝ) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeVel ι (rotationRest a v) σ y 0 = ((-a : ℝ) : ℂ) * modeVel ι (vortField v) σ y 1 ∧
      modeVel ι (rotationRest a v) σ y 1 = (a : ℂ) * modeVel ι (vortField v) σ y 0 ∧
      modeVel ι (rotationRest a v) σ y 2 = 0 := by
  unfold modeVel rotationRest
  refine ⟨modeAverage_congr_mul ι _ _ 0 1 (-a) fun τ φ => (rot_perp _ _ _).1,
    modeAverage_congr_mul ι _ _ 1 0 a fun τ φ => (rot_perp _ _ _).2.1, ?_⟩
  have := modeAverage_congr_mul ι (fun τ φ i => axialRot (-φ) (a • axialPerp (vortField v (σ + τ) (axialRot φ y))) i)
    (fun τ φ i => axialRot (-φ) (vortField v (σ + τ) (axialRot φ y)) i) 2 2 0 fun τ φ => by
      rw [(rot_perp _ _ _).2.2, zero_mul]
  rw [this, Complex.ofReal_zero, zero_mul]

theorem rotation_term_le (c a : ℝ) (x : Fin 3 → ℂ) (Z : Fin 3 → ℂ) (h0 : Z 0 = ((-a : ℝ) : ℂ) * x 1)
    (h1 : Z 1 = (a : ℂ) * x 0) (h2 : Z 2 = 0) :
    |(Complex.I * (c : ℂ) * cdot x Z).re| ≤ |c| * |a| * cnormSq x := by
  unfold cdot cnormSq
  simp only [Fin.sum_univ_three, h0, h1, h2]
  have e : (Complex.I * (c : ℂ) * (x 0 * (starRingEnd ℂ) (((-a : ℝ) : ℂ) * x 1) + x 1 * (starRingEnd ℂ) ((a : ℂ) * x 0)
      + x 2 * (starRingEnd ℂ) 0)).re = -2 * c * a * ((x 1).im * (x 0).re - (x 1).re * (x 0).im) := by
    simp only [map_mul, Complex.conj_ofReal, map_zero, mul_zero, add_zero, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [e, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
    Complex.normSq_apply]
  have hb : 2 * |(x 1).im * (x 0).re - (x 1).re * (x 0).im| ≤
      (x 0).re * (x 0).re + (x 0).im * (x 0).im + ((x 1).re * (x 1).re + (x 1).im * (x 1).im) := by
    rcases abs_cases ((x 1).im * (x 0).re - (x 1).re * (x 0).im) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
      nlinarith [sq_nonneg ((x 1).im - (x 0).re), sq_nonneg ((x 1).re + (x 0).im),
        sq_nonneg ((x 1).im + (x 0).re), sq_nonneg ((x 1).re - (x 0).im)]
  have h2' : 0 ≤ (x 2).re * (x 2).re + (x 2).im * (x 2).im := by nlinarith [sq_nonneg (x 2).re, sq_nonneg (x 2).im]
  rw [show -2 * c * a * ((x 1).im * (x 0).re - (x 1).re * (x 0).im)
      = -(c * a) * (2 * ((x 1).im * (x 0).re - (x 1).re * (x 0).im)) by ring, abs_mul, abs_neg, abs_mul, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hca : 0 ≤ |c| * |a| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  calc |c| * |a| * (2 * |(x 1).im * (x 0).re - (x 1).re * (x 0).im|)
      ≤ |c| * |a| * ((x 0).re * (x 0).re + (x 0).im * (x 0).im + ((x 1).re * (x 1).re + (x 1).im * (x 1).im)) :=
        mul_le_mul_of_nonneg_left hb hca
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hca

section Bound

variable {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds} {w : Space → ℝ}
  {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}

theorem restPart_split (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE) (ι : ℤ × ℤ)
    (σ : ℝ) (y : Space) :
    restTerm (m.epsP β).modes (m.epsP β).wt (m.epsP β).frame W v ι σ y
      = restPart (m.epsP β).modes (m.epsP β).wt v (transportRest (m.epsP β).frame W v) ι σ y
        - restPart (m.epsP β).modes (m.epsP β).wt v (stretchRest W v) ι σ y
        + restPart (m.epsP β).modes (m.epsP β).wt v (vortTransportRest W v) ι σ y
        - restPart (m.epsP β).modes (m.epsP β).wt v (vortStretchRest W v) ι σ y
        + restPart (m.epsP β).modes (m.epsP β).wt v (rotationRest (m.epsP β).frame v) ι σ y := by
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hS.smooth.smooth 2
  have hW := hS.flow_smooth
  set a := (m.epsP β).frame
  have cv : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv2.continuous
  have cW : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.continuous
  have c1 : Continuous (fun z : ℝ × Space => transportRest a W v z.1 z.2) := by
    unfold transportRest
    have hx : Continuous (fun z : ℝ × Space => (1 / 2 : ℝ) • z.2) := by fun_prop
    have hp : Continuous (fun z : ℝ × Space => a • axialPerp z.2) :=
      (axialPerp_continuous.comp continuous_snd).const_smul a
    exact (vortGrad_continuous hv2).clm_apply ((cW.add hx).sub hp)
  have c2 : Continuous (fun z : ℝ × Space => stretchRest W v z.1 z.2) := by
    unfold stretchRest
    exact (continuous_fderiv_slice hW).clm_apply (vortField_continuous hv2)
  have c3 : Continuous (fun z : ℝ × Space => vortTransportRest W v z.1 z.2) := by
    unfold vortTransportRest
    exact (vortGrad_continuous hW).clm_apply cv
  have c4 : Continuous (fun z : ℝ × Space => vortStretchRest W v z.1 z.2) := by
    unfold vortStretchRest
    exact (continuous_fderiv_slice hv2).clm_apply (vortField_continuous hW)
  have c5 : Continuous (fun z : ℝ × Space => rotationRest a v z.1 z.2) := by
    unfold rotationRest
    exact (axialPerp_continuous.comp (vortField_continuous hv2)).const_smul a
  have c12 : Continuous (fun z : ℝ × Space => (transportRest a W v - stretchRest W v) z.1 z.2) := c1.sub c2
  have c123 : Continuous (fun z : ℝ × Space =>
      (transportRest a W v - stretchRest W v + vortTransportRest W v) z.1 z.2) := c12.add c3
  have c1234 : Continuous (fun z : ℝ × Space =>
      (transportRest a W v - stretchRest W v + vortTransportRest W v - vortStretchRest W v) z.1 z.2) := c123.sub c4
  have e : frameRest a W v = transportRest a W v - stretchRest W v + vortTransportRest W v
      - vortStretchRest W v + rotationRest a v := rfl
  unfold restTerm restPart
  rw [e, Internal.Field.modeVel_add c1234 c5, modeVel_sub' c123 c4, Internal.Field.modeVel_add c12 c3,
    modeVel_sub' c1 c2]
  simp only [cdot_add, cdot_sub, mul_add, mul_sub, Complex.add_re, Complex.sub_re]

theorem transport_bound (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeries m h W v β z.1 z.2 < ⊤ →
      Summable (fun ι => restPart (m.epsP β).modes (m.epsP β).wt v (transportRest (m.epsP β).frame W v) ι z.1 z.2) ∧
      -(∑' ι, restPart (m.epsP β).modes (m.epsP β).wt v (transportRest (m.epsP β).frame W v) ι z.1 z.2)
        ≤ (∑' ι, (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
            * edgeSum h (m.epsP β).modes (fun α => velAmp W α z.1 z.2) (fun κ => vortGradAmp (secondDerivField v) κ z.1 z.2) ι)
          + (m.epsP β).wt z.2 * frameSpeedSup W (m.epsP β).frame z.2
            * pieceNorm (m.epsP β).modes (fun κ => vortGradAmp (secondDerivField v) κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) := by
  exact Internal.SmoothPieceEpsCompression.transport_bound hPars hDer hRotM hSP hS β

theorem stretch_bound (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeries m h W v β z.1 z.2 < ⊤ →
      Summable (fun ι => restPart (m.epsP β).modes (m.epsP β).wt v (stretchRest W v) ι z.1 z.2) ∧
      (∑' ι, restPart (m.epsP β).modes (m.epsP β).wt v (stretchRest W v) ι z.1 z.2)
        ≤ (∑' ι, (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
            * edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α z.1 z.2) (fun κ => vortAmp (gradField v) κ z.1 z.2) ι)
          + (m.epsP β).wt z.2 * ((1 / 2) * vortSup W z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) ^ 2 := by
  exact Internal.SmoothPieceEpsCompression.stretch_bound hPars hDer hRotM hSP hS β

theorem vortTransport_bound (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeries m h W v β z.1 z.2 < ⊤ →
      Summable (fun ι => restPart (m.epsP β).modes (m.epsP β).wt v (vortTransportRest W v) ι z.1 z.2) ∧
      -(∑' ι, restPart (m.epsP β).modes (m.epsP β).wt v (vortTransportRest W v) ι z.1 z.2)
        ≤ (∑' ι, (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
            * edgeSum h (m.epsP β).modes (fun α => vortGradAmp (secondDerivField W) α z.1 z.2) (fun κ => velAmp v κ z.1 z.2) ι)
          + (m.epsP β).wt z.2 * vortGradSup W z.2
            * pieceNorm (m.epsP β).modes (fun κ => velAmp v κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) := by
  exact Internal.SmoothPieceEpsCompression.vortTransport_bound hPars hDer hRotM hSP hS β

theorem vortStretch_bound (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeries m h W v β z.1 z.2 < ⊤ →
      Summable (fun ι => restPart (m.epsP β).modes (m.epsP β).wt v (vortStretchRest W v) ι z.1 z.2) ∧
      (∑' ι, restPart (m.epsP β).modes (m.epsP β).wt v (vortStretchRest W v) ι z.1 z.2)
        ≤ (∑' ι, (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
            * edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α z.1 z.2) (fun κ => gradAmp (gradField v) κ z.1 z.2) ι)
          + (m.epsP β).wt z.2 * vortSup W z.2
            * pieceNorm (m.epsP β).modes (fun κ => gradAmp (gradField v) κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) := by
  exact Internal.SmoothPieceEpsCompression.vortStretch_bound hPars hDer hRotM hSP hS β

theorem rotation_bound (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeries m h W v β z.1 z.2 < ⊤ →
      Summable (fun ι => restPart (m.epsP β).modes (m.epsP β).wt v (rotationRest (m.epsP β).frame v) ι z.1 z.2) ∧
      -(∑' ι, restPart (m.epsP β).modes (m.epsP β).wt v (rotationRest (m.epsP β).frame v) ι z.1 z.2)
        ≤ (m.epsP β).wt z.2 * |(m.epsP β).frame|
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) ^ 2 := by
  have hp := hSP P v hS.smooth
  have hG := hp.measurable_gradient
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hS.smooth.smooth 1
  have hAm : AEMeasurable (fun z : ℝ × Space =>
      ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι z.1 z.2 ^ 2)) slabMeasure :=
    Internal.SmoothPieceEps.slab_aem
      (AEMeasurable.ennreal_tsum fun ι => ((aem_vortAmp hG ι).pow_const 2).ennreal_ofReal)
  have hfin : ∫⁻ z, ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι z.1 z.2 ^ 2) ∂slabMeasure < ⊤ := by
    refine lt_of_le_of_lt (lintegral_prod_le _) (lt_of_le_of_lt
      (lintegral_mono fun σ => lintegral_mono fun y => ?_)
      (Internal.SmoothPieceEps.amplitudeSeries_finite hPars hSP P v hS.smooth))
    exact le_trans (le_trans le_self_add le_self_add) le_self_add
  filter_upwards [ae_lt_top' hAm hfin.ne] with z hz _hN
  have hwt0 : 0 ≤ (m.epsP β).wt z.2 := hS.admissible.eps_wt_nonneg β z.2
  have hq0 : ∀ ι, 0 ≤ vortAmp (gradField v) ι z.1 z.2 ^ 2 := fun ι => sq_nonneg _
  have hq : Summable (fun ι => vortAmp (gradField v) ι z.1 z.2 ^ 2) := by
    have := ENNReal.summable_toReal hz.ne
    simpa only [ENNReal.toReal_ofReal (hq0 _)] using this
  have hi0 : ∀ ι, 0 ≤ ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) := fun ι => by
    unfold ModeWeights.ind; split_ifs <;> norm_num
  have hi1 : ∀ ι, ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) ≤ 1 := fun ι => by
    unfold ModeWeights.ind; split_ifs <;> norm_num
  have hiq : Summable (fun ι => ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι)
      * vortAmp (gradField v) ι z.1 z.2 ^ 2) :=
    hq.of_nonneg_of_le (fun ι => mul_nonneg (hi0 ι) (hq0 ι))
      (fun ι => mul_le_of_le_one_left (hq0 ι) (hi1 ι))
  have hsum := hiq.mul_left ((m.epsP β).wt z.2 * |(m.epsP β).frame|)
  have hbd : ∀ ι, |restPart (m.epsP β).modes (m.epsP β).wt v (rotationRest (m.epsP β).frame v) ι z.1 z.2|
      ≤ (m.epsP β).wt z.2 * |(m.epsP β).frame| * (ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι)
        * vortAmp (gradField v) ι z.1 z.2 ^ 2) := by
    intro ι
    have eq : cnormSq (modeVel ι (vortField v) z.1 z.2) = vortAmp (gradField v) ι z.1 z.2 ^ 2 := by
      rw [← vortMode_eq_modeVel hv1]
      unfold vortMode vortAmp
      rw [Real.sq_sqrt (Internal.FieldModes.cnormSq_nonneg _)]
    obtain ⟨h0, h1, h2⟩ := modeVel_rotationRest (m.epsP β).frame v ι z.1 z.2
    unfold restPart
    rw [vortMode_eq_modeVel hv1]
    refine le_trans (rotation_term_le _ _ _ _ h0 h1 h2) (le_of_eq ?_)
    rw [abs_mul, abs_sgn_eq, abs_of_nonneg hwt0, eq]
    ring
  have hrs : Summable (fun ι =>
      restPart (m.epsP β).modes (m.epsP β).wt v (rotationRest (m.epsP β).frame v) ι z.1 z.2) :=
    (hsum.of_nonneg_of_le (fun ι => abs_nonneg _) hbd).of_abs
  refine ⟨hrs, ?_⟩
  have hn := norm_tsum_le_tsum_norm hrs.norm
  simp only [Real.norm_eq_abs] at hn
  have ht := hrs.abs.tsum_le_tsum hbd hsum
  rw [tsum_mul_left] at ht
  have hpn : pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) ^ 2
      = ∑' ι, ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) * vortAmp (gradField v) ι z.1 z.2 ^ 2 := by
    unfold pieceNorm
    exact Real.sq_sqrt (tsum_nonneg fun ι => mul_nonneg (hi0 ι) (hq0 ι))
  rw [hpn]
  linarith [neg_le_abs (∑' ι, restPart (m.epsP β).modes (m.epsP β).wt v (rotationRest (m.epsP β).frame v) ι z.1 z.2)]

theorem compression_bound (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeries m h W v β z.1 z.2 < ⊤ →
      Summable (fun ι : ℤ × ℤ => restTerm (m.epsP β).modes (m.epsP β).wt (m.epsP β).frame W v ι z.1 z.2) →
      -(∑' ι : ℤ × ℤ, restTerm (m.epsP β).modes (m.epsP β).wt (m.epsP β).frame W v ι z.1 z.2)
        ≤ (negSeries m h W v β z.1 z.2).toReal - gradPart (m.epsP β).modes (m.epsP β).wt v z.1 z.2 := by
  filter_upwards [transport_bound hPars hDer hRotM hSP hS β, stretch_bound hPars hDer hRotM hSP hS β,
    vortTransport_bound hPars hDer hRotM hSP hS β, vortStretch_bound hPars hDer hRotM hSP hS β,
    rotation_bound hPars hDer hRotM hSP hS β] with z b1 b2 b3 b4 b5 hN _hR
  obtain ⟨s1, i1⟩ := b1 hN
  obtain ⟨s2, i2⟩ := b2 hN
  obtain ⟨s3, i3⟩ := b3 hN
  obtain ⟨s4, i4⟩ := b4 hN
  obtain ⟨s5, i5⟩ := b5 hN
  have eR : ∑' ι, restTerm (m.epsP β).modes (m.epsP β).wt (m.epsP β).frame W v ι z.1 z.2
      = (∑' ι, restPart (m.epsP β).modes (m.epsP β).wt v (transportRest (m.epsP β).frame W v) ι z.1 z.2)
        - (∑' ι, restPart (m.epsP β).modes (m.epsP β).wt v (stretchRest W v) ι z.1 z.2)
        + (∑' ι, restPart (m.epsP β).modes (m.epsP β).wt v (vortTransportRest W v) ι z.1 z.2)
        - (∑' ι, restPart (m.epsP β).modes (m.epsP β).wt v (vortStretchRest W v) ι z.1 z.2)
        + (∑' ι, restPart (m.epsP β).modes (m.epsP β).wt v (rotationRest (m.epsP β).frame v) ι z.1 z.2) := by
    rw [tsum_congr fun ι => restPart_split hS β ι z.1 z.2, (((s1.sub s2).add s3).sub s4).tsum_add s5,
      ((s1.sub s2).add s3).tsum_sub s4, (s1.sub s2).tsum_add s3, s1.tsum_sub s2]
  have hwt0 : 0 ≤ (m.epsP β).wt z.2 := hS.admissible.eps_wt_nonneg β z.2
  set E1 : ℤ × ℤ → ℝ := fun ι => (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
    * edgeSum h (m.epsP β).modes (fun α => velAmp W α z.1 z.2) (fun κ => vortGradAmp (secondDerivField v) κ z.1 z.2) ι
  set E2 : ℤ × ℤ → ℝ := fun ι => (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
    * edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α z.1 z.2) (fun κ => vortAmp (gradField v) κ z.1 z.2) ι
  set E3 : ℤ × ℤ → ℝ := fun ι => (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
    * edgeSum h (m.epsP β).modes (fun α => vortGradAmp (secondDerivField W) α z.1 z.2) (fun κ => velAmp v κ z.1 z.2) ι
  set E4 : ℤ × ℤ → ℝ := fun ι => (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
    * edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α z.1 z.2) (fun κ => gradAmp (gradField v) κ z.1 z.2) ι
  have hE : ∀ ι, -pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι z.1 z.2 = E1 ι + E2 ι + E3 ι + E4 ι := by
    intro ι
    unfold pieceEpsRestMode
    simp only [E1, E2, E3, E4]
    ring
  have n1 : ∀ ι, 0 ≤ E1 ι := fun ι => mul_nonneg (mul_nonneg hwt0 (Real.sqrt_nonneg _))
    (edge_nonneg _ _ _ _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _))
  have n2 : ∀ ι, 0 ≤ E2 ι := fun ι => mul_nonneg (mul_nonneg hwt0 (Real.sqrt_nonneg _))
    (edge_nonneg _ _ _ _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _))
  have n3 : ∀ ι, 0 ≤ E3 ι := fun ι => mul_nonneg (mul_nonneg hwt0 (Real.sqrt_nonneg _))
    (edge_nonneg _ _ _ _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _))
  have n4 : ∀ ι, 0 ≤ E4 ι := fun ι => mul_nonneg (mul_nonneg hwt0 (Real.sqrt_nonneg _))
    (edge_nonneg _ _ _ _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _))
  have hR0 : ∀ ι, 0 ≤ -pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι z.1 z.2 := fun ι => by
    rw [hE]; linarith [n1 ι, n2 ι, n3 ι, n4 ι]
  have hAne : (∑' ι, ENNReal.ofReal (-pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι z.1 z.2)) ≠ ⊤ :=
    ne_top_of_le_ne_top hN.ne le_self_add
  have hBne : ENNReal.ofReal (-pieceEpsBlock m W v (gradField v) (secondDerivField v) β z.1 z.2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have sR : Summable (fun ι => -pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι z.1 z.2) := by
    have := ENNReal.summable_toReal hAne
    simpa only [ENNReal.toReal_ofReal (hR0 _)] using this
  have eA : (∑' ι, ENNReal.ofReal (-pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι z.1 z.2)).toReal
      = ∑' ι, -pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι z.1 z.2 := by
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun ι => ENNReal.toReal_ofReal (hR0 ι)
  have t1 : Summable E1 := Summable.of_nonneg_of_le n1 (fun ι => by rw [hE ι]; linarith [n2 ι, n3 ι, n4 ι]) sR
  have t2 : Summable E2 := Summable.of_nonneg_of_le n2 (fun ι => by rw [hE ι]; linarith [n1 ι, n3 ι, n4 ι]) sR
  have t3 : Summable E3 := Summable.of_nonneg_of_le n3 (fun ι => by rw [hE ι]; linarith [n1 ι, n2 ι, n4 ι]) sR
  have t4 : Summable E4 := Summable.of_nonneg_of_le n4 (fun ι => by rw [hE ι]; linarith [n1 ι, n2 ι, n3 ι]) sR
  have eS : ∑' ι, -pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι z.1 z.2
      = tsum E1 + tsum E2 + tsum E3 + tsum E4 := by
    rw [tsum_congr hE, ((t1.add t2).add t3).tsum_add t4, (t1.add t2).tsum_add t3, t1.tsum_add t2]
  have eN : (negSeries m h W v β z.1 z.2).toReal
      = (∑' ι, ENNReal.ofReal (-pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι z.1 z.2)).toReal
        + (ENNReal.ofReal (-pieceEpsBlock m W v (gradField v) (secondDerivField v) β z.1 z.2)).toReal := by
    unfold negSeries
    exact ENNReal.toReal_add hAne hBne
  have hB : -pieceEpsBlock m W v (gradField v) (secondDerivField v) β z.1 z.2
      ≤ (ENNReal.ofReal (-pieceEpsBlock m W v (gradField v) (secondDerivField v) β z.1 z.2)).toReal := by
    rw [ENNReal.toReal_ofReal']
    exact le_max_left _ _
  have eBlk : -pieceEpsBlock m W v (gradField v) (secondDerivField v) β z.1 z.2
      - gradPart (m.epsP β).modes (m.epsP β).wt v z.1 z.2
      = (m.epsP β).wt z.2 * frameSpeedSup W (m.epsP β).frame z.2
            * pieceNorm (m.epsP β).modes (fun κ => vortGradAmp (secondDerivField v) κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2)
        + (m.epsP β).wt z.2 * ((1 / 2) * vortSup W z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) ^ 2
        + (m.epsP β).wt z.2 * |(m.epsP β).frame|
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) ^ 2
        + (m.epsP β).wt z.2 * vortGradSup W z.2
            * pieceNorm (m.epsP β).modes (fun κ => velAmp v κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2)
        + (m.epsP β).wt z.2 * vortSup W z.2
            * pieceNorm (m.epsP β).modes (fun κ => gradAmp (gradField v) κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) := by
    unfold pieceEpsBlock gradPart
    ring
  rw [eR]
  linarith [i1, i2, i3, i4, i5, eS, eN, hB, eBlk, eA]

end Bound

theorem term_split (c f : ℝ) (x X Y Z : Fin 3 → ℂ)
    (hX : ∀ i, X i - Y i = ((f : ℂ) * Complex.I) * x i + x i + Z i) :
    (Complex.I * (c : ℂ) * cdot x X).re - (Complex.I * (c : ℂ) * cdot x Y).re
      = c * f * cnormSq x + (Complex.I * (c : ℂ) * cdot x Z).re := by
  have e : ∀ i, X i = Y i + (((f : ℂ) * Complex.I) * x i + x i + Z i) := fun i => by
    rw [← hX i]; ring
  unfold cdot cnormSq
  simp only [Finset.mul_sum, Complex.re_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [e i, Complex.sq_norm, Complex.normSq_apply]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im]
  ring

theorem frameFreq_neg (P a : ℝ) (ι : ℤ × ℤ) :
    PieceWeights.frameFreq P a (-ι) = -PieceWeights.frameFreq P a ι := by
  unfold PieceWeights.frameFreq
  simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  ring

theorem sgn_mul_frameFreq {P a : ℝ} {T : Set (ℤ × ℤ)} (hT : ∃ Ωs > 0, ∀ ι ∈ T, Ωs ≤ PieceWeights.frameFreq P a ι)
    (ι : ℤ × ℤ) :
    PieceWeights.sgn T ι * PieceWeights.frameFreq P a ι
      = ModeWeights.ind (PieceWeights.inPiece T ι) * |PieceWeights.frameFreq P a ι| := by
  obtain ⟨Ωs, hΩ, hT⟩ := hT
  unfold PieceWeights.sgn ModeWeights.ind PieceWeights.inPiece
  by_cases h1 : ι ∈ T
  · have := hT ι h1
    rw [if_pos h1, if_pos (Or.inl h1), abs_of_pos (by linarith)]
    try ring
  · by_cases h2 : -ι ∈ T
    · have := hT (-ι) h2
      rw [frameFreq_neg] at this
      rw [if_neg h1, if_pos h2, if_pos (Or.inr h2), abs_of_neg (by linarith)]
      try ring
    · rw [if_neg h1, if_neg h2, if_neg (by tauto)]
      try ring

section Parts

variable {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds} {w : Space → ℝ}
  {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}

theorem pieceTerm_sub (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE) (ι : ℤ × ℤ)
    (σ : ℝ) (y : Space) :
    pieceTerm (m.epsP β).modes (m.epsP β).wt v (smoothRight P W v) ι σ y
      - pieceTerm (m.epsP β).modes (m.epsP β).wt v (negSumSecondPartials v) ι σ y
      = pieceEpsPos m P (gradField v) β ι σ y
        + restTerm (m.epsP β).modes (m.epsP β).wt (m.epsP β).frame W v ι σ y := by
  have hm := hS.admissible
  have hid := mode_identity (a := (m.epsP β).frame) hS.smooth hS.flow_smooth hS.flow_periodic hS.flow_div ι σ y
  have e := term_split (PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y)
    (PieceWeights.frameFreq P (m.epsP β).frame ι) (vortMode v ι σ y) (vortMode (smoothRight P W v) ι σ y)
    (vortMode (negSumSecondPartials v) ι σ y) (modeVel ι (frameRest (m.epsP β).frame W v) σ y) hid
  unfold pieceTerm restTerm
  unfold vortMode at e ⊢
  rw [e]
  congr 1
  unfold pieceEpsPos vortAmp
  rw [Real.sq_sqrt (Internal.FieldModes.cnormSq_nonneg _)]
  have hs := sgn_mul_frameFreq (hm.eps_oneSided β) ι
  calc PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y * PieceWeights.frameFreq P (m.epsP β).frame ι
        * cnormSq (curlOfGrad (modeGrad ι (gradField v) σ y))
      = (PieceWeights.sgn (m.epsP β).modes ι * PieceWeights.frameFreq P (m.epsP β).frame ι) * (m.epsP β).wt y
        * cnormSq (curlOfGrad (modeGrad ι (gradField v) σ y)) := by ring
    _ = _ := by rw [hs]; ring

theorem pointwise_lower (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, posSeries m P v β z.1 z.2 < ⊤ → negSeries m h W v β z.1 z.2 < ⊤ →
      Summable (fun ι : ℤ × ℤ => pieceTerm (m.epsP β).modes (m.epsP β).wt v (smoothRight P W v) ι z.1 z.2) →
      Summable (fun ι : ℤ × ℤ => pieceTerm (m.epsP β).modes (m.epsP β).wt v (negSumSecondPartials v) ι z.1 z.2) →
      (posSeries m P v β z.1 z.2).toReal ≤
        (∑' ι : ℤ × ℤ, pieceTerm (m.epsP β).modes (m.epsP β).wt v (smoothRight P W v) ι z.1 z.2)
          + (negSeries m h W v β z.1 z.2).toReal
          - (gradPart (m.epsP β).modes (m.epsP β).wt v z.1 z.2
            + ∑' ι : ℤ × ℤ, pieceTerm (m.epsP β).modes (m.epsP β).wt v (negSumSecondPartials v) ι z.1 z.2) := by
  filter_upwards [compression_bound hPars hDer hRotM hSP hS β] with z hc hA hN hs hl
  have hm := hS.admissible
  have hpos : ∀ ι, 0 ≤ pieceEpsPos m P (gradField v) β ι z.1 z.2 := fun ι => by
    unfold pieceEpsPos
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ (hm.eps_wt_nonneg β z.2)) (abs_nonneg _)) (sq_nonneg _)
    unfold ModeWeights.ind
    split_ifs <;> norm_num
  have hAs : Summable (fun ι => pieceEpsPos m P (gradField v) β ι z.1 z.2) := by
    have := ENNReal.summable_toReal hA.ne
    simpa only [ENNReal.toReal_ofReal (hpos _)] using this
  have eA : (posSeries m P v β z.1 z.2).toReal = ∑' ι, pieceEpsPos m P (gradField v) β ι z.1 z.2 := by
    unfold posSeries
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun ι => ENNReal.toReal_ofReal (hpos ι)
  have eT : ∀ ι, restTerm (m.epsP β).modes (m.epsP β).wt (m.epsP β).frame W v ι z.1 z.2
      = (pieceTerm (m.epsP β).modes (m.epsP β).wt v (smoothRight P W v) ι z.1 z.2
        - pieceTerm (m.epsP β).modes (m.epsP β).wt v (negSumSecondPartials v) ι z.1 z.2)
        - pieceEpsPos m P (gradField v) β ι z.1 z.2 := fun ι => by
    rw [pieceTerm_sub hS β ι z.1 z.2]; ring
  have hRs : Summable (fun ι => restTerm (m.epsP β).modes (m.epsP β).wt (m.epsP β).frame W v ι z.1 z.2) := by
    simp_rw [eT]
    exact (hs.sub hl).sub hAs
  have hb := hc hN hRs
  have eS : (∑' ι, pieceTerm (m.epsP β).modes (m.epsP β).wt v (smoothRight P W v) ι z.1 z.2)
      - ∑' ι, pieceTerm (m.epsP β).modes (m.epsP β).wt v (negSumSecondPartials v) ι z.1 z.2
      = (∑' ι, pieceEpsPos m P (gradField v) β ι z.1 z.2)
        + ∑' ι, restTerm (m.epsP β).modes (m.epsP β).wt (m.epsP β).frame W v ι z.1 z.2 := by
    rw [← hs.tsum_sub hl, ← hAs.tsum_add hRs]
    exact tsum_congr fun ι => pieceTerm_sub hS β ι z.1 z.2
  rw [eA]
  linarith

theorem core_inequality_of_setting (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRotM : ModeRotationHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hSsp : WeightedSumSecondPartialsPairingHolds)
    (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE)
    (hA : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, posSeries m P v β σ y) < ⊤)
    (hN : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, negSeries m h W v β σ y) < ⊤) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, posSeries m P v β σ y).toReal ≤
      epsPairing (fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y) v (smoothRight P W v)
        + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, negSeries m h W v β σ y).toReal := by
  obtain ⟨hAm, hNm⟩ := parts_aemeasurable hSP hS β
  obtain ⟨hSs, hSi, hX⟩ := pairing_exchange hPars hDer hSP hS β
  obtain ⟨hLs, hQi, hQ⟩ := sumSecondPartials_lower hPars hDer hSP hSsp hS β
  have eA : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, posSeries m P v β σ y)
      = ∫⁻ z, posSeries m P v β z.1 z.2 ∂slabMeasure := (lintegral_prod _ hAm).symm
  have eN : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, negSeries m h W v β σ y)
      = ∫⁻ z, negSeries m h W v β z.1 z.2 ∂slabMeasure := (lintegral_prod _ hNm).symm
  rw [eA] at hA
  rw [eN] at hN
  rw [eA, eN]
  refine core_of_parts hAm hNm hA hN hSi hX hQi hQ ?_
  filter_upwards [pointwise_lower hPars hDer hRotM hSP hS β, hSs, hLs, ae_lt_top' hAm hA.ne,
    ae_lt_top' hNm hN.ne] with z h3 hs hl ha hn
  exact h3 ha hn hs hl

end Parts

end Internal.SmoothPieceEpsCore

end Coercive

end Breakdown
