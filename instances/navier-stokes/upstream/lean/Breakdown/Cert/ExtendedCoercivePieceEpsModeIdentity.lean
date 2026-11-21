import Breakdown.Cert.CoerciveSmoothPieceEpsCoreModes
import Breakdown.Cert.ExtendedCoercivePieceEpsRightGradient
import Breakdown.Cert.ExtendedCoerciveSecondDerivSymm
import Breakdown.Cert.ExtendedCoerciveVortGradMap
import Breakdown.Cert.CoerciveDensityPassageLinear
import Breakdown.Cert.CoerciveModeL2

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.WeakModeIdentity

open Coercive Coercive.Internal.SmoothPieceEpsCore Coercive.Internal.PieceAbsorb

abbrev orbitBox : Measure (ℝ × ℝ) := Coercive.Internal.ModeRotation.boxMeasure

theorem ae_orbit_of_ae {Q : ℝ × Space → Prop} (h : ∀ᵐ p ∂(volume : Measure (ℝ × Space)), Q p) :
    ∀ᵐ z ∂(volume : Measure (ℝ × Space)), ∀ᵐ q ∂orbitBox, Q (z.1 + q.1, axialRot q.2 z.2) :=
  Measure.ae_ae_of_ae_prod ((Coercive.ModeL2Internal.quasiMeasurePreserving_shiftRot orbitBox).ae h)

theorem ae_orbit_integrable_of_bound {E : Type*} [NormedAddCommGroup E] {F : ℝ → Space → E}
    {g : ℝ × Space → ℝ} (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hg : Continuous g)
    (hb : ∀ᵐ p ∂(volume : Measure (ℝ × Space)), ‖F p.1 p.2‖ ≤ g p) :
    ∀ᵐ z ∂(volume : Measure (ℝ × Space)),
      Integrable (fun q : ℝ × ℝ => F (z.1 + q.1) (axialRot q.2 z.2)) orbitBox := by
  have hq := hF.comp_quasiMeasurePreserving (Coercive.ModeL2Internal.quasiMeasurePreserving_shiftRot orbitBox)
  have hs := hq.prodMk_left
  filter_upwards [hs, ae_orbit_of_ae hb] with z hz hbz
  have cb : Continuous (fun q : ℝ × ℝ => g (z.1 + q.1, axialRot q.2 z.2)) :=
    hg.comp ((continuous_const.add continuous_fst).prodMk
      (Coercive.Internal.Field.axialRot_comp_continuous continuous_snd continuous_const))
  exact (Coercive.StretchInternal.integrable_box_of_continuous cb).mono' hz hbz

theorem modeVel_congr_orbit {X Y : ℝ → Space → Space} {z : ℝ × Space}
    (h : ∀ᵐ q ∂orbitBox, X (z.1 + q.1) (axialRot q.2 z.2) = Y (z.1 + q.1) (axialRot q.2 z.2))
    (ι : ℤ × ℤ) : modeVel ι X z.1 z.2 = modeVel ι Y z.1 z.2 := by
  have h2 := Measure.ae_ae_of_ae_prod h
  rw [ae_restrict_iff' measurableSet_Ioc] at h2
  funext i
  unfold modeVel modeAverage
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [h2] with τ hτ hτI
  rw [Set.uIoc_of_le zero_le_one] at hτI
  have h3 := hτ hτI
  rw [ae_restrict_iff' measurableSet_Ioc] at h3
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [h3] with φ hφ hφI
  rw [Set.uIoc_of_le (by positivity)] at hφI
  rw [hφ hφI]

variable {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}

theorem ae_good_point (hW : IsWeakSecondDerivState W HW D) :
    ∀ᵐ p ∂(volume : Measure (ℝ × Space)), HasFDerivAt (fderiv ℝ (W p.1)) (HW p.1 p.2) p.2 ∧
      ∀ a b : Space, HW p.1 p.2 a b = HW p.1 p.2 b a := by
  set H' := hW.secondDeriv_measurable.mk _ with hH'
  have hm : StronglyMeasurable H' := hW.secondDeriv_measurable.stronglyMeasurable_mk
  have he : (fun z : ℝ × Space => HW z.1 z.2) =ᵐ[volume] H' := hW.secondDeriv_measurable.ae_eq_mk
  have cDW : Continuous (Function.uncurry fun (s : ℝ) (y : Space) => fderiv ℝ (W s) y) :=
    Coercive.Internal.SmoothPieceEpsCore.fderiv_slice_continuous hW.smooth
  have mD := measurableSet_of_differentiableAt_with_param ℝ cDW
  have mF : StronglyMeasurable (fun p : ℝ × Space => fderiv ℝ (fderiv ℝ (W p.1)) p.2) :=
    (measurable_fderiv_with_param ℝ cDW).stronglyMeasurable
  have mflip : StronglyMeasurable (fun p => (H' p).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ Space Space Space).continuous.comp_stronglyMeasurable hm
  set M : Set (ℝ × Space) := {p | DifferentiableAt ℝ (fderiv ℝ (W p.1)) p.2}
    ∩ {p | fderiv ℝ (fderiv ℝ (W p.1)) p.2 = H' p} ∩ {p | (H' p).flip = H' p} with hMdef
  have hM : MeasurableSet M := (mD.inter (mF.measurableSet_eq_fun hm)).inter (mflip.measurableSet_eq_fun hm)
  have he' : (fun z : ℝ × Space => HW z.1 z.2) =ᵐ[(volume : Measure ℝ).prod (volume : Measure Space)] H' := by
    rw [← Measure.volume_eq_prod]
    exact he
  have he2 := Measure.ae_ae_of_ae_prod he'
  have hnull : (volume : Measure (ℝ × Space)) Mᶜ = 0 := by
    rw [Measure.volume_eq_prod, Measure.measure_prod_null hM.compl]
    filter_upwards [he2] with s hs
    have hy : ∀ᵐ y, (s, y) ∈ M := by
      filter_upwards [WeakGradientSlope.ae_hasFDerivAt_fderiv hW s, weakSecondDerivSymmetricHolds_proof hW s, hs]
        with y h1 h2 h3
      refine ⟨⟨h1.differentiableAt, ?_⟩, ?_⟩
      · show fderiv ℝ (fderiv ℝ (W s)) y = H' (s, y)
        rw [h1.fderiv]
        exact h3
      · show (H' (s, y)).flip = H' (s, y)
        rw [← (show HW s y = H' (s, y) from h3)]
        refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
        rw [ContinuousLinearMap.flip_apply]
        exact (h2 a b).symm
    exact ae_iff.1 hy
  have hMae : ∀ᵐ p ∂(volume : Measure (ℝ × Space)), p ∈ M := ae_iff.2 hnull
  filter_upwards [hMae, he] with p hp hpe
  obtain ⟨⟨hd, hf⟩, hs⟩ := hp
  have hf' : fderiv ℝ (fderiv ℝ (W p.1)) p.2 = H' p := hf
  have hs' : (H' p).flip = H' p := hs
  have e : H' p = HW p.1 p.2 := hpe.symm
  refine ⟨?_, fun a b => ?_⟩
  · have h0 := hd.hasFDerivAt
    rwa [hf', e] at h0
  · have h0 := congrArg (fun A : Space →L[ℝ] Space →L[ℝ] Space => A b a) hs'
    simp only [ContinuousLinearMap.flip_apply] at h0
    rw [← e]
    exact h0

private theorem frame_alg_weak (a b : Fin 3 → Fin 3 → ℝ) (ha : a 0 0 + a 1 1 + a 2 2 = 0)
    (hb : b 0 0 + b 1 1 + b 2 2 = 0) (i : Fin 3) :
    ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l *
        (∑ k : Fin 3, b j k * a k l + ∑ k : Fin 3, a j k * b k l)
      = -(∑ k : Fin 3, (∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol k j l * a j l) * b k i)
        - ∑ k : Fin 3, (∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol k j l * b j l) * a k i := by
  fin_cases i <;> simp [Fin.sum_univ_three, alternatingSymbol]
  · linear_combination (b 1 2 - b 2 1) * ha + (a 1 2 - a 2 1) * hb
  · linear_combination (b 2 0 - b 0 2) * ha + (a 2 0 - a 0 2) * hb
  · linear_combination (b 0 1 - b 1 0) * ha + (a 0 1 - a 1 0) * hb

private theorem apply_expand_weak (A : Space →L[ℝ] Space) (x : Space) (i : Fin 3) :
    A x i = ∑ k : Fin 3, x k * A (unitVector k) i := by
  have hx : x = ∑ k : Fin 3, x k • unitVector k := by
    ext m
    fin_cases m <;> simp [unitVector, Fin.sum_univ_three]
  conv_lhs => rw [hx]
  simp only [map_sum, map_smul]
  simp [Fin.sum_univ_three]

private theorem curl_comp_pair_weak (A B : Space →L[ℝ] Space) (hA : ∑ i : Fin 3, A (unitVector i) i = 0)
    (hB : ∑ i : Fin 3, B (unitVector i) i = 0) :
    curlVec (A.comp B) + curlVec (B.comp A) = -(B (curlVec A)) - A (curlVec B) := by
  have e := fun i => frame_alg_weak (fun j l => A (unitVector j) l) (fun j l => B (unitVector j) l)
    (by simpa [Fin.sum_univ_three] using hA) (by simpa [Fin.sum_univ_three] using hB) i
  ext i
  have ei := e i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply]
  rw [apply_expand_weak B (curlVec A) i, apply_expand_weak A (curlVec B) i]
  simp only [StretchInternal.curlVec_apply, ContinuousLinearMap.comp_apply]
  have hAB : ∀ j l, A (B (unitVector j)) l = ∑ k : Fin 3, B (unitVector j) k * A (unitVector k) l :=
    fun j l => apply_expand_weak A _ l
  have hBA : ∀ j l, B (A (unitVector j)) l = ∑ k : Fin 3, A (unitVector j) k * B (unitVector k) l :=
    fun j l => apply_expand_weak B _ l
  simp only [hAB, hBA]
  simp only [Fin.sum_univ_three] at ei ⊢
  linear_combination ei

private theorem hasDerivAt_curlVec_weak {G : ℝ → Space →L[ℝ] Space} {G' : Space →L[ℝ] Space} {σ : ℝ}
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

private theorem flip_eq_of_symm_weak {f : Space → Space} {y : Space} (hf : IsSymmSndFDerivAt ℝ f y) (u : Space) :
    (fderiv ℝ (fderiv ℝ f) y).flip u = fderiv ℝ (fderiv ℝ f) y u := by
  ext w : 1
  rw [ContinuousLinearMap.flip_apply]
  exact hf w u

theorem vortField_identity_weak {P a : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    (hWc : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0) (σ : ℝ)
    (y : Space) {E2 : Space →L[ℝ] Space →L[ℝ] Space} (hE : HasFDerivAt (fderiv ℝ (W σ)) E2 y)
    (hsym : ∀ a b : Space, E2 a b = E2 b a) :
    vortField (smoothRight P W v) σ y - vortField (negSumSecondPartials v) σ y
      = (1 / P) • deriv (fun s => vortField v s y) σ + vortField v σ y
        + a • (fderiv ℝ (vortField v σ) y (axialPerp y) - axialPerp (vortField v σ y))
        + (fderiv ℝ (vortField v σ) y (W σ y + (1 / 2 : ℝ) • y - a • axialPerp y)
          - fderiv ℝ (W σ) y (vortField v σ y) + curlVec (E2 (v σ y))
          - fderiv ℝ (v σ) y (vortField W σ y) + a • axialPerp (vortField v σ y)) := by
  have hvs : ContDiff ℝ ∞ (v σ) := hv.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hWs : ContDiff ℝ 1 (W σ) := hWc.comp (contDiff_const.prodMk contDiff_id)
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 2
  have hvd : Differentiable ℝ (v σ) := hvs.differentiable (by simp)
  have hWd : Differentiable ℝ (W σ) := hWs.differentiable (by norm_num)
  have hD1 : ContDiff ℝ ∞ (fderiv ℝ (v σ)) := hvs.fderiv_right (m := ∞) (by simp)
  have hD : Differentiable ℝ (fderiv ℝ (v σ)) := hD1.differentiable (by simp)
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
  have flipE : E2.flip (v σ y) = E2 (v σ y) := by
    ext w : 1
    rw [ContinuousLinearMap.flip_apply]
    exact hsym w (v σ y)
  rw [← Coercive.Internal.SmoothPieceEps.curlLinear_apply (E2 (v σ y))]
  set D := fderiv ℝ (v σ) y with hDdef
  set E := fderiv ℝ (W σ) y with hEdef
  set D2 := fderiv ℝ (fderiv ℝ (v σ)) y with hD2def
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
    have h5 := hE.clm_apply (hvd y).hasFDerivAt
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
      = Coercive.Internal.SmoothPieceEps.curlLinear ((1 / P) • T' + (1 / 2 : ℝ) • D
        + (1 / 2 : ℝ) • (D.comp (ContinuousLinearMap.id ℝ Space) + D2.flip y)
        + (D.comp E + D2.flip (W σ y)) + (E.comp D + E2.flip (v σ y))) := by
    show curlVec (fderiv ℝ (smoothRight P W v σ) y) - curlVec (fderiv ℝ (negSumSecondPartials v σ) y) = _
    rw [eS, eN, hS.fderiv, hN.fderiv, ← Coercive.Internal.SmoothPieceEps.curlLinear_apply,
      ← Coercive.Internal.SmoothPieceEps.curlLinear_apply, map_add]
    abel
  have ht : deriv (fun s => vortField v s y) σ = Coercive.Internal.SmoothPieceEps.curlLinear T' :=
    (hasDerivAt_curlVec_weak fun u => Internal.SmoothPieceEpsFrequency.hasDerivAt_gradField_time hv.smooth σ y u).deriv
  have hgv : fderiv ℝ (vortField v σ) y = Coercive.Internal.SmoothPieceEps.curlLinear.comp D2 := vortGrad_eq hv2 σ y
  have hvv : vortField v σ y = Coercive.Internal.SmoothPieceEps.curlLinear D := rfl
  have hvW : vortField W σ y = Coercive.Internal.SmoothPieceEps.curlLinear E := rfl
  have hpair : Coercive.Internal.SmoothPieceEps.curlLinear (D.comp E)
      = -(E (Coercive.Internal.SmoothPieceEps.curlLinear D)) - D (Coercive.Internal.SmoothPieceEps.curlLinear E)
        - Coercive.Internal.SmoothPieceEps.curlLinear (E.comp D) := by
    have hA : ∑ i : Fin 3, D (unitVector i) i = 0 := hv.divergence_free σ y
    have hB : ∑ i : Fin 3, E (unitVector i) i = 0 := hWdiv σ y
    have := curl_comp_pair_weak D E hA hB
    rw [Coercive.Internal.SmoothPieceEps.curlLinear_apply, Coercive.Internal.SmoothPieceEps.curlLinear_apply,
      Coercive.Internal.SmoothPieceEps.curlLinear_apply, Coercive.Internal.SmoothPieceEps.curlLinear_apply, ← this]
    abel
  rw [lhs, ht]
  rw [hgv, hvv, hvW, flip_eq_of_symm_weak hsv, flip_eq_of_symm_weak hsv, flipE, ContinuousLinearMap.comp_id]
  simp only [ContinuousLinearMap.comp_apply, map_add, map_sub, map_smul]
  rw [hpair]
  module

open Coercive.Internal.SmoothRightGradient in
theorem ae_norm_gradField_smoothRight_le {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    (hW : IsWeakSecondDerivState W HW D) :
    ∃ g : ℝ × Space → ℝ, Continuous g ∧
      ∀ᵐ p ∂(volume : Measure (ℝ × Space)), ‖gradField (smoothRight P W v) p.1 p.2‖ ≤ g p := by
  have hV : ContDiff ℝ 3 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 3
  have hD0 : 0 ≤ D := by
    have h0 := (hW.decay 0 0).1
    rw [norm_zero, add_zero, div_one] at h0
    exact le_trans (norm_nonneg _) h0
  have hy1 : ∀ y : Space, (1 : ℝ) ≤ 1 + ‖y‖ := fun y => le_add_of_nonneg_right (norm_nonneg y)
  have hW0 : ∀ σ y, ‖W σ y‖ ≤ D := fun σ y =>
    (hW.decay σ y).1.trans (div_le_self hD0 (hy1 y))
  have hW1 : ∀ σ y, ‖fderiv ℝ (W σ) y‖ ≤ D := fun σ y =>
    (hW.decay σ y).2.1.trans (div_le_self hD0 (one_le_pow₀ (hy1 y)))
  have hW2 : ∀ σ y, ‖HW σ y‖ ≤ D := fun σ y =>
    (hW.decay σ y).2.2.trans (div_le_self hD0 (one_le_pow₀ (hy1 y)))
  have hDv : ContDiff ℝ 2 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    contDiff_fderiv_param (F := v) hV (by norm_num)
  have hD2v : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (fderiv ℝ (v z.1)) z.2) :=
    contDiff_fderiv_param (F := fun σ x => fderiv ℝ (v σ) x) hDv (by norm_num)
  have hD3v : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (fderiv ℝ (fderiv ℝ (v z.1))) z.2) :=
    contDiff_fderiv_param (F := fun σ x => fderiv ℝ (fderiv ℝ (v σ)) x) hD2v (by norm_num)
  have e1 : (fun z : ℝ × Space => ‖fderiv ℝ (transportPart P v z.1) z.2‖)
      = fun z => ‖fderiv ℝ (fun y => transportJoint P v (z.1, y)) z.2‖ := by
    funext z
    rw [transportPart_eq (hV.differentiable (by norm_num)) z.1]
  have c1 : Continuous fun z : ℝ × Space => ‖fderiv ℝ (transportPart P v z.1) z.2‖ := by
    rw [e1]
    exact (contDiff_fderiv_param (F := fun σ y => transportJoint P v (σ, y)) (m := 0)
      (contDiff_transportJoint (hV.of_le (by norm_num))) (by norm_num)).continuous.norm
  have cv : Continuous (fun z : ℝ × Space => v z.1 z.2) := hV.continuous
  refine ⟨fun z => ‖fderiv ℝ (transportPart P v z.1) z.2‖
    + ‖negTrace‖ * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (v z.1))) z.2‖
    + D * ‖fderiv ℝ (fderiv ℝ (v z.1)) z.2‖ + 2 * D * ‖fderiv ℝ (v z.1) z.2‖ + D * ‖v z.1 z.2‖, ?_, ?_⟩
  · exact (((c1.add (continuous_const.mul hD3v.continuous.norm)).add (continuous_const.mul hD2v.continuous.norm)).add
      (continuous_const.mul hDv.continuous.norm)).add (continuous_const.mul cv.norm)
  · filter_upwards [ae_good_point hW] with p hp
    have hn := Internal.WeakRightGradient.norm_fderiv_smoothRight_weak_le (P := P) hV hW.smooth p.1 p.2
      hp.1.differentiableAt
    rw [hp.1.fderiv] at hn
    have f1 : ‖fderiv ℝ (v p.1) p.2‖ * ‖fderiv ℝ (W p.1) p.2‖ ≤ ‖fderiv ℝ (v p.1) p.2‖ * D :=
      mul_le_mul_of_nonneg_left (hW1 p.1 p.2) (norm_nonneg _)
    have f2 : ‖fderiv ℝ (fderiv ℝ (v p.1)) p.2‖ * ‖W p.1 p.2‖ ≤ ‖fderiv ℝ (fderiv ℝ (v p.1)) p.2‖ * D :=
      mul_le_mul_of_nonneg_left (hW0 p.1 p.2) (norm_nonneg _)
    have f3 : ‖fderiv ℝ (W p.1) p.2‖ * ‖fderiv ℝ (v p.1) p.2‖ ≤ D * ‖fderiv ℝ (v p.1) p.2‖ :=
      mul_le_mul_of_nonneg_right (hW1 p.1 p.2) (norm_nonneg _)
    have f4 : ‖HW p.1 p.2‖ * ‖v p.1 p.2‖ ≤ D * ‖v p.1 p.2‖ :=
      mul_le_mul_of_nonneg_right (hW2 p.1 p.2) (norm_nonneg _)
    show ‖fderiv ℝ (smoothRight P W v p.1) p.2‖ ≤ _
    linarith

theorem orbit_integrable_of_continuous_weak {X : ℝ → Space → Space}
    (hX : Continuous (fun z : ℝ × Space => X z.1 z.2)) (z : ℝ × Space) :
    Integrable (fun p : ℝ × ℝ => X (z.1 + p.1) (axialRot p.2 z.2)) orbitBox :=
  Coercive.StretchInternal.integrable_box_of_continuous (hX.comp ((continuous_const.add continuous_fst).prodMk
    (Coercive.Internal.Field.axialRot_comp_continuous continuous_snd continuous_const)))

theorem modeVel_add_orbit {X Y : ℝ → Space → Space} {z : ℝ × Space}
    (hX : Integrable (fun p : ℝ × ℝ => X (z.1 + p.1) (axialRot p.2 z.2)) orbitBox)
    (hY : Integrable (fun p : ℝ × ℝ => Y (z.1 + p.1) (axialRot p.2 z.2)) orbitBox)
    (ι : ℤ × ℤ) : modeVel ι (X + Y) z.1 z.2 = modeVel ι X z.1 z.2 + modeVel ι Y z.1 z.2 := by
  have e := Coercive.Internal.DensityPassageLinear.modeVel_sub (v₁ := fun σ y => X σ y + Y σ y) (v₂ := Y)
    (z := z) (hX.add hY) hY ι
  have e2 : (fun σ y => X σ y + Y σ y - Y σ y) = X := by
    funext σ y
    simp
  rw [e2] at e
  change modeVel ι (fun σ y => X σ y + Y σ y) z.1 z.2 = _
  rw [e]
  abel

theorem ae_mode_identity_weak {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    (hW : IsWeakSecondDerivState W HW D) (a : ℝ) {R : ℝ → Space → Space}
    (hR : ∀ s x, R s x = fderiv ℝ (vortField v s) x (W s x + (1 / 2 : ℝ) • x - a • axialPerp x)
      - fderiv ℝ (W s) x (vortField v s x) + curlVec (HW s x (v s x))
      - fderiv ℝ (v s) x (vortField W s x) + a • axialPerp (vortField v s x))
    {μ : Measure (ℝ × Space)} (hμ : μ ≪ (volume : Measure (ℝ × Space)))
    (hRi : ∀ᵐ z ∂μ, Integrable (fun q : ℝ × ℝ => R (z.1 + q.1) (axialRot q.2 z.2)) orbitBox) :
    ∀ᵐ z ∂μ, ∀ (ι : ℤ × ℤ) (i : Fin 3),
      vortMode (smoothRight P W v) ι z.1 z.2 i - vortMode (negSumSecondPartials v) ι z.1 z.2 i
        = ((PieceWeights.frameFreq P a ι : ℂ) * Complex.I) * vortMode v ι z.1 z.2 i
          + vortMode v ι z.1 z.2 i + modeVel ι R z.1 z.2 i := by
  have hv3 : ContDiff ℝ 3 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 3
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 2
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 1
  have hH := SmoothEpsInternal.contDiff_secondDerivField_one hv3
  have hNL : ContDiff ℝ 1 (fun z : ℝ × Space => negSumSecondPartials v z.1 z.2) := by
    unfold negSumSecondPartials secondDerivTrace secondDerivField
    exact (ContDiff.sum fun j _ => (hH.clm_apply contDiff_const).clm_apply contDiff_const).neg
  have cB : Continuous (fun z : ℝ × Space => vortField (negSumSecondPartials v) z.1 z.2) :=
    Coercive.Internal.SmoothPieceEps.curlLinear.continuous.comp (fderiv_slice_continuous hNL)
  have hVs := vortField_smooth hv.smooth
  have c1' : Continuous (fun z : ℝ × Space => deriv (fun r => vortField v r z.2) z.1) :=
    (Internal.SmoothPieceEpsFrequency.timeDeriv_smooth hVs).continuous
  have c1 : Continuous (fun z : ℝ × Space =>
      ((1 / P : ℝ) • fun s x => deriv (fun r => vortField v r x) s) z.1 z.2) :=
    c1'.const_smul (1 / P)
  have c2 : Continuous (fun z : ℝ × Space => vortField v z.1 z.2) := vortField_continuous hv2
  have c3' : Continuous (fun z : ℝ × Space =>
      fderiv ℝ (vortField v z.1) z.2 (axialPerp z.2) - axialPerp (vortField v z.1 z.2)) :=
    ((vortGrad_continuous hv2).clm_apply (axialPerp_continuous.comp continuous_snd)).sub
      (axialPerp_continuous.comp c2)
  have c3 : Continuous (fun z : ℝ × Space => (a • fun s x =>
      fderiv ℝ (vortField v s) x (axialPerp x) - axialPerp (vortField v s x)) z.1 z.2) := c3'.const_smul a
  have c12 : Continuous (fun z : ℝ × Space => (((1 / P : ℝ) • fun s x => deriv (fun r => vortField v r x) s)
      + vortField v) z.1 z.2) := c1.add c2
  have c123 : Continuous (fun z : ℝ × Space => (((1 / P : ℝ) • fun s x => deriv (fun r => vortField v r x) s)
      + vortField v + (a • fun s x => fderiv ℝ (vortField v s) x (axialPerp x) - axialPerp (vortField v s x)))
      z.1 z.2) := c12.add c3
  obtain ⟨g, hg, hb⟩ := ae_norm_gradField_smoothRight_le hv hW
  have hGi := ae_orbit_integrable_of_bound
    (Internal.WeakRightGradient.rightGradient_finite_of_weak hv hW).1 hg hb
  have hId : ∀ᵐ p ∂(volume : Measure (ℝ × Space)),
      vortField (smoothRight P W v) p.1 p.2 - vortField (negSumSecondPartials v) p.1 p.2
        = ((((1 / P : ℝ) • fun s x => deriv (fun r => vortField v r x) s) + vortField v
          + (a • fun s x => fderiv ℝ (vortField v s) x (axialPerp x) - axialPerp (vortField v s x))) + R) p.1 p.2 := by
    filter_upwards [ae_good_point hW] with p hp
    rw [vortField_identity_weak (a := a) hv hW.smooth hW.divergence_free p.1 p.2 hp.1 hp.2]
    show _ = _ + R p.1 p.2
    rw [hR]
    rfl
  filter_upwards [hμ.ae_le hGi, hRi, hμ.ae_le (ae_orbit_of_ae hId)] with z hzG hzR hzI
  intro ι i
  have hsR : vortMode (smoothRight P W v) ι z.1 z.2 = modeVel ι (vortField (smoothRight P W v)) z.1 z.2 :=
    Coercive.Internal.CurlEnergy.curlOfGrad_modeGrad_eq ι hzG
  have iA : Integrable (fun q : ℝ × ℝ => vortField (smoothRight P W v) (z.1 + q.1) (axialRot q.2 z.2)) orbitBox :=
    Coercive.Internal.SmoothPieceEps.curlLinear.integrable_comp hzG
  have iB := orbit_integrable_of_continuous_weak cB z
  have e1 := Coercive.Internal.DensityPassageLinear.modeVel_sub iA iB ι
  have e2 := modeVel_congr_orbit (X := fun s x => vortField (smoothRight P W v) s x - vortField (negSumSecondPartials v) s x)
    (Y := (((1 / P : ℝ) • fun s x => deriv (fun r => vortField v r x) s) + vortField v
          + (a • fun s x => fderiv ℝ (vortField v s) x (axialPerp x) - axialPerp (vortField v s x))) + R) hzI ι
  have e3 := modeVel_add_orbit (X := ((1 / P : ℝ) • fun s x => deriv (fun r => vortField v r x) s) + vortField v
          + (a • fun s x => fderiv ℝ (vortField v s) x (axialPerp x) - axialPerp (vortField v s x))) (Y := R)
    (orbit_integrable_of_continuous_weak c123 z) hzR ι
  rw [hsR, vortMode_eq_modeVel hNL, vortMode_eq_modeVel hv1]
  have k2 := congrFun e1 i
  simp only [Pi.sub_apply] at k2
  rw [← k2, e2, e3, Coercive.Internal.Field.modeVel_add c12 c3,
    Coercive.Internal.Field.modeVel_add c1 c2, Coercive.Internal.Field.modeVel_smul,
    Coercive.Internal.Field.modeVel_smul, modeVel_time_vort hv, modeVel_angular_vort hv]
  simp only [Pi.add_apply]
  unfold PieceWeights.frameFreq
  push_cast
  ring

theorem boxInt_congr_orbit {F F' : ℝ → ℝ → ℂ} (h : ∀ᵐ q ∂orbitBox, F q.1 q.2 = F' q.1 q.2) :
    Coercive.Internal.MuSmooth.boxInt F = Coercive.Internal.MuSmooth.boxInt F' := by
  have h2 := Measure.ae_ae_of_ae_prod h
  rw [ae_restrict_iff' measurableSet_Ioc] at h2
  unfold Coercive.Internal.MuSmooth.boxInt
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [h2] with τ hτ hτI
  rw [Set.uIoc_of_le zero_le_one] at hτI
  have h3 := hτ hτI
  rw [ae_restrict_iff' measurableSet_Ioc] at h3
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [h3] with φ hφ hφI
  rw [Set.uIoc_of_le (by positivity)] at hφI
  exact hφ hφI

open Coercive.Internal.MuSmooth in
theorem mode_product_orbit (s : Finset (ℤ × ℤ)) (G : ℝ → Space → (Space →L[ℝ] Space)) (v : ℝ → Space → Space)
    (hvc : Continuous fun z : ℝ × Space => v z.1 z.2) (z : ℝ × Space)
    (D : Fin 3 → Fin 3 → ℂ) (g : ℤ × ℤ → Fin 3 × Fin 3 → ℂ)
    (hE : ∀ᵐ q ∂orbitBox, ∀ i j : Fin 3,
      ((axialRot (-q.2) (G (z.1 + q.1) (axialRot q.2 z.2) (axialRot q.2 (unitVector j))) i : ℝ) : ℂ)
        = D i j + ∑ α ∈ s, Complex.exp (((2 * Real.pi * α.1 * q.1 + α.2 * q.2 : ℝ) : ℂ) * Complex.I) * g α (i, j))
    (ι : ℤ × ℤ) (i : Fin 3) :
    modeVel ι (fun σ y => G σ y (v σ y)) z.1 z.2 i
      = ∑ j : Fin 3, (D i j * modeVel ι v z.1 z.2 j + ∑ α ∈ s, g α (i, j) * modeVel (ι - α) v z.1 z.2 j) := by
  set E : ℤ × ℤ → ℝ → ℝ → ℂ := fun κ τ φ =>
    Complex.exp (-(((2 * Real.pi * κ.1 * τ + κ.2 * φ : ℝ) : ℂ) * Complex.I)) with hEdef
  set U : Fin 3 → ℝ → ℝ → ℂ := fun j τ φ => ((axialRot (-φ) (v (z.1 + τ) (axialRot φ z.2)) j : ℝ) : ℂ) with hUdef
  have hUc : ∀ j, Continuous fun p : ℝ × ℝ => U j p.1 p.2 := fun j => cont_rot_field v hvc z.1 z.2 j
  have hEc : ∀ κ, Continuous fun p : ℝ × ℝ => E κ p.1 p.2 := fun κ => cont_exp_pair κ
  have hmv : ∀ κ j, modeVel κ v z.1 z.2 j = (1 / (2 * Real.pi) : ℂ) * boxInt (fun τ φ => E κ τ φ * U j τ φ) :=
    fun κ j => rfl
  have hpt : ∀ᵐ q ∂orbitBox, E ι q.1 q.2 * ((axialRot (-q.2) (G (z.1 + q.1) (axialRot q.2 z.2)
        (v (z.1 + q.1) (axialRot q.2 z.2))) i : ℝ) : ℂ)
      = ∑ j : Fin 3, (D i j * (E ι q.1 q.2 * U j q.1 q.2)
        + ∑ α ∈ s, g α (i, j) * (E (ι - α) q.1 q.2 * U j q.1 q.2)) := by
    filter_upwards [hE] with q hq
    rw [rot_apply_clm]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hq i j, hEdef, hUdef]
    simp only
    rw [add_mul, mul_add, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun α _ => ?_
      rw [← exp_pair_mul ι α q.1 q.2]
      ring
  have hb := boxInt_congr_orbit (F := fun τ φ => E ι τ φ * ((axialRot (-φ) (G (z.1 + τ) (axialRot φ z.2)
        (v (z.1 + τ) (axialRot φ z.2))) i : ℝ) : ℂ))
    (F' := fun τ φ => ∑ j : Fin 3, (D i j * (E ι τ φ * U j τ φ)
        + ∑ α ∈ s, g α (i, j) * (E (ι - α) τ φ * U j τ φ))) hpt
  have hlhs : modeVel ι (fun σ y => G σ y (v σ y)) z.1 z.2 i
      = (1 / (2 * Real.pi) : ℂ) * boxInt (fun τ φ => ∑ j : Fin 3, (D i j * (E ι τ φ * U j τ φ)
        + ∑ α ∈ s, g α (i, j) * (E (ι - α) τ φ * U j τ φ))) := by
    rw [← hb]
    rfl
  have hc1 : ∀ κ j, Continuous fun p : ℝ × ℝ => E κ p.1 p.2 * U j p.1 p.2 := fun κ j => (hEc κ).mul (hUc j)
  rw [hlhs, boxInt_sum _ _ (fun j => ((continuous_const.mul (hc1 ι j)).add
    (continuous_finsetSum _ fun α _ => continuous_const.mul (hc1 (ι - α) j))))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [boxInt_add _ _ (continuous_const.mul (hc1 ι j))
    (continuous_finsetSum _ fun α _ => continuous_const.mul (hc1 (ι - α) j)),
    boxInt_sum _ _ (fun α => continuous_const.mul (hc1 (ι - α) j)), boxInt_const_mul, hmv]
  simp_rw [boxInt_const_mul, hmv]
  rw [mul_add, Finset.mul_sum, mul_left_comm]
  congr 1
  exact Finset.sum_congr rfl fun α _ => mul_left_comm _ _ _

end Internal.WeakModeIdentity

end CoerciveWeak

end Breakdown
