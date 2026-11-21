import Breakdown.Cert.CoerciveNodes

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal

namespace SmoothRightGradient

theorem contDiff_fderiv_param {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n m : WithTop ℕ∞}
    {F : ℝ → Space → E} (hF : ContDiff ℝ n (fun z : ℝ × Space => F z.1 z.2)) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (fun z : ℝ × Space => fderiv ℝ (F z.1) z.2) :=
  ContDiff.fderiv (f := fun (p : ℝ × Space) (x : Space) => F p.1 x) (g := fun p => p.2)
    (hF.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd hmn

theorem contDiff_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}
    {F : ℝ → Space → E} (hF : ContDiff ℝ n (fun z : ℝ × Space => F z.1 z.2)) (σ : ℝ) :
    ContDiff ℝ n (F σ) :=
  hF.comp (contDiff_const.prodMk contDiff_id)

theorem deriv_time_eq {v : ℝ → Space → Space} (hV : Differentiable ℝ (fun z : ℝ × Space => v z.1 z.2))
    (σ : ℝ) (y : Space) :
    deriv (fun s => v s y) σ = fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (σ, y) ((1 : ℝ), (0 : Space)) := by
  have h1 : HasDerivAt (fun s : ℝ => ((s, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) σ :=
    (hasDerivAt_id σ).prodMk (hasDerivAt_const σ y)
  exact (((hV (σ, y)).hasFDerivAt).comp_hasDerivAt σ h1).deriv

def transportJoint (P : ℝ) (v : ℝ → Space → Space) (z : ℝ × Space) : Space :=
  (1 / P) • fderiv ℝ (fun q : ℝ × Space => v q.1 q.2) z ((1 : ℝ), (0 : Space)) + (1 / 2 : ℝ) • v z.1 z.2
    + (1 / 2 : ℝ) • fderiv ℝ (v z.1) z.2 z.2

theorem transportPart_eq {P : ℝ} {v : ℝ → Space → Space}
    (hV : Differentiable ℝ (fun z : ℝ × Space => v z.1 z.2)) (σ : ℝ) :
    transportPart P v σ = fun y => transportJoint P v (σ, y) := by
  funext y
  unfold transportPart transportJoint
  rw [deriv_time_eq hV σ y]

theorem contDiff_transportJoint {P : ℝ} {v : ℝ → Space → Space}
    (hV : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2)) :
    ContDiff ℝ 1 (transportJoint P v) := by
  have hd : ContDiff ℝ 1 (fun z : ℝ × Space =>
      fderiv ℝ (fun q : ℝ × Space => v q.1 q.2) z ((1 : ℝ), (0 : Space))) :=
    (hV.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hg : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    contDiff_fderiv_param (F := v) hV (by norm_num)
  exact ((hd.const_smul _).add ((hV.of_le (by norm_num)).const_smul _)).add
    ((hg.clm_apply contDiff_snd).const_smul _)

def negTrace : (Space →L[ℝ] Space →L[ℝ] Space) →L[ℝ] Space :=
  -∑ j : Fin 3, (ContinuousLinearMap.apply ℝ Space (unitVector j)).comp
    (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector j))

theorem negTrace_apply (H : Space →L[ℝ] Space →L[ℝ] Space) : negTrace H = -secondDerivTrace H := by
  simp [negTrace, secondDerivTrace]

theorem smoothRight_eq (P : ℝ) (W v : ℝ → Space → Space) (σ : ℝ) :
    smoothRight P W v σ = fun y => transportPart P v σ y + negTrace (fderiv ℝ (fderiv ℝ (v σ)) y)
      + fderiv ℝ (v σ) y (W σ y) + fderiv ℝ (W σ) y (v σ y) := by
  funext y
  simp only [smoothRight, transportPart, secondDerivField, negTrace_apply]
  abel

theorem matSq_le (G : Space →L[ℝ] Space) : matSq G ≤ 3 * ‖G‖ ^ 2 := by
  unfold matSq
  have h : ∀ i : Fin 3, ‖G (unitVector i)‖ ^ 2 ≤ ‖G‖ ^ 2 := fun i => by
    have h1 : ‖G (unitVector i)‖ ≤ ‖G‖ := by
      calc ‖G (unitVector i)‖ ≤ ‖G‖ * ‖unitVector i‖ := G.le_opNorm _
        _ = ‖G‖ := by rw [show ‖unitVector i‖ = 1 by simp [unitVector], mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ∑ i : Fin 3, ‖G (unitVector i)‖ ^ 2 ≤ ∑ _i : Fin 3, ‖G‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖G‖ ^ 2 := by simp

theorem apply_hasFDerivAt {f g : Space → Space} {y : Space} (hf : DifferentiableAt ℝ (fderiv ℝ f) y)
    (hg : DifferentiableAt ℝ g y) :
    HasFDerivAt (fun x => fderiv ℝ f x (g x))
      ((fderiv ℝ f y).comp (fderiv ℝ g y) + (fderiv ℝ (fderiv ℝ f) y).flip (g y)) y :=
  hf.hasFDerivAt.clm_apply hg.hasFDerivAt

theorem norm_apply_deriv_le (A : Space →L[ℝ] Space) (B : Space →L[ℝ] Space) (C : Space →L[ℝ] Space →L[ℝ] Space)
    (u : Space) : ‖A.comp B + C.flip u‖ ≤ ‖A‖ * ‖B‖ + ‖C‖ * ‖u‖ := by
  refine (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) ?_)
  calc ‖C.flip u‖ ≤ ‖C.flip‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖C‖ * ‖u‖ := by rw [ContinuousLinearMap.opNorm_flip]

theorem norm_fderiv_smoothRight_le {P : ℝ} {W v : ℝ → Space → Space}
    (hV : ContDiff ℝ 3 (fun z : ℝ × Space => v z.1 z.2)) (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (σ : ℝ) (y : Space) :
    ‖fderiv ℝ (smoothRight P W v σ) y‖ ≤ ‖fderiv ℝ (transportPart P v σ) y‖
      + ‖negTrace‖ * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (v σ))) y‖
      + (‖fderiv ℝ (v σ) y‖ * ‖fderiv ℝ (W σ) y‖ + ‖fderiv ℝ (fderiv ℝ (v σ)) y‖ * ‖W σ y‖)
      + (‖fderiv ℝ (W σ) y‖ * ‖fderiv ℝ (v σ) y‖ + ‖fderiv ℝ (fderiv ℝ (W σ)) y‖ * ‖v σ y‖) := by
  have hs : ContDiff ℝ 3 (v σ) := contDiff_slice hV σ
  have hws : ContDiff ℝ 2 (W σ) := contDiff_slice hW σ
  have hv1 : ContDiff ℝ 2 (fderiv ℝ (v σ)) := hs.fderiv_right (m := 2) (by norm_num)
  have hv2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (v σ))) := hv1.fderiv_right (m := 1) (by norm_num)
  have hw1 : ContDiff ℝ 1 (fderiv ℝ (W σ)) := hws.fderiv_right (m := 1) (by norm_num)
  have htp : DifferentiableAt ℝ (transportPart P v σ) y := by
    rw [transportPart_eq (hV.differentiable (by norm_num)) σ]
    exact ((contDiff_transportJoint (P := P) (hV.of_le (by norm_num))).comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num) y
  have d1 := htp.hasFDerivAt
  have d2 : HasFDerivAt (fun x => negTrace (fderiv ℝ (fderiv ℝ (v σ)) x))
      (negTrace.comp (fderiv ℝ (fderiv ℝ (fderiv ℝ (v σ))) y)) y :=
    negTrace.hasFDerivAt.comp y ((hv2.differentiable (by norm_num)) y).hasFDerivAt
  have d3 := apply_hasFDerivAt (f := v σ) (g := W σ) ((hv1.differentiable (by norm_num)) y)
    ((hws.differentiable (by norm_num)) y)
  have d4 := apply_hasFDerivAt (f := W σ) (g := v σ) ((hw1.differentiable (by norm_num)) y)
    ((hs.differentiable (by norm_num)) y)
  have H := ((d1.add d2).add d3).add d4
  rw [smoothRight_eq P W v σ]
  refine (congrArg (fun L => ‖L‖) H.fderiv).trans_le ?_
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add le_rfl (ContinuousLinearMap.opNorm_comp_le _ _)))
    (norm_apply_deriv_le _ _ _ _))) (norm_apply_deriv_le _ _ _ _))

theorem norm_iteratedFDeriv_two_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Space → E)
    (y : Space) : ‖iteratedFDeriv ℝ 2 f y‖ = ‖fderiv ℝ (fderiv ℝ f) y‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]

theorem norm_iteratedFDeriv_three_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Space → E)
    (y : Space) : ‖iteratedFDeriv ℝ 3 f y‖ = ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 2), ← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]

theorem periodLIntegral_add_of_continuous {f g : ℝ → Space → ℝ} (hf : Continuous fun z : ℝ × Space => f z.1 z.2) :
    periodLIntegral (fun σ y => f σ y + g σ y) ≤ periodLIntegral f + periodLIntegral g := by
  unfold periodLIntegral
  have hmf : Measurable (fun z : ℝ × Space => ENNReal.ofReal (f z.1 z.2)) :=
    ENNReal.measurable_ofReal.comp hf.measurable
  have hA : Measurable (fun σ => ∫⁻ y, ENNReal.ofReal (f σ y)) := hmf.lintegral_prod_right'
  calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (f σ y + g σ y))
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ((∫⁻ y, ENNReal.ofReal (f σ y)) + ∫⁻ y, ENNReal.ofReal (g σ y)) := by
        refine lintegral_mono fun σ => ?_
        have hfy : Measurable (fun y => ENNReal.ofReal (f σ y)) :=
          ENNReal.measurable_ofReal.comp (hf.comp (continuous_const.prodMk continuous_id)).measurable
        rw [← lintegral_add_left hfy]
        exact lintegral_mono fun y => ENNReal.ofReal_add_le
    _ = _ := lintegral_add_left hA _

theorem periodLIntegral_const_mul_lt_top {f : ℝ → Space → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : periodLIntegral f < ⊤) : periodLIntegral (fun σ y => c * f σ y) < ⊤ := by
  have hle : periodLIntegral (fun σ y => c * f σ y) ≤ ENNReal.ofReal c * periodLIntegral f := by
    unfold periodLIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun σ => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y => ?_
    rw [ENNReal.ofReal_mul hc]
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h)

theorem periodLIntegral_lt_top_of_le {f g : ℝ → Space → ℝ} (hfg : ∀ σ y, f σ y ≤ g σ y)
    (h : periodLIntegral g < ⊤) : periodLIntegral f < ⊤ :=
  lt_of_le_of_lt (lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hfg σ y)) h

theorem sq_sum_five_le (a b c d e : ℝ) :
    (a + b + c + d + e) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d), sq_nonneg (c - e), sq_nonneg (d - e)]

theorem gradField_smoothRight_sq_finite {P : ℝ} {W v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hD : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) :
    periodLIntegral (fun σ y => matSq (gradField (smoothRight P W v) σ y)) < ⊤ := by
  obtain ⟨D, hD⟩ := hD
  have hV : ContDiff ℝ 3 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 3
  have hD0 : 0 ≤ D := by
    have h := hD 0 0 0 (by norm_num)
    have : 0 ≤ D / (1 + ‖(0 : Space)‖) ^ (0 + 1) := (norm_nonneg _).trans h
    simpa using this
  have hW0 : ∀ σ y, ‖W σ y‖ ≤ D := fun σ y => by
    have h := hD σ y 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero] at h
    refine h.trans (div_le_self hD0 ?_)
    rw [zero_add, pow_one]
    exact le_add_of_nonneg_right (norm_nonneg y)
  have hW1 : ∀ σ y, ‖fderiv ℝ (W σ) y‖ ≤ D := fun σ y => by
    have h := hD σ y 1 (by norm_num)
    rw [norm_iteratedFDeriv_one] at h
    refine h.trans (div_le_self hD0 ?_)
    exact one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg y))
  have hW2 : ∀ σ y, ‖fderiv ℝ (fderiv ℝ (W σ)) y‖ * ‖v σ y‖ ≤ D * (‖v σ y‖ / (1 + ‖y‖)) := fun σ y => by
    have h := hD σ y 2 (by norm_num)
    rw [norm_iteratedFDeriv_two_eq] at h
    have hy : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
    have h3 : D / (1 + ‖y‖) ^ (2 + 1) ≤ D / (1 + ‖y‖) := by
      refine div_le_div_of_nonneg_left hD0 (by positivity) ?_
      exact le_self_pow₀ hy (by norm_num)
    calc ‖fderiv ℝ (fderiv ℝ (W σ)) y‖ * ‖v σ y‖ ≤ D / (1 + ‖y‖) * ‖v σ y‖ :=
          mul_le_mul_of_nonneg_right (h.trans h3) (norm_nonneg _)
      _ = D * (‖v σ y‖ / (1 + ‖y‖)) := by ring
  set c := ‖negTrace‖
  set b1 : ℝ → Space → ℝ := fun σ y => ‖fderiv ℝ (transportPart P v σ) y‖
  set b2 : ℝ → Space → ℝ := fun σ y => ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (v σ))) y‖
  set b3 : ℝ → Space → ℝ := fun σ y => ‖fderiv ℝ (fderiv ℝ (v σ)) y‖
  set b4 : ℝ → Space → ℝ := fun σ y => ‖fderiv ℝ (v σ) y‖
  set b5 : ℝ → Space → ℝ := fun σ y => ‖v σ y‖ / (1 + ‖y‖)
  have hpt : ∀ σ y, matSq (gradField (smoothRight P W v) σ y) ≤
      15 * (b1 σ y ^ 2 + c ^ 2 * b2 σ y ^ 2 + D ^ 2 * b3 σ y ^ 2 + 4 * D ^ 2 * b4 σ y ^ 2
        + D ^ 2 * b5 σ y ^ 2) := fun σ y => by
    have hn := norm_fderiv_smoothRight_le (P := P) hV hW σ y
    have e1 : ‖fderiv ℝ (v σ) y‖ * ‖fderiv ℝ (W σ) y‖ ≤ b4 σ y * D :=
      mul_le_mul_of_nonneg_left (hW1 σ y) (norm_nonneg _)
    have e2 : ‖fderiv ℝ (fderiv ℝ (v σ)) y‖ * ‖W σ y‖ ≤ b3 σ y * D :=
      mul_le_mul_of_nonneg_left (hW0 σ y) (norm_nonneg _)
    have e3 : ‖fderiv ℝ (W σ) y‖ * ‖fderiv ℝ (v σ) y‖ ≤ D * b4 σ y :=
      mul_le_mul_of_nonneg_right (hW1 σ y) (norm_nonneg _)
    have e4 := hW2 σ y
    have hsum : ‖gradField (smoothRight P W v) σ y‖ ≤
        b1 σ y + c * b2 σ y + D * b3 σ y + 2 * D * b4 σ y + D * b5 σ y := by
      show ‖fderiv ℝ (smoothRight P W v σ) y‖ ≤ _
      simp only [b1, b2, b3, b4, b5]
      linarith
    have h0 : 0 ≤ ‖gradField (smoothRight P W v) σ y‖ := norm_nonneg _
    have hsq := pow_le_pow_left₀ h0 hsum 2
    have h5 := sq_sum_five_le (b1 σ y) (c * b2 σ y) (D * b3 σ y) (2 * D * b4 σ y) (D * b5 σ y)
    have hf := matSq_le (gradField (smoothRight P W v) σ y)
    nlinarith [hsq, h5, hf]
  have hs : ∀ σ, ContDiff ℝ 3 (v σ) := contDiff_slice hV
  have cb1 : Continuous fun z : ℝ × Space => b1 z.1 z.2 ^ 2 := by
    have e : (fun z : ℝ × Space => b1 z.1 z.2) = fun z => ‖fderiv ℝ (fun y => transportJoint P v (z.1, y)) z.2‖ := by
      funext z
      simp only [b1]
      rw [transportPart_eq (hV.differentiable (by norm_num)) z.1]
    have hc : Continuous fun z : ℝ × Space => fderiv ℝ (fun y => transportJoint P v (z.1, y)) z.2 :=
      (contDiff_fderiv_param (F := fun σ y => transportJoint P v (σ, y)) (m := 0)
        (contDiff_transportJoint (hV.of_le (by norm_num))) (by norm_num)).continuous
    rw [show (fun z : ℝ × Space => b1 z.1 z.2 ^ 2) = fun z => (fun z : ℝ × Space => b1 z.1 z.2) z ^ 2 from rfl, e]
    exact hc.norm.pow 2
  have hDv : ContDiff ℝ 2 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    contDiff_fderiv_param (F := v) hV (by norm_num)
  have hD2v : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (fderiv ℝ (v z.1)) z.2) :=
    contDiff_fderiv_param (F := fun σ x => fderiv ℝ (v σ) x) hDv (by norm_num)
  have hD3v : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (fderiv ℝ (fderiv ℝ (v z.1))) z.2) :=
    contDiff_fderiv_param (F := fun σ x => fderiv ℝ (fderiv ℝ (v σ)) x) hD2v (by norm_num)
  have cb2 : Continuous fun z : ℝ × Space => c ^ 2 * b2 z.1 z.2 ^ 2 :=
    continuous_const.mul (hD3v.continuous.norm.pow 2)
  have cb3 : Continuous fun z : ℝ × Space => D ^ 2 * b3 z.1 z.2 ^ 2 :=
    continuous_const.mul (hD2v.continuous.norm.pow 2)
  have cb4 : Continuous fun z : ℝ × Space => 4 * D ^ 2 * b4 z.1 z.2 ^ 2 :=
    continuous_const.mul (hDv.continuous.norm.pow 2)
  have fin1 : periodLIntegral (fun σ y => b1 σ y ^ 2) < ⊤ := by
    refine periodLIntegral_lt_top_of_le (fun σ y => le_of_eq ?_) (hv.transport_finite 1)
    simp only [b1]
    rw [norm_iteratedFDeriv_one]
  have fin2 : periodLIntegral (fun σ y => c ^ 2 * b2 σ y ^ 2) < ⊤ := by
    refine periodLIntegral_const_mul_lt_top (by positivity) ?_
    refine periodLIntegral_lt_top_of_le (fun σ y => le_of_eq ?_) (hv.derivatives_finite 3 (by norm_num))
    simp only [b2]
    rw [norm_iteratedFDeriv_three_eq]
  have fin3 : periodLIntegral (fun σ y => D ^ 2 * b3 σ y ^ 2) < ⊤ := by
    refine periodLIntegral_const_mul_lt_top (by positivity) ?_
    refine periodLIntegral_lt_top_of_le (fun σ y => le_of_eq ?_) (hv.derivatives_finite 2 (by norm_num))
    simp only [b3]
    rw [norm_iteratedFDeriv_two_eq]
  have fin4 : periodLIntegral (fun σ y => 4 * D ^ 2 * b4 σ y ^ 2) < ⊤ := by
    refine periodLIntegral_const_mul_lt_top (by positivity) ?_
    refine periodLIntegral_lt_top_of_le (fun σ y => le_of_eq ?_) (hv.derivatives_finite 1 (by norm_num))
    simp only [b4]
    rw [norm_iteratedFDeriv_one]
  have fin5 : periodLIntegral (fun σ y => D ^ 2 * b5 σ y ^ 2) < ⊤ := by
    refine periodLIntegral_const_mul_lt_top (by positivity) ?_
    refine periodLIntegral_lt_top_of_le (fun σ y => le_of_eq ?_) hv.weighted_finite
    simp only [b5]
    rw [div_pow]
  have hsplit : periodLIntegral (fun σ y => b1 σ y ^ 2 + c ^ 2 * b2 σ y ^ 2 + D ^ 2 * b3 σ y ^ 2
      + 4 * D ^ 2 * b4 σ y ^ 2 + D ^ 2 * b5 σ y ^ 2) < ⊤ := by
    refine lt_of_le_of_lt (periodLIntegral_add_of_continuous (((cb1.add cb2).add cb3).add cb4)) ?_
    refine ENNReal.add_lt_top.mpr ⟨lt_of_le_of_lt (periodLIntegral_add_of_continuous ((cb1.add cb2).add cb3)) ?_, fin5⟩
    refine ENNReal.add_lt_top.mpr ⟨lt_of_le_of_lt (periodLIntegral_add_of_continuous (cb1.add cb2)) ?_, fin4⟩
    refine ENNReal.add_lt_top.mpr ⟨lt_of_le_of_lt (periodLIntegral_add_of_continuous cb1) ?_, fin3⟩
    exact ENNReal.add_lt_top.mpr ⟨fin1, fin2⟩
  exact periodLIntegral_lt_top_of_le hpt (periodLIntegral_const_mul_lt_top (by norm_num) hsplit)

theorem smoothRight_periodic {P : ℝ} {W v : ℝ → Space → Space} (hv : IsTimePeriodic v) (hW : IsTimePeriodic W) :
    IsTimePeriodic (smoothRight P W v) := by
  intro σ y
  have ev : v (σ + 1) = v σ := funext (hv σ)
  have eW : W (σ + 1) = W σ := funext (hW σ)
  have ed : deriv (fun s => v s y) (σ + 1) = deriv (fun s => v s y) σ := by
    have e : (fun s => v (s + 1) y) = (fun s => v s y) := funext fun s => hv s y
    rw [← deriv_comp_add_const, e]
  unfold smoothRight secondDerivField
  rw [ed, ev, eW]

theorem gradField_smoothRight_square {P : ℝ} {W v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hD : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) :
    AEStronglyMeasurable (fun z : ℝ × Space => gradField (smoothRight P W v) z.1 z.2) volume ∧
      IsTimePeriodic (gradField (smoothRight P W v)) ∧
      periodLIntegral (fun σ y => matSq (gradField (smoothRight P W v) σ y)) < ⊤ := by
  have hV : ContDiff ℝ 3 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 3
  have hDv : ContDiff ℝ 2 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    contDiff_fderiv_param (F := v) hV (by norm_num)
  have hD2v : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (fderiv ℝ (v z.1)) z.2) :=
    contDiff_fderiv_param (F := fun σ x => fderiv ℝ (v σ) x) hDv (by norm_num)
  have hDW : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
    contDiff_fderiv_param (F := W) hW (by norm_num)
  have hR : ContDiff ℝ 1 (fun z : ℝ × Space => smoothRight P W v z.1 z.2) := by
    have e : (fun z : ℝ × Space => smoothRight P W v z.1 z.2) = fun z =>
        transportJoint P v z + negTrace (fderiv ℝ (fderiv ℝ (v z.1)) z.2)
          + fderiv ℝ (v z.1) z.2 (W z.1 z.2) + fderiv ℝ (W z.1) z.2 (v z.1 z.2) := by
      funext z
      rw [smoothRight_eq P W v z.1, transportPart_eq (hV.differentiable (by norm_num)) z.1]
    rw [e]
    exact (((contDiff_transportJoint (hV.of_le (by norm_num))).add (negTrace.contDiff.comp hD2v)).add
      ((hDv.of_le (by norm_num)).clm_apply (hW.of_le (by norm_num)))).add (hDW.clm_apply (hV.of_le (by norm_num)))
  have hper : IsTimePeriodic (gradField (smoothRight P W v)) := by
    intro σ y
    have e : smoothRight P W v (σ + 1) = smoothRight P W v σ := funext (smoothRight_periodic hv.periodic hWp σ)
    unfold gradField
    rw [e]
  exact ⟨(contDiff_fderiv_param (F := smoothRight P W v) (m := 0) hR (by norm_num)).continuous.aestronglyMeasurable,
    hper, gradField_smoothRight_sq_finite hv hW hD⟩

end SmoothRightGradient

end Internal

end Coercive

end Breakdown
