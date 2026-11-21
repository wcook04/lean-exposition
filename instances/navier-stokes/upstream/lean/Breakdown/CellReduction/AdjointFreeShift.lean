import Breakdown.CellReduction.AdjointAssemblyAlgebra
import Breakdown.CellReduction.AdjointRepresentationSlice

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace Internal

namespace FreeShift

theorem entrySqSum_nonneg (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem continuous_entrySqSum : Continuous matSq := by
  unfold matSq
  fun_prop

theorem norm_apply_le_root (A : Space →L[ℝ] Space) (w : Space) :
    ‖A w‖ ≤ ‖w‖ * Real.sqrt (matSq A) := by
  rw [RepresentationParts.Internal.Slice.linear_expand A w, EuclideanSpace.norm_eq w]
  calc ‖∑ k : Fin 3, w k • A (unitVector k)‖ ≤ ∑ k : Fin 3, ‖w k‖ * ‖A (unitVector k)‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_smul]
    _ ≤ Real.sqrt (∑ k : Fin 3, ‖w k‖ ^ 2) * Real.sqrt (∑ k : Fin 3, ‖A (unitVector k)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt (∑ k : Fin 3, ‖w k‖ ^ 2) * Real.sqrt (matSq A) := rfl

theorem sum_abs_mul_sq_le {k : ℕ} (S : Finset (Fin k)) (q ϱ a : Fin k → ℝ) (hϱ : ∀ i ∈ S, 0 < ϱ i) :
    (∑ i ∈ S, |q i| * a i) ^ 2 ≤ (∑ i ∈ S, q i ^ 2 / ϱ i) * ∑ i ∈ S, ϱ i * a i ^ 2 := by
  have e : ∑ i ∈ S, |q i| * a i = ∑ i ∈ S, (|q i| / Real.sqrt (ϱ i)) * (Real.sqrt (ϱ i) * a i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have h := Real.sqrt_pos.2 (hϱ i hi)
    rw [← mul_assoc, div_mul_cancel₀ _ h.ne']
  rw [e]
  refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans (le_of_eq ?_)
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [div_pow, sq_abs, Real.sq_sqrt (hϱ i hi).le]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [mul_pow, Real.sq_sqrt (hϱ i hi).le]

theorem fderiv_combo {k : ℕ} {S : Finset (Fin k)} {f : Fin k → ℝ → Space → Space} {D : ℝ}
    (hf : ∀ i ∈ S, IsFlowPiece (f i) D) (q : Fin k → ℝ) (σ : ℝ) (y : Space) :
    fderiv ℝ (fun x => ∑ i ∈ S, q i • f i σ x) y = ∑ i ∈ S, q i • fderiv ℝ (f i σ) y := by
  have h : ∀ i ∈ S, HasFDerivAt (fun x => q i • f i σ x) (q i • fderiv ℝ (f i σ) y) y := fun i hi =>
    ((slice_differentiableAt (hf i hi).smooth σ y).hasFDerivAt).const_smul (q i)
  have h2 := HasFDerivAt.sum h
  have e : (∑ i ∈ S, fun x => q i • f i σ x) = fun x => ∑ i ∈ S, q i • f i σ x := by
    funext x
    simp [Finset.sum_apply]
  rw [e] at h2
  exact h2.fderiv

theorem gradient_slice_finite {Γ : Set Symmetry} {P : ℝ} {v g : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hv : IsPerturbation Γ P v G H g) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) < ⊤ := by
  have hm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (matSq (G z.1 z.2))) volume :=
    (continuous_entrySqSum.comp_aestronglyMeasurable hv.measurable_gradient).aemeasurable.ennreal_ofReal
  rw [Measure.volume_eq_prod] at hm
  have hm2 : AEMeasurable (fun s => ∫⁻ y, ENNReal.ofReal (matSq (G s y))) volume :=
    hm.lintegral_prod_right'
  have hfin : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) ≠ ⊤ :=
    hv.gradient_finite.ne
  exact ae_lt_top' hm2.restrict hfin

theorem convection_slice_integrable {v ζ F : Space → Space} {G : Space → (Space →L[ℝ] Space)} {D C γ : ℝ}
    (hvG : IsWeakGradient v G) (hv6 : ∫⁻ y, ENNReal.ofReal (‖v y‖ ^ 6) < ⊤)
    (hF : Continuous F) (hFb : ∀ y, ‖F y‖ ≤ D) (hζ : ContDiff ℝ 1 ζ) (hγ : 5 / 2 < γ) (hC : 0 ≤ C)
    (hζd : ∀ y, ‖fderiv ℝ ζ y‖ ≤ C / (1 + ‖y‖) ^ (γ + 1)) :
    Integrable (fun y => inner ℝ (v y) (fderiv ℝ ζ y (F y))) := by
  have hD : 0 ≤ D := (norm_nonneg _).trans (hFb 0)
  have hdζ : Continuous fun y => fderiv ℝ ζ y := hζ.continuous_fderiv one_ne_zero
  have iv6 : Integrable (fun y => ‖v y‖ ^ 6) := by
    refine ⟨hvG.1.aestronglyMeasurable.norm.pow 6, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => by positivity)).2 hv6
  have idζ6 : Integrable (fun y => ‖fderiv ℝ ζ y‖ ^ ((6 : ℝ) / 5)) :=
    RepresentationParts.Internal.Slice.decay_rpow_integrable hdζ.norm (fun y => norm_nonneg _)
      (by norm_num) hC hζd (by linarith)
  have ib : Integrable (fun y => D * (‖v y‖ ^ 6 + ‖fderiv ℝ ζ y‖ ^ ((6 : ℝ) / 5))) :=
    Integrable.const_mul (iv6.add idζ6) D
  refine ib.mono' (hvG.1.aestronglyMeasurable.inner (hdζ.clm_apply hF).aestronglyMeasurable)
    (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs]
  have h1 : ‖fderiv ℝ ζ y (F y)‖ ≤ ‖fderiv ℝ ζ y‖ * D :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (hFb y) (norm_nonneg _))
  have h2 := RepresentationParts.Internal.Slice.mul_le_sixth_add ‖v y‖ ‖fderiv ℝ ζ y‖
    (norm_nonneg _) (norm_nonneg _)
  calc |inner ℝ (v y) (fderiv ℝ ζ y (F y))| ≤ ‖v y‖ * ‖fderiv ℝ ζ y (F y)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v y‖ * (‖fderiv ℝ ζ y‖ * D) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = D * (‖v y‖ * ‖fderiv ℝ ζ y‖) := by ring
    _ ≤ D * (‖v y‖ ^ 6 + ‖fderiv ℝ ζ y‖ ^ ((6 : ℝ) / 5)) := mul_le_mul_of_nonneg_left h2 hD

theorem pairing_bound {Γ : Set Symmetry} {P : ℝ} {v g F ζ : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {w : ℝ → Space → ℝ} {Q ν : ℝ} (hv : IsPerturbation Γ P v G H g)
    (hF : Continuous (fun z : ℝ × Space => F z.1 z.2)) (hζ : Continuous (fun z : ℝ × Space => ζ z.1 z.2))
    (hw : Continuous (fun z : ℝ × Space => w z.1 z.2)) (hQ : 0 ≤ Q) (hν : 0 ≤ ν)
    (hpt : ∀ σ y, ‖F σ y‖ ^ 2 * ‖ζ σ y‖ ^ 2 ≤ Q * w σ y)
    (hval : periodLIntegral w ≤ ENNReal.ofReal (ν ^ 2)) :
    |∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (G σ y (F σ y)) (ζ σ y)| ≤
      Real.sqrt Q * ν * gradientNorm G := by
  set μ : Measure (ℝ × Space) :=
    ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space) with hμdef
  have hμ : μ = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    rw [hμdef, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hGμ : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) μ := by
    rw [hμ]; exact hv.measurable_gradient.restrict
  have ha : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (Real.sqrt (matSq (G z.1 z.2)))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((Real.continuous_sqrt.comp continuous_entrySqSum).comp_aestronglyMeasurable hGμ).aemeasurable
  have hb : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖F z.1 z.2‖ * ‖ζ z.1 z.2‖)) μ :=
    (ENNReal.continuous_ofReal.comp (hF.norm.mul hζ.norm)).aemeasurable
  have hab := ha.mul hb
  have h1 : ‖∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (G σ y (F σ y)) (ζ σ y)‖ₑ ≤
      ∫⁻ z, ((fun z : ℝ × Space => ENNReal.ofReal (Real.sqrt (matSq (G z.1 z.2))))
        * fun z : ℝ × Space => ENNReal.ofReal (‖F z.1 z.2‖ * ‖ζ z.1 z.2‖)) z ∂μ := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [hμdef, lintegral_prod _ hab]
    refine lintegral_mono fun σ => (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    calc |inner ℝ (G σ y (F σ y)) (ζ σ y)| ≤ ‖G σ y (F σ y)‖ * ‖ζ σ y‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖F σ y‖ * Real.sqrt (matSq (G σ y))) * ‖ζ σ y‖ :=
          mul_le_mul_of_nonneg_right (norm_apply_le_root _ _) (norm_nonneg _)
      _ = Real.sqrt (matSq (G σ y)) * (‖F σ y‖ * ‖ζ σ y‖) := by ring
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two ha hb
  have hA : ∫⁻ z, ENNReal.ofReal (Real.sqrt (matSq (G z.1 z.2))) ^ (2 : ℝ) ∂μ =
      periodLIntegral (fun σ y => matSq (G σ y)) := by
    have e : (fun z : ℝ × Space => ENNReal.ofReal (Real.sqrt (matSq (G z.1 z.2))) ^ (2 : ℝ)) =
        fun z => ENNReal.ofReal (matSq (G z.1 z.2)) := by
      funext z
      rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (entrySqSum_nonneg _)]
    have hm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (matSq (G z.1 z.2))) μ :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (continuous_entrySqSum.comp_aestronglyMeasurable hGμ).aemeasurable
    rw [e, hμdef, lintegral_prod _ hm]
    rfl
  have hB : ∫⁻ z, ENNReal.ofReal (‖F z.1 z.2‖ * ‖ζ z.1 z.2‖) ^ (2 : ℝ) ∂μ ≤
      ENNReal.ofReal Q * ENNReal.ofReal (ν ^ 2) := by
    have hwm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (w z.1 z.2)) μ :=
      (ENNReal.continuous_ofReal.comp hw).aemeasurable
    calc ∫⁻ z, ENNReal.ofReal (‖F z.1 z.2‖ * ‖ζ z.1 z.2‖) ^ (2 : ℝ) ∂μ
        ≤ ∫⁻ z, ENNReal.ofReal Q * ENNReal.ofReal (w z.1 z.2) ∂μ := by
          refine lintegral_mono fun z => ?_
          rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul hQ, mul_pow]
          exact ENNReal.ofReal_le_ofReal (hpt z.1 z.2)
      _ = ENNReal.ofReal Q * periodLIntegral w := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hμdef, lintegral_prod _ hwm]
          rfl
      _ ≤ ENNReal.ofReal Q * ENNReal.ofReal (ν ^ 2) := mul_le_mul' le_rfl hval
  have hE : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤ := hv.gradient_finite
  have hgn : 0 ≤ gradientNorm G := Real.sqrt_nonneg _
  have hA' : (∫⁻ z, ENNReal.ofReal (Real.sqrt (matSq (G z.1 z.2))) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) =
      ENNReal.ofReal (gradientNorm G) := by
    rw [hA, ← ENNReal.ofReal_toReal hE.ne, ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ← Real.sqrt_eq_rpow]
    rfl
  have hB' : (∫⁻ z, ENNReal.ofReal (‖F z.1 z.2‖ * ‖ζ z.1 z.2‖) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal (Real.sqrt Q * ν) := by
    refine (ENNReal.rpow_le_rpow hB (by norm_num)).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul hQ, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← Real.sqrt_eq_rpow, Real.sqrt_mul hQ, Real.sqrt_sq hν]
  have hfin : ‖∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (G σ y (F σ y)) (ζ σ y)‖ₑ ≤
      ENNReal.ofReal (Real.sqrt Q * ν * gradientNorm G) := by
    refine h1.trans (hH.trans ?_)
    rw [hA']
    refine (mul_le_mul' le_rfl hB').trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul hgn]
    congr 1
    ring
  rw [Real.enorm_eq_ofReal_abs] at hfin
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hfin

theorem freeShift_of_combo {k : ℕ} {Γ : Set Symmetry} {P D C γ : ℝ} {v g ζ F : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {S : Finset (Fin k)} {f : Fin k → ℝ → Space → Space} {q ϱ δ : Fin k → ℝ} {ν μ : ℝ}
    (hv : IsPerturbation Γ P v G H g) (hζ : IsAdjointField ζ C γ)
    (hf : ∀ i ∈ S, IsFlowPiece (f i) D) (hϱ : ∀ i ∈ S, 0 < ϱ i) (hν : 0 ≤ ν) (hμ : 0 ≤ μ)
    (hval : periodLIntegral (fun σ y => (∑ i ∈ S, ϱ i * ‖f i σ y‖ ^ 2) * ‖ζ σ y‖ ^ 2) ≤
      ENNReal.ofReal (ν ^ 2))
    (hdual : ∀ i ∈ S, RemainderDualBound (fun σ y => transposeApply (fderiv ℝ (f i σ) y) (ζ σ y)) (δ i))
    (hsum : ∑ i ∈ S, ϱ i * δ i ^ 2 ≤ μ ^ 2)
    (hF : ∀ σ y, F σ y = ∑ i ∈ S, q i • f i σ y) :
    |periodInnerIntegral v (advectionShift F ζ)| ≤
      Real.sqrt (∑ i ∈ S, q i ^ 2 / ϱ i) * (ν + μ) * gradientNorm G := by
  classical
  have hQ0 : 0 ≤ ∑ i ∈ S, q i ^ 2 / ϱ i :=
    Finset.sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (hϱ i hi).le
  have hFp : IsFlowPiece F ((∑ i ∈ S, |q i|) * D) :=
    flowPiece_congr (flowPiece_sum S q f hf) fun σ y => (hF σ y).symm
  have hgn : 0 ≤ gradientNorm G := Real.sqrt_nonneg _
  have hR0 : 0 ≤ Real.sqrt (∑ i ∈ S, q i ^ 2 / ϱ i) * (ν + μ) * gradientNorm G := by positivity
  have hD := fun i hi => hdual i hi v G hv.measurable_velocity hv.measurable_gradient hv.weak_gradient
    hv.sixth_power hv.gradient_finite
  unfold periodInnerIntegral
  by_cases hI : IntegrableOn (fun σ => ∫ y, inner ℝ (v σ y) (advectionShift F ζ σ y)) (Set.Icc (0 : ℝ) 1)
  swap
  · rw [integral_undef hI, abs_zero]
    exact hR0
  have hC : 0 ≤ C := by
    have h := (hζ.decay 0 0).1
    simp at h
    exact (norm_nonneg _).trans h
  have hsplit : ∀ σ y, advectionShift F ζ σ y =
      ∑ i ∈ S, q i • transposeApply (fderiv ℝ (f i σ) y) (ζ σ y) - fderiv ℝ (ζ σ) y (F σ y) := by
    intro σ y
    have e : F σ = fun x => ∑ i ∈ S, q i • f i σ x := funext (hF σ)
    have e2 : fderiv ℝ (F σ) y = ∑ i ∈ S, q i • fderiv ℝ (f i σ) y := by
      rw [e]
      exact fderiv_combo hf q σ y
    unfold advectionShift
    rw [e2, transposeApply_sum]
  have hslice : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      (∫ y, inner ℝ (v σ y) (advectionShift F ζ σ y)) =
        ∑ i ∈ S, q i * (∫ y, inner ℝ (v σ y) (transposeApply (fderiv ℝ (f i σ) y) (ζ σ y)))
          - ∫ y, inner ℝ (v σ y) (fderiv ℝ (ζ σ) y (F σ y)) ∧
      (∫ y, inner ℝ (v σ y) (fderiv ℝ (ζ σ) y (F σ y))) = -∫ y, inner ℝ (G σ y (F σ y)) (ζ σ y) := by
    have hT : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ i ∈ S,
        Integrable (fun y => inner ℝ (v σ y) (transposeApply (fderiv ℝ (f i σ) y) (ζ σ y))) :=
      (Filter.eventually_all_finset S).2 fun i hi => (hD i hi).1
    filter_upwards [hT, ae_restrict_of_ae hv.weak_gradient, ae_restrict_of_ae hv.sixth_power,
      gradient_slice_finite hv] with σ h0 h1 h2 h3
    have hFs : ContDiff ℝ 1 (F σ) := hFp.smooth.comp (contDiff_const.prodMk contDiff_id)
    have hζs : ContDiff ℝ 1 (ζ σ) := hζ.smooth.comp (contDiff_const.prodMk contDiff_id)
    have hB := convection_slice_integrable h1 h2 hFs.continuous (fun y => (hFp.decay σ y).1) hζs
      hζ.rate_gt hC (fun y => (hζ.decay σ y).2.2)
    refine ⟨?_, ?_⟩
    · have e : (fun y => inner ℝ (v σ y) (advectionShift F ζ σ y)) = fun y =>
          ∑ i ∈ S, q i * inner ℝ (v σ y) (transposeApply (fderiv ℝ (f i σ) y) (ζ σ y))
            - inner ℝ (v σ y) (fderiv ℝ (ζ σ) y (F σ y)) := by
        funext y
        rw [hsplit σ y, inner_sub_right, inner_sum]
        simp only [inner_smul_right]
      have hsI : Integrable (fun y =>
          ∑ i ∈ S, q i * inner ℝ (v σ y) (transposeApply (fderiv ℝ (f i σ) y) (ζ σ y))) :=
        integrable_finsetSum S fun i hi => (h0 i hi).const_mul (q i)
      rw [e, integral_sub hsI hB, integral_finsetSum S fun i hi => (h0 i hi).const_mul (q i)]
      simp only [integral_const_mul]
    · rw [RepresentationParts.slice_convection_pairing h1 h2 h3 hFs (hFp.divergence_free σ)
        (fun y => (hFp.decay σ y).1) hζs hζ.rate_gt (fun y => ⟨(hζ.decay σ y).1, (hζ.decay σ y).2.2⟩),
        neg_neg]
  have hA : IntegrableOn (fun σ => ∑ i ∈ S, q i *
      ∫ y, inner ℝ (v σ y) (transposeApply (fderiv ℝ (f i σ) y) (ζ σ y))) (Set.Icc (0 : ℝ) 1) :=
    integrable_finsetSum S fun i hi => (hD i hi).2.1.const_mul (q i)
  have hb : IntegrableOn (fun σ => ∫ y, inner ℝ (v σ y) (fderiv ℝ (ζ σ) y (F σ y))) (Set.Icc (0 : ℝ) 1) := by
    refine (hA.sub hI).congr ?_
    filter_upwards [hslice] with σ h
    simp only [Pi.sub_apply]
    rw [h.1]
    ring
  rw [integral_congr_ae (hslice.mono fun σ h => h.1), integral_sub hA hb,
    integral_finsetSum S fun i hi => (hD i hi).2.1.const_mul (q i)]
  simp only [integral_const_mul]
  rw [integral_congr_ae (hslice.mono fun σ h => h.2), integral_neg, sub_neg_eq_add]
  have hw : Continuous (fun z : ℝ × Space => (∑ i ∈ S, ϱ i * ‖f i z.1 z.2‖ ^ 2) * ‖ζ z.1 z.2‖ ^ 2) :=
    (continuous_finsetSum S fun i hi => continuous_const.mul ((hf i hi).smooth.continuous.norm.pow 2)).mul
      (hζ.smooth.continuous.norm.pow 2)
  have hpt : ∀ σ y, ‖F σ y‖ ^ 2 * ‖ζ σ y‖ ^ 2 ≤
      (∑ i ∈ S, q i ^ 2 / ϱ i) * ((∑ i ∈ S, ϱ i * ‖f i σ y‖ ^ 2) * ‖ζ σ y‖ ^ 2) := by
    intro σ y
    have h1 : ‖F σ y‖ ≤ ∑ i ∈ S, |q i| * ‖f i σ y‖ := by
      rw [hF σ y]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp only [norm_smul, Real.norm_eq_abs]
    have h2 : ‖F σ y‖ ^ 2 ≤ (∑ i ∈ S, q i ^ 2 / ϱ i) * ∑ i ∈ S, ϱ i * ‖f i σ y‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (sum_abs_mul_sq_le S q ϱ _ hϱ)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have hc := pairing_bound hv hFp.smooth.continuous hζ.smooth.continuous hw hQ0 hν hpt hval
  have hqδ : ∑ i ∈ S, |q i| * δ i ≤ Real.sqrt (∑ i ∈ S, q i ^ 2 / ϱ i) * μ := by
    have h2 : (∑ i ∈ S, |q i| * δ i) ^ 2 ≤ (Real.sqrt (∑ i ∈ S, q i ^ 2 / ϱ i) * μ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hQ0]
      exact (sum_abs_mul_sq_le S q ϱ δ hϱ).trans (mul_le_mul_of_nonneg_left hsum hQ0)
    exact (le_abs_self _).trans ((sq_le_sq.1 h2).trans (le_of_eq (abs_of_nonneg (by positivity))))
  have hAi : ∀ i ∈ S, |∫ σ in Set.Icc (0 : ℝ) 1,
      ∫ y, inner ℝ (v σ y) (transposeApply (fderiv ℝ (f i σ) y) (ζ σ y))| ≤ δ i * gradientNorm G :=
    fun i hi => (hD i hi).2.2
  calc |∑ i ∈ S, q i * (∫ σ in Set.Icc (0 : ℝ) 1,
          ∫ y, inner ℝ (v σ y) (transposeApply (fderiv ℝ (f i σ) y) (ζ σ y)))
        + ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (G σ y (F σ y)) (ζ σ y)|
      ≤ |∑ i ∈ S, q i * (∫ σ in Set.Icc (0 : ℝ) 1,
          ∫ y, inner ℝ (v σ y) (transposeApply (fderiv ℝ (f i σ) y) (ζ σ y)))|
        + |∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (G σ y (F σ y)) (ζ σ y)| := abs_add_le _ _
    _ ≤ ∑ i ∈ S, |q i| * (δ i * gradientNorm G)
        + Real.sqrt (∑ i ∈ S, q i ^ 2 / ϱ i) * ν * gradientNorm G := by
        refine add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)) hc
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hAi i hi) (abs_nonneg _)
    _ = (∑ i ∈ S, |q i| * δ i) * gradientNorm G
        + Real.sqrt (∑ i ∈ S, q i ^ 2 / ϱ i) * ν * gradientNorm G := by
        rw [Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ Real.sqrt (∑ i ∈ S, q i ^ 2 / ϱ i) * μ * gradientNorm G
        + Real.sqrt (∑ i ∈ S, q i ^ 2 / ϱ i) * ν * gradientNorm G := by
        gcongr
    _ = Real.sqrt (∑ i ∈ S, q i ^ 2 / ϱ i) * (ν + μ) * gradientNorm G := by ring

end FreeShift

end Internal

theorem freeShiftBoundHolds_proof : FreeShiftBoundHolds := by
  intro k Γ P D C γ v g ζ G H S f q ϱ δ ν μ hv hζ hf hϱ _ hν hμ hval hdual hsum
  exact Internal.FreeShift.freeShift_of_combo hv hζ hf hϱ hν hμ hval hdual hsum fun _ _ => rfl

end AdjointDefect

end Breakdown
