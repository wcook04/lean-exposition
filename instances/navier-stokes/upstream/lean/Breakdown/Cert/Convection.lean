import Breakdown.Cert.Nodes
import Breakdown.Cert.PeriodIntegral
import Breakdown.Cert.JointRepresentative
import Breakdown.Weak.VelocityWeakGradient
import Breakdown.Cert.SliceFields

open scoped ContDiff ENNReal NNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.Convection

structure IsCoefficient (W : ℝ → Space → Space) (D : ℝ) : Prop where
  smooth : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)
  periodic : IsTimePeriodic W
  bound_zero : ∀ σ y, ‖W σ y‖ ≤ D / (1 + ‖y‖)
  bound_one : ∀ σ y, ‖fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖) ^ 2

def weightCube : ℝ := (eLpNorm (fun y : Space => (1 + ‖y‖) ^ (-2 : ℝ)) 3 volume).toReal

def sliceConst (D : ℝ) : ℝ := D * (3 + weightCube * ‖(velocity : X →L[ℝ] L6R)‖)

def readingConvection (W : ℝ → Space → Space) (v : VelField) (G : GradField) :
    ℝ → Space → Space :=
  fun σ y => G σ y (W σ y) + fderiv ℝ (W σ) y (v σ y)

theorem isCoefficient_profile {k : ℕ} {d : CertificateData k} (hd : IsCertificate d)
    {p : Fin k → ℝ} (hp : p ∈ d.box) : IsCoefficient (d.profile p) d.decay := by
  refine ⟨?_, hd.profile_periodic p, fun σ y => ?_, fun σ y => ?_⟩
  · exact hd.profile_smooth.comp (contDiff_const.prodMk contDiff_id)
  · have h0 := hd.profile_decay p hp σ y 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero] at h0
    simpa using h0
  · have h1 := hd.profile_decay p hp σ y 1 (by norm_num)
    rw [norm_iteratedFDeriv_one] at h1
    simpa using h1

theorem apply_aesm {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : α → E →L[ℝ] F} {b : α → E} (hA : AEStronglyMeasurable A μ)
    (hb : AEStronglyMeasurable b μ) : AEStronglyMeasurable (fun x => A x (b x)) μ :=
  (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := F)).continuous.comp_aestronglyMeasurable
    (hA.prodMk hb)

theorem aesm_readingConvection {W : ℝ → Space → Space} {D : ℝ} (hW : IsCoefficient W D)
    {v : VelField} {G : GradField}
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : ℝ × Space => readingConvection W v G z.1 z.2) volume := by
  have hc : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.smooth.continuous
  have hd : Measurable (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
    measurable_fderiv_with_param ℝ (f := W) hc
  exact (apply_aesm hG hc.aestronglyMeasurable).add (apply_aesm hd.aestronglyMeasurable hv)

theorem exponentTriple_three_six : ENNReal.HolderTriple 3 6 2 := by
  constructor
  have h3 : (3 : ℝ≥0∞) = ((3 : ℝ≥0) : ℝ≥0∞) := rfl
  have h6 : (6 : ℝ≥0∞) = ((6 : ℝ≥0) : ℝ≥0∞) := rfl
  have h2 : (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞) := rfl
  rw [h3, h6, h2, ← ENNReal.coe_inv (by norm_num), ← ENNReal.coe_inv (by norm_num),
    ← ENNReal.coe_inv (by norm_num), ← ENNReal.coe_add]
  congr 1
  norm_num

theorem norm_partialX_le (j : Fin 3) (h : X) : ‖partialX j h‖ ≤ ‖h‖ := by
  have hs := Internal.SliceFields.sum_norm_partialX_sq h
  have h1 : ‖partialX j h‖ ^ 2 ≤ ‖h‖ ^ 2 := by
    rw [← hs]
    exact Finset.single_le_sum (f := fun i => ‖partialX i h‖ ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

theorem coefficient_nonneg {W : ℝ → Space → Space} {D : ℝ} (hW : IsCoefficient W D) : 0 ≤ D := by
  have h := hW.bound_zero 0 0
  simp only [norm_zero, add_zero, div_one] at h
  exact (norm_nonneg _).trans h

theorem slice_contDiff {W : ℝ → Space → Space} {D : ℝ} (hW : IsCoefficient W D) (σ : ℝ) :
    ContDiff ℝ 2 (W σ) :=
  hW.smooth.comp (contDiff_const.prodMk contDiff_id)

theorem weight_memLp : MemLp (fun y : Space => (1 + ‖y‖) ^ (-2 : ℝ)) 3 volume := by
  have hm : AEStronglyMeasurable (fun y : Space => (1 + ‖y‖) ^ (-2 : ℝ)) volume :=
    Measurable.aestronglyMeasurable (by fun_prop)
  refine (integrable_norm_rpow_iff hm (by norm_num) (by norm_num)).1 ?_
  have hi := integrable_one_add_norm (E := Space) (μ := volume) (r := 6) (by simp; norm_num)
  refine hi.congr (ae_of_all _ fun y => ?_)
  have hpos : 0 < 1 + ‖y‖ := by positivity
  simp only
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hpos _), ← Real.rpow_mul hpos.le]
  norm_num

theorem first_term {W : ℝ → Space → Space} {D : ℝ} (hW : IsCoefficient W D) (σ : ℝ) (h : X)
    (j : Fin 3) :
    MemLp (fun y => (W σ y) j • (partialX j h : Space → Space) y) 2 volume ∧
      eLpNorm (fun y => (W σ y) j • (partialX j h : Space → Space) y) 2 volume ≤
        ENNReal.ofReal (D * ‖h‖) := by
  have hD := coefficient_nonneg hW
  have hc : Continuous (W σ) := (slice_contDiff hW σ).continuous
  have hm : AEStronglyMeasurable (fun y => (W σ y) j • (partialX j h : Space → Space) y) volume :=
    ((EuclideanSpace.proj j).continuous.comp hc).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable _)
  have hb : ∀ᵐ y ∂volume, ‖(W σ y) j • (partialX j h : Space → Space) y‖ ≤
      D * ‖(partialX j h : Space → Space) y‖ := by
    refine ae_of_all _ fun y => ?_
    rw [norm_smul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ‖(W σ y) j‖ ≤ ‖W σ y‖ := PiLp.norm_apply_le _ _
      _ ≤ D / (1 + ‖y‖) := hW.bound_zero σ y
      _ ≤ D := div_le_self hD (by linarith [norm_nonneg y])
  refine ⟨(Lp.memLp _).of_le_mul hm hb, ?_⟩
  refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hb 2).trans ?_
  rw [← Lp.enorm_def, ← ofReal_norm, ← ENNReal.ofReal_mul hD]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (norm_partialX_le j h) hD)

theorem second_term {W : ℝ → Space → Space} {D : ℝ} (hW : IsCoefficient W D) (σ : ℝ) (h : X) :
    MemLp (fun y => fderiv ℝ (W σ) y ((velocity h : Space → Space) y)) 2 volume ∧
      eLpNorm (fun y => fderiv ℝ (W σ) y ((velocity h : Space → Space) y)) 2 volume ≤
        ENNReal.ofReal (D * weightCube * ‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) := by
  have hD := coefficient_nonneg hW
  have hcf : Continuous (fderiv ℝ (W σ)) := (slice_contDiff hW σ).continuous_fderiv (by norm_num)
  have hf : AEStronglyMeasurable (fderiv ℝ (W σ)) volume := hcf.aestronglyMeasurable
  have hg : AEStronglyMeasurable (velocity h : Space → Space) volume := Lp.aestronglyMeasurable _
  have hm : AEStronglyMeasurable (fun y => fderiv ℝ (W σ) y ((velocity h : Space → Space) y))
      volume :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable (hf.prodMk hg)
  have hH : eLpNorm (fun y => fderiv ℝ (W σ) y ((velocity h : Space → Space) y)) 2 volume ≤
      ((1 : ℝ≥0) : ℝ≥0∞) * eLpNorm (fderiv ℝ (W σ)) 3 volume *
        eLpNorm (velocity h : Space → Space) 6 volume := by
    have := exponentTriple_three_six
    exact eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hf hg (fun L x => L x) 1
      (ae_of_all _ fun y => by rw [one_mul]; exact ContinuousLinearMap.le_opNNNorm _ _)
  have hw : eLpNorm (fderiv ℝ (W σ)) 3 volume ≤
      ENNReal.ofReal D * eLpNorm (fun y : Space => (1 + ‖y‖) ^ (-2 : ℝ)) 3 volume := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (ae_of_all _ fun y => ?_) 3
    have hpos : 0 < 1 + ‖y‖ := by positivity
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hpos _), Real.rpow_neg hpos.le,
      Real.rpow_two, ← div_eq_mul_inv]
    exact hW.bound_one σ y
  have hwc : eLpNorm (fun y : Space => (1 + ‖y‖) ^ (-2 : ℝ)) 3 volume = ENNReal.ofReal weightCube :=
    (ENNReal.ofReal_toReal weight_memLp.eLpNorm_lt_top.ne).symm
  have hv : eLpNorm (velocity h : Space → Space) 6 volume ≤
      ENNReal.ofReal (‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) := by
    rw [← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (ContinuousLinearMap.le_opNorm _ _)
  have hwc0 : 0 ≤ weightCube := ENNReal.toReal_nonneg
  have hbound : eLpNorm (fun y => fderiv ℝ (W σ) y ((velocity h : Space → Space) y)) 2 volume ≤
      ENNReal.ofReal (D * weightCube * ‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) := by
    refine hH.trans ?_
    rw [ENNReal.coe_one, one_mul]
    calc eLpNorm (fderiv ℝ (W σ)) 3 volume * eLpNorm (velocity h : Space → Space) 6 volume
        ≤ (ENNReal.ofReal D * ENNReal.ofReal weightCube) *
            ENNReal.ofReal (‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) := by
          rw [← hwc]
          exact mul_le_mul' hw hv
      _ = ENNReal.ofReal (D * weightCube * ‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) := by
          rw [← ENNReal.ofReal_mul hD, ← ENNReal.ofReal_mul (mul_nonneg hD hwc0), mul_assoc _ ‖_‖]
  exact ⟨⟨hm, hbound.trans_lt ENNReal.ofReal_lt_top⟩, hbound⟩

theorem slice_bound {W : ℝ → Space → Space} {D : ℝ} (hW : IsCoefficient W D) (σ : ℝ) (h : X) :
    MemLp (sliceConvection (W σ) h) 2 volume ∧
      eLpNorm (sliceConvection (W σ) h) 2 volume ≤ ENNReal.ofReal (sliceConst D * ‖h‖) := by
  have hD := coefficient_nonneg hW
  set t : Fin 3 → Space → Space := fun j y => (W σ y) j • (partialX j h : Space → Space) y with ht
  have hsum : (fun y => ∑ j : Fin 3, t j y) = ∑ j : Fin 3, t j := by
    funext y
    simp [Finset.sum_apply]
  have heq : sliceConvection (W σ) h = (∑ j : Fin 3, t j) +
      fun y => fderiv ℝ (W σ) y ((velocity h : Space → Space) y) := by
    rw [← hsum]
    rfl
  have h1 : MemLp (∑ j : Fin 3, t j) 2 volume :=
    memLp_finsetSum' _ fun j _ => (first_term hW σ h j).1
  have h1b : eLpNorm (∑ j : Fin 3, t j) 2 volume ≤ ENNReal.ofReal (3 * (D * ‖h‖)) := by
    refine (eLpNorm_sum_le (fun j _ => (first_term hW σ h j).1.1) (by norm_num)).trans ?_
    calc ∑ j : Fin 3, eLpNorm (t j) 2 volume ≤ ∑ _j : Fin 3, ENNReal.ofReal (D * ‖h‖) :=
          Finset.sum_le_sum fun j _ => (first_term hW σ h j).2
      _ = ENNReal.ofReal (3 * (D * ‖h‖)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
          norm_num
  have h2 := second_term hW σ h
  rw [heq]
  refine ⟨h1.add h2.1, ?_⟩
  refine (eLpNorm_add_le h1.1 h2.1.1 (by norm_num)).trans ?_
  refine (add_le_add h1b h2.2).trans ?_
  have hwc0 : 0 ≤ weightCube := ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  unfold sliceConst
  ring

theorem eq_sum_unitVector (w : Space) : w = ∑ j : Fin 3, w j • unitVector j := by
  ext i
  simp [unitVector, Pi.single_apply]

theorem apply_eq_sum_unitVector (L : Space →L[ℝ] Space) (w : Space) :
    L w = ∑ j : Fin 3, w j • L (unitVector j) := by
  conv_lhs => rw [eq_sum_unitVector w]
  simp only [map_sum, map_smul]

theorem slice_pointwise (W : Space → Space) (h : X) (v : Space) (G : Space →L[ℝ] Space) (y : Space)
    (hv : v = (velocity h : Space → Space) y)
    (hG : ∀ j : Fin 3, G (unitVector j) = (partialX j h : Space → Space) y) :
    G (W y) + fderiv ℝ W y v = sliceConvection W h y := by
  unfold sliceConvection
  rw [hv, apply_eq_sum_unitVector G (W y)]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [hG j]

theorem locallyIntegrable_apply_unitVector {g : Space → (Space →L[ℝ] Space)}
    (hg : LocallyIntegrable g volume) (j : Fin 3) :
    LocallyIntegrable (fun y => g y (unitVector j)) volume := by
  rw [locallyIntegrable_iff] at hg ⊢
  intro K hK
  exact (ContinuousLinearMap.apply ℝ Space (unitVector j)).integrable_comp (hg K hK)

theorem partialX_ae_of_weakGradient {f : Space → Space} {g : Space → (Space →L[ℝ] Space)}
    (hg : IsWeakGradient f g) (h : X) (hf : f =ᵐ[volume] (velocity h : Space → Space)) (j : Fin 3) :
    (fun y => g y (unitVector j)) =ᵐ[volume] (partialX j h : Space → Space) := by
  have hl2 : LocallyIntegrable (partialX j h : Space → Space) volume :=
    (Lp.memLp (partialX j h)).locallyIntegrable (by norm_num)
  refine ae_eq_of_integral_contDiff_smul_eq (locallyIntegrable_apply_unitVector hg.2.1 j) hl2
    fun φ hφ hc => ?_
  rw [hg.2.2 φ ⟨hφ, hc⟩ j, WeakProfile.velocityWeakGradient_holds h φ ⟨hφ, hc⟩ j]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hf] with y hy
  rw [hy]

theorem readingConvection_slice {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) (W : ℝ → Space → Space) :
    ∀ᵐ σ : ℝ, readingConvection W v G σ =ᵐ[volume]
      sliceConvection (W σ) (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) := by
  filter_upwards [hr.velocity_eq, hr.weak_gradient] with σ h1 h2
  have hj : ∀ᵐ y, ∀ j : Fin 3, G σ y (unitVector j) =
      (partialX j (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) y :=
    ae_all_iff.2 fun j => partialX_ae_of_weakGradient h2 _ h1 j
  filter_upwards [h1, hj] with y hy1 hy2
  exact slice_pointwise (W σ) _ (v σ y) (G σ y) y hy1 hy2

theorem sliceConst_nonneg {W : ℝ → Space → Space} {D : ℝ} (hW : IsCoefficient W D) :
    0 ≤ sliceConst D := by
  have h0 := hW.bound_zero 0 0
  have hD : 0 ≤ D := by simpa using (norm_nonneg _).trans h0
  have hw : 0 ≤ weightCube := ENNReal.toReal_nonneg
  unfold sliceConst
  positivity

theorem ofReal_norm_sq_eq {E : Type*} [NormedAddCommGroup E] (x : E) :
    ENNReal.ofReal (‖x‖ ^ 2) = ‖x‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg x), ofReal_norm]

theorem ofReal_norm_sq_Lp {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    (f : Lp E 2 μ) : ENNReal.ofReal (‖f‖ ^ 2) = ∫⁻ a, ‖(f : α → E) a‖ₑ ^ 2 ∂μ := by
  rw [Lp.norm_def, ← ENNReal.toReal_pow,
    ENNReal.ofReal_toReal (ENNReal.pow_ne_top (Lp.eLpNorm_ne_top f)),
    JointRepresentativeInternal.sq_eLpNorm_two]

theorem ofReal_norm_sq_gradCLM (u : XX) :
    ENNReal.ofReal (‖gradCLM u‖ ^ 2) =
      ∫⁻ t, ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2) := by
  have ht : ((gradCLM u : HH) : TimeCircle → HBar) =ᵐ[volume]
      fun t => gradPart ((u : TimeCircle → XBar) t) :=
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) gradPart u
  refine (ofReal_norm_sq_Lp (gradCLM u)).trans (lintegral_congr_ae ?_)
  filter_upwards [ht] with t h
  exact (congrArg (fun x : HBar => ‖x‖ₑ ^ 2) h).trans
    (ofReal_norm_sq_eq (gradPart ((u : TimeCircle → XBar) t))).symm

theorem lintegral_slice_le {W : ℝ → Space → Space} {D : ℝ} (hW : IsCoefficient W D) (σ : ℝ)
    (h : X) (f : Space → Space) (hf : f =ᵐ[volume] sliceConvection (W σ) h) :
    ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) ≤
      ENNReal.ofReal (sliceConst D ^ 2) * ENNReal.ofReal (‖h‖ ^ 2) := by
  have hb := (slice_bound hW σ h).2
  have hM := sliceConst_nonneg hW
  calc ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) = ∫⁻ y, ‖sliceConvection (W σ) h y‖ₑ ^ 2 :=
        lintegral_congr_ae (hf.mono fun y hy =>
          (congrArg (fun x : Space => ENNReal.ofReal (‖x‖ ^ 2)) hy).trans (ofReal_norm_sq_eq _))
    _ = eLpNorm (sliceConvection (W σ) h) 2 volume ^ 2 :=
        (JointRepresentativeInternal.sq_eLpNorm_two _ _).symm
    _ ≤ ENNReal.ofReal (sliceConst D * ‖h‖) ^ 2 := by gcongr
    _ = ENNReal.ofReal (sliceConst D ^ 2) * ENNReal.ofReal (‖h‖ ^ 2) := by
        rw [← ENNReal.ofReal_pow (mul_nonneg hM (norm_nonneg h)), mul_pow,
          ENNReal.ofReal_mul (sq_nonneg (sliceConst D))]

theorem periodLIntegral_le {W : ℝ → Space → Space} {D : ℝ} (hW : IsCoefficient W D) (u : XX)
    (F : ℝ → Space → Space)
    (hF : ∀ᵐ σ : ℝ, F σ =ᵐ[volume]
      sliceConvection (W σ) (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)))) :
    periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) ≤ ENNReal.ofReal ((sliceConst D * ‖gradCLM u‖) ^ 2) := by
  have hmeas : AEMeasurable (fun t : TimeCircle =>
      ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2)) volume :=
    ((gradPart.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).norm.pow
      2).aemeasurable.ennreal_ofReal
  calc periodLIntegral (fun σ y => ‖F σ y‖ ^ 2)
      = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖F σ y‖ ^ 2) := rfl
    _ ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (sliceConst D ^ 2) *
        ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) :=
      lintegral_mono_ae (ae_restrict_of_ae (hF.mono fun σ hσ => lintegral_slice_le hW σ _ _ hσ))
    _ = ∫⁻ t, ENNReal.ofReal (sliceConst D ^ 2) *
        ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2) :=
      lintegral_Icc_coe (fun t => ENNReal.ofReal (sliceConst D ^ 2) *
        ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2)) (hmeas.const_mul _)
    _ = ENNReal.ofReal (sliceConst D ^ 2) * ENNReal.ofReal (‖gradCLM u‖ ^ 2) :=
      (lintegral_const_mul'' (ENNReal.ofReal (sliceConst D ^ 2)) hmeas).trans
        (congrArg (fun x => ENNReal.ofReal (sliceConst D ^ 2) * x) (ofReal_norm_sq_gradCLM u).symm)
    _ = ENNReal.ofReal ((sliceConst D * ‖gradCLM u‖) ^ 2) :=
      (ENNReal.ofReal_mul (sq_nonneg (sliceConst D))).symm.trans
        (congrArg ENNReal.ofReal (mul_pow (sliceConst D) ‖gradCLM u‖ 2).symm)

theorem coe_circleRep (t : TimeCircle) : ((circleRep t : ℝ) : TimeCircle) = t :=
  AddCircle.coe_equivIco

theorem eq_of_coe_eq {β : Type*} {f : ℝ → β} (hf : Function.Periodic f 1) {r σ : ℝ}
    (h : (r : TimeCircle) = σ) : f r = f σ := by
  have h0 : ((r - σ : ℝ) : TimeCircle) = 0 := by rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff 1).1 h0
  have hr : r = σ + n • (1 : ℝ) := by rw [hn]; ring
  rw [hr]
  exact hf.zsmul n σ

theorem ae_circle_of_ae {β : Type*} {f : ℝ → β} (hf : Function.Periodic f 1)
    {R : TimeCircle → β → Prop} (h : ∀ᵐ σ : ℝ, R (σ : TimeCircle) (f σ)) :
    ∀ᵐ t : TimeCircle, R t (f (circleRep t)) := by
  refine (ae_coe_iff (fun t => R t (f (circleRep t)))).2 ?_
  filter_upwards [h] with σ hσ
  rwa [eq_of_coe_eq hf (coe_circleRep (σ : TimeCircle))]

theorem periodic_of_isTimePeriodic {β : Type*} {f : ℝ → Space → β} (hf : IsTimePeriodic f) :
    Function.Periodic f 1 := fun σ => funext (hf σ)

theorem periodic_readingConvection {W : ℝ → Space → Space} {D : ℝ} (hW : IsCoefficient W D)
    {u : XX} {v : VelField} {G : GradField} {H : SecondField} (hr : IsReadingOf u v G H) :
    IsTimePeriodic (readingConvection W v G) := by
  intro σ y
  have hw : W (σ + 1) = W σ := funext (hW.periodic σ)
  simp only [readingConvection, hw, hr.periodic_gradient σ y, hr.periodic_velocity σ y]

theorem toLpOrZero_congr {f g : Space → Space} (h : f =ᵐ[volume] g) :
    toLpOrZero 2 f = toLpOrZero 2 g := by
  by_cases hf : MemLp f 2 volume
  · have hg : MemLp g 2 volume := hf.ae_eq h
    rw [toLpOrZero, toLpOrZero, dif_pos hf, dif_pos hg]
    exact MemLp.toLp_congr hf hg h
  · have hg : ¬ MemLp g 2 volume := fun hg => hf (hg.ae_eq h.symm)
    rw [toLpOrZero, toLpOrZero, dif_neg hf, dif_neg hg]

theorem toLpOrZero_of_ae {f : Space → Space} (g : L2R) (h : (g : Space → Space) =ᵐ[volume] f) :
    toLpOrZero 2 f = g := by
  have hm : MemLp f 2 volume := (Lp.memLp g).ae_eq h
  rw [toLpOrZero, dif_pos hm]
  exact Lp.ext (hm.coeFn_toLp.trans h.symm)

abbrev CurveSpace := Lp (α := TimeCircle) L2R 2

def IsSliceCurve (W : ℝ → Space → Space) (u : XX) (c : CurveSpace) : Prop :=
  ∀ᵐ t : TimeCircle, ((c t : L2R) : Space → Space) =ᵐ[volume]
    sliceConvection (W (circleRep t)) (gradPart ((u : TimeCircle → XBar) t))

theorem exists_sliceCurve (h1 : ReadingExistsHolds) {W : ℝ → Space → Space} {D : ℝ}
    (hW : IsCoefficient W D) (u : XX) :
    ∃ c, IsSliceCurve W u c ∧ ‖c‖ ≤ sliceConst D * ‖gradCLM u‖ := by
  have e := h1 u
  have hr : IsReadingOf u e.choose e.choose_spec.choose e.choose_spec.choose_spec.choose :=
    e.choose_spec.choose_spec.choose_spec.1
  have hs := readingConvection_slice hr W
  have hfin := periodLIntegral_le hW u _ hs
  have ec := exists_curve_of_joint (readingConvection W e.choose e.choose_spec.choose)
    (aesm_readingConvection hW hr.measurable_velocity hr.measurable_gradient)
    (periodic_readingConvection hW hr) (lt_of_le_of_lt hfin ENNReal.ofReal_lt_top)
  refine ⟨ec.choose, ?_, ?_⟩
  · have h' : ∀ᵐ σ : ℝ, ((ec.choose (σ : TimeCircle) : L2R) : Space → Space) =ᵐ[volume]
        sliceConvection (W σ) (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) := by
      filter_upwards [ec.choose_spec.1, hs] with σ ha hb using ha.trans hb
    exact ae_circle_of_ae (f := W) (periodic_of_isTimePeriodic hW.periodic)
      (R := fun t w => ((ec.choose t : L2R) : Space → Space) =ᵐ[volume]
        sliceConvection w (gradPart ((u : TimeCircle → XBar) t))) h'
  · have hM : 0 ≤ sliceConst D * ‖gradCLM u‖ :=
      mul_nonneg (sliceConst_nonneg hW) (norm_nonneg (gradCLM u))
    have hsq : ‖ec.choose‖ ^ 2 ≤ (sliceConst D * ‖gradCLM u‖) ^ 2 :=
      (le_of_eq ec.choose_spec.2).trans (ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) hfin)
    exact (pow_le_pow_iff_left₀ (norm_nonneg ec.choose) hM (by norm_num)).1 hsq

theorem sliceCurve_unique {W : ℝ → Space → Space} {u : XX} {c c' : CurveSpace}
    (hc : IsSliceCurve W u c) (hc' : IsSliceCurve W u c') : c = c' := by
  refine Lp.ext ?_
  filter_upwards [hc, hc'] with t ha hb
  exact Lp.ext (ha.trans hb.symm)

theorem sliceConvection_add (w : Space → Space) (h h' : X) :
    sliceConvection w (h + h') =ᵐ[volume] sliceConvection w h + sliceConvection w h' := by
  filter_upwards [Lp.coeFn_add (velocity h) (velocity h'),
    ae_all_iff.2 (fun j : Fin 3 => Lp.coeFn_add (partialX j h) (partialX j h'))] with y hv hp
  simp only [sliceConvection, map_add, hv, hp, Pi.add_apply, smul_add, Finset.sum_add_distrib]
  abel

theorem sliceConvection_smul (w : Space → Space) (a : ℝ) (h : X) :
    sliceConvection w (a • h) =ᵐ[volume] a • sliceConvection w h := by
  filter_upwards [Lp.coeFn_smul a (velocity h),
    ae_all_iff.2 (fun j : Fin 3 => Lp.coeFn_smul a (partialX j h))] with y hv hp
  simp only [sliceConvection, map_smul, hv, hp, Pi.smul_apply, smul_add, Finset.smul_sum]
  simp only [smul_comm a]

theorem isSliceCurve_add {W : ℝ → Space → Space} {u u' : XX} {c c' : CurveSpace}
    (hc : IsSliceCurve W u c) (hc' : IsSliceCurve W u' c') : IsSliceCurve W (u + u') (c + c') := by
  filter_upwards [hc, hc', Lp.coeFn_add c c', Lp.coeFn_add u u'] with t ha hb h3 h4
  have e3 : (c + c' : CurveSpace) t = c t + c' t := h3
  have e4 : gradPart (((u + u' : XX) : TimeCircle → XBar) t) =
      gradPart ((u : TimeCircle → XBar) t) + gradPart ((u' : TimeCircle → XBar) t) :=
    (congrArg gradPart h4).trans (map_add gradPart _ _)
  refine (EventuallyEq.of_eq (congrArg (fun x : L2R => (x : Space → Space)) e3)).trans ?_
  refine EventuallyEq.trans ?_ (EventuallyEq.of_eq
    (congrArg (fun g => sliceConvection (W (circleRep t)) g) e4.symm))
  exact (Lp.coeFn_add (c t) (c' t)).trans ((ha.add hb).trans (sliceConvection_add _ _ _).symm)

theorem isSliceCurve_smul {W : ℝ → Space → Space} {u : XX} {c : CurveSpace}
    (a : ℝ) (hc : IsSliceCurve W u c) : IsSliceCurve W (a • u) (a • c) := by
  filter_upwards [hc, Lp.coeFn_smul a c, Lp.coeFn_smul a u] with t ha h3 h4
  have e3 : (a • c : CurveSpace) t = a • c t := h3
  have e4 : gradPart (((a • u : XX) : TimeCircle → XBar) t) = a • gradPart ((u : TimeCircle → XBar) t) :=
    (congrArg gradPart h4).trans (map_smul gradPart _ _)
  refine (EventuallyEq.of_eq (congrArg (fun x : L2R => (x : Space → Space)) e3)).trans ?_
  refine EventuallyEq.trans ?_ (EventuallyEq.of_eq
    (congrArg (fun g => sliceConvection (W (circleRep t)) g) e4.symm))
  exact (Lp.coeFn_smul a (c t)).trans ((ha.const_smul a).trans (sliceConvection_smul _ _ _).symm)

theorem exists_sliceCurveCLM (h1 : ReadingExistsHolds) {W : ℝ → Space → Space} {D : ℝ}
    (hW : IsCoefficient W D) :
    ∃ T : XX →L[ℝ] CurveSpace, ∀ u,
      IsSliceCurve W u (T u) ∧ ‖T u‖ ≤ sliceConst D * ‖gradCLM u‖ := by
  choose c hc hb using exists_sliceCurve h1 hW
  let L : XX →ₗ[ℝ] CurveSpace :=
    { toFun := c
      map_add' := fun u u' => sliceCurve_unique (hc (u + u')) (isSliceCurve_add (hc u) (hc u'))
      map_smul' := fun a u => sliceCurve_unique (hc (a • u)) (isSliceCurve_smul a (hc u)) }
  refine ⟨L.mkContinuous (sliceConst D * ‖gradCLM‖) fun u => ?_, fun u => ⟨hc u, hb u⟩⟩
  calc ‖L u‖ ≤ sliceConst D * ‖gradCLM u‖ := hb u
    _ ≤ sliceConst D * (‖gradCLM‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left (gradCLM.le_opNorm u) (sliceConst_nonneg hW)
    _ = sliceConst D * ‖gradCLM‖ * ‖u‖ := by ring

theorem convectionSpec_of_curve {k : ℕ} {d : CertificateData k} {p : Fin k → ℝ}
    (T : XX →L[ℝ] CurveSpace) (hT : ∀ u, IsSliceCurve (d.profile p) u (T u)) :
    ConvectionSpec d p ((ContinuousLinearMap.compLpL 2 volume solProj).comp T) := by
  intro u
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) solProj (T u), hT u]
    with t ha hb
  exact ha.trans (congrArg solProj (toLpOrZero_of_ae ((T u : CurveSpace) t) hb).symm)

theorem convection_eq_of_spec {k : ℕ} {d : CertificateData k} {p : Fin k → ℝ}
    {T : XX →L[ℝ] HH} (hT : ConvectionSpec d p T) : convection d p = T := by
  have hex : ∃ T, ConvectionSpec d p T := ⟨T, hT⟩
  have hc : ConvectionSpec d p (convection d p) := by
    unfold convection
    rw [dif_pos hex]
    exact hex.choose_spec
  ext1 u
  exact Lp.ext ((hc u).trans (hT u).symm)

theorem physToHH_eq_convection {k : ℕ} {d : CertificateData k} {p : Fin k → ℝ} {D : ℝ}
    (hW : IsCoefficient (d.profile p) D) (hc : ConvectionSpec d p (convection d p)) {u : XX}
    {F : ℝ → Space → Space} (hper : IsTimePeriodic F)
    (hF : ∀ᵐ σ : ℝ, F σ =ᵐ[volume]
      sliceConvection (d.profile p σ) (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)))) :
    physToHH F = convection d p u := by
  have hpair : Function.Periodic (fun σ => (F σ, d.profile p σ)) 1 := fun σ =>
    Prod.ext (periodic_of_isTimePeriodic hper σ) (periodic_of_isTimePeriodic hW.periodic σ)
  have h1 : ∀ᵐ t : TimeCircle, F (circleRep t) =ᵐ[volume]
      sliceConvection (d.profile p (circleRep t)) (gradPart ((u : TimeCircle → XBar) t)) :=
    ae_circle_of_ae (f := fun σ => (F σ, d.profile p σ)) hpair
      (R := fun t q => q.1 =ᵐ[volume] sliceConvection q.2 (gradPart ((u : TimeCircle → XBar) t))) hF
  have h2 : (onCircle fun σ => solField (F σ)) =ᵐ[volume]
      ((convection d p u : HH) : TimeCircle → HBar) := by
    filter_upwards [h1, hc u] with t ht hct
    exact (congrArg solProj (toLpOrZero_congr ht)).trans hct.symm
  have hm : MemLp (onCircle fun σ => solField (F σ)) 2 volume := (Lp.memLp _).ae_eq h2.symm
  exact ((dif_pos hm).trans (Lp.ext (hm.coeFn_toLp.trans h2)) :
    circleLpOrZero (onCircle fun σ => solField (F σ)) = convection d p u)

end Internal.Convection

open Internal.Convection

theorem convectionHolds_of (h1 : ReadingExistsHolds) (_h2 : ProjectionHolds) (h3 : TestPairingHolds) :
    ConvectionHolds := by
  intro k d hd p hp
  have hW := isCoefficient_profile hd hp
  have eT := exists_sliceCurveCLM h1 hW
  have hspec := convectionSpec_of_curve (d := d) (p := p) eT.choose (fun u => (eT.choose_spec u).1)
  have hconv := convection_eq_of_spec hspec
  have hc : ConvectionSpec d p (convection d p) := fun u =>
    (EventuallyEq.of_eq (congrArg (fun L : XX →L[ℝ] HH => ((L u : HH) : TimeCircle → HBar)) hconv)).trans
      (hspec u)
  refine ⟨⟨_, hspec⟩, ⟨‖solProj‖ * sliceConst d.decay, fun u => ?_⟩, ?_⟩
  · calc ‖convection d p u‖ = ‖(ContinuousLinearMap.compLpL 2 volume solProj) (eT.choose u)‖ :=
          congrArg (‖·‖) (DFunLike.congr_fun hconv u)
      _ ≤ ‖ContinuousLinearMap.compLpL 2 volume solProj‖ * ‖eT.choose u‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖solProj‖ * (sliceConst d.decay * ‖gradCLM u‖) :=
        mul_le_mul (ContinuousLinearMap.norm_compLpL_le _) (eT.choose_spec u).2 (norm_nonneg _)
          (norm_nonneg _)
      _ = ‖solProj‖ * sliceConst d.decay * ‖gradCLM u‖ := by ring
  · intro u v G H hr φ hφ
    have hs := readingConvection_slice hr (d.profile p)
    have hF : IsPeriodicField (readingConvection (d.profile p) v G) :=
      ⟨aesm_readingConvection hW hr.measurable_velocity hr.measurable_gradient,
        periodic_readingConvection hW hr,
        lt_of_le_of_lt (periodLIntegral_le hW u _ hs) ENNReal.ofReal_lt_top⟩
    have hphys := physToHH_eq_convection hW hc (periodic_readingConvection hW hr) hs
    exact ((congrArg (fun x => inner ℝ x (testInHH φ)) hphys).symm.trans (h3 _ hF φ hφ)).symm

end Breakdown.Cert
