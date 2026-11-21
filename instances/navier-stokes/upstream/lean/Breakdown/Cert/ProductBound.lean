import Breakdown.Cert.Nodes
import Breakdown.Cert.ReadingExists
import Breakdown.Cert.ProjectionSpec

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Breakdown.Cert

open Freq Internal.SliceFields Internal.ReadingExists

namespace Internal.ProductBound

theorem apply_eq_sum (L : Space →L[ℝ] Space) (v : Space) :
    L v = ∑ j : Fin 3, v j • L (unitVector j) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v]
  simp [map_sum, map_smul, EuclideanSpace.basisFun_apply, unitVector]

theorem ext_of_unit {L L' : Space →L[ℝ] Space} (h : ∀ i, L (unitVector i) = L' (unitVector i)) :
    L = L' := by
  ext1 v
  rw [apply_eq_sum L, apply_eq_sum L']
  simp only [h]

theorem norm_sum_smul_sq_le (a : Space) (c : Fin 3 → Space) :
    ‖∑ j : Fin 3, a j • c j‖ ^ 2 ≤ ‖a‖ ^ 2 * ∑ j : Fin 3, ‖c j‖ ^ 2 := by
  have h1 : ‖∑ j : Fin 3, a j • c j‖ ≤ ∑ j : Fin 3, |a j| * ‖c j‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [norm_smul, Real.norm_eq_abs]
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => |a j|) (fun j => ‖c j‖)
  have h3 : √(∑ j : Fin 3, |a j| ^ 2) = ‖a‖ := by
    simp [EuclideanSpace.norm_eq, sq_abs]
  rw [h3] at h2
  calc ‖∑ j : Fin 3, a j • c j‖ ^ 2 ≤ (‖a‖ * √(∑ j : Fin 3, ‖c j‖ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
    _ = ‖a‖ ^ 2 * ∑ j : Fin 3, ‖c j‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]

theorem lintegral_sum_sq (p : Fin 3 → L2R) :
    ∫⁻ y, ENNReal.ofReal (∑ j : Fin 3, ‖(p j : Space → Space) y‖ ^ 2) =
      ENNReal.ofReal (∑ j : Fin 3, ‖p j‖ ^ 2) := by
  have hint : Integrable (fun y => ∑ j : Fin 3, ‖(p j : Space → Space) y‖ ^ 2) volume :=
    integrable_finsetSum _ fun j _ => integrable_norm_sq_L2R _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _), integral_finsetSum _ fun j _ => integrable_norm_sq_L2R _]
  simp only [integral_norm_sq_L2R]

theorem lintegral_norm_sq_L2R (f : L2R) :
    ∫⁻ y, ENNReal.ofReal (‖(f : Space → Space) y‖ ^ 2) = ENNReal.ofReal (‖f‖ ^ 2) := by
  rw [← integral_norm_sq_L2R, ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_L2R f)
    (ae_of_all _ fun y => sq_nonneg _)]

theorem lintegral_sum_smul_le (a : Space → Space) (p : Fin 3 → L2R) {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ᵐ y, ‖a y‖ ^ 2 ≤ M) :
    ∫⁻ y, ENNReal.ofReal (‖∑ j : Fin 3, (a y) j • (p j : Space → Space) y‖ ^ 2) ≤
      ENNReal.ofReal M * ENNReal.ofReal (∑ j : Fin 3, ‖p j‖ ^ 2) := by
  rw [← lintegral_sum_sq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ha] with y hy
  rw [← ENNReal.ofReal_mul hM]
  refine ENNReal.ofReal_le_ofReal ((norm_sum_smul_sq_le _ _).trans ?_)
  exact mul_le_mul_of_nonneg_right hy (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem productSlice_apply (h h' : Freq.X) (y : Space) :
    productSlice h h' y =
      ∑ j : Fin 3, ((velocity h : Space → Space) y) j • (partialX j h' : Space → Space) y := rfl

theorem lintegral_productSlice_le (hs : SliceSupBoundHolds) (q q' : XBar) :
    ∫⁻ y, ENNReal.ofReal (‖productSlice (gradPart q) (gradPart q') y‖ ^ 2) ≤
      ENNReal.ofReal ((1 / (2 * Real.pi)) * ‖gradPart q‖ * ‖secondPart q‖) *
        ENNReal.ofReal (‖gradPart q'‖ ^ 2) := by
  simp only [productSlice_apply]
  have h := lintegral_sum_smul_le (velocity (gradPart q) : Space → Space)
    (fun j => partialX j (gradPart q')) (by positivity) (hs q)
  simp only [sum_norm_partialX_sq] at h
  exact h

theorem locallyIntegrable_apply {g : Space → (Space →L[ℝ] Space)} (hg : LocallyIntegrable g volume)
    (v : Space) : LocallyIntegrable (fun y => g y v) volume :=
  locallyIntegrable_iff.2 fun K hK =>
    Integrable.apply_continuousLinearMap (locallyIntegrable_iff.1 hg K hK) v

theorem weakGradient_unique {f : Space → Space} {g g' : Space → (Space →L[ℝ] Space)}
    (hg : IsWeakGradient f g) (hg' : IsWeakGradient f g') : g =ᵐ[volume] g' := by
  have hi : ∀ i : Fin 3, ∀ᵐ y, g y (unitVector i) = g' y (unitVector i) := fun i =>
    ae_eq_of_integral_contDiff_smul_eq (locallyIntegrable_apply hg.2.1 _)
      (locallyIntegrable_apply hg'.2.1 _) fun φ h1 h2 => by
        rw [hg.2.2 φ ⟨h1, h2⟩ i, hg'.2.2 φ ⟨h1, h2⟩ i]
  filter_upwards [ae_all_iff.2 hi] with y hy
  exact ext_of_unit hy

theorem ae_gradient_eq {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) : ∀ᵐ σ : ℝ, G σ =ᵐ[volume]
      gradField fun j => (partialX j (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) := by
  filter_upwards [hr.velocity_eq, hr.weak_gradient] with σ hv hw
  exact weakGradient_unique (isWeakGradient_congr hw hv EventuallyEq.rfl) (weakGradient_velocity _)

theorem lintegral_matSq_eq {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) :
    ∀ᵐ σ : ℝ, ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) =
      ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) := by
  filter_upwards [ae_gradient_eq hr] with σ hσ
  have e := lintegral_sum_sq (fun j => partialX j (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))))
  simp only [sum_norm_partialX_sq] at e
  rw [← e]
  refine lintegral_congr_ae ?_
  filter_upwards [hσ] with y hy
  simp only [matSq, hy, gradField_unit]

theorem lintegral_congr_neg {f : Space → Space} (g : L2R)
    (h : f =ᵐ[volume] fun y => -(g : Space → Space) y) :
    ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) = ENNReal.ofReal (‖g‖ ^ 2) := by
  rw [← lintegral_norm_sq_L2R]
  refine lintegral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy, norm_neg]

theorem aemeasurable_of_ae_neg {f : Space → Space} (g : L2R)
    (h : f =ᵐ[volume] fun y => -(g : Space → Space) y) :
    AEMeasurable (fun y => ENNReal.ofReal (‖f y‖ ^ 2)) volume := by
  refine (((Lp.aestronglyMeasurable g).norm.aemeasurable.pow_const 2).ennreal_ofReal).congr ?_
  filter_upwards [h] with y hy
  rw [hy, norm_neg]

theorem lintegral_trace_eq {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) :
    ∀ᵐ σ : ℝ, ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2) =
      ENNReal.ofReal (‖secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) := by
  filter_upwards [hr.trace_eq] with σ hσ
  exact (lintegral_congr_neg _ hσ).trans
    (congrArg (fun r : ℝ => ENNReal.ofReal (r ^ 2)) (norm_toPhysH _))

theorem apply_eq_productSlice {L : Space →L[ℝ] Space} {a : Space} {h h' : Freq.X} {y : Space}
    (hL : L = gradField (fun j => (partialX j h' : Space → Space)) y)
    (ha : a = (velocity h : Space → Space) y) : L a = productSlice h h' y := by
  rw [hL, ha, gradField_apply, productSlice_apply]

theorem lintegral_productField_le (hs : SliceSupBoundHolds) {u u' : XX} {v : VelField}
    {G : GradField} {H : SecondField} {v' : VelField} {G' : GradField} {H' : SecondField}
    (hr : IsReadingOf u v G H) (hr' : IsReadingOf u' v' G' H') :
    ∀ᵐ σ : ℝ, ∫⁻ y, ENNReal.ofReal (‖G' σ y (v σ y)‖ ^ 2) ≤
      ENNReal.ofReal ((1 / (2 * Real.pi)) * ‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ *
        ‖secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖) *
        ENNReal.ofReal (‖gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) := by
  filter_upwards [hr.velocity_eq, ae_gradient_eq hr'] with σ hv hG
  refine (lintegral_congr_ae ?_).trans_le (lintegral_productSlice_le hs _ _)
  filter_upwards [hv, hG] with y hy1 hy2
  exact congrArg (fun z : Space => ENNReal.ofReal (‖z‖ ^ 2)) (apply_eq_productSlice hy2 hy1)

theorem aemeasurable_sq (L : XBar →L[ℝ] Freq.X) (u : XX) :
    AEMeasurable (fun t : TimeCircle => ENNReal.ofReal (‖L ((u : TimeCircle → XBar) t)‖ ^ 2)) volume :=
  ((L.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).norm.aemeasurable.pow_const
    2).ennreal_ofReal

theorem lintegral_add_mul_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (c : ℝ) :
    ∫⁻ a, (f a + ENNReal.ofReal c * g a) ∂μ = ∫⁻ a, f a ∂μ + ENNReal.ofReal c * ∫⁻ a, g a ∂μ := by
  rw [lintegral_add_left' hf, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem lintegral_energy_slices (u : XX) (c : ℝ) :
    ∫⁻ σ in Icc (0 : ℝ) 1, (ENNReal.ofReal (‖secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) +
      ENNReal.ofReal c * ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2)) =
      ENNReal.ofReal (‖secondCLM u‖ ^ 2) + ENNReal.ofReal c * ENNReal.ofReal (‖gradCLM u‖ ^ 2) := by
  calc _ = ∫⁻ t, (ENNReal.ofReal (‖secondPart ((u : TimeCircle → XBar) t)‖ ^ 2) +
        ENNReal.ofReal c * ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2)) :=
      lintegral_Icc_coe (fun t => ENNReal.ofReal (‖secondPart ((u : TimeCircle → XBar) t)‖ ^ 2) +
        ENNReal.ofReal c * ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2))
        ((aemeasurable_sq secondPart u).add ((aemeasurable_sq gradPart u).const_mul _))
    _ = (∫⁻ t, ENNReal.ofReal (‖secondPart ((u : TimeCircle → XBar) t)‖ ^ 2)) +
        ENNReal.ofReal c * ∫⁻ t, ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2) :=
      lintegral_add_mul_eq (aemeasurable_sq secondPart u) c
    _ = _ := congrArg₂ (fun a b => a + ENNReal.ofReal c * b)
      (ofReal_norm_compLpL_sq secondPart u).symm (ofReal_norm_compLpL_sq gradPart u).symm

theorem matSq_nonneg (L : Space →L[ℝ] Space) : 0 ≤ matSq L :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem slice_energy_bounds {f F w : Space → ℝ} {w₀ C : ℝ} (hw0 : 0 ≤ w₀) (hC0 : 0 ≤ C)
    (hlow : ∀ y, w₀ ≤ w y) (hC : ∀ y, w y ≤ C) (hF : ∀ y, 0 ≤ F y)
    (hf : AEMeasurable (fun y => ENNReal.ofReal (f y ^ 2)) volume) {A B : ℝ≥0∞}
    (h1 : ∫⁻ y, ENNReal.ofReal (f y ^ 2) = A) (h2 : ∫⁻ y, ENNReal.ofReal (F y) = B) :
    A + ENNReal.ofReal w₀ * B ≤ ∫⁻ y, ENNReal.ofReal (f y ^ 2 + w y * F y) ∧
      ∫⁻ y, ENNReal.ofReal (f y ^ 2 + w y * F y) ≤ A + ENNReal.ofReal C * B := by
  rw [← h1, ← h2, ← lintegral_add_mul_eq hf, ← lintegral_add_mul_eq hf]
  constructor
  · refine lintegral_mono fun y => ?_
    rw [← ENNReal.ofReal_mul hw0, ← ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg hw0 (hF y))]
    exact ENNReal.ofReal_le_ofReal (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hlow y) (hF y)))
  · refine lintegral_mono fun y => ?_
    rw [← ENNReal.ofReal_mul hC0]
    refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (hC y) (hF y))

theorem le_toReal_of {a b w₀ : ℝ} {I : ℝ≥0∞} (hw0 : 0 ≤ w₀) (ha : 0 ≤ a) (hb : 0 ≤ b) (hI : I ≠ ⊤)
    (h : ENNReal.ofReal a + ENNReal.ofReal w₀ * ENNReal.ofReal b ≤ I) : a + w₀ * b ≤ I.toReal := by
  rw [← ENNReal.ofReal_mul hw0, ← ENNReal.ofReal_add ha (mul_nonneg hw0 hb)] at h
  exact (ENNReal.ofReal_le_iff_le_toReal hI).1 h

theorem energy_ge {w : Space → ℝ} {w₀ : ℝ} (hw : IsAdmissibleWeight w w₀) {u : XX} {v : VelField}
    {G : GradField} {H : SecondField} (hr : IsReadingOf u v G H)
    (he : weightedEnergy w G H = energyW w u) :
    ‖secondCLM u‖ ^ 2 + w₀ * ‖gradCLM u‖ ^ 2 ≤ energyW w u := by
  obtain ⟨hw0, -, hlow, C, hC⟩ := hw
  have hslice : ∀ᵐ σ : ℝ,
      ENNReal.ofReal (‖secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) +
        ENNReal.ofReal w₀ * ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) ≤
        ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y)) ∧
      ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y)) ≤
        ENNReal.ofReal (‖secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) +
        ENNReal.ofReal (max C 0) *
          ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) := by
    filter_upwards [lintegral_trace_eq hr, lintegral_matSq_eq hr, hr.trace_eq] with σ h1 h2 h3
    exact slice_energy_bounds hw0.le (le_max_right _ _) hlow (fun y => (hC y).trans (le_max_left _ _))
      (fun y => matSq_nonneg _) (aemeasurable_of_ae_neg _ h3) h1 h2
  have hlowI : ENNReal.ofReal (‖secondCLM u‖ ^ 2) + ENNReal.ofReal w₀ * ENNReal.ofReal (‖gradCLM u‖ ^ 2) ≤
      periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y)) :=
    (lintegral_energy_slices u w₀).symm.trans_le
      (lintegral_mono_ae (ae_restrict_of_ae (hslice.mono fun σ h => h.1)))
  have hupI : periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y)) ≤
      ENNReal.ofReal (‖secondCLM u‖ ^ 2) + ENNReal.ofReal (max C 0) * ENNReal.ofReal (‖gradCLM u‖ ^ 2) :=
    (lintegral_mono_ae (ae_restrict_of_ae (hslice.mono fun σ h => h.2))).trans_eq
      (lintegral_energy_slices u (max C 0))
  have hfin : periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩) hupI
  exact (le_toReal_of hw0.le (sq_nonneg _) (sq_nonneg _) hfin hlowI).trans_eq he

theorem ae_norm_le_supGrad {u : XX} (hu : supGrad u < ⊤) :
    ∀ᵐ t : TimeCircle, ‖gradPart ((u : TimeCircle → XBar) t)‖ ≤ (supGrad u).toReal := by
  filter_upwards [ae_le_eLpNormEssSup (μ := volume) (f := fun t => gradPart ((u : TimeCircle → XBar) t))] with t ht
  have h2 : ‖gradPart ((u : TimeCircle → XBar) t)‖ₑ ≤ supGrad u := ht.trans_eq eLpNorm_exponent_top.symm
  exact (toReal_enorm _).symm.trans_le (ENNReal.toReal_mono hu.ne h2)

theorem mul_le_energy {a b w₀ : ℝ} (hw : 0 < w₀) :
    a * b ≤ (b ^ 2 + w₀ * a ^ 2) / (2 * Real.sqrt w₀) := by
  have hs : 0 < Real.sqrt w₀ := Real.sqrt_pos.2 hw
  rw [le_div_iff₀ (by positivity)]
  have h2 : Real.sqrt w₀ ^ 2 = w₀ := Real.sq_sqrt hw.le
  nlinarith [sq_nonneg (Real.sqrt w₀ * a - b), h2]

theorem supBoundFactor_sq {w₀ : ℝ} : supBoundFactor w₀ ^ 2 = 1 / (2 * Real.pi * (2 * Real.sqrt w₀)) := by
  have hp : 0 ≤ 2 * Real.pi * (2 * Real.sqrt w₀) := by positivity
  rw [supBoundFactor, div_pow, one_pow, Real.sq_sqrt hp]

theorem supBoundFactor_nonneg (w₀ : ℝ) : 0 ≤ supBoundFactor w₀ := by
  unfold supBoundFactor
  positivity

theorem slice_real_le {a b c K w₀ : ℝ} (hw : 0 < w₀) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hcK : c ≤ K) :
    (1 / (2 * Real.pi)) * a * b * c ^ 2 ≤ supBoundFactor w₀ ^ 2 * K ^ 2 * (b ^ 2 + w₀ * a ^ 2) := by
  rw [supBoundFactor_sq]
  have h1 : a * b ≤ (b ^ 2 + w₀ * a ^ 2) / (2 * Real.sqrt w₀) := mul_le_energy hw
  have h2 : c ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hc hcK 2
  have hpi : 0 < 1 / (2 * Real.pi) := by positivity
  calc (1 / (2 * Real.pi)) * a * b * c ^ 2 = (1 / (2 * Real.pi)) * (a * b) * c ^ 2 := by ring
    _ ≤ (1 / (2 * Real.pi)) * ((b ^ 2 + w₀ * a ^ 2) / (2 * Real.sqrt w₀)) * K ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hpi.le) h2 (sq_nonneg _)
          (mul_nonneg hpi.le ((mul_nonneg ha hb).trans h1))
    _ = _ := by ring

theorem slice_ennreal_le {a b c K w₀ : ℝ} (hw : 0 < w₀) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hcK : c ≤ K) :
    ENNReal.ofReal ((1 / (2 * Real.pi)) * a * b) * ENNReal.ofReal (c ^ 2) ≤
      ENNReal.ofReal (supBoundFactor w₀ ^ 2 * K ^ 2) *
        (ENNReal.ofReal (b ^ 2) + ENNReal.ofReal w₀ * ENNReal.ofReal (a ^ 2)) := by
  have e1 : ENNReal.ofReal ((1 / (2 * Real.pi)) * a * b) * ENNReal.ofReal (c ^ 2) =
      ENNReal.ofReal ((1 / (2 * Real.pi)) * a * b * c ^ 2) := by
    exact (ENNReal.ofReal_mul (p := (1 / (2 * Real.pi)) * a * b) (q := c ^ 2) (by positivity)).symm
  have e2 : ENNReal.ofReal (supBoundFactor w₀ ^ 2 * K ^ 2) *
      (ENNReal.ofReal (b ^ 2) + ENNReal.ofReal w₀ * ENNReal.ofReal (a ^ 2)) =
      ENNReal.ofReal (supBoundFactor w₀ ^ 2 * K ^ 2 * (b ^ 2 + w₀ * a ^ 2)) := by
    rw [ENNReal.ofReal_mul (p := supBoundFactor w₀ ^ 2 * K ^ 2) (by positivity),
      ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg hw.le (sq_nonneg _)), ENNReal.ofReal_mul hw.le]
  rw [e1, e2]
  exact ENNReal.ofReal_le_ofReal (slice_real_le hw ha hb hc hcK)

theorem ofReal_combine {A S D w₀ : ℝ} (hA : 0 ≤ A) (hw0 : 0 ≤ w₀) :
    ENNReal.ofReal A * (ENNReal.ofReal (S ^ 2) + ENNReal.ofReal w₀ * ENNReal.ofReal (D ^ 2)) =
      ENNReal.ofReal (A * (S ^ 2 + w₀ * D ^ 2)) := by
  rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg hw0 (sq_nonneg _)),
    ENNReal.ofReal_mul hw0]

theorem final_real_le {A K S E : ℝ} (hE0 : 0 ≤ E) (he : S ≤ E) :
    A ^ 2 * K ^ 2 * S ≤ (A * Real.sqrt E * K) ^ 2 := by
  rw [mul_pow, mul_pow, Real.sq_sqrt hE0]
  have h0 : 0 ≤ A ^ 2 * K ^ 2 := by positivity
  exact (mul_le_mul_of_nonneg_left he h0).trans_eq (by ring)

theorem lintegral_Icc_le {w : Space → ℝ} {w₀ : ℝ} (hw : IsAdmissibleWeight w w₀) {u u' : XX}
    (he : ‖secondCLM u‖ ^ 2 + w₀ * ‖gradCLM u‖ ^ 2 ≤ energyW w u) (hu' : supGrad u' < ⊤)
    {F : ℝ → ℝ≥0∞}
    (hF : ∀ᵐ σ : ℝ, F σ ≤ ENNReal.ofReal ((1 / (2 * Real.pi)) *
        ‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ * ‖secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖) *
        ENNReal.ofReal (‖gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2)) :
    ∫⁻ σ in Icc (0 : ℝ) 1, F σ ≤
      ENNReal.ofReal ((supBoundFactor w₀ * Real.sqrt (energyW w u) * (supGrad u').toReal) ^ 2) := by
  have hw0 := hw.1
  have hsup := (ae_coe_iff _).1 (ae_norm_le_supGrad hu')
  have hS0 : 0 ≤ ‖secondCLM u‖ ^ 2 + w₀ * ‖gradCLM u‖ ^ 2 :=
    add_nonneg (sq_nonneg _) (mul_nonneg hw0.le (sq_nonneg _))
  have hE0 : 0 ≤ energyW w u := hS0.trans he
  calc ∫⁻ σ in Icc (0 : ℝ) 1, F σ ≤ ∫⁻ σ in Icc (0 : ℝ) 1,
        ENNReal.ofReal (supBoundFactor w₀ ^ 2 * (supGrad u').toReal ^ 2) *
          (ENNReal.ofReal (‖secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) +
            ENNReal.ofReal w₀ * ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2)) := by
        refine lintegral_mono_ae (ae_restrict_of_ae ?_)
        filter_upwards [hF, hsup] with σ h1 h2
        exact h1.trans (slice_ennreal_le hw0 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) h2)
    _ = ENNReal.ofReal (supBoundFactor w₀ ^ 2 * (supGrad u').toReal ^ 2) *
          (ENNReal.ofReal (‖secondCLM u‖ ^ 2) + ENNReal.ofReal w₀ * ENNReal.ofReal (‖gradCLM u‖ ^ 2)) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans
          (congrArg (fun x => ENNReal.ofReal (supBoundFactor w₀ ^ 2 * (supGrad u').toReal ^ 2) * x)
            (lintegral_energy_slices u w₀))
    _ = ENNReal.ofReal (supBoundFactor w₀ ^ 2 * (supGrad u').toReal ^ 2 *
          (‖secondCLM u‖ ^ 2 + w₀ * ‖gradCLM u‖ ^ 2)) :=
        ofReal_combine (by positivity) hw0.le
    _ ≤ _ := ENNReal.ofReal_le_ofReal
        (final_real_le hE0 he)

theorem ofReal_norm_toLp_sq {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    (f : α → E) (hf : MemLp f 2 μ) :
    ENNReal.ofReal (‖hf.toLp f‖ ^ 2) = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
  rw [Lp.norm_toLp, ← ENNReal.toReal_pow,
    ENNReal.ofReal_toReal (ENNReal.pow_ne_top hf.eLpNorm_ne_top),
    JointRepresentativeInternal.sq_eLpNorm_two]
  congr 1
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem ofReal_norm_toLpOrZero_sq_le (F : Space → Space) :
    ENNReal.ofReal (‖toLpOrZero 2 F‖ ^ 2) ≤ ∫⁻ y, ENNReal.ofReal (‖F y‖ ^ 2) := by
  unfold toLpOrZero
  split_ifs with h
  · exact (ofReal_norm_toLp_sq F h).le
  · simp

theorem ofReal_norm_solField_sq_le (F : Space → Space) :
    ENNReal.ofReal (‖solField F‖ ^ 2) ≤ ∫⁻ y, ENNReal.ofReal (‖F y‖ ^ 2) :=
  (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (norm_solProj_le _) 2)).trans
    (ofReal_norm_toLpOrZero_sq_le F)

theorem ofReal_norm_circleLpOrZero_sq_le {E : Type*} [NormedAddCommGroup E] (f : TimeCircle → E)
    {B : ℝ≥0∞}
    (h : MemLp f 2 volume → ∫⁻ σ in Icc (0 : ℝ) 1, ENNReal.ofReal (‖f (σ : TimeCircle)‖ ^ 2) ≤ B) :
    ENNReal.ofReal (‖circleLpOrZero f‖ ^ 2) ≤ B := by
  unfold circleLpOrZero
  split_ifs with hm
  · rw [ofReal_norm_toLp_sq _ hm,
      ← lintegral_Icc_coe _ (hm.1.norm.aemeasurable.pow_const 2).ennreal_ofReal]
    exact h hm
  · simp

theorem sqrt_toReal_le {I : ℝ≥0∞} {B : ℝ} (hB : 0 ≤ B) (h : I ≤ ENNReal.ofReal (B ^ 2)) :
    Real.sqrt I.toReal ≤ B :=
  (Real.sqrt_le_sqrt (ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) h)).trans_eq (Real.sqrt_sq hB)

theorem le_of_ofReal_sq_le {x B : ℝ} (hx : 0 ≤ x) (hB : 0 ≤ B)
    (h : ENNReal.ofReal (x ^ 2) ≤ ENNReal.ofReal (B ^ 2)) : x ≤ B :=
  (sq_le_sq₀ hx hB).1 ((ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 h)

theorem isReadingOf_readingOf (h2 : ReadingExistsHolds) (x : XX) :
    IsReadingOf x (readingOf x).1 (readingOf x).2.1 (readingOf x).2.2 := by
  have hx : ∃ r : VelField × GradField × SecondField, IsReadingOf x r.1 r.2.1 r.2.2 := by
    obtain ⟨v, G, H, h, -⟩ := h2 x
    exact ⟨(v, G, H), h⟩
  unfold readingOf
  rw [dif_pos hx]
  exact hx.choose_spec

end Internal.ProductBound

open Internal.ProductBound

theorem productBoundHolds_of (h1 : SliceSupBoundHolds) (h2 : ReadingExistsHolds)
    (h3 : ReadingEnergyHolds) : ProductBoundHolds := by
  intro w w₀ hw u u' hu'
  have hr := isReadingOf_readingOf h2
  have hE := energy_ge hw (hr u) (h3 w w₀ hw u _ _ _ (hr u)).1
  have hB0 : 0 ≤ supBoundFactor w₀ * Real.sqrt (energyW w u) * (supGrad u').toReal :=
    mul_nonneg (mul_nonneg (supBoundFactor_nonneg _) (Real.sqrt_nonneg _)) ENNReal.toReal_nonneg
  have hP : periodLIntegral (fun σ y => ‖productField u u' σ y‖ ^ 2) ≤
      ENNReal.ofReal ((supBoundFactor w₀ * Real.sqrt (energyW w u) * (supGrad u').toReal) ^ 2) :=
    lintegral_Icc_le hw hE hu' (lintegral_productField_le h1 (hr u) (hr u'))
  refine ⟨⟨?_, fun σ y => ?_, hP.trans_lt ENNReal.ofReal_lt_top⟩, sqrt_toReal_le hB0 hP, ?_⟩
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      ((hr u').measurable_gradient.prodMk (hr u).measurable_velocity)
  · exact congrArg₂ (fun (L : Space →L[ℝ] Space) (a : Space) => L a)
      ((hr u').periodic_gradient σ y) ((hr u).periodic_velocity σ y)
  · exact le_of_ofReal_sq_le (norm_nonneg _) hB0 (ofReal_norm_circleLpOrZero_sq_le _ fun _ =>
      lintegral_Icc_le hw hE hu' (ae_of_all _ fun σ =>
        (ofReal_norm_solField_sq_le _).trans (lintegral_productSlice_le h1 _ _)))

end Breakdown.Cert
