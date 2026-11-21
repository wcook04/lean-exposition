import Breakdown.Cert.Nodes
import Breakdown.Cert.JointRepresentative
import Breakdown.Cert.SliceFields
import Breakdown.Cert.PeriodIntegral
import Breakdown.Cert.HalfOrderGraphMem

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Breakdown.Cert

open Freq Internal.SliceFields

namespace Internal.ReadingExists

theorem isWeakGradient_congr {f f' : Space → Space} {G G' : Space → (Space →L[ℝ] Space)}
    (h : IsWeakGradient f G) (hf : f =ᵐ[volume] f') (hG : G =ᵐ[volume] G') :
    IsWeakGradient f' G' := by
  unfold IsWeakGradient at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.congr hf, h2.congr hG, fun φ hφ i => ?_⟩
  have e1 : ∫ y, φ y • G' y (unitVector i) = ∫ y, φ y • G y (unitVector i) :=
    integral_congr_ae (hG.mono fun y hy => by simp only [hy])
  have e2 : ∫ y, fderiv ℝ φ y (unitVector i) • f' y = ∫ y, fderiv ℝ φ y (unitVector i) • f y :=
    integral_congr_ae (hf.mono fun y hy => by simp only [hy])
  rw [e1, e2]
  exact h3 φ hφ i

theorem gradField_ae {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p q : Fin 3 → Space → F} (h : ∀ j, p j =ᵐ[volume] q j) :
    gradField p =ᵐ[volume] gradField q := by
  filter_upwards [ae_all_iff.2 h] with y hy
  simp only [gradField, hy]

theorem aestronglyMeasurable_gradField {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure (ℝ × Space)} {p : Fin 3 → ℝ → Space → F}
    (hp : ∀ j, AEStronglyMeasurable (fun z : ℝ × Space => p j z.1 z.2) μ) :
    AEStronglyMeasurable (fun z : ℝ × Space => gradField (fun j => p j z.1) z.2) μ := by
  have h : (fun z : ℝ × Space => gradField (fun j => p j z.1) z.2) = fun z =>
      ∑ j : Fin 3, ContinuousLinearMap.smulRightL ℝ Space F (EuclideanSpace.proj j : Space →L[ℝ] ℝ) (p j z.1 z.2) := by
    funext z
    simp [gradField]
  rw [h]
  exact Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
    (ContinuousLinearMap.smulRightL ℝ Space F (EuclideanSpace.proj j : Space →L[ℝ] ℝ)).continuous.comp_aestronglyMeasurable (hp j)

theorem weakGradient_velocity (x : X) :
    IsWeakGradient (velocity x : Space → Space) (gradField fun j => (partialX j x : Space → Space)) :=
  ⟨(Lp.memLp (velocity x)).locallyIntegrable (by norm_num),
    (memLp_gradField fun j => Lp.memLp (partialX j x)).locallyIntegrable (by norm_num),
    fun φ hφ i => by
      simp only [gradField_unit]
      exact WeakProfile.velocityWeakGradient_holds x φ hφ i⟩

theorem weakGradient_partial (x k : X) (h : IsHalfSspOf x k) (j : Fin 3) :
    IsWeakGradient (partialX j x : Space → Space)
      (gradField fun i => (partialX i (derivX j k) : Space → Space)) :=
  ⟨(Lp.memLp (partialX j x)).locallyIntegrable (by norm_num),
    (memLp_gradField fun i => Lp.memLp (partialX i (derivX j k))).locallyIntegrable (by norm_num),
    fun φ hφ i => by
      simp only [gradField_unit]
      rw [WeakProfile.velocityWeakGradient_holds (derivX j k) φ hφ i]
      congr 1
      apply integral_congr_ae
      filter_upwards [velocityInverts_holds _ _ (halfSsp_derivX j h)] with y hy
      rw [hy, partialX_eq]⟩

theorem slice_reading (x k : X) (hxk : IsHalfSspOf x k) (v' : Space → Space)
    (g' : Fin 3 → Space → Space) (h' : Fin 3 → Fin 3 → Space → Space)
    (hv : v' =ᵐ[volume] (velocity x : Space → Space))
    (hg : ∀ j, g' j =ᵐ[volume] (partialX j x : Space → Space))
    (hh : ∀ i j, h' i j =ᵐ[volume] (partialX i (derivX j k) : Space → Space)) :
    IsWeakGradient v' (gradField g') ∧
      (∀ j : Fin 3, IsWeakGradient (fun y => gradField g' y (unitVector j))
        (fun y => (secondDerivField h' y).flip (unitVector j))) ∧
      (fun y => secondDerivTrace (secondDerivField h' y)) =ᵐ[volume]
        (fun y => -(toPhys (k : L2C) : Space → Space) y) ∧
      ∫⁻ y, ENNReal.ofReal (‖secondDerivField h' y‖ ^ 2) ≤ ENNReal.ofReal (‖k‖ ^ 2) := by
  refine ⟨isWeakGradient_congr (weakGradient_velocity x) hv.symm (gradField_ae hg).symm,
    fun j => ?_, ?_, ?_⟩
  · refine isWeakGradient_congr (weakGradient_partial x k hxk j) ?_ ?_
    · filter_upwards [hg j] with y hy
      rw [gradField_unit, hy]
    · filter_upwards [gradField_ae fun i => hh i j] with y hy
      rw [flip_secondDerivField, hy]
  · filter_upwards [ae_all_iff.2 fun j => hh j j,
      Lp.coeFn_finsetSum Finset.univ (fun j : Fin 3 => partialX j (derivX j k)),
      Lp.coeFn_neg (toPhys (k : L2C))] with y hy h1 h2
    calc secondDerivTrace (secondDerivField h' y) = ∑ j : Fin 3, h' j j y := secondDerivTrace_secondDerivField h' y
      _ = ∑ j : Fin 3, (partialX j (derivX j k) : Space → Space) y :=
          Finset.sum_congr rfl fun j _ => hy j
      _ = ((∑ j : Fin 3, partialX j (derivX j k) : L2R) : Space → Space) y := by
          rw [h1, Finset.sum_apply]
      _ = ((-toPhys (k : L2C) : L2R) : Space → Space) y := by rw [sum_partialX_derivX]
      _ = -(toPhys (k : L2C) : Space → Space) y := by rw [h2, Pi.neg_apply]
  · have hnn : ∀ y, ENNReal.ofReal (‖secondDerivField h' y‖ ^ 2) ≤
        ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3, ‖h' i j y‖ ^ 2) := fun y =>
      ENNReal.ofReal_le_ofReal (by simpa only [secondDerivField_unit] using norm_secondDerivField_sq_le h' y)
    have hint : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3,
        ‖(partialX i (derivX j k) : Space → Space) y‖ ^ 2) volume :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => integrable_norm_sq_L2R _
    have hval : ∫ y, ∑ i : Fin 3, ∑ j : Fin 3, ‖(partialX i (derivX j k) : Space → Space) y‖ ^ 2 =
        ‖k‖ ^ 2 := by
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => integrable_norm_sq_L2R _]
      rw [Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => integrable_norm_sq_L2R _]
      simp only [integral_norm_sq_L2R]
      rw [Finset.sum_comm]
      simp only [sum_norm_partialX_sq]
      exact sum_norm_derivX_sq k
    have hae : (fun y => ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3, ‖h' i j y‖ ^ 2)) =ᵐ[volume]
        fun y => ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3,
          ‖(partialX i (derivX j k) : Space → Space) y‖ ^ 2) := by
      filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j => hh i j] with y hy
      simp only [hy]
    calc ∫⁻ y, ENNReal.ofReal (‖secondDerivField h' y‖ ^ 2)
        ≤ ∫⁻ y, ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3, ‖h' i j y‖ ^ 2) := lintegral_mono hnn
      _ = ∫⁻ y, ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3,
            ‖(partialX i (derivX j k) : Space → Space) y‖ ^ 2) := lintegral_congr_ae hae
      _ = ENNReal.ofReal (∫ y, ∑ i : Fin 3, ∑ j : Fin 3,
            ‖(partialX i (derivX j k) : Space → Space) y‖ ^ 2) :=
          (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y =>
            Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
      _ = ENNReal.ofReal (‖k‖ ^ 2) := by rw [hval]

theorem ae_slice {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)] (L : E →L[ℝ] Lp (α := Space) F p)
    (u : Lp (α := TimeCircle) E 2) (f : ℝ → Space → F)
    (hf : ∀ᵐ σ : ℝ, ((ContinuousLinearMap.compLpL 2 volume L u (σ : TimeCircle) :
      Lp (α := Space) F p) : Space → F) =ᵐ[volume] f σ) :
    ∀ᵐ σ : ℝ, f σ =ᵐ[volume] (L (u (σ : TimeCircle)) : Space → F) := by
  have h1 := (ae_coe_iff (fun t => ContinuousLinearMap.compLpL 2 volume L u t = L (u t))).1
    (ContinuousLinearMap.coeFn_compLpL L u)
  filter_upwards [h1, hf] with σ h1 h2
  rw [h1] at h2
  exact h2.symm

theorem ofReal_norm_sq_eq {E : Type*} [NormedAddCommGroup E] (f : Lp (α := TimeCircle) E 2) :
    ENNReal.ofReal (‖f‖ ^ 2) = ∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) := by
  rw [Lp.norm_def, ← ENNReal.toReal_pow,
    ENNReal.ofReal_toReal (ENNReal.pow_ne_top (Lp.eLpNorm_ne_top f)),
    JointRepresentativeInternal.sq_eLpNorm_two]
  congr 1
  funext t
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem ofReal_norm_compLpL_sq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (u : Lp (α := TimeCircle) E 2) :
    ENNReal.ofReal (‖ContinuousLinearMap.compLpL 2 volume L u‖ ^ 2) =
      ∫⁻ t, ENNReal.ofReal (‖L (u t)‖ ^ 2) := by
  rw [ofReal_norm_sq_eq]
  refine lintegral_congr_ae ((ContinuousLinearMap.coeFn_compLpL L u).mono fun t ht => ?_)
  simp only [ht]

theorem exists_slice_representative {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (L : E →L[ℝ] Lp (α := Space) F p) (u : Lp (α := TimeCircle) E 2) :
    ∃ f : ℝ → Space → F, AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume ∧
      IsTimePeriodic f ∧ ∀ᵐ σ : ℝ, f σ =ᵐ[volume] (L (u (σ : TimeCircle)) : Space → F) := by
  have hc := exists_joint_representative (ContinuousLinearMap.compLpL 2 volume L u)
  obtain ⟨f, hm, hp, ha⟩ := hc
  exact ⟨f, hm, hp, ae_slice L u f ha⟩

end Internal.ReadingExists

open Internal.ReadingExists

theorem exists_reading (u : XX) : ∃ v G H, IsReadingOf u v G H ∧
    periodLIntegral (fun σ y => ‖H σ y‖ ^ 2) ≤ ENNReal.ofReal (‖secondCLM u‖ ^ 2) := by
  have hv := exists_slice_representative (velocity ∘L gradPart) u
  obtain ⟨v, hvm, hvp, eA⟩ := hv
  have hg := fun j : Fin 3 => exists_slice_representative (partialX j ∘L gradPart) u
  choose g hgm hgp eB using hg
  have hh := fun i j : Fin 3 => exists_slice_representative (partialX i ∘L derivX j ∘L secondPart) u
  choose h hhm hhp eC using hh
  have eB' := ae_all_iff.2 eB
  have eC' := ae_all_iff.2 fun i => ae_all_iff.2 (eC i)
  have hmeas : AEMeasurable (fun t : TimeCircle => ENNReal.ofReal (‖secondPart (u t)‖ ^ 2)) volume :=
    ((secondPart.continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable u)).norm.aemeasurable.pow_const 2).ennreal_ofReal
  refine ⟨v, fun σ y => gradField (fun j => g j σ) y, fun σ y => secondDerivField (fun i j => h i j σ) y,
    ⟨hvm, aestronglyMeasurable_gradField hgm,
      aestronglyMeasurable_gradField (p := fun i σ y => gradField (fun j => h i j σ) y)
        fun i => aestronglyMeasurable_gradField fun j => hhm i j,
      hvp, fun σ y => ?_, fun σ y => ?_, eA, ?_, ?_, ?_⟩, ?_⟩
  · show gradField (fun j => g j (σ + 1)) y = gradField (fun j => g j σ) y
    congr 1
    funext j y'
    exact hgp j σ y'
  · show secondDerivField (fun i j => h i j (σ + 1)) y = secondDerivField (fun i j => h i j σ) y
    congr 1
    funext i j y'
    exact hhp i j σ y'
  · filter_upwards [eA, eB', eC'] with σ hA hB hC
    exact (slice_reading (gradPart (u σ)) (secondPart (u σ)) (halfSsp_of_xbar (u σ)) _ _ _
      hA hB hC).1
  · filter_upwards [eA, eB', eC'] with σ hA hB hC
    exact (slice_reading (gradPart (u σ)) (secondPart (u σ)) (halfSsp_of_xbar (u σ)) _ _ _
      hA hB hC).2.1
  · filter_upwards [eA, eB', eC'] with σ hA hB hC
    exact (slice_reading (gradPart (u σ)) (secondPart (u σ)) (halfSsp_of_xbar (u σ)) _ _ _
      hA hB hC).2.2.1
  · unfold periodLIntegral
    calc ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖secondDerivField (fun i j => h i j σ) y‖ ^ 2)
        ≤ ∫⁻ σ in Icc (0 : ℝ) 1, ENNReal.ofReal (‖secondPart (u (σ : TimeCircle))‖ ^ 2) := by
          refine lintegral_mono_ae (ae_restrict_of_ae ?_)
          filter_upwards [eA, eB', eC'] with σ hA hB hC
          exact (slice_reading (gradPart (u σ)) (secondPart (u σ)) (halfSsp_of_xbar (u σ)) _ _ _
            hA hB hC).2.2.2
      _ = ∫⁻ t, ENNReal.ofReal (‖secondPart (u t)‖ ^ 2) := lintegral_Icc_coe _ hmeas
      _ = ENNReal.ofReal (‖secondCLM u‖ ^ 2) := (ofReal_norm_compLpL_sq secondPart u).symm

theorem readingExistsHolds_proof : ReadingExistsHolds := fun u => exists_reading u

end Breakdown.Cert
