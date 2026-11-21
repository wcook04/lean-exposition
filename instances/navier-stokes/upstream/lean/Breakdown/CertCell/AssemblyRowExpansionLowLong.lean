import Breakdown.CertCell.AssemblyRowParts
import Breakdown.CertCell.AssemblyRowExpansionLowAlgebra
import Breakdown.Cert.CoerciveSmoothPieceEpsBounds
import Breakdown.Cert.CoercivePairingSplit

open scoped ENNReal NNReal
open MeasureTheory Set Matrix

noncomputable section

namespace Breakdown.CertCell.Assembly

open Breakdown Breakdown.CertCell CellCalculus CellCert CellCert.CellAnalysis CellCert.CellFormula

namespace Internal.RowIdentity

theorem continuous_crossTest_triple (j : Fin 12) :
    Continuous (fun x : (Fin 3 → ℂ) × (Fin 3 → ℂ) × (Fin 3 → ℂ) => crossTest x.1 x.2.1 x.2.2 j) := by
  unfold crossTest pairVec
  split_ifs
  · refine Complex.continuous_conj.comp ?_
    refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
    refine continuous_finsetSum _ fun j' _ => continuous_finsetSum _ fun l' _ => ?_
    exact (continuous_const.mul ((continuous_apply j').comp continuous_fst)).mul
      (Complex.continuous_conj.comp ((continuous_apply l').comp (continuous_snd.comp continuous_snd)))
  · refine Complex.continuous_conj.comp ?_
    refine continuous_finsetSum _ fun j' _ => continuous_finsetSum _ fun l' _ => ?_
    exact (continuous_const.mul (Complex.continuous_conj.comp
      ((continuous_apply j').comp (continuous_snd.comp continuous_snd)))).mul
      ((continuous_apply l').comp (continuous_fst.comp continuous_snd))

theorem pair_integrableOn_ae {K : CellBox} (hK : IsCellBox K) {σ : ℝ × ℝ → Fin 12 → ℂ}
    (hσ : ∀ j, RectSquare K (fun p => σ p j)) {W Ω φ : ℝ × ℝ → Fin 3 → ℂ}
    (hW : ∀ a, AEStronglyMeasurable (fun p => W p a) (volume.restrict K.rect))
    (hΩ : ∀ a, AEStronglyMeasurable (fun p => Ω p a) (volume.restrict K.rect))
    (hφ : ∀ a, Continuous fun p => φ p a) {C : ℝ}
    (hb : ∀ᵐ p ∂(volume.restrict K.rect), ∀ a, ‖W p a‖ ≤ C ∧ ‖Ω p a‖ ≤ C) :
    IntegrableOn (fun p => (p.1 : ℂ) * ∑ j, σ p j * (starRingEnd ℂ) (crossTest (W p) (Ω p) (φ p) j)) K.rect := by
  choose Mφ hMφ using fun a => (rect_regular_of_eqOn (K := K) (f := fun p => φ p a) (hφ a) fun _ _ => rfl).2
  have hR0 : 0 ≤ |C| + ∑ a, |Mφ a| := add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun a _ => abs_nonneg _)
  have hC : |C| ≤ |C| + ∑ a, |Mφ a| := le_add_of_nonneg_right (Finset.sum_nonneg fun a _ => abs_nonneg _)
  have hMa : ∀ a, |Mφ a| ≤ |C| + ∑ a, |Mφ a| := fun a =>
    (Finset.single_le_sum (f := fun a => |Mφ a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)).trans
      (le_add_of_nonneg_left (abs_nonneg _))
  have hbox : ∀ᵐ p ∂(volume.restrict K.rect), ((W p, Ω p, φ p) : (Fin 3 → ℂ) × (Fin 3 → ℂ) × (Fin 3 → ℂ))
      ∈ Metric.closedBall 0 (|C| + ∑ a, |Mφ a|) := by
    filter_upwards [hb, ae_restrict_mem (CellCalculus.Internal.RowForm.rect_meas K)] with p hp hpr
    rw [mem_closedBall_zero_iff]
    refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
    · exact (pi_norm_le_iff_of_nonneg hR0).2 fun a => ((hp a).1.trans (le_abs_self C)).trans hC
    · exact (pi_norm_le_iff_of_nonneg hR0).2 fun a => ((hp a).2.trans (le_abs_self C)).trans hC
    · exact (pi_norm_le_iff_of_nonneg hR0).2 fun a => ((hMφ a p hpr).trans (le_abs_self _)).trans (hMa a)
  have e : (fun p => (p.1 : ℂ) * ∑ j, σ p j * (starRingEnd ℂ) (crossTest (W p) (Ω p) (φ p) j))
      = fun p => ∑ j, (p.1 : ℂ) * σ p j * (starRingEnd ℂ) (crossTest (W p) (Ω p) (φ p) j) := by
    funext p
    simp only [Finset.mul_sum, mul_assoc]
  rw [e]
  have hm3 : AEStronglyMeasurable (fun p => ((W p, Ω p, φ p) : (Fin 3 → ℂ) × (Fin 3 → ℂ) × (Fin 3 → ℂ)))
      (volume.restrict K.rect) :=
    (aemeasurable_pi_iff.2 fun a => (hW a).aemeasurable).aestronglyMeasurable.prodMk
      ((aemeasurable_pi_iff.2 fun a => (hΩ a).aemeasurable).aestronglyMeasurable.prodMk
        (aemeasurable_pi_iff.2 fun a => (hφ a).aestronglyMeasurable.aemeasurable).aestronglyMeasurable)
  refine integrable_finsetSum _ fun j _ => ?_
  obtain ⟨MF, hMF⟩ := (isCompact_closedBall (0 : (Fin 3 → ℂ) × (Fin 3 → ℂ) × (Fin 3 → ℂ))
    (|C| + ∑ a, |Mφ a|)).exists_bound_of_continuousOn (continuous_crossTest_triple j).continuousOn
  have ht : AEStronglyMeasurable (fun p => (starRingEnd ℂ) (crossTest (W p) (Ω p) (φ p) j)) (volume.restrict K.rect) := by
    have h := (Complex.continuous_conj.comp (continuous_crossTest_triple j)).comp_aestronglyMeasurable hm3
    simpa only [Function.comp_def] using h
  have hI1 : IntegrableOn (fun p => (p.1 : ℂ) * σ p j * 1) K.rect :=
    rectSquare_pairing hK (hσ j) aestronglyMeasurable_const (M := 1) fun _ _ => by simp
  have hp1 : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 : ℂ)) (volume.restrict K.rect) :=
    (Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun p => (p.1 : ℂ) * σ p j * (starRingEnd ℂ) (crossTest (W p) (Ω p) (φ p) j))
      (volume.restrict K.rect) := (hp1.mul (hσ j).1).mul ht
  have hdom : Integrable (fun p => MF * ‖(p.1 : ℂ) * σ p j * 1‖) (volume.restrict K.rect) := hI1.norm.const_mul MF
  refine Integrable.mono' hdom hm ?_
  filter_upwards [hbox] with p hp
  have h1 := hMF _ hp
  simp only at h1
  calc ‖(p.1 : ℂ) * σ p j * (starRingEnd ℂ) (crossTest (W p) (Ω p) (φ p) j)‖
      = ‖(p.1 : ℂ) * σ p j‖ * ‖crossTest (W p) (Ω p) (φ p) j‖ := by rw [norm_mul, Complex.norm_conj]
    _ ≤ ‖(p.1 : ℂ) * σ p j‖ * MF := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = MF * ‖(p.1 : ℂ) * σ p j * 1‖ := by rw [mul_one, mul_comm]

theorem aestronglyMeasurable_off_axis {X : ℝ → Space → Space}
    (hX : ContinuousOn (fun z : ℝ × Space => X z.1 z.2)
      {z | 0 < CellCert.CellAnalysis.cylRadius z.2 ∧ CellCert.CellAnalysis.cylHeight z.2 ≠ 0}) :
    AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume := by
  have hc : ∀ i : Fin 3, Continuous (fun z : ℝ × Space => z.2 i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp continuous_snd
  have hr : Continuous (fun z : ℝ × Space => CellCert.CellAnalysis.cylRadius z.2) := by
    unfold CellCert.CellAnalysis.cylRadius
    exact (((hc 0).pow 2).add ((hc 1).pow 2)).sqrt
  have hh : Continuous (fun z : ℝ × Space => CellCert.CellAnalysis.cylHeight z.2) := by
    unfold CellCert.CellAnalysis.cylHeight
    exact hc 2
  have hU : MeasurableSet {z : ℝ × Space | 0 < CellCert.CellAnalysis.cylRadius z.2 ∧
      CellCert.CellAnalysis.cylHeight z.2 ≠ 0} :=
    ((isOpen_lt continuous_const hr).inter (isOpen_ne_fun hh continuous_const)).measurableSet
  have hnull : ∀ i : Fin 3, (volume : Measure (ℝ × Space)) {z | z.2 i = 0} = 0 := by
    intro i
    have e : {z : ℝ × Space | z.2 i = 0} = Set.univ ×ˢ {y : Space | y i = 0} := by
      ext z
      simp
    have e2 : {y : Space | y i = 0}
        = ((LinearMap.ker (EuclideanSpace.proj i : Space →L[ℝ] ℝ).toLinearMap : Submodule ℝ Space) : Set Space) := by
      ext y
      simp
    have hs : (volume : Measure Space) {y : Space | y i = 0} = 0 := by
      rw [e2]
      refine Measure.addHaar_submodule _ _ fun htop => ?_
      have h1 : EuclideanSpace.single i (1 : ℝ)
          ∈ LinearMap.ker (EuclideanSpace.proj i : Space →L[ℝ] ℝ).toLinearMap := by
        rw [htop]
        exact Submodule.mem_top
      simp at h1
    rw [e, Measure.volume_eq_prod, Measure.prod_prod, hs, mul_zero]
  have hae : ∀ᵐ z ∂(volume : Measure (ℝ × Space)), z ∈ {z : ℝ × Space | 0 < CellCert.CellAnalysis.cylRadius z.2 ∧
      CellCert.CellAnalysis.cylHeight z.2 ≠ 0} := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) (measure_union_null (hnull 0) (hnull 2))
    simp only [Set.mem_ofPred_eq, not_and_or, not_lt, not_not] at hz
    rcases hz with h | h
    · left
      show z.2 0 = 0
      unfold CellCert.CellAnalysis.cylRadius at h
      have h2 : z.2 0 ^ 2 + z.2 1 ^ 2 ≤ 0 := Real.sqrt_eq_zero'.1 (le_antisymm h (Real.sqrt_nonneg _))
      have h3 : z.2 0 ^ 2 = 0 := by nlinarith [sq_nonneg (z.2 0), sq_nonneg (z.2 1)]
      exact pow_eq_zero_iff two_ne_zero |>.1 h3
    · right
      exact h
  have h := hX.aestronglyMeasurable (μ := volume) hU
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at h

theorem norm_labelVel_le_orbit {X : ℝ → Space → Space} {C : ℝ} {p : ℝ × ℝ}
    (hC : ∀ σ φ, ‖X σ (axialRot φ (planePoint p))‖ ≤ C) (m : ℕ) (ι : ℤ × ℤ) (a : Fin 3) :
    ‖labelVel m ι X p a‖ ≤ C := by
  unfold labelVel modeVel
  refine Coercive.Internal.SmoothPieceEps.norm_modeAverage_le _ _ a fun τ φ => ?_
  have h1 : |axialRot (-φ) (X (0 + τ) (axialRot φ (planePoint p))) a|
      ≤ ‖axialRot (-φ) (X (0 + τ) (axialRot φ (planePoint p)))‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (axialRot (-φ) (X (0 + τ) (axialRot φ (planePoint p)))) a
  rw [Coercive.PairingSplitInternal.norm_axialRot] at h1
  exact h1.trans (hC _ _)

end Internal.RowIdentity

end Breakdown.CertCell.Assembly
