import Breakdown.Cert.ExtendedNodes
import Breakdown.Cert.BorderedInvertible

open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ExtendedBorderedInvertible

open Internal.BorderedInvertible

theorem eq_zero_of_bordered_eq_zero (h2 : ExtendedCoerciveBorderedHolds) {k : ℕ}
    (d : ExtendedCertificateData k) (hd : IsNormalExtendedCertificate d) (q : Fin k → ℝ)
    (hq : q ∈ d.params) (x : HH × (Fin k → ℝ)) (hx : x.1 ∈ invariantHH d.symmetries)
    (h : bordered d.toCertificateData q x = 0) : x = 0 := by
  have hb1 : x.1 + convection d.toCertificateData q (freeInv (d.period q) x.1)
      + actuatorH d.toCertificateData x.2 = 0 := congrArg Prod.fst h
  have hb2 : pinMap d.toCertificateData (freeInv (d.period q) x.1) = 0 := congrArg Prod.snd h
  have hfst : (bordered d.toCertificateData q (x.1, x.2)).1 = 0 := congrArg Prod.fst h
  have hc := h2 d hd q hq x.1 hx x.2 (fun _ _ => 0)
    ⟨aestronglyMeasurable_const, fun _ _ => rfl, by simp [periodLIntegral]⟩
    (fun φ _ => (by simp : ∫ z : ℝ × Space,
        inner ℝ ((fun _ _ => (0 : Space)) z.1 z.2 : Space) (φ z.1 z.2) = 0).trans
      ((congrArg (fun v : HH => inner ℝ v (testInHH φ)) hfst).trans (inner_zero_left _)).symm)
  have hv : vecNorm (pinMap d.toCertificateData (freeInv (d.period q) x.1)) = 0 := by
    simp only [hb2, vecNorm, Pi.zero_apply]
    simp
  have hr : d.rows (fun _ _ => (0 : Space)) = 0 := by
    simp [ExtendedCertificateData.rows, rowNorm, periodPairing]
  have h0 : sizeZ d.weightFn (freeInv (d.period q) x.1) x.2 ≤ 0 := by
    refine hc.trans (le_of_eq ?_)
    rw [hv, hr]
    simp [periodNorm, periodLIntegral]
  have hE : 0 ≤ ∫ t, sliceWeightedGrad d.weightFn
      (gradPart (((freeInv (d.period q) x.1 : XX) : TimeCircle → XBar) t)) := by
    refine integral_nonneg fun t => ?_
    unfold sliceWeightedGrad
    exact integral_nonneg fun y => mul_nonneg
      (le_trans hd.certificate.weight_pos.le (hd.certificate.weightFn_lower y))
      (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hsum : 0 ≤ ∑ i, x.2 i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hx0 : energyW d.weightFn (freeInv (d.period q) x.1) + ∑ i, x.2 i ^ 2 ≤ 0 :=
    Real.sqrt_eq_zero'.1 (le_antisymm h0 (Real.sqrt_nonneg _))
  unfold energyW at hx0
  have hsq := sq_nonneg ‖secondCLM (freeInv (d.period q) x.1)‖
  have hs : ‖secondCLM (freeInv (d.period q) x.1)‖ ^ 2 = 0 := le_antisymm (by linarith) hsq
  have hκs : ∑ i, x.2 i ^ 2 = 0 := le_antisymm (by linarith) hsum
  have hκ : x.2 = 0 := funext fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x.2 i))).1 hκs i
      (Finset.mem_univ _)
    simpa using this
  have hu : freeInv (d.period q) x.1 = 0 :=
    eq_zero_of_secondCLM_eq_zero _ (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hs))
  have hc0 : convection d.toCertificateData q (freeInv (d.period q) x.1) = 0 :=
    (congrArg (convection d.toCertificateData q) hu).trans
      (map_zero (convection d.toCertificateData q))
  have ha0 : actuatorH d.toCertificateData x.2 = 0 :=
    (congrArg (actuatorH d.toCertificateData) hκ).trans (map_zero (actuatorH d.toCertificateData))
  have hb3 : x.1 + convection d.toCertificateData q (freeInv (d.period q) x.1)
      + actuatorH d.toCertificateData x.2 = x.1 :=
    (congrArg₂ (fun a b => x.1 + a + b) hc0 ha0).trans ((add_zero _).trans (add_zero _))
  exact Prod.ext (hb3.symm.trans hb1) hκ

theorem exists_borderedInvSpec (h1 : ExtendedConvectionCompactHolds)
    (h3 : ExtendedInvarianceHolds) (h4 : FreeEquivariantHolds) {k : ℕ}
    (d : ExtendedCertificateData k) (hd : IsExtendedCertificate d) (q : Fin k → ℝ)
    (hq : q ∈ d.params)
    (hinj : ∀ x : HH × (Fin k → ℝ), x.1 ∈ invariantHH d.symmetries →
      bordered d.toCertificateData q x = 0 → x = 0)
    (Pr : HH →L[ℝ] HH) (hP1 : ∀ x, Pr x ∈ invariantHH d.symmetries)
    (hP2 : ∀ x ∈ invariantHH d.symmetries, Pr x = x) :
    ∃ T, BorderedInvSpec d.toCertificateData q T :=
  exists_inverse_of_compact_bordered (invariantHH d.symmetries) (bordered d.toCertificateData q)
    ((ContinuousLinearMap.inl ℝ HH (Fin k → ℝ)).comp
        (((convection d.toCertificateData q).comp (freeInv (d.period q))).comp
          (Pr.comp (ContinuousLinearMap.fst ℝ HH (Fin k → ℝ)))))
    (((actuatorH d.toCertificateData).comp
        (ContinuousLinearMap.fst ℝ (Fin k → ℝ) (Fin k → ℝ))).prod
        (ContinuousLinearMap.snd ℝ (Fin k → ℝ) (Fin k → ℝ)))
    ((ContinuousLinearMap.snd ℝ HH (Fin k → ℝ)).prod
        ((pinMap d.toCertificateData).comp ((freeInv (d.period q)).comp
          (Pr.comp (ContinuousLinearMap.fst ℝ HH (Fin k → ℝ))))
          - ContinuousLinearMap.snd ℝ HH (Fin k → ℝ)))
    (((h1 d hd q hq).comp_clm (Pr.comp (ContinuousLinearMap.fst ℝ HH (Fin k → ℝ)))).clm_comp
      (ContinuousLinearMap.inl ℝ HH (Fin k → ℝ)))
    (fun g => convection d.toCertificateData q (freeInv (d.period q) g))
    (actuatorH d.toCertificateData)
    (fun g => pinMap d.toCertificateData (freeInv (d.period q) g)) Pr
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun g hg => ((h3 d hd q hq).1 _ (h4 d.symmetries (d.period q) (hd.period_pos q hq) g hg)).1)
    (h3 d hd q hq).2.1 hP1 hP2 hinj

end Internal.ExtendedBorderedInvertible

open Internal.ExtendedBorderedInvertible

theorem extendedBorderedInvertibleHolds_of (h1 : ExtendedConvectionCompactHolds)
    (h2 : ExtendedCoerciveBorderedHolds) (h3 : ExtendedInvarianceHolds)
    (h4 : FreeEquivariantHolds) : ExtendedBorderedInvertibleHolds := by
  intro k d hd q hq
  have hinj : ∀ x : HH × (Fin k → ℝ), x.1 ∈ invariantHH d.symmetries →
      bordered d.toCertificateData q x = 0 → x = 0 :=
    eq_zero_of_bordered_eq_zero h2 d hd q hq
  have hP := exists_projection_invariantHH d.symmetries
  exact ⟨exists_borderedInvSpec h1 h3 h4 d hd.certificate q hq hinj hP.choose hP.choose_spec.1
      hP.choose_spec.2,
    fun x y hx hy hxy =>
    sub_eq_zero.1 (hinj (x - y) (Submodule.sub_mem _ hx hy)
      ((map_sub _ x y).trans (sub_eq_zero.2 hxy)))⟩

end Breakdown.Cert
