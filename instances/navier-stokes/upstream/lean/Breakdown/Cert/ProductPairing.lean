import Breakdown.Cert.Nodes
import Breakdown.Cert.ReadingExists
import Breakdown.Cert.PeriodIntegral

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Breakdown.Cert

open Freq Internal.SliceFields Internal.ReadingExists

namespace Internal.ProductPairing

theorem apply_eq_sum (L : Space →L[ℝ] Space) (v : Space) :
    L v = ∑ j : Fin 3, v j • L (unitVector j) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v]
  simp [map_sum, map_smul, EuclideanSpace.basisFun_apply, unitVector]

theorem ext_of_unit {L L' : Space →L[ℝ] Space} (h : ∀ i, L (unitVector i) = L' (unitVector i)) :
    L = L' := by
  ext1 v
  rw [apply_eq_sum L, apply_eq_sum L']
  simp only [h]

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

theorem isReadingOf_readingOf (h : ReadingExistsHolds) (x : XX) :
    IsReadingOf x (readingOf x).1 (readingOf x).2.1 (readingOf x).2.2 := by
  have hx : ∃ r : VelField × GradField × SecondField, IsReadingOf x r.1 r.2.1 r.2.2 := by
    obtain ⟨v, G, H, hr, -⟩ := h x
    exact ⟨(v, G, H), hr⟩
  unfold readingOf
  rw [dif_pos hx]
  exact hx.choose_spec

theorem productSlice_apply (h h' : Freq.X) (y : Space) :
    productSlice h h' y =
      ∑ j : Fin 3, ((velocity h : Space → Space) y) j • (partialX j h' : Space → Space) y := rfl

theorem ae_apply_eq {u u' : XX} {v : VelField} {G : GradField} {H : SecondField}
    {v' : VelField} {G' : GradField} {H' : SecondField}
    (hr : IsReadingOf u v G H) (hr' : IsReadingOf u' v' G' H') :
    ∀ᵐ σ : ℝ, (fun y => G' σ y (v σ y)) =ᵐ[volume]
      productSlice (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)))
        (gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))) := by
  filter_upwards [hr.velocity_eq, hr'.velocity_eq, hr'.weak_gradient] with σ hv hv' hw
  have hG := weakGradient_unique (isWeakGradient_congr hw hv' EventuallyEq.rfl)
    (weakGradient_velocity (gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))))
  filter_upwards [hv, hG] with y hy1 hy2
  simp only [hy1, hy2, gradField_apply, productSlice_apply]

theorem ae_productField_eq (h : ReadingExistsHolds) (u u' : XX) :
    ∀ᵐ σ : ℝ, productField u u' σ =ᵐ[volume]
      productSlice (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)))
        (gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))) := by
  unfold productField
  exact ae_apply_eq (isReadingOf_readingOf h u) (isReadingOf_readingOf h u')

theorem circleRep_coe (x : ℝ) : circleRep (x : TimeCircle) = Int.fract x := by
  have e := AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) x
  rw [div_one, mul_one] at e
  exact e

theorem periodic_circleRep {β : Type*} {F : ℝ → Space → β} (hF : IsTimePeriodic F) (σ : ℝ) :
    F (circleRep (σ : TimeCircle)) = F σ := by
  have hp : Function.Periodic F 1 := fun s => funext (hF s)
  rw [circleRep_coe, Int.fract, ← mul_one ((⌊σ⌋ : ℤ) : ℝ)]
  exact hp.sub_int_mul_eq ⌊σ⌋

theorem solField_congr {F G : Space → Space} (h : F =ᵐ[volume] G) : solField F = solField G := by
  by_cases hF : MemLp F 2 volume
  · have hG : MemLp G 2 volume := hF.ae_eq h
    simp only [solField, toLpOrZero, dif_pos hF, dif_pos hG]
    rw [MemLp.toLp_congr hF hG h]
  · have hG : ¬ MemLp G 2 volume := fun hG => hF (hG.ae_eq h.symm)
    simp only [solField, toLpOrZero, dif_neg hF, dif_neg hG]

theorem circleLpOrZero_congr {g g' : TimeCircle → HBar} (h : g =ᵐ[volume] g') :
    circleLpOrZero g = circleLpOrZero g' := by
  by_cases hg : MemLp g 2 volume
  · have hg' : MemLp g' 2 volume := hg.ae_eq h
    simp only [circleLpOrZero, dif_pos hg, dif_pos hg']
    exact MemLp.toLp_congr hg hg' h
  · have hg' : ¬ MemLp g' 2 volume := fun hg' => hg (hg'.ae_eq h.symm)
    simp only [circleLpOrZero, dif_neg hg, dif_neg hg']

theorem productH_eq_physToHH (h : ReadingExistsHolds) {u u' : XX}
    (hper : IsTimePeriodic (productField u u')) :
    productH u u' = physToHH (productField u u') := by
  unfold productH physToHH
  refine circleLpOrZero_congr ?_
  refine (ae_coe_iff (fun t => solField (productSlice (gradPart ((u : TimeCircle → XBar) t))
    (gradPart ((u' : TimeCircle → XBar) t))) = onCircle (fun σ => solField (productField u u' σ)) t)).2 ?_
  filter_upwards [ae_productField_eq h u u'] with σ hσ
  exact (solField_congr hσ.symm).trans (congrArg solField (periodic_circleRep hper σ).symm)

end Internal.ProductPairing

open Internal.ProductPairing

theorem productPairingHolds_of (h1 : ProductBoundHolds) (_h2 : ProjectionHolds)
    (h3 : TestPairingHolds) (h4 : ReadingExistsHolds) : ProductPairingHolds := by
  intro u u' hu' φ hφ
  have hw : IsAdmissibleWeight (fun _ => (1 : ℝ)) 1 :=
    ⟨one_pos, measurable_const, fun _ => le_rfl, 1, fun _ => le_rfl⟩
  have hP := (h1 _ _ hw u u' hu').1
  rw [productH_eq_physToHH h4 hP.2.1]
  exact h3 _ hP φ hφ

end Breakdown.Cert
