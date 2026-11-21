import Breakdown.Cert.Nodes
import Breakdown.Cert.CompactPerturbation
import Breakdown.Cert.HalfOrderGraphMem

open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

theorem isClosed_invariantHH (Γ : Set Symmetry) : IsClosed (invariantHH Γ : Set HH) := by
  simp only [invariantHH, Submodule.coe_iInf]
  exact isClosed_iInter fun γ => isClosed_iInter fun _ => ContinuousLinearMap.isClosed_ker _

theorem completeSpace_invariantHH (Γ : Set Symmetry) : CompleteSpace (invariantHH Γ) :=
  (isClosed_invariantHH Γ).completeSpace_coe

theorem exists_projection_invariantHH (Γ : Set Symmetry) :
    ∃ Pr : HH →L[ℝ] HH, (∀ x, Pr x ∈ invariantHH Γ) ∧ ∀ x ∈ invariantHH Γ, Pr x = x := by
  have := completeSpace_invariantHH Γ
  exact ⟨_, Submodule.starProjection_apply_mem _, fun x hx =>
    Submodule.starProjection_eq_self_iff.2 hx⟩

namespace Internal.BorderedInvertible

theorem eq_zero_of_secondPart_eq_zero (q : XBar) (hq : secondPart q = 0) : q = 0 := by
  have hl := halfSsp_of_xbar q
  have hnull : ∀ᵐ ξ : Space ∂volume, ξ ≠ 0 := by
    rw [ae_iff]
    simp
  have hg : gradPart q = 0 := by
    apply Subtype.ext
    apply Lp.ext
    rw [hq] at hl
    filter_upwards [hl, hnull, Lp.coeFn_zero (E := CSpace) (p := 2) (μ := (volume : Measure Space))]
      with ξ h1 h2 h3
    have h1' : (2 * Real.pi * ‖ξ‖) • ((gradPart q : Freq.X) : L2C) ξ = 0 := by
      rw [← h1]
      simp
    have hne : (2 * Real.pi * ‖ξ‖) ≠ 0 := by
      have := norm_pos_iff.2 h2
      positivity
    have := (smul_eq_zero.1 h1').resolve_left hne
    simpa [h3] using this
  have hn := norm_xbar_sq q
  rw [hg, hq, norm_zero] at hn
  have h2 : ‖q‖ ^ 2 = 0 := by rw [hn]; norm_num
  exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)

theorem eq_zero_of_secondCLM_eq_zero (u : XX) (h : secondCLM u = 0) : u = 0 := by
  have h1 : (secondCLM u : TimeCircle → HBar) =ᵐ[volume] fun t => secondPart ((u : TimeCircle → XBar) t) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  have e : ((secondCLM u : HH) : TimeCircle → HBar) = ((0 : HH) : TimeCircle → HBar) :=
    congrArg (fun v : HH => (v : TimeCircle → HBar)) h
  refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
  have h0 := Lp.coeFn_zero HBar 2 (volume : Measure TimeCircle)
  have h0' := Lp.coeFn_zero XBar 2 (volume : Measure TimeCircle)
  filter_upwards [h1, h0, h0'] with t ht hz hz'
  exact eq_zero_of_secondPart_eq_zero _ (ht.symm.trans ((congrFun e t).trans hz))

theorem eq_zero_of_bordered_eq_zero (h2 : CoerciveBorderedHolds) {k : ℕ} (d : CertificateData k)
    (hd : IsCertificate d) (p : Fin k → ℝ) (hp : p ∈ d.box) (x : HH × (Fin k → ℝ))
    (hx : x.1 ∈ invariantHH d.symmetries) (h : bordered d p x = 0) : x = 0 := by
  have hb1 : x.1 + convection d p (freeInv (d.period p) x.1) + actuatorH d x.2 = 0 :=
    congrArg Prod.fst h
  have hb2 : pinMap d (freeInv (d.period p) x.1) = 0 := congrArg Prod.snd h
  have hfst : (bordered d p (x.1, x.2)).1 = 0 := congrArg Prod.fst h
  have hc := h2 d hd p hp x.1 hx x.2 (fun _ _ => 0)
    ⟨aestronglyMeasurable_const, fun _ _ => rfl, by simp [periodLIntegral]⟩
    (fun φ _ => (by simp : ∫ z : ℝ × Space, inner ℝ ((fun _ _ => (0 : Space)) z.1 z.2 : Space) (φ z.1 z.2) = 0).trans
      ((congrArg (fun v : HH => inner ℝ v (testInHH φ)) hfst).trans (inner_zero_left _)).symm)
  have hv : vecNorm (pinMap d (freeInv (d.period p) x.1)) = 0 := by
    simp only [hb2, vecNorm, Pi.zero_apply]
    simp
  have h0 : sizeZ d.weightFn (freeInv (d.period p) x.1) x.2 ≤ 0 := by
    refine hc.trans (le_of_eq ?_)
    rw [hv]
    simp [periodNorm, periodBallNorm, periodLIntegral, periodBallLIntegral]
  have hE : 0 ≤ ∫ t, sliceWeightedGrad d.weightFn
      (gradPart (((freeInv (d.period p) x.1 : XX) : TimeCircle → XBar) t)) := by
    refine integral_nonneg fun t => ?_
    unfold sliceWeightedGrad
    exact integral_nonneg fun y => mul_nonneg (le_trans hd.weight_pos.le (hd.weightFn_lower y))
      (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hsum : 0 ≤ ∑ i, x.2 i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hx0 : energyW d.weightFn (freeInv (d.period p) x.1) + ∑ i, x.2 i ^ 2 ≤ 0 :=
    Real.sqrt_eq_zero'.1 (le_antisymm h0 (Real.sqrt_nonneg _))
  unfold energyW at hx0
  have hsq := sq_nonneg ‖secondCLM (freeInv (d.period p) x.1)‖
  have hs : ‖secondCLM (freeInv (d.period p) x.1)‖ ^ 2 = 0 := le_antisymm (by linarith) hsq
  have hκs : ∑ i, x.2 i ^ 2 = 0 := le_antisymm (by linarith) hsum
  have hκ : x.2 = 0 := funext fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x.2 i))).1 hκs i
      (Finset.mem_univ _)
    simpa using this
  have hu : freeInv (d.period p) x.1 = 0 :=
    eq_zero_of_secondCLM_eq_zero _ (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hs))
  have hc0 : convection d p (freeInv (d.period p) x.1) = 0 :=
    (congrArg (convection d p) hu).trans (map_zero (convection d p))
  have ha0 : actuatorH d x.2 = 0 := (congrArg (actuatorH d) hκ).trans (map_zero (actuatorH d))
  have hb3 : x.1 + convection d p (freeInv (d.period p) x.1) + actuatorH d x.2 = x.1 :=
    (congrArg₂ (fun a b => x.1 + a + b) hc0 ha0).trans ((add_zero _).trans (add_zero _))
  exact Prod.ext (hb3.symm.trans hb1) hκ

theorem exists_inverse_of_compact_bordered {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] {k : ℕ}
    (V : Submodule ℝ H) (Bd A : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ)))
    (M : ((Fin k → ℝ) × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ)))
    (S : (H × (Fin k → ℝ)) →L[ℝ] ((Fin k → ℝ) × (Fin k → ℝ))) (hA : IsCompactOperator A)
    (c : H → H) (a : (Fin k → ℝ) → H) (q : H → (Fin k → ℝ)) (Pr : H → H)
    (hA1 : ∀ z, (A z).1 = c (Pr z.1)) (hA2 : ∀ z, (A z).2 = 0)
    (hB1 : ∀ z, (M (S z)).1 = a z.2) (hB2 : ∀ z, (M (S z)).2 = q (Pr z.1) - z.2)
    (hBd1 : ∀ z, (Bd z).1 = z.1 + c z.1 + a z.2) (hBd2 : ∀ z, (Bd z).2 = q z.1)
    (hc : ∀ g ∈ V, c g ∈ V) (ha : ∀ κ, a κ ∈ V) (hP1 : ∀ x, Pr x ∈ V) (hP2 : ∀ x ∈ V, Pr x = x)
    (hinj : ∀ x, x.1 ∈ V → Bd x = 0 → x = 0) :
    ∃ T : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ)), ∀ y, y.1 ∈ V → (T y).1 ∈ V ∧ Bd (T y) = y := by
  have hB : IsCompactOperator (M.comp S) := (isCompactOperator_of_locallyCompactSpace_dom S).clm_comp M
  set K := A + M.comp S with hKdef
  have hK : IsCompactOperator K := by
    rw [hKdef, FunLike.coe_add]
    exact hA.add hB
  have hform1 : ∀ z, (((1 : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ))) + K) z).1 =
      z.1 + (c (Pr z.1) + a z.2) := fun z => by
    simp [hKdef, hA1, hB1]
  have hform2 : ∀ z, (((1 : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ))) + K) z).2 =
      q (Pr z.1) := fun z => by
    simp [hKdef, hA2, hB2]
  have hfix : ∀ z, (((1 : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ))) + K) z).1 ∈ V →
      z.1 ∈ V ∧ Bd z = ((1 : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ))) + K) z := by
    intro z hz
    rw [hform1] at hz
    have hmem : z.1 ∈ V :=
      (Submodule.add_mem_iff_left _ (Submodule.add_mem _ (hc _ (hP1 z.1)) (ha _))).1 hz
    have hPr : Pr z.1 = z.1 := hP2 _ hmem
    refine ⟨hmem, Prod.ext ?_ ?_⟩
    · rw [hBd1, hform1, hPr, add_assoc]
    · rw [hBd2, hform2, hPr]
  have hinj' : Function.Injective ((1 : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ))) + K) := by
    intro x y hxy
    have hz : ((1 : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ))) + K) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨hm, hb⟩ := hfix (x - y) (by rw [hz]; exact Submodule.zero_mem _)
    exact sub_eq_zero.1 (hinj _ hm (hb.trans hz))
  obtain ⟨u, hu⟩ := Breakdown.isUnit_one_add_of_isCompactOperator_of_injective K hK hinj'
  have hT : ∀ y, ((1 : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ))) + K) ((↑u⁻¹ :
      (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ))) y) = y := fun y => by
    rw [← hu]
    show ((u : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ))) * ↑u⁻¹) y = y
    rw [Units.mul_inv]
    rfl
  refine ⟨↑u⁻¹, fun y hy => ?_⟩
  obtain ⟨hm, hb⟩ := hfix _ (by rw [hT]; exact hy)
  exact ⟨hm, hb.trans (hT y)⟩

theorem exists_borderedInvSpec (h1 : ConvectionCompactHolds)
    (h3 : InvarianceHolds) (h4 : FreeEquivariantHolds) {k : ℕ} (d : CertificateData k)
    (hd : IsCertificate d) (p : Fin k → ℝ) (hp : p ∈ d.box)
    (hinj : ∀ x : HH × (Fin k → ℝ), x.1 ∈ invariantHH d.symmetries → bordered d p x = 0 → x = 0)
    (Pr : HH →L[ℝ] HH) (hP1 : ∀ x, Pr x ∈ invariantHH d.symmetries)
    (hP2 : ∀ x ∈ invariantHH d.symmetries, Pr x = x) :
    ∃ T, BorderedInvSpec d p T :=
  exists_inverse_of_compact_bordered (invariantHH d.symmetries) (bordered d p)
    ((ContinuousLinearMap.inl ℝ HH (Fin k → ℝ)).comp
        (((convection d p).comp (freeInv (d.period p))).comp
          (Pr.comp (ContinuousLinearMap.fst ℝ HH (Fin k → ℝ)))))
    (((actuatorH d).comp (ContinuousLinearMap.fst ℝ (Fin k → ℝ) (Fin k → ℝ))).prod
        (ContinuousLinearMap.snd ℝ (Fin k → ℝ) (Fin k → ℝ)))
    ((ContinuousLinearMap.snd ℝ HH (Fin k → ℝ)).prod
        ((pinMap d).comp ((freeInv (d.period p)).comp
          (Pr.comp (ContinuousLinearMap.fst ℝ HH (Fin k → ℝ))))
          - ContinuousLinearMap.snd ℝ HH (Fin k → ℝ)))
    (((h1 d hd p hp).comp_clm (Pr.comp (ContinuousLinearMap.fst ℝ HH (Fin k → ℝ)))).clm_comp
      (ContinuousLinearMap.inl ℝ HH (Fin k → ℝ)))
    (fun g => convection d p (freeInv (d.period p) g)) (actuatorH d)
    (fun g => pinMap d (freeInv (d.period p) g)) Pr
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun g hg => ((h3 d hd p hp).1 _ (h4 d.symmetries (d.period p) (hd.period_pos p hp) g hg)).1)
    (h3 d hd p hp).2.1 hP1 hP2 hinj

end Internal.BorderedInvertible

open Internal.BorderedInvertible

theorem borderedInvertibleHolds_of (h1 : ConvectionCompactHolds) (h2 : CoerciveBorderedHolds)
    (h3 : InvarianceHolds) (h4 : FreeEquivariantHolds) (h5 : DataHolds) (h6 : FreeInvHolds) :
    BorderedInvertibleHolds := by
  intro k d hd p hp
  have hinj : ∀ x : HH × (Fin k → ℝ), x.1 ∈ invariantHH d.symmetries → bordered d p x = 0 →
      x = 0 := eq_zero_of_bordered_eq_zero h2 d hd p hp
  have hP := exists_projection_invariantHH d.symmetries
  exact ⟨exists_borderedInvSpec h1 h3 h4 d hd p hp hinj hP.choose hP.choose_spec.1 hP.choose_spec.2,
    fun x y hx hy hxy =>
    sub_eq_zero.1 (hinj (x - y) (Submodule.sub_mem _ hx hy)
      ((map_sub _ x y).trans (sub_eq_zero.2 hxy)))⟩

end Breakdown.Cert
