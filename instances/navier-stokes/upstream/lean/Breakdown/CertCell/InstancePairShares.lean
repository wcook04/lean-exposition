import Breakdown.CertCell.InstancePairSharesPin

open scoped ENNReal ComplexOrder
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace InstancePair

open Instance

namespace Internal

open Bridge.Internal.ModeFlip (ae_flip_gradient ae_joint_flip grad_of_columns)

theorem actuator_input (hgm : ActuatorGradientModes) {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (S : Fin k → Finset (ℤ × ℤ))
    (hclass : Bridge.IsModeClass D.cert.symmetries D.azimuthOrder)
    (hfmt : ∀ i, ActuatorShapeFacts D.azimuthOrder (S i) (D.cert.actuator i))
    (hsupp : ActuatorSupportInCells D) (hrec : IsPairEntry D R S) (i : Fin k) :
    PairInput D.azimuthOrder R.pairLabels (fun K => (D.mesh.box K).rect) (gradField (D.cert.actuator i)) := by
  obtain ⟨γ, -, hγ1, -⟩ := hclass.flip
  refine ⟨(hfmt i).gradient_measurable, (hfmt i).gradient_periodic, (hfmt i).gradient_finite, ?_, ?_, ?_⟩
  · have hinv : ∀ᵐ z : ℝ × Space, D.cert.actuator i z.1 (flipPoint z.2) = flipPoint (D.cert.actuator i z.1 z.2) :=
      (hfmt i).invariant.mono fun z hz => hz.2
    have hvs : ∀ᵐ s, ∀ᵐ x, D.cert.actuator i s (flipPoint x) = flipPoint (D.cert.actuator i s x) :=
      Measure.ae_ae_of_ae_prod hinv
    have hGs : ∀ᵐ s, ∀ᵐ x, ∀ j, gradField (D.cert.actuator i) s (flipPoint x) (unitVector j)
        = frameSign j • flipPoint (gradField (D.cert.actuator i) s x (unitVector j)) := by
      filter_upwards [hvs] with s h1
      filter_upwards [ae_flip_gradient γ.1 hγ1 ((hfmt i).weak_gradient s) 1 (one_mul 1)
        (h1.mono fun x hx => by rw [hx, one_smul])] with x hx j
      rw [hx j, one_mul]
    have hGj : ∀ j, ∀ᵐ z : ℝ × Space, gradField (D.cert.actuator i) z.1 (flipPoint z.2) (unitVector j)
        = frameSign j • flipPoint (gradField (D.cert.actuator i) z.1 z.2 (unitVector j)) := fun j =>
      ae_joint_flip γ.1 hγ1 (fun s x => gradField (D.cert.actuator i) s x (unitVector j))
        ((continuous_id.clm_apply continuous_const).comp_aestronglyMeasurable (hfmt i).gradient_measurable)
        (frameSign j) (hGs.mono fun s hs => hs.mono fun x hx => hx j)
    filter_upwards [ae_all_iff.2 hGj] with z hz u
    exact grad_of_columns γ.1 hγ1 hz u
  · intro ξ hξ
    refine hgm D.azimuthOrder (S i) (D.cert.actuator i) (lt_of_lt_of_le zero_lt_one hclass.order_pos) (hfmt i) ξ
      fun ι hι => ⟨hξ ι (hrec.actuator_labels i ι hι).1, fun h => hξ (-ι) (hrec.actuator_labels i ι hι).2 ?_⟩
    rw [labelHarmonic_neg, h, neg_neg]
  · intro σ y h
    by_contra hno
    push Not at hno
    apply h
    have hU : IsOpen (cylFold ⁻¹' (⋃ K, (D.mesh.box K).rect)ᶜ) :=
      (isOpen_compl_iff.2 (isClosed_iUnion_of_finite fun K => isClosed_Icc.prod isClosed_Icc)).preimage
        continuous_cylFold
    have hyU : y ∈ cylFold ⁻¹' (⋃ K, (D.mesh.box K).rect)ᶜ := by
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
      exact hno
    have hz : D.cert.actuator i σ =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [hU.mem_nhds hyU] with y' hy'
      by_contra hb
      obtain ⟨K, hK⟩ := hsupp i σ y' hb
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hy'
      exact hy' K hK
    show fderiv ℝ (D.cert.actuator i σ) y = 0
    rw [hz.fderiv_eq]
    exact fderiv_const_apply 0

end Internal

open Internal in
theorem pairSharesFromExactProfiles (hreg : CellMatFieldRegular) (hgm : ActuatorGradientModes)
    (hhalf : HalfPlanePairing) (hibp : ActuatorPairingByParts) : PairSharesFromExactProfiles := by
  intro k C nE nM D R S jmax e hclass hact hfmt hsupp hpin hrec he q hq v G H g hp κ ζ
  have hbox := hpin.mesh_valid.box_valid
  have hq0 : ∀ K, (D.mesh.box K).rect ⊆ Set.Ici 0 ×ˢ Set.Ici 0 := fun K p hp' =>
    ⟨le_trans (hbox K).r_order.1 hp'.1.1, le_trans (hbox K).z_order.1 hp'.2.1⟩
  have hcl : ∀ K, IsClosed (D.mesh.box K).rect := fun K => isClosed_Icc.prod isClosed_Icc
  let Bg : Fin k ⊕ Fin k → ℝ → Space → (Space →L[ℝ] Space) :=
    Sum.elim (fun i => gradField (D.cert.actuator i)) (fun i => D.cert.pin i)
  have hin : ∀ gg, PairInput D.azimuthOrder R.pairLabels (fun K => (D.mesh.box K).rect) (Bg gg) := by
    rintro (i | i)
    · exact actuator_input hgm D R S hclass hfmt hsupp hrec i
    · exact pin_input hreg D R S hpin hrec i
  have hpe : ∀ gg, pairing G (Bg gg)
      = 4 * Real.pi * ∑ K, rectPair D.azimuthOrder R.pairLabels G (Bg gg) (D.mesh.box K).rect := fun gg =>
    pairing_eq_sum hhalf hclass hp hq0 hcl hpin.mesh_valid.boxes_apart (hin gg)
  have hshare : ∀ K, CellCalculus.pairShare D K R.pairLabels (R.pairProfile K) κ ζ G
      = ∑ gg, CellCalculus.pairWeight κ ζ gg * rectPair D.azimuthOrder R.pairLabels G (Bg gg) (D.mesh.box K).rect := by
    intro K
    unfold CellCalculus.pairShare rectPair
    refine Finset.sum_congr rfl fun gg _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun ι _ => ?_
    have hI : (∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
          CellCalculus.gradAt D.azimuthOrder ι G a b p * starRingEnd ℂ (R.pairProfile K gg ι p a b))
        = ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
          CellCalculus.gradAt D.azimuthOrder ι G a b p
            * starRingEnd ℂ (CellCalculus.gradAt D.azimuthOrder ι (Bg gg) a b p) := by
      refine setIntegral_congr_fun (hcl K).measurableSet fun p hp' => ?_
      rcases gg with i | i
      · simp only [hrec.actuator_profile K i ι p hp', Bg, Sum.elim_inl]
      · simp only [hrec.pin_profile K i ι p hp', Bg, Sum.elim_inr]
    rw [hI]
  have hpi : (4 * Real.pi) ≠ 0 := by positivity
  have hsum : ∑ K, CellCalculus.pairShare D K R.pairLabels (R.pairProfile K) κ ζ G
      = ∑ gg, CellCalculus.pairWeight κ ζ gg * (pairing G (Bg gg) / (4 * Real.pi)) := by
    simp_rw [hshare]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun gg _ => ?_
    rw [← Finset.mul_sum, hpe gg, mul_div_cancel_left₀ _ hpi]
  rw [hsum, Fintype.sum_sum_type]
  have hA : ∀ i, pairing G (Bg (Sum.inl i)) = multiplierRight (D.pieces q) v G H (D.cert.actuator i) := fun i =>
    (hibp D S jmax hact hfmt q hq v G H g hp i).symm
  have hP : ∀ i, pairing G (Bg (Sum.inr i)) = pinValue (D.cert.pin i) G := fun i => rfl
  simp only [CellCalculus.pairWeight, hA, hP]
  have hk : 0 ≤ e * ∑ i, κ i ^ 2 := mul_nonneg he (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hE : (∑ i, κ i * multiplierRight (D.pieces q) v G H (D.cert.actuator i)
        + 2 * ∑ i, ζ i * pinValue (D.cert.pin i) G) / (4 * Real.pi)
      = ∑ i, κ i * (multiplierRight (D.pieces q) v G H (D.cert.actuator i) / (4 * Real.pi))
        + ∑ i, 2 * ζ i * (pinValue (D.cert.pin i) G / (4 * Real.pi)) := by
    rw [add_div, Finset.sum_div, Finset.mul_sum, Finset.sum_div]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
  rw [hE]
  linarith

end InstancePair

end CertCell

end Breakdown
