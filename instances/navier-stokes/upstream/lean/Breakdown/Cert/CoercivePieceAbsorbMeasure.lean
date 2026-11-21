import Breakdown.Cert.CoercivePieceAbsorbEdge
import Breakdown.Cert.CoercivePerturbationFacts
import Breakdown.Cert.CoerciveFieldModes

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PieceAbsorb

section Pieces

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
  (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
  (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))

abbrev slabMeasure : Measure (ℝ × Space) :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)

open Internal.FieldModes Internal.ModeRotation in
theorem slabMeasure_eq :
    slabMeasure = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := slab_eq

theorem ae_summable_of_tsum_lintegral {f : ℤ × ℤ → ℝ → Space → ℝ} (hf0 : ∀ ι σ y, 0 ≤ f ι σ y)
    (hfm : ∀ ι, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (f ι z.1 z.2)) slabMeasure)
    (hfin : ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (f ι σ y) < ⊤) :
    ∀ᵐ z ∂slabMeasure, Summable (fun ι => f ι z.1 z.2) := by
  have h1 : ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (f ι σ y)
      = ∫⁻ z, ∑' ι, ENNReal.ofReal (f ι z.1 z.2) ∂slabMeasure := by
    rw [lintegral_tsum hfm]
    exact tsum_congr fun ι => (lintegral_prod _ (hfm ι)).symm
  rw [h1] at hfin
  have hm : AEMeasurable (fun z : ℝ × Space => ∑' ι, ENNReal.ofReal (f ι z.1 z.2)) slabMeasure :=
    AEMeasurable.tsum hfm
  filter_upwards [ae_lt_top' hm hfin.ne] with z hz
  have := ENNReal.summable_toReal hz.ne
  simpa [ENNReal.toReal_ofReal (hf0 _ z.1 z.2)] using this

theorem alternatingSymbol_abs_le (i j l : Fin 3) : |alternatingSymbol i j l| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> norm_num [alternatingSymbol]

theorem norm_le_sqrt_cnormSq {β : Type*} [Fintype β] (x : β → ℂ) (b : β) :
    ‖x b‖ ≤ Real.sqrt (cnormSq x) := by
  apply Real.le_sqrt_of_sq_le
  unfold cnormSq
  exact Finset.single_le_sum (f := fun b => ‖x b‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ b)

theorem cnormSq_nonneg' {β : Type*} [Fintype β] (x : β → ℂ) : 0 ≤ cnormSq x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem cnormSq_curlOfGrad_le (g : Fin 3 × Fin 3 → ℂ) : cnormSq (curlOfGrad g) ≤ 243 * cnormSq g := by
  have hss := Real.sq_sqrt (cnormSq_nonneg' g)
  have hs := Real.sqrt_nonneg (cnormSq g)
  have hi : ∀ i, ‖curlOfGrad g i‖ ≤ 9 * Real.sqrt (cnormSq g) := by
    intro i
    unfold curlOfGrad
    calc ‖∑ j : Fin 3, ∑ l : Fin 3, (alternatingSymbol i j l : ℂ) * g (l, j)‖
        ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖(alternatingSymbol i j l : ℂ) * g (l, j)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
      _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, Real.sqrt (cnormSq g) := by
          refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc |alternatingSymbol i j l| * ‖g (l, j)‖ ≤ 1 * Real.sqrt (cnormSq g) :=
                mul_le_mul (alternatingSymbol_abs_le i j l) (norm_le_sqrt_cnormSq g _) (norm_nonneg _) zero_le_one
            _ = _ := one_mul _
      _ = 9 * Real.sqrt (cnormSq g) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  calc cnormSq (curlOfGrad g) = ∑ i : Fin 3, ‖curlOfGrad g i‖ ^ 2 := rfl
    _ ≤ ∑ i : Fin 3, (9 * Real.sqrt (cnormSq g)) ^ 2 :=
        Finset.sum_le_sum fun i _ => by nlinarith [hi i, norm_nonneg (curlOfGrad g i)]
    _ = 243 * cnormSq g := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow, hss]
        ring

theorem cnormSq_curlGradOfSecondDeriv_le (h : Fin 3 × Fin 3 × Fin 3 → ℂ) :
    cnormSq (curlGradOfSecondDeriv h) ≤ 729 * cnormSq h := by
  have hss := Real.sq_sqrt (cnormSq_nonneg' h)
  have hs := Real.sqrt_nonneg (cnormSq h)
  have hi : ∀ il, ‖curlGradOfSecondDeriv h il‖ ≤ 9 * Real.sqrt (cnormSq h) := by
    intro il
    unfold curlGradOfSecondDeriv
    calc ‖∑ j : Fin 3, ∑ m : Fin 3, (alternatingSymbol il.1 j m : ℂ) * h (m, il.2, j)‖
        ≤ ∑ j : Fin 3, ∑ m : Fin 3, ‖(alternatingSymbol il.1 j m : ℂ) * h (m, il.2, j)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
      _ ≤ ∑ j : Fin 3, ∑ m : Fin 3, Real.sqrt (cnormSq h) := by
          refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun m _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc |alternatingSymbol il.1 j m| * ‖h (m, il.2, j)‖ ≤ 1 * Real.sqrt (cnormSq h) :=
                mul_le_mul (alternatingSymbol_abs_le il.1 j m) (norm_le_sqrt_cnormSq h _) (norm_nonneg _)
                  zero_le_one
            _ = _ := one_mul _
      _ = 9 * Real.sqrt (cnormSq h) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  calc cnormSq (curlGradOfSecondDeriv h) = ∑ il : Fin 3 × Fin 3, ‖curlGradOfSecondDeriv h il‖ ^ 2 := rfl
    _ ≤ ∑ il : Fin 3 × Fin 3, (9 * Real.sqrt (cnormSq h)) ^ 2 :=
        Finset.sum_le_sum fun il _ => by nlinarith [hi il, norm_nonneg (curlGradOfSecondDeriv h il)]
    _ = 729 * cnormSq h := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
          mul_pow, hss]
        ring

open Internal.FieldModes in
theorem aestronglyMeasurable_modeSecondDeriv {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) (ι : ℤ × ℤ)
    (ijl : Fin 3 × Fin 3 × Fin 3) :
    AEStronglyMeasurable (fun z : ℝ × Space => modeSecondDeriv ι H z.1 z.2 ijl) volume := by
  have hc : Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
      axialRot (-q.1) (q.2 (axialRot q.1 (unitVector ijl.2.1)) (axialRot q.1 (unitVector ijl.2.2))) ijl.1) := by
    unfold axialRot
    fun_prop
  exact aestronglyMeasurable_modeAverage_comp ι ijl
    (E := Space →L[ℝ] Space →L[ℝ] Space)
    (fun (φ : ℝ) (A : Space →L[ℝ] Space →L[ℝ] Space) (k : Fin 3 × Fin 3 × Fin 3) =>
      axialRot (-φ) (A (axialRot φ (unitVector k.2.1)) (axialRot φ (unitVector k.2.2))) k.1) hc hH

open Internal.FieldModes in
theorem aemeasurable_modeSecondDeriv {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space => modeSecondDeriv ι H z.1 z.2) slabMeasure := by
  rw [slabMeasure_eq]
  exact (aemeasurable_pi_iff.2 fun ijl => (aestronglyMeasurable_modeSecondDeriv hH ι ijl).aemeasurable).restrict

theorem aemeasurable_ofReal_cnormSq {β : Type*} [Fintype β] {a : ℝ × Space → β → ℂ}
    (ha : AEMeasurable a slabMeasure) :
    AEMeasurable (fun z => ENNReal.ofReal (cnormSq (a z))) slabMeasure :=
  ENNReal.measurable_ofReal.comp_aemeasurable (Internal.FieldModes.continuous_cnormSq.measurable.comp_aemeasurable ha)

theorem fderiv_slice_eq {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (σ : ℝ) (x : Space) :
    fderiv ℝ (W σ) x
      = (fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) (σ, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
  have h1 : HasFDerivAt (fun z : ℝ × Space => W z.1 z.2)
      (fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) (σ, x)) (σ, x) :=
    ((hW.differentiable (by simp)) (σ, x)).hasFDerivAt
  exact (h1.comp x (hasFDerivAt_prodMk_right σ x)).fderiv

theorem continuous_fderiv_slice {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) := by
  have : (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2)
      = fun z => (fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
    funext z
    exact fderiv_slice_eq hW z.1 z.2
  rw [this]
  exact (hW.continuous_fderiv (by simp)).clm_comp continuous_const

theorem measurable_secondDeriv_slice {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    Measurable (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (W z.1) x) z.2) :=
  measurable_fderiv_with_param ℝ (f := fun σ x => fderiv ℝ (W σ) x) (continuous_fderiv_slice hW)

theorem aem_sqrt_cnormSq {β : Type*} [Fintype β] {a : ℝ × Space → β → ℂ}
    (ha : ∀ b, AEStronglyMeasurable (fun z => a z b) volume) :
    AEMeasurable (fun z => Real.sqrt (cnormSq (a z))) volume :=
  Real.continuous_sqrt.measurable.comp_aemeasurable
    (Internal.FieldModes.continuous_cnormSq.measurable.comp_aemeasurable
      (aemeasurable_pi_iff.2 fun b => (ha b).aemeasurable))

theorem aem_velAmp {X : ℝ → Space → Space} (hX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume)
    (ι : ℤ × ℤ) : AEMeasurable (fun z : ℝ × Space => velAmp X ι z.1 z.2) volume :=
  aem_sqrt_cnormSq fun i => Internal.FieldModes.aestronglyMeasurable_modeVel hX ι i

theorem aem_gradAmp {K : ℝ → Space → (Space →L[ℝ] Space)}
    (hK : AEStronglyMeasurable (fun z : ℝ × Space => K z.1 z.2) volume)
    (ι : ℤ × ℤ) : AEMeasurable (fun z : ℝ × Space => gradAmp K ι z.1 z.2) volume :=
  aem_sqrt_cnormSq fun ij => Internal.FieldModes.aestronglyMeasurable_modeGrad hK ι ij

theorem aem_vortAmp {K : ℝ → Space → (Space →L[ℝ] Space)}
    (hK : AEStronglyMeasurable (fun z : ℝ × Space => K z.1 z.2) volume)
    (ι : ℤ × ℤ) : AEMeasurable (fun z : ℝ × Space => vortAmp K ι z.1 z.2) volume := by
  refine aem_sqrt_cnormSq (a := fun z => curlOfGrad (modeGrad ι K z.1 z.2)) fun i => ?_
  unfold curlOfGrad
  exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => Finset.aestronglyMeasurable_fun_sum _ fun l _ =>
    (Internal.FieldModes.aestronglyMeasurable_modeGrad hK ι (l, j)).const_mul _

theorem aem_secondDerivAmp {K : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hK : AEStronglyMeasurable (fun z : ℝ × Space => K z.1 z.2) volume)
    (ι : ℤ × ℤ) : AEMeasurable (fun z : ℝ × Space => secondDerivAmp K ι z.1 z.2) volume :=
  aem_sqrt_cnormSq fun ijl => aestronglyMeasurable_modeSecondDeriv hK ι ijl

theorem aem_vortGradAmp {K : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hK : AEStronglyMeasurable (fun z : ℝ × Space => K z.1 z.2) volume)
    (ι : ℤ × ℤ) : AEMeasurable (fun z : ℝ × Space => vortGradAmp K ι z.1 z.2) volume := by
  refine aem_sqrt_cnormSq (a := fun z => curlGradOfSecondDeriv (modeSecondDeriv ι K z.1 z.2)) fun il => ?_
  unfold curlGradOfSecondDeriv
  exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => Finset.aestronglyMeasurable_fun_sum _ fun m _ =>
    (aestronglyMeasurable_modeSecondDeriv hK ι (m, il.2, j)).const_mul _

open Classical in
theorem aem_edgeSum (hh : HarmonicBounds) (T : Set (ℤ × ℤ)) {X g : ℝ × Space → ℤ × ℤ → ℝ}
    (hX : ∀ α, AEMeasurable (fun z => X z α) volume) (hg : ∀ κ, AEMeasurable (fun z => g z κ) volume)
    (ι : ℤ × ℤ) : AEMeasurable (fun z => edgeSum hh T (X z) (g z) ι) volume := by
  unfold edgeSum
  split_ifs with h1 h2
  · refine Finset.aemeasurable_fun_sum _ fun α _ => ?_
    by_cases hc : ι - α ∈ T
    · simp only [hc, if_true]
      exact aemeasurable_const
    · simp only [hc, if_false]
      exact (hX α).mul (hg _)
  · refine Finset.aemeasurable_fun_sum _ fun α _ => ?_
    by_cases hc : -ι - α ∈ T
    · simp only [hc, if_true]
      exact aemeasurable_const
    · simp only [hc, if_false]
      exact (hX α).mul (hg _)
  · exact aemeasurable_const

def stretchOfData (p : (Space →L[ℝ] Space) × (Space →L[ℝ] Space) × (Space →L[ℝ] Space →L[ℝ] Space) × Space) : ℝ :=
  -(∑ i : Fin 3, ∑ j : Fin 3, curlVec p.1 i
      * ((p.2.1 (unitVector j) i + p.2.1 (unitVector i) j) / 2) * curlVec p.1 j)
    + ∑ j : Fin 3, (∑ m : Fin 3, p.2.2.2 m * vortGrad p.2.2.1 j m) * curlVec p.1 j
    + (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * vortGrad p.2.2.1 j m * p.1 (unitVector j) i * p.2.2.2 l

theorem stretchForm_eq (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space) :
    stretchForm W v G σ y
      = stretchOfData (G σ y, fderiv ℝ (W σ) y, fderiv ℝ (fun x => fderiv ℝ (W σ) x) y, v σ y) := rfl

theorem continuous_stretchOfData : Continuous stretchOfData := by
  unfold stretchOfData curlVec vortGrad
  fun_prop

theorem aem_stretchForm {W v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) :
    AEMeasurable (fun z : ℝ × Space => stretchForm W v G z.1 z.2) volume := by
  have ht : AEStronglyMeasurable (fun z : ℝ × Space =>
      (G z.1 z.2, fderiv ℝ (W z.1) z.2, fderiv ℝ (fun x => fderiv ℝ (W z.1) x) z.2, v z.1 z.2)) volume :=
    hG.prodMk ((continuous_fderiv_slice hW).aestronglyMeasurable.prodMk
      ((measurable_secondDeriv_slice hW).aestronglyMeasurable.prodMk hv))
  exact (continuous_stretchOfData.comp_aestronglyMeasurable ht).aemeasurable

theorem block_nonpos_of (hE : ∀ β y, 0 ≤ (m.epsP β).wt y) (hM : ∀ β y, 0 ≤ (m.muP β).wt y)
    (σ : ℝ) (y : Space) : pieceBlock m W v G H σ y ≤ 0 := by
  have hFS : ∀ a, 0 ≤ frameSpeedSup W a y := fun a => Real.iSup_nonneg fun _ => norm_nonneg _
  have hvS : 0 ≤ vortSup W y := Real.iSup_nonneg fun _ => norm_nonneg _
  have hvGS : 0 ≤ vortGradSup W y := Real.iSup_nonneg fun _ => norm_nonneg _
  have hpn : ∀ T (g : ℤ × ℤ → ℝ), 0 ≤ pieceNorm T g := fun _ _ => Real.sqrt_nonneg _
  have hwg : ∀ f, 0 ≤ PieceWeights.wtGrad f y := fun _ => norm_nonneg _
  unfold pieceBlock pieceEpsBlock pieceMuBlock
  refine add_nonpos (Finset.sum_nonpos fun β _ => ?_) (Finset.sum_nonpos fun β _ => ?_)
  · have ha := hE β y
    have h1 := hpn (m.epsP β).modes (fun κ => vortGradAmp H κ σ y)
    have h2 := hpn (m.epsP β).modes (fun κ => vortAmp G κ σ y)
    have h3 := hpn (m.epsP β).modes (fun κ => velAmp v κ σ y)
    have h4 := hpn (m.epsP β).modes (fun κ => gradAmp G κ σ y)
    nlinarith [mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg ha (hFS (m.epsP β).frame)) (hwg (m.epsP β).wt)) h1) h2,
      mul_nonneg (mul_nonneg ha (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hvS)
        (abs_nonneg (m.epsP β).frame))) (sq_nonneg (pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y))),
      mul_nonneg (mul_nonneg (mul_nonneg ha hvGS) h3) h2, mul_nonneg (mul_nonneg (mul_nonneg ha hvS) h4) h2]
  · have ha := hM β y
    have h1 := hpn (m.muP β).modes (fun κ => gradAmp G κ σ y)
    have h2 := hpn (m.muP β).modes (fun κ => velAmp v κ σ y)
    nlinarith [mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg ha (hFS (m.muP β).frame)) (hwg (m.muP β).wt)) h1) h2,
      mul_nonneg (mul_nonneg ha (abs_nonneg (m.muP β).frame))
        (sq_nonneg (pieceNorm (m.muP β).modes (fun κ => velAmp v κ σ y)))]

theorem ae_goodPoint {Γ : Set Symmetry} {g : ℝ → Space → Space} (hPar : ModeSquareSumHolds)
    (hSecondDeriv : PerturbationSecondDerivBoundHolds) (hL2 : PerturbationLocalSquareIntegrabilityHolds)
    (hv : IsPerturbation Γ P v G H g) :
    ∀ᵐ z ∂slabMeasure, IsGoodPoint v G H z.1 z.2 := by
  have hRot := axialRotationHolds_proof
  have hGfin := hv.gradient_finite
  have hGs : ∀ᵐ z ∂slabMeasure, Summable (fun ι => cnormSq (modeGrad ι G z.1 z.2)) := by
    refine ae_summable_of_tsum_lintegral (f := fun ι σ y => cnormSq (modeGrad ι G σ y))
      (fun _ _ _ => cnormSq_nonneg' _)
      (fun ι => aemeasurable_ofReal_cnormSq (Internal.FieldModes.aemeasurable_modeGrad hv.measurable_gradient ι)) ?_
    rw [← hPar.2.1 G hv.measurable_gradient hv.periodic_gradient hGfin]
    exact hGfin
  have hHfin : periodLIntegral (fun σ y => secondDerivSq (H σ y)) < ⊤ :=
    lt_of_le_of_lt (hSecondDeriv Γ P v G H g hv) hv.sumSecondPartials_finite
  have hHs : ∀ᵐ z ∂slabMeasure, Summable (fun ι => cnormSq (modeSecondDeriv ι H z.1 z.2)) := by
    refine ae_summable_of_tsum_lintegral (f := fun ι σ y => cnormSq (modeSecondDeriv ι H σ y))
      (fun _ _ _ => cnormSq_nonneg' _)
      (fun ι => aemeasurable_ofReal_cnormSq (aemeasurable_modeSecondDeriv hv.measurable_secondDeriv ι)) ?_
    rw [← hPar.2.2.1 H hv.measurable_secondDeriv hv.periodic_secondDeriv hHfin]
    exact hHfin
  have hvn : ∀ n : ℕ, ∀ᵐ z ∂slabMeasure, ‖z.2‖ ≤ n → Summable (fun ι => cnormSq (modeVel ι v z.1 z.2)) := by
    intro n
    set X : ℝ → Space → Space := fun σ y => (Metric.closedBall (0 : Space) n).indicator (v σ) y with hXdef
    have hXm : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume := by
      refine (hv.measurable_velocity.indicator
        ((measurableSet_closedBall (x := (0 : Space)) (ε := (n : ℝ))).preimage measurable_snd)).congr
        (ae_of_all _ fun z => ?_)
      by_cases hz : z.2 ∈ Metric.closedBall (0 : Space) n
      · rw [Set.indicator_of_mem (show z ∈ Prod.snd ⁻¹' Metric.closedBall (0 : Space) n from hz)]
        exact (Set.indicator_of_mem hz _).symm
      · rw [Set.indicator_of_notMem (show z ∉ Prod.snd ⁻¹' Metric.closedBall (0 : Space) n from hz)]
        exact (Set.indicator_of_notMem hz _).symm
    have hXp : IsTimePeriodic X := by
      intro σ y
      have hp : v (σ + 1) = v σ := funext fun y => hv.periodic_velocity σ y
      simp only [hXdef, hp]
    have hXf : periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) < ⊤ := by
      have hL := hL2 Γ P v G H g hv n
      refine lt_of_le_of_lt (le_of_eq ?_) hL
      unfold periodLIntegral
      refine lintegral_congr fun σ => ?_
      rw [← lintegral_indicator measurableSet_closedBall]
      refine lintegral_congr fun y => ?_
      by_cases hy : y ∈ Metric.closedBall (0 : Space) n
      · simp only [hXdef, Set.indicator_of_mem hy]
      · simp only [hXdef, Set.indicator_of_notMem hy, norm_zero]
        norm_num
    have hXs : ∀ᵐ z ∂slabMeasure, Summable (fun ι => cnormSq (modeVel ι X z.1 z.2)) := by
      refine ae_summable_of_tsum_lintegral (f := fun ι σ y => cnormSq (modeVel ι X σ y))
        (fun _ _ _ => cnormSq_nonneg' _)
        (fun ι => aemeasurable_ofReal_cnormSq (Internal.FieldModes.aemeasurable_modeVel hXm ι)) ?_
      rw [← hPar.1 X hXm hXp hXf]
      exact hXf
    filter_upwards [hXs] with z hz hzn
    have heq : ∀ ι, modeVel ι X z.1 z.2 = modeVel ι v z.1 z.2 := by
      intro ι
      unfold modeVel
      congr 1
      funext τ φ i
      have hmem : axialRot φ z.2 ∈ Metric.closedBall (0 : Space) n := by
        rw [Metric.mem_closedBall, dist_zero_right, Internal.ModeRotation.norm_axialRot hRot]
        exact hzn
      simp only [hXdef, Set.indicator_of_mem hmem]
    simpa only [heq] using hz
  have hvs : ∀ᵐ z ∂slabMeasure, Summable (fun ι => cnormSq (modeVel ι v z.1 z.2)) := by
    filter_upwards [ae_all_iff.2 hvn] with z hz
    obtain ⟨n, hn⟩ := exists_nat_ge ‖z.2‖
    exact hz n hn
  filter_upwards [hGs, hHs, hvs] with z hG hH hV
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [secondDerivAmp, Real.sq_sqrt (cnormSq_nonneg' _)] using hH
  · refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun ι => ?_) (hH.mul_left 729)
    rw [vortGradAmp, Real.sq_sqrt (cnormSq_nonneg' _)]
    exact cnormSq_curlGradOfSecondDeriv_le _
  · simpa only [gradAmp, Real.sq_sqrt (cnormSq_nonneg' _)] using hG
  · refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun ι => ?_) (hG.mul_left 243)
    rw [vortAmp, Real.sq_sqrt (cnormSq_nonneg' _)]
    exact cnormSq_curlOfGrad_le _
  · simpa only [velAmp, Real.sq_sqrt (cnormSq_nonneg' _)] using hV

theorem aemeasurable_hypothesisSide {Γ : Set Symmetry} {g : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hv : IsPerturbation Γ P v G H g) :
    AEMeasurable (fun z : ℝ × Space =>
      (∑' ι, ENNReal.ofReal (piecePos m P v G ι z.1 z.2)) + (∑' ι, ENNReal.ofReal (pieceRest m h w W v G H ι z.1 z.2))
        + ENNReal.ofReal (pieceBlock m W v G H z.1 z.2) + ENNReal.ofReal (stretchForm W v G z.1 z.2)) slabMeasure := by
  have hWc : AEStronglyMeasurable (fun z : ℝ × Space => W z.1 z.2) volume := hW.continuous.aestronglyMeasurable
  have hgW : AEStronglyMeasurable (fun z : ℝ × Space => gradField W z.1 z.2) volume :=
    (continuous_fderiv_slice hW).aestronglyMeasurable
  have hhW : AEStronglyMeasurable (fun z : ℝ × Space => secondDerivField W z.1 z.2) volume :=
    (measurable_secondDeriv_slice hW).aestronglyMeasurable
  have hwE : ∀ β, Measurable (m.epsP β).wt := fun β => by
    obtain ⟨K, hK⟩ := hm.eps_increment β
    exact hK.continuous.measurable
  have hwM : ∀ β, Measurable (m.muP β).wt := fun β => by
    obtain ⟨K, hK⟩ := hm.mu_increment β
    exact hK.continuous.measurable
  have hPos : ∀ ι, AEMeasurable (fun z : ℝ × Space => piecePos m P v G ι z.1 z.2) volume := by
    intro ι
    unfold piecePos pieceEpsPos pieceMuPos
    refine AEMeasurable.add (Finset.aemeasurable_fun_sum _ fun β _ => ?_)
      (Finset.aemeasurable_fun_sum _ fun β _ => ?_)
    · have h1 := hwE β
      have h2 := aem_vortAmp hv.measurable_gradient ι
      fun_prop
    · have h1 := hwM β
      have h2 := aem_velAmp hv.measurable_velocity ι
      fun_prop
  have hRest : ∀ ι, AEMeasurable (fun z : ℝ × Space => pieceRest m h w W v G H ι z.1 z.2) volume := by
    intro ι
    have a2 := aem_secondDerivAmp hv.measurable_secondDeriv ι
    have ac := aem_vortGradAmp hv.measurable_secondDeriv ι
    have a1 := aem_gradAmp hv.measurable_gradient ι
    have ao := aem_vortAmp hv.measurable_gradient ι
    have a0 := aem_velAmp hv.measurable_velocity ι
    have hD : Measurable (m.convD (m.classOf ι)) := (hm.convD_smooth _).continuous.measurable
    have hZ : Measurable (m.convZ (m.classOf ι)) := (hm.convZ_smooth _).continuous.measurable
    have hDD : Measurable (ModeWeights.secondDerivNorm (m.convD (m.classOf ι))) :=
      ((hm.convD_smooth _).continuous_iteratedFDeriv le_rfl).norm.measurable
    have hZZ : Measurable (ModeWeights.secondDerivNorm (m.convZ (m.classOf ι))) :=
      ((hm.convZ_smooth _).continuous_iteratedFDeriv le_rfl).norm.measurable
    have hw := hm.weight_measurable
    unfold pieceRest modeVals baseDensity pieceEpsRestMode pieceMuRestMode
    refine AEMeasurable.add (AEMeasurable.add ?_ (Finset.aemeasurable_fun_sum _ fun β _ => ?_))
      (Finset.aemeasurable_fun_sum _ fun β _ => ?_)
    · fun_prop
    · have h1 := hwE β
      have e1 := aem_edgeSum h (m.epsP β).modes (X := fun z α => velAmp W α z.1 z.2)
        (g := fun z κ => vortGradAmp H κ z.1 z.2) (fun α => aem_velAmp hWc α)
        (fun κ => aem_vortGradAmp hv.measurable_secondDeriv κ) ι
      have e2 := aem_edgeSum h (m.epsP β).modes (X := fun z α => gradAmp (gradField W) α z.1 z.2)
        (g := fun z κ => vortAmp G κ z.1 z.2) (fun α => aem_gradAmp hgW α)
        (fun κ => aem_vortAmp hv.measurable_gradient κ) ι
      have e3 := aem_edgeSum h (m.epsP β).modes (X := fun z α => vortGradAmp (secondDerivField W) α z.1 z.2)
        (g := fun z κ => velAmp v κ z.1 z.2) (fun α => aem_vortGradAmp hhW α)
        (fun κ => aem_velAmp hv.measurable_velocity κ) ι
      have e4 := aem_edgeSum h (m.epsP β).modes (X := fun z α => vortAmp (gradField W) α z.1 z.2)
        (g := fun z κ => gradAmp G κ z.1 z.2) (fun α => aem_vortAmp hgW α)
        (fun κ => aem_gradAmp hv.measurable_gradient κ) ι
      exact (((h1.comp_aemeasurable measurable_snd.aemeasurable).mul ao).mul
        (((e1.add e2).add e3).add e4)).neg
    · have h1 := hwM β
      have e1 := aem_edgeSum h (m.muP β).modes (X := fun z α => velAmp W α z.1 z.2)
        (g := fun z κ => gradAmp G κ z.1 z.2) (fun α => aem_velAmp hWc α)
        (fun κ => aem_gradAmp hv.measurable_gradient κ) ι
      have s1 : AEMeasurable (fun z : ℝ × Space =>
          ∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2 * velAmp v (ι - α) z.1 z.2) volume :=
        Finset.aemeasurable_fun_sum _ fun α _ => (aem_gradAmp hgW α).mul (aem_velAmp hv.measurable_velocity _)
      have hw1 : AEMeasurable (fun z : ℝ × Space => (m.muP β).wt z.2) volume :=
        h1.comp_aemeasurable measurable_snd.aemeasurable
      have q1 : AEMeasurable (fun z : ℝ × Space =>
          (∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2 * velAmp v (ι - α) z.1 z.2) ^ 2
              / (2 * (m.muP β).eta)
            + (1 / 2) * (m.muP β).eta * (m.muP β).wt z.2 ^ 2 * velAmp v ι z.1 z.2 ^ 2) volume :=
        ((s1.pow_const 2).div_const _).add ((aemeasurable_const.mul (hw1.pow_const 2)).mul (a0.pow_const 2))
      exact (((hw1.mul a0).mul e1).neg).sub (q1.const_mul (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)))
  have hB : ∀ z : ℝ × Space, ENNReal.ofReal (pieceBlock m W v G H z.1 z.2) = 0 := fun z =>
    ENNReal.ofReal_of_nonpos (block_nonpos_of m W v G H hm.eps_wt_nonneg hm.mu_wt_nonneg z.1 z.2)
  simp only [hB, add_zero]
  rw [slabMeasure_eq]
  exact (((AEMeasurable.tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (hPos ι)).add
    (AEMeasurable.tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (hRest ι))).add
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (aem_stretchForm hW hv.measurable_velocity hv.measurable_gradient))).restrict

theorem aemeasurable_stretchNeg {Γ : Set Symmetry} {g : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hv : IsPerturbation Γ P v G H g) :
    AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (-stretchForm W v G z.1 z.2)) slabMeasure := by
  rw [slabMeasure_eq]
  exact (ENNReal.measurable_ofReal.comp_aemeasurable
    (aem_stretchForm hW hv.measurable_velocity hv.measurable_gradient).neg).restrict


end Pieces

end Internal.PieceAbsorb

end Coercive

end Breakdown
