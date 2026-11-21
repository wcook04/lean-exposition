import Breakdown.FracCell.CircleProduct
import Breakdown.FracCell.SliceMeasurable
import Breakdown.FracCell.MeshFarRegular

open MeasureTheory ComplexConjugate Real

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.SharpCircleStrainParts

open SteadyCert Assembly SharpParts SharpSupremumParts SharpCircleBoundParts CircleProduct

attribute [local instance] CircleProduct.pi_fact

theorem interior_ae (K : CellBox) :
    ∀ᵐ p ∂(volume.restrict K.rect), p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂ := by
  have h : volume.restrict K.rect = volume.restrict (Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂) :=
    Measure.restrict_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc).symm
  rw [h]
  exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)

theorem fst_ne_ae (K : CellBox) : ∀ᵐ p ∂(volume.restrict K.rect), p.1 ≠ 0 := by
  refine ae_restrict_of_ae ?_
  rw [ae_iff]
  have e : {a : ℝ × ℝ | ¬a.1 ≠ 0} = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
    ext a; simp
  rw [e, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

theorem curl_sq_le (s : Fin 3 → Fin 3 → ℂ) (i : Fin 3) : ‖curlComp s i‖ ^ 2 ≤ 9 * sumSq s := by
  have h0 : ‖curlComp s i‖ ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖s l j‖ := by
    unfold curlComp
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans ?_)
    refine Finset.sum_le_sum fun l _ => ?_
    rw [norm_mul]
    have hs : ‖(CellCert.permSign i j l : ℂ)‖ ≤ 1 := by
      unfold CellCert.permSign
      split_ifs <;> simp
    calc ‖(CellCert.permSign i j l : ℂ)‖ * ‖s l j‖ ≤ 1 * ‖s l j‖ :=
          mul_le_mul_of_nonneg_right hs (norm_nonneg _)
      _ = ‖s l j‖ := one_mul _
  have h1 : ‖curlComp s i‖ ^ 2 ≤ (∑ j : Fin 3, ∑ l : Fin 3, ‖s l j‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h0 2
  have h2 : (∑ j : Fin 3, ∑ l : Fin 3, ‖s l j‖) ^ 2 ≤ 3 * ∑ j : Fin 3, (∑ l : Fin 3, ‖s l j‖) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3))) (f := fun j => ∑ l : Fin 3, ‖s l j‖)
    simpa using this
  have h3 : ∀ j : Fin 3, (∑ l : Fin 3, ‖s l j‖) ^ 2 ≤ 3 * ∑ l : Fin 3, ‖s l j‖ ^ 2 := by
    intro j
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3))) (f := fun l => ‖s l j‖)
    simpa using this
  have h4 : ∑ j : Fin 3, (∑ l : Fin 3, ‖s l j‖) ^ 2 ≤ ∑ j : Fin 3, 3 * ∑ l : Fin 3, ‖s l j‖ ^ 2 :=
    Finset.sum_le_sum fun j _ => h3 j
  have h5 : ∑ j : Fin 3, 3 * ∑ l : Fin 3, ‖s l j‖ ^ 2 = 3 * sumSq s := by
    rw [← Finset.mul_sum]
    unfold sumSq
    rw [Finset.sum_comm]
  nlinarith

end Breakdown.CellCert.CellAnalysis.SharpCircleStrainParts

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly SharpParts SharpSupremumParts SharpCircleBoundParts CircleProduct SharpCircleStrainParts

attribute [local instance] CircleProduct.pi_fact

theorem sharpCircleStrain_holds : SharpCircleStrainStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx
  have hK := hd.box
  have hm : 1 ≤ c.order := le_trans (by norm_num) hc.base.order_ge
  obtain ⟨C0, hC0⟩ := hc.model_bounded
  filter_upwards [SliceMeasurable.slice_aesm K hK hc.model_measurable.2.2.1, interior_ae K, fst_ne_ae K,
    ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hsl hpI hp0 hpR hq hv
  have hpR' : p ∈ K.rect := hpR
  set f : Fin 3 → Fin 3 → ℝ → ℂ := fun a b θ => (frameMat θ (c.modelStrain (cylPoint p.1 θ p.2)) a b : ℂ)
    with hf
  set F : Fin 3 → Fin 3 → AddCircle (π - -π) → ℂ := fun a b => AddCircle.liftIoc (π - -π) (-π) (f a b)
    with hF
  have hfb : ∀ a b θ, ‖f a b θ‖ ≤ C0 := by
    intro a b θ
    simp only [hf, Complex.norm_real, Real.norm_eq_abs]
    exact (LowEntry.Internal.frameMat_bound θ _ a b).trans
      (hC0 _ (hd.solid_in_region (MeshFarRegularInternal.cyl_mem K hK p hpR' θ))).2.2.1
  have hFval : ∀ a b t, ∃ θ : ℝ, F a b t = f a b θ ∧
      ∀ a' b', F a' b' t = f a' b' θ := fun a b t =>
    ⟨((AddCircle.equivIoc (π - -π) (-π) t : Set.Ioc (-π) (-π + (π - -π))) : ℝ), rfl, fun _ _ => rfl⟩
  have hFm : ∀ a b, AEStronglyMeasurable (F a b) AddCircle.haarAddCircle := by
    intro a b
    have hset : Set.Ioc (-π) (-π + (π - -π)) = Set.Ioc (-π) π := by ring_nf
    have hL : MemLp (f a b) 2 (volume.restrict (Set.Ioc (-π) (-π + (π - -π)))) := by
      rw [hset]
      exact MemLp.of_bound (hsl a b) C0 (ae_of_all _ fun θ => hfb a b θ)
    exact hL.memLp_liftIoc.haarAddCircle.1
  have hFb : ∀ a b t, ‖F a b t‖ ≤ C0 := by
    intro a b t
    obtain ⟨θ, h, _⟩ := hFval a b t
    rw [h]; exact hfb a b θ
  have hreal : ∀ a b t, (F a b t).im = 0 := by
    intro a b t
    obtain ⟨θ, h, _⟩ := hFval a b t
    rw [h]; simp only [hf, Complex.ofReal_im]
  have hle : ∀ t (u : Fin 3 → ℝ), ∑ a, ∑ b, u a * (F a b t).re * u b ≤ S.strainBound p * ∑ a, u a ^ 2 := by
    intro t u
    obtain ⟨θ, _, h⟩ := hFval 0 0 t
    simp only [h, hf, Complex.ofReal_re]
    rw [frame_quad, ← frame_sq θ u]
    exact hd.scalars.strain_le p hpI hp0 θ _
  set ω : ℤ → Fin 3 → ℂ := fun n => curlComp (sharpGrad c K S x n p) with hω
  have hωs : ∀ a, Summable (fun n => ‖ω n a‖ ^ 2) := fun a =>
    Summable.of_nonneg_of_le (fun n => by positivity) (fun n => curl_sq_le _ a) (hq.mul_left 9)
  obtain ⟨A1, A2, A3⟩ := bandPairing_bound (T := π - -π) hm F hFm C0 hFb hreal (S.strainBound p) hle ω hωs
  have hW : ∀ n n', strainWave c K S x n n' p = -bandPairing (m := c.order) F ω n n' := by
    intro n n'
    unfold strainWave bandPairing CellScalars.strainMode
    simp only [mode_coeff]
    rfl
  simp_rw [hW, tsum_neg]
  refine ⟨fun n => (A1 n).neg, A2.neg, ?_⟩
  rw [Complex.neg_re]
  have e : ∑' n : ℤ, S.strainBound p * curlSq (sharpGrad c K S x n p) = S.strainBound p * ∑' n, ∑ a, ‖ω n a‖ ^ 2 := by
    rw [tsum_mul_left]
    rfl
  rw [e]
  linarith

end Breakdown.CellCert.CellAnalysis
