import Breakdown.FracCell.GivenAuxDefs
import Breakdown.FracCell.GivenAuxDualPartsRestOpen

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

namespace DualRestInternal

theorem weak_of_slopeBound {X : Space → Space} {C : NNReal} (hX : LipschitzWith C X) :
    IsWeakGradientOf X (fun y => fderiv ℝ X y) := by
  intro φ hφ j
  obtain ⟨D, hD⟩ := hφ.1.lipschitzWith_of_hasCompactSupport hφ.2 (by simp)
  have hd : ∀ᵐ y ∂(volume : Measure Space), DifferentiableAt ℝ X y := hX.ae_differentiableAt
  have hφd : ∀ y, DifferentiableAt ℝ φ y := fun y => (hφ.1.differentiable (by simp)) y
  have hmeas : AEStronglyMeasurable (fun y => fderiv ℝ X y (unitVector j)) volume :=
    ((measurable_fderiv ℝ X).apply_continuousLinearMap (unitVector j)).aestronglyMeasurable
  have hbd : ∀ y, ‖fderiv ℝ X y (unitVector j)‖ ≤ C := fun y => by
    calc ‖fderiv ℝ X y (unitVector j)‖ ≤ ‖fderiv ℝ X y‖ * ‖unitVector j‖ := (fderiv ℝ X y).le_opNorm _
      _ ≤ C * 1 := by
        gcongr
        · exact norm_fderiv_le_of_lipschitz ℝ hX
        · simp [unitVector]
      _ = C := mul_one _
  have hi1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • X y) :=
    (((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const).smul hX.continuous).integrable_of_hasCompactSupport
      (((hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun T : Space →L[ℝ] ℝ => T (unitVector j)) (by simp)).smul_right)
  have hi2 : Integrable (fun y => φ y • fderiv ℝ X y (unitVector j)) := by
    have hb : Integrable (fun y => (C : ℝ) * ‖φ y‖) :=
      (hφ.1.continuous.norm.integrable_of_hasCompactSupport hφ.2.norm).const_mul _
    refine hb.mono' (hφ.1.continuous.aestronglyMeasurable.smul hmeas) (Filter.Eventually.of_forall (fun y => ?_))
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hbd y) (norm_nonneg _)
  ext c
  rw [show (∫ y, fderiv ℝ φ y (unitVector j) • X y) c =
      (EuclideanSpace.proj c : Space →L[ℝ] ℝ) (∫ y, fderiv ℝ φ y (unitVector j) • X y) from rfl,
    show (-∫ y, φ y • fderiv ℝ X y (unitVector j)) c =
      (EuclideanSpace.proj c : Space →L[ℝ] ℝ) (-∫ y, φ y • fderiv ℝ X y (unitVector j)) from rfl,
    map_neg, ← (EuclideanSpace.proj c : Space →L[ℝ] ℝ).integral_comp_comm hi1,
    ← (EuclideanSpace.proj c : Space →L[ℝ] ℝ).integral_comp_comm hi2]
  have hXc : LipschitzWith C (fun y => X y c) := by
    have h1 := (EuclideanSpace.proj c : Space →L[ℝ] ℝ).lipschitz.comp hX
    have h2 : ‖(EuclideanSpace.proj c : Space →L[ℝ] ℝ)‖₊ ≤ 1 := by
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by
        simpa using PiLp.norm_apply_le v c)
    exact (h1.weaken (by simpa using mul_le_mul_of_nonneg_right h2 (zero_le (a := C))))
  have key := hXc.integral_lineDeriv_mul_eq (μ := (volume : Measure Space)) hD hφ.2 (unitVector j)
  have e1 : ∀ᵐ y ∂(volume : Measure Space), lineDeriv ℝ (fun z => X z c) y (unitVector j) * φ y =
      (EuclideanSpace.proj c : Space →L[ℝ] ℝ) (φ y • fderiv ℝ X y (unitVector j)) := by
    filter_upwards [hd] with y hy
    have hc : DifferentiableAt ℝ (fun z => X z c) y :=
      ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).differentiableAt).comp y hy
    rw [hc.lineDeriv_eq_fderiv]
    have := ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).hasFDerivAt.comp y hy.hasFDerivAt).fderiv
    rw [show (fun z => X z c) = (EuclideanSpace.proj c : Space →L[ℝ] ℝ) ∘ X from rfl, this]
    simp [mul_comm]
  have e2 : ∀ y, lineDeriv ℝ φ y (-unitVector j) * X y c =
      -(EuclideanSpace.proj c : Space →L[ℝ] ℝ) (fderiv ℝ φ y (unitVector j) • X y) := by
    intro y
    rw [(hφd y).lineDeriv_eq_fderiv]
    simp
  rw [integral_congr_ae e1, funext e2, integral_neg] at key
  linarith

theorem unit_norm (k : Fin 3) : ‖unitVector k‖ = 1 := by
  simp [unitVector]

theorem memLp_of_decay {E : Type*} [NormedAddCommGroup E] {g : Space → E}
    (hg : AEStronglyMeasurable g volume) (C : ℝ)
    (hb : ∀ᵐ y ∂volume, ‖g y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ))) : MemLp g 2 volume := by
  have hc : Continuous (fun y : Space => C * (1 + ‖y‖) ^ (-(2 : ℝ))) :=
    continuous_const.mul ((continuous_const.add continuous_norm).rpow_const
      (fun y => Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg y)).ne'))
  have h2 : MemLp (fun y : Space => C * (1 + ‖y‖) ^ (-(2 : ℝ))) 2 volume := by
    rw [memLp_two_iff_integrable_sq hc.aestronglyMeasurable]
    have hi : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) volume :=
      integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; norm_num)
    refine (hi.const_mul (C ^ 2)).congr (Filter.Eventually.of_forall fun y => ?_)
    have h1 : 0 < 1 + ‖y‖ := by positivity
    simp only
    rw [mul_pow, ← Real.rpow_natCast ((1 + ‖y‖) ^ (-(2 : ℝ))), ← Real.rpow_mul h1.le]
    norm_num
  refine h2.of_le hg ?_
  filter_upwards [hb] with y hy
  exact hy.trans ((le_abs_self _).trans_eq (Real.norm_eq_abs _).symm)

theorem decay_le_one (y : Space) : (1 + ‖y‖) ^ (-(2 : ℝ)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)

theorem slopeBound_of_decay {F : Space → Space} (h1 : ContDiff ℝ 1 F) {C : ℝ}
    (hC : ∀ y, ‖fderiv ℝ F y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ))) : ∃ K : NNReal, LipschitzWith K F := by
  refine ⟨C.toNNReal, lipschitzWith_of_nnnorm_fderiv_le (h1.differentiable one_ne_zero) fun y => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
  have h0 : 0 ≤ (1 + ‖y‖) ^ (-(2 : ℝ)) := by positivity
  calc ‖fderiv ℝ F y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := hC y
    _ ≤ max C 0 * (1 + ‖y‖) ^ (-(2 : ℝ)) := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left (decay_le_one y) (le_max_right _ _)
    _ = max C 0 := mul_one _

theorem gradMemLp_of_decay {F : Space → Space} {C : ℝ}
    (hC : ∀ y, ‖fderiv ℝ F y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ))) (k : Fin 3) :
    MemLp (fun y => fderiv ℝ F y (unitVector k)) 2 volume := by
  refine memLp_of_decay ((measurable_fderiv ℝ F).apply_continuousLinearMap (unitVector k)).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun y => ?_)
  calc ‖fderiv ℝ F y (unitVector k)‖ ≤ ‖fderiv ℝ F y‖ * ‖unitVector k‖ := (fderiv ℝ F y).le_opNorm _
    _ = ‖fderiv ℝ F y‖ := by rw [unit_norm, mul_one]
    _ ≤ _ := hC y

theorem second_of_slope {F : Space → Space} {K : NNReal} (hL : LipschitzWith K (fderiv ℝ F)) {C : ℝ}
    (hC : ∀ᵐ y ∂volume, ‖fderiv ℝ (fderiv ℝ F) y‖ ≤ C * (1 + ‖y‖) ^ (-(3 : ℝ))) :
    ∃ H : Fin 3 → Space → (Space →L[ℝ] Space),
      (∀ k, IsWeakGradientOf (fun y => fderiv ℝ F y (unitVector k)) (H k)) ∧
      (∀ k, LocallyIntegrable (fun y => H k y (unitVector k)) volume) ∧
      MemLp (fun y => ‖y‖ • ∑ k, H k y (unitVector k)) 2 volume := by
  have hg : ∀ k : Fin 3, LipschitzWith (‖ContinuousLinearMap.apply ℝ Space (unitVector k)‖₊ * K)
      (fun y => fderiv ℝ F y (unitVector k)) :=
    fun k => (ContinuousLinearMap.apply ℝ Space (unitVector k)).lipschitz.comp hL
  refine ⟨fun k y => fderiv ℝ (fun y => fderiv ℝ F y (unitVector k)) y, fun k => weak_of_slopeBound (hg k),
    fun k => ?_, ?_⟩
  · refine (memLp_top_of_bound (((measurable_fderiv ℝ _).apply_continuousLinearMap
      (unitVector k)).aestronglyMeasurable) ((‖ContinuousLinearMap.apply ℝ Space (unitVector k)‖₊ * K : NNReal) : ℝ)
      (Filter.Eventually.of_forall fun y => ?_)).locallyIntegrable le_top
    calc ‖fderiv ℝ (fun y => fderiv ℝ F y (unitVector k)) y (unitVector k)‖ ≤
        ‖fderiv ℝ (fun y => fderiv ℝ F y (unitVector k)) y‖ * ‖unitVector k‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (fun y => fderiv ℝ F y (unitVector k)) y‖ := by rw [unit_norm, mul_one]
      _ ≤ _ := norm_fderiv_le_of_lipschitz ℝ (hg k)
  · have hd := hL.ae_differentiableAt (μ := (volume : Measure Space))
    refine memLp_of_decay ?_ (3 * C) ?_
    · exact continuous_norm.aestronglyMeasurable.smul (Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
        ((measurable_fderiv ℝ _).apply_continuousLinearMap (unitVector k)).aestronglyMeasurable)
    filter_upwards [hd, hC] with y hy hy2
    have hk : ∀ k : Fin 3, ‖fderiv ℝ (fun y => fderiv ℝ F y (unitVector k)) y (unitVector k)‖ ≤
        C * (1 + ‖y‖) ^ (-(3 : ℝ)) := by
      intro k
      have he : fderiv ℝ (fun y => fderiv ℝ F y (unitVector k)) y =
          (ContinuousLinearMap.apply ℝ Space (unitVector k)).comp (fderiv ℝ (fderiv ℝ F) y) :=
        ((ContinuousLinearMap.apply ℝ Space (unitVector k)).hasFDerivAt.comp y hy.hasFDerivAt).fderiv
      rw [he]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
      calc ‖fderiv ℝ (fderiv ℝ F) y (unitVector k) (unitVector k)‖ ≤
          ‖fderiv ℝ (fderiv ℝ F) y (unitVector k)‖ * ‖unitVector k‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ (fderiv ℝ F) y‖ * ‖unitVector k‖ * ‖unitVector k‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ (fderiv ℝ F) y‖ := by rw [unit_norm, mul_one, mul_one]
        _ ≤ _ := hy2
    have h1 : 0 < 1 + ‖y‖ := by positivity
    have hC0 : 0 ≤ C * (1 + ‖y‖) ^ (-(3 : ℝ)) := (norm_nonneg _).trans (hk 0)
    have hs : ‖∑ k, fderiv ℝ (fun y => fderiv ℝ F y (unitVector k)) y (unitVector k)‖ ≤
        3 * (C * (1 + ‖y‖) ^ (-(3 : ℝ))) := by
      calc _ ≤ ∑ k : Fin 3, ‖fderiv ℝ (fun y => fderiv ℝ F y (unitVector k)) y (unitVector k)‖ := norm_sum_le _ _
        _ ≤ ∑ k : Fin 3, C * (1 + ‖y‖) ^ (-(3 : ℝ)) := Finset.sum_le_sum fun k _ => hk k
        _ = _ := by simp
    rw [norm_smul, norm_norm]
    calc ‖y‖ * ‖∑ k, fderiv ℝ (fun y => fderiv ℝ F y (unitVector k)) y (unitVector k)‖ ≤
        (1 + ‖y‖) * (3 * (C * (1 + ‖y‖) ^ (-(3 : ℝ)))) :=
          mul_le_mul (by linarith) hs (norm_nonneg _) h1.le
      _ = 3 * C * ((1 + ‖y‖) ^ (1 : ℝ) * (1 + ‖y‖) ^ (-(3 : ℝ))) := by rw [Real.rpow_one]; ring
      _ = 3 * C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
          rw [← Real.rpow_add h1]
          norm_num

end DualRestInternal

open DualRestInternal

namespace DualRestInternal

def lin (w : ℂ) (i : Fin 3) : ℂ →L[ℝ] Space :=
  (Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ w)).smulRight (unitVector i)

theorem lin_apply (w z : ℂ) (i : Fin 3) : lin w i z = (w * z).re • unitVector i := by
  simp [lin]

theorem atom_fun (P : ChartParams) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline) (w : ℂ) (i : Fin 3) :
    (fun y => (w * ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y).re • unitVector i) =
      fun y => lin w i (((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) := by
  funext y
  rw [lin_apply, mul_assoc]

theorem li_comp (L : ℂ →L[ℝ] Space) {f : Space → ℂ} (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun y => L (f y)) volume := fun x => by
  obtain ⟨s, hs, hi⟩ := hf x
  exact ⟨s, hs, L.integrable_comp hi⟩

theorem tr_fderiv (L : ℂ →L[ℝ] Space) {u : Space → ℂ} {K : NNReal} (hu : LipschitzWith K u) :
    ∀ᵐ y ∂volume, fderiv ℝ (fun y => L (u y)) y = L.comp (fderiv ℝ u y) := by
  filter_upwards [hu.ae_differentiableAt (μ := (volume : Measure Space))] with y hy
  exact (L.hasFDerivAt.comp y hy.hasFDerivAt).fderiv

theorem tr_grad (L : ℂ →L[ℝ] Space) {u : Space → ℂ} {K : NNReal} (hu : LipschitzWith K u) {C : ℝ}
    (hC : ∀ᵐ y ∂volume, ‖fderiv ℝ u y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ))) (k : Fin 3) :
    MemLp (fun y => fderiv ℝ (fun y => L (u y)) y (unitVector k)) 2 volume := by
  refine memLp_of_decay ((measurable_fderiv ℝ _).apply_continuousLinearMap (unitVector k)).aestronglyMeasurable
    (‖L‖ * C) ?_
  filter_upwards [tr_fderiv L hu, hC] with y h1 h2
  rw [h1, ContinuousLinearMap.comp_apply]
  calc ‖L (fderiv ℝ u y (unitVector k))‖ ≤ ‖L‖ * ‖fderiv ℝ u y (unitVector k)‖ := L.le_opNorm _
    _ ≤ ‖L‖ * (‖fderiv ℝ u y‖ * ‖unitVector k‖) := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖L‖ * ‖fderiv ℝ u y‖ := by rw [unit_norm, mul_one]
    _ ≤ ‖L‖ * (C * (1 + ‖y‖) ^ (-(2 : ℝ))) := by gcongr
    _ = ‖L‖ * C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by ring

theorem tr_second (L : ℂ →L[ℝ] Space) {u : Space → ℂ} {K : NNReal} (hu : LipschitzWith K u)
    (H : Fin 3 → Space → (Space →L[ℝ] ℂ))
    (hw : ∀ k : Fin 3, ∀ φ : Space → ℝ, IsTestScalar φ → ∀ i : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector i) • fderiv ℝ u y (unitVector k) = -∫ y, φ y • H k y (unitVector i))
    (hl : ∀ k i : Fin 3, LocallyIntegrable (fun y => H k y (unitVector i)) volume)
    (hm : MemLp (fun y => ‖y‖ • ∑ k, H k y (unitVector k)) 2 volume) :
    ∃ H' : Fin 3 → Space → (Space →L[ℝ] Space),
      (∀ k, IsWeakGradientOf (fun y => fderiv ℝ (fun y => L (u y)) y (unitVector k)) (H' k)) ∧
      (∀ k, LocallyIntegrable (fun y => H' k y (unitVector k)) volume) ∧
      MemLp (fun y => ‖y‖ • ∑ k, H' k y (unitVector k)) 2 volume := by
  refine ⟨fun k y => L.comp (H k y), fun k φ hφ i => ?_, fun k => li_comp L (hl k k), ?_⟩
  · have hg : LocallyIntegrable (fun y => fderiv ℝ u y (unitVector k)) volume := by
      refine (memLp_top_of_bound ((measurable_fderiv ℝ u).apply_continuousLinearMap
        (unitVector k)).aestronglyMeasurable (K : ℝ) (Filter.Eventually.of_forall fun y => ?_)).locallyIntegrable le_top
      calc ‖fderiv ℝ u y (unitVector k)‖ ≤ ‖fderiv ℝ u y‖ * ‖unitVector k‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ u y‖ := by rw [unit_norm, mul_one]
        _ ≤ K := norm_fderiv_le_of_lipschitz ℝ hu
    have hcφ : Continuous (fun y => fderiv ℝ φ y (unitVector i)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hsφ : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector i)) :=
      (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun T : Space →L[ℝ] ℝ => T (unitVector i)) (by simp)
    have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector i) • fderiv ℝ u y (unitVector k)) volume :=
      hg.integrable_smul_left_of_hasCompactSupport hcφ hsφ
    have i2 : Integrable (fun y => φ y • H k y (unitVector i)) volume :=
      (hl k i).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    have e1 : ∫ y, fderiv ℝ φ y (unitVector i) • fderiv ℝ (fun y => L (u y)) y (unitVector k) =
        ∫ y, L (fderiv ℝ φ y (unitVector i) • fderiv ℝ u y (unitVector k)) := by
      refine integral_congr_ae ?_
      filter_upwards [tr_fderiv L hu] with y hy
      rw [hy, ContinuousLinearMap.comp_apply, map_smul]
    have e2 : ∫ y, φ y • (L.comp (H k y)) (unitVector i) = ∫ y, L (φ y • H k y (unitVector i)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [ContinuousLinearMap.comp_apply, map_smul]
    rw [e1, e2, L.integral_comp_comm i1, L.integral_comp_comm i2, hw k φ hφ i, map_neg]
  · have e : (fun y => ‖y‖ • ∑ k, (L.comp (H k y)) (unitVector k)) =
        fun y => L (‖y‖ • ∑ k, H k y (unitVector k)) := by
      funext y
      simp only [ContinuousLinearMap.comp_apply, map_smul, map_sum]
    rw [e]
    exact L.comp_memLp' hm

end DualRestInternal

namespace DualRestInternal

theorem comp_fderiv' {Φ : Space → Space} (hΦ : ContDiff ℝ ∞ Φ) (c : Fin 3) (y v : Space) :
    fderiv ℝ (fun z => Φ z c) y v = fderiv ℝ Φ y v c := by
  have h := ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).hasFDerivAt).comp y
    ((hΦ.differentiable (by simp)) y).hasFDerivAt
  rw [show (fun z => Φ z c) = (EuclideanSpace.proj c : Space →L[ℝ] ℝ) ∘ Φ from rfl, h.fderiv]
  rfl

theorem comp_test' {Φ : Space → Space} (hΦ : IsTestVectorField Φ) (c : Fin 3) :
    IsTestScalar (fun z => Φ z c) := by
  refine ⟨(EuclideanSpace.proj c : Space →L[ℝ] ℝ).contDiff.comp hΦ.1, ?_⟩
  exact hΦ.2.comp_left (g := fun w : Space => w c) (by simp)

theorem radial_eq' (y : Space) : ofComponents (radialVec y) = ‖y‖⁻¹ • y := by
  ext k
  have e : ofComponents (radialVec y) k = radialVec y k := by
    fin_cases k <;> simp [ofComponents]
  rw [e, radialVec, PiLp.smul_apply, smul_eq_mul, div_eq_inv_mul]

theorem inner_unit (x : Space) (i : Fin 3) : inner ℝ x (unitVector i) = x i := by
  simp [unitVector, EuclideanSpace.inner_single_right]

theorem entry_radial (G : Space →L[ℝ] Space) (v x : Space) :
    entryInner G ((innerSL ℝ v).smulRight x) = inner ℝ (G v) x := by
  have hv : v = ∑ k : Fin 3, v k • unitVector k := by
    ext c
    fin_cases c <;> simp [unitVector, Fin.sum_univ_three]
  unfold entryInner
  have hG : G v = ∑ k : Fin 3, v k • G (unitVector k) := by
    conv_lhs => rw [hv]
    simp only [map_sum, map_smul]
  rw [hG, sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, real_inner_smul_left, inner_smul_right, inner_unit]

end DualRestInternal

open DualRestInternal

theorem atomTerm_boundedSlope (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S j) (hM : j = 0 → M.natAbs = a) (w : ℂ) (i : Fin 3) :
    ∃ C : NNReal, LipschitzWith C (fun y => (w * ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y).re • unitVector i) := by
  obtain ⟨K, hK⟩ := atomScalar_slope P hP j a M β S ha hS hM
  rw [atom_fun]
  exact ⟨_, (lin w i).lipschitz.comp hK⟩

theorem atomTerm_gradMemLpTwo (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S j) (hM : j = 0 → M.natAbs = a) (w : ℂ) (i : Fin 3) (k : Fin 3) :
    MemLp (fun y => fderiv ℝ (fun y => (w * ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y).re • unitVector i) y (unitVector k)) 2 volume := by
  obtain ⟨K, hK⟩ := atomScalar_slope P hP j a M β S ha hS hM
  obtain ⟨C, hC⟩ := atomScalar_gradDecay P hP j a M β S ha hS hM
  rw [atom_fun]
  exact tr_grad (lin w i) hK hC k

theorem atomTerm_second (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S j) (hM : j = 0 → M.natAbs = a) (w : ℂ) (i : Fin 3) :
    ∃ H : Fin 3 → Space → (Space →L[ℝ] Space),
      (∀ k, IsWeakGradientOf (fun y => fderiv ℝ (fun y => (w * ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y).re • unitVector i) y (unitVector k)) (H k)) ∧
      (∀ k, LocallyIntegrable (fun y => H k y (unitVector k)) volume) ∧
      MemLp (fun y => ‖y‖ • ∑ k, H k y (unitVector k)) 2 volume := by
  obtain ⟨K, hK⟩ := atomScalar_slope P hP j a M β S ha hS hM
  obtain ⟨H, hw, hl, hm⟩ := atomScalar_second P hP j a M β S ha hS hM
  rw [atom_fun]
  exact tr_second (lin w i) hK H hw hl hm

theorem fieldMode_boundedSlope (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (n : ℤ) (hn : n ∈ D.modes) (β : ℝ) :
    ∃ C : NNReal, LipschitzWith C (fun y => ofComponents (fun i => ((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re)) := by
  obtain ⟨C, hC⟩ := fieldMode_gradDecay P hP D hD n hn β
  exact slopeBound_of_decay (fieldMode_contDiffOne P hP D hD n hn β) hC

theorem fieldMode_memLpTwo (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (n : ℤ) (hn : n ∈ D.modes) (β : ℝ) :
    MemLp (fun y => ofComponents (fun i => ((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re)) 2 volume := by
  obtain ⟨C, hC⟩ := fieldMode_decay P hP D hD n hn β
  exact memLp_of_decay (fieldMode_contDiffOne P hP D hD n hn β).continuous.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem fieldMode_gradMemLpTwo (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (n : ℤ) (hn : n ∈ D.modes) (β : ℝ) (k : Fin 3) :
    MemLp (fun y => fderiv ℝ (fun y => ofComponents (fun i => ((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re)) y (unitVector k)) 2 volume := by
  obtain ⟨C, hC⟩ := fieldMode_gradDecay P hP D hD n hn β
  exact gradMemLp_of_decay hC k

theorem fieldMode_second (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (n : ℤ) (hn : n ∈ D.modes) (β : ℝ) :
    ∃ H : Fin 3 → Space → (Space →L[ℝ] Space),
      (∀ k, IsWeakGradientOf (fun y => fderiv ℝ (fun y => ofComponents (fun i => ((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re)) y (unitVector k)) (H k)) ∧
      (∀ k, LocallyIntegrable (fun y => H k y (unitVector k)) volume) ∧
      MemLp (fun y => ‖y‖ • ∑ k, H k y (unitVector k)) 2 volume := by
  obtain ⟨K, hK⟩ := fieldMode_fderivSlope P hP D hD n hn β
  obtain ⟨C, hC⟩ := fieldMode_secondDecay P hP D hD n hn β
  exact second_of_slope hK hC

theorem fluxTerm_radialDiv (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsFluxSpline S) (w : ℂ) (i : Fin 3) :
    ∃ D : Space → Space, CellCert.Reduction.IsWeakMatrixDivergenceOf (fun y => (innerSL ℝ (ofComponents (radialVec y))).smulRight
      ((w * ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y).re • unitVector i)) D ∧
      LocallyIntegrable D volume ∧ MemLp (fun y => ‖y‖ • D y) 2 volume := by
  obtain ⟨d, hd, hdl, hdm⟩ := fluxScalar_radialDiv P hP j a M β S hS
  refine ⟨fun y => lin w i (d y), fun Φ hΦ => ?_, li_comp _ hdl, ?_⟩
  · let L1 : ℂ →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ w)
    have hL1 : ∀ z, L1 z = (w * z).re := fun z => by simp [L1]
    have hφ : IsTestScalar (fun z => Φ z i) := comp_test' hΦ i
    obtain ⟨i1, e⟩ := hd _ hφ
    have i2 : Integrable (fun y => (fun z => Φ z i) y • d y) volume :=
      hdl.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    have p1 : ∀ y, entryInner (fderiv ℝ Φ y) ((innerSL ℝ (ofComponents (radialVec y))).smulRight
        ((w * ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y).re • unitVector i)) =
        L1 (fderiv ℝ (fun z => Φ z i) y (‖y‖⁻¹ • y) • (((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y)) := by
      intro y
      rw [entry_radial, radial_eq', hL1, comp_fderiv' hΦ.1, inner_smul_right, inner_unit, Complex.real_smul,
        mul_left_comm, Complex.re_ofReal_mul, mul_assoc w]
      ring
    have p2 : ∀ y, inner ℝ (lin w i (d y)) (Φ y) = L1 ((fun z => Φ z i) y • d y) := by
      intro y
      rw [lin_apply, real_inner_smul_left, real_inner_comm, inner_unit, hL1, Complex.real_smul, mul_left_comm,
        Complex.re_ofReal_mul]
      simp only [Complex.mul_re]
      ring
    simp only [p1, p2]
    rw [L1.integral_comp_comm i1, L1.integral_comp_comm i2, e, map_neg]
  · have e : (fun y => ‖y‖ • lin w i (d y)) = fun y => lin w i (‖y‖ • d y) := by
      funext y
      rw [map_smul]
    rw [e]
    exact (lin w i).comp_memLp' hdm

end GivenFields

end CellCert

end Breakdown
