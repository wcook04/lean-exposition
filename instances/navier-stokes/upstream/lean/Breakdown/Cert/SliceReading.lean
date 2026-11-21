import Breakdown.Cert.Nodes
import Breakdown.Cert.ReadingExists

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Breakdown.Cert

open Freq Internal.SliceFields Internal.ReadingExists

namespace Internal.SliceReading

theorem norm_gradField_sq_le (p : Fin 3 → Space → Space) (y : Space) :
    ‖gradField p y‖ ^ 2 ≤ ∑ j : Fin 3, ‖p j y‖ ^ 2 := by
  have h0 : 0 ≤ ∑ j : Fin 3, ‖p j y‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : ‖gradField p y‖ ≤ Real.sqrt (∑ j : Fin 3, ‖p j y‖ ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
    rw [gradField_apply]
    have h1 : ‖∑ j : Fin 3, v j • p j y‖ ≤ ∑ j : Fin 3, |v j| * ‖p j y‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by rw [norm_smul, Real.norm_eq_abs])
    have h2 := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 3)) (fun j => |v j|)
      (fun j => ‖p j y‖)
    have h3 : Real.sqrt (∑ j : Fin 3, |v j| ^ 2) = ‖v‖ := by
      rw [EuclideanSpace.norm_eq v]
      simp only [Real.norm_eq_abs]
    rw [h3] at h2
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ = _ := mul_comm _ _
  calc ‖gradField p y‖ ^ 2 ≤ Real.sqrt (∑ j : Fin 3, ‖p j y‖ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = _ := Real.sq_sqrt h0

theorem lintegral_sixth_eq (f : L6R) :
    ∫⁻ y, ENNReal.ofReal (‖(f : Space → Space) y‖ ^ 6) = ENNReal.ofReal (‖f‖ ^ 6) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := (f : Space → Space)) (μ := volume)
    (p := (6 : NNReal)) (by norm_num)
  rw [Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
  have e6 : ((6 : NNReal) : ℝ≥0∞) = 6 := rfl
  have r6 : ((6 : NNReal) : ℝ) = ((6 : ℕ) : ℝ) := by norm_num
  rw [e6, r6, ENNReal.rpow_natCast] at h
  rw [h]
  refine lintegral_congr fun y => ?_
  rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem isWeakGradient_zero : IsWeakGradient (0 : Space → Space) (0 : Space → (Space →L[ℝ] Space)) :=
  ⟨locallyIntegrable_zero, locallyIntegrable_zero, fun φ _ i => by simp⟩

def IsGoodTime (u : XX) (Y : ℝ → ℝ) (v : ℝ → Space → Space) (g : Fin 3 → ℝ → Space → Space)
    (h : Fin 3 → Fin 3 → ℝ → Space → Space) (σ : ℝ) : Prop :=
  v σ =ᵐ[volume] ((velocity ∘L gradPart) (u (σ : TimeCircle)) : Space → Space) ∧
    (∀ j, g j σ =ᵐ[volume] ((partialX j ∘L gradPart) (u (σ : TimeCircle)) : Space → Space)) ∧
    (∀ i j, h i j σ =ᵐ[volume]
      ((partialX i ∘L derivX j ∘L secondPart) (u (σ : TimeCircle)) : Space → Space)) ∧
    Y σ = ‖gradPart (u (σ : TimeCircle))‖ ^ 2


def IsGoodAt (u : XX) (a : ℝ) (w : Space → Space) (g : Fin 3 → Space → Space)
    (h : Fin 3 → Fin 3 → Space → Space) (t : TimeCircle) : Prop :=
  w =ᵐ[volume] ((velocity ∘L gradPart) (u t) : Space → Space) ∧
    (∀ j, g j =ᵐ[volume] ((partialX j ∘L gradPart) (u t) : Space → Space)) ∧
    (∀ i j, h i j =ᵐ[volume] ((partialX i ∘L derivX j ∘L secondPart) (u t) : Space → Space)) ∧
    a = ‖gradPart (u t)‖ ^ 2

theorem isGoodTime_iff (u : XX) (Y : ℝ → ℝ) (v : ℝ → Space → Space) (g : Fin 3 → ℝ → Space → Space)
    (h : Fin 3 → Fin 3 → ℝ → Space → Space) (σ : ℝ) :
    IsGoodTime u Y v g h σ ↔
      IsGoodAt u (Y σ) (v σ) (fun j => g j σ) (fun i j => h i j σ) (σ : TimeCircle) := Iff.rfl

theorem isGoodTime_add_one {u : XX} {Y : ℝ → ℝ} {v : ℝ → Space → Space}
    {g : Fin 3 → ℝ → Space → Space} {h : Fin 3 → Fin 3 → ℝ → Space → Space}
    (hY : ∀ σ, Y (σ + 1) = Y σ) (hv : IsTimePeriodic v) (hg : ∀ j, IsTimePeriodic (g j))
    (hh : ∀ i j, IsTimePeriodic (h i j)) (σ : ℝ) :
    IsGoodTime u Y v g h (σ + 1) ↔ IsGoodTime u Y v g h σ := by
  have e1 : v (σ + 1) = v σ := funext (hv σ)
  have e2 : (fun j => g j (σ + 1)) = fun j => g j σ := funext fun j => funext (hg j σ)
  have e3 : (fun i j => h i j (σ + 1)) = fun i j => h i j σ :=
    funext fun i => funext fun j => funext (hh i j σ)
  rw [isGoodTime_iff, isGoodTime_iff, e1, e2, e3, hY σ]
  exact (congrArg (IsGoodAt u (Y σ) (v σ) (fun j => g j σ) (fun i j => h i j σ))
    (AddCircle.coe_add_period (1 : ℝ) σ)).to_iff

open scoped Classical in
def goodVel (u : XX) (Y : ℝ → ℝ) (v : ℝ → Space → Space) (g : Fin 3 → ℝ → Space → Space)
    (h : Fin 3 → Fin 3 → ℝ → Space → Space) : ℝ → Space → Space :=
  fun σ y => if IsGoodTime u Y v g h σ then v σ y else 0

open scoped Classical in
def goodGrad (u : XX) (Y : ℝ → ℝ) (v : ℝ → Space → Space) (g : Fin 3 → ℝ → Space → Space)
    (h : Fin 3 → Fin 3 → ℝ → Space → Space) : ℝ → Space → (Space →L[ℝ] Space) :=
  fun σ y => if IsGoodTime u Y v g h σ then gradField (fun j => g j σ) y else 0

section

variable {u : XX} {Y : ℝ → ℝ} {v : ℝ → Space → Space} {g : Fin 3 → ℝ → Space → Space}
  {h : Fin 3 → Fin 3 → ℝ → Space → Space} {σ : ℝ}

theorem goodVel_of_good (hσ : IsGoodTime u Y v g h σ) : goodVel u Y v g h σ = v σ := by
  funext y
  simp only [goodVel, if_pos hσ]

theorem goodVel_of_not (hσ : ¬ IsGoodTime u Y v g h σ) : goodVel u Y v g h σ = 0 := by
  funext y
  simp only [goodVel, if_neg hσ, Pi.zero_apply]

theorem goodGrad_of_good (hσ : IsGoodTime u Y v g h σ) :
    goodGrad u Y v g h σ = gradField (fun j => g j σ) := by
  funext y
  simp only [goodGrad, if_pos hσ]

theorem goodGrad_of_not (hσ : ¬ IsGoodTime u Y v g h σ) : goodGrad u Y v g h σ = 0 := by
  funext y
  simp only [goodGrad, if_neg hσ, Pi.zero_apply]

theorem good_slice (hgc : GraphClosedHolds) (hσ : IsGoodTime u Y v g h σ) :
    IsWeakGradient (v σ) (gradField fun j => g j σ) ∧
      (∀ j : Fin 3, IsWeakGradient (fun y => gradField (fun i => g i σ) y (unitVector j))
        (fun y => (secondDerivField (fun i j => h i j σ) y).flip (unitVector j))) ∧
      (fun y => secondDerivTrace (secondDerivField (fun i j => h i j σ) y)) =ᵐ[volume]
        (fun y => -(toPhysH (secondPart (u (σ : TimeCircle))) : Space → Space) y) ∧
      ∫⁻ y, ENNReal.ofReal (‖secondDerivField (fun i j => h i j σ) y‖ ^ 2) ≤
        ENNReal.ofReal (‖secondPart (u (σ : TimeCircle))‖ ^ 2) :=
  slice_reading _ _ (hgc _) _ _ _ hσ.1 hσ.2.1 hσ.2.2.1


theorem divergence_of_good (hσ : IsGoodTime u Y v g h σ) :
    ∀ᵐ y, ∑ i : Fin 3, (gradField (fun j => g j σ) y (unitVector i)) i = 0 := by
  have hB : ∀ j, g j σ =ᵐ[volume] (partialX j (gradPart (u (σ : TimeCircle))) : Space → Space) :=
    fun j => by simpa only [ContinuousLinearMap.comp_apply] using hσ.2.1 j
  filter_upwards [partialX_divergence (gradPart (u (σ : TimeCircle))), ae_all_iff.2 hB]
    with y hy hgy
  simp only [gradField_unit, hgy]
  exact hy

theorem sixth_le_of_ae (x : X) (w : Space → Space)
    (hA : w =ᵐ[volume] (velocity x : Space → Space)) {K : ℝ} (hx : ‖x‖ ^ 2 ≤ K) :
    ∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 6) ≤
      ENNReal.ofReal ((‖(velocity : X →L[ℝ] L6R)‖ ^ 2 * K) ^ 3) := by
  have e : ∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 6) =
      ∫⁻ y, ENNReal.ofReal (‖(velocity x : Space → Space) y‖ ^ 6) :=
    lintegral_congr_ae (hA.mono fun y hy => by simp only [hy])
  rw [e, lintegral_sixth_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := (velocity : X →L[ℝ] L6R).le_opNorm x
  calc ‖velocity x‖ ^ 6 ≤ (‖(velocity : X →L[ℝ] L6R)‖ * ‖x‖) ^ 6 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 6
    _ = (‖(velocity : X →L[ℝ] L6R)‖ ^ 2 * ‖x‖ ^ 2) ^ 3 := by ring
    _ ≤ (‖(velocity : X →L[ℝ] L6R)‖ ^ 2 * K) ^ 3 :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hx (by positivity)) 3

theorem grad_le_of_ae (x : X) (p : Fin 3 → Space → Space)
    (hB : ∀ j, p j =ᵐ[volume] (partialX j x : Space → Space)) :
    ∫⁻ y, ENNReal.ofReal (‖gradField p y‖ ^ 2) ≤ ENNReal.ofReal (‖x‖ ^ 2) := by
  have hint : Integrable (fun y => ∑ j : Fin 3, ‖(partialX j x : Space → Space) y‖ ^ 2) volume :=
    integrable_finsetSum _ fun j _ => integrable_norm_sq_L2R _
  have hval : ∫ y, ∑ j : Fin 3, ‖(partialX j x : Space → Space) y‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [integral_finsetSum _ fun j _ => integrable_norm_sq_L2R _]
    simp only [integral_norm_sq_L2R]
    exact sum_norm_partialX_sq _
  have hae : (fun y => ENNReal.ofReal (∑ j : Fin 3, ‖p j y‖ ^ 2)) =ᵐ[volume]
      fun y => ENNReal.ofReal (∑ j : Fin 3, ‖(partialX j x : Space → Space) y‖ ^ 2) := by
    filter_upwards [ae_all_iff.2 hB] with y hy
    simp only [hy]
  calc ∫⁻ y, ENNReal.ofReal (‖gradField p y‖ ^ 2)
      ≤ ∫⁻ y, ENNReal.ofReal (∑ j : Fin 3, ‖p j y‖ ^ 2) :=
        lintegral_mono fun y => ENNReal.ofReal_le_ofReal (norm_gradField_sq_le _ y)
    _ = ∫⁻ y, ENNReal.ofReal (∑ j : Fin 3, ‖(partialX j x : Space → Space) y‖ ^ 2) :=
        lintegral_congr_ae hae
    _ = ENNReal.ofReal (∫ y, ∑ j : Fin 3, ‖(partialX j x : Space → Space) y‖ ^ 2) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y =>
          Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
    _ = _ := by rw [hval]

theorem sixth_le_of_good (hσ : IsGoodTime u Y v g h σ) {K : ℝ}
    (hx : ‖gradPart (u (σ : TimeCircle))‖ ^ 2 ≤ K) :
    ∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6) ≤
      ENNReal.ofReal ((‖(velocity : X →L[ℝ] L6R)‖ ^ 2 * K) ^ 3) :=
  sixth_le_of_ae _ _ (by simpa only [ContinuousLinearMap.comp_apply] using hσ.1) hx

theorem grad_le_of_good (hσ : IsGoodTime u Y v g h σ) :
    ∫⁻ y, ENNReal.ofReal (‖gradField (fun j => g j σ) y‖ ^ 2) ≤
      ENNReal.ofReal (‖gradPart (u (σ : TimeCircle))‖ ^ 2) :=
  grad_le_of_ae _ _ fun j => by simpa only [ContinuousLinearMap.comp_apply] using hσ.2.1 j

theorem secondDeriv_lt_top_of_good (hgc : GraphClosedHolds) (hgood : ∀ᵐ σ : ℝ, IsGoodTime u Y v g h σ) :
    periodLIntegral (fun σ y => ‖secondDerivField (fun i j => h i j σ) y‖ ^ 2) < ⊤ := by
  have hmeas : AEMeasurable (fun t : TimeCircle => ENNReal.ofReal (‖secondPart (u t)‖ ^ 2)) volume :=
    ((secondPart.continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable u)).norm.aemeasurable.pow_const 2).ennreal_ofReal
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := ‖secondCLM u‖ ^ 2))
  unfold periodLIntegral
  calc ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖secondDerivField (fun i j => h i j σ) y‖ ^ 2)
      ≤ ∫⁻ σ in Icc (0 : ℝ) 1, ENNReal.ofReal (‖secondPart (u (σ : TimeCircle))‖ ^ 2) := by
        refine lintegral_mono_ae (ae_restrict_of_ae ?_)
        filter_upwards [hgood] with σ hσ
        exact (good_slice hgc hσ).2.2.2
    _ = ∫⁻ t, ENNReal.ofReal (‖secondPart (u t)‖ ^ 2) := lintegral_Icc_coe _ hmeas
    _ = ENNReal.ofReal (‖secondCLM u‖ ^ 2) := (ofReal_norm_compLpL_sq secondPart u).symm

end



theorem exists_everywhere_reading (hgc : GraphClosedHolds) (u : XX) (Y : ℝ → ℝ) (hYc : Continuous Y)
    (hYp : ∀ σ, Y (σ + 1) = Y σ)
    (hYae : ∀ᵐ σ : ℝ, Y σ = ‖gradPart (u (σ : TimeCircle))‖ ^ 2) :
    ∃ v G H, IsReadingOf u v G H ∧
    (∀ σ, IsWeakGradient (v σ) (G σ)) ∧ (∀ σ, ∀ᵐ y, ∑ i : Fin 3, (G σ y (unitVector i)) i = 0) ∧
    (∃ B, ∀ σ, ∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6) ≤ ENNReal.ofReal B ∧
      ∫⁻ y, ENNReal.ofReal (‖G σ y‖ ^ 2) ≤ ENNReal.ofReal B) ∧
    periodLIntegral (fun σ y => ‖H σ y‖ ^ 2) < ⊤ := by
  obtain ⟨v₀, hvm, hvp, eA⟩ := exists_slice_representative (velocity ∘L gradPart) u
  have hg := fun j : Fin 3 => exists_slice_representative (partialX j ∘L gradPart) u
  choose g hgm hgp eB using hg
  have hh := fun i j : Fin 3 => exists_slice_representative (partialX i ∘L derivX j ∘L secondPart) u
  choose h hhm hhp eC using hh
  have hgood : ∀ᵐ σ : ℝ, IsGoodTime u Y v₀ g h σ := by
    filter_upwards [eA, ae_all_iff.2 eB, ae_all_iff.2 fun i => ae_all_iff.2 (eC i), hYae]
      with σ hA hB hC hD
    exact ⟨hA, hB, hC, hD⟩
  have hper : ∀ σ, IsGoodTime u Y v₀ g h (σ + 1) ↔ IsGoodTime u Y v₀ g h σ :=
    isGoodTime_add_one hYp hvp hgp hhp
  have hv0p : ∀ σ, v₀ (σ + 1) = v₀ σ := fun σ => funext (hvp σ)
  have hg0p : ∀ σ j, g j (σ + 1) = g j σ := fun σ j => funext (hgp j σ)
  have hh0p : ∀ σ i j, h i j (σ + 1) = h i j σ := fun σ i j => funext (hhp i j σ)
  obtain ⟨v, hv⟩ : ∃ v, v = goodVel u Y v₀ g h := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = goodGrad u Y v₀ g h := ⟨_, rfl⟩
  have hvg : ∀ σ, IsGoodTime u Y v₀ g h σ → v σ = v₀ σ := fun σ hσ => hv ▸ goodVel_of_good hσ
  have hvb : ∀ σ, ¬ IsGoodTime u Y v₀ g h σ → v σ = 0 := fun σ hσ => hv ▸ goodVel_of_not hσ
  have hGg : ∀ σ, IsGoodTime u Y v₀ g h σ → G σ = gradField (fun j => g j σ) := fun σ hσ =>
    hG ▸ goodGrad_of_good hσ
  have hGb : ∀ σ, ¬ IsGoodTime u Y v₀ g h σ → G σ = 0 := fun σ hσ => hG ▸ goodGrad_of_not hσ
  have hjoint : ∀ᵐ z : ℝ × Space, IsGoodTime u Y v₀ g h z.1 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.ae hgood
  have hslice : ∀ σ, IsGoodTime u Y v₀ g h σ → _ := fun σ hσ => good_slice hgc hσ
  obtain ⟨M, hM⟩ := (isBounded_iff_bddBelow_bddAbove.1
    (Function.Periodic.isBounded_of_continuous (f := Y) (c := 1) hYp one_ne_zero hYc)).2
  have hYM : ∀ σ, Y σ ≤ max M 0 := fun σ => (hM ⟨σ, rfl⟩).trans (le_max_left _ _)
  refine ⟨v, G, fun σ y => secondDerivField (fun i j => h i j σ) y, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine hvm.congr (hjoint.mono fun z hz => ?_)
    show v₀ z.1 z.2 = v z.1 z.2
    rw [hvg z.1 hz]
  · refine (aestronglyMeasurable_gradField hgm).congr (hjoint.mono fun z hz => ?_)
    show gradField (fun j => g j z.1) z.2 = G z.1 z.2
    rw [hGg z.1 hz]
  · exact aestronglyMeasurable_gradField (p := fun i σ y => gradField (fun j => h i j σ) y)
        fun i => aestronglyMeasurable_gradField fun j => hhm i j
  · intro σ y
    by_cases hσ : IsGoodTime u Y v₀ g h σ
    · rw [hvg σ hσ, hvg (σ + 1) ((hper σ).2 hσ), hv0p σ]
    · rw [hvb σ hσ, hvb (σ + 1) (fun h' => hσ ((hper σ).1 h'))]
  · intro σ y
    by_cases hσ : IsGoodTime u Y v₀ g h σ
    · rw [hGg σ hσ, hGg (σ + 1) ((hper σ).2 hσ)]
      simp only [hg0p σ]
    · rw [hGb σ hσ, hGb (σ + 1) (fun h' => hσ ((hper σ).1 h'))]
  · intro σ y
    show secondDerivField (fun i j => h i j (σ + 1)) y = secondDerivField (fun i j => h i j σ) y
    simp only [hh0p σ]
  · filter_upwards [hgood] with σ hσ
    have e := hσ.1
    rw [ContinuousLinearMap.comp_apply, ← hvg σ hσ] at e
    exact e
  · filter_upwards [hgood] with σ hσ
    rw [hvg σ hσ, hGg σ hσ]
    exact (hslice σ hσ).1
  · filter_upwards [hgood] with σ hσ
    rw [hGg σ hσ]
    exact (hslice σ hσ).2.1
  · filter_upwards [hgood] with σ hσ
    exact (hslice σ hσ).2.2.1
  · intro σ
    by_cases hσ : IsGoodTime u Y v₀ g h σ
    · rw [hvg σ hσ, hGg σ hσ]
      exact (hslice σ hσ).1
    · rw [hvb σ hσ, hGb σ hσ]
      exact isWeakGradient_zero
  · intro σ
    by_cases hσ : IsGoodTime u Y v₀ g h σ
    · rw [hGg σ hσ]
      exact divergence_of_good hσ
    · rw [hGb σ hσ]
      exact ae_of_all _ fun y => by simp
  · refine ⟨max ((‖(velocity : X →L[ℝ] L6R)‖ ^ 2 * max M 0) ^ 3) (max M 0), fun σ => ?_⟩
    by_cases hσ : IsGoodTime u Y v₀ g h σ
    · have hx : ‖gradPart (u (σ : TimeCircle))‖ ^ 2 ≤ max M 0 := hσ.2.2.2 ▸ hYM σ
      constructor
      · rw [hvg σ hσ]
        exact (sixth_le_of_good hσ hx).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      · rw [hGg σ hσ]
        exact (grad_le_of_good hσ).trans
          (ENNReal.ofReal_le_ofReal (hx.trans (le_max_right _ _)))
    · rw [hvb σ hσ, hGb σ hσ]
      simp
  · exact secondDeriv_lt_top_of_good hgc hgood

end Internal.SliceReading

open Internal.SliceReading

theorem sliceReadingHolds_of (h1 : FreeEnergyLocalHolds) (_h2 : ReadingExistsHolds)
    (h3 : GraphClosedHolds) (_h4 : GradInvHolds) (_h5 : FreeInvHolds) : SliceReadingHolds :=
  fun P hP f => (h1 P hP f).elim fun Y hY =>
    exists_everywhere_reading h3 (freeInv P f) Y hY.1 hY.2.1 hY.2.2.1

end Breakdown.Cert
