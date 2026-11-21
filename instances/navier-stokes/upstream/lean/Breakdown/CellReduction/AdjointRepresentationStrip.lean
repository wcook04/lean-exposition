import Breakdown.CellReduction.AdjointRepresentationWindow
import Breakdown.CertCell.FormNegativeInverseSquare
import Breakdown.CertCell.SixthPower

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace RepresentationParts

namespace Internal

theorem indicator_rpow_two {α : Type*} (s : Set α) (f : α → ℝ≥0∞) (x : α) :
    s.indicator f x ^ (2 : ℝ) = s.indicator (fun x => f x ^ 2) x := by
  rw [ENNReal.rpow_two]
  by_cases h : x ∈ s <;> simp [h]

theorem lintegral_strip_indicator {f : ℝ × Space → ℝ≥0∞} (hf : AEMeasurable f) :
    ∫⁻ z, (Set.Icc (-2 : ℝ) 2 ×ˢ (Set.univ : Set Space)).indicator f z =
      ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, f (s, y) := by
  rw [lintegral_indicator (measurableSet_Icc.prod MeasurableSet.univ), Measure.volume_eq_prod,
    setLIntegral_prod f hf.restrict]
  simp only [Measure.restrict_univ]

theorem abs_decay_bound (c p : ℝ) (y : Space) :
    c / (1 + ‖y‖) ^ p ≤ |c| * (1 + ‖y‖) ^ (-p) := by
  rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv]
  gcongr
  exact le_abs_self c

theorem lintegral_decay_lt_top (c : ℝ) {r : ℝ} (hr : 3 < r) :
    ∫⁻ y : Space, ENNReal.ofReal (c * (1 + ‖y‖) ^ (-r)) < ⊤ := by
  have hd : ((Module.finrank ℝ Space : ℕ) : ℝ) < r := by
    rw [finrank_euclideanSpace_fin]
    exact_mod_cast hr
  exact ((integrable_one_add_norm hd).const_mul c).lintegral_lt_top

theorem strip_const_lt_top {F : ℝ → ℝ≥0∞} {K : ℝ≥0∞} (hK : K < ⊤)
    (hF : ∀ s, F s ≤ (Set.Icc (-2 : ℝ) 2).indicator (fun _ => K) s) :
    ∫⁻ s, F s < ⊤ := by
  calc ∫⁻ s, F s ≤ ∫⁻ s, (Set.Icc (-2 : ℝ) 2).indicator (fun _ => K) s := lintegral_mono hF
    _ = K * volume (Set.Icc (-2 : ℝ) 2) := lintegral_indicator_const measurableSet_Icc K
    _ < ⊤ := ENNReal.mul_lt_top hK (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)

theorem entrySqSum_nonneg (M : Space →L[ℝ] Space) : 0 ≤ matSq M :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem entrySqSum_continuous : Continuous matSq :=
  continuous_finsetSum _ fun i _ =>
    ((ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.norm).pow 2

end Internal

theorem lintegral_mul_le_strip_sq {a e : ℝ × Space → ℝ≥0∞} (ha : AEMeasurable a) (he : AEMeasurable e)
    (hz : ∀ z : ℝ × Space, z.1 ∉ Set.Icc (-2 : ℝ) 2 → e z = 0) :
    ∫⁻ z, a z * e z ≤
      (∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, a (s, y) ^ 2) ^ (1 / 2 : ℝ) * (∫⁻ z, e z ^ 2) ^ (1 / 2 : ℝ) := by
  set S : Set (ℝ × Space) := Set.Icc (-2 : ℝ) 2 ×ˢ (Set.univ : Set Space) with hSdef
  have hS : MeasurableSet S := measurableSet_Icc.prod MeasurableSet.univ
  have heq : (fun z => a z * e z) = fun z => (S.indicator a * e) z := by
    funext z
    by_cases h : z.1 ∈ Set.Icc (-2 : ℝ) 2
    · have hm : z ∈ S := ⟨h, Set.mem_univ _⟩
      simp only [Pi.mul_apply, Set.indicator_of_mem hm]
    · have hm : z ∉ S := fun hm => h hm.1
      simp only [Pi.mul_apply, Set.indicator_of_notMem hm, hz z h, mul_zero]
  rw [heq]
  calc ∫⁻ z, (S.indicator a * e) z
      ≤ (∫⁻ z, S.indicator a z ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∫⁻ z, e z ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two (ha.indicator hS) he
    _ = _ := by
      have hi : ∀ z, S.indicator a z ^ (2 : ℝ) = S.indicator (fun z => a z ^ 2) z :=
        Internal.indicator_rpow_two S a
      simp only [hi]
      simp only [ENNReal.rpow_two]
      rw [hSdef, Internal.lintegral_strip_indicator (ha.pow_const 2)]

theorem lintegral_mul_le_strip_mixed {a e : ℝ × Space → ℝ≥0∞} (ha : AEMeasurable a) (he : AEMeasurable e)
    (hz : ∀ z : ℝ × Space, z.1 ∉ Set.Icc (-2 : ℝ) 2 → e z = 0) :
    ∫⁻ z, a z * e z ≤
      (∫⁻ s in Set.Icc (-2 : ℝ) 2, (∫⁻ y, a (s, y) ^ (6 : ℝ)) ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫⁻ s, (∫⁻ y, e (s, y) ^ (6 / 5 : ℝ)) ^ (5 / 3 : ℝ)) ^ (1 / 2 : ℝ) := by
  have ha' : AEMeasurable a ((volume : Measure ℝ).prod (volume : Measure Space)) := ha
  have he' : AEMeasurable e ((volume : Measure ℝ).prod (volume : Measure Space)) := he
  set A : ℝ → ℝ≥0∞ := fun s => ∫⁻ y, a (s, y) ^ (6 : ℝ) with hAdef
  set E : ℝ → ℝ≥0∞ := fun s => ∫⁻ y, e (s, y) ^ (6 / 5 : ℝ) with hEdef
  have hA : AEMeasurable A := (ha'.pow_const (6 : ℝ)).lintegral_prod_right'
  have hE : AEMeasurable E := (he'.pow_const (6 / 5 : ℝ)).lintegral_prod_right'
  have hsa : ∀ᵐ s : ℝ, AEMeasurable (fun y => a (s, y)) :=
    ha'.aestronglyMeasurable.prodMk_left.mono fun s hs => hs.aemeasurable
  have hse : ∀ᵐ s : ℝ, AEMeasurable (fun y => e (s, y)) :=
    he'.aestronglyMeasurable.prodMk_left.mono fun s hs => hs.aemeasurable
  have hconj : (6 : ℝ).HolderConjugate (6 / 5) := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hslice : ∀ᵐ s : ℝ, ∫⁻ y, a (s, y) * e (s, y) ≤
      (Set.Icc (-2 : ℝ) 2).indicator (fun s => A s ^ (1 / (6 : ℝ))) s * E s ^ (1 / (6 / 5 : ℝ)) := by
    filter_upwards [hsa, hse] with s h1 h2
    by_cases hs : s ∈ Set.Icc (-2 : ℝ) 2
    · rw [Set.indicator_of_mem hs]
      exact ENNReal.lintegral_mul_le_Lp_mul_Lq volume hconj h1 h2
    · have h0 : ∀ y, e (s, y) = 0 := fun y => hz (s, y) hs
      simp [h0]
  have hmeasI : AEMeasurable ((Set.Icc (-2 : ℝ) 2).indicator (fun s => A s ^ (1 / (6 : ℝ)))) :=
    (hA.pow_const _).indicator measurableSet_Icc
  calc ∫⁻ z, a z * e z = ∫⁻ s, ∫⁻ y, a (s, y) * e (s, y) := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod _ (ha'.mul he')
    _ ≤ ∫⁻ s, ((Set.Icc (-2 : ℝ) 2).indicator (fun s => A s ^ (1 / (6 : ℝ))) *
          fun s => E s ^ (1 / (6 / 5 : ℝ))) s := lintegral_mono_ae hslice
    _ ≤ (∫⁻ s, (Set.Icc (-2 : ℝ) 2).indicator (fun s => A s ^ (1 / (6 : ℝ))) s ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ s, (E s ^ (1 / (6 / 5 : ℝ))) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hmeasI (hE.pow_const _)
    _ = _ := by
      have h1 : ∀ s, (A s ^ (1 / (6 : ℝ))) ^ 2 = A s ^ (1 / 3 : ℝ) := fun s => by
        rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
        norm_num
      have h2 : ∀ s, (E s ^ (1 / (6 / 5 : ℝ))) ^ (2 : ℝ) = E s ^ (5 / 3 : ℝ) := fun s => by
        rw [← ENNReal.rpow_mul]
        norm_num
      simp only [Internal.indicator_rpow_two, h1, h2]
      rw [lintegral_indicator measurableSet_Icc]

theorem square_decay_lt_top {e : ℝ × Space → ℝ≥0∞} {c p : ℝ} (hp : 3 / 2 < p)
    (he : ∀ z : ℝ × Space, e z ≤ ENNReal.ofReal (c / (1 + ‖z.2‖) ^ p))
    (hz : ∀ z : ℝ × Space, z.1 ∉ Set.Icc (-2 : ℝ) 2 → e z = 0) :
    ∫⁻ z, e z ^ 2 < ⊤ := by
  set K : ℝ≥0∞ := ∫⁻ y : Space, ENNReal.ofReal (|c| ^ 2 * (1 + ‖y‖) ^ (-(2 * p))) with hKdef
  have hK : K < ⊤ := Internal.lintegral_decay_lt_top _ (by linarith)
  have hpt : ∀ z : ℝ × Space, e z ^ 2 ≤ ENNReal.ofReal (|c| ^ 2 * (1 + ‖z.2‖) ^ (-(2 * p))) := by
    intro z
    have hpos : (0 : ℝ) ≤ |c| * (1 + ‖z.2‖) ^ (-p) := by positivity
    calc e z ^ 2 ≤ ENNReal.ofReal (|c| * (1 + ‖z.2‖) ^ (-p)) ^ 2 := by
          gcongr
          exact (he z).trans (ENNReal.ofReal_le_ofReal (Internal.abs_decay_bound c p z.2))
      _ = ENNReal.ofReal (|c| ^ 2 * (1 + ‖z.2‖) ^ (-(2 * p))) := by
          rw [← ENNReal.ofReal_pow hpos, mul_pow, ← Real.rpow_mul_natCast (by positivity)]
          congr 3
          push_cast
          ring
  have hvol : volume = (volume : Measure ℝ).prod (volume : Measure Space) := rfl
  calc ∫⁻ z, e z ^ 2 ≤ ∫⁻ s, ∫⁻ y, e (s, y) ^ 2 := by
        rw [hvol]
        exact lintegral_prod_le _
    _ < ⊤ := by
      refine Internal.strip_const_lt_top hK fun s => ?_
      by_cases hs : s ∈ Set.Icc (-2 : ℝ) 2
      · rw [Set.indicator_of_mem hs]
        exact lintegral_mono fun y => hpt (s, y)
      · have h0 : ∀ y, e (s, y) = 0 := fun y => hz (s, y) hs
        simp [h0]

theorem mixed_decay_lt_top {e : ℝ × Space → ℝ≥0∞} {c p : ℝ} (hp : 5 / 2 < p)
    (he : ∀ z : ℝ × Space, e z ≤ ENNReal.ofReal (c / (1 + ‖z.2‖) ^ p))
    (hz : ∀ z : ℝ × Space, z.1 ∉ Set.Icc (-2 : ℝ) 2 → e z = 0) :
    ∫⁻ s, (∫⁻ y, e (s, y) ^ (6 / 5 : ℝ)) ^ (5 / 3 : ℝ) < ⊤ := by
  set K : ℝ≥0∞ := ∫⁻ y : Space, ENNReal.ofReal (|c| ^ (6 / 5 : ℝ) * (1 + ‖y‖) ^ (-(p * (6 / 5))))
    with hKdef
  have hK : K < ⊤ := Internal.lintegral_decay_lt_top _ (by linarith)
  have hpt : ∀ z : ℝ × Space,
      e z ^ (6 / 5 : ℝ) ≤ ENNReal.ofReal (|c| ^ (6 / 5 : ℝ) * (1 + ‖z.2‖) ^ (-(p * (6 / 5)))) := by
    intro z
    have hpos : (0 : ℝ) ≤ |c| * (1 + ‖z.2‖) ^ (-p) := by positivity
    calc e z ^ (6 / 5 : ℝ) ≤ ENNReal.ofReal (|c| * (1 + ‖z.2‖) ^ (-p)) ^ (6 / 5 : ℝ) :=
          ENNReal.rpow_le_rpow
            ((he z).trans (ENNReal.ofReal_le_ofReal (Internal.abs_decay_bound c p z.2))) (by norm_num)
      _ = ENNReal.ofReal (|c| ^ (6 / 5 : ℝ) * (1 + ‖z.2‖) ^ (-(p * (6 / 5)))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hpos (by norm_num),
            Real.mul_rpow (abs_nonneg c) (by positivity), ← Real.rpow_mul (by positivity), neg_mul]
  refine Internal.strip_const_lt_top (K := K ^ (5 / 3 : ℝ))
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hK.ne) fun s => ?_
  by_cases hs : s ∈ Set.Icc (-2 : ℝ) 2
  · rw [Set.indicator_of_mem hs]
    exact ENNReal.rpow_le_rpow (lintegral_mono fun y => hpt (s, y)) (by norm_num)
  · have h0 : ∀ y, e (s, y) = 0 := fun y => hz (s, y) hs
    simp [h0]

theorem strip_square_lt_top {F : ℝ → Space → Space} (hF : IsTimePeriodic F)
    (h2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) :
    ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, ENNReal.ofReal ‖F s y‖ ^ 2 < ⊤ := by
  have hsq : ∀ s y, ENNReal.ofReal ‖F s y‖ ^ 2 = ENNReal.ofReal (‖F s y‖ ^ 2) := fun s y =>
    (ENNReal.ofReal_pow (norm_nonneg _) 2).symm
  simp only [hsq]
  calc ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, ENNReal.ofReal (‖F s y‖ ^ 2)
      ≤ 4 * ∫⁻ s in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖F s y‖ ^ 2) :=
        setLIntegral_strip_le (h := fun s => ∫⁻ y, ENNReal.ofReal (‖F s y‖ ^ 2))
          fun s => by simp only [hF s]
    _ < ⊤ := ENNReal.mul_lt_top (by norm_num) h2

theorem strip_entrySq_lt_top {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, ENNReal.ofReal (matSq (G s y)) < ⊤ :=
  calc ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, ENNReal.ofReal (matSq (G s y))
      ≤ 4 * ∫⁻ s in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (matSq (G s y)) :=
        setLIntegral_strip_le (h := fun s => ∫⁻ y, ENNReal.ofReal (matSq (G s y)))
          fun s => by simp only [hv.periodic_gradient s]
    _ < ⊤ := ENNReal.mul_lt_top (by norm_num) hv.gradient_finite

theorem strip_inverseSquare_lt_top {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, ENNReal.ofReal (‖v s y‖ / (1 + ‖y‖)) ^ 2 < ⊤ := by
  have h0 : ∀ᵐ y : Space, y ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton (0 : Space))
  have hpt : ∀ s, ∫⁻ y, ENNReal.ofReal (‖v s y‖ / (1 + ‖y‖)) ^ 2 ≤
      ∫⁻ y, ENNReal.ofReal (‖v s y‖ ^ 2 / ‖y‖ ^ 2) := by
    intro s
    refine lintegral_mono_ae (h0.mono fun y hy => ?_)
    have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
    rw [← ENNReal.ofReal_pow (by positivity), div_pow]
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (by positivity) (by positivity) ?_)
    nlinarith
  calc ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, ENNReal.ofReal (‖v s y‖ / (1 + ‖y‖)) ^ 2
      ≤ ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, ENNReal.ofReal (‖v s y‖ ^ 2 / ‖y‖ ^ 2) := lintegral_mono hpt
    _ ≤ 4 * ∫⁻ s in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖v s y‖ ^ 2 / ‖y‖ ^ 2) :=
        setLIntegral_strip_le (h := fun s => ∫⁻ y, ENNReal.ofReal (‖v s y‖ ^ 2 / ‖y‖ ^ 2))
          fun s => by simp only [hv.periodic_velocity s]
    _ ≤ 4 * (4 * periodLIntegral (fun σ y => matSq (G σ y))) := by
        gcongr
        exact CertCell.perturbation_inverseSquare Γ P v G H g hv
    _ < ⊤ := ENNReal.mul_lt_top (by norm_num) (ENNReal.mul_lt_top (by norm_num) hv.gradient_finite)

theorem strip_sixth_lt_top {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    ∫⁻ s in Set.Icc (-2 : ℝ) 2, (∫⁻ y, ENNReal.ofReal ‖v s y‖ ^ (6 : ℝ)) ^ (1 / 3 : ℝ) < ⊤ := by
  have hvs : ∀ᵐ σ, AEStronglyMeasurable (v σ) volume := hv.measurable_velocity.prodMk_left
  have hGs : ∀ᵐ σ, AEStronglyMeasurable (G σ) volume := hv.measurable_gradient.prodMk_left
  have hpt : ∀ᵐ σ : ℝ, (∫⁻ y, ENNReal.ofReal ‖v σ y‖ ^ (6 : ℝ)) ^ (1 / 3 : ℝ) ≤
      ENNReal.ofReal (4 / 3) * ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) := by
    filter_upwards [hvs, hGs, hv.weak_gradient, hv.sixth_power] with σ h1 h2 h3 h4
    have e6 : ∫⁻ y, ENNReal.ofReal ‖v σ y‖ ^ (6 : ℝ) = ∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6) := by
      congr 1
      funext y
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
        ENNReal.ofReal_pow (norm_nonneg _)]
    rw [e6]
    by_cases hk : ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) = ⊤
    · rw [hk, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by norm_num)).ne']
      exact le_top
    have hkt : ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) < ⊤ := lt_top_iff_ne_top.mpr hk
    have hb := sixthPowerGradientBound_four_thirds (v σ) (G σ) h3 h4 hkt
    have hI6 : Integrable (fun y => ‖v σ y‖ ^ 6) :=
      ⟨h1.norm.pow 6, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => by positivity)).mpr h4⟩
    have hIG : Integrable (fun y => matSq (G σ y)) :=
      ⟨Internal.entrySqSum_continuous.comp_aestronglyMeasurable h2,
        (hasFiniteIntegral_iff_ofReal
          (ae_of_all _ fun y => Internal.entrySqSum_nonneg _)).mpr hkt⟩
    rw [← ofReal_integral_eq_lintegral_ofReal hI6 (ae_of_all _ fun y => by positivity),
      ← ofReal_integral_eq_lintegral_ofReal hIG
        (ae_of_all _ fun y => Internal.entrySqSum_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun y => by positivity) (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hb
  calc ∫⁻ s in Set.Icc (-2 : ℝ) 2, (∫⁻ y, ENNReal.ofReal ‖v s y‖ ^ (6 : ℝ)) ^ (1 / 3 : ℝ)
      ≤ ∫⁻ s in Set.Icc (-2 : ℝ) 2, ENNReal.ofReal (4 / 3) * ∫⁻ y, ENNReal.ofReal (matSq (G s y)) :=
        lintegral_mono_ae (ae_restrict_of_ae hpt)
    _ = ENNReal.ofReal (4 / 3) * ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, ENNReal.ofReal (matSq (G s y)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (strip_entrySq_lt_top hv)

end RepresentationParts

end Breakdown
