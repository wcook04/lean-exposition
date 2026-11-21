import Breakdown.FracCell.VelocityTailSt

open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

private lemma exists_eq_near_aux {u w : ℝ → ℂ} {a b : ℝ} (h : u =ᵐ[volume.restrict (Set.Icc a b)] w)
    {x δ : ℝ} (hx : x ∈ Set.Ioo a b) (hδ : 0 < δ) :
    ∃ y, a < y ∧ y < x ∧ x - δ < y ∧ u y = w y := by
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc] at h
  by_contra hne
  push Not at hne
  have hnull : ∀ᵐ y ∂volume, y ∉ Set.Ioo (max (x - δ) a) x := by
    filter_upwards [h] with y hy hyA
    have h1 : max (x - δ) a < y := hyA.1
    have h2 : y < x := hyA.2
    have hya : a < y := lt_of_le_of_lt (le_max_right _ _) h1
    have hyd : x - δ < y := lt_of_le_of_lt (le_max_left _ _) h1
    exact hne y hya h2 hyd (hy ⟨hya.le, (h2.trans hx.2).le⟩)
  have h0 : volume (Set.Ioo (max (x - δ) a) x) = 0 := measure_eq_zero_iff_ae_notMem.2 hnull
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
  have : max (x - δ) a < x := max_lt (by linarith) hx.1
  linarith

private lemma hasDerivAt_of_ae_aux {u w : ℝ → ℂ} {a b x : ℝ} {L : ℂ}
    (h : u =ᵐ[volume.restrict (Set.Icc a b)] w) (hw : ContinuousOn w (Set.Ioo a b))
    (hx : x ∈ Set.Ioo a b) (hu : HasDerivAt u L x) : HasDerivAt w L x := by
  have hwc : ∀ y ∈ Set.Ioo a b, ContinuousAt w y := fun y hy => hw.continuousAt (Ioo_mem_nhds hy.1 hy.2)
  have hval : u x = w x := by
    by_contra hne
    have hε : 0 < ‖u x - w x‖ / 2 := by
      have := norm_pos_iff.2 (sub_ne_zero.2 hne)
      linarith
    obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousAt_iff.1 hu.continuousAt _ hε
    obtain ⟨δ2, hδ2, h2⟩ := Metric.continuousAt_iff.1 (hwc x hx) _ hε
    obtain ⟨y, -, hyx, hyd, hyeq⟩ := exists_eq_near_aux h hx (lt_min hδ1 hδ2)
    have hd : dist y x < min δ1 δ2 := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have e1 := h1 (lt_of_lt_of_le hd (min_le_left _ _))
    have e2 := h2 (lt_of_lt_of_le hd (min_le_right _ _))
    rw [dist_eq_norm] at e1 e2
    have : ‖u x - w x‖ ≤ ‖w y - w x‖ + ‖u y - u x‖ := by
      calc ‖u x - w x‖ = ‖(w y - w x) - (u y - u x)‖ := by rw [hyeq]; congr 1; ring
        _ ≤ ‖w y - w x‖ + ‖u y - u x‖ := norm_sub_le _ _
    linarith
  rw [hasDerivAt_iff_tendsto_slope] at hu ⊢
  rw [Metric.tendsto_nhdsWithin_nhds] at hu ⊢
  intro ε hε
  obtain ⟨δ1, hδ1, h1⟩ := hu (ε / 2) (by linarith)
  have hxa : 0 < x - a := by linarith [hx.1]
  have hxb : 0 < b - x := by linarith [hx.2]
  refine ⟨min δ1 (min (x - a) (b - x)), lt_min hδ1 (lt_min hxa hxb), ?_⟩
  intro y hyne hyd
  have hyne' : y ≠ x := hyne
  have hδ1' : min δ1 (min (x - a) (b - x)) ≤ δ1 := min_le_left _ _
  have hδa : min δ1 (min (x - a) (b - x)) ≤ x - a := (min_le_right _ _).trans (min_le_left _ _)
  have hδb : min δ1 (min (x - a) (b - x)) ≤ b - x := (min_le_right _ _).trans (min_le_right _ _)
  rw [Real.dist_eq] at hyd
  have hyd2 := abs_lt.1 hyd
  have hyI : y ∈ Set.Ioo a b := ⟨by linarith [hyd2.1], by linarith [hyd2.2]⟩
  have hsl : slope w x = fun z => (z - x)⁻¹ • (w z - w x) := funext fun z => slope_def_module w x z
  have hsc : ContinuousAt (slope w x) y := by
    rw [hsl]
    exact ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.2 hyne')).smul
      ((hwc y hyI).sub continuousAt_const)
  obtain ⟨η, hη, hη'⟩ := Metric.continuousAt_iff.1 hsc (ε / 2) (by linarith)
  have hpos : 0 < |y - x| := abs_pos.2 (sub_ne_zero.2 hyne')
  have hgap : 0 < min δ1 (min (x - a) (b - x)) - |y - x| := sub_pos.2 hyd
  obtain ⟨μ, hμpos, hμη, hμ1, hμ2⟩ : ∃ μ : ℝ, 0 < μ ∧ μ ≤ η ∧ μ ≤ |y - x| ∧
      μ ≤ min δ1 (min (x - a) (b - x)) - |y - x| :=
    ⟨min η (min |y - x| (min δ1 (min (x - a) (b - x)) - |y - x|)), lt_min hη (lt_min hpos hgap),
      min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  obtain ⟨z, -, hzy, hzd, hzeq⟩ := exists_eq_near_aux h hyI hμpos
  have hzx : z ≠ x ∧ |z - x| < δ1 := by
    rcases lt_or_gt_of_ne hyne' with hlt | hgt
    · rw [abs_of_neg (by linarith)] at hμ1 hμ2
      refine ⟨by intro hzx'; linarith, ?_⟩
      rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)] at hμ1 hμ2
      refine ⟨by intro hzx'; linarith, ?_⟩
      rw [abs_of_pos (by linarith)]
      linarith
  have hz1 := h1 (show z ∈ ({x}ᶜ : Set ℝ) from hzx.1) (by rw [Real.dist_eq]; exact hzx.2)
  have hzyd : dist z y < η := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hz2 := hη' hzyd
  have hsame : slope w x z = slope u x z := by
    rw [slope_def_module, slope_def_module, hzeq, hval]
  rw [hsame] at hz2
  calc dist (slope w x y) L ≤ dist (slope w x y) (slope u x z) + dist (slope u x z) L := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by rw [dist_comm] at hz2; linarith
    _ = ε := by ring

private lemma norm_deriv_le_of_ae_aux {u w : ℝ → ℂ} {a b x : ℝ}
    (h : u =ᵐ[volume.restrict (Set.Icc a b)] w) (hw : ContinuousOn w (Set.Ioo a b))
    (hx : x ∈ Set.Ioo a b) : ‖deriv u x‖ ≤ ‖deriv w x‖ := by
  by_cases hd : DifferentiableAt ℝ u x
  · rw [(hasDerivAt_of_ae_aux h hw hx hd.hasDerivAt).deriv]
  · rw [deriv_zero_of_not_differentiableAt hd, norm_zero]
    exact norm_nonneg _

private lemma lineProj_congr_aux {ρ : ℝ → ℝ} {a b : ℝ} {F f : ℝ → ℂ}
    (hFf : F =ᵐ[volume.restrict (Set.Icc a b)] f) (e : ℕ) : lineProj ρ a b e F = lineProj ρ a b e f := by
  have hp : (fun c : Fin (e + 1) → ℂ => ∀ t : Fin (e + 1),
      ∫ r in Set.Icc a b, (ρ r : ℂ) * (F r - ∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0)
      = (fun c : Fin (e + 1) → ℂ => ∀ t : Fin (e + 1),
      ∫ r in Set.Icc a b, (ρ r : ℂ) * (f r - ∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0) := by
    funext c
    apply propext
    apply forall_congr'
    intro t
    have hi : ∫ r in Set.Icc a b, (ρ r : ℂ) * (F r - ∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))
        = ∫ r in Set.Icc a b, (ρ r : ℂ) * (f r - ∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) :=
      integral_congr_ae (by filter_upwards [hFf] with r hr; rw [hr])
    rw [hi]
  funext x
  unfold lineProj
  rw [hp]

private lemma lineProj_continuous_aux (ρ : ℝ → ℝ) (a b : ℝ) (e : ℕ) (f : ℝ → ℂ) :
    Continuous (lineProj ρ a b e f) := by
  by_cases hP : ∃ c : Fin (e + 1) → ℂ, ∀ t : Fin (e + 1),
      ∫ r in Set.Icc a b, (ρ r : ℂ) * (f r - ∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0
  · have h : lineProj ρ a b e f = fun x : ℝ => ∑ j, hP.choose j * (x : ℂ) ^ (j : ℕ) :=
      funext fun x => by unfold lineProj; rw [dif_pos hP]
    rw [h]
    fun_prop
  · have h : lineProj ρ a b e f = fun _ => 0 := funext fun x => by unfold lineProj; rw [dif_neg hP]
    rw [h]
    exact continuous_const

private lemma shape_nonneg_aux {a b r : ℝ} (hab : a < b) (hr : r ∈ Set.Icc a b) :
    0 ≤ 1 - ((2 * r - a - b) / (b - a)) ^ 2 := by
  have hba : 0 < b - a := by linarith
  rw [sub_nonneg, div_pow, div_le_one (by positivity)]
  nlinarith [hr.1, hr.2]

theorem oneVarTail_of (h : OneVarTailGoodStatement) : OneVarTailStatement := by
  intro a b ρ ha hab hρ d hd F f g hf hcont hgm hg hfi hFf
  obtain ⟨hI, hle⟩ := h a b ρ ha hab hρ d hd f g hf hcont hgm hg hfi
  rw [lineProj_congr_aux hFf (d - 1)]
  refine le_trans ?_ hle
  have hρnn : ∀ r ∈ Set.Ioo a b, 0 ≤ ρ r := by
    intro r hr
    rcases hρ with h1 | ⟨h0, h1⟩
    · rw [h1]
      exact zero_le_one
    · rw [h1]
      have := hr.1
      rw [h0] at this
      exact this.le
  rw [integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo]
  refine integral_mono_of_nonneg ?_ (hI.mono_set Set.Ioo_subset_Icc_self) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have h1 := hρnn r hr
    have h2 := shape_nonneg_aux hab (Set.Ioo_subset_Icc_self hr)
    show (0 : ℝ) ≤ _
    positivity
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have huw : (fun x => F x - lineProj ρ a b (d - 1) f x)
        =ᵐ[volume.restrict (Set.Icc a b)] (fun x => f x - lineProj ρ a b (d - 1) f x) := by
      filter_upwards [hFf] with x hx
      rw [hx]
    have hwc : ContinuousOn (fun x => f x - lineProj ρ a b (d - 1) f x) (Set.Ioo a b) :=
      (hcont.mono Set.Ioo_subset_Ioc_self).sub (lineProj_continuous_aux ρ a b (d - 1) f).continuousOn
    have key := norm_deriv_le_of_ae_aux huw hwc hr
    have h1 := hρnn r hr
    have h2 := shape_nonneg_aux hab (Set.Ioo_subset_Icc_self hr)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) key 2) (mul_nonneg h1 h2)

private lemma lineWeight_nonneg_aux (K : CellBox) {r : ℝ} (hr : r ∈ Set.Icc K.r₁ K.r₂) :
    0 ≤ K.lineWeight r := by
  unfold CellBox.lineWeight
  split_ifs with h
  · have := hr.1
    rw [h] at this
    exact this
  · exact zero_le_one

private lemma lineWeight_cases_aux (K : CellBox) :
    K.lineWeight = (fun _ => 1) ∨ (K.r₁ = 0 ∧ K.lineWeight = id) := by
  by_cases h0 : K.r₁ = 0
  · exact Or.inr ⟨h0, funext fun r => by simp [CellBox.lineWeight, h0]⟩
  · exact Or.inl (funext fun r => by simp [CellBox.lineWeight, h0])

private lemma tailNormSq_nonneg_aux (K : CellBox) (Q : ℕ) (F : ℝ × ℝ → ℂ) :
    0 ≤ K.tailNormSq Q F := by
  unfold CellBox.tailNormSq CellBox.normSqOn CellBox.lineWeightFn
  refine setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) ?_
  intro p hp
  have hw := lineWeight_nonneg_aux K hp.1
  positivity

private lemma projR_eq_lineProj_aux (K : CellBox) (d : ℕ) (F : ℝ × ℝ → ℂ) (x z : ℝ) :
    K.projR d F (x, z) = lineProj K.lineWeight K.r₁ K.r₂ d (fun r => F (r, z)) x := by
  unfold CellBox.projR lineProj
  rfl

theorem radialTailPart_of (h1 : OneVarTailStatement) (h2 : ModeRadialLineStatement)
    (h3 : RadialProjBoundStatement) (h4 : ModeGradSquareStatement) : RadialTailPartStatement := by
  intro K hK m Q hQ v G H hs n a
  obtain ⟨hsm, hsi⟩ := h4 K hK m v G H hs n a 0
  obtain ⟨hint, hle⟩ := h3 K hK Q hQ (gradMode m n G a 0) hsm hsi
  refine le_trans ?_ hle
  have hnn : 0 ≤ ∫ z in Set.Icc K.z₁ K.z₂, ∫ r in Set.Icc K.r₁ K.r₂,
      K.lineWeight r * ‖gradMode m n G a 0 (r, z) - K.projR (Q - 2) (gradMode m n G a 0) (r, z)‖ ^ 2 := by
    refine integral_nonneg fun z => ?_
    refine setIntegral_nonneg measurableSet_Icc fun r hr => ?_
    have hw := lineWeight_nonneg_aux K hr
    positivity
  unfold CellBox.normSqOn
  by_cases hI : IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) *
      ‖CellBox.radialDeriv (fun p => modeVec m n v p.1 p.2 a
        - K.projR (Q - 1) (fun p => modeVec m n v p.1 p.2 a) p) p‖ ^ 2) K.rect
  · have hrect : volume.restrict K.rect
        = (volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      rfl
    unfold IntegrableOn at hI
    rw [hrect] at hI ⊢
    rw [integral_prod_symm _ hI]
    refine integral_mono_ae hI.integral_prod_right hint ?_
    filter_upwards [h2 K hK m v G H hs n a] with z hz
    obtain ⟨f, hf1, hf0, hfm, hf2, hf3, hf4⟩ := hz
    have key := h1 K.r₁ K.r₂ K.lineWeight hK.r_order.1 hK.r_order.2 (lineWeight_cases_aux K) Q (by omega)
      (fun r => modeVec m n v r z a) f (fun r => gradMode m n G a 0 (r, z)) hf1 hf0 hfm hf2 hf3 hf4
    simp only [CellBox.radialDeriv, projR_eq_lineProj_aux, CellBox.refR]
    exact key
  · rw [integral_undef hI]
    exact hnn

theorem heightTailPart_of (h1 : OneVarTailStatement) (h2 : ModeHeightLineStatement)
    (h3 : HeightProjBoundStatement) (h4 : ModeGradSquareStatement) (h5 : ModeVelSquareStatement)
    (h6 : ProjComposeStatement) : HeightTailPartStatement := by
  intro K hK m Q hQ v G H hs n a
  obtain ⟨hsm, hsi⟩ := h4 K hK m v G H hs n a 2
  obtain ⟨hFm, hFi⟩ := h5 K hK m v G H hs n a
  obtain ⟨hint, hle⟩ := h3 K hK Q hQ (gradMode m n G a 2) hsm hsi
  refine le_trans ?_ hle
  have hnn : 0 ≤ ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ∫ z in Set.Icc K.z₁ K.z₂,
      (1 : ℝ) * ‖K.projR (Q - 1) (gradMode m n G a 2) (r, z)
        - lineProj (fun _ => 1) K.z₁ K.z₂ (Q - 2) (fun z => K.projR (Q - 1) (gradMode m n G a 2) (r, z)) z‖ ^ 2 := by
    refine setIntegral_nonneg measurableSet_Icc fun r hr => ?_
    have hw := lineWeight_nonneg_aux K hr
    have hi : 0 ≤ ∫ z in Set.Icc K.z₁ K.z₂,
        (1 : ℝ) * ‖K.projR (Q - 1) (gradMode m n G a 2) (r, z)
          - lineProj (fun _ => 1) K.z₁ K.z₂ (Q - 2) (fun z => K.projR (Q - 1) (gradMode m n G a 2) (r, z)) z‖ ^ 2 :=
      integral_nonneg fun z => by positivity
    exact mul_nonneg hw hi
  unfold CellBox.normSqOn
  by_cases hI : IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) *
      ‖CellBox.heightDeriv (fun p => K.projR (Q - 1) (fun p => modeVec m n v p.1 p.2 a) p
        - K.proj (Q - 1) (Q - 1) (fun p => modeVec m n v p.1 p.2 a) p) p‖ ^ 2) K.rect
  · have hrect : volume.restrict K.rect
        = (volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      rfl
    unfold IntegrableOn at hI
    rw [hrect] at hI ⊢
    rw [integral_prod _ hI]
    refine integral_mono_ae hI.integral_prod_left hint ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    obtain ⟨f, hf1, hf0, hfm, hf2, hf3, hf4⟩ := h2 K hK m v G H hs n a Q r
    have key := h1 K.z₁ K.z₂ (fun _ => 1) hK.z_order.1 hK.z_order.2 (Or.inl rfl) Q (by omega)
      (fun z => K.projR (Q - 1) (fun p => modeVec m n v p.1 p.2 a) (r, z)) f
      (fun z => K.projR (Q - 1) (gradMode m n G a 2) (r, z)) hf1 hf0 hfm hf2 hf3 hf4
    have hc := h6 K hK (Q - 1) (fun p => modeVec m n v p.1 p.2 a) hFm hFi r
    simp only [hc] at key
    have hw := lineWeight_nonneg_aux K hr
    simp only [CellBox.heightDeriv, CellBox.refZ]
    simp only [mul_assoc]
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hw
    simpa only [one_mul] using key
  · rw [integral_undef hI]
    exact hnn

theorem velocityTail_of (h1 : RadialTailPartStatement) (h2 : HeightTailPartStatement) :
    VelocityTailStatement := by
  intro K hK m Q hQ v G H hs n bn hbn
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ hbn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  have hr := h1 K hK m Q hQ v G H hs n a
  have hz := h2 K hK m Q hQ v G H hs n a
  have h0 := tailNormSq_nonneg_aux K Q (gradMode m n G a 1)
  rw [Fin.sum_univ_three]
  unfold CellBox.velocityTail CellBox.topPart
  linarith

theorem velocityTail_of_parts (h1 : OneVarTailStatement) (h2 : ModeRadialLineStatement)
    (h3 : RadialProjBoundStatement) (h4 : ModeGradSquareStatement) (h5 : ModeHeightLineStatement)
    (h6 : HeightProjBoundStatement) (h7 : ModeVelSquareStatement) (h8 : ProjComposeStatement) :
    VelocityTailStatement :=
  velocityTail_of (radialTailPart_of h1 h2 h3 h4) (heightTailPart_of h1 h5 h6 h4 h7 h8)

theorem velocityTail_of_leaves (h1 : OneVarTailGoodStatement) (h2 : ModeRadialLineStatement)
    (h3 : RadialProjBoundStatement) (h4 : ModeGradSquareStatement) (h5 : ModeHeightLineStatement)
    (h6 : HeightProjBoundStatement) (h7 : ModeVelSquareStatement) (h8 : ProjComposeStatement) :
    VelocityTailStatement :=
  velocityTail_of_parts (oneVarTail_of h1) h2 h3 h4 h5 h6 h7 h8

end CellAnalysis

end CellCert

end Breakdown
