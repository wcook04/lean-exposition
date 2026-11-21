import Breakdown.FracCell.MeshTailSquares
import Breakdown.FracCell.MeshTailCoef

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace MeshTailRadial

theorem coef_sq_sum_le_height (K : CellBox) (hK : IsCellBox K) (B : CellBases) (hB : IsCellBases K B) (G : ℝ × ℝ → ℂ)
    (hGm : AEStronglyMeasurable G (volume.restrict K.rect)) (C : ℝ) (hGb : ∀ p ∈ K.rect, ‖G p‖ ≤ C)
    (j' : ℕ) (F2 : Finset ℕ) :
    Integrable (fun z => ‖∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * G (r, z) * (B.radialPoly j' r : ℂ)‖ ^ 2)
        (volume.restrict (Set.Icc K.z₁ K.z₂)) ∧
    ∑ l' ∈ F2, ‖B.coef K G j' l'‖ ^ 2
      ≤ ∫ z in Set.Icc K.z₁ K.z₂, ‖∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * G (r, z) * (B.radialPoly j' r : ℂ)‖ ^ 2 := by
  have hrectc : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hμ : volume.restrict K.rect = (volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; rfl
  have hlw := MeshTailCoef.lineWeight_continuous K
  have hrp : Continuous (fun r : ℝ => B.radialPoly j' r) := by
    unfold CellBases.radialPoly; exact continuous_finsetSum _ fun i _ => by fun_prop
  have hhp : ∀ l, Continuous (fun z : ℝ => B.heightPoly l z) := by
    intro l; unfold CellBases.heightPoly; exact continuous_finsetSum _ fun i _ => by fun_prop
  have hWc : Continuous (fun r : ℝ => (K.lineWeight r : ℂ) * (B.radialPoly j' r : ℂ)) := by fun_prop
  obtain ⟨CW, hCW⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc K.r₁ K.r₂) hWc.continuousOn
  have hCWn : 0 ≤ CW := le_trans (norm_nonneg _) (hCW K.r₁ ⟨le_refl _, hK.r_order.2.le⟩)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hGb (K.r₁, K.z₁) ⟨⟨le_refl _, hK.r_order.2.le⟩, ⟨le_refl _, hK.z_order.2.le⟩⟩)
  have : IsFiniteMeasure (volume.restrict (Set.Icc K.r₁ K.r₂)) := isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (Set.Icc K.z₁ K.z₂)) := isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  set gz : ℝ → ℂ := fun z => ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * G (r, z) * (B.radialPoly j' r : ℂ) with hgz
  set f : ℝ × ℝ → ℂ := fun p => ((K.lineWeight p.1 : ℂ) * (B.radialPoly j' p.1 : ℂ)) * G p with hf
  have hfm : AEStronglyMeasurable f ((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))) := by
    rw [← hμ]; exact (hWc.comp continuous_fst).aestronglyMeasurable.mul hGm
  have hfb : ∀ᵐ p ∂((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))), ‖f p‖ ≤ CW * C := by
    rw [← hμ]
    refine (ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)).mono fun p hp => ?_
    simp only [hf]; rw [norm_mul]
    exact mul_le_mul (hCW p.1 hp.1) (hGb p hp) (norm_nonneg _) hCWn
  have hfi : Integrable f ((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))) :=
    Integrable.of_bound hfm _ hfb
  have hgm : AEStronglyMeasurable gz (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
    refine (hfm.prod_swap.integral_prod_right').congr (Filter.Eventually.of_forall fun z => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [hf, Prod.swap_prod_mk]; ring
  have hgb : ∀ z ∈ Set.Icc K.z₁ K.z₂, ‖gz z‖ ≤ CW * C * (volume.real (Set.Icc K.r₁ K.r₂)) := by
    intro z hz
    simp only [hgz]
    refine norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top fun r hr => ?_
    have e : (K.lineWeight r : ℂ) * G (r, z) * (B.radialPoly j' r : ℂ)
        = ((K.lineWeight r : ℂ) * (B.radialPoly j' r : ℂ)) * G (r, z) := by ring
    rw [e, norm_mul]
    exact mul_le_mul (hCW r hr) (hGb (r, z) ⟨hr, hz⟩) (norm_nonneg _) hCWn
  have hgb' : ∀ᵐ z ∂(volume.restrict (Set.Icc K.z₁ K.z₂)), ‖gz z‖ ≤ CW * C * (volume.real (Set.Icc K.r₁ K.r₂)) :=
    (ae_restrict_mem measurableSet_Icc).mono fun z hz => hgb z hz
  have hfub : ∀ l', B.coef K G j' l' = ∫ z in Set.Icc K.z₁ K.z₂, ((1 : ℝ) : ℂ) * gz z * (B.heightPoly l' z : ℂ) := by
    intro l'
    obtain ⟨CP, hCP⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc K.z₁ K.z₂) (hhp l').continuousOn
    have hfi' : Integrable (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * G p * ((B.radialPoly j' p.1 * B.heightPoly l' p.2 : ℝ) : ℂ))
        ((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))) := by
      have e : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * G p * ((B.radialPoly j' p.1 * B.heightPoly l' p.2 : ℝ) : ℂ))
          = fun p => f p * (B.heightPoly l' p.2 : ℂ) := by
        funext p; simp only [hf]; push_cast; ring
      rw [e]
      refine Integrable.of_bound (hfm.mul (Complex.continuous_ofReal.comp ((hhp l').comp continuous_snd)).aestronglyMeasurable)
        (CW * C * CP) ?_
      rw [← hμ]
      refine (ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)).mono fun p hp => ?_
      simp only [hf]; rw [norm_mul, norm_mul, Complex.norm_real]
      exact mul_le_mul (mul_le_mul (hCW p.1 hp.1) (hGb p hp) (norm_nonneg _) hCWn) (hCP p.2 hp.2) (norm_nonneg _)
        (mul_nonneg hCWn hC0)
    unfold CellBases.coef
    rw [hμ, integral_prod_symm _ hfi']
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hgz]
    rw [← integral_const_mul, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    push_cast; ring
  have hgg : Integrable (fun z => (1 : ℝ) * ‖gz z‖ ^ 2) (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
    refine Integrable.of_bound ((hgm.norm.pow 2).const_mul _) ((CW * C * (volume.real (Set.Icc K.r₁ K.r₂))) ^ 2) ?_
    refine hgb'.mono fun z hz => ?_
    rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hge : ∀ k ∈ F2, Integrable (fun z => ((1 : ℝ) : ℂ) * gz z * (B.heightPoly k z : ℂ)) (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
    intro k _
    obtain ⟨CP, hCP⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc K.z₁ K.z₂) (hhp k).continuousOn
    refine Integrable.of_bound ((aestronglyMeasurable_const.mul hgm).mul
      (Complex.continuous_ofReal.comp (hhp k)).aestronglyMeasurable.restrict) (CW * C * (volume.real (Set.Icc K.r₁ K.r₂)) * CP) ?_
    refine (ae_restrict_mem measurableSet_Icc).mono fun z hz => ?_
    rw [norm_mul, norm_mul, Complex.ofReal_one, norm_one, one_mul, Complex.norm_real]
    exact mul_le_mul (hgb z hz) (hCP z hz) (norm_nonneg _) (by have := hgb z hz; positivity)
  have hee : ∀ k ∈ F2, ∀ k' ∈ F2, Integrable (fun z => (1 : ℝ) * B.heightPoly k z * B.heightPoly k' z)
      (volume.restrict (Set.Icc K.z₁ K.z₂)) := fun k _ k' _ =>
    Continuous.integrableOn_Icc (continuous_const.mul (hhp k) |>.mul (hhp k'))
  have horth : ∀ k ∈ F2, ∀ k' ∈ F2, ∫ z in Set.Icc K.z₁ K.z₂, (1 : ℝ) * B.heightPoly k z * B.heightPoly k' z
      = if k = k' then 1 else 0 := fun k _ k' _ => by simp only [one_mul]; exact hB.height_orthonormal k k'
  have hsumInner := MeshTailSquares.proj_sq_sum_le F2 (fun _ => (1 : ℝ)) B.heightPoly gz (ae_of_all _ fun _ => zero_le_one)
    hgg hge hee horth
  simp only [Complex.ofReal_one, one_mul] at hsumInner
  refine ⟨by simpa only [one_mul] using hgg, ?_⟩
  calc ∑ l' ∈ F2, ‖B.coef K G j' l'‖ ^ 2
      = ∑ l' ∈ F2, ‖∫ z in Set.Icc K.z₁ K.z₂, gz z * (B.heightPoly l' z : ℂ)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun l' _ => ?_
        rw [hfub l']; simp only [Complex.ofReal_one, one_mul]
    _ ≤ _ := hsumInner

theorem radial_point (K : CellBox) (hK : IsCellBox K) (B : CellBases) (hB : IsCellBases K B) (m D : ℕ)
    {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O) (hreg : IsTailRegular K T) (hb : IsTailBounds K B D T)
    (w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ) (F1 : Finset ℕ) (θ z : ℝ) (hz : z ∈ Set.Icc K.z₁ K.z₂) (hz' : z ∈ Set.Ioo K.z₁ K.z₂)
    (hsec : ∀ i o c, AEStronglyMeasurable (fun r => T.mult i o c (r, z) θ) (volume.restrict (Set.Icc K.r₁ K.r₂))) :
    (∑ o, T.outWeight o * ∑ j' ∈ F1, (if D < j' then
        ‖∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * T.angleField m B w o (r, z) θ * (B.radialPoly j' r : ℂ)‖ ^ 2
        else 0))
      ≤ T.radialTotal * ∑ i, ∑ j ∈ Finset.range (T.inputDeg i + 1), T.radialBound i j *
          ∑ c, ‖T.radialInput m B w i j c z θ‖ ^ 2 := by
  set S := (Finset.univ : Finset I).sigma (fun i => Finset.range (T.inputDeg i + 1)) with hS
  set hq : O → (Σ _ : I, ℕ) → ℝ → ℂ := fun o q r =>
    (∑ c, T.mult q.1 o c (r, z) θ * T.radialInput m B w q.1 q.2 c z θ) * (B.radialPoly q.2 r : ℂ) with hhq
  have hdec : ∀ o r, T.angleField m B w o (r, z) θ = ∑ q ∈ S, hq o q r := by
    intro o r
    rw [hS, Finset.sum_sigma _ _ (fun q => hq o q r)]
    unfold TailFamily.angleField
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hhq, TailFamily.inputFn, TailFamily.radialInput, Finset.mul_sum, Finset.sum_mul]
    conv_lhs => enter [2, c]; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun n' _ => Finset.sum_congr rfl fun l _ => ?_
    push_cast; ring

  have : IsFiniteMeasure (volume.restrict (Set.Icc K.r₁ K.r₂)) := isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have hlw := MeshTailCoef.lineWeight_continuous K
  have hrp : ∀ j, Continuous (fun r : ℝ => B.radialPoly j r) := by
    intro j; unfold CellBases.radialPoly; exact continuous_finsetSum _ fun i _ => by fun_prop
  have hlw0 : ∀ r ∈ Set.Icc K.r₁ K.r₂, 0 ≤ K.lineWeight r := by
    intro r hr
    unfold CellBox.lineWeight
    split_ifs
    · exact le_trans hK.r_order.1 hr.1
    · exact zero_le_one
  choose Cm hCm using hreg.mult_bounded
  have hmi : ∀ i o c, Integrable (fun r => T.mult i o c (r, z) θ) (volume.restrict (Set.Icc K.r₁ K.r₂)) :=
    fun i o c => Integrable.of_bound (hsec i o c) (Cm i o c)
      ((ae_restrict_mem measurableSet_Icc).mono fun r hr => hCm i o c (r, z) ⟨hr, hz⟩ θ)
  have hqg : ∀ o q (g : ℝ → ℂ), Continuous g →
      Integrable (fun r => hq o q r * g r) (volume.restrict (Set.Icc K.r₁ K.r₂)) := by
    intro o q g hg
    have e : (fun r => hq o q r * g r) = fun r => ∑ c, T.mult q.1 o c (r, z) θ *
        (T.radialInput m B w q.1 q.2 c z θ * (B.radialPoly q.2 r : ℂ) * g r) := by
      funext r; simp only [hhq, Finset.sum_mul]; exact Finset.sum_congr rfl fun c _ => by ring
    rw [e]
    exact integrable_finsetSum _ fun c _ => IntegrableOn.mul_continuousOn (K := Set.Icc K.r₁ K.r₂) (hmi q.1 o c)
      ((continuous_const.mul (Complex.continuous_ofReal.comp (hrp q.2))).mul hg).continuousOn isCompact_Icc
  have hqb : ∀ o q, ∃ M, ∀ r ∈ Set.Icc K.r₁ K.r₂, ‖hq o q r‖ ≤ M := by
    intro o q
    obtain ⟨Cp, hCp⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc K.r₁ K.r₂)
      (Complex.continuous_ofReal.comp (hrp q.2)).continuousOn
    refine ⟨(∑ c, |Cm q.1 o c| * ‖T.radialInput m B w q.1 q.2 c z θ‖) * |Cp|, fun r hr => ?_⟩
    simp only [hhq]
    rw [norm_mul]
    refine mul_le_mul ((norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)) ((hCp r hr).trans (le_abs_self _))
      (norm_nonneg _) (Finset.sum_nonneg fun c _ => by positivity)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ((hCm q.1 o c (r, z) ⟨hr, hz⟩ θ).trans (le_abs_self _)) (norm_nonneg _)
  have hgg : ∀ o q, Integrable (fun r => K.lineWeight r * ‖hq o q r‖ ^ 2) (volume.restrict (Set.Icc K.r₁ K.r₂)) := by
    intro o q
    obtain ⟨M, hM⟩ := hqb o q
    obtain ⟨CL, hCL⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc K.r₁ K.r₂) hlw.continuousOn
    have hqm : AEStronglyMeasurable (hq o q) (volume.restrict (Set.Icc K.r₁ K.r₂)) := by
      simpa using (hqg o q (fun _ => 1) continuous_const).aestronglyMeasurable
    refine Integrable.of_bound (hlw.aestronglyMeasurable.mul (hqm.norm.pow 2)) (CL * M ^ 2)
      ((ae_restrict_mem measurableSet_Icc).mono fun r hr => ?_)
    rw [norm_mul, norm_pow, norm_norm]
    exact mul_le_mul (hCL r hr) (pow_le_pow_left₀ (norm_nonneg _) (hM r hr) 2) (by positivity)
      ((norm_nonneg _).trans (hCL r hr))
  have hge : ∀ o q k, Integrable (fun r => (K.lineWeight r : ℂ) * hq o q r * (B.radialPoly k r : ℂ))
      (volume.restrict (Set.Icc K.r₁ K.r₂)) := by
    intro o q k
    have e : (fun r => (K.lineWeight r : ℂ) * hq o q r * (B.radialPoly k r : ℂ))
        = fun r => hq o q r * ((K.lineWeight r : ℂ) * (B.radialPoly k r : ℂ)) := by funext r; ring
    rw [e]; exact hqg o q _ (by fun_prop)
  have hv : ∀ o q, ∑ j' ∈ F1.filter (fun j' => D < j'),
      ‖∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * hq o q r * (B.radialPoly j' r : ℂ)‖ ^ 2
        ≤ K.radialTail B D (hq o q) := by
    intro o q
    have hdis : Disjoint (Finset.range (D + 1)) (F1.filter (fun j' => D < j')) := by
      rw [Finset.disjoint_left]; intro a ha hb
      simp only [Finset.mem_range, Finset.mem_filter] at ha hb; omega
    have hb' := MeshTailSquares.proj_sq_sum_le (Finset.range (D + 1) ∪ F1.filter (fun j' => D < j')) K.lineWeight
      B.radialPoly (hq o q) ((ae_restrict_mem measurableSet_Icc).mono fun r hr => hlw0 r hr) (hgg o q)
      (fun k _ => hge o q k)
      (fun k _ k' _ => Continuous.integrableOn_Icc ((hlw.mul (hrp k)).mul (hrp k')))
      (fun k _ k' _ => hB.radial_orthonormal k k')
    rw [Finset.sum_union hdis] at hb'
    unfold CellBox.radialTail
    linarith
  have hq2 : ∀ q ∈ S, ∑ o, T.outWeight o * ∑ j' ∈ F1.filter (fun j' => D < j'),
      ‖∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * hq o q r * (B.radialPoly j' r : ℂ)‖ ^ 2
        ≤ T.radialBound q.1 q.2 ^ 2 * ∑ c, ‖T.radialInput m B w q.1 q.2 c z θ‖ ^ 2 := by
    intro q hqS
    have hj : q.2 ≤ T.inputDeg q.1 := by
      rw [hS, Finset.mem_sigma, Finset.mem_range] at hqS; omega
    exact (Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_left (hv o q) (hb.outWeight_nonneg o)).trans
      (hb.radial_bound q.1 q.2 hj z hz' θ (fun c => T.radialInput m B w q.1 q.2 c z θ))
  have hlin : ∀ o j', ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * T.angleField m B w o (r, z) θ * (B.radialPoly j' r : ℂ)
      = ∑ q ∈ S, ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * hq o q r * (B.radialPoly j' r : ℂ) := by
    intro o j'
    rw [← integral_finsetSum _ fun q _ => hge o q j']
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    dsimp only
    rw [hdec, Finset.mul_sum, Finset.sum_mul]
  calc (∑ o, T.outWeight o * ∑ j' ∈ F1, (if D < j' then
        ‖∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * T.angleField m B w o (r, z) θ * (B.radialPoly j' r : ℂ)‖ ^ 2
        else 0))
      = ∑ o, T.outWeight o * ∑ j' ∈ F1.filter (fun j' => D < j'),
          ‖∑ q ∈ S, ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * hq o q r * (B.radialPoly j' r : ℂ)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [Finset.sum_filter]
        refine congrArg (T.outWeight o * ·) (Finset.sum_congr rfl fun j' _ => ?_)
        rw [hlin]
    _ ≤ (∑ q ∈ S, T.radialBound q.1 q.2) * ∑ q ∈ S, T.radialBound q.1 q.2 *
          ∑ c, ‖T.radialInput m B w q.1 q.2 c z θ‖ ^ 2 :=
        MeshTailSquares.weighted_sum_sq_le S _ T.outWeight hb.outWeight_nonneg
          (fun o q j' => ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * hq o q r * (B.radialPoly j' r : ℂ))
          (fun q => T.radialBound q.1 q.2) (fun q => ∑ c, ‖T.radialInput m B w q.1 q.2 c z θ‖ ^ 2)
          (fun q => hb.radialBound_nonneg q.1 q.2) (fun q => Finset.sum_nonneg fun c _ => by positivity) hq2
    _ = _ := by
        rw [hS, Finset.sum_sigma, Finset.sum_sigma]
        rfl

end MeshTailRadial

open MeshTailRadial in
theorem radialBranch_holds : RadialBranchStatement := by
  intro K B hK hB m D I O _ _ T hreg hb w F1 F2 θ hθ
  have hrectc : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have : IsFiniteMeasure (volume.restrict (Set.Icc K.z₁ K.z₂)) := isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have hμ : volume.restrict K.rect = (volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; rfl
  have hinC : ∀ i c, Continuous (fun p : ℝ × ℝ => T.inputFn m B w i c p θ) := by
    intro i c
    unfold TailFamily.inputFn CellBases.radialPoly CellBases.heightPoly
    fun_prop
  have hGm : ∀ o, AEStronglyMeasurable (fun p => T.angleField m B w o p θ) (volume.restrict K.rect) := by
    intro o
    unfold TailFamily.angleField
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => Finset.aestronglyMeasurable_fun_sum _ fun c _ =>
      (hθ i o c).mul (hinC i c).aestronglyMeasurable
  choose Cm hCm using hreg.mult_bounded
  have hGb : ∀ o, ∃ C, ∀ p ∈ K.rect, ‖T.angleField m B w o p θ‖ ≤ C := by
    intro o
    have hCi : ∀ i c, ∃ C, ∀ p ∈ K.rect, ‖T.inputFn m B w i c p θ‖ ≤ C :=
      fun i c => hrectc.exists_bound_of_continuousOn (hinC i c).continuousOn
    choose Ci hCi using hCi
    refine ⟨∑ i, ∑ c, |Cm i o c| * |Ci i c|, fun p hp => ?_⟩
    unfold TailFamily.angleField
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun c _ => ?_))
    rw [norm_mul]
    exact mul_le_mul ((hCm i o c p hp θ).trans (le_abs_self _)) ((hCi i c p hp).trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)
  have hstep := fun o j' => coef_sq_sum_le_height K hK B hB (fun p => T.angleField m B w o p θ) (hGm o)
    (hGb o).choose (hGb o).choose_spec j' F2
  have hXc : ∀ i j, Continuous (fun z => ∑ c, ‖T.radialInput m B w i j c z θ‖ ^ 2) := by
    intro i j
    refine continuous_finsetSum _ fun c _ => (Continuous.norm ?_).pow 2
    unfold TailFamily.radialInput CellBases.heightPoly
    fun_prop
  have hsec : ∀ᵐ z ∂(volume.restrict (Set.Icc K.z₁ K.z₂)), z ∈ Set.Icc K.z₁ K.z₂ ∧ ∀ i o c,
      AEStronglyMeasurable (fun r => T.mult i o c (r, z) θ) (volume.restrict (Set.Icc K.r₁ K.r₂)) := by
    refine (ae_restrict_mem measurableSet_Icc).and ?_
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro o; rw [ae_all_iff]; intro c
    have h1 := hθ i o c
    rw [hμ] at h1
    exact h1.prodMk_right
  calc (∑ o, T.outWeight o * ∑ j' ∈ F1, ∑ l' ∈ F2,
          (if D < j' then ‖B.coef K (fun p => T.angleField m B w o p θ) j' l'‖ ^ 2 else 0))
      ≤ ∑ o, T.outWeight o * ∑ j' ∈ F1, (if D < j' then
          ∫ z in Set.Icc K.z₁ K.z₂, ‖∫ r in Set.Icc K.r₁ K.r₂,
            (K.lineWeight r : ℂ) * T.angleField m B w o (r, z) θ * (B.radialPoly j' r : ℂ)‖ ^ 2 else 0) := by
        refine Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j' _ => ?_)
          (hb.outWeight_nonneg o)
        by_cases hj : D < j'
        · simp only [hj, if_true]; exact (hstep o j').2
        · simp only [hj, if_false, Finset.sum_const_zero, le_refl]
    _ = ∫ z in Set.Icc K.z₁ K.z₂, ∑ o, T.outWeight o * ∑ j' ∈ F1, (if D < j' then
          ‖∫ r in Set.Icc K.r₁ K.r₂,
            (K.lineWeight r : ℂ) * T.angleField m B w o (r, z) θ * (B.radialPoly j' r : ℂ)‖ ^ 2 else 0) := by
        have hII : ∀ o j', Integrable (fun z => if D < j' then
            ‖∫ r in Set.Icc K.r₁ K.r₂,
              (K.lineWeight r : ℂ) * T.angleField m B w o (r, z) θ * (B.radialPoly j' r : ℂ)‖ ^ 2 else 0)
            (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
          intro o j'
          by_cases hj : D < j'
          · simpa only [hj, if_true] using (hstep o j').1
          · simp only [hj, if_false]; exact integrable_zero _ _ _
        rw [integral_finsetSum _ fun o _ => (integrable_finsetSum _ fun j' _ => hII o j').const_mul _]
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [integral_const_mul, integral_finsetSum _ fun j' _ => hII o j']
        refine congrArg (T.outWeight o * ·) (Finset.sum_congr rfl fun j' _ => ?_)
        by_cases hj : D < j'
        · simp only [hj, if_true]
        · simp only [hj, if_false, integral_zero]
    _ ≤ ∫ z in Set.Icc K.z₁ K.z₂, T.radialTotal * ∑ i, ∑ j ∈ Finset.range (T.inputDeg i + 1),
          T.radialBound i j * ∑ c, ‖T.radialInput m B w i j c z θ‖ ^ 2 := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => ?_) ?_ ?_
        · exact Finset.sum_nonneg fun o _ => mul_nonneg (hb.outWeight_nonneg o)
            (Finset.sum_nonneg fun j' _ => by split_ifs <;> positivity)
        · exact ((continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
            continuous_const.mul (hXc i j))).integrableOn_Icc)
        · have hIoo : ∀ᵐ z ∂(volume.restrict (Set.Icc K.z₁ K.z₂)), z ∈ Set.Ioo K.z₁ K.z₂ := by
            rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
            exact ae_restrict_mem measurableSet_Ioo
          filter_upwards [hsec, hIoo] with z hz hz'
          exact radial_point K hK B hB m D T hreg hb w F1 θ z hz.1 hz' hz.2
    _ = _ := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          ((hXc i j).integrableOn_Icc).const_mul _, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => ((hXc i j).integrableOn_Icc).const_mul _, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul]
        ring

end CellAnalysis

end CellCert

end Breakdown
