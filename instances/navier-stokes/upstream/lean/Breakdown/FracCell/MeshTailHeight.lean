import Breakdown.FracCell.MeshTailSquares
import Breakdown.FracCell.MeshTailCoef

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace MeshTailHeight

theorem coef_sq_sum_le_radial (K : CellBox) (hK : IsCellBox K) (B : CellBases) (hB : IsCellBases K B) (G : ℝ × ℝ → ℂ)
    (hGm : AEStronglyMeasurable G (volume.restrict K.rect)) (C : ℝ) (hGb : ∀ p ∈ K.rect, ‖G p‖ ≤ C)
    (l' : ℕ) (F1 : Finset ℕ) :
    Integrable (fun r => K.lineWeight r * ‖∫ z in Set.Icc K.z₁ K.z₂, G (r, z) * (B.heightPoly l' z : ℂ)‖ ^ 2)
        (volume.restrict (Set.Icc K.r₁ K.r₂)) ∧
    ∑ j' ∈ F1, ‖B.coef K G j' l'‖ ^ 2
      ≤ ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ‖∫ z in Set.Icc K.z₁ K.z₂, G (r, z) * (B.heightPoly l' z : ℂ)‖ ^ 2 := by
  have hμ : volume.restrict K.rect = (volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; rfl
  have hlw := MeshTailCoef.lineWeight_continuous K
  have hrp : ∀ j, Continuous (fun r : ℝ => B.radialPoly j r) := by
    intro j; unfold CellBases.radialPoly; exact continuous_finsetSum _ fun i _ => by fun_prop
  have hhp : Continuous (fun z : ℝ => B.heightPoly l' z) := by
    unfold CellBases.heightPoly; exact continuous_finsetSum _ fun i _ => by fun_prop
  have hlw0 : ∀ r ∈ Set.Icc K.r₁ K.r₂, 0 ≤ K.lineWeight r := by
    intro r hr
    unfold CellBox.lineWeight
    split_ifs
    · exact le_trans hK.r_order.1 hr.1
    · exact zero_le_one
  obtain ⟨CP, hCP⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc K.z₁ K.z₂)
    (Complex.continuous_ofReal.comp hhp).continuousOn
  obtain ⟨CL, hCL⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc K.r₁ K.r₂) hlw.continuousOn
  have hCPn : 0 ≤ CP := le_trans (norm_nonneg _) (hCP K.z₁ ⟨le_refl _, hK.z_order.2.le⟩)
  have hCLn : 0 ≤ CL := le_trans (norm_nonneg _) (hCL K.r₁ ⟨le_refl _, hK.r_order.2.le⟩)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hGb (K.r₁, K.z₁) ⟨⟨le_refl _, hK.r_order.2.le⟩, ⟨le_refl _, hK.z_order.2.le⟩⟩)
  have : IsFiniteMeasure (volume.restrict (Set.Icc K.r₁ K.r₂)) := isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (Set.Icc K.z₁ K.z₂)) := isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  set gr : ℝ → ℂ := fun r => ∫ z in Set.Icc K.z₁ K.z₂, G (r, z) * (B.heightPoly l' z : ℂ) with hgr
  set f : ℝ × ℝ → ℂ := fun p => G p * (B.heightPoly l' p.2 : ℂ) with hf
  have hfm : AEStronglyMeasurable f ((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))) := by
    rw [← hμ]; exact hGm.mul (Complex.continuous_ofReal.comp (hhp.comp continuous_snd)).aestronglyMeasurable
  have hgm : AEStronglyMeasurable gr (volume.restrict (Set.Icc K.r₁ K.r₂)) := hfm.integral_prod_right'
  have hgb : ∀ r ∈ Set.Icc K.r₁ K.r₂, ‖gr r‖ ≤ C * CP * (volume.real (Set.Icc K.z₁ K.z₂)) := by
    intro r hr
    simp only [hgr]
    refine norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top fun z hz => ?_
    rw [norm_mul]
    exact mul_le_mul (hGb (r, z) ⟨hr, hz⟩) (hCP z hz) (norm_nonneg _) hC0
  have hMn : 0 ≤ C * CP * (volume.real (Set.Icc K.z₁ K.z₂)) := by positivity
  have hfub : ∀ j', B.coef K G j' l' = ∫ r in Set.Icc K.r₁ K.r₂, ((K.lineWeight r : ℝ) : ℂ) * gr r * (B.radialPoly j' r : ℂ) := by
    intro j'
    obtain ⟨CR, hCR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc K.r₁ K.r₂)
      (Complex.continuous_ofReal.comp (hrp j')).continuousOn
    have hfi' : Integrable (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * G p * ((B.radialPoly j' p.1 * B.heightPoly l' p.2 : ℝ) : ℂ))
        ((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))) := by
      have e : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * G p * ((B.radialPoly j' p.1 * B.heightPoly l' p.2 : ℝ) : ℂ))
          = fun p => ((K.lineWeight p.1 : ℂ) * (B.radialPoly j' p.1 : ℂ)) * f p := by
        funext p; simp only [hf]; push_cast; ring
      rw [e]
      refine Integrable.of_bound (((Complex.continuous_ofReal.comp (hlw.comp continuous_fst)).mul
        (Complex.continuous_ofReal.comp ((hrp j').comp continuous_fst))).aestronglyMeasurable.mul hfm) (CL * CR * (C * CP)) ?_
      rw [← hμ]
      refine (ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)).mono fun p hp => ?_
      simp only [hf]; rw [norm_mul, norm_mul, norm_mul, Complex.norm_real]
      have h1 := hCR p.1 hp.1
      simp only [Function.comp_apply] at h1
      have h2 := hCL p.1 hp.1
      exact mul_le_mul (mul_le_mul h2 h1 (norm_nonneg _) hCLn) (mul_le_mul (hGb p hp) (hCP p.2 hp.2) (norm_nonneg _) hC0)
        (by positivity) (mul_nonneg hCLn ((norm_nonneg _).trans h1))
    unfold CellBases.coef
    rw [hμ, integral_prod _ hfi']
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [hgr]
    rw [← integral_const_mul, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    push_cast; ring
  have hgg : Integrable (fun r => K.lineWeight r * ‖gr r‖ ^ 2) (volume.restrict (Set.Icc K.r₁ K.r₂)) := by
    refine Integrable.of_bound (hlw.aestronglyMeasurable.mul (hgm.norm.pow 2))
      (CL * (C * CP * (volume.real (Set.Icc K.z₁ K.z₂))) ^ 2) ((ae_restrict_mem measurableSet_Icc).mono fun r hr => ?_)
    rw [norm_mul, norm_pow, norm_norm]
    exact mul_le_mul (hCL r hr) (pow_le_pow_left₀ (norm_nonneg _) (hgb r hr) 2) (by positivity) hCLn
  have hge : ∀ k ∈ F1, Integrable (fun r => ((K.lineWeight r : ℝ) : ℂ) * gr r * (B.radialPoly k r : ℂ))
      (volume.restrict (Set.Icc K.r₁ K.r₂)) := by
    intro k _
    obtain ⟨CR, hCR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc K.r₁ K.r₂)
      (Complex.continuous_ofReal.comp (hrp k)).continuousOn
    refine Integrable.of_bound (((Complex.continuous_ofReal.comp hlw).aestronglyMeasurable.mul hgm).mul
      (Complex.continuous_ofReal.comp (hrp k)).aestronglyMeasurable) (CL * (C * CP * (volume.real (Set.Icc K.z₁ K.z₂))) * CR) ?_
    refine (ae_restrict_mem measurableSet_Icc).mono fun r hr => ?_
    rw [norm_mul, norm_mul, Complex.norm_real]
    have h2 := hCL r hr
    exact mul_le_mul (mul_le_mul h2 (hgb r hr) (norm_nonneg _) hCLn) (hCR r hr) (norm_nonneg _) (by positivity)
  have hsumInner := MeshTailSquares.proj_sq_sum_le F1 K.lineWeight B.radialPoly gr
    ((ae_restrict_mem measurableSet_Icc).mono fun r hr => hlw0 r hr) hgg hge
    (fun k _ k' _ => Continuous.integrableOn_Icc ((hlw.mul (hrp k)).mul (hrp k')))
    (fun k _ k' _ => hB.radial_orthonormal k k')
  refine ⟨hgg, ?_⟩
  calc ∑ j' ∈ F1, ‖B.coef K G j' l'‖ ^ 2
      = ∑ j' ∈ F1, ‖∫ r in Set.Icc K.r₁ K.r₂, ((K.lineWeight r : ℝ) : ℂ) * gr r * (B.radialPoly j' r : ℂ)‖ ^ 2 :=
        Finset.sum_congr rfl fun j' _ => by rw [hfub j']
    _ ≤ _ := hsumInner

theorem height_point (K : CellBox) (_hK : IsCellBox K) (B : CellBases) (hB : IsCellBases K B) (m D : ℕ)
    {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O) (hreg : IsTailRegular K T) (hb : IsTailBounds K B D T)
    (w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ) (F2 : Finset ℕ) (θ r : ℝ) (hr : r ∈ Set.Icc K.r₁ K.r₂) (hr' : r ∈ Set.Ioo K.r₁ K.r₂)
    (hsec : ∀ i o c, AEStronglyMeasurable (fun z => T.mult i o c (r, z) θ) (volume.restrict (Set.Icc K.z₁ K.z₂))) :
    (∑ o, T.outWeight o * ∑ l' ∈ F2, (if D < l' then
        ‖∫ z in Set.Icc K.z₁ K.z₂, T.angleField m B w o (r, z) θ * (B.heightPoly l' z : ℂ)‖ ^ 2
        else 0))
      ≤ T.heightTotal * ∑ i, ∑ l ∈ Finset.range (T.inputDeg i + 1), T.heightBound i l *
          ∑ c, ‖T.heightInput m B w i l c r θ‖ ^ 2 := by
  set S := (Finset.univ : Finset I).sigma (fun i => Finset.range (T.inputDeg i + 1)) with hS
  set hq : O → (Σ _ : I, ℕ) → ℝ → ℂ := fun o q z =>
    (∑ c, T.mult q.1 o c (r, z) θ * T.heightInput m B w q.1 q.2 c r θ) * (B.heightPoly q.2 z : ℂ) with hhq
  have hdec : ∀ o z, T.angleField m B w o (r, z) θ = ∑ q ∈ S, hq o q z := by
    intro o z
    rw [hS, Finset.sum_sigma _ _ (fun q => hq o q z)]
    unfold TailFamily.angleField
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hhq, TailFamily.inputFn, TailFamily.heightInput, Finset.mul_sum, Finset.sum_mul]
    conv_lhs => enter [2, c, 2, n']; rw [Finset.sum_comm]
    conv_lhs => enter [2, c]; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun n' _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast; ring
  have : IsFiniteMeasure (volume.restrict (Set.Icc K.z₁ K.z₂)) := isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have hhp : ∀ l, Continuous (fun z : ℝ => B.heightPoly l z) := by
    intro l; unfold CellBases.heightPoly; exact continuous_finsetSum _ fun i _ => by fun_prop
  choose Cm hCm using hreg.mult_bounded
  have hmi : ∀ i o c, Integrable (fun z => T.mult i o c (r, z) θ) (volume.restrict (Set.Icc K.z₁ K.z₂)) :=
    fun i o c => Integrable.of_bound (hsec i o c) (Cm i o c)
      ((ae_restrict_mem measurableSet_Icc).mono fun z hz => hCm i o c (r, z) ⟨hr, hz⟩ θ)
  have hqg : ∀ o q (g : ℝ → ℂ), Continuous g →
      Integrable (fun z => hq o q z * g z) (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
    intro o q g hg
    have e : (fun z => hq o q z * g z) = fun z => ∑ c, T.mult q.1 o c (r, z) θ *
        (T.heightInput m B w q.1 q.2 c r θ * (B.heightPoly q.2 z : ℂ) * g z) := by
      funext z; simp only [hhq, Finset.sum_mul]; exact Finset.sum_congr rfl fun c _ => by ring
    rw [e]
    exact integrable_finsetSum _ fun c _ => IntegrableOn.mul_continuousOn (K := Set.Icc K.z₁ K.z₂) (hmi q.1 o c)
      ((continuous_const.mul (Complex.continuous_ofReal.comp (hhp q.2))).mul hg).continuousOn isCompact_Icc
  have hqb : ∀ o q, ∃ M, ∀ z ∈ Set.Icc K.z₁ K.z₂, ‖hq o q z‖ ≤ M := by
    intro o q
    obtain ⟨Cp, hCp⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc K.z₁ K.z₂)
      (Complex.continuous_ofReal.comp (hhp q.2)).continuousOn
    refine ⟨(∑ c, |Cm q.1 o c| * ‖T.heightInput m B w q.1 q.2 c r θ‖) * |Cp|, fun z hz => ?_⟩
    simp only [hhq]
    rw [norm_mul]
    refine mul_le_mul ((norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)) ((hCp z hz).trans (le_abs_self _))
      (norm_nonneg _) (Finset.sum_nonneg fun c _ => by positivity)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ((hCm q.1 o c (r, z) ⟨hr, hz⟩ θ).trans (le_abs_self _)) (norm_nonneg _)
  have hgg : ∀ o q, Integrable (fun z => (1 : ℝ) * ‖hq o q z‖ ^ 2) (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
    intro o q
    obtain ⟨M, hM⟩ := hqb o q
    have hqm : AEStronglyMeasurable (hq o q) (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
      simpa using (hqg o q (fun _ => 1) continuous_const).aestronglyMeasurable
    refine Integrable.of_bound ((hqm.norm.pow 2).const_mul _) (M ^ 2)
      ((ae_restrict_mem measurableSet_Icc).mono fun z hz => ?_)
    rw [one_mul, norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hM z hz) 2
  have hge : ∀ o q k, Integrable (fun z => ((1 : ℝ) : ℂ) * hq o q z * (B.heightPoly k z : ℂ))
      (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
    intro o q k
    have e : (fun z => ((1 : ℝ) : ℂ) * hq o q z * (B.heightPoly k z : ℂ))
        = fun z => hq o q z * (B.heightPoly k z : ℂ) := by funext z; push_cast; ring
    rw [e]; exact hqg o q _ (Complex.continuous_ofReal.comp (hhp k))
  have hv : ∀ o q, ∑ l' ∈ F2.filter (fun l' => D < l'),
      ‖∫ z in Set.Icc K.z₁ K.z₂, hq o q z * (B.heightPoly l' z : ℂ)‖ ^ 2
        ≤ K.heightTail B D (hq o q) := by
    intro o q
    have hdis : Disjoint (Finset.range (D + 1)) (F2.filter (fun l' => D < l')) := by
      rw [Finset.disjoint_left]; intro a ha hb
      simp only [Finset.mem_range, Finset.mem_filter] at ha hb; omega
    have hb' := MeshTailSquares.proj_sq_sum_le (Finset.range (D + 1) ∪ F2.filter (fun l' => D < l')) (fun _ => (1 : ℝ))
      B.heightPoly (hq o q) (ae_of_all _ fun _ => zero_le_one) (hgg o q)
      (fun k _ => hge o q k)
      (fun k _ k' _ => Continuous.integrableOn_Icc ((continuous_const.mul (hhp k)).mul (hhp k')))
      (fun k _ k' _ => by simp only [one_mul]; exact hB.height_orthonormal k k')
    rw [Finset.sum_union hdis] at hb'
    simp only [Complex.ofReal_one, one_mul] at hb'
    unfold CellBox.heightTail
    linarith
  have hq2 : ∀ q ∈ S, ∑ o, T.outWeight o * ∑ l' ∈ F2.filter (fun l' => D < l'),
      ‖∫ z in Set.Icc K.z₁ K.z₂, hq o q z * (B.heightPoly l' z : ℂ)‖ ^ 2
        ≤ T.heightBound q.1 q.2 ^ 2 * ∑ c, ‖T.heightInput m B w q.1 q.2 c r θ‖ ^ 2 := by
    intro q hqS
    have hj : q.2 ≤ T.inputDeg q.1 := by
      rw [hS, Finset.mem_sigma, Finset.mem_range] at hqS; omega
    exact (Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_left (hv o q) (hb.outWeight_nonneg o)).trans
      (hb.height_bound q.1 q.2 hj r hr' θ (fun c => T.heightInput m B w q.1 q.2 c r θ))
  have hge' : ∀ o q k, Integrable (fun z => hq o q z * (B.heightPoly k z : ℂ)) (volume.restrict (Set.Icc K.z₁ K.z₂)) :=
    fun o q k => hqg o q _ (Complex.continuous_ofReal.comp (hhp k))
  have hlin : ∀ o l', ∫ z in Set.Icc K.z₁ K.z₂, T.angleField m B w o (r, z) θ * (B.heightPoly l' z : ℂ)
      = ∑ q ∈ S, ∫ z in Set.Icc K.z₁ K.z₂, hq o q z * (B.heightPoly l' z : ℂ) := by
    intro o l'
    rw [← integral_finsetSum _ fun q _ => hge' o q l']
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [hdec, Finset.sum_mul]
  calc (∑ o, T.outWeight o * ∑ l' ∈ F2, (if D < l' then
        ‖∫ z in Set.Icc K.z₁ K.z₂, T.angleField m B w o (r, z) θ * (B.heightPoly l' z : ℂ)‖ ^ 2
        else 0))
      = ∑ o, T.outWeight o * ∑ l' ∈ F2.filter (fun l' => D < l'),
          ‖∑ q ∈ S, ∫ z in Set.Icc K.z₁ K.z₂, hq o q z * (B.heightPoly l' z : ℂ)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [Finset.sum_filter]
        refine congrArg (T.outWeight o * ·) (Finset.sum_congr rfl fun l' _ => ?_)
        rw [hlin]
    _ ≤ (∑ q ∈ S, T.heightBound q.1 q.2) * ∑ q ∈ S, T.heightBound q.1 q.2 *
          ∑ c, ‖T.heightInput m B w q.1 q.2 c r θ‖ ^ 2 :=
        MeshTailSquares.weighted_sum_sq_le S _ T.outWeight hb.outWeight_nonneg
          (fun o q l' => ∫ z in Set.Icc K.z₁ K.z₂, hq o q z * (B.heightPoly l' z : ℂ))
          (fun q => T.heightBound q.1 q.2) (fun q => ∑ c, ‖T.heightInput m B w q.1 q.2 c r θ‖ ^ 2)
          (fun q => hb.heightBound_nonneg q.1 q.2) (fun q => Finset.sum_nonneg fun c _ => by positivity) hq2
    _ = _ := by
        rw [hS, Finset.sum_sigma, Finset.sum_sigma]
        rfl

end MeshTailHeight

open MeshTailHeight in
theorem heightBranch_holds : HeightBranchStatement := by
  intro K B hK hB m D I O _ _ T hreg hb w F1 F2 θ hθ
  have hrectc : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have : IsFiniteMeasure (volume.restrict (Set.Icc K.r₁ K.r₂)) := isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have hμ : volume.restrict K.rect = (volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; rfl
  have hlw := MeshTailCoef.lineWeight_continuous K
  have hlw0 : ∀ r ∈ Set.Icc K.r₁ K.r₂, 0 ≤ K.lineWeight r := by
    intro r hr
    unfold CellBox.lineWeight
    split_ifs
    · exact le_trans hK.r_order.1 hr.1
    · exact zero_le_one
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
  have hstep := fun o l' => coef_sq_sum_le_radial K hK B hB (fun p => T.angleField m B w o p θ) (hGm o)
    (hGb o).choose (hGb o).choose_spec l' F1
  have hXc : ∀ i l, Continuous (fun r => K.lineWeight r * ∑ c, ‖T.heightInput m B w i l c r θ‖ ^ 2) := by
    intro i l
    refine hlw.mul (continuous_finsetSum _ fun c _ => (Continuous.norm ?_).pow 2)
    unfold TailFamily.heightInput CellBases.radialPoly
    fun_prop
  have hsec : ∀ᵐ r ∂(volume.restrict (Set.Icc K.r₁ K.r₂)), r ∈ Set.Icc K.r₁ K.r₂ ∧ ∀ i o c,
      AEStronglyMeasurable (fun z => T.mult i o c (r, z) θ) (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
    refine (ae_restrict_mem measurableSet_Icc).and ?_
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro o; rw [ae_all_iff]; intro c
    have h1 := hθ i o c
    rw [hμ] at h1
    exact h1.prodMk_left
  have hII : ∀ o l', Integrable (fun r => if D < l' then K.lineWeight r *
      ‖∫ z in Set.Icc K.z₁ K.z₂, T.angleField m B w o (r, z) θ * (B.heightPoly l' z : ℂ)‖ ^ 2 else 0)
      (volume.restrict (Set.Icc K.r₁ K.r₂)) := by
    intro o l'
    by_cases hj : D < l'
    · simpa only [hj, if_true] using (hstep o l').1
    · simp only [hj, if_false]; exact integrable_zero _ _ _
  calc (∑ o, T.outWeight o * ∑ j' ∈ F1, ∑ l' ∈ F2,
          (if D < l' then ‖B.coef K (fun p => T.angleField m B w o p θ) j' l'‖ ^ 2 else 0))
      ≤ ∑ o, T.outWeight o * ∑ l' ∈ F2, (if D < l' then ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r *
          ‖∫ z in Set.Icc K.z₁ K.z₂, T.angleField m B w o (r, z) θ * (B.heightPoly l' z : ℂ)‖ ^ 2 else 0) := by
        refine Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_left ?_ (hb.outWeight_nonneg o)
        rw [Finset.sum_comm]
        refine Finset.sum_le_sum fun l' _ => ?_
        by_cases hj : D < l'
        · simp only [hj, if_true]; exact (hstep o l').2
        · simp only [hj, if_false, Finset.sum_const_zero, le_refl]
    _ = ∫ r in Set.Icc K.r₁ K.r₂, ∑ o, T.outWeight o * ∑ l' ∈ F2, (if D < l' then K.lineWeight r *
          ‖∫ z in Set.Icc K.z₁ K.z₂, T.angleField m B w o (r, z) θ * (B.heightPoly l' z : ℂ)‖ ^ 2 else 0) := by
        rw [integral_finsetSum _ fun o _ => (integrable_finsetSum _ fun l' _ => hII o l').const_mul _]
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [integral_const_mul, integral_finsetSum _ fun l' _ => hII o l']
        refine congrArg (T.outWeight o * ·) (Finset.sum_congr rfl fun l' _ => ?_)
        by_cases hj : D < l'
        · simp only [hj, if_true]
        · simp only [hj, if_false, integral_zero]
    _ ≤ ∫ r in Set.Icc K.r₁ K.r₂, ∑ i, ∑ l ∈ Finset.range (T.inputDeg i + 1), T.heightTotal * T.heightBound i l *
          (K.lineWeight r * ∑ c, ‖T.heightInput m B w i l c r θ‖ ^ 2) := by
        refine integral_mono_of_nonneg ((ae_restrict_mem measurableSet_Icc).mono fun r hr => ?_) ?_ ?_
        · exact Finset.sum_nonneg fun o _ => mul_nonneg (hb.outWeight_nonneg o)
            (Finset.sum_nonneg fun l' _ => by
              split_ifs
              · exact mul_nonneg (hlw0 r hr) (by positivity)
              · exact le_refl _)
        · exact (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun l _ =>
            continuous_const.mul (hXc i l)).integrableOn_Icc
        · have hIoo : ∀ᵐ r ∂(volume.restrict (Set.Icc K.r₁ K.r₂)), r ∈ Set.Ioo K.r₁ K.r₂ := by
            rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
            exact ae_restrict_mem measurableSet_Ioo
          filter_upwards [hsec, hIoo] with r hr hr'
          have hp := height_point K hK B hB m D T hreg hb w F2 θ r hr.1 hr' hr.2
          have hl := hlw0 r hr.1
          calc ∑ o, T.outWeight o * ∑ l' ∈ F2, (if D < l' then K.lineWeight r *
                ‖∫ z in Set.Icc K.z₁ K.z₂, T.angleField m B w o (r, z) θ * (B.heightPoly l' z : ℂ)‖ ^ 2 else 0)
              = K.lineWeight r * ∑ o, T.outWeight o * ∑ l' ∈ F2, (if D < l' then
                ‖∫ z in Set.Icc K.z₁ K.z₂, T.angleField m B w o (r, z) θ * (B.heightPoly l' z : ℂ)‖ ^ 2 else 0) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun o _ => ?_
                rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
                refine Finset.sum_congr rfl fun l' _ => ?_
                split_ifs <;> ring
            _ ≤ K.lineWeight r * (T.heightTotal * ∑ i, ∑ l ∈ Finset.range (T.inputDeg i + 1), T.heightBound i l *
                ∑ c, ‖T.heightInput m B w i l c r θ‖ ^ 2) := mul_le_mul_of_nonneg_left hp hl
            _ = _ := by
                rw [Finset.mul_sum, Finset.mul_sum]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [Finset.mul_sum, Finset.mul_sum]
                refine Finset.sum_congr rfl fun l _ => ?_
                ring
    _ = _ := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ =>
          ((hXc i l).integrableOn_Icc).const_mul _]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun l _ => ((hXc i l).integrableOn_Icc).const_mul _]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [integral_const_mul]

end CellAnalysis

end CellCert

end Breakdown
