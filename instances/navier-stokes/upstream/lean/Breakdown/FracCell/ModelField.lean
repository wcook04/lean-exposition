import Breakdown.FracCell.StClauses
import Breakdown.FracCert.HeldExists
import Breakdown.FracCert.HeldWeakProfileParts

open scoped ContDiff ENNReal Convolution
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace Breakdown

namespace CellCert

namespace ModelFieldInternal

open SteadyCert SteadyCert.HeldWeakProfilePartsInternal FracInternal.HeldExists

theorem unit_norm (j : Fin 3) : ‖unitVector j‖ = 1 := by simp [unitVector]

theorem zero_off {ψ : Space → ℝ} {x : Space} (hx : x ∉ tsupport ψ) : fderiv ℝ ψ x = 0 := by
  by_contra h
  exact hx (support_fderiv_subset ℝ (Function.mem_support.2 h))

theorem zero_off' {ψ : Space → ℝ} {x : Space} (hx : x ∉ tsupport ψ) : ψ x = 0 := by
  by_contra h
  exact hx (subset_tsupport _ (Function.mem_support.2 h))

theorem precomp_eq (f : Space → ℝ) (g : Space → (Space →L[ℝ] ℝ)) :
    (f ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR Space, volume] g) =
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := by
  funext x
  simp only [convolution_def]
  congr 1

theorem weak_c1 {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (j k : Fin 3)
    (hv : LocallyIntegrable v volume) (hG : LocallyIntegrable (fun y => G y (unitVector j)) volume)
    (hw : IsWeakGradientOf v G) {ψ : Space → ℝ} (hψ : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) :
    ∫ y, fderiv ℝ ψ y (unitVector j) * v y k = -∫ y, ψ y * G y (unitVector j) k := by
  set a : Space → ℝ := fun y => v y k with ha_def
  set b : Space → ℝ := fun y => G y (unitVector j) k with hb_def
  have la : LocallyIntegrable a volume := by
    refine hv.mono ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
      hv.aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    exact (PiLp.norm_apply_le (v y) k)
  have lb : LocallyIntegrable b volume := by
    refine hG.mono ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
      hG.aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    exact (PiLp.norm_apply_le (G y (unitVector j)) k)
  set Dψ : Space → (Space →L[ℝ] ℝ) := fderiv ℝ ψ with hDψ
  have hDc : Continuous Dψ := hψ.continuous_fderiv one_ne_zero
  have hDs : HasCompactSupport Dψ := hs.fderiv (𝕜 := ℝ)
  have hψc : Continuous ψ := hψ.continuous
  set K : Set Space := Metric.cthickening 1 (tsupport ψ) with hK_def
  have hK : IsCompact K := hs.isCompact.cthickening
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set S : ℝ := (∫ y in K, |a y|) + ∫ y in K, |b y| with hS_def
  have iaK : Integrable (K.indicator fun y => |a y|) := IntegrableOn.integrable_indicator (f := fun y => |a y|) ((la.integrableOn_isCompact hK).abs) hKm
  have ibK : Integrable (K.indicator fun y => |b y|) := IntegrableOn.integrable_indicator (f := fun y => |b y|) ((lb.integrableOn_isCompact hK).abs) hKm
  have hS0 : 0 ≤ S := add_nonneg (integral_nonneg fun _ => abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _)
  have i1 : Integrable (fun y => fderiv ℝ ψ y (unitVector j) * a y) := by
    simpa [smul_eq_mul] using la.integrable_smul_left_of_hasCompactSupport (hDc.clm_apply continuous_const)
      (hs.fderiv_apply (𝕜 := ℝ) (unitVector j))
  have i2 : Integrable (fun y => ψ y * b y) := by
    simpa [smul_eq_mul] using lb.integrable_smul_left_of_hasCompactSupport hψc hs
  have key : ∀ ε : ℝ, 0 < ε → |(∫ y, fderiv ℝ ψ y (unitVector j) * a y) + ∫ y, ψ y * b y| ≤ ε * S := by
    intro ε hε
    obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.uniformContinuous_iff.1
      (hψc.uniformContinuous_of_tendsto_cocompact hs.is_zero_at_infty) ε hε
    obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.uniformContinuous_iff.1
      (hDc.uniformContinuous_of_tendsto_cocompact hDs.is_zero_at_infty) ε hε
    set R : ℝ := min (min δ₁ δ₂) 1 with hR_def
    have hR : 0 < R := lt_min (lt_min hδ₁ hδ₂) one_pos
    let ρ : ContDiffBump (0 : Space) := ⟨R / 2, R, half_pos hR, half_lt_self hR⟩
    set r : Space → ℝ := ρ.normed volume with hr_def
    have hrs : Function.support r ⊆ Metric.ball 0 R := by rw [hr_def, ρ.support_normed_eq]
    have hr0 : ∀ x, 0 ≤ r x := fun x => ρ.nonneg_normed x
    have hr1 : ∫ x, r x = 1 := ρ.integral_normed
    set χ : Space → ℝ := r ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ with hχ_def
    have hχsm : ContDiff ℝ ∞ χ :=
      ρ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) ρ.contDiff_normed
        hψc.locallyIntegrable
    have hχs : HasCompactSupport χ := ρ.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hs
    have hχd : ∀ y, fderiv ℝ χ y = (r ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Dψ) y := by
      intro y
      rw [← precomp_eq]
      exact (hs.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
        (ρ.contDiff_normed (n := 0)).continuous.locallyIntegrable hψ y).fderiv
    have hχc : Continuous (fun y => fderiv ℝ χ y (unitVector j)) :=
      (hχsm.continuous_fderiv (by simp)).clm_apply continuous_const
    have c1 : Integrable (fun y => fderiv ℝ χ y (unitVector j) * a y) := by
      simpa [smul_eq_mul] using la.integrable_smul_left_of_hasCompactSupport hχc
        (hχs.fderiv_apply (𝕜 := ℝ) (unitVector j))
    have c2 : Integrable (fun y => χ y * a y) := by
      simpa [smul_eq_mul] using la.integrable_smul_left_of_hasCompactSupport hχsm.continuous hχs
    have c3 : Integrable (fun y => χ y * b y) := by
      simpa [smul_eq_mul] using lb.integrable_smul_left_of_hasCompactSupport hχsm.continuous hχs
    have hweak := weak_component j k hv hG hw hχsm c1 c2 c3
    have bD : ∀ y, |fderiv ℝ ψ y (unitVector j) - fderiv ℝ χ y (unitVector j)| ≤ ε * K.indicator (fun _ => 1) y := by
      intro y
      by_cases hy : y ∈ K
      · have hd : dist ((r ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Dψ) y) (Dψ y) ≤ ε := by
          refine dist_convolution_le hε.le hrs hr0 hr1 hDc.aestronglyMeasurable fun x hx => ?_
          have : dist x y < δ₂ := lt_of_lt_of_le (Metric.mem_ball.1 hx) ((min_le_left _ _).trans (min_le_right _ _))
          exact (h₂ this).le
        rw [Set.indicator_of_mem hy, mul_one]
        have e : fderiv ℝ ψ y (unitVector j) - fderiv ℝ χ y (unitVector j) = (Dψ y - fderiv ℝ χ y) (unitVector j) := by
          simp [hDψ]
        rw [e, hχd, ← Real.norm_eq_abs]
        refine ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
        rw [unit_norm, mul_one, ← dist_eq_norm, dist_comm]
        exact hd
      · have hoff : ∀ x ∈ Metric.ball y R, x ∉ tsupport ψ := by
          intro x hx hxt
          apply hy
          refine Metric.mem_cthickening_of_dist_le y x 1 _ hxt ?_
          rw [dist_comm]
          exact (Metric.mem_ball.1 hx).le.trans (min_le_right _ _) |>.trans' le_rfl
        have hd : dist ((r ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Dψ) y) 0 ≤ 0 := by
          refine dist_convolution_le le_rfl hrs hr0 hr1 hDc.aestronglyMeasurable fun x hx => ?_
          simp only [hDψ]
          rw [zero_off (hoff x hx), dist_self]
        have h0 : fderiv ℝ χ y = 0 := by rw [hχd]; exact dist_le_zero.1 hd
        have h0' : fderiv ℝ ψ y = 0 := zero_off (hoff y (Metric.mem_ball_self hR))
        rw [Set.indicator_of_notMem hy, h0, h0']
        simp
    have bP : ∀ y, |ψ y - χ y| ≤ ε * K.indicator (fun _ => 1) y := by
      intro y
      by_cases hy : y ∈ K
      · have hd : dist (χ y) (ψ y) ≤ ε := by
          refine dist_convolution_le hε.le hrs hr0 hr1 hψc.aestronglyMeasurable fun x hx => ?_
          have : dist x y < δ₁ := lt_of_lt_of_le (Metric.mem_ball.1 hx) ((min_le_left _ _).trans (min_le_left _ _))
          exact (h₁ this).le
        rw [Set.indicator_of_mem hy, mul_one, ← Real.dist_eq, dist_comm]
        exact hd
      · have hoff : ∀ x ∈ Metric.ball y R, x ∉ tsupport ψ := by
          intro x hx hxt
          apply hy
          refine Metric.mem_cthickening_of_dist_le y x 1 _ hxt ?_
          rw [dist_comm]
          exact (Metric.mem_ball.1 hx).le.trans (min_le_right _ _)
        have hd : dist (χ y) 0 ≤ 0 := by
          refine dist_convolution_le le_rfl hrs hr0 hr1 hψc.aestronglyMeasurable fun x hx => ?_
          rw [zero_off' (hoff x hx), dist_self]
        have h0 : χ y = 0 := dist_le_zero.1 hd
        rw [Set.indicator_of_notMem hy, h0, zero_off' (hoff y (Metric.mem_ball_self hR))]
        simp
    have e1 : (∫ y, fderiv ℝ ψ y (unitVector j) * a y) + ∫ y, ψ y * b y =
        (∫ y, (fderiv ℝ ψ y (unitVector j) - fderiv ℝ χ y (unitVector j)) * a y) +
          ∫ y, (ψ y - χ y) * b y := by
      have s1 : (∫ y, (fderiv ℝ ψ y (unitVector j) - fderiv ℝ χ y (unitVector j)) * a y) =
          (∫ y, fderiv ℝ ψ y (unitVector j) * a y) - ∫ y, fderiv ℝ χ y (unitVector j) * a y := by
        rw [← integral_sub i1 c1]; congr 1; funext y; ring
      have s2 : (∫ y, (ψ y - χ y) * b y) = (∫ y, ψ y * b y) - ∫ y, χ y * b y := by
        rw [← integral_sub i2 c3]; congr 1; funext y; ring
      rw [s1, s2]
      have : (∫ y, fderiv ℝ χ y (unitVector j) * a y) + ∫ y, χ y * b y = 0 := by
        simp only [ha_def, hb_def]; rw [hweak]; ring
      linarith
    rw [e1]
    have n1 : |∫ y, (fderiv ℝ ψ y (unitVector j) - fderiv ℝ χ y (unitVector j)) * a y| ≤
        ε * ∫ y in K, |a y| := by
      rw [← Real.norm_eq_abs, ← integral_indicator hKm, ← integral_const_mul]
      refine norm_integral_le_of_norm_le (iaK.const_mul ε) (ae_of_all _ fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      by_cases hy : y ∈ K
      · have := bD y
        rw [Set.indicator_of_mem hy, mul_one] at this
        rw [Set.indicator_of_mem hy]
        exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
      · have := bD y
        rw [Set.indicator_of_notMem hy, mul_zero] at this
        rw [Set.indicator_of_notMem hy, mul_zero]
        have h0 : |fderiv ℝ ψ y (unitVector j) - fderiv ℝ χ y (unitVector j)| = 0 :=
          le_antisymm this (abs_nonneg _)
        rw [h0, zero_mul]
    have n2 : |∫ y, (ψ y - χ y) * b y| ≤ ε * ∫ y in K, |b y| := by
      rw [← Real.norm_eq_abs, ← integral_indicator hKm, ← integral_const_mul]
      refine norm_integral_le_of_norm_le (ibK.const_mul ε) (ae_of_all _ fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      by_cases hy : y ∈ K
      · have := bP y
        rw [Set.indicator_of_mem hy, mul_one] at this
        rw [Set.indicator_of_mem hy]
        exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
      · have := bP y
        rw [Set.indicator_of_notMem hy, mul_zero] at this
        rw [Set.indicator_of_notMem hy, mul_zero]
        have h0 : |ψ y - χ y| = 0 := le_antisymm this (abs_nonneg _)
        rw [h0, zero_mul]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ ε * (∫ y in K, |a y|) + ε * ∫ y in K, |b y| := add_le_add n1 n2
      _ = ε * S := by rw [hS_def]; ring
  set X : ℝ := (∫ y, fderiv ℝ ψ y (unitVector j) * a y) + ∫ y, ψ y * b y with hX
  have hX0 : X = 0 := by
    by_contra hne
    have hpos : 0 < |X| := abs_pos.2 hne
    have h := key (|X| / (S + 1)) (div_pos hpos (by linarith))
    have : |X| / (S + 1) * S < |X| := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  simp only [hX, ha_def, hb_def] at hX0
  linarith


theorem aesm_apply {f : Space → (Space →L[ℝ] Space)} {g : Space → Space} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) : AEStronglyMeasurable (fun y => f y (g y)) volume :=
  isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable (hf.prodMk hg)

theorem aesm_adj {f : Space → (Space →L[ℝ] Space)} {g : Space → Space} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (fun y => ContinuousLinearMap.adjoint (f y) (g y)) volume :=
  aesm_apply ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Space) (F := Space)).continuous.comp_aestronglyMeasurable hf) hg

theorem comp_li {v : Space → Space} (hv : LocallyIntegrable v volume) (k : Fin 3) :
    LocallyIntegrable (fun y => v y k) volume :=
  hv.mono ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
      hv.aestronglyMeasurable) (ae_of_all _ fun y => PiLp.norm_apply_le (v y) k)

theorem cint {g f : Space → ℝ} (hg : Continuous g) (hs : HasCompactSupport g) (hf : LocallyIntegrable f volume) :
    Integrable (fun y => g y * f y) := by
  simpa [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport hg hs

theorem opNorm_sq_le (A : Space →L[ℝ] Space) : ‖A‖ ^ 2 ≤ 3 * entrySq A := by
  have hb : ‖A‖ ≤ Real.sqrt (3 * entrySq A) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun w => ?_
    have h := norm_apply_sq_le A w
    rw [← Real.sqrt_sq (norm_nonneg (A w))]
    calc Real.sqrt (‖A w‖ ^ 2) ≤ Real.sqrt (3 * ‖w‖ ^ 2 * entrySq A) := Real.sqrt_le_sqrt h
      _ = Real.sqrt (3 * entrySq A) * ‖w‖ := by
        rw [show 3 * ‖w‖ ^ 2 * entrySq A = (3 * entrySq A) * ‖w‖ ^ 2 by ring,
          Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have he : 0 ≤ 3 * entrySq A := by unfold entrySq; positivity
  calc ‖A‖ ^ 2 ≤ (Real.sqrt (3 * entrySq A)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = _ := Real.sq_sqrt he

theorem memLp_grad {G : Space → (Space →L[ℝ] Space)} (hGm : AEStronglyMeasurable G volume)
    (hG : Integrable (fun y => entrySq (G y))) : MemLp G 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm hGm).2 ?_
  refine (hG.const_mul 3).mono' (hGm.norm.pow 2) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact opNorm_sq_le _

theorem li_col {G : Space → (Space →L[ℝ] Space)} (hGm : AEStronglyMeasurable G volume)
    (hG : Integrable (fun y => entrySq (G y))) (j : Fin 3) :
    LocallyIntegrable (fun y => G y (unitVector j)) volume :=
  (((ContinuousLinearMap.apply ℝ Space (unitVector j)).comp_memLp' (memLp_grad hGm hG))).locallyIntegrable
    (by norm_num)

theorem li_v {v : Space → Space} (h6 : MemLp v 6 volume) : LocallyIntegrable v volume :=
  h6.locallyIntegrable (by norm_num)

theorem product_rule {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    (hv : LocallyIntegrable v volume) (hGc : ∀ j, LocallyIntegrable (fun y => G y (unitVector j)) volume)
    (hw : IsWeakGradientOf v G) {c : Space → Space} (hc : ContDiff ℝ 1 c)
    (l1 : LocallyIntegrable (fun y => inner ℝ (c y) (v y)) volume)
    (l2 : ∀ j, LocallyIntegrable (fun y => inner ℝ (v y) (fderiv ℝ c y (unitVector j))
      + inner ℝ (c y) (G y (unitVector j))) volume)
    {φ : Space → ℝ} (hφ : IsTestScalar φ) (j : Fin 3) :
    ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (c y) (v y) =
      -∫ y, φ y * (inner ℝ (v y) (fderiv ℝ c y (unitVector j)) + inner ℝ (c y) (G y (unitVector j))) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.1.of_le (by exact_mod_cast le_top)
  have hcd : Differentiable ℝ c := hc.differentiable one_ne_zero
  have hci : ∀ i : Fin 3, ContDiff ℝ 1 (fun y => c y i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hc
  have hψ : ∀ i : Fin 3, ContDiff ℝ 1 (fun y => φ y * c y i) := fun i => hφ1.mul (hci i)
  have hψs : ∀ i : Fin 3, HasCompactSupport (fun y => φ y * c y i) := fun i => hφ.2.mul_right
  have hder : ∀ (i : Fin 3) y, fderiv ℝ (fun y => φ y * c y i) y (unitVector j) =
      fderiv ℝ φ y (unitVector j) * c y i + φ y * fderiv ℝ c y (unitVector j) i := by
    intro i y
    have hd := ((hφ1.differentiable one_ne_zero) y).hasFDerivAt.mul (((hci i).differentiable one_ne_zero) y).hasFDerivAt
    rw [show (fun y => φ y * c y i) = φ * (fun y => c y i) from rfl, hd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [coord_fderiv hcd i y (unitVector j)]
    ring
  have hw1 : ∀ i : Fin 3, ∫ y, (fderiv ℝ φ y (unitVector j) * c y i + φ y * fderiv ℝ c y (unitVector j) i) * v y i =
      -∫ y, (φ y * c y i) * G y (unitVector j) i := by
    intro i
    have h := weak_c1 j i hv (hGc j) hw (hψ i) (hψs i)
    simp only [hder] at h
    exact h
  have iT : ∀ i : Fin 3, Integrable (fun y => (fderiv ℝ φ y (unitVector j) * c y i + φ y * fderiv ℝ c y (unitVector j) i) * v y i) := by
    intro i
    have hc1 : Continuous (fun y => fderiv ℝ (fun y => φ y * c y i) y (unitVector j)) :=
      ((hψ i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have := cint hc1 ((hψs i).fderiv_apply (𝕜 := ℝ) (unitVector j)) (comp_li hv i)
    simpa only [hder] using this
  have iU : ∀ i : Fin 3, Integrable (fun y => (φ y * c y i) * G y (unitVector j) i) :=
    fun i => cint (hψ i).continuous (hψs i) (comp_li (hGc j) i)
  have hsum : ∫ y, ∑ i : Fin 3, ((fderiv ℝ φ y (unitVector j) * c y i + φ y * fderiv ℝ c y (unitVector j) i) * v y i
      + (φ y * c y i) * G y (unitVector j) i) = 0 := by
    have hfs := integral_finset_sum (μ := volume) Finset.univ
      (f := fun (i : Fin 3) y => (fderiv ℝ φ y (unitVector j) * c y i + φ y * fderiv ℝ c y (unitVector j) i) * v y i
        + (φ y * c y i) * G y (unitVector j) i) (fun i _ => (iT i).add (iU i))
    rw [hfs]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_add (iT i) (iU i), hw1 i]
    ring
  have hpt : ∀ y, ∑ i : Fin 3, ((fderiv ℝ φ y (unitVector j) * c y i + φ y * fderiv ℝ c y (unitVector j) i) * v y i
      + (φ y * c y i) * G y (unitVector j) i) = fderiv ℝ φ y (unitVector j) * inner ℝ (c y) (v y) +
        φ y * (inner ℝ (v y) (fderiv ℝ c y (unitVector j)) + inner ℝ (c y) (G y (unitVector j))) := by
    intro y
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
    ring
  simp only [hpt] at hsum
  have i1 := cint ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector j)) l1
  have i2 := cint hφ.1.continuous hφ.2 (l2 j)
  rw [integral_add i1 i2] at hsum
  linarith

theorem single_cont (i : Fin 3) : Continuous (fun x : ℝ => (EuclideanSpace.single i x : Space)) := by
  have : (fun x : ℝ => (EuclideanSpace.single i x : Space)) = fun x => x • (EuclideanSpace.single i (1 : ℝ) : Space) := by
    funext x
    ext k
    simp only [EuclideanSpace.single_apply, PiLp.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [this]
  fun_prop

theorem cross_cont : Continuous (fun p : Space × Space => crossVec p.1 p.2) := by
  unfold crossVec
  refine (((single_cont 0).comp ?_).add ((single_cont 1).comp ?_)).add ((single_cont 2).comp ?_) <;> fun_prop

theorem curl_cont : Continuous curlOf := by
  unfold curlOf entry
  fun_prop

theorem cross_sq (a b : Space) : ‖crossVec a b‖ ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := by
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three]
  simp [crossVec]
  nlinarith [sq_nonneg (a 0 * b 0 + a 1 * b 1 + a 2 * b 2)]

theorem cross_le (a b : Space) : ‖crossVec a b‖ ≤ ‖a‖ * ‖b‖ := by
  have h := cross_sq a b
  have h0 : 0 ≤ ‖a‖ * ‖b‖ := by positivity
  by_contra hc
  push_neg at hc
  nlinarith [mul_self_lt_mul_self h0 hc]

theorem entry_le (M : Space →L[ℝ] Space) (l j : Fin 3) : |entry M l j| ≤ ‖M‖ := by
  unfold entry
  rw [← Real.norm_eq_abs]
  refine (PiLp.norm_apply_le _ _).trans ?_
  refine (M.le_opNorm _).trans ?_
  rw [unit_norm, mul_one]

theorem sign_le (i j l : Fin 3) : |permSign i j l| ≤ 1 := by
  unfold permSign
  split_ifs <;> norm_num

theorem curl_le (M : Space →L[ℝ] Space) : ‖curlOf M‖ ≤ 27 * ‖M‖ := by
  unfold curlOf
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ i : Fin 3, ‖(∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * entry M l j) • unitVector i‖ ≤ 9 * ‖M‖ := by
    intro i
    rw [norm_smul, unit_norm, mul_one, Real.norm_eq_abs]
    have h1 : ∀ j l : Fin 3, |permSign i j l * entry M l j| ≤ ‖M‖ := by
      intro j l
      rw [abs_mul]
      have := sign_le i j l
      have := entry_le M l j
      nlinarith [abs_nonneg (permSign i j l), abs_nonneg (entry M l j)]
    calc |∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * entry M l j|
        ≤ ∑ j : Fin 3, |∑ l : Fin 3, permSign i j l * entry M l j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, |permSign i j l * entry M l j| :=
          Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖M‖ := Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => h1 j l
      _ = 9 * ‖M‖ := by simp [Fin.sum_univ_three]; ring
  calc ∑ i : Fin 3, ‖(∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * entry M l j) • unitVector i‖
      ≤ ∑ i : Fin 3, 9 * ‖M‖ := Finset.sum_le_sum fun i _ => h i
    _ = 27 * ‖M‖ := by simp [Fin.sum_univ_three]; ring

theorem adj_le (A : Space →L[ℝ] Space) (w : Space) : ‖ContinuousLinearMap.adjoint A w‖ ≤ ‖A‖ * ‖w‖ := by
  refine ((ContinuousLinearMap.adjoint A).le_opNorm w).trans ?_
  rw [LinearIsometryEquiv.norm_map]

theorem sqK {v : Space → Space} (hvm : AEStronglyMeasurable v volume) (h6 : MemLp v 6 volume) {K : Set Space}
    (hK : volume K ≠ ⊤) : IntegrableOn (fun y => ‖v y‖ ^ 2) K := by
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK
  have h2 : MemLp v 2 (volume.restrict K) := (h6.restrict K).mono_exponent (by norm_num)
  exact (memLp_two_iff_integrable_sq_norm hvm.restrict).1 h2

theorem memLp_ind {v : Space → Space} (h6 : MemLp v 6 volume) {K : Set Space} (hKm : MeasurableSet K)
    (hK : volume K ≠ ⊤) : MemLp (K.indicator v) 2 volume := by
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK
  rw [memLp_indicator_iff_restrict hKm]
  exact (h6.restrict K).mono_exponent (by norm_num)

theorem li_bound {f : Space → ℝ} {g : Space → Space} (hg : LocallyIntegrable g volume)
    (hf : AEStronglyMeasurable f volume) {B : ℝ} (h : ∀ y, |f y| ≤ B * ‖g y‖) : LocallyIntegrable f volume := by
  refine (hg.smul B).mono hf (ae_of_all _ fun y => ?_)
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact (h y).trans (mul_le_mul_of_nonneg_right (le_abs_self B) (norm_nonneg _))

theorem grad_field {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hso : IsSecondOrderField m v G H)
    {c : Space → Space} (hc : ContDiff ℝ 1 c) {B : ℝ} (hcB : ∀ y, ‖c y‖ ≤ B) (hdB : ∀ y, ‖fderiv ℝ c y‖ ≤ B) :
    IsGradientField (fun y => -(ContinuousLinearMap.adjoint (fderiv ℝ c y) (v y)
      + ContinuousLinearMap.adjoint (G y) (c y))) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hcB 0)
  have hvm := hso.measurable_velocity
  have h6 := hso.velocity_six
  have hGm := hso.measurable_gradient
  have hG2 := hso.gradient_two
  have hv := li_v h6
  have hcm : AEStronglyMeasurable c volume := hc.continuous.aestronglyMeasurable
  have hDm : AEStronglyMeasurable (fun y => fderiv ℝ c y) volume :=
    (hc.continuous_fderiv one_ne_zero).aestronglyMeasurable
  have hQm : AEStronglyMeasurable (fun y => -(ContinuousLinearMap.adjoint (fderiv ℝ c y) (v y)
      + ContinuousLinearMap.adjoint (G y) (c y))) volume :=
    ((aesm_adj hDm hvm).add (aesm_adj hGm hcm)).neg
  refine ⟨fun y => -inner ℝ (c y) (v y), ?_, ?_, hQm, ?_⟩
  · intro K hK
    have hv2 := sqK hvm h6 hK.measure_lt_top.ne
    refine (hv2.const_mul (B ^ 2)).mono' ((hcm.inner hvm).neg.pow 2).restrict (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), neg_sq]
    have h1 := abs_real_inner_le_norm (c y) (v y)
    have h2 : ‖c y‖ * ‖v y‖ ≤ B * ‖v y‖ := mul_le_mul_of_nonneg_right (hcB y) (norm_nonneg _)
    have h4 := pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
    rw [sq_abs, mul_pow] at h4
    exact h4
  · intro K hK
    have hv2 := sqK hvm h6 hK.measure_lt_top.ne
    have hGi : Integrable (fun y => 6 * B ^ 2 * entrySq (G y)) := hG2.const_mul _
    refine ((hv2.const_mul (2 * B ^ 2)).add hGi.integrableOn).mono' (hQm.norm.pow 2).restrict
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_neg]
    have e1 := adj_le (fderiv ℝ c y) (v y)
    have e2 := adj_le (G y) (c y)
    have e3 : ‖fderiv ℝ c y‖ * ‖v y‖ ≤ B * ‖v y‖ := mul_le_mul_of_nonneg_right (hdB y) (norm_nonneg _)
    have e4 : ‖G y‖ * ‖c y‖ ≤ ‖G y‖ * B := mul_le_mul_of_nonneg_left (hcB y) (norm_nonneg _)
    have e5 := norm_add_le (ContinuousLinearMap.adjoint (fderiv ℝ c y) (v y)) (ContinuousLinearMap.adjoint (G y) (c y))
    have e6 := mul_le_mul_of_nonneg_left (opNorm_sq_le (G y)) (by positivity : (0 : ℝ) ≤ 2 * B ^ 2)
    set X := ‖ContinuousLinearMap.adjoint (fderiv ℝ c y) (v y) + ContinuousLinearMap.adjoint (G y) (c y)‖
    have hX : X ≤ B * ‖v y‖ + ‖G y‖ * B := by linarith
    have hX0 : 0 ≤ X := norm_nonneg _
    show X ^ 2 ≤ 2 * B ^ 2 * ‖v y‖ ^ 2 + 6 * B ^ 2 * entrySq (G y)
    calc X ^ 2 ≤ (B * ‖v y‖ + ‖G y‖ * B) ^ 2 := pow_le_pow_left₀ hX0 hX 2
      _ ≤ 2 * B ^ 2 * ‖v y‖ ^ 2 + 2 * B ^ 2 * ‖G y‖ ^ 2 := by nlinarith [sq_nonneg (B * ‖v y‖ - ‖G y‖ * B)]
      _ ≤ _ := by nlinarith [e6]
  · intro φ hφ j
    have hcol : ∀ j, LocallyIntegrable (fun y => G y (unitVector j)) volume := li_col hGm hG2
    have l1 : LocallyIntegrable (fun y => inner ℝ (c y) (v y)) volume :=
      li_bound hv (hcm.inner hvm) fun y =>
        (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hcB y) (norm_nonneg _))
    have l2 : ∀ j, LocallyIntegrable (fun y => inner ℝ (v y) (fderiv ℝ c y (unitVector j))
        + inner ℝ (c y) (G y (unitVector j))) volume := by
      intro j
      refine LocallyIntegrable.add ?_ ?_
      · refine li_bound (B := B) hv (hvm.inner (aesm_apply hDm (aestronglyMeasurable_const))) fun y => ?_
        refine (abs_real_inner_le_norm _ _).trans ?_
        have : ‖fderiv ℝ c y (unitVector j)‖ ≤ B := by
          refine ((fderiv ℝ c y).le_opNorm _).trans ?_
          rw [unit_norm, mul_one]; exact hdB y
        nlinarith [norm_nonneg (v y), norm_nonneg (fderiv ℝ c y (unitVector j))]
      · refine li_bound (B := B) (hcol j) (hcm.inner (hcol j).aestronglyMeasurable) fun y => ?_
        exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hcB y) (norm_nonneg _))
    have hp := product_rule hv hcol hso.weak_gradient hc l1 l2 hφ j
    have eQ : ∀ y, inner ℝ (-(ContinuousLinearMap.adjoint (fderiv ℝ c y) (v y)
        + ContinuousLinearMap.adjoint (G y) (c y))) (unitVector j) =
        -(inner ℝ (v y) (fderiv ℝ c y (unitVector j)) + inner ℝ (c y) (G y (unitVector j))) := by
      intro y
      rw [inner_neg_left, inner_add_left, ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.adjoint_inner_left]
    simp only [eQ, mul_neg, integral_neg, hp]

theorem memLp_sym {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hvm : AEStronglyMeasurable v volume)
    (h6 : MemLp v 6 volume) (hGm : AEStronglyMeasurable G volume) (hG2 : Integrable (fun y => entrySq (G y)))
    {W : Space → Space} {DW : Space → (Space →L[ℝ] Space)} (hWm : AEStronglyMeasurable W volume)
    (hDWm : AEStronglyMeasurable DW volume) {K : ℝ} (hW : ∀ y, ‖W y‖ ≤ K)
    (hDW : ∀ y, ‖DW y‖ ≤ K * (1 + ‖y‖) ^ (-(2 : ℝ))) :
    MemLp (fun y => (2 : ℝ) • symProduct W DW v G y) 2 volume := by
  have e : (fun y => (2 : ℝ) • symProduct W DW v G y) = fun y => G y (W y) + DW y (v y) := by
    funext y
    simp only [symProduct, smul_smul]
    norm_num
  rw [e]
  refine MemLp.add ?_ ?_
  · refine ((memLp_grad hGm hG2).const_smul K).of_le (aesm_apply hGm hWm) (ae_of_all _ fun y => ?_)
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
    refine ((G y).le_opNorm (W y)).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right ((hW y).trans (le_abs_self K)) (norm_nonneg _)
  · have hm := aesm_apply hDWm hvm
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    have i6 : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(6 : ℝ))) :=
      integrable_one_add_norm (by simp only [finrank_euclideanSpace_fin, Nat.cast_ofNat]; norm_num)
    have iv : Integrable (fun y => ‖v y‖ ^ 6) := h6.integrable_norm_pow (p := 6) (by norm_num)
    refine ((i6.add iv).const_mul (K ^ 2)).mono' (hm.norm.pow 2) (ae_of_all _ fun y => ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have ht : 0 ≤ (1 + ‖y‖) ^ (-(2 : ℝ)) := by positivity
    have ht3 : ((1 + ‖y‖) ^ (-(2 : ℝ))) ^ 3 = (1 + ‖y‖) ^ (-(6 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    have h1 : ‖DW y (v y)‖ ≤ K * (1 + ‖y‖) ^ (-(2 : ℝ)) * ‖v y‖ :=
      ((DW y).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hDW y) (norm_nonneg _))
    have h2 : ‖DW y (v y)‖ ^ 2 ≤ K ^ 2 * (((1 + ‖y‖) ^ (-(2 : ℝ))) ^ 2 * ‖v y‖ ^ 2) := by
      calc ‖DW y (v y)‖ ^ 2 ≤ (K * (1 + ‖y‖) ^ (-(2 : ℝ)) * ‖v y‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = _ := by ring
    have h3 := weight_split ((1 + ‖y‖) ^ (-(2 : ℝ))) (‖v y‖ ^ 2) ht (sq_nonneg _)
    rw [← ht3]
    calc ‖DW y (v y)‖ ^ 2 ≤ K ^ 2 * (((1 + ‖y‖) ^ (-(2 : ℝ))) ^ 2 * ‖v y‖ ^ 2) := h2
      _ ≤ K ^ 2 * (((1 + ‖y‖) ^ (-(2 : ℝ))) ^ 3 + (‖v y‖ ^ 2) ^ 3) := mul_le_mul_of_nonneg_left h3 (sq_nonneg K)
      _ = _ := by ring

theorem aesm_cross {f g : Space → Space} (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (fun y => crossVec (f y) (g y)) volume :=
  Continuous.comp_aestronglyMeasurable₂ (g := crossVec) cross_cont hf hg

theorem aesm_curl {G : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume) :
    AEStronglyMeasurable (fun y => curlOf (G y)) volume :=
  curl_cont.comp_aestronglyMeasurable hG

theorem cross_sub_right (a b b' : Space) : crossVec a (b - b') = crossVec a b - crossVec a b' := by
  ext i
  fin_cases i <;> simp [crossVec] <;> ring

theorem cross_sub_left (a a' b : Space) : crossVec (a - a') b = crossVec a b - crossVec a' b := by
  ext i
  fin_cases i <;> simp [crossVec] <;> ring

theorem cross_zero_left (b : Space) : crossVec 0 b = 0 := by
  ext i
  fin_cases i <;> simp [crossVec]

variable {k N : ℕ}

theorem rows_congr (d : FracCertData k N) {F F' : Space → Space}
    (h : ∀ a, l2Pair F (d.row a) = l2Pair F' (d.row a)) : d.rows F = d.rows F' := by
  unfold FracCertData.rows rowSize
  simp only [h]

theorem pair_ind {F e : Space → Space} {R : Set Space} (he : ∀ y ∉ R, e y = 0) :
    l2Pair F e = l2Pair (R.indicator F) e := by
  unfold l2Pair
  congr 1
  funext y
  by_cases hy : y ∈ R
  · rw [Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy, he y hy, inner_zero_right, inner_zero_right]

theorem rows_add (d : FracCertData k N) (hw : ∀ a, 0 ≤ d.rowWeight a) (he : ∀ a, MemLp (d.row a) 2 volume)
    {X Y : Space → Space} (hX : MemLp X 2 volume) (hY : MemLp Y 2 volume) :
    d.rows (fun y => X y + Y y) ≤ d.rows X + d.rows Y :=
  rowSize_le hw fun a => by
    have : l2Pair (fun y => X y + Y y) (d.row a) = l2Pair X (d.row a) + l2Pair Y (d.row a) := by
      unfold l2Pair
      rw [← integral_add (inner_integrable hX (he a)) (inner_integrable hY (he a))]
      congr 1
      funext y
      rw [inner_add_left]
    rw [this]
    exact abs_add_le _ _

theorem rows_smul (d : FracCertData k N) (hw : ∀ a, 0 ≤ d.rowWeight a) (t : ℝ) (X : Space → Space) :
    d.rows (fun y => t • X y) = |t| * d.rows X := by
  unfold FracCertData.rows rowSize l2Pair
  have h : ∀ a, (∫ y, inner ℝ (t • X y) (d.row a y)) = t * ∫ y, inner ℝ (X y) (d.row a y) := fun a => by
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [real_inner_smul_left]
  simp only [h]
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem rows_zero (d : FracCertData k N) : d.rows (fun _ => (0 : Space)) = 0 := by
  unfold FracCertData.rows rowSize l2Pair
  simp

theorem rows_sum (d : FracCertData k N) (hw : ∀ a, 0 ≤ d.rowWeight a) (he : ∀ a, MemLp (d.row a) 2 volume)
    {ι : Type*} (s : Finset ι) (X : ι → Space → Space) (hX : ∀ i, MemLp (X i) 2 volume) :
    d.rows (fun y => ∑ i ∈ s, X i y) ≤ ∑ i ∈ s, d.rows (X i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    rw [rows_zero]
  · intro i s hi ih
    simp only [Finset.sum_insert hi]
    refine (rows_add d hw he (hX i) (memLp_finset_sum s fun j _ => hX j)).trans ?_
    linarith

theorem es_nonneg (M : Space →L[ℝ] Space) : 0 ≤ entrySq M := by
  unfold entrySq
  positivity

theorem bound_one {C t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : C * t ≤ |C| := by
  have h1 := mul_le_mul_of_nonneg_right (le_abs_self C) ht0
  have h2 := mul_le_mul_of_nonneg_left ht1 (abs_nonneg C)
  linarith

theorem bound_abs {C t : ℝ} (ht0 : 0 ≤ t) : C * t ≤ |C| * t := mul_le_mul_of_nonneg_right (le_abs_self C) ht0

theorem turn_cont : Continuous (fun y : Space => axialTurn y) := by
  have : (fun y : Space => axialTurn y) = fun y => turnCLM y := funext fun y => (turnCLM_apply y).symm
  rw [this]
  exact turnCLM.continuous

theorem sum_mul_le_sqrt {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    ∑ i ∈ s, f i * g i ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s f g
  have h0 : 0 ≤ ∑ i ∈ s, f i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [← Real.sqrt_mul h0]
  exact (le_abs_self _).trans (Real.abs_le_sqrt h)

end ModelFieldInternal

open SteadyCert ModelFieldInternal SteadyCert.HeldWeakProfilePartsInternal FracInternal.HeldExists in
theorem modelField_of (h1 : ChosenAgreeStatement) (h2 : CrossIdentityStatement) (h3 : SecondIdentityStatement) :
    ModelFieldStatement := by
  intro α hα1 hα2 k N c hc p hp v G H hso P hP hD κ
  have hso' : IsSecondOrderField c.order v G H := hso
  have hb := hc.base
  obtain ⟨hG', hH'⟩ := h1 c.order v G H hso'
  have hvm := hso'.measurable_velocity
  have h6 := hso'.velocity_six
  have hGm := hso'.measurable_gradient
  have hG2 := hso'.gradient_two
  have hw0 : ∀ a, 0 ≤ c.rowWeight a := fun a => (hb.rowWeight_pos a).le
  have he : ∀ a, MemLp (c.row a) 2 volume := hb.row_two
  obtain ⟨Cc, hCc⟩ := hc.centre_bounds
  obtain ⟨Cp, hCp⟩ := hb.profile_bounds
  obtain ⟨Cm, hCm⟩ := hc.model_bounded
  have hRm := hc.cellRegion_measurable
  have hRfin : volume c.cellRegion ≠ ⊤ := hc.cellRegion_bounded.measure_lt_top.ne
  have t1 : ∀ y : Space, 0 ≤ (1 + ‖y‖) ^ (-(1 : ℝ)) ∧ (1 + ‖y‖) ^ (-(1 : ℝ)) ≤ 1 := fun y =>
    ⟨by positivity, Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)⟩
  have t2 : ∀ y : Space, 0 ≤ (1 + ‖y‖) ^ (-(2 : ℝ)) ∧ (1 + ‖y‖) ^ (-(2 : ℝ)) ≤ 1 := fun y =>
    ⟨by positivity, Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)⟩
  have cenB : ∀ y, ‖c.centre y‖ ≤ |Cc| := fun y => (hCc y).1.trans (bound_one (t1 y).1 (t1 y).2)
  have cenD : ∀ y, ‖c.centreGrad y‖ ≤ |Cc| := fun y => (hCc y).2.1.trans (bound_one (t2 y).1 (t2 y).2)
  have hcs := hc.centre_smooth
  have hps := hb.profile_smooth p hp
  have hcm : AEStronglyMeasurable c.centre volume := hcs.continuous.aestronglyMeasurable
  have hDcm : AEStronglyMeasurable c.centreGrad volume :=
    (hcs.continuous_fderiv one_ne_zero).aestronglyMeasurable
  have hQ := grad_field hso' hcs (B := |Cc|) cenB cenD
  refine ⟨_, hQ, ?_⟩
  obtain ⟨A, hA_def⟩ : ∃ A : Space → Space, A = fun y => (2 : ℝ) • symProduct (fun z => c.profile p z - c.centre z)
    (fun z => c.gradProfile p z - c.centreGrad z) v G y := ⟨_, rfl⟩
  obtain ⟨Bf, hB_def⟩ : ∃ Bf : Space → Space, Bf = fun y => crossVec (curlOf (G y)) (c.velocityError y) := ⟨_, rfl⟩
  obtain ⟨Cf, hC_def⟩ : ∃ Cf : Space → Space, Cf = fun y => crossVec (c.curlError y) (v y) := ⟨_, rfl⟩
  obtain ⟨Df, hD_def⟩ : ∃ Df : Space → Space, Df = fun y => (c.rotationRate p - c.modelRate) • (G y (axialTurn y) - axialTurn (v y))
 := ⟨_, rfl⟩
  obtain ⟨X, hX_def⟩ : ∃ X : Fin k → Space → Space, X = fun i y => c.actuator i y - c.modelActuator i y := ⟨_, rfl⟩
  obtain ⟨Ef, hE_def⟩ : ∃ Ef : Space → Space, Ef = fun y => ∑ i, κ i • X i y := ⟨_, rfl⟩
  have hA : MemLp A 2 volume := by
    rw [hA_def]
    refine memLp_sym hvm h6 hGm hG2 (hps.continuous.aestronglyMeasurable.sub hcm)
      (((hps.continuous_fderiv one_ne_zero).aestronglyMeasurable).sub hDcm) (K := |Cp| + |Cc|)
      (fun y => ?_) (fun y => ?_)
    · refine (norm_sub_le _ _).trans (add_le_add ?_ (cenB y))
      exact ((hCp p hp y).1).trans (bound_one (t1 y).1 (t1 y).2)
    · refine (norm_sub_le _ _).trans ?_
      have e1 : ‖c.gradProfile p y‖ ≤ |Cp| * (1 + ‖y‖) ^ (-(2 : ℝ)) :=
        ((hCp p hp y).2.1).trans (bound_abs (t2 y).1)
      have e2 : ‖c.centreGrad y‖ ≤ |Cc| * (1 + ‖y‖) ^ (-(2 : ℝ)) := ((hCc y).2.1).trans (bound_abs (t2 y).1)
      linarith
  obtain ⟨Kv, hKv⟩ : ∃ Kv : ℝ, Kv = |Cc| + |Cm| := ⟨_, rfl⟩
  have hve : ∀ y, ‖c.velocityError y‖ ≤ Kv := by
    intro y
    unfold FracCellData.velocityError
    by_cases hy : y ∈ c.cellRegion
    · rw [Set.indicator_of_mem hy, hKv]
      refine (norm_sub_le _ _).trans (add_le_add (cenB y) ?_)
      exact ((hCm y hy).1).trans (le_abs_self _)
    · rw [Set.indicator_of_notMem hy, norm_zero, hKv]
      positivity
  have hveM : AEStronglyMeasurable c.velocityError volume :=
    (hcm.sub hc.model_measurable.1).indicator hRm
  have hBm : AEStronglyMeasurable Bf volume := by
    rw [hB_def]
    exact aesm_cross (aesm_curl hGm) hveM
  have hB2 : MemLp Bf 2 volume := by
    refine ((memLp_grad hGm hG2).const_smul (27 * Kv)).of_le hBm (ae_of_all _ fun y => ?_)
    have hKv0 : 0 ≤ Kv := by rw [hKv]; positivity
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), hB_def]
    refine (cross_le _ _).trans ?_
    have := curl_le (G y)
    have := hve y
    nlinarith [norm_nonneg (curlOf (G y)), norm_nonneg (c.velocityError y), norm_nonneg (G y)]
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ, Kc = 27 * |Cc| + |Cm| := ⟨_, rfl⟩
  have hce : ∀ y, ‖c.curlError y‖ * ‖v y‖ ≤ Kc * ‖c.cellRegion.indicator v y‖ := by
    intro y
    unfold FracCellData.curlError
    by_cases hy : y ∈ c.cellRegion
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hKc]
      refine mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) (norm_nonneg _)
      · exact (curl_le _).trans (by nlinarith [cenD y])
      · exact ((hCm y hy).2.1).trans (le_abs_self _)
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
      simp
  have hceM : AEStronglyMeasurable c.curlError volume :=
    ((aesm_curl hDcm).sub hc.model_measurable.2.1).indicator hRm
  have hCm' : AEStronglyMeasurable Cf volume := by
    rw [hC_def]
    exact aesm_cross hceM hvm
  have hvR := memLp_ind h6 hRm hRfin
  have hC2 : MemLp Cf 2 volume := by
    refine (hvR.const_smul Kc).of_le hCm' (ae_of_all _ fun y => ?_)
    have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hKc0, hC_def]
    exact (cross_le _ _).trans (hce y)
  obtain ⟨ρ, hρ⟩ := hc.cellRegion_bounded.subset_closedBall 0
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℝ, Δ = c.rotationRate p - c.modelRate := ⟨_, rfl⟩
  have hDm : AEStronglyMeasurable Df volume := by
    rw [hD_def]
    exact ((aesm_apply hGm turn_cont.aestronglyMeasurable).sub (turn_cont.comp_aestronglyMeasurable hvm)).const_smul
      (c.rotationRate p - c.modelRate)
  have hD2 : MemLp (c.cellRegion.indicator Df) 2 volume := by
    have hg : MemLp (fun y => |Δ| * (|ρ| * ‖G y‖ + ‖c.cellRegion.indicator v y‖)) 2 volume :=
      (((memLp_grad hGm hG2).norm.const_mul |ρ|).add hvR.norm).const_mul |Δ|
    refine hg.of_le (hDm.indicator hRm) (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases hy : y ∈ c.cellRegion
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hD_def, norm_smul, Real.norm_eq_abs, ← hΔ]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine (norm_sub_le _ _).trans (add_le_add ?_ (norm_axialTurn_le' _))
      have hy' : ‖y‖ ≤ ρ := by simpa using hρ hy
      refine ((G y).le_opNorm _).trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (((norm_axialTurn_le' y).trans hy').trans (le_abs_self _)) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hy, norm_zero]
      positivity
  have hXm : ∀ i, MemLp (X i) 2 volume := fun i => by
    rw [hX_def]
    exact (hb.actuator_two i).sub (hc.modelActuator_data i).1
  have hE2 : MemLp Ef 2 volume := by
    rw [hE_def]
    exact memLp_finset_sum _ fun i _ => (hXm i).const_smul (κ i)
  have key : ∀ y ∈ c.cellRegion, FracCellData.chosenGrad c.order v y = G y → FracCellData.chosenSecond c.order v y = H y →
      (c.toCertData α).localField α p v G H κ y - (c.toCertData α).modelField p v κ y
        + -(ContinuousLinearMap.adjoint (fderiv ℝ c.centre y) (v y) + ContinuousLinearMap.adjoint (G y) (c.centre y))
        = A y + Bf y + Cf y + c.cellRegion.indicator Df y + Ef y := by
    intro y hy hy1 hy2
    have hx := h2 (c.centre y) (v y) (c.centreGrad y) (G y)
    have hx' : crossVec (curlOf (G y)) (c.centre y) = G y (c.centre y) + c.centreGrad y (v y)
        - crossVec (curlOf (c.centreGrad y)) (v y) - ContinuousLinearMap.adjoint (c.centreGrad y) (v y)
        - ContinuousLinearMap.adjoint (G y) (c.centre y) := by
      rw [hx]; abel
    show c.toFracCertData.localField α p v G H κ y
        - c.modelFieldOf α v (FracCellData.chosenGrad c.order v) (FracCellData.chosenSecond c.order v) κ y
        + -(ContinuousLinearMap.adjoint (c.centreGrad y) (v y) + ContinuousLinearMap.adjoint (G y) (c.centre y))
        = A y + Bf y + Cf y + c.cellRegion.indicator Df y + Ef y
    simp only [FracCertData.localField, FracCellData.modelFieldOf, hy1, hy2, hA_def, hB_def, hC_def, hE_def,
      hX_def, Set.indicator_of_mem hy, FracCellData.velocityError, FracCellData.curlError, FracCellData.centreCurl,
      cross_sub_right, cross_sub_left, symProduct, driftField, hD_def, smul_smul, smul_sub, sub_smul,
      Finset.sum_sub_distrib, map_sub, ContinuousLinearMap.sub_apply, FracCertData.gradProfile, FracCellData.centreGrad]
    simp only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
    simp only [FracCellData.centreGrad] at hx'
    rw [hx']
    abel

  have hdec : ∀ a, l2Pair (fun y => (c.toCertData α).localField α p v G H κ y - (c.toCertData α).modelField p v κ y
        + -(ContinuousLinearMap.adjoint (fderiv ℝ c.centre y) (v y) + ContinuousLinearMap.adjoint (G y) (c.centre y)))
        (c.row a) = l2Pair (fun y => A y + Bf y + Cf y + c.cellRegion.indicator Df y + Ef y) (c.row a) := by
    intro a
    unfold l2Pair
    refine integral_congr_ae ?_
    filter_upwards [hG', hH'] with y hy1 hy2
    by_cases hy : y ∈ c.cellRegion
    · rw [key y hy hy1 hy2]
    · rw [hc.row_in_cells a y hy, inner_zero_right, inner_zero_right]
  show c.toFracCertData.rows (fun y => (c.toCertData α).localField α p v G H κ y - (c.toCertData α).modelField p v κ y
        + -(ContinuousLinearMap.adjoint (fderiv ℝ c.centre y) (v y) + ContinuousLinearMap.adjoint (G y) (c.centre y)))
      ≤ c.rowLoss * c.toFracCertData.size G H κ
  rw [rows_congr c.toFracCertData hdec]
  have hcw0 := hc.cellWeight_nonneg
  have hcwm : AEStronglyMeasurable c.cellWeight volume := hc.cellWeight_measurable.aestronglyMeasurable
  have hrm := hb.rowMax_pos.le
  obtain ⟨cL0, rL0, -, -, vL0, kL0, -, aL0, -⟩ := hc.losses_nonneg'
  obtain ⟨ES, hES⟩ : ∃ ES, ES = ∫ y, entrySq (G y) := ⟨_, rfl⟩
  have ES0 : 0 ≤ ES := hES ▸ integral_nonneg fun y => es_nonneg _
  have hEn : c.weightMin * ES ≤ c.toFracCertData.energy G H := by
    have hw0' : ∀ y, 0 ≤ c.weight y := fun y => hb.weightMin_pos.le.trans (hb.weight_lower y)
    have i1 : Integrable (fun y => c.weight y * entrySq (G y)) :=
      (hG2.const_mul c.weightMax).mono' (hb.weight_measurable.aestronglyMeasurable.mul hG2.aestronglyMeasurable)
        (ae_of_all _ fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0' y) (es_nonneg _))]
          exact mul_le_mul_of_nonneg_right (hb.weight_upper y) (es_nonneg _))
    have h1 : c.weightMin * ES ≤ ∫ y, c.weight y * entrySq (G y) := by
      rw [hES, ← integral_const_mul]
      exact integral_mono (hG2.const_mul _) i1 fun y => mul_le_mul_of_nonneg_right (hb.weight_lower y) (es_nonneg _)
    have h2 : 0 ≤ ∫ y, ‖secondTrace (H y)‖ ^ 2 := integral_nonneg fun y => sq_nonneg _
    unfold FracCertData.energy weightedEnergy
    linarith
  have En0 : 0 ≤ c.toFracCertData.energy G H := le_trans (mul_nonneg hb.weightMin_pos.le ES0) hEn
  have hsz : c.toFracCertData.size G H κ =
      Real.sqrt (c.toFracCertData.energy G H + c.multiplierScale ^ 2 * ∑ i, κ i ^ 2) := rfl
  have hsz1 : Real.sqrt (c.toFracCertData.energy G H) ≤ c.toFracCertData.size G H κ := by
    rw [hsz]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (by positivity))
  have hsz2 : c.multiplierScale * vecNorm κ ≤ c.toFracCertData.size G H κ := by
    rw [hsz]
    unfold vecNorm
    have e : c.multiplierScale * Real.sqrt (∑ i, κ i ^ 2) = Real.sqrt (c.multiplierScale ^ 2 * ∑ i, κ i ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hb.multiplierScale_pos.le]
    rw [e]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_left En0)
  have hsz3 : Real.sqrt ES * Real.sqrt c.weightMin ≤ c.toFracCertData.size G H κ := by
    rw [← Real.sqrt_mul ES0, mul_comm]
    exact (Real.sqrt_le_sqrt hEn).trans hsz1
  have bA : c.toFracCertData.rows A ≤ Real.sqrt c.rowMax * (c.centreLoss * Real.sqrt (c.toFracCertData.energy G H)) := by
    have iA : Integrable (fun y => ‖A y‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hA.1).1 hA
    have i2 : Integrable (fun y => c.cellWeight y * ‖A y‖ ^ 2) :=
      (iA.const_mul c.rowMax).mono' (hcwm.mul iA.aestronglyMeasurable) (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hcw0 y) (sq_nonneg _))]
        exact mul_le_mul_of_nonneg_right (hc.cellWeight_le y) (sq_nonneg _))
    have h3' : (∫ y, c.cellWeight y * ‖A y‖ ^ 2) ≤ c.rowMax * ∫ y, ‖A y‖ ^ 2 := by
      rw [← integral_const_mul]
      exact integral_mono i2 (iA.const_mul _) fun y => mul_le_mul_of_nonneg_right (hc.cellWeight_le y) (sq_nonneg _)
    have hl : l2Norm A ≤ c.centreLoss * Real.sqrt (c.toFracCertData.energy G H) := by
      rw [hA_def]
      exact hc.centreLoss_bound p hp v G H hso'
    calc c.toFracCertData.rows A ≤ Real.sqrt (∫ y, c.cellWeight y * ‖A y‖ ^ 2) :=
          (le_abs_self _).trans (Real.abs_le_sqrt (hc.rows_dominated A hA))
      _ ≤ Real.sqrt (c.rowMax * ∫ y, ‖A y‖ ^ 2) := Real.sqrt_le_sqrt h3'
      _ = Real.sqrt c.rowMax * l2Norm A := by unfold l2Norm; exact Real.sqrt_mul hrm _
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg _)
  have bB : c.toFracCertData.rows Bf ≤ c.velocityLoss * Real.sqrt ES := by
    have iB : Integrable (fun y => ‖Bf y‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hB2.1).1 hB2
    have ic : Integrable (fun y => ‖curlOf (G y)‖ ^ 2) := by
      refine (hG2.const_mul (729 * 3)).mono' ((aesm_curl hGm).norm.pow 2) (ae_of_all _ fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have e1 := pow_le_pow_left₀ (norm_nonneg _) (curl_le (G y)) 2
      have e2 := opNorm_sq_le (G y)
      nlinarith
    have i2 : Integrable (fun y => c.cellWeight y * ‖Bf y‖ ^ 2) :=
      (iB.const_mul c.rowMax).mono' (hcwm.mul iB.aestronglyMeasurable) (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hcw0 y) (sq_nonneg _))]
        exact mul_le_mul_of_nonneg_right (hc.cellWeight_le y) (sq_nonneg _))
    have hpt : ∀ y, c.cellWeight y * ‖Bf y‖ ^ 2 ≤ c.velocityLoss ^ 2 * ‖curlOf (G y)‖ ^ 2 := by
      intro y
      have hvl := hc.velocityLoss_bound y
      have sq := pow_le_pow_left₀ (by positivity) hvl 2
      rw [mul_pow, Real.sq_sqrt (hcw0 y)] at sq
      have hb2 := pow_le_pow_left₀ (norm_nonneg _) (cross_le (curlOf (G y)) (c.velocityError y)) 2
      rw [hB_def]
      calc c.cellWeight y * ‖crossVec (curlOf (G y)) (c.velocityError y)‖ ^ 2
          ≤ c.cellWeight y * ((‖curlOf (G y)‖ * ‖c.velocityError y‖) ^ 2) := mul_le_mul_of_nonneg_left hb2 (hcw0 y)
        _ = (c.cellWeight y * ‖c.velocityError y‖ ^ 2) * ‖curlOf (G y)‖ ^ 2 := by ring
        _ ≤ c.velocityLoss ^ 2 * ‖curlOf (G y)‖ ^ 2 := mul_le_mul_of_nonneg_right sq (sq_nonneg _)
    have hI : (∫ y, c.cellWeight y * ‖Bf y‖ ^ 2) ≤ c.velocityLoss ^ 2 * ES := by
      rw [hES, ← (h3 c.order v G H hso').2.2, ← integral_const_mul]
      exact integral_mono i2 (ic.const_mul _) hpt
    calc c.toFracCertData.rows Bf ≤ Real.sqrt (∫ y, c.cellWeight y * ‖Bf y‖ ^ 2) :=
          (le_abs_self _).trans (Real.abs_le_sqrt (hc.rows_dominated Bf hB2))
      _ ≤ Real.sqrt (c.velocityLoss ^ 2 * ES) := Real.sqrt_le_sqrt hI
      _ = c.velocityLoss * Real.sqrt ES := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq vL0]
  have bC : c.toFracCertData.rows Cf ≤ c.curlLoss * Real.sqrt ES := by
    have iC : Integrable (fun y => ‖Cf y‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hC2.1).1 hC2
    have ivR : Integrable (fun y => ‖c.cellRegion.indicator v y‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm hvR.1).1 hvR
    have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
    have hg : Integrable (fun y => c.cellWeight y * ‖c.curlError y‖ ^ 2 * ‖v y‖ ^ 2) := by
      refine (ivR.const_mul (c.rowMax * Kc ^ 2)).mono' ((hcwm.mul (hceM.norm.pow 2)).mul (hvm.norm.pow 2))
        (ae_of_all _ fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := hcw0 y; positivity)]
      have e2 := pow_le_pow_left₀ (by positivity) (hce y) 2
      rw [mul_pow, mul_pow] at e2
      calc c.cellWeight y * ‖c.curlError y‖ ^ 2 * ‖v y‖ ^ 2
          = c.cellWeight y * (‖c.curlError y‖ ^ 2 * ‖v y‖ ^ 2) := by ring
        _ ≤ c.rowMax * (Kc ^ 2 * ‖c.cellRegion.indicator v y‖ ^ 2) :=
            mul_le_mul (hc.cellWeight_le y) e2 (by positivity) hrm
        _ = _ := by ring
    have i2 : Integrable (fun y => c.cellWeight y * ‖Cf y‖ ^ 2) :=
      (iC.const_mul c.rowMax).mono' (hcwm.mul iC.aestronglyMeasurable) (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hcw0 y) (sq_nonneg _))]
        exact mul_le_mul_of_nonneg_right (hc.cellWeight_le y) (sq_nonneg _))
    have hpt : ∀ y, c.cellWeight y * ‖Cf y‖ ^ 2 ≤ c.cellWeight y * ‖c.curlError y‖ ^ 2 * ‖v y‖ ^ 2 := by
      intro y
      have hb2 := pow_le_pow_left₀ (norm_nonneg _) (cross_le (c.curlError y) (v y)) 2
      rw [hC_def]
      calc c.cellWeight y * ‖crossVec (c.curlError y) (v y)‖ ^ 2
          ≤ c.cellWeight y * ((‖c.curlError y‖ * ‖v y‖) ^ 2) := mul_le_mul_of_nonneg_left hb2 (hcw0 y)
        _ = _ := by ring
    have hcl := hc.curlLoss_bound v G H hso'
    rw [← hES] at hcl
    have hI : (∫ y, c.cellWeight y * ‖Cf y‖ ^ 2) ≤ (c.curlLoss * Real.sqrt ES) ^ 2 := by
      refine (integral_mono i2 hg hpt).trans ?_
      have h0 : 0 ≤ ∫ y, c.cellWeight y * ‖c.curlError y‖ ^ 2 * ‖v y‖ ^ 2 :=
        integral_nonneg fun y => by have := hcw0 y; positivity
      rw [← Real.sq_sqrt h0]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hcl 2
    calc c.toFracCertData.rows Cf ≤ Real.sqrt (∫ y, c.cellWeight y * ‖Cf y‖ ^ 2) :=
          (le_abs_self _).trans (Real.abs_le_sqrt (hc.rows_dominated Cf hC2))
      _ ≤ Real.sqrt ((c.curlLoss * Real.sqrt ES) ^ 2) := Real.sqrt_le_sqrt hI
      _ = c.curlLoss * Real.sqrt ES := Real.sqrt_sq (mul_nonneg kL0 (Real.sqrt_nonneg _))
  have bD : c.toFracCertData.rows (c.cellRegion.indicator Df) ≤
      c.rateLoss * Real.sqrt (c.toFracCertData.energy G H) := by
    rw [← rows_congr c.toFracCertData fun a => pair_ind (hc.row_in_cells a), hD_def]
    exact hc.rateLoss_bound p hp v G H hso'
  have bE : c.toFracCertData.rows Ef ≤ c.actuatorLoss * vecNorm κ := by
    have s1 := rows_sum c.toFracCertData hw0 he Finset.univ (fun i y => κ i • X i y)
      (fun i => (hXm i).const_smul (κ i))
    have s2 : ∀ i, c.toFracCertData.rows (fun y => κ i • X i y) = |κ i| * c.toFracCertData.rows (X i) :=
      fun i => rows_smul _ hw0 _ _
    have cs := sum_mul_le_sqrt Finset.univ (fun i => |κ i|) (fun i => c.toFracCertData.rows (X i))
    simp only [sq_abs] at cs
    have hal : Real.sqrt (∑ i, c.toFracCertData.rows (X i) ^ 2) ≤ c.actuatorLoss := by
      rw [← Real.sqrt_sq aL0]
      refine Real.sqrt_le_sqrt ?_
      rw [hX_def]
      exact hc.actuatorLoss_bound
    rw [hE_def]
    calc c.toFracCertData.rows (fun y => ∑ i, κ i • X i y) ≤ ∑ i, c.toFracCertData.rows (fun y => κ i • X i y) := s1
      _ = ∑ i, |κ i| * c.toFracCertData.rows (X i) := Finset.sum_congr rfl fun i _ => s2 i
      _ ≤ Real.sqrt (∑ i, κ i ^ 2) * Real.sqrt (∑ i, c.toFracCertData.rows (X i) ^ 2) := cs
      _ ≤ vecNorm κ * c.actuatorLoss := mul_le_mul_of_nonneg_left hal (Real.sqrt_nonneg _)
      _ = _ := mul_comm _ _
  have tri : c.toFracCertData.rows (fun y => A y + Bf y + Cf y + c.cellRegion.indicator Df y + Ef y) ≤
      c.toFracCertData.rows A + c.toFracCertData.rows Bf + c.toFracCertData.rows Cf
        + c.toFracCertData.rows (c.cellRegion.indicator Df) + c.toFracCertData.rows Ef := by
    have m1 : MemLp (fun y => A y + Bf y) 2 volume := hA.add hB2
    have m2 : MemLp (fun y => A y + Bf y + Cf y) 2 volume := m1.add hC2
    have m3 : MemLp (fun y => A y + Bf y + Cf y + c.cellRegion.indicator Df y) 2 volume := m2.add hD2
    have r4 := rows_add c.toFracCertData hw0 he m3 hE2
    have r3 := rows_add c.toFracCertData hw0 he m2 hD2
    have r2 := rows_add c.toFracCertData hw0 he m1 hC2
    have r1 := rows_add c.toFracCertData hw0 he hA hB2
    linarith
  have hsw : 0 < Real.sqrt c.weightMin := Real.sqrt_pos.2 hb.weightMin_pos
  have hES' : Real.sqrt ES ≤ c.toFracCertData.size G H κ / Real.sqrt c.weightMin := by
    rw [le_div_iff₀ hsw]
    exact hsz3
  have hk' : vecNorm κ ≤ c.toFracCertData.size G H κ / c.multiplierScale := by
    rw [le_div_iff₀ hb.multiplierScale_pos]
    linarith [hsz2]
  have hrl := hc.rowLoss_ge
  have szn : 0 ≤ c.toFracCertData.size G H κ := Real.sqrt_nonneg _
  have f1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsz1 cL0) (Real.sqrt_nonneg c.rowMax)
  have f2 := mul_le_mul_of_nonneg_left hES' vL0
  have f3 := mul_le_mul_of_nonneg_left hES' kL0
  have f4 := mul_le_mul_of_nonneg_left hsz1 rL0
  have f5 := mul_le_mul_of_nonneg_left hk' aL0
  have f6 := mul_le_mul_of_nonneg_right hrl szn
  have f7 : (Real.sqrt c.rowMax * c.centreLoss + c.rateLoss + (c.velocityLoss + c.curlLoss) / Real.sqrt c.weightMin
      + c.actuatorLoss / c.multiplierScale) * c.toFracCertData.size G H κ =
      Real.sqrt c.rowMax * (c.centreLoss * c.toFracCertData.size G H κ)
        + c.velocityLoss * (c.toFracCertData.size G H κ / Real.sqrt c.weightMin)
        + c.curlLoss * (c.toFracCertData.size G H κ / Real.sqrt c.weightMin)
        + c.rateLoss * c.toFracCertData.size G H κ
        + c.actuatorLoss * (c.toFracCertData.size G H κ / c.multiplierScale) := by ring
  linarith [tri, bA, bB, bC, bD, bE]


end CellCert

end Breakdown
