import Breakdown.FracCell.StrainFaceDefs
import Breakdown.FracCell.LowEntry
import Breakdown.FracCell.PlaneDeleted
import Breakdown.FracCell.AngularFrame
import Breakdown.FracCert.DriftPowerSolenoidal

open MeasureTheory Set
open scoped ContDiff

noncomputable section

namespace Breakdown.CellCert.CellFormula.Internal.StrainFaceFaceTraceFree

open SteadyCert Assembly CellAnalysis Real

theorem frame_orth (θ : ℝ) (i l : Fin 3) :
    ∑ a : Fin 3, frameUnit θ a i * frameUnit θ a l = if i = l then 1 else 0 := by
  have h := Real.cos_sq_add_sin_sq θ
  fin_cases i <;> fin_cases l <;>
    simp [Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit] <;> nlinarith [h]

theorem mat_trace (θ : ℝ) (M : Space →L[ℝ] Space) :
    ∑ a : Fin 3, frameMat θ M a a = ∑ i : Fin 3, inner ℝ (M (unitVector i)) (unitVector i) := by
  simp only [CellEnergy.Internal.AngularFrame.mat_expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, frame_orth]
  simp [Finset.sum_ite_eq]

theorem third_trace (θ : ℝ) (H : Space →L[ℝ] Space →L[ℝ] Space) (c : Fin 3) :
    ∑ a : Fin 3, frameThird θ H a a c =
      ∑ j : Fin 3, frameUnit θ c j * ∑ i : Fin 3, inner ℝ (H (unitVector j) (unitVector i)) (unitVector i) := by
  have e : ∀ a, frameThird θ H a a c = frameMat θ (H (frameUnit θ c)) a a := fun a => rfl
  simp only [e, mat_trace]
  conv_lhs => rw [CellEnergy.Internal.AngularFrame.vec_expand (frameUnit θ c)]
  simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, sum_inner, real_inner_smul_left]
  rw [Finset.sum_comm]
  simp [Finset.mul_sum]

theorem opnorm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (M : Space →L[ℝ] E) :
    ‖M‖ ≤ ∑ i : Fin 3, ‖M (unitVector i)‖ := by
  refine M.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun u => ?_
  conv_lhs => rw [CellEnergy.Internal.AngularFrame.vec_expand u]
  rw [map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_smul, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u i) (norm_nonneg _)

theorem grad_loc {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsSecondOrderField m v G H) :
    LocallyIntegrable G volume := by
  have hl : ∀ i : Fin 3, LocallyIntegrable (fun y => ‖G y (unitVector i)‖) volume :=
    fun i => ((DriftPowerSolenoidalInternal.memLp_col h i).norm).locallyIntegrable (by norm_num)
  have hs : LocallyIntegrable (fun y => ∑ i : Fin 3, ‖G y (unitVector i)‖) volume := by
    simp only [Fin.sum_univ_three]
    exact ((hl 0).add (hl 1)).add (hl 2)
  refine hs.mono h.measurable_gradient (ae_of_all _ fun y => ?_)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  exact opnorm_le (G y)

theorem second_loc {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsSecondOrderField m v G H) :
    LocallyIntegrable H volume := by
  have hl : ∀ j i : Fin 3, LocallyIntegrable (fun y => ‖H y (unitVector j) (unitVector i)‖) volume :=
    fun j i => ((PlaneDeleted.memLp_second h.measurable_second h.second_two j i).norm).locallyIntegrable
      (by norm_num)
  have hs : LocallyIntegrable (fun y => ∑ j : Fin 3, ∑ i : Fin 3, ‖H y (unitVector j) (unitVector i)‖) volume := by
    simp only [Fin.sum_univ_three]
    exact ((((hl 0 0).add (hl 0 1)).add (hl 0 2)).add (((hl 1 0).add (hl 1 1)).add (hl 1 2))).add
      (((hl 2 0).add (hl 2 1)).add (hl 2 2))
  refine hs.mono h.measurable_second (ae_of_all _ fun y => ?_)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  refine (opnorm_le (H y)).trans (Finset.sum_le_sum fun j _ => ?_)
  exact opnorm_le (H y (unitVector j))

theorem second_trace {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsSecondOrderField m v G H) (j : Fin 3) :
    ∀ᵐ y ∂volume, ∑ i : Fin 3, inner ℝ (H y (unitVector j) (unitVector i)) (unitVector i) = 0 := by
  have hl : ∀ i : Fin 3, LocallyIntegrable (fun y => H y (unitVector j) (unitVector i)) volume :=
    fun i => (PlaneDeleted.memLp_second h.measurable_second h.second_two j i).locallyIntegrable (by norm_num)
  have hli : ∀ i : Fin 3, LocallyIntegrable
      (fun y => inner ℝ (H y (unitVector j) (unitVector i)) (unitVector i)) volume := fun i => by
    refine (hl i).mono (((hl i).aestronglyMeasurable).inner aestronglyMeasurable_const)
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    simp [unitVector]
  have hT : LocallyIntegrable (fun y => ∑ i : Fin 3, inner ℝ (H y (unitVector j) (unitVector i)) (unitVector i))
      volume := by
    simp only [Fin.sum_univ_three]
    exact ((hli 0).add (hli 1)).add (hli 2)
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hT fun ψ hψ hψc => ?_
  have htest : IsTestScalar ψ := ⟨hψ, hψc⟩
  have hdc := _root_.Breakdown.Internal.PressureMollify.contDiff_fderiv_apply hψ (unitVector j)
  have hds := _root_.Breakdown.Internal.PressureMollify.hasCompactSupport_fderiv_apply hψc (unitVector j)
  have hpair : ∀ i : Fin 3, ∫ y, ψ y * inner ℝ (H y (unitVector j) (unitVector i)) (unitVector i) =
      -∫ y, fderiv ℝ ψ y (unitVector j) * inner ℝ (G y (unitVector i)) (unitVector i) := by
    intro i
    have e := congrArg (fun w : Space => inner ℝ w (unitVector i)) (h.weak_second ψ htest i j)
    have hg := (DriftPowerSolenoidalInternal.locInt_col h i).integrable_smul_left_of_hasCompactSupport
      hdc.continuous hds
    have hh := (hl i).integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
    simp only [inner_neg_left] at e
    rw [real_inner_comm (unitVector i), real_inner_comm (unitVector i), ← integral_inner hg,
      ← integral_inner hh] at e
    simp only [real_inner_smul_right, DriftPowerSolenoidalInternal.unit_inner,
      DriftPowerSolenoidalInternal.unit_inner'] at e ⊢
    linarith
  have hI : ∀ i : Fin 3, Integrable (fun y => ψ y * inner ℝ (H y (unitVector j) (unitVector i)) (unitVector i)) :=
    fun i => by
      have := (hli i).integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
      simpa [smul_eq_mul] using this
  have hJ : ∀ i : Fin 3, Integrable (fun y => fderiv ℝ ψ y (unitVector j) * inner ℝ (G y (unitVector i)) (unitVector i)) :=
    fun i => DriftPowerSolenoidalInternal.integrable_pair (DriftPowerSolenoidalInternal.locInt_col h i)
        hdc.continuous hds (unitVector i)
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hI i), Finset.sum_congr rfl (fun i _ => hpair i),
    Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hJ i)]
  have e2 : (fun y => ∑ i : Fin 3, fderiv ℝ ψ y (unitVector j) * inner ℝ (G y (unitVector i)) (unitVector i))
      =ᵐ[volume] fun _ => (0 : ℝ) := by
    filter_upwards [h.divergence] with y hy
    rw [← Finset.mul_sum, hy, mul_zero]
  rw [integral_congr_ae e2]
  simp

theorem circ_int {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : CellBox) (hK : IsCellBox K)
    {X : Space → E} (hX : LocallyIntegrable X volume) :
    ∀ᵐ p ∂(volume.restrict K.rect), 0 < p.1 ∧
      Integrable (fun θ => X (cylPoint p.1 θ p.2)) (volume.restrict (Ioo (-π) π)) := by
  set R : ℝ := 2 * K.r₂ + K.z₂ with hR
  set g : Space → E := (Metric.closedBall (0 : Space) R).indicator X with hg
  have hgi : Integrable g :=
    (hX.integrableOn_isCompact (isCompact_closedBall 0 R)).integrable_indicator measurableSet_closedBall
  have hgm : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => g (LowEntry.Internal.cylArg q))
      LowEntry.Internal.muU :=
    hgi.aestronglyMeasurable.comp_quasiMeasurePreserving LowEntry.Internal.qmp
  have hfm : AEMeasurable (fun q : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal q.1.1 * ‖g (LowEntry.Internal.cylArg q)‖ₑ) LowEntry.Internal.muU :=
    (ENNReal.measurable_ofReal.comp measurable_fst.fst).aemeasurable.mul hgm.enorm
  have hlin : ∫⁻ q, ENNReal.ofReal q.1.1 * ‖g (LowEntry.Internal.cylArg q)‖ₑ ∂LowEntry.Internal.muU ≠ ⊤ := by
    rw [LowEntry.Internal.key (fun y => ‖g y‖ₑ)]
    exact hgi.2.ne
  rw [LowEntry.Internal.muU_def] at hgm hfm hlin
  rw [lintegral_prod _ hfm] at hlin
  have h1 := ae_lt_top' hfm.lintegral_prod_right' hlin
  have h2 := hgm.prodMk_left
  have hle : volume.restrict K.rect ≤ volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    refine Measure.restrict_mono_ae ?_
    have hsub : K.rect ⊆ Ici (0 : ℝ) ×ˢ (univ : Set ℝ) := fun p hp => ⟨le_trans hK.r_order.1 hp.1.1, trivial⟩
    refine hsub.eventuallyLE.trans ?_
    have : (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)) =ᵐ[volume] Ici (0 : ℝ) ×ˢ (univ : Set ℝ) :=
      Measure.set_prod_ae_eq Ioi_ae_eq_Ici (ae_eq_refl _)
    exact this.symm.le
  have h0 : ∀ᵐ p ∂(volume.restrict K.rect), p.1 ≠ 0 := ae_restrict_of_ae PlaneDeleted.ae_fst_ne
  filter_upwards [ae_mono hle h1, ae_mono hle h2, h0, ae_restrict_mem (LowEntry.Internal.rect_meas K)]
    with p hp1 hp2 hp0 hpr
  have hpos : 0 < p.1 := lt_of_le_of_ne (le_trans hK.r_order.1 hpr.1.1) (Ne.symm hp0)
  refine ⟨hpos, ?_⟩
  have hball : ∀ θ, cylPoint p.1 θ p.2 ∈ Metric.closedBall (0 : Space) R := by
    intro θ
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (LowEntry.Internal.cylPoint_norm _ _ _).trans ?_
    have h2' : 0 ≤ p.2 := le_trans hK.z_order.1 hpr.2.1
    rw [abs_of_nonneg hpos.le, abs_of_nonneg h2', hR]
    linarith [hpr.1.2, hpr.2.2]
  have heq : (fun θ => g (LowEntry.Internal.cylArg (p, θ))) = fun θ => X (cylPoint p.1 θ p.2) := by
    funext θ
    show g (cylPoint p.1 θ p.2) = X (cylPoint p.1 θ p.2)
    rw [hg, Set.indicator_of_mem (hball θ)]
  rw [← heq]
  refine ⟨hp2, ?_⟩
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hp1
  exact ENNReal.lt_top_of_mul_ne_top_right hp1.ne (by simpa using hpos)

def thirdKernel (m : ℕ) (n : ℤ) (a b c : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space →L[ℝ] Space) : ℂ :=
  Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * (frameThird θ M a b c : ℂ)

theorem thirdKernel_cont (m : ℕ) (n : ℤ) (a b c : Fin 3) :
    Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) => thirdKernel m n a b c q.1 q.2) := by
  have hu : ∀ d : Fin 3, Continuous fun θ : ℝ => frameUnit θ d := fun d => LowEntry.Internal.unit_cont d
  have hf : Continuous fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) => frameThird q.1 q.2 a b c := by
    unfold frameThird
    exact ((continuous_snd.clm_apply ((hu c).comp continuous_fst)).clm_apply
      ((hu b).comp continuous_fst)).inner ((hu a).comp continuous_fst)
  unfold thirdKernel
  fun_prop

theorem thirdKernel_bound (m : ℕ) (n : ℤ) (a b c : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖thirdKernel m n a b c θ M‖ ≤ ‖M‖ := by
  unfold thirdKernel
  rw [norm_mul, LowEntry.Internal.phase_norm, one_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold frameThird
  refine (abs_real_inner_le_norm _ _).trans ?_
  have ha := LowEntry.Internal.unit_norm θ a
  have hb := LowEntry.Internal.unit_norm θ b
  have hc := LowEntry.Internal.unit_norm θ c
  have h1 := M.le_opNorm₂ (frameUnit θ c) (frameUnit θ b)
  have e : ∀ d, frameUnit θ d = ![radialUnit θ, angularUnit θ, axialUnit] d := fun d => rfl
  simp only [e] at h1 ⊢
  calc ‖M (![radialUnit θ, angularUnit θ, axialUnit] c) (![radialUnit θ, angularUnit θ, axialUnit] b)‖ *
        ‖![radialUnit θ, angularUnit θ, axialUnit] a‖
      ≤ (‖M‖ * 1 * 1) * 1 := by
        gcongr
        refine h1.trans ?_
        gcongr
    _ = ‖M‖ := by ring

theorem third_eq (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b c : Fin 3) (p : ℝ × ℝ) :
    modeThird m n H a b c p =
      (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, thirdKernel m n a b c θ (H (cylPoint p.1 θ p.2)) := by
  unfold modeThird
  rw [LowEntry.Internal.per_interval]
  · rfl
  · intro θ
    simp only [PlaneDeleted.exp_per', PlaneDeleted.cyl_per, frameThird, frameUnit, PlaneDeleted.radial_per,
      PlaneDeleted.angular_per]

theorem grad_sum (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsSecondOrderField m v G H) (n : ℤ) :
    ∀ᵐ p ∂(volume.restrict K.rect), ∑ a : Fin 3, gradMode m n G a a p = 0 := by
  have hd := PlaneDeleted.cyl_ae h.divergence
  filter_upwards [circ_int K hK (grad_loc h), ae_restrict_of_ae hd] with p hp hdp
  obtain ⟨hpos, hint⟩ := hp
  have hI : ∀ a : Fin 3, Integrable (fun θ => LowEntry.Internal.gradKernel m n a a θ (G (cylPoint p.1 θ p.2)))
      (volume.restrict (Ioo (-π) π)) := fun a => by
    refine Integrable.mono' hint.norm ?_ (ae_of_all _ fun θ => LowEntry.Internal.gradKernel_bound m n a a θ _)
    exact (LowEntry.Internal.gradKernel_cont m n a a).comp_aestronglyMeasurable
      (f := fun θ => (θ, G (cylPoint p.1 θ p.2)))
      (measurable_id.aestronglyMeasurable.prodMk hint.aestronglyMeasurable)
  have e : ∑ a : Fin 3, gradMode m n G a a p = (1 / (2 * π) : ℂ) *
      ∫ θ in Ioo (-π) π, ∑ a : Fin 3, LowEntry.Internal.gradKernel m n a a θ (G (cylPoint p.1 θ p.2)) := by
    rw [integral_finsetSum _ (fun a _ => hI a), Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => LowEntry.Internal.gradMode_eq m n G a a p
  rw [e, integral_eq_zero_of_ae, mul_zero]
  filter_upwards [hdp hpos] with θ hθ
  have e2 : ∑ a : Fin 3, LowEntry.Internal.gradKernel m n a a θ (G (cylPoint p.1 θ p.2)) =
      Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) *
        ((∑ a : Fin 3, frameMat θ (G (cylPoint p.1 θ p.2)) a a : ℝ) : ℂ) := by
    simp only [LowEntry.Internal.gradKernel, Complex.ofReal_sum, Finset.mul_sum]
  rw [e2, mat_trace, hθ]
  simp

theorem third_sum (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsSecondOrderField m v G H) (n : ℤ) (c : Fin 3) :
    ∀ᵐ p ∂(volume.restrict K.rect), ∑ a : Fin 3, modeThird m n H a a c p = 0 := by
  have hd := PlaneDeleted.cyl_ae (ae_all_iff.2 (second_trace h))
  filter_upwards [circ_int K hK (second_loc h), ae_restrict_of_ae hd] with p hp hdp
  obtain ⟨hpos, hint⟩ := hp
  have hI : ∀ a : Fin 3, Integrable (fun θ => thirdKernel m n a a c θ (H (cylPoint p.1 θ p.2)))
      (volume.restrict (Ioo (-π) π)) := fun a => by
    refine Integrable.mono' hint.norm ?_ (ae_of_all _ fun θ => thirdKernel_bound m n a a c θ _)
    exact (thirdKernel_cont m n a a c).comp_aestronglyMeasurable
      (f := fun θ => (θ, H (cylPoint p.1 θ p.2)))
      (measurable_id.aestronglyMeasurable.prodMk hint.aestronglyMeasurable)
  have e : ∑ a : Fin 3, modeThird m n H a a c p = (1 / (2 * π) : ℂ) *
      ∫ θ in Ioo (-π) π, ∑ a : Fin 3, thirdKernel m n a a c θ (H (cylPoint p.1 θ p.2)) := by
    rw [integral_finsetSum _ (fun a _ => hI a), Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => third_eq m n H a a c p
  rw [e, integral_eq_zero_of_ae, mul_zero]
  filter_upwards [hdp hpos] with θ hθ
  have e2 : ∑ a : Fin 3, thirdKernel m n a a c θ (H (cylPoint p.1 θ p.2)) =
      Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) *
        ((∑ a : Fin 3, frameThird θ (H (cylPoint p.1 θ p.2)) a a c : ℝ) : ℂ) := by
    simp only [thirdKernel, Complex.ofReal_sum, Finset.mul_sum]
  rw [e2, third_trace]
  simp [hθ]

theorem third_int (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsSecondOrderField m v G H) (n : ℤ) (a b c : Fin 3) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * modeThird m n H a b c p) K.rect := by
  have hm := LowEntry.Internal.mode_int K hK (second_loc h) (thirdKernel m n a b c) (thirdKernel_cont m n a b c)
    (thirdKernel_bound m n a b c)
  have e : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * modeThird m n H a b c p) = fun p => (1 / (2 * π) : ℂ) *
      ((K.lineWeight p.1 : ℂ) * ∫ θ in Ioo (-π) π, thirdKernel m n a b c θ (H (cylPoint p.1 θ p.2))) := by
    funext p; rw [third_eq]; ring
  rw [e]
  exact hm.const_mul _

theorem weighted (K : CellBox) {X : ℝ × ℝ → ℂ}
    (hX : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * X p) K.rect) {o : ℝ} (ho : K.r₁ = 0 → o = 0)
    {w : ℝ × ℝ → ℂ} (hw : Continuous w) :
    IntegrableOn (fun p => ((p.1 - o : ℝ) : ℂ) * w p * X p) K.rect := by
  by_cases h0 : K.r₁ = 0
  · have e : (fun p : ℝ × ℝ => ((p.1 - o : ℝ) : ℂ) * w p * X p) =
        fun p => w p * ((K.lineWeight p.1 : ℂ) * X p) := by
      funext p
      simp only [CellBox.lineWeight, h0, if_true, ho h0, sub_zero]
      ring
    rw [e]
    exact IntegrableOn.continuousOn_mul hw.continuousOn hX (LowEntry.Internal.rect_compact K)
  · have e : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * X p) = X := by
      funext p
      simp [CellBox.lineWeight, h0]
    rw [e] at hX
    have hc : Continuous fun p : ℝ × ℝ => ((p.1 - o : ℝ) : ℂ) * w p := by fun_prop
    exact IntegrableOn.continuousOn_mul hc.continuousOn hX (LowEntry.Internal.rect_compact K)

theorem radial_int (K : CellBox) {F dF : ℝ × ℝ → ℂ} (hF : IntegrableOn F K.rect)
    (hdF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * dF p) K.rect) {c o : ℝ} (ho : K.r₁ = 0 → o = 0)
    {t : ℝ → ℝ} (ht : Continuous t) :
    IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p) *
      ((t p.2 : ℝ) : ℂ)) K.rect := by
  have h1 : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * ((t p.2 : ℝ) : ℂ)) * F p) K.rect := by
    have hc : Continuous fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * ((t p.2 : ℝ) : ℂ)) := by fun_prop
    exact IntegrableOn.continuousOn_mul hc.continuousOn hF (LowEntry.Internal.rect_compact K)
  have h2 := weighted K hdF ho (w := fun p : ℝ × ℝ => (((1 / (c - o) : ℝ)) : ℂ) * ((t p.2 : ℝ) : ℂ))
    (by fun_prop)
  refine (h1.add h2).congr_fun (fun p _ => ?_) (LowEntry.Internal.rect_meas K)
  simp only [Pi.add_apply]
  push_cast
  ring

theorem height_int (K : CellBox) {F dF : ℝ × ℝ → ℂ} (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect)
    (hdF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * dF p) K.rect) (c o : ℝ)
    {t : ℝ → ℝ} (ht : Continuous t) :
    IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p) *
      ((p.1 * t p.1 : ℝ) : ℂ)) K.rect := by
  have h1 := weighted K hF (o := 0) (fun _ => rfl)
    (w := fun p : ℝ × ℝ => (((1 / (c - o) : ℝ)) : ℂ) * ((t p.1 : ℝ) : ℂ)) (by fun_prop)
  have h2 := weighted K hdF (o := 0) (fun _ => rfl)
    (w := fun p : ℝ × ℝ => ((((p.2 - o) / (c - o) : ℝ)) : ℂ) * ((t p.1 : ℝ) : ℂ)) (by fun_prop)
  refine (h1.add h2).congr_fun (fun p _ => ?_) (LowEntry.Internal.rect_meas K)
  simp only [Pi.add_apply]
  push_cast
  ring

theorem sum3 {s : Set (ℝ × ℝ)} {g : Fin 3 → ℝ × ℝ → ℂ} (hg : ∀ a, IntegrableOn (g a) s)
    (h0 : ∀ᵐ p ∂(volume.restrict s), g 0 p + g 1 p + g 2 p = 0) :
    (∫ p in s, g 0 p) + (∫ p in s, g 1 p) + ∫ p in s, g 2 p = 0 := by
  rw [← integral_add (hg 0) (hg 1), ← integral_add (f := fun p => g 0 p + g 1 p) ((hg 0).add (hg 1)) (hg 2)]
  exact integral_eq_zero_of_ae h0

theorem radial_zero (K : CellBox) (c o : ℝ) (hs : Icc (min c o) (max c o) ×ˢ Icc K.z₁ K.z₂ = K.rect)
    (F dF : Fin 3 → ℝ × ℝ → ℂ) (t : ℝ → ℝ)
    (hI : ∀ a, IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F a p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF a p) * ((t p.2 : ℝ) : ℂ)) K.rect)
    (hF : ∀ᵐ p ∂(volume.restrict K.rect), ∑ a : Fin 3, F a p = 0)
    (hdF : ∀ᵐ p ∂(volume.restrict K.rect), ∑ a : Fin 3, dF a p = 0) :
    radialStripMoment c o K.z₁ K.z₂ (F 0) (dF 0) t + radialStripMoment c o K.z₁ K.z₂ (F 1) (dF 1) t
      + radialStripMoment c o K.z₁ K.z₂ (F 2) (dF 2) t = 0 := by
  unfold radialStripMoment
  rw [hs, ← mul_add, ← mul_add, sum3 hI, mul_zero]
  filter_upwards [hF, hdF] with p h1 h2
  simp only [Fin.sum_univ_three] at h1 h2
  linear_combination ((((1 / (c - o) : ℝ)) : ℂ) * ((t p.2 : ℝ) : ℂ)) * h1
    + ((((p.1 - o) / (c - o) : ℝ) : ℂ) * ((t p.2 : ℝ) : ℂ)) * h2

theorem height_zero (K : CellBox) (c o : ℝ) (hs : Icc K.r₁ K.r₂ ×ˢ Icc (min c o) (max c o) = K.rect)
    (F dF : Fin 3 → ℝ × ℝ → ℂ) (t : ℝ → ℝ)
    (hI : ∀ a, IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F a p
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF a p) * ((p.1 * t p.1 : ℝ) : ℂ)) K.rect)
    (hF : ∀ᵐ p ∂(volume.restrict K.rect), ∑ a : Fin 3, F a p = 0)
    (hdF : ∀ᵐ p ∂(volume.restrict K.rect), ∑ a : Fin 3, dF a p = 0) :
    heightStripMoment c o K.r₁ K.r₂ (fun r => r) (F 0) (dF 0) t
      + heightStripMoment c o K.r₁ K.r₂ (fun r => r) (F 1) (dF 1) t
      + heightStripMoment c o K.r₁ K.r₂ (fun r => r) (F 2) (dF 2) t = 0 := by
  unfold heightStripMoment
  rw [hs, ← mul_add, ← mul_add, sum3 hI, mul_zero]
  filter_upwards [hF, hdF] with p h1 h2
  simp only [Fin.sum_univ_three] at h1 h2
  linear_combination ((((1 / (c - o) : ℝ)) : ℂ) * ((p.1 * t p.1 : ℝ) : ℂ)) * h1
    + ((((p.2 - o) / (c - o) : ℝ) : ℂ) * ((p.1 * t p.1 : ℝ) : ℂ)) * h2

end Breakdown.CellCert.CellFormula.Internal.StrainFaceFaceTraceFree

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis Internal.StrainFaceFaceTraceFree

def AxisGradModeIntegrableStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
      ∀ K : CellBox, IsCellBox K → K.r₁ = 0 → ∀ (n : ℤ) (a b : Fin 3), IntegrableOn (gradMode m n G a b) K.rect

theorem faceTraceFree_of (hA : AxisGradModeIntegrableStatement) {k N : ℕ} (c : FracCellData k N) (K : CellBox)
    (S : CellScalars) (B : CellBases) (L : CellLayout) (hL : IsCellLayout c K S B L) (x : FieldTuple k)
    (hx : IsAdmissible c x) (n : ℤ) (i : Fin 2) (t : ℝ → ℝ) (htp : IsAnyPolyFn t) (hi : i = 0 → K.r₁ ≠ 0) :
    radialFaceMoment L.box (L.gradModeOf n x 0 0) (L.secondModeOf n x 0 0 0) i t
        + radialFaceMoment L.box (L.gradModeOf n x 1 1) (L.secondModeOf n x 1 1 0) i t
        + radialFaceMoment L.box (L.gradModeOf n x 2 2) (L.secondModeOf n x 2 2 0) i t = 0 ∧
      heightFaceMoment L.box (L.gradModeOf n x 0 0) (L.secondModeOf n x 0 0 2) i t
        + heightFaceMoment L.box (L.gradModeOf n x 1 1) (L.secondModeOf n x 1 1 2) i t
        + heightFaceMoment L.box (L.gradModeOf n x 2 2) (L.secondModeOf n x 2 2 2) i t = 0 := by
  have hK : IsCellBox K := hL.box_valid
  have hf : IsSecondOrderField L.order x.1 x.2.1 x.2.2.1 := by rw [hL.order_eq]; exact hx.1
  have ht : Continuous t := by
    obtain ⟨q, hq⟩ := htp
    rw [show t = fun u => q.eval u from funext hq]
    exact q.continuous
  have hr : K.r₁ ≤ K.r₂ := hK.r_order.2.le
  have hz : K.z₁ ≤ K.z₂ := hK.z_order.2.le
  have hG : ∀ a b : Fin 3, IntegrableOn (gradMode L.order n x.2.1 a b) K.rect := by
    intro a b
    by_cases h0 : K.r₁ = 0
    · exact hA _ _ _ _ hf K hK h0 n a b
    · have := LowEntry.Internal.gradMode_int K hK L.order n hf.measurable_gradient hf.gradient_two a b
      have e : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * gradMode L.order n x.2.1 a b p) =
          gradMode L.order n x.2.1 a b := by
        funext p
        simp [CellBox.lineWeight, h0]
      rwa [e] at this
  have hGw : ∀ a b : Fin 3, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * gradMode L.order n x.2.1 a b p) K.rect :=
    fun a b => LowEntry.Internal.gradMode_int K hK L.order n hf.measurable_gradient hf.gradient_two a b
  have hH : ∀ a b e : Fin 3, IntegrableOn
      (fun p => (K.lineWeight p.1 : ℂ) * modeThird L.order n x.2.2.1 a b e p) K.rect :=
    fun a b e => third_int K hK hf n a b e
  rw [hL.box_eq]
  simp only [CellLayout.gradModeOf, CellLayout.secondModeOf]
  constructor
  · unfold radialFaceMoment
    split_ifs with h1
    · exact radial_zero K K.r₂ K.r₁ (by rw [min_eq_right hr, max_eq_left hr]; rfl)
        (fun a => gradMode L.order n x.2.1 a a) (fun a => modeThird L.order n x.2.2.1 a a 0) t
        (fun a => radial_int K (hG a a) (hH a a 0) (fun h => h) ht)
        (grad_sum K hK hf n) (third_sum K hK hf n 0)
    · have h0 : i = 0 := by omega
      have hr0 : K.r₁ ≠ 0 := hi h0
      exact radial_zero K K.r₁ K.r₂ (by rw [min_eq_left hr, max_eq_right hr]; rfl)
        (fun a => gradMode L.order n x.2.1 a a) (fun a => modeThird L.order n x.2.2.1 a a 0) t
        (fun a => radial_int K (hG a a) (hH a a 0) (fun h => absurd h hr0) ht)
        (grad_sum K hK hf n) (third_sum K hK hf n 0)
  · unfold heightFaceMoment
    split_ifs with h1
    · exact height_zero K K.z₂ K.z₁ (by rw [min_eq_right hz, max_eq_left hz]; rfl)
        (fun a => gradMode L.order n x.2.1 a a) (fun a => modeThird L.order n x.2.2.1 a a 2) t
        (fun a => height_int K (hGw a a) (hH a a 2) _ _ ht)
        (grad_sum K hK hf n) (third_sum K hK hf n 2)
    · exact height_zero K K.z₁ K.z₂ (by rw [min_eq_left hz, max_eq_right hz]; rfl)
        (fun a => gradMode L.order n x.2.1 a a) (fun a => modeThird L.order n x.2.2.1 a a 2) t
        (fun a => height_int K (hGw a a) (hH a a 2) _ _ ht)
        (grad_sum K hK hf n) (third_sum K hK hf n 2)

end Breakdown.CellCert.CellFormula
