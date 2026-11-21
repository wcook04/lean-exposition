import Breakdown.CertCell.LocalFieldDefs2
import Breakdown.CertCell.LocalModeIntegrable
import Breakdown.CertCell.LocalRelationsB

open MeasureTheory Set
open scoped ContDiff

noncomputable section

namespace Breakdown.CertCell.LocalField.Internal.FaceTraceFree

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula Real
open CellCert.CellFormula.Internal.StrainFaceFaceTraceFree

theorem gradient_column_locInt {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsLocalSecondOrderField v G H) (j : Fin 3) :
    LocallyIntegrable (fun y => G y (unitVector j)) volume := by
  have hm : AEStronglyMeasurable (fun y => G y (unitVector j)) volume :=
    h.measurable_gradient.apply_continuousLinearMap _
  have h2 : MemLp (fun y => G y (unitVector j)) 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    refine h.gradient_two.mono' (hm.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact Finset.single_le_sum (f := fun i : Fin 3 => ‖G y (unitVector i)‖ ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
  exact h2.locallyIntegrable (by norm_num)

theorem second_locInt {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsLocalSecondOrderField v G H) :
    LocallyIntegrable H volume := by
  have hl : ∀ j i : Fin 3, LocallyIntegrable (fun y => ‖H y (unitVector j) (unitVector i)‖) volume :=
    fun j i => ((CellCert.CellFormula.Internal.PlaneDeleted.memLp_second h.measurable_second h.second_two j i).norm).locallyIntegrable
      (by norm_num)
  have hs : LocallyIntegrable
      (fun y => ∑ j : Fin 3, ∑ i : Fin 3, ‖H y (unitVector j) (unitVector i)‖) volume := by
    simp only [Fin.sum_univ_three]
    exact ((((hl 0 0).add (hl 0 1)).add (hl 0 2)).add (((hl 1 0).add (hl 1 1)).add (hl 1 2))).add
      (((hl 2 0).add (hl 2 1)).add (hl 2 2))
  refine hs.mono h.measurable_second (ae_of_all _ fun y => ?_)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  refine (opnorm_le (H y)).trans (Finset.sum_le_sum fun j _ => ?_)
  exact opnorm_le (H y (unitVector j))

theorem second_trace_zero {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsLocalSecondOrderField v G H) (j : Fin 3) :
    ∀ᵐ y ∂volume, ∑ i : Fin 3, inner ℝ (H y (unitVector j) (unitVector i)) (unitVector i) = 0 := by
  have hl : ∀ i : Fin 3, LocallyIntegrable (fun y => H y (unitVector j) (unitVector i)) volume :=
    fun i => (CellCert.CellFormula.Internal.PlaneDeleted.memLp_second h.measurable_second h.second_two j i).locallyIntegrable (by norm_num)
  have hli : ∀ i : Fin 3, LocallyIntegrable
      (fun y => inner ℝ (H y (unitVector j) (unitVector i)) (unitVector i)) volume := fun i => by
    refine (hl i).mono (((hl i).aestronglyMeasurable).inner aestronglyMeasurable_const)
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    simp [unitVector]
  have hT : LocallyIntegrable
      (fun y => ∑ i : Fin 3, inner ℝ (H y (unitVector j) (unitVector i)) (unitVector i)) volume := by
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
    have hg := (gradient_column_locInt h i).integrable_smul_left_of_hasCompactSupport hdc.continuous hds
    have hh := (hl i).integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
    simp only [inner_neg_left] at e
    rw [real_inner_comm (unitVector i), real_inner_comm (unitVector i), ← integral_inner hg,
      ← integral_inner hh] at e
    simp only [real_inner_smul_right, DriftPowerSolenoidalInternal.unit_inner,
      DriftPowerSolenoidalInternal.unit_inner'] at e ⊢
    linarith
  have hI : ∀ i : Fin 3,
      Integrable (fun y => ψ y * inner ℝ (H y (unitVector j) (unitVector i)) (unitVector i)) := fun i => by
    have := (hli i).integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
    simpa [smul_eq_mul] using this
  have hJ : ∀ i : Fin 3,
      Integrable (fun y => fderiv ℝ ψ y (unitVector j) * inner ℝ (G y (unitVector i)) (unitVector i)) :=
    fun i => DriftPowerSolenoidalInternal.integrable_pair (gradient_column_locInt h i)
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

theorem grad_trace_zero (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (h : IsLocalSecondOrderField v G H) (n : ℤ) :
    ∀ᵐ p ∂(volume.restrict K.rect), ∑ a : Fin 3, gradMode m n G a a p = 0 := by
  filter_upwards [ae_restrict_of_ae (localModeTrace m v G H h n), ae_restrict_of_ae CellCert.CellFormula.Internal.PlaneDeleted.ae_fst_ne,
    ae_restrict_mem (LowEntry.Internal.rect_meas K)] with p h1 h2 h3
  exact h1 (lt_of_le_of_ne (le_trans hK.r_order.1 h3.1.1) (Ne.symm h2))

theorem third_trace_zero (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (h : IsLocalSecondOrderField v G H) (n : ℤ) (c : Fin 3) :
    ∀ᵐ p ∂(volume.restrict K.rect), ∑ a : Fin 3, modeThird m n H a a c p = 0 := by
  have hd := CellCert.CellFormula.Internal.PlaneDeleted.cyl_ae (ae_all_iff.2 (second_trace_zero h))
  filter_upwards [circ_int K hK (second_locInt h), ae_restrict_of_ae hd] with p hp hdp
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

theorem third_weighted_int (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (h : IsLocalSecondOrderField v G H) (n : ℤ) (a b c : Fin 3) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * modeThird m n H a b c p) K.rect := by
  have hm := LowEntry.Internal.mode_int K hK (second_locInt h) (thirdKernel m n a b c)
    (thirdKernel_cont m n a b c) (thirdKernel_bound m n a b c)
  have e : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * modeThird m n H a b c p) = fun p =>
      (1 / (2 * π) : ℂ) * ((K.lineWeight p.1 : ℂ) *
        ∫ θ in Ioo (-π) π, thirdKernel m n a b c θ (H (cylPoint p.1 θ p.2))) := by
    funext p
    rw [third_eq]
    ring
  rw [e]
  exact hm.const_mul _

theorem grad_rect_int (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (h : IsLocalSecondOrderField v G H) (n : ℤ) (a b : Fin 3) :
    IntegrableOn (gradMode m n G a b) K.rect :=
  ((localModeStripIntegrable m v G H h n K.r₂ K.z₁ K.z₂).2 a b).mono_set
    (prod_mono (Icc_subset_Icc_left hK.r_order.1) subset_rfl)

end Breakdown.CertCell.LocalField.Internal.FaceTraceFree

namespace Breakdown.CertCell.LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula
open CellCert.CellFormula.Internal.StrainFaceFaceTraceFree Internal.FaceTraceFree

theorem localAxisGradModeIntegrable : LocalAxisGradModeIntegrableStatement := by
  intro m v G H hs K hK _ n a b
  exact grad_rect_int K hK hs n a b

theorem localFaceHeightTraceFree {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)
    (B : CellBases) (L : CellLayout) (hL : IsCellLayout c K S B L) (x : FieldTuple k) (hx : IsLocalAdmissible x)
    (n : ℤ) (i : Fin 2) (t : ℝ → ℝ) (htp : IsAnyPolyFn t) :
    heightFaceMoment L.box (L.gradModeOf n x 0 0) (L.secondModeOf n x 0 0 2) i t
        + heightFaceMoment L.box (L.gradModeOf n x 1 1) (L.secondModeOf n x 1 1 2) i t
        + heightFaceMoment L.box (L.gradModeOf n x 2 2) (L.secondModeOf n x 2 2 2) i t = 0 := by
  have hK : IsCellBox K := hL.box_valid
  have hf : IsLocalSecondOrderField x.1 x.2.1 x.2.2.1 := hx.1
  have ht : Continuous t := by
    obtain ⟨q, hq⟩ := htp
    rw [show t = fun u => q.eval u from funext hq]
    exact q.continuous
  have hz : K.z₁ ≤ K.z₂ := hK.z_order.2.le
  have hGw : ∀ a b : Fin 3,
      IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * gradMode L.order n x.2.1 a b p) K.rect :=
    fun a b => ((localModeIntegrable L.order x.1 x.2.1 x.2.2.1 hf K hK n a).2 b)
  have hH : ∀ a b e : Fin 3, IntegrableOn
      (fun p => (K.lineWeight p.1 : ℂ) * modeThird L.order n x.2.2.1 a b e p) K.rect :=
    fun a b e => third_weighted_int K hK hf n a b e
  rw [hL.box_eq]
  simp only [CellLayout.gradModeOf, CellLayout.secondModeOf]
  unfold heightFaceMoment
  split_ifs with h1
  · exact height_zero K K.z₂ K.z₁ (by rw [min_eq_right hz, max_eq_left hz]; rfl)
      (fun a => gradMode L.order n x.2.1 a a) (fun a => modeThird L.order n x.2.2.1 a a 2) t
      (fun a => height_int K (hGw a a) (hH a a 2) _ _ ht)
      (grad_trace_zero K hK hf n) (third_trace_zero K hK hf n 2)
  · exact height_zero K K.z₁ K.z₂ (by rw [min_eq_left hz, max_eq_right hz]; rfl)
      (fun a => gradMode L.order n x.2.1 a a) (fun a => modeThird L.order n x.2.2.1 a a 2) t
      (fun a => height_int K (hGw a a) (hH a a 2) _ _ ht)
      (grad_trace_zero K hK hf n) (third_trace_zero K hK hf n 2)

theorem localFaceTraceFree : LocalFaceTraceFreeStatement := by
  intro k N c K S B L hL x hx n i t htp hi
  refine ⟨?_, localFaceHeightTraceFree c K S B L hL x hx n i t htp⟩
  have hK : IsCellBox K := hL.box_valid
  have hf : IsLocalSecondOrderField x.1 x.2.1 x.2.2.1 := hx.1
  have ht : Continuous t := by
    obtain ⟨q, hq⟩ := htp
    rw [show t = fun u => q.eval u from funext hq]
    exact q.continuous
  have hr : K.r₁ ≤ K.r₂ := hK.r_order.2.le
  have hG : ∀ a b : Fin 3, IntegrableOn (gradMode L.order n x.2.1 a b) K.rect :=
    fun a b => grad_rect_int K hK hf n a b
  have hH : ∀ a b e : Fin 3, IntegrableOn
      (fun p => (K.lineWeight p.1 : ℂ) * modeThird L.order n x.2.2.1 a b e p) K.rect :=
    fun a b e => third_weighted_int K hK hf n a b e
  rw [hL.box_eq]
  simp only [CellLayout.gradModeOf, CellLayout.secondModeOf]
  unfold radialFaceMoment
  split_ifs with h1
  · exact radial_zero K K.r₂ K.r₁ (by rw [min_eq_right hr, max_eq_left hr]; rfl)
      (fun a => gradMode L.order n x.2.1 a a) (fun a => modeThird L.order n x.2.2.1 a a 0) t
      (fun a => radial_int K (hG a a) (hH a a 0) (fun h => h) ht)
      (grad_trace_zero K hK hf n) (third_trace_zero K hK hf n 0)
  · have h0 : i = 0 := by omega
    have hr0 : K.r₁ ≠ 0 := hi h0
    exact radial_zero K K.r₁ K.r₂ (by rw [min_eq_left hr, max_eq_right hr]; rfl)
      (fun a => gradMode L.order n x.2.1 a a) (fun a => modeThird L.order n x.2.2.1 a a 0) t
      (fun a => radial_int K (hG a a) (hH a a 0) (fun h => absurd h hr0) ht)
      (grad_trace_zero K hK hf n) (third_trace_zero K hK hf n 0)

end Breakdown.CertCell.LocalField
