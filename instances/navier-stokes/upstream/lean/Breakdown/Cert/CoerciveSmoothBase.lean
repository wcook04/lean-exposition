import Breakdown.Cert.CoerciveBase

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothBaseInternal

open BaseDensityInternal

theorem smooth_fields_continuous {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    Continuous (fun z : ℝ × Space => v z.1 z.2) ∧
      Continuous (fun z : ℝ × Space => gradField v z.1 z.2) ∧
      Continuous (fun z : ℝ × Space => secondDerivField v z.1 z.2) := by
  have h0 := hv.smooth
  have h1 : ContDiff ℝ 2 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => v z.1 y) (g := fun z => z.2)
      (h0.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (top_add_le 2)
  have h2 : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (v z.1) x) z.2) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => fderiv ℝ (v z.1) y) (g := fun z => z.2)
      (h1.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)
  exact ⟨h0.continuous, h1.continuous, h2.continuous⟩

theorem smooth_modes_continuous {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    (ι : ℤ × ℤ) :
    Continuous (fun z : ℝ × Space => modeVel ι v z.1 z.2) ∧
      Continuous (fun z : ℝ × Space => modeGrad ι (gradField v) z.1 z.2) ∧
      Continuous (fun z : ℝ × Space => modeSecondDeriv ι (secondDerivField v) z.1 z.2) := by
  obtain ⟨c0, c1, c2⟩ := smooth_fields_continuous hv
  have hrot : ∀ {a : (ℝ × Space) × ℝ × ℝ → ℝ} {u : (ℝ × Space) × ℝ × ℝ → Space}, Continuous a →
      Continuous u → Continuous fun q => axialRot (a q) (u q) := fun ha hu => continuous_axialRot_of ha hu
  have hcoord : ∀ {u : (ℝ × Space) × ℝ × ℝ → Space} (i : Fin 3), Continuous u →
      Continuous fun q => u q i := fun i hu => (PiLp.continuous_apply 2 _ i).comp hu
  have hs : Continuous fun q : (ℝ × Space) × ℝ × ℝ => q.1.1 + q.2.1 := by fun_prop
  have hy : Continuous fun q : (ℝ × Space) × ℝ × ℝ => axialRot q.2.2 q.1.2 :=
    continuous_axialRot_of (by fun_prop : Continuous fun q : (ℝ × Space) × ℝ × ℝ => q.2.2)
      (by fun_prop : Continuous fun q : (ℝ × Space) × ℝ × ℝ => q.1.2)
  have he : ∀ j : Fin 3, Continuous fun q : (ℝ × Space) × ℝ × ℝ => axialRot q.2.2 (unitVector j) := fun j =>
    continuous_axialRot_of (by fun_prop : Continuous fun q : (ℝ × Space) × ℝ × ℝ => q.2.2) continuous_const
  have hneg : Continuous fun q : (ℝ × Space) × ℝ × ℝ => -q.2.2 := by fun_prop
  have f0 : ∀ i : Fin 3, Continuous fun q : (ℝ × Space) × ℝ × ℝ =>
      axialRot (-q.2.2) (v (q.1.1 + q.2.1) (axialRot q.2.2 q.1.2)) i := fun i =>
    hcoord i (hrot hneg (c0.comp (hs.prodMk hy)))
  have f1 : ∀ ij : Fin 3 × Fin 3, Continuous fun q : (ℝ × Space) × ℝ × ℝ =>
      axialRot (-q.2.2) (gradField v (q.1.1 + q.2.1) (axialRot q.2.2 q.1.2)
        (axialRot q.2.2 (unitVector ij.2))) ij.1 := fun ij =>
    hcoord ij.1 (hrot hneg ((c1.comp (hs.prodMk hy)).clm_apply (he ij.2)))
  have f2 : ∀ ijl : Fin 3 × Fin 3 × Fin 3, Continuous fun q : (ℝ × Space) × ℝ × ℝ =>
      axialRot (-q.2.2) (secondDerivField v (q.1.1 + q.2.1) (axialRot q.2.2 q.1.2)
        (axialRot q.2.2 (unitVector ijl.2.1)) (axialRot q.2.2 (unitVector ijl.2.2))) ijl.1 := fun ijl =>
    hcoord ijl.1 (hrot hneg (((c2.comp (hs.prodMk hy)).clm_apply (he ijl.2.1)).clm_apply (he ijl.2.2)))
  refine ⟨continuous_pi fun i => ?_, continuous_pi fun ij => ?_, continuous_pi fun ijl => ?_⟩
  · exact continuous_modeAverage ι (fun (z : ℝ × Space) τ φ (i : Fin 3) =>
      axialRot (-φ) (v (z.1 + τ) (axialRot φ z.2)) i) i (f0 i)
  · exact continuous_modeAverage ι (fun (z : ℝ × Space) τ φ (ij : Fin 3 × Fin 3) =>
      axialRot (-φ) (gradField v (z.1 + τ) (axialRot φ z.2) (axialRot φ (unitVector ij.2))) ij.1) ij (f1 ij)
  · exact continuous_modeAverage ι (fun (z : ℝ × Space) τ φ (ijl : Fin 3 × Fin 3 × Fin 3) =>
      axialRot (-φ) (secondDerivField v (z.1 + τ) (axialRot φ z.2) (axialRot φ (unitVector ijl.2.1))
        (axialRot φ (unitVector ijl.2.2))) ijl.1) ijl (f2 ijl)

theorem smooth_squares_measurable {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    (ι : ℤ × ℤ) :
    Measurable (fun z : ℝ × Space => velSq v ι z.1 z.2) ∧
      Measurable (fun z : ℝ × Space => gradSq v ι z.1 z.2) ∧
      Measurable (fun z : ℝ × Space => vortSq v ι z.1 z.2) ∧
      Measurable (fun z : ℝ × Space => secondDerivModeSq v ι z.1 z.2) ∧
      Measurable (fun z : ℝ × Space => vortGradSq v ι z.1 z.2) := by
  obtain ⟨h0, h1, h2⟩ := smooth_modes_continuous hv ι
  exact ⟨(continuous_cnormSq h0).measurable, (continuous_cnormSq h1).measurable,
    (continuous_cnormSq (continuous_curlOfGrad h1)).measurable, (continuous_cnormSq h2).measurable,
    (continuous_cnormSq (continuous_curlGradOfSecondDeriv h2)).measurable⟩

theorem smooth_measurable_expanded {θD θZ : Space → ℝ} (hD : ContDiff ℝ 2 θD) (hZ : ContDiff ℝ 2 θZ)
    (c : ℝ) {w : Space → ℝ} (hwm : Measurable w) {P : ℝ} {v : ℝ → Space → Space}
    (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    Measurable fun z : ℝ × Space => expanded θD θZ c w v ι z.1 z.2 := by
  obtain ⟨m0, m1, m2, m3, m4⟩ := smooth_squares_measurable hv ι
  have gD : Measurable fun z : ℝ × Space => θD z.2 := hD.continuous.measurable.comp measurable_snd
  have gZ : Measurable fun z : ℝ × Space => θZ z.2 := hZ.continuous.measurable.comp measurable_snd
  have hD' : Measurable fun z : ℝ × Space => ModeWeights.secondDerivNorm θD z.2 :=
    (continuous_secondDerivNorm hD).measurable.comp measurable_snd
  have hZ' : Measurable fun z : ℝ × Space => ModeWeights.secondDerivNorm θZ z.2 :=
    (continuous_secondDerivNorm hZ).measurable.comp measurable_snd
  have gw : Measurable fun z : ℝ × Space => w z.2 := hwm.comp measurable_snd
  unfold expanded
  exact (((((gD.sub measurable_const).mul m3).add ((measurable_const.sub gD).mul m4)).add
    ((measurable_const.sub gZ).mul m2)).add (((gZ.sub hD').sub (measurable_const.mul gw)).mul m1)).sub
    (hZ'.mul m0)

theorem smooth_measurable_mainPos (c : ℝ) {w : Space → ℝ} (hwm : Measurable w) {P : ℝ}
    {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    Measurable fun z : ℝ × Space => mainPos c w v ι z.1 z.2 := by
  obtain ⟨m0, m1, m2, m3, m4⟩ := smooth_squares_measurable hv ι
  have gw : Measurable fun z : ℝ × Space => w z.2 := hwm.comp measurable_snd
  unfold mainPos
  exact (m4.add (measurable_const.mul m2)).add (measurable_const.mul (m3.add (gw.mul m1)))

theorem norm_unit (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem apply_unit_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : Space →L[ℝ] E) (i : Fin 3) :
    ‖G (unitVector i)‖ ≤ ‖G‖ := by
  simpa [norm_unit] using G.le_opNorm (unitVector i)

theorem apply_unit₂_le (H : Space →L[ℝ] Space →L[ℝ] Space) (i j : Fin 3) :
    ‖H (unitVector i) (unitVector j)‖ ≤ ‖H‖ := by
  simpa [norm_unit] using H.le_opNorm₂ (unitVector i) (unitVector j)

theorem matNorm_le (G : Space →L[ℝ] Space) : matSq G ≤ 3 * ‖G‖ ^ 2 := by
  unfold matSq
  calc ∑ i : Fin 3, ‖G (unitVector i)‖ ^ 2 ≤ ∑ _i : Fin 3, ‖G‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (apply_unit_le G i) 2
    _ = 3 * ‖G‖ ^ 2 := by simp

theorem secondDerivSq_le (H : Space →L[ℝ] Space →L[ℝ] Space) : secondDerivSq H ≤ 9 * ‖H‖ ^ 2 := by
  unfold secondDerivSq
  calc ∑ j : Fin 3, ∑ l : Fin 3, ‖H (unitVector j) (unitVector l)‖ ^ 2
      ≤ ∑ _j : Fin 3, ∑ _l : Fin 3, ‖H‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ =>
          pow_le_pow_left₀ (norm_nonneg _) (apply_unit₂_le H j l) 2
    _ = 9 * ‖H‖ ^ 2 := by simp; ring

theorem trace_sq_le (H : Space →L[ℝ] Space →L[ℝ] Space) : ‖secondDerivTrace H‖ ^ 2 ≤ 9 * ‖H‖ ^ 2 := by
  have h1 : ‖secondDerivTrace H‖ ≤ 3 * ‖H‖ := by
    unfold secondDerivTrace
    calc ‖∑ j : Fin 3, H (unitVector j) (unitVector j)‖ ≤ ∑ j : Fin 3, ‖H (unitVector j) (unitVector j)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, ‖H‖ := Finset.sum_le_sum fun j _ => apply_unit₂_le H j j
      _ = 3 * ‖H‖ := by simp
  nlinarith [norm_nonneg (secondDerivTrace H), norm_nonneg H]

def curlMap : (Space →L[ℝ] Space) →L[ℝ] Space := LinearMap.toContinuousLinearMap curlLinear

theorem curl_sq_le (G : Space →L[ℝ] Space) : ‖curlVec G‖ ^ 2 ≤ ‖curlMap‖ ^ 2 * ‖G‖ ^ 2 := by
  have h : ‖curlVec G‖ ≤ ‖curlMap‖ * ‖G‖ := curlMap.le_opNorm G
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem period_finite_of_le {f g : ℝ → Space → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hle : ∀ σ y, f σ y ≤ K * g σ y) (hg : periodLIntegral g < ⊤) : periodLIntegral f < ⊤ := by
  refine lt_of_le_of_lt (b := ENNReal.ofReal K * periodLIntegral g) ?_
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg)
  unfold periodLIntegral
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun σ => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  rw [← ENNReal.ofReal_mul hK]
  exact ENNReal.ofReal_le_ofReal (hle σ y)

theorem norm_iter_one (f : Space → Space) (y : Space) :
    ‖iteratedFDeriv ℝ 1 f y‖ = ‖fderiv ℝ f y‖ := by
  rw [norm_iteratedFDeriv_one]

theorem norm_iter_two (f : Space → Space) (y : Space) :
    ‖iteratedFDeriv ℝ 2 f y‖ = ‖fderiv ℝ (fun x => fderiv ℝ f x) y‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]

theorem smooth_fderiv_curl_apply {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    (σ : ℝ) (y u : Space) :
    fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y u = curlVec (secondDerivField v σ y u) := by
  have hvs : ContDiff ℝ ∞ (v σ) := hv.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hd : DifferentiableAt ℝ (fderiv ℝ (v σ)) y :=
    ((hvs.fderiv_right (m := 1) (top_add_le 1)).differentiable (by norm_num)) y
  have e : (fun x => curlVec (fderiv ℝ (v σ) x)) = (LinearMap.toContinuousLinearMap curlLinear) ∘ fderiv ℝ (v σ) :=
    funext fun x => rfl
  rw [e, ((LinearMap.toContinuousLinearMap curlLinear).hasFDerivAt.comp y hd.hasFDerivAt).fderiv]
  rfl

theorem smooth_energy_continuous {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    Continuous (fun z : ℝ × Space => matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v z.1) x)) z.2)) ∧
      Continuous (fun z : ℝ × Space => ‖curlVec (fderiv ℝ (v z.1) z.2)‖ ^ 2) ∧
      Continuous (fun z : ℝ × Space => ‖secondDerivTrace (secondDerivField v z.1 z.2)‖ ^ 2) ∧
      Continuous (fun z : ℝ × Space => matSq (gradField v z.1 z.2)) := by
  obtain ⟨-, c1, c2⟩ := smooth_fields_continuous hv
  have h1 : ContDiff ℝ 2 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => v z.1 y) (g := fun z => z.2)
      (hv.smooth.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (top_add_le 2)
  have hL : ContDiff ℝ 2 fun G : Space →L[ℝ] Space => curlVec G :=
    (LinearMap.toContinuousLinearMap curlLinear).contDiff
  have h3 : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (fun x => curlVec (fderiv ℝ (v z.1) x)) z.2) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => curlVec (fderiv ℝ (v z.1) y))
      (g := fun z => z.2) (hL.comp (h1.comp (contDiff_fst.fst.prodMk contDiff_snd))) contDiff_snd
      (by norm_num)
  have hc : Continuous fun z : ℝ × Space => curlVec (fderiv ℝ (v z.1) z.2) :=
    hL.continuous.comp c1
  refine ⟨continuous_matSq h3.continuous, hc.norm.pow 2, ?_, continuous_matSq c1⟩
  exact (continuous_finsetSum _ fun j _ => (c2.clm_apply continuous_const).clm_apply continuous_const).norm.pow 2

theorem integral_eq_period {f : ℝ → Space → ℝ} (hf : Measurable fun z : ℝ × Space => f z.1 z.2)
    (hf0 : ∀ σ y, 0 ≤ f σ y) (hfin : periodLIntegral f < ⊤) :
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, f σ y = (periodLIntegral f).toReal := by
  have hy : ∀ σ, ∫ y, f σ y = (∫⁻ y, ENNReal.ofReal (f σ y)).toReal := fun σ =>
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hf0 σ))
      (hf.comp measurable_prodMk_left).aestronglyMeasurable
  simp_rw [hy]
  unfold periodLIntegral
  exact integral_toReal (measurable_inner hf).aemeasurable (ae_lt_top (measurable_inner hf) hfin.ne)

theorem smooth_fields_finite {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    {w : Space → ℝ} (hw0 : ∀ y, 0 ≤ w y) {B : ℝ} (hB : ∀ y, w y ≤ B) (hwm : Measurable w) :
    periodLIntegral (fun σ y => matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)) < ⊤ ∧
      periodLIntegral (fun σ y => ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2) < ⊤ ∧
      periodLIntegral (fun σ y => ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2) < ⊤ ∧
      periodLIntegral (fun σ y => w y * matSq (gradField v σ y)) < ⊤ := by
  have d1 := hv.derivatives_finite 1 le_rfl
  have d2 := hv.derivatives_finite 2 (by norm_num)
  have hB0 : 0 ≤ B := (hw0 0).trans (hB 0)
  refine ⟨period_finite_of_le (K := 3 * ‖curlMap‖ ^ 2) (by positivity) (fun σ y => ?_) d2,
    period_finite_of_le (K := ‖curlMap‖ ^ 2) (by positivity) (fun σ y => ?_) d1,
    period_finite_of_le (K := 9) (by norm_num) (fun σ y => ?_) d2,
    period_finite_of_le (K := B * 3) (by positivity) (fun σ y => ?_) d1⟩
  · rw [norm_iter_two]
    unfold matSq
    simp only [smooth_fderiv_curl_apply hv]
    calc ∑ i : Fin 3, ‖curlVec (secondDerivField v σ y (unitVector i))‖ ^ 2
        ≤ ∑ i : Fin 3, ‖curlMap‖ ^ 2 * ‖secondDerivField v σ y (unitVector i)‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => curl_sq_le _
      _ ≤ ∑ _i : Fin 3, ‖curlMap‖ ^ 2 * ‖secondDerivField v σ y‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (apply_unit_le (secondDerivField v σ y) i) 2) (by positivity)
      _ = 3 * ‖curlMap‖ ^ 2 * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, secondDerivField]
          push_cast
          ring
  · rw [norm_iter_one]
    exact curl_sq_le _
  · rw [norm_iter_two]
    exact trace_sq_le _
  · rw [norm_iter_one]
    calc w y * matSq (gradField v σ y) ≤ B * (3 * ‖fderiv ℝ (v σ) y‖ ^ 2) :=
          mul_le_mul (hB y) (matNorm_le _) (Finset.sum_nonneg fun _ _ => sq_nonneg _) hB0
      _ = B * 3 * ‖fderiv ℝ (v σ) y‖ ^ 2 := by ring

theorem smooth_vorticityEnergy_eq {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    vorticityEnergy v =
      (periodLIntegral (fun σ y => matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y))).toReal
        + 1 / 4 * (periodLIntegral (fun σ y => ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2)).toReal := by
  obtain ⟨e1, e2, -, -⟩ := smooth_energy_continuous hv
  obtain ⟨f1, f2, -, -⟩ := smooth_fields_finite hv (w := fun _ => 0) (fun _ => le_rfl) (B := 0)
    (fun _ => le_rfl) measurable_const
  have n1 : ∀ σ y, 0 ≤ matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y) := fun σ y =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have n2 : ∀ σ y, 0 ≤ (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2 := fun σ y => by positivity
  have f2' : periodLIntegral (fun σ y => (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2) < ⊤ :=
    period_finite_of_le (K := 1 / 4) (by norm_num) (fun σ y => le_rfl) f2
  have hfin : periodLIntegral (fun σ y => matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)
      + (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2) < ⊤ := by
    rw [periodLIntegral_add n1 n2 e1.measurable]
    exact ENNReal.add_lt_top.2 ⟨f1, f2'⟩
  unfold vorticityEnergy
  rw [integral_eq_period (e1.add (continuous_const.mul e2)).measurable
      (fun σ y => add_nonneg (n1 σ y) (n2 σ y)) hfin,
    periodLIntegral_add n1 n2 e1.measurable]
  have e : periodLIntegral (fun σ y => (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2)
      = ENNReal.ofReal (1 / 4) * periodLIntegral (fun σ y => ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2) := by
    unfold periodLIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext σ
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext y
    exact ENNReal.ofReal_mul (by norm_num)
  rw [e, ENNReal.toReal_add f1.ne (ENNReal.mul_ne_top ENNReal.ofReal_ne_top f2.ne), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num)]

theorem smooth_weightedEnergy_eq {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    {w : Space → ℝ} (hw0 : ∀ y, 0 ≤ w y) {B : ℝ} (hB : ∀ y, w y ≤ B) (hwm : Measurable w) :
    weightedEnergy w (gradField v) (secondDerivField v) =
      (periodLIntegral (fun σ y => ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2)).toReal
        + (periodLIntegral (fun σ y => w y * matSq (gradField v σ y))).toReal := by
  obtain ⟨-, -, e3, -⟩ := smooth_energy_continuous hv
  obtain ⟨-, -, f3, f4⟩ := smooth_fields_finite hv hw0 hB hwm
  unfold weightedEnergy
  rw [periodLIntegral_add (f := fun σ y => ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2)
      (g := fun σ y => w y * matSq (gradField v σ y)) (fun σ y => sq_nonneg _)
      (fun σ y => mul_nonneg (hw0 y) (Finset.sum_nonneg fun _ _ => sq_nonneg _)) e3.measurable,
    ENNReal.toReal_add f3.ne f4.ne]

theorem smooth_modeSum_eq_vortGrad (hP : ModeSquareSumHolds) {P : ℝ} {v : ℝ → Space → Space}
    (hv : IsSmoothPerturbation P v) :
    modeSum (vortGradSq v) =
      periodLIntegral (fun σ y => matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)) := by
  obtain ⟨-, -, c2⟩ := smooth_fields_continuous hv
  have h1 : ContDiff ℝ 2 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => v z.1 y) (g := fun z => z.2)
      (hv.smooth.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (top_add_le 2)
  have hL : ContDiff ℝ 2 fun G : Space →L[ℝ] Space => curlVec G :=
    (LinearMap.toContinuousLinearMap curlLinear).contDiff
  have h3 : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (fun x => curlVec (fderiv ℝ (v z.1) x)) z.2) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => curlVec (fderiv ℝ (v z.1) y))
      (g := fun z => z.2) (hL.comp (h1.comp (contDiff_fst.fst.prodMk contDiff_snd))) contDiff_snd
      (by norm_num)
  set G : ℝ → Space → (Space →L[ℝ] Space) := fun σ y => fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y
    with hG
  have hper : IsTimePeriodic G := by
    intro σ y
    have : v (σ + 1) = v σ := funext (hv.periodic σ)
    simp only [hG, this]
  have hfin : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤ :=
    (smooth_fields_finite hv (w := fun _ => 0) (fun _ => le_rfl) (B := 0) (fun _ => le_rfl) measurable_const).1
  have key := hP.2.1 G h3.continuous.aestronglyMeasurable hper hfin
  have hmode : ∀ ι σ y, modeGrad ι G σ y = curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) σ y) := by
    intro ι σ y
    funext il
    have hs : Continuous fun q : ℝ × ℝ => σ + q.1 := by fun_prop
    have hy : Continuous fun q : ℝ × ℝ => axialRot q.2 y :=
      continuous_axialRot_of (by fun_prop : Continuous fun q : ℝ × ℝ => q.2) continuous_const
    have he : ∀ j : Fin 3, Continuous fun q : ℝ × ℝ => axialRot q.2 (unitVector j) := fun j =>
      continuous_axialRot_of (by fun_prop : Continuous fun q : ℝ × ℝ => q.2) continuous_const
    have hg : ∀ p : Fin 3 × Fin 3, Continuous fun q : ℝ × ℝ =>
        axialRot (-q.2) (secondDerivField v (σ + q.1) (axialRot q.2 y) (axialRot q.2 (unitVector il.2))
          (axialRot q.2 (unitVector p.1))) p.2 :=
      fun p => (PiLp.continuous_apply 2 _ p.2).comp (continuous_axialRot_of
        (by fun_prop : Continuous fun q : ℝ × ℝ => -q.2)
        (((c2.comp (hs.prodMk hy)).clm_apply (he il.2)).clm_apply (he p.1)))
    have e1 : modeGrad ι G σ y il = modeAverage ι (fun τ φ (_ : Fin 3 × Fin 3) =>
        ∑ p ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), alternatingSymbol il.1 p.1 p.2 *
          axialRot (-φ) (secondDerivField v (σ + τ) (axialRot φ y) (axialRot φ (unitVector il.2))
            (axialRot φ (unitVector p.1))) p.2) il := by
      simp only [modeGrad, modeAverage]
      congr 1
      refine intervalIntegral.integral_congr fun τ _ => ?_
      refine intervalIntegral.integral_congr fun φ _ => ?_
      simp only [hG]
      rw [smooth_fderiv_curl_apply hv, curl_covariant, ← Finset.univ_product_univ, Finset.sum_product]
    rw [e1, modeAverage_finset_sum ι _ _ _ hg, ← Finset.univ_product_univ, Finset.sum_product]
    rfl
  have hcn : ∀ ι σ y, cnormSq (modeGrad ι G σ y) = vortGradSq v ι σ y := fun ι σ y => by
    rw [hmode]; rfl
  unfold modeSum
  simp_rw [hcn] at key
  exact key.symm

theorem smooth_modeSum_eq_vort (hP : ModeSquareSumHolds) {P : ℝ} {v : ℝ → Space → Space}
    (hv : IsSmoothPerturbation P v) :
    modeSum (vortSq v) = periodLIntegral (fun σ y => ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2) := by
  obtain ⟨-, c1, -⟩ := smooth_fields_continuous hv
  set X : ℝ → Space → Space := fun σ y => curlVec (fderiv ℝ (v σ) y) with hX
  have hL : Continuous fun G : Space →L[ℝ] Space => curlVec G :=
    (LinearMap.toContinuousLinearMap curlLinear).continuous
  have hXc : Continuous fun z : ℝ × Space => X z.1 z.2 := hL.comp c1
  have hper : IsTimePeriodic X := by
    intro σ y
    have : v (σ + 1) = v σ := funext (hv.periodic σ)
    simp only [hX, this]
  have hfin : periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) < ⊤ :=
    (smooth_fields_finite hv (w := fun _ => 0) (fun _ => le_rfl) (B := 0) (fun _ => le_rfl) measurable_const).2.1
  have key := hP.1 X hXc.aestronglyMeasurable hper hfin
  have hmode : ∀ ι σ y, modeVel ι X σ y = curlOfGrad (modeGrad ι (gradField v) σ y) := by
    intro ι σ y
    funext i
    have hs : Continuous fun q : ℝ × ℝ => σ + q.1 := by fun_prop
    have hy : Continuous fun q : ℝ × ℝ => axialRot q.2 y :=
      continuous_axialRot_of (by fun_prop : Continuous fun q : ℝ × ℝ => q.2) continuous_const
    have hg : ∀ p : Fin 3 × Fin 3, Continuous fun q : ℝ × ℝ =>
        axialRot (-q.2) (gradField v (σ + q.1) (axialRot q.2 y) (axialRot q.2 (unitVector p.1))) p.2 :=
      fun p => (PiLp.continuous_apply 2 _ p.2).comp (continuous_axialRot_of
        (by fun_prop : Continuous fun q : ℝ × ℝ => -q.2) ((c1.comp (hs.prodMk hy)).clm_apply
          (continuous_axialRot_of (by fun_prop : Continuous fun q : ℝ × ℝ => q.2) continuous_const)))
    have e1 : modeVel ι X σ y i = modeAverage ι (fun τ φ (_ : Fin 3) =>
        ∑ p ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), alternatingSymbol i p.1 p.2 *
          axialRot (-φ) (gradField v (σ + τ) (axialRot φ y) (axialRot φ (unitVector p.1))) p.2) i := by
      simp only [modeVel, modeAverage]
      congr 1
      refine intervalIntegral.integral_congr fun τ _ => ?_
      refine intervalIntegral.integral_congr fun φ _ => ?_
      simp only [hX]
      rw [curl_covariant, ← Finset.univ_product_univ, Finset.sum_product]
      rfl
    rw [e1, modeAverage_finset_sum ι _ _ _ hg, ← Finset.univ_product_univ, Finset.sum_product]
    rfl
  have hcn : ∀ ι σ y, cnormSq (modeVel ι X σ y) = vortSq v ι σ y := fun ι σ y => by
    rw [hmode]; rfl
  unfold modeSum
  simp_rw [hcn] at key
  exact key.symm

theorem slice_finite_of_le {f g : Space → ℝ} {K : ℝ} (hK : 0 ≤ K) (hle : ∀ y, f y ≤ K * g y)
    (hg : (∫⁻ y, ENNReal.ofReal (g y)) < ⊤) : (∫⁻ y, ENNReal.ofReal (f y)) < ⊤ := by
  refine lt_of_le_of_lt (b := ENNReal.ofReal K * ∫⁻ y, ENNReal.ofReal (g y)) ?_
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  rw [← ENNReal.ofReal_mul hK]
  exact ENNReal.ofReal_le_ofReal (hle y)

theorem integrable_of_lintegral {f : Space → ℝ} (hf : Continuous f) (h0 : ∀ y, 0 ≤ f y)
    (h : (∫⁻ y, ENNReal.ofReal (f y)) < ⊤) : Integrable f :=
  ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ h0)).2 h⟩

theorem weight_div_le (a : ℝ) (y : Space) (ha : 0 ≤ a) : a / (1 + ‖y‖) ^ 2 ≤ a :=
  div_le_self ha (one_le_pow₀ (by linarith [norm_nonneg y]))

theorem smooth_slice_smooth {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (σ : ℝ) :
    ContDiff ℝ ∞ (v σ) ∧ ContDiff ℝ ∞ (fderiv ℝ (v σ)) ∧
      ∀ y a b, fderiv ℝ (fderiv ℝ (v σ)) y a b = fderiv ℝ (fderiv ℝ (v σ)) y b a := by
  have hf : ContDiff ℝ ∞ (v σ) := hv.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hDf : ContDiff ℝ ∞ (fderiv ℝ (v σ)) := hf.fderiv_right (m := ∞) (by
    rw [← WithTop.coe_one, ← WithTop.coe_add, top_add])
  exact ⟨hf, hDf, fun y a b => hf.contDiffAt.isSymmSndFDerivAt (by simp; exact le_trans (le_of_eq (by norm_num)) (top_add_le 1)) a b⟩

theorem smooth_column_fderiv {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (σ : ℝ)
    (l : Fin 3) (y a : Space) :
    fderiv ℝ (fun x => fderiv ℝ (v σ) x (unitVector l)) y a = fderiv ℝ (fderiv ℝ (v σ)) y a (unitVector l) := by
  obtain ⟨-, hDf, -⟩ := smooth_slice_smooth hv σ
  rw [fderiv_clm_apply ((hDf.differentiable (by simp)) y) (differentiableAt_const _)]
  simp

theorem smooth_divergence_deriv_zero {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    (σ : ℝ) (y a : Space) :
    ∑ i : Fin 3, (fderiv ℝ (fderiv ℝ (v σ)) y a (unitVector i)) i = 0 := by
  obtain ⟨-, hDf, -⟩ := smooth_slice_smooth hv σ
  have hd : ∀ i : Fin 3, HasFDerivAt (fun x => (fderiv ℝ (v σ) x (unitVector i)) i)
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp ((fderiv ℝ (fderiv ℝ (v σ)) y).flip (unitVector i))) y := by
    intro i
    have h1 : HasFDerivAt (fun x => fderiv ℝ (v σ) x (unitVector i))
        ((fderiv ℝ (fderiv ℝ (v σ)) y).flip (unitVector i)) y := by
      have := ((hDf.differentiable (by simp)) y).hasFDerivAt.clm_apply (hasFDerivAt_const (unitVector i) y)
      simpa using this
    exact (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y h1
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => hd i
  have hzero : (fun x => ∑ i : Fin 3, (fderiv ℝ (v σ) x (unitVector i)) i) = fun _ => 0 :=
    funext fun x => hv.divergence_free σ x
  rw [hzero] at hsum
  have := congrArg (fun L : Space →L[ℝ] ℝ => L a) ((hasFDerivAt_const (0 : ℝ) y).unique hsum)
  simpa using this.symm

theorem smooth_slice_good {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      (∫⁻ y, ENNReal.ofReal (‖fderiv ℝ (v σ) y‖ ^ 2)) < ⊤ ∧
      (∫⁻ y, ENNReal.ofReal (‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ ^ 2)) < ⊤ := by
  obtain ⟨-, c1, c2⟩ := smooth_fields_continuous hv
  have d1 := hv.derivatives_finite 1 le_rfl
  have d2 := hv.derivatives_finite 2 (by norm_num)
  simp only [periodLIntegral, norm_iter_one, norm_iter_two] at d1 d2
  have m1 : Measurable fun σ => ∫⁻ y, ENNReal.ofReal (‖fderiv ℝ (v σ) y‖ ^ 2) :=
    measurable_inner (F := fun σ y => ‖fderiv ℝ (v σ) y‖ ^ 2) (c1.norm.pow 2).measurable
  have m2 : Measurable fun σ => ∫⁻ y, ENNReal.ofReal (‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ ^ 2) :=
    measurable_inner (F := fun σ y => ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ ^ 2) (c2.norm.pow 2).measurable
  filter_upwards [ae_lt_top m1 d1.ne, ae_lt_top m2 d2.ne] with σ h1 h2
  exact ⟨h1, h2⟩

theorem const_one_bound : ∃ B, ∀ y : Space, ∀ j ≤ 2,
    (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j (fun _ : Space => (1 : ℝ)) y‖ ≤ B := by
  refine ⟨1, fun y j _ => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  · rw [iteratedFDeriv_const_of_ne hj0.ne']
    simp

theorem smooth_slice_secondDerivSq_eq (hI4 : CurlWeightIdentityDecayHolds) {P : ℝ} {v : ℝ → Space → Space}
    (hv : IsSmoothPerturbation P v) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∫⁻ y, ENNReal.ofReal (secondDerivSq (secondDerivField v σ y)) =
        ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2) := by
  filter_upwards [smooth_slice_good hv] with σ hg
  obtain ⟨g1, g2⟩ := hg
  obtain ⟨hf, hDf, hsym⟩ := smooth_slice_smooth hv σ
  set H : Space → Space →L[ℝ] Space →L[ℝ] Space := fun y => fderiv ℝ (fderiv ℝ (v σ)) y with hHdef
  have hH : ∀ y, secondDerivField v σ y = H y := fun y => rfl
  have g2' : (∫⁻ y, ENNReal.ofReal (‖H y‖ ^ 2)) < ⊤ := g2
  have hs : ∀ y (a b c : Fin 3), H y (unitVector a) (unitVector b) c = H y (unitVector b) (unitVector a) c :=
    fun y a b c => by rw [hHdef]; simp only; rw [hsym]
  have hdz : ∀ y (m : Fin 3), ∑ i : Fin 3, H y (unitVector m) (unitVector i) i = 0 :=
    fun y m => smooth_divergence_deriv_zero hv σ y (unitVector m)
  have hL : ContDiff ℝ ∞ fun G : Space →L[ℝ] Space => curlVec G :=
    (LinearMap.toContinuousLinearMap curlLinear).contDiff
  set u : Fin 3 → Space → Space := fun l x => fderiv ℝ (v σ) x (unitVector l) with hudef
  set om : Space → Space := fun x => curlVec (fderiv ℝ (v σ) x) with homdef
  have hu_d : ∀ l y a, fderiv ℝ (u l) y a = H y a (unitVector l) := fun l y a => smooth_column_fderiv hv σ l y a
  have hom_d : ∀ y a, fderiv ℝ om y a = curlVec (H y a) := fun y a => smooth_fderiv_curl_apply hv σ y a
  have hu_cd : ∀ l, ContDiff ℝ ∞ (u l) := fun l => hDf.clm_apply contDiff_const
  have hom_cd : ContDiff ℝ ∞ om := hL.comp hDf
  have two_le : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
  have hu_div : ∀ l y, divergenceAt (u l) y = 0 := by
    intro l y
    simp only [divergenceAt, hu_d]
    rw [← hdz y l]
    exact Finset.sum_congr rfl fun i _ => hs y i l i
  have hom_div : ∀ y, divergenceAt om y = 0 := by
    intro y
    simp only [divergenceAt, hom_d, curlVec_coord, Fin.sum_univ_three]
    norm_num [alternatingSymbol]
    linear_combination hs y 0 1 2 + hs y 1 2 0 + hs y 2 0 1
  have hcol : ∀ l y, fderiv ℝ (u l) y = H y (unitVector l) := by
    intro l y
    ext a : 1
    rw [hu_d]
    simp only [hHdef]
    exact hsym y a (unitVector l)
  have hHe : ∀ y (l : Fin 3), ‖H y (unitVector l)‖ ^ 2 ≤ ‖H y‖ ^ 2 := fun y l =>
    pow_le_pow_left₀ (norm_nonneg _) (apply_unit_le (H y) l) 2
  have hue : ∀ l y, ‖u l y‖ ^ 2 ≤ ‖fderiv ℝ (v σ) y‖ ^ 2 := fun l y =>
    pow_le_pow_left₀ (norm_nonneg _) (apply_unit_le (fderiv ℝ (v σ) y) l) 2
  have fu1 : ∀ l, (∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ (u l) y))) < ⊤ := fun l =>
    slice_finite_of_le (K := 3) (by norm_num) (fun y => by
      rw [hcol]; exact (matNorm_le _).trans (by nlinarith [hHe y l])) g2'
  have fu2 : ∀ l, (∫⁻ y, ENNReal.ofReal (‖u l y‖ ^ 2 / (1 + ‖y‖) ^ 2)) < ⊤ := fun l =>
    slice_finite_of_le (K := 1) (by norm_num) (fun y => by
      rw [one_mul]; exact (weight_div_le _ y (sq_nonneg _)).trans (hue l y)) g1
  have hfo : ∀ y, matSq (fderiv ℝ om y) ≤ 3 * ‖curlMap‖ ^ 2 * ‖H y‖ ^ 2 := by
    intro y
    unfold matSq
    simp only [hom_d]
    calc ∑ i : Fin 3, ‖curlVec (H y (unitVector i))‖ ^ 2
        ≤ ∑ i : Fin 3, ‖curlMap‖ ^ 2 * ‖H y (unitVector i)‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => curl_sq_le _
      _ ≤ ∑ _i : Fin 3, ‖curlMap‖ ^ 2 * ‖H y‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hHe y i) (by positivity)
      _ = 3 * ‖curlMap‖ ^ 2 * ‖H y‖ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have fo1 : (∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ om y))) < ⊤ :=
    slice_finite_of_le (K := 3 * ‖curlMap‖ ^ 2) (by positivity) hfo g2'
  have fo2 : (∫⁻ y, ENNReal.ofReal (‖om y‖ ^ 2 / (1 + ‖y‖) ^ 2)) < ⊤ :=
    slice_finite_of_le (K := ‖curlMap‖ ^ 2) (by positivity) (fun y =>
      (weight_div_le _ y (sq_nonneg _)).trans (curl_sq_le _)) g1
  have I4u := fun l => hI4 (fun _ => 1) (u l) contDiff_const const_one_bound ((hu_cd l).of_le two_le)
    (hu_div l) (fu1 l) (fu2 l)
  have I4w := hI4 (fun _ => 1) om contDiff_const const_one_bound (hom_cd.of_le two_le) hom_div fo1 fo2
  have hz : ∀ y, fderiv ℝ (fun x => fderiv ℝ (fun _ : Space => (1 : ℝ)) x) y = 0 := fun y => by simp
  simp only [hz, ContinuousLinearMap.zero_apply, zero_mul, Finset.sum_const_zero, integral_zero, sub_zero,
    one_mul] at I4u I4w
  have hdz' : ∀ y (m : Fin 3), H y (unitVector m) (unitVector 0) 0 + H y (unitVector m) (unitVector 1) 1
      + H y (unitVector m) (unitVector 2) 2 = 0 := fun y m => by
    have := hdz y m
    rwa [Fin.sum_univ_three] at this
  have P1 : ∀ y, secondDerivSq (secondDerivField v σ y) = ∑ l : Fin 3, matSq (fderiv ℝ (u l) y) := by
    intro y
    simp only [secondDerivSq, matSq, hu_d, hH]
    exact Finset.sum_comm
  have P2 : ∀ y, ∑ l : Fin 3, ‖curlVec (fderiv ℝ (u l) y)‖ ^ 2 = matSq (fderiv ℝ om y) := by
    intro y
    simp only [matSq, hom_d, hcol]
  have P3 : ∀ y, ‖curlVec (fderiv ℝ om y)‖ ^ 2 = ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2 := by
    intro y
    have hv3 : curlVec (fderiv ℝ om y) = -secondDerivTrace (H y) := by
      apply space_eq_of_coords
      · simp only [curlVec_coord, hom_d, secondDerivTrace, Fin.sum_univ_three, PiLp.neg_apply, PiLp.add_apply]
        norm_num [alternatingSymbol]
        linear_combination hdz' y 0 + hs y 1 0 1 + hs y 2 0 2
      · simp only [curlVec_coord, hom_d, secondDerivTrace, Fin.sum_univ_three, PiLp.neg_apply, PiLp.add_apply]
        norm_num [alternatingSymbol]
        linear_combination hdz' y 1 + hs y 0 1 0 + hs y 2 1 2
      · simp only [curlVec_coord, hom_d, secondDerivTrace, Fin.sum_univ_three, PiLp.neg_apply, PiLp.add_apply]
        norm_num [alternatingSymbol]
        linear_combination hdz' y 2 + hs y 0 2 0 + hs y 1 2 1
    rw [hv3, norm_neg, hH]
  have i1 : ∀ l, Integrable fun y => matSq (fderiv ℝ (u l) y) := fun l =>
    integrable_of_lintegral (continuous_matSq ((hu_cd l).continuous_fderiv (by simp)))
      (fun y => Finset.sum_nonneg fun _ _ => sq_nonneg _) (fu1 l)
  have i2 : ∀ l, Integrable fun y => ‖curlVec (fderiv ℝ (u l) y)‖ ^ 2 := fun l =>
    integrable_of_lintegral ((hL.continuous.comp ((hu_cd l).continuous_fderiv (by simp))).norm.pow 2)
      (fun y => sq_nonneg _)
      (slice_finite_of_le (K := ‖curlMap‖ ^ 2) (by positivity) (fun y => by
        rw [hcol]; exact (curl_sq_le _).trans (mul_le_mul_of_nonneg_left (hHe y l) (by positivity))) g2')
  have i3 : Integrable fun y => ‖curlVec (fderiv ℝ om y)‖ ^ 2 :=
    integrable_of_lintegral ((hL.continuous.comp (hom_cd.continuous_fderiv (by simp))).norm.pow 2)
      (fun y => sq_nonneg _)
      (slice_finite_of_le (K := 9) (by norm_num) (fun y => by
        rw [P3, hH]; exact trace_sq_le _) g2')
  have chain : ∫ y, secondDerivSq (secondDerivField v σ y) = ∫ y, ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2 := by
    calc ∫ y, secondDerivSq (secondDerivField v σ y) = ∫ y, ∑ l : Fin 3, matSq (fderiv ℝ (u l) y) := by simp only [P1]
      _ = ∑ l : Fin 3, ∫ y, matSq (fderiv ℝ (u l) y) := integral_finsetSum _ fun l _ => i1 l
      _ = ∑ l : Fin 3, ∫ y, ‖curlVec (fderiv ℝ (u l) y)‖ ^ 2 := by simp only [I4u]
      _ = ∫ y, ∑ l : Fin 3, ‖curlVec (fderiv ℝ (u l) y)‖ ^ 2 := (integral_finsetSum _ fun l _ => i2 l).symm
      _ = ∫ y, matSq (fderiv ℝ om y) := by simp only [P2]
      _ = ∫ y, ‖curlVec (fderiv ℝ om y)‖ ^ 2 := I4w.symm
      _ = ∫ y, ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2 := by simp only [P3]
  have j1 : Integrable fun y => secondDerivSq (secondDerivField v σ y) := by
    simp only [P1]; exact integrable_finsetSum _ fun l _ => i1 l
  have j2 : Integrable fun y => ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2 := by
    simp only [← P3]; exact i3
  rw [← ofReal_integral_eq_lintegral_ofReal j1 (ae_of_all _ fun y =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal j2 (ae_of_all _ fun y => sq_nonneg _), chain]

theorem smooth_modeSum_eq_secondDeriv (hP : ModeSquareSumHolds) (hI4 : CurlWeightIdentityDecayHolds) {P : ℝ}
    {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    modeSum (secondDerivModeSq v) = periodLIntegral (fun σ y => ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2) := by
  obtain ⟨-, -, c2⟩ := smooth_fields_continuous hv
  have hfin : periodLIntegral (fun σ y => secondDerivSq (secondDerivField v σ y)) < ⊤ :=
    period_finite_of_le (K := 9) (by norm_num) (fun σ y => by rw [norm_iter_two]; exact secondDerivSq_le _)
      (hv.derivatives_finite 2 (by norm_num))
  have hper : IsTimePeriodic (secondDerivField v) := by
    intro σ y
    have : v (σ + 1) = v σ := funext (hv.periodic σ)
    simp only [secondDerivField, this]
  have key := hP.2.2.1 (secondDerivField v) c2.aestronglyMeasurable hper hfin
  have e : periodLIntegral (fun σ y => secondDerivSq (secondDerivField v σ y)) =
      periodLIntegral (fun σ y => ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2) := by
    unfold periodLIntegral
    exact lintegral_congr_ae (smooth_slice_secondDerivSq_eq hI4 hv)
  rw [← e, key]
  rfl

theorem smooth_modeSum_eq_weighted_grad (hP : ModeSquareSumHolds) {P : ℝ} {v : ℝ → Space → Space}
    (hv : IsSmoothPerturbation P v) {w : Space → ℝ} (hw0 : ∀ y, 0 ≤ w y) {B : ℝ} (hB : ∀ y, w y ≤ B)
    (hwm : Measurable w) (hwa : IsAxisymmetric w) :
    modeSum (fun ι σ y => w y * gradSq v ι σ y) =
      periodLIntegral (fun σ y => w y * matSq (gradField v σ y)) := by
  obtain ⟨-, c1, -⟩ := smooth_fields_continuous hv
  set G' : ℝ → Space → (Space →L[ℝ] Space) := fun σ y => Real.sqrt (w y) • gradField v σ y with hG'
  have hfr : ∀ σ y, matSq (G' σ y) = w y * matSq (gradField v σ y) := by
    intro σ y
    simp only [hG', matSq, ContinuousLinearMap.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (hw0 y), Finset.mul_sum]
  have hfin : periodLIntegral (fun σ y => matSq (G' σ y)) < ⊤ := by
    simp_rw [hfr]
    exact (smooth_fields_finite hv hw0 hB hwm).2.2.2
  have hmeas : AEStronglyMeasurable (fun z : ℝ × Space => G' z.1 z.2) volume :=
    ((hwm.comp measurable_snd).sqrt.aestronglyMeasurable).smul c1.aestronglyMeasurable
  have hper : IsTimePeriodic G' := by
    intro σ y
    have : v (σ + 1) = v σ := funext (hv.periodic σ)
    simp only [hG', gradField, this]
  have key := hP.2.1 G' hmeas hper hfin
  have hcn : ∀ ι σ y, cnormSq (modeGrad ι G' σ y) = w y * gradSq v ι σ y := by
    intro ι σ y
    have hm : modeGrad ι G' σ y = fun ij => (Real.sqrt (w y) : ℂ) * modeGrad ι (gradField v) σ y ij := by
      funext ij
      unfold modeGrad
      rw [← modeAverage_const_mul]
      congr 1
      funext τ φ ij'
      simp only [hG', hwa φ y, ContinuousLinearMap.smul_apply, axialRot_smul_vec, PiLp.smul_apply, smul_eq_mul]
    rw [hm]
    simp only [gradSq, cnormSq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (hw0 y), Finset.mul_sum]
  unfold modeSum
  simp_rw [hfr, hcn] at key
  exact key.symm

theorem smooth_modeSum_eq_weighted_vel (hP : ModeSquareSumHolds) {P : ℝ} {v : ℝ → Space → Space}
    (hv : IsSmoothPerturbation P v) :
    modeSum (fun ι σ y => velSq v ι σ y / (1 + ‖y‖) ^ 2) =
      periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) := by
  obtain ⟨c0, -, -⟩ := smooth_fields_continuous hv
  set X : ℝ → Space → Space := fun σ y => (1 + ‖y‖)⁻¹ • v σ y with hX
  have hpos : ∀ y : Space, 0 < 1 + ‖y‖ := fun y => by linarith [norm_nonneg y]
  have hnx : ∀ σ y, ‖X σ y‖ ^ 2 = ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 := by
    intro σ y
    simp only [hX, norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, abs_of_pos (hpos y)]
    field_simp
  have hfin : periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) < ⊤ := by
    simp_rw [hnx]
    exact hv.weighted_finite
  have hmeas : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume :=
    (((continuous_const.add (continuous_norm.comp continuous_snd)).inv₀ fun z => (hpos z.2).ne').smul
      c0).aestronglyMeasurable
  have hper : IsTimePeriodic X := by
    intro σ y
    simp only [hX, hv.periodic σ y]
  have key := hP.1 X hmeas hper hfin
  have hcn : ∀ ι σ y, cnormSq (modeVel ι X σ y) = velSq v ι σ y / (1 + ‖y‖) ^ 2 := by
    intro ι σ y
    have hm : modeVel ι X σ y = fun i => (((1 + ‖y‖)⁻¹ : ℝ) : ℂ) * modeVel ι v σ y i := by
      funext i
      unfold modeVel
      rw [← modeAverage_const_mul]
      congr 1
      funext τ φ i'
      simp only [hX, norm_axialRot, axialRot_smul_vec, PiLp.smul_apply, smul_eq_mul]
    rw [hm]
    simp only [velSq, cnormSq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_pos (hpos y), div_eq_mul_inv, inv_pow, mul_comm]
    rw [Finset.sum_mul]
  unfold modeSum
  simp_rw [hnx, hcn] at key
  exact key.symm

theorem ae_slice_of_modeSum {F : ℤ × ℤ → ℝ → Space → ℝ}
    (hF : ∀ ι, Measurable fun z : ℝ × Space => F ι z.1 z.2) (h : modeSum F < ⊤) (ι : ℤ × ℤ) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), (∫⁻ y, ENNReal.ofReal (F ι σ y)) < ⊤ :=
  ae_lt_top (measurable_inner (hF ι)) (ENNReal.lt_top_of_tsum_ne_top h.ne ι).ne

theorem smooth_mode_slices (hP : ModeSquareSumHolds) (hI4 : CurlWeightIdentityDecayHolds) {P : ℝ}
    {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      (∫⁻ y, ENNReal.ofReal (velSq v ι σ y / (1 + ‖y‖) ^ 2)) < ⊤ ∧
      (∫⁻ y, ENNReal.ofReal (gradSq v ι σ y)) < ⊤ ∧ (∫⁻ y, ENNReal.ofReal (vortSq v ι σ y)) < ⊤ ∧
      (∫⁻ y, ENNReal.ofReal (secondDerivModeSq v ι σ y)) < ⊤ ∧
      (∫⁻ y, ENNReal.ofReal (vortGradSq v ι σ y)) < ⊤ := by
  have mm := smooth_squares_measurable hv
  obtain ⟨f1, f2, f3, f4⟩ := smooth_fields_finite hv (w := fun _ => 1) (fun _ => zero_le_one) (B := 1)
    (fun _ => le_rfl) measurable_const
  have hax : IsAxisymmetric (fun _ : Space => (1 : ℝ)) := fun _ _ => rfl
  have g1 : modeSum (fun ι σ y => (1 : ℝ) * gradSq v ι σ y) < ⊤ := by
    rw [smooth_modeSum_eq_weighted_grad hP hv (w := fun _ => 1) (fun _ => zero_le_one) (B := 1)
      (fun _ => le_rfl) measurable_const hax]
    exact f4
  simp only [one_mul] at g1
  have g0 : modeSum (fun ι σ y => velSq v ι σ y / (1 + ‖y‖) ^ 2) < ⊤ := by
    rw [smooth_modeSum_eq_weighted_vel hP hv]; exact hv.weighted_finite
  have g2 : modeSum (vortSq v) < ⊤ := by rw [smooth_modeSum_eq_vort hP hv]; exact f2
  have g3 : modeSum (secondDerivModeSq v) < ⊤ := by rw [smooth_modeSum_eq_secondDeriv hP hI4 hv]; exact f3
  have g4 : modeSum (vortGradSq v) < ⊤ := by rw [smooth_modeSum_eq_vortGrad hP hv]; exact f1
  have hm0 : ∀ ι, Measurable fun z : ℝ × Space => velSq v ι z.1 z.2 / (1 + ‖z.2‖) ^ 2 := fun ι =>
    (mm ι).1.div ((measurable_const.add (continuous_norm.measurable.comp measurable_snd)).pow_const 2)
  filter_upwards [ae_slice_of_modeSum hm0 g0 ι, ae_slice_of_modeSum (fun ι => (mm ι).2.1) g1 ι,
    ae_slice_of_modeSum (fun ι => (mm ι).2.2.1) g2 ι, ae_slice_of_modeSum (fun ι => (mm ι).2.2.2.1) g3 ι,
    ae_slice_of_modeSum (fun ι => (mm ι).2.2.2.2) g4 ι] with σ a0 a1 a2 a3 a4
  exact ⟨a0, a1, a2, a3, a4⟩

theorem weight_bound_one_add {θ : Space → ℝ} (hθ : ContDiff ℝ 2 θ)
    (hb : ∃ B, ∀ y, ∀ j ≤ 2, ‖y‖ ^ j * ‖iteratedFDeriv ℝ j θ y‖ ≤ B) :
    ∃ B, ∀ y, ∀ j ≤ 2, (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j θ y‖ ≤ B := by
  obtain ⟨B, hB⟩ := hb
  have hB0 : 0 ≤ B := (mul_nonneg (pow_nonneg (norm_nonneg _) 0) (norm_nonneg _)).trans (hB 0 0 (by norm_num))
  have hc : Continuous fun y => ∑ j ∈ Finset.range 3, ‖iteratedFDeriv ℝ j θ y‖ :=
    continuous_finsetSum _ fun j hj => (hθ.continuous_iteratedFDeriv (m := j) (by
      have : j ≤ 2 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      exact_mod_cast this)).norm
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : Space) 1).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨4 * (B + |K|), fun y j hj => ?_⟩
  have hpow : (2 : ℝ) ^ j ≤ 4 := by
    calc (2 : ℝ) ^ j ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hj
      _ = 4 := by norm_num
  have hn := norm_nonneg (iteratedFDeriv ℝ j θ y)
  rcases le_total ‖y‖ 1 with hy | hy
  · have hle : ‖iteratedFDeriv ℝ j θ y‖ ≤ |K| := by
      have h1 : ‖iteratedFDeriv ℝ j θ y‖ ≤ ∑ j ∈ Finset.range 3, ‖iteratedFDeriv ℝ j θ y‖ :=
        Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j θ y‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_range.2 (by omega))
      have h2 := hK y (by simpa [Metric.mem_closedBall, dist_zero_right] using hy)
      rw [Real.norm_eq_abs] at h2
      linarith [le_abs_self (∑ j ∈ Finset.range 3, ‖iteratedFDeriv ℝ j θ y‖), le_abs_self K]
    have hp : (1 + ‖y‖) ^ j ≤ 4 :=
      (pow_le_pow_left₀ (by positivity) (by linarith) j).trans hpow
    calc (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j θ y‖ ≤ 4 * |K| :=
          mul_le_mul hp hle hn (by norm_num)
      _ ≤ 4 * (B + |K|) := by nlinarith
  · have hp : (1 + ‖y‖) ^ j ≤ 4 * ‖y‖ ^ j := by
      calc (1 + ‖y‖) ^ j ≤ (2 * ‖y‖) ^ j := pow_le_pow_left₀ (by positivity) (by linarith) j
        _ = 2 ^ j * ‖y‖ ^ j := mul_pow _ _ _
        _ ≤ 4 * ‖y‖ ^ j := mul_le_mul_of_nonneg_right hpow (by positivity)
    calc (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j θ y‖ ≤ 4 * ‖y‖ ^ j * ‖iteratedFDeriv ℝ j θ y‖ :=
          mul_le_mul_of_nonneg_right hp hn
      _ = 4 * (‖y‖ ^ j * ‖iteratedFDeriv ℝ j θ y‖) := by ring
      _ ≤ 4 * B := by nlinarith [hB y j hj]
      _ ≤ 4 * (B + |K|) := by nlinarith [abs_nonneg K]

theorem weight_value_bounds {θ : Space → ℝ} {B : ℝ}
    (hB : ∀ y, ∀ j ≤ 2, (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j θ y‖ ≤ B) (y : Space) :
    |θ y| ≤ B ∧ ModeWeights.secondDerivNorm θ y ≤ B / (1 + ‖y‖) ^ 2 ∧ ModeWeights.secondDerivNorm θ y ≤ B := by
  have hpos : 0 < (1 + ‖y‖) ^ 2 := by positivity
  have h0 := hB y 0 (by norm_num)
  have h2 := hB y 2 le_rfl
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h0
  have hn : 0 ≤ ModeWeights.secondDerivNorm θ y := norm_nonneg _
  have h2' : (1 + ‖y‖) ^ 2 * ModeWeights.secondDerivNorm θ y ≤ B := h2
  have hone : 1 ≤ (1 + ‖y‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg y])
  refine ⟨h0, ?_, ?_⟩
  · rw [le_div_iff₀ hpos]; linarith
  · nlinarith

theorem space_norm_sq (w : Space) : ‖w‖ ^ 2 = ∑ i : Fin 3, w i ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [Real.norm_eq_abs, sq_abs]

theorem reVec_apply (x : Fin 3 → ℂ) (i : Fin 3) : reVec x i = (x i).re := by
  fin_cases i <;> simp [reVec, unitVector, Fin.sum_univ_three]

theorem imVec_apply (x : Fin 3 → ℂ) (i : Fin 3) : imVec x i = (x i).im := by
  fin_cases i <;> simp [imVec, unitVector, Fin.sum_univ_three]

theorem reMat_apply (g : Fin 3 × Fin 3 → ℂ) (j l : Fin 3) : reMat g (unitVector j) l = (g (l, j)).re := by
  fin_cases j <;> fin_cases l <;> simp [reMat, unitVector, Fin.sum_univ_three, EuclideanSpace.inner_single_left]

theorem imMat_apply (g : Fin 3 × Fin 3 → ℂ) (j l : Fin 3) : imMat g (unitVector j) l = (g (l, j)).im := by
  fin_cases j <;> fin_cases l <;> simp [imMat, unitVector, Fin.sum_univ_three, EuclideanSpace.inner_single_left]

theorem matNorm_re_im (g : Fin 3 × Fin 3 → ℂ) : matSq (reMat g) + matSq (imMat g) = cnormSq g := by
  simp only [matSq, space_norm_sq, reMat_apply, imMat_apply, cnormSq, Complex.sq_norm, Complex.normSq_apply,
    Fintype.sum_prod_type, Fin.sum_univ_three]
  ring

theorem curl_re_im (g : Fin 3 × Fin 3 → ℂ) :
    ‖curlVec (reMat g)‖ ^ 2 + ‖curlVec (imMat g)‖ ^ 2 = cnormSq (curlOfGrad g) := by
  simp only [space_norm_sq, curlVec_coord, reMat_apply, imMat_apply, cnormSq, curlOfGrad, Complex.sq_norm,
    Complex.normSq_apply, Fin.sum_univ_three, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem secondDerivQuad_re_im (θ : Space → ℝ) (y : Space) (x : Fin 3 → ℂ) :
    secondDerivQuad θ y x = (∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ (fun x => fderiv ℝ θ x) y (unitVector i) (unitVector j) * reVec x i * reVec x j)
      + ∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ (fun x => fderiv ℝ θ x) y (unitVector i) (unitVector j) * imVec x i * imVec x j := by
  simp only [secondDerivQuad, reVec_apply, imVec_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Fin.sum_univ_three]
  ring


theorem vec_re_im (x : Fin 3 → ℂ) : ‖reVec x‖ ^ 2 + ‖imVec x‖ ^ 2 = cnormSq x := by
  simp only [space_norm_sq, reVec_apply, imVec_apply, cnormSq, Complex.sq_norm, Complex.normSq_apply,
    Fin.sum_univ_three]
  ring

theorem curl_le_matNorm (G : Space →L[ℝ] Space) : ‖curlVec G‖ ^ 2 ≤ 2 * matSq G := by
  simp only [space_norm_sq, curlVec_coord, matSq, Fin.sum_univ_three]
  norm_num [alternatingSymbol]
  nlinarith [sq_nonneg (G (unitVector 1) 2 + G (unitVector 2) 1), sq_nonneg (G (unitVector 0) 2 + G (unitVector 2) 0),
    sq_nonneg (G (unitVector 0) 1 + G (unitVector 1) 0), sq_nonneg (G (unitVector 0) 0), sq_nonneg (G (unitVector 1) 1),
    sq_nonneg (G (unitVector 2) 2)]

theorem coord_sq_le (u : Space) (i : Fin 3) : u i ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [space_norm_sq]
  exact Finset.single_le_sum (f := fun j => u j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem quad_abs_le (A : Space →L[ℝ] Space →L[ℝ] ℝ) (u : Space) :
    |∑ i : Fin 3, ∑ j : Fin 3, A (unitVector i) (unitVector j) * u i * u j| ≤ 9 * ‖A‖ * ‖u‖ ^ 2 := by
  have hA : ∀ i j, |A (unitVector i) (unitVector j)| ≤ ‖A‖ := fun i j => by
    simpa [norm_unit, Real.norm_eq_abs] using A.le_opNorm₂ (unitVector i) (unitVector j)
  have hu : ∀ i j, |u i * u j| ≤ ‖u‖ ^ 2 := fun i j => by
    rw [abs_mul]
    nlinarith [coord_sq_le u i, coord_sq_le u j, sq_abs (u i), sq_abs (u j), abs_nonneg (u i), abs_nonneg (u j),
      sq_nonneg (|u i| - |u j|)]
  have ht : ∀ i j, |A (unitVector i) (unitVector j) * u i * u j| ≤ ‖A‖ * ‖u‖ ^ 2 := fun i j => by
    rw [mul_assoc, abs_mul]
    exact mul_le_mul (hA i j) (hu i j) (abs_nonneg _) (norm_nonneg _)
  calc |∑ i : Fin 3, ∑ j : Fin 3, A (unitVector i) (unitVector j) * u i * u j|
      ≤ ∑ i : Fin 3, ∑ j : Fin 3, |A (unitVector i) (unitVector j) * u i * u j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖A‖ * ‖u‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ht i j
    _ = 9 * ‖A‖ * ‖u‖ ^ 2 := by simp; ring

theorem secondDerivNorm_eq (θ : Space → ℝ) (y : Space) :
    ModeWeights.secondDerivNorm θ y = ‖fderiv ℝ (fun x => fderiv ℝ θ x) y‖ := by
  rw [ModeWeights.secondDerivNorm, ← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]

theorem real_field_identity (hI4 : CurlWeightIdentityDecayHolds) {θ : Space → ℝ} (hθ : ContDiff ℝ 2 θ)
    {Bθ : ℝ} (hb : ∀ y, ∀ j ≤ 2, (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j θ y‖ ≤ Bθ)
    {u : Space → Space} {G : Space → Space →L[ℝ] Space} {a b : Space → ℝ}
    (hu : ContDiff ℝ 2 u) (du : ∀ y, fderiv ℝ u y = G y) (hdiv : ∀ y, divergenceAt u y = 0)
    (ha : Continuous a) (fa : (∫⁻ y, ENNReal.ofReal (a y)) < ⊤) (hGa : ∀ y, matSq (G y) ≤ a y)
    (hbc : Continuous b) (fb : (∫⁻ y, ENNReal.ofReal (b y / (1 + ‖y‖) ^ 2)) < ⊤) (hub : ∀ y, ‖u y‖ ^ 2 ≤ b y) :
    Integrable (fun y => θ y * matSq (G y)) ∧ Integrable (fun y => θ y * ‖curlVec (G y)‖ ^ 2) ∧
      Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ (fun x => fderiv ℝ θ x) y (unitVector i) (unitVector j) * u y i * u y j) ∧
      (∫ y, θ y * matSq (G y)) - (∫ y, θ y * ‖curlVec (G y)‖ ^ 2) =
        ∫ y, ∑ i : Fin 3, ∑ j : Fin 3,
          fderiv ℝ (fun x => fderiv ℝ θ x) y (unitVector i) (unitVector j) * u y i * u y j := by
  have wb := weight_value_bounds hb
  have hpos : ∀ y : Space, 0 < (1 + ‖y‖) ^ 2 := fun y => by positivity
  have hG0 : ∀ y, 0 ≤ matSq (G y) := fun y => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfr : (∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ u y))) < ⊤ :=
    slice_finite_of_le (K := 1) zero_le_one (fun y => by rw [du, one_mul]; exact hGa y) fa
  have hwu : (∫⁻ y, ENNReal.ofReal (‖u y‖ ^ 2 / (1 + ‖y‖) ^ 2)) < ⊤ :=
    slice_finite_of_le (K := 1) zero_le_one (fun y => by
      rw [one_mul]; exact div_le_div_of_nonneg_right (hub y) (hpos y).le) fb
  have key := hI4 θ u hθ ⟨Bθ, hb⟩ hu hdiv hfr hwu
  simp only [du] at key
  have cG : Continuous G := by
    rw [show G = fderiv ℝ u from (funext du).symm]
    exact hu.continuous_fderiv (by norm_num)
  have a0 : ∀ y, 0 ≤ a y := fun y => (hG0 y).trans (hGa y)
  have ia : Integrable a := integrable_of_lintegral ha a0 fa
  have iF : Integrable fun y => matSq (G y) :=
    ia.mono' (continuous_matSq cG).aestronglyMeasurable (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hG0 y)]; exact hGa y)
  have iC : Integrable fun y => ‖curlVec (G y)‖ ^ 2 :=
    (iF.const_mul 2).mono' ((((LinearMap.toContinuousLinearMap curlLinear).continuous.comp cG).norm.pow 2
      ).aestronglyMeasurable) (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact curl_le_matNorm _)
  have hθm : AEStronglyMeasurable θ volume := hθ.continuous.aestronglyMeasurable
  have i1 : Integrable fun y => θ y * matSq (G y) :=
    iF.bdd_mul (c := Bθ) hθm (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact (wb y).1)
  have i2 : Integrable fun y => θ y * ‖curlVec (G y)‖ ^ 2 :=
    iC.bdd_mul (c := Bθ) hθm (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact (wb y).1)
  have cA : Continuous fun y => fderiv ℝ (fun x => fderiv ℝ θ x) y :=
    (hθ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have cQ : Continuous fun y => ∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ (fun x => fderiv ℝ θ x) y (unitVector i) (unitVector j) * u y i * u y j :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((((cA.clm_apply continuous_const).clm_apply continuous_const)).mul
        ((PiLp.continuous_apply 2 _ i).comp hu.continuous)).mul ((PiLp.continuous_apply 2 _ j).comp hu.continuous)
  have ib : Integrable fun y => b y / (1 + ‖y‖) ^ 2 :=
    integrable_of_lintegral (hbc.div (by fun_prop) fun y => (hpos y).ne')
      (fun y => div_nonneg ((sq_nonneg _).trans (hub y)) (hpos y).le) fb
  have i3 : Integrable fun y => ∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ (fun x => fderiv ℝ θ x) y (unitVector i) (unitVector j) * u y i * u y j := by
    refine (ib.const_mul (9 * Bθ)).mono' cQ.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs]
    refine (quad_abs_le _ _).trans ?_
    rw [← secondDerivNorm_eq]
    have h1 := (wb y).2.1
    have hn : 0 ≤ ModeWeights.secondDerivNorm θ y := norm_nonneg _
    calc 9 * ModeWeights.secondDerivNorm θ y * ‖u y‖ ^ 2 ≤ 9 * (Bθ / (1 + ‖y‖) ^ 2) * b y := by
          have := hub y
          have h9 : 9 * ModeWeights.secondDerivNorm θ y ≤ 9 * (Bθ / (1 + ‖y‖) ^ 2) := by linarith
          exact mul_le_mul h9 this (sq_nonneg _) (by nlinarith)
      _ = 9 * Bθ * (b y / (1 + ‖y‖) ^ 2) := by ring
  exact ⟨i1, i2, i3, by linarith⟩

theorem complex_field_identity (hI4 : CurlWeightIdentityDecayHolds) {θ : Space → ℝ} (hθ : ContDiff ℝ 2 θ)
    {Bθ : ℝ} (hb : ∀ y, ∀ j ≤ 2, (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j θ y‖ ≤ Bθ)
    {x : Space → Fin 3 → ℂ} {g : Space → Fin 3 × Fin 3 → ℂ}
    (hR : ContDiff ℝ 2 fun y => reVec (x y)) (hI : ContDiff ℝ 2 fun y => imVec (x y))
    (dR : ∀ y, fderiv ℝ (fun y => reVec (x y)) y = reMat (g y))
    (dI : ∀ y, fderiv ℝ (fun y => imVec (x y)) y = imMat (g y))
    (hdiv : ∀ y, ∑ i : Fin 3, g y (i, i) = 0)
    (hgc : Continuous fun y => cnormSq (g y)) (fg : (∫⁻ y, ENNReal.ofReal (cnormSq (g y))) < ⊤)
    (hxc : Continuous fun y => cnormSq (x y))
    (fx : (∫⁻ y, ENNReal.ofReal (cnormSq (x y) / (1 + ‖y‖) ^ 2)) < ⊤) :
    Integrable (fun y => θ y * (cnormSq (g y) - cnormSq (curlOfGrad (g y)))) ∧
      Integrable (fun y => secondDerivQuad θ y (x y)) ∧
      (∫ y, θ y * (cnormSq (g y) - cnormSq (curlOfGrad (g y)))) = ∫ y, secondDerivQuad θ y (x y) := by
  have frR : ∀ y, matSq (reMat (g y)) ≤ cnormSq (g y) := fun y => by
    rw [← matNorm_re_im]; linarith [show 0 ≤ matSq (imMat (g y)) from Finset.sum_nonneg fun _ _ => sq_nonneg _]
  have frI : ∀ y, matSq (imMat (g y)) ≤ cnormSq (g y) := fun y => by
    rw [← matNorm_re_im]; linarith [show 0 ≤ matSq (reMat (g y)) from Finset.sum_nonneg fun _ _ => sq_nonneg _]
  have vR : ∀ y, ‖reVec (x y)‖ ^ 2 ≤ cnormSq (x y) := fun y => by
    rw [← vec_re_im]; linarith [sq_nonneg ‖imVec (x y)‖]
  have vI : ∀ y, ‖imVec (x y)‖ ^ 2 ≤ cnormSq (x y) := fun y => by
    rw [← vec_re_im]; linarith [sq_nonneg ‖reVec (x y)‖]
  have divR : ∀ y, divergenceAt (fun y => reVec (x y)) y = 0 := fun y => by
    simp only [divergenceAt, dR, reMat_apply]
    rw [← Complex.re_sum, hdiv y, Complex.zero_re]
  have divI : ∀ y, divergenceAt (fun y => imVec (x y)) y = 0 := fun y => by
    simp only [divergenceAt, dI, imMat_apply]
    rw [← Complex.im_sum, hdiv y, Complex.zero_im]
  obtain ⟨iR1, iR2, iR3, eR⟩ := real_field_identity hI4 hθ hb hR dR divR hgc fg frR hxc fx vR
  obtain ⟨iI1, iI2, iI3, eI⟩ := real_field_identity hI4 hθ hb hI dI divI hgc fg frI hxc fx vI
  have pw : (fun y => θ y * (cnormSq (g y) - cnormSq (curlOfGrad (g y)))) = fun y =>
      (θ y * matSq (reMat (g y)) - θ y * ‖curlVec (reMat (g y))‖ ^ 2)
        + (θ y * matSq (imMat (g y)) - θ y * ‖curlVec (imMat (g y))‖ ^ 2) := by
    funext y
    rw [← matNorm_re_im, ← curl_re_im]
    ring
  have pq : (fun y => secondDerivQuad θ y (x y)) = fun y =>
      (∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ (fun x => fderiv ℝ θ x) y (unitVector i) (unitVector j) *
        reVec (x y) i * reVec (x y) j)
      + ∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ (fun x => fderiv ℝ θ x) y (unitVector i) (unitVector j) *
        imVec (x y) i * imVec (x y) j := by
    funext y
    exact secondDerivQuad_re_im θ y (x y)
  refine ⟨?_, ?_, ?_⟩
  · rw [pw]; exact (iR1.sub iR2).add (iI1.sub iI2)
  · rw [pq]; exact iR3.add iI3
  · rw [pw, pq]
    have h1 := integral_add (iR1.sub iR2) (iI1.sub iI2)
    have h2 := integral_add iR3 iI3
    simp only [Pi.sub_apply] at h1 h2
    rw [h1, h2, integral_sub iR1 iR2, integral_sub iI1 iI2, eR, eI]

theorem rot_trace (K : Space →L[ℝ] Space) (φ : ℝ) :
    ∑ i : Fin 3, axialRot (-φ) (K (axialRot φ (unitVector i))) i = ∑ i : Fin 3, K (unitVector i) i := by
  have hs := Real.sin_sq_add_cos_sq φ
  simp only [Fin.sum_univ_three, axialRot_unit_zero, axialRot_unit_one, axialRot_unit_two, map_add, map_smul,
    axialRot_coord_zero, axialRot_coord_one, axialRot_coord_two, Real.cos_neg, Real.sin_neg,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  linear_combination (K (unitVector 0) 0 + K (unitVector 1) 1) * hs

theorem smooth_modeSecondDeriv_symm {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) (m j l : Fin 3) :
    modeSecondDeriv ι (secondDerivField v) σ y (m, j, l) = modeSecondDeriv ι (secondDerivField v) σ y (m, l, j) := by
  unfold modeSecondDeriv modeAverage
  congr 1
  refine intervalIntegral.integral_congr fun τ _ => intervalIntegral.integral_congr fun φ _ => ?_
  simp only [secondDerivField]
  rw [(smooth_slice_smooth hv (σ + τ)).2.2]

theorem smooth_mode_trace {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    (∑ i : Fin 3, modeGrad ι (gradField v) σ y (i, i) = 0) ∧
      ∀ l : Fin 3, ∑ i : Fin 3, modeSecondDeriv ι (secondDerivField v) σ y (i, i, l) = 0 := by
  obtain ⟨-, c1, c2⟩ := smooth_fields_continuous hv
  have hs : Continuous fun q : ℝ × ℝ => σ + q.1 := by fun_prop
  have hy : Continuous fun q : ℝ × ℝ => axialRot q.2 y :=
    continuous_axialRot_of (by fun_prop : Continuous fun q : ℝ × ℝ => q.2) continuous_const
  have he : ∀ j : Fin 3, Continuous fun q : ℝ × ℝ => axialRot q.2 (unitVector j) := fun j =>
    continuous_axialRot_of (by fun_prop : Continuous fun q : ℝ × ℝ => q.2) continuous_const
  have hn : Continuous fun q : ℝ × ℝ => -q.2 := by fun_prop
  constructor
  · have hg : ∀ i : Fin 3, Continuous fun q : ℝ × ℝ =>
        axialRot (-q.2) (gradField v (σ + q.1) (axialRot q.2 y) (axialRot q.2 (unitVector i))) i :=
      fun i => (PiLp.continuous_apply 2 _ i).comp (continuous_axialRot_of hn
        ((c1.comp (hs.prodMk hy)).clm_apply (he i)))
    have e := modeAverage_finset_sum ι (Finset.univ : Finset (Fin 3)) (fun _ => 1)
      (fun i τ φ => axialRot (-φ) (gradField v (σ + τ) (axialRot φ y) (axialRot φ (unitVector i))) i) hg
      (0 : Fin 3)
    simp only [one_mul, Complex.ofReal_one] at e
    have h0 : ∀ τ φ, ∑ i : Fin 3, axialRot (-φ) (gradField v (σ + τ) (axialRot φ y)
        (axialRot φ (unitVector i))) i = 0 := fun τ φ => by
      rw [rot_trace]
      exact hv.divergence_free (σ + τ) (axialRot φ y)
    simp only [h0] at e
    rw [modeAverage_eq_zero ι (fun _ _ _ => (0 : ℝ)) _ (fun _ _ => rfl)] at e
    unfold modeGrad
    unfold modeAverage at e ⊢
    exact e.symm
  · intro l
    have hg : ∀ i : Fin 3, Continuous fun q : ℝ × ℝ =>
        axialRot (-q.2) (secondDerivField v (σ + q.1) (axialRot q.2 y) (axialRot q.2 (unitVector i))
          (axialRot q.2 (unitVector l))) i :=
      fun i => (PiLp.continuous_apply 2 _ i).comp (continuous_axialRot_of hn
        (((c2.comp (hs.prodMk hy)).clm_apply (he i)).clm_apply (he l)))
    have e := modeAverage_finset_sum ι (Finset.univ : Finset (Fin 3)) (fun _ => 1)
      (fun i τ φ => axialRot (-φ) (secondDerivField v (σ + τ) (axialRot φ y) (axialRot φ (unitVector i))
        (axialRot φ (unitVector l))) i) hg ((0 : Fin 3), (0 : Fin 3), l)
    simp only [one_mul, Complex.ofReal_one] at e
    have h0 : ∀ τ φ, ∑ i : Fin 3, axialRot (-φ) (secondDerivField v (σ + τ) (axialRot φ y)
        (axialRot φ (unitVector i)) (axialRot φ (unitVector l))) i = 0 := fun τ φ => by
      have := rot_trace ((secondDerivField v (σ + τ) (axialRot φ y)).flip (axialRot φ (unitVector l))) φ
      simp only [ContinuousLinearMap.flip_apply] at this
      rw [this]
      have hsym := (smooth_slice_smooth hv (σ + τ)).2.2 (axialRot φ y)
      have hz := smooth_divergence_deriv_zero hv (σ + τ) (axialRot φ y) (axialRot φ (unitVector l))
      simp only [secondDerivField]
      rw [← hz]
      exact Finset.sum_congr rfl fun i _ => by rw [hsym]
    simp only [h0] at e
    rw [modeAverage_eq_zero ι (fun _ _ _ => (0 : ℝ)) _ (fun _ _ => rfl)] at e
    unfold modeSecondDeriv
    unfold modeAverage at e ⊢
    exact e.symm

theorem param_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Space → ℝ → E}
    {F' : Space → ℝ → Space →L[ℝ] E} (a b : ℝ) (hF : Continuous fun p : Space × ℝ => F p.1 p.2)
    (hF' : Continuous fun p : Space × ℝ => F' p.1 p.2) (hd : ∀ y t, HasFDerivAt (fun y => F y t) (F' y t) y)
    (y₀ : Space) : HasFDerivAt (fun y => ∫ t in a..b, F y t) (∫ t in a..b, F' y₀ t) y₀ := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall y₀ 1).prod (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn
    hF'.continuousOn
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds y₀ one_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · exact Filter.Eventually.of_forall fun y => (hF.comp (Continuous.prodMk_right y)).aestronglyMeasurable
  · exact (hF.comp (Continuous.prodMk_right y₀)).intervalIntegrable _ _
  · exact (hF'.comp (Continuous.prodMk_right y₀)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t ht y hy => hC (y, t) ⟨hy, Set.uIoc_subset_uIcc ht⟩
  · exact Filter.Eventually.of_forall fun t _ y _ => hd y t

def doubleIntegral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Space → ℝ → ℝ → E) (y : Space) : E :=
  ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), F y τ φ

theorem doubleIntegral_continuous {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Space → ℝ → ℝ → E}
    (hF : Continuous fun p : Space × ℝ × ℝ => F p.1 p.2.1 p.2.2) : Continuous (doubleIntegral F) := by
  unfold doubleIntegral
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun y τ => ∫ φ in (0 : ℝ)..(2 * Real.pi), F y τ φ) ?_ 0 1
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (q : Space × ℝ) φ => F q.1 q.2 φ)
    (hF.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))) 0 (2 * Real.pi)

theorem doubleIntegral_hasFDerivAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Space → ℝ → ℝ → E}
    {F' : Space → ℝ → ℝ → Space →L[ℝ] E}
    (hF : Continuous fun p : Space × ℝ × ℝ => F p.1 p.2.1 p.2.2)
    (hF' : Continuous fun p : Space × ℝ × ℝ => F' p.1 p.2.1 p.2.2)
    (hd : ∀ y τ φ, HasFDerivAt (fun y => F y τ φ) (F' y τ φ) y) (y₀ : Space) :
    HasFDerivAt (doubleIntegral F) (doubleIntegral F' y₀) y₀ := by
  have inner : ∀ τ y, HasFDerivAt (fun y => ∫ φ in (0 : ℝ)..(2 * Real.pi), F y τ φ)
      (∫ φ in (0 : ℝ)..(2 * Real.pi), F' y τ φ) y := fun τ y =>
    param_hasFDerivAt (F := fun y φ => F y τ φ) (F' := fun y φ => F' y τ φ) 0 (2 * Real.pi)
      (hF.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)))
      (hF'.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))) (fun y φ => hd y τ φ) y
  exact param_hasFDerivAt (F := fun y τ => ∫ φ in (0 : ℝ)..(2 * Real.pi), F y τ φ)
    (F' := fun y τ => ∫ φ in (0 : ℝ)..(2 * Real.pi), F' y τ φ) 0 1
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (q : Space × ℝ) φ => F q.1 q.2 φ)
      (hF.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))) 0 (2 * Real.pi))
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (q : Space × ℝ) φ => F' q.1 q.2 φ)
      (hF'.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))) 0 (2 * Real.pi))
    (fun y τ => inner τ y) y₀

theorem doubleIntegral_contDiff (n : ℕ) : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Space → ℝ → ℝ → E},
    ContDiff ℝ ∞ (fun p : Space × ℝ × ℝ => F p.1 p.2.1 p.2.2) → ContDiff ℝ n (doubleIntegral F) := by
  induction n with
  | zero =>
    intro E _ _ F hF
    exact contDiff_zero.2 (doubleIntegral_continuous hF.continuous)
  | succ n ih =>
    intro E _ _ F hF
    set F' : Space → ℝ → ℝ → Space →L[ℝ] E := fun y τ φ => fderiv ℝ (fun x => F x τ φ) y with hF'def
    have hF'c : ContDiff ℝ ∞ (fun p : Space × ℝ × ℝ => F' p.1 p.2.1 p.2.2) := by
      have := ContDiff.fderiv (f := fun (p : Space × ℝ × ℝ) (x : Space) => F x p.2.1 p.2.2) (g := fun p => p.1)
        (m := ∞) (hF.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst
        (by rw [← WithTop.coe_one, ← WithTop.coe_add, top_add])
      exact this
    have hd : ∀ y τ φ, HasFDerivAt (fun y => F y τ φ) (F' y τ φ) y := by
      intro y τ φ
      have hdf : Differentiable ℝ (fun x => F x τ φ) :=
        (hF.comp (contDiff_id.prodMk (contDiff_const (c := ((τ, φ) : ℝ × ℝ))))).differentiable (by simp)
      exact (hdf y).hasFDerivAt
    have hD : ∀ y, HasFDerivAt (doubleIntegral F) (doubleIntegral F' y) y :=
      doubleIntegral_hasFDerivAt hF.continuous hF'c.continuous hd
    have hfd : fderiv ℝ (doubleIntegral F) = doubleIntegral F' := funext fun y => (hD y).fderiv
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl, contDiff_succ_iff_fderiv]
    refine ⟨fun y => (hD y).differentiableAt, by simp, ?_⟩
    rw [hfd]
    exact ih hF'c


def rotPlane : Space →L[ℝ] Space :=
  (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 0)
    + (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 1)

def rotTurn : Space →L[ℝ] Space :=
  -(EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 0)
    + (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 1)

def rotAxis : Space →L[ℝ] Space := (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 2)

def rotMap (φ : ℝ) : Space →L[ℝ] Space := Real.cos φ • rotPlane + Real.sin φ • rotTurn + rotAxis

theorem rotMap_apply (φ : ℝ) (y : Space) : rotMap φ y = axialRot φ y := by
  apply space_eq_of_coords <;>
    simp [rotMap, rotPlane, rotTurn, rotAxis, axialRot_coord_zero, axialRot_coord_one, axialRot_coord_two, unitVector] <;> ring

theorem rotMap_contDiff : ContDiff ℝ ∞ rotMap := by
  unfold rotMap
  exact ((Real.contDiff_cos.smul contDiff_const).add (Real.contDiff_sin.smul contDiff_const)).add contDiff_const

theorem doubleIntegral_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : Space → ℝ → ℝ → Space →L[ℝ] E}
    (hG : Continuous fun p : Space × ℝ × ℝ => G p.1 p.2.1 p.2.2) (y a : Space) :
    doubleIntegral G y a = doubleIntegral (fun y τ φ => G y τ φ a) y := by
  unfold doubleIntegral
  have hin : Continuous fun τ => ∫ φ in (0 : ℝ)..(2 * Real.pi), G y τ φ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun τ φ => G y τ φ)
      (hG.comp (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))) 0 (2 * Real.pi)
  rw [ContinuousLinearMap.intervalIntegral_apply (hin.intervalIntegrable 0 1)]
  refine intervalIntegral.integral_congr fun τ _ => ?_
  exact ContinuousLinearMap.intervalIntegral_apply
    ((hG.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))).intervalIntegrable _ _) a

theorem mode_field (ι : ℤ × ℤ) {f : ℝ → ℝ → Space → Space}
    (hf : ContDiff ℝ ∞ fun p : ℝ × ℝ × Space => f p.1 p.2.1 p.2.2) :
    (ContDiff ℝ 2 fun y => reVec (fun i => modeAverage ι
        (fun τ φ (i : Fin 3) => axialRot (-φ) (f τ φ (axialRot φ y)) i) i)) ∧
      (ContDiff ℝ 2 fun y => imVec (fun i => modeAverage ι
        (fun τ φ (i : Fin 3) => axialRot (-φ) (f τ φ (axialRot φ y)) i) i)) ∧
      (∀ y, fderiv ℝ (fun y => reVec (fun i => modeAverage ι
        (fun τ φ (i : Fin 3) => axialRot (-φ) (f τ φ (axialRot φ y)) i) i)) y =
          reMat (fun ij => modeAverage ι (fun τ φ (ij : Fin 3 × Fin 3) =>
            axialRot (-φ) (fderiv ℝ (f τ φ) (axialRot φ y) (axialRot φ (unitVector ij.2))) ij.1) ij)) ∧
      (∀ y, fderiv ℝ (fun y => imVec (fun i => modeAverage ι
        (fun τ φ (i : Fin 3) => axialRot (-φ) (f τ φ (axialRot φ y)) i) i)) y =
          imMat (fun ij => modeAverage ι (fun τ φ (ij : Fin 3 × Fin 3) =>
            axialRot (-φ) (fderiv ℝ (f τ φ) (axialRot φ y) (axialRot φ (unitVector ij.2))) ij.1) ij)) := by
  set ex : ℝ → ℝ → ℂ := fun τ φ => Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
    with hex
  set Fc : Fin 3 → Space → ℝ → ℝ → ℂ := fun i y τ φ =>
    ex τ φ * ((rotMap (-φ) (f τ φ (rotMap φ y)) i : ℝ) : ℂ) with hFc
  set Fd : Fin 3 → Space → ℝ → ℝ → Space →L[ℝ] ℂ := fun i y τ φ =>
    ex τ φ • (Complex.ofRealCLM.comp ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp ((rotMap (-φ)).comp
      ((fderiv ℝ (f τ φ) (rotMap φ y)).comp (rotMap φ))))) with hFd
  set mA : Space → Fin 3 → ℂ := fun y i => modeAverage ι
    (fun τ φ (i : Fin 3) => axialRot (-φ) (f τ φ (axialRot φ y)) i) i with hmA
  have hx : ∀ y i, mA y i = (1 / (2 * Real.pi) : ℂ) * doubleIntegral (Fc i) y := by
    intro y i
    simp only [hmA, modeAverage, doubleIntegral, hFc, hex, rotMap_apply]
  have hexc : ContDiff ℝ ∞ fun p : ℝ × ℝ => ex p.1 p.2 := by
    simp only [hex]
    exact Complex.contDiff_exp.comp (((Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_fst).add (contDiff_const.mul contDiff_snd))).mul contDiff_const).neg)
  have hrot : ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {a : X → ℝ} {u : X → Space},
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ u → ContDiff ℝ ∞ fun q => rotMap (a q) (u q) :=
    fun ha hu => (rotMap_contDiff.comp ha).clm_apply hu
  have hsm : ∀ i, ContDiff ℝ ∞ (fun p : Space × ℝ × ℝ => Fc i p.1 p.2.1 p.2.2) := by
    intro i
    have h1 : ContDiff ℝ ∞ fun p : Space × ℝ × ℝ => rotMap p.2.2 p.1 := hrot contDiff_snd.snd contDiff_fst
    have h2 : ContDiff ℝ ∞ fun p : Space × ℝ × ℝ => f p.2.1 p.2.2 (rotMap p.2.2 p.1) :=
      hf.comp (contDiff_snd.fst.prodMk (contDiff_snd.snd.prodMk h1))
    have h3 : ContDiff ℝ ∞ fun p : Space × ℝ × ℝ => rotMap (-p.2.2) (f p.2.1 p.2.2 (rotMap p.2.2 p.1)) :=
      hrot contDiff_snd.snd.neg h2
    have h4 : ContDiff ℝ ∞ fun p : Space × ℝ × ℝ => rotMap (-p.2.2) (f p.2.1 p.2.2 (rotMap p.2.2 p.1)) i :=
      (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp h3
    exact (hexc.comp contDiff_snd).mul (Complex.ofRealCLM.contDiff.comp h4)
  have hDf : ContDiff ℝ ∞ fun p : ℝ × ℝ × Space => fderiv ℝ (f p.1 p.2.1) p.2.2 :=
    ContDiff.fderiv (f := fun (p : ℝ × ℝ × Space) (z : Space) => f p.1 p.2.1 z) (g := fun p => p.2.2)
      (hf.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk contDiff_snd))) contDiff_snd.snd
      (by rw [← WithTop.coe_one, ← WithTop.coe_add, top_add])
  have hFdc : ∀ i, Continuous (fun p : Space × ℝ × ℝ => Fd i p.1 p.2.1 p.2.2) := by
    intro i
    have c1 : Continuous fun p : Space × ℝ × ℝ => fderiv ℝ (f p.2.1 p.2.2) (rotMap p.2.2 p.1) :=
      hDf.continuous.comp (continuous_snd.fst.prodMk (continuous_snd.snd.prodMk
        (hrot contDiff_snd.snd contDiff_fst).continuous))
    have c2 : Continuous fun p : Space × ℝ × ℝ => rotMap p.2.2 := rotMap_contDiff.continuous.comp continuous_snd.snd
    have c3 : Continuous fun p : Space × ℝ × ℝ => rotMap (-p.2.2) :=
      rotMap_contDiff.continuous.comp continuous_snd.snd.neg
    exact ((hexc.continuous.comp continuous_snd)).smul (continuous_const.clm_comp (continuous_const.clm_comp
      (c3.clm_comp (c1.clm_comp c2))))
  have hd : ∀ i y τ φ, HasFDerivAt (fun y => Fc i y τ φ) (Fd i y τ φ) y := by
    intro i y τ φ
    have hfd : DifferentiableAt ℝ (f τ φ) (rotMap φ y) :=
      ((hf.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))).differentiable (by simp)) _
    have h3 := hfd.hasFDerivAt.comp y (rotMap φ).hasFDerivAt
    have h4 := (rotMap (-φ)).hasFDerivAt.comp y h3
    have h5 := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y h4
    have h6 := Complex.ofRealCLM.hasFDerivAt.comp y h5
    have h7 := h6.const_mul (ex τ φ)
    simpa [hFc, hFd, Function.comp_def] using h7
  have hcd : ∀ i, ContDiff ℝ 2 (fun y => mA y i) := by
    intro i
    have e : (fun y => mA y i) = fun y => (1 / (2 * Real.pi) : ℂ) * doubleIntegral (Fc i) y := funext fun y => hx y i
    rw [e]
    exact contDiff_const.mul (by simpa using doubleIntegral_contDiff 2 (hsm i))
  have hhd : ∀ i y, HasFDerivAt (fun y => mA y i) ((1 / (2 * Real.pi) : ℂ) • doubleIntegral (Fd i) y) y := by
    intro i y
    have e : (fun y => mA y i) = fun y => (1 / (2 * Real.pi) : ℂ) * doubleIntegral (Fc i) y := funext fun y => hx y i
    rw [e]
    exact (doubleIntegral_hasFDerivAt (hsm i).continuous (hFdc i) (hd i) y).const_mul _
  have happ : ∀ i y j, ((1 / (2 * Real.pi) : ℂ) • doubleIntegral (Fd i) y) (unitVector j) =
      modeAverage ι (fun τ φ (ij : Fin 3 × Fin 3) =>
        axialRot (-φ) (fderiv ℝ (f τ φ) (axialRot φ y) (axialRot φ (unitVector ij.2))) ij.1) (i, j) := by
    intro i y j
    rw [ContinuousLinearMap.smul_apply, doubleIntegral_apply (hFdc i)]
    simp only [modeAverage, doubleIntegral, hFd, hex, rotMap_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
    rfl
  have hreC : ContDiff ℝ 2 fun y => reVec (mA y) := by
    unfold reVec
    exact ContDiff.sum fun i _ => (Complex.reCLM.contDiff.comp (hcd i)).smul contDiff_const
  have himC : ContDiff ℝ 2 fun y => imVec (mA y) := by
    unfold imVec
    exact ContDiff.sum fun i _ => (Complex.imCLM.contDiff.comp (hcd i)).smul contDiff_const
  have hRd : ∀ y, HasFDerivAt (fun y => reVec (mA y)) (∑ i : Fin 3,
      (Complex.reCLM.comp ((1 / (2 * Real.pi) : ℂ) • doubleIntegral (Fd i) y)).smulRight (unitVector i)) y := by
    intro y
    unfold reVec
    exact HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => (Complex.reCLM.hasFDerivAt.comp y (hhd i y)).smul_const (unitVector i)
  have hId : ∀ y, HasFDerivAt (fun y => imVec (mA y)) (∑ i : Fin 3,
      (Complex.imCLM.comp ((1 / (2 * Real.pi) : ℂ) • doubleIntegral (Fd i) y)).smulRight (unitVector i)) y := by
    intro y
    unfold imVec
    exact HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => (Complex.imCLM.hasFDerivAt.comp y (hhd i y)).smul_const (unitVector i)
  have ext_unit : ∀ {A B : Space →L[ℝ] Space}, (∀ j, A (unitVector j) = B (unitVector j)) → A = B := by
    intro A B h
    exact ContinuousLinearMap.coe_injective ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext fun j => by
      simpa [EuclideanSpace.basisFun_apply, unitVector] using h j)
  have reMat_unit : ∀ (g : Fin 3 × Fin 3 → ℂ) j, reMat g (unitVector j) = reVec (fun i => g (i, j)) := by
    intro g j
    ext l
    rw [reMat_apply, reVec_apply]
  have imMat_unit : ∀ (g : Fin 3 × Fin 3 → ℂ) j, imMat g (unitVector j) = imVec (fun i => g (i, j)) := by
    intro g j
    ext l
    rw [imMat_apply, imVec_apply]
  refine ⟨hreC, himC, fun y => ?_, fun y => ?_⟩
  · rw [(hRd y).fderiv]
    refine ext_unit fun j => ?_
    rw [reMat_unit]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      happ, Complex.reCLM_apply, reVec]
  · rw [(hId y).fderiv]
    refine ext_unit fun j => ?_
    rw [imMat_unit]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      happ, Complex.imCLM_apply, imVec]

theorem smooth_mode_derivatives {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    (ι : ℤ × ℤ) (σ : ℝ) :
    (ContDiff ℝ 2 fun y => reVec (modeVel ι v σ y)) ∧ (ContDiff ℝ 2 fun y => imVec (modeVel ι v σ y)) ∧
      (∀ y, fderiv ℝ (fun y => reVec (modeVel ι v σ y)) y = reMat (modeGrad ι (gradField v) σ y)) ∧
      (∀ y, fderiv ℝ (fun y => imVec (modeVel ι v σ y)) y = imMat (modeGrad ι (gradField v) σ y)) ∧
      (∀ l : Fin 3, (ContDiff ℝ 2 fun y => reVec (fun i => modeGrad ι (gradField v) σ y (i, l))) ∧
        (ContDiff ℝ 2 fun y => imVec (fun i => modeGrad ι (gradField v) σ y (i, l))) ∧
        (∀ y, fderiv ℝ (fun y => reVec (fun i => modeGrad ι (gradField v) σ y (i, l))) y =
          reMat (fun mj => modeSecondDeriv ι (secondDerivField v) σ y (mj.1, mj.2, l))) ∧
        (∀ y, fderiv ℝ (fun y => imVec (fun i => modeGrad ι (gradField v) σ y (i, l))) y =
          imMat (fun mj => modeSecondDeriv ι (secondDerivField v) σ y (mj.1, mj.2, l)))) := by
  have hfv : ContDiff ℝ ∞ fun p : ℝ × ℝ × Space => v (σ + p.1) p.2.2 :=
    hv.smooth.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd.snd)
  obtain ⟨a1, a2, a3, a4⟩ := mode_field ι (f := fun τ _ => v (σ + τ)) hfv
  refine ⟨a1, a2, a3, a4, fun l => ?_⟩
  have hDv : ContDiff ℝ ∞ fun p : ℝ × ℝ × Space => fderiv ℝ (v (σ + p.1)) p.2.2 :=
    ContDiff.fderiv (f := fun (p : ℝ × ℝ × Space) (z : Space) => v (σ + p.1) z) (g := fun p => p.2.2)
      (hv.smooth.comp ((contDiff_const.add contDiff_fst.fst).prodMk contDiff_snd)) contDiff_snd.snd
      (by rw [← WithTop.coe_one, ← WithTop.coe_add, top_add])
  have hfl : ContDiff ℝ ∞ fun p : ℝ × ℝ × Space =>
      (fun (τ φ : ℝ) (z : Space) => fderiv ℝ (v (σ + τ)) z (axialRot φ (unitVector l))) p.1 p.2.1 p.2.2 := by
    have e : (fun p : ℝ × ℝ × Space => fderiv ℝ (v (σ + p.1)) p.2.2 (axialRot p.2.1 (unitVector l))) =
        fun p => fderiv ℝ (v (σ + p.1)) p.2.2 (rotMap p.2.1 (unitVector l)) := by
      funext p; rw [rotMap_apply]
    show ContDiff ℝ ∞ fun p : ℝ × ℝ × Space => fderiv ℝ (v (σ + p.1)) p.2.2 (axialRot p.2.1 (unitVector l))
    rw [e]
    exact hDv.clm_apply ((rotMap_contDiff.comp contDiff_snd.fst).clm_apply contDiff_const)
  obtain ⟨b1, b2, b3, b4⟩ := mode_field ι
    (f := fun (τ φ : ℝ) (z : Space) => fderiv ℝ (v (σ + τ)) z (axialRot φ (unitVector l))) hfl
  have hcol' : ∀ s z a b, fderiv ℝ (fun x => fderiv ℝ (v s) x b) z a = fderiv ℝ (fderiv ℝ (v s)) z a b := by
    intro s z a b
    obtain ⟨-, hDf, -⟩ := smooth_slice_smooth hv s
    rw [fderiv_clm_apply ((hDf.differentiable (by simp)) z) (differentiableAt_const _)]
    simp
  have hg : ∀ y, (fun ij : Fin 3 × Fin 3 => modeAverage ι (fun τ φ (ij : Fin 3 × Fin 3) =>
      axialRot (-φ) (fderiv ℝ (fun z => fderiv ℝ (v (σ + τ)) z (axialRot φ (unitVector l))) (axialRot φ y)
        (axialRot φ (unitVector ij.2))) ij.1) ij) =
      fun mj => modeSecondDeriv ι (secondDerivField v) σ y (mj.1, mj.2, l) := by
    intro y
    funext mj
    unfold modeSecondDeriv modeAverage
    congr 1
    refine intervalIntegral.integral_congr fun τ _ => intervalIntegral.integral_congr fun φ _ => ?_
    simp only [secondDerivField]
    rw [hcol']
  refine ⟨b1, b2, fun y => ?_, fun y => ?_⟩
  · rw [← hg y]; exact b3 y
  · rw [← hg y]; exact b4 y

theorem smooth_mode_calculus {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    (ι : ℤ × ℤ) (σ : ℝ) :
    (ContDiff ℝ 2 fun y => reVec (modeVel ι v σ y)) ∧ (ContDiff ℝ 2 fun y => imVec (modeVel ι v σ y)) ∧
      (∀ y, fderiv ℝ (fun y => reVec (modeVel ι v σ y)) y = reMat (modeGrad ι (gradField v) σ y)) ∧
      (∀ y, fderiv ℝ (fun y => imVec (modeVel ι v σ y)) y = imMat (modeGrad ι (gradField v) σ y)) ∧
      (∀ l : Fin 3, (ContDiff ℝ 2 fun y => reVec (fun i => modeGrad ι (gradField v) σ y (i, l))) ∧
        (ContDiff ℝ 2 fun y => imVec (fun i => modeGrad ι (gradField v) σ y (i, l))) ∧
        (∀ y, fderiv ℝ (fun y => reVec (fun i => modeGrad ι (gradField v) σ y (i, l))) y =
          reMat (fun mj => modeSecondDeriv ι (secondDerivField v) σ y (mj.1, mj.2, l))) ∧
        (∀ y, fderiv ℝ (fun y => imVec (fun i => modeGrad ι (gradField v) σ y (i, l))) y =
          imMat (fun mj => modeSecondDeriv ι (secondDerivField v) σ y (mj.1, mj.2, l)))) ∧
      (∀ y, ∑ i : Fin 3, modeGrad ι (gradField v) σ y (i, i) = 0) ∧
      (∀ y (l : Fin 3), ∑ i : Fin 3, modeSecondDeriv ι (secondDerivField v) σ y (i, i, l) = 0) ∧
      ∀ y (m j l : Fin 3), modeSecondDeriv ι (secondDerivField v) σ y (m, j, l) = modeSecondDeriv ι (secondDerivField v) σ y (m, l, j) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := smooth_mode_derivatives hv ι σ
  exact ⟨a1, a2, a3, a4, a5, fun y => (smooth_mode_trace hv ι σ y).1, fun y l => (smooth_mode_trace hv ι σ y).2 l,
    fun y m j l => smooth_modeSecondDeriv_symm hv ι σ y m j l⟩

theorem column_cnormSq_le (h : Fin 3 × Fin 3 × Fin 3 → ℂ) (l : Fin 3) :
    cnormSq (fun mj : Fin 3 × Fin 3 => h (mj.1, mj.2, l)) ≤ cnormSq h := by
  simp only [cnormSq, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun j _ => ?_
  exact Finset.single_le_sum (f := fun l' => ‖h (m, j, l')‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ l)

theorem column_cnormSq_le' (g : Fin 3 × Fin 3 → ℂ) (l : Fin 3) :
    cnormSq (fun i : Fin 3 => g (i, l)) ≤ cnormSq g := by
  simp only [cnormSq, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Finset.single_le_sum (f := fun l' => ‖g (i, l')‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ l)

theorem smooth_mode_weight_identity (hP : ModeSquareSumHolds) (hI4 : CurlWeightIdentityDecayHolds)
    {θ : Space → ℝ} (hθ : ContDiff ℝ 2 θ)
    (hθb : ∃ B, ∀ y, ∀ j ≤ 2, (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j θ y‖ ≤ B)
    {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      (∫ y, θ y * (secondDerivModeSq v ι σ y - vortGradSq v ι σ y)) =
          ∫ y, ∑ l : Fin 3, secondDerivQuad θ y (fun i => modeGrad ι (gradField v) σ y (i, l)) ∧
        (∫ y, θ y * (gradSq v ι σ y - vortSq v ι σ y)) = ∫ y, secondDerivQuad θ y (modeVel ι v σ y) := by
  obtain ⟨Bθ, hb⟩ := hθb
  obtain ⟨m0, m1, m2⟩ := smooth_modes_continuous hv ι
  filter_upwards [smooth_mode_slices hP hI4 hv ι] with σ hs
  obtain ⟨s0, s1, -, s3, -⟩ := hs
  obtain ⟨cR, cI, dR, dI, hcol, hdiv, hdivc, hsym⟩ := smooth_mode_calculus hv ι σ
  have kV : Continuous fun y => modeVel ι v σ y := by
    simpa only [Function.comp_def] using m0.comp (Continuous.prodMk_right σ)
  have kG : Continuous fun y => modeGrad ι (gradField v) σ y := by
    simpa only [Function.comp_def] using m1.comp (Continuous.prodMk_right σ)
  have kH : Continuous fun y => modeSecondDeriv ι (secondDerivField v) σ y := by
    simpa only [Function.comp_def] using m2.comp (Continuous.prodMk_right σ)
  have hpos : ∀ y : Space, 0 < (1 + ‖y‖) ^ 2 := fun y => by positivity
  obtain ⟨-, -, e2⟩ := complex_field_identity hI4 hθ hb cR cI dR dI hdiv (continuous_cnormSq kG) s1
    (continuous_cnormSq kV) s0
  have col : ∀ l : Fin 3, _ := fun l => complex_field_identity hI4 hθ hb (hcol l).1 (hcol l).2.1 (hcol l).2.2.1
    (hcol l).2.2.2 (fun y => hdivc y l)
    (continuous_cnormSq (continuous_pi fun mj => (continuous_apply (mj.1, mj.2, l)).comp kH))
    (slice_finite_of_le (K := 1) zero_le_one (fun y => by rw [one_mul]; exact column_cnormSq_le _ l) s3)
    (continuous_cnormSq (continuous_pi fun i => (continuous_apply (i, l)).comp kG))
    (slice_finite_of_le (K := 1) zero_le_one (fun y => by
      rw [one_mul]
      exact (weight_div_le _ y (cnormSq_nonneg _)).trans (column_cnormSq_le' _ l)) s1)
  refine ⟨?_, e2⟩
  have p1 : ∀ y, θ y * (secondDerivModeSq v ι σ y - vortGradSq v ι σ y) = ∑ l : Fin 3,
      θ y * (cnormSq (fun mj : Fin 3 × Fin 3 => modeSecondDeriv ι (secondDerivField v) σ y (mj.1, mj.2, l))
        - cnormSq (curlOfGrad (fun mj : Fin 3 × Fin 3 => modeSecondDeriv ι (secondDerivField v) σ y (mj.1, mj.2, l)))) := by
    intro y
    have hc : ∀ (i l : Fin 3), curlOfGrad (fun mj : Fin 3 × Fin 3 => modeSecondDeriv ι (secondDerivField v) σ y (mj.1, mj.2, l)) i
        = curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) σ y) (i, l) := by
      intro i l
      simp only [curlOfGrad, curlGradOfSecondDeriv]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => by rw [hsym y m j l]
    have a1 : secondDerivModeSq v ι σ y = ∑ l : Fin 3,
        cnormSq (fun mj : Fin 3 × Fin 3 => modeSecondDeriv ι (secondDerivField v) σ y (mj.1, mj.2, l)) := by
      simp only [secondDerivModeSq, cnormSq, Fintype.sum_prod_type, Fin.sum_univ_three]
      ring
    have a2 : vortGradSq v ι σ y = ∑ l : Fin 3,
        cnormSq (curlOfGrad (fun mj : Fin 3 × Fin 3 => modeSecondDeriv ι (secondDerivField v) σ y (mj.1, mj.2, l))) := by
      simp only [vortGradSq, cnormSq, hc, Fintype.sum_prod_type]
      exact Finset.sum_comm
    rw [a1, a2, ← Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [p1]
  rw [integral_finsetSum _ fun l _ => (col l).1, integral_finsetSum _ fun l _ => (col l).2.1]
  exact Finset.sum_congr rfl fun l _ => (col l).2.2

theorem slice_curl_weight {θ : Space → ℝ} (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ)
    (e1 : (∫ y, θ y * (secondDerivModeSq v ι σ y - vortGradSq v ι σ y)) =
      ∫ y, ∑ l : Fin 3, secondDerivQuad θ y (fun i => modeGrad ι (gradField v) σ y (i, l)))
    (e2 : (∫ y, θ y * (gradSq v ι σ y - vortSq v ι σ y)) = ∫ y, secondDerivQuad θ y (modeVel ι v σ y))
    (i1 : Integrable fun y => θ y * (secondDerivModeSq v ι σ y - vortGradSq v ι σ y))
    (i2 : Integrable fun y => ModeWeights.secondDerivNorm θ y * gradSq v ι σ y)
    (i3 : Integrable fun y => θ y * (gradSq v ι σ y - vortSq v ι σ y))
    (i4 : Integrable fun y => ModeWeights.secondDerivNorm θ y * velSq v ι σ y) :
    (∫ y, secondDerivDefect θ v ι σ y) ≤ 0 ∧ (∫ y, gradDefect θ v ι σ y) ≤ 0 := by
  have hN : ∀ y, 0 ≤ ModeWeights.secondDerivNorm θ y := fun y => norm_nonneg _
  constructor
  · have p : ∀ y, ∑ l : Fin 3, secondDerivQuad θ y (fun i => modeGrad ι (gradField v) σ y (i, l))
        ≤ ModeWeights.secondDerivNorm θ y * gradSq v ι σ y := by
      intro y
      calc ∑ l : Fin 3, secondDerivQuad θ y (fun i => modeGrad ι (gradField v) σ y (i, l))
          ≤ ∑ l : Fin 3, ModeWeights.secondDerivNorm θ y * cnormSq (fun i => modeGrad ι (gradField v) σ y (i, l)) :=
            Finset.sum_le_sum fun l _ => secondDerivQuad_le θ y _
        _ = ModeWeights.secondDerivNorm θ y * gradSq v ι σ y := by
            rw [← Finset.mul_sum]
            congr 1
            simp only [gradSq, cnormSq, Fintype.sum_prod_type]
            exact Finset.sum_comm
    have hle := integral_le_of_pointwise i2 (fun y => mul_nonneg (hN y) (squares_nonneg v ι σ y).2.1) p
    have hs : ∫ y, secondDerivDefect θ v ι σ y =
        (∫ y, θ y * (secondDerivModeSq v ι σ y - vortGradSq v ι σ y))
          - ∫ y, ModeWeights.secondDerivNorm θ y * gradSq v ι σ y := integral_sub i1 i2
    linarith
  · have p : ∀ y, secondDerivQuad θ y (modeVel ι v σ y) ≤ ModeWeights.secondDerivNorm θ y * velSq v ι σ y :=
      fun y => secondDerivQuad_le θ y _
    have hle := integral_le_of_pointwise i4 (fun y => mul_nonneg (hN y) (squares_nonneg v ι σ y).1) p
    have hs : ∫ y, gradDefect θ v ι σ y =
        (∫ y, θ y * (gradSq v ι σ y - vortSq v ι σ y))
          - ∫ y, ModeWeights.secondDerivNorm θ y * velSq v ι σ y := integral_sub i3 i4
    linarith

theorem smooth_per_mode (hP : ModeSquareSumHolds) (hI4 : CurlWeightIdentityDecayHolds) {θD θZ : Space → ℝ}
    (hD : ContDiff ℝ 2 θD) (hZ : ContDiff ℝ 2 θZ)
    (hDb : ∃ B, ∀ y, ∀ j ≤ 2, ‖y‖ ^ j * ‖iteratedFDeriv ℝ j θD y‖ ≤ B)
    (hZb : ∃ B, ∀ y, ∀ j ≤ 2, (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j θZ y‖ ≤ B)
    (c : ℝ) {w : Space → ℝ} (hwm : Measurable w) (hw0 : ∀ y, 0 ≤ w y) {B : ℝ}
    (hB : ∀ y, w y ≤ B) (hwa : IsAxisymmetric w) {P : ℝ} {v : ℝ → Space → Space}
    (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      (∫⁻ y, ENNReal.ofReal (expanded θD θZ c w v ι σ y)) + ∫⁻ y, ENNReal.ofReal (mainNeg c w v ι σ y)
        ≤ (∫⁻ y, ENNReal.ofReal (mainPos c w v ι σ y))
          + ∫⁻ y, ENNReal.ofReal (-expanded θD θZ c w v ι σ y) := by
  obtain ⟨BD, hBD⟩ := weight_bound_one_add hD hDb
  obtain ⟨BZ, hBZ⟩ := hZb
  obtain ⟨c0, c1, c2, c3, c4⟩ := (fun h => ⟨continuous_cnormSq h.1, continuous_cnormSq h.2.1,
    continuous_cnormSq (continuous_curlOfGrad h.2.1), continuous_cnormSq h.2.2,
    continuous_cnormSq (continuous_curlGradOfSecondDeriv h.2.2)⟩ :
      (Continuous (fun z : ℝ × Space => modeVel ι v z.1 z.2) ∧
        Continuous (fun z : ℝ × Space => modeGrad ι (gradField v) z.1 z.2) ∧
        Continuous (fun z : ℝ × Space => modeSecondDeriv ι (secondDerivField v) z.1 z.2)) →
      Continuous (fun z : ℝ × Space => velSq v ι z.1 z.2) ∧
        Continuous (fun z : ℝ × Space => gradSq v ι z.1 z.2) ∧
        Continuous (fun z : ℝ × Space => vortSq v ι z.1 z.2) ∧
        Continuous (fun z : ℝ × Space => secondDerivModeSq v ι z.1 z.2) ∧
        Continuous (fun z : ℝ × Space => vortGradSq v ι z.1 z.2)) (smooth_modes_continuous hv ι)
  filter_upwards [smooth_mode_slices hP hI4 hv ι,
    smooth_mode_weight_identity hP hI4 hD ⟨BD, hBD⟩ hv ι,
    smooth_mode_weight_identity hP hI4 hZ ⟨BZ, hBZ⟩ hv ι] with σ hs hDe hZe
  obtain ⟨s0, s1, s2, s3, s4⟩ := hs
  have k0 : Continuous fun y => velSq v ι σ y := by
    simpa only [Function.comp_def] using c0.comp (Continuous.prodMk_right σ)
  have k1 : Continuous fun y => gradSq v ι σ y := by
    simpa only [Function.comp_def] using c1.comp (Continuous.prodMk_right σ)
  have k2 : Continuous fun y => vortSq v ι σ y := by
    simpa only [Function.comp_def] using c2.comp (Continuous.prodMk_right σ)
  have k3 : Continuous fun y => secondDerivModeSq v ι σ y := by
    simpa only [Function.comp_def] using c3.comp (Continuous.prodMk_right σ)
  have k4 : Continuous fun y => vortGradSq v ι σ y := by
    simpa only [Function.comp_def] using c4.comp (Continuous.prodMk_right σ)
  have nn := squares_nonneg v ι σ
  have hpos : ∀ y : Space, 0 < (1 + ‖y‖) ^ 2 := fun y => by positivity
  have iv : Integrable fun y => velSq v ι σ y / (1 + ‖y‖) ^ 2 :=
    integrable_of_lintegral (k0.div (by fun_prop) fun y => (hpos y).ne')
      (fun y => div_nonneg (nn y).1 (hpos y).le) s0
  have i1 : Integrable fun y => gradSq v ι σ y := integrable_of_lintegral k1 (fun y => (nn y).2.1) s1
  have i2 : Integrable fun y => vortSq v ι σ y := integrable_of_lintegral k2 (fun y => (nn y).2.2.1) s2
  have i3 : Integrable fun y => secondDerivModeSq v ι σ y :=
    integrable_of_lintegral k3 (fun y => (nn y).2.2.2.1) s3
  have i4 : Integrable fun y => vortGradSq v ι σ y :=
    integrable_of_lintegral k4 (fun y => (nn y).2.2.2.2) s4
  have defects : ∀ {θ : Space → ℝ} {Bθ : ℝ}, ContDiff ℝ 2 θ →
      (∀ y, ∀ j ≤ 2, (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j θ y‖ ≤ Bθ) →
      Integrable (fun y => θ y * (secondDerivModeSq v ι σ y - vortGradSq v ι σ y)) ∧
        Integrable (fun y => ModeWeights.secondDerivNorm θ y * gradSq v ι σ y) ∧
        Integrable (fun y => θ y * (gradSq v ι σ y - vortSq v ι σ y)) ∧
        Integrable (fun y => ModeWeights.secondDerivNorm θ y * velSq v ι σ y) := by
    intro θ Bθ hθ hb
    have wb := weight_value_bounds hb
    have hn0 : ∀ y, 0 ≤ ModeWeights.secondDerivNorm θ y := fun y => norm_nonneg _
    refine ⟨(i3.sub i4).bdd_mul (c := Bθ) hθ.continuous.aestronglyMeasurable
        (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact (wb y).1),
      i1.bdd_mul (c := Bθ) (continuous_secondDerivNorm hθ).aestronglyMeasurable
        (ae_of_all _ fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hn0 y)]; exact (wb y).2.2),
      (i1.sub i2).bdd_mul (c := Bθ) hθ.continuous.aestronglyMeasurable
        (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact (wb y).1), ?_⟩
    refine (iv.const_mul Bθ).mono' ((continuous_secondDerivNorm hθ).mul k0).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hn0 y) (nn y).1)]
    calc ModeWeights.secondDerivNorm θ y * velSq v ι σ y ≤ Bθ / (1 + ‖y‖) ^ 2 * velSq v ι σ y :=
          mul_le_mul_of_nonneg_right (wb y).2.1 (nn y).1
      _ = Bθ * (velSq v ι σ y / (1 + ‖y‖) ^ 2) := by ring
  obtain ⟨dD1, dD2, dD3, dD4⟩ := defects hD hBD
  obtain ⟨dZ1, dZ2, dZ3, dZ4⟩ := defects hZ hBZ
  have iw : Integrable fun y => w y * gradSq v ι σ y :=
    i1.bdd_mul (c := B) hwm.aestronglyMeasurable (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hw0 y)]; exact hB y)
  have iS : Integrable fun y => secondDerivModeSq v ι σ y + w y * gradSq v ι σ y := i3.add iw
  have iM : Integrable fun y => vortGradSq v ι σ y + 1 / 4 * vortSq v ι σ y :=
    i4.add (i2.const_mul (1 / 4))
  have iMain : Integrable (baseMain c w v ι σ) := iM.sub (iS.const_mul c)
  have iHD : Integrable (secondDerivDefect θD v ι σ) := dD1.sub dD2
  have iGD : Integrable (gradDefect θZ v ι σ) := dZ3.sub dZ4
  have iPos : Integrable (mainPos c w v ι σ) := iM.add (iS.const_mul _)
  have iNeg : Integrable (mainNeg c w v ι σ) := iS.const_mul _
  have hexp : expanded θD θZ c w v ι σ =
      fun y => baseMain c w v ι σ y + secondDerivDefect θD v ι σ y + gradDefect θZ v ι σ y := by
    funext y
    simp only [expanded, baseMain, secondDerivDefect, gradDefect]
    ring
  have hbm : baseMain c w v ι σ = fun y => mainPos c w v ι σ y - mainNeg c w v ι σ y := by
    funext y
    simp only [baseMain, mainPos, mainNeg]
    linear_combination (-(secondDerivModeSq v ι σ y + w y * gradSq v ι σ y)) *
      (max_zero_sub_max_neg_zero_eq_self c).symm
  have iExp : Integrable (expanded θD θZ c w v ι σ) := by
    rw [hexp]; exact (iMain.add iHD).add iGD
  obtain ⟨d1, -⟩ := slice_curl_weight v ι σ hDe.1 hDe.2 dD1 dD2 dD3 dD4
  obtain ⟨-, d2⟩ := slice_curl_weight v ι σ hZe.1 hZe.2 dZ1 dZ2 dZ3 dZ4
  refine ennreal_le_of_integral_le iExp iPos iNeg (fun y => ?_) (fun y => ?_) ?_
  · obtain ⟨n0, n1, n2, n3, n4⟩ := nn y
    exact add_nonneg (add_nonneg n4 (mul_nonneg (by norm_num) n2))
      (mul_nonneg (le_max_right _ _) (add_nonneg n3 (mul_nonneg (hw0 y) n1)))
  · obtain ⟨n0, n1, n2, n3, n4⟩ := nn y
    exact mul_nonneg (le_max_right _ _) (add_nonneg n3 (mul_nonneg (hw0 y) n1))
  · have e1 : ∫ y, expanded θD θZ c w v ι σ y =
        (∫ y, baseMain c w v ι σ y) + (∫ y, secondDerivDefect θD v ι σ y) + ∫ y, gradDefect θZ v ι σ y := by
      rw [hexp]
      show ∫ y, (baseMain c w v ι σ y + secondDerivDefect θD v ι σ y + gradDefect θZ v ι σ y) = _
      rw [integral_add (f := fun y => baseMain c w v ι σ y + secondDerivDefect θD v ι σ y) (iMain.add iHD) iGD,
        integral_add iMain iHD]
    have e2 : ∫ y, baseMain c w v ι σ y = (∫ y, mainPos c w v ι σ y) - ∫ y, mainNeg c w v ι σ y := by
      rw [hbm, integral_sub iPos iNeg]
    linarith

theorem smooth_modeSum_mainPos (hP : ModeSquareSumHolds) (hI4 : CurlWeightIdentityDecayHolds) (c : ℝ)
    {w : Space → ℝ} (hw0 : ∀ y, 0 ≤ w y) {B : ℝ} (hB : ∀ y, w y ≤ B) (hwm : Measurable w)
    (hwa : IsAxisymmetric w) {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    modeSum (mainPos c w v) =
      periodLIntegral (fun σ y => matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y))
        + ENNReal.ofReal (1 / 4) * periodLIntegral (fun σ y => ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2)
        + ENNReal.ofReal (max (-c) 0) * (periodLIntegral (fun σ y => ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2)
          + periodLIntegral (fun σ y => w y * matSq (gradField v σ y))) := by
  have nn := squares_nonneg v
  have mm := smooth_squares_measurable hv
  have e : mainPos c w v = fun ι σ y => (vortGradSq v ι σ y + 1 / 4 * vortSq v ι σ y)
      + max (-c) 0 * (secondDerivModeSq v ι σ y + w y * gradSq v ι σ y) := rfl
  rw [e, modeSum_add (F := fun ι σ y => vortGradSq v ι σ y + 1 / 4 * vortSq v ι σ y)
      (G := fun ι σ y => max (-c) 0 * (secondDerivModeSq v ι σ y + w y * gradSq v ι σ y))
      (fun ι σ y => add_nonneg (nn ι σ y).2.2.2.2 (mul_nonneg (by norm_num) (nn ι σ y).2.2.1))
      (fun ι σ y => mul_nonneg (le_max_right _ _) (add_nonneg (nn ι σ y).2.2.2.1 (mul_nonneg (hw0 y) (nn ι σ y).2.1)))
      (fun ι => (mm ι).2.2.2.2.add (measurable_const.mul (mm ι).2.2.1)),
    modeSum_add (F := fun ι σ y => vortGradSq v ι σ y) (G := fun ι σ y => 1 / 4 * vortSq v ι σ y)
      (fun ι σ y => (nn ι σ y).2.2.2.2) (fun ι σ y => mul_nonneg (by norm_num) (nn ι σ y).2.2.1)
      (fun ι => (mm ι).2.2.2.2),
    modeSum_const_mul (F := fun ι σ y => vortSq v ι σ y) (by norm_num),
    modeSum_const_mul (F := fun ι σ y => secondDerivModeSq v ι σ y + w y * gradSq v ι σ y) (le_max_right _ _),
    modeSum_add (F := fun ι σ y => secondDerivModeSq v ι σ y) (G := fun ι σ y => w y * gradSq v ι σ y)
      (fun ι σ y => (nn ι σ y).2.2.2.1) (fun ι σ y => mul_nonneg (hw0 y) (nn ι σ y).2.1)
      (fun ι => (mm ι).2.2.2.1)]
  rw [show (modeSum fun ι σ y => vortGradSq v ι σ y) = modeSum (vortGradSq v) from rfl,
    show (modeSum fun ι σ y => vortSq v ι σ y) = modeSum (vortSq v) from rfl,
    show (modeSum fun ι σ y => secondDerivModeSq v ι σ y) = modeSum (secondDerivModeSq v) from rfl,
    smooth_modeSum_eq_vortGrad hP hv, smooth_modeSum_eq_vort hP hv, smooth_modeSum_eq_secondDeriv hP hI4 hv,
    smooth_modeSum_eq_weighted_grad hP hv hw0 hB hwm hwa]

theorem smooth_modeSum_mainNeg (hP : ModeSquareSumHolds) (hI4 : CurlWeightIdentityDecayHolds) (c : ℝ)
    {w : Space → ℝ} (hw0 : ∀ y, 0 ≤ w y) {B : ℝ} (hB : ∀ y, w y ≤ B) (hwm : Measurable w)
    (hwa : IsAxisymmetric w) {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    modeSum (mainNeg c w v) =
      ENNReal.ofReal (max c 0) * (periodLIntegral (fun σ y => ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2)
          + periodLIntegral (fun σ y => w y * matSq (gradField v σ y))) := by
  have nn := squares_nonneg v
  have mm := smooth_squares_measurable hv
  have e : mainNeg c w v = fun ι σ y => max c 0 * (secondDerivModeSq v ι σ y + w y * gradSq v ι σ y) := rfl
  rw [e, modeSum_const_mul (F := fun ι σ y => secondDerivModeSq v ι σ y + w y * gradSq v ι σ y) (le_max_right _ _),
    modeSum_add (F := fun ι σ y => secondDerivModeSq v ι σ y) (G := fun ι σ y => w y * gradSq v ι σ y)
      (fun ι σ y => (nn ι σ y).2.2.2.1) (fun ι σ y => mul_nonneg (hw0 y) (nn ι σ y).2.1)
      (fun ι => (mm ι).2.2.2.1),
    show (modeSum fun ι σ y => secondDerivModeSq v ι σ y) = modeSum (secondDerivModeSq v) from rfl,
    smooth_modeSum_eq_secondDeriv hP hI4 hv, smooth_modeSum_eq_weighted_grad hP hv hw0 hB hwm hwa]

end SmoothBaseInternal

open BaseDensityInternal SmoothBaseInternal in
theorem baseDensitySmoothHolds_of (hPars : ModeSquareSumHolds) (hI4 : CurlWeightIdentityDecayHolds) :
    BaseDensitySmoothHolds := by
  intro C P cl convD convZ c w w₀ _ hw₀ hww hwb hwm hwa hD hZ _ _ hDb hZb v hv
  obtain ⟨B, hB⟩ := hwb
  obtain ⟨BD, hBD⟩ := hDb
  obtain ⟨BZ, hBZ⟩ := hZb
  have hw0 : ∀ y, 0 ≤ w y := fun y => hw₀.le.trans (hww y)
  obtain ⟨f1, f2, f3, f4⟩ := smooth_fields_finite hv hw0 hB hwm
  have mE := fun ι => smooth_measurable_expanded (hD (cl ι)) (hZ (cl ι)) c hwm hv ι
  unfold IsDensityLowerBound
  simp only [modeValues_baseDensity]
  rw [lintegral_tsum_swap (F := fun ι σ y => expanded (convD (cl ι)) (convZ (cl ι)) c w v ι σ y) mE,
    lintegral_tsum_swap (F := fun ι σ y => -expanded (convD (cl ι)) (convZ (cl ι)) c w v ι σ y)
      (fun ι => (mE ι).neg)]
  refine final_algebra (N := modeSum (mainNeg c w v)) (Q := modeSum (mainPos c w v)) ?_ ?_ ?_ ?_
  · rw [smooth_modeSum_mainNeg hPars hI4 c hw0 hB hwm hwa hv]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨f3.ne, f4.ne⟩)
  · rw [smooth_modeSum_mainPos hPars hI4 c hw0 hB hwm hwa hv]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨f1.ne, ENNReal.mul_ne_top ENNReal.ofReal_ne_top f2.ne⟩,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨f3.ne, f4.ne⟩)⟩
  · rw [smooth_modeSum_mainNeg hPars hI4 c hw0 hB hwm hwa hv, smooth_modeSum_mainPos hPars hI4 c hw0 hB hwm hwa hv,
      smooth_vorticityEnergy_eq hv, smooth_weightedEnergy_eq hv hw0 hB hwm]
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨f1.ne,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top f2.ne⟩)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨f3.ne, f4.ne⟩)),
      ENNReal.toReal_add f1.ne (ENNReal.mul_ne_top ENNReal.ofReal_ne_top f2.ne),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_add f3.ne f4.ne,
      ENNReal.toReal_ofReal (le_max_right _ _), ENNReal.toReal_ofReal (le_max_right _ _),
      ENNReal.toReal_ofReal (by norm_num)]
    linear_combination ((periodLIntegral fun σ y => ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2).toReal
      + (periodLIntegral fun σ y => w y * matSq (gradField v σ y)).toReal) *
        (max_zero_sub_max_neg_zero_eq_self c).symm
  · unfold modeSum
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun ι => ?_
    rw [← lintegral_add_left (measurable_inner (mE ι)),
      ← lintegral_add_left (measurable_inner (smooth_measurable_mainPos c hwm hv ι))]
    exact lintegral_mono_ae (smooth_per_mode hPars hI4 (hD (cl ι)) (hZ (cl ι))
      ⟨BD, fun y j hj => hBD (cl ι) y j hj⟩ ⟨BZ, fun y j hj => hBZ (cl ι) y j hj⟩ c hwm hw0 hB hwa hv ι)

end Coercive

end Breakdown
