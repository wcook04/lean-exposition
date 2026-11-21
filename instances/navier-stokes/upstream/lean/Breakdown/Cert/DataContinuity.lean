import Breakdown.Cert.Nodes
import Breakdown.Cert.TestPairing

open scoped ContDiff ENNReal Topology
open MeasureTheory Set Filter

noncomputable section

namespace Breakdown.Cert

namespace Internal.DataContinuity

theorem inner_gradientAt (g : Space → ℝ) (x w : Space) :
    inner ℝ (gradientAt g x) w = ∑ i : Fin 3, fderiv ℝ g x (unitVector i) * w i := by
  simp [gradientAt, sum_inner, real_inner_smul_left, unitVector, EuclideanSpace.inner_single_left]

theorem partial_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {F : ℝ × Space → X}
    {s : ℝ} {y : Space} (h : DifferentiableAt ℝ F (s, y)) (e : Space) :
    fderiv ℝ (fun u => F (s, u)) y e = fderiv ℝ F (s, y) (0, e) := by
  have h1 := (h.hasFDerivAt.comp y (hasFDerivAt_prodMk_right s y)).fderiv
  have h2 : (fun u => F (s, u)) = F ∘ fun u => (s, u) := rfl
  rw [h2, h1]
  simp

theorem integrable_of_cont_supp {f : ℝ × Space → ℝ} {φ : ℝ × Space → Space} (hf : Continuous f)
    (hc : HasCompactSupport φ) (h0 : ∀ z, φ z = 0 → f z = 0) : Integrable f := by
  refine hf.integrable_of_hasCompactSupport (hc.mono fun z hz => ?_)
  intro hφ
  exact hz (h0 z hφ)

theorem pressure_pairing {Q : ℝ → Space → ℝ} (hQ : ContDiff ℝ 1 (fun z : ℝ × Space => Q z.1 z.2))
    {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Integrable (fun z : ℝ × Space => inner ℝ (gradientAt (Q z.1) z.2) (φ z.1 z.2)) ∧
    ∫ z : ℝ × Space, inner ℝ (gradientAt (Q z.1) z.2) (φ z.1 z.2) = 0 := by
  obtain ⟨hs, hc, hdiv⟩ := hφ
  set q : ℝ × Space → ℝ := fun z => Q z.1 z.2 with hq_def
  set Φ : ℝ × Space → Space := fun z => φ z.1 z.2 with hΦ_def
  have hqd : Differentiable ℝ q := hQ.differentiable one_ne_zero
  have hΦd : Differentiable ℝ Φ := hs.differentiable (by simp)
  have hq'c : Continuous (fderiv ℝ q) := hQ.continuous_fderiv one_ne_zero
  have hΦ'c : Continuous (fderiv ℝ Φ) := hs.continuous_fderiv (by simp)
  have hqc : Continuous q := hQ.continuous
  have hΦc : Continuous Φ := hs.continuous
  have hpw : ∀ z : ℝ × Space, inner ℝ (gradientAt (Q z.1) z.2) (φ z.1 z.2) =
      ∑ i : Fin 3, fderiv ℝ q z (0, unitVector i) * (Φ z) i := by
    intro z
    rw [inner_gradientAt]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := partial_apply (F := q) (s := z.1) (y := z.2) (hqd _) (unitVector i)
    simp only [hq_def] at this ⊢
    rw [this]
  have hint1 : ∀ i : Fin 3, Integrable (fun z => fderiv ℝ q z (0, unitVector i) * (Φ z) i) := by
    intro i
    refine integrable_of_cont_supp (φ := Φ) ?_ hc fun z hz => by simp [hz]
    exact (hq'c.clm_apply continuous_const).mul ((EuclideanSpace.proj i).continuous.comp hΦc)
  have hint2 : ∀ i : Fin 3, Integrable (fun z => q z * (fderiv ℝ Φ z (0, unitVector i)) i) := by
    intro i
    refine hqc.mul ((EuclideanSpace.proj i).continuous.comp (hΦ'c.clm_apply continuous_const))
      |>.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.mul_left ?_
    have h3 := (hc.fderiv_apply (𝕜 := ℝ) ((0 : ℝ), unitVector i)).comp_left
      (g := EuclideanSpace.proj (𝕜 := ℝ) i) (by simp)
    exact h3
  have hint3 : ∀ i : Fin 3, Integrable (fun z => q z * (Φ z) i) := by
    intro i
    refine integrable_of_cont_supp (φ := Φ) ?_ hc fun z hz => by simp [hz]
    exact hqc.mul ((EuclideanSpace.proj i).continuous.comp hΦc)
  have : (volume : Measure (ℝ × Space)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hibp : ∀ i : Fin 3, ∫ z, fderiv ℝ q z (0, unitVector i) * (Φ z) i =
      -∫ z, q z * (fderiv ℝ Φ z (0, unitVector i)) i := by
    intro i
    have h := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
      (μ := (volume : Measure (ℝ × Space)))
      (f := q) (f' := fderiv ℝ q) (g := fun z => (Φ z) i)
      (g' := fun z => (EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ Φ z))
      (v := ((0 : ℝ), unitVector i)) (B := ContinuousLinearMap.mul ℝ ℝ)
      (hint1 i) (hint2 i) (hint3 i) (fun z _ => (hqd z).hasFDerivAt)
      (fun z _ => (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp z (hΦd z).hasFDerivAt)
    have e1 : ∀ x, (EuclideanSpace.proj (𝕜 := ℝ) i) (fderiv ℝ Φ x (0, unitVector i)) =
        (fderiv ℝ Φ x (0, unitVector i)) i := fun x => rfl
    simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.comp_apply, e1] at h
    rw [h, neg_neg]
  have hdivz : ∀ z : ℝ × Space, ∑ i : Fin 3, (fderiv ℝ Φ z (0, unitVector i)) i = 0 := by
    intro z
    have h := hdiv z.1 z.2
    unfold divergenceAt at h
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h
    have := partial_apply (F := Φ) (s := z.1) (y := z.2) (hΦd _) (unitVector i)
    exact (congrArg (fun v : Space => v i) this).symm
  have hfun : (fun z : ℝ × Space => inner ℝ (gradientAt (Q z.1) z.2) (φ z.1 z.2)) =
      fun z => ∑ i : Fin 3, fderiv ℝ q z (0, unitVector i) * (Φ z) i := funext hpw
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact integrable_finsetSum _ fun i _ => hint1 i
  · rw [hfun, integral_finsetSum _ fun i _ => hint1 i]
    simp only [hibp]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ => hint2 i]
    simp only [← Finset.mul_sum, hdivz, mul_zero, integral_zero, neg_zero]

variable {k : ℕ} {d : CertificateData k}

def smoothPart (d : CertificateData k) (p : Fin k → ℝ) (z : ℝ × Space) : Space :=
  (1 / d.period p) • deriv (fun s => d.profile p s z.2) z.1 + (1 / 2 : ℝ) • d.profile p z.1 z.2
    + (1 / 2 : ℝ) • fderiv ℝ (d.profile p z.1) z.2 z.2 - sumSecondPartialsAt (d.profile p z.1) z.2
    + advectionAt (d.profile p z.1) z.2

theorem contDiff_profile_fderiv (hd : IsCertificate d) :
    ContDiff ℝ 1 (fun x : (Fin k → ℝ) × ℝ × Space => fderiv ℝ (d.profile x.1 x.2.1) x.2.2) :=
  ContDiff.fderiv (f := fun (x : (Fin k → ℝ) × ℝ × Space) (y : Space) => d.profile x.1 x.2.1 y)
    (g := fun x => x.2.2)
    (hd.profile_smooth.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk contDiff_snd)))
    contDiff_snd.snd one_add_one_eq_two.le

theorem continuousOn_smoothPart (hd : IsCertificate d) :
    ContinuousOn (fun x : (Fin k → ℝ) × (ℝ × Space) => smoothPart d x.1 x.2) (d.box ×ˢ univ) := by
  have hP : ContDiff ℝ 2 (fun x : (Fin k → ℝ) × ℝ × Space => d.profile x.1 x.2.1 x.2.2) :=
    hd.profile_smooth
  have hA2 : Continuous (fun x : (Fin k → ℝ) × ℝ × Space => d.profile x.1 x.2.1 x.2.2) :=
    hP.continuous
  have hA3 := (contDiff_profile_fderiv hd).continuous
  have hB : ContDiff ℝ 1 (fun w : ((Fin k → ℝ) × ℝ × Space) × Space =>
      fderiv ℝ (d.profile w.1.1 w.1.2.1) w.2) :=
    ContDiff.fderiv (f := fun (w : ((Fin k → ℝ) × ℝ × Space) × Space) (y : Space) =>
      d.profile w.1.1 w.1.2.1 y) (g := fun w => w.2)
      (hP.comp (contDiff_fst.fst.fst.prodMk (contDiff_fst.fst.snd.fst.prodMk contDiff_snd)))
      contDiff_snd one_add_one_eq_two.le
  have hA4 : ContDiff ℝ 0 (fun x : (Fin k → ℝ) × ℝ × Space =>
      fderiv ℝ (fun y => fderiv ℝ (d.profile x.1 x.2.1) y) x.2.2) :=
    ContDiff.fderiv (f := fun (x : (Fin k → ℝ) × ℝ × Space) (y : Space) =>
      fderiv ℝ (d.profile x.1 x.2.1) y) (g := fun x => x.2.2) hB contDiff_snd.snd (by rw [zero_add])
  have hA1 : ContDiff ℝ 1 (fun x : (Fin k → ℝ) × ℝ × Space =>
      fderiv ℝ (fun s => d.profile x.1 s x.2.2) x.2.1) :=
    ContDiff.fderiv (f := fun (x : (Fin k → ℝ) × ℝ × Space) (s : ℝ) => d.profile x.1 s x.2.2)
      (g := fun x => x.2.1)
      (hP.comp (contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd.snd)))
      contDiff_snd.fst one_add_one_eq_two.le
  have hT : Continuous (fun x : (Fin k → ℝ) × ℝ × Space =>
      deriv (fun s => d.profile x.1 s x.2.2) x.2.1) :=
    hA1.continuous.clm_apply continuous_const
  have hL : Continuous (fun x : (Fin k → ℝ) × ℝ × Space =>
      sumSecondPartialsAt (d.profile x.1 x.2.1) x.2.2) := by
    have e : (fun x : (Fin k → ℝ) × ℝ × Space => sumSecondPartialsAt (d.profile x.1 x.2.1) x.2.2) =
        fun x => ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (d.profile x.1 x.2.1) y) x.2.2
          (unitVector i) (unitVector i) := by
      funext x
      simp [sumSecondPartialsAt, iteratedFDeriv_two_apply]
    rw [e]
    exact continuous_finsetSum _ fun i _ =>
      (hA4.continuous.clm_apply continuous_const).clm_apply continuous_const
  have hPinv : ContinuousOn (fun x : (Fin k → ℝ) × ℝ × Space => 1 / d.period x.1)
      (d.box ×ˢ univ) :=
    continuousOn_const.div (hd.period_continuous.comp continuousOn_fst fun x hx => hx.1)
      fun x hx => (hd.period_pos _ hx.1).ne'
  have c1 : ContinuousOn (fun x : (Fin k → ℝ) × ℝ × Space =>
      (1 / d.period x.1) • deriv (fun s => d.profile x.1 s x.2.2) x.2.1) (d.box ×ˢ univ) :=
    hPinv.smul hT.continuousOn
  have c2 : Continuous (fun x : (Fin k → ℝ) × ℝ × Space =>
      (1 / 2 : ℝ) • d.profile x.1 x.2.1 x.2.2) := hA2.const_smul (1 / 2 : ℝ)
  have c3 : Continuous (fun x : (Fin k → ℝ) × ℝ × Space =>
      (1 / 2 : ℝ) • fderiv ℝ (d.profile x.1 x.2.1) x.2.2 x.2.2) :=
    (hA3.clm_apply continuous_snd.snd).const_smul (1 / 2 : ℝ)
  have c5 : Continuous (fun x : (Fin k → ℝ) × ℝ × Space =>
      advectionAt (d.profile x.1 x.2.1) x.2.2) := hA3.clm_apply hA2
  unfold smoothPart
  exact (((c1.add c2.continuousOn).add c3.continuousOn).sub hL.continuousOn).add c5.continuousOn

theorem continuousOn_smooth_pairing (hd : IsCertificate d) {φ : ℝ → Space → Space}
    (hφ : IsSpaceTimeTestField φ) :
    ContinuousOn (fun p => ∫ z, inner ℝ (smoothPart d p z) (φ z.1 z.2)) d.box := by
  refine continuousOn_integral_of_compact_support (k := tsupport (fun z : ℝ × Space => φ z.1 z.2))
    hφ.2.1 ?_ ?_
  · exact (continuousOn_smoothPart hd).inner (hφ.1.continuous.comp continuous_snd).continuousOn
  · intro p z _ hz
    have h0 := image_eq_zero_of_notMem_tsupport hz
    rw [h0, inner_zero_right]

theorem actuator_periodicField (hd : IsCertificate d) (i : Fin k) : IsPeriodicField (d.actuator i) :=
  ⟨hd.actuator_measurable i, hd.actuator_periodic i,
    lt_of_le_of_lt ((Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)).trans
      hd.actuator_norm) ENNReal.ofReal_lt_top⟩

theorem defect_pairing_eq (hd : IsCertificate d) {φ : ℝ → Space → Space}
    (hφ : IsSpaceTimeTestField φ) {p : Fin k → ℝ} (hp : p ∈ d.box) :
    ∫ z : ℝ × Space, inner ℝ (defectField (d.period p) (d.profile p) (d.pressure p) d.actuator
        (d.multiplier p) z.1 z.2) (φ z.1 z.2) =
      (∫ z, inner ℝ (smoothPart d p z) (φ z.1 z.2))
        + ∑ i, d.multiplier p i * ∫ z : ℝ × Space, inner ℝ (d.actuator i z.1 z.2) (φ z.1 z.2) := by
  have hpt : ∀ z : ℝ × Space, inner ℝ (defectField (d.period p) (d.profile p) (d.pressure p)
      d.actuator (d.multiplier p) z.1 z.2) (φ z.1 z.2) =
      inner ℝ (smoothPart d p z) (φ z.1 z.2)
        + ∑ i, d.multiplier p i * inner ℝ (d.actuator i z.1 z.2) (φ z.1 z.2)
        + inner ℝ (gradientAt (d.pressure p z.1) z.2) (φ z.1 z.2) := by
    intro z
    have e : defectField (d.period p) (d.profile p) (d.pressure p) d.actuator (d.multiplier p)
        z.1 z.2 = smoothPart d p z + ∑ i, d.multiplier p i • d.actuator i z.1 z.2
          + gradientAt (d.pressure p z.1) z.2 := by
      unfold defectField smoothPart
      rfl
    rw [e, inner_add_left, inner_add_left, sum_inner]
    simp only [real_inner_smul_left]
  obtain ⟨R, -, hR⟩ := Internal.TestPairing.exists_bound hφ.2.1
  have I1 : Integrable (fun z : ℝ × Space => inner ℝ (smoothPart d p z) (φ z.1 z.2)) := by
    refine integrable_of_cont_supp (φ := fun z : ℝ × Space => φ z.1 z.2) ?_ hφ.2.1
      fun z hz => by rw [hz, inner_zero_right]
    have hpz : Continuous (fun z : ℝ × Space => (p, z)) := continuous_const.prodMk continuous_id
    have hc : Continuous (fun z : ℝ × Space => smoothPart d p z) :=
      (continuousOn_smoothPart hd).comp_continuous (f := fun z : ℝ × Space => (p, z)) hpz
        fun z => ⟨hp, mem_univ _⟩
    exact hc.inner hφ.1.continuous
  have I2 : ∀ i, Integrable (fun z : ℝ × Space => inner ℝ (d.actuator i z.1 z.2) (φ z.1 z.2)) :=
    fun i => Internal.TestPairing.integrable_pairing (actuator_periodicField hd i) hφ.1 hφ.2.1 hR
  have I2' : Integrable (fun z : ℝ × Space =>
      ∑ i, d.multiplier p i * inner ℝ (d.actuator i z.1 z.2) (φ z.1 z.2)) :=
    integrable_finsetSum _ fun i _ => (I2 i).const_mul _
  obtain ⟨I3, h3⟩ := pressure_pairing (hd.pressure_smooth p hp) hφ
  have I12 : Integrable (fun z : ℝ × Space => inner ℝ (smoothPart d p z) (φ z.1 z.2)
      + ∑ i, d.multiplier p i * inner ℝ (d.actuator i z.1 z.2) (φ z.1 z.2)) := I1.add I2'
  rw [show (fun z : ℝ × Space => inner ℝ (defectField (d.period p) (d.profile p) (d.pressure p)
      d.actuator (d.multiplier p) z.1 z.2) (φ z.1 z.2)) = _ from funext hpt,
    integral_add I12 I3, integral_add I1 I2', h3, add_zero, integral_finsetSum _
      fun i _ => (I2 i).const_mul _]
  simp only [integral_const_mul]

theorem continuousOn_defect (h : DataHolds) (hd : IsCertificate d) {φ : ℝ → Space → Space}
    (hφ : IsSpaceTimeTestField φ) :
    ContinuousOn (fun p => inner ℝ (defectH d p) (testInHH φ)) d.box := by
  have h1 := continuousOn_smooth_pairing hd hφ
  have h2 : ContinuousOn (fun p => ∑ i, d.multiplier p i *
      ∫ z : ℝ × Space, inner ℝ (d.actuator i z.1 z.2) (φ z.1 z.2)) d.box :=
    continuousOn_finsetSum _ fun i _ =>
      ((continuous_apply i).comp_continuousOn hd.multiplier_continuous).mul continuousOn_const
  have hc : ContinuousOn (fun p => (∫ z, inner ℝ (smoothPart d p z) (φ z.1 z.2))
      + ∑ i, d.multiplier p i * ∫ z : ℝ × Space, inner ℝ (d.actuator i z.1 z.2) (φ z.1 z.2))
      d.box := h1.add h2
  refine hc.congr fun p hp => ?_
  show inner ℝ (defectH d p) (testInHH φ) = _
  rw [(h d hd p hp).1 φ hφ, defect_pairing_eq hd hφ hp]

theorem matSq_nonneg (K : Space →L[ℝ] Space) : 0 ≤ matSq K :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem matNorm_bound (G K : Space →L[ℝ] Space) : |matInner G K| ≤ (3 * ‖G‖ ^ 2 + matSq K) / 2 := by
  have hu : ∀ i, ‖unitVector i‖ = 1 := fun i => by simp [unitVector]
  have hG : ∀ i, ‖G (unitVector i)‖ ≤ ‖G‖ := fun i => by
    simpa [hu i] using G.le_opNorm (unitVector i)
  have hi : ∀ i, |inner ℝ (G (unitVector i)) (K (unitVector i))| ≤
      (‖G‖ ^ 2 + ‖K (unitVector i)‖ ^ 2) / 2 := by
    intro i
    have h1 := abs_real_inner_le_norm (G (unitVector i)) (K (unitVector i))
    have h2 := mul_le_mul_of_nonneg_right (hG i) (norm_nonneg (K (unitVector i)))
    nlinarith [sq_nonneg (‖G‖ - ‖K (unitVector i)‖)]
  unfold matInner matSq
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  linarith [abs_add_three (inner ℝ (G (unitVector 0)) (K (unitVector 0)))
    (inner ℝ (G (unitVector 1)) (K (unitVector 1))) (inner ℝ (G (unitVector 2)) (K (unitVector 2))),
    hi 0, hi 1, hi 2]

theorem sq_fderiv_le (hd : IsCertificate d) {p : Fin k → ℝ} (hp : p ∈ d.box) (σ : ℝ) (y : Space) :
    ‖fderiv ℝ (d.profile p σ) y‖ ^ 2 ≤ d.decay ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
  have h := hd.profile_decay p hp σ y 1 (by norm_num)
  rw [norm_iteratedFDeriv_one] at h
  have hy : 0 < 1 + ‖y‖ := by positivity
  have h0 := norm_nonneg (fderiv ℝ (d.profile p σ) y)
  have e : (1 + ‖y‖) ^ (-(4 : ℝ)) = 1 / (1 + ‖y‖) ^ 4 := by
    rw [Real.rpow_neg hy.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  rw [e]
  calc ‖fderiv ℝ (d.profile p σ) y‖ ^ 2 ≤ (d.decay / (1 + ‖y‖) ^ (1 + 1)) ^ 2 :=
        pow_le_pow_left₀ h0 h 2
    _ = d.decay ^ 2 * (1 / (1 + ‖y‖) ^ 4) := by
      generalize 1 + ‖y‖ = t
      ring

theorem restrict_eq : ((volume : Measure ℝ).restrict (Icc (0 : ℝ) 1)).prod (volume : Measure Space) =
    (volume : Measure (ℝ × Space)).restrict (Icc 0 1 ×ˢ univ) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem continuousOn_pinValue (hd : IsCertificate d) {χ : ℝ → Space → (Space →L[ℝ] Space)}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => χ z.1 z.2) volume)
    (hf : periodLIntegral (fun σ y => matSq (χ σ y)) < ⊤) :
    ContinuousOn (fun p => pinValue χ (fun σ y => fderiv ℝ (d.profile p σ) y)) d.box := by
  set μ := ((volume : Measure ℝ).restrict (Icc (0 : ℝ) 1)).prod (volume : Measure Space) with hμ
  have hmμ : AEStronglyMeasurable (fun z : ℝ × Space => χ z.1 z.2) μ := by
    rw [hμ, restrict_eq]
    exact hm.restrict
  have hD := (contDiff_profile_fderiv hd).continuous
  have hSq : Continuous (fun K : Space →L[ℝ] Space => matSq K) :=
    continuous_finsetSum _ fun i _ => ((continuous_id.clm_apply continuous_const).norm.pow 2)
  have hsqm : AEStronglyMeasurable (fun z : ℝ × Space => matSq (χ z.1 z.2)) μ :=
    hSq.comp_aestronglyMeasurable hmμ
  have hsqμ : Integrable (fun z : ℝ × Space => matSq (χ z.1 z.2)) μ := by
    refine ⟨hsqm, ?_⟩
    show ∫⁻ z, ‖matSq (χ z.1 z.2)‖ₑ ∂μ < ⊤
    simp only [Real.enorm_of_nonneg (matSq_nonneg _)]
    rw [hμ, lintegral_prod _ hsqm.aemeasurable.ennreal_ofReal]
    exact hf
  have hdec : Integrable (fun z : ℝ × Space => d.decay ^ 2 * (1 + ‖z.2‖) ^ (-(4 : ℝ))) μ :=
    (integrable_const (d.decay ^ 2)).mul_prod (integrable_one_add_norm (E := Space)
      (μ := volume) (r := 4) (by rw [finrank_euclideanSpace, Fintype.card_fin]; norm_num))
  have hb : Integrable (fun z : ℝ × Space =>
      (3 * (d.decay ^ 2 * (1 + ‖z.2‖) ^ (-(4 : ℝ))) + matSq (χ z.1 z.2)) / 2) μ :=
    ((hdec.const_mul 3).add hsqμ).div_const 2
  have hFm : ∀ p ∈ d.box, AEStronglyMeasurable
      (fun z : ℝ × Space => matInner (fderiv ℝ (d.profile p z.1) z.2) (χ z.1 z.2)) μ := by
    intro p _
    have hDp : Continuous (fun z : ℝ × Space => fderiv ℝ (d.profile p z.1) z.2) :=
      hD.comp (continuous_const.prodMk continuous_id)
    unfold matInner
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      ((hDp.clm_apply continuous_const).aestronglyMeasurable).inner
        ((continuous_id.clm_apply continuous_const).comp_aestronglyMeasurable hmμ)
  have hbd : ∀ p ∈ d.box, ∀ᵐ z ∂μ, ‖matInner (fderiv ℝ (d.profile p z.1) z.2) (χ z.1 z.2)‖ ≤
      (3 * (d.decay ^ 2 * (1 + ‖z.2‖) ^ (-(4 : ℝ))) + matSq (χ z.1 z.2)) / 2 := by
    intro p hp
    refine ae_of_all _ fun z => ?_
    rw [Real.norm_eq_abs]
    have h1 := matNorm_bound (fderiv ℝ (d.profile p z.1) z.2) (χ z.1 z.2)
    have h2 := sq_fderiv_le hd hp z.1 z.2
    linarith
  have hcont : ∀ᵐ z ∂μ, ContinuousOn
      (fun p => matInner (fderiv ℝ (d.profile p z.1) z.2) (χ z.1 z.2)) d.box := by
    refine ae_of_all _ fun z => Continuous.continuousOn ?_
    unfold matInner
    exact continuous_finsetSum _ fun i _ =>
      ((hD.comp (continuous_id.prodMk continuous_const)).clm_apply continuous_const).inner
        continuous_const
  refine (continuousOn_of_dominated hFm hbd hb hcont).congr fun p hp => ?_
  show pinValue χ (fun σ y => fderiv ℝ (d.profile p σ) y) = _
  unfold pinValue
  exact (integral_prod _ (hb.mono' (hFm p hp) (hbd p hp))).symm

end Internal.DataContinuity

open Internal.DataContinuity in
theorem dataContinuityHolds_of (h : DataHolds) : DataContinuityHolds := by
  intro k d hd
  refine ⟨?_, fun φ hφ => continuousOn_defect h hd hφ⟩
  refine continuousOn_pi.2 fun i => ?_
  exact ((continuous_apply i).comp_continuousOn hd.target_continuous).sub
    (continuousOn_pinValue hd (hd.pin_measurable i) (hd.pin_finite i))

end Breakdown.Cert
