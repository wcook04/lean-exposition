import Breakdown.Cert.ExtendedNodes
import Breakdown.Cert.TestPairing

open scoped ContDiff ENNReal Topology
open MeasureTheory Set Filter

noncomputable section

namespace Breakdown.Cert

namespace Internal.ExtendedDataContinuity

theorem slice_fderiv_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : ℝ × Space → X} {s : ℝ} {y : Space} (h : DifferentiableAt ℝ F (s, y)) (e : Space) :
    fderiv ℝ (fun u => F (s, u)) y e = fderiv ℝ F (s, y) (0, e) := by
  have h1 := (h.hasFDerivAt.comp y (hasFDerivAt_prodMk_right s y)).fderiv
  have h2 : (fun u => F (s, u)) = F ∘ fun u => (s, u) := rfl
  rw [h2, h1]
  simp

theorem norm_trace_le (H : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖secondDerivTrace H‖ ≤ 3 * ‖H‖ := by
  have hj : ∀ j : Fin 3, ‖H (unitVector j) (unitVector j)‖ ≤ ‖H‖ := fun j => by
    have h := H.le_opNorm₂ (unitVector j) (unitVector j)
    simpa [unitVector] using h
  unfold secondDerivTrace
  calc ‖∑ j : Fin 3, H (unitVector j) (unitVector j)‖
      ≤ ∑ j : Fin 3, ‖H (unitVector j) (unitVector j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, ‖H‖ := Finset.sum_le_sum fun j _ => hj j
    _ = 3 * ‖H‖ := by simp

theorem continuous_trace :
    Continuous (fun H : Space →L[ℝ] Space →L[ℝ] Space => secondDerivTrace H) := by
  unfold secondDerivTrace
  exact continuous_finsetSum _ fun j _ =>
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const

theorem inner_eq_sum (x w : Space) : inner ℝ x w = ∑ m : Fin 3, x m * w m := by
  simp [PiLp.inner_apply, mul_comm]

theorem testField_isCompact {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    IsCompact (tsupport (fun w : ℝ × Space => φ w.1 w.2)) :=
  hφ.2.1

theorem testField_partial {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) (z : ℝ × Space)
    (e : Space) :
    fderiv ℝ (φ z.1) z.2 e = fderiv ℝ (fun w : ℝ × Space => φ w.1 w.2) z (0, e) :=
  slice_fderiv_apply (F := fun w : ℝ × Space => φ w.1 w.2) (s := z.1) (y := z.2)
    ((hφ.1.differentiable (by simp)) _) e

variable {k : ℕ} {d : ExtendedCertificateData k}

def firstOrderPart (d : ExtendedCertificateData k) (q : Fin k → ℝ) (z : ℝ × Space) : Space :=
  (1 / d.period q) • deriv (fun s => d.profile q s z.2) z.1 + (1 / 2 : ℝ) • d.profile q z.1 z.2
    + (1 / 2 : ℝ) • fderiv ℝ (d.profile q z.1) z.2 z.2 + advectionAt (d.profile q z.1) z.2

def gradientPairing (d : ExtendedCertificateData k) (φ : ℝ → Space → Space) (q : Fin k → ℝ)
    (z : ℝ × Space) : ℝ :=
  ∑ j : Fin 3, inner ℝ (fderiv ℝ (d.profile q z.1) z.2 (unitVector j))
    (fderiv ℝ (φ z.1) z.2 (unitVector j))

theorem continuous_profile_fderiv (hd : IsExtendedCertificate d) :
    Continuous (fun x : (Fin k → ℝ) × ℝ × Space => fderiv ℝ (d.profile x.1 x.2.1) x.2.2) :=
  (ContDiff.fderiv (n := 0)
    (f := fun (x : (Fin k → ℝ) × ℝ × Space) (y : Space) => d.profile x.1 x.2.1 y)
    (g := fun x => x.2.2)
    (hd.profile_smooth.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk contDiff_snd)))
    contDiff_snd.snd (by rw [zero_add])).continuous

theorem continuous_profile_timeDeriv (hd : IsExtendedCertificate d) :
    Continuous (fun x : (Fin k → ℝ) × ℝ × Space =>
      deriv (fun s => d.profile x.1 s x.2.2) x.2.1) :=
  (ContDiff.fderiv (n := 0)
    (f := fun (x : (Fin k → ℝ) × ℝ × Space) (s : ℝ) => d.profile x.1 s x.2.2)
    (g := fun x => x.2.1)
    (hd.profile_smooth.comp (contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd.snd)))
    contDiff_snd.fst (by rw [zero_add])).continuous.clm_apply continuous_const

theorem continuousOn_firstOrderPart (hd : IsExtendedCertificate d) :
    ContinuousOn (fun x : (Fin k → ℝ) × (ℝ × Space) => firstOrderPart d x.1 x.2)
      (d.params ×ˢ univ) := by
  have hA2 : Continuous (fun x : (Fin k → ℝ) × ℝ × Space => d.profile x.1 x.2.1 x.2.2) :=
    hd.profile_smooth.continuous
  have hA3 := continuous_profile_fderiv hd
  have hT := continuous_profile_timeDeriv hd
  have hPinv : ContinuousOn (fun x : (Fin k → ℝ) × ℝ × Space => 1 / d.period x.1)
      (d.params ×ˢ univ) :=
    continuousOn_const.div (hd.period_continuous.comp continuousOn_fst fun x hx => hx.1)
      fun x hx => (hd.period_pos _ hx.1).ne'
  have c1 : ContinuousOn (fun x : (Fin k → ℝ) × ℝ × Space =>
      (1 / d.period x.1) • deriv (fun s => d.profile x.1 s x.2.2) x.2.1) (d.params ×ˢ univ) :=
    hPinv.smul hT.continuousOn
  have c2 : Continuous (fun x : (Fin k → ℝ) × ℝ × Space =>
      (1 / 2 : ℝ) • d.profile x.1 x.2.1 x.2.2) := hA2.const_smul (1 / 2 : ℝ)
  have c3 : Continuous (fun x : (Fin k → ℝ) × ℝ × Space =>
      (1 / 2 : ℝ) • fderiv ℝ (d.profile x.1 x.2.1) x.2.2 x.2.2) :=
    (hA3.clm_apply continuous_snd.snd).const_smul (1 / 2 : ℝ)
  have c5 : Continuous (fun x : (Fin k → ℝ) × ℝ × Space =>
      advectionAt (d.profile x.1 x.2.1) x.2.2) := hA3.clm_apply hA2
  unfold firstOrderPart
  exact ((c1.add c2.continuousOn).add c3.continuousOn).add c5.continuousOn

theorem continuous_gradientPairing (hd : IsExtendedCertificate d) {φ : ℝ → Space → Space}
    (hφ : IsSpaceTimeTestField φ) :
    Continuous (fun x : (Fin k → ℝ) × (ℝ × Space) => gradientPairing d φ x.1 x.2) := by
  have hΦ'c : Continuous (fderiv ℝ (fun w : ℝ × Space => φ w.1 w.2)) :=
    hφ.1.continuous_fderiv (by simp)
  have hA3 := continuous_profile_fderiv hd
  have hc : Continuous (fun x : (Fin k → ℝ) × (ℝ × Space) =>
      ∑ j : Fin 3, inner ℝ (fderiv ℝ (d.profile x.1 x.2.1) x.2.2 (unitVector j))
        (fderiv ℝ (fun w : ℝ × Space => φ w.1 w.2) x.2 (0, unitVector j))) :=
    continuous_finsetSum _ fun j _ => (hA3.clm_apply continuous_const).inner
      ((hΦ'c.comp continuous_snd).clm_apply continuous_const)
  refine hc.congr fun x => ?_
  unfold gradientPairing
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [testField_partial hφ x.2 (unitVector j)]

theorem gradientPairing_eq_zero {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ)
    (q : Fin k → ℝ) {z : ℝ × Space} (hz : z ∉ tsupport (fun w : ℝ × Space => φ w.1 w.2)) :
    gradientPairing d φ q z = 0 := by
  have h0 : fderiv ℝ (fun w : ℝ × Space => φ w.1 w.2) z = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hz (tsupport_fderiv_subset ℝ h)
  unfold gradientPairing
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [testField_partial hφ z (unitVector j), h0]
  simp

theorem integrable_gradientPairing (hd : IsExtendedCertificate d) {φ : ℝ → Space → Space}
    (hφ : IsSpaceTimeTestField φ) (q : Fin k → ℝ) : Integrable (gradientPairing d φ q) := by
  have hc : Continuous (fun z : ℝ × Space => gradientPairing d φ q z) :=
    (continuous_gradientPairing hd hφ).comp (f := fun z : ℝ × Space => (q, z))
      (continuous_const.prodMk continuous_id)
  have hs : HasCompactSupport (fun z : ℝ × Space => gradientPairing d φ q z) :=
    HasCompactSupport.intro (testField_isCompact hφ) fun _ hz => gradientPairing_eq_zero hφ q hz
  exact hc.integrable_of_hasCompactSupport hs

theorem continuousOn_gradientPairing_integral (hd : IsExtendedCertificate d)
    {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    ContinuousOn (fun q => ∫ z, gradientPairing d φ q z) d.params :=
  continuousOn_integral_of_compact_support (k := tsupport (fun w : ℝ × Space => φ w.1 w.2))
    hφ.2.1 (continuous_gradientPairing hd hφ).continuousOn
    fun q _ _ hz => gradientPairing_eq_zero hφ q hz

theorem integrable_secondOrder_pairing (hd : IsExtendedCertificate d) {q : Fin k → ℝ}
    (hq : q ∈ d.params) {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Integrable (fun z : ℝ × Space =>
      inner ℝ (secondDerivTrace (d.profileSecondDeriv q z.1 z.2)) (φ z.1 z.2)) := by
  have hΦc : Continuous (fun z : ℝ × Space => φ z.1 z.2) := hφ.1.continuous
  have hm : AEStronglyMeasurable (fun z : ℝ × Space =>
      inner ℝ (secondDerivTrace (d.profileSecondDeriv q z.1 z.2)) (φ z.1 z.2)) volume :=
    (continuous_trace.comp_aestronglyMeasurable
      (hd.profileSecondDeriv_measurable q hq)).inner hΦc.aestronglyMeasurable
  have hb : Integrable (fun z : ℝ × Space => 3 * d.decay * ‖φ z.1 z.2‖) :=
    (hΦc.norm.const_mul _).integrable_of_hasCompactSupport hφ.2.1.norm.mul_left
  refine hb.mono' hm (ae_of_all _ fun z => ?_)
  have h1 := (hd.profile_decay q hq z.1 z.2).2.2
  have hy : 1 ≤ (1 + ‖z.2‖) ^ 3 := one_le_pow₀ (by linarith [norm_nonneg z.2])
  have hpos : 0 < (1 + ‖z.2‖) ^ 3 := by positivity
  have hdec0 : 0 ≤ d.decay := by
    have := mul_nonneg ((norm_nonneg _).trans h1) hpos.le
    rwa [div_mul_cancel₀ _ hpos.ne'] at this
  have h2 : ‖d.profileSecondDeriv q z.1 z.2‖ ≤ d.decay := h1.trans (div_le_self hdec0 hy)
  rw [Real.norm_eq_abs]
  calc |inner ℝ (secondDerivTrace (d.profileSecondDeriv q z.1 z.2)) (φ z.1 z.2)|
      ≤ ‖secondDerivTrace (d.profileSecondDeriv q z.1 z.2)‖ * ‖φ z.1 z.2‖ := abs_real_inner_le_norm _ _
    _ ≤ 3 * d.decay * ‖φ z.1 z.2‖ := by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact (norm_trace_le _).trans (by linarith)

theorem slice_identity (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params)
    {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) (σ : ℝ) :
    ∫ y, inner ℝ (secondDerivTrace (d.profileSecondDeriv q σ y)) (φ σ y) =
      -∫ y, gradientPairing d φ q (σ, y) := by
  obtain ⟨R, -, hR⟩ := Internal.TestPairing.exists_bound hφ.2.1
  have hsm : ContDiff ℝ ∞ (φ σ) := Internal.TestPairing.slice_contDiff hφ.1 σ
  have hsc : HasCompactSupport (φ σ) := Internal.TestPairing.slice_hasCompactSupport hR σ
  set ψ : Fin 3 → Space → ℝ := fun m y => φ σ y m with hψ
  have e1 : ∀ m, ψ m = (EuclideanSpace.proj (𝕜 := ℝ) m) ∘ φ σ := fun m => by
    funext y
    simp [hψ]
  have hψs : ∀ m, ContDiff ℝ ∞ (ψ m) := fun m => by
    rw [e1 m]
    exact (EuclideanSpace.proj (𝕜 := ℝ) m).contDiff.comp hsm
  have hψc : ∀ m, HasCompactSupport (ψ m) := fun m => by
    rw [e1 m]
    exact hsc.comp_left (g := EuclideanSpace.proj (𝕜 := ℝ) m) (by simp)
  have hψd : ∀ m y e, fderiv ℝ (ψ m) y e = (fderiv ℝ (φ σ) y e) m := by
    intro m y e
    have h := ((EuclideanSpace.proj (𝕜 := ℝ) m).hasFDerivAt.comp y
      ((hsm.differentiable (by simp)) y).hasFDerivAt).fderiv
    rw [e1 m, h]
    simp
  have hW : Continuous (fun y => fderiv ℝ (d.profile q σ) y) :=
    (continuous_profile_fderiv hd).comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have key : ∀ j m : Fin 3,
      Integrable (fun y => ψ m y * (d.profileSecondDeriv q σ y (unitVector j) (unitVector j)) m) ∧
      Integrable (fun y => fderiv ℝ (ψ m) y (unitVector j)
        * (fderiv ℝ (d.profile q σ) y (unitVector j)) m) ∧
      ∫ y, ψ m y * (d.profileSecondDeriv q σ y (unitVector j) (unitVector j)) m =
        -∫ y, fderiv ℝ (ψ m) y (unitVector j) * (fderiv ℝ (d.profile q σ) y (unitVector j)) m := by
    intro j m
    have hw := hd.profileSecondDeriv_weak q hq σ j
    have hloc : LocallyIntegrable
        (fun y => (d.profileSecondDeriv q σ y).flip (unitVector j) (unitVector j)) volume :=
      locallyIntegrableOn_univ.1 ((ContinuousLinearMap.apply ℝ Space (unitVector j)).locallyIntegrableOn_comp
        (f := fun y => (d.profileSecondDeriv q σ y).flip (unitVector j))
        (locallyIntegrableOn_univ.2 hw.2.1))
    have i1 : Integrable (fun y =>
        ψ m y • (d.profileSecondDeriv q σ y).flip (unitVector j) (unitVector j)) :=
      hloc.integrable_smul_left_of_hasCompactSupport (hψs m).continuous (hψc m)
    have hfc : Continuous (fun y => fderiv ℝ (ψ m) y (unitVector j)) :=
      ((hψs m).continuous_fderiv (by simp)).clm_apply continuous_const
    have i2 : Integrable (fun y =>
        fderiv ℝ (ψ m) y (unitVector j) • fderiv ℝ (d.profile q σ) y (unitVector j)) :=
      (hfc.smul (hW.clm_apply continuous_const)).integrable_of_hasCompactSupport
        ((hψc m).fderiv_apply (𝕜 := ℝ) (unitVector j)).smul_right
    have hid := hw.2.2 (ψ m) ⟨hψs m, hψc m⟩ j
    have h3 := congrArg (EuclideanSpace.proj (𝕜 := ℝ) m) hid
    rw [map_neg, ← (EuclideanSpace.proj (𝕜 := ℝ) m).integral_comp_comm i1,
      ← (EuclideanSpace.proj (𝕜 := ℝ) m).integral_comp_comm i2] at h3
    have j1 := (EuclideanSpace.proj (𝕜 := ℝ) m).integrable_comp i1
    have j2 := (EuclideanSpace.proj (𝕜 := ℝ) m).integrable_comp i2
    simp only [ContinuousLinearMap.flip_apply, PiLp.proj_apply, WithLp.ofLp_smul,
      Pi.smul_apply, smul_eq_mul] at h3 j1 j2
    exact ⟨j1, j2, h3⟩
  have eL : (fun y => inner ℝ (secondDerivTrace (d.profileSecondDeriv q σ y)) (φ σ y)) =
      fun y => ∑ j : Fin 3, ∑ m : Fin 3,
        ψ m y * (d.profileSecondDeriv q σ y (unitVector j) (unitVector j)) m := by
    funext y
    simp only [secondDerivTrace, sum_inner, inner_eq_sum, hψ]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => mul_comm _ _
  have eR : (fun y => gradientPairing d φ q (σ, y)) =
      fun y => ∑ j : Fin 3, ∑ m : Fin 3,
        fderiv ℝ (ψ m) y (unitVector j) * (fderiv ℝ (d.profile q σ) y (unitVector j)) m := by
    funext y
    simp only [gradientPairing, inner_eq_sum, hψd]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => mul_comm _ _
  rw [eL, eR, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun m _ => (key j m).1,
    integral_finsetSum _ fun j _ => integrable_finsetSum _ fun m _ => (key j m).2.1,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun m _ => (key j m).1, integral_finsetSum _ fun m _ => (key j m).2.1,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun m _ => (key j m).2.2

theorem secondOrder_integral (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params)
    {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    ∫ z : ℝ × Space, inner ℝ (secondDerivTrace (d.profileSecondDeriv q z.1 z.2)) (φ z.1 z.2) =
      -∫ z, gradientPairing d φ q z := by
  rw [Measure.volume_eq_prod, integral_prod _ (integrable_secondOrder_pairing hd hq hφ),
    integral_prod _ (integrable_gradientPairing hd hφ q), ← integral_neg]
  congr 1
  funext σ
  exact slice_identity hd hq hφ σ

theorem integrable_firstOrder_pairing (hd : IsExtendedCertificate d) {q : Fin k → ℝ}
    (hq : q ∈ d.params) {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Integrable (fun z : ℝ × Space => inner ℝ (firstOrderPart d q z) (φ z.1 z.2)) := by
  have hc : Continuous (fun z : ℝ × Space => firstOrderPart d q z) :=
    (continuousOn_firstOrderPart hd).comp_continuous (f := fun z : ℝ × Space => (q, z))
      (continuous_const.prodMk continuous_id) fun z => ⟨hq, mem_univ _⟩
  refine (hc.inner hφ.1.continuous).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (testField_isCompact hφ) fun z hz => ?_
  have h0 := image_eq_zero_of_notMem_tsupport hz
  rw [h0, inner_zero_right]

theorem actuator_periodicField (hd : IsExtendedCertificate d) (i : Fin k) :
    IsPeriodicField (d.actuator i) :=
  ⟨hd.actuator_measurable i, hd.actuator_periodic i,
    lt_of_le_of_lt ((Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)).trans
      hd.actuator_norm) ENNReal.ofReal_lt_top⟩

theorem defect_inner_eq (d : ExtendedCertificateData k) (q : Fin k → ℝ) (φ : ℝ → Space → Space)
    (z : ℝ × Space) :
    inner ℝ (d.defect q z.1 z.2) (φ z.1 z.2) =
      inner ℝ (firstOrderPart d q z) (φ z.1 z.2)
        - inner ℝ (secondDerivTrace (d.profileSecondDeriv q z.1 z.2)) (φ z.1 z.2)
        + ∑ i, d.multiplier q i * inner ℝ (d.actuator i z.1 z.2) (φ z.1 z.2)
        + inner ℝ (d.pressureGrad q z.1 z.2) (φ z.1 z.2) := by
  have e : d.defect q z.1 z.2 = firstOrderPart d q z - secondDerivTrace (d.profileSecondDeriv q z.1 z.2)
      + ∑ i, d.multiplier q i • d.actuator i z.1 z.2 + d.pressureGrad q z.1 z.2 := by
    simp only [ExtendedCertificateData.defect, weakDefectField, firstOrderPart]
    abel
  rw [e, inner_add_left, inner_add_left, inner_sub_left, sum_inner]
  simp only [real_inner_smul_left]

theorem defect_pairing_eq (h : ExtendedDataHolds) (hd : IsExtendedCertificate d)
    {q : Fin k → ℝ} (hq : q ∈ d.params) {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    ∫ z : ℝ × Space, inner ℝ (d.defect q z.1 z.2) (φ z.1 z.2) =
      (∫ z, inner ℝ (firstOrderPart d q z) (φ z.1 z.2)) + (∫ z, gradientPairing d φ q z)
        + ∑ i, d.multiplier q i * ∫ z : ℝ × Space, inner ℝ (d.actuator i z.1 z.2) (φ z.1 z.2) := by
  obtain ⟨R, -, hR⟩ := Internal.TestPairing.exists_bound hφ.2.1
  have I0 : Integrable (fun z : ℝ × Space => inner ℝ (d.defect q z.1 z.2) (φ z.1 z.2)) :=
    Internal.TestPairing.integrable_pairing (h d hd q hq).1 hφ.1 hφ.2.1 hR
  have I1 := integrable_firstOrder_pairing hd hq hφ
  have I2 := integrable_secondOrder_pairing hd hq hφ
  have I3 : ∀ i, Integrable (fun z : ℝ × Space => inner ℝ (d.actuator i z.1 z.2) (φ z.1 z.2)) :=
    fun i => Internal.TestPairing.integrable_pairing (actuator_periodicField hd i) hφ.1 hφ.2.1 hR
  have I3' : Integrable (fun z : ℝ × Space =>
      ∑ i, d.multiplier q i * inner ℝ (d.actuator i z.1 z.2) (φ z.1 z.2)) :=
    integrable_finsetSum _ fun i _ => (I3 i).const_mul _
  have I12 : Integrable (fun z : ℝ × Space => inner ℝ (firstOrderPart d q z) (φ z.1 z.2)
      - inner ℝ (secondDerivTrace (d.profileSecondDeriv q z.1 z.2)) (φ z.1 z.2)) := I1.sub I2
  have I123 : Integrable (fun z : ℝ × Space => inner ℝ (firstOrderPart d q z) (φ z.1 z.2)
      - inner ℝ (secondDerivTrace (d.profileSecondDeriv q z.1 z.2)) (φ z.1 z.2)
      + ∑ i, d.multiplier q i * inner ℝ (d.actuator i z.1 z.2) (φ z.1 z.2)) := I12.add I3'
  have I4 : Integrable (fun z : ℝ × Space => inner ℝ (d.pressureGrad q z.1 z.2) (φ z.1 z.2)) := by
    refine (I0.sub I123).congr (ae_of_all _ fun z => ?_)
    simp only [Pi.sub_apply]
    rw [defect_inner_eq]
    ring
  rw [show (fun z : ℝ × Space => inner ℝ (d.defect q z.1 z.2) (φ z.1 z.2)) = _ from
      funext (defect_inner_eq d q φ),
    integral_add I123 I4, hd.pressureGrad_orthogonal q hq φ hφ, add_zero, integral_add I12 I3',
    integral_sub I1 I2, secondOrder_integral hd hq hφ,
    integral_finsetSum _ fun i _ => (I3 i).const_mul _]
  simp only [integral_const_mul, sub_neg_eq_add]

theorem continuousOn_defect (h : ExtendedDataHolds) (hd : IsExtendedCertificate d)
    {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    ContinuousOn (fun q => inner ℝ (d.defectH q) (testInHH φ)) d.params := by
  have h1 : ContinuousOn (fun q => ∫ z, inner ℝ (firstOrderPart d q z) (φ z.1 z.2)) d.params := by
    refine continuousOn_integral_of_compact_support
      (k := tsupport (fun z : ℝ × Space => φ z.1 z.2)) hφ.2.1 ?_ ?_
    · exact (continuousOn_firstOrderPart hd).inner
        (hφ.1.continuous.comp continuous_snd).continuousOn
    · intro q z _ hz
      have h0 := image_eq_zero_of_notMem_tsupport hz
      rw [h0, inner_zero_right]
  have h2 := continuousOn_gradientPairing_integral hd hφ
  have h3 : ContinuousOn (fun q => ∑ i, d.multiplier q i *
      ∫ z : ℝ × Space, inner ℝ (d.actuator i z.1 z.2) (φ z.1 z.2)) d.params :=
    continuousOn_finsetSum _ fun i _ =>
      ((continuous_apply i).comp_continuousOn hd.multiplier_continuous).mul continuousOn_const
  refine ((h1.add h2).add h3).congr fun q hq => ?_
  show inner ℝ (d.defectH q) (testInHH φ) = _
  rw [(h d hd q hq).2.1 φ hφ, defect_pairing_eq h hd hq hφ]
  rfl

theorem columnSq_nonneg (K : Space →L[ℝ] Space) : 0 ≤ matSq K :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem columnInner_bound (G K : Space →L[ℝ] Space) : |matInner G K| ≤ (3 * ‖G‖ ^ 2 + matSq K) / 2 := by
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

theorem sq_fderiv_le (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params) (σ : ℝ)
    (y : Space) :
    ‖fderiv ℝ (d.profile q σ) y‖ ^ 2 ≤ d.decay ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
  have h := (hd.profile_decay q hq σ y).2.1
  have hy : 0 < 1 + ‖y‖ := by positivity
  have h0 := norm_nonneg (fderiv ℝ (d.profile q σ) y)
  have e : (1 + ‖y‖) ^ (-(4 : ℝ)) = 1 / (1 + ‖y‖) ^ 4 := by
    rw [Real.rpow_neg hy.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  rw [e]
  calc ‖fderiv ℝ (d.profile q σ) y‖ ^ 2 ≤ (d.decay / (1 + ‖y‖) ^ 2) ^ 2 :=
        pow_le_pow_left₀ h0 h 2
    _ = d.decay ^ 2 * (1 / (1 + ‖y‖) ^ 4) := by
      generalize 1 + ‖y‖ = t
      ring

theorem restrict_eq : ((volume : Measure ℝ).restrict (Icc (0 : ℝ) 1)).prod (volume : Measure Space) =
    (volume : Measure (ℝ × Space)).restrict (Icc 0 1 ×ˢ univ) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem continuousOn_pinValue (hd : IsExtendedCertificate d) {χ : ℝ → Space → (Space →L[ℝ] Space)}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => χ z.1 z.2) volume)
    (hf : periodLIntegral (fun σ y => matSq (χ σ y)) < ⊤) :
    ContinuousOn (fun q => pinValue χ (fun σ y => fderiv ℝ (d.profile q σ) y)) d.params := by
  set μ := ((volume : Measure ℝ).restrict (Icc (0 : ℝ) 1)).prod (volume : Measure Space) with hμ
  have hmμ : AEStronglyMeasurable (fun z : ℝ × Space => χ z.1 z.2) μ := by
    rw [hμ, restrict_eq]
    exact hm.restrict
  have hD := continuous_profile_fderiv hd
  have hSq : Continuous (fun K : Space →L[ℝ] Space => matSq K) :=
    continuous_finsetSum _ fun i _ => ((continuous_id.clm_apply continuous_const).norm.pow 2)
  have hsqm : AEStronglyMeasurable (fun z : ℝ × Space => matSq (χ z.1 z.2)) μ :=
    hSq.comp_aestronglyMeasurable hmμ
  have hsqμ : Integrable (fun z : ℝ × Space => matSq (χ z.1 z.2)) μ := by
    refine ⟨hsqm, ?_⟩
    show ∫⁻ z, ‖matSq (χ z.1 z.2)‖ₑ ∂μ < ⊤
    simp only [Real.enorm_of_nonneg (columnSq_nonneg _)]
    rw [hμ, lintegral_prod _ hsqm.aemeasurable.ennreal_ofReal]
    exact hf
  have hdec : Integrable (fun z : ℝ × Space => d.decay ^ 2 * (1 + ‖z.2‖) ^ (-(4 : ℝ))) μ :=
    (integrable_const (d.decay ^ 2)).mul_prod (integrable_one_add_norm (E := Space)
      (μ := volume) (r := 4) (by rw [finrank_euclideanSpace, Fintype.card_fin]; norm_num))
  have hb : Integrable (fun z : ℝ × Space =>
      (3 * (d.decay ^ 2 * (1 + ‖z.2‖) ^ (-(4 : ℝ))) + matSq (χ z.1 z.2)) / 2) μ :=
    ((hdec.const_mul 3).add hsqμ).div_const 2
  have hFm : ∀ q ∈ d.params, AEStronglyMeasurable
      (fun z : ℝ × Space => matInner (fderiv ℝ (d.profile q z.1) z.2) (χ z.1 z.2)) μ := by
    intro q _
    have hDq : Continuous (fun z : ℝ × Space => fderiv ℝ (d.profile q z.1) z.2) :=
      hD.comp (continuous_const.prodMk continuous_id)
    unfold matInner
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      ((hDq.clm_apply continuous_const).aestronglyMeasurable).inner
        ((continuous_id.clm_apply continuous_const).comp_aestronglyMeasurable hmμ)
  have hbd : ∀ q ∈ d.params, ∀ᵐ z ∂μ, ‖matInner (fderiv ℝ (d.profile q z.1) z.2) (χ z.1 z.2)‖ ≤
      (3 * (d.decay ^ 2 * (1 + ‖z.2‖) ^ (-(4 : ℝ))) + matSq (χ z.1 z.2)) / 2 := by
    intro q hq
    refine ae_of_all _ fun z => ?_
    rw [Real.norm_eq_abs]
    have h1 := columnInner_bound (fderiv ℝ (d.profile q z.1) z.2) (χ z.1 z.2)
    have h2 := sq_fderiv_le hd hq z.1 z.2
    linarith
  have hcont : ∀ᵐ z ∂μ, ContinuousOn
      (fun q => matInner (fderiv ℝ (d.profile q z.1) z.2) (χ z.1 z.2)) d.params := by
    refine ae_of_all _ fun z => Continuous.continuousOn ?_
    unfold matInner
    exact continuous_finsetSum _ fun i _ =>
      ((hD.comp (continuous_id.prodMk continuous_const)).clm_apply continuous_const).inner
        continuous_const
  refine (continuousOn_of_dominated hFm hbd hb hcont).congr fun q hq => ?_
  show pinValue χ (fun σ y => fderiv ℝ (d.profile q σ) y) = _
  unfold pinValue
  exact (integral_prod _ (hb.mono' (hFm q hq) (hbd q hq))).symm

end Internal.ExtendedDataContinuity

open Internal.ExtendedDataContinuity in
theorem extendedDataContinuityHolds_of (h : ExtendedDataHolds) : ExtendedDataContinuityHolds := by
  intro k d hd
  refine ⟨?_, fun φ hφ => continuousOn_defect h hd hφ⟩
  refine continuousOn_pi.2 fun i => ?_
  exact ((continuous_apply i).comp_continuousOn hd.target_continuous).sub
    (continuousOn_pinValue hd (hd.pin_measurable i) (hd.pin_finite i))

end Breakdown.Cert
