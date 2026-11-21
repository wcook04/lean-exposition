import Breakdown.CertCell.CellCalculusStatements
import Breakdown.CertCell.FormNegativeFinite
import Breakdown.CertCell.ModeDensityBridgeLinksParts

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal.TrueRegular

open CellCert.CellAnalysis CellCalculus

theorem continuous_planePoint : Continuous planePoint := by
  have e : planePoint = fun p : ℝ × ℝ => p.1 • unitVector 0 + p.2 • unitVector 2 :=
    funext TailBand.Internal.AngularPlane.planePoint_eq
  rw [e]
  fun_prop

theorem measurable_planePoint : Measurable planePoint := continuous_planePoint.measurable

theorem rect_ae_le_halfPlane {B : CellBox} (hB : IsCellBox B) : B.rect ≤ᵐ[volume] halfPlane := by
  rw [ae_le_set]
  refine measure_mono_null (t := ({0} ×ˢ Set.univ) ∪ (Set.univ ×ˢ {0})) ?_ ?_
  · rintro ⟨r, z⟩ ⟨⟨⟨hr1, _⟩, hz1, _⟩, hn⟩
    simp only [halfPlane, Set.mem_prod, Set.mem_Ioi, not_and_or, not_lt] at hn
    rcases hn with h | h
    · exact Or.inl ⟨Set.mem_singleton_iff.2 (le_antisymm h (hB.r_order.1.trans hr1)), trivial⟩
    · exact Or.inr ⟨trivial, Set.mem_singleton_iff.2 (le_antisymm h (hB.z_order.1.trans hz1))⟩
  · refine measure_union_null ?_ ?_
    · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
    · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

theorem restrict_ac {S : Set (ℝ × ℝ)} (hS : S ≤ᵐ[volume] halfPlane) :
    volume.restrict S ≪ volume.restrict halfPlane :=
  (Measure.restrict_mono_ae hS).absolutelyContinuous

theorem measurableSet_rect (B : CellBox) : MeasurableSet B.rect :=
  measurableSet_Icc.prod measurableSet_Icc

theorem aesm_cnormSq {α β : Type*} [Fintype β] [MeasurableSpace α] {μ : Measure α} {f : α → β → ℂ}
    (hf : ∀ b, AEStronglyMeasurable (fun x => f x b) μ) : AEStronglyMeasurable (fun x => cnormSq (f x)) μ := by
  unfold cnormSq
  exact Finset.aestronglyMeasurable_fun_sum _ fun b _ => ((hf b).norm).pow 2

theorem aesm_curlOfGrad' {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → Fin 3 × Fin 3 → ℂ}
    (hf : ∀ b, AEStronglyMeasurable (fun x => f x b) μ) (i : Fin 3) :
    AEStronglyMeasurable (fun x => curlOfGrad (f x) i) μ := by
  unfold curlOfGrad
  exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => Finset.aestronglyMeasurable_fun_sum _ fun l _ =>
    aestronglyMeasurable_const.mul (hf (l, j))

theorem aesm_curlSecond {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → Fin 3 × Fin 3 × Fin 3 → ℂ} (hf : ∀ b, AEStronglyMeasurable (fun x => f x b) μ) (il : Fin 3 × Fin 3) :
    AEStronglyMeasurable (fun x => curlGradOfSecondDeriv (f x) il) μ := by
  unfold curlGradOfSecondDeriv
  exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => Finset.aestronglyMeasurable_fun_sum _ fun l _ =>
    aestronglyMeasurable_const.mul (hf (l, il.2, j))

theorem aesm_modeVel_plane {v : ℝ → Space → Space}
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume) (ξ : ℤ × ℤ) (a : Fin 3) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => modeVel ξ v 0 (planePoint p) a) (volume.restrict halfPlane) := by
  have h := (TailBand.Internal.AngularPlane.aestronglyMeasurable_orbitAverage hv ξ
    (fun φ x => axialRot (-φ) x a) (Internal.NegativeModeSum.continuous_rotCoord a)).const_mul
      (1 / (2 * Real.pi) : ℂ)
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [modeVel, modeAverage, Coercive.Internal.ModeRotation.expFactor, zero_add]

theorem aesm_modeGrad_plane {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (ξ : ℤ × ℤ) (ab : Fin 3 × Fin 3) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => modeGrad ξ G 0 (planePoint p) ab) (volume.restrict halfPlane) := by
  have hc : Continuous (fun q : ℝ × (Space →L[ℝ] Space) =>
      axialRot (-q.1) (q.2 (axialRot q.1 (unitVector ab.2))) ab.1) := by
    unfold axialRot
    fun_prop
  have h := (TailBand.Internal.AngularPlane.aestronglyMeasurable_orbitAverage hG ξ
    (fun φ (A : Space →L[ℝ] Space) => axialRot (-φ) (A (axialRot φ (unitVector ab.2))) ab.1) hc).const_mul
      (1 / (2 * Real.pi) : ℂ)
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [modeGrad, modeAverage, Coercive.Internal.ModeRotation.expFactor, zero_add]

theorem aesm_modeSecond_plane {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) (ξ : ℤ × ℤ)
    (ijl : Fin 3 × Fin 3 × Fin 3) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => modeSecondDeriv ξ H 0 (planePoint p) ijl) (volume.restrict halfPlane) := by
  have hc : Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
      axialRot (-q.1) (q.2 (axialRot q.1 (unitVector ijl.2.1)) (axialRot q.1 (unitVector ijl.2.2))) ijl.1) := by
    unfold axialRot
    fun_prop
  have h := (TailBand.Internal.AngularPlane.aestronglyMeasurable_orbitAverage hH ξ
    (fun φ (B : Space →L[ℝ] Space →L[ℝ] Space) =>
      axialRot (-φ) (B (axialRot φ (unitVector ijl.2.1)) (axialRot φ (unitVector ijl.2.2))) ijl.1) hc).const_mul
      (1 / (2 * Real.pi) : ℂ)
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [modeSecondDeriv, modeAverage, Coercive.Internal.ModeRotation.expFactor, zero_add]

theorem sum_pairVec_sq (s : Fin 3 → Fin 3 → ℂ) (w : Fin 3 → ℂ) :
    ∑ j, ‖pairVec s w j‖ ^ 2 = (∑ a, ∑ b, ‖s a b‖ ^ 2) + ∑ a, ‖w a‖ ^ 2 := by
  simp [Fin.sum_univ_succ, pairVec]
  ring

theorem bandSum_eq (m : ℕ) (ι : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (p : ℝ × ℝ) :
    ∑ j, ‖pairVec (gradArray m ι G p) (velArray m ι v p) j‖ ^ 2 =
      cnormSq (modeGrad (labelHarmonic m ι) G 0 (planePoint p))
        + cnormSq (modeVel (labelHarmonic m ι) v 0 (planePoint p)) := by
  rw [sum_pairVec_sq]
  simp only [cnormSq, Fintype.sum_prod_type, gradArray, gradAt, labelGrad, velArray, velAt, labelVel]

theorem aesm_pairVec {μ : Measure (ℝ × ℝ)} {s : ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {w : ℝ × ℝ → Fin 3 → ℂ}
    (hs : ∀ a b, AEStronglyMeasurable (fun p => s p a b) μ) (hw : ∀ a, AEStronglyMeasurable (fun p => w p a) μ)
    (j : Fin 12) : AEStronglyMeasurable (fun p => pairVec (s p) (w p) j) μ := by
  by_cases h : j.val < 9
  · simp only [pairVec, dif_pos h]
    exact hs _ _
  · simp only [pairVec, dif_neg h]
    exact hw _

theorem profile_point_le {B : CellBox} {p : ℝ × ℝ} (hp : p ∈ B.rect ∩ halfPlane) (a : ℝ) {b : ℝ}
    (hb : 0 ≤ b) :
    ENNReal.ofReal (p.1 * (a + b)) ≤ ENNReal.ofReal (a * p.1)
      + ENNReal.ofReal (B.r₂ ^ 2 + B.z₂ ^ 2) * ENNReal.ofReal (b / (p.1 ^ 2 + p.2 ^ 2) * p.1) := by
  obtain ⟨⟨⟨hr1, hr2⟩, hz1, hz2⟩, hr0, hz0⟩ := hp
  have hr0' : (0 : ℝ) < p.1 := hr0
  have hz0' : (0 : ℝ) < p.2 := hz0
  have hρ : 0 < p.1 ^ 2 + p.2 ^ 2 := by positivity
  have hρle : p.1 ^ 2 + p.2 ^ 2 ≤ B.r₂ ^ 2 + B.z₂ ^ 2 :=
    add_le_add (pow_le_pow_left₀ hr0'.le hr2 2) (pow_le_pow_left₀ hz0'.le hz2 2)
  have hq : 0 ≤ b / (p.1 ^ 2 + p.2 ^ 2) * p.1 := by positivity
  have key : b * p.1 ≤ (B.r₂ ^ 2 + B.z₂ ^ 2) * (b / (p.1 ^ 2 + p.2 ^ 2) * p.1) := by
    have e : b * p.1 = (p.1 ^ 2 + p.2 ^ 2) * (b / (p.1 ^ 2 + p.2 ^ 2) * p.1) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hρle hq
  calc ENNReal.ofReal (p.1 * (a + b)) = ENNReal.ofReal (a * p.1 + b * p.1) := by
        congr 1
        ring
    _ ≤ ENNReal.ofReal (a * p.1) + ENNReal.ofReal (b * p.1) := ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (a * p.1) + ENNReal.ofReal ((B.r₂ ^ 2 + B.z₂ ^ 2) * (b / (p.1 ^ 2 + p.2 ^ 2) * p.1)) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal key)
    _ = _ := by rw [ENNReal.ofReal_mul (p := B.r₂ ^ 2 + B.z₂ ^ 2) (by positivity)]

theorem profile_bound {m : ℕ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)} {B : CellBox}
    (hB : IsCellBox B) (ι : ℤ × ℤ)
    (hGm : AEMeasurable (fun p => cnormSq (modeGrad (labelHarmonic m ι) G 0 (planePoint p)))
      (volume.restrict halfPlane)) :
    ∫⁻ p in B.rect, ENNReal.ofReal (p.1 * ∑ j, ‖pairVec (gradArray m ι G p) (velArray m ι v p) j‖ ^ 2)
      ≤ (∫⁻ p in halfPlane, ENNReal.ofReal (cnormSq (modeGrad (labelHarmonic m ι) G 0 (planePoint p)) * p.1))
        + ENNReal.ofReal (B.r₂ ^ 2 + B.z₂ ^ 2) * ∫⁻ p in halfPlane,
          ENNReal.ofReal (cnormSq (modeVel (labelHarmonic m ι) v 0 (planePoint p)) / (p.1 ^ 2 + p.2 ^ 2) * p.1) := by
  have hle : B.rect ≤ᵐ[volume] (B.rect ∩ halfPlane : Set (ℝ × ℝ)) := by
    have h := ae_le_set_inter (Filter.EventuallyLE.refl (ae volume) B.rect) (rect_ae_le_halfPlane hB)
    rwa [Set.inter_self] at h
  calc ∫⁻ p in B.rect, ENNReal.ofReal (p.1 * ∑ j, ‖pairVec (gradArray m ι G p) (velArray m ι v p) j‖ ^ 2)
      ≤ ∫⁻ p in B.rect ∩ halfPlane,
          ENNReal.ofReal (p.1 * ∑ j, ‖pairVec (gradArray m ι G p) (velArray m ι v p) j‖ ^ 2) :=
        lintegral_mono_set' hle
    _ ≤ ∫⁻ p in B.rect ∩ halfPlane,
          (ENNReal.ofReal (cnormSq (modeGrad (labelHarmonic m ι) G 0 (planePoint p)) * p.1)
            + ENNReal.ofReal (B.r₂ ^ 2 + B.z₂ ^ 2) * ENNReal.ofReal
              (cnormSq (modeVel (labelHarmonic m ι) v 0 (planePoint p)) / (p.1 ^ 2 + p.2 ^ 2) * p.1)) := by
        refine setLIntegral_mono' ((measurableSet_rect B).inter Bridge.Internal.StretchMeanParts.measurableSet_halfPlane)
          fun p hp => ?_
        rw [bandSum_eq]
        exact profile_point_le hp _ (Internal.FormNegative.cnormSq_nonneg_local _)
    _ ≤ ∫⁻ p in halfPlane,
          (ENNReal.ofReal (cnormSq (modeGrad (labelHarmonic m ι) G 0 (planePoint p)) * p.1)
            + ENNReal.ofReal (B.r₂ ^ 2 + B.z₂ ^ 2) * ENNReal.ofReal
              (cnormSq (modeVel (labelHarmonic m ι) v 0 (planePoint p)) / (p.1 ^ 2 + p.2 ^ 2) * p.1)) :=
        lintegral_mono_set Set.inter_subset_right
    _ = _ := by
        have hm1 : AEMeasurable (fun p : ℝ × ℝ =>
            ENNReal.ofReal (cnormSq (modeGrad (labelHarmonic m ι) G 0 (planePoint p)) * p.1))
            (volume.restrict halfPlane) := (hGm.mul measurable_fst.aemeasurable).ennreal_ofReal
        rw [lintegral_add_left' hm1,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem profile_regular {m : ℕ} (hm : 1 ≤ m) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {B : CellBox} (hB : IsCellBox B) :
    (∀ ι, (∀ j, AEStronglyMeasurable (fun p => pairVec (gradArray m ι G p) (velArray m ι v p) j)
        (volume.restrict B.rect)) ∧
      IntegrableOn (fun p => p.1 * ∑ j, ‖pairVec (gradArray m ι G p) (velArray m ι v p) j‖ ^ 2) B.rect) ∧
    Summable (fun ι : ℤ × ℤ =>
      ∫ p in B.rect, p.1 * ∑ j, ‖pairVec (gradArray m ι G p) (velArray m ι v p) j‖ ^ 2) := by
  have hac := restrict_ac (rect_ae_le_halfPlane hB)
  have hcomp : ∀ ι j, AEStronglyMeasurable (fun p => pairVec (gradArray m ι G p) (velArray m ι v p) j)
      (volume.restrict B.rect) := fun ι j =>
    aesm_pairVec (s := fun p => gradArray m ι G p) (w := fun p => velArray m ι v p)
      (fun a b => (aesm_modeGrad_plane hv.measurable_gradient (labelHarmonic m ι) (a, b)).mono_ac hac)
      (fun a => (aesm_modeVel_plane hv.measurable_velocity (labelHarmonic m ι) a).mono_ac hac) j
  have hS : ∀ ι, AEStronglyMeasurable
      (fun p : ℝ × ℝ => p.1 * ∑ j, ‖pairVec (gradArray m ι G p) (velArray m ι v p) j‖ ^ 2)
      (volume.restrict B.rect) := fun ι =>
    measurable_fst.aestronglyMeasurable.mul
      (Finset.aestronglyMeasurable_fun_sum _ fun j _ => ((hcomp ι j).norm).pow 2)
  have hnn : ∀ ι, 0 ≤ᵐ[volume.restrict B.rect]
      (fun p : ℝ × ℝ => p.1 * ∑ j, ‖pairVec (gradArray m ι G p) (velArray m ι v p) j‖ ^ 2) := fun ι =>
    (ae_restrict_iff' (measurableSet_rect B)).2 (Filter.Eventually.of_forall fun p hp =>
      mul_nonneg (hB.r_order.1.trans hp.1.1) (Finset.sum_nonneg fun j _ => sq_nonneg _))
  have hGm : ∀ ι, AEMeasurable (fun p => cnormSq (modeGrad (labelHarmonic m ι) G 0 (planePoint p)))
      (volume.restrict halfPlane) := fun ι =>
    (aesm_cnormSq fun ab => aesm_modeGrad_plane hv.measurable_gradient (labelHarmonic m ι) ab).aemeasurable
  have hA := Internal.FormNegative.gradient_sum_lt_top m hm hv
  have hV := Internal.FormNegative.velocity_inverse_sum_lt_top m hm hv
  have htot : ∑' ι : ℤ × ℤ, ∫⁻ p in B.rect,
      ENNReal.ofReal (p.1 * ∑ j, ‖pairVec (gradArray m ι G p) (velArray m ι v p) j‖ ^ 2) < ⊤ := by
    calc _ ≤ ∑' ι : ℤ × ℤ, ((∫⁻ p in halfPlane,
            ENNReal.ofReal (cnormSq (modeGrad (labelHarmonic m ι) G 0 (planePoint p)) * p.1))
          + ENNReal.ofReal (B.r₂ ^ 2 + B.z₂ ^ 2) * ∫⁻ p in halfPlane,
            ENNReal.ofReal (cnormSq (modeVel (labelHarmonic m ι) v 0 (planePoint p)) / (p.1 ^ 2 + p.2 ^ 2) * p.1)) :=
          ENNReal.tsum_le_tsum fun ι => profile_bound hB ι (hGm ι)
      _ = (∑' ι : ℤ × ℤ, ∫⁻ p in halfPlane,
            ENNReal.ofReal (cnormSq (modeGrad (labelHarmonic m ι) G 0 (planePoint p)) * p.1))
          + ENNReal.ofReal (B.r₂ ^ 2 + B.z₂ ^ 2) * ∑' ι : ℤ × ℤ, ∫⁻ p in halfPlane,
            ENNReal.ofReal (cnormSq (modeVel (labelHarmonic m ι) v 0 (planePoint p)) / (p.1 ^ 2 + p.2 ^ 2) * p.1) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hA, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hV⟩
  have hfin : ∀ ι : ℤ × ℤ, ∫⁻ p in B.rect,
      ENNReal.ofReal (p.1 * ∑ j, ‖pairVec (gradArray m ι G p) (velArray m ι v p) j‖ ^ 2) < ⊤ :=
    fun ι => lt_of_le_of_lt (ENNReal.le_tsum ι) htot
  refine ⟨fun ι => ⟨hcomp ι, hS ι, (hasFiniteIntegral_iff_ofReal (hnn ι)).2 (hfin ι)⟩, ?_⟩
  have e : (fun ι : ℤ × ℤ => ∫ p in B.rect, p.1 * ∑ j, ‖pairVec (gradArray m ι G p) (velArray m ι v p) j‖ ^ 2)
      = fun ι => (∫⁻ p in B.rect,
          ENNReal.ofReal (p.1 * ∑ j, ‖pairVec (gradArray m ι G p) (velArray m ι v p) j‖ ^ 2)).toReal :=
    funext fun ι => integral_eq_lintegral_of_nonneg_ae (hnn ι) (hS ι)
  rw [e]
  exact ENNReal.summable_toReal htot.ne

theorem measurable_modeDensity_joint {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ)
    (h : HarmonicBounds) (w : Space → ℝ) (ξ : ℤ × ℤ)
    (s1 : Measurable fun y => m.shareHat h ξ y) (s2 : Measurable fun y => m.coefA P h ξ y)
    (s3 : Measurable fun y => m.coefAA h w ξ y) (s4 : Measurable fun y => m.coefB P h ξ y)
    (hD : Measurable (m.convD (m.classOf ξ))) (hZ : Measurable (m.convZ (m.classOf ξ))) :
    Measurable (fun t : Space × ℝ × ℝ × ℝ × ℝ × ℝ =>
      m.modeDensity P h w ξ t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2) := by
  unfold PieceWeights.modeDensity
  fun_prop

theorem aesm_labelDensity_half {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    {q : Fin k → ℝ} {w₀ e₁ e₂ e₃ : ℝ}
    (hadm : CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn D.given
      D.givenHess w₀ e₁ e₂ e₃)
    (hb : Bridge.HasMeasurableBoundData (D.pieces q) (D.bounds q)) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hvm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hGm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hHm : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) (ι : ℤ × ℤ) :
    AEStronglyMeasurable (D.labelDensity q v G H ι) (volume.restrict halfPlane) := by
  obtain ⟨s1, s2, s3, s4⟩ := Bridge.Internal.ModeDensityBridge.measurable_coefs (D.pieces q) (D.cert.period q)
    (D.bounds q) D.cert.weightFn hadm hb (labelHarmonic D.azimuthOrder ι)
  have hD : Measurable ((D.pieces q).convD ((D.pieces q).classOf (labelHarmonic D.azimuthOrder ι))) :=
    (hadm.convD_smooth _).continuous.measurable
  have hZ : Measurable ((D.pieces q).convZ ((D.pieces q).classOf (labelHarmonic D.azimuthOrder ι))) :=
    (hadm.convZ_smooth _).continuous.measurable
  have J := measurable_modeDensity_joint (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn
    (labelHarmonic D.azimuthOrder ι) s1 s2 s3 s4 hD hZ
  have X2 : AEMeasurable (fun p => Real.sqrt (cnormSq (modeSecondDeriv (labelHarmonic D.azimuthOrder ι) H 0 (planePoint p))))
      (volume.restrict halfPlane) :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable
      (aesm_cnormSq fun b => aesm_modeSecond_plane hHm _ b)).aemeasurable
  have Xc : AEMeasurable (fun p => Real.sqrt (cnormSq (curlGradOfSecondDeriv
      (modeSecondDeriv (labelHarmonic D.azimuthOrder ι) H 0 (planePoint p))))) (volume.restrict halfPlane) :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable
      (aesm_cnormSq fun il => aesm_curlSecond (fun b => aesm_modeSecond_plane hHm _ b) il)).aemeasurable
  have X1 : AEMeasurable (fun p => Real.sqrt (cnormSq (modeGrad (labelHarmonic D.azimuthOrder ι) G 0 (planePoint p))))
      (volume.restrict halfPlane) :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable
      (aesm_cnormSq fun b => aesm_modeGrad_plane hGm _ b)).aemeasurable
  have Xo : AEMeasurable (fun p => Real.sqrt (cnormSq (curlOfGrad
      (modeGrad (labelHarmonic D.azimuthOrder ι) G 0 (planePoint p))))) (volume.restrict halfPlane) :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable
      (aesm_cnormSq fun i => aesm_curlOfGrad' (fun b => aesm_modeGrad_plane hGm _ b) i)).aemeasurable
  have X0 : AEMeasurable (fun p => Real.sqrt (cnormSq (modeVel (labelHarmonic D.azimuthOrder ι) v 0 (planePoint p))))
      (volume.restrict halfPlane) :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable
      (aesm_cnormSq fun b => aesm_modeVel_plane hvm _ b)).aemeasurable
  have hT := J.comp_aemeasurable (measurable_planePoint.aemeasurable.prodMk
    (X2.prodMk (Xc.prodMk (X1.prodMk (Xo.prodMk X0)))))
  exact hT.aestronglyMeasurable

theorem aesm_orbit_stretch {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {B : ℝ}
    (hW : CoerciveWeak.IsWeakSecondDerivState W HW B) {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hvm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hGm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) :
    AEStronglyMeasurable (fun w : ((ℝ × ℝ) × ℝ) × ℝ =>
        CoerciveWeak.stretchFormWith W HW v G w.1.2 (axialRot w.2 (planePoint w.1.1)))
      (((volume.restrict halfPlane).prod (volume : Measure ℝ)).prod (volume : Measure ℝ)) := by
  have h1 : AEStronglyMeasurable (fun z : ℝ × Space => CoerciveWeak.stretchFormWith W HW v G z.1 z.2) volume :=
    (CoerciveWeak.Internal.AbsorbStep.aem_stretchFormWith W v G HW hW hvm hGm).aestronglyMeasurable
  have h2 := h1.comp_quasiMeasurePreserving TailBand.quasiMeasurePreserving_orbitPlane
  exact h2

theorem aesm_meanStretch {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) {B : ℝ}
    (hW : CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hvm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hGm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) {S : Set (ℝ × ℝ)}
    (hS : S ≤ᵐ[volume] halfPlane) :
    AEStronglyMeasurable (D.meanStretch v G) (volume.restrict S) := by
  have h0 := aesm_orbit_stretch hW hvm hGm
  have hac : ((volume.restrict S).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))).prod
      (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))
      ≪ ((volume.restrict halfPlane).prod (volume : Measure ℝ)).prod (volume : Measure ℝ) :=
    ((restrict_ac hS).prod Measure.restrict_le_self.absolutelyContinuous).prod
      Measure.restrict_le_self.absolutelyContinuous
  have h1 := (h0.mono_ac hac).integral_prod_right'
  have h2 := h1.integral_prod_right'
  refine (h2.const_mul (1 / (2 * Real.pi))).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [CellLayerData.meanStretch, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

theorem aesm_stretch_integrand {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {B : ℝ} (hW : CoerciveWeak.IsWeakSecondDerivState W HW B) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hvm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hGm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) {S : Set (ℝ × ℝ)}
    (hS : S ≤ᵐ[volume] halfPlane) :
    AEStronglyMeasurable (fun z : (ℝ × ℝ) × ℝ × ℝ =>
        CoerciveWeak.stretchFormWith W HW v G z.2.1 (axialRot z.2.2 (planePoint z.1)))
      ((volume.restrict S).prod
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))) := by
  have h0 := aesm_orbit_stretch hW hvm hGm
  have hmp := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (volume.restrict halfPlane) (volume : Measure ℝ) (volume : Measure ℝ))
  have h1 := h0.comp_measurePreserving hmp
  have hac : (volume.restrict S).prod
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))
      ≪ (volume.restrict halfPlane).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (restrict_ac hS).prod (Measure.restrict_le_self.absolutelyContinuous.prod
      Measure.restrict_le_self.absolutelyContinuous)
  exact (h1.mono_ac hac).congr (Filter.Eventually.of_forall fun z => rfl)

theorem continuous_curlVec : Continuous (fun A : Space →L[ℝ] Space => curlVec A) := by
  unfold curlVec
  fun_prop

theorem given_modes_measurable {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {B : ℝ} (hW : CoerciveWeak.IsWeakSecondDerivState W HW B) (m : ℕ) {S : Set (ℝ × ℝ)}
    (hS : S ≤ᵐ[volume] halfPlane) (α : ℤ × ℤ) :
    (∀ a b, AEStronglyMeasurable (fun p => labelGrad m α (gradField W) p (a, b)) (volume.restrict S)) ∧
    (∀ a b c, AEStronglyMeasurable (fun p => labelHess m α HW p (a, b, c)) (volume.restrict S)) ∧
    (∀ a, AEStronglyMeasurable (fun p => labelVel m α W p a) (volume.restrict S)) ∧
    (∀ a, AEStronglyMeasurable (fun p => labelVel m α (vorticityOf W) p a) (volume.restrict S)) := by
  have hac := restrict_ac hS
  have hd : Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
    CoerciveWeak.Internal.AbsorbStep.continuous_fderiv_slice_of_one hW.smooth
  have hg : AEStronglyMeasurable (fun z : ℝ × Space => gradField W z.1 z.2) volume := hd.aestronglyMeasurable
  have hv : AEStronglyMeasurable (fun z : ℝ × Space => W z.1 z.2) volume :=
    hW.smooth.continuous.aestronglyMeasurable
  have hc : AEStronglyMeasurable (fun z : ℝ × Space => vorticityOf W z.1 z.2) volume :=
    (continuous_curlVec.comp hd).aestronglyMeasurable
  exact ⟨fun a b => (aesm_modeGrad_plane hg _ (a, b)).mono_ac hac,
    fun a b c => (aesm_modeSecond_plane hW.secondDeriv_measurable _ (a, b, c)).mono_ac hac,
    fun a => (aesm_modeVel_plane hv _ a).mono_ac hac,
    fun a => (aesm_modeVel_plane hc _ a).mono_ac hac⟩

theorem density_measurable_on {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    {q : Fin k → ℝ} {w₀ e₁ e₂ e₃ : ℝ}
    (hadm : CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn D.given
      D.givenHess w₀ e₁ e₂ e₃)
    (hb : Bridge.HasMeasurableBoundData (D.pieces q) (D.bounds q)) {B : ℝ}
    (hW : CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B) {Γ : Set Symmetry} {P : ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {S : Set (ℝ × ℝ)} (hS : S ≤ᵐ[volume] halfPlane) :
    (∀ ι, AEStronglyMeasurable (D.labelDensity q v G H ι) (volume.restrict S)) ∧
      AEStronglyMeasurable (D.meanStretch v G) (volume.restrict S) :=
  ⟨fun ι => (aesm_labelDensity_half D hadm hb hv.measurable_velocity hv.measurable_gradient
      hv.measurable_secondDeriv ι).mono_ac (restrict_ac hS),
    aesm_meanStretch D hW hv.measurable_velocity hv.measurable_gradient hS⟩

theorem inter_halfPlane_ae_le (T : Set (ℝ × ℝ)) : (T ∩ halfPlane : Set (ℝ × ℝ)) ≤ᵐ[volume] halfPlane :=
  Filter.Eventually.of_forall fun _ hp => hp.2

end Internal.TrueRegular

end Assembly

end CertCell

end Breakdown
