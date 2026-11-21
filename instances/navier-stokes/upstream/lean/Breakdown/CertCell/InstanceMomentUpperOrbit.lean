import Breakdown.CertCell.InstanceGeneratorForm
import Breakdown.CertCell.TailAngularPlane
import Breakdown.CertCell.StretchMeanIntegral

open scoped ENNReal NNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.Instance

open Breakdown Breakdown.CertCell
open Breakdown.CellCert.CellAnalysis (CellBox IsCellBox cylRadius cylHeight radialUnit angularUnit axialUnit)

namespace Internal.MomentUpper

def openHalf : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)

def orbitMeasure : Measure ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (volume.restrict openHalf).prod ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi))))

def orbit (w : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ × Space := (w.2.1, axialRot w.2.2 (planePoint w.1))

def periodMeasure : Measure (ℝ × Space) := (volume.restrict (Icc (0 : ℝ) 1)).prod volume

theorem measurable_orbit : Measurable orbit :=
  Bridge.Internal.StretchMeanParts.measurable_orbit

theorem measurableSet_openHalf : MeasurableSet openHalf := measurableSet_Ioi.prod MeasurableSet.univ

theorem axialRot_add_two_pi (φ : ℝ) (y : Space) : axialRot (φ + 2 * Real.pi) y = axialRot φ y := by
  simp only [axialRot, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem lintegral_orbit (h : ℝ × Space → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ z, h z ∂periodMeasure = ∫⁻ w, ENNReal.ofReal w.1.1 * h (orbit w) ∂orbitMeasure := by
  have hF : Measurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal w.1.1 * h (orbit w)) :=
    (ENNReal.measurable_ofReal.comp measurable_fst.fst).mul (hh.comp measurable_orbit)
  have hin : Measurable (fun x : (ℝ × ℝ) × ℝ =>
      ∫⁻ φ in Ioc 0 (2 * Real.pi), ENNReal.ofReal x.1.1 * h (orbit (x.1, (x.2, φ)))) :=
    (hF.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))).lintegral_prod_right'
  have hR : ∫⁻ w, ENNReal.ofReal w.1.1 * h (orbit w) ∂orbitMeasure =
      ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ p in openHalf, ∫⁻ φ in Ioc 0 (2 * Real.pi),
        ENNReal.ofReal p.1 * h (orbit (p, (τ, φ))) := by
    unfold orbitMeasure
    rw [lintegral_prod _ hF.aemeasurable]
    have e1 : ∀ p : ℝ × ℝ, ∫⁻ s, ENNReal.ofReal (p, s).1.1 * h (orbit (p, s))
        ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi)))) =
        ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ φ in Ioc 0 (2 * Real.pi), ENNReal.ofReal p.1 * h (orbit (p, (τ, φ))) :=
      fun p => lintegral_prod _ (hF.comp measurable_prodMk_left).aemeasurable
    rw [lintegral_congr e1]
    exact lintegral_lintegral_swap hin.aemeasurable
  rw [hR]
  unfold periodMeasure
  rw [lintegral_prod _ hh.aemeasurable, Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := 1)).symm]
  refine lintegral_congr fun τ => ?_
  rw [TailBand.lintegral_eq_cylindrical (fun y => h (τ, y)) (hh.comp measurable_prodMk_left)]
  unfold openHalf
  refine lintegral_congr fun p => ?_
  rw [Bridge.Internal.StretchMeanParts.lintegral_angle_shift _ (fun φ => by
    simp only [axialRot_add_two_pi])]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rfl

def orbitDensity (w : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ≥0 := Real.toNNReal w.1.1

theorem measurable_orbitDensity : Measurable orbitDensity :=
  measurable_real_toNNReal.comp measurable_fst.fst

theorem map_orbit :
    Measure.map orbit (orbitMeasure.withDensity fun w => (orbitDensity w : ℝ≥0∞)) = periodMeasure := by
  ext s hs
  rw [Measure.map_apply measurable_orbit hs, withDensity_apply _ (measurable_orbit hs),
    ← lintegral_indicator_one hs, lintegral_orbit _ (measurable_one.indicator hs),
    ← lintegral_indicator (measurable_orbit hs)]
  refine lintegral_congr fun w => ?_
  by_cases hw : orbit w ∈ s
  · have hw' : w ∈ orbit ⁻¹' s := hw
    rw [indicator_of_mem hw', indicator_of_mem hw]
    simp [orbitDensity, ENNReal.ofReal]
  · have hw' : w ∉ orbit ⁻¹' s := hw
    rw [indicator_of_notMem hw', indicator_of_notMem hw, mul_zero]

theorem ae_orbit_pos : ∀ᵐ w ∂orbitMeasure, 0 < w.1.1 := by
  have h := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict openHalf)
    (ν := (volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi))))).ae
    (ae_restrict_mem measurableSet_openHalf)
  filter_upwards [h] with w hw
  exact hw.1

theorem orbitMeasure_ac :
    orbitMeasure ≪ orbitMeasure.withDensity fun w => (orbitDensity w : ℝ≥0∞) := by
  refine withDensity_absolutelyContinuous' measurable_orbitDensity.coe_nnreal_ennreal.aemeasurable ?_
  filter_upwards [ae_orbit_pos] with w hw
  simp [orbitDensity, hw]

theorem integral_orbit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℝ × Space → E}
    (hg : Integrable g periodMeasure) :
    Integrable (fun w => w.1.1 • g (orbit w)) orbitMeasure ∧
      ∫ z, g z ∂periodMeasure = ∫ w, w.1.1 • g (orbit w) ∂orbitMeasure := by
  rw [← map_orbit] at hg ⊢
  have hm := hg.aestronglyMeasurable
  have he : (fun w => (orbitDensity w : ℝ≥0) • g (orbit w)) =ᵐ[orbitMeasure] fun w => w.1.1 • g (orbit w) := by
    filter_upwards [ae_orbit_pos] with w hw
    rw [NNReal.smul_def, orbitDensity, Real.coe_toNNReal _ hw.le]
  refine ⟨?_, ?_⟩
  · rw [integrable_map_measure hm measurable_orbit.aemeasurable,
      integrable_withDensity_iff_integrable_smul measurable_orbitDensity] at hg
    exact hg.congr he
  · rw [integral_map measurable_orbit.aemeasurable hm,
      integral_withDensity_eq_integral_smul measurable_orbitDensity]
    exact integral_congr_ae he

theorem aestronglyMeasurable_orbit {X : Type*} [TopologicalSpace X] {g : ℝ × Space → X}
    (hg : AEStronglyMeasurable g periodMeasure) : AEStronglyMeasurable (fun w => g (orbit w)) orbitMeasure := by
  rw [← map_orbit] at hg
  exact (hg.comp_aemeasurable measurable_orbit.aemeasurable).mono_ac orbitMeasure_ac

end Internal.MomentUpper

namespace Internal.MomentUpper

theorem orbit_coord0 (p : ℝ × ℝ) (φ : ℝ) : axialRot φ (planePoint p) 0 = p.1 * Real.cos φ := by
  simp [axialRot, planePoint, CellCert.CellAnalysis.cylPoint, unitVector, mul_comm]

theorem orbit_coord1 (p : ℝ × ℝ) (φ : ℝ) : axialRot φ (planePoint p) 1 = p.1 * Real.sin φ := by
  simp [axialRot, planePoint, CellCert.CellAnalysis.cylPoint, unitVector]; ring

theorem orbit_coord2 (p : ℝ × ℝ) (φ : ℝ) : axialRot φ (planePoint p) 2 = p.2 := by
  simp [axialRot, planePoint, CellCert.CellAnalysis.cylPoint, unitVector]

theorem pointPlane_orbit {p : ℝ × ℝ} (hp : 0 ≤ p.1) (φ : ℝ) : pointPlane (axialRot φ (planePoint p)) = p := by
  unfold pointPlane
  rw [orbit_coord0, orbit_coord1, orbit_coord2]
  have e : (p.1 * Real.cos φ) ^ 2 + (p.1 * Real.sin φ) ^ 2 = p.1 ^ 2 := by
    linear_combination p.1 ^ 2 * Real.cos_sq_add_sin_sq φ
  rw [e, Real.sqrt_sq hp]

theorem pointAngle_orbit {p : ℝ × ℝ} (hp : 0 < p.1) (φ : ℝ) :
    ∃ k : ℤ, pointAngle (axialRot φ (planePoint p)) = φ - k * (2 * Real.pi) := by
  refine ⟨toIocDiv Real.two_pi_pos (-Real.pi) φ, ?_⟩
  unfold pointAngle
  rw [orbit_coord0, orbit_coord1]
  have e : ((p.1 * Real.cos φ : ℝ) : ℂ) + ((p.1 * Real.sin φ : ℝ) : ℂ) * Complex.I =
      (p.1 : ℂ) * (Complex.cos φ + Complex.sin φ * Complex.I) := by
    push_cast; ring
  rw [e, Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod hp, ← self_sub_toIocDiv_zsmul, zsmul_eq_mul]

theorem frameUnit_sub (φ : ℝ) (k : ℤ) (c : Fin 3) : frameUnit (φ - k * (2 * Real.pi)) c = frameUnit φ c := by
  fin_cases c <;>
    simp [frameUnit, radialUnit, angularUnit, Real.cos_sub_int_mul_two_pi, Real.sin_sub_int_mul_two_pi]

theorem labelPhase_sub (m : ℕ) (κ : ℤ × ℤ) (σ φ : ℝ) (k : ℤ) :
    labelPhase m κ σ (φ - k * (2 * Real.pi)) = labelPhase m κ σ φ := by
  unfold labelPhase
  have e : (((2 * Real.pi * (labelTime κ : ℝ) * σ + (labelAzimuth m κ : ℝ) * (φ - k * (2 * Real.pi)) : ℝ) : ℂ)
      * Complex.I) = (((2 * Real.pi * (labelTime κ : ℝ) * σ + (labelAzimuth m κ : ℝ) * φ : ℝ) : ℂ) * Complex.I)
        - ((labelAzimuth m κ * k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [e, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

theorem rot_neg_coord (φ : ℝ) (v : Space) (c : Fin 3) :
    axialRot (-φ) v c = inner ℝ v (frameUnit φ c) := by
  fin_cases c <;>
    simp [axialRot, frameUnit, radialUnit, angularUnit, axialUnit, unitVector, inner_add_right,
      EuclideanSpace.inner_single_right]

theorem norm_frameUnit (θ : ℝ) (c : Fin 3) : ‖frameUnit θ c‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  fin_cases c <;>
    simp [frameUnit, radialUnit, angularUnit, axialUnit, Fin.sum_univ_three, Real.cos_sq_add_sin_sq,
      Real.sin_sq_add_cos_sq]

theorem norm_labelPhase (m : ℕ) (κ : ℤ × ℤ) (σ θ : ℝ) : ‖labelPhase m κ σ θ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem conj_labelPhase (m : ℕ) (κ : ℤ × ℤ) (σ θ : ℝ) :
    starRingEnd ℂ (labelPhase m κ σ θ) = Complex.exp (-(((2 * Real.pi * ((labelHarmonic m κ).1 : ℝ) * σ +
      ((labelHarmonic m κ).2 : ℝ) * θ : ℝ) : ℂ) * Complex.I)) := by
  unfold labelPhase labelHarmonic
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]

theorem continuous_pointPlane' : Continuous pointPlane := by
  unfold pointPlane; fun_prop

theorem measurable_pointAngle' : Measurable pointAngle := by
  unfold pointAngle; fun_prop

theorem single_smul_unit (i : Fin 3) (x : ℝ) : (EuclideanSpace.single i x : Space) = x • unitVector i := by
  ext j
  by_cases h : j = i <;> simp [unitVector, h]

theorem continuous_frameUnit (c : Fin 3) : Continuous fun θ => frameUnit θ c := by
  fin_cases c <;> simp only [frameUnit, radialUnit, angularUnit, axialUnit, single_smul_unit] <;> fun_prop

theorem continuous_labelPhase (m : ℕ) (κ : ℤ × ℤ) : Continuous fun q : ℝ × ℝ => labelPhase m κ q.1 q.2 := by
  unfold labelPhase; fun_prop

end Internal.MomentUpper

namespace Internal.MomentUpper

def sliceMeasure : Measure (ℝ × ℝ) := (volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi)))

instance : SFinite sliceMeasure := by unfold sliceMeasure; infer_instance

theorem periodMeasure_eq : periodMeasure = volume.restrict (Icc (0 : ℝ) 1 ×ˢ (univ : Set Space)) := by
  rw [periodMeasure, ← Measure.restrict_univ (μ := (volume : Measure Space)), Measure.prod_restrict,
    Measure.volume_eq_prod]

theorem aesm_period {X : Type*} [TopologicalSpace X] {g : ℝ × Space → X} (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable g periodMeasure := by
  rw [periodMeasure_eq]; exact hg.restrict

theorem integrable_sq {F : ℝ → Space → Space} (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) :
    Integrable (fun z : ℝ × Space => ‖F z.1 z.2‖ ^ 2) periodMeasure := by
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => ‖F z.1 z.2‖ ^ 2) periodMeasure :=
    (aesm_period hFm).norm.pow 2
  refine ⟨hm, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => by positivity)]
  unfold periodMeasure
  rw [lintegral_prod (fun z : ℝ × Space => ENNReal.ofReal (‖F z.1 z.2‖ ^ 2))
    (ENNReal.measurable_ofReal.comp_aemeasurable hm.aemeasurable)]
  exact hF2

theorem norm_sq_pointPlane (y : Space) : ‖y‖ ^ 2 = (pointPlane y).1 ^ 2 + (pointPlane y).2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [pointPlane, Real.norm_eq_abs, sq_abs]
  rw [Real.sq_sqrt (by positivity)]

theorem volume_planeSet_lt_top {S : Set (ℝ × ℝ)} (hSb : Bornology.IsBounded S) :
    volume {y : Space | pointPlane y ∈ S} < ⊤ := by
  obtain ⟨R, hR⟩ := hSb.subset_closedBall 0
  refine lt_of_le_of_lt (measure_mono (μ := volume) (t := Metric.closedBall (0 : Space) (2 * R)) ?_)
    measure_closedBall_lt_top
  intro y hy
  have hP : pointPlane y ∈ Metric.closedBall (0 : ℝ × ℝ) R := hR hy
  rw [mem_closedBall_zero_iff] at hP ⊢
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hP
  have h1 : (pointPlane y).1 ^ 2 ≤ R ^ 2 := by
    have h := (norm_fst_le (pointPlane y)).trans hP
    rw [Real.norm_eq_abs] at h
    exact sq_le_sq.2 (by rwa [abs_of_nonneg hR0])
  have h2 : (pointPlane y).2 ^ 2 ≤ R ^ 2 := by
    have h := (norm_snd_le (pointPlane y)).trans hP
    rw [Real.norm_eq_abs] at h
    exact sq_le_sq.2 (by rwa [abs_of_nonneg hR0])
  have h3 : ‖y‖ ^ 2 ≤ (2 * R) ^ 2 := by
    rw [norm_sq_pointPlane]; nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3

theorem measurableSet_planeSet {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) :
    MeasurableSet {y : Space | pointPlane y ∈ S} :=
  continuous_pointPlane'.measurable hS

theorem integrable_planeSet {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) (hSb : Bornology.IsBounded S) :
    Integrable (fun z : ℝ × Space => {y : Space | pointPlane y ∈ S}.indicator (fun _ => (1 : ℝ)) z.2)
      periodMeasure := by
  have hg : Integrable ({y : Space | pointPlane y ∈ S}.indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff (measurableSet_planeSet hS)).2
      (integrableOn_const (volume_planeSet_lt_top hSb).ne)
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc (0 : ℝ) 1)) :=
    integrable_const _
  refine (h1.mul_prod hg).congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [one_mul]

def planeField (m : ℕ) (κ : ℤ × ℤ) (S : Set (ℝ × ℝ)) (ψ : ℝ × ℝ → Fin 3 → ℂ) (σ : ℝ) (y : Space) : Space :=
  Set.indicator {y | pointPlane y ∈ S}
    (fun y => ∑ c : Fin 3, (labelPhase m κ σ (pointAngle y) * ψ (pointPlane y) c).re • frameUnit (pointAngle y) c) y

theorem measurable_planeField (m : ℕ) (κ : ℤ × ℤ) {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    {ψ : ℝ × ℝ → Fin 3 → ℂ} (hψ : ∀ c, Measurable fun p => ψ p c) :
    Measurable (fun z : ℝ × Space => planeField m κ S ψ z.1 z.2) := by
  have hA : Measurable fun z : ℝ × Space => pointAngle z.2 := measurable_pointAngle'.comp measurable_snd
  have hP : Measurable fun z : ℝ × Space => pointPlane z.2 := continuous_pointPlane'.measurable.comp measurable_snd
  have hG : Measurable fun z : ℝ × Space => ∑ c : Fin 3,
      (labelPhase m κ z.1 (pointAngle z.2) * ψ (pointPlane z.2) c).re • frameUnit (pointAngle z.2) c := by
    refine Finset.measurable_sum _ fun c _ => ?_
    refine (Complex.measurable_re.comp (((continuous_labelPhase m κ).measurable.comp
      (measurable_fst.prodMk hA)).mul ((hψ c).comp hP))).smul ((continuous_frameUnit c).measurable.comp hA)
  exact hG.indicator (measurable_snd (measurableSet_planeSet hS))

theorem norm_planeField_le (m : ℕ) (κ : ℤ × ℤ) {S : Set (ℝ × ℝ)} {ψ : ℝ × ℝ → Fin 3 → ℂ} {C : ℝ}
    (hC : ∀ p ∈ S, ∀ c, ‖ψ p c‖ ≤ C) (σ : ℝ) (y : Space) :
    ‖planeField m κ S ψ σ y‖ ≤ 3 * C * {y : Space | pointPlane y ∈ S}.indicator (fun _ => (1 : ℝ)) y := by
  unfold planeField
  by_cases hy : y ∈ {y : Space | pointPlane y ∈ S}
  · rw [indicator_of_mem hy, indicator_of_mem hy, mul_one]
    refine (norm_sum_le _ _).trans ?_
    have hc : ∀ c : Fin 3, ‖(labelPhase m κ σ (pointAngle y) * ψ (pointPlane y) c).re •
        frameUnit (pointAngle y) c‖ ≤ C := by
      intro c
      rw [norm_smul, norm_frameUnit, mul_one, Real.norm_eq_abs]
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_labelPhase, one_mul]
      exact hC _ hy c
    calc ∑ c : Fin 3, ‖(labelPhase m κ σ (pointAngle y) * ψ (pointPlane y) c).re •
          frameUnit (pointAngle y) c‖ ≤ ∑ _c : Fin 3, C := Finset.sum_le_sum fun c _ => hc c
      _ = 3 * C := by simp
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, norm_zero, mul_zero]

end Internal.MomentUpper

end Breakdown.CertCell.Instance
