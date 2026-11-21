import Breakdown.CertCell.AssemblyRowExpansionLowOrbit
import Breakdown.CertCell.CellCalculusStatements
import Breakdown.Cert.CoerciveFrequencySeminormTransportModes
import Breakdown.CertCell.ModeShiftRotate
import Breakdown.CertCell.ModeShiftRotateTensor

open scoped ENNReal NNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.Assembly.Internal.RowIdentity

open Breakdown Breakdown.CertCell CellCalculus CellCert CellCert.CellAnalysis
open Instance.Internal.MomentUpper Coercive.RotationInternal Coercive.FrequencySeminorm.Internal

theorem rotate_column_dot (φ : ℝ) (b : Fin 3) (y : Space) :
    ∑ j : Fin 3, axialRot φ (unitVector b) j * axialRot φ y j = y b := by
  rw [Fin.sum_univ_three, axialRot_apply_zero, axialRot_apply_one, axialRot_apply_two,
    axialRot_apply_zero, axialRot_apply_one, axialRot_apply_two]
  fin_cases b
  · simp [unitVector]
    linear_combination y 0 * Real.cos_sq_add_sin_sq φ
  · simp [unitVector]
    linear_combination y 1 * Real.cos_sq_add_sin_sq φ
  · simp [unitVector]

theorem rotate_vec_eq_zero (φ : ℝ) {w : Fin 3 → ℂ}
    (h : ∀ i : Fin 3, ∑ a : Fin 3, ((axialRot φ (unitVector a) i : ℝ) : ℂ) * w a = 0) : w = 0 := by
  have hcs := Complex.cos_sq_add_sin_sq (φ : ℂ)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [Fin.sum_univ_three, axialRot_apply_zero, axialRot_apply_one, axialRot_apply_two] at h0 h1 h2
  simp [unitVector] at h0 h1 h2
  funext b
  fin_cases b
  · show w 0 = 0
    linear_combination Complex.cos (φ : ℂ) * h0 + Complex.sin (φ : ℂ) * h1 - w 0 * hcs
  · show w 1 = 0
    linear_combination -Complex.sin (φ : ℂ) * h0 + Complex.cos (φ : ℂ) * h1 - w 1 * hcs
  · simpa using h2

theorem transportDefect_rotate {P : ℝ} {ξ : ℤ × ℤ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hvp : IsTimePeriodic v) (hGp : IsTimePeriodic G) (hgp : IsTimePeriodic g) {y : Space}
    (hvi : IntegrableOn (fun q : ℝ × ℝ => v (0 + q.1) (axialRot q.2 y))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (2 * Real.pi)))
    (hGi : ∀ j : Fin 3, IntegrableOn
      (fun q : ℝ × ℝ => G (0 + q.1) (axialRot q.2 y) (axialRot q.2 (unitVector j)))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (2 * Real.pi)))
    (hgi : IntegrableOn (fun q : ℝ × ℝ => g (0 + q.1) (axialRot q.2 y))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (2 * Real.pi)))
    (φ : ℝ) (i : Fin 3) :
    transportDefect P ξ v G g 0 (axialRot φ y) i =
      Complex.exp (((2 * Real.pi * ξ.1 * 0 + ξ.2 * φ : ℝ) : ℂ) * Complex.I) *
        ∑ a : Fin 3, ((axialRot φ (unitVector a) i : ℝ) : ℂ) * transportDefect P ξ v G g 0 y a := by
  have hV := Bridge.modeShiftRotate v hvp ξ 0 0 φ y hvi
  have hG := Bridge.modeShiftRotateTensor.1 G hGp ξ 0 0 φ y hGi
  have hg := Bridge.modeShiftRotate g hgp ξ 0 0 φ y hgi
  rw [add_zero] at hV hG hg
  have hK : ∀ b : Fin 3, ∑ j : Fin 3, ((axialRot φ (unitVector b) j : ℝ) : ℂ) * ((axialRot φ y j : ℝ) : ℂ)
      = ((y b : ℝ) : ℂ) := fun b => by exact_mod_cast rotate_column_dot φ b y
  have hmid : ∑ j : Fin 3, modeGrad ξ G 0 (axialRot φ y) (i, j) * ((axialRot φ y j : ℝ) : ℂ)
      = Complex.exp (((2 * Real.pi * ξ.1 * 0 + ξ.2 * φ : ℝ) : ℂ) * Complex.I) *
        ∑ a : Fin 3, ((axialRot φ (unitVector a) i : ℝ) : ℂ) *
          ∑ b : Fin 3, modeGrad ξ G 0 y (a, b) * ((y b : ℝ) : ℂ) := by
    rw [hG]
    simp only [← hK]
    simp only [Fin.sum_univ_three, Complex.ofReal_mul]
    ring
  simp only [transportDefect]
  rw [hmid]
  simp only [hV, hg, Fin.sum_univ_three]
  ring

theorem transportDefect_eq_zero_of_rotate {P : ℝ} {ξ : ℤ × ℤ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hvp : IsTimePeriodic v) (hGp : IsTimePeriodic G) (hgp : IsTimePeriodic g) {y : Space}
    (hvi : IntegrableOn (fun q : ℝ × ℝ => v (0 + q.1) (axialRot q.2 y))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (2 * Real.pi)))
    (hGi : ∀ j : Fin 3, IntegrableOn
      (fun q : ℝ × ℝ => G (0 + q.1) (axialRot q.2 y) (axialRot q.2 (unitVector j)))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (2 * Real.pi)))
    (hgi : IntegrableOn (fun q : ℝ × ℝ => g (0 + q.1) (axialRot q.2 y))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (2 * Real.pi)))
    (φ : ℝ) (h : transportDefect P ξ v G g 0 (axialRot φ y) = 0) :
    transportDefect P ξ v G g 0 y = 0 := by
  refine rotate_vec_eq_zero φ fun i => ?_
  have e := transportDefect_rotate (P := P) (ξ := ξ) hvp hGp hgp hvi hGi hgi φ i
  rw [h, Pi.zero_apply] at e
  exact (mul_eq_zero.1 e.symm).resolve_left (Complex.exp_ne_zero _)

theorem slice_eq_restrict :
    sliceMeasure = (volume : Measure (ℝ × ℝ)).restrict (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) := by
  rw [sliceMeasure, Measure.volume_eq_prod, Measure.prod_restrict]

theorem integrableOn_of_slice {E : Type*} [NormedAddCommGroup E] {f : ℝ × ℝ → E}
    (h : Integrable f sliceMeasure) : IntegrableOn f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (2 * Real.pi)) := by
  have h2 : IntegrableOn f (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) := by
    rw [IntegrableOn, ← slice_eq_restrict]
    exact h
  refine h2.congr_set_ae ?_
  rw [Measure.volume_eq_prod]
  exact Measure.set_prod_ae_eq Ioc_ae_eq_Icc.symm Ioc_ae_eq_Icc.symm

theorem column_of_slice {G : ℝ → Space → (Space →L[ℝ] Space)} {y : Space}
    (h : Integrable (fun s : ℝ × ℝ => G s.1 (axialRot s.2 y)) sliceMeasure) (j : Fin 3) :
    Integrable (fun s : ℝ × ℝ => G s.1 (axialRot s.2 y) (axialRot s.2 (unitVector j))) sliceMeasure := by
  have hc : Continuous (fun x : (ℝ × ℝ) × (Space →L[ℝ] Space) => x.2 (axialRot x.1.2 (unitVector j))) := by
    refine continuous_snd.clm_apply ?_
    unfold axialRot
    fun_prop
  have hm : AEStronglyMeasurable
      (fun s : ℝ × ℝ => G s.1 (axialRot s.2 y) (axialRot s.2 (unitVector j))) sliceMeasure :=
    hc.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk h.aestronglyMeasurable)
  refine Integrable.mono' h.norm hm (Filter.Eventually.of_forall fun s => ?_)
  calc ‖G s.1 (axialRot s.2 y) (axialRot s.2 (unitVector j))‖
      ≤ ‖G s.1 (axialRot s.2 y)‖ * ‖axialRot s.2 (unitVector j)‖ := (G _ _).le_opNorm _
    _ = ‖G s.1 (axialRot s.2 y)‖ := by
      rw [axialRot_norm]
      simp [unitVector]

theorem planePoint_coords (p : ℝ × ℝ) :
    planePoint p 0 = p.1 ∧ planePoint p 1 = 0 ∧ planePoint p 2 = p.2 := by
  simp [planePoint, cylPoint]

theorem labelVel_transport_plane {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (hP : 0 < P) (m : ℕ) (ι : ℤ × ℤ) :
    ∀ᵐ p : ℝ × ℝ, 0 < p.1 → ∀ a : Fin 3,
      labelVel m ι g p a = ((labelTimeFreq P ι : ℂ) * Complex.I + 1 / 2) * velAt m ι v a p
        + (1 / 2 : ℂ) * ((p.1 : ℂ) * gradAt m ι G a 0 p + (p.2 : ℂ) * gradAt m ι G a 2 p) := by
  obtain ⟨hvl, hGl, -⟩ := Coercive.perturbationLocalIntegrabilityHolds_proof Γ P v G H g hv
  have hgl := derivative_locallyIntegrable hv
  have h0 := ae_transportDefect hv hP (labelHarmonic m ι) 0
  have hcov : ∀ᵐ p : ℝ × ℝ, 0 < p.1 → ∀ φ : ℝ,
      transportDefect P (labelHarmonic m ι) v G g 0 (axialRot φ (planePoint p)) = 0 →
        transportDefect P (labelHarmonic m ι) v G g 0 (planePoint p) = 0 := by
    filter_upwards [ae_slice_integrable hvl, ae_slice_integrable hGl, ae_slice_integrable hgl]
      with p hpv hpG hpg hp φ hE
    refine transportDefect_eq_zero_of_rotate hv.periodic_velocity hv.periodic_gradient
      hv.periodic_derivative ?_ (fun j => ?_) ?_ φ hE
    · simpa only [zero_add] using integrableOn_of_slice (hpv hp)
    · simpa only [zero_add] using integrableOn_of_slice (column_of_slice (hpG hp) j)
    · simpa only [zero_add] using integrableOn_of_slice (hpg hp)
  filter_upwards [ae_plane_of_ae_space h0 hcov] with p hp hp1 a
  have h := congrFun (hp hp1) a
  obtain ⟨c0, c1, c2⟩ := planePoint_coords p
  simp only [transportDefect, Pi.zero_apply, Fin.sum_univ_three, c0, c1, c2, Complex.ofReal_zero,
    mul_zero, add_zero] at h
  simp only [labelVel, velAt, gradAt, labelGrad, labelTimeFreq]
  simp only [labelHarmonic] at h ⊢
  push_cast at h ⊢
  linear_combination -h

end Breakdown.CertCell.Assembly.Internal.RowIdentity
