import Breakdown.CertCell.AssemblyPotentialExpandCoupling
import Breakdown.CertCell.PinHalfPlane
import Breakdown.CertCell.ModeRotationNorms
import Breakdown.Cert.CoerciveFrequencySeminormTransportModes
import Breakdown.CertCell.LabelArithmetic

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

namespace Internal.StretchPairs

section OffLattice

open Coercive.Internal.ModeRotation

theorem modeVel_zero_of_shift {v : ℝ → Space → Space} (hp : IsTimePeriodic v) (ξ : ℤ × ℤ) (σ : ℝ) (y : Space)
    (h : modeVel ξ v σ y = 0) : modeVel ξ v 0 y = 0 := by
  funext i
  have key := Coercive.FrequencySeminorm.Internal.modeAverage_shift ξ
    (fun t φ (i : Fin 3) => axialRot (-φ) (v t (axialRot φ y)) i) (fun t φ b => by simp only [hp t]) σ i
  have h1 := congrFun h i
  unfold modeVel at h1 ⊢
  simp only [zero_add]
  rw [key] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact absurd h2 (Complex.exp_ne_zero _)
  · simpa using h2

theorem modeGrad_zero_of_shift {G : ℝ → Space → (Space →L[ℝ] Space)} (hp : IsTimePeriodic G) (ξ : ℤ × ℤ) (σ : ℝ)
    (y : Space) (h : modeGrad ξ G σ y = 0) : modeGrad ξ G 0 y = 0 := by
  funext ij
  have key := Coercive.FrequencySeminorm.Internal.modeAverage_shift ξ
    (fun t φ (ij : Fin 3 × Fin 3) => axialRot (-φ) (G t (axialRot φ y) (axialRot φ (unitVector ij.2))) ij.1)
    (fun t φ b => by simp only [hp t]) σ ij
  have h1 := congrFun h ij
  unfold modeGrad at h1 ⊢
  simp only [zero_add]
  rw [key] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact absurd h2 (Complex.exp_ne_zero _)
  · simpa using h2

theorem eq_zero_of_cnormSq {β : Type*} [Fintype β] {x : β → ℂ} (h : cnormSq x = 0) : x = 0 := by
  funext b
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg ‖x b‖)).1 h b (Finset.mem_univ b)
  simpa using h1

theorem gradient_local_finite {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g)
    (R : ℝ) : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖G σ y‖ ^ 2) < ⊤ := by
  refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := 3)) hv.gradient_finite)
  unfold periodLIntegral
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun σ => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun y => ?_)
  rw [← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (Bridge.Internal.MeanStretch.opNorm_sq_le_matSq _)

theorem ae_offLattice_zero (hC : Bridge.ClassSupportHolds) {Γ : Set Symmetry} {m : ℕ} (hclass : Bridge.IsModeClass Γ m)
    {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g)
    (ξ : ℤ × ℤ) (hξ : ¬ IsLatticeHarmonic m ξ) :
    ∀ᵐ p ∂(volume.restrict halfPlane), modeVel ξ v 0 (planePoint p) = 0 ∧ modeGrad ξ G 0 (planePoint p) = 0 := by
  have h1 := hC Γ m P v G H g hclass hv ξ hξ
  have h2 : ∀ᵐ y : Space, modeVel ξ v 0 y = 0 ∧ modeGrad ξ G 0 y = 0 := by
    refine Bridge.Internal.PinHalf.ae_of_snd ?_
    filter_upwards [h1] with z hz
    exact ⟨modeVel_zero_of_shift hv.periodic_velocity ξ z.1 z.2 hz.1,
      modeGrad_zero_of_shift hv.periodic_gradient ξ z.1 z.2 hz.2.1⟩
  have h3 := TailBand.ae_exists_rotation_planePoint_of_ae h2
  have hvL := Bridge.Internal.MeanStretch.ae_memLp_orbit hv.measurable_velocity
    (Coercive.perturbationLocalSquareIntegrabilityHolds_proof Γ P v G H g hv)
  have hGL := Bridge.Internal.MeanStretch.ae_memLp_orbit (u := G) hv.measurable_gradient (gradient_local_finite hv)
  filter_upwards [h3, hvL, hGL] with p hp hpv hpG
  obtain ⟨θ, hθv, hθG⟩ := hp
  have iv : Integrable (fun q : ℝ × ℝ => v ((0 : ℝ) + q.1) (axialRot q.2 (planePoint p))) boxMeasure := by
    simpa only [zero_add] using hpv.integrable one_le_two
  have iG : Integrable (fun q : ℝ × ℝ => G ((0 : ℝ) + q.1) (axialRot q.2 (planePoint p))) boxMeasure := by
    simpa only [zero_add] using hpG.integrable one_le_two
  have ev := modeVel_rotation_of Coercive.axialRotationHolds_proof (z := ((0 : ℝ), planePoint p)) ξ θ iv
  have eG := modeGrad_rotation_of Coercive.axialRotationHolds_proof (z := ((0 : ℝ), planePoint p)) ξ θ iG
  simp only at ev eG
  rw [hθv] at ev
  rw [hθG] at eG
  constructor
  · have hr : Coercive.rotC θ (modeVel ξ v 0 (planePoint p)) = 0 := by
      funext i
      have := congrFun ev i
      simp only [Pi.zero_apply] at this
      rcases mul_eq_zero.1 this.symm with h | h
      · exact absurd h (Complex.exp_ne_zero _)
      · exact h
    have hn := TailBand.Internal.AngularPlane.cnormSq_rotC θ (modeVel ξ v 0 (planePoint p))
    rw [hr] at hn
    exact eq_zero_of_cnormSq (by rw [← hn]; simp [cnormSq])
  · have hr : Coercive.rotCMat θ (modeGrad ξ G 0 (planePoint p)) = 0 := by
      funext ij
      have := congrFun eG ij
      simp only [Pi.zero_apply] at this
      rcases mul_eq_zero.1 this.symm with h | h
      · exact absurd h (Complex.exp_ne_zero _)
      · exact h
    have hn := TailBand.Internal.AngularPlane.cnormSq_rotCMat θ (modeGrad ξ G 0 (planePoint p))
    rw [hr] at hn
    exact eq_zero_of_cnormSq (by rw [← hn]; simp [cnormSq])

end OffLattice

section PointwiseSum

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)

def orbitTerm (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (y : Space) (β ξ : ℤ × ℤ) : ℝ :=
  (Bridge.stretchTriple (modeGrad β (gradField D.given) 0 y) (modeSecondDeriv β D.givenHess 0 y) (modeVel ξ v 0 y)
    (modeGrad ξ G 0 y) (star (modeVel (ξ + β) v 0 y)) (star (modeGrad (ξ + β) G 0 y))).re

theorem orbitTerm_label (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) (α κ : ℤ × ℤ) :
    orbitTerm D v G (planePoint p) (labelHarmonic D.azimuthOrder α) (labelHarmonic D.azimuthOrder (κ - α))
      = (sesq12 (trueCoupling D α p) (bandProfile D κ v G p) (bandProfile D (κ - α) v G p)).re := by
  rw [sesq12_trueCoupling_eq, velOf_bandProfile, gradOf_bandProfile, velOf_bandProfile, gradOf_bandProfile]
  unfold orbitTerm
  rw [← labelHarmonic_add, sub_add_cancel]
  rfl

end PointwiseSum

end Internal.StretchPairs

section LabelSum

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)

open Internal.StretchPairs in
theorem meanStretch_eq_labelSum (hMS : Bridge.MeanStretchModeSumHolds) (hC : Bridge.ClassSupportHolds)
    (hW : ∃ B, CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B)
    (hE : Bridge.IsHarmonicExpansion D.givenLabels D.given D.givenHess) (hm : 1 ≤ D.azimuthOrder)
    {Γ : Set Symmetry} (hclass : Bridge.IsModeClass Γ D.azimuthOrder) (Hs : Finset (ℤ × ℤ))
    (hHs : ∀ α, α ∈ Hs ↔ labelHarmonic D.azimuthOrder α ∈ D.givenLabels)
    {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    ∀ᵐ p ∂(volume.restrict halfPlane),
      (∀ α ∈ Hs, Summable (fun κ : ℤ × ℤ =>
        (sesq12 (trueCoupling D α p) (bandProfile D κ v G p) (bandProfile D (κ - α) v G p)).re)) ∧
      D.meanStretch v G p = ∑' κ : ℤ × ℤ, ∑ α ∈ Hs,
        (sesq12 (trueCoupling D α p) (bandProfile D κ v G p) (bandProfile D (κ - α) v G p)).re := by
  classical
  obtain ⟨B, hB⟩ := hW
  set m := D.azimuthOrder with hmdef
  have hinj : Function.Injective (labelHarmonic m) := (Bridge.labelArithmetic m hm).1
  have hoff : ∀ ξ : ℤ × ℤ, ∀ᵐ p ∂(volume.restrict halfPlane), ¬ IsLatticeHarmonic m ξ →
      modeVel ξ v 0 (planePoint p) = 0 ∧ modeGrad ξ G 0 (planePoint p) = 0 := by
    intro ξ
    by_cases hξ : IsLatticeHarmonic m ξ
    · exact Filter.Eventually.of_forall fun p h => absurd hξ h
    · filter_upwards [ae_offLattice_zero hC hclass hv ξ hξ] with p hp
      exact fun _ => hp
  filter_upwards [hMS D B hB hE Γ P v G H g hv, ae_all_iff.2 hoff] with p hp hpo
  obtain ⟨hsum, heq⟩ := hp
  set y := planePoint p with hy
  have hzero : ∀ β ξ, ¬ IsLatticeHarmonic m ξ → orbitTerm D v G y β ξ = 0 := by
    intro β ξ hξ
    obtain ⟨h1, h2⟩ := hpo ξ hξ
    unfold orbitTerm
    rw [h1, h2, stretchTriple_zero_left]
    simp
  have hzero' : ∀ β ι, ¬ IsLatticeHarmonic m β → orbitTerm D v G y β (labelHarmonic m ι) = 0 := by
    intro β ι hβ
    have hn : ¬ IsLatticeHarmonic m (labelHarmonic m ι + β) := by
      rintro ⟨κ, hκ⟩
      exact hβ ⟨κ - ι, by rw [labelHarmonic_sub, hκ]; abel⟩
    obtain ⟨h1, h2⟩ := hpo _ hn
    unfold orbitTerm
    rw [h1, h2, star_zero, star_zero, stretchTriple_zero_right]
    simp
  have hrange : ∀ β, ∑' ξ : ℤ × ℤ, orbitTerm D v G y β ξ = ∑' ι : ℤ × ℤ, orbitTerm D v G y β (labelHarmonic m ι) := by
    intro β
    refine (hinj.tsum_eq fun ξ hξ => ?_).symm
    by_contra hr
    exact hξ (hzero β ξ fun ⟨ι, hι⟩ => hr ⟨ι, hι⟩)
  have hsumT : ∀ β ∈ D.givenLabels, Summable (fun ξ : ℤ × ℤ => orbitTerm D v G y β ξ) := by
    intro β hβ
    refine Summable.of_norm_bounded (hsum β hβ) fun ξ => ?_
    rw [Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  have hF : ∀ α ∈ Hs, ∀ κ, orbitTerm D v G y (labelHarmonic m α) (labelHarmonic m (κ - α))
      = (sesq12 (trueCoupling D α p) (bandProfile D κ v G p) (bandProfile D (κ - α) v G p)).re :=
    fun α _ κ => orbitTerm_label D v G p α κ
  have hsumF : ∀ α ∈ Hs, Summable (fun κ : ℤ × ℤ =>
      (sesq12 (trueCoupling D α p) (bandProfile D κ v G p) (bandProfile D (κ - α) v G p)).re) := by
    intro α hα
    have h1 := (hsumT _ ((hHs α).1 hα)).comp_injective hinj
    have h2 := (Equiv.subRight α).summable_iff.2 h1
    refine h2.congr fun κ => ?_
    exact hF α hα κ
  refine ⟨hsumF, ?_⟩
  have s1 : D.meanStretch v G p = ∑ β ∈ D.givenLabels, ∑' ι : ℤ × ℤ, orbitTerm D v G y β (labelHarmonic m ι) := by
    rw [heq]
    exact Finset.sum_congr rfl fun β _ => hrange β
  have s2 : ∑ β ∈ D.givenLabels, ∑' ι : ℤ × ℤ, orbitTerm D v G y β (labelHarmonic m ι)
      = ∑ β ∈ Hs.image (labelHarmonic m), ∑' ι : ℤ × ℤ, orbitTerm D v G y β (labelHarmonic m ι) := by
    refine (Finset.sum_subset (fun β hβ => ?_) fun β hβ hn => ?_).symm
    · obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hβ
      exact (hHs α).1 hα
    · have hl : ¬ IsLatticeHarmonic m β := by
        rintro ⟨α, rfl⟩
        exact hn (Finset.mem_image.2 ⟨α, (hHs α).2 hβ, rfl⟩)
      simp only [hzero' β _ hl, tsum_zero]
  have s3 : ∑ β ∈ Hs.image (labelHarmonic m), ∑' ι : ℤ × ℤ, orbitTerm D v G y β (labelHarmonic m ι)
      = ∑ α ∈ Hs, ∑' κ : ℤ × ℤ,
        (sesq12 (trueCoupling D α p) (bandProfile D κ v G p) (bandProfile D (κ - α) v G p)).re := by
    rw [Finset.sum_image fun a _ b _ h => hinj h]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [← (Equiv.subRight α).tsum_eq]
    exact tsum_congr fun κ => hF α hα κ
  rw [s1, s2, s3, Summable.tsum_finsetSum hsumF]

end LabelSum

end Assembly

end CertCell

end Breakdown
