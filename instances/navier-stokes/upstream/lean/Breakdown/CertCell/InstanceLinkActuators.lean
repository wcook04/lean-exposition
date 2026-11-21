import Breakdown.CertCell.InstanceStatements
import Breakdown.CertCell.RotationAverage

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Instance

namespace Internal.ActuatorSymmetry

theorem axialRot_axialRot (α β : ℝ) (y : Space) : axialRot α (axialRot β y) = axialRot (α + β) y := by
  ext i
  fin_cases i <;> simp [axialRot, unitVector, Real.cos_add, Real.sin_add] <;> ring

theorem axialRot_zero_angle (y : Space) : axialRot 0 y = y := by
  ext i
  fin_cases i <;> simp [axialRot, unitVector]

def flipMap : Space →ₗ[ℝ] Space where
  toFun := flipPoint
  map_add' u v := by
    ext i
    fin_cases i <;> simp [flipPoint, unitVector] <;> ring
  map_smul' c u := by
    ext i
    fin_cases i <;> simp [flipPoint, unitVector]

theorem flipPoint_involutive (y : Space) : flipPoint (flipPoint y) = y := by
  ext i
  fin_cases i <;> simp [flipPoint, unitVector]

theorem norm_flipPoint_eq (y : Space) : ‖flipPoint y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_three, flipPoint, unitVector]

def flipIso : Space ≃ₗᵢ[ℝ] Space :=
  { LinearEquiv.ofInvolutive flipMap (fun y => flipPoint_involutive y) with
    norm_map' := fun y => norm_flipPoint_eq y }

theorem measurePreserving_flipPoint : MeasurePreserving flipPoint (volume : Measure Space) volume := by
  have e : (flipIso : Space → Space) = flipPoint := rfl
  rw [← e]
  exact flipIso.measurePreserving

theorem quasi_shift_rotate (c φ : ℝ) :
    Measure.QuasiMeasurePreserving (fun z : ℝ × Space => (z.1 + c, axialRot φ z.2)) volume volume := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) c).prod
    (Bridge.RotationAverageInternal.measurePreserving_axialRot φ)
  rw [← Measure.volume_eq_prod ℝ Space] at h
  exact h.quasiMeasurePreserving

theorem quasi_flip :
    Measure.QuasiMeasurePreserving (fun z : ℝ × Space => (z.1, flipPoint z.2)) volume volume := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod measurePreserving_flipPoint
  rw [← Measure.volume_eq_prod ℝ Space] at h
  exact h.quasiMeasurePreserving

theorem periodic_int_shift {f : ℝ → Space → Space} (hf : IsTimePeriodic f) (j : ℤ) :
    ∀ σ y, f (σ + j) y = f σ y := by
  refine Int.induction_on j ?_ ?_ ?_
  · intro σ y
    simp
  · intro n ih σ y
    have e : σ + ((n + 1 : ℤ) : ℝ) = (σ + ((n : ℤ) : ℝ)) + 1 := by
      push_cast
      ring
    rw [e, hf, ih]
  · intro n ih σ y
    have h1 := hf (σ + ((-(n : ℤ) - 1 : ℤ) : ℝ)) y
    have e : σ + ((-(n : ℤ) - 1 : ℤ) : ℝ) + 1 = σ + ((-(n : ℤ) : ℤ) : ℝ) := by
      push_cast
      ring
    rw [e, ih] at h1
    exact h1.symm

theorem rotate_iterate (f : ℝ → Space → Space) (θ : ℝ)
    (hinv : ∀ᵐ z : ℝ × Space, f (z.1 + 1 / 2) (axialRot θ z.2) = axialRot θ (f z.1 z.2)) (a : ℕ) :
    ∀ᵐ z : ℝ × Space, f (z.1 + (a : ℝ) / 2) (axialRot ((a : ℝ) * θ) z.2)
      = axialRot ((a : ℝ) * θ) (f z.1 z.2) := by
  induction a with
  | zero =>
    filter_upwards with z
    simp [axialRot_zero_angle]
  | succ n ih =>
    have h1 := (quasi_shift_rotate (1 / 2) θ).ae ih
    filter_upwards [h1, hinv] with z h1 h2
    have e1 : z.1 + ((n + 1 : ℕ) : ℝ) / 2 = z.1 + 1 / 2 + (n : ℝ) / 2 := by
      push_cast
      ring
    have e2 : ∀ v, axialRot (((n + 1 : ℕ) : ℝ) * θ) v = axialRot ((n : ℝ) * θ) (axialRot θ v) := by
      intro v
      rw [axialRot_axialRot]
      congr 1
      push_cast
      ring
    rw [e1, e2, e2, h1, h2]

end Internal.ActuatorSymmetry

open Internal.ActuatorSymmetry in
theorem actuatorInvariant_of_shape_holds {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (modes : Fin k → Finset (ℤ × ℤ)) (hfmt : ∀ i, ActuatorShapeFacts D.azimuthOrder (modes i) (D.cert.actuator i))
    (hgen : GeneratedByClassSymmetries D) :
    ∀ i, ∀ γ ∈ D.cert.symmetries, ∀ᵐ z : ℝ × Space,
      D.cert.actuator i (z.1 + γ.2) (γ.1 z.2) = γ.1 (D.cert.actuator i z.1 z.2) := by
  intro i γ hγ
  obtain ⟨a, b, j, hγ1, hγ2⟩ := hgen γ hγ
  have hrot := (hfmt i).invariant
  have hR := rotate_iterate (D.cert.actuator i) (Real.pi / D.azimuthOrder) (hrot.mono fun z h => h.1) a
  have hF : ∀ᵐ z : ℝ × Space, D.cert.actuator i z.1 (flipPoint z.2) = flipPoint (D.cert.actuator i z.1 z.2) :=
    hrot.mono fun z h => h.2
  have hRF := quasi_flip.ae hR
  have hper := periodic_int_shift (hfmt i).periodic j
  filter_upwards [hR, hRF, hF] with z h1 h2 h3
  rw [hγ1, hγ1, hγ2]
  have e : z.1 + ((a : ℝ) / 2 + (j : ℝ)) = (z.1 + (a : ℝ) / 2) + (j : ℝ) := by ring
  rw [e, hper]
  cases b
  · rw [if_neg (by decide), if_neg (by decide)]
    exact h1
  · rw [if_pos rfl, if_pos rfl, h2, h3]

theorem actuatorFacts_of_instance_holds {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (modes : Fin k → Finset (ℤ × ℤ)) (jmax : ℕ) (h : IsActuatorInstance D modes jmax)
    (hfmt : ∀ i, ActuatorShapeFacts D.azimuthOrder (modes i) (D.cert.actuator i)) (q : Fin k → ℝ)
    (hq : q ∈ D.cert.params) (i : Fin k) :
    ActuatorFacts (D.pieces q) (D.cert.actuator i) := by
  have hf := hfmt i
  have key : ∀ ξ, (∃ σ y, (pointPlane y).1 ≠ 0 ∧ modeVel ξ (D.cert.actuator i) σ y ≠ 0) →
      ∃ ι : ℤ × ℤ, |ι.2| ≤ jmax ∧ |ι.2 - ι.1| ≤ jmax ∧
        (labelHarmonic D.azimuthOrder ι = ξ ∨ labelHarmonic D.azimuthOrder ι = -ξ) := by
    rintro ξ ⟨σ, y, hy, hne⟩
    obtain ⟨ι, hι, hξ⟩ := hf.modes_in ξ σ y hy hne
    exact ⟨ι, (h.modes_bound i ι hι).1, (h.modes_bound i ι hι).2, hξ⟩
  have piece : ∀ (T : Set (ℤ × ℤ)) (ξ ι : ℤ × ℤ),
      (labelHarmonic D.azimuthOrder ι = ξ ∨ labelHarmonic D.azimuthOrder ι = -ξ) →
      PieceWeights.inPiece T ξ → PieceWeights.inPiece T (labelHarmonic D.azimuthOrder ι) := by
    rintro T ξ ι (hξ | hξ) hT
    · rw [hξ]
      exact hT
    · rw [hξ]
      unfold PieceWeights.inPiece at hT ⊢
      rw [neg_neg]
      exact hT.symm
  refine
    { measurable := hf.measurable
      periodic := hf.periodic
      bounded_support := hf.bounded_support
      square_finite := hf.square_finite
      gradient_measurable := hf.gradient_measurable
      gradient_periodic := hf.gradient_periodic
      gradient_finite := hf.gradient_finite
      weak_gradient := hf.weak_gradient
      finite_modes := ?_
      mu_free := ?_
      eps_vanish := ?_ }
  · refine ⟨(modes i).image (labelHarmonic D.azimuthOrder) ∪
      (modes i).image (fun ι => -labelHarmonic D.azimuthOrder ι), ?_⟩
    intro ξ hξ σ y hy
    by_contra hne
    obtain ⟨ι, hι, hh⟩ := hf.modes_in ξ σ y hy hne
    apply hξ
    rcases hh with hh | hh
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨ι, hι, hh⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨ι, hι, by rw [hh, neg_neg]⟩)
  · intro β ξ hex hin
    obtain ⟨ι, h1, h2, hξ⟩ := key ξ hex
    exact h.mu_avoid q hq β ι h1 h2 (piece _ ξ ι hξ hin)
  · intro β ξ hex hin
    obtain ⟨ι, h1, h2, hξ⟩ := key ξ hex
    exact absurd (piece _ ξ ι hξ hin) (h.eps_avoid q hq β ι h1 h2)

theorem pinInstance_clauses_holds (hreg : CellMatFieldRegular) {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM) (h : IsPinInstance D) :
    (∀ i, AEStronglyMeasurable (fun z : ℝ × Space => D.cert.pin i z.1 z.2) volume) ∧
    (∀ i, periodLIntegral (fun σ y => matSq (D.cert.pin i σ y)) < ⊤) := by
  have hg : ∀ i, D.cert.pin i = (D.pinValues i).field D.mesh.box D.azimuthOrder := by
    intro i
    rw [h.pin_eq]
    rfl
  refine ⟨fun i => ?_, fun i => ?_⟩
  · rw [hg i]
    exact (hreg D.mesh (D.pinValues i) D.azimuthOrder h.mesh_valid).1
  · rw [hg i]
    exact (hreg D.mesh (D.pinValues i) D.azimuthOrder h.mesh_valid).2.2.2

end Instance

end CertCell

end Breakdown
