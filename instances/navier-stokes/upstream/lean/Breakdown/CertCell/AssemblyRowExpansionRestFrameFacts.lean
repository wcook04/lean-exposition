import Breakdown.CertCell.AssemblyRowExpansionRestFrame
import Breakdown.Cert.CoerciveSmoothMuWave

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace VecFrame

open CellCert.CellAnalysis Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation
  Coercive.StretchInternal Coercive.RotationInternal

theorem rot_plane_coords (φ : ℝ) (p : ℝ × ℝ) :
    (axialRot φ (planePoint p)) 0 = p.1 * Real.cos φ ∧ (axialRot φ (planePoint p)) 1 = p.1 * Real.sin φ ∧
      (axialRot φ (planePoint p)) 2 = p.2 := by
  simp [axialRot, planePoint, cylPoint, unitVector]
  constructor <;> ring

theorem rot_plane_sq (φ r : ℝ) : (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 = r ^ 2 := by
  have := Real.sin_sq_add_cos_sq φ
  linear_combination r ^ 2 * this

theorem rot_plane_radius (φ : ℝ) (p : ℝ × ℝ) (hp : 0 ≤ p.1) :
    Real.sqrt ((axialRot φ (planePoint p)) 0 ^ 2 + (axialRot φ (planePoint p)) 1 ^ 2) = p.1 := by
  obtain ⟨h0, h1, -⟩ := rot_plane_coords φ p
  rw [h0, h1, rot_plane_sq, Real.sqrt_sq hp]

theorem rot_plane_solid_iff (L : CellBox) (φ : ℝ) (p : ℝ × ℝ) (h1 : 0 ≤ p.1) (h2 : 0 ≤ p.2) :
    axialRot φ (planePoint p) ∈ L.solid ↔ p ∈ L.rect := by
  have hr := rot_plane_radius φ p h1
  obtain ⟨-, -, hz⟩ := rot_plane_coords φ p
  simp only [CellBox.solid, CellBox.rect, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Icc,
    CellCert.CellAnalysis.cylRadius, CellCert.CellAnalysis.cylHeight]
  rw [hr, hz, abs_of_nonneg h2]
  tauto

theorem rot_plane_back (φ : ℝ) (p : ℝ × ℝ) (h1 : 0 ≤ p.1) :
    pointPlane (axialRot φ (planePoint p)) = p := by
  unfold pointPlane
  rw [rot_plane_radius φ p h1, (rot_plane_coords φ p).2.2]

theorem rot_plane_angle (φ : ℝ) (p : ℝ × ℝ) (h1 : 0 < p.1) :
    Real.cos (pointAngle (axialRot φ (planePoint p))) = Real.cos φ ∧
      Real.sin (pointAngle (axialRot φ (planePoint p))) = Real.sin φ := by
  obtain ⟨h0, h1', -⟩ := rot_plane_coords φ p
  unfold pointAngle
  rw [h0, h1']
  set w : ℂ := ((p.1 * Real.cos φ : ℝ) : ℂ) + ((p.1 * Real.sin φ : ℝ) : ℂ) * Complex.I with hw
  have hn : ‖w‖ = p.1 := by
    rw [hw, Complex.norm_add_mul_I, rot_plane_sq, Real.sqrt_sq h1.le]
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    linarith
  rw [Complex.cos_arg hw0, Complex.sin_arg, hn]
  simp only [hw, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im]
  constructor <;> field_simp <;> ring

theorem unit_of_angle (θ φ : ℝ) (hc : Real.cos θ = Real.cos φ) (hs : Real.sin θ = Real.sin φ)
    (a : Fin 3) : frameUnit θ a = axialRot φ (unitVector a) := by
  ext k
  fin_cases a <;> fin_cases k <;>
    simp [frameUnit, radialUnit, angularUnit, axialUnit, axialRot, unitVector, hc, hs]

theorem phase_of_angle (m : ℕ) (ι : ℤ × ℤ) (σ θ φ : ℝ) (hc : Real.cos θ = Real.cos φ)
    (hs : Real.sin θ = Real.sin φ) : labelPhase m ι σ θ = labelPhase m ι σ φ := by
  have he : Complex.exp ((θ : ℂ) * Complex.I) = Complex.exp ((φ : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, hc, hs]
  have split : ∀ ψ : ℝ, labelPhase m ι σ ψ
      = Complex.exp (((2 * Real.pi * (labelTime ι : ℝ) * σ : ℝ) : ℂ) * Complex.I)
        * Complex.exp ((ψ : ℂ) * Complex.I) ^ (labelAzimuth m ι) := by
    intro ψ
    rw [labelPhase, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [split, split, he]

theorem frame_comps (φ : ℝ) (x : Fin 3 → ℝ) (a : Fin 3) :
    axialRot (-φ) (∑ b : Fin 3, x b • axialRot φ (unitVector b)) a = x a := by
  have e : ∀ z, axialRot (-φ) z = axialRotEquiv (-φ) z := fun _ => rfl
  rw [e]
  simp only [map_sum, map_smul]
  simp only [← e, axialRot_neg_self]
  simp [unitVector, Fin.sum_univ_three]
  fin_cases a <;> simp

theorem phase_neg (m : ℕ) (ι : ℤ × ℤ) (σ θ : ℝ) :
    labelPhase m (-ι) σ θ = starRingEnd ℂ (labelPhase m ι σ θ) := by
  rw [labelPhase, labelPhase, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, labelTime, labelAzimuth, Prod.fst_neg, Prod.snd_neg]
  push_cast
  ring

theorem value_neg {count : ℕ} (F : CellVecField count) (box : Fin count → CellBox)
    (hF : F.IsConjugateClosed box) (K : Fin count) (ι : ℤ × ℤ) (a : Fin 3) (p : ℝ × ℝ) :
    F.planeValue box K (-ι) a p = starRingEnd ℂ (F.planeValue box K ι a p) := by
  have hflip : labelFlip (-ι) = -labelFlip ι := by
    simp only [labelFlip, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk, neg_neg]
    congr 1
    ring
  unfold CellVecField.planeValue labelValueAt
  split_ifs with h
  · exact hF.2 K ι a p
  · rw [hflip, hF.2 K (labelFlip ι) a, map_mul, Complex.conj_ofReal]

theorem field_in_frame {M : CellMesh} (F : CellVecField M.count) (m : ℕ) (K : Fin M.count)
    (p : ℝ × ℝ) (hK : p ∈ (M.box K).rect) (h1 : 0 < p.1) (h2 : 0 ≤ p.2)
    (hL : ∀ L, L ≠ K → p ∉ (M.box L).rect) (τ φ : ℝ) (a : Fin 3) :
    fibVel (F.field M.box m) (planePoint p) τ φ a
      = ∑ ι ∈ F.labels K, (labelPhase m ι τ φ * F.planeValue M.box K ι a p).re := by
  set x := axialRot φ (planePoint p) with hx
  obtain ⟨hc, hs⟩ := rot_plane_angle φ p h1
  have hU := unit_of_angle _ _ hc hs
  have hP := rot_plane_back φ p h1.le
  have hval : F.field M.box m τ x = ∑ b : Fin 3, (∑ ι ∈ F.labels K,
      (labelPhase m ι τ φ * F.planeValue M.box K ι b p).re) • axialRot φ (unitVector b) := by
    unfold CellVecField.field
    rw [Finset.sum_eq_single K]
    · rw [Set.indicator_of_mem ((rot_plane_solid_iff _ φ p h1.le h2).2 hK), Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun ι _ => ?_
      rw [hU, hP, phase_of_angle m ι τ _ φ hc hs]
    · intro L _ hLK
      exact Set.indicator_of_notMem (fun h => hL L hLK ((rot_plane_solid_iff _ φ p h1.le h2).1 h)) _
    · intro h
      exact absurd (Finset.mem_univ K) h
  unfold fibVel
  rw [← hx, hval, frame_comps]

end VecFrame

open CellCert.CellAnalysis Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation
  Coercive.StretchInternal in
theorem vecFieldFrame : VecFieldFrameStatement := by
  intro M F m K hM hF
  have hbox := hM.box_valid K
  have hmeas : ∀ L, MeasurableSet (M.box L).rect := fun L => measurableSet_Icc.prod measurableSet_Icc
  have hax : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.1 ≠ 0 := by
    rw [ae_iff]
    simp only [not_not]
    have e : {p : ℝ × ℝ | p.1 = 0} = {0} ×ˢ Set.univ := by
      ext
      simp
    rw [e, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hapart : ∀ᵐ p ∂(volume.restrict (M.box K).rect), ∀ L, L ≠ K → p ∉ (M.box L).rect := by
    rw [ae_all_iff]
    intro L
    by_cases hLK : L = K
    · exact Filter.Eventually.of_forall fun p h => absurd hLK h
    · have h0 : volume.restrict (M.box K).rect (M.box L).rect = 0 := by
        rw [Measure.restrict_apply (hmeas L), Set.inter_comm]
        exact hM.boxes_apart K L (Ne.symm hLK)
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with p hp _ using hp
  filter_upwards [ae_restrict_mem (hmeas K), ae_restrict_of_ae hax, hapart] with p hpK hp0 hpL
  intro τ φ a
  have h1 : 0 < p.1 := lt_of_le_of_ne (hbox.r_order.1.trans hpK.1.1) (Ne.symm hp0)
  have h2 : 0 ≤ p.2 := hbox.z_order.1.trans hpK.2.1
  rw [VecFrame.field_in_frame F m K p hpK h1 h2 hpL τ φ a]
  exact Coercive.Internal.MuSmooth.re_sum_sym (F.labels K) (fun ι hι => (hF.1 K ι hι).1) _ (fun ι => by
    rw [VecFrame.phase_neg, VecFrame.value_neg F M.box hF, map_mul])

end Internal

end Assembly

end CertCell

end Breakdown
