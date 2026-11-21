import Breakdown.CertCell.CellCalculusStatements
import Breakdown.CertCell.AssemblyPotentialModelFrameFactsAlgebra

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

open CellCert.CellAnalysis Assembly.Internal Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation
  Coercive.StretchInternal Coercive.RotationInternal

theorem orbit_coords (φ : ℝ) (p : ℝ × ℝ) :
    axialRot φ (planePoint p) 0 = Real.cos φ * p.1 ∧ axialRot φ (planePoint p) 1 = Real.sin φ * p.1 ∧
      axialRot φ (planePoint p) 2 = p.2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [axialRot, planePoint, cylPoint, unitVector]

theorem orbit_radius (φ : ℝ) (p : ℝ × ℝ) (h1 : 0 ≤ p.1) :
    CellCert.CellAnalysis.cylRadius (axialRot φ (planePoint p)) = p.1 := by
  obtain ⟨c0, c1, _⟩ := orbit_coords φ p
  unfold CellCert.CellAnalysis.cylRadius
  rw [c0, c1, show (Real.cos φ * p.1) ^ 2 + (Real.sin φ * p.1) ^ 2 = p.1 ^ 2 by
    nlinarith [Real.sin_sq_add_cos_sq φ], Real.sqrt_sq h1]

theorem orbit_mem_solid_iff (L : CellBox) (φ : ℝ) (p : ℝ × ℝ) (h1 : 0 ≤ p.1) (h2 : 0 ≤ p.2) :
    axialRot φ (planePoint p) ∈ L.solid ↔ p ∈ L.rect := by
  obtain ⟨_, _, c2⟩ := orbit_coords φ p
  have hr := orbit_radius φ p h1
  unfold CellBox.solid CellBox.rect
  simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Icc]
  rw [hr, show CellCert.CellAnalysis.cylHeight (axialRot φ (planePoint p)) = p.2 from c2, abs_of_nonneg h2]
  tauto

theorem orbit_mem_ownSolid {count : ℕ} (box : Fin count → CellBox) (K : Fin count) (hK : IsCellBox (box K))
    (p : ℝ × ℝ) (hp : p ∈ (box K).rect) (hpos : 0 < p.1) (hL : ∀ L, L ≠ K → p ∉ (box L).rect) (φ : ℝ) :
    axialRot φ (planePoint p) ∈ ownSolid box K := by
  have h2 : 0 ≤ p.2 := hK.z_order.1.trans hp.2.1
  refine ⟨(orbit_mem_solid_iff _ φ p hpos.le h2).2 hp, ?_, fun L hLK h => hL L hLK ?_⟩
  · rw [orbit_radius φ p hpos.le]; exact hpos
  · exact (orbit_mem_solid_iff _ φ p hpos.le h2).1 h

theorem ae_own_point (M : CellMesh) (hM : IsCellMesh M) (K : Fin M.count) :
    ∀ᵐ p ∂(volume.restrict (M.box K).rect), 0 < p.1 ∧ ∀ L, L ≠ K → p ∉ (M.box L).rect := by
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
  exact ⟨lt_of_le_of_ne (hbox.r_order.1.trans hpK.1.1) (Ne.symm hp0), hpL⟩

theorem ae_off_plane (B : CellBox) : ∀ᵐ p ∂(volume.restrict B.rect), p.2 ≠ 0 := by
  refine ae_restrict_of_ae ?_
  rw [ae_iff]
  simp only [not_not]
  have e : {p : ℝ × ℝ | p.2 = 0} = Set.univ ×ˢ {0} := by
    ext
    simp
  rw [e, Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem orbit_height (φ : ℝ) (p : ℝ × ℝ) : CellCert.CellAnalysis.cylHeight (axialRot φ (planePoint p)) = p.2 :=
  (orbit_coords φ p).2.2

end CellCalculus

end CertCell

end Breakdown
