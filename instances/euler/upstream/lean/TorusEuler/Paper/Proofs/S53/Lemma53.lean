import TorusEuler.Paper.Proofs.S53.Library.CopyPHI
import TorusEuler.Paper.Proofs.S5a.Library.Near519
import TorusEuler.Paper.Proofs.S5Bridge.Operators
import TorusEuler.Paper.Proofs.S5Bridge.Norms
import TorusEuler.PhysicalWaveEnvelopeSupport
import TorusEuler.Paper.Proofs.S5a.Library.Inactive

/-!
# Lemma 5.3: the assembly of the conditional proof

`lemma_5_3_of_leaves` proves `Statement.lemma_5_3` from `h5_1` and the instance `Leaves` (Lemmas 3.1, D.1, D.2, D.3 in
the form consumed by the copied chain `Paper.Lib.S53.Copy*`).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

noncomputable section

namespace Lib.S53

/-- `SeedNear` is monotone in the scale `D`. -/
theorem seedNear_mono {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3} {center : ℝ → Vec3}
    {t₀ T ell D D' C : ℝ} {amp : ℝ → Vec3 → Vec3} (hD : 0 < D) (hDD' : D ≤ D')
    (h : Bridge.SeedNear M κ center t₀ T ell D C amp) :
    Bridge.SeedNear M κ center t₀ T ell D' C amp := by
  intro a ha t ht
  obtain ⟨h1, h2, h3, h4, h5⟩ := h a ha t ht
  refine ⟨h1, h2, le_trans ?_ h3, h4, le_trans ?_ h5⟩
  · exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) (by linarith)) (by positivity)
  · exact inv_anti₀ (by positivity) (by linarith)

variable [Leaves]

/-- Lemma 5.3 from `h5_1` and the leaves. -/
theorem lemma_5_3_of_leaves (h5_1 : Statement.proposition_5_1) : Statement.lemma_5_3 := by
  obtain ⟨C0, B, hB, hLeaf⟩ := Lib.S5a.leafBounds_of_h51 h5_1
  obtain ⟨A₁, hA₁, Cinv, hCinv, hInv⟩ := HierarchyTwistedProfile.exists_paper_hierarchy_inverse B hB
  obtain ⟨A₂, hA₂, hLead⟩ := LocalizedAmplitude.exists_paper_hierarchy_leading B hB
  obtain ⟨A₃, hA₃, Cs, hNear⟩ := Lib.S5a.seedNear_of_h51 h5_1
  choose Clead hClead hLead' using hLead
  let e := (C0 + 1) * 64
  refine ⟨e * (A₁ + A₂) + A₃, fun a ha => ⟨20 * e, fun n => Cinv n + Clead n, ?_⟩⟩
  intro T hT U X pU k D lam t₀ center d hP hL hO ℓ h γ M κ Sg
  have hT₁ : T ≤ 1 := hP.time_le_one
  have hD2 : 2 ≤ D := hP.scale_ge_two
  have hD1 : 1 ≤ D := by linarith
  have hD0 : 0 < D := by linarith
  have he : 1 ≤ e := by omega
  have hD1' : 1 ≤ D ^ (C0 + 1) := one_le_pow₀ hD1
  have hDD' : D ≤ D ^ e := le_self_pow₀ hD1 (by omega)
  have hD'2 : 2 ≤ D ^ e := hD2.trans hDD'
  have hℓpos : 0 < ℓ := Bridge.radius_pos hP a
  have hℓle (A : ℕ) (hA : e * A ≤ a) : ℓ ≤ ((D ^ e) ^ A)⁻¹ := by
    change (D ^ a)⁻¹ ≤ _
    rw [← pow_mul]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hD1 hA)
  have hℓle' (A : ℕ) (hA : A ≤ a) : ℓ ≤ (D ^ A)⁻¹ :=
    (inv_anti₀ (by positivity) (pow_le_pow_right₀ hD1 hA))
  have hsub : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc_left hL.start_nonneg
  have hfreq : 1 ≤ lam := hP.frequency_ge_one
  have hcarrier : ‖labelWaveVector X 0 0 k t₀‖ = lam := hL.frequency
  have hLeaf' : Leaf2 B U X T (D ^ e) k lam :=
    ⟨D ^ (C0 + 1), hD1', by
      show (D ^ (C0 + 1)) ^ 64 ≤ D ^ e
      rw [← pow_mul],
      leafBounds_mono hB (one_le_pow₀ hD1) (pow_le_pow_right₀ hD1 (by omega)) (hLeaf hT hP hL)⟩
  have hcenter : LocalizedAmplitude.CenterWaveOn (fun t => fderiv ℝ (U t) (X 0 t 0))
      (fun t => labelWaveVector X 0 0 k t) center t₀ T (D ^ e) :=
    Lib.S5a.centerWaveOn_mono hO.wave hD0 hDD'
  have hpow : (D ^ e) ^ 20 = D ^ (20 * e) := by rw [← pow_mul, mul_comm]
  have hSg : ∀ x ∈ Sg, ∃ z : Fin 3 → ℤ, ‖x - latticeVector z‖ ≤ 2 * ℓ := by
    intro x hx
    obtain ⟨z, hz⟩ := exists_lattice_dist_le_of_mem_periodicEnvelope_tsupport hℓpos hx
    exact ⟨z, by rwa [dist_comm, dist_eq_norm] at hz⟩
  obtain ⟨Bw, hBw⟩ := Bridge.Origin.exists_inverse_weight_bound hP hL hO
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (5.19)
    intro amp hamp t ht x hx
    obtain ⟨_, ⟨_, h2⟩, _, h4, _⟩ :=
      hNear hT hP hL hO hℓpos (hℓle' A₃ (by nlinarith)) amp hamp x hx t ht
    refine ⟨?_, h4⟩
    rw [hamp.at_origin t ht]
    exact h2
  · -- (i), (5.20)
    intro n V f hV0 hf0 hperp hderiv
    have hmain := (hInv (D := D ^ e) d hT₁ hL.start_nonneg hL.start_lt hD'2 hℓpos
      (hℓle A₁ (by nlinarith)) hfreq hcarrier hP.flow hP.velocity_smooth hP.velocity_periodic
      (fun t ht a => (hP.deformation_le t ht a).trans hDD')
      (fun t ht a => (hP.inverse_deformation_le t ht a).trans hDD')
      (fun t ht a => (hP.gradient_le t ht a).trans hDD') hLeaf' hcenter n
      (S := Sg) (Lib.S5a.isClosed_envelopeSupport ℓ) hSg).1 V f hV0 hf0
      (fun t ht x s => by
        rw [Bridge.oscillation_covector_eq d (hsub ht) x]
        exact hperp t ht x s)
      (fun t ht x s => by
        rw [Bridge.oscillation_covector_eq d (hsub ht) x, Bridge.oscillation_strain_eq d (hsub ht) x]
        exact hderiv t ht x s)
    have hγpos : 0 < (γ t₀)⁻¹ :=
      inv_pos.mpr (Bridge.Origin.weight_pos hP hO t₀ ⟨le_rfl, hL.start_lt.le⟩)
    have hX : 0 ≤ (γ t₀)⁻¹ * S5.launchNorm ℓ h t₀ n V + S5.wNorm ℓ h t₀ γ n f := by
      refine add_nonneg (mul_nonneg hγpos.le ?_)
        (Bridge.wNorm_nonneg ℓ h n hT hL.start_nonneg γ hBw f)
      rw [Bridge.launchNorm_eq_hierarchyLaunchSeminorm ℓ h n hT ⟨hL.start_nonneg, hL.start_lt.le⟩ V]
      exact apply_nonneg _ _
    refine hmain.trans ?_
    rw [hpow]
    refine mul_le_mul_of_nonneg_right ?_ hX
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hClead n)) (by positivity)
  · -- (ii), (5.21)
    intro n f V q hmean hsupp hsol
    have hmain := (hInv (D := D ^ e) d hT₁ hL.start_nonneg hL.start_lt hD'2 hℓpos
      (hℓle A₁ (by nlinarith)) hfreq hcarrier hP.flow hP.velocity_smooth hP.velocity_periodic
      (fun t ht a => (hP.deformation_le t ht a).trans hDD')
      (fun t ht a => (hP.inverse_deformation_le t ht a).trans hDD')
      (fun t ht a => (hP.gradient_le t ht a).trans hDD') hLeaf' hcenter n
      (S := Sg) (Lib.S5a.isClosed_envelopeSupport ℓ) hSg).2 f hmean hsupp
    let r := HierarchyTwistedProfile.solveTransverse hT d.inverse d.strain d.covector d.oscillation f hmean
    have hsolr : S5.TransverseSolution d f r.output.V r.output.p :=
      ⟨r.momentum, fun t ht a s => by
        have h := r.transverse t ht a s
        rw [d.covector_value (t, a, s) ⟨ht, mem_univ _⟩] at h
        exact h, r.output.average_V, r.velocity_initial, r.pressure_mean⟩
    obtain ⟨rfl, rfl⟩ := Bridge.TransverseSolution.unique d hsol hsolr
    refine hmain.trans ?_
    rw [hpow]
    have hf0 := Bridge.wNorm_nonneg ℓ h n hT hL.start_nonneg γ hBw f
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (hClead n)) (by positivity)) hf0
  · -- (iii), (5.22)
    intro n amp hamp
    have hnear := seedNear_mono hD0 hDD'
      (hNear hT hP hL hO hℓpos (hℓle' A₃ (by nlinarith)) amp hamp)
    let w := Bridge.seedOnOfIsSeed hamp hnear
    have hreg : w.HierarchyRegularity 0 h :=
      Bridge.hierarchyRegularity_of_isSeed hP hL w hamp le_rfl hℓpos
        (Bridge.radius_fits hD2 (by omega)) (Bridge.width_pos hP) (Bridge.width_le_one hP)
    have hmain := hLead' n hL.start_nonneg hL.start_lt hT₁ hD'2 hℓpos
      (hℓle A₂ (by nlinarith)) hfreq hcarrier hP.flow hP.velocity_smooth hP.velocity_periodic
      (fun t ht a => (hP.deformation_le t ht a).trans hDD')
      (fun t ht a => (hP.inverse_deformation_le t ht a).trans hDD') hLeaf' hcenter w hreg
    refine hmain.trans ?_
    rw [hpow]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (hCinv n)) (by positivity)) (Real.rpow_nonneg (by linarith) _)

end Lib.S53

end

end TorusEuler.Paper

namespace TorusEuler.Paper

noncomputable section

/-- **Lemma 5.3**, from `h3_1`, `h5_1`, `hD_1`, `hD_2` and the weighted derivative recurrence of Lemma D.3
for the ODE (`Lib.S53.OdeWordBound`, derived from `hD_3` in `Proof53.lean`). -/
theorem lemma_5_3_of_ode (h3_1 : Statement.lemma_3_1) (h5_1 : Statement.proposition_5_1)
    (hD_1 : Statement.lemma_D_1) (hD_2 : Statement.lemma_D_2) (hode : Lib.S53.OdeWordBound) :
    Statement.lemma_5_3 :=
  @Lib.S53.lemma_5_3_of_leaves (Lib.S53.leavesOf h3_1 hD_1 hD_2 hode) h5_1

end

end TorusEuler.Paper
