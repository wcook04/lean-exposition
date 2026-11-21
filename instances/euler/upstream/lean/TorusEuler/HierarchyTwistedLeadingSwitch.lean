import TorusEuler.LaterWaveHierarchyInput
import TorusEuler.HierarchyTwistedRelayBounds

/-! The homogeneous linear relay of the switched leading profile. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.LocalizedAmplitude.SeedOn

variable {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3}
  {center : ℝ → Vec3} {t₀ T ell D C r h : ℝ}
  {w : SeedOn M κ center t₀ T ell D C} {k : Vec3}

/-- The flat activation force is itself transverse to the transported
covector at every point of the twisted profile slab. -/
theorem twistedLeadingSwitch_transverse (d : w.HierarchyRegularity r h)
    (κ₀ : HierarchyTwistedProfile T k Vec3)
    (hκ : ∀ x ∈ hierarchyProfileSlab T, κ₀.val.val.val x = κ x.1 x.2.1) :
    ∀ x ∈ hierarchyProfileSlab T,
      ⟪κ₀.val.val.val x, (twistedLeadingSwitch d k).val.val.val x⟫_ℝ = 0 := by
  have hCell (t : ℝ) (ht : t ∈ Icc 0 T) (a : Vec3) (ha : a ∈ centeredCell) (s : ℝ) :
      ⟪κ₀.val.val.val (t, a, s), (twistedLeadingSwitch d k).val.val.val (t, a, s)⟫_ℝ = 0 := by
    by_cases hpre : t ≤ t₀
    · rw [twistedLeadingSwitch_before_activation d k ht hpre a s, inner_zero_right]
    · rw [hκ _ ⟨ht, mem_univ _⟩, twistedLeadingSwitch_cell_eval d k ht ha]
      simp only [leadingSwitchProfile, SeedOn.leading, real_inner_smul_right,
        w.transverse a t ⟨le_of_not_ge hpre, ht.2⟩, mul_zero]
  rintro ⟨t, a, s⟩ ht
  obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell a
  have hshift (V : HierarchyTwistedProfile T k Vec3) :
      V.val.val.val (t, a, s) =
        V.val.val.val (t, a - latticeVector n, s - ⟪k, latticeVector n⟫_ℝ) := by
    simpa only [sub_add_cancel] using
      HierarchyTwistedProfile.twistedSlice V t (a - latticeVector n)
        (s - ⟪k, latticeVector n⟫_ℝ) n
  rw [hshift κ₀, hshift (twistedLeadingSwitch d k)]
  exact hCell t ht.1 _ hn _

open HierarchyTwistedProfile

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)

/-- After subtracting the completion of the activation force, the actual
later-wave relay is the homogeneous relay of the switched velocity. -/
theorem twistedLeadingRelay_apply (d : w.HierarchyRegularity r h) (G M₀ : MP) (κ₀ : VP)
    (hGPhase : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hMPhase : HierarchyPeriodicProfile.PhaseIndependent M₀.val.val)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ₀.val.val)
    (hκne : ∀ t ∈ Icc 0 T, ∀ a, κ₀.val.val.val (t, a, 0) ≠ 0)
    (hM : ∀ x ∈ hierarchyProfileSlab T, M₀.val.val.val x = M x.1 x.2.1)
    (hκ : ∀ x ∈ hierarchyProfileSlab T, κ₀.val.val.val x = κ x.1 x.2.1)
    (hGdot : ∀ t ∈ Icc 0 T, ∀ a,
      HasDerivWithinAt (fun u => G.val.val.val (u, a, 0))
        (-((G.val.val.val (t, a, 0)).comp (M₀.val.val.val (t, a, 0)))) (Icc 0 T) t)
    (hκdot : ∀ t ∈ Icc 0 T, ∀ a,
      HasDerivWithinAt (fun u => κ₀.val.val.val (u, a, 0))
        (-((M₀.val.val.val (t, a, 0)).adjoint (κ₀.val.val.val (t, a, 0)))) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    let ops := twistedHierarchyOperators d.end_pos G M₀ κ₀
    let V := twistedLeading d k
    (ops.material (complete d.end_pos G κ₀ hκPhase hκne V) +
      ops.labelGrad (twistedPressure d k) -
      twistedCompletionSwitch d G κ₀ hκPhase hκne).val.val.val (t, x) =
        waveRelayAt G M₀ κ₀ V 0 t x := by
  let V := twistedLeading d k
  let F := twistedLeadingSwitch d k
  let L := twistedLeadingOutput d G M₀ κ₀ hκ
  have hV (u : ℝ) (hu : u ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
      ⟪κ₀.val.val.val (u, a, 0), V.val.val.val (u, a, s)⟫_ℝ = 0 := by
    have hv := transverse_of_phaseAdv_eq_zero d.end_pos G M₀ κ₀ V L.phaseAdv_V
      (u, a, s) ⟨hu, mem_univ _⟩
    rwa [hκPhase (u, a, 0) ⟨hu, mem_univ _⟩ s] at hv
  have hF (u : ℝ) (hu : u ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
      ⟪κ₀.val.val.val (u, a, 0), F.val.val.val (u, a, s)⟫_ℝ = 0 := by
    have hf := twistedLeadingSwitch_transverse d κ₀ hκ (u, a, s) ⟨hu, mem_univ _⟩
    rwa [hκPhase (u, a, 0) ⟨hu, mem_univ _⟩ s] at hf
  exact material_complete_add_labelGrad_sub_switch_apply_relay d.end_pos G M₀ κ₀ V F
    (twistedPressure d k) hGPhase hMPhase hκPhase hκne (twistedLeading_average_zero d k)
    (twistedLeadingSwitch_average_zero d k) hGdot hκdot hV hF
    (fun _ hu a => twistedPressure_phaseMean_zero d k hu a)
    (twistedLeadingOutput_momentum d G M₀ κ₀ hM hκ) ht x

/-- The later-wave linear relay has the inverse-frequency bound with only
the switched leading velocity on the right-hand side. -/
theorem boundedWeightSeminorm_twistedLeadingRelay_le
    (d : w.HierarchyRegularity r h) (G M₀ : MP) (κ₀ : VP)
    (hGPhase : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hMPhase : HierarchyPeriodicProfile.PhaseIndependent M₀.val.val)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ₀.val.val)
    (hκne : ∀ t ∈ Icc 0 T, ∀ a, κ₀.val.val.val (t, a, 0) ≠ 0)
    (hM : ∀ x ∈ hierarchyProfileSlab T, M₀.val.val.val x = M x.1 x.2.1)
    (hκ : ∀ x ∈ hierarchyProfileSlab T, κ₀.val.val.val x = κ x.1 x.2.1)
    (hGdot : ∀ t ∈ Icc 0 T, ∀ a,
      HasDerivWithinAt (fun u => G.val.val.val (u, a, 0))
        (-((G.val.val.val (t, a, 0)).comp (M₀.val.val.val (t, a, 0)))) (Icc 0 T) t)
    (hκdot : ∀ t ∈ Icc 0 T, ∀ a,
      HasDerivWithinAt (fun u => κ₀.val.val.val (u, a, 0))
        (-((M₀.val.val.val (t, a, 0)).adjoint (κ₀.val.val.val (t, a, 0)))) (Icc 0 T) t)
    (n : ℕ) {freq K : ℝ} (hfreq : 0 < freq) {S : Set ℝ} (hS : S ⊆ Icc (0 : ℝ) T)
    (τ : ℝ → ℝ) {B : ℝ} (hτ : ∀ t ∈ S, ‖τ t‖ ≤ B)
    (hCoeff : WaveRelayCoefficientBudget ell h n K
      (fun (t : S) a => G.val.val.val (t, a, 0))
      (fun (t : S) a => M₀.val.val.val (t, a, 0))
      (fun (t : S) a => freq⁻¹ • κ₀.val.val.val (t, a, 0))) :
    let ops := twistedHierarchyOperators d.end_pos G M₀ κ₀
    let V := twistedLeading d k
    let R := ops.material (complete d.end_pos G κ₀ hκPhase hκne V) +
      ops.labelGrad (twistedPressure d k) - twistedCompletionSwitch d G κ₀ hκPhase hκne
    boundedWeightSeminorm False ell h n d.end_pos hS τ hτ R ≤
      waveRelayOrderConstant n * K ^ 2 * freq⁻¹ *
        boundedWeightSeminorm False ell h (n + 1) d.end_pos hS τ hτ V := by
  let ops := twistedHierarchyOperators d.end_pos G M₀ κ₀
  let V := twistedLeading d k
  let R := ops.material (complete d.end_pos G κ₀ hκPhase hκne V) +
    ops.labelGrad (twistedPressure d k) - twistedCompletionSwitch d G κ₀ hκPhase hκne
  have hRelay := boundedWeightSeminorm_waveRelay_le_of_eval d.end_pos G M₀ κ₀ V 0 R
    ell h d.envelope_pos.ne' n hfreq hS τ hτ (twistedLeading_average_zero d k) (map_zero _)
    (fun _ ht x => twistedLeadingRelay_apply d G M₀ κ₀ hGPhase hMPhase hκPhase hκne
      hM hκ hGdot hκdot (hS ht) x) hCoeff
  simpa only [map_zero, add_zero] using hRelay

end TorusEuler.LocalizedAmplitude.SeedOn
