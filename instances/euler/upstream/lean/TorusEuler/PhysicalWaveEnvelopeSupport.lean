import TorusEuler.ActivationProfiles
import TorusEuler.LabelFlowGeometry
import TorusEuler.PeriodicLift
import TorusEuler.WaveDivergence
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Spatial confinement of the physical wave envelope in Theorem 7.1. -/

open Set
open scoped ContDiff NNReal

namespace TorusEuler

/-- The closed support of the periodic radial envelope lies in the union
of the closed radius-`2 * ℓ` balls around the lattice. -/
theorem exists_lattice_dist_le_of_mem_periodicEnvelope_tsupport {ℓ : ℝ} (hℓ : 0 < ℓ)
    {a : Vec3} (ha : a ∈ tsupport (periodizeCentered (radialEnvelope ℓ))) :
    ∃ n : Fin 3 → ℤ, dist (latticeVector n) a ≤ 2 * ℓ := by
  let L : Set Vec3 := range latticeVector
  let S : Set Vec3 := {y | Metric.infDist y L ≤ 2 * ℓ}
  have hs : IsClosed S := isClosed_Iic.preimage (Metric.continuous_infDist_pt L)
  have hsub : Function.support (periodizeCentered (radialEnvelope ℓ)) ⊆ S := by
    intro y hy
    let n : Fin 3 → ℤ := fun i => ⌊y i + 1 / 2⌋
    have hy' : radialEnvelope ℓ (centeredLabel y) ≠ 0 := hy
    have hcenter : centeredLabel y = y - latticeVector n := by
      apply PiLp.ext
      intro i
      change Int.fract (y i + 1 / 2) - 1 / 2 = y i - (⌊y i + 1 / 2⌋ : ℤ)
      rw [Int.fract]
      ring
    have hrad : ‖centeredLabel y‖ ≤ 2 * ℓ :=
      (lt_of_not_ge (fun h => hy' (radialEnvelope_eq_zero hℓ h))).le
    change Metric.infDist y L ≤ 2 * ℓ
    refine (Metric.infDist_le_dist_of_mem (s := L) (mem_range_self n)).trans ?_
    rw [dist_eq_norm, ← hcenter]
    exact hrad
  have ha' : Metric.infDist a L ≤ 2 * ℓ := closure_minimal hsub hs ha
  obtain ⟨_, ⟨n, rfl⟩, hdist⟩ := isClosed_range_latticeVector.exists_infDist_eq_dist
    (range_nonempty latticeVector) a
  exact ⟨n, by rw [dist_comm, ← hdist]; exact ha'⟩

/-- If the inverse label lies in the periodic envelope support, the
Eulerian point is at most `2 * D * ℓ` from a lattice point. -/
theorem IsLabelFlowOn.exists_lattice_dist_le_of_inverse_mem_periodicEnvelope_tsupport
    {U : Velocity} {X : ℝ → Velocity} {T t D ℓ : ℝ} (hT : 0 < T)
    (hX : IsLabelFlowOn U X (Icc 0 T)) (hℓ : 0 < ℓ)
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hUper : ∀ s ∈ Icc 0 T, SpatiallyPeriodic (U s))
    (hUodd : ∀ s ∈ Icc 0 T, Function.Odd (U s))
    (ht : t ∈ Icc 0 T) (hD : 0 ≤ D) (hF : ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D)
    {x : Vec3} (hx : X t 0 x ∈ tsupport (periodizeCentered (radialEnvelope ℓ))) :
    ∃ n : Fin 3 → ℤ, dist (latticeVector n) x ≤ D * (2 * ℓ) := by
  obtain ⟨n, hn⟩ := exists_lattice_dist_le_of_mem_periodicEnvelope_tsupport hℓ hx
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by norm_num)) hUper
  let D₀ : ℝ≥0 := ⟨D, hD⟩
  have hLip : LipschitzWith D₀ (X 0 t) :=
    lipschitzWith_of_nnnorm_fderiv_le (hX.differentiableAt_transition hT hU hUper h0 ht)
      (fun a => by exact_mod_cast hF a)
  have hfix : X 0 t (0 : Vec3) = 0 := by
    have h := (hX.odd hK hUodd h0 ht) (0 : Vec3)
    rw [neg_zero] at h
    apply PiLp.ext
    intro i
    have hi := congrArg (fun z : Vec3 => z i) h
    simp only [PiLp.neg_apply] at hi
    rw [PiLp.zero_apply]
    linarith
  have hfixn : X 0 t (latticeVector n) = latticeVector n := by
    simpa only [zero_add, hfix] using hX.add_latticeVector hK hUper h0 ht n 0
  have hInv : X 0 t (X t 0 x) = x := (hX.inverse hK h0 ht).2 x
  refine ⟨n, ?_⟩
  calc
    dist (latticeVector n) x = dist (X 0 t (latticeVector n)) (X 0 t (X t 0 x)) := by rw [hfixn, hInv]
    _ ≤ D * dist (latticeVector n) (X t 0 x) := hLip.dist_le_mul _ _
    _ ≤ D * (2 * ℓ) := mul_le_mul_of_nonneg_left hn hD

/-- The chosen negative-power radius confines the physical envelope to
the required inverse-parent-frequency distance from the lattice. -/
theorem IsLabelFlowOn.exists_lattice_dist_le_inv_of_inverse_mem_periodicEnvelope_tsupport
    {U : Velocity} {X : ℝ → Velocity} {T t D ℓ μ : ℝ} (hT : 0 < T)
    (hX : IsLabelFlowOn U X (Icc 0 T)) (hℓ : 0 < ℓ)
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hUper : ∀ s ∈ Icc 0 T, SpatiallyPeriodic (U s))
    (hUodd : ∀ s ∈ Icc 0 T, Function.Odd (U s))
    (ht : t ∈ Icc 0 T) (hμ : 2 ≤ μ) (hμD : μ ≤ D) (hell : ℓ ≤ (D ^ (3 : ℕ))⁻¹)
    (hF : ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D)
    {x : Vec3} (hx : X t 0 x ∈ tsupport (periodizeCentered (radialEnvelope ℓ))) :
    ∃ n : Fin 3 → ℤ, dist (latticeVector n) x ≤ μ⁻¹ := by
  have hμpos : 0 < μ := zero_lt_two.trans_le hμ
  have hDpos : 0 < D := hμpos.trans_le hμD
  obtain ⟨n, hn⟩ := hX.exists_lattice_dist_le_of_inverse_mem_periodicEnvelope_tsupport
    hT hℓ hU hUper hUodd ht hDpos.le hF hx
  refine ⟨n, hn.trans ?_⟩
  calc
    _ ≤ D * (2 * (D ^ (3 : ℕ))⁻¹) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hell zero_le_two) hDpos.le
    _ = 2 / D ^ (2 : ℕ) := by field_simp
    _ ≤ μ⁻¹ := by
      rw [← one_div μ]
      apply (div_le_div_iff₀ (pow_pos hDpos _) hμpos).2
      simpa only [one_mul, pow_two] using mul_le_mul (hμ.trans hμD) hμD hμpos.le hDpos.le

end TorusEuler
