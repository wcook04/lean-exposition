import Mathlib.Geometry.Manifold.PartitionOfUnity
import TorusEuler.PeriodicLift

/-! Lattice periodization of a smooth extension on the punctured lift. -/

noncomputable section

open Filter Function Set Metric
open scoped ContDiff Manifold Topology

namespace TorusEuler

local notation "LatticeIndex" => Fin 3 → ℤ

private theorem latticeVector_add_extension (k l : LatticeIndex) :
    latticeVector (k + l) = latticeVector k + latticeVector l := by
  apply PiLp.ext
  intro i
  change (((k i) + (l i) : ℤ) : ℝ) = (k i : ℝ) + (l i : ℝ)
  exact Int.cast_add _ _

private theorem latticeVector_sub_extension (k l : LatticeIndex) :
    latticeVector (k - l) = latticeVector k - latticeVector l := by
  apply PiLp.ext
  intro i
  change (((k i) - (l i) : ℤ) : ℝ) = (k i : ℝ) - (l i : ℝ)
  exact Int.cast_sub _ _

private theorem sub_latticeVector_mem_offOrigin {x : Vec3} (hx : x ∈ offOrigin) (k : LatticeIndex) :
    x - latticeVector k ∈ offOrigin := by
  rintro ⟨l, hl⟩
  apply hx
  exact ⟨l + k, by rw [latticeVector_add_extension, hl, sub_add_cancel]⟩

private theorem latticeVector_norm_le_finite (R : ℝ) :
    {k : LatticeIndex | ‖latticeVector k‖ ≤ R}.Finite := by
  let M : ℤ := ⌈R⌉
  refine (Set.Finite.pi (t := fun _ : Fin 3 => Icc (-M) M) (fun _ => finite_Icc _ _)).subset ?_
  intro k hk i _
  have hz : |(k i : ℝ)| ≤ R :=
    ((PiLp.norm_apply_le (latticeVector k) i : ‖(k i : ℝ)‖ ≤ ‖latticeVector k‖).trans hk)
  have htop : (k i : ℝ) ≤ (M : ℝ) := (abs_le.mp hz).2.trans (Int.le_ceil _)
  have hbot : -(M : ℝ) ≤ (k i : ℝ) := (neg_le_neg (Int.le_ceil R)).trans (abs_le.mp hz).1
  exact ⟨by exact_mod_cast hbot, by exact_mod_cast htop⟩

private theorem locallyFinite_latticeTranslateSupport (φ : ContDiffBump (0 : Vec3)) :
    LocallyFinite (fun k : LatticeIndex => support (fun x => φ (x - latticeVector k))) := by
  intro x
  refine ⟨ball x 1, ball_mem_nhds x zero_lt_one,
    (latticeVector_norm_le_finite (‖x‖ + 1 + φ.rOut)).subset ?_⟩
  rintro k ⟨y, hyφ, hyx⟩
  have hyφ' : y - latticeVector k ∈ support (φ : Vec3 → ℝ) := hyφ
  rw [φ.support_eq] at hyφ'
  have hdy : ‖y - latticeVector k‖ < φ.rOut := by
    simpa only [dist_zero_right] using mem_ball.mp hyφ'
  have hxy : ‖y - x‖ < 1 := by simpa only [dist_eq_norm] using mem_ball.mp hyx
  have hy : ‖y‖ ≤ ‖x‖ + 1 := calc
    ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
    _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl hxy.le
  calc
    ‖latticeVector k‖ = ‖y - (y - latticeVector k)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖y‖ + ‖y - latticeVector k‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add hy hdy.le

private theorem latticeTranslate_reindex (x : Vec3) (k j : LatticeIndex) :
    (x + latticeVector k) - latticeVector j = x - latticeVector ((Equiv.subRight k) j) := by
  change (x + latticeVector k) - latticeVector j = x - latticeVector (j - k)
  rw [latticeVector_sub_extension]
  abel

/-- A smooth field on the punctured Euclidean lift can be periodized by a
locally finite weighted lattice sum. The periodization preserves equality
with a periodic field on any specified time set. -/
theorem exists_spatiallyPeriodic_contDiffOn_extension
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J A : Set ℝ} (hJ : IsOpen J) {f g : ℝ × Vec3 → F}
    (hg : ContDiffOn ℝ ∞ g (J ×ˢ offOrigin))
    (hagree : EqOn g f (A ×ˢ offOrigin))
    (hf : ∀ t ∈ A, SpatiallyPeriodic (fun x => f (t, x))) :
    ∃ G : ℝ × Vec3 → F, ContDiffOn ℝ ∞ G (J ×ˢ offOrigin) ∧
      EqOn G f (A ×ˢ offOrigin) ∧ ∀ t, SpatiallyPeriodic (fun x => G (t, x)) := by
  classical
  obtain ⟨R, hR, hcover⟩ := isCompact_centeredCell.isBounded.subset_closedBall_lt 0 0
  let φ : ContDiffBump (0 : Vec3) := ⟨R, R + 1, hR, lt_add_one R⟩
  let w (k : LatticeIndex) (x : Vec3) : ℝ := φ (x - latticeVector k)
  let d (x : Vec3) : ℝ := ∑ᶠ k, w k x
  let shift (k : LatticeIndex) (z : ℝ × Vec3) : ℝ × Vec3 := (z.1, z.2 - latticeVector k)
  let N (z : ℝ × Vec3) : F := ∑ᶠ k, w k z.2 • g (shift k z)
  let G (z : ℝ × Vec3) : F := (d z.2)⁻¹ • N z
  have hw : LocallyFinite (fun k => support (w k)) := locallyFinite_latticeTranslateSupport φ
  have hpos (x : Vec3) : 0 < d x := by
    obtain ⟨k, hk⟩ := exists_sub_latticeVector_mem_centeredCell x
    have h1 : w k x = 1 := φ.one_of_mem_closedBall (hcover hk)
    have hle : w k x ≤ d x := single_le_finsum k (hw.point_finite x) (fun j => φ.nonneg)
    rw [h1] at hle
    exact zero_lt_one.trans_le hle
  have hwSmooth (k : LatticeIndex) : ContDiff ℝ ∞ (w k) :=
    φ.contDiff.comp (contDiff_id.sub contDiff_const)
  have hdSmooth (x : Vec3) : ContDiffAt ℝ ∞ d x :=
    contMDiffAt_iff_contDiffAt.mp
      (contMDiffAt_finsum hw fun k => (hwSmooth k).contDiffAt.contMDiffAt)
  have hshiftSmooth (k : LatticeIndex) : ContDiff ℝ ∞ (shift k) :=
    contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)
  have hN (z : ℝ × Vec3) (hz : z ∈ J ×ˢ offOrigin) : ContDiffAt ℝ ∞ N z := by
    have hLoc : LocallyFinite (fun k => support (fun y : ℝ × Vec3 => w k y.2 • g (shift k y))) :=
      (hw.preimage_continuous (continuous_snd : Continuous (Prod.snd : ℝ × Vec3 → Vec3))).subset
        (fun k y hh hw0 => hh (show w k y.2 • g (shift k y) = 0 by rw [hw0, zero_smul]))
    have hs (k : LatticeIndex) : shift k z ∈ J ×ˢ offOrigin :=
      ⟨hz.1, sub_latticeVector_mem_offOrigin hz.2 k⟩
    refine contMDiffAt_iff_contDiffAt.mp (contMDiffAt_finsum hLoc fun k => ?_)
    exact ((((hwSmooth k).contDiffAt.comp z contDiffAt_snd).smul
      (((hg (shift k z) (hs k)).contDiffAt ((hJ.prod isOpen_offOrigin).mem_nhds (hs k))).comp z
        (hshiftSmooth k).contDiffAt))).contMDiffAt
  refine ⟨G, ?_, ?_, ?_⟩
  · intro z hz
    exact ((((hdSmooth z.2).comp z contDiffAt_snd).inv (hpos z.2).ne').smul
      (hN z hz)).contDiffWithinAt
  · intro z hz
    have hNf : N z = ∑ᶠ k, w k z.2 • f z := by
      apply finsum_congr
      intro k
      have hmem : shift k z ∈ A ×ˢ offOrigin := ⟨hz.1, sub_latticeVector_mem_offOrigin hz.2 k⟩
      rw [hagree hmem]
      have hper := hf z.1 hz.1 k (z.2 - latticeVector k)
      change f (z.1, z.2 - latticeVector k + latticeVector k) = f (shift k z) at hper
      rw [sub_add_cancel] at hper
      rw [← hper]
    change (d z.2)⁻¹ • N z = f z
    rw [hNf, ← finsum_smul]
    change (d z.2)⁻¹ • (d z.2 • f z) = f z
    rw [smul_smul, inv_mul_cancel₀ (hpos z.2).ne', one_smul]
  · intro t k x
    have hDper : d (x + latticeVector k) = d x :=
      finsum_eq_of_bijective _ (Equiv.subRight k).bijective fun j => by
        simp only [w, latticeTranslate_reindex x k j]
    have hNper : N (t, x + latticeVector k) = N (t, x) :=
      finsum_eq_of_bijective _ (Equiv.subRight k).bijective fun j => by
        simp only [w, shift, latticeTranslate_reindex x k j]
    change (d (x + latticeVector k))⁻¹ • N (t, x + latticeVector k) = (d x)⁻¹ • N (t, x)
    rw [hDper, hNper]

end TorusEuler
