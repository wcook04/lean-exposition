import TorusEuler.Paper.Proofs.S5a.Library.TowerJets
import TorusEuler.Paper.Proofs.S5a.Library.MeanIntegrate

/-!
# S5a library: the velocity tower of a smooth mean solution lies in `E`

For a smooth divergence-free velocity `v = z_t` of the slab with displacement `z` (`z(0) = z(T) = 0`), the
symmetric tower of `v` consists of solenoidal curves (the Leray projection commutes with derivatives) with
`∫_0^T v_w = 0` (the words of `z` are the primitives of the words of `v`, `endpointSourceWords_eq_negPrimitive`):
it is an element of `Esp T`.
-/

open Set
open scoped ContDiff

namespace TorusEuler.Paper.Lib.S5a.Tower

noncomputable section

local notation "C½" => HalfHolder (UnitAddTorus (Fin 3)) Vec3
local notation "S" => endpointHalfHolderSolenoidal

local instance towerVelSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance towerVelSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `phaseOperatorWord_zero`. -/
theorem phaseOperatorWord_zero {ι : Type*} (D : ι → Vec3 → Vec3) (w : List ι) :
    phaseOperatorWord D w (fun _ : Vec3 => (0 : Vec3)) = fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    simp only [phaseOperatorWord, ih, phaseDirectionalDerivative]
    simp

/-- The symmetric tower of a smooth divergence-free velocity `v = z_t` with `z(0) = z(T) = 0` is an element of `Esp T` (the endpoint and divergence constraints are preserved by label derivatives, `sections/06d_mean_estimates.tex:46-47`). -/
theorem exists_velocityTower {T : ℝ} (hT : 0 < T) {v z : ℝ → Vec3 → Vec3}
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hz : ContDiffOn ℝ ∞ (Function.uncurry z) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hzper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (z t))
    (hz0 : z 0 = 0) (hzT : z T = 0)
    (hzd : ∀ t ∈ Icc 0 T, ∀ x, HasDerivWithinAt (fun r => z r x) (v t x) (Icc 0 T) t)
    (hdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (v t) x = 0)
    (Vt : SymTower T (Function.uncurry v)) :
    ∃ u : Wd → ℝ → S, u ∈ Esp T hT.le ∧ ∀ w, ∀ t ∈ Icc 0 T, ((u w t : S) : C½) = Vt.Y w t := by
  classical
  let : CompleteSpace S := isClosed_endpointHalfHolderSolenoidal.completeSpace_coe
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hvslice (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (v t) :=
    contDiffOn_univ.mp ((hv.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩)))
  -- the base words are solenoidal
  have hbase (t : ℝ) (ht : t ∈ Icc 0 T) : Vt.Y [] t ∈ endpointHalfHolderSolenoidal := by
    have hEval (x : Vec3) : (Vt.Y [] t).val.1 (toUnitTorus x) = v t x := Vt.lift [] t ht x
    exact (mem_endpointHalfHolderSolenoidal _).mpr
      ((endpointTorusGradientPairing_iff_divergence_free (hvslice t ht) hEval).mpr (hdiv t ht))
  have hmem := mem_solenoidal_of_der Vt.der hbase
  let u : Wd → ℝ → S := fun w t => if ht : t ∈ Icc 0 T then ⟨Vt.Y w t, hmem w t ht⟩ else 0
  have hu (w : Wd) (t : ℝ) (ht : t ∈ Icc 0 T) : ((u w t : S) : C½) = Vt.Y w t := by
    simp only [u, dite_eq_left ht]
  -- continuity
  have hcont (w : Wd) : ContinuousOn (u w) (Icc 0 T) := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply Continuous.subtype_mk
    exact (continuousOn_iff_continuous_domRestrict.mp (Vt.smooth w).continuousOn).congr
      (fun t => (hu w t t.property).symm)
  have hsym : ∀ p q : Wd, p.Perm q → u p = u q := by
    intro p q h
    funext t
    by_cases ht : t ∈ Icc 0 T
    · apply Subtype.ext
      rw [hu p t ht, hu q t ht]
      exact congrFun (Vt.sym p q h) t
    · simp only [u, dite_eq_right ht]
  -- the displacement tower
  obtain ⟨Zt⟩ := exists_symTower hT (fun p : ℝ × Vec3 => -(Function.uncurry z p)) hz.neg
    (fun t ht n x => by
      change -z t (x + latticeVector n) = -z t x
      rw [hzper t ht n x])
  have hFTC (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) :
      z t x = endpointPrimitive (fun r => v r x) t := by
    have hint : IntervalIntegrable (fun r => v r x) MeasureTheory.volume 0 t :=
      ((meanInt_slice_time hv x).continuousOn.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc
        ht.1
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      ((meanInt_slice_time hz x).continuousOn.mono (Icc_subset_Icc_right ht.2))
      (fun r hr => (hzd r ⟨hr.1.le, hr.2.le.trans ht.2⟩ x).hasDerivAt
        (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hr)
          (fun r' hr' => ⟨hr'.1.le, hr'.2.le.trans ht.2⟩))) hint
    rw [hz0] at h
    simpa only [endpointPrimitive, Pi.zero_apply, sub_zero] using h.symm
  have hBase : EqOn (Zt.Y []) (fun t => -endpointPrimitive (Vt.Y []) t) (Icc 0 T) :=
    endpointSourceCurve_eq_negPrimitive_of_lift (Zt.Y []) (Vt.Y []) (fun t x => v t x)
      (Vt.smooth []).continuousOn (fun t ht x => Vt.lift [] t ht x)
      (fun t ht x => by
        have h := Zt.lift [] t ht x
        change _ = -z t x at h
        rw [h, hFTC t ht x])
  have hkey (q : Wd) : EqOn (Zt.Y q) (fun t => -endpointPrimitive (Vt.Y q) t) (Icc 0 T) :=
    endpointSourceWords_eq_negPrimitive hT Zt.Y Vt.Y coordinateDirection q.length
      (fun r _ => (Zt.smooth r).differentiableOn (by simp))
      (fun r _ => (Vt.smooth r).continuousOn)
      (fun i r _ t ht => Zt.der i r t ht) (fun i r _ t ht => Vt.der i r t ht) hBase q le_rfl
  have hprimC (q : Wd) : endpointPrimitive (Vt.Y q) T = 0 := by
    have h1 := hkey q ⟨hT.le, le_rfl⟩
    have h2 : Zt.Y q T = 0 := by
      apply HalfHolder.ext
      intro a
      obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
      rw [Zt.lift q T ⟨hT.le, le_rfl⟩ x]
      have hf : (fun y => (fun p : ℝ × Vec3 => -(Function.uncurry z p)) (T, y)) = fun _ => 0 := by
        funext y
        change -z T y = 0
        rw [hzT]; simp
      rw [spatialDerivativeWord, hf, phaseOperatorWord_zero]
      simp
    rw [h2] at h1
    exact (neg_eq_zero.mp h1.symm)
  have hprim (w : Wd) : endpointPrimitive (u w) T = 0 := by
    apply Subtype.ext
    have hi : IntervalIntegrable (u w) MeasureTheory.volume 0 T :=
      (hcont w).intervalIntegrable_of_Icc hT.le
    change endpointHalfHolderSolenoidal.subtypeL (∫ r in (0 : ℝ)..T, u w r) = 0
    rw [← endpointHalfHolderSolenoidal.subtypeL.intervalIntegral_comp_comm hi]
    have : (∫ r in (0 : ℝ)..T, endpointHalfHolderSolenoidal.subtypeL (u w r)) =
        ∫ r in (0 : ℝ)..T, Vt.Y w r := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le hT.le]
      intro r hr
      exact hu w r hr
    rw [this]
    exact hprimC w
  exact ⟨u, ⟨⟨hsym, hcont⟩, hprim⟩, hu⟩

end

end TorusEuler.Paper.Lib.S5a.Tower
