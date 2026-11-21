import TorusEuler.Paper.Proofs.S5a.Library.TowerLift

/-!
# S5a library: the zero-order estimate for the tower system from Theorem 4.2

For every tower `u ∈ E` (a continuous solenoidal curve `v = u_∅` with `∫_0^T v = 0`) the
projected forcing `f = P(Kv)(t) - P(Kv)(0) - P ∫_0^t Ωv` satisfies `‖v‖ ≤ A ‖f‖`, where `A` is the
constant of the first item of Theorem 4.2: `v` is the velocity of a solution of the integrated system
(4.9) with source `L = -f` (`sections/06d_mean_estimates.tex:48-49`, "Theorem 4.2 bounds the map
`L ↦ v` by `A`").
-/

open Set
open scoped ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace TorusEuler.Paper.Lib.S5a.Tower

noncomputable section

local notation "C½" => HalfHolder (UnitAddTorus (Fin 3)) Vec3
local notation "K½" => HalfHolder (UnitAddTorus (Fin 3)) (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal

local instance towerZeroSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance towerZeroSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

variable {T : ℝ}

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Pr_coe`. -/
theorem Pr_coe (s : S) : endpointStrongSpatialProjection (s : C½) = s :=
  Subtype.ext ((endpointStrongSpatialLeray_fixed_iff s.val).mpr s.property)

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `endpointClosedTimeNorm_congr`. -/
theorem endpointClosedTimeNorm_congr {X : Type*} [NormedAddCommGroup X] {f g : ℝ → X}
    (h : EqOn f g (Icc 0 T)) : endpointClosedTimeNorm T f = endpointClosedTimeNorm T g := by
  unfold endpointClosedTimeNorm
  congr 1
  apply Set.image_congr
  intro t ht
  rw [h ht]

/-- **The zero-order estimate** for towers, from the first item of Theorem 4.2. -/
theorem zero_order (hT : 0 < T) {K Ω : ℝ → K½} (hKc : ContinuousOn K (Icc 0 T))
    (hΩc : ContinuousOn Ω (Icc 0 T)) {A : ℝ}
    (H1 : ∀ src : ℝ → C½, ContinuousOn src (Icc 0 T) →
      ∃ (z v : ℝ → S) (c : S) (φ : Pressure) (G : ℝ → C½),
        EndpointSystemSolution T K Ω src z v c φ G ∧
        endpointClosedTimeNorm T v ≤ A * endpointClosedTimeNorm T src ∧
        ∀ (z' v' : ℝ → S) (c' : S) (φ' : Pressure) (G' : ℝ → C½),
          EndpointSystemSolution T K Ω src z' v' c' φ' G' →
          EqOn z' z (Icc 0 T) ∧ EqOn v' v (Icc 0 T) ∧ c' = c ∧ EqOn G' G (Icc 0 T))
    {aK aΩ : Wd → ℝ → K½} (haK : aK ∈ tower T K½) (haΩ : aΩ ∈ tower T K½)
    (hKe : EqOn (aK []) K (Icc 0 T)) (hΩe : EqOn (aΩ []) Ω (Icc 0 T)) :
    ∀ u ∈ Esp T hT.le, endpointClosedTimeNorm T (u []) ≤
      A * endpointClosedTimeNorm T (Tk aK u [] + Tom T aΩ u []) := by
  intro u hu
  let : CompleteSpace S := isClosed_endpointHalfHolderSolenoidal.completeSpace_coe
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  let v : ℝ → S := u []
  have hvc : ContinuousOn v (Icc 0 T) := hu.1.2 []
  have hvT : endpointPrimitive v T = 0 := hu.2 []
  let f0 : ℝ → C½ := fun t => Tk aK u [] t + Tom T aΩ u [] t
  have hf0c : ContinuousOn f0 (Icc 0 T) :=
    (Tk_continuousOn haK hu.1 []).add (Tom_continuousOn hT haΩ hu.1 [])
  let x : ℝ → C½ := fun t => paperMeanIntegratedMomentum K Ω 0 v t
  -- the base words in terms of `K`, `Ω`, `v`
  have hTw : ∀ t ∈ Icc 0 T, Tw [] aK u t = (K t).coefficientMul (v t : C½) := by
    intro t ht
    simp only [Tw]
    rw [hKe ht]
  have hprim : ∀ t ∈ Icc 0 T, primC T (Tw [] aΩ u) t =
      endpointPrimitive (fun r => (Ω r).coefficientMul (v r : C½)) t := by
    intro t ht
    rw [primC_eq ht]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le ht.1]
    intro r hr
    have hr' : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
    simp only [Tw]
    rw [hΩe hr']
  have hx : ∀ t ∈ Icc 0 T, pjL (x t) - pjL (x 0) = f0 t := by
    intro t ht
    have e1 : x t = (K t).coefficientMul (v t : C½) -
        endpointPrimitive (fun r => (Ω r).coefficientMul (v r : C½)) t := by
      simp only [x, paperMeanIntegratedMomentum, Pi.zero_apply, add_zero]
    have e0 : x 0 = (K 0).coefficientMul (v 0 : C½) := by
      simp only [x, paperMeanIntegratedMomentum, Pi.zero_apply, add_zero, endpointPrimitive_zero,
        sub_zero]
    simp only [f0, Tk, Tom, hTw t ht, hTw 0 h0, hprim t ht, e1, e0, map_sub]
    abel
  -- the source `L = -f0` and the solution
  let L : ℝ → C½ := fun t => -f0 t
  have hLc : ContinuousOn L (Icc 0 T) := hf0c.neg
  let s : ℝ → S := fun t => endpointStrongSpatialProjection (x t) -
    endpointStrongSpatialProjection (x 0)
  have hs : ∀ t ∈ Icc 0 T, f0 t = (s t : C½) := by
    intro t ht
    rw [← hx t ht]
    rfl
  have hproj : ∀ t ∈ Icc 0 T, endpointStrongSpatialProjection
      (paperMeanIntegratedMomentum K Ω L v t) = endpointStrongSpatialProjection (x 0) := by
    intro t ht
    have e : paperMeanIntegratedMomentum K Ω L v t = x t + L t := by
      simp only [x, paperMeanIntegratedMomentum, Pi.zero_apply, add_zero, L]
    rw [e, map_add, show L t = -(s t : C½) by simp only [L, hs t ht], map_neg, Pr_coe]
    simp only [s]; abel
  let sol : PaperMeanIntegratedSolution T K Ω L :=
    ⟨v, endpointStrongSpatialProjection (x 0), hvc, hvT, hproj⟩
  obtain ⟨φ, Gφ, hGc, hG⟩ := sol.exists_potential hKc hΩc hLc
  have hess : EndpointSystemSolution T K Ω L (endpointPrimitive v) v
      (endpointStrongSpatialProjection (x 0)) φ Gφ :=
    ⟨hvc, fun t ht => hasDerivWithinAt_endpointPrimitive_of_continuousOn hvc ht,
      by simp only [endpointPrimitive, intervalIntegral.integral_same], hvT, hGc,
      fun t ht => ⟨(hG t ht).1, (hG t ht).2.2.1⟩, fun t ht => (hG t ht).2.2.2⟩
  obtain ⟨z0, v0, c0, φ0, G0, -, hb, huniq⟩ := H1 L hLc
  obtain ⟨-, hv, -, -⟩ := huniq _ _ _ _ _ hess
  have e1 : endpointClosedTimeNorm T v = endpointClosedTimeNorm T v0 :=
    endpointClosedTimeNorm_congr hv
  have e2 : endpointClosedTimeNorm T L = endpointClosedTimeNorm T f0 := by
    unfold endpointClosedTimeNorm
    simp only [L, norm_neg]
  have e3 : endpointClosedTimeNorm T (Tk aK u [] + Tom T aΩ u []) = endpointClosedTimeNorm T f0 :=
    rfl
  change endpointClosedTimeNorm T v ≤ _
  rw [e1, e3, ← e2]
  exact hb

end

end TorusEuler.Paper.Lib.S5a.Tower
