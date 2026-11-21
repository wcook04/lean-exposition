import TorusEuler.PaperTruncatedHierarchyBounds
import TorusEuler.HierarchyPhysicalVelocityBounds
import TorusEuler.HierarchyHigherPressure

/-! The parent estimates required for the Eulerian readout in Lemmas 5.8–5.10. -/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile.TruncatedHierarchyParent

noncomputable section

open InductiveEulerStage

variable {U : Velocity} {X : ℝ → Velocity} {p : Pressure} {T : ℝ}
  {k : Vec3} {hT : 0 < T}

local notation "Time(" T ")" => Icc (0 : ℝ) T
local notation "G(" X "," t ")" => (fun x : Vec3 => fderiv ℝ (X t 0) (X 0 t x))
local notation "L(" C "," n ")" => stageCoframeOrderConstant C n
local notation "ℓ(" D "," a ")" => ((D ^ a)⁻¹)

/-- Uniform Eulerian parent estimates and their label-coordinate versions.
The constants `R` and `C` depend only on derivative order. -/
structure PhysicalParentInputs (d : ParentGeometry hT U X k) (D freq : ℝ)
    (a e : ℕ) (R C : ℕ → ℝ) : Prop where
  radius_pos : 0 < ℓ(D,a)
  radius_le_one : ℓ(D,a) ≤ 1
  radius_scale : ℓ(D,a) * D ^ (7 : ℕ) ≤ 1
  radius_inverse : ℓ(D,a)⁻¹ = D ^ a
  carrier : ‖k‖ ≤ D * freq
  deformation : ∀ t ∈ Time(T), ∀ x,
    ‖fderiv ℝ (X 0 t) x‖ ≤ D ∧ ‖fderiv ℝ (X t 0) x‖ ≤ D
  inverse_smooth : ∀ t ∈ Time(T), ContDiff ℝ ∞ (X t 0)
  coframe_readout : ∀ t ∈ Time(T), ∀ x, G(X,t) (X t 0 x) = fderiv ℝ (X t 0) x
  coframe_smooth : ∀ t ∈ Time(T), ContDiff ℝ ∞ G(X,t)
  velocity_jets : ∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Time(T), ∀ x,
    ‖iteratedFDeriv ℝ j (U t) x‖ ≤ R n * D ^ j
  coframe_jets : ∀ j, ∀ t ∈ Time(T), ∀ x,
    ‖iteratedFDeriv ℝ j G(X,t) x‖ ≤ C j * D ^ (7 * j + 1)
  scaled_coframe : ∀ n, ∀ t ∈ Time(T), ∀ j ≤ n, ∀ x,
    ℓ(D,a) ^ j * ‖iteratedFDeriv ℝ j G(X,t) x‖ ≤ L(C,n) * D
  geometry_coframe : ∀ t ∈ Time(T), (fun x => d.inverse.val.val.val (t, x, 0)) = G(X,t)
  pressure_coframe : ∀ t ∈ Time(T), ∀ j ≤ 2, ∀ x,
    ℓ(D,a) ^ j * ‖iteratedFDeriv ℝ j (fun x => d.inverse.val.val.val (t, x, 0)) x‖ ≤ L(C,2) * D ^ (24 : ℕ)
  pressure_adjoint : ∀ t ∈ Time(T), ∀ j ≤ 1, ∀ x,
    ℓ(D,a) ^ j * ‖iteratedFDeriv ℝ j (fun y => (d.inverse.val.val.val (t, y, 0)).adjoint) x‖ ≤ L(C,2) * D ^ (24 : ℕ)
  pressure_strain : ∀ t ∈ Time(T), ∀ j ≤ 1, ∀ x,
    ℓ(D,a) ^ j * ‖iteratedFDeriv ℝ j (fun y => d.strain.val.val.val (t, y, 0)) x‖ ≤
      L(C,2) * D ^ (24 : ℕ)
  pressure_projection : ∀ t ∈ Time(T), ∀ j ≤ 1, ∀ x,
    ℓ(D,a) ^ j * ‖iteratedFDeriv ℝ j
      (fun y => hierarchyLongitudinalProjection (d.covector.val.val.val (t, y, 0))) x‖ ≤
        L(C,2) * D ^ (24 : ℕ)
  pressure_cost : ℓ(D,a)⁻¹ * (L(C,2) * D ^ (24 : ℕ)) ≤ D ^ (a + 24 + e)
  parent_gradient : ∀ t ∈ Time(T), SpatialHolderHalf 0 (fderiv ℝ (U t)) ∧
    spatialHolderHalfNorm 0 (fderiv ℝ (U t)) ≤ (3 * R 2) * D ^ (2 : ℕ)

private theorem gradient_holder_of_jets {u : Vec3 → Vec3} {D R : ℝ}
    (hu : ContDiff ℝ ∞ u) (hD : 1 ≤ D) (hR : 0 ≤ R)
    (hjet : ∀ j : ℕ, 1 ≤ j → j ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ j u x‖ ≤ R * D ^ j) :
    SpatialHolderHalf 0 (fderiv ℝ u) ∧ spatialHolderHalfNorm 0 (fderiv ℝ u) ≤ 3 * R * D ^ 2 := by
  have h : ∀ j ≤ 0 + 1, ∀ x, ‖iteratedFDeriv ℝ j (fderiv ℝ u) x‖ ≤ R * D ^ 2 := by
    intro j hj x
    rw [norm_iteratedFDeriv_fderiv]
    exact (hjet (j + 1) (by omega) (by omega) x).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) hR)
  obtain ⟨hs, hb⟩ := spatialHolderHalfNorm_le_of_uniformJets (m := 0)
    (hu.fderiv_right (m := ∞) (by simp)) (by positivity) h
  refine ⟨hs, hb.trans_eq ?_⟩
  norm_num
  ring

set_option maxHeartbeats 2400000 in
/-- The uniform parent estimates hold for each Fourier-truncated parent in
§5, with the launch frequency measured at the center. -/
theorem exists_physicalParentInputs :
    ∃ (R C : ℕ → ℝ) (e : ℕ), (∀ j, 0 ≤ R j) ∧ (∀ j, 0 ≤ C j) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {p : Pressure} {T D freq t₀ : ℝ}
        {k : Vec3} {hT : 0 < T} {d : ParentGeometry hT U X k},
        TruncatedHierarchyParent d p D freq → t₀ ∈ Icc 0 T →
        ‖labelWaveVector X 0 0 k t₀‖ = freq → ∀ a : ℕ, 7 ≤ a →
          PhysicalParentInputs d D freq a e R C := by
  obtain ⟨R, hR, hVelocity⟩ := exists_parentVelocityJetBounds
  obtain ⟨C, hC, hParent⟩ := exists_parent_coefficientJetBounds R hR
  obtain ⟨e, he⟩ := pow_unbounded_of_one_lt (L(C,2)) (by norm_num : (1 : ℝ) < 2)
  refine ⟨R, C, e, hR, hC, ?_⟩
  intro U X p T D freq t₀ k hT d data ht₀ hc a ha
  let ell := ℓ(D,a)
  have hD := one_le_two.trans data.scale_ge_two
  have hDpos := zero_lt_one.trans_le hD
  have hf := zero_lt_one.trans_le data.frequency_ge_one
  have hEll : 0 < ell := inv_pos.mpr (pow_pos hDpos _)
  have hEll₁ : ell ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hD)
  have hScale : ell * D ^ (7 : ℕ) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD ha) hEll.le).trans
      (inv_mul_cancel₀ (pow_pos hDpos _).ne').le
  have hVel (m j : ℕ) (hj : 1 ≤ j) (hm : j ≤ m) (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) :
      ‖iteratedFDeriv ℝ j (U t) x‖ ≤ R m * D ^ j := by
    rw [← data.velocity_lift t ht]
    exact hVelocity (data.torusVelocity t) hD
      (fun z hz => data.velocity_band t ht z (by linarith [hDpos.le]))
      (by rw [data.velocity_lift t ht]; exact data.velocity_gradient_le t ht) m j hj hm x
  have hJets := hParent hT data.time_le_one hD data.flow data.velocity_smooth data.velocity_periodic
    data.deformation_le data.inverse_deformation_le hVel k hf ht₀ hc
  have hGraph (t : ℝ) (ht : t ∈ Time(T)) :=
    PhysicalApproximationData.graphCoframe_geometry hT data.flow data.velocity_smooth data.velocity_periodic ht
  have hK (n : ℕ) : 1 ≤ L(C,n) := stageCoframeOrderConstant_ge_one C hC n
  have hCj (n j : ℕ) (hj : j ≤ n) : C j ≤ L(C,n) :=
    (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).trans
      (le_add_of_nonneg_left zero_le_one)
  have hScaled (n : ℕ) (t : ℝ) (ht : t ∈ Time(T)) :
      ∀ j ≤ n, ∀ x, ell ^ j * ‖iteratedFDeriv ℝ j G(X,t) x‖ ≤ L(C,n) * D := by
    apply scaledCoframe_jet_bound hEll.le hD (zero_le_one.trans (hK n)) hScale
    intro j hj x
    exact (hJets j t ht x).2.1.trans (mul_le_mul_of_nonneg_right (hCj n j hj) (by positivity))
  have hGvalue (t : ℝ) (ht : t ∈ Time(T)) : (fun x => d.inverse.val.val.val (t, x, 0)) = G(X,t) :=
    funext fun x => d.inverse_value (t, x, 0) ⟨ht, mem_univ _⟩
  have hWiden {u : ℝ} {j l : ℕ} (hj : j ≤ 1) (hl : l ≤ 24) (hu : 0 ≤ u)
      (hb : u ≤ C j * D ^ l) : ell ^ j * u ≤ L(C,2) * D ^ (24 : ℕ) :=
    (mul_le_of_le_one_left hu (pow_le_one₀ hEll.le hEll₁)).trans
      (hb.trans (mul_le_mul (hCj 2 j (by omega)) (pow_le_pow_right₀ hD hl)
        (by positivity) (zero_le_one.trans (hK 2))))
  refine {
    radius_pos := hEll
    radius_le_one := hEll₁
    radius_scale := hScale
    radius_inverse := inv_inv _
    carrier := (div_le_iff₀ hf).mp
      (data.flow.norm_normalizedLabelWaveVector_bounds hT (data.velocity_smooth.of_le (by simp))
        data.velocity_periodic ht₀ ht₀ 0 k hD hf hc
        (data.deformation_le t₀ ht₀ 0) (data.inverse_deformation_le t₀ ht₀ 0)
        (data.deformation_le t₀ ht₀ 0) (data.inverse_deformation_le t₀ ht₀ 0)).1
    deformation := fun t ht x => ⟨data.deformation_le t ht x,
      (hGraph t ht).2.1 x ▸ data.inverse_deformation_le t ht (X t 0 x)⟩
    inverse_smooth := fun t ht => (hGraph t ht).1
    coframe_readout := fun t ht => (hGraph t ht).2.1
    coframe_smooth := fun t ht => (hGraph t ht).2.2
    velocity_jets := hVel
    coframe_jets := fun j t ht x => (hJets j t ht x).2.1
    scaled_coframe := hScaled
    geometry_coframe := hGvalue
    pressure_coframe := ?_
    pressure_adjoint := ?_
    pressure_strain := ?_
    pressure_projection := ?_
    pressure_cost := ?_
    parent_gradient := ?_ }
  · intro t ht j hj x
    rw [hGvalue t ht]
    exact (hScaled 2 t ht j hj x).trans
      (mul_le_mul_of_nonneg_left (by
        conv_lhs => rw [← pow_one D]
        exact pow_le_pow_right₀ hD (by decide : 1 ≤ (24 : ℕ)))
        (zero_le_one.trans (hK 2)))
  · intro t ht j hj x
    rw [show (fun y => (d.inverse.val.val.val (t, y, 0)).adjoint) =
      (fun y => (G(X,t) y).adjoint) from
      congrArg (fun f : Vec3 → Vec3 →L[ℝ] Vec3 => fun y => (f y).adjoint) (hGvalue t ht)]
    exact hWiden hj (by omega) (norm_nonneg _) (hJets j t ht x).2.2.1
  · intro t ht j hj x
    rw [show (fun y => d.strain.val.val.val (t, y, 0)) =
      (fun y => fderiv ℝ (U t) (X 0 t y)) from
      funext fun y => d.strain_value (t, y, 0) ⟨ht, mem_univ _⟩]
    exact hWiden hj (by omega) (norm_nonneg _) (hJets j t ht x).2.2.2.1
  · intro t ht j hj x
    rw [show (fun y => hierarchyLongitudinalProjection (d.covector.val.val.val (t, y, 0))) =
      (fun y => hierarchyLongitudinalProjection (labelWaveVector X 0 y k t)) from
      funext fun y => congrArg hierarchyLongitudinalProjection
        (d.covector_value (t, y, 0) ⟨ht, mem_univ _⟩)]
    exact hWiden hj (by omega) (norm_nonneg _) (hJets j t ht x).2.2.2.2.2.2
  · rw [inv_inv, pow_add D (a + 24), pow_add D a]
    have hE := he.le.trans (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) data.scale_ge_two e)
    calc
      _ ≤ D ^ a * (D ^ e * D ^ (24 : ℕ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hE (by positivity)) (by positivity)
      _ = _ := by ring
  · intro t ht
    have hU : ContDiff ℝ ∞ (U t) :=
      contDiffOn_univ.mp (data.velocity_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun x _ => ⟨ht, mem_univ x⟩))
    exact gradient_holder_of_jets hU hD (hR 2) (fun j hj hj₂ x => hVel 2 j hj hj₂ t ht x)

/-- The standing Fourier, flow, and coercivity hypotheses supply the
actual parent geometry used by the hierarchy and its physical readout. -/
theorem exists_of_torus_bands_and_coercivity {D freq : ℝ}
    (hT : 0 < T) (hTime : T ≤ 1) (hD : 2 ≤ D) (hf : 1 ≤ freq) (hk : k ≠ 0)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.prod (Icc 0 T) (univ : Set Vec3)))
    (hp : ContDiffOn ℝ ∞ (Function.uncurry p) (Set.prod (Icc 0 T) (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (hF : ∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D)
    (hG : ∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D)
    (hM : ∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (U t) x‖ ≤ D)
    (hUpper : ∀ t ∈ Icc 0 T, ∀ x v : Vec3,
      ⟪(fderiv ℝ (gradient (p t)) x - fderiv ℝ (momentumResidual (Icc 0 T) U p t) x) v, v⟫_ℝ ≤ ‖v‖ ^ 2)
    (v r : ℝ → C(UnitAddTorus (Fin 3), Vec3))
    (hv : ∀ t ∈ Icc 0 T, (fun x => v t (toUnitTorus x)) = U t)
    (hr : ∀ t ∈ Icc 0 T, ∀ x, r t (toUnitTorus x) = momentumResidual (Icc 0 T) U p t x)
    (hvBand : ∀ t ∈ Icc 0 T, RealTorusFourierBand (2 * D) (v t))
    (hrBand : ∀ t ∈ Icc 0 T, RealTorusFourierBand (4 * D) (r t))
    (hrSize : ∀ t ∈ Icc 0 T, ‖r t‖ ≤ freq ^ (-5 / 2 : ℝ)) :
    ∃ d : ParentGeometry hT U X k, Nonempty (TruncatedHierarchyParent d p D freq) := by
  have hPressure (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) : DifferentiableAt ℝ (gradient (p t)) x := by
    have hSlice : ContDiff ℝ ∞ (p t) :=
      contDiffOn_univ.mp (hp.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun x _ => ⟨ht, mem_univ x⟩))
    exact ((InnerProductSpace.toDual ℝ Vec3).symm.contDiff.comp
      (hSlice.fderiv_right (m := ∞) (by simp))).differentiable (by simp) x
  have hD₁ : 1 ≤ D := one_le_two.trans hD
  obtain ⟨d, hInverse, hStrain⟩ := exists_parentGeometry_withBounds hT hX hk hU hper
    hPressure hD₁ (zero_le_one.trans hD₁) hG hM hUpper
  exact ⟨d, ⟨⟨hTime, hD, hf, hX, hU, hper, hF, hG, hM, hInverse.le, hStrain.le,
    v, r, hv, hr, hvBand, hrBand, hrSize⟩⟩⟩

end

end TorusEuler.HierarchyTwistedProfile.TruncatedHierarchyParent
