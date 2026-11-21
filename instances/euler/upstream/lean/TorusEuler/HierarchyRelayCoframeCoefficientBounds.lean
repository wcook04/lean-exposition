import TorusEuler.HierarchyLinearRelayBounds

/-! Parent derivative bounds for the geometric coefficients in the linear relay. -/

open ContinuousLinearMap
open scoped ContDiff

namespace TorusEuler

noncomputable section

local notation "Coefficient" => Vec3 →L[ℝ] Vec3

private theorem norm_crossLeft_le (v : Vec3) : ‖cross3Left v‖ ≤ ‖v‖ :=
  (cross3Left v).opNorm_le_bound (norm_nonneg v) fun w => norm_cross3_le v w

private def relayCrossLeftCLM : Vec3 →L[ℝ] Coefficient :=
  ({ toFun := cross3Left
     map_add' := fun u v => by
       ext1 w
       apply WithLp.ofLp_injective
       simp only [add_apply, cross3Left_apply, cross3, WithLp.ofLp_add, WithLp.ofLp_toLp,
         map_add, LinearMap.add_apply]
     map_smul' := fun r v => by
       ext1 w
       apply WithLp.ofLp_injective
       simp only [smul_apply, cross3Left_apply, cross3, WithLp.ofLp_smul, WithLp.ofLp_toLp,
         map_smul, LinearMap.smul_apply, RingHom.id_apply] } : Vec3 →ₗ[ℝ] Coefficient).mkContinuous
    1 fun v => by simpa only [LinearMap.coe_mk, AddHom.coe_mk, one_mul] using norm_crossLeft_le v

private def relayAdjointCoordinate (i : Fin 3) : Coefficient →L[ℝ] Vec3 :=
  (ContinuousLinearMap.apply ℝ Vec3 (coordinateDirection i)).comp
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)).toLinearIsometry.toContinuousLinearMap

private theorem norm_adjoint_coordinate_le (A : Coefficient) (i : Fin 3) :
    ‖A.adjoint (coordinateDirection i)‖ ≤ ‖A‖ := by
  have hnorm : ‖A.adjoint‖ = ‖A‖ := LinearIsometryEquiv.norm_map _ _
  simpa only [hnorm, show ‖coordinateDirection i‖ = 1 by simp [coordinateDirection], mul_one]
    using A.adjoint.le_opNorm (coordinateDirection i)

def relayCurlRowCLM (ℓ : ℝ) (i : Fin 3) : Coefficient →L[ℝ] Coefficient :=
  ℓ⁻¹ • relayCrossLeftCLM.comp (relayAdjointCoordinate i)

def relayPressureRowCLM (ℓ : ℝ) (i : Fin 3) : Coefficient →L[ℝ] (ℝ →L[ℝ] Vec3) :=
  ℓ⁻¹ • (toSpanSingletonLIE ℝ Vec3).toLinearIsometry.toContinuousLinearMap.comp
    (relayAdjointCoordinate i)

private theorem relayCurlRowCLM_apply (ℓ : ℝ) (i : Fin 3) (G : Coefficient) :
    relayCurlRowCLM ℓ i G = hierarchyRelayCurlRow ℓ G i := rfl

private theorem relayPressureRowCLM_apply (ℓ : ℝ) (i : Fin 3) (G : Coefficient) :
    relayPressureRowCLM ℓ i G = hierarchyRelayPressureRow ℓ G i := rfl

private theorem norm_relayCurlRowCLM_le (ℓ : ℝ) (i : Fin 3) :
    ‖relayCurlRowCLM ℓ i‖ ≤ ‖ℓ⁻¹‖ := by
  refine (relayCurlRowCLM ℓ i).opNorm_le_bound (norm_nonneg _) fun G => ?_
  rw [relayCurlRowCLM_apply, hierarchyRelayCurlRow, norm_smul]
  exact mul_le_mul_of_nonneg_left
    ((norm_crossLeft_le _).trans (norm_adjoint_coordinate_le G i)) (norm_nonneg _)

private theorem norm_relayPressureRowCLM_le (ℓ : ℝ) (i : Fin 3) :
    ‖relayPressureRowCLM ℓ i‖ ≤ ‖ℓ⁻¹‖ := by
  refine (relayPressureRowCLM ℓ i).opNorm_le_bound (norm_nonneg _) fun G => ?_
  rw [relayPressureRowCLM_apply, hierarchyRelayPressureRow, norm_smul, norm_toSpanSingleton]
  exact mul_le_mul_of_nonneg_left (norm_adjoint_coordinate_le G i) (norm_nonneg _)

private theorem norm_iteratedFDeriv_geomRow_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Coefficient →L[ℝ] E) {a₀ : ℝ} (hP : ‖P‖ ≤ a₀)
    {G : Vec3 → Coefficient} (hG : ContDiff ℝ ∞ G) {j : ℕ} {x : Vec3}
    {B : ℝ} (hB : ‖iteratedFDeriv ℝ j G x‖ ≤ B) :
    ‖iteratedFDeriv ℝ j (P ∘ G) x‖ ≤ a₀ * B :=
  (P.norm_iteratedFDeriv_comp_left hG.contDiffAt (by simp)).trans
    (mul_le_mul hP hB (norm_nonneg _) ((norm_nonneg P).trans hP))


/-- A common bound for the geometric rows of the linear relay. -/
def hierarchyRelayGeometricRowBudget (C : ℕ → ℝ) (n : ℕ) (ℓ D : ℝ) : ℝ :=
  let A := ∑ j ∈ Finset.range (n + 1), C j
  (n + 1 : ℕ) * (A + 2 * (2 : ℝ) ^ n * A ^ 2) * (‖ℓ⁻¹‖ * D ^ 2)

set_option maxHeartbeats 1500000 in
/-- The actual curl, material commutator and pressure-gradient rows have a
common normalized budget. Each row contains the inverse label width.
The commutator contains both coframe and strain, so it costs two parent powers. -/
theorem hierarchyRelayGeometricCoefficientJets_of_parent_power_bounds
    {X : Type*} {ℓ h D : ℝ} (n : ℕ) (C : ℕ → ℝ) (G M : X → Vec3 → Coefficient)
    (hℓ : 0 ≤ ℓ) (hD : 1 ≤ D) (hscale : ℓ * D ^ (16 : ℕ) ≤ 1)
    (hC : ∀ j ≤ n, 0 ≤ C j)
    (hG : ∀ t, ContDiff ℝ ∞ (G t)) (hM : ∀ t, ContDiff ℝ ∞ (M t))
    (hGjets : ∀ t j, j ≤ n → ∀ a,
      ‖iteratedFDeriv ℝ j (G t) a‖ ≤ C j * D ^ (7 * j + 1))
    (hMjets : ∀ t j, j ≤ n → ∀ a,
      ‖iteratedFDeriv ℝ j (M t) a‖ ≤ C j * D ^ (6 * j + 1)) :
    let K := hierarchyRelayGeometricRowBudget C n ℓ D
    (∀ i, HierarchyRelayCoefficientJets ℓ h n K
      (fun t a => hierarchyRelayCurlRow ℓ (G t a) i)) ∧
    (∀ i, HierarchyRelayCoefficientJets ℓ h n K
      (fun t a => hierarchyRelayMaterialRow ℓ (G t a) (M t a) i)) ∧
    (∀ i, HierarchyRelayCoefficientJets ℓ h n K
      (fun t a => hierarchyRelayPressureRow ℓ (G t a) i)) := by
  let A := ∑ j ∈ Finset.range (n + 1), C j
  let B := A + 2 * (2 : ℝ) ^ n * A ^ 2
  let I := ‖ℓ⁻¹‖
  have hI : 0 ≤ I := norm_nonneg _
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hA : 0 ≤ A := Finset.sum_nonneg fun j hj => hC j
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hAB : A ≤ B := le_add_of_nonneg_right (by positivity)
  have hAB' : 2 * (2 : ℝ) ^ n * A ^ 2 ≤ B :=
    le_add_of_nonneg_left hA
  have hCA {j : ℕ} (hj : j ≤ n) : C j ≤ A :=
    Finset.single_le_sum (fun k hk => hC k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  have hGjet (t : X) (j : ℕ) (hj : j ≤ n) (a : Vec3) :
      ‖iteratedFDeriv ℝ j (G t) a‖ ≤ A * D ^ (7 * j + 1) :=
    (hGjets t j hj a).trans (mul_le_mul_of_nonneg_right (hCA hj) (pow_nonneg hD₀ _))
  have hMjet (t : X) (j : ℕ) (hj : j ≤ n) (a : Vec3) :
      ‖iteratedFDeriv ℝ j (M t) a‖ ≤ A * D ^ (7 * j + 1) := by
    calc
      _ ≤ C j * D ^ (6 * j + 1) := hMjets t j hj a
      _ ≤ A * D ^ (6 * j + 1) :=
        mul_le_mul_of_nonneg_right (hCA hj) (pow_nonneg hD₀ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) hA
  have hscale7 : ℓ * D ^ (7 : ℕ) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by norm_num : 7 ≤ 16)) hℓ).trans hscale
  have hLift {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : X → Vec3 → E) (hf : ∀ t, ContDiff ℝ ∞ (f t))
      (hj : ∀ t j, j ≤ n → ∀ a,
        ‖iteratedFDeriv ℝ j (f t) a‖ ≤ B * (I * D ^ 2) * D ^ (7 * j)) :
      HierarchyRelayCoefficientJets ℓ h n (hierarchyRelayGeometricRowBudget C n ℓ D) f := by
    have hcoef := HierarchyRelayCoefficientJets.of_parent_power_bound (h := h)
      (C := fun _ => B) hℓ hD₀ (mul_nonneg hI (sq_nonneg D)) hscale7 hf (fun _ _ => hB) hj
    simpa only [hierarchyRelayGeometricRowBudget, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, A, B, I] using hcoef
  have hlinear {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (P : Coefficient →L[ℝ] E) (hP : ‖P‖ ≤ I) :
      HierarchyRelayCoefficientJets ℓ h n (hierarchyRelayGeometricRowBudget C n ℓ D)
        (fun t => P ∘ G t) := by
    apply hLift _ (fun t => P.contDiff.comp (hG t))
    intro t j hj a
    calc
      _ ≤ I * (A * D ^ (7 * j + 1)) := norm_iteratedFDeriv_geomRow_le P hP (hG t) (hGjet t j hj a)
      _ ≤ I * (B * D ^ (7 * j + 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hAB (pow_le_pow_right₀ hD (Nat.le_succ _)) (pow_nonneg hD₀ _) hB) hI
      _ = _ := by rw [pow_add]; ring
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · change HierarchyRelayCoefficientJets ℓ h n (hierarchyRelayGeometricRowBudget C n ℓ D)
      (fun t => relayCurlRowCLM ℓ i ∘ G t)
    exact hlinear (relayCurlRowCLM ℓ i) (norm_relayCurlRowCLM_le ℓ i)
  · let P := relayCurlRowCLM ℓ i
    let curl (t : X) := P ∘ G t
    let GM (t : X) (a : Vec3) := (G t a).comp (M t a)
    let Mcurl (t : X) (a : Vec3) := (M t a).comp (curl t a)
    let Bcomp := compL ℝ Vec3 Vec3 Vec3
    have hP : ‖P‖ ≤ I := norm_relayCurlRowCLM_le ℓ i
    have hBcomp := norm_compL_le ℝ Vec3 Vec3 Vec3
    have hcurl (t : X) : ContDiff ℝ ∞ (curl t) := P.contDiff.comp (hG t)
    have hGM (t : X) : ContDiff ℝ ∞ (GM t) := (hG t).clm_comp (hM t)
    have hMcurl (t : X) : ContDiff ℝ ∞ (Mcurl t) := (hM t).clm_comp (hcurl t)
    have hcurlJet (t : X) (j : ℕ) (hj : j ≤ n) (a : Vec3) :
        ‖iteratedFDeriv ℝ j (curl t) a‖ ≤ (I * A) * D ^ (7 * j + 1) :=
      (norm_iteratedFDeriv_geomRow_le P hP (hG t) (hGjet t j hj a)).trans_eq (by ring)
    have hGMjet (t : X) (j : ℕ) (hj : j ≤ n) (a : Vec3) :
        ‖iteratedFDeriv ℝ j (GM t) a‖ ≤ (2 : ℝ) ^ j * (A * A) * D ^ (7 * j + 2) :=
      norm_iteratedFDeriv_bilinear_scaled_le Bcomp hBcomp (p := 7) (q := 1) (r := 1)
        ((hG t).of_le (by simp)) ((hM t).of_le (by simp)) a
        (fun k hk => hGjet t k (hk.trans hj) a) (fun k hk => hMjet t k (hk.trans hj) a)
    have hMcurlJet (t : X) (j : ℕ) (hj : j ≤ n) (a : Vec3) :
        ‖iteratedFDeriv ℝ j (Mcurl t) a‖ ≤ (2 : ℝ) ^ j * (A * (I * A)) * D ^ (7 * j + 2) :=
      norm_iteratedFDeriv_bilinear_scaled_le Bcomp hBcomp (p := 7) (q := 1) (r := 1)
        ((hM t).of_le (by simp)) ((hcurl t).of_le (by simp)) a
        (fun k hk => hMjet t k (hk.trans hj) a) (fun k hk => hcurlJet t k (hk.trans hj) a)
    have hMaterial : (fun t a => hierarchyRelayMaterialRow ℓ (G t a) (M t a) i) =
        (fun t => Mcurl t - P ∘ GM t) := by
      funext t a
      simp only [hierarchyRelayMaterialRow, Pi.sub_apply, Function.comp_apply,
        Mcurl, curl, GM, P, relayCurlRowCLM_apply]
    rw [hMaterial]
    refine hLift _ (fun t => (hMcurl t).sub (P.contDiff.comp (hGM t))) ?_
    intro t j hj a
    rw [iteratedFDeriv_sub_apply ((hMcurl t).of_le (by simp)).contDiffAt
      ((P.contDiff.comp (hGM t)).of_le (by simp)).contDiffAt]
    calc
      _ ≤ ‖iteratedFDeriv ℝ j (Mcurl t) a‖ + ‖iteratedFDeriv ℝ j (P ∘ GM t) a‖ :=
        norm_sub_le _ _
      _ ≤ (2 : ℝ) ^ j * (A * (I * A)) * D ^ (7 * j + 2) +
          I * ((2 : ℝ) ^ j * (A * A) * D ^ (7 * j + 2)) :=
        add_le_add (hMcurlJet t j hj a) (norm_iteratedFDeriv_geomRow_le P hP (hGM t) (hGMjet t j hj a))
      _ = (2 * (2 : ℝ) ^ j * A ^ 2) * (I * D ^ 2) * D ^ (7 * j) := by
        rw [pow_add]; ring
      _ ≤ (2 * (2 : ℝ) ^ n * A ^ 2) * (I * D ^ 2) * D ^ (7 * j) := by
        gcongr
        norm_num
      _ ≤ _ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAB' (by positivity)) (by positivity)
  · change HierarchyRelayCoefficientJets ℓ h n (hierarchyRelayGeometricRowBudget C n ℓ D)
      (fun t => relayPressureRowCLM ℓ i ∘ G t)
    exact hlinear (relayPressureRowCLM ℓ i) (norm_relayPressureRowCLM_le ℓ i)

end

end TorusEuler


#print axioms TorusEuler.hierarchyRelayGeometricCoefficientJets_of_parent_power_bounds
