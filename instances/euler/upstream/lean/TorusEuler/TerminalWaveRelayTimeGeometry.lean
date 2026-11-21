import TorusEuler.TerminalCoefficientTimeProduct
import TorusEuler.HierarchyRelayCoframeCoefficientBounds

/-! Mixed jets of the three geometric rows in the normalized wave relay. -/

open ContinuousLinearMap Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

namespace TerminalMixedJetBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b D A : ℝ} {q p : ℕ} {C : ℕ → ℝ} {f : ℝ → Vec3 → E}

set_option maxHeartbeats 500000 in
/-- Fixed scalar multiplication changes the amplitude of a mixed jet bound. -/
theorem const_smul (h : TerminalMixedJetBound a b q p D A C f)
    (hab : a < b) (hD : 0 ≤ D) (hA : 0 ≤ A) (hC : ∀ n, 0 ≤ C n)
    (hreg : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set Vec3))) (r : ℝ) :
    TerminalMixedJetBound a b q p D (‖r‖ * A) C (fun t x => r • f t x) := by
  let L : E →L[ℝ] E := r • ContinuousLinearMap.id ℝ E
  have hL : ‖L‖ ≤ ‖r‖ := by
    dsimp only [L]
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_id_le (𝕜 := ℝ) (E := E))
  have hRaw := h.apply_clm hab hreg L
  intro i hi n t ht x
  change ‖iteratedFDeriv ℝ n (slabTimeJet a b i (fun t x => L (f t x)) t) x‖ ≤ _
  refine (hRaw i hi n t ht x).trans ?_
  rw [show ‖L‖ * C n * A = C n * (‖L‖ * A) by ring]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL hA) (hC n))
    (pow_nonneg hD _)

end TerminalMixedJetBound

local notation "End" => (Vec3 →L[ℝ] Vec3)
local notation "GradRow" => (ℝ →L[ℝ] Vec3)
local notation "Slab(" T ")" => Set.prod (Icc (0 : ℝ) T) (univ : Set Vec3)

private def relayMaterialUnitBilinear (i : Fin 3) : End →L[ℝ] End →L[ℝ] End :=
  let C := compL ℝ Vec3 Vec3 Vec3
  let L := compL ℝ End End End
  let P := relayCurlRowCLM 1 i
  ((L.flip P).comp C).flip - (L P).comp C

private theorem hierarchyRelayMaterialRow_eq_scaled_bilinear (ell : ℝ) (G M : End) (i : Fin 3) :
    hierarchyRelayMaterialRow ell G M i = ell⁻¹ • relayMaterialUnitBilinear i G M := by
  let P := relayCurlRowCLM 1 i
  change M.comp (hierarchyRelayCurlRow ell G i) - hierarchyRelayCurlRow ell (G.comp M) i =
    ell⁻¹ • (M.comp (P G) - P (G.comp M))
  simp only [P, relayCurlRowCLM, hierarchyRelayCurlRow, inv_one, one_smul, smul_sub,
    comp_smulₛₗ, RingHom.id_apply]
  rfl

private theorem hierarchyRelayCurlRow_eq_scaled_linear (ell : ℝ) (G : End) (i : Fin 3) :
    hierarchyRelayCurlRow ell G i = ell⁻¹ • relayCurlRowCLM 1 i G := by
  simp only [relayCurlRowCLM, hierarchyRelayCurlRow, inv_one, one_smul]
  rfl

private theorem hierarchyRelayPressureRow_eq_scaled_linear (ell : ℝ) (G : End) (i : Fin 3) :
    hierarchyRelayPressureRow ell G i = ell⁻¹ • relayPressureRowCLM 1 i G := by
  simp only [relayPressureRowCLM, hierarchyRelayPressureRow, inv_one, one_smul]
  rfl

/-- The exact normalized curl, material, and gradient rows are jointly
smooth when the parent inverse coframe and strain are. -/
theorem terminal_waveRelayGeometry_contDiffOn {T ell : ℝ} {G M : ℝ → Vec3 → End}
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (Slab(T)))
    (hM : ContDiffOn ℝ ∞ (Function.uncurry M) (Slab(T))) :
    (∀ i, ContDiffOn ℝ ∞ (Function.uncurry (fun t a => hierarchyRelayCurlRow ell (G t a) i))
      (Slab(T))) ∧
    (∀ i, ContDiffOn ℝ ∞
      (Function.uncurry (fun t a => hierarchyRelayMaterialRow ell (G t a) (M t a) i)) (Slab(T))) ∧
    (∀ i, ContDiffOn ℝ ∞
      (Function.uncurry (fun t a => hierarchyRelayPressureRow ell (G t a) i)) (Slab(T))) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · refine (((relayCurlRowCLM 1 i).contDiff.comp_contDiffOn hG).const_smul ell⁻¹).congr ?_
    rintro ⟨t, x⟩ _
    exact hierarchyRelayCurlRow_eq_scaled_linear ell (G t x) i
  · refine ((((relayMaterialUnitBilinear i).contDiff.comp_contDiffOn hG).clm_apply hM).const_smul ell⁻¹).congr ?_
    rintro ⟨t, x⟩ _
    exact hierarchyRelayMaterialRow_eq_scaled_bilinear ell (G t x) (M t x) i
  · refine (((relayPressureRowCLM 1 i).contDiff.comp_contDiffOn hG).const_smul ell⁻¹).congr ?_
    rintro ⟨t, x⟩ _
    exact hierarchyRelayPressureRow_eq_scaled_linear ell (G t x) i

set_option maxHeartbeats 1800000 in
/-- The exact three geometric relay rows have a common mixed jet bound
with a fixed label slope. Their common order-independent amplitude is
the inverse label width times the square of the parent amplitude. -/
theorem exists_terminalWaveRelayGeometricJetBounds (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n) (q : ℕ) :
    ∃ K : ℕ → ℝ, (∀ n, 0 ≤ K n) ∧
      ∀ {T D A ell : ℝ} {G M : ℝ → Vec3 → End},
        0 < T → 1 ≤ D → 1 ≤ A →
        ContDiffOn ℝ ∞ (Function.uncurry G) (Slab(T)) →
        ContDiffOn ℝ ∞ (Function.uncurry M) (Slab(T)) →
        TerminalMixedJetBound 0 T q 16 D A C G →
        TerminalMixedJetBound 0 T q 16 D A C M →
        let B := ‖ell⁻¹‖ * A ^ 2
        (∀ i, TerminalMixedJetBound 0 T q 16 D B K
          (fun t a => hierarchyRelayCurlRow ell (G t a) i)) ∧
        (∀ i, TerminalMixedJetBound 0 T q 16 D B K
          (fun t a => hierarchyRelayMaterialRow ell (G t a) (M t a) i)) ∧
        (∀ i, TerminalMixedJetBound 0 T q 16 D B K
          (fun t a => hierarchyRelayPressureRow ell (G t a) i)) := by
  let L (i : Fin 3) (n : ℕ) := ‖relayCurlRowCLM 1 i‖ * C n
  let R (i : Fin 3) (n : ℕ) := ‖relayPressureRowCLM 1 i‖ * C n
  let P (i : Fin 3) := terminalMixedProductCost q (relayMaterialUnitBilinear i) C C
  let K (n : ℕ) := ∑ i : Fin 3, (L i n + R i n + P i n)
  have hL (i : Fin 3) (n : ℕ) : 0 ≤ L i n := mul_nonneg (norm_nonneg (relayCurlRowCLM 1 i)) (hC n)
  have hR (i : Fin 3) (n : ℕ) : 0 ≤ R i n := mul_nonneg (norm_nonneg (relayPressureRowCLM 1 i)) (hC n)
  have hP (i : Fin 3) (n : ℕ) : 0 ≤ P i n :=
    terminalMixedProductCost_nonneg q (relayMaterialUnitBilinear i) hC hC n
  have hTotal (i : Fin 3) (n : ℕ) : 0 ≤ L i n + R i n + P i n :=
    add_nonneg (add_nonneg (hL i n) (hR i n)) (hP i n)
  have hK (i : Fin 3) (n : ℕ) : L i n + R i n + P i n ≤ K n :=
    Finset.single_le_sum (fun j _ => hTotal j n) (Finset.mem_univ i)
  refine ⟨K, fun n => Finset.sum_nonneg (fun i _ => hTotal i n), ?_⟩
  intro T D A ell G M hT hD hA hGreg hMreg hG hM B
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hA₀ : 0 ≤ A := zero_le_one.trans hA
  have hA₂ : A ≤ A ^ 2 := by nlinarith only [hA, mul_nonneg hA₀ (sub_nonneg.mpr hA)]
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hGe (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (F : End →L[ℝ] E) (hF : ∀ n, ‖F‖ * C n ≤ K n) :
      TerminalMixedJetBound 0 T q 16 D B K (fun t a => ell⁻¹ • F (G t a)) := by
    have hOne : ∀ n, 0 ≤ ‖F‖ * C n := fun n => mul_nonneg (norm_nonneg F) (hC n)
    have hRaw := (hG.apply_clm hT hGreg F).mono_amplitude hD₀ hOne hA₂
    exact (hRaw.const_smul hT hD₀ (sq_nonneg A) hOne
      (F.contDiff.comp_contDiffOn hGreg) ell⁻¹).mono_constant hD₀ hB hF
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · have hF (n : ℕ) : ‖relayCurlRowCLM 1 i‖ * C n ≤ K n :=
      (show L i n ≤ L i n + R i n + P i n by linarith [hR i n, hP i n]).trans (hK i n)
    exact (hGe End (relayCurlRowCLM 1 i) hF).congr
      (fun t _ x => (hierarchyRelayCurlRow_eq_scaled_linear ell (G t x) i).symm)
  · have hF (n : ℕ) : P i n ≤ K n :=
      (show P i n ≤ L i n + R i n + P i n by linarith [hL i n, hR i n]).trans (hK i n)
    have hRaw := TerminalMixedJetBound.bilinear (relayMaterialUnitBilinear i) hT hD₀ hA₀ hA₀ hC hC
      hG hM hGreg hMreg
    rw [← pow_two] at hRaw
    have hReg := ((relayMaterialUnitBilinear i).contDiff.comp_contDiffOn hGreg).clm_apply hMreg
    exact ((hRaw.const_smul hT hD₀ (sq_nonneg A) (hP i) hReg ell⁻¹).mono_constant hD₀ hB hF).congr
      (fun t _ x => (hierarchyRelayMaterialRow_eq_scaled_bilinear ell (G t x) (M t x) i).symm)
  · have hF (n : ℕ) : ‖relayPressureRowCLM 1 i‖ * C n ≤ K n :=
      (show R i n ≤ L i n + R i n + P i n by linarith [hL i n, hP i n]).trans (hK i n)
    exact (hGe GradRow (relayPressureRowCLM 1 i) hF).congr
      (fun t _ x => (hierarchyRelayPressureRow_eq_scaled_linear ell (G t x) i).symm)

end

end TorusEuler
