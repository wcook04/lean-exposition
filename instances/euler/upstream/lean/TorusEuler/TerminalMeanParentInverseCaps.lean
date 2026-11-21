import TorusEuler.EndpointPhysicalMeanEstimate

/-! Fixed-time and mixed inverses for the recovered mean on an actual parent slab. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "S" => endpointHalfHolderSolenoidal
local notation "Coefficient" => (Vec3 →L[ℝ] Vec3)
local notation "TimeSlab(" T ")" => Icc (0 : ℝ) T
local notation "LiftSlab(" T ")" => Set.prod (TimeSlab(T)) (univ : Set Vec3)
local notation "MixedFixed(" T ")" => freezingFixedSpace (endpointStrongMixedLeray T)

local instance terminalParentSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance terminalParentSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

private theorem contDiff_terminalMeanCoefficientSlice {T : ℝ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ × Vec3 → E} (hf : ContDiffOn ℝ ∞ f LiftSlab(T))
    {t : ℝ} (ht : t ∈ TimeSlab(T)) : ContDiff ℝ ∞ (fun x => f (t, x)) :=
  hf.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht, mem_univ x⟩)

/-- The inverse maps and their bounds for the same exact recovery. The
fixed-time cap and the mixed recovery cap are controlled by one parent power. -/
structure TerminalMeanParentInverseData {T D L : ℝ} {hT : 0 < T} {F M : ℝ × A → Coefficient}
    {force v : Velocity} (rec : EndpointPhysicalMeanRecovery hT D L F M force v) (p : ℕ) where
  eS : ℝ → S ≃L[ℝ] S
  eM : MixedFixed(T) ≃L[ℝ] MixedFixed(T)
  As : ℝ
  Am : ℝ
  LK : ℝ
  CK : ℝ
  hLK : 0 ≤ LK
  hLip : ∀ t ∈ TimeSlab(T), ∀ a b : A,
    ‖HalfHolder.eval a (rec.jets.kinetic.curve [] t) -
      HalfHolder.eval b (rec.jets.kinetic.curve [] t)‖ ≤ LK * dist a b
  hSup : ∀ t ∈ TimeSlab(T), ‖(rec.jets.kinetic.curve [] t).val.1‖ ≤ CK
  heS : ∀ t ∈ TimeSlab(T), ∀ z : S,
    eS t z = endpointStrongSpatialProjection ((rec.jets.kinetic.curve [] t).coefficientMul z.val)
  hAs : ∀ t ∈ TimeSlab(T), ‖((eS t).symm : S →L[ℝ] S)‖ ≤ As
  hAsPower : ∀ t ∈ TimeSlab(T), ‖((eS t).symm : S →L[ℝ] S)‖ ≤ D ^ p
  heM : (eM : MixedFixed(T) →L[ℝ] MixedFixed(T)) = freezingCompression (endpointStrongMixedLeray T)
    (endpointMixedPathCoefficient hT.le (rec.jets.kineticMixed []) (rec.jets.vorticityMixed [])).coefficientMul
      (endpointStrongMixedLeray_idempotent hT)
  hAm : ‖(eM.symm : MixedFixed(T) →L[ℝ] MixedFixed(T))‖ ≤ Am
  hCap : endpointPhysicalInverseBudget hT.le (rec.jets.kineticMixed [])
    (rec.jets.vorticityMixed []) As Am ≤ D ^ p

set_option maxHeartbeats 5400000 in
/-- The exact parent flow supplies one power for both inverses and one
common label-radius threshold for all positive coefficient words. -/
theorem exists_terminalMeanParentInverseCaps (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ (p s₀ : ℕ) (H : ℕ → ℝ), 2 * (p + 9) ≤ s₀ ∧ (∀ n, 0 ≤ H n) ∧
      ∀ {T D L : ℝ} {U : Velocity} {X : ℝ → Velocity},
      ∀ (hT : 0 < T), T ≤ 1 → 2 ≤ D → 0 ≤ L → L ≤ D →
      IsLabelFlowOn U X (Icc 0 T) →
      ContDiffOn ℝ ∞ (Function.uncurry U) LiftSlab(T) →
      (∀ t ∈ TimeSlab(T), SpatiallyPeriodic (U t)) →
      (∀ t ∈ TimeSlab(T), ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
      (∀ t ∈ TimeSlab(T), ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
      (∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ t ∈ TimeSlab(T), ∀ x,
        ‖iteratedFDeriv ℝ k (U t) x‖ ≤ R n * D ^ k) →
      ∀ (F M : ℝ × A → Coefficient) (force v : Velocity),
      ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => F (z.1, toUnitTorus z.2)) LiftSlab(T) →
      ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => M (z.1, toUnitTorus z.2)) LiftSlab(T) →
      (∀ t ∈ TimeSlab(T), ∀ x, F (t, toUnitTorus x) = fderiv ℝ (X 0 t) x) →
      (∀ t ∈ TimeSlab(T), ∀ x, M (t, toUnitTorus x) = fderiv ℝ (U t) (X 0 t x)) →
      ∀ rec : EndpointPhysicalMeanRecovery hT D L F M force v,
      Nonempty (TerminalMeanParentInverseData rec p) ∧
      ∀ s : ℕ, s₀ ≤ s → ∀ q : List (Fin 3), 1 ≤ q.length →
        let ℓ := (D ^ s)⁻¹
        ℓ ^ q.length * (endpointClosedTimeNorm T (rec.jets.kinetic.curve q) +
          endpointClosedTimeNorm T (rec.jets.vorticity.curve q)) ≤
          H q.length * D ^ (9 : ℕ) * Real.sqrt ℓ := by
  obtain ⟨J, hJ, hRaw⟩ := exists_parentMeanCoefficientJetBounds R hR
  obtain ⟨_, H, _, hH, hWeighted⟩ := exists_parentMeanWeightedCoefficientBounds R hR
  let C₀ := 13 + J 0 + J 0 + 4 * J 1 + 4 * J 1
  have hC₀ : 1 ≤ C₀ := by dsimp only [C₀]; linarith only [hJ 0, hJ 1]
  obtain ⟨CI, _, hInverse⟩ := exists_endpointPhysicalInverseCaps 9 hC₀
  obtain ⟨pMixed, hPowMixed⟩ := exists_endpointPower_absorb_prefactor CI (291 * 9)
  obtain ⟨CS, hCS, hInstant⟩ := exists_endpointSpatialSolenoidalInverse
  obtain ⟨pSpatial, hPowSpatial⟩ := exists_endpointPower_absorb_prefactor (CS * C₀ ^ (145 : ℕ)) (9 * 145)
  let p := max pMixed pSpatial
  let H' (n : ℕ) := Real.sqrt 2 * H n
  have hH' (n : ℕ) : 0 ≤ H' n := mul_nonneg (Real.sqrt_nonneg 2) (hH n)
  refine ⟨p, 2 * (p + 9), H', le_rfl, hH', ?_⟩
  intro T D L U X hT hT₁ hD hL hLD hX hU hUper hF₀ hG₀ hUjets
    F M force v hF hM hFEq hMEq rec
  have hD₁ : 1 ≤ D := one_le_two.trans hD
  have hDpos : 0 < D := zero_lt_one.trans_le hD₁
  let K := rec.jets.kinetic.curve
  let Ω := rec.jets.vorticity.curve
  let k (t : ℝ) (x : Vec3) := kineticForm (F (t, toUnitTorus x))
  let o (t : ℝ) (x : Vec3) := vorticityForm (F (t, toUnitTorus x)) (M (t, toUnitTorus x))
  let Adj : Coefficient ≃ₗᵢ[ℝ] Coefficient := ContinuousLinearMap.adjoint
  have hFa : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => (F (z.1, toUnitTorus z.2)).adjoint) LiftSlab(T) :=
    Adj.contDiff.comp_contDiffOn hF
  have hMa : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => (M (z.1, toUnitTorus z.2)).adjoint) LiftSlab(T) :=
    Adj.contDiff.comp_contDiffOn hM
  have hkC : ContDiffOn ℝ ∞ (Function.uncurry k) LiftSlab(T) := hFa.clm_comp hF
  have hoC : ContDiffOn ℝ ∞ (Function.uncurry o) LiftSlab(T) :=
    hFa.clm_comp ((hMa.sub hM).clm_comp hF)
  have hraw (t : ℝ) (ht : t ∈ TimeSlab(T)) (m : ℕ) (x : Vec3) :
      ‖iteratedFDeriv ℝ m (k t) x‖ ≤ J m * D ^ (5 * m + 2) ∧
        ‖iteratedFDeriv ℝ m (o t) x‖ ≤ J m * D ^ (6 * m + 3) := by
    have h := hRaw hT hT₁ hD₁ hX hU hUper hF₀ hG₀ hUjets t ht
    have hKO := (h.2.2.2.2 m x).2.2
    simpa only [k, o, hFEq t ht, hMEq t ht] using hKO
  have hd₀ : 0 ≤ D := hDpos.le
  obtain ⟨hKB, hKL⟩ := endpointHalfHolderCaps_of_lift_gradient
    (mul_nonneg (hJ 0) (pow_nonneg hd₀ 2)) (mul_nonneg (hJ 1) (pow_nonneg hd₀ 7)) (K []) k
    (fun t ht x => rec.jets.kinetic.eval_lift [] t ht x)
    (fun t ht => (contDiff_terminalMeanCoefficientSlice hkC ht).differentiable (by simp))
    (fun t ht x => by simpa only [norm_iteratedFDeriv_zero] using (hraw t ht 0 x).1)
    (fun t ht x => by simpa only [norm_iteratedFDeriv_one] using (hraw t ht 1 x).1)
  obtain ⟨hΩB, hΩL⟩ := endpointHalfHolderCaps_of_lift_gradient
    (mul_nonneg (hJ 0) (pow_nonneg hd₀ 3)) (mul_nonneg (hJ 1) (pow_nonneg hd₀ 9)) (Ω []) o
    (fun t ht x => rec.jets.vorticity.eval_lift [] t ht x)
    (fun t ht => (contDiff_terminalMeanCoefficientSlice hoC ht).differentiable (by simp))
    (fun t ht x => by simpa only [norm_iteratedFDeriv_zero] using (hraw t ht 0 x).2)
    (fun t ht x => by simpa only [norm_iteratedFDeriv_one] using (hraw t ht 1 x).2)
  let μ := (D ^ 2)⁻¹
  let μmix := 1 / (2 * D ^ 2 * (1 + L) ^ 2)
  let LK := 2 * (J 1 * D ^ 7)
  let LΩ := 2 * (J 1 * D ^ 9)
  let CK := J 0 * D ^ 2 + LK
  let CΩ := J 0 * D ^ 3 + LΩ
  have hμ : 0 < μ := inv_pos.mpr (pow_pos hDpos 2)
  have hμmix : 0 < μmix := by dsimp only [μmix]; positivity
  have hLK : 0 ≤ LK := mul_nonneg zero_le_two (mul_nonneg (hJ 1) (pow_nonneg hd₀ 7))
  have hLΩ : 0 ≤ LΩ := mul_nonneg zero_le_two (mul_nonneg (hJ 1) (pow_nonneg hd₀ 9))
  have hCK : 0 ≤ CK := add_nonneg (mul_nonneg (hJ 0) (pow_nonneg hd₀ 2)) hLK
  have hCΩ : 0 ≤ CΩ := add_nonneg (mul_nonneg (hJ 0) (pow_nonneg hd₀ 3)) hLΩ
  have hCommon : 4 + μ⁻¹ + μmix⁻¹ + CK + CΩ + LK + LΩ ≤ C₀ * D ^ 9 := by
    simpa only [μ, μmix, CK, CΩ, LK, LΩ, C₀, mul_assoc] using
      endpointInverseCommonScale_le_power_nine hD₁ hL hLD (hJ 0) (hJ 0) (hJ 1) (hJ 1)
  obtain ⟨eS, eM, As, Am, heS, hAs, heM, hAm, hCap⟩ :=
    hInverse (D := D) (μ := μ) (μmix := μmix) (CK := CK) (CΩ := CΩ) (LK := LK) (LΩ := LΩ)
      hT hT₁ hD₁ (rec.jets.kineticMixed []) (rec.jets.vorticityMixed []) (K []) (Ω [])
      (rec.jets.kinetic.smooth []).continuousOn (rec.jets.vorticity.smooth []).continuousOn
      (rec.jets.kinetic_action []) (rec.jets.vorticity_action [])
      hCK hCΩ hLK hLΩ hKB hΩB hKL hΩL hμ hμmix rec.kinetic_coercive rec.mixed_coercive hCommon
  have hSup (t : ℝ) (ht : t ∈ TimeSlab(T)) : ‖(K [] t).val.1‖ ≤ CK :=
    (norm_fst_le (K [] t).val).trans (hKB t ht)
  have hAsPower (t : ℝ) (ht : t ∈ TimeSlab(T)) : ‖((eS t).symm : S →L[ℝ] S)‖ ≤ D ^ p := by
    obtain ⟨e, he, hBound⟩ := hInstant (K [] t) hμ hLK (hKL t ht) (rec.kinetic_coercive t ht)
    have hEq : eS t = e := by
      apply DFunLike.ext
      intro z
      exact (heS t ht z).trans (he z).symm
    have hScale : 4 + μ⁻¹ + ‖(K [] t).val.1‖ + LK ≤ C₀ * D ^ (9 : ℕ) := by
      have hmm : 0 ≤ μmix⁻¹ := inv_nonneg.mpr hμmix.le
      linarith only [hCommon, hSup t ht, hmm, hCΩ, hLΩ]
    rw [hEq]
    calc
      _ ≤ CS * (4 + μ⁻¹ + ‖(K [] t).val.1‖ + LK) ^ (145 : ℕ) := hBound
      _ ≤ CS * (C₀ * D ^ (9 : ℕ)) ^ (145 : ℕ) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hScale _) hCS
      _ = (CS * C₀ ^ (145 : ℕ)) * D ^ (9 * 145 : ℕ) := by
        rw [mul_pow, ← mul_assoc, pow_mul]
      _ ≤ D ^ pSpatial := hPowSpatial D hD
      _ ≤ D ^ p := pow_le_pow_right₀ hD₁ (le_max_right _ _)
  have hCapPower : endpointPhysicalInverseBudget hT.le (rec.jets.kineticMixed [])
      (rec.jets.vorticityMixed []) As Am ≤ D ^ p :=
    hCap.trans ((hPowMixed D hD).trans (pow_le_pow_right₀ hD₁ (le_max_left _ _)))
  refine ⟨⟨⟨eS, eM, As, Am, LK, CK, hLK, hKL, hSup, heS, hAs, hAsPower, heM, hAm, hCapPower⟩⟩, ?_⟩
  intro s hs q hq
  let ℓ := (D ^ s)⁻¹
  let dir := hierarchyLabelDirection ℓ
  have hℓ : 0 < ℓ := inv_pos.mpr (pow_pos hDpos _)
  have hScale : ℓ * D ^ (6 : ℕ) ≤ 1 := by
    dsimp only [ℓ]
    rw [inv_mul_eq_div]
    exact (div_le_one (pow_pos hDpos _)).mpr (pow_le_pow_right₀ hD₁ (by omega))
  have hWeight := hWeighted hT hT₁ hD₁ hℓ hScale hX hU hUper hF₀ hG₀ hUjets
  have hKM : (fun t : TimeSlab(T) => k t) =
      fun (t : TimeSlab(T)) x => kineticForm (fderiv ℝ (X 0 t.val) x) := by
    funext t x
    dsimp only [k]
    rw [hFEq t t.property]
  have hOM : (fun t : TimeSlab(T) => o t) =
      fun (t : TimeSlab(T)) x => vorticityForm (fderiv ℝ (X 0 t.val) x) (fderiv ℝ (U t.val) (X 0 t.val x)) := by
    funext t x
    dsimp only [o]
    rw [hFEq t t.property, hMEq t t.property]
  have hkB : BddAbove (hierarchyJetValues True dir q (fun t : TimeSlab(T) => k t)) := by
    rw [hKM]
    exact (hWeight.1 q).2.2.1
  have hoB : BddAbove (hierarchyJetValues True dir q (fun t : TimeSlab(T) => o t)) := by
    rw [hOM]
    exact (hWeight.1 q).2.2.2
  have hkW := rec.jets.kinetic.mul_closedTimeNorm_le_liftCap hT hℓ hkC q hkB
  have hoW := rec.jets.vorticity.mul_closedTimeNorm_le_liftCap hT hℓ hoC q hoB
  have hKO : sSup (hierarchyJetValues True dir q (fun t : TimeSlab(T) => k t)) +
      sSup (hierarchyJetValues True dir q (fun t : TimeSlab(T) => o t)) ≤
      H q.length * D ^ 9 * Real.sqrt ℓ := by
    rw [hKM, hOM]
    exact (hWeight.2.2 q) (by omega)
  change ℓ ^ q.length * (endpointClosedTimeNorm T (K q) + endpointClosedTimeNorm T (Ω q)) ≤ _
  rw [mul_add]
  calc
    _ ≤ Real.sqrt 2 *
        (sSup (hierarchyJetValues True dir q (fun t : TimeSlab(T) => k t)) +
          sSup (hierarchyJetValues True dir q (fun t : TimeSlab(T) => o t))) := by
      rw [mul_add]
      exact add_le_add hkW hoW
    _ ≤ Real.sqrt 2 * (H q.length * D ^ 9 * Real.sqrt ℓ) :=
      mul_le_mul_of_nonneg_left hKO (Real.sqrt_nonneg _)
    _ = _ := by dsimp only [H']; ac_rfl

end

end TorusEuler
