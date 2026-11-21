import TorusEuler.PhysicalAmplificationCrossing

/-! The arbitrary-start central growth bound in Lemma 2.5 and §6. -/

open Set MeasureTheory
open scoped InnerProductSpace

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real linear plane transverse to a wave vector. -/
noncomputable def transversePlane (k : E) : Submodule ℝ E := (innerSL ℝ k).ker

@[simp] theorem mem_transversePlane {k v : E} :
    v ∈ transversePlane k ↔ ⟪k, v⟫_ℝ = 0 := Iff.rfl

private theorem affineWave_perp_of_mem_Icc [CompleteSpace E] {D : ℝ → E →L[ℝ] E} {k b : ℝ → E}
    {l r s : ℝ} (hs : s ∈ Icc l r)
    (hk₀ : ∀ q ∈ Icc l r, k q ≠ 0)
    (hk : ∀ q ∈ Icc l r, HasDerivWithinAt k (-((D q).adjoint (k q))) (Icc l r) q)
    (hb : ∀ q ∈ Icc l r, HasDerivWithinAt b
      (affineWaveAmplitudeOperator (D q) (k q) (b q)) (Icc l r) q)
    (hinit : ⟪k s, b s⟫_ℝ = 0) :
    ∀ q ∈ Icc l r, ⟪k q, b q⟫_ℝ = 0 := by
  have hd (q : ℝ) (hq : q ∈ Icc l r) :
      HasDerivWithinAt (fun u => ⟪k u, b u⟫_ℝ) 0 (Icc l r) q :=
    hasDerivWithinAt_affineWavePairing_zero (hk₀ q hq) (hk q hq)
      (by simpa only [affineWaveAmplitudeOperator_apply] using hb q hq)
  exact linearODE_unique_of_mem (A := fun _ => 0) ordConnected_Icc hs continuousOn_const
    (by simpa only [zero_apply] using hd)
    (fun q _ => by simpa only [zero_apply] using hasDerivWithinAt_const q (Icc l r) (0 : ℝ)) hinit

/-- On a closed slab, affine amplitude transport is a continuous linear equivalence
from the initial transverse plane onto the final transverse plane. -/
theorem exists_affineWave_transverse_equiv_Icc [CompleteSpace E] {D : ℝ → E →L[ℝ] E} {k : ℝ → E}
    {l r s t : ℝ} (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) (hD : ContinuousOn D (Icc l r))
    (hk₀ : ∀ q ∈ Icc l r, k q ≠ 0)
    (hk : ∀ q ∈ Icc l r, HasDerivWithinAt k (-((D q).adjoint (k q))) (Icc l r) q) :
    ∃ Φ : transversePlane (k s) ≃L[ℝ] transversePlane (k t),
      ∀ v : transversePlane (k s), ∃ b : ℝ → E,
        b s = (v : E) ∧ b t = (Φ v : E) ∧
        (∀ q ∈ Icc l r, HasDerivWithinAt b
          (affineWaveAmplitudeOperator (D q) (k q) (b q)) (Icc l r) q) ∧
        ∀ q ∈ Icc l r, ⟪k q, b q⟫_ℝ = 0 := by
  let A (q : ℝ) := affineWaveAmplitudeOperator (D q) (k q)
  have hA : ContinuousOn A (Icc l r) :=
    continuousOn_affineWaveAmplitudeOperator hD (HasDerivWithinAt.continuousOn hk) hk₀
  have hFundamental (u : ℝ) (hu : u ∈ Icc l r) :
      ∃ F : ℝ → E →L[ℝ] E, F u = ContinuousLinearMap.id ℝ E ∧
        ∀ q ∈ Icc l r, HasDerivWithinAt F ((A q).comp (F q)) (Icc l r) q := by
    obtain ⟨F, hFu, hF⟩ := linearODE_exists_Icc_of_mem hu
      ((ContinuousLinearMap.compL ℝ E E E).continuous.comp_continuousOn hA)
      (ContinuousLinearMap.id ℝ E)
    exact ⟨F, hFu, fun q hq => by
      simpa only [Function.comp_apply, ContinuousLinearMap.compL_apply] using hF q hq⟩
  obtain ⟨F, hFs, hF⟩ := hFundamental s hs
  obtain ⟨G, hGt, hG⟩ := hFundamental t ht
  have hEvaluate (P : ℝ → E →L[ℝ] E)
      (hP : ∀ q ∈ Icc l r, HasDerivWithinAt P ((A q).comp (P q)) (Icc l r) q)
      (v : E) (q : ℝ) (hq : q ∈ Icc l r) :
      HasDerivWithinAt (fun u => P u v) (A q (P q v)) (Icc l r) q := by
    simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero] using
      (hP q hq).clm_apply (hasDerivWithinAt_const q (Icc l r) v)
  have hFperp (v : E) (hv : v ∈ transversePlane (k s)) (q : ℝ) (hq : q ∈ Icc l r) :
      F q v ∈ transversePlane (k q) := by
    rw [mem_transversePlane] at hv ⊢
    exact affineWave_perp_of_mem_Icc hs hk₀ hk (hEvaluate F hF v)
      (by simpa only [hFs, ContinuousLinearMap.id_apply] using hv) q hq
  have hGperp (v : E) (hv : v ∈ transversePlane (k t)) :
      G s v ∈ transversePlane (k s) := by
    rw [mem_transversePlane] at hv ⊢
    exact affineWave_perp_of_mem_Icc ht hk₀ hk (hEvaluate G hG v)
      (by simpa only [hGt, ContinuousLinearMap.id_apply] using hv) s hs
  let f := (F t).restrict fun v hv => hFperp v hv t ht
  let g := (G s).restrict hGperp
  have hLeft : Function.LeftInverse g f := by
    intro v
    apply Subtype.ext
    change G s (F t v) = (v : E)
    have h := linearODE_unique_of_mem ordConnected_Icc ht hA
      (hEvaluate G hG (F t v)) (hEvaluate F hF (v : E))
      (by rw [hGt, ContinuousLinearMap.id_apply]) hs
    simpa only [hFs, ContinuousLinearMap.id_apply] using h
  have hRight : Function.RightInverse g f := by
    intro v
    apply Subtype.ext
    change F t (G s v) = (v : E)
    have h := linearODE_unique_of_mem ordConnected_Icc hs hA
      (hEvaluate F hF (G s v)) (hEvaluate G hG (v : E))
      (by rw [hFs, ContinuousLinearMap.id_apply]) ht
    simpa only [hGt, ContinuousLinearMap.id_apply] using h
  refine ⟨ContinuousLinearEquiv.equivOfInverse f g hLeft hRight, fun v =>
    ⟨fun q => F q v, by simp only [hFs, ContinuousLinearMap.id_apply], rfl,
      hEvaluate F hF (v : E), ?_⟩⟩
  exact fun q hq => mem_transversePlane.mp (hFperp v v.property q hq)

end TorusEuler

namespace TorusEuler.ReferenceAmplitude

open ReferenceRiccati (s s_pos hasDerivAt_s)

/-- The normalized error budget on a forward subinterval is bounded by the budget
from time zero up to the same endpoint. -/
theorem integrated_growing_error_Icc_le {ε T a t η : ℝ} {Y : ℝ → ℝ}
    (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) (hT : 2 ≤ T)
    (ha : a ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hat : a ≤ t) (hη : 0 ≤ η)
    (hYc : ContinuousOn Y (Icc 0 T)) (hYb : ∀ r ∈ Icc 0 T, |Y r| ≤ 1) :
    let D := ∫ r in a..t, ((1 + |Y r|) ^ 2 / s ε r) * η
    0 ≤ D ∧ D ≤ 4 * T ^ 3 * η := by
  let ω (r : ℝ) := ((1 + |Y r|) ^ 2 / s ε r) * η
  change 0 ≤ (∫ r in a..t, ω r) ∧ (∫ r in a..t, ω r) ≤ _
  have hω₀ (r : ℝ) : 0 ≤ ω r :=
    mul_nonneg (div_nonneg (sq_nonneg _) (s_pos ε r).le) hη
  have hs : Continuous (s ε) :=
    continuous_iff_continuousAt.2 fun r => (hasDerivAt_s ε r).continuousAt
  have hω : ContinuousOn ω (Icc 0 T) :=
    ((((continuousOn_const.add hYc.abs).pow 2).div hs.continuousOn
      (fun r _ => (s_pos ε r).ne')).mul continuousOn_const)
  have hprefix₀ : 0 ≤ (∫ r in 0..a, ω r) :=
    intervalIntegral.integral_nonneg_of_forall ha.1 hω₀
  have hsplit : (∫ r in 0..a, ω r) + (∫ r in a..t, ω r) = ∫ r in 0..t, ω r :=
    intervalIntegral.integral_add_adjacent_intervals
      ((hω.mono (Icc_subset_Icc_right ha.2)).intervalIntegrable_of_Icc ha.1)
      ((hω.mono (Icc_subset_Icc ha.1 ht.2)).intervalIntegrable_of_Icc hat)
  have hprefix := (integrated_growing_error_le hε hε₁ hT ht hη hYc hYb).2
  change (∫ r in 0..t, ω r) ≤ _ at hprefix
  rw [← hsplit] at hprefix
  exact ⟨intervalIntegral.integral_nonneg_of_forall hat hω₀, by linarith only [hprefix₀, hprefix]⟩

/-- The polynomial smallness budget bounds the arbitrary-start exponential
amplification factor uniformly on the normalized slab. -/
theorem exp_integrated_growing_error_Icc_le {ε T a t C δ : ℝ} {Y : ℝ → ℝ} {p : ℕ}
    (hε : 0 ≤ ε) (hε₁ : ε ≤ 1 / 2) (hT : 2 ≤ T)
    (ha : a ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hat : a ≤ t) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hsmall : 64 * C * T ^ (p + 3) * δ + 40 * T ^ 4 * δ ≤ ε)
    (hYc : ContinuousOn Y (Icc 0 T)) (hYb : ∀ r ∈ Icc 0 T, |Y r| ≤ 1) :
    let η := C * T ^ p * δ
    let D := ∫ r in a..t, ((1 + |Y r|) ^ 2 / s ε r) * η
    Real.exp (2 * D) ≤ 2 := by
  let η := C * T ^ p * δ
  let D := ∫ r in a..t, ((1 + |Y r|) ^ 2 / s ε r) * η
  have hT₀ : 0 ≤ T := by linarith
  have hη : 0 ≤ η := by unfold η; positivity
  obtain ⟨hD₀, hbudgetRaw⟩ := integrated_growing_error_Icc_le hε (hε₁.trans (by norm_num))
    hT ha ht hat hη hYc hYb
  change 0 ≤ D at hD₀
  change D ≤ 4 * T ^ 3 * η at hbudgetRaw
  have hbudget : D ≤ 4 * C * T ^ (p + 3) * δ := by
    convert hbudgetRaw using 1
    rw [pow_add]
    unfold η
    ring
  have hD : D ≤ 1 / 4 := by
    nlinarith only [hbudget, hsmall, hε₁, show 0 ≤ 40 * T ^ 4 * δ by positivity]
  have hexp := Real.abs_exp_sub_one_le (x := 2 * D)
    (by rw [abs_of_nonneg (by positivity)]; linarith)
  change Real.exp (2 * D) ≤ 2
  rw [abs_of_nonneg (by positivity : 0 ≤ 2 * D)] at hexp
  linarith [(abs_le.mp hexp).2]

end TorusEuler.ReferenceAmplitude

namespace TorusEuler.MovingWaveVector.AmplificationWindow

open MovingAmplitude ReferenceAmplitude ReferenceComparison ReferencePropagator
open ReferenceRiccati (rhs s)

private theorem window_sq_le_shear {T ε S δ : ℝ} (w : AmplificationWindow T ε S δ) :
    T ^ 2 ≤ S := by
  have hT : 1 ≤ T := by linarith [w.timeLower]
  have hS : 0 < S := by linarith [w.shearLower]
  have hpow : T ^ 2 ≤ T ^ 6 := pow_le_pow_right₀ hT (by decide)
  have hδ : 0 ≤ δ := w.errorNonnegative
  have hnum : 2 * δ * T ^ 2 ≤ 1 := by
    nlinarith only [w.smallness, mul_le_mul_of_nonneg_left hpow hδ,
      show 0 ≤ δ * T ^ 6 by positivity]
  have hInv : T ^ 2 * S⁻¹ ≤ 1 :=
    (mul_le_mul_of_nonneg_left w.inverseShear (sq_nonneg T)).trans (by nlinarith only [hnum])
  rw [← div_eq_mul_inv] at hInv
  exact (div_le_one₀ hS).mp hInv

private theorem growingFactor_ratio_le {ε u v : ℝ} {Y : ℝ → ℝ} {a : ℝ → Space}
    (hε : 2 * ε ≤ 1) (hu : 0 < ‖a u‖)
    (hlo : Real.exp (-ε) * growingFactor Y v ≤ ‖a v‖)
    (hhi : ‖a u‖ ≤ Real.exp ε * growingFactor Y u) :
    growingFactor Y v / growingFactor Y u ≤ Real.exp 1 * (‖a v‖ / ‖a u‖) := by
  have hgv : growingFactor Y v ≤ Real.exp ε * ‖a v‖ := by
    have h := mul_le_mul_of_nonneg_left hlo (Real.exp_pos ε).le
    rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h
  rw [← mul_div_assoc, div_le_div_iff₀ (growingFactor_pos Y u) hu]
  calc
    _ ≤ (Real.exp ε * ‖a v‖) * (Real.exp ε * growingFactor Y u) :=
      mul_le_mul hgv hhi (norm_nonneg _) (by positivity)
    _ = Real.exp (ε + ε) * ‖a v‖ * growingFactor Y u := by rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [hε]))
        (norm_nonneg _)) (growingFactor_pos Y u).le

/-- On the actual normalized affine system, every transverse solution is
bounded in norm relative to the growing solution, including for an
arbitrary initial time in the closed slab. The growing seed may already
have been rescaled by a positive constant. -/
theorem exists_growth_bound_threshold :
    ∃ N : ℕ, 240 ≤ N ∧ ∀ {T ε S δ scale c : ℝ} {C₀ : ℕ}, N ≤ C₀ →
      ∀ (w : AmplificationWindow T ε S δ), scale ≠ 0 → 0 < c →
      (C₀ : ℝ) * T ^ C₀ * δ ≤ ε →
      ∀ {k a b : ℝ → Space} {Y : ℝ → ℝ},
        k 0 = scale • w.basis 0 2 →
        a 0 = c • ((-S⁻¹) • w.basis 0 0 + w.basis 0 1) →
        (∀ t ∈ Icc 0 T,
          HasDerivWithinAt k (-((w.gradient t).adjoint (k t))) (Icc 0 T) t) →
        (∀ t ∈ Icc 0 T,
          HasDerivWithinAt a (affineWaveAmplitudeOperator (w.gradient t) (k t) (a t)) (Icc 0 T) t) →
        (∀ t ∈ Icc 0 T,
          HasDerivWithinAt b (affineWaveAmplitudeOperator (w.gradient t) (k t) (b t)) (Icc 0 T) t) →
        (∀ t ∈ Icc 0 T, a t ≠ 0 ∧ ⟪k t, a t⟫_ℝ = 0) →
        (∀ t ∈ Icc 0 T, ⟪k t, b t⟫_ℝ = 0) →
        Y 0 = 1 → (∀ t ∈ Ici 0, HasDerivWithinAt Y (rhs ε t (Y t)) (Ici 0) t) →
        ∀ {u v : ℝ}, u ∈ Icc 0 T → v ∈ Icc u T →
          ‖b v‖ / ‖a v‖ ≤ 252 * Real.exp 1 * S * (‖b u‖ / ‖a u‖) := by
  obtain ⟨C, hC, p, hmatrix⟩ := matrixError_polynomial_bound
  let L := 64 * C + 40
  let N := 240 + (p + 3) + Nat.ceil L
  refine ⟨N, by unfold N; omega, ?_⟩
  intro T ε S δ scale c C₀ hN w hscale hc hsmall k a b Y hk₀ ha₀ hk ha hb hA hB hY₀ hY u v hu hv
  have hC₀ : L ≤ (C₀ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil L ≤ C₀ by unfold N at hN; omega))
  have hBudget := growing_budget_of_polynomial_smallness w.timeLower hC w.errorNonnegative
    (show p + 3 ≤ C₀ by unfold N at hN; omega) (show 4 ≤ C₀ by unfold N at hN; omega)
    hC₀ hsmall
  have hε₁ := w.ratioSmall.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hYb (t : ℝ) (ht : t ∈ Icc 0 T) : |Y t| ≤ 1 :=
    ReferenceRiccati.riccati_abs_le_one w.ratioPositive hε₁ hY₀ hY t ht.1
  have hYw (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt Y (rhs ε t (Y t)) (Icc 0 T) t :=
    (hY t ht.1).mono Icc_subset_Ici_self
  have ht₀ : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, by linarith [w.timeLower]⟩
  let A (t : ℝ) := c⁻¹ • a t
  have hA₀ : A 0 = (-S⁻¹) • w.basis 0 0 + w.basis 0 1 := by
    change c⁻¹ • a 0 = _
    rw [ha₀, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  have hAder (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt A (affineWaveAmplitudeOperator (w.gradient t) (k t) (A t)) (Icc 0 T) t := by
    simpa only [A, map_smul] using (ha t ht).fun_const_smul c⁻¹
  have hAperp (t : ℝ) (ht : t ∈ Icc 0 T) : ⟪k t, A t⟫_ℝ = 0 := by
    change ⟪k t, c⁻¹ • a t⟫_ℝ = 0
    rw [real_inner_smul_right, (hA t ht).2, mul_zero]
  have hApos (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < ‖A t‖ :=
    norm_pos_iff.mpr (smul_ne_zero (inv_ne_zero hc.ne') (hA t ht).1)
  obtain ⟨hU₀, hV₀⟩ := growing_components (w.orthonormal_basis ht₀)
    (by linarith [w.shearLower]) hA₀
  have hAeq (t : ℝ) (ht : t ∈ Icc 0 T) :=
    w.raw_amplitude_equations hscale hk₀ hk hAder ht (hAperp t ht)
  have hBeq (t : ℝ) (ht : t ∈ Icc 0 T) :=
    w.raw_amplitude_equations hscale hk₀ hk hb ht (hB t ht)
  have hR := w.continuousOn_matrixError hscale hk₀ hk
  have hRη := hmatrix w hscale hk₀ hk
  have hlog (t : ℝ) (ht : t ∈ Icc 0 T) : |Real.log (‖A t‖ / growingFactor Y t)| ≤ ε := by
    obtain ⟨hZ, _, hX, hQ, _⟩ := w.wave_geometry hscale hk₀ hk ht
    exact log_growing_physical_norm_of_raw_matrix w.ratioPositive hε₁ w.timeLower hC
      w.errorNonnegative hBudget w.shearLower w.inverseShear hscale hY₀ hYb hYw hR hRη
      hU₀ hV₀ (fun r hr => (hAeq r hr).1) (fun r hr => (hAeq r hr).2)
      ht (w.orthonormal_basis ht) (hAperp t ht) hX hQ hZ
  have hvT : v ∈ Icc 0 T := ⟨hu.1.trans hv.1, hv.2⟩
  have hsub : Icc u T ⊆ Icc 0 T := Icc_subset_Icc_left hu.1
  have hsub' : Icc u v ⊆ Icc 0 T := Icc_subset_Icc hu.1 hv.2
  have hTS := window_sq_le_shear w
  have hTpow : T ≤ T ^ 2 := by nlinarith [w.timeLower, sq_nonneg (T - 1)]
  have hGeom (r : ℝ) (hr : r ∈ Icc u v) :
      Orthonormal ℝ (w.basis r) ∧ ⟪k r, b r⟫_ℝ = 0 ∧
        |X w.basis k scale r| ≤ S ∧ |Q w.basis k scale S r| ≤ S ∧
        1 / 2 ≤ Z w.basis k scale r ∧ Z w.basis k scale r ≤ 3 / 2 ∧
        |Y r| ≤ 1 ∧ |X w.basis k scale r - ReferenceRiccati.x ε r| ≤ 1 / 2 := by
    have hrT := hsub' hr
    obtain ⟨hZ₀, hZ₁, hX, hQ, _⟩ := w.wave_geometry hscale hk₀ hk hrT
    obtain ⟨hclose, hsmall⟩ := w.wave_comparison hscale hk₀ hk hrT
    have hXclose : |X w.basis k scale r - ReferenceRiccati.x ε r| ≤ 1 / 2 := by
      linarith only [hclose, hsmall, abs_nonneg (Q w.basis k scale S r + ε * r),
        abs_nonneg (Z w.basis k scale r - 1)]
    exact ⟨w.orthonormal_basis hrT, hB r hrT, hX.trans hTS, hQ.trans (hTpow.trans hTS),
      hZ₀, hZ₁, hYb r hrT, hXclose⟩
  let η := C * T ^ p * δ
  let D := ∫ r in u..v, ((1 + |Y r|) ^ 2 / s ε r) * η
  have hGrow : ‖b v‖ ≤ 126 * S * Real.exp (2 * D) *
      (growingFactor Y v / growingFactor Y u) * ‖b u‖ :=
    norm_movingAmplitude_le_from w.ratioPositive hY₀ hYw hu hv hscale w.shearLower
      hGeom (hR.mono hsub) continuousOn_const (fun r hr => hRη r (hsub hr))
      (fun r hr => (hBeq r hr).1) (fun r hr => (hBeq r hr).2)
  have hE : Real.exp (2 * D) ≤ 2 :=
    exp_integrated_growing_error_Icc_le w.ratioPositive.le w.ratioSmall w.timeLower hu hvT hv.1 hC
      w.errorNonnegative hBudget (HasDerivWithinAt.continuousOn hYw) hYb
  have hCompare (t : ℝ) (ht : t ∈ Icc 0 T) :
      Real.exp (-ε) * growingFactor Y t ≤ ‖A t‖ ∧
        ‖A t‖ ≤ Real.exp ε * growingFactor Y t :=
    reference_comparison_of_growing_log_bound (A := fun r => ‖A r‖) (Y := Y)
      (t := t) (hApos t ht) (hlog t ht)
  have hG := growingFactor_ratio_le (Y := Y) (a := A)
    (by linarith only [w.ratioSmall]) (hApos u hu) (hCompare v hvT).1 (hCompare u hu).2
  have hRatio : ‖A v‖ / ‖A u‖ = ‖a v‖ / ‖a u‖ := by
    simp only [A, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    exact mul_div_mul_left _ _ (inv_ne_zero hc.ne')
  rw [hRatio] at hG
  have hbound : ‖b v‖ ≤ 252 * Real.exp 1 * S * (‖a v‖ / ‖a u‖) * ‖b u‖ := by
    calc
      _ ≤ _ := hGrow
      _ ≤ 126 * S * 2 * (Real.exp 1 * (‖a v‖ / ‖a u‖)) * ‖b u‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_left hE (by linarith [w.shearLower])) hG
            (div_nonneg (growingFactor_pos Y v).le (growingFactor_pos Y u).le)
            (by linarith [w.shearLower])) (norm_nonneg _)
      _ = _ := by ring
  have hv₀ := norm_pos_iff.mpr (hA v hvT).1
  have hu₀ := norm_pos_iff.mpr (hA u hu).1
  apply (div_le_iff₀ hv₀).mpr
  refine hbound.trans_eq ?_
  field_simp [hu₀.ne']

end TorusEuler.MovingWaveVector.AmplificationWindow

namespace TorusEuler.MovingWaveVector.PhysicalAmplification

variable {I : Set ℝ} {t₀ : ℝ} (w : PhysicalAmplification I t₀)

private theorem normalized_physical_paths
    {T : ℝ} {C₀ : ℕ} {k a : ℝ → Space}
    (hT : 2 ≤ T) (hC₀ : 240 ≤ C₀) (hclock : MapsTo w.clock (Icc 0 T) I)
    (hsmallε : (C₀ : ℝ) * w.ratio ≤ 1) (hsmallδ : (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio)
    (hk : ∀ t ∈ w.activeSlab T,
      HasDerivWithinAt k (-((w.gradient t).adjoint (k t))) (w.activeSlab T) t)
    (ha : ∀ t ∈ w.activeSlab T,
      HasDerivWithinAt a (affineWaveAmplitudeOperator (w.gradient t) (k t) (a t)) (w.activeSlab T) t) :
    let W := w.toNormalized hT hC₀ hclock hsmallε hsmallδ
    let K := k ∘ w.clock
    let A := a ∘ w.clock
    (∀ t ∈ Icc 0 T, HasDerivWithinAt K (-((W.gradient t).adjoint (K t))) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt A (affineWaveAmplitudeOperator (W.gradient t) (K t) (A t))
        (Icc 0 T) t) := by
  have hmap : MapsTo w.clock (Icc 0 T) (w.activeSlab T) :=
    mapsTo_amplificationTime_Icc w.rate_pos
  have h (t : ℝ) (ht : t ∈ Icc 0 T) := normalized_affineWave_derivatives
    (D := w.gradient (w.clock t)) hmap (hk _ (hmap ht))
    (by simpa only [affineWaveAmplitudeOperator_apply, clock] using ha _ (hmap ht))
  dsimp only
  constructor
  · intro t ht
    rw [w.toNormalized_gradient_eq hT hC₀ hclock hsmallε hsmallδ ht]
    exact (h t ht).1
  · intro t ht
    rw [w.toNormalized_gradient_eq hT hC₀ hclock hsmallε hsmallδ ht, affineWaveAmplitudeOperator_apply]
    exact (h t ht).2

/-- The normalized comparison supplies the arbitrary-start estimate on the
same physical affine path as the peak-normalized crossing. -/
theorem exists_physical_growth_bound_threshold :
    ∃ N : ℕ, 240 ≤ N ∧
      ∀ {I : Set ℝ} {t₀ T scale Ustar next : ℝ} {C₀ : ℕ}, N ≤ C₀ →
        ∀ (w : PhysicalAmplification I t₀) (d : w.GrowingCrossing T scale Ustar next),
          2 ≤ T → scale ≠ 0 → (C₀ : ℝ) * w.ratio ≤ 1 →
          (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio →
          ∀ (b : ℝ → Space),
            (∀ t ∈ w.activeSlab T, HasDerivWithinAt b
              (affineWaveAmplitudeOperator (w.gradient t) (d.waveVector t) (b t))
              (w.activeSlab T) t) →
            (∀ t ∈ w.activeSlab T, ⟪d.waveVector t, b t⟫_ℝ = 0) →
            ∀ {u v : ℝ}, u ∈ w.activeSlab T → v ∈ w.activeSlab T → u ≤ v →
              ‖b v‖ / ‖d.amplitude v‖ ≤ 252 * Real.exp 1 * w.shear * (‖b u‖ / ‖d.amplitude u‖) := by
  obtain ⟨N, hN, hnorm⟩ := AmplificationWindow.exists_growth_bound_threshold
  refine ⟨N, hN, ?_⟩
  intro I t₀ T scale Ustar next C₀ hNC w d hT hscale hsmallε hsmallδ b hb hB u v hu hv huv
  have hC₀ := hN.trans hNC
  have hmap : MapsTo w.clock (Icc 0 T) (w.activeSlab T) :=
    mapsTo_amplificationTime_Icc w.rate_pos
  have hclock : MapsTo w.clock (Icc 0 T) I := fun t ht => d.slab_in_window (hmap ht)
  let W := w.toNormalized hT hC₀ hclock hsmallε hsmallδ
  let K := d.waveVector ∘ w.clock
  let A := d.amplitude ∘ w.clock
  let B := b ∘ w.clock
  have hBasis₀ : W.basis 0 = w.basis t₀ := by
    funext i
    simp only [W, toNormalized, AmplificationWindow.basis, frame, clock_zero]
  have hK₀ : K 0 = scale • W.basis 0 2 := by
    simpa only [K, Function.comp_apply, clock_zero, hBasis₀] using d.initial_waveVector
  have hA₀ : A 0 = d.seedFactor • ((-w.shear⁻¹) • W.basis 0 0 + W.basis 0 1) := by
    simpa only [A, Function.comp_apply, clock_zero, hBasis₀] using d.initial_amplitude
  obtain ⟨hK, hA⟩ := w.normalized_physical_paths hT hC₀ hclock hsmallε hsmallδ
    d.waveVector_derivative d.amplitude_derivative
  have hBder := (w.normalized_physical_paths hT hC₀ hclock hsmallε hsmallδ d.waveVector_derivative hb).2
  have hAperp (r : ℝ) (hr : r ∈ Icc 0 T) : A r ≠ 0 ∧ ⟪K r, A r⟫_ℝ = 0 :=
    (d.transverse _ (hmap hr)).2
  have hBperp (r : ℝ) (hr : r ∈ Icc 0 T) : ⟪K r, B r⟫_ℝ = 0 := hB _ (hmap hr)
  have hIn : MapsTo w.elapsed (w.activeSlab T) (Icc 0 T) :=
    mapsTo_inverse_amplificationTime_Icc w.rate_pos
  have hu' := hIn hu
  have hv' : w.elapsed v ∈ Icc (w.elapsed u) T :=
    ⟨w.strictMono_elapsed.monotone huv, (hIn hv).2⟩
  have h := hnorm hNC W hscale d.seedFactor_pos hsmallδ hK₀ hA₀ hK hA hBder hAperp hBperp
    d.reference_initial d.reference_derivative hu' hv'
  simpa only [A, B, Function.comp_apply, clock_elapsed] using h

private theorem continuousOn_gradient_of_physical_window : ContinuousOn w.gradient I := by
  have hkp := HasDerivWithinAt.continuousOn w.preceding_vector
  have hap := HasDerivWithinAt.continuousOn w.preceding_amplitude
  have hR : ContinuousOn (fun t => InnerProductSpace.rankOne ℝ (w.ap t) (w.kp t)) I :=
    ((InnerProductSpace.rankOne ℝ).continuous.comp_continuousOn hap).clm_apply hkp
  exact (w.older_continuous.add hR).add w.error_continuous

/-- The actual physical propagator maps the initial transverse plane onto
the final one with the rate relative to the same growing amplitude. -/
theorem exists_physical_propagator_threshold :
    ∃ N : ℕ, 240 ≤ N ∧
      ∀ {I : Set ℝ} {t₀ T scale Ustar next : ℝ} {C₀ : ℕ}, N ≤ C₀ →
        ∀ (w : PhysicalAmplification I t₀) (d : w.GrowingCrossing T scale Ustar next),
          2 ≤ T → scale ≠ 0 → (C₀ : ℝ) * w.ratio ≤ 1 →
          (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio →
          ∀ {u v : ℝ}, u ∈ w.activeSlab T → v ∈ w.activeSlab T → u ≤ v →
            ∃ Φ : transversePlane (d.waveVector u) ≃L[ℝ] transversePlane (d.waveVector v),
              ‖Φ.toContinuousLinearMap‖ ≤
                252 * Real.exp 1 * w.shear * (‖d.amplitude v‖ / ‖d.amplitude u‖) ∧
              ∀ b₀ : transversePlane (d.waveVector u), ∃ b : ℝ → Space,
                b u = (b₀ : Space) ∧ b v = (Φ b₀ : Space) ∧
                (∀ t ∈ w.activeSlab T, HasDerivWithinAt b
                  (affineWaveAmplitudeOperator (w.gradient t) (d.waveVector t) (b t))
                  (w.activeSlab T) t) ∧
                ∀ t ∈ w.activeSlab T, ⟪d.waveVector t, b t⟫_ℝ = 0 := by
  obtain ⟨N, hN, hgrowth⟩ := exists_physical_growth_bound_threshold
  refine ⟨N, hN, ?_⟩
  intro I t₀ T scale Ustar next C₀ hNC w d hT hscale hε hδ u v hu hv huv
  have hD := w.continuousOn_gradient_of_physical_window.mono d.slab_in_window
  obtain ⟨Φ, hΦ⟩ := exists_affineWave_transverse_equiv_Icc hu hv hD
    (fun t ht => (d.transverse t ht).1) d.waveVector_derivative
  refine ⟨Φ, ?_, hΦ⟩
  have hShear : 0 < w.shear := div_pos w.initialStrength_pos w.rate_pos
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b₀
  obtain ⟨b, hb₀, hb₁, hb, hperp⟩ := hΦ b₀
  change ‖(Φ b₀ : Space)‖ ≤ _ * ‖(b₀ : Space)‖
  rw [← hb₀, ← hb₁]
  have hV : 0 < ‖d.amplitude v‖ := norm_pos_iff.mpr (d.transverse v hv).2.1
  have h := (div_le_iff₀ hV).mp (hgrowth hNC w d hT hscale hε hδ b hb hperp hu hv huv)
  exact h.trans_eq (by ring)

/-- The actual central pair satisfies both clauses of (5.21), provided the
chosen parameter bounds the amplification and inverse coupling constants. -/
theorem exists_center_hypothesis_threshold :
    ∃ N : ℕ, 240 ≤ N ∧
      ∀ {I : Set ℝ} {t₀ T scale Ustar next : ℝ} {C₀ : ℕ}, N ≤ C₀ →
        ∀ (w : PhysicalAmplification I t₀) (d : w.GrowingCrossing T scale Ustar next),
          2 ≤ T → 0 < scale → (C₀ : ℝ) * w.ratio ≤ 1 →
          (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio →
          ∀ D : ℝ, 252 * Real.exp 1 * w.shear ≤ D → 2 / (w.firstCoupling * w.ratio) ≤ D →
            let γ (t : ℝ) := scale ^ (3 / 4 : ℝ) * ‖d.amplitude t‖
            (∀ (b : ℝ → Space),
              (∀ t ∈ w.activeSlab T, HasDerivWithinAt b
                (affineWaveAmplitudeOperator (w.gradient t) (d.waveVector t) (b t))
                (w.activeSlab T) t) →
              (∀ t ∈ w.activeSlab T, ⟪d.waveVector t, b t⟫_ℝ = 0) →
              ∀ {u v : ℝ}, u ∈ w.activeSlab T → v ∈ w.activeSlab T → u ≤ v →
                ‖b v‖ / γ v ≤ D * (‖b u‖ / γ u)) ∧
              ∀ t ∈ w.activeSlab T, D⁻¹ ≤ w.physicalNu d.waveVector d.amplitude t := by
  obtain ⟨N, hN, hgrowth⟩ := exists_physical_growth_bound_threshold
  refine ⟨N, hN, ?_⟩
  intro I t₀ T scale Ustar next C₀ hNC w d hT hscale hε hδ D hDgrowth hDν
  let L := scale ^ (3 / 4 : ℝ)
  have hL : 0 < L := Real.rpow_pos_of_pos hscale _
  constructor
  · intro b hb hperp u v hu hv huv
    have h := hgrowth hNC w d hT hscale.ne' hε hδ b hb hperp hu hv huv
    have h' := h.trans (mul_le_mul_of_nonneg_right hDgrowth
      (div_nonneg (norm_nonneg _) (norm_nonneg _)))
    have h'' := div_le_div_of_nonneg_right h' hL.le
    change ‖b v‖ / (L * ‖d.amplitude v‖) ≤ D * (‖b u‖ / (L * ‖d.amplitude u‖))
    rw [div_mul_eq_div_div_swap, div_mul_eq_div_div_swap, ← mul_div_assoc]
    exact h''
  · intro t ht
    have hbase : 0 < w.firstCoupling * w.ratio / 2 :=
      half_pos (mul_pos w.first_coupling_positive w.ratio_pos)
    have hInv : (w.firstCoupling * w.ratio / 2)⁻¹ = 2 / (w.firstCoupling * w.ratio) :=
      inv_div _ _
    have h := inv_anti₀ (inv_pos.mpr hbase) (hInv.trans_le hDν)
    exact (h.trans_eq (inv_inv _)).trans (d.first_coupling_lower t ht)


/-- One threshold yields a physical crossing and the center estimates for
that same peak-normalized affine path. -/
theorem exists_growingCrossing_with_center_hypothesis :
    ∃ N : ℕ, 240 ≤ N ∧
      ∀ {I : Set ℝ} {t₀ T scale Ustar next : ℝ} {C₀ : ℕ}, N ≤ C₀ →
        ∀ (w : PhysicalAmplification I t₀), 2 ≤ T → 0 < scale → 0 < Ustar →
          MapsTo w.clock (Icc 0 T) I →
          (C₀ : ℝ) * w.ratio ≤ 1 → (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio →
          0 < next → next ≤ w.ratio / 32 →
          AmplificationCrossing.crossingHorizon w.ratio next ≤ T →
          ∀ D : ℝ, 252 * Real.exp 1 * w.shear ≤ D → 2 / (w.firstCoupling * w.ratio) ≤ D →
            ∃ d : w.GrowingCrossing T scale Ustar next,
              let γ (t : ℝ) := scale ^ (3 / 4 : ℝ) * ‖d.amplitude t‖
              (∀ (b : ℝ → Space),
                (∀ t ∈ w.activeSlab T, HasDerivWithinAt b
                  (affineWaveAmplitudeOperator (w.gradient t) (d.waveVector t) (b t))
                  (w.activeSlab T) t) →
                (∀ t ∈ w.activeSlab T, ⟪d.waveVector t, b t⟫_ℝ = 0) →
                ∀ {u v : ℝ}, u ∈ w.activeSlab T → v ∈ w.activeSlab T → u ≤ v →
                  ‖b v‖ / γ v ≤ D * (‖b u‖ / γ u)) ∧
                ∀ t ∈ w.activeSlab T, D⁻¹ ≤ w.physicalNu d.waveVector d.amplitude t := by
  obtain ⟨N₁, hN₁, hcrossing⟩ := exists_growingCrossing
  obtain ⟨N₂, _, hcenter⟩ := exists_center_hypothesis_threshold
  refine ⟨max N₁ N₂, hN₁.trans (le_max_left _ _), ?_⟩
  intro I t₀ T scale Ustar next C₀ hN w hT hscale hUstar hclock hε hδ hnext hnext' hH D hDgrowth hDν
  obtain ⟨d⟩ := hcrossing ((le_max_left _ _).trans hN) w hT hscale hUstar hclock hε hδ hnext hnext' hH
  exact ⟨d, hcenter ((le_max_right _ _).trans hN) w d hT hscale hε hδ D hDgrowth hDν⟩


end TorusEuler.MovingWaveVector.PhysicalAmplification
