import TorusEuler.SeedDerivativeBudgets
import TorusEuler.LaterWaveDerivativeBudgets

/-! The quantitative leading velocity and pressure jets of the actual parent seed. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

namespace LocalizedAmplitude

private theorem exists_coframe_radius_exponent (C : ℝ) :
    ∃ A : ℕ, 30 ≤ A ∧ ∀ {D ℓ : ℝ}, 2 ≤ D → 0 < ℓ → ℓ ≤ (D ^ A)⁻¹ →
      2 * C * ℓ * D ^ 30 ≤ 1 := by
  obtain ⟨A, hA⟩ := pow_unbounded_of_one_lt (2 * C) (show (1 : ℝ) < 2 by norm_num)
  refine ⟨30 + A, by omega, fun {D ℓ} hD hℓ hR => ?_⟩
  have hD₀ : 0 < D := by linarith
  have hCD : 2 * C ≤ D ^ A := hA.le.trans (pow_le_pow_left₀ (by norm_num) hD A)
  calc
    _ ≤ D ^ A * ℓ * D ^ 30 := by gcongr
    _ = ℓ * D ^ (30 + A) := by rw [pow_add]; ring
    _ ≤ 1 := by
      apply (le_div_iff₀ (show 0 < D ^ (30 + A) by positivity)).mp
      simpa only [one_div] using hR

set_option maxHeartbeats 2700000 in
/-- On the actual closed parent slab, the same radius exponent serves all
orders of the initial leading velocity and pressure estimates. -/
theorem exists_parent_seed_leadingAndSlowJetBounds (W : ℕ → ℝ) (hW : ∀ m, 0 ≤ W m) :
    ∃ A : ℕ, 30 ≤ A ∧ ∀ n : ℕ, ∃ C Bseed Pcoef : ℝ, 1 ≤ C ∧ 1 ≤ Bseed ∧ 1 ≤ Pcoef ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T t₀ D ℓ Cseed freq : ℝ}
        {k : Vec3} {center : ℝ → Vec3},
      0 ≤ t₀ → t₀ < T → T ≤ 1 → 2 ≤ D → 0 < ℓ → ℓ ≤ (D ^ A)⁻¹ →
      1 ≤ freq → ‖labelWaveVector X 0 0 k t₀‖ = freq →
      IsLabelFlowOn U X (Icc 0 T) →
      ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
      (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
      (∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
        ‖iteratedFDeriv ℝ j (U t) x‖ ≤ W n * D ^ j) →
      let M (t : ℝ) (a : Vec3) := fderiv ℝ (U t) (X 0 t a)
      let κ (t : ℝ) (a : Vec3) := labelWaveVector X 0 a k t
      CenterWaveOn (fun t => M t 0) (fun t => κ t 0) center t₀ T D →
      ∀ (w : SeedOn M κ center t₀ T ℓ D Cseed) {χ : ℝ}, |χ| ≤ 1 →
        ∀ t, t ∈ Icc t₀ T →
        let h := freq ^ (-1 / 2 : ℝ)
        let γ := freq ^ (3 / 4 : ℝ) * ‖center t‖
        let B := γ * (C * D ^ 20 * freq ^ (-5 / 4 : ℝ))
        (PhaseJetBound n B (scaledPhaseProfile ℓ h (fun a s => χ • w.leading h t a s)) ∧
          PhaseJetBound n B (scaledPhaseProfile ℓ h (fun a s => freq * (χ * w.leadingPressure h t a s)))) ∧
        PhaseJetBound n (Bseed * D ^ 13 * ‖center t‖)
          (fun a => radialEnvelope ℓ (ℓ • a) • w.amplitude t (ℓ • a)) ∧
        let P (a : Vec3) := hierarchyRelayPressureAmplitudeCoefficient (M t (ℓ • a)) (freq⁻¹ • κ t (ℓ • a))
        ContDiff ℝ ∞ P ∧ PhaseJetBound n (Pcoef * D ^ 7) P := by
  obtain ⟨Cf, hCf, hCoframe⟩ := exists_parent_transverseCoframeJetBounds W hW
  obtain ⟨Cp, hCp, hPressure⟩ := exists_parent_coefficientJetBounds W hW
  let Q (n : ℕ) := 1 + ∑ m ∈ Finset.range (n + 1), Cp m
  let P (n : ℕ) := 1 + 2 * (2 : ℝ) ^ (2 * n) * (Q n) ^ 3
  have hQ (n : ℕ) : 1 ≤ Q n := by
    have hs : 0 ≤ ∑ m ∈ Finset.range (n + 1), Cp m := Finset.sum_nonneg fun m _ => hCp m
    dsimp only [Q]
    linarith
  have hP (n : ℕ) : 1 ≤ P n := by
    have hQ₀ := zero_le_one.trans (hQ n)
    dsimp only [P]
    exact le_add_of_nonneg_right (by positivity)
  obtain ⟨A, hA, hRadius⟩ := exists_coframe_radius_exponent (1 + Cf 1)
  refine ⟨A, hA, fun n => ?_⟩
  obtain ⟨B, hB, hSeed⟩ := exists_seedOn_envelopedAmplitude_scaledJetBound_polynomial
    n (1 + Cf n) (by linarith only [hCf n])
  obtain ⟨C, hC, hLeading⟩ := exists_leading_scaledJetBounds_polynomial n hB (hP n)
  refine ⟨C, B, P n, hC, hB, hP n, ?_⟩
  intro U X T t₀ D ℓ Cseed freq k center ht₀ ht₀T hT₁ hD hℓ hℓA hf hfreq
    hX hU hper hFbound hGbound hUjet M κ hc w χ hχ t ht hwidth γ Bjet
  let I := Icc t₀ T
  let F (u : ℝ) (a : Vec3) := fderiv ℝ (X 0 u) a
  let G (u : ℝ) (a : Vec3) := fderiv ℝ (X u 0) (X 0 u a)
  let J (u : ℝ) (a : Vec3) := coframeLift k (F u a)
  let R (u : ℝ) (a : Vec3) := coframePullback k (G u a)
  let L (u : ℝ) (a : Vec3) := fixedTransverseGenerator (M u a) (J u a) (R u a)
  have hT : 0 < T := ht₀.trans_lt ht₀T
  have hf₀ : 0 < freq := zero_lt_one.trans_le hf
  have hD₁ : 1 ≤ D := by linarith
  have hD₀ : 0 ≤ D := zero_le_one.trans hD₁
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have ht₀' : t₀ ∈ Icc 0 T := ⟨ht₀, ht₀T.le⟩
  have hsub : I ⊆ Icc 0 T := Icc_subset_Icc_left ht₀
  have hsubS : I ×ˢ (univ : Set Vec3) ⊆ Icc 0 T ×ˢ (univ : Set Vec3) :=
    fun _ h => ⟨hsub h.1, h.2⟩
  have hU₂ : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hU.of_le (by simp)
  have hk : k ≠ 0 := by
    intro hz
    simp [hz, labelWaveVector] at hfreq
    linarith
  have hκ₀ (u : ℝ) (hu : u ∈ I) (a : Vec3) : κ u a ≠ 0 :=
    transportedCovector_ne_zero_of_parent hT hX hU hper hk u (hsub hu) a
  have hFs : ContDiffOn ℝ ∞ (Function.uncurry F) (I ×ˢ (univ : Set Vec3)) :=
    (hX.contDiffOn_forwardLabelDerivative hT hU hper).mono hsubS
  have hGs : ContDiffOn ℝ ∞ (Function.uncurry G) (I ×ˢ (univ : Set Vec3)) :=
    (hX.contDiffOn_inverseLabelDerivative hT hU hper).mono hsubS
  have hMs : ContDiffOn ℝ ∞ (Function.uncurry M) (I ×ˢ (univ : Set Vec3)) :=
    (hX.contDiffOn_materialGradient hT hU hper).mono hsubS
  have hκs : ContDiffOn ℝ ∞ (Function.uncurry κ) (I ×ˢ (univ : Set Vec3)) :=
    (hX.contDiffOn_transportedCovector hT hU hper k).mono hsubS
  have hws : ContDiffOn ℝ ∞ (Function.uncurry w.amplitude) (I ×ˢ (univ : Set Vec3)) :=
    SeedOn.contDiffOn_amplitude (M := M) (κ := κ) (center := center) w ht₀T hMs hκs hκ₀
  have hFder (a : Vec3) (u : ℝ) (hu : u ∈ I) :
      HasDerivWithinAt (fun s => F s a) ((M u a).comp (F u a)) I u :=
    ((hX.labelDerivative_evolves hT hU₂ hper h₀ a).2 u (hsub hu)).mono hsub
  have hInv (a : Vec3) (u : ℝ) (hu : u ∈ I) :
      (G u a).comp (F u a) = .id ℝ Vec3 ∧ (F u a).comp (G u a) = .id ℝ Vec3 :=
    hX.labelDerivative_inverse hT hU₂ hper h₀ (hsub hu) a
  let centerPoint (u : ℝ) : ℝ × Vec3 := (u, 0)
  have hCenterPoint : Continuous centerPoint := continuous_id.prodMk continuous_const
  have hMaps : MapsTo centerPoint I (I ×ˢ (univ : Set Vec3)) := fun u hu => ⟨hu, mem_univ 0⟩
  have hMzero : ContinuousOn (fun s => M s 0) I :=
    hMs.continuousOn.comp hCenterPoint.continuousOn hMaps
  have hκzero : ContinuousOn (fun s => κ s 0) I :=
    fun u hu => (hc.covector u hu).continuousWithinAt
  let op (u : ℝ) := affineWaveAmplitudeOperator (M u 0) (κ u 0)
  have hCc : ContinuousOn op I :=
    continuousOn_affineWaveAmplitudeOperator hMzero hκzero fun u hu => hκ₀ u hu 0
  have hpos : ∀ u ∈ I, 0 < ‖center u‖ := fun u hu => norm_pos_iff.mpr (hc.nonzero u hu).2.1
  have hCont : ContinuousOn center I := fun u hu => (hc.amplitude u hu).continuousWithinAt
  have hdc : ContinuousOn (fun u => op u (center u)) I := hCc.clm_apply hCont
  obtain ⟨dg, hdg, hg⟩ := norm_hasContinuous_derivative (f := center)
    (df := fun u => op u (center u)) (I := I) hc.amplitude hdc fun u hu => (hc.nonzero u hu).2.1
  have hstable (y : ℝ → transversePlane k)
      (hy : ∀ u ∈ I, HasDerivWithinAt y (L u 0 (y u)) I u)
      (s : ℝ) (hs : s ∈ I) (v : ℝ) (hv : v ∈ Icc s T) :
      ‖y v‖ / ‖center v‖ ≤ D ^ 3 * (‖y s‖ / ‖center s‖) := by
    have hId (u : ℝ) (hu : u ∈ I) := coframe_identities k (hInv 0 u hu).1 (hInv 0 u hu).2
    have hv' : v ∈ I := ⟨hs.1.trans hv.1, hv.2⟩
    have hb := weighted_fixedTransverse_forward (M := fun u => M u 0) (k := fun u => κ u 0)
      (J := fun u => J u 0) (R := fun u => R u 0) (g := fun u => ‖center u‖)
      hD₀ hD₀ (fun u hu => hκ₀ u hu 0)
      hpos (fun u hu => (hId u hu).1) (fun u hu => (hId u hu).2)
      (fun u hu => coframeLift_hasDerivWithinAt k (F := fun v => F v 0)
        (M := fun v => M v 0) (hFder 0 u hu))
      (fun u hu => (norm_coframeLift_le k _).trans (hFbound u (hsub hu) 0))
      (fun u hu => (norm_coframePullback_le k _).trans (hGbound u (hsub hu) 0))
      hc.stability y hy hs hv' hv.1
    simpa only [show D ^ 3 = D * D * D by ring] using hb
  have hcjets (m : ℕ) (u : ℝ) (hu : u ∈ I) :=
    (hCoframe hT hT₁ hD₁ hX hU hper hFbound hGbound hUjet k hf₀ ht₀' hfreq m u (hsub hu)).2.2.2
  have hrad := hRadius hD hℓ hℓA
  have hC₁ : 1 ≤ 1 + Cf 1 := by linarith [hCf 1]
  have hCJ (m : ℕ) (u : ℝ) (hu : u ∈ I) (j : ℕ) (hj : j ≤ m) (a : Vec3) :
      ‖iteratedFDeriv ℝ j (J u) a‖ ≤ (1 + Cf m) * D ^ (16 * j + 1) ∧
      ‖iteratedFDeriv ℝ j (R u) a‖ ≤ (1 + Cf m) * D ^ (16 * j + 9) ∧
      ‖iteratedFDeriv ℝ j (L u) a‖ ≤ (1 + Cf m) * D ^ (16 * j + 11) := by
    obtain ⟨hJ, hR, hA⟩ := hcjets m u hu a j hj
    have hCfm : Cf m ≤ 1 + Cf m := by linarith
    exact ⟨hJ.trans (mul_le_mul_of_nonneg_right hCfm (by positivity)),
      hR.trans (mul_le_mul_of_nonneg_right hCfm (by positivity)),
      hA.trans (mul_le_mul_of_nonneg_right hCfm (by positivity))⟩
  have hgrad (u : ℝ) (hu : u ∈ I) (a : Vec3) :
      ‖iteratedFDeriv ℝ 1 (L u) a‖ ≤ (1 + Cf 1) * D ^ 27 :=
    (hCJ 1 u hu 1 le_rfl a).2.2
  have hAjet := hSeed (F := F) (G := G) (M := M) (k := k) w
    ht₀T (by linarith only [hT₁, ht₀]) hℓ hD₁ hC₁ hrad
    (fun a u hu => hκ₀ u hu a) hFder hInv hFs hGs hMs hws hpos hg hdg hgrad (hCJ n) hstable t ht
  have hQm (m : ℕ) (hm : m ≤ n) : Cp m ≤ Q n :=
    (Finset.single_le_sum (fun m _ => hCp m) (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))).trans
      (le_add_of_nonneg_left zero_le_one)
  have hQ₀ : 0 ≤ Q n := zero_le_one.trans (hQ n)
  have hjet (m : ℕ) (hm : m ≤ n) (a : Vec3) :
      ‖iteratedFDeriv ℝ m (M t) a‖ ≤ Q n * D ^ (6 * m + 1) ∧
      ‖iteratedFDeriv ℝ m (fun b => freq⁻¹ • κ t b) a‖ ≤ Q n * D ^ (7 * m + 2) ∧
      ‖iteratedFDeriv ℝ m (fun b => freq ^ 2 / ‖κ t b‖ ^ 2) a‖ ≤ Q n * D ^ (16 * m + 4) := by
    have h := hPressure hT hT₁ hD₁ hX hU hper hFbound hGbound hUjet k hf₀ ht₀' hfreq m t (hsub ht) a
    have hb (e : ℕ) : Cp m * D ^ e ≤ Q n * D ^ e :=
      mul_le_mul_of_nonneg_right (hQm m hm) (pow_nonneg hD₀ _)
    exact ⟨h.2.2.2.1.trans (hb _), h.2.2.2.2.1.trans (hb _), h.2.2.2.2.2.1.trans (hb _)⟩
  have hMslice := contDiff_slice_on_closedSlab (u := M) hMs ht
  have hκslice := contDiff_slice_on_closedSlab (u := κ) hκs ht
  obtain ⟨hPs, hPjet⟩ := phaseJetBound_normalizedPressureAmplitudeCoefficient_polynomial n
    (M := M t) (κ := κ t) (freq := freq) (ℓ := ℓ) (D := D) (C := Q n)
    hf₀ hℓ hD₁ (radius_power_small hD₁ hℓ.le hC₁ hrad (by decide)) hQ₀
    hMslice hκslice (hκ₀ t ht) hjet
  have hPjet' : PhaseJetBound n (P n * D ^ 7)
      (fun a => hierarchyRelayPressureAmplitudeCoefficient (M t (ℓ • a)) (freq⁻¹ • κ t (ℓ • a))) := by
    intro m hm a
    refine (hPjet m hm a).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    dsimp only [P]
    linarith
  have hScale : ContDiff ℝ ∞ (fun a : Vec3 => ℓ • a) := contDiff_id.const_smul _
  have hAs : ContDiff ℝ ∞ (fun a => radialEnvelope ℓ (ℓ • a) • w.amplitude t (ℓ • a)) :=
    ((contDiff_radialEnvelope hℓ).comp hScale).smul ((contDiff_slice_on_closedSlab hws ht).comp hScale)
  obtain ⟨hv, hp⟩ := hLeading (freq := freq) (ℓ := ℓ) (χ := χ) (D := D)
    (a := w.amplitude t) (κ := κ t) (M := M t) hf hD₁ hχ
    (norm_nonneg (center t)) hAs hPs hAjet hPjet'
  have hvEq : (fun a s => ((χ * radialEnvelope ℓ a) * waveProfile hwidth s) • w.amplitude t a) =
      fun a s => χ • w.leading hwidth t a s := by
    funext a s
    rw [SeedOn.leading, smul_smul, mul_assoc]
  have hpEq : (fun a s => freq * oscillatoryPhasePressure (M t a) (κ t a) (fun _ => 0)
      (fun q => ((χ * radialEnvelope ℓ a) * waveProfile hwidth q) • w.amplitude t a) s) =
      fun a s => freq * (χ * w.leadingPressure hwidth t a s) := by
    funext a s
    rw [oscillatoryPhasePressure_primary_eq, SeedOn.leadingPressure]
    simp only [wavePressureCoefficient]
    ring
  rw [hvEq] at hv
  rw [hpEq] at hp
  exact ⟨⟨hv, hp⟩, hAjet, hPs, hPjet'⟩

set_option maxHeartbeats 650000 in
/-- The scaled leading velocity and pressure estimates obtained from the
same seed and parent coefficients. -/
theorem exists_parent_seed_leadingScaledJetBounds (W : ℕ → ℝ) (hW : ∀ m, 0 ≤ W m) :
    ∃ A : ℕ, 30 ≤ A ∧ ∀ n : ℕ, ∃ C : ℝ, 1 ≤ C ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T t₀ D ℓ Cseed freq : ℝ}
        {k : Vec3} {center : ℝ → Vec3},
      0 ≤ t₀ → t₀ < T → T ≤ 1 → 2 ≤ D → 0 < ℓ → ℓ ≤ (D ^ A)⁻¹ →
      1 ≤ freq → ‖labelWaveVector X 0 0 k t₀‖ = freq →
      IsLabelFlowOn U X (Icc 0 T) →
      ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
      (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
      (∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
        ‖iteratedFDeriv ℝ j (U t) x‖ ≤ W n * D ^ j) →
      let M (t : ℝ) (a : Vec3) := fderiv ℝ (U t) (X 0 t a)
      let κ (t : ℝ) (a : Vec3) := labelWaveVector X 0 a k t
      CenterWaveOn (fun t => M t 0) (fun t => κ t 0) center t₀ T D →
      ∀ (w : SeedOn M κ center t₀ T ℓ D Cseed) {χ : ℝ}, |χ| ≤ 1 →
        ∀ t, t ∈ Icc t₀ T →
        let h := freq ^ (-1 / 2 : ℝ)
        let γ := freq ^ (3 / 4 : ℝ) * ‖center t‖
        let B := γ * (C * D ^ 20 * freq ^ (-5 / 4 : ℝ))
        PhaseJetBound n B (scaledPhaseProfile ℓ h (fun a s => χ • w.leading h t a s)) ∧
        PhaseJetBound n B (scaledPhaseProfile ℓ h (fun a s => freq * (χ * w.leadingPressure h t a s))) := by
  obtain ⟨A, hA, hJets⟩ := exists_parent_seed_leadingAndSlowJetBounds W hW
  refine ⟨A, hA, fun n => ?_⟩
  obtain ⟨C, _, _, hC, _, _, hBound⟩ := hJets n
  refine ⟨C, hC, ?_⟩
  intro U X T t₀ D ℓ Cseed freq k center ht₀ ht₀T hT₁ hD hℓ hr hf hκ hX hU hper hF hG hUjet
    M κ hc w χ hχ t ht hwidth γ Bjet
  exact (hBound (Cseed := Cseed) ht₀ ht₀T hT₁ hD hℓ hr hf hκ hX hU hper hF hG hUjet hc w hχ t ht).1

end LocalizedAmplitude

namespace LocalizedAmplitude

set_option maxHeartbeats 1450000 in
/-- The actual switched later velocity and pressure satisfy (5.25) in the
twisted hierarchy norm, at every fixed order and one common envelope radius. -/
theorem exists_parent_seed_twistedLeading_ampSeminorm_le (W : ℕ → ℝ) (hW : ∀ m, 0 ≤ W m) :
    ∃ A : ℕ, 30 ≤ A ∧ ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T t₀ D ℓ Cseed freq r : ℝ}
        {k : Vec3} {center : ℝ → Vec3},
      T ≤ 1 → 2 ≤ D → 0 < ℓ → ℓ ≤ (D ^ A)⁻¹ →
      ∀ (hf : 1 ≤ freq), ‖labelWaveVector X 0 0 k t₀‖ = freq →
      IsLabelFlowOn U X (Icc 0 T) →
      ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
      (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
      (∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
        ‖iteratedFDeriv ℝ j (U t) x‖ ≤ W n * D ^ j) →
      let M (t : ℝ) (a : Vec3) := fderiv ℝ (U t) (X 0 t a)
      let κ (t : ℝ) (a : Vec3) := labelWaveVector X 0 a k t
      ∀ (hc : CenterWaveOn (fun t => M t 0) (fun t => κ t 0) center t₀ T D)
        (w : SeedOn M κ center t₀ T ℓ D Cseed),
      let h := freq ^ (-1 / 2 : ℝ)
      ∀ (d : w.HierarchyRegularity r h),
      let γ (t : ℝ) := freq ^ (3 / 4 : ℝ) * ‖center t‖
      let hγ : ContinuousOn γ (Icc t₀ T) :=
        (HasDerivWithinAt.continuousOn hc.amplitude).norm.const_mul _
      let hpos (t : ℝ) (ht : t ∈ Icc t₀ T) : 0 < γ t :=
        mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hf) _)
          (norm_pos_iff.mpr (hc.nonzero t ht).2.1)
      let v := HierarchyTwistedProfile.amplitudeSeminorm False ℓ h n d.end_pos d.nonneg_start
        d.start_lt_end.le γ hγ hpos (SeedOn.twistedLeading d k)
      let p := HierarchyTwistedProfile.amplitudeSeminorm False ℓ h n d.end_pos d.nonneg_start
        d.start_lt_end.le γ hγ hpos (SeedOn.twistedPressure d k)
      v + freq * p ≤ C * D ^ 20 * freq ^ (-5 / 4 : ℝ) := by
  obtain ⟨A, hA, hRawAll⟩ := exists_parent_seed_leadingScaledJetBounds W hW
  refine ⟨A, hA, fun n => ?_⟩
  obtain ⟨C₀, hC₀, hRaw⟩ := hRawAll n
  let count : ℝ := (hierarchyAdmissibleWords (Fin 4) n).card
  let C := 2 * count * C₀
  have hC₀' : 0 ≤ C₀ := zero_le_one.trans hC₀
  refine ⟨C, mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) hC₀', ?_⟩
  intro U X T t₀ D ℓ Cseed freq r k center hT hD hℓ hℓA hf hfreq
    hX hU hper hF hG hUjets M κ hc w h d γ hγ hpos v p
  let B := C₀ * D ^ 20 * freq ^ (-5 / 4 : ℝ)
  have hD₀ : 0 ≤ D := by linarith
  have hf₀ : 0 ≤ freq := zero_le_one.trans hf
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hJet (t : ℝ) (ht : t ∈ Icc t₀ T) :
      PhaseJetBound n (γ t * B) (scaledPhaseProfile ℓ h (w.switchedLeading r h t)) ∧
      PhaseJetBound n (γ t * B) (scaledPhaseProfile ℓ h (fun a z => freq * w.switchedPressure r h t a z)) := by
    have hχ : |waveSwitch t₀ r t| ≤ 1 := by
      change |Real.smoothTransition (r * (t - t₀))| ≤ 1
      rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    exact hRaw d.nonneg_start d.start_lt_end hT hD hℓ hℓA hf hfreq hX hU hper hF hG hUjets
      hc w hχ t ht
  obtain ⟨hv, hp⟩ := SeedOn.twistedLeading_pressure_amplitudeSeminorm_le_of_scaledJetBounds
    d k n hf₀ hB hB hγ hpos (fun t ht => (hJet t ht).1) (fun t ht => (hJet t ht).2)
  calc
    _ ≤ count * B + count * B := add_le_add hv hp
    _ = _ := by dsimp only [B, C]; ring

end LocalizedAmplitude

end

end TorusEuler
