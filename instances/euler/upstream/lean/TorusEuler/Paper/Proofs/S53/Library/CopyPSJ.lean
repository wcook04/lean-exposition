import TorusEuler.ParentSeedJetBudgets
import TorusEuler.Paper.Proofs.S53.Library.Leaf51
import TorusEuler.Paper.Proofs.S53.Library.CopySDB
import TorusEuler.Paper.Proofs.S53.Library.Leaves
import TorusEuler.Paper.Proofs.S53.Library.D2Bridge
import TorusEuler.Paper.Proofs.S53.Library.D2Coframe
import TorusEuler.Paper.Proofs.S53.Library.CopyLAC
import TorusEuler.Paper.Proofs.S53.Library.CopyLACaux
import TorusEuler.Paper.Proofs.S53.Library.CopyODEaux
import TorusEuler.Paper.Proofs.S53.Library.CopyODE
import TorusEuler.Paper.Proofs.S53.Library.CopySDB

/-!
# S53 library: Lemma 5.3 chain: parent seed jets

Generated copy (script `s53tools/mkcopy.py`) of the declarations exists_parent_seed_leadingScaledJetBounds, exists_parent_seed_leadingAndSlowJetBounds, exists_coframe_radius_exponent of
`TorusEuler/ParentSeedJetBudgets.lean`, placed in `TorusEuler.Paper.Lib.S53` so that the calls of the leaf results of
Lemmas 3.1, D.1 and D.3 resolve to the hypotheses carried by `Leaves`; the bounds of Lemma D.2 come from
`Leaves.d2` (`mul_of_D2`, `rescale_of_D2`) and the jets of Proposition 5.1 enter through the hypothesis
`Leaf2` / `Lib.S5a.LeafBounds`.
-/
noncomputable section

variable [TorusEuler.Paper.Lib.S53.Leaves]

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S53

open TorusEuler
noncomputable section

namespace LocalizedAmplitude

open LocalizedAmplitude
omit [TorusEuler.Paper.Lib.S53.Leaves] in
/-- Copy of the library lemma `TorusEuler.exists_coframe_radius_exponent` (glue), placed in `Paper.Lib.S53`. -/
theorem exists_coframe_radius_exponent (C : ℝ) :
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
      Leaf2 W U X T D k freq →
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
  obtain ⟨Kg, Ka, hKg, hKa, hCoframe⟩ := exists_parent_transverseCoframeJetPower W hW
  obtain ⟨A, hA, hRadius⟩ := exists_coframe_radius_exponent (1 + Ka 1)
  refine ⟨A, hA, fun n => ?_⟩
  obtain ⟨Cpress, hCpress, hPress⟩ :=
    phaseJetBound_normalizedPressureAmplitudeCoefficient_polynomial n W hW
  let P : ℝ := 1 + Cpress
  have hP : 1 ≤ P := by dsimp only [P]; linarith
  obtain ⟨B, hB, hSeed⟩ :=
    exists_seedOn_envelopedAmplitude_scaledJetBound_polynomial n W Kg Ka hW hKg hKa
  obtain ⟨C, hC, hLeading⟩ := exists_leading_scaledJetBounds_polynomial n hB hP
  refine ⟨C, B, P, hC, hB, hP, ?_⟩
  intro U X T t₀ D ℓ Cseed freq k center ht₀ ht₀T hT₁ hD hℓ hℓA hf hfreq
    hX hU hper hFbound hGbound hUjet M κ hc w χ hχ t ht hwidth γ Bjet
  obtain ⟨D₀, hDb, hpow, hLeaf₀⟩ := hUjet
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
  have hcoframe (u : ℝ) (hu : u ∈ I) :=
    hCoframe hT hT₁ hD₁ hDb hX hU hper hFbound hGbound k hf₀ ht₀' hfreq hLeaf₀ u (hsub hu)
  have hrad := hRadius hD hℓ hℓA
  have hC₁ : 1 ≤ 1 + Ka 1 := by linarith [hKa 1]
  have hpow64 : D₀ ^ 64 ≤ D := hpow
  have hgrad (u : ℝ) (hu : u ∈ I) (a : Vec3) :
      ‖iteratedFDeriv ℝ 1 (L u) a‖ ≤ (1 + Ka 1) * D ^ 27 := by
    have hAt := (hcoframe u hu).2.2.2.2.2
    have hEq : L u = fun b => (transversePlane k).orthogonalProjectionOnto.comp (coframeLift k
        ((-2 : ℝ) • ((fderiv ℝ (X u 0) (X 0 u b)).comp (oscillatoryTransverseProjection
          ((fderiv ℝ (X u 0) (X 0 u b)).adjoint k))).comp
            ((fderiv ℝ (U u) (X 0 u b)).comp (fderiv ℝ (X 0 u) b)))) := by
      funext b
      exact fixedTransverseGenerator_eq k _ _ _
    rw [hEq]
    refine (norm_iteratedFDeriv_generator_le k hAt.1 1 a).trans ((hAt.2 1 a).trans ?_)
    have h2 : D₀ ^ (64 * (1 + 1)) ≤ D ^ 27 := by
      rw [show 64 * (1 + 1) = 64 * 2 by norm_num, pow_mul]
      exact (pow_le_pow_left₀ (pow_nonneg (by linarith) _) hpow64 2).trans
        (pow_le_pow_right₀ hD₁ (by norm_num))
    exact mul_le_mul (by linarith [hKa 1]) h2 (pow_nonneg (by linarith) _) (by linarith [hKa 1])
  have hAjet := hSeed (F := F) (G := G) (M := M) (k := k) w
    ht₀T (by linarith only [hT₁, ht₀]) hℓ hD₁ hDb hpow hC₁ hrad
    (fun a u hu => hκ₀ u hu a) hFder hInv hFs hGs hMs hws hpos hg hdg hgrad
    (fun u hu => (hcoframe u hu).2.2.2.1) (fun u hu => (hcoframe u hu).2.2.2.2.1)
    (fun u hu => (hcoframe u hu).2.2.2.2.2) hstable t ht
  have hMslice := contDiff_slice_on_closedSlab (u := M) hMs ht
  have hκslice := contDiff_slice_on_closedSlab (u := κ) hκs ht
  have hpow16 (e m : ℕ) (he : e ≤ 16 * (m + 1)) : D₀ ^ e ≤ D₀ ^ (16 * (m + 1)) :=
    pow_le_pow_right₀ hDb he
  have hMj : JetPower W D₀ 16 (M t) := ⟨hMslice, fun m a =>
    ((hLeaf₀ m t (hsub ht) a).2.2.2.1).trans
      (mul_le_mul_of_nonneg_left (hpow16 _ m (by omega)) (hW m))⟩
  have hKj : JetPower W D₀ 16 (fun b => freq⁻¹ • κ t b) := ⟨hκslice.const_smul _, fun m a =>
    ((hLeaf₀ m t (hsub ht) a).2.2.2.2.1).trans
      (mul_le_mul_of_nonneg_left (hpow16 _ m (by omega)) (hW m))⟩
  have hQj : JetPower W D₀ 16 (fun b => freq ^ 2 / ‖κ t b‖ ^ 2) :=
    ⟨contDiff_const.div (hκslice.norm_sq ℝ) fun a => pow_ne_zero _ (norm_ne_zero_iff.mpr (hκ₀ t ht a)),
      fun m a => ((hLeaf₀ m t (hsub ht) a).2.2.2.2.2.1).trans
        (mul_le_mul_of_nonneg_left (hpow16 _ m (by omega)) (hW m))⟩
  obtain ⟨hPs, hPjet⟩ := hPress (M := M t) (κ := κ t) (freq := freq) (ℓ := ℓ) (D := D) (D₀ := D₀)
    hf₀ hℓ hD₁ hDb hpow (radius_power_small hD₁ hℓ.le hC₁ hrad (by decide)) hκslice (hκ₀ t ht)
    hMj hKj hQj
  have hPjet' : PhaseJetBound n (P * D ^ 7)
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
      Leaf2 W U X T D k freq →
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

open LocalizedAmplitude
end LocalizedAmplitude

end

end TorusEuler.Paper.Lib.S53

