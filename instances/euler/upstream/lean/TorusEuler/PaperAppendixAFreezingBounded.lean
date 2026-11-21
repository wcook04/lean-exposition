import TorusEuler.PaperAppendixAFreezingHolder
import TorusEuler.PaperAppendixAFreezingWordBounds

/-! Bounded inverses on the higher Hölder spaces in Lemma A.2. -/

open MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "Paths" => Lp Vec3 2 (volume.restrict (Ioc (0 : ℝ) 1))
local notation "lift(" f ")" => (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) f)

set_option maxHeartbeats 1500000 in
private theorem freezingHigherHolderBound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : HalfHolder A H →L[ℝ] HalfHolder A H) (hP : ∀ z, P (P z) = P z)
    (hWeak : ∀ z, ‖freezingHaarEmbedding (P z)‖ ≤ ‖freezingHaarEmbedding z‖)
    (hPair : ∀ z (w : freezingFixedSpace P),
      ⟪freezingHaarEmbedding (P z), freezingHaarEmbedding w.val⟫_ℝ =
        ⟪freezingHaarEmbedding z, freezingHaarEmbedding w.val⟫_ℝ)
    (hTrans : ∀ a z, P (HalfHolder.torusTranslate a z) = HalfHolder.torusTranslate a (P z))
    (B : HalfHolder A (H →L[ℝ] H)) (e : freezingFixedSpace P ≃L[ℝ] freezingFixedSpace P)
    (he : (e : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) =
      freezingCompression P B.coefficientMul hP)
    {μ : ℝ} (hμ : 0 < μ) (hCoercive : ∀ (z : freezingFixedSpace P) a,
      μ * ‖HalfHolder.eval a z.val‖ ^ 2 ≤
        ⟪HalfHolder.eval a B (HalfHolder.eval a z.val), HalfHolder.eval a z.val⟫_ℝ)
    (N : ℕ) (hB : SpatialHolderHalf N lift(B)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : freezingFixedSpace P, SpatialHolderHalf N lift(f.val) →
      SpatialHolderHalf N lift((e.symm f).val) ∧
        spatialHolderHalfNorm N lift((e.symm f).val) ≤ C * spatialHolderHalfNorm N lift(f.val) := by
  let a := ‖(e.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P)‖
  let b := Real.sqrt 2 * spatialHolderHalfNorm N lift(B)
  let K := max 1 (a * (1 + ‖P‖ * ((2 : ℝ) ^ N * (2 * b)))) ^ (N + 1)
  have ha : 0 ≤ a := (e.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P).opNorm_nonneg
  have hb : 0 ≤ b := mul_nonneg (Real.sqrt_nonneg _) (nonneg_spatialHolderHalfNorm _ _ hB)
  have hK : 0 ≤ K := pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  obtain ⟨Bjet, hB₀, hBjet, hBnorm⟩ := exists_halfHolderWords_norm_le hB
  obtain ⟨C, hC, hBound⟩ := exists_spatialHolderHalfNorm_le_of_word_bounds (E := H) N
  refine ⟨C * K * Real.sqrt 2, by positivity, ?_⟩
  intro f hf
  let F := Real.sqrt 2 * spatialHolderHalfNorm N lift(f.val)
  have hF : 0 ≤ F := mul_nonneg (Real.sqrt_nonneg _) (nonneg_spatialHolderHalfNorm _ _ hf)
  obtain ⟨Fjet, hF₀, hFjet, hFnorm⟩ := exists_halfHolderWords_norm_le hf
  let v := e.symm f
  have hV : P v.val = v.val := (mem_freezingFixedSpace _ _).mp v.property
  have hEq : P ((Bjet []).coefficientMul v.val) = Fjet [] := by
    rw [hB₀, hF₀, ← freezingCompression_val P B.coefficientMul hP v]
    have heval : e v = freezingCompression P B.coefficientMul hP v := DFunLike.congr_fun he v
    rw [← heval, e.apply_symm_apply]
  have heJet : (e : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) =
      freezingCompression P (Bjet []).coefficientMul hP := by rwa [hB₀]
  have hCoerciveJet (z : freezingFixedSpace P) (x : A) :
      μ * ‖HalfHolder.eval x z.val‖ ^ 2 ≤
        ⟪HalfHolder.eval x (Bjet []) (HalfHolder.eval x z.val), HalfHolder.eval x z.val⟫_ℝ := by
    rw [hB₀]
    exact hCoercive z x
  obtain ⟨w, hw, hfix, hEqJet, hDer⟩ := endpointSpatialAllFiniteMixedDerivatives P hP 1 zero_le_one
    (fun z => by simpa only [one_mul] using hWeak z) hPair Bjet Fjet v.val coordinateDirection
    (fun i r z => hTrans (toUnitTorus (r • coordinateDirection i)) z) hV hEq e heJet
    hμ hCoerciveJet N hBjet hFjet
  have hNorm := paperA2_wordNorm_le N a ‖P‖ b F
    ha P.opNorm_nonneg hb hF (fun l => ‖Bjet l‖) (fun l => ‖Fjet l‖) (fun l => ‖w l‖)
    (fun l hl => ⟨norm_nonneg (Bjet l), hBnorm l hl⟩) hFnorm
    (fun l hl => norm_endpointSpatialMixedDerivative_le_of_equation
      P hP Bjet Fjet w l (hfix l hl) (hEqJet l hl) e heJet)
  have hReg := (hasSpatialHolderWords_iff_spatialHolderHalf N v.val).1 ⟨w, hw, hDer⟩
  have hv := hBound w (K * F) (mul_nonneg hK hF) hDer hNorm
  rw [hw] at hv
  refine ⟨hReg, hv.trans_eq ?_⟩
  dsimp only [F]
  ring

private theorem freezingHolderOne {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : Vec3 → H} {n : ℕ} (hf : SpatialHolderHalf (n + 1) f) : SpatialHolderHalf 1 f := by
  refine ⟨hf.1.of_le ?_, fun j hj => hf.2 j (hj.trans (Nat.succ_le_succ (Nat.zero_le n)))⟩
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

set_option maxHeartbeats 2000000 in
/-- The compressed spatial inverse is bounded in the genuine positive-order Hölder norm. -/
theorem paperLemmaA2_spatial_holder_boundedInverse {μ : ℝ} (hμ : 0 < μ)
    (B : HalfHolder A (Vec3 →L[ℝ] Vec3))
    (hCoercive : ∀ a w, μ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a B w, w⟫_ℝ)
    (n : ℕ) (hB : SpatialHolderHalf (n + 1) lift(B)) :
    let P := endpointStrongSpatialLeray
    ∃ e : freezingFixedSpace P ≃L[ℝ] freezingFixedSpace P,
      (e : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) =
        freezingCompression P B.coefficientMul endpointStrongSpatialLeray_idempotent ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f : freezingFixedSpace P, SpatialHolderHalf (n + 1) lift(f.val) →
        SpatialHolderHalf (n + 1) lift((e.symm f).val) ∧
          spatialHolderHalfNorm (n + 1) lift((e.symm f).val) ≤
            C * spatialHolderHalfNorm (n + 1) lift(f.val) := by
  dsimp only
  obtain ⟨_, _, hInverse⟩ := paperLemmaA2_spatial_holder
  obtain ⟨e, he, _⟩ := hInverse B hμ (freezingHolderOne hB) hCoercive
  exact ⟨e, he, freezingHigherHolderBound endpointStrongSpatialLeray endpointStrongSpatialLeray_idempotent
    endpointStrongSpatialLeray_haar_norm_le endpointStrongSpatialLeray_pairing
    endpointStrongSpatialLeray_torusTranslate B e he hμ (fun z a => hCoercive a _) (n + 1) hB⟩

set_option maxHeartbeats 12000000 in
/-- The time-path inverse on the mixed fixed space satisfies the same higher Hölder conclusion. -/
theorem paperLemmaA2_mixed_holder_boundedInverse {μ : ℝ} (hμ : 0 < μ)
    (B : HalfHolder A (Paths →L[ℝ] Paths))
    (hCoercive : ∀ a w, endpointIntegral 1 w = 0 → μ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a B w, w⟫_ℝ)
    (n : ℕ) (hB : SpatialHolderHalf (n + 1) lift(B)) :
    let Q := endpointStrongMixedLeray 1
    ∃ e : freezingFixedSpace Q ≃L[ℝ] freezingFixedSpace Q,
      (e : freezingFixedSpace Q →L[ℝ] freezingFixedSpace Q) =
        freezingCompression Q B.coefficientMul (endpointStrongMixedLeray_idempotent zero_lt_one) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f : freezingFixedSpace Q, SpatialHolderHalf (n + 1) lift(f.val) →
        SpatialHolderHalf (n + 1) lift((e.symm f).val) ∧
          spatialHolderHalfNorm (n + 1) lift((e.symm f).val) ≤
            C * spatialHolderHalfNorm (n + 1) lift(f.val) := by
  dsimp only
  obtain ⟨_, _, hInverse⟩ := paperLemmaA2_mixed_holder
  obtain ⟨e, he, _⟩ := hInverse B hμ (freezingHolderOne hB) hCoercive
  have hc (z : freezingFixedSpace (endpointStrongMixedLeray 1)) (x : A) :
      μ * ‖HalfHolder.eval x z.val‖ ^ 2 ≤
        ⟪HalfHolder.eval x B (HalfHolder.eval x z.val), HalfHolder.eval x z.val⟫_ℝ := by
    apply hCoercive x
    have hz := (mem_freezingFixedSpace _ _).mp z.property
    rw [← hz]
    exact endpointStrongMixedLeray_timeIntegral_eq_zero zero_lt_one z.val x
  exact ⟨e, he, freezingHigherHolderBound (endpointStrongMixedLeray 1)
    (endpointStrongMixedLeray_idempotent zero_lt_one)
    (endpointStrongMixedLeray_haar_norm_le zero_lt_one) (endpointStrongMixedLeray_pairing zero_lt_one)
    (endpointStrongMixedLeray_torusTranslate 1) B e he hμ hc (n + 1) hB⟩

private theorem freezingHolderBoundedForward {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : HalfHolder A H →L[ℝ] HalfHolder A H) (hComm : CommutesTorusLineDerivatives P)
    (B : HalfHolder A (H →L[ℝ] H)) (n : ℕ) (hB : SpatialHolderHalf n lift(B)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : freezingFixedSpace P, SpatialHolderHalf n lift(v.val) →
      SpatialHolderHalf n lift(P (B.coefficientMul v.val)) ∧
        spatialHolderHalfNorm n lift(P (B.coefficientMul v.val)) ≤ C * spatialHolderHalfNorm n lift(v.val) := by
  let ev : (H →L[ℝ] H) →L[ℝ] H →L[ℝ] H := (ContinuousLinearMap.apply ℝ H).flip
  let Cprod := 3 * ((n : ℝ) + 1) * ‖ev‖ * (2 : ℝ) ^ n * spatialHolderHalfNorm n lift(B)
  let Cproj := 2 * Real.sqrt 2 * ‖P‖
  have hB₀ := nonneg_spatialHolderHalfNorm _ _ hB
  have hCproj : 0 ≤ Cproj := by positivity
  refine ⟨Cproj * Cprod, by positivity, ?_⟩
  intro v hv
  let M := B.coefficientMul v.val
  have heq : lift(M) = (fun x => ev (HalfHolder.eval (toUnitTorus x) B)
      (HalfHolder.eval (toUnitTorus x) v.val)) := by
    funext x
    exact HalfHolder.eval_coefficientMul B v.val (toUnitTorus x)
  have hMul := spatialHolderHalf_bilinear ev hB hv
  rw [← heq] at hMul
  have hM₀ := (spatialHolderHalf_zero_of_halfHolder M).1
  have hPer : SpatiallyPeriodic lift(M) := by
    intro k x
    exact congrArg (fun a => HalfHolder.eval a M) ((toUnitTorus_eq_iff _ _).mpr ⟨k, rfl⟩)
  have hOut := spatialHolderHalf_halfHolderProjectionLift n P hComm hPer hMul.1
  rw [halfHolderProjectionLift_eq_of_descent P hPer hM₀ M (fun _ => rfl)] at hOut
  refine ⟨hOut.1, hOut.2.trans ((mul_le_mul_of_nonneg_left hMul.2 hCproj).trans_eq ?_)⟩
  change Cproj * (Cprod * spatialHolderHalfNorm n lift(v.val)) = _
  exact (mul_assoc Cproj Cprod _).symm

/-- The compressed spatial multiplication operator is bounded on each higher Hölder space. -/
theorem paperLemmaA2_spatial_holder_boundedForward (B : HalfHolder A (Vec3 →L[ℝ] Vec3))
    (n : ℕ) (hB : SpatialHolderHalf n lift(B)) :
    let P := endpointStrongSpatialLeray
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : freezingFixedSpace P, SpatialHolderHalf n lift(v.val) →
      SpatialHolderHalf n lift(P (B.coefficientMul v.val)) ∧
        spatialHolderHalfNorm n lift(P (B.coefficientMul v.val)) ≤ C * spatialHolderHalfNorm n lift(v.val) :=
  freezingHolderBoundedForward endpointStrongSpatialLeray
    endpointStrongSpatialLeray_preserves_torusDirectionalDerivative B n hB

/-- The compressed time-path multiplication operator is bounded on each higher Hölder space. -/
theorem paperLemmaA2_mixed_holder_boundedForward (B : HalfHolder A (Paths →L[ℝ] Paths))
    (n : ℕ) (hB : SpatialHolderHalf n lift(B)) :
    let Q := endpointStrongMixedLeray 1
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : freezingFixedSpace Q, SpatialHolderHalf n lift(v.val) →
      SpatialHolderHalf n lift(Q (B.coefficientMul v.val)) ∧
        spatialHolderHalfNorm n lift(Q (B.coefficientMul v.val)) ≤ C * spatialHolderHalfNorm n lift(v.val) := by
  apply freezingHolderBoundedForward (endpointStrongMixedLeray 1) _ B n hB
  intro u f df hf
  exact freezingProjection_preserves_torusDirectionalDerivative_of_haar_bound
    (endpointStrongMixedLeray 1) 1 zero_le_one
    (fun z => by simpa only [one_mul] using endpointStrongMixedLeray_haar_norm_le zero_lt_one z)
    u (fun h z => endpointStrongMixedLeray_torusTranslate 1 (toUnitTorus (h • u)) z) f df hf

end

end TorusEuler
