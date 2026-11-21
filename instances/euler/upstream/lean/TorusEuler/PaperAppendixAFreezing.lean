import TorusEuler.EndpointConcreteInverses
import TorusEuler.EndpointConcreteSpatialBootstrap
import TorusEuler.PhaseJetBounds

/-! The spatial and time-path instances of the freezing lemma A.2. -/

open MeasureTheory Set UnitAddTorus
open scoped InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "Paths" => Lp Vec3 2 (volume.restrict (Ioc (0 : ℝ) 1))
local notation "P" => endpointStrongSpatialLeray
local notation "Q" => endpointStrongMixedLeray 1

private theorem freezingScale_four_le_double {μ S L : ℝ} (hμ : 0 < μ)
    (hS : 0 ≤ S) (hL : 0 ≤ L) :
    4 + μ⁻¹ + S + L ≤ 2 * (2 + μ⁻¹ + S + L) := by
  linarith only [inv_nonneg.mpr hμ.le, hS, hL]

private theorem appendixInversePointwise {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃L[ℝ] E) {μ M S L : ℝ} (hμ : 0 < μ) (hM : 0 ≤ M) (hS : 0 ≤ S) (hL : 0 ≤ L)
    (hNorm : ‖(e.symm : E →L[ℝ] E)‖ ≤ M * (4 + μ⁻¹ + S + L) ^ (145 : ℕ)) (v : E) :
    ‖v‖ ≤ M * 2 ^ (145 : ℕ) * (2 + μ⁻¹ + S + L) ^ (145 : ℕ) * ‖e v‖ := by
  have hcomp : ‖v‖ ≤ ‖(e.symm : E →L[ℝ] E)‖ * ‖e v‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
      using (e.symm : E →L[ℝ] E).le_opNorm (e v)
  have hPow := pow_le_pow_left₀ (show 0 ≤ 4 + μ⁻¹ + S + L by positivity)
    (freezingScale_four_le_double hμ hS hL) 145
  apply hcomp.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  refine hNorm.trans ((mul_le_mul_of_nonneg_left hPow hM).trans_eq ?_)
  rw [mul_pow, mul_assoc]

private theorem appendixCompression_solve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (proj B : E →L[ℝ] E) (hP : ∀ f, proj (proj f) = proj f)
    (e : freezingFixedSpace proj ≃L[ℝ] freezingFixedSpace proj)
    (he : (e : freezingFixedSpace proj →L[ℝ] freezingFixedSpace proj) = freezingCompression proj B hP)
    (f : freezingFixedSpace proj) :
    proj (B (e.symm f).val) = f.val ∧
      ∀ u : freezingFixedSpace proj, proj (B u.val) = f.val → u = e.symm f := by
  have heval (v : freezingFixedSpace proj) : (e v).val = proj (B v.val) :=
    congrArg Subtype.val (DFunLike.congr_fun he v)
  have hsolve : proj (B (e.symm f).val) = f.val := by rw [← heval, e.apply_symm_apply]
  exact ⟨hsolve, fun u hu => e.injective (Subtype.ext ((heval u).trans (hu.trans (hsolve.symm.trans (heval _).symm))))⟩

/-- The spatial clause of Lemma A.2, with a fixed polynomial in the
coercivity, sup-norm and Lipschitz constants. -/
theorem paperLemmaA2_spatial :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : HalfHolder A (Vec3 →L[ℝ] Vec3)) {μ L : ℝ},
      0 < μ → 0 ≤ L →
      (∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ L * dist a b) →
      (∀ a w, μ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a B w, w⟫_ℝ) →
      ∃ e : freezingFixedSpace P ≃L[ℝ] freezingFixedSpace P,
        (e : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) =
          freezingCompression P B.coefficientMul endpointStrongSpatialLeray_idempotent ∧
        ∀ v : freezingFixedSpace P, ‖v‖ ≤
          C * (2 + μ⁻¹ + ‖B.val.1‖ + L) ^ (145 : ℕ) * ‖e v‖ := by
  obtain ⟨C, hC, hInv⟩ := exists_endpointSpatialLerayInverse
  refine ⟨C * 2 ^ (145 : ℕ), by positivity, ?_⟩
  intro B μ L hμ hL hLip hCoercive
  obtain ⟨e, he, hNorm⟩ := hInv B hμ hL hLip hCoercive
  exact ⟨e, he, appendixInversePointwise e hμ hC (norm_nonneg _) hL hNorm⟩

set_option maxHeartbeats 12000000 in
/-- The time-path clause of Lemma A.2, restricted to time-mean-zero fields
by the same mixed projection as Appendix A. -/
theorem paperLemmaA2_mixed :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : HalfHolder A (Paths →L[ℝ] Paths)) {μ L : ℝ},
      0 < μ → 0 ≤ L →
      (∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ L * dist a b) →
      (∀ a w, endpointIntegral 1 w = 0 → μ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a B w, w⟫_ℝ) →
      ∃ e : freezingFixedSpace Q ≃L[ℝ] freezingFixedSpace Q,
        (e : freezingFixedSpace Q →L[ℝ] freezingFixedSpace Q) =
          freezingCompression Q B.coefficientMul (endpointStrongMixedLeray_idempotent zero_lt_one) ∧
        ∀ v : freezingFixedSpace Q, ‖v‖ ≤
          C * (2 + μ⁻¹ + ‖B.val.1‖ + L) ^ (145 : ℕ) * ‖e v‖ := by
  obtain ⟨C, hC, hInv⟩ := exists_endpointMixedLerayInverse (T := 1) zero_lt_one
  refine ⟨C * 2 ^ (145 : ℕ), by positivity, ?_⟩
  intro B μ L hμ hL hLip hCoercive
  obtain ⟨e, he, hNorm⟩ := hInv B hμ hL hLip hCoercive
  exact ⟨e, he, appendixInversePointwise e hμ hC (norm_nonneg _) hL hNorm⟩

/-- The data of a finite family of actual spatial Hölder derivative
words, as in the higher-order assertion of Lemma A.2. -/
def HasSpatialHolderWords {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : HalfHolder A E) : Prop :=
  ∃ w : List (Fin 3) → HalfHolder A E, w [] = f ∧
    ∀ (i : Fin 3) (t : List (Fin 3)), t.length < n →
      endpointTorusHasSpatialDerivative (coordinateDirection i) (w t) (w (i :: t))

/-- The spatial Hölder inverse preserves every finite number of
coordinate derivative words. -/
theorem paperLemmaA2_spatial_higher {μ L : ℝ} (hμ : 0 < μ) (hL : 0 ≤ L)
    (B : HalfHolder A (Vec3 →L[ℝ] Vec3))
    (hLip : ∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ L * dist a b)
    (hCoercive : ∀ a w, μ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a B w, w⟫_ℝ)
    (n : ℕ) (hB : HasSpatialHolderWords n B) (f : freezingFixedSpace P)
    (hf : HasSpatialHolderWords n f.val) :
    ∃! v : freezingFixedSpace P, P (B.coefficientMul v.val) = f.val ∧ HasSpatialHolderWords n v.val := by
  obtain ⟨_, _, hInv⟩ := exists_endpointSpatialLerayInverse
  obtain ⟨e, he, _⟩ := hInv B hμ hL hLip hCoercive
  let v := e.symm f
  have hV : P v.val = v.val := (mem_freezingFixedSpace _ _).mp v.property
  obtain ⟨heq, hSame⟩ := appendixCompression_solve P B.coefficientMul endpointStrongSpatialLeray_idempotent e he f
  obtain ⟨Bjet, hB₀, hBjet⟩ := hB
  obtain ⟨Fjet, hF₀, hFjet⟩ := hf
  have hc (z : freezingFixedSpace P) a :
      μ * ‖HalfHolder.eval a z.val‖ ^ 2 ≤
        ⟪HalfHolder.eval a (Bjet []) (HalfHolder.eval a z.val), HalfHolder.eval a z.val⟫_ℝ :=
    hB₀.symm ▸ hCoercive a _
  obtain ⟨w, hw, _, _, hd, _⟩ := endpointStrongSpatialLeray_allSpatialDerivatives Bjet Fjet v.val
    coordinateDirection hV (by rw [hB₀, hF₀]; exact heq) e (by rwa [hB₀]) hμ hc n hBjet hFjet
  exact ⟨v, ⟨heq, w, hw, hd⟩, fun u hu => hSame u hu.1⟩

set_option maxHeartbeats 12000000 in
/-- The mixed Hölder inverse preserves every finite number of coordinate
derivative words, with the quotient equation on the same fixed space. -/
theorem paperLemmaA2_mixed_higher {μ L : ℝ} (hμ : 0 < μ) (hL : 0 ≤ L)
    (B : HalfHolder A (Paths →L[ℝ] Paths))
    (hLip : ∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ L * dist a b)
    (hCoercive : ∀ a w, endpointIntegral 1 w = 0 → μ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a B w, w⟫_ℝ)
    (n : ℕ) (hB : HasSpatialHolderWords n B) (f : freezingFixedSpace Q)
    (hf : HasSpatialHolderWords n f.val) :
    ∃! v : freezingFixedSpace Q, Q (B.coefficientMul v.val) = f.val ∧ HasSpatialHolderWords n v.val := by
  obtain ⟨_, _, hInv⟩ := exists_endpointMixedLerayInverse (T := 1) zero_lt_one
  obtain ⟨e, he, _⟩ := hInv B hμ hL hLip hCoercive
  let v := e.symm f
  have hV : Q v.val = v.val := (mem_freezingFixedSpace _ _).mp v.property
  obtain ⟨heq, hSame⟩ := appendixCompression_solve Q B.coefficientMul (endpointStrongMixedLeray_idempotent zero_lt_one) e he f
  obtain ⟨Bjet, hB₀, hBjet⟩ := hB
  obtain ⟨Fjet, hF₀, hFjet⟩ := hf
  have hc (z : freezingFixedSpace Q) a :
      μ * ‖HalfHolder.eval a z.val‖ ^ 2 ≤
        ⟪HalfHolder.eval a (Bjet []) (HalfHolder.eval a z.val), HalfHolder.eval a z.val⟫_ℝ := by
    rw [hB₀]
    have hz := (mem_freezingFixedSpace _ _).mp z.property
    apply hCoercive a
    rw [← hz]
    exact endpointStrongMixedLeray_timeIntegral_eq_zero zero_lt_one z.val a
  obtain ⟨w, hw, _, _, hd, _⟩ := endpointStrongMixedLeray_allSpatialDerivatives (T := 1)
    zero_lt_one Bjet Fjet v.val coordinateDirection hV (by rw [hB₀, hF₀]; exact heq)
    e (by rwa [hB₀]) hμ hc n hBjet hFjet
  exact ⟨v, ⟨heq, w, hw, hd⟩, fun u hu => hSame u hu.1⟩

end

end TorusEuler
