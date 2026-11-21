import TorusEuler.Paper.Proofs.S5a.Library.Budget

/-!
# S5a library: the relay coefficient budget of Lemma 5.5

`relayBudget` builds the `WaveRelayCoefficientBudget` consumed by the relay estimates of
Lemma 5.5 from bounds `Θ` on the weighted mixed derivatives of the four basic coefficients
`(D_aX)⁻¹`, `M`, `κ/λ`, `λ²/|κ|²` (which Proposition 5.1 (5.8) provides) and `‖ℓ_*⁻¹‖ ≤ Θ`.
Every product is estimated with the product rule (D.4) of Lemma D.1 (`MonoW.bilinear`),
as in the proof of Lemma 5.5 (`sections/06c_finite_hierarchy.tex:416-446`).
-/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5a

noncomputable section

open HierarchyTwistedProfile

/-- The norms of the fixed linear maps are at most `relayNorms`. -/
theorem relayNorms_bounds :
    ‖appL Vec3 (Vec3 →L[ℝ] Vec3)‖ ≤ relayNorms ∧
    ‖appL (Vec3 →L[ℝ] Vec3) (Vec3 →L[ℝ] Vec3)‖ ≤ relayNorms ∧
    ‖appL Vec3 Vec3‖ ≤ relayNorms ∧ ‖ContinuousLinearMap.compL ℝ Vec3 Vec3 Vec3‖ ≤ relayNorms ∧
    ‖ContinuousLinearMap.lsmul ℝ ℝ (E := Vec3 →L[ℝ] Vec3)‖ ≤ relayNorms ∧
    ‖innerL‖ ≤ relayNorms ∧ ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ relayNorms ∧
    ‖appL Vec3 (Vec3 →L[ℝ] ℝ)‖ ≤ relayNorms ∧
    ‖ContinuousLinearMap.lsmul ℝ ℝ (E := Vec3 →L[ℝ] ℝ)‖ ≤ relayNorms ∧
    ‖appL Vec3 (ℝ →L[ℝ] Vec3)‖ ≤ relayNorms ∧
    ‖crossL‖ ≤ relayNorms ∧ ‖adjL‖ ≤ relayNorms ∧ ‖toSpanL‖ ≤ relayNorms ∧
    (2 : ℝ) ≤ relayNorms := by
  unfold relayNorms
  have := norm_nonneg (appL Vec3 (Vec3 →L[ℝ] Vec3))
  have := norm_nonneg (appL (Vec3 →L[ℝ] Vec3) (Vec3 →L[ℝ] Vec3))
  have := norm_nonneg (appL Vec3 Vec3)
  have := norm_nonneg (ContinuousLinearMap.compL ℝ Vec3 Vec3 Vec3)
  have := norm_nonneg (ContinuousLinearMap.lsmul ℝ ℝ (E := Vec3 →L[ℝ] Vec3))
  have := norm_nonneg innerL
  have := norm_nonneg (ContinuousLinearMap.mul ℝ ℝ)
  have := norm_nonneg (appL Vec3 (Vec3 →L[ℝ] ℝ))
  have := norm_nonneg (ContinuousLinearMap.lsmul ℝ ℝ (E := Vec3 →L[ℝ] ℝ))
  have := norm_nonneg (appL Vec3 (ℝ →L[ℝ] Vec3))
  have := norm_nonneg crossL
  have := norm_nonneg adjL
  have := norm_nonneg toSpanL
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- A weighted bound of the product type gives the monotone-weight bound. -/
theorem MonoW.of_wb {T E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ℓ h Ω Θ : ℝ} {m : ℕ}
    {f : T → Vec3 × ℝ → E} (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hb : HierarchyRelayWordBound ℓ h m Θ f) : MonoW ℓ h m Ω Θ 0 1 f :=
  ⟨hf, by simpa using hb⟩

set_option maxHeartbeats 4000000 in
/-- **The coefficient budget of the relay** (`sections/06c_finite_hierarchy.tex:416-446`):
from word bounds `Θ` at order `n+1` for `(D_aX)⁻¹ = G`, `M`, `κ/λ = κn` and
`λ²/|κ|² = ν = |κn|^{-2}`, and `‖ℓ_*⁻¹‖ ≤ Θ`, every coefficient of the relay has word bound
`ω^{10} Θ^6`, `ω = relayOmega (n+1)`. Products use (D.4) of `hD` (`MonoW.bilinear`). -/
theorem relayBudget (hD : Statement.lemma_D_1) {S : Type} {ℓ h Θ : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h)
    (hΘ : 1 ≤ Θ) (n : ℕ)
    {G M : S → Vec3 → Vec3 →L[ℝ] Vec3} {κn : S → Vec3 → Vec3} {ν : S → Vec3 → ℝ}
    (hG : MonoW ℓ h (n + 1) (relayOmega (n + 1)) Θ 0 1 (fun t x => G t x.1))
    (hM : MonoW ℓ h (n + 1) (relayOmega (n + 1)) Θ 0 1 (fun t x => M t x.1))
    (hκ : MonoW ℓ h (n + 1) (relayOmega (n + 1)) Θ 0 1 (fun t x => κn t x.1))
    (hν : MonoW ℓ h (n + 1) (relayOmega (n + 1)) Θ 0 1 (fun t x => ν t x.1))
    (hνeq : ∀ t a, ν t a = (‖κn t a‖ ^ 2)⁻¹) (hℓΘ : ‖ℓ⁻¹‖ ≤ Θ) :
    WaveRelayCoefficientBudget ℓ h n (relayOmega (n + 1) ^ 10 * Θ ^ 6) G M κn := by
  have hΩ2 : 2 ≤ relayOmega (n + 1) := two_le_relayOmega (n + 1)
  have hΩ1 : 1 ≤ relayOmega (n + 1) := one_le_two.trans hΩ2
  have hN (x : ℝ) (hx : x ≤ relayNorms) : x ≤ relayOmega (n + 1) :=
    hx.trans (relayOmega_ge (n + 1))
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14⟩ := relayNorms_bounds
  have hP {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
      [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (B : E →L[ℝ] F →L[ℝ] G)
      (hB : ‖B‖ ≤ relayNorms) := product_le_relayOmega (n + 1) B hB
  have h2 : ‖(2 : ℝ)‖ ≤ relayOmega (n + 1) := by simpa using hN 2 b14
  have hm2 : ‖(-2 : ℝ)‖ ≤ relayOmega (n + 1) := by simpa using hN 2 b14
  have hm1 : ‖(-1 : ℝ)‖ ≤ relayOmega (n + 1) := by simpa using hΩ1
  -- the constant fields
  have cX := MonoW.const (T := S) (ℓ := ℓ) (h := h) (m := n + 1) (Θ := Θ) crossL (hN _ b11)
  have cA := MonoW.const (T := S) (ℓ := ℓ) (h := h) (m := n + 1) (Θ := Θ) adjL (hN _ b12)
  have cI := MonoW.const (T := S) (ℓ := ℓ) (h := h) (m := n + 1) (Θ := Θ) innerL
    (hN _ b6)
  have cS := MonoW.const (T := S) (ℓ := ℓ) (h := h) (m := n + 1) (Θ := Θ) toSpanL (hN _ b13)
  have ce (i : Fin 3) := MonoW.const (T := S) (ℓ := ℓ) (h := h) (m := n + 1) (Θ := Θ)
    (coordinateDirection i) (by simpa [coordinateDirection] using hΩ1)
  -- products, each estimated by (D.4)
  have mXk := MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b1) cX hκ
  have mMT := MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b2) cA hM
  have mMTk := MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b3) mMT hκ
  have mXMTk := MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b1) cX mMTk
  have mXkM := MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b4) mXk hM
  have mMk := MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b3) hM hκ
  have mIn := MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b6) hκ mMk
  have mνν := MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b7) hν hν
  have mPr := MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b7) mIn mνν
  have mIk := MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b8) cI hκ
  have mIMTk := MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b8) cI mMTk
  have mGT := MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b2) cA hG
  have mGTe (i : Fin 3) := MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b3) mGT (ce i)
  have mXGTe (i : Fin 3) := MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b1) cX (mGTe i)
  have mGM := MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b4) hG hM
  have mGMT := MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b2) cA mGM
  have mGMTe (i : Fin 3) := MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b3) mGMT (ce i)
  have mXGMTe (i : Fin 3) := MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b1) cX (mGMTe i)
  -- the seven coefficients
  have mPot := MonoW.bilinear hD hℓ hh hΩ1 hΘ (ContinuousLinearMap.lsmul ℝ ℝ) (hP _ b5)
    (hν.smul hΩ1 hΘ (-1) hm1) mXk
  have mT1 := MonoW.bilinear hD hℓ hh hΩ1 hΘ (ContinuousLinearMap.lsmul ℝ ℝ) (hP _ b5) hν
    ((mXMTk.raise hΩ1 hΘ (a' := 5) (i' := 2) (by norm_num) (by norm_num)).add hΩ2 hΘ
      (mXkM.raise hΩ1 hΘ (a' := 5) (i' := 2) (by norm_num) (by norm_num)))
  have mT2 := MonoW.bilinear hD hℓ hh hΩ1 hΘ (ContinuousLinearMap.lsmul ℝ ℝ) (hP _ b5)
    (mPr.smul hΩ1 hΘ 2 h2) mXk
  have mTime := (mT1.raise hΩ1 hΘ (a' := 8) (i' := 6) (by norm_num) (by norm_num)).sub hΩ2 hΘ
    (mT2.raise hΩ1 hΘ (a' := 8) (i' := 6) (by norm_num) (by norm_num))
  have mPA := MonoW.bilinear hD hℓ hh hΩ1 hΘ (ContinuousLinearMap.lsmul ℝ ℝ) (hP _ b9)
    (hν.smul hΩ1 hΘ (-2) hm2) mIMTk
  have mPS := MonoW.bilinear hD hℓ hh hΩ1 hΘ (ContinuousLinearMap.lsmul ℝ ℝ) (hP _ b9) hν mIk
  have mCurl (i : Fin 3) := (mXGTe i).smulΘ hΩ1 ℓ⁻¹ hℓΘ
  have mMat (i : Fin 3) :=
    ((MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b4) hM (mCurl i)).raise hΩ1 hΘ (a' := 7) (i' := 3)
      (by norm_num) (by norm_num)).sub hΩ2 hΘ
    (((mXGMTe i).smulΘ hΩ1 ℓ⁻¹ hℓΘ).raise hΩ1 hΘ (a' := 7) (i' := 3) (by norm_num) (by norm_num))
  have mGrad (i : Fin 3) := ((MonoW.bilinear hD hℓ hh hΩ1 hΘ _ (hP _ b10) cS (mGTe i)).smulΘ
    hΩ1 ℓ⁻¹ hℓΘ)
  -- conclude: identify each field and raise to `ω^10 Θ^6`
  have fin {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {a i : ℕ} {c : S → Vec3 → E}
      (hc : MonoW ℓ h (n + 1) (relayOmega (n + 1)) Θ a i (fun t x => c t x.1))
      (ha : a ≤ 10) (hi : i ≤ 6) :
      HierarchyRelayCoefficientJets ℓ h (n + 1) (relayOmega (n + 1) ^ 10 * Θ ^ 6) c :=
    let hc' := hc.raise hΩ1 hΘ ha hi
    ⟨hc'.1, hc'.2⟩
  have finRow {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {a i : ℕ} {c : S → Vec3 → E}
      (hc : MonoW ℓ h (n + 1) (relayOmega (n + 1)) Θ a i (fun t x => c t x.1))
      (ha : a ≤ 10) (hi : i ≤ 6) :
      HierarchyRelayCoefficientJets ℓ h n (relayOmega (n + 1) ^ 10 * Θ ^ 6) c :=
    let hc' := hc.raise hΩ1 hΘ ha hi
    ⟨hc'.1, relayWordBound_mono hc'.2 (Nat.le_succ n) le_rfl⟩
  refine ⟨fin (mPot.congr fun t x => ?_) (by norm_num) (by norm_num),
    fin (mTime.congr fun t x => ?_) (by norm_num) (by norm_num),
    fin (mPA.congr fun t x => ?_) (by norm_num) (by norm_num),
    fin (mPS.congr fun t x => ?_) (by norm_num) (by norm_num),
    fun i => finRow ((mCurl i).congr fun t x => ?_) (by norm_num) (by norm_num),
    fun i => finRow ((mMat i).congr fun t x => ?_) (by norm_num) (by norm_num),
    fun i => finRow ((mGrad i).congr fun t x => ?_) (by norm_num) (by norm_num)⟩
  · simp [hierarchyRelayPotentialCoefficient, hνeq]
    exact (neg_smul _ _).symm
  · simp only [hierarchyRelayTimeAmplitudeCoefficient, hνeq, ContinuousLinearMap.lsmul_apply,
      ContinuousLinearMap.id_apply, crossL_apply, adjL_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.mul_apply', innerL_apply, smul_eq_mul]
    have e : ∀ (b a : ℝ), (2 : ℝ) * (b * (a⁻¹ * a⁻¹)) = 2 * b / a ^ 2 := fun b a => by ring
    rw [e]
  · simp only [hierarchyRelayPressureAmplitudeCoefficient, hνeq, ContinuousLinearMap.lsmul_apply,
      ContinuousLinearMap.id_apply, adjL_apply, smul_eq_mul]
    congr 1
    ext v
    simp [ContinuousLinearMap.adjoint_inner_left]
  · simp only [hierarchyRelayPressureSourceCoefficient, hνeq, ContinuousLinearMap.lsmul_apply,
      ContinuousLinearMap.id_apply]
    congr 1
  · simp [hierarchyRelayCurlRow]
  · simp [hierarchyRelayMaterialRow, hierarchyRelayCurlRow]
  · simp [hierarchyRelayPressureRow]

end

end TorusEuler.Paper.Lib.S5a
