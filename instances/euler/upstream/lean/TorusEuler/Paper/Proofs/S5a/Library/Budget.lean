import TorusEuler.Paper.Proofs.S5a.Library.Relay

/-!
# S5a library: the coefficient budget of the relay from (5.8) and the product rule (D.4)

The relay estimates of Lemma 5.5 (`Lib.S5a.boundedWeightSeminorm_complete_le_of_D1`,
`Lib.S5a.boundedWeightSeminorm_waveRelay_le_of_eval_of_D1`) consume a
`WaveRelayCoefficientBudget`: uniform bounds on the weighted mixed derivatives of the
coefficients of `Q[V]`, `∂_t Q[V]` and `∂_s 𝗉` (built from `κ/λ`, `λ²/|κ|²`, `M`) and of the
inverse-radius rows of the curl and gradient (built from `(D_aX)⁻¹`, `M`, `ℓ_*⁻¹`).

Following the proof of Lemma 5.5 (`sections/06c_finite_hierarchy.tex:416-422`: "`Q[V]` is
`λ⁻¹` times the phase primitive of `V`, multiplied by the coefficients `κ/λ` and `λ²/|κ|²` …
(D.4) … and (5.8) give (5.31)"), each of these coefficients is a product of the basic
coefficients `(D_aX)⁻¹`, `M`, `κ/λ`, `λ²/|κ|²` (bounded by (5.8)) with fixed linear maps
and the power `ℓ_*⁻¹` of `𝖣`; every product is estimated with the product rule (D.4) of
Lemma D.1 (`wb_bilinear_of_D1`, applied to phase-independent fields with `γ ≡ 1`).

Bounds are kept in the form `c Θ^i` with a common `Θ ≥ 1` that dominates the four basic
coefficients and `ℓ_*⁻¹`; the budget constant is `budgetConstant m * Θ^6`.
-/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5a

noncomputable section

open HierarchyTwistedProfile

/-! ## Fixed linear maps -/

/-- The cross product `κ ↦ κ × ·` as a continuous linear map of `κ`. -/
def crossL : Vec3 →L[ℝ] (Vec3 →L[ℝ] Vec3) :=
  LinearMap.toContinuousLinearMap
    { toFun := cross3Left
      map_add' := fun a b => by
        ext v i
        fin_cases i <;> simp [cross3Left_apply, cross3, crossProduct]
      map_smul' := fun c a => by
        ext v i
        fin_cases i <;> simp [cross3Left_apply, cross3, crossProduct] }

@[simp] theorem crossL_apply (κ : Vec3) : crossL κ = cross3Left κ := rfl

/-- The adjoint `A ↦ Aᵀ` as a continuous linear map. -/
def adjL : (Vec3 →L[ℝ] Vec3) →L[ℝ] (Vec3 →L[ℝ] Vec3) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A.adjoint
      map_add' := fun A B => map_add _ A B
      map_smul' := fun c A => by
        simp [ContinuousLinearMap.adjoint.map_smulₛₗ] }

@[simp] theorem adjL_apply (A : Vec3 →L[ℝ] Vec3) : adjL A = A.adjoint := rfl

/-- `v ↦ (r ↦ r v)`, the map `toSpanSingleton` as a continuous linear map of `v`. -/
def toSpanL : Vec3 →L[ℝ] (ℝ →L[ℝ] Vec3) := (ContinuousLinearMap.lsmul ℝ ℝ).flip

@[simp] theorem toSpanL_apply (v : Vec3) : toSpanL v = toSpanSingleton ℝ v := by
  ext
  simp [toSpanL]

/-- The inner product `(u, v) ↦ ⟪u, v⟫` as a bilinear map (the map `innerSL ℝ`). -/
def innerL : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ := innerSL ℝ

@[simp] theorem innerL_apply (u v : Vec3) : innerL u v = ⟪u, v⟫_ℝ := rfl

/-- The application `(A, v) ↦ A v` of a field of linear maps to a field. -/
abbrev appL (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] : (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F := ContinuousLinearMap.id ℝ (E →L[ℝ] F)

/-! ## Word bounds of products, from (D.4) -/

section Products

variable {T : Type} {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The constant of the product rule on word bounds: the factor of (D.4) times the
two conversions between word bounds and the norm (D.1) (`#words` each). -/
def productConstant (m : ℕ) : ℝ :=
  ((hierarchyAdmissibleWords (Fin 4) m).card * (2 : ℝ) ^ m * 2) *
    (hierarchyAdmissibleWords (Fin 4) m).card * (hierarchyAdmissibleWords (Fin 4) m).card

/-- The product constant of order `m` is nonnegative. -/
theorem productConstant_nonneg (m : ℕ) : 0 ≤ productConstant m := by
  unfold productConstant
  positivity

/-- **The product rule (D.4) of Lemma D.1 on word bounds**: if every weighted mixed
derivative of order at most `m` of `f` is at most `A` and of `g` at most `C`, those of
`B(f, g)` are at most `productConstant m · ‖B‖ A C`. The norm of the product and its
finiteness are the (D.4) clause of `hD` (weight `γ ≡ 1`). -/
theorem wb_bilinear_of_D1 (hD : Statement.lemma_D_1) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h)
    {m : ℕ} (B : E →L[ℝ] F →L[ℝ] G) {f : T → Vec3 × ℝ → E} {g : T → Vec3 × ℝ → F} {A C : ℝ}
    (hf : ∀ t, ContDiff ℝ ∞ (f t)) (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hfA : HierarchyRelayWordBound ℓ h m A f) (hgC : HierarchyRelayWordBound ℓ h m C g) :
    HierarchyRelayWordBound ℓ h m (productConstant m * ‖B‖ * A * C)
      (fun t x => B (f t x) (g t x)) := by
  have hfF : AppendixD.FieldNormFinite ℓ h m f := ⟨hf, relayWordBound_bdd hfA⟩
  have hgF : AppendixD.FieldNormFinite ℓ h m (AppendixD.weighted (fun _ => (1 : ℝ)) g) := by
    rw [weighted_one]
    exact ⟨hg, relayWordBound_bdd hgC⟩
  obtain ⟨hfin, hle⟩ :=
    (hD T ℓ h hℓ hh (fun _ => 1) (fun _ => one_pos) m).2.1 E F G B f g hfF hgF
  rw [weighted_one] at hfin
  unfold AppendixD.weightedFieldNorm at hle
  rw [weighted_one, weighted_one] at hle
  have h1 : AppendixD.fieldNorm ℓ h m f ≤ (hierarchyAdmissibleWords (Fin 4) m).card * A :=
    hfA.finiteNorm_le
  have h2 : AppendixD.fieldNorm ℓ h m g ≤ (hierarchyAdmissibleWords (Fin 4) m).card * C :=
    hgC.finiteNorm_le
  have hf0 : 0 ≤ AppendixD.fieldNorm ℓ h m f :=
    Finset.sum_nonneg fun w hw => le_csSup (hfF.2 w hw) (Or.inl rfl)
  have hg0 : 0 ≤ AppendixD.fieldNorm ℓ h m g :=
    Finset.sum_nonneg fun w hw => le_csSup (relayWordBound_bdd hgC w hw) (Or.inl rfl)
  have hA := hfA.1
  have hC := hgC.1
  refine relayWordBound_mono (hierarchyRelayWordBound_of_finiteNorm hfin.2) le_rfl ?_
  calc
    _ ≤ ((hierarchyAdmissibleWords (Fin 4) m).card * (2 : ℝ) ^ m * (2 * ‖B‖)) *
          AppendixD.fieldNorm ℓ h m f * AppendixD.fieldNorm ℓ h m g := hle
    _ ≤ ((hierarchyAdmissibleWords (Fin 4) m).card * (2 : ℝ) ^ m * (2 * ‖B‖)) *
          ((hierarchyAdmissibleWords (Fin 4) m).card * A) *
          ((hierarchyAdmissibleWords (Fin 4) m).card * C) := by
      gcongr
    _ = productConstant m * ‖B‖ * A * C := by unfold productConstant; ring

/-- A word bound is unchanged by a pointwise equal field. -/
theorem wb_congr {ℓ h : ℝ} {m : ℕ} {A : ℝ} {f g : T → Vec3 × ℝ → E}
    (hfg : ∀ t x, f t x = g t x) (hf : HierarchyRelayWordBound ℓ h m A f) :
    HierarchyRelayWordBound ℓ h m A g := by
  have : f = g := funext fun t => funext fun x => hfg t x
  rwa [← this]

/-- A constant field has the word bound `‖v‖`. -/
theorem wb_const (ℓ h : ℝ) (m : ℕ) (v : E) :
    HierarchyRelayWordBound ℓ h m (‖v‖) (fun (_ : T) (_ : Vec3 × ℝ) => v) := by
  have hconst : ∀ w : List (Fin 4), ∃ c : E,
      phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun _ : Vec3 × ℝ => v) = fun _ => c := by
    intro w
    induction w with
    | nil => exact ⟨v, rfl⟩
    | cons i w ih =>
      obtain ⟨c, hc⟩ := ih
      exact ⟨0, by funext x; simp [phaseOperatorWord, phaseDirectionalDerivative, hc]⟩
  refine ⟨norm_nonneg _, fun w _ t x => ?_⟩
  cases w with
  | nil => exact le_rfl
  | cons i w =>
    obtain ⟨c, hc⟩ := hconst w
    simp [phaseOperatorWord, phaseDirectionalDerivative, hc]

end Products


/-! ## Bounds of the form `Ω^a Θ^i` -/

section Monomials

variable {T : Type} {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Smooth fields whose weighted mixed derivatives of order at most `m` are bounded by
`Ω^a Θ^i`: `Ω ≥ 1` absorbs the fixed constants (products, linear maps, numbers) and
`Θ ≥ 1` the powers of `𝖣` (basic coefficients and `ℓ_*⁻¹`). -/
def MonoW (ℓ h : ℝ) (m : ℕ) (Ω Θ : ℝ) (a i : ℕ) (f : T → Vec3 × ℝ → E) : Prop :=
  (∀ t, ContDiff ℝ ∞ (f t)) ∧ HierarchyRelayWordBound ℓ h m (Ω ^ a * Θ ^ i) f

variable {ℓ h Ω Θ : ℝ} {m : ℕ}

/-- Pointwise equal families satisfy the same monotone-weight bound. -/
theorem MonoW.congr {a i : ℕ} {f g : T → Vec3 × ℝ → E} (hfg : ∀ t x, f t x = g t x)
    (hf : MonoW ℓ h m Ω Θ a i f) : MonoW ℓ h m Ω Θ a i g := by
  have : f = g := funext fun t => funext fun x => hfg t x
  rwa [← this]

/-- The monotone-weight bound persists when the parameters are raised. -/
theorem MonoW.raise (hΩ : 1 ≤ Ω) (hΘ : 1 ≤ Θ) {a i a' i' : ℕ} {f : T → Vec3 × ℝ → E}
    (hf : MonoW ℓ h m Ω Θ a i f) (ha : a ≤ a') (hi : i ≤ i') : MonoW ℓ h m Ω Θ a' i' f :=
  ⟨hf.1, relayWordBound_mono hf.2 le_rfl
    (mul_le_mul (pow_le_pow_right₀ hΩ ha) (pow_le_pow_right₀ hΘ hi)
      (pow_nonneg (zero_le_one.trans hΘ) _) (pow_nonneg (zero_le_one.trans hΩ) _))⟩

/-- A constant of norm at most `Ω` satisfies the monotone-weight bound. -/
theorem MonoW.const (v : E) (hv : ‖v‖ ≤ Ω) :
    MonoW ℓ h m Ω Θ 1 0 (fun (_ : T) (_ : Vec3 × ℝ) => v) :=
  ⟨fun _ => contDiff_const, relayWordBound_mono (wb_const ℓ h m v) le_rfl (by simpa using hv)⟩

/-- Bilinear products satisfy the monotone-weight bound (product estimate (D.4)). -/
theorem MonoW.bilinear (hD : Statement.lemma_D_1) (hℓ : 0 < ℓ) (hh : 0 < h)
    (hΩ : 1 ≤ Ω) (hΘ : 1 ≤ Θ) (B : E →L[ℝ] F →L[ℝ] G) (hB : productConstant m * ‖B‖ ≤ Ω)
    {a b i j : ℕ} {f : T → Vec3 × ℝ → E} {g : T → Vec3 × ℝ → F}
    (hf : MonoW ℓ h m Ω Θ a i f) (hg : MonoW ℓ h m Ω Θ b j g) :
    MonoW ℓ h m Ω Θ (a + b + 1) (i + j) (fun t x => B (f t x) (g t x)) := by
  refine ⟨fun t => (B.contDiff.comp (hf.1 t)).clm_apply (hg.1 t), ?_⟩
  have h := wb_bilinear_of_D1 hD hℓ hh B hf.1 hg.1 hf.2 hg.2
  refine relayWordBound_mono h le_rfl ?_
  have hΩ₀ : 0 ≤ Ω := zero_le_one.trans hΩ
  have hΘ₀ : 0 ≤ Θ := zero_le_one.trans hΘ
  calc productConstant m * ‖B‖ * (Ω ^ a * Θ ^ i) * (Ω ^ b * Θ ^ j)
      ≤ Ω * (Ω ^ a * Θ ^ i) * (Ω ^ b * Θ ^ j) := by gcongr
    _ = Ω ^ (a + b + 1) * Θ ^ (i + j) := by ring

/-- Sums satisfy the monotone-weight bound. -/
theorem MonoW.add (hΩ : 2 ≤ Ω) (hΘ : 1 ≤ Θ) {a i : ℕ} {f g : T → Vec3 × ℝ → E}
    (hf : MonoW ℓ h m Ω Θ a i f) (hg : MonoW ℓ h m Ω Θ a i g) :
    MonoW ℓ h m Ω Θ (a + 1) i (fun t x => f t x + g t x) := by
  refine ⟨fun t => (hf.1 t).add (hg.1 t), ?_⟩
  have h := relayWordBound_add hf.1 hg.1 hf.2 hg.2
  refine relayWordBound_mono h le_rfl ?_
  have hΩ₀ : 0 ≤ Ω := zero_le_two.trans hΩ
  have hp : 0 ≤ Ω ^ a * Θ ^ i := mul_nonneg (pow_nonneg hΩ₀ _) (pow_nonneg (zero_le_one.trans hΘ) _)
  calc Ω ^ a * Θ ^ i + Ω ^ a * Θ ^ i = 2 * (Ω ^ a * Θ ^ i) := by ring
    _ ≤ Ω * (Ω ^ a * Θ ^ i) := mul_le_mul_of_nonneg_right hΩ hp
    _ = Ω ^ (a + 1) * Θ ^ i := by ring

/-- Scalar multiples satisfy the monotone-weight bound. -/
theorem MonoW.smul (hΩ : 1 ≤ Ω) (hΘ : 1 ≤ Θ) {a i : ℕ} {f : T → Vec3 × ℝ → E}
    (hf : MonoW ℓ h m Ω Θ a i f) (r : ℝ) (hr : ‖r‖ ≤ Ω) :
    MonoW ℓ h m Ω Θ (a + 1) i (fun t x => r • f t x) := by
  refine ⟨fun t => (hf.1 t).const_smul r, ?_⟩
  have h := relayWordBound_const_smul hf.1 hf.2 r
  refine relayWordBound_mono h le_rfl ?_
  have hp : 0 ≤ Ω ^ a * Θ ^ i :=
    mul_nonneg (pow_nonneg (zero_le_one.trans hΩ) _) (pow_nonneg (zero_le_one.trans hΘ) _)
  calc ‖r‖ * (Ω ^ a * Θ ^ i) ≤ Ω * (Ω ^ a * Θ ^ i) := mul_le_mul_of_nonneg_right hr hp
    _ = Ω ^ (a + 1) * Θ ^ i := by ring

/-- Differences satisfy the monotone-weight bound. -/
theorem MonoW.sub (hΩ : 2 ≤ Ω) (hΘ : 1 ≤ Θ) {a i : ℕ} {f g : T → Vec3 × ℝ → E}
    (hf : MonoW ℓ h m Ω Θ a i f) (hg : MonoW ℓ h m Ω Θ a i g) :
    MonoW ℓ h m Ω Θ (a + 1 + 1) i (fun t x => f t x - g t x) := by
  have hΩ₁ : 1 ≤ Ω := one_le_two.trans hΩ
  have h := (hf.raise hΩ₁ hΘ (Nat.le_succ a) le_rfl).add hΩ hΘ
    ((hg.smul hΩ₁ hΘ (-1) (by simpa using hΩ₁)))
  exact h.congr fun t x => by simp [sub_eq_add_neg]

/-- Multiplying by a scalar of size at most `Θ` (such as `ℓ_*⁻¹`) raises the power of `Θ`. -/
theorem MonoW.smulΘ (hΩ : 1 ≤ Ω) {a i : ℕ} {f : T → Vec3 × ℝ → E} (hf : MonoW ℓ h m Ω Θ a i f)
    (r : ℝ) (hr : ‖r‖ ≤ Θ) : MonoW ℓ h m Ω Θ a (i + 1) (fun t x => r • f t x) := by
  refine ⟨fun t => (hf.1 t).const_smul r, ?_⟩
  have h := relayWordBound_const_smul hf.1 hf.2 r
  refine relayWordBound_mono h le_rfl ?_
  have hΘ : 0 ≤ Θ := (norm_nonneg r).trans hr
  have hp : 0 ≤ Ω ^ a * Θ ^ i := mul_nonneg (pow_nonneg (zero_le_one.trans hΩ) _) (pow_nonneg hΘ _)
  calc ‖r‖ * (Ω ^ a * Θ ^ i) ≤ Θ * (Ω ^ a * Θ ^ i) := mul_le_mul_of_nonneg_right hr hp
    _ = Ω ^ a * Θ ^ (i + 1) := by ring

end Monomials

/-! ## The coefficient budget -/

/-- A bound for the norms of the fixed linear maps used to build the relay coefficients,
and for the numbers `2`, `1`. -/
def relayNorms : ℝ :=
  3 + ‖appL Vec3 (Vec3 →L[ℝ] Vec3)‖ + ‖appL (Vec3 →L[ℝ] Vec3) (Vec3 →L[ℝ] Vec3)‖ +
    ‖appL Vec3 Vec3‖ + ‖ContinuousLinearMap.compL ℝ Vec3 Vec3 Vec3‖ +
    ‖ContinuousLinearMap.lsmul ℝ ℝ (E := Vec3 →L[ℝ] Vec3)‖ + ‖innerL‖ +
    ‖ContinuousLinearMap.mul ℝ ℝ‖ + ‖appL Vec3 (Vec3 →L[ℝ] ℝ)‖ +
    ‖ContinuousLinearMap.lsmul ℝ ℝ (E := Vec3 →L[ℝ] ℝ)‖ + ‖appL Vec3 (ℝ →L[ℝ] Vec3)‖ +
    ‖crossL‖ + ‖adjL‖ + ‖toSpanL‖

/-- The constant `Ω` of order `m`: `(productConstant m + 1)(relayNorms + 1)`. -/
def relayOmega (m : ℕ) : ℝ := (productConstant m + 1) * (relayNorms + 1)

/-- The relay norm count is at least `3`. -/
theorem relayNorms_ge : 3 ≤ relayNorms := by
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
  linarith

/-- The relay constant of order `m` dominates the relay norm count. -/
theorem relayOmega_ge (m : ℕ) : relayNorms ≤ relayOmega m := by
  unfold relayOmega
  have h0 := productConstant_nonneg m
  have h3 := relayNorms_ge
  nlinarith

/-- The relay constant of order `m` is at least `2`. -/
theorem two_le_relayOmega (m : ℕ) : 2 ≤ relayOmega m :=
  (by linarith [relayNorms_ge] : (2 : ℝ) ≤ relayNorms).trans (relayOmega_ge m)

/-- `productConstant m · ‖B‖ ≤ Ω` when `‖B‖ ≤ relayNorms`. -/
theorem product_le_relayOmega {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (m : ℕ) (B : E →L[ℝ] F →L[ℝ] G) (hB : ‖B‖ ≤ relayNorms) :
    productConstant m * ‖B‖ ≤ relayOmega m := by
  unfold relayOmega
  have h0 := productConstant_nonneg m
  have h1 := norm_nonneg B
  nlinarith

end

end TorusEuler.Paper.Lib.S5a
