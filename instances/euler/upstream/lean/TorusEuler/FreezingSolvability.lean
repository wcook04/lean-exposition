import TorusEuler.FreezingContinuation
import TorusEuler.FreezingLocalization
import TorusEuler.EndpointCoefficientCompatibility

/-! The compressed half-Hölder solve of Lemma A.2 from frozen multiplier bounds. -/

open BoundedContinuousFunction ContinuousLinearMap MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace TorusEuler

section Compression

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fixed space of a bounded operator is closed in the ambient space. -/
def freezingFixedSpace (P : E →L[ℝ] E) : Submodule ℝ E := (P - 1).ker

@[simp] theorem mem_freezingFixedSpace (P : E →L[ℝ] E) (v : E) :
    v ∈ freezingFixedSpace P ↔ P v = v := by
  change (P - 1) v = 0 ↔ _
  simp only [_root_.sub_apply, one_apply_eq_self, sub_eq_zero]

theorem isClosed_freezingFixedSpace (P : E →L[ℝ] E) :
    IsClosed (freezingFixedSpace P : Set E) := (P - 1).isClosed_ker

instance [CompleteSpace E] (P : E →L[ℝ] E) : CompleteSpace (freezingFixedSpace P) :=
  (isClosed_freezingFixedSpace P).isComplete.completeSpace_coe

/-- Apply the coefficient and project back to the fixed space. -/
def freezingCompression (P A : E →L[ℝ] E) (hP : ∀ v, P (P v) = P v) :
    freezingFixedSpace P →L[ℝ] freezingFixedSpace P :=
  (P.comp A).restrict (fun v _ => (mem_freezingFixedSpace P _).mpr (hP (A v)))

@[simp] theorem freezingCompression_val (P A : E →L[ℝ] E) (hP : ∀ v, P (P v) = P v)
    (v : freezingFixedSpace P) : (freezingCompression P A hP v).val = P (A v.val) := rfl

theorem freezingCompressionLine_val (P A : E →L[ℝ] E) (hP : ∀ v, P (P v) = P v)
    (s : ℝ) (v : freezingFixedSpace P) :
    (freezingContinuationLine (freezingCompression P A hP) s v).val =
      P (freezingContinuationLine A s v.val) := by
  rw [freezingContinuationLine_project P A s ((mem_freezingFixedSpace P _).mp v.property)]
  rfl

end Compression

section Haar

local notation "Labels" => UnitAddTorus (Fin 3)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local notation "W" => HalfHolder Labels H
local notation "W₂" => Lp H 2 unitTorusMeasure
local notation "M" => HalfHolder Labels (H →L[ℝ] H)

/-- The spatial Haar embedding for either of the Hilbert coefficient spaces of Lemma A.2. -/
noncomputable def freezingHaarEmbedding : W →L[ℝ] W₂ :=
  (BoundedContinuousFunction.toLp 2 unitTorusMeasure ℝ).comp <|
    (ContinuousLinearMap.fst ℝ (Labels →ᵇ H) (DistinctPairs Labels →ᵇ H)).comp
      (halfHolderSubspace Labels H).toSubmodule.subtypeL

theorem freezingHaarEmbedding_apply_ae (v : W) :
    (freezingHaarEmbedding v : Labels → H) =ᵐ[unitTorusMeasure] fun a => HalfHolder.eval a v :=
  BoundedContinuousFunction.coeFn_toLp 2 unitTorusMeasure ℝ v.val.1

theorem freezingHaarEmbedding_injective :
    Function.Injective (freezingHaarEmbedding (H := H)) := by
  intro v w h
  change (BoundedContinuousFunction.toLp 2 unitTorusMeasure ℝ) v.val.1 =
    (BoundedContinuousFunction.toLp 2 unitTorusMeasure ℝ) w.val.1 at h
  have h' : v.val.1 = w.val.1 := BoundedContinuousFunction.toLp_injective unitTorusMeasure h
  exact HalfHolder.ext fun a => congrArg (fun f : Labels →ᵇ H => f a) h'

theorem norm_freezingHaarEmbedding_apply_le (v : W) :
    ‖freezingHaarEmbedding v‖ ≤ ‖v‖ := by
  let L : (Labels →ᵇ H) →L[ℝ] W₂ := BoundedContinuousFunction.toLp 2 unitTorusMeasure ℝ
  have hL : ‖L‖ ≤ 1 := by
    have h := BoundedContinuousFunction.toLp_norm_le (p := 2) (𝕜 := ℝ) (E := H) unitTorusMeasure
    rw [measureUnivNNReal, measure_univ, ENNReal.toNNReal_one, NNReal.coe_one, Real.one_rpow] at h
    exact h
  change ‖L v.val.1‖ ≤ ‖v‖
  calc
    _ ≤ 1 * ‖v.val.1‖ := L.le_of_opNorm_le hL _
    _ ≤ _ := by
      change 1 * ‖v.val.1‖ ≤ ‖v.val‖
      simpa only [one_mul] using norm_fst_le v.val

theorem freezingHaarEmbedding_inner (v w : W) :
    ⟪freezingHaarEmbedding v, freezingHaarEmbedding w⟫_ℝ =
      ∫ a, ⟪HalfHolder.eval a v, HalfHolder.eval a w⟫_ℝ ∂unitTorusMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [freezingHaarEmbedding_apply_ae v, freezingHaarEmbedding_apply_ae w] with a hv hw
  rw [hv, hw]

theorem norm_freezingHaarEmbedding_eq (v : W) :
    ‖freezingHaarEmbedding v‖ = Real.sqrt (∫ a, ‖HalfHolder.eval a v‖ ^ 2 ∂unitTorusMeasure) := by
  rw [← Real.sqrt_sq (norm_nonneg (freezingHaarEmbedding v)),
    ← real_inner_self_eq_norm_sq, freezingHaarEmbedding_inner]
  simp only [real_inner_self_eq_norm_sq]

/-- The identity coefficient for the affine deformation in Lemma A.2. -/
noncomputable def freezingIdentityCoefficient : M :=
  HalfHolder.ofBound (ContinuousMap.const Labels (1 : H →L[ℝ] H))
    (fun _ => (norm_id_le (𝕜 := ℝ) (E := H)))
    (fun _ _ => by
      change ‖(1 : H →L[ℝ] H) - 1‖ ≤ 1 * Real.sqrt _
      simpa only [sub_self, norm_zero, one_mul] using Real.sqrt_nonneg _)

@[simp] theorem freezingIdentityCoefficient_eval (a : Labels) :
    HalfHolder.eval a (freezingIdentityCoefficient (H := H)) = 1 := rfl

noncomputable def freezingCoefficientLine (B : M) (s : ℝ) : M :=
  (1 - s) • freezingIdentityCoefficient + s • B

@[simp] theorem freezingCoefficientLine_eval (B : M) (s : ℝ) (a : Labels) :
    HalfHolder.eval a (freezingCoefficientLine B s) =
      (1 - s) • (1 : H →L[ℝ] H) + s • HalfHolder.eval a B := by
  simp only [freezingCoefficientLine, map_add, map_smul,
    freezingIdentityCoefficient_eval]

theorem freezingCoefficientLine_mul (B : M) (s : ℝ) (v : W) :
    (freezingCoefficientLine B s).coefficientMul v =
      freezingContinuationLine B.coefficientMul s v := by
  apply HalfHolder.ext
  intro a
  simp only [HalfHolder.eval_coefficientMul, freezingCoefficientLine_eval, _root_.add_apply,
    _root_.smul_apply, one_apply_eq_self, freezingContinuationLine, map_add, map_smul]

theorem freezingCoefficientLine_lipschitz (B : M) {L s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hB : ∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ L * dist a b) (a b : Labels) :
    ‖HalfHolder.eval a (freezingCoefficientLine B s) -
      HalfHolder.eval b (freezingCoefficientLine B s)‖ ≤ L * dist a b := by
  simp only [freezingCoefficientLine_eval]
  rw [show ∀ x y : H →L[ℝ] H,
      (1 - s) • (1 : H →L[ℝ] H) + s • x - ((1 - s) • (1 : H →L[ℝ] H) + s • y) =
        s • (x - y) by intros; rw [smul_sub]; abel]
  rw [norm_smul, Real.norm_of_nonneg hs.1]
  exact (mul_le_of_le_one_left (norm_nonneg _) hs.2).trans (hB a b)

theorem freezingCoefficientLine_sup_le (B : M) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖(freezingCoefficientLine B s).val.1‖ ≤ 1 + ‖B.val.1‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro a
  change ‖HalfHolder.eval a (freezingCoefficientLine B s)‖ ≤ _
  simp only [freezingCoefficientLine_eval]
  have h1s : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
  calc
    _ ≤ ‖(1 - s) • (1 : H →L[ℝ] H)‖ + ‖s • HalfHolder.eval a B‖ := norm_add_le _ _
    _ ≤ (1 - s) * 1 + s * ‖B.val.1‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg h1s, Real.norm_of_nonneg hs.1]
      exact add_le_add (mul_le_mul_of_nonneg_left (norm_id_le (𝕜 := ℝ) (E := H)) h1s)
        (mul_le_mul_of_nonneg_left (B.val.1.norm_coe_le_norm a) hs.1)
    _ ≤ 1 + ‖B.val.1‖ := by nlinarith only [hs.1, mul_le_of_le_one_left (norm_nonneg B.val.1) hs.2]

/-- A spatial $L^2$ orthogonal projection gives the projected pairing for
half-Hölder fields when the two projections agree under the Haar embedding. -/
theorem freezingHaarEmbedding_projected_pairing (P : W →L[ℝ] W) (Q : W₂ →L[ℝ] W₂)
    (hcompatible : ∀ w, freezingHaarEmbedding (P w) = Q (freezingHaarEmbedding w))
    (hself : ∀ w u, ⟪Q w, u⟫_ℝ = ⟪w, Q u⟫_ℝ)
    (w : W) (v : freezingFixedSpace P) :
    ⟪freezingHaarEmbedding (P w), freezingHaarEmbedding v.val⟫_ℝ =
      ⟪freezingHaarEmbedding w, freezingHaarEmbedding v.val⟫_ℝ := by
  rw [hcompatible, hself, ← hcompatible, (mem_freezingFixedSpace P _).mp v.property]

/-- Compatibility with the weak orthogonal projection gives idempotence
of the half-Hölder projection by injectivity of the Haar embedding. -/
theorem freezingProjection_idempotent_of_compatible
    (P : W →L[ℝ] W) (Q : W₂ →L[ℝ] W₂) (hQ : ∀ w, Q (Q w) = Q w)
    (hcompatible : ∀ w, freezingHaarEmbedding (P w) = Q (freezingHaarEmbedding w)) (v : W) :
    P (P v) = P v := by
  apply freezingHaarEmbedding_injective
  simp only [hcompatible, hQ]

/-- A compatible bounded projection fixes exactly the half-Hölder fields
whose Haar representatives belong to the weak projected subspace. -/
theorem mem_freezingFixedSpace_iff_weak
    (P : W →L[ℝ] W) (Q : W₂ →L[ℝ] W₂) {V : Submodule ℝ W₂}
    (hQ : ∀ w, Q w = w ↔ w ∈ V)
    (hcompatible : ∀ w, freezingHaarEmbedding (P w) = Q (freezingHaarEmbedding w)) (v : W) :
    v ∈ freezingFixedSpace P ↔ freezingHaarEmbedding v ∈ V := by
  rw [mem_freezingFixedSpace, ← hQ, ← hcompatible]
  exact freezingHaarEmbedding_injective.eq_iff.symm

/-- Pointwise coercivity on the projected unknown supplies the same $L^2$
coefficient for every member of the affine deformation. -/
theorem freezingHaarEmbedding_line_coercive (B : M) (v : W) {μ s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hB : ∀ a, μ * ‖HalfHolder.eval a v‖ ^ 2 ≤
      ⟪HalfHolder.eval a B (HalfHolder.eval a v), HalfHolder.eval a v⟫_ℝ) :
    (min 1 μ) * ‖freezingHaarEmbedding v‖ ^ 2 ≤
      ⟪freezingHaarEmbedding ((freezingCoefficientLine B s).coefficientMul v),
        freezingHaarEmbedding v⟫_ℝ := by
  let w := (freezingCoefficientLine B s).coefficientMul v
  have hleft : Integrable (fun a : Labels => (min 1 μ) * ‖HalfHolder.eval a v‖ ^ 2)
      unitTorusMeasure := by
    rw [← integrableOn_univ]
    exact ((v.val.1.continuous.norm.pow 2).const_mul _).continuousOn.integrableOn_compact isCompact_univ
  have hright : Integrable (fun a : Labels => ⟪HalfHolder.eval a w, HalfHolder.eval a v⟫_ℝ)
      unitTorusMeasure := by
    rw [← integrableOn_univ]
    exact (w.val.1.continuous.inner v.val.1.continuous).continuousOn.integrableOn_compact isCompact_univ
  change _ ≤ ⟪freezingHaarEmbedding w, freezingHaarEmbedding v⟫_ℝ
  rw [← real_inner_self_eq_norm_sq, freezingHaarEmbedding_inner, freezingHaarEmbedding_inner]
  simp only [real_inner_self_eq_norm_sq]
  rw [← integral_const_mul]
  apply integral_mono hleft hright
  intro a
  let u := HalfHolder.eval a v
  change min 1 μ * ‖u‖ ^ 2 ≤ ⟪HalfHolder.eval a w, u⟫_ℝ
  calc
    _ = (1 - s) * (min 1 μ * ‖u‖ ^ 2) + s * (min 1 μ * ‖u‖ ^ 2) := by ring
    _ ≤ (1 - s) * ‖u‖ ^ 2 + s * ⟪HalfHolder.eval a B u, u⟫_ℝ :=
      add_le_add (mul_le_mul_of_nonneg_left
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_left 1 μ) (sq_nonneg ‖u‖))
        (sub_nonneg.mpr hs.2))
      (mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_right (min_le_right 1 μ) (sq_nonneg ‖u‖)).trans (hB a)) hs.1)
    _ = _ := by
      simp only [w, u, HalfHolder.eval_coefficientMul, freezingCoefficientLine_eval,
        _root_.add_apply, _root_.smul_apply, one_apply_eq_self, inner_add_left,
        real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- Testing the compressed affine operator against its unknown gives the
uniform spatial $L^2$ bound needed in the localization estimate. -/
theorem freezingHaarEmbedding_compressed_line_bound
    (P : W →L[ℝ] W) (hP : ∀ v, P (P v) = P v) (B : M)
    (hpair : ∀ w (v : freezingFixedSpace P),
      ⟪freezingHaarEmbedding (P w), freezingHaarEmbedding v.val⟫_ℝ =
        ⟪freezingHaarEmbedding w, freezingHaarEmbedding v.val⟫_ℝ)
    (v : freezingFixedSpace P) {μ s : ℝ} (hμ : 0 < μ) (hs : s ∈ Icc (0 : ℝ) 1)
    (hB : ∀ a, μ * ‖HalfHolder.eval a v.val‖ ^ 2 ≤
      ⟪HalfHolder.eval a B (HalfHolder.eval a v.val), HalfHolder.eval a v.val⟫_ℝ) :
    let f := (freezingContinuationLine (freezingCompression P B.coefficientMul hP) s v).val
    ‖freezingHaarEmbedding v.val‖ ≤ (min 1 μ)⁻¹ * ‖f‖ := by
  let f := (freezingContinuationLine (freezingCompression P B.coefficientMul hP) s v).val
  let U := freezingHaarEmbedding v.val
  have hν : 0 < min 1 μ := lt_min zero_lt_one hμ
  have hF : f = P ((freezingCoefficientLine B s).coefficientMul v.val) := by
    rw [freezingCoefficientLine_mul]
    exact freezingCompressionLine_val P B.coefficientMul hP s v
  have htest : min 1 μ * ‖U‖ ^ 2 ≤ ⟪freezingHaarEmbedding f, U⟫_ℝ := by
    rw [hF, hpair]
    exact freezingHaarEmbedding_line_coercive B v.val hs hB
  change ‖U‖ ≤ (min 1 μ)⁻¹ * ‖f‖
  by_cases hzero : ‖U‖ = 0
  · rw [hzero]
    exact mul_nonneg (inv_nonneg.mpr hν.le) (norm_nonneg _)
  have hpos : 0 < ‖U‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
  have h := htest.trans ((real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_freezingHaarEmbedding_apply_le f) (norm_nonneg U)))
  rw [pow_two, ← mul_assoc] at h
  have hh := le_of_mul_le_mul_right h hpos
  rw [mul_comm (min 1 μ) ‖U‖] at hh
  simpa only [div_eq_mul_inv, mul_comm] using (le_div_iff₀ hν).mpr hh

variable [CompleteSpace H]

/-- Lemma A.2 on the projected half-Hölder space, given the frozen multiplier
bounds and identities uniformly along the affine deformation. Coercivity is
required only on values of projected fields, so the same result applies
when the projection includes a zero-time-mean constraint. -/
theorem exists_freezingCompressionEquiv
    (P : W →L[ℝ] W) (hP : ∀ v, P (P v) = P v) (B : M)
    (F G : ℝ → Labels → W →L[ℝ] W) {r C D L μ : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D) (hL : 0 ≤ L) (hμ : 0 < μ)
    (hBlip : ∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ L * dist a b)
    (hsmall : 8 * C * L * Real.sqrt r ≤ 1 / 2)
    (hpair : ∀ w (v : freezingFixedSpace P),
      ⟪freezingHaarEmbedding (P w), freezingHaarEmbedding v.val⟫_ℝ =
        ⟪freezingHaarEmbedding w, freezingHaarEmbedding v.val⟫_ℝ)
    (hcoercive : ∀ (v : freezingFixedSpace P) a, μ * ‖HalfHolder.eval a v.val‖ ^ 2 ≤
      ⟪HalfHolder.eval a B (HalfHolder.eval a v.val), HalfHolder.eval a v.val⟫_ℝ)
    (hF : ∀ s ∈ Icc (0 : ℝ) 1, ∀ a, ‖F s a‖ ≤ C)
    (hG : ∀ s ∈ Icc (0 : ℝ) 1, ∀ a, ‖G s a‖ ≤ C)
    (hfreeze : ∀ s ∈ Icc (0 : ℝ) 1, ∀ (v : freezingFixedSpace P) a w,
      (∀ x, HalfHolder.eval x w =
        (HalfHolder.eval a (freezingCoefficientLine B s) -
          HalfHolder.eval x (freezingCoefficientLine B s)) (HalfHolder.eval x v.val)) →
      v.val = F s a (P ((freezingCoefficientLine B s).coefficientMul v.val)) + G s a w)
    (hoff : ∀ s ∈ Icc (0 : ℝ) 1, ∀ a w,
      (∀ x, dist x a ≤ r → HalfHolder.eval x w = 0) →
      ∀ b, dist a b ≤ r / 4 →
        ‖HalfHolder.eval a (G s a w) - HalfHolder.eval b (G s a w)‖ ≤
          D * ‖w.val.1‖ * dist a b) :
    let K := freezingLowerOrder r (2 * D * (1 + ‖B.val.1‖))
    ∃ e : freezingFixedSpace P ≃L[ℝ] freezingFixedSpace P,
      (e : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) = freezingCompression P B.coefficientMul hP ∧
      ‖(e.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P)‖ ≤
        4 * (C + K * (4 * K) ^ 3 * (min 1 μ)⁻¹) := by
  let K := freezingLowerOrder r (2 * D * (1 + ‖B.val.1‖))
  have hK : 1 ≤ K := one_le_freezingLowerOrder _ _
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hν : 0 < min 1 μ := lt_min zero_lt_one hμ
  refine exists_freezingContinuationEquiv (freezingCompression P B.coefficientMul hP) ?_ ?_
  · positivity
  · intro s hs v
    let Bₛ := freezingCoefficientLine B s
    let f := (freezingContinuationLine (freezingCompression P B.coefficientMul hP) s v).val
    change ‖v.val‖ ≤ 4 * (C + K * (4 * K) ^ 3 * (min 1 μ)⁻¹) * ‖f‖
    have hf : f = P (Bₛ.coefficientMul v.val) := by
      dsimp only [Bₛ]
      rw [freezingCoefficientLine_mul]
      exact freezingCompressionLine_val P B.coefficientMul hP s v
    have hloc := halfHolder_norm_le_of_frozen_operator Bₛ f v.val (F s) (G s)
      hr hr₁ hC hD hL (freezingCoefficientLine_lipschitz B hs hBlip)
      (hF s hs) (hG s hs) hsmall (fun a w hw => by rw [hf]; exact hfreeze s hs v a w hw)
      (hoff s hs)
    have hKₛ : freezingLowerOrder r (2 * D * ‖Bₛ.val.1‖) ≤ K := by
      unfold freezingLowerOrder K
      exact max_le_max le_rfl (max_le_max
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (freezingCoefficientLine_sup_le B hs) (by positivity))
          (Real.sqrt_nonneg _)) le_rfl)
    have hprior : ‖v.val‖ ≤ 2 * (C * ‖f‖ + K * ‖v.val.val.1‖) :=
      hloc.trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hKₛ (norm_nonneg _))) (by norm_num))
    have hco := freezingHaarEmbedding_compressed_line_bound P hP B hpair v hμ hs (hcoercive v)
    rw [norm_freezingHaarEmbedding_eq] at hco
    exact freezing_torus_absorb_supremum f v.val hK hprior hco

omit [CompleteSpace H] in
/-- If the weak projector and coefficient intertwine with the Haar
embedding, so do the compressed operators. This is the fixed-time
compatibility used to identify the Hölder inverse with the weak solution. -/
theorem freezingCompression_intertwines
    (P : W →L[ℝ] W) (Q : W₂ →L[ℝ] W₂)
    (hP : ∀ v, P (P v) = P v) (hQ : ∀ v, Q (Q v) = Q v)
    (B : M) (B₂ : W₂ →L[ℝ] W₂)
    (hproj : ∀ w, freezingHaarEmbedding (P w) = Q (freezingHaarEmbedding w))
    (hcoeff : ∀ w, freezingHaarEmbedding (B.coefficientMul w) = B₂ (freezingHaarEmbedding w)) :
    ∃ J : freezingFixedSpace P →L[ℝ] freezingFixedSpace Q,
      (∀ w, (J w).val = freezingHaarEmbedding w.val) ∧
      Function.Injective J ∧
      ∀ w, J (freezingCompression P B.coefficientMul hP w) =
        freezingCompression Q B₂ hQ (J w) := by
  let J : freezingFixedSpace P →L[ℝ] freezingFixedSpace Q :=
    freezingHaarEmbedding.restrict (fun w hw => by
      rw [mem_freezingFixedSpace] at hw ⊢
      rw [← hproj, hw])
  refine ⟨J, fun _ => rfl, ?_, ?_⟩
  · intro x y hxy
    exact Subtype.ext (freezingHaarEmbedding_injective (congrArg Subtype.val hxy))
  · intro w
    apply Subtype.ext
    change freezingHaarEmbedding (P (B.coefficientMul w.val)) =
      Q (B₂ (freezingHaarEmbedding w.val))
    rw [hproj, hcoeff]

omit [CompleteSpace H] in
/-- The projected coefficient depends Lipschitz-continuously on the coefficient
field in the spatial half-Hölder norm. -/
theorem freezingCompression_lipschitz (P : W →L[ℝ] W) (hP : ∀ v, P (P v) = P v) :
    LipschitzWith ⟨2 * ‖P‖, by positivity⟩
      (fun B : M => freezingCompression P B.coefficientMul hP) := by
  apply LipschitzWith.of_dist_le_mul
  intro B C
  rw [dist_eq_norm, dist_eq_norm]
  change ‖freezingCompression P B.coefficientMul hP - freezingCompression P C.coefficientMul hP‖ ≤
    (2 * ‖P‖) * ‖B - C‖
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖P (B.coefficientMul v.val) - P (C.coefficientMul v.val)‖ ≤
    (2 * ‖P‖) * ‖B - C‖ * ‖v.val‖
  have hdiff : (B - C).coefficientMul v.val = B.coefficientMul v.val - C.coefficientMul v.val :=
    congrArg (fun S : W →L[ℝ] W => S v.val) (HalfHolder.coefficientMul_sub B C)
  rw [← map_sub, ← hdiff]
  calc
    _ ≤ ‖P‖ * ‖(B - C).coefficientMul v.val‖ := P.le_opNorm _
    _ ≤ ‖P‖ * ((2 * ‖B - C‖) * ‖v.val‖) :=
      mul_le_mul_of_nonneg_left
        ((B - C).coefficientMul.le_of_opNorm_le (HalfHolder.norm_coefficientMul_le (B - C)) _)
        (norm_nonneg P)
    _ = _ := by ring

/-- Time-continuous coefficients give operator-norm continuous fixed-time
inverses on a common projected half-Hölder space. -/
theorem continuousOn_freezingCompression_inverse
    (P : W →L[ℝ] W) (hP : ∀ v, P (P v) = P v) {I : Set ℝ}
    {B : ℝ → M} (hB : ContinuousOn B I)
    {e : ℝ → freezingFixedSpace P ≃L[ℝ] freezingFixedSpace P}
    (he : ∀ t ∈ I, (e t : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) =
      freezingCompression P (B t).coefficientMul hP) :
    ContinuousOn (fun t => ((e t).symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P)) I := by
  apply continuousOn_endpointFixedInverse
  exact ((freezingCompression_lipschitz P hP).continuous.comp_continuousOn hB).congr he

end Haar

end TorusEuler
