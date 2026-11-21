import TorusEuler.AngularLeraySymbol
import TorusEuler.EndpointComplexification
import TorusEuler.HalfHolderMultiplierUniform
import TorusEuler.MultiplierOffSupport

/-! The complex Fourier symbols for the real frozen inverses of Appendix A. -/

open ContinuousLinearMap Set MeasureTheory UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler

universe u v

noncomputable section

section FrozenSymbols

variable {H Hc : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Hc] [NormedSpace ℂ Hc]

/-- The complexification of the real frozen inverse symbol. -/
def complexFrozenInverseSymbol (X : EndpointComplexification H Hc)
    (P : Vec3 → H →L[ℝ] H) (B : H →L[ℝ] H) (ξ : Vec3) : Hc →L[ℂ] Hc :=
  X.extendOperator (Ring.inverse (frozenSymbol (P ξ) B))

/-- The symbol for the correction source in the frozen identity. -/
def complexFrozenProjectedInverseSymbol (X : EndpointComplexification H Hc)
    (P : Vec3 → H →L[ℝ] H) (B : H →L[ℝ] H) (ξ : Vec3) : Hc →L[ℂ] Hc :=
  X.extendOperator (Ring.inverse (frozenSymbol (P ξ) B) * P ξ)

omit [CompleteSpace H] in
theorem complexFrozenProjectedInverseSymbol_eq (X : EndpointComplexification H Hc)
    (P : Vec3 → H →L[ℝ] H) (B : H →L[ℝ] H) (ξ : Vec3) :
    complexFrozenProjectedInverseSymbol X P B ξ =
      complexFrozenInverseSymbol X P B ξ * X.extendOperator (P ξ) :=
  X.extendOperator_mul _ _

theorem norm_complexFrozenInverseSymbol_le (X : EndpointComplexification H Hc)
    {P : Vec3 → H →L[ℝ] H} {B : H →L[ℝ] H} {ξ : Vec3} {μ : ℝ}
    (hP : (P ξ : H →ₗ[ℝ] H).IsSymmetricProjection) (hμ : 0 < μ)
    (hB : ∀ v, P ξ v = v → μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ) :
    ‖complexFrozenInverseSymbol X P B ξ‖ ≤ (min 1 μ)⁻¹ := by
  rw [complexFrozenInverseSymbol, X.norm_extendOperator]
  exact norm_frozenSymbol_inverse_le hP hμ hB

theorem norm_complexFrozenProjectedInverseSymbol_le (X : EndpointComplexification H Hc)
    {P : Vec3 → H →L[ℝ] H} {B : H →L[ℝ] H} {ξ : Vec3} {μ : ℝ}
    (hP : (P ξ : H →ₗ[ℝ] H).IsSymmetricProjection) (hPnorm : ‖P ξ‖ ≤ 1)
    (hμ : 0 < μ) (hB : ∀ v, P ξ v = v → μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ) :
    ‖complexFrozenProjectedInverseSymbol X P B ξ‖ ≤ (min 1 μ)⁻¹ := by
  rw [complexFrozenProjectedInverseSymbol_eq]
  refine (norm_mul_le _ _).trans ?_
  rw [X.norm_extendOperator]
  exact (mul_le_of_le_one_right (norm_nonneg _) hPnorm).trans
    (norm_complexFrozenInverseSymbol_le X hP hμ hB)

omit [CompleteSpace H] in
theorem complexFrozenInverseSymbol_pos_smul (X : EndpointComplexification H Hc)
    {P : Vec3 → H →L[ℝ] H} (B : H →L[ℝ] H) {c : ℝ} {ξ : Vec3}
    (hP : P (c • ξ) = P ξ) :
    complexFrozenInverseSymbol X P B (c • ξ) = complexFrozenInverseSymbol X P B ξ := by
  simp only [complexFrozenInverseSymbol, hP]

omit [CompleteSpace H] in
theorem complexFrozenProjectedInverseSymbol_pos_smul (X : EndpointComplexification H Hc)
    {P : Vec3 → H →L[ℝ] H} (B : H →L[ℝ] H) {c : ℝ} {ξ : Vec3}
    (hP : P (c • ξ) = P ξ) :
    complexFrozenProjectedInverseSymbol X P B (c • ξ) =
      complexFrozenProjectedInverseSymbol X P B ξ := by
  simp only [complexFrozenProjectedInverseSymbol, hP]

private theorem contDiffOn_realFrozenInverseSymbol {P : Vec3 → H →L[ℝ] H}
    {B : H →L[ℝ] H} {s : Set Vec3} (hP : ContDiffOn ℝ ∞ P s)
    (hUnit : ∀ ξ ∈ s, IsUnit (frozenSymbol (P ξ) B)) :
    ContDiffOn ℝ ∞ (fun ξ => Ring.inverse (frozenSymbol (P ξ) B)) s := by
  have hDirect : ContDiffOn ℝ ∞ (fun ξ => frozenSymbol (P ξ) B) s :=
    ((hP.mul contDiffOn_const).mul hP).add (contDiffOn_const.sub hP)
  have hInv : ContDiffOn ℝ ∞ (Ring.inverse : (H →L[ℝ] H) → H →L[ℝ] H) {a | IsUnit a} := by
    intro a ha
    obtain ⟨b, rfl⟩ := ha
    exact (contDiffAt_ringInverse ℝ b).contDiffWithinAt
  exact hInv.comp hDirect hUnit

theorem contDiffOn_complexFrozenInverseSymbol (X : EndpointComplexification H Hc)
    {P : Vec3 → H →L[ℝ] H} {B : H →L[ℝ] H} {s : Set Vec3}
    (hP : ContDiffOn ℝ ∞ P s) (hUnit : ∀ ξ ∈ s, IsUnit (frozenSymbol (P ξ) B)) :
    ContDiffOn ℝ ∞ (complexFrozenInverseSymbol X P B) s :=
  X.extendOperatorCLM.contDiff.comp_contDiffOn (contDiffOn_realFrozenInverseSymbol hP hUnit)

theorem contDiffOn_complexFrozenProjectedInverseSymbol (X : EndpointComplexification H Hc)
    {P : Vec3 → H →L[ℝ] H} {B : H →L[ℝ] H} {s : Set Vec3}
    (hP : ContDiffOn ℝ ∞ P s) (hUnit : ∀ ξ ∈ s, IsUnit (frozenSymbol (P ξ) B)) :
    ContDiffOn ℝ ∞ (complexFrozenProjectedInverseSymbol X P B) s :=
  X.extendOperatorCLM.contDiff.comp_contDiffOn ((contDiffOn_realFrozenInverseSymbol hP hUnit).mul hP)

theorem norm_iteratedFDeriv_complexFrozenInverseSymbol_le (X : EndpointComplexification H Hc)
    {P : Vec3 → H →L[ℝ] H} {B : H →L[ℝ] H} {s : Set Vec3} (hs : IsOpen s)
    (hP : ContDiffOn ℝ ∞ P s) {μ : ℝ} (hμ : 0 < μ)
    (hProj : ∀ ξ ∈ s, (P ξ : H →ₗ[ℝ] H).IsSymmetricProjection)
    (hB : ∀ ξ ∈ s, ∀ v, P ξ v = v → μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ)
    {x : Vec3} (hx : x ∈ s) {n : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (hDeriv : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i P x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (complexFrozenInverseSymbol X P B) x‖ ≤
      (n.factorial : ℝ) ^ 2 * ((min 1 μ)⁻¹) ^ (n + 1) * (2 * D * (‖B‖ + 1)) ^ n := by
  have hUnit (ξ : Vec3) (hξ : ξ ∈ s) : IsUnit (frozenSymbol (P ξ) B) :=
    frozenSymbol_isUnit (hProj ξ hξ) hμ (hB ξ hξ)
  have hOp : ‖X.extendOperatorCLM‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro A
    rw [X.extendOperatorCLM_apply, X.norm_extendOperator, one_mul]
  have hAt : ContDiffAt ℝ n (fun ξ => Ring.inverse (frozenSymbol (P ξ) B)) x :=
    ((contDiffOn_realFrozenInverseSymbol hP hUnit).contDiffAt (hs.mem_nhds hx)).of_le (by simp)
  have hComplex := X.extendOperatorCLM.norm_iteratedFDeriv_comp_left hAt le_rfl
  exact (hComplex.trans (mul_le_of_le_one_left (norm_nonneg _) hOp)).trans
    (norm_iteratedFDeriv_frozenSymbol_inverse_of_projection_bounds hs hμ hProj hB hx
      (hP.of_le (by simp)) hD hDeriv)

/-- Leibniz gives the derivative bound for the frozen inverse followed by
the projection. The last two inputs bound all derivatives up to order (n). -/
theorem norm_iteratedFDeriv_complexFrozenProjectedInverseSymbol_le (X : EndpointComplexification H Hc)
    {P : Vec3 → H →L[ℝ] H} {B : H →L[ℝ] H} {s : Set Vec3} (hs : IsOpen s)
    (hP : ContDiffOn ℝ ∞ P s) (hUnit : ∀ ξ ∈ s, IsUnit (frozenSymbol (P ξ) B))
    {x : Vec3} (hx : x ∈ s) {n : ℕ} {C D : ℝ} (hC : 0 ≤ C)
    (hInv : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i (complexFrozenInverseSymbol X P B) x‖ ≤ C)
    (hProj : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i P x‖ ≤ D) :
    ‖iteratedFDeriv ℝ n (complexFrozenProjectedInverseSymbol X P B) x‖ ≤ (2 : ℝ) ^ n * C * D := by
  let F := complexFrozenInverseSymbol X P B
  let G := X.extendOperatorCLM ∘ P
  have hF : ContDiffOn ℝ ∞ F s := contDiffOn_complexFrozenInverseSymbol X hP hUnit
  have hG : ContDiffOn ℝ ∞ G s := X.extendOperatorCLM.contDiff.comp_contDiffOn hP
  have hprod : ContDiffOn ℝ ∞ (fun y => F y * G y) s := hF.mul hG
  have hOp : ‖X.extendOperatorCLM‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro A
    rw [X.extendOperatorCLM_apply, X.norm_extendOperator, one_mul]
  have eqWithin {f : Vec3 → Hc →L[ℂ] Hc} (hf : ContDiffOn ℝ ∞ f s) (i : ℕ) :
      iteratedFDerivWithin ℝ i f s x = iteratedFDeriv ℝ i f x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn
      ((hf.contDiffAt (hs.mem_nhds hx)).of_le (by simp)) hx
  have hf (i : ℕ) (hi : i ≤ n) : ‖iteratedFDerivWithin ℝ i F s x‖ ≤ C := by
    rw [eqWithin hF]
    exact hInv i hi
  have hg (i : ℕ) (hi : i ≤ n) : ‖iteratedFDerivWithin ℝ i G s x‖ ≤ D := by
    rw [eqWithin hG]
    have hAt : ContDiffAt ℝ i P x := (hP.contDiffAt (hs.mem_nhds hx)).of_le (by simp)
    have h := X.extendOperatorCLM.norm_iteratedFDeriv_comp_left hAt le_rfl
    exact h.trans ((mul_le_of_le_one_left (norm_nonneg _) hOp).trans (hProj i hi))
  have heq : complexFrozenProjectedInverseSymbol X P B = fun y => F y * G y :=
    funext (complexFrozenProjectedInverseSymbol_eq X P B)
  rw [heq, ← eqWithin hprod]
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i F s x‖ *
        ‖iteratedFDerivWithin ℝ (n - i) G s x‖ :=
      norm_iteratedFDerivWithin_mul_le hF hG hs.uniqueDiffOn hx (by simp)
    _ ≤ ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * C) * D := by
      refine Finset.sum_le_sum fun i hi => ?_
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hf i (by simpa using hi)) (by positivity))
        (hg (n - i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = _ := by
      have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
        exact_mod_cast Nat.sum_range_choose n
      rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]

/-- A uniform five-jet bound for the projection yields polynomial five-jet
bounds for both frozen inverse symbols. -/
theorem complexFrozenSymbols_fiveJets_le (X : EndpointComplexification H Hc)
    {P : Vec3 → H →L[ℝ] H} {B : H →L[ℝ] H} {s : Set Vec3} (hs : IsOpen s)
    (hP : ContDiffOn ℝ ∞ P s) {μ : ℝ} (hμ : 0 < μ)
    (hProj : ∀ ξ ∈ s, (P ξ : H →ₗ[ℝ] H).IsSymmetricProjection)
    (hB : ∀ ξ ∈ s, ∀ v, P ξ v = v → μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ)
    {x : Vec3} (hx : x ∈ s) {D : ℝ} (hD : 1 ≤ D)
    (hDeriv : ∀ i, i ≤ 5 → ‖iteratedFDeriv ℝ i P x‖ ≤ D ^ i) :
    let C := (((5 : ℕ).factorial : ℝ)) ^ 2 * (2 * D) ^ 5
    let Q := 2 + μ⁻¹ + ‖B‖
    (∀ i, i ≤ 5 → ‖iteratedFDeriv ℝ i (complexFrozenInverseSymbol X P B) x‖ ≤ C * Q ^ 11) ∧
      (∀ i, i ≤ 5 → ‖iteratedFDeriv ℝ i (complexFrozenProjectedInverseSymbol X P B) x‖ ≤
        (32 * D ^ 5) * C * Q ^ 11) := by
  intro C Q
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hQ : 1 ≤ Q := by
    unfold Q
    linarith [norm_nonneg B, inv_nonneg.mpr hμ.le]
  have hBsize : ‖B‖ + 1 ≤ Q := by
    unfold Q
    linarith [inv_nonneg.mpr hμ.le]
  have hK : (min 1 μ)⁻¹ ≤ Q := by
    rcases le_total μ 1 with h | h
    · rw [min_eq_right h]
      unfold Q
      linarith [norm_nonneg B]
    · rw [min_eq_left h, inv_one]
      exact hQ
  have hInv (n : ℕ) (hn : n ≤ 5) :
      ‖iteratedFDeriv ℝ n (complexFrozenInverseSymbol X P B) x‖ ≤ C * Q ^ 11 := by
    have hfact : (n.factorial : ℝ) ≤ ((5 : ℕ).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le hn
    have hkpow : ((min 1 μ)⁻¹) ^ (n + 1) ≤ Q ^ 6 :=
      (pow_le_pow_left₀ (by positivity) hK _).trans (pow_le_pow_right₀ hQ (by omega))
    have htwoD : 1 ≤ 2 * D := by linarith
    have hDQ : 1 ≤ (2 * D) * Q := by
      have h := mul_le_mul htwoD hQ (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ 2 * D)
      simpa only [one_mul] using h
    have hbpow : (2 * D * (‖B‖ + 1)) ^ n ≤ ((2 * D) * Q) ^ 5 :=
      (pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left hBsize (by positivity)) _).trans
        (pow_le_pow_right₀ hDQ hn)
    calc
      _ ≤ (n.factorial : ℝ) ^ 2 * ((min 1 μ)⁻¹) ^ (n + 1) * (2 * D * (‖B‖ + 1)) ^ n :=
        norm_iteratedFDeriv_complexFrozenInverseSymbol_le X hs hP hμ hProj hB hx hD₀
          (fun i hi => hDeriv i (hi.trans hn))
      _ ≤ (((5 : ℕ).factorial : ℝ)) ^ 2 * Q ^ 6 * ((2 * D) * Q) ^ 5 := by
        gcongr
      _ = _ := by unfold C; rw [mul_pow]; ring
  refine ⟨hInv, fun n hn => ?_⟩
  have hUnit (ξ : Vec3) (hξ : ξ ∈ s) : IsUnit (frozenSymbol (P ξ) B) :=
    frozenSymbol_isUnit (hProj ξ hξ) hμ (hB ξ hξ)
  have hprojBound (i : ℕ) (hi : i ≤ n) : ‖iteratedFDeriv ℝ i P x‖ ≤ D ^ 5 :=
    (hDeriv i (hi.trans hn)).trans (pow_le_pow_right₀ hD (hi.trans hn))
  calc
    _ ≤ (2 : ℝ) ^ n * (C * Q ^ 11) * D ^ 5 :=
      norm_iteratedFDeriv_complexFrozenProjectedInverseSymbol_le X hs hP hUnit hx
        (by unfold C; positivity) (fun i hi => hInv i (hi.trans hn)) hprojBound
    _ ≤ (2 : ℝ) ^ 5 * (C * Q ^ 11) * D ^ 5 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) (by unfold C; positivity))
        (by positivity)
    _ = _ := by ring

/-- The compressed frozen identity at one Fourier mode. In this statement
`w` is the coefficient of the variable multiplication `B(·)v`, while
`s` is the coefficient of the source using the difference from the frozen
coefficient. -/
theorem complexFrozenMode_identity (X : EndpointComplexification H Hc)
    {r B : H →L[ℝ] H} {μ : ℝ} (hr : (r : H →ₗ[ℝ] H).IsSymmetricProjection)
    (hμ : 0 < μ) (hB : ∀ v, r v = v → μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ)
    {v f s w : Hc} (hv : X.extendOperator r v = v)
    (hf : f = X.extendOperator r w) (hs : s = X.extendOperator B v - w) :
    X.extendOperator (Ring.inverse (frozenSymbol r B)) f +
      X.extendOperator (Ring.inverse (frozenSymbol r B) * r) s = v := by
  let A := frozenSymbol r B
  let I := X.extendOperator (Ring.inverse A)
  let P := X.extendOperator r
  have hUnit : IsUnit A := frozenSymbol_isUnit hr hμ hB
  have hF : X.extendOperator A v = P (X.extendOperator B v) := by
    rw [show A = frozenSymbol r B from rfl, X.extendOperator_frozenSymbol]
    change P (X.extendOperator B (P v)) + (v - P v) = _
    rw [show P v = v from hv, sub_self, add_zero]
  have hInv : I (X.extendOperator A v) = v := by
    have hprod := X.extendOperator_mul (Ring.inverse A) A
    rw [Ring.inverse_mul_cancel A hUnit, X.extendOperator_one] at hprod
    exact (DFunLike.congr_fun hprod v).symm
  rw [X.extendOperator_mul, hf, hs]
  change I (P w) + I (P (X.extendOperator B v - w)) = _
  rw [← map_add, ← map_add, add_sub_cancel, ← hF]
  exact hInv

end FrozenSymbols

section RealHalfHolder

variable {A H Hc : Type*} [MetricSpace A] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup Hc] [NormedSpace ℝ Hc] [NormedSpace ℂ Hc] [IsScalarTower ℝ ℂ Hc]

theorem norm_complexification_ofReal_le_one (X : EndpointComplexification H Hc) :
    ‖X.ofReal‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro x
  rw [X.norm_ofReal, one_mul]

theorem norm_complexification_re_le_one (X : EndpointComplexification H Hc) : ‖X.re‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro z
  rw [one_mul]
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [X.norm_sq]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Restrict a complex Fourier multiplier to real inputs and take its real part. -/
def realifyHalfHolderMultiplier (X : EndpointComplexification H Hc)
    (L : HalfHolder A Hc →L[ℝ] HalfHolder A Hc) : HalfHolder A H →L[ℝ] HalfHolder A H :=
  (HalfHolder.map X.re).comp (L.comp (HalfHolder.map X.ofReal))

theorem norm_realifyHalfHolderMultiplier_le (X : EndpointComplexification H Hc)
    (L : HalfHolder A Hc →L[ℝ] HalfHolder A Hc) :
    ‖realifyHalfHolderMultiplier X L‖ ≤ ‖L‖ := by
  have hout : ‖HalfHolder.map (X := A) X.re‖ ≤ 1 :=
    (HalfHolder.norm_map_le _).trans (norm_complexification_re_le_one X)
  have hin : ‖HalfHolder.map (X := A) X.ofReal‖ ≤ 1 :=
    (HalfHolder.norm_map_le _).trans (norm_complexification_ofReal_le_one X)
  unfold realifyHalfHolderMultiplier
  exact (opNorm_comp_le _ _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) hout).trans
      ((opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hin)))

@[simp] theorem eval_realifyHalfHolderMultiplier (X : EndpointComplexification H Hc)
    (L : HalfHolder A Hc →L[ℝ] HalfHolder A Hc) (f : HalfHolder A H) (x : A) :
    HalfHolder.eval x (realifyHalfHolderMultiplier X L f) =
      X.re (HalfHolder.eval x (L (HalfHolder.map X.ofReal f))) := by
  change HalfHolder.eval x (HalfHolder.map X.re (L (HalfHolder.map X.ofReal f))) = _
  rw [HalfHolder.eval_map]

theorem norm_eval_realifyHalfHolderMultiplier_sub_le (X : EndpointComplexification H Hc)
    (L : HalfHolder A Hc →L[ℝ] HalfHolder A Hc) (f : HalfHolder A H) (x y : A) :
    ‖HalfHolder.eval x (realifyHalfHolderMultiplier X L f) -
      HalfHolder.eval y (realifyHalfHolderMultiplier X L f)‖ ≤
      ‖HalfHolder.eval x (L (HalfHolder.map X.ofReal f)) -
        HalfHolder.eval y (L (HalfHolder.map X.ofReal f))‖ := by
  rw [eval_realifyHalfHolderMultiplier, eval_realifyHalfHolderMultiplier, ← map_sub]
  exact (X.re.le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_complexification_re_le_one X))

theorem realifyHalfHolderMultiplier_identity (X : EndpointComplexification H Hc)
    (F G : HalfHolder A Hc →L[ℝ] HalfHolder A Hc) (v f s : HalfHolder A H)
    (h : HalfHolder.map X.ofReal v = F (HalfHolder.map X.ofReal f) + G (HalfHolder.map X.ofReal s)) :
    v = realifyHalfHolderMultiplier X F f + realifyHalfHolderMultiplier X G s := by
  apply HalfHolder.ext
  intro x
  have hx := congrArg (fun w => X.re (HalfHolder.eval x w)) h
  rw [map_add, map_add, HalfHolder.eval_map, X.re_ofReal] at hx
  simpa only [map_add, eval_realifyHalfHolderMultiplier] using hx

end RealHalfHolder

/-- The actual angular projection on integer frequencies is the complex
Leray projection used in the spatial (L^2) model. -/
theorem endpointComplexify_angularLeray_latticeVector (k : Fin 3 → ℤ) :
    endpointSpatialComplexification.extendOperator (angularLeray (latticeVector k)) =
      lerayModeProjection k := by
  apply ContinuousLinearMap.ext
  intro z
  have h := lerayModeProjection_toLp k z.ofLp
  change lerayModeProjection k z = WithLp.toLp 2 (lerayMode k z.ofLp) at h
  rw [h, endpointSpatialComplexification.extendOperator_apply]
  apply PiLp.ext
  intro i
  have hc := congrFun (lerayMode_eq_angularLeray_complex_parts k z.ofLp) i
  change ((angularLeray (latticeVector k) (periodicRealPartVector z)) i : ℂ) +
      Complex.I * ((angularLeray (latticeVector k) (periodicImagPartVector z)) i : ℂ) =
    lerayMode k z.ofLp i
  exact hc.symm

/-- A single five-jet constant works for the spatial and mixed projections on
the annulus used by the dyadic multiplier. -/
theorem exists_angularProjection_annular_fiveJets :
    ∃ D : ℝ, 1 ≤ D ∧
      (∀ i : ℕ, i ≤ 5 → ∀ ξ : Vec3, 1 / 2 ≤ ‖ξ‖ →
        ‖iteratedFDeriv ℝ i angularLeray ξ‖ ≤ D ^ i) ∧
      (∀ T : ℝ, 0 < T → ∀ i : ℕ, i ≤ 5 → ∀ ξ : Vec3, 1 / 2 ≤ ‖ξ‖ →
        ‖iteratedFDeriv ℝ i (angularTimeLeray T) ξ‖ ≤ D ^ i) := by
  obtain ⟨D, hD, hjet⟩ := exists_angularLeray_jet_bound 5
  have hD₀ := zero_le_one.trans hD
  have hξpos (ξ : Vec3) (hξ : 1 / 2 ≤ ‖ξ‖) : 0 < ‖ξ‖ :=
    (by norm_num : 0 < (1 / 2 : ℝ)).trans_le hξ
  have hupper (ξ : Vec3) (hξ : 1 / 2 ≤ ‖ξ‖) : D / ‖ξ‖ ≤ 2 * D := by
    apply (div_le_iff₀ (hξpos ξ hξ)).mpr
    calc
      D = (2 * D) * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hξ (by positivity)
  have hSpatial (i : ℕ) (hi : i ≤ 5) (ξ : Vec3) (hξ : 1 / 2 ≤ ‖ξ‖) :
      ‖iteratedFDeriv ℝ i angularLeray ξ‖ ≤ (2 * D) ^ i :=
    (hjet ξ (norm_pos_iff.mp (hξpos ξ hξ)) i hi).trans
      (pow_le_pow_left₀ (by positivity) (hupper ξ hξ) i)
  refine ⟨2 * D, by linarith, hSpatial, fun T hT i hi ξ hξ => ?_⟩
  exact (norm_iteratedFDeriv_angularTimeLeray_le hT i (norm_pos_iff.mp (hξpos ξ hξ))).trans
    (hSpatial i hi ξ hξ)

section ConcreteTorus

local notation "Labels" => UnitAddTorus (Fin 3)
local notation "Punctured" => ({0}ᶜ : Set Vec3)
local notation "FrozenCutoff" => (dyadicMultiplierCutoff : Vec3 → ℝ)

noncomputable local instance freezingConcreteCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance freezingConcreteCircleHaar : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

variable {H Hc : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Hc] [NormedSpace ℂ Hc]
  [CompleteSpace Hc]

/-- The fixed-cutoff homogeneous Fourier multiplier, acting on real fields. -/
def realHomogeneousHalfHolderMultiplier (X : EndpointComplexification H Hc)
    {A : Vec3 → Hc →L[ℂ] Hc} (hA : ContDiffOn ℝ ∞ A Punctured) :
    HalfHolder Labels H →L[ℝ] HalfHolder Labels H :=
  realifyHalfHolderMultiplier (A := Labels) X
    (homogeneousHalfHolderMultiplier (E := Hc) (F := Hc) (ψ := FrozenCutoff)
      dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero hA)

/-- The frozen inverse (A_0(D)^{-1}) on real half-Hölder fields. -/
def freezingInverseHalfHolderMultiplier (X : EndpointComplexification H Hc)
    {P : Vec3 → H →L[ℝ] H} {B : H →L[ℝ] H}
    (hP : ContDiffOn ℝ ∞ P Punctured) (hUnit : ∀ ξ ∈ Punctured, IsUnit (frozenSymbol (P ξ) B)) :
    HalfHolder Labels H →L[ℝ] HalfHolder Labels H :=
  realHomogeneousHalfHolderMultiplier X (contDiffOn_complexFrozenInverseSymbol X hP hUnit)

/-- The frozen correction operator (A_0(D)^{-1}mathcal R) on real fields. -/
def freezingProjectedInverseHalfHolderMultiplier (X : EndpointComplexification H Hc)
    {P : Vec3 → H →L[ℝ] H} {B : H →L[ℝ] H}
    (hP : ContDiffOn ℝ ∞ P Punctured) (hUnit : ∀ ξ ∈ Punctured, IsUnit (frozenSymbol (P ξ) B)) :
    HalfHolder Labels H →L[ℝ] HalfHolder Labels H :=
  realHomogeneousHalfHolderMultiplier X (contDiffOn_complexFrozenProjectedInverseSymbol X hP hUnit)

omit [CompleteSpace H] in
theorem exists_norm_realHomogeneousHalfHolderMultiplier_le_mass
    (X : EndpointComplexification H Hc) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {A : Vec3 → Hc →L[ℂ] Hc} (hA : ContDiffOn ℝ ∞ A Punctured),
        ‖realHomogeneousHalfHolderMultiplier X hA‖ ≤
          C * multiplierDerivativeMass (annularLocalize FrozenCutoff A) + ‖A 0‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_homogeneousHalfHolderMultiplier_le_mass (E := Hc) (F := Hc)
      dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero
  exact ⟨C, hC, fun hA => (norm_realifyHalfHolderMultiplier_le X _).trans (hbound hA)⟩

/-- Fourier coefficients of the complexification of a real Hölder field. -/
def complexifiedHalfHolderFourierCoeff (X : EndpointComplexification H Hc)
    (f : HalfHolder Labels H) (k : Fin 3 → ℤ) : Hc :=
  mFourierCoeff (continuousHalfHolder (HalfHolder.map X.ofReal f)) k

omit [CompleteSpace H] [CompleteSpace Hc] in
theorem complexifiedHalfHolderFourierCoeff_sub (X : EndpointComplexification H Hc)
    (u v : HalfHolder Labels H) (k : Fin 3 → ℤ) :
    complexifiedHalfHolderFourierCoeff X (u - v) k =
      complexifiedHalfHolderFourierCoeff X u k - complexifiedHalfHolderFourierCoeff X v k := by
  unfold complexifiedHalfHolderFourierCoeff
  rw [map_sub]
  change (continuousFourierCoefficient k)
    (continuousHalfHolder (HalfHolder.map X.ofReal u) -
      continuousHalfHolder (HalfHolder.map X.ofReal v)) = _
  rw [map_sub, continuousFourierCoefficient_apply, continuousFourierCoefficient_apply]

omit [CompleteSpace H] in
/-- Constant real coefficients complexify inside a torus Fourier integral. -/
theorem complexifiedHalfHolderFourierCoeff_map (X : EndpointComplexification H Hc)
    (B : H →L[ℝ] H) (v : HalfHolder Labels H) (k : Fin 3 → ℤ) :
    complexifiedHalfHolderFourierCoeff X (HalfHolder.map B v) k =
      X.extendOperator B (complexifiedHalfHolderFourierCoeff X v k) := by
  let f := continuousHalfHolder (HalfHolder.map X.ofReal v)
  have hpoint (z : Labels) : continuousHalfHolder (HalfHolder.map X.ofReal (HalfHolder.map B v)) z =
      X.extendOperator B (f z) := by
    change HalfHolder.eval z (HalfHolder.map X.ofReal (HalfHolder.map B v)) =
      X.extendOperator B (HalfHolder.eval z (HalfHolder.map X.ofReal v))
    rw [HalfHolder.eval_map, HalfHolder.eval_map, HalfHolder.eval_map, X.extendOperator_ofReal]
  unfold complexifiedHalfHolderFourierCoeff mFourierCoeff
  change (∫ z, mFourier (-k) z •
    continuousHalfHolder (HalfHolder.map X.ofReal (HalfHolder.map B v)) z) =
      X.extendOperator B (∫ z, mFourier (-k) z • f z)
  have hint : Integrable (fun z => mFourier (-k) z • f z) :=
    ((mFourier (-k)).continuous.smul f.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [hpoint, ← map_smul]
  exact (X.extendOperator B).integral_comp_comm hint

set_option maxHeartbeats 500000 in
/-- A projected Fourier mode identity gives the full real frozen identity,
with the inverse acting on the data and its projected version on the source. -/
theorem freezingHalfHolderMultipliers_identity (X : EndpointComplexification H Hc)
    {P : Vec3 → H →L[ℝ] H} {B : H →L[ℝ] H}
    (hP : ContDiffOn ℝ ∞ P Punctured) (hUnit : ∀ ξ ∈ Punctured, IsUnit (frozenSymbol (P ξ) B))
    (hhom : ∀ c : ℝ, 0 < c → ∀ ξ : Vec3, ξ ≠ 0 → P (c • ξ) = P ξ)
    (hProj : ∀ ξ, (P ξ : H →ₗ[ℝ] H).IsSymmetricProjection) {μ : ℝ} (hμ : 0 < μ)
    (hB : ∀ ξ v, P ξ v = v → μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ)
    (v f s w : HalfHolder Labels H)
    (hv : ∀ k, X.extendOperator (P (latticeVector k)) (complexifiedHalfHolderFourierCoeff X v k) =
      complexifiedHalfHolderFourierCoeff X v k)
    (hf : ∀ k, complexifiedHalfHolderFourierCoeff X f k =
      X.extendOperator (P (latticeVector k)) (complexifiedHalfHolderFourierCoeff X w k))
    (hs : ∀ k, complexifiedHalfHolderFourierCoeff X s k =
      X.extendOperator B (complexifiedHalfHolderFourierCoeff X v k) -
        complexifiedHalfHolderFourierCoeff X w k) :
    v = freezingInverseHalfHolderMultiplier X hP hUnit f +
      freezingProjectedInverseHalfHolderMultiplier X hP hUnit s := by
  let hA := contDiffOn_complexFrozenInverseSymbol X hP hUnit
  let hG := contDiffOn_complexFrozenProjectedInverseSymbol X hP hUnit
  let F := homogeneousHalfHolderMultiplier (E := Hc) (F := Hc) dyadicMultiplierCutoff_smooth
    dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero hA
  let G := homogeneousHalfHolderMultiplier (E := Hc) (F := Hc) dyadicMultiplierCutoff_smooth
    dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero hG
  have hFhom (c : ℝ) (hc : 0 < c) (ξ : Vec3) (hξ : ξ ≠ 0) :
      complexFrozenInverseSymbol X P B (c • ξ) = complexFrozenInverseSymbol X P B ξ :=
    complexFrozenInverseSymbol_pos_smul X B (hhom c hc ξ hξ)
  have hGhom (c : ℝ) (hc : 0 < c) (ξ : Vec3) (hξ : ξ ≠ 0) :
      complexFrozenProjectedInverseSymbol X P B (c • ξ) = complexFrozenProjectedInverseSymbol X P B ξ :=
    complexFrozenProjectedInverseSymbol_pos_smul X B (hhom c hc ξ hξ)
  apply realifyHalfHolderMultiplier_identity X F G v f s
  apply eq_halfHolder_of_mFourierCoeff_eq
  intro k
  change complexifiedHalfHolderFourierCoeff X v k = continuousFourierCoefficient k
    (continuousHalfHolder (F (HalfHolder.map X.ofReal f)) +
      continuousHalfHolder (G (HalfHolder.map X.ofReal s)))
  rw [map_add, continuousFourierCoefficient_apply, continuousFourierCoefficient_apply]
  have hFcoef := mFourierCoeff_homogeneousHalfHolderMultiplier dyadicMultiplierCutoff_smooth
    dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero hA hFhom (HalfHolder.map X.ofReal f) k
  have hGcoef := mFourierCoeff_homogeneousHalfHolderMultiplier dyadicMultiplierCutoff_smooth
    dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero hG hGhom (HalfHolder.map X.ofReal s) k
  change _ = mFourierCoeff (continuousHalfHolder (F (HalfHolder.map X.ofReal f))) k +
    mFourierCoeff (continuousHalfHolder (G (HalfHolder.map X.ofReal s))) k
  rw [show F = homogeneousHalfHolderMultiplier dyadicMultiplierCutoff_smooth
    dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero hA from rfl,
    show G = homogeneousHalfHolderMultiplier dyadicMultiplierCutoff_smooth
    dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero hG from rfl, hFcoef, hGcoef]
  exact (complexFrozenMode_identity X (hProj (latticeVector k)) hμ (hB (latticeVector k))
    (hv k) (hf k) (hs k)).symm

omit [CompleteSpace H] in
private theorem realHomogeneousHalfHolderMultiplier_off_support (X : EndpointComplexification H Hc)
    {A : Vec3 → Hc →L[ℂ] Hc} (hA : ContDiffOn ℝ ∞ A Punctured)
    (f : HalfHolder Labels H) {a b : Labels} {r : ℝ} (hr : 0 < r)
    (hzero : ∀ z, dist z a ≤ r → HalfHolder.eval z f = 0) (hb : dist b a ≤ r / 4) :
    let C := 32 * ((1 + 2 * Real.pi) * (4 : ℝ) ^ 5 *
      multiplierDerivativeMass (annularLocalize FrozenCutoff A))
    ‖HalfHolder.eval a (realHomogeneousHalfHolderMultiplier X hA f) -
      HalfHolder.eval b (realHomogeneousHalfHolderMultiplier X hA f)‖ ≤
      (32 * (18 * C) * unitInverseFourthPowerTail / r) * ‖f.val.1‖ * dist b a := by
  intro C
  let g := HalfHolder.map X.ofReal f
  unfold realHomogeneousHalfHolderMultiplier
  refine (norm_eval_realifyHalfHolderMultiplier_sub_le X _ f a b).trans ?_
  rw [eval_sub_homogeneousHalfHolderMultiplier_eq_dyadic
    dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero hA]
  let σ := annularLocalize FrozenCutoff A
  have hc : HasCompactSupport σ := annularLocalize_compact dyadicMultiplierCutoff_zero A
  have hs : ContDiff ℝ ∞ σ :=
    annularLocalize_smooth dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit hA
  have hs0 : σ 0 = 0 := annularLocalize_zero_of_small dyadicMultiplierCutoff_unit A 0 (by norm_num)
  have hband (ξ : Vec3) (hξ : 4 < ‖ξ‖) : σ ξ = 0 :=
    annularLocalize_zero_of_large dyadicMultiplierCutoff_zero A ξ (by linarith)
  have hquot : Continuous toUnitTorus :=
    continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i)
  have hbound (z : Labels) : ‖continuousHalfHolder g z‖ ≤ ‖f.val.1‖ := by
    change ‖HalfHolder.eval z (HalfHolder.map X.ofReal f)‖ ≤ _
    rw [HalfHolder.eval_map, X.norm_ofReal, HalfHolder.eval_apply]
    exact f.val.1.norm_coe_le_norm z
  have hvanish (z : Labels) (hz : dist z a ≤ r) : continuousHalfHolder g z = 0 := by
    change HalfHolder.eval z (HalfHolder.map X.ofReal f) = 0
    rw [HalfHolder.eval_map, hzero z hz, map_zero]
  exact norm_sub_compactMultiplierDyadicLimit_le_off_support hc hs
    ((continuousHalfHolder g).continuous.comp hquot) hbound
    (tendsto_operatorLiftConvolution_compactSymbolDyadicBlocks (fun ξ h => dyadicMultiplierCutoff_zero ξ h.le)
      dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit hc hs hs0 hband g)
    hr hvanish hb

/-- The real frozen correction inherits the concrete off-support bound. -/
theorem freezingProjectedInverseHalfHolderMultiplier_off_support (X : EndpointComplexification H Hc)
    {P : Vec3 → H →L[ℝ] H} {B : H →L[ℝ] H}
    (hP : ContDiffOn ℝ ∞ P Punctured) (hUnit : ∀ ξ ∈ Punctured, IsUnit (frozenSymbol (P ξ) B))
    (f : HalfHolder Labels H) {a b : Labels} {r : ℝ} (hr : 0 < r)
    (hzero : ∀ z, dist z a ≤ r → HalfHolder.eval z f = 0) (hb : dist b a ≤ r / 4) :
    let A := complexFrozenProjectedInverseSymbol X P B
    let C := 32 * ((1 + 2 * Real.pi) * (4 : ℝ) ^ 5 *
      multiplierDerivativeMass (annularLocalize FrozenCutoff A))
    let G := freezingProjectedInverseHalfHolderMultiplier X hP hUnit
    ‖HalfHolder.eval a (G f) - HalfHolder.eval b (G f)‖ ≤
      (32 * (18 * C) * unitInverseFourthPowerTail / r) * ‖f.val.1‖ * dist b a :=
  realHomogeneousHalfHolderMultiplier_off_support X
    (contDiffOn_complexFrozenProjectedInverseSymbol X hP hUnit) f hr hzero hb

set_option maxHeartbeats 500000 in
/-- The frozen multiplier and off-support constants depend only on the common
annular projection jet bound and the fixed spatial cutoff. -/
theorem exists_uniform_freezingHalfHolderMultipliers_bounds {D : ℝ} (hD : 1 ≤ D) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ {H : Type u} {Hc : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [NormedAddCommGroup Hc] [NormedSpace ℂ Hc] [CompleteSpace Hc]
        (X : EndpointComplexification H Hc)
        (P : Vec3 → H →L[ℝ] H) (hP : ContDiffOn ℝ ∞ P Punctured)
        (hProj : ∀ ξ, (P ξ : H →ₗ[ℝ] H).IsSymmetricProjection) (_hP₀ : ‖P 0‖ ≤ 1)
        (_hjets : ∀ i : ℕ, i ≤ 5 → ∀ ξ : Vec3, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 →
          ‖iteratedFDeriv ℝ i P ξ‖ ≤ D ^ i)
        (B : H →L[ℝ] H) {μ : ℝ} (hμ : 0 < μ)
        (hB : ∀ ξ v, P ξ v = v → μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ),
        let hUnit : ∀ ξ ∈ Punctured, IsUnit (frozenSymbol (P ξ) B) :=
          fun ξ _ => frozenSymbol_isUnit (hProj ξ) hμ (hB ξ)
        let F := freezingInverseHalfHolderMultiplier X hP hUnit
        let G := freezingProjectedInverseHalfHolderMultiplier X hP hUnit
        let Q := 2 + μ⁻¹ + ‖B‖
        ‖F‖ ≤ C * Q ^ 11 ∧ ‖G‖ ≤ C * Q ^ 11 ∧
          ∀ (f : HalfHolder Labels H) {a b : Labels} {r : ℝ}, 0 < r →
            (∀ z, dist z a ≤ r → HalfHolder.eval z f = 0) → dist b a ≤ r / 4 →
            ‖HalfHolder.eval a (G f) - HalfHolder.eval b (G f)‖ ≤
              ((K * Q ^ 11) / r) * ‖f.val.1‖ * dist b a := by
  obtain ⟨L, hL, hMass⟩ := exists_annularLocalize_mass_universal_le.{v, v}
    dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero
  obtain ⟨N, hN, hNorm⟩ := exists_norm_universal_homogeneousHalfHolderMultiplier_le_mass.{v, v}
    dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero
  let C₀ : ℝ := (((5 : ℕ).factorial : ℝ)) ^ 2 * (2 * D) ^ 5
  let J := 32 * D ^ 5 * C₀
  let M := L * J
  let C := N * M + 1
  let K := 32 * 18 * (32 * ((1 + 2 * Real.pi) * (4 : ℝ) ^ 5 * M)) * unitInverseFourthPowerTail
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hC₀ : 0 ≤ C₀ := by unfold C₀; positivity
  have hJ : 0 ≤ J := by unfold J; positivity
  have hM : 0 ≤ M := mul_nonneg hL hJ
  have htail := unitInverseFourthPowerTail_nonneg
  refine ⟨C, K, by unfold C; positivity, by unfold K; positivity, ?_⟩
  intro H Hc _ _ _ _ _ _ X P hP hProj hP₀ hjets B μ hμ hB hUnit F G Q
  have hRealNorm {A : Vec3 → Hc →L[ℂ] Hc} (hA : ContDiffOn ℝ ∞ A Punctured) :
      ‖realHomogeneousHalfHolderMultiplier X hA‖ ≤
        N * multiplierDerivativeMass (annularLocalize FrozenCutoff A) + ‖A 0‖ :=
    (norm_realifyHalfHolderMultiplier_le X _).trans (hNorm hA)
  let A := complexFrozenInverseSymbol X P B
  let R := complexFrozenProjectedInverseSymbol X P B
  have hA := contDiffOn_complexFrozenInverseSymbol X hP hUnit
  have hR := contDiffOn_complexFrozenProjectedInverseSymbol X hP hUnit
  have hQ : 1 ≤ Q := by unfold Q; linarith [inv_nonneg.mpr hμ.le, norm_nonneg B]
  have hJQ : 0 ≤ J * Q ^ 11 := by positivity
  have hjet (ξ : Vec3) (hlo : 1 / 2 ≤ ‖ξ‖) (hhi : ‖ξ‖ ≤ 2) :=
    complexFrozenSymbols_fiveJets_le X isOpen_compl_singleton hP hμ
      (fun ξ _ => hProj ξ) (fun ξ _ => hB ξ) (x := ξ)
      (show ξ ∈ Punctured from by
        change ξ ≠ 0
        exact norm_pos_iff.mp ((by norm_num : 0 < (1 / 2 : ℝ)).trans_le hlo))
      hD (fun i hi => hjets i hi ξ hlo hhi)
  have hmassA : multiplierDerivativeMass (annularLocalize FrozenCutoff A) ≤ M * Q ^ 11 := by
    have ha (i : ℕ) (hi : i ≤ 5) (ξ : Vec3) (hlo : 1 / 2 ≤ ‖ξ‖) (hhi : ‖ξ‖ ≤ 2) :
        ‖iteratedFDeriv ℝ i A ξ‖ ≤ J * Q ^ 11 := by
      refine ((hjet ξ hlo hhi).1 i hi).trans ?_
      have hDJ : 1 ≤ 32 * D ^ 5 := by
        have hpow := one_le_pow₀ hD (n := 5)
        linarith
      unfold J
      exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hC₀ hDJ) (by positivity)
    exact (hMass hA hJQ ha).trans_eq (by unfold M; ring)
  have hmassR : multiplierDerivativeMass (annularLocalize FrozenCutoff R) ≤ M * Q ^ 11 := by
    exact (hMass hR hJQ (fun i hi ξ hlo hhi => (hjet ξ hlo hhi).2 i hi)).trans_eq (by unfold M; ring)
  have hzero : (min 1 μ)⁻¹ ≤ Q ^ 11 := by
    refine le_trans (b := Q) ?_ ?_
    · rcases le_total μ 1 with h | h
      · rw [min_eq_right h]
        unfold Q
        linarith [norm_nonneg B]
      · rw [min_eq_left h, inv_one]
        exact hQ
    · simpa only [pow_one] using pow_le_pow_right₀ hQ (show 1 ≤ 11 by norm_num)
  have hNormA : ‖A 0‖ ≤ Q ^ 11 :=
    (norm_complexFrozenInverseSymbol_le X (hProj 0) hμ (hB 0)).trans hzero
  have hNormR : ‖R 0‖ ≤ Q ^ 11 :=
    (norm_complexFrozenProjectedInverseSymbol_le X (hProj 0) hP₀ hμ (hB 0)).trans hzero
  have hmerge : N * (M * Q ^ 11) + Q ^ 11 = C * Q ^ 11 := by unfold C; ring
  refine ⟨(hRealNorm hA).trans
      ((add_le_add (mul_le_mul_of_nonneg_left hmassA hN) hNormA).trans_eq hmerge),
    (hRealNorm hR).trans
      ((add_le_add (mul_le_mul_of_nonneg_left hmassR hN) hNormR).trans_eq hmerge), ?_⟩
  intro f a b r hr hvanish hb
  have h := freezingProjectedInverseHalfHolderMultiplier_off_support X hP hUnit f hr hvanish hb
  dsimp only at h
  refine h.trans ?_
  have hc : 0 ≤ dist b a := dist_nonneg
  calc
    _ ≤ (32 * (18 * (32 * ((1 + 2 * Real.pi) * (4 : ℝ) ^ 5 * (M * Q ^ 11)))) *
          unitInverseFourthPowerTail / r) * ‖f.val.1‖ * dist b a := by
      gcongr
    _ = _ := by unfold K; ring

/-- The frozen multiplier norm and off-support estimate for a fixed Hilbert target. -/
theorem exists_freezingHalfHolderMultipliers_bounds (X : EndpointComplexification H Hc)
    (P : Vec3 → H →L[ℝ] H) (hP : ContDiffOn ℝ ∞ P Punctured)
    (hProj : ∀ ξ, (P ξ : H →ₗ[ℝ] H).IsSymmetricProjection) (hP₀ : ‖P 0‖ ≤ 1)
    {D : ℝ} (hD : 1 ≤ D)
    (hjets : ∀ i : ℕ, i ≤ 5 → ∀ ξ : Vec3, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 →
      ‖iteratedFDeriv ℝ i P ξ‖ ≤ D ^ i) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ (B : H →L[ℝ] H) {μ : ℝ} (hμ : 0 < μ)
        (hB : ∀ ξ v, P ξ v = v → μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ),
        let hUnit : ∀ ξ ∈ Punctured, IsUnit (frozenSymbol (P ξ) B) :=
          fun ξ _ => frozenSymbol_isUnit (hProj ξ) hμ (hB ξ)
        let F := freezingInverseHalfHolderMultiplier X hP hUnit
        let G := freezingProjectedInverseHalfHolderMultiplier X hP hUnit
        let Q := 2 + μ⁻¹ + ‖B‖
        ‖F‖ ≤ C * Q ^ 11 ∧ ‖G‖ ≤ C * Q ^ 11 ∧
          ∀ (f : HalfHolder Labels H) {a b : Labels} {r : ℝ}, 0 < r →
            (∀ z, dist z a ≤ r → HalfHolder.eval z f = 0) → dist b a ≤ r / 4 →
            ‖HalfHolder.eval a (G f) - HalfHolder.eval b (G f)‖ ≤
              ((K * Q ^ 11) / r) * ‖f.val.1‖ * dist b a := by
  obtain ⟨C, K, hC, hK, hbound⟩ := exists_uniform_freezingHalfHolderMultipliers_bounds hD
  exact ⟨C, K, hC, hK, hbound X P hP hProj hP₀ hjets⟩

end ConcreteTorus

end
end TorusEuler
