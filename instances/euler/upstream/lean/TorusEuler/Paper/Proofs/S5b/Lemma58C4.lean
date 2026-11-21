import TorusEuler.Paper.Proofs.S5b.Lemma58C3
import TorusEuler.PaperGenericPhysicalResidual

/-!
# Lemma 5.8, third part (end): the bound of `R_χ̃^♮` from a bound of `(A₁ + C[A₁])^♮`

`activation_holder`: if `(V₀ + C[V₀])^♮(t)` is bounded in `C^{1,1/2}` by `B γ(t)` for
`t ∈ [t₀,T]` (this is (5.45) of Lemma 5.7 at `m = 1` with the bound of `‖A₁ + C[A₁]‖_{[2],γ}`
from (5.22) and (5.31), supplied by the caller), then
`‖R_χ̃^♮(t)‖_{C^{1,1/2}} ≤ B ‖χ̃'γ‖_{∞,[t₀,T]}` on `[0,T]`
(`sections/08_exact_wave.tex:139-143`: "at each time `t`, `R_χ̃` is `χ̃'(t)` times this field").
-/

open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper.S5b

open HierarchyTwistedProfile LocalizedAmplitude Lib.S5Bridge

noncomputable section

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {t₀ : ℝ} {center : ℝ → Vec3}
  {pU : Pressure} {D lam : ℝ}

/-- The half-Hölder norm is nonnegative. -/
theorem spatialHolderHalfNorm_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (f : Vec3 → E) : 0 ≤ spatialHolderHalfNorm m f :=
  Finset.sum_nonneg fun _ _ => add_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _)
    (Real.iSup_nonneg fun _ => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))

/-- **The activation term in `C^{1,1/2}`.** -/
theorem activation_holder {hT : 0 < T} (d : ParentGeometry hT U X k)
    (hL : S5.Launch T X k lam t₀) {χ : PaperWaveCutoff t₀ T}
    {ℓ h : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1)
    {amp ampE : ℝ → Vec3 → Vec3}
    (hE : ContDiffOn ℝ ∞ (Function.uncurry ampE) (univ ×ˢ (univ : Set Vec3)))
    (hEq : ∀ t ∈ Icc t₀ T, ∀ a, ampE t a = amp t a)
    {P : ℕ} {R S : HierarchyTwistedProfile T k Vec3}
    {u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)}
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) {γ : ℝ → ℝ} (hγc : ContinuousOn γ (Icc t₀ T))
    (hγ : ∀ t ∈ Icc t₀ T, 0 < γ t) {B : ℝ}
    (hV : ∀ t ∈ Icc t₀ T,
      SpatialHolderHalf 1 (graphRead (fun r => X r 0) (extLeading (T := T) k hℓ hfit hh hh₁ hE +
        S5.curlCorrection d (extLeading (T := T) k hℓ hfit hh hh₁ hE)) t) ∧
      spatialHolderHalfNorm 1 (graphRead (fun r => X r 0) (extLeading (T := T) k hℓ hfit hh hh₁ hE +
        S5.curlCorrection d (extLeading (T := T) k hℓ hfit hh hh₁ hE)) t) ≤ B * γ t) :
    ∀ t ∈ Icc 0 T, SpatialHolderHalf 1 (graphRead (fun r => X r 0) (S + S5.curlCorrection d S) t) ∧
      spatialHolderHalfNorm 1 (graphRead (fun r => X r 0) (S + S5.curlCorrection d S) t) ≤
        B * χ.derivativeSize γ := by
  let V₀ := extLeading (T := T) k hℓ hfit hh hh₁ hE
  have ht₀ : t₀ ∈ Icc t₀ T := ⟨le_rfl, hL.start_lt.le⟩
  have hB : 0 ≤ B := by
    have h1 := (spatialHolderHalfNorm_nonneg 1 _).trans (hV t₀ ht₀).2
    exact nonneg_of_mul_nonneg_left h1 (hγ t₀ ht₀)
  obtain ⟨hSize, hPoint⟩ := χ.derivativeSize_bounds hT hL.start_nonneg hL.start_lt.le hγc
    (fun t ht => (hγ t ht).le)
  intro t ht
  by_cases hpre : t < t₀
  · -- before activation `S = 0` and `C[S] = 0` at time `t`
    have hχ := χ.derivative_zero_before hT ht hpre
    have hκ : ∀ x ∈ hierarchyProfileSlab T, d.covector.val.val.val x = S5.waveVector X k x.1 x.2.1 :=
      fun x hx => d.covector_value x hx
    have hzero : graphRead (fun r => X r 0) (S + S5.curlCorrection d S) t = 0 := by
      funext x
      change S.val.val.val (t, X t 0 x, ⟪k, X t 0 x⟫_ℝ) +
        (S5.curlCorrection d S).val.val.val (t, X t 0 x, ⟪k, X t 0 x⟫_ℝ) = 0
      have hS := activation_eval d hℓ hfit hu (t, X t 0 x, ⟪k, X t 0 x⟫_ℝ) ⟨ht, mem_univ _⟩
      change S.val.val.val (t, X t 0 x, ⟪k, X t 0 x⟫_ℝ) = _ at hS
      rw [hS]
      change χ.derivative t • _ + (complete hT d.inverse d.covector _ _ S).val.val.val
        (t, X t 0 x, ⟪k, X t 0 x⟫_ℝ) = 0
      rw [complete_smul_wrapped_eval hT d.inverse d.covector S
        d.oscillation.covector_independent d.oscillation.covector_ne_zero hκ
        (by exact activation_average d hℓ hfit hh hh₁ hu) ht
        (c := χ.derivative) (raw := rawLeading ℓ h amp)
        (fun b q => activation_eval d hℓ hfit hu (t, b, q) ⟨ht, mem_univ _⟩), hχ, zero_smul,
        zero_smul, add_zero]
    rw [hzero]
    exact ⟨(holder_zero 1).1, (holder_zero 1).2.trans (mul_nonneg hB hSize)⟩
  · have hact : t ∈ Icc t₀ T := ⟨le_of_not_gt hpre, ht.2⟩
    have hEqF : graphRead (fun r => X r 0) (S + S5.curlCorrection d S) t =
        χ.derivative t • graphRead (fun r => X r 0) (V₀ + S5.curlCorrection d V₀) t := by
      funext x
      change S.val.val.val (t, X t 0 x, ⟪k, X t 0 x⟫_ℝ) +
          (S5.curlCorrection d S).val.val.val (t, X t 0 x, ⟪k, X t 0 x⟫_ℝ) =
        χ.derivative t • (V₀.val.val.val (t, X t 0 x, ⟪k, X t 0 x⟫_ℝ) +
          (S5.curlCorrection d V₀).val.val.val (t, X t 0 x, ⟪k, X t 0 x⟫_ℝ))
      rw [activation_eval d hℓ hfit hu (t, X t 0 x, ⟪k, X t 0 x⟫_ℝ) ⟨ht, mem_univ _⟩,
        curlCorrection_activation_eval d hL hℓ hfit hh hh₁ hE hEq hu hact,
        extLeading_active_eval k hℓ hfit hh hh₁ hE hEq hL.start_nonneg hact, smul_add]
    obtain ⟨h1, h2⟩ := hV t hact
    obtain ⟨h3, h4⟩ := holder_smul h1 (χ.derivative t)
    rw [hEqF]
    refine ⟨h3, ?_⟩
    rw [h4]
    calc |χ.derivative t| * spatialHolderHalfNorm 1 (graphRead (fun r => X r 0)
          (V₀ + S5.curlCorrection d V₀) t) ≤ |χ.derivative t| * (B * γ t) :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = B * (|χ.derivative t| * γ t) := by ring
      _ ≤ B * χ.derivativeSize γ := mul_le_mul_of_nonneg_left (hPoint t hact) hB

end

end TorusEuler.Paper.S5b
