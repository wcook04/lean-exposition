import Breakdown.Spectral.SpectralProjection

noncomputable section

open Metric

namespace Breakdown.Spectral

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

theorem isCompactOperator_circleIntegral {f : ℂ → Y →L[ℂ] Y} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ContinuousOn f (sphere c R)) (hc : ∀ z ∈ sphere c R, IsCompactOperator (f z)) :
    IsCompactOperator ⇑(∮ z in C(c, R), f z) := by
  have hS : IsClosed {T : Y →L[ℂ] Y | IsCompactOperator T} := isClosed_setOfPred_isCompactOperator
  have hconv : Convex ℝ {T : Y →L[ℂ] Y | IsCompactOperator T} :=
    ((compactOperator (RingHom.id ℂ) Y Y).restrictScalars ℝ).convex
  set g : ℝ → Y →L[ℂ] Y := fun θ => deriv (circleMap c R) θ • f (circleMap c R θ) with hg
  have hgc : Continuous g := by
    have h1 : Continuous fun θ => f (circleMap c R θ) :=
      hf.comp_continuous (continuous_circleMap c R) (circleMap_mem_sphere c hR)
    have h2 : Continuous fun θ : ℝ => deriv (circleMap c R) θ := by
      simp only [deriv_circleMap]
      exact (continuous_circleMap 0 R).mul continuous_const
    exact h2.smul h1
  have hgm : ∀ θ, IsCompactOperator (g θ) := fun θ => by
    have := (hc _ (circleMap_mem_sphere c hR θ)).smul (deriv (circleMap c R) θ)
    simpa [hg, FunLike.coe_smul] using this
  have hpos : (0:ℝ) < 2 * Real.pi := Real.two_pi_pos
  have h0 : MeasureTheory.volume (Set.Ioc (0:ℝ) (2 * Real.pi)) ≠ 0 := by simp [Real.pi_pos]
  have hfin : MeasureTheory.volume (Set.Ioc (0:ℝ) (2 * Real.pi)) ≠ ⊤ := measure_Ioc_lt_top.ne
  have havg := hconv.set_average_mem hS h0 hfin (Filter.Eventually.of_forall hgm)
    hgc.integrableOn_Ioc
  rw [MeasureTheory.setAverage_eq] at havg
  have hm : MeasureTheory.volume.real (Set.Ioc (0:ℝ) (2 * Real.pi)) ≠ 0 := by
    rw [MeasureTheory.measureReal_def]
    exact ENNReal.toReal_ne_zero.mpr ⟨h0, hfin⟩
  have hint : (∮ z in C(c, R), f z) = (MeasureTheory.volume.real (Set.Ioc (0:ℝ) (2 * Real.pi))) •
      ((MeasureTheory.volume.real (Set.Ioc (0:ℝ) (2 * Real.pi)))⁻¹ •
        ∫ θ in Set.Ioc 0 (2 * Real.pi), g θ) := by
    rw [smul_smul, mul_inv_cancel₀ hm, one_smul, circleIntegral,
      intervalIntegral.integral_of_le hpos.le]
  rw [hint, FunLike.coe_smul]
  exact IsCompactOperator.smul havg _

theorem isCompactOperator_one_sub_specProj (T₀ C : Y →L[ℂ] Y) {b ρ : ℝ} (hT₀ : ‖T₀‖ ≤ b)
    (hbρ : b < ρ) (hC : IsCompactOperator C)
    (hA : ∀ z : ℂ, ‖z‖ = ρ → z ∈ resolventSet ℂ (T₀ + C)) :
    IsCompactOperator ⇑((1 : Y →L[ℂ] Y) - specProj (T₀ + C) ρ) := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans hT₀
  have hρ0 : 0 ≤ ρ := by linarith
  have hA₀ : ∀ z : ℂ, ‖z‖ = ρ → z ∈ resolventSet ℂ T₀ := fun z hz =>
    mem_resolventSet_of_norm_le_lt hT₀ (by rw [hz]; exact hbρ)
  have hsph : ∀ {S : Y →L[ℂ] Y}, (∀ z : ℂ, ‖z‖ = ρ → z ∈ resolventSet ℂ S) →
      sphere (0:ℂ) ρ ⊆ resolventSet ℂ S :=
    fun h z hz => h z (by simpa using hz)
  have hc₀ : ContinuousOn (fun z : ℂ => resolvent T₀ z) (sphere 0 ρ) := (continuousOn_resolvent T₀).mono (hsph hA₀)
  have hc₁ : ContinuousOn (fun z : ℂ => resolvent (T₀ + C) z) (sphere 0 ρ) :=
    (continuousOn_resolvent _).mono (hsph hA)
  have hone : specProj T₀ ρ = 1 := specProj_large T₀ (lt_of_le_of_lt hT₀ hbρ)
  have heq : (1 : Y →L[ℂ] Y) - specProj (T₀ + C) ρ =
      (2 * Real.pi * Complex.I)⁻¹ • ∮ z in C(0, ρ), (resolvent T₀ z - resolvent (T₀ + C) z) := by
    rw [← hone, specProj, specProj, ← smul_sub,
      circleIntegral.integral_sub (hc₀.circleIntegrable hρ0) (hc₁.circleIntegrable hρ0)]
  have hpt : ∀ z ∈ sphere (0:ℂ) ρ, resolvent T₀ z - resolvent (T₀ + C) z =
      -(resolvent T₀ z * C * resolvent (T₀ + C) z) := by
    intro z hz
    have h1 := resolvent_mul_sub T₀ (hsph hA₀ hz)
    have h2 := sub_mul_resolvent (T₀ + C) (hsph hA hz)
    have hCe : (z • (1 : Y →L[ℂ] Y) - T₀) - (z • 1 - (T₀ + C)) = C := by abel
    calc resolvent T₀ z - resolvent (T₀ + C) z
        = -(resolvent T₀ z * ((z • (1 : Y →L[ℂ] Y) - T₀) - (z • 1 - (T₀ + C))) *
            resolvent (T₀ + C) z) := by
          rw [mul_sub, sub_mul, h1, one_mul, mul_assoc, h2, mul_one, neg_sub]
      _ = -(resolvent T₀ z * C * resolvent (T₀ + C) z) := by rw [hCe]
  have hcomp : ∀ z ∈ sphere (0:ℂ) ρ,
      IsCompactOperator ⇑(resolvent T₀ z - resolvent (T₀ + C) z) := by
    intro z hz
    rw [hpt z hz, FunLike.coe_neg]
    refine IsCompactOperator.neg ?_
    exact (hC.clm_comp (resolvent T₀ z)).comp_clm (resolvent (T₀ + C) z)
  have hint := isCompactOperator_circleIntegral hρ0 (hc₀.sub hc₁) hcomp
  rw [heq, FunLike.coe_smul]
  exact hint.smul _

theorem finiteDimensional_range_of_isCompactOperator (P : Y →L[ℂ] Y) (hP : P * P = P)
    (hc : IsCompactOperator P) : FiniteDimensional ℂ (LinearMap.range (P : Y →ₗ[ℂ] Y)) := by
  have hfix : ∀ v ∈ LinearMap.range (P : Y →ₗ[ℂ] Y), P v = v := by
    rintro v ⟨y, rfl⟩
    change (P * P) y = P y
    rw [hP]
  have hclosed : IsClosed (LinearMap.range (P : Y →ₗ[ℂ] Y) : Set Y) := by
    have : (LinearMap.range (P : Y →ₗ[ℂ] Y) : Set Y) = {x | P x = x} := by
      ext x
      constructor
      · intro hx
        exact hfix x hx
      · intro hx
        exact ⟨x, hx⟩
    rw [this]
    exact isClosed_eq P.continuous continuous_id
  have hV : ∀ v ∈ LinearMap.range (P : Y →ₗ[ℂ] Y), (P : Y →ₗ[ℂ] Y) v ∈
      LinearMap.range (P : Y →ₗ[ℂ] Y) := fun v _ => LinearMap.mem_range_self _ v
  have hr := IsCompactOperator.restrict (f := (P : Y →ₗ[ℂ] Y)) hc hV hclosed
  have hid : (((P : Y →ₗ[ℂ] Y).restrict hV : LinearMap.range (P : Y →ₗ[ℂ] Y) →ₗ[ℂ]
      LinearMap.range (P : Y →ₗ[ℂ] Y)) : LinearMap.range (P : Y →ₗ[ℂ] Y) →
      LinearMap.range (P : Y →ₗ[ℂ] Y)) = id := by
    funext v
    apply Subtype.ext
    rw [LinearMap.restrict_apply]
    exact hfix v v.2
  rw [hid] at hr
  exact FiniteDimensional.of_isCompactOperator_id hr

end Breakdown.Spectral
