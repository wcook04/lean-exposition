import Breakdown.Torus.StatementsAnalysis
import Breakdown.Torus.StatementsSmooth

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace Final.Internal

theorem contDiff_slice {v : ℝ → Space → Space}
    (h : ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.1 z.2) (Ici 0 ×ˢ univ)) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (v t) := by
  have hg : ContDiff ℝ ∞ (fun x : Space => ((t, x) : ℝ × Space)) :=
    contDiff_const.prodMk contDiff_id
  have := ContDiffOn.comp (s := univ) h hg.contDiffOn
    (fun (x : Space) (_ : x ∈ univ) => show ((t, x) : ℝ × Space) ∈ Ici 0 ×ˢ univ from ⟨ht, trivial⟩)
  exact contDiffOn_univ.mp this

theorem divergenceAt_smul (c : ℝ) (f : Space → Space) (x : Space) :
    divergenceAt (fun y => c • f y) x = c * divergenceAt f x := by
  have hf : (fun y => c • f y) = c • f := rfl
  rw [hf]
  simp [divergenceAt, fderiv_const_smul_field, Finset.mul_sum]

theorem gradientAt_mul (c : ℝ) (p : Space → ℝ) (x : Space) :
    gradientAt (fun y => c * p y) x = c • gradientAt p x := by
  have hf : (fun y => c * p y) = c • p := rfl
  rw [hf]
  simp [gradientAt, fderiv_const_smul_field, Finset.smul_sum, smul_smul]

theorem advectionAt_smul (c : ℝ) (f : Space → Space) (x : Space) :
    advectionAt (fun y => c • f y) x = (c * c) • advectionAt f x := by
  have hf : (fun y => c • f y) = c • f := rfl
  rw [hf]
  simp [advectionAt, fderiv_const_smul_field, smul_smul]

theorem sumSecondPartialsAt_smul (c : ℝ) {f : Space → Space} (hf : ContDiff ℝ ∞ f) (x : Space) :
    sumSecondPartialsAt (fun y => c • f y) x = c • sumSecondPartialsAt f x := by
  have h2 : ContDiffAt ℝ 2 f x := hf.contDiffAt.of_le (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | norm_cast)
  simp only [sumSecondPartialsAt, iteratedFDeriv_const_smul_apply' h2, Finset.smul_sum, smul_apply]

theorem scaled_solution {ν : ℝ} (hν : 0 < ν) {u₀ : Space → Space} {v : ℝ → Space → Space}
    {q : ℝ → Space → ℝ} (h : IsSmoothSolution ν (fun x => ν • u₀ x) v q) :
    IsSmoothSolution 1 u₀ (fun t x => ν⁻¹ • v (ν⁻¹ * t) x)
      (fun t x => (ν⁻¹ * ν⁻¹) * q (ν⁻¹ * t) x) := by
  have hν0 : ν ≠ 0 := hν.ne'
  have hg : ContDiff ℝ ∞ (fun z : ℝ × Space => ((ν⁻¹ * z.1, z.2) : ℝ × Space)) :=
    (contDiff_const.mul contDiff_fst).prodMk contDiff_snd
  have hmaps : MapsTo (fun z : ℝ × Space => ((ν⁻¹ * z.1, z.2) : ℝ × Space))
      (Ici 0 ×ˢ univ) (Ici 0 ×ˢ univ) := by
    rintro ⟨t, x⟩ ⟨ht, -⟩
    exact ⟨mul_nonneg (inv_nonneg.mpr hν.le) ht, trivial⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (h.smooth_velocity.comp hg.contDiffOn hmaps).const_smul ν⁻¹
  · exact contDiffOn_const.mul (h.smooth_pressure.comp hg.contDiffOn hmaps)
  · intro x
    simp only [mul_zero, h.initial x, smul_smul, inv_mul_cancel₀ hν0, one_smul]
  · intro t ht x
    have hs : 0 < ν⁻¹ * t := mul_pos (inv_pos.mpr hν) ht
    have hsm := contDiff_slice h.smooth_velocity hs.le
    have key := h.momentum (ν⁻¹ * t) hs x
    have hd : deriv (fun τ => ν⁻¹ • v (ν⁻¹ * τ) x) t =
        ν⁻¹ • (ν⁻¹ • deriv (fun τ => v τ x) (ν⁻¹ * t)) := by
      have hfun : (fun τ => ν⁻¹ • v (ν⁻¹ * τ) x) = ν⁻¹ • (fun τ => v (ν⁻¹ * τ) x) := rfl
      rw [hfun, deriv_const_smul_field]
      congr 1
      exact deriv_comp_mul_left ν⁻¹ (fun τ => v τ x) t
    have hc : ν⁻¹ * ν⁻¹ * ν = ν⁻¹ := by field_simp
    rw [hd, advectionAt_smul, sumSecondPartialsAt_smul _ hsm, gradientAt_mul]
    set D := deriv (fun τ => v τ x) (ν⁻¹ * t)
    set A := advectionAt (v (ν⁻¹ * t)) x
    set L := sumSecondPartialsAt (v (ν⁻¹ * t)) x
    set G := gradientAt (q (ν⁻¹ * t)) x
    calc ν⁻¹ • (ν⁻¹ • D) + (ν⁻¹ * ν⁻¹) • A = (ν⁻¹ * ν⁻¹) • (D + A) := by module
      _ = (ν⁻¹ * ν⁻¹) • (ν • L - G) := by rw [key]
      _ = (ν⁻¹ * ν⁻¹ * ν) • L - (ν⁻¹ * ν⁻¹) • G := by module
      _ = (1 : ℝ) • (ν⁻¹ • L) - (ν⁻¹ * ν⁻¹) • G := by rw [hc]; module
  · intro t ht x
    have hs : 0 < ν⁻¹ * t := mul_pos (inv_pos.mpr hν) ht
    rw [divergenceAt_smul, h.incompressible _ hs x, mul_zero]

end Final.Internal

open Final.Internal in
theorem breakdownOnTorus_of_blowup (hU : MildUniqueness) (hS : SmoothPeriodicIsMild)
    (hG : MovingFrameReduction) (hB : TorusBlowup) : BreakdownOnTorus := by
  obtain ⟨u₀, hu₀, hper₀, hdiv₀, T, hT, u, hu0, hmild, hunb⟩ := hB
  intro ν hν
  refine ⟨fun x => ν • u₀ x, hu₀.const_smul ν, ?_, ?_, ?_⟩
  · intro i x
    simp only [hper₀ i x]
  · intro x
    rw [divergenceAt_smul, hdiv₀ x, mul_zero]
  · rintro ⟨v, q, hsol, hper⟩
    have hsol' := scaled_solution hν hsol
    have hper' : ∀ t ≥ 0, IsPeriodic (fun x => ν⁻¹ • v (ν⁻¹ * t) x) := by
      intro t ht i x
      simp only [hper (ν⁻¹ * t) (mul_nonneg (inv_nonneg.mpr hν.le) ht) i x]
    obtain ⟨v'', q'', hsol'', hper'', hperq''⟩ := hG u₀ _ _ hsol' hper'
    have hw := hS u₀ v'' q'' hsol'' hper'' hperq'' T hT
    have h0 : u 0 = (fun t => toV (v'' t)) 0 := by
      rw [hu0]
      show toV u₀ = toV (v'' 0)
      congr 1
      funext x
      exact (hsol''.initial x).symm
    have heq := hU u (fun t => toV (v'' t)) 0 T hmild hw h0
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hw.1
    apply hunb
    refine ⟨C, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    show ‖u t‖ ≤ C
    rw [heq ht]
    exact hC t (Ico_subset_Icc_self ht)

end Breakdown.Periodic
