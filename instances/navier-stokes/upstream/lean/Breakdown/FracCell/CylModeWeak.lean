import Breakdown.FracCell.CylChange
import Breakdown.FracCell.AxisWeak

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert CellAnalysis

private def pw (N : ℤ) (q : ℝ × ℝ) : ℂ :=
  ((q.1 : ℂ) - (q.2 : ℂ) * Complex.I) ^ N.toNat * ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ^ (-N).toNat

private theorem pw_smooth (N : ℤ) : ContDiff ℝ ∞ (pw N) := by
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ => (q.1 : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ ∞ (fun q : ℝ × ℝ => (q.2 : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_snd
  exact ((h1.sub (h2.mul contDiff_const)).pow _).mul ((h1.add (h2.mul contDiff_const)).pow _)

private theorem pw_circle (N : ℤ) (θ : ℝ) :
    pw N (Real.cos θ, Real.sin θ) = Complex.exp (-((N : ℝ) * θ : ℝ) * Complex.I) := by
  have e1 : ((Real.cos θ : ℝ) : ℂ) - ((Real.sin θ : ℝ) : ℂ) * Complex.I = Complex.exp ((-(θ : ℂ)) * Complex.I) := by
    rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos, Complex.ofReal_sin]; ring
  have e2 : ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hN : ((N.toNat : ℕ) : ℂ) - (((-N).toNat : ℕ) : ℂ) = (N : ℂ) := by
    exact_mod_cast Int.toNat_sub_toNat_neg N
  simp only [pw]
  rw [e1, e2, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  rw [← hN]
  ring

private def wt {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : ℝ × ℝ → (F →L[ℝ] ℝ)) (N : ℤ)
    (q : ℝ × ℝ) : F →L[ℝ] ℂ :=
  (L q).smulRight (pw N q)

private theorem rad_cyl {r : ℝ} (hr : 0 < r) (θ z : ℝ) : cylRadius (cylPoint r θ z) = r := by
  have h0 : (cylPoint r θ z) 0 = r * Real.cos θ := by simp [cylPoint]
  have h1 : (cylPoint r θ z) 1 = r * Real.sin θ := by simp [cylPoint]
  unfold cylRadius
  rw [h0, h1, show (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 by
    linear_combination r ^ 2 * Real.cos_sq_add_sin_sq θ, Real.sqrt_sq hr.le]

private theorem cyl_ratio {r : ℝ} (hr : 0 < r) (θ z : ℝ) :
    (cylPoint r θ z) 0 / cylRadius (cylPoint r θ z) = Real.cos θ ∧
      (cylPoint r θ z) 1 / cylRadius (cylPoint r θ z) = Real.sin θ ∧ (cylPoint r θ z) 2 = z := by
  rw [rad_cyl hr]
  refine ⟨?_, ?_, ?_⟩ <;> simp [cylPoint, hr.ne']

private theorem cylPull (h1 : CylChangeStatement) (a : ℝ × ℝ → ℝ) (ha : ∀ p, a p ≠ 0 → 0 < p.1) (K : Space → ℂ)
    (hi : Integrable (fun y => ((a (cylRadius y, y 2) / cylRadius y : ℝ) : ℂ) * K y)) :
    ∫ y, ((a (cylRadius y, y 2) / cylRadius y : ℝ) : ℂ) * K y =
      ∫ p, (a p : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), K (cylPoint p.1 θ p.2) := by
  rw [h1 _ hi, setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ)
    (g := fun p => (a p : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), K (cylPoint p.1 θ p.2)) ?_,
    setIntegral_eq_integral_of_forall_compl_eq_zero ?_]
  · intro p hp
    have hp' : a p = 0 := by
      by_contra hne
      exact hp ⟨ha p hne, Set.mem_univ _⟩
    simp [hp']
  · intro p hp
    have hp1 : 0 < p.1 := hp.1
    have e : ∀ θ, ((a (cylRadius (cylPoint p.1 θ p.2), (cylPoint p.1 θ p.2) 2) /
        cylRadius (cylPoint p.1 θ p.2) : ℝ) : ℂ) = ((a p / p.1 : ℝ) : ℂ) := fun θ => by
      rw [rad_cyl hp1, (cyl_ratio hp1 θ p.2).2.2]
    simp only [e, intervalIntegral.integral_const_mul]
    have : (p.1 : ℂ) ≠ 0 := by exact_mod_cast hp1.ne'
    push_cast
    field_simp

private theorem congr_p (a : ℝ × ℝ → ℝ) (ha : ∀ p, a p ≠ 0 → 0 < p.1) (A B : ℝ × ℝ → ℝ → ℂ)
    (h : ∀ p, 0 < p.1 → ∀ θ, A p θ = B p θ) :
    ∫ p, (a p : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), A p θ =
      ∫ p, (a p : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), B p θ := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  by_cases hp : a p = 0
  · simp [hp]
  · simp only
    rw [intervalIntegral.integral_congr (fun θ _ => h p (ha p hp) θ)]

private theorem supp_of {a : ℝ × ℝ → ℝ} (h : ∀ p ∈ tsupport a, 0 < p.1) : ∀ p, a p ≠ 0 → 0 < p.1 :=
  fun p hp => h p (subset_tsupport _ hp)

theorem cylModeWeak_of (h1 : CylChangeStatement) (h2 : AxisWeakStatement) : CylModeWeakStatement := by
  intro F _ _ _ _ f g hf hg hw L hL m n ψ hψ hc hpos
  set N : ℤ := n * m with hNdef
  have hW : ContDiff ℝ ∞ (wt L N) := hL.smulRight (pw_smooth N)
  have hwc : ∀ θ (u : F), wt L N (Real.cos θ, Real.sin θ) u =
      Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (L (Real.cos θ, Real.sin θ) u : ℂ) := by
    intro θ u
    simp only [wt, ContinuousLinearMap.smulRight_apply, Complex.real_smul, pw_circle, azimuth, hNdef]
    push_cast
    ring
  obtain ⟨⟨i1, i2, i3, i4⟩, eR, eZ⟩ := h2 F f g hf hg hw (wt L N) hW ψ hψ hc hpos
  have sψ := supp_of hpos
  have sr := supp_of (fun p hp => hpos p (tsupport_fderiv_apply_subset ℝ (1, 0) hp))
  have sz := supp_of (fun p hp => hpos p (tsupport_fderiv_apply_subset ℝ (0, 1) hp))
  have kf : ∀ p : ℝ × ℝ, 0 < p.1 → ∀ θ,
      Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (L (Real.cos θ, Real.sin θ) (f (cylPoint p.1 θ p.2)) : ℂ) =
        wt L N ((cylPoint p.1 θ p.2) 0 / cylRadius (cylPoint p.1 θ p.2),
          (cylPoint p.1 θ p.2) 1 / cylRadius (cylPoint p.1 θ p.2)) (f (cylPoint p.1 θ p.2)) := by
    intro p hp θ
    rw [(cyl_ratio hp θ p.2).1, (cyl_ratio hp θ p.2).2.1, hwc]
  have kr : ∀ p : ℝ × ℝ, 0 < p.1 → ∀ θ,
      Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
          (L (Real.cos θ, Real.sin θ) (g (cylPoint p.1 θ p.2) (radialUnit θ)) : ℂ) =
        wt L N ((cylPoint p.1 θ p.2) 0 / cylRadius (cylPoint p.1 θ p.2),
          (cylPoint p.1 θ p.2) 1 / cylRadius (cylPoint p.1 θ p.2))
          (g (cylPoint p.1 θ p.2) (EuclideanSpace.single 0 ((cylPoint p.1 θ p.2) 0 / cylRadius (cylPoint p.1 θ p.2)) +
            EuclideanSpace.single 1 ((cylPoint p.1 θ p.2) 1 / cylRadius (cylPoint p.1 θ p.2)))) := by
    intro p hp θ
    rw [(cyl_ratio hp θ p.2).1, (cyl_ratio hp θ p.2).2.1, hwc]
    rfl
  have kz : ∀ p : ℝ × ℝ, 0 < p.1 → ∀ θ,
      Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
          (L (Real.cos θ, Real.sin θ) (g (cylPoint p.1 θ p.2) axialUnit) : ℂ) =
        wt L N ((cylPoint p.1 θ p.2) 0 / cylRadius (cylPoint p.1 θ p.2),
          (cylPoint p.1 θ p.2) 1 / cylRadius (cylPoint p.1 θ p.2)) (g (cylPoint p.1 θ p.2) axialUnit) := by
    intro p hp θ
    rw [(cyl_ratio hp θ p.2).1, (cyl_ratio hp θ p.2).2.1, hwc]
  refine ⟨?_, ?_⟩
  · rw [congr_p _ sr _ _ kf, congr_p _ sψ _ _ kr, ← cylPull h1 _ sr _ i1, ← cylPull h1 _ sψ _ i3]
    exact eR
  · rw [congr_p _ sz _ _ kf, congr_p _ sψ _ _ kz, ← cylPull h1 _ sz _ i2, ← cylPull h1 _ sψ _ i4]
    exact eZ

theorem cylModeWeak : CylModeWeakStatement :=
  cylModeWeak_of cylChange axisWeak

end Breakdown.CellCert.CellFormula
