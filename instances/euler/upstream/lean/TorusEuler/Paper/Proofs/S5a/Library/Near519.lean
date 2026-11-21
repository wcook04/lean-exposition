import TorusEuler.Paper.Proofs.S5a.Library.Seed519

/-!
# S5a library: (5.19) for every seed, from Proposition 5.1

Route of the TeX proof of Lemma 5.3 to (5.19) (`sections/06c_finite_hierarchy.tex:105-158`):
the first label derivatives (D.6) of the coefficients (hypothesis `h5_1`) give the label-Lipschitz
bounds, `Lib.S5a.exists_seedOn_of_D6` constructs the seed with the near-origin bounds, and
`Bridge.IsSeed.eqOn_amplitude` identifies every `S5.IsSeed` with it (linear ODE uniqueness).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5a

noncomputable section

open HierarchyTwistedProfile LocalizedAmplitude

/-- The near-origin bounds `SeedNear` (strictly stronger than (5.19)) for every `S5.IsSeed`, with a
Lipschitz constant `Cs(D)` depending only on `D`, for `ℓ ≤ 𝖣^{-A}`; from the case `m = 1` of
(D.6) in `h5_1`. -/
theorem seedNear_of_h51 (h5_1 : Statement.proposition_5_1) :
    ∃ A : ℕ, 3 ≤ A ∧ ∃ Cs : ℝ → ℝ,
      ∀ {T D lam t₀ ell : ℝ} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
        {center : ℝ → Vec3},
        0 < T → S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ →
        S5.Origin T U X k D lam t₀ center → 0 < ell → ell ≤ (D ^ A)⁻¹ →
        ∀ amp : ℝ → Vec3 → Vec3, S5.IsSeed U X k t₀ T center amp →
          Bridge.SeedNear (Bridge.seedStrain U X) (Bridge.seedCovector X k) center t₀ T ell D
            (Cs D) amp := by
  obtain ⟨C, K, hK⟩ := h5_1
  obtain ⟨Kf, hKf⟩ := hK (fun _ => 0)
  let c : ℝ := max (K 1) 0
  obtain ⟨A, hA, hSeed⟩ := exists_seedOn_of_D6 c (le_max_right _ _) (C * 2)
  refine ⟨A, hA, fun D => amplitudeLabelSlope D (c * D ^ (C * 2 + 2)) (c * D ^ (C * 2 + 2))
    (c * D ^ (C * 2 + 2)) (c * D ^ (C * 2 + 2)), ?_⟩
  intro T D lam t₀ ell U X pU k center hT hP hL hO hell hellA amp hamp
  have hD6 := (hKf hT hP hL).1
  have hcD : ∀ x : ℝ, x ≤ K 1 * D ^ (C * (1 + 1)) → x ≤ c * D ^ (C * 2) := by
    intro x hx
    have hD0 : 0 ≤ D ^ (C * 2) := pow_nonneg (by linarith [hP.scale_ge_two]) _
    exact hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hD0)
  obtain ⟨w⟩ := hSeed hT hP hL hO (fun t ht a => by
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hD6 1 t ht a
      exact ⟨hcD _ h1, hcD _ h2, hcD _ h3, hcD _ h4, hcD _ h6⟩) hell hellA
  have hEq := Bridge.IsSeed.eqOn_amplitude hP hL hamp w
  exact Bridge.seedNear_of_eqOn (Bridge.seedOn_seedNear w) (fun t ht a => hEq t ht a)

end

end TorusEuler.Paper.Lib.S5a
