import TorusEuler.Paper.Proofs.S5b.Lemma57
import TorusEuler.Paper.Proofs.S5b.T56Bounds

/-!
# Theorem 5.6, glue: the coefficient norms from Proposition 5.1

"By (5.39) ... and the coefficient bound (5.8)" (TeX :500-503): the norms (D.1) of the
coefficients `(D_aX)⁻¹` and `κ` on any time set in `[0,T]` are at most `C_n 𝖣^C` and
`C_n 𝖣^C λ` when `ℓ_* ≤ 𝖣^{-C}`. This is (D.6) and (5.8) of **Proposition 5.1** (`h5_1`) for the
coefficients `(D_aX)⁻¹` and `κ/λ`, in the form `CoefBounds` of `T56Bounds`.
-/

open Set
open scoped ContDiff

namespace TorusEuler.Paper.S5b

open AppendixD HierarchyTwistedProfile

noncomputable section

/-- Pointwise jet bounds `‖∇^m c‖ ≤ K_m 𝖣^{C(m+1)}` (D.6) and the sup bounds (5.8) give uniform
jets and `ℓ^m ‖∇^m c‖ ≤ max(K_n,0) 𝖣^C` for `m ≤ n`. -/
theorem jets_of_bounds {I : Type} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {c : I → Vec3 → F} {ℓ D : ℝ} {K₁ : ℕ → ℝ} {C₁ : ℕ} (hℓ : 0 < ℓ) (hD : 0 < D)
    (hD6 : ∀ m, ∀ t b, ‖iteratedFDeriv ℝ m (c t) b‖ ≤ K₁ m * D ^ (C₁ * (m + 1)))
    (h58 : ∀ n, ∀ t, (∑ j ∈ Finset.range (n + 1),
      ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (c t))) ≤ K₁ n * D ^ C₁) :
    (∀ m, ∃ b, ∀ t a, ‖iteratedFDeriv ℝ m (c t) a‖ ≤ b) ∧
      ∀ n, ∀ m ≤ n, ∀ t a, ℓ ^ m * ‖iteratedFDeriv ℝ m (c t) a‖ ≤ max (K₁ n) 0 * D ^ C₁ := by
  refine ⟨fun m => ⟨K₁ m * D ^ (C₁ * (m + 1)), fun t a => hD6 m t a⟩, ?_⟩
  intro n m hm t b
  have hbdd : BddAbove (range fun x => ‖iteratedFDeriv ℝ m (c t) x‖) :=
    ⟨K₁ m * D ^ (C₁ * (m + 1)), forall_mem_range.mpr fun x => hD6 m t x⟩
  have hsup := norm_le_spatialSupNorm hbdd b
  have hterm : ℓ ^ m * spatialSupNorm (iteratedFDeriv ℝ m (c t)) ≤
      ∑ j ∈ Finset.range (n + 1), ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (c t)) :=
    Finset.single_le_sum (f := fun j => ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (c t)))
      (fun j _ => mul_nonneg (pow_nonneg hℓ.le _) (Real.iSup_nonneg fun _ => norm_nonneg _))
      (Finset.mem_range.mpr (by omega))
  calc ℓ ^ m * ‖iteratedFDeriv ℝ m (c t) b‖ ≤ ℓ ^ m * spatialSupNorm (iteratedFDeriv ℝ m (c t)) :=
        mul_le_mul_of_nonneg_left hsup (pow_nonneg hℓ.le _)
    _ ≤ K₁ n * D ^ C₁ := hterm.trans (h58 n t)
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hD.le _)

/-- **The coefficient norms** `‖(D_aX)⁻¹‖_{[n]} ≤ N_G(n)`, `‖κ‖_{[n]} ≤ N_κ(n)` on every time set
in `[0,T]` (TeX :500-503), from (D.6) and (5.8) of Proposition 5.1 (`h5_1`), when
`ℓ_* ≤ 𝖣^{-C}`; `N_G(n) = K_n 𝖣^C`, `N_κ(n) = K_n 𝖣^C λ`. -/
theorem coefBounds_of_h5_1 (h5_1 : Statement.proposition_5_1) :
    ∃ C : ℕ, ∃ K : ℕ → ℝ, (∀ n, 0 ≤ K n) ∧
      ∀ {T : ℝ} (_hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
        {D lam t₀ ℓ h : ℝ}, S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ → 0 < ℓ →
        ℓ ≤ (D ^ C)⁻¹ →
        CoefBounds T ℓ h X k (fun n => K n * D ^ C) (fun n => K n * D ^ C * lam) := by
  obtain ⟨C₁, K₁, h51⟩ := h5_1
  obtain ⟨_, h51'⟩ := h51 (fun _ => 0)
  refine ⟨C₁, fun n => ((hierarchyAdmissibleWords (Fin 3) n).card : ℝ) * max (K₁ n) 0,
    fun n => mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _), ?_⟩
  intro T hT U X pU k D lam t₀ ℓ h hP hL hℓ hℓD
  unfold CoefBounds
  intro A hA n
  obtain ⟨hD6, -, h58⟩ := h51' hT hP hL
  have hD : 1 ≤ D := Bridge.Parent.scale_ge_one hP
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hlam : 1 ≤ lam := hP.frequency_ge_one
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam
  have hB : 0 ≤ max (K₁ n) 0 * D ^ C₁ := mul_nonneg (le_max_right _ _) (pow_nonneg hD0.le _)
  have hcard : 0 ≤ ((hierarchyAdmissibleWords (Fin 3) n).card : ℝ) := Nat.cast_nonneg _
  -- the coframe
  have hGs : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (fun b => fderiv ℝ (X t 0) (X 0 t b)) := fun t ht =>
    slice_contDiff (hP.flow.contDiffOn_inverseLabelDerivative hT hP.velocity_smooth
      hP.velocity_periodic) ht
  obtain ⟨hGu, hGj⟩ := jets_of_bounds (I := A) (c := coframeC X A) (ℓ := ℓ) (D := D) (K₁ := K₁)
    (C₁ := C₁) hℓ hD0 (fun m t b => (hD6 m t (hA t.2) b).2.1)
    (fun n t => (h58 ℓ hℓ hℓD n t (hA t.2)).2.1)
  have hG := coefField_bounds (c := coframeC X A) hℓ.le h n hB (fun t => hGs t (hA t.2)) hGu
    (hGj n)
  -- the wave vector
  have hκs : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (fun b => S5.waveVector X k t b) := fun t ht =>
    slice_contDiff (Bridge.Parent.waveVector_smooth hT hP) ht
  have hκns : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (fun b => lam⁻¹ • S5.waveVector X k t b) :=
    fun t ht => (hκs t ht).const_smul lam⁻¹
  obtain ⟨hκu, hκj⟩ := jets_of_bounds (I := A)
    (c := fun (t : A) b => lam⁻¹ • S5.waveVector X k t b) (ℓ := ℓ) (D := D) (K₁ := K₁)
    (C₁ := C₁) hℓ hD0 (fun m t b => (hD6 m t (hA t.2) b).2.2.2.1)
    (fun n t => (h58 ℓ hℓ hℓD n t (hA t.2)).2.2.2.1)
  have hwave (t : A) : (waveC X k A t) = lam • fun b => lam⁻¹ • S5.waveVector X k t b := by
    funext b
    simp only [waveC, Pi.smul_apply, smul_smul, mul_inv_cancel₀ hlam0.ne', one_smul]
  have hnorm (m : ℕ) (t : A) (b : Vec3) :
      ‖iteratedFDeriv ℝ m (waveC X k A t) b‖ =
        lam * ‖iteratedFDeriv ℝ m (fun b => lam⁻¹ • S5.waveVector X k t b) b‖ := by
    have hdiffAt : ContDiffAt ℝ (m : WithTop ℕ∞) (fun b => lam⁻¹ • S5.waveVector X k t b) b :=
      ((hκns t (hA t.2)).of_le (by exact_mod_cast le_top)).contDiffAt
    rw [hwave t, iteratedFDeriv_const_smul_apply hdiffAt, norm_smul, Real.norm_of_nonneg hlam0.le]
  have hκ := coefField_bounds (c := waveC X k A) hℓ.le h n (mul_nonneg hlam0.le hB)
    (fun t => by rw [hwave t]; exact (hκns t (hA t.2)).const_smul lam)
    (fun m => by
      obtain ⟨b, hb⟩ := hκu m
      exact ⟨lam * b, fun t a => by rw [hnorm]; exact mul_le_mul_of_nonneg_left (hb t a) hlam0.le⟩)
    (fun m hm t a => by
      rw [hnorm, ← mul_assoc, mul_comm (ℓ ^ m) lam, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hκj n m hm t a) hlam0.le)
  refine ⟨⟨hG.1, ?_⟩, ⟨hκ.1, ?_⟩⟩
  · refine hG.2.trans (le_of_eq ?_)
    ring
  · refine hκ.2.trans (le_of_eq ?_)
    ring

end

end TorusEuler.Paper.S5b
