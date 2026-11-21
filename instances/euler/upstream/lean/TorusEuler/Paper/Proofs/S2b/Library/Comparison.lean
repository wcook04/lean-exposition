import TorusEuler.Paper.Proofs.S2b.Library.Propagator

/-! # Glue for the proof of Lemma 2.6: coordinate bounds and the norm of the amplitude

Two routine steps of the proof of Lemma 2.6 (`sections/03_amplification.tex:663-672`),
in namespace `TorusEuler.Paper.Lib.S2b`: the coordinate bounds `|X| ≤ T²`, `|Q| ≤ T`
from `|ζ - ζ₀| ≤ 1/2` (`geometry_of_close`, new glue), and the second bound of (2.17)
from closeness of the normalized coordinates to `(1, 0)` (`norm_bounds_of_state_close`,
the `hnorm`/`hF` step of the library lemma `ReferenceAmplitude.log_growing_physical_norm_le`
stated on its own).
-/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper.Lib.S2b

open MovingWaveVector MovingAmplitude ReferenceRiccati ReferenceAmplitude ReferencePropagator
  ReferenceComparison

/-- The coordinate bounds `|X| ≤ T²`, `|Q| ≤ T` from `|ζ - ζ₀| ≤ 1/2` (first bound of
(2.10)) and `x = ετ²/2 ≤ T²/4`, `ετ ≤ T/2` for `ε ≤ 1/2`. -/
theorem geometry_of_close {ε T τ X Q : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1 / 2) (hT : 2 ≤ T)
    (hτ : τ ∈ Icc 0 T) (hX : |X - x ε τ| ≤ 1 / 2) (hQ : |Q + ε * τ| ≤ 1 / 2) :
    |X| ≤ T ^ 2 ∧ |Q| ≤ T := by
  have hx0 := x_nonneg hε τ
  have hττ : τ ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hτ.1 hτ.2 2
  have hxT : x ε τ ≤ T ^ 2 / 4 := by
    unfold x
    nlinarith [mul_le_mul hε₁ hττ (sq_nonneg τ) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hετ0 : 0 ≤ ε * τ := mul_nonneg hε hτ.1
  have hετ : ε * τ ≤ T / 2 := by nlinarith [mul_le_mul hε₁ hτ.2 hτ.1 (by norm_num)]
  obtain ⟨hX1, hX2⟩ := abs_le.mp hX
  obtain ⟨hQ1, hQ2⟩ := abs_le.mp hQ
  exact ⟨abs_le.mpr ⟨by nlinarith, by nlinarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- The second bound of (2.17) in the library coordinates: closeness of the normalized
coordinates `(h, l)` to `(1, 0)` gives `V ≤ |a| ≤ (1 + 40T⁴S⁻²)V`. This is the identity
`|a|² = α₂² + S⁻²(α₁² + α₃²)` (`sections/03_amplification.tex:663-672`) with the bound
`|α₁| ≤ 2α₂` and the geometry of the wave vector. The steps are those of the library
lemma `ReferenceAmplitude.log_growing_physical_norm_le`, which uses the same bound
without stating it. -/
theorem norm_bounds_of_state_close {e : ℝ → Fin 3 → Space} {k a : ℝ → Space}
    {Y : ℝ → ℝ} {ε t scale S T δ : ℝ}
    (he : Orthonormal ℝ (e t)) (hscale : scale ≠ 0) (hS : 0 < S)
    (hperp : ⟪k t, a t⟫_ℝ = 0) (hT : 1 ≤ T) (hX : |X e k scale t| ≤ T ^ 2)
    (hQ : |Q e k scale S t| ≤ T) (hZ : 1 / 2 ≤ Z e k scale t)
    (hY : |Y t| ≤ 1) (hδ : δ ≤ 1 / 2)
    (hclose : ‖normalizedState ε Y (U e a S) (V e a) t - (1, 0)‖ ≤ δ) :
    V e a t ≤ ‖a t‖ ∧ ‖a t‖ ≤ (1 + 40 * T ^ 4 * (S ^ 2)⁻¹) * V e a t := by
  obtain ⟨hV, hratio⟩ := raw_ratio_close_of_growing_state_close hδ hclose
  have hw : |U e a S t / V e a t| ≤ 2 := by
    calc
      _ = |U e a S t / V e a t - Y t + Y t| := by rw [sub_add_cancel]
      _ ≤ |U e a S t / V e a t - Y t| + |Y t| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hZ₀ : Z e k scale t ≠ 0 := by linarith
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ Space := by simp
  let B := OrthonormalBasis.mk he (he.linearIndependent.span_eq_top_of_card_eq_finrank hcard).ge
  have hB (i : Fin 3) : B.repr (a t) i = ⟪e t i, a t⟫_ℝ := by
    simp only [B, OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_mk]
  obtain ⟨h₀, h₁, h₂⟩ := amplitude_pairings he hscale hS.ne' hZ₀ hperp
  set F := normCorrection (X e k scale t) (Q e k scale S t) (Z e k scale t) (U e a S t)
    (V e a t) with hFdef
  have hF : F ≤ 40 * T ^ 4 := normCorrection_le_of_growing_geometry hT hX hQ hZ hw
  have hF0 : 0 ≤ F := normCorrection_nonneg _ _ _ _ _
  have hnorm : ‖a t‖ = V e a t * Real.sqrt (1 + (S ^ 2)⁻¹ * F) :=
    orthonormal_physical_norm_eq B (a t) hV hZ₀ hS
      ((hB 0).trans h₀) ((hB 1).trans h₁) ((hB 2).trans h₂)
  have hφ : 0 ≤ (S ^ 2)⁻¹ := by positivity
  have hx : 0 ≤ (S ^ 2)⁻¹ * F := mul_nonneg hφ hF0
  have hs1 : 1 ≤ Real.sqrt (1 + (S ^ 2)⁻¹ * F) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + (S ^ 2)⁻¹ * F by linarith)
    rwa [Real.sqrt_one] at h
  have hs2 : Real.sqrt (1 + (S ^ 2)⁻¹ * F) ≤ 1 + (S ^ 2)⁻¹ * F := by
    calc
      _ ≤ Real.sqrt ((1 + (S ^ 2)⁻¹ * F) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = _ := Real.sqrt_sq (by linarith)
  have hs3 : (S ^ 2)⁻¹ * F ≤ 40 * T ^ 4 * (S ^ 2)⁻¹ := by
    rw [mul_comm (40 * T ^ 4)]
    exact mul_le_mul_of_nonneg_left hF hφ
  rw [hnorm]
  constructor
  · exact le_mul_of_one_le_right hV.le hs1
  · rw [mul_comm (1 + 40 * T ^ 4 * (S ^ 2)⁻¹)]
    exact mul_le_mul_of_nonneg_left
      (hs2.trans (by linarith : 1 + (S ^ 2)⁻¹ * F ≤ 1 + 40 * T ^ 4 * (S ^ 2)⁻¹)) hV.le

end TorusEuler.Paper.Lib.S2b
