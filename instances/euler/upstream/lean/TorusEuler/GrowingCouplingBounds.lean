import TorusEuler.MovingAmplitudeCoefficients
import TorusEuler.ReferenceRatio
import TorusEuler.WaveCompletion

/-! The normalized new-frame couplings from the proof of Lemma 2.5. -/

open scoped InnerProductSpace
open NormedSpace (normalize)

namespace TorusEuler.GrowingCoupling

open MovingWaveVector
open MovingAmplitude (U V normFactor Entries)

noncomputable section

private theorem cross3_swap (u v : Space) : cross3 v u = -cross3 u v := by
  apply WithLp.ofLp_injective
  simp only [cross3, WithLp.ofLp_toLp, WithLp.ofLp_neg]
  exact (cross_anticomm u.ofLp v.ofLp).symm

private theorem cross3_self' (u : Space) : cross3 u u = 0 := by
  apply WithLp.ofLp_injective
  simp [cross3, cross_self]

private theorem cross3_add_left (u v w : Space) :
    cross3 (u + v) w = cross3 u w + cross3 v w := by
  apply WithLp.ofLp_injective
  simp only [cross3, WithLp.ofLp_add, WithLp.ofLp_toLp, map_add, LinearMap.add_apply]

private theorem cross3_add_right (u v w : Space) :
    cross3 u (v + w) = cross3 u v + cross3 u w := by
  apply WithLp.ofLp_injective
  simp only [cross3, WithLp.ofLp_add, WithLp.ofLp_toLp, map_add]

private theorem cross3_smul_left (c : ℝ) (u v : Space) :
    cross3 (c • u) v = c • cross3 u v := by
  apply WithLp.ofLp_injective
  simp only [cross3, WithLp.ofLp_smul, WithLp.ofLp_toLp, map_smul, LinearMap.smul_apply]

private theorem cross3_smul_right (c : ℝ) (u v : Space) :
    cross3 u (c • v) = c • cross3 u v := by
  apply WithLp.ofLp_injective
  simp only [cross3, WithLp.ofLp_smul, WithLp.ofLp_toLp, map_smul]

private theorem cross3_frame_coordinates {e : Fin 3 → Space}
    (he : Orthonormal ℝ e) (hOrient : cross3 (e 0) (e 1) = e 2)
    (k₁ k₂ k₃ a₁ a₂ a₃ : ℝ) :
    cross3 (k₁ • e 0 + k₂ • e 1 + k₃ • e 2) (a₁ • e 0 + a₂ • e 1 + a₃ • e 2) =
      (k₂ * a₃ - k₃ * a₂) • e 0 + (k₃ * a₁ - k₁ * a₃) • e 1 +
        (k₁ * a₂ - k₂ * a₁) • e 2 := by
  have hE := orthonormal_iff_ite.mp he
  have h12 : cross3 (e 1) (e 2) = e 0 := by
    rw [← hOrient, cross3_cross3]
    simp [hE, he.1]
  have h02 : cross3 (e 0) (e 2) = -e 1 := by
    rw [← hOrient, cross3_cross3]
    simp [hE, he.1]
  have h10 := (cross3_swap (e 0) (e 1)).trans (congrArg Neg.neg hOrient)
  have h20 := (cross3_swap (e 0) (e 2)).trans (congrArg Neg.neg h02)
  have h21 := (cross3_swap (e 1) (e 2)).trans (congrArg Neg.neg h12)
  simp only [cross3_add_left, cross3_add_right, cross3_smul_left, cross3_smul_right,
    cross3_self', smul_zero, smul_neg, hOrient, h12, h02, h10, h20, h21,
    neg_neg]
  module

/-- Scaled components of the strain applied to a transverse amplitude with
normalized coordinates `(-w / S, 1, z / S)`. -/
def forcing (A : Entries) (w z S : ℝ) : Fin 3 → ℝ :=
  ![-w * A 0 0 + S * A 0 1 + z * A 0 2,
    -w / S * A 1 0 + A 1 1 + z / S * A 1 2,
    -w * A 2 0 + S * A 2 1 + z * A 2 2]

/-- Numerators of the two normalized couplings, including both factors of two. -/
def couplingNumerators (X Q Z w z r : ℝ) (f : Fin 3 → ℝ) : ℝ × ℝ :=
  (2 * (X * f 0 + Q * f 1 + Z * f 2),
    2 * ((-Z + Q * z * r) * f 0 - (Z * w + X * z) * f 1 +
      (X + Q * w * r) * f 2))

/-- The first coupling evaluated on a strain divided by the growth rate.
The scale conversion is `r / ν = 2S`. -/
def normalizedNu (M : Space →L[ℝ] Space) (k a : Space) (S : ℝ) : ℝ :=
  (2 * S) * ⟪normalize k, M (normalize a)⟫_ℝ

/-- The second coupling evaluated on the same normalized strain. -/
def normalizedEta (M : Space →L[ℝ] Space) (k a : Space) (S : ℝ) : ℝ :=
  (2 * S) * ⟪cross3 (normalize k) (normalize a), M (normalize a)⟫_ℝ

private theorem strain_pairings (e : Fin 3 → Space) (M : Space →L[ℝ] Space)
    {w z S : ℝ} (hS : S ≠ 0) :
    let a := (-w / S) • e 0 + e 1 + (z / S) • e 2
    let f := forcing (entry e M) w z S
    ⟪e 0, M a⟫_ℝ = f 0 / S ∧
      ⟪e 1, M a⟫_ℝ = f 1 ∧
      ⟪e 2, M a⟫_ℝ = f 2 / S := by
  simp only [map_add, map_smul, inner_add_right, real_inner_smul_right, forcing,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, entry]
  exact ⟨by field_simp, trivial, by field_simp⟩

private theorem normalize_of_scaled {a v : Space} {c n : ℝ}
    (hc : c ≠ 0) (hn : n ≠ 0) (ha : a = c • v) (hnorm : ‖a‖ = c * n) :
    normalize a = n⁻¹ • v := by
  rw [NormedSpace.normalize, hnorm, ha, smul_smul]
  congr 1
  field_simp

/-- In the proof of Lemma 2.5 the new-frame couplings equal the rational
formulas in the scaled wave and amplitude coordinates. The strain is
divided by the growth rate and may include the strain error. -/
theorem normalized_couplings_eq {e : ℝ → Fin 3 → Space} {k a : ℝ → Space}
    {scale S t : ℝ} (he : Orthonormal ℝ (e t))
    (hOrient : cross3 (e t 0) (e t 1) = e t 2) (hscale : 0 < scale) (hS : 0 < S)
    (hZ : Z e k scale t ≠ 0) (hV : 0 < V e a t) (hperp : ⟪k t, a t⟫_ℝ = 0)
    (M : Space →L[ℝ] Space) :
    let x := X e k scale t
    let q := Q e k scale S t
    let zₖ := Z e k scale t
    let w := U e a S t / V e a t
    let z := (x * w - q) / zₖ
    let m := normFactor x q zₖ S
    let n := Real.sqrt (1 + (S ^ 2)⁻¹ * (w ^ 2 + z ^ 2))
    let f := forcing (entry (e t) M) w z S
    let N := couplingNumerators x q zₖ w z (S ^ 2)⁻¹ f
    normalizedNu M (k t) (a t) S = N.1 / (Real.sqrt m * n) ∧
      normalizedEta M (k t) (a t) S = N.2 / (Real.sqrt m * n ^ 2) := by
  let x := X e k scale t
  let q := Q e k scale S t
  let zₖ := Z e k scale t
  let u := U e a S t
  let v := V e a t
  let w := u / v
  let z := (x * w - q) / zₖ
  let m := normFactor x q zₖ S
  let n := Real.sqrt (1 + (S ^ 2)⁻¹ * (w ^ 2 + z ^ 2))
  let f := forcing (entry (e t) M) w z S
  let N := couplingNumerators x q zₖ w z (S ^ 2)⁻¹ f
  let K := x • e t 0 + (q / S) • e t 1 + zₖ • e t 2
  let A := (-w / S) • e t 0 + e t 1 + (z / S) • e t 2
  change normalizedNu M (k t) (a t) S = N.1 / (Real.sqrt m * n) ∧
      normalizedEta M (k t) (a t) S = N.2 / (Real.sqrt m * n ^ 2)
  have hm : 0 < m := by
    change 0 < x ^ 2 + q ^ 2 / S ^ 2 + zₖ ^ 2
    positivity
  have hn : 0 < n := by
    dsimp only [n]
    positivity
  have hK : k t = scale • K := scaled_waveVector_decomposition he hscale.ne' hS.ne'
  have hKnorm : ‖k t‖ = scale * Real.sqrt m := by
    calc
      _ = Real.sqrt (‖k t‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = _ := by
        rw [MovingAmplitude.wave_norm_sq_eq he hscale.ne' hS.ne', ← show m = _ from rfl,
          Real.sqrt_mul (sq_nonneg scale), Real.sqrt_sq hscale.le]
  have hKunit := normalize_of_scaled hscale.ne' (Real.sqrt_pos.2 hm).ne' hK hKnorm
  obtain ⟨ha₁, ha₂, ha₃⟩ := MovingAmplitude.amplitude_pairings he hscale.ne' hS.ne' hZ hperp
  let basis : OrthonormalBasis (Fin 3) ℝ Space :=
    OrthonormalBasis.mk he (he.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge
  have hb (i : Fin 3) : basis.repr (a t) i = ⟪e t i, a t⟫_ℝ := by
    simp only [OrthonormalBasis.repr_apply_apply, basis, OrthonormalBasis.coe_mk]
  have hAnorm : ‖a t‖ = v * n :=
    ReferenceAmplitude.orthonormal_physical_norm_eq basis (a t) hV hZ hS
      ((hb 0).trans ha₁) ((hb 1).trans ha₂) ((hb 2).trans ha₃)
  have hA : a t = v • A := by
    have hv : v ≠ 0 := hV.ne'
    have hzₖ : zₖ ≠ 0 := hZ
    have h₁ : -u / S = v * (-w / S) := by
      unfold w
      field_simp
    have h₃ : (x * u - q * v) / (S * zₖ) = v * (z / S) := by
      unfold z w
      field_simp
    calc
      _ = (-u / S) • e t 0 + v • e t 1 + ((x * u - q * v) / (S * zₖ)) • e t 2 :=
        MovingAmplitude.amplitude_decomposition he hscale.ne' hS.ne' hZ hperp
      _ = _ := by
        simp only [A, w, z, smul_add, smul_smul]
        rw [h₁, h₃]
  have hAunit := normalize_of_scaled hV.ne' hn.ne' hA hAnorm
  obtain ⟨hf₁, hf₂, hf₃⟩ := strain_pairings (w := w) (z := z) (e t) M hS.ne'
  change ⟪e t 0, M A⟫_ℝ = f 0 / S at hf₁
  change ⟪e t 1, M A⟫_ℝ = f 1 at hf₂
  change ⟪e t 2, M A⟫_ℝ = f 2 / S at hf₃
  have hcross :
      cross3 K A = (q * z / S ^ 2 - zₖ) • e t 0 +
        (-(zₖ * w + x * z) / S) • e t 1 + (x + q * w / S ^ 2) • e t 2 := by
    have hA' : A = (-w / S) • e t 0 + (1 : ℝ) • e t 1 + (z / S) • e t 2 := by
      simp only [A, one_smul]
    rw [hA']
    unfold K
    rw [cross3_frame_coordinates he hOrient]
    have h₁ : q / S * (z / S) - zₖ * 1 = q * z / S ^ 2 - zₖ := by ring
    have h₂ : zₖ * (-w / S) - x * (z / S) = -(zₖ * w + x * z) / S := by ring
    have h₃ : x * 1 - q / S * (-w / S) = x + q * w / S ^ 2 := by ring
    rw [h₁, h₂, h₃]
  constructor <;>
    simp only [normalizedNu, normalizedEta, hKunit, hAunit, cross3_smul_left, cross3_smul_right,
      map_smul, real_inner_smul_left, real_inner_smul_right]
  · simp only [K, inner_add_left, real_inner_smul_left, hf₁, hf₂, hf₃, N, couplingNumerators]
    field_simp
  · rw [hcross]
    simp only [inner_add_left, real_inner_smul_left, hf₁, hf₂, hf₃, N, couplingNumerators]
    field_simp
    ring

/-- The contribution of the additional strain to either normalized coupling
is bounded by its operator norm times the conversion factor `2S`. -/
theorem normalized_couplings_strain_error {k a : Space} {S : ℝ}
    (hk : k ≠ 0) (ha : a ≠ 0) (hperp : ⟪k, a⟫_ℝ = 0) (hS : 0 ≤ S)
    (M E : Space →L[ℝ] Space) :
    |normalizedNu (M + E) k a S - normalizedNu M k a S| ≤ 2 * S * ‖E‖ ∧
      |normalizedEta (M + E) k a S - normalizedEta M k a S| ≤ 2 * S * ‖E‖ := by
  have he := orthonormal_movingFrame hk ha hperp
  have h₂ : ‖cross3 (normalize k) (normalize a)‖ = 1 := he.1 2
  have hbound (v : Space) (hv : ‖v‖ = 1) :
      |(2 * S) * ⟪v, (M + E) (normalize a)⟫_ℝ -
        (2 * S) * ⟪v, M (normalize a)⟫_ℝ| ≤ 2 * S * ‖E‖ := by
    have hprod : |⟪v, E (normalize a)⟫_ℝ| ≤ ‖E‖ := by
      calc
        _ ≤ ‖v‖ * ‖E (normalize a)‖ := abs_real_inner_le_norm _ _
        _ ≤ _ := by
          rw [hv, one_mul]
          simpa only [NormedSpace.norm_normalize ha, mul_one] using E.le_opNorm (normalize a)
    have hEq :
        (2 * S) * ⟪v, (M + E) (normalize a)⟫_ℝ - (2 * S) * ⟪v, M (normalize a)⟫_ℝ =
          (2 * S) * ⟪v, E (normalize a)⟫_ℝ := by
      simp only [_root_.add_apply, inner_add_right]
      ring
    rw [hEq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * S)]
    exact mul_le_mul_of_nonneg_left hprod (by positivity)
  exact ⟨hbound _ (NormedSpace.norm_normalize hk), hbound _ h₂⟩


/-- Reference numerator values obtained by setting the scaled coordinate and
strain errors to zero in the two formulas preceding (2.10). -/
theorem couplingNumerators_reference (ε τ y : ℝ) :
    let x := ReferenceRiccati.x ε τ
    couplingNumerators x (-(ε * τ)) 1 y (x * y + ε * τ) 0 ![1 / 2, -y, ε / 2] =
      (x + ε + 2 * ε * τ * y,
        -1 + ε * x + 2 * (1 + x ^ 2) * y ^ 2 + 2 * ε * τ * x * y) := by
  simp only [couplingNumerators, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Prod.mk.injEq]
  constructor <;> ring

end

end TorusEuler.GrowingCoupling
