import TorusEuler.Paper.Proofs.S2b.Library.Glue

/-! # Copies of the propagator estimates of Lemma 2.6 with `e ≥ 0` as a hypothesis

The bound `|Ψ₀| ≤ 2` for the propagator of the triangular system (2.16)
(`sections/03_amplification.tex:567-584`) uses `e ≥ 0`, where `e` is the function of
the form (2.13) of the reference solution `Y` (Lemma 2.5). The library estimates of the
proof of Lemma 2.6 derive `e ≥ 0` from the Riccati equation of `Y`
(`ReferenceRiccati.riccati_deviation_bounds`). The copies below take it as a hypothesis
`hdev`, which the proof of Lemma 2.6 supplies from `Statement.lemma_2_5`, and obtain the
continuity of `e` from that of `Y` (`continuousOn_deviation`, new glue) instead of from the
derivative of `e` (`ReferenceRiccati.hasDerivWithinAt_deviation`); nothing else changes
(the then unused hypotheses `0 < ε` and, where unused, `Y 0 = 1` are dropped).

| Library (namespace `TorusEuler`) | Copy (namespace `TorusEuler.Paper.Lib.S2b`) |
| --- | --- |
| `ReferenceComparison.riccati_perturbation_bounds` | `riccati_perturbation_bounds_of_dev` |
| `ReferenceComparison.raw_matrix_comparison` | `raw_matrix_comparison_of_dev` |
| `ReferenceAmplitude.normalized_close_to_growing_of_raw_matrix` | `normalized_close_to_growing_of_dev` |
| `ReferenceComparison.riccati_perturbation_norm_le_from` (private) | `riccati_perturbation_norm_le_from_of_dev` |
| `ReferenceComparison.normalizedState_norm_le_of_raw_matrix_from` | `normalizedState_norm_le_of_raw_matrix_from_of_dev` |
| `ReferenceComparison.norm_movingAmplitude_le_from` | `norm_movingAmplitude_le_from_of_dev` |
-/

open Set MeasureTheory
open scoped InnerProductSpace

namespace TorusEuler.Paper.Lib.S2b

open ReferenceRiccati ReferencePropagator ReferenceComparison ReferenceAmplitude
open MovingWaveVector MovingAmplitude

noncomputable section

/-- The library deviation `e = (Y + ετ sin 2φ/4)/cos φ - 1` (the function `e` of the form
(2.13)) of a continuous `Y` is continuous. The library copies below obtain this continuity
from the derivative of `e` (`ReferenceRiccati.hasDerivWithinAt_deviation`, the equation for
`e'` in the proof of Lemma 2.5); continuity of `Y` suffices. -/
theorem continuousOn_deviation {ε : ℝ} {Y : ℝ → ℝ} {D : Set ℝ} (hY : ContinuousOn Y D) :
    ContinuousOn (deviation ε Y) D := by
  have hs : Continuous (s ε) := continuous_iff_continuousAt.2
    (fun r => (hasDerivAt_s ε r).continuousAt)
  have hd : Continuous (fun t => damping ε t / 4) :=
    continuous_iff_continuousAt.mpr fun t => by
      have hs' := (hasDerivAt_s ε t).continuousAt
      have hx := (hasDerivAt_x ε t).continuousAt
      unfold damping
      fun_prop
  exact ((hY.add hd.continuousOn).div hs.continuousOn (fun r _ => (s_pos ε r).ne')).sub
    continuousOn_const

/-- Copy of `ReferenceComparison.riccati_perturbation_bounds` with `e ≥ 0` as a
hypothesis: the variation-of-constants bounds for the triangular system (2.16) with an
added coefficient matrix `R` (`sections/03_amplification.tex:567-584, 640-648`). -/
theorem riccati_perturbation_bounds_of_dev {ε T t : ℝ} {Y ρ : ℝ → ℝ}
    {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)} {x y : ℝ → ℝ × ℝ}
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (hdev : ∀ r ∈ Icc 0 T, 0 ≤ deviation ε Y r)
    (hR : ContinuousOn R (Icc 0 T)) (hρ : ContinuousOn ρ (Icc 0 T))
    (hRρ : ∀ r ∈ Icc 0 T, ‖R r‖ ≤ ρ r)
    (hx : ∀ r ∈ Icc 0 T, HasDerivWithinAt x
      (triangularGenerator (s ε) (deviation ε Y) r (x r) + R r (x r)) (Icc 0 T) r)
    (hy : ∀ r ∈ Icc 0 T, HasDerivWithinAt y
      (triangularGenerator (s ε) (deviation ε Y) r (y r)) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T) :
    let D := ∫ r in 0..t, ρ r
    ‖x t‖ ≤ 2 * ‖x 0‖ * Real.exp (2 * D) ∧
      ‖x t - y t‖ ≤ 2 * ‖x 0 - y 0‖ + 4 * ‖x 0‖ * Real.exp (2 * D) * D := by
  have hs : Continuous (s ε) := continuous_iff_continuousAt.2
    (fun r => (hasDerivAt_s ε r).continuousAt)
  have he : ContinuousOn (deviation ε Y) (Icc 0 T) :=
    continuousOn_deviation (HasDerivWithinAt.continuousOn hY)
  exact triangular_perturbation_bounds hs.continuousOn he (fun r _ => (s_pos ε r).le)
    hdev hR hρ hRρ hx hy ht

/-- Copy of `ReferenceComparison.raw_matrix_comparison` with `e ≥ 0` as a hypothesis:
comparison of a solution of the raw system with error `R` and a solution of the
reference system, in the normalized coordinates (2.15). -/
theorem raw_matrix_comparison_of_dev {ε T t : ℝ} {Y U V U₀ V₀ η : ℝ → ℝ}
    {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (hdev : ∀ r ∈ Icc 0 T, 0 ≤ deviation ε Y r)
    (hR : ContinuousOn R (Icc 0 T)) (hη : ContinuousOn η (Icc 0 T))
    (hRη : ∀ r ∈ Icc 0 T, ‖R r‖ ≤ η r)
    (hU : ∀ r ∈ Icc 0 T, HasDerivWithinAt U
      (-damping ε r * U r + driving ε r * V r + (R r (U r, V r)).1) (Icc 0 T) r)
    (hV : ∀ r ∈ Icc 0 T, HasDerivWithinAt V (U r + (R r (U r, V r)).2) (Icc 0 T) r)
    (hU₀ : ∀ r ∈ Icc 0 T,
      HasDerivWithinAt U₀ (-damping ε r * U₀ r + driving ε r * V₀ r) (Icc 0 T) r)
    (hV₀ : ∀ r ∈ Icc 0 T, HasDerivWithinAt V₀ (U₀ r) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T) :
    let z := normalizedState ε Y U V
    let z₀ := normalizedState ε Y U₀ V₀
    let D := ∫ r in 0..t, ((1 + |Y r|) ^ 2 / s ε r) * η r
    ‖z t‖ ≤ 2 * ‖z 0‖ * Real.exp (2 * D) ∧
      ‖z t - z₀ t‖ ≤ 2 * ‖z 0 - z₀ 0‖ + 4 * ‖z 0‖ * Real.exp (2 * D) * D := by
  have hYC := HasDerivWithinAt.continuousOn hY
  have hs : Continuous (s ε) := continuous_iff_continuousAt.2
    (fun r => (hasDerivAt_s ε r).continuousAt)
  let ρ (r : ℝ) := ((1 + |Y r|) ^ 2 / s ε r) * η r
  have hρ : ContinuousOn ρ (Icc 0 T) :=
    ((((continuousOn_const.add hYC.abs).pow 2).div hs.continuousOn
      (fun r _ => (s_pos ε r).ne')).mul hη)
  have hRρ (r : ℝ) (hr : r ∈ Icc 0 T) : ‖normalizedMatrixError ε Y R r‖ ≤ ρ r :=
    (norm_normalizedMatrixError_le ε Y R r).trans
      (mul_le_mul_of_nonneg_left (hRη r hr) (div_nonneg (sq_nonneg _) (s_pos ε r).le))
  refine riccati_perturbation_bounds_of_dev hY hdev (continuousOn_normalizedMatrixError hYC hR)
    hρ hRρ (fun r hr => hasDerivWithinAt_normalized_perturbed hY hr (hU r hr) (hV r hr)) ?_ ht
  intro r hr
  rw [triangularGenerator_apply]
  obtain ⟨hH, hL⟩ := hasDerivWithinAt_normalized hY hr (hU₀ r hr) (hV₀ r hr)
  exact hH.prodMk hL

/-- Copy of `ReferenceAmplitude.normalized_close_to_growing_of_raw_matrix` with `e ≥ 0` as
a hypothesis: the solution of the raw system with data `(U, V)(0) = (1, 1)` (that is
`(α₁, α₂)(0) = (-1, 1)`) stays close to the reference solution, `(h, l)` close to
`(1, 0)` (`sections/03_amplification.tex:649-656`). -/
theorem normalized_close_to_growing_of_dev {ε T t : ℝ} {Y U V η : ℝ → ℝ}
    {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (hY₀ : Y 0 = 1) (hU₀ : U 0 = 1) (hV₀ : V 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (hdev : ∀ r ∈ Icc 0 T, 0 ≤ deviation ε Y r)
    (hR : ContinuousOn R (Icc 0 T)) (hη : ContinuousOn η (Icc 0 T))
    (hRη : ∀ r ∈ Icc 0 T, ‖R r‖ ≤ η r)
    (hU : ∀ r ∈ Icc 0 T, HasDerivWithinAt U
      (-damping ε r * U r + driving ε r * V r + (R r (U r, V r)).1) (Icc 0 T) r)
    (hV : ∀ r ∈ Icc 0 T, HasDerivWithinAt V (U r + (R r (U r, V r)).2) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T) :
    let D := ∫ r in 0..t, ((1 + |Y r|) ^ 2 / s ε r) * η r
    ‖normalizedState ε Y U V t - (1, 0)‖ ≤ 4 * Real.exp (2 * D) * D := by
  let G := growingFactor Y
  let Ug (r : ℝ) := Y r * G r
  have hG (r : ℝ) (hr : r ∈ Icc 0 T) :
      HasDerivWithinAt G (Y r * G r) (Icc 0 T) r :=
    hasDerivWithinAt_growingFactor (HasDerivWithinAt.continuousOn hY) hr
  have hUg (r : ℝ) (hr : r ∈ Icc 0 T) : HasDerivWithinAt Ug
      (-damping ε r * Ug r + driving ε r * G r) (Icc 0 T) r := by
    refine ((hY r hr).mul (hG r hr)).congr_deriv ?_
    unfold rhs Ug
    ring
  have href (r : ℝ) : normalizedState ε Y Ug G r = (1, 0) := by
    simp [normalizedState, normalizedH, normalizedL, G, Ug, (growingFactor_pos Y r).ne']
  have hzero : normalizedState ε Y U V 0 = (1, 0) := by
    simp [normalizedState, normalizedH, normalizedL, hU₀, hV₀, hY₀]
  have hone : ‖((1, 0) : ℝ × ℝ)‖ = 1 := by norm_num [Prod.norm_def]
  have h := (raw_matrix_comparison_of_dev hY hdev hR hη hRη hU hV hUg hG ht).2
  simpa [hzero, href, hone] using h

/-- Copy of the private `ReferenceComparison.riccati_perturbation_norm_le_from` with
`e ≥ 0` as a hypothesis: the forward bound `|Ψ| ≤ 2 exp(2∫ρ)` from an arbitrary initial
time. -/
theorem riccati_perturbation_norm_le_from_of_dev {ε T a t : ℝ} {Y ρ : ℝ → ℝ}
    {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)} {z : ℝ → ℝ × ℝ}
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (hdev : ∀ r ∈ Icc 0 T, 0 ≤ deviation ε Y r)
    (ha : a ∈ Icc 0 T) (ht : t ∈ Icc a T)
    (hR : ContinuousOn R (Icc a T)) (hρ : ContinuousOn ρ (Icc a T))
    (hRρ : ∀ r ∈ Icc a T, ‖R r‖ ≤ ρ r)
    (hz : ∀ r ∈ Icc a T, HasDerivWithinAt z
      (triangularGenerator (s ε) (deviation ε Y) r (z r) + R r (z r)) (Icc a T) r) :
    ‖z t‖ ≤ 2 * ‖z a‖ * Real.exp (2 * (∫ r in a..t, ρ r)) := by
  have hsub : Icc a T ⊆ Icc 0 T := Icc_subset_Icc_left ha.1
  have hs : Continuous (s ε) := continuous_iff_continuousAt.2
    (fun r => (hasDerivAt_s ε r).continuousAt)
  have he : ContinuousOn (deviation ε Y) (Icc a T) :=
    (continuousOn_deviation (HasDerivWithinAt.continuousOn hY)).mono hsub
  have hzero (r : ℝ) (_ : r ∈ Icc a T) :
      HasDerivWithinAt (fun _ => (0 : ℝ × ℝ))
        (triangularGenerator (s ε) (deviation ε Y) r 0) (Icc a T) r := by
    simpa only [map_zero] using hasDerivWithinAt_const r (Icc a T) (0 : ℝ × ℝ)
  exact (triangular_perturbation_bounds hs.continuousOn he (fun r _ => (s_pos ε r).le)
    (fun r hr => hdev r (hsub hr)) hR hρ hRρ hz hzero ht).1

/-- Copy of `ReferenceComparison.normalizedState_norm_le_of_raw_matrix_from` with `e ≥ 0`
as a hypothesis. -/
theorem normalizedState_norm_le_of_raw_matrix_from_of_dev {ε T a t : ℝ} {Y U V η : ℝ → ℝ}
    {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (hdev : ∀ r ∈ Icc 0 T, 0 ≤ deviation ε Y r)
    (ha : a ∈ Icc 0 T) (ht : t ∈ Icc a T)
    (hR : ContinuousOn R (Icc a T)) (hη : ContinuousOn η (Icc a T))
    (hRη : ∀ r ∈ Icc a T, ‖R r‖ ≤ η r)
    (hU : ∀ r ∈ Icc 0 T, HasDerivWithinAt U
      (-damping ε r * U r + driving ε r * V r + (R r (U r, V r)).1) (Icc 0 T) r)
    (hV : ∀ r ∈ Icc 0 T, HasDerivWithinAt V (U r + (R r (U r, V r)).2) (Icc 0 T) r) :
    let z := normalizedState ε Y U V
    let D := ∫ r in a..t, ((1 + |Y r|) ^ 2 / s ε r) * η r
    ‖z t‖ ≤ 2 * ‖z a‖ * Real.exp (2 * D) := by
  have hsub : Icc a T ⊆ Icc 0 T := Icc_subset_Icc_left ha.1
  have hYC := (HasDerivWithinAt.continuousOn hY).mono hsub
  have hs : Continuous (s ε) := continuous_iff_continuousAt.2
    (fun r => (hasDerivAt_s ε r).continuousAt)
  let ρ (r : ℝ) := ((1 + |Y r|) ^ 2 / s ε r) * η r
  have hρ : ContinuousOn ρ (Icc a T) :=
    ((((continuousOn_const.add hYC.abs).pow 2).div hs.continuousOn
      (fun r _ => (s_pos ε r).ne')).mul hη)
  have hRρ (r : ℝ) (hr : r ∈ Icc a T) : ‖normalizedMatrixError ε Y R r‖ ≤ ρ r :=
    (norm_normalizedMatrixError_le ε Y R r).trans
      (mul_le_mul_of_nonneg_left (hRη r hr) (div_nonneg (sq_nonneg _) (s_pos ε r).le))
  exact riccati_perturbation_norm_le_from_of_dev hY hdev ha ht
    (continuousOn_normalizedMatrixError hYC hR) hρ hRρ
    (fun r hr => (hasDerivWithinAt_normalized_perturbed hY (hsub hr)
      (hU r (hsub hr)) (hV r (hsub hr))).mono hsub)

/-- Copy of `ReferenceComparison.norm_movingAmplitude_le_from` with `e ≥ 0` as a
hypothesis: an amplitude vector `b` with coordinates `(β₁, β₂)` of the raw system satisfies
`|b(τ₂)| ≤ 126 S exp(2D) (a_ref(τ₂)/a_ref(τ₁)) |b(τ₁)|`, from the coordinate maps `L_h`,
`L_l` and the propagator bound (`sections/03_amplification.tex:680-702`). -/
theorem norm_movingAmplitude_le_from_of_dev {e : ℝ → Fin 3 → Space} {k b : ℝ → Space}
    {ε T a t scale S : ℝ} {Y η : ℝ → ℝ} {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (hdev : ∀ r ∈ Icc 0 T, 0 ≤ deviation ε Y r)
    (ha : a ∈ Icc 0 T) (ht : t ∈ Icc a T)
    (hscale : scale ≠ 0) (hS : 1 ≤ S)
    (hGeom : ∀ r ∈ Icc a t, Orthonormal ℝ (e r) ∧ ⟪k r, b r⟫_ℝ = 0 ∧
      |X e k scale r| ≤ S ∧ |Q e k scale S r| ≤ S ∧
      1 / 2 ≤ Z e k scale r ∧ Z e k scale r ≤ 3 / 2 ∧
      |Y r| ≤ 1 ∧ |X e k scale r - x ε r| ≤ 1 / 2)
    (hR : ContinuousOn R (Icc a T)) (hη : ContinuousOn η (Icc a T))
    (hRη : ∀ r ∈ Icc a T, ‖R r‖ ≤ η r)
    (hU : ∀ r ∈ Icc 0 T, HasDerivWithinAt (U e b S)
      (-damping ε r * U e b S r + driving ε r * V e b r + (R r (U e b S r, V e b r)).1)
      (Icc 0 T) r)
    (hV : ∀ r ∈ Icc 0 T, HasDerivWithinAt (V e b)
      (U e b S r + (R r (U e b S r, V e b r)).2) (Icc 0 T) r) :
    let D := ∫ r in a..t, ((1 + |Y r|) ^ 2 / s ε r) * η r
    ‖b t‖ ≤ 126 * S * Real.exp (2 * D) * (growingFactor Y t / growingFactor Y a) * ‖b a‖ := by
  let z := normalizedState ε Y (U e b S) (V e b)
  let D := ∫ r in a..t, ((1 + |Y r|) ^ 2 / s ε r) * η r
  have hB (r : ℝ) (hr : r ∈ Icc a t) :
      ‖b r‖ ≤ 9 * growingFactor Y r * ‖z r‖ ∧
      ‖z r‖ ≤ 7 * S * (‖b r‖ / growingFactor Y r) := by
    obtain ⟨hOrth, hperp, hX, hQ, hZ₀, hZ₁, hYabs, hx⟩ := hGeom r hr
    exact norm_movingAmplitude_bounds hOrth hscale hS hperp hX hQ hZ₀ hZ₁ hYabs hx
  have hStart := (hB a (left_mem_Icc.2 ht.1)).2
  have hEnd := (hB t (right_mem_Icc.2 ht.1)).1
  have hGrowth : ‖z t‖ ≤ 2 * ‖z a‖ * Real.exp (2 * D) :=
    normalizedState_norm_le_of_raw_matrix_from_of_dev hY hdev ha ht hR hη hRη hU hV
  have hGa := growingFactor_pos Y a
  have hGt := growingFactor_pos Y t
  calc
    ‖b t‖ ≤ 9 * growingFactor Y t * ‖z t‖ := hEnd
    _ ≤ 9 * growingFactor Y t * (2 * ‖z a‖ * Real.exp (2 * D)) :=
      mul_le_mul_of_nonneg_left hGrowth (by positivity)
    _ ≤ 9 * growingFactor Y t * (2 * (7 * S * (‖b a‖ / growingFactor Y a)) * Real.exp (2 * D)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hStart (by norm_num)) (by positivity))
        (by positivity)
    _ = _ := by ring

end

end TorusEuler.Paper.Lib.S2b
