import TorusEuler.ReferenceComparison
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Selected transverse amplitude and physical norm comparison -/

open Set MeasureTheory

namespace TorusEuler.ReferenceAmplitude

open ReferenceComparison ReferencePropagator
open ReferenceRiccati (s s_pos s_zero s_le_one rhs damping driving deviation hasDerivAt_s
  hasDerivWithinAt_deviation riccati_deviation_bounds)

noncomputable section

private theorem hasDerivWithinAt_primitive {f : ℝ → ℝ} {T t : ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun u => ∫ r in 0..u, f r) (f t) (Icc 0 T) t := by
  let _ : Fact (t ∈ Icc 0 T) := ⟨ht⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right
    ((hf.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1)
    (hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hf t ht)

/-- The decaying kernel for the solution with initial raw amplitudes $(0,1)$. -/
def kernel (ε : ℝ) (Y : ℝ → ℝ) (t : ℝ) : ℝ := s ε t * decay (s ε) (deviation ε Y) 0 t

/-- The time integral of the kernel in the selected seed. -/
def kernelIntegral (ε : ℝ) (Y : ℝ → ℝ) (t : ℝ) : ℝ := transfer (s ε) (deviation ε Y) 0 t

/-- The selected seed, whose initial raw amplitudes are $(0,1)$. -/
def selectedV (ε : ℝ) (Y : ℝ → ℝ) (t : ℝ) : ℝ :=
  growingFactor Y t * (1 - kernelIntegral ε Y t)

def selectedU (ε : ℝ) (Y : ℝ → ℝ) (t : ℝ) : ℝ :=
  growingFactor Y t * (Y t * (1 - kernelIntegral ε Y t) - kernel ε Y t)

@[simp] theorem kernel_zero (ε : ℝ) (Y : ℝ → ℝ) : kernel ε Y 0 = 1 := by simp [kernel]

@[simp] theorem kernelIntegral_zero (ε : ℝ) (Y : ℝ → ℝ) : kernelIntegral ε Y 0 = 0 := by
  simp [kernelIntegral]

@[simp] theorem selectedV_zero (ε : ℝ) (Y : ℝ → ℝ) : selectedV ε Y 0 = 1 := by
  simp [selectedV]

theorem selectedU_zero {ε : ℝ} {Y : ℝ → ℝ} (hY₀ : Y 0 = 1) : selectedU ε Y 0 = 0 := by
  simp [selectedU, hY₀]

private theorem continuous_s (ε : ℝ) : Continuous (s ε) :=
  continuous_iff_continuousAt.2 (fun t => (hasDerivAt_s ε t).continuousAt)

private theorem continuousOn_deviation {ε T : ℝ} {Y : ℝ → ℝ}
    (hY : ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε t (Y t)) (Icc 0 T) t) :
    ContinuousOn (deviation ε Y) (Icc 0 T) :=
  HasDerivWithinAt.continuousOn (fun t ht => hasDerivWithinAt_deviation (hY t ht))

private theorem hasDerivWithinAt_kernel_decay {ε T t : ℝ} {Y : ℝ → ℝ}
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (decay (s ε) (deviation ε Y) 0)
      (-(2 * s ε t * (1 + deviation ε Y t)) * decay (s ε) (deviation ε Y) 0 t) (Icc 0 T) t := by
  have hC : ContinuousOn (fun r => 2 * s ε r * (1 + deviation ε Y r)) (Icc 0 T) :=
    (continuousOn_const.mul (continuous_s ε).continuousOn).mul
      (continuousOn_const.add (continuousOn_deviation hY))
  unfold decay
  exact (hasDerivWithinAt_primitive hC ht).neg.exp.congr_deriv (mul_comm _ _)

theorem hasDerivWithinAt_kernel {ε T t : ℝ} {Y : ℝ → ℝ}
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (kernel ε Y) (-(2 * Y t + damping ε t) * kernel ε Y t) (Icc 0 T) t := by
  unfold kernel
  refine ((hasDerivAt_s ε t).hasDerivWithinAt.mul
    (hasDerivWithinAt_kernel_decay hY ht)).congr_deriv ?_
  unfold deviation
  field_simp [(s_pos ε t).ne']
  ring_nf

theorem hasDerivWithinAt_kernelIntegral {ε T t : ℝ} {Y : ℝ → ℝ}
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (kernelIntegral ε Y) (kernel ε Y t) (Icc 0 T) t :=
  hasDerivWithinAt_primitive
    (HasDerivWithinAt.continuousOn (fun _ hr => hasDerivWithinAt_kernel hY hr)) ht

theorem kernel_eq_exp {ε T t : ℝ} {Y : ℝ → ℝ}
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T) :
    kernel ε Y t = Real.exp (-(∫ r in 0..t, 2 * Y r + damping ε r)) := by
  let c (r : ℝ) := 2 * Y r + damping ε r
  let A (r : ℝ) : ℝ →L[ℝ] ℝ := (-c r) • ContinuousLinearMap.id ℝ ℝ
  have hc : ContinuousOn c (Icc 0 T) := by
    refine ((HasDerivWithinAt.continuousOn hY).const_mul 2).add ?_
    unfold damping
    have hx : Continuous (ReferenceRiccati.x ε) := continuous_iff_continuousAt.2
      (fun r => (ReferenceRiccati.hasDerivAt_x ε r).continuousAt)
    exact ((continuousOn_id.const_mul (2 * ε)).mul hx.continuousOn).mul
      ((continuous_s ε).continuousOn.pow 2)
  have hA : ContinuousOn A (Icc 0 T) := hc.neg.smul continuousOn_const
  have hEq := linearODE_unique_of_mem (A := A) ordConnected_Icc
    (left_mem_Icc.2 (ht.1.trans ht.2)) hA
    (fun r hr => by simpa [A, c] using hasDerivWithinAt_kernel hY hr)
    (y := fun r => Real.exp (-(∫ u in 0..r, c u)))
    (fun r hr => by
      refine (hasDerivWithinAt_primitive hc hr).neg.exp.congr_deriv ?_
      simp [A, mul_comm]) (by simp [c])
  exact hEq ht

theorem kernel_bounds {ε T t : ℝ} {Y : ℝ → ℝ} (hε : 0 < ε) (hY₀ : Y 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r) (ht : t ∈ Icc 0 T) :
    (0 < kernel ε Y t ∧ kernel ε Y t ≤ 1) ∧
    (0 ≤ kernelIntegral ε Y t ∧ kernelIntegral ε Y t ≤ 1 / 2) := by
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  obtain ⟨⟨hB₀, hB₁⟩, hA₀, hA₁⟩ := triangular_coefficient_bounds ht.1
    (continuous_s ε).continuousOn ((continuousOn_deviation hY).mono hsub)
    (fun r _ => (s_pos ε r).le) (fun r hr => (riccati_deviation_bounds hε hY₀ hY r (hsub hr)).1)
  exact ⟨⟨mul_pos (s_pos ε t) hB₀, mul_le_one₀ (s_le_one ε t) hB₀.le hB₁⟩,
    hA₀, hA₁.trans (by linarith)⟩

theorem selectedV_pos {ε T t : ℝ} {Y : ℝ → ℝ} (hε : 0 < ε) (hY₀ : Y 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r) (ht : t ∈ Icc 0 T) :
    0 < selectedV ε Y t :=
  mul_pos (growingFactor_pos Y t) (by linarith [(kernel_bounds hε hY₀ hY ht).2.2])

theorem selected_seed_solves {ε T t : ℝ} {Y : ℝ → ℝ}
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r) (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (selectedU ε Y)
      (-damping ε t * selectedU ε Y t + driving ε t * selectedV ε Y t) (Icc 0 T) t ∧
    HasDerivWithinAt (selectedV ε Y) (selectedU ε Y t) (Icc 0 T) t := by
  have hg := hasDerivWithinAt_growingFactor (HasDerivWithinAt.continuousOn hY) ht
  have hI := (hasDerivWithinAt_kernelIntegral hY ht).const_sub 1
  constructor
  · refine (hg.mul (((hY t ht).mul hI).sub (hasDerivWithinAt_kernel hY ht))).congr_deriv ?_
    simp only [rhs, selectedU, selectedV, Pi.mul_apply, Pi.sub_apply]
    ring
  · refine (hg.mul hI).congr_deriv ?_
    simp only [selectedU]
    ring

theorem hasDerivWithinAt_log_selectedV {ε T t : ℝ} {Y : ℝ → ℝ} (hε : 0 < ε) (hY₀ : Y 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r) (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun r => Real.log (selectedV ε Y r))
      (Y t - kernel ε Y t / (1 - kernelIntegral ε Y t)) (Icc 0 T) t := by
  refine ((selected_seed_solves hY ht).2.log (selectedV_pos hε hY₀ hY ht).ne').congr_deriv ?_
  have hI : 1 - kernelIntegral ε Y t ≠ 0 := by linarith [(kernel_bounds hε hY₀ hY ht).2.2]
  unfold selectedU selectedV
  field_simp [(growingFactor_pos Y t).ne']

theorem normalizedState_selected (ε : ℝ) (Y : ℝ → ℝ) (t : ℝ) :
    normalizedState ε Y (selectedU ε Y) (selectedV ε Y) t =
      (1 - kernelIntegral ε Y t, -decay (s ε) (deviation ε Y) 0 t) := by
  have hg := (growingFactor_pos Y t).ne'
  have hs := (s_pos ε t).ne'
  simp only [normalizedState, normalizedH, normalizedL, selectedU, selectedV, Prod.mk.injEq]
  constructor
  · field_simp
  · unfold kernel
    field_simp
    ring

private theorem abs_fst_le_norm (p : ℝ × ℝ) : |p.1| ≤ ‖p‖ := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact le_max_left _ _

private theorem abs_snd_le_norm (p : ℝ × ℝ) : |p.2| ≤ ‖p‖ := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact le_max_right _ _

/-- Closeness of the triangular states gives the two normalized raw component errors. -/
theorem raw_components_of_normalized_close {ε t δ : ℝ} {Y U V : ℝ → ℝ}
    (hclose : ‖normalizedState ε Y U V t -
      normalizedState ε Y (selectedU ε Y) (selectedV ε Y) t‖ ≤ δ) :
    |V t / growingFactor Y t - (1 - kernelIntegral ε Y t)| ≤ δ ∧
      |V t / growingFactor Y t - (1 - kernelIntegral ε Y t)| +
        |U t / growingFactor Y t - Y t * (1 - kernelIntegral ε Y t) + kernel ε Y t| ≤
        (1 + |Y t| + s ε t) * δ := by
  rw [normalizedState_selected] at hclose
  have hh : |normalizedH Y V t - (1 - kernelIntegral ε Y t)| ≤ δ :=
    (abs_fst_le_norm _).trans hclose
  have hl : |normalizedL ε Y U V t + decay (s ε) (deviation ε Y) 0 t| ≤ δ := by
    rw [← sub_neg_eq_add]
    exact (abs_snd_le_norm _).trans hclose
  have hEq : U t / growingFactor Y t - Y t * (1 - kernelIntegral ε Y t) + kernel ε Y t =
      Y t * (normalizedH Y V t - (1 - kernelIntegral ε Y t)) +
        s ε t * (normalizedL ε Y U V t + decay (s ε) (deviation ε Y) 0 t) := by
    unfold normalizedH normalizedL kernel
    field_simp [(growingFactor_pos Y t).ne', (s_pos ε t).ne']
    ring
  refine ⟨hh, ?_⟩
  rw [hEq]
  calc
    _ ≤ δ + (|Y t| * δ + s ε t * δ) := by
      refine add_le_add hh ((abs_add_le _ _).trans ?_)
      rw [abs_mul, abs_mul, abs_of_pos (s_pos ε t)]
      exact add_le_add (mul_le_mul_of_nonneg_left hh (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hl (s_pos ε t).le)
    _ = (1 + |Y t| + s ε t) * δ := by ring

/-- The physical transverse component remains positive under the comparison. -/
theorem transverse_pos_of_normalized_close {ε T t δ : ℝ} {Y U V : ℝ → ℝ}
    (hε : 0 < ε) (hY₀ : Y 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T) (hδ : δ < 1 / 2)
    (hclose : ‖normalizedState ε Y U V t -
      normalizedState ε Y (selectedU ε Y) (selectedV ε Y) t‖ ≤ δ) :
    1 / 2 - δ ≤ V t / growingFactor Y t ∧ 0 < V t := by
  have hh := (abs_le.mp (raw_components_of_normalized_close hclose).1).1
  have hI := (kernel_bounds hε hY₀ hY ht).2.2
  have hLower : 1 / 2 - δ ≤ V t / growingFactor Y t := by linarith
  exact ⟨hLower, (div_pos_iff_of_pos_right (growingFactor_pos Y t)).1
    ((sub_pos.mpr hδ).trans_le hLower)⟩

/-- The raw amplitude ratio in terms of the two normalized components. -/
theorem raw_ratio_eq {ε t : ℝ} {Y U V : ℝ → ℝ} (hV : V t ≠ 0) :
    U t / V t = Y t + s ε t * (normalizedL ε Y U V t / normalizedH Y V t) := by
  unfold normalizedL normalizedH
  field_simp [hV, (growingFactor_pos Y t).ne', (s_pos ε t).ne']
  ring

/-- The comparison starts at the physical unit seed, so its initial error vanishes. -/
theorem normalized_close_to_selected_of_raw_matrix {ε T t : ℝ} {Y U V η : ℝ → ℝ}
    {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (hε : 0 < ε) (hY₀ : Y 0 = 1) (hU₀ : U 0 = 0) (hV₀ : V 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (hR : ContinuousOn R (Icc 0 T)) (hη : ContinuousOn η (Icc 0 T))
    (hRη : ∀ r ∈ Icc 0 T, ‖R r‖ ≤ η r)
    (hU : ∀ r ∈ Icc 0 T, HasDerivWithinAt U
      (-damping ε r * U r + driving ε r * V r + (R r (U r, V r)).1) (Icc 0 T) r)
    (hV : ∀ r ∈ Icc 0 T, HasDerivWithinAt V (U r + (R r (U r, V r)).2) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T) :
    let D := ∫ r in 0..t, ((1 + |Y r|) ^ 2 / s ε r) * η r
    ‖normalizedState ε Y U V t - normalizedState ε Y (selectedU ε Y) (selectedV ε Y) t‖ ≤
      4 * Real.exp (2 * D) * D := by
  have hB := (raw_matrix_comparison hε hY₀ hY hR hη hRη hU hV
    (fun r hr => (selected_seed_solves hY hr).1) (fun r hr => (selected_seed_solves hY hr).2) ht).2
  have hzero : normalizedState ε Y U V 0 = (1, -1) := by
    simp [normalizedState, normalizedH, normalizedL, hU₀, hV₀, hY₀]
  have hN : ‖((1, -1) : ℝ × ℝ)‖ = 1 := by
    norm_num [Prod.norm_def]
  simpa [hzero, normalizedState_selected, hN] using hB

/-- The growing polarization of Lemma 2.5 starts at $(U,V)=(1,1)$, so its
reference state in the triangular coordinates is the constant pair $(1,0)$. -/
theorem normalized_close_to_growing_of_raw_matrix {ε T t : ℝ} {Y U V η : ℝ → ℝ}
    {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (hε : 0 < ε) (hY₀ : Y 0 = 1) (hU₀ : U 0 = 1) (hV₀ : V 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
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
  have h := (raw_matrix_comparison hε hY₀ hY hR hη hRη hU hV hUg hG ht).2
  simpa [hzero, href, hone] using h

/-- The nonnegative correction from the first and third moving-frame components. -/
def normCorrection (X Q Z U V : ℝ) : ℝ :=
  (U / V) ^ 2 + ((X * (U / V) - Q) / Z) ^ 2

theorem normCorrection_nonneg (X Q Z U V : ℝ) : 0 ≤ normCorrection X Q Z U V := by
  unfold normCorrection
  positivity

/-- The physical norm of the three moving-frame components when the transverse
component and the shear parameter are positive. -/
theorem physical_norm_eq {X Q Z U V S : ℝ} (hV : 0 < V) (hZ : Z ≠ 0) (hS : 0 < S) :
    Real.sqrt ((-U / S) ^ 2 + V ^ 2 + ((X * U - Q * V) / (S * Z)) ^ 2) =
      V * Real.sqrt (1 + (S ^ 2)⁻¹ * normCorrection X Q Z U V) := by
  calc
    _ = Real.sqrt (V ^ 2 * (1 + (S ^ 2)⁻¹ * normCorrection X Q Z U V)) := by
      congr 1
      unfold normCorrection
      field_simp [hV.ne', hZ, hS.ne']
      ring
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg V), Real.sqrt_sq hV.le]

/-- The same physical norm identity in any supplied orthonormal moving frame. -/
theorem orthonormal_physical_norm_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : OrthonormalBasis (Fin 3) ℝ E) (a : E) {X Q Z U V S : ℝ}
    (hV : 0 < V) (hZ : Z ≠ 0) (hS : 0 < S)
    (h₀ : B.repr a 0 = -U / S) (h₁ : B.repr a 1 = V)
    (h₂ : B.repr a 2 = (X * U - Q * V) / (S * Z)) :
    ‖a‖ = V * Real.sqrt (1 + (S ^ 2)⁻¹ * normCorrection X Q Z U V) := by
  calc
    ‖a‖ = ‖B.repr a‖ := (B.repr.norm_map a).symm
    _ = Real.sqrt (‖B.repr a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt ((-U / S) ^ 2 + V ^ 2 + ((X * U - Q * V) / (S * Z)) ^ 2) := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, h₀, h₁, h₂]
    _ = _ := physical_norm_eq hV hZ hS

/-- The amplitude with a geometric correction to its transverse component. -/
def physicalAmplitude (g h F : ℝ → ℝ) (φ t : ℝ) : ℝ :=
  g t * h t * Real.sqrt (1 + φ * F t)

private theorem abs_log_ratio_le {a b m δ : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b)
    (hδ : |a - b| ≤ δ) : |Real.log (a / b)| ≤ δ / m := by
  have ha₀ := hm.trans_le ha
  have hb₀ := hm.trans_le hb
  have hδ₀ := (abs_nonneg _).trans hδ
  have hUpper (x y : ℝ) (hx : 0 < x) (hy : m ≤ y) (hxy : x - y ≤ δ) :
      Real.log (x / y) ≤ δ / m := by
    have hy₀ := hm.trans_le hy
    calc
      Real.log (x / y) ≤ x / y - 1 := Real.log_le_sub_one_of_pos (div_pos hx hy₀)
      _ = (x - y) / y := by rw [sub_div, div_self hy₀.ne']
      _ ≤ δ / y := div_le_div_of_nonneg_right hxy hy₀.le
      _ ≤ δ / m := div_le_div_of_nonneg_left hδ₀ hm hy
  refine abs_le.mpr ⟨?_, hUpper a b ha₀ hb ((abs_le.mp hδ).2)⟩
  have hrev := hUpper b a hb₀ ha (by linarith [(abs_le.mp hδ).1])
  rw [Real.log_div hb₀.ne' ha₀.ne'] at hrev
  rw [Real.log_div ha₀.ne' hb₀.ne']
  linarith

/-- A positive normalized transverse component and a nonnegative geometry
correction control the logarithmic value error. -/
theorem log_amplitude_ratio_le {g h h₀ F φ m δ : ℝ} (hg : 0 < g) (hm : 0 < m)
    (hh : m ≤ h) (hh₀ : m ≤ h₀) (hclose : |h - h₀| ≤ δ) (hφ : 0 ≤ φ) (hF : 0 ≤ F) :
    |Real.log ((g * h * Real.sqrt (1 + φ * F)) / (g * h₀))| ≤ δ / m + φ * F / 2 := by
  have hhpos := hm.trans_le hh
  have hh₀pos := hm.trans_le hh₀
  have hB : 0 < 1 + φ * F := by positivity
  have hEq : g * h * Real.sqrt (1 + φ * F) / (g * h₀) =
      (h / h₀) * Real.sqrt (1 + φ * F) := by
    field_simp [hg.ne', hh₀pos.ne']
  rw [hEq, Real.log_mul (div_pos hhpos hh₀pos).ne' (Real.sqrt_pos.2 hB).ne', Real.log_sqrt hB.le]
  refine (abs_add_le _ _).trans (add_le_add (abs_log_ratio_le hm hh hh₀ hclose) ?_)
  have hnonneg := Real.log_nonneg (show 1 ≤ 1 + φ * F by linarith [mul_nonneg hφ hF])
  rw [abs_of_nonneg (div_nonneg hnonneg (by norm_num))]
  linarith [Real.log_le_sub_one_of_pos hB]

/-- The exact logarithmic derivative of the physical amplitude and its reference,
after separating the common growing factor. -/
theorem hasDerivWithinAt_log_physicalAmplitude {g h F : ℝ → ℝ} {J : Set ℝ}
    {φ t g' h' F' : ℝ} (ht : t ∈ J) (hg₀ : ∀ r ∈ J, 0 < g r)
    (hh₀ : ∀ r ∈ J, 0 < h r) (hφ : 0 ≤ φ) (hF₀ : ∀ r ∈ J, 0 ≤ F r)
    (hg : HasDerivWithinAt g g' J t) (hh : HasDerivWithinAt h h' J t)
    (hF : HasDerivWithinAt F F' J t) :
    HasDerivWithinAt (fun r => Real.log (physicalAmplitude g h F φ r))
      (g' / g t + h' / h t + φ * F' / (2 * (1 + φ * F t))) J t := by
  have hB (r : ℝ) (hr : r ∈ J) : 0 < 1 + φ * F r := by
    have := hF₀ r hr
    positivity
  have hbracket := (((hF.const_mul φ).const_add 1).log (hB t ht).ne').div_const 2
  refine (((hg.log (hg₀ t ht).ne').add (hh.log (hh₀ t ht).ne')).add hbracket).congr_of_mem ?_ ht
    |>.congr_deriv ?_
  · intro r hr
    rw [physicalAmplitude, Real.log_mul (mul_pos (hg₀ r hr) (hh₀ r hr)).ne'
      (Real.sqrt_pos.2 (hB r hr)).ne', Real.log_mul (hg₀ r hr).ne' (hh₀ r hr).ne',
      Real.log_sqrt (hB r hr).le]
    rfl
  · rw [div_div, mul_comm (1 + φ * F t) 2]

/-- Quantitative comparison of the logarithmic rates once the normalized
components and their time derivatives are close. -/
theorem log_amplitude_rate_error_le {h h₀ h' h₀' F F' φ m δ δ' : ℝ}
    (hm : 0 < m) (hh : m ≤ h) (hh₀ : 1 / 2 ≤ h₀) (hclose : |h - h₀| ≤ δ)
    (hclose' : |h' - h₀'| ≤ δ') (hφ : 0 ≤ φ) (hF : 0 ≤ F) :
    |h' / h + φ * F' / (2 * (1 + φ * F)) - h₀' / h₀| ≤
      (δ' + 2 * |h₀'| * δ) / m + φ * |F'| / 2 := by
  have hhpos := hm.trans_le hh
  have hh₀pos : 0 < h₀ := by linarith
  have hδ₀ := (abs_nonneg _).trans hclose
  have hδ'₀ := (abs_nonneg _).trans hclose'
  have hB : 0 < 1 + φ * F := by positivity
  have hEq : h' / h + φ * F' / (2 * (1 + φ * F)) - h₀' / h₀ =
      ((h' - h₀') / h + h₀' * (h₀ - h) / (h * h₀)) + φ * F' / (2 * (1 + φ * F)) := by
    field_simp [hhpos.ne', hh₀pos.ne', hB.ne']
    ring
  have hInv : |h₀'| * δ / (h * h₀) ≤ (2 * |h₀'| * δ) / m := by
    have hdenom : m / 2 ≤ h * h₀ := by
      linarith [mul_le_mul hh hh₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhpos.le]
    calc
      |h₀'| * δ / (h * h₀) ≤ |h₀'| * δ / (m / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) hδ₀) (by positivity) hdenom
      _ = (2 * |h₀'| * δ) / m := by ring
  have hR : |(h' - h₀') / h + h₀' * (h₀ - h) / (h * h₀)| ≤ (δ' + 2 * |h₀'| * δ) / m := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, abs_of_pos hhpos, abs_div, abs_mul, abs_sub_comm h₀ h,
      abs_of_pos (mul_pos hhpos hh₀pos), add_div]
    exact add_le_add ((div_le_div_of_nonneg_right hclose' hhpos.le).trans
      (div_le_div_of_nonneg_left hδ'₀ hm hh))
      ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hclose (abs_nonneg _))
        (mul_pos hhpos hh₀pos).le).trans hInv)
  have hCorr : |φ * F' / (2 * (1 + φ * F))| ≤ φ * |F'| / 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg hφ, abs_of_pos (mul_pos (by norm_num) hB)]
    exact div_le_div_of_nonneg_left (mul_nonneg hφ (abs_nonneg _)) (by norm_num)
      (by linarith [mul_nonneg hφ hF])
  rw [hEq]
  exact (abs_add_le _ _).trans (add_le_add hR hCorr)

/-- The first normalized derivative differs from the selected rate by the
second-component error and the actual matrix forcing. -/
theorem normalized_transverse_derivative_error {ε T t δ : ℝ} {Y U V : ℝ → ℝ}
    {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T)
    (hU : HasDerivWithinAt U
      (-damping ε t * U t + driving ε t * V t + (R t (U t, V t)).1) (Icc 0 T) t)
    (hV : HasDerivWithinAt V (U t + (R t (U t, V t)).2) (Icc 0 T) t)
    (hclose : ‖normalizedState ε Y U V t -
      normalizedState ε Y (selectedU ε Y) (selectedV ε Y) t‖ ≤ δ) :
    let z := normalizedState ε Y U V t
    let R₁ := normalizedMatrixError ε Y R t
    let d := s ε t * z.2 + (R₁ z).1
    HasDerivWithinAt (normalizedH Y V) d (Icc 0 T) t ∧
      |d + kernel ε Y t| ≤ δ + ‖R₁‖ * ‖z‖ := by
  dsimp only
  constructor
  · have h := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt t
      (hasDerivWithinAt_normalized_perturbed hY ht hU hV)
    simpa [Function.comp_def, normalizedState] using h
  · let z := normalizedState ε Y U V t
    let R₁ := normalizedMatrixError ε Y R t
    let B := decay (s ε) (deviation ε Y) 0 t
    have hl : |z.2 + B| ≤ δ := by
      rw [normalizedState_selected] at hclose
      have h := (abs_snd_le_norm (z - (1 - kernelIntegral ε Y t, -B))).trans hclose
      change |z.2 - (-B)| ≤ δ at h
      simpa only [sub_neg_eq_add] using h
    change |s ε t * z.2 + (R₁ z).1 + s ε t * B| ≤ δ + ‖R₁‖ * ‖z‖
    rw [show s ε t * z.2 + (R₁ z).1 + s ε t * B = s ε t * (z.2 + B) + (R₁ z).1 by ring]
    refine (abs_add_le _ _).trans (add_le_add ?_ ((abs_fst_le_norm _).trans (R₁.le_opNorm _)))
    rw [abs_mul, abs_of_pos (s_pos ε t)]
    exact (mul_le_of_le_one_left (abs_nonneg _) (s_le_one ε t)).trans hl

/-- The selected seed gives a common positive reference for the physical
logarithmic value and rate estimates. Here `F` is the nonnegative norm correction. -/
theorem selected_log_comparison {ε T t δ δ' φ h' F' : ℝ} {Y U V F : ℝ → ℝ}
    (hε : 0 < ε) (hY₀ : Y 0 = 1) (hδ₀ : 0 ≤ δ) (hδ : δ < 1 / 2) (hφ : 0 ≤ φ)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (hclose : ∀ r ∈ Icc 0 T, ‖normalizedState ε Y U V r -
      normalizedState ε Y (selectedU ε Y) (selectedV ε Y) r‖ ≤ δ)
    (hF₀ : ∀ r ∈ Icc 0 T, 0 ≤ F r) (ht : t ∈ Icc 0 T)
    (hh : HasDerivWithinAt (normalizedH Y V) h' (Icc 0 T) t)
    (hF : HasDerivWithinAt F F' (Icc 0 T) t) (herr' : |h' + kernel ε Y t| ≤ δ') :
    let A := physicalAmplitude (growingFactor Y) (normalizedH Y V) F φ
    let m := 1 / 2 - δ
    let h₀ := 1 - kernelIntegral ε Y t
    let q := h' / normalizedH Y V t + φ * F' / (2 * (1 + φ * F t))
    |Real.log (A t / selectedV ε Y t)| ≤ δ / m + φ * F t / 2 ∧
      HasDerivWithinAt (fun r => Real.log (A r)) (Y t + q) (Icc 0 T) t ∧
      |q + kernel ε Y t / h₀| ≤ (δ' + 2 * kernel ε Y t * δ) / m + φ * |F'| / 2 := by
  have hhalf (r : ℝ) (hr : r ∈ Icc 0 T) : 1 / 2 ≤ 1 - kernelIntegral ε Y r := by
    linarith [(kernel_bounds hε hY₀ hY hr).2.2]
  have hm : 0 < 1 / 2 - δ := sub_pos.mpr hδ
  have hH (r : ℝ) (hr : r ∈ Icc 0 T) : 1 / 2 - δ ≤ normalizedH Y V r :=
    (transverse_pos_of_normalized_close hε hY₀ hY hr hδ (hclose r hr)).1
  have hh₀ : 1 / 2 - δ ≤ 1 - kernelIntegral ε Y t := by linarith [hhalf t ht]
  have herr : |normalizedH Y V t - (1 - kernelIntegral ε Y t)| ≤ δ :=
    (raw_components_of_normalized_close (hclose t ht)).1
  refine ⟨log_amplitude_ratio_le (growingFactor_pos Y t) hm (hH t ht) hh₀ herr hφ (hF₀ t ht),
    ?_, ?_⟩
  · refine (hasDerivWithinAt_log_physicalAmplitude ht (fun r _ => growingFactor_pos Y r)
      (fun r hr => hm.trans_le (hH r hr)) hφ hF₀
      (hasDerivWithinAt_growingFactor (HasDerivWithinAt.continuousOn hY) ht) hh hF).congr_deriv ?_
    rw [mul_div_cancel_right₀ _ (growingFactor_pos Y t).ne']
    ring
  · have hK := (kernel_bounds hε hY₀ hY ht).1.1
    simpa only [sub_neg_eq_add, neg_div, abs_neg, abs_of_pos hK] using
      log_amplitude_rate_error_le (h₀' := -kernel ε Y t) hm (hH t ht) (hhalf t ht) herr
        (by simpa only [sub_neg_eq_add] using herr') hφ (hF₀ t ht) (F' := F')

/-- The growing reference factor reaches its maximum where its logarithmic
derivative changes sign. -/
theorem growingFactor_isMaxOn_of_sign {Y : ℝ → ℝ} {T p : ℝ} (hp : p ∈ Icc 0 T)
    (hY : ContinuousOn Y (Icc 0 T)) (hleft : ∀ r ∈ Ioo 0 p, 0 ≤ Y r)
    (hright : ∀ r ∈ Ioo p T, Y r ≤ 0) : IsMaxOn (growingFactor Y) (Icc 0 T) p := by
  have hg (r : ℝ) (hr : r ∈ Icc 0 T) :
      HasDerivWithinAt (growingFactor Y) (Y r * growingFactor Y r) (Icc 0 T) r :=
    hasDerivWithinAt_growingFactor hY hr
  have hL : Icc 0 p ⊆ Icc 0 T := Icc_subset_Icc_right hp.2
  have hR : Icc p T ⊆ Icc 0 T := Icc_subset_Icc_left hp.1
  have hUp : MonotoneOn (growingFactor Y) (Icc 0 p) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 p)
      ((HasDerivWithinAt.continuousOn hg).mono hL)
      (fun r hr => (hg r (hL (interior_subset hr))).mono (interior_subset.trans hL)) ?_
    intro r hr
    rw [interior_Icc] at hr
    exact mul_nonneg (hleft r hr) (growingFactor_pos Y r).le
  have hDown : AntitoneOn (growingFactor Y) (Icc p T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc p T)
      ((HasDerivWithinAt.continuousOn hg).mono hR)
      (fun r hr => (hg r (hR (interior_subset hr))).mono (interior_subset.trans hR)) ?_
    intro r hr
    rw [interior_Icc] at hr
    exact mul_nonpos_of_nonpos_of_nonneg (hright r hr) (growingFactor_pos Y r).le
  apply isMaxOn_iff.2
  intro r hr
  rcases le_total r p with h | h
  · exact hUp ⟨hr.1, h⟩ ⟨hp.1, le_rfl⟩ h
  · exact hDown ⟨le_rfl, hp.2⟩ ⟨h, hr.2⟩ h

/-- Pointwise log closeness to the selected seed bounds the actual peak gain.
The loss of at most `log 2` is the loss from selecting the physical unit seed. -/
theorem peak_log_gain_bounds {ε T a p δ : ℝ} {Y A : ℝ → ℝ} (hε : 0 < ε) (hY₀ : Y 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (ha : a ∈ Icc 0 T) (hp : p ∈ Icc 0 T) (hA : ∀ r ∈ Icc 0 T, 0 < A r)
    (hclose : ∀ r ∈ Icc 0 T, |Real.log (A r / selectedV ε Y r)| ≤ δ)
    (hmaxA : IsMaxOn A (Icc 0 T) a) (hmaxG : IsMaxOn (growingFactor Y) (Icc 0 T) p) :
    -(Real.log 2 + δ) ≤ Real.log (A a) - Real.log (growingFactor Y p) ∧
      Real.log (A a) - Real.log (growingFactor Y p) ≤ δ := by
  have hC (r : ℝ) (hr : r ∈ Icc 0 T) :
      |Real.log (A r) - Real.log (selectedV ε Y r)| ≤ δ := by
    rw [← Real.log_div (hA r hr).ne' (selectedV_pos hε hY₀ hY hr).ne']
    exact hclose r hr
  have hGle (r : ℝ) (hr : r ∈ Icc 0 T) :
      growingFactor Y r / 2 ≤ selectedV ε Y r ∧ selectedV ε Y r ≤ growingFactor Y r := by
    obtain ⟨_, hI₀, hI⟩ := kernel_bounds hε hY₀ hY hr
    have hG := (growingFactor_pos Y r).le
    unfold selectedV
    constructor
    · have hh : 1 / 2 ≤ 1 - kernelIntegral ε Y r := by linarith
      linarith [mul_le_mul_of_nonneg_left hh hG]
    · exact mul_le_of_le_one_right hG (by linarith)
  have hGa := Real.log_le_log (selectedV_pos hε hY₀ hY ha)
    ((hGle a ha).2.trans (isMaxOn_iff.1 hmaxG a ha))
  have hGp := Real.log_le_log (div_pos (growingFactor_pos Y p) (by norm_num : 0 < (2 : ℝ)))
    (hGle p hp).1
  rw [Real.log_div (growingFactor_pos Y p).ne' (by norm_num)] at hGp
  have hAp := Real.log_le_log (hA p hp) (isMaxOn_iff.1 hmaxA p hp)
  exact ⟨by linarith [(abs_le.mp (hC p hp)).1], by linarith [(abs_le.mp (hC a ha)).2]⟩

/-- Early comparison and the two strict derivative signs localize every maximum
to the closed peak window. The statement also applies directly to log amplitude. -/
theorem peak_mem_window_of_signs {A A' : ℝ → ℝ} {T c p q w a : ℝ}
    (hc : 0 ≤ c) (hcp : c ≤ p) (hpq : p ≤ q) (hqT : q ≤ T)
    (hw : w ∈ Icc 0 T) (ha : a ∈ Icc 0 T) (hmax : IsMaxOn A (Icc 0 T) a)
    (hD : ∀ r ∈ Icc 0 T, HasDerivWithinAt A (A' r) (Icc 0 T) r)
    (hearly : ∀ r ∈ Ico 0 c, A r < A w)
    (hleft : ∀ r ∈ Ioo c p, 0 < A' r) (hright : ∀ r ∈ Ioo q T, A' r < 0) :
    a ∈ Icc p q := by
  have hsubL : Icc c p ⊆ Icc 0 T := Icc_subset_Icc hc (hpq.trans hqT)
  have hsubR : Icc q T ⊆ Icc 0 T := Icc_subset_Icc_left (hc.trans (hcp.trans hpq))
  have hUp : StrictMonoOn A (Icc c p) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc c p)
      ((HasDerivWithinAt.continuousOn hD).mono hsubL)
      (fun r hr => (hD r (hsubL (interior_subset hr))).mono (interior_subset.trans hsubL)) ?_
    intro r hr
    rw [interior_Icc] at hr
    exact hleft r hr
  have hDown : StrictAntiOn A (Icc q T) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc q T)
      ((HasDerivWithinAt.continuousOn hD).mono hsubR)
      (fun r hr => (hD r (hsubR (interior_subset hr))).mono (interior_subset.trans hsubR)) ?_
    intro r hr
    rw [interior_Icc] at hr
    exact hright r hr
  have hmax' := isMaxOn_iff.1 hmax
  have hca : c ≤ a := le_of_not_gt (fun h => (not_lt_of_ge (hmax' w hw)) (hearly a ⟨ha.1, h⟩))
  constructor
  · exact le_of_not_gt (fun h =>
      (not_lt_of_ge (hmax' p (hsubL ⟨hcp, le_rfl⟩))) (hUp ⟨hca, h.le⟩ ⟨hcp, le_rfl⟩ h))
  · exact le_of_not_gt (fun h =>
      (not_lt_of_ge (hmax' q (hsubR ⟨le_rfl, hqT⟩))) (hDown ⟨le_rfl, hqT⟩ ⟨h.le, ha.2⟩ h))

/-- A continuous positive amplitude can be normalized to any prescribed positive peak. -/
theorem exists_positive_peak_normalization {A : ℝ → ℝ} {T Ustar : ℝ} (hT : 0 ≤ T)
    (hA : ContinuousOn A (Icc 0 T)) (hpos : ∀ r ∈ Icc 0 T, 0 < A r) (hUstar : 0 < Ustar) :
    ∃ a ∈ Icc 0 T, ∃ c > 0, c * A a = Ustar ∧ ∀ r ∈ Icc 0 T, c * A r ≤ Ustar := by
  obtain ⟨a, ha, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, hT⟩ hA
  have ha₀ := hpos a ha
  have hnorm : Ustar / A a * A a = Ustar := div_mul_cancel₀ _ ha₀.ne'
  refine ⟨a, ha, Ustar / A a, div_pos hUstar ha₀, hnorm, ?_⟩
  intro r hr
  calc
    _ ≤ Ustar / A a * A a :=
      mul_le_mul_of_nonneg_left (isMaxOn_iff.1 hmax r hr) (div_pos hUstar ha₀).le
    _ = Ustar := hnorm

end

end TorusEuler.ReferenceAmplitude
