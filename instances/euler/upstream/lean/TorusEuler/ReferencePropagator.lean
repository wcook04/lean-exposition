import TorusEuler.LinearFlow
import TorusEuler.ReferenceRiccati
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The normalized transverse model and its forward propagator -/

open Set MeasureTheory

namespace TorusEuler.ReferencePropagator

open ReferenceRiccati

noncomputable section

private theorem hasDerivWithinAt_primitive {f : ℝ → ℝ} {a b c t : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hc : c ∈ Icc a b) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun u => ∫ r in c..u, f r) (f t) (Icc a b) t := by
  let _ : Fact (t ∈ Icc a b) := ⟨ht⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right
    (hf.mono (uIcc_subset_Icc hc ht)).intervalIntegrable
    (hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hf t ht)

/-- The growing reference factor $v_g$ normalized at time zero. -/
def growingFactor (Y : ℝ → ℝ) (t : ℝ) : ℝ := Real.exp (∫ r in 0..t, Y r)

theorem growingFactor_pos (Y : ℝ → ℝ) (t : ℝ) : 0 < growingFactor Y t := Real.exp_pos _

@[simp] theorem growingFactor_zero (Y : ℝ → ℝ) : growingFactor Y 0 = 1 := by
  simp [growingFactor]

theorem hasDerivWithinAt_growingFactor {Y : ℝ → ℝ} {T t : ℝ}
    (hY : ContinuousOn Y (Icc 0 T)) (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (growingFactor Y) (Y t * growingFactor Y t) (Icc 0 T) t := by
  unfold growingFactor
  exact (hasDerivWithinAt_primitive hY (left_mem_Icc.2 (ht.1.trans ht.2)) ht).exp.congr_deriv
    (mul_comm _ _)

/-- The first normalized component $V/v_g$. -/
def normalizedH (Y V : ℝ → ℝ) (t : ℝ) : ℝ := V t / growingFactor Y t

/-- The second normalized component $(U-YV)/(s v_g)$. -/
def normalizedL (ε : ℝ) (Y U V : ℝ → ℝ) (t : ℝ) : ℝ :=
  (U t - Y t * V t) / (s ε t * growingFactor Y t)

/-- The exact triangular system for an unperturbed transverse path, with one-sided
derivatives included at the endpoints. -/
theorem hasDerivWithinAt_normalized {ε T t : ℝ} {Y U V : ℝ → ℝ}
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T)
    (hU : HasDerivWithinAt U (-damping ε t * U t + driving ε t * V t) (Icc 0 T) t)
    (hV : HasDerivWithinAt V (U t) (Icc 0 T) t) :
    HasDerivWithinAt (normalizedH Y V) (s ε t * normalizedL ε Y U V t) (Icc 0 T) t ∧
    HasDerivWithinAt (normalizedL ε Y U V)
      (-(2 * s ε t * (1 + deviation ε Y t)) * normalizedL ε Y U V t) (Icc 0 T) t := by
  have hg := hasDerivWithinAt_growingFactor (HasDerivWithinAt.continuousOn hY) ht
  have hg₀ := (growingFactor_pos Y t).ne'
  have hs := (hasDerivAt_s ε t).hasDerivWithinAt (s := Icc 0 T)
  have hs₀ := (s_pos ε t).ne'
  have hproduct := hs.mul hg
  have hdiff := hU.sub ((hY t ht).mul hV)
  constructor
  · refine (hV.div hg hg₀).congr_deriv ?_
    unfold normalizedL
    field_simp
  · refine (hdiff.div hproduct (mul_ne_zero hs₀ hg₀)).congr_deriv ?_
    unfold rhs normalizedL deviation
    simp only [Pi.mul_apply, Pi.sub_apply]
    field_simp
    ring

/-- The diagonal coefficient of the forward propagator for the triangular system. -/
def decay (scale deviation : ℝ → ℝ) (a t : ℝ) : ℝ :=
  Real.exp (-(∫ r in a..t, 2 * scale r * (1 + deviation r)))

/-- The off-diagonal coefficient of the forward propagator for the triangular system. -/
def transfer (scale deviation : ℝ → ℝ) (a t : ℝ) : ℝ :=
  ∫ r in a..t, scale r * decay scale deviation a r

@[simp] theorem decay_self (scale deviation : ℝ → ℝ) (a : ℝ) :
    decay scale deviation a a = 1 := by simp [decay]

@[simp] theorem transfer_self (scale deviation : ℝ → ℝ) (a : ℝ) :
    transfer scale deviation a a = 0 := by simp [transfer]

theorem decay_pos (scale deviation : ℝ → ℝ) (a t : ℝ) :
    0 < decay scale deviation a t := Real.exp_pos _

private theorem hasDerivWithinAt_decay {scale e : ℝ → ℝ} {a b t : ℝ}
    (hs : ContinuousOn scale (Icc a b)) (he : ContinuousOn e (Icc a b)) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (decay scale e a)
      (-(2 * scale t * (1 + e t)) * decay scale e a t) (Icc a b) t := by
  have h : ContinuousOn (fun r => 2 * scale r * (1 + e r)) (Icc a b) :=
    (continuousOn_const.mul hs).mul (continuousOn_const.add he)
  unfold decay
  exact (hasDerivWithinAt_primitive h (left_mem_Icc.2 (ht.1.trans ht.2)) ht).neg.exp.congr_deriv
    (mul_comm _ _)

private theorem hasDerivWithinAt_transfer {scale e : ℝ → ℝ} {a b t : ℝ}
    (hs : ContinuousOn scale (Icc a b)) (he : ContinuousOn e (Icc a b)) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (transfer scale e a) (scale t * decay scale e a t) (Icc a b) t :=
  hasDerivWithinAt_primitive
    (hs.mul (HasDerivWithinAt.continuousOn (fun _ hr => hasDerivWithinAt_decay hs he hr)))
    (left_mem_Icc.2 (ht.1.trans ht.2)) ht

/-- The forward triangular propagator maps $(h(a),l(a))$ to
$(h(a)+A(a,t)l(a), B(a,t)l(a))$. -/
theorem triangular_propagator_formula {scale e h l : ℝ → ℝ} {a b : ℝ}
    (hs : ContinuousOn scale (Icc a b)) (he : ContinuousOn e (Icc a b))
    (hh : ∀ t ∈ Icc a b, HasDerivWithinAt h (scale t * l t) (Icc a b) t)
    (hl : ∀ t ∈ Icc a b, HasDerivWithinAt l (-(2 * scale t * (1 + e t)) * l t) (Icc a b) t)
    {t : ℝ} (ht : t ∈ Icc a b) :
    h t = h a + transfer scale e a t * l a ∧ l t = decay scale e a t * l a := by
  have ha : a ∈ Icc a b := left_mem_Icc.2 (ht.1.trans ht.2)
  let C (r : ℝ) : ℝ →L[ℝ] ℝ := (-(2 * scale r * (1 + e r))) • ContinuousLinearMap.id ℝ ℝ
  have hC : ContinuousOn C (Icc a b) :=
    ((continuousOn_const.mul hs).mul (continuousOn_const.add he)).neg.smul continuousOn_const
  have hl_eq : EqOn l (fun r => decay scale e a r * l a) (Icc a b) := by
    apply linearODE_unique_of_mem (A := C) ordConnected_Icc ha hC
    · simpa [C] using hl
    · intro r hr
      simpa only [C, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
        mul_assoc] using (hasDerivWithinAt_decay hs he hr).mul_const (l a)
    · simp
  have hdiff : EqOn (fun r => h r - (h a + transfer scale e a r * l a))
      (fun _ => 0) (Icc a b) := by
    apply linearODE_unique_of_mem (A := fun _ => 0) ordConnected_Icc ha continuousOn_const
    · intro r hr
      exact ((hh r hr).sub (((hasDerivWithinAt_transfer hs he hr).mul_const (l a)).const_add
        (h a))).congr_deriv (by simp [hl_eq hr, mul_assoc])
    · exact fun r _ => by simpa using hasDerivWithinAt_const r (Icc a b) (0 : ℝ)
    · simp
  exact ⟨sub_eq_zero.mp (hdiff ht), hl_eq ht⟩

/-- The off-diagonal transfer is nonnegative and consumes at most half the loss
of the decaying coefficient. -/
theorem triangular_coefficient_bounds {scale e : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hs : ContinuousOn scale (Icc a b)) (he : ContinuousOn e (Icc a b))
    (hs₀ : ∀ t ∈ Icc a b, 0 ≤ scale t) (he₀ : ∀ t ∈ Icc a b, 0 ≤ e t) :
    (0 < decay scale e a b ∧ decay scale e a b ≤ 1) ∧
      (0 ≤ transfer scale e a b ∧ transfer scale e a b ≤ (1 - decay scale e a b) / 2) := by
  have hdecay : decay scale e a b ≤ 1 := by
    rw [decay, ← Real.exp_zero, Real.exp_le_exp]
    exact neg_nonpos.mpr (intervalIntegral.integral_nonneg hab (fun r hr => by
      have := hs₀ r hr
      have := he₀ r hr
      positivity))
  have htransfer : 0 ≤ transfer scale e a b :=
    intervalIntegral.integral_nonneg hab (fun r hr =>
      mul_nonneg (hs₀ r hr) (decay_pos scale e a r).le)
  let F (r : ℝ) := 2 * transfer scale e a r + decay scale e a r
  have hF (r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivWithinAt F (-(2 * scale r * e r * decay scale e a r)) (Icc a b) r := by
    refine (((hasDerivWithinAt_transfer hs he hr).const_mul 2).add
      (hasDerivWithinAt_decay hs he hr)).congr_deriv ?_
    ring
  have hanti : AntitoneOn F (Icc a b) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
      (HasDerivWithinAt.continuousOn hF)
      (fun r hr => (hF r (interior_subset hr)).mono interior_subset) ?_
    intro r hr
    have := hs₀ r (interior_subset hr)
    have := he₀ r (interior_subset hr)
    have := (decay_pos scale e a r).le
    exact neg_nonpos.mpr (by positivity)
  have hlimit := hanti (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab
  simp [F] at hlimit
  exact ⟨⟨decay_pos scale e a b, hdecay⟩, htransfer, by linarith⟩

/-- The triangular flow contracts the sum norm on the two normalized coordinates. -/
theorem triangular_propagator_abs_add_le {scale e h l : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hs : ContinuousOn scale (Icc a b)) (he : ContinuousOn e (Icc a b))
    (hs₀ : ∀ t ∈ Icc a b, 0 ≤ scale t) (he₀ : ∀ t ∈ Icc a b, 0 ≤ e t)
    (hh : ∀ t ∈ Icc a b, HasDerivWithinAt h (scale t * l t) (Icc a b) t)
    (hl : ∀ t ∈ Icc a b, HasDerivWithinAt l (-(2 * scale t * (1 + e t)) * l t) (Icc a b) t) :
    |h b| + |l b| ≤ |h a| + |l a| := by
  obtain ⟨hhb, hlb⟩ := triangular_propagator_formula hs he hh hl (right_mem_Icc.2 hab)
  obtain ⟨⟨hB₀, hB₁⟩, hA₀, hA₁⟩ := triangular_coefficient_bounds hab hs he hs₀ he₀
  rw [hhb, hlb]
  calc
    |h a + transfer scale e a b * l a| + |decay scale e a b * l a| ≤
        |h a| + (transfer scale e a b + decay scale e a b) * |l a| := by
      have h := abs_add_le (h a) (transfer scale e a b * l a)
      rw [abs_mul, abs_of_nonneg hA₀] at h
      rw [abs_mul, abs_of_pos hB₀, add_mul]
      linarith
    _ ≤ |h a| + |l a| := by
      exact add_le_add_right (mul_le_of_le_one_left (abs_nonneg _) (by linarith)) _

/-- The forward propagator has Euclidean operator norm at most two. -/
theorem triangular_propagator_euclidean_le {scale e h l : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hs : ContinuousOn scale (Icc a b)) (he : ContinuousOn e (Icc a b))
    (hs₀ : ∀ t ∈ Icc a b, 0 ≤ scale t) (he₀ : ∀ t ∈ Icc a b, 0 ≤ e t)
    (hh : ∀ t ∈ Icc a b, HasDerivWithinAt h (scale t * l t) (Icc a b) t)
    (hl : ∀ t ∈ Icc a b, HasDerivWithinAt l (-(2 * scale t * (1 + e t)) * l t) (Icc a b) t) :
    Real.sqrt (h b ^ 2 + l b ^ 2) ≤ 2 * Real.sqrt (h a ^ 2 + l a ^ 2) := by
  have hcontract := triangular_propagator_abs_add_le hab hs he hs₀ he₀ hh hl
  have hb : (h b) ^ 2 + (l b) ^ 2 ≤ (|h b| + |l b|) ^ 2 := by
    nlinarith [sq_abs (h b), sq_abs (l b), mul_nonneg (abs_nonneg (h b)) (abs_nonneg (l b))]
  have ha : (|h a| + |l a|) ^ 2 ≤ 2 * ((h a) ^ 2 + (l a) ^ 2) := by
    nlinarith [sq_abs (h a), sq_abs (l a), sq_nonneg (|h a| - |l a|)]
  have hsq : (h b) ^ 2 + (l b) ^ 2 ≤ 2 * ((h a) ^ 2 + (l a) ^ 2) :=
    hb.trans ((pow_le_pow_left₀ (by positivity) hcontract 2).trans ha)
  rw [← Real.sqrt_sq (show 0 ≤ 2 * Real.sqrt (h a ^ 2 + l a ^ 2) by positivity)]
  apply Real.sqrt_le_sqrt
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  nlinarith [sq_nonneg (h a), sq_nonneg (l a)]

/-- The normalized transverse model obeys the Euclidean propagator bound between
any two ordered times in its interval. -/
theorem normalized_model_euclidean_le {ε T a b : ℝ} {Y U V : ℝ → ℝ}
    (hε : 0 < ε) (hY₀ : Y 0 = 1) (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) (hab : a ≤ b)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (hU : ∀ r ∈ Icc 0 T,
      HasDerivWithinAt U (-damping ε r * U r + driving ε r * V r) (Icc 0 T) r)
    (hV : ∀ r ∈ Icc 0 T, HasDerivWithinAt V (U r) (Icc 0 T) r) :
    Real.sqrt ((normalizedH Y V b) ^ 2 + (normalizedL ε Y U V b) ^ 2) ≤
      2 * Real.sqrt ((normalizedH Y V a) ^ 2 + (normalizedL ε Y U V a) ^ 2) := by
  have hsub : Icc a b ⊆ Icc 0 T := Icc_subset_Icc ha.1 hb.2
  have hs : Continuous (s ε) := continuous_iff_continuousAt.2
    (fun r => (hasDerivAt_s ε r).continuousAt)
  have he : ContinuousOn (deviation ε Y) (Icc 0 T) :=
    HasDerivWithinAt.continuousOn (fun r hr => hasDerivWithinAt_deviation (hY r hr))
  refine triangular_propagator_euclidean_le hab hs.continuousOn (he.mono hsub)
    (fun r _ => (s_pos ε r).le) (fun r hr => (riccati_deviation_bounds hε hY₀ hY r (hsub hr)).1)
    (fun r hr => ?_) (fun r hr => ?_)
  · exact (hasDerivWithinAt_normalized hY (hsub hr) (hU r (hsub hr)) (hV r (hsub hr))).1.mono hsub
  · exact (hasDerivWithinAt_normalized hY (hsub hr) (hU r (hsub hr)) (hV r (hsub hr))).2.mono hsub

end

end TorusEuler.ReferencePropagator
