import TorusEuler.EndpointSmoothSlices
import TorusEuler.FourierHolderTail
import TorusEuler.Piola
import TorusEuler.PeriodicLift
import TorusEuler.ParentResidualEstimates
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! Reflection-compatible outputs for the physical endpoint mean equation. -/

open ContinuousLinearMap MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "TimeSlab(" T ")" => Icc (0 : ℝ) T
local notation "LiftSlab(" T ")" => (Set.prod (TimeSlab(T)) (univ : Set Vec3))

section Reflection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The reflection projection with sign `-1` for vectors and `1` for pressure. -/
def endpointParityPart (sign : ℝ) (f : Vec3 → E) (x : Vec3) : E :=
  (1 / 2 : ℝ) • (f x + sign • f (-x))

def endpointTimeParityPart (sign : ℝ) (f : ℝ → Vec3 → E) (t : ℝ) : Vec3 → E :=
  endpointParityPart sign (f t)

theorem endpointParityPart_const_smul (sign c : ℝ) (f : Vec3 → E) :
    endpointParityPart sign (c • f) = c • endpointParityPart sign f := by
  funext x
  simp only [endpointParityPart, Pi.smul_apply]
  rw [smul_comm sign c, ← smul_add, smul_comm (1 / 2 : ℝ) c]

theorem odd_endpointParityPart (f : Vec3 → E) : Function.Odd (endpointParityPart (-1) f) := by
  intro x
  simp only [endpointParityPart, neg_neg, neg_one_smul, ← smul_neg]
  congr 1
  abel

theorem even_endpointParityPart (f : Vec3 → E) : Function.Even (endpointParityPart 1 f) := by
  intro x
  simp only [endpointParityPart, neg_neg, one_smul, add_comm]

private theorem endpointParity_latticeVector_neg (n : Fin 3 → ℤ) :
    latticeVector (-n) = -latticeVector n := by
  apply PiLp.ext
  intro i
  simp only [latticeVector, PiLp.neg_apply, PiLp.toLp_apply, Pi.neg_apply, Int.cast_neg]

theorem spatiallyPeriodic_endpointParityPart {f : Vec3 → E} (hf : SpatiallyPeriodic f)
    (sign : ℝ) : SpatiallyPeriodic (endpointParityPart sign f) := by
  intro n x
  rw [endpointParityPart, endpointParityPart, hf n x, neg_add_rev,
    add_comm (-latticeVector n), ← endpointParity_latticeVector_neg, hf (-n) (-x)]

private theorem contDiffOn_endpointReflectedLift {T : ℝ} {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) LiftSlab(T)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => f z.1 (-z.2)) LiftSlab(T) :=
  hf.comp (contDiff_fst.prodMk contDiff_snd.neg).contDiffOn
    (fun _ hz => ⟨hz.1, mem_univ _⟩)

theorem contDiffOn_endpointTimeParityPart {T : ℝ} {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) LiftSlab(T)) (sign : ℝ) :
    ContDiffOn ℝ ∞ (Function.uncurry (endpointTimeParityPart sign f)) LiftSlab(T) :=
  (hf.add ((contDiffOn_endpointReflectedLift hf).const_smul sign)).const_smul (1 / 2 : ℝ)

private theorem endpointParity_contDiff_slice {T t : ℝ} {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) LiftSlab(T)) (ht : t ∈ TimeSlab(T)) :
    ContDiff ℝ ∞ (f t) := by
  apply contDiffOn_univ.mp
  exact hf.comp (contDiffOn_const.prodMk contDiffOn_id) (fun x _ => ⟨ht, mem_univ x⟩)

theorem hasDerivWithinAt_endpointTimeParityPart {T t : ℝ} {f : ℝ → Vec3 → E}
    {x : Vec3} {a b : E} (sign : ℝ)
    (hx : HasDerivWithinAt (fun r => f r x) a TimeSlab(T) t)
    (hneg : HasDerivWithinAt (fun r => f r (-x)) b TimeSlab(T) t) :
    HasDerivWithinAt (fun r => endpointTimeParityPart sign f r x)
      ((1 / 2 : ℝ) • (a + sign • b)) TimeSlab(T) t :=
  (hx.add (hneg.const_smul sign)).const_smul (1 / 2 : ℝ)

private theorem hasFDerivAt_endpointParityPart {f : Vec3 → E} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) (hneg : DifferentiableAt ℝ f (-x)) (sign : ℝ) :
    HasFDerivAt (endpointParityPart sign f)
      ((1 / 2 : ℝ) • (fderiv ℝ f x + (-sign) • fderiv ℝ f (-x))) x := by
  have hR : HasFDerivAt (fun y => f (-y)) (-fderiv ℝ f (-x)) x := by
    have h := hneg.hasFDerivAt.comp x (hasFDerivAt_id x).neg
    refine h.congr_fderiv ?_
    ext z
    simp
  have h := (hf.hasFDerivAt.add (hR.const_smul sign)).const_smul (1 / 2 : ℝ)
  exact h.congr_fderiv (by rw [smul_neg, neg_smul])

private theorem divergence_endpointOddPart {f : Vec3 → Vec3} {x : Vec3}
    (hf : Differentiable ℝ f) :
    divergence (endpointParityPart (-1) f) x =
      (1 / 2 : ℝ) * (divergence f x + divergence f (-x)) := by
  rw [divergence_eq_trace_fderiv, divergence_eq_trace_fderiv, divergence_eq_trace_fderiv,
    (hasFDerivAt_endpointParityPart (hf x) (hf (-x)) (-1)).fderiv, neg_neg, one_smul]
  change LinearMap.trace ℝ Vec3 ((1 / 2 : ℝ) •
    ((fderiv ℝ f x).toLinearMap + (fderiv ℝ f (-x)).toLinearMap)) = _
  simp only [map_smul, map_add, smul_eq_mul]

theorem gradient_endpointEvenPart {f : Vec3 → ℝ} {x : Vec3}
    (hf : Differentiable ℝ f) :
    gradient (endpointParityPart 1 f) x =
      (1 / 2 : ℝ) • (gradient f x - gradient f (-x)) := by
  rw [gradient, (hasFDerivAt_endpointParityPart (hf x) (hf (-x)) 1).fderiv]
  simp [gradient, sub_eq_add_neg]

/-- The spatial pressure gradient commutes with the compatible vector projection. -/
theorem gradient_endpointEvenPart_eq_endpointOddPart {f : Vec3 → ℝ} (hf : Differentiable ℝ f) :
    gradient (endpointParityPart 1 f) = endpointParityPart (-1) (gradient f) := by
  funext x
  rw [gradient_endpointEvenPart hf]
  simp only [endpointParityPart, sub_eq_add_neg, neg_one_smul]

theorem contDiff_endpointParityPart {m : WithTop ℕ∞} {f : Vec3 → E}
    (hf : ContDiff ℝ m f) (sign : ℝ) : ContDiff ℝ m (endpointParityPart sign f) :=
  (hf.add ((hf.comp contDiff_id.neg).const_smul sign)).const_smul (1 / 2 : ℝ)

theorem iteratedFDeriv_endpointParityPart {m : ℕ} {f : Vec3 → E} (hf : ContDiff ℝ m f)
    (sign : ℝ) (x : Vec3) :
    iteratedFDeriv ℝ m (endpointParityPart sign f) x =
      (1 / 2 : ℝ) • (iteratedFDeriv ℝ m f x +
        (sign * (-1 : ℝ) ^ m) • iteratedFDeriv ℝ m f (-x)) := by
  have hn : ContDiff ℝ m (fun y => f (-y)) := hf.comp contDiff_id.neg
  have hderiv := congrFun (iteratedFDeriv_comp_const_smul (-1 : ℝ) hf) x
  simp only [neg_one_smul] at hderiv
  unfold endpointParityPart
  rw [iteratedFDeriv_const_smul_apply' (hf.add (hn.const_smul sign)).contDiffAt,
    fun_iteratedFDeriv_add_apply hf.contDiffAt (hn.const_smul sign).contDiffAt,
    iteratedFDeriv_const_smul_apply' hn.contDiffAt, hderiv, smul_smul]

private theorem norm_endpointParityAverage_le {a b : E} {sign D : ℝ}
    (hsign : |sign| ≤ 1) (ha : ‖a‖ ≤ D) (hb : ‖b‖ ≤ D) :
    ‖(1 / 2 : ℝ) • (a + sign • b)‖ ≤ D := by
  have hscale : ‖sign • b‖ ≤ D := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hsign (norm_nonneg b)).trans (by simpa using hb)
  calc
    _ = (1 / 2 : ℝ) * ‖a + sign • b‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ (1 / 2 : ℝ) * (D + D) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ha hscale)) (by norm_num)
    _ = D := by ring

theorem norm_endpointParityPart_le {f : Vec3 → E} {sign D : ℝ}
    (hsign : |sign| ≤ 1) (hf : ∀ x, ‖f x‖ ≤ D) (x : Vec3) :
    ‖endpointParityPart sign f x‖ ≤ D :=
  norm_endpointParityAverage_le hsign (hf x) (hf (-x))

theorem norm_increment_endpointParityPart_le {f : Vec3 → E} {sign D : ℝ}
    (hsign : |sign| ≤ 1) (hf : ∀ x v, ‖f (x + v) - f x‖ ≤ D * Real.sqrt ‖v‖)
    (x v : Vec3) : ‖endpointParityPart sign f (x + v) - endpointParityPart sign f x‖ ≤
      D * Real.sqrt ‖v‖ := by
  have hreflect : ‖f (-x + -v) - f (-x)‖ ≤ D * Real.sqrt ‖v‖ := by
    simpa only [norm_neg] using hf (-x) (-v)
  have hadd : endpointParityPart sign f (x + v) - endpointParityPart sign f x =
      (1 / 2 : ℝ) • ((f (x + v) - f x) + sign • (f (-x + -v) - f (-x))) := by
    rw [endpointParityPart, endpointParityPart, ← smul_sub, neg_add]
    congr 1
    rw [smul_sub]
    abel
  rw [hadd]
  exact norm_endpointParityAverage_le hsign (hf x v) hreflect

private theorem spatialHolderHalfEndpointParityPart_order_le {f : Vec3 → E} {sign : ℝ}
    (hsign : |sign| ≤ 1) (hb : BddAbove (range (fun x => ‖f x‖)))
    (hh : BddAbove (range (spatialHolderHalfQuotient f))) :
    BddAbove (range (fun x => ‖endpointParityPart sign f x‖)) ∧
    BddAbove (range (spatialHolderHalfQuotient (endpointParityPart sign f))) ∧
    spatialSupNorm (endpointParityPart sign f) ≤ spatialSupNorm f ∧
    spatialHolderHalfSeminorm (endpointParityPart sign f) ≤ spatialHolderHalfSeminorm f := by
  have hpoint := norm_endpointParityPart_le hsign (norm_le_spatialSupNorm hb)
  have hincr := norm_increment_endpointParityPart_le hsign
    (norm_increment_le_spatialHolderHalfSeminorm hh)
  have hzero : 0 ≤ spatialHolderHalfSeminorm f := by
    have heq : spatialHolderHalfQuotient f (0, 0) = 0 := by simp [spatialHolderHalfQuotient]
    have hle := le_ciSup hh ((0 : Vec3), (0 : Vec3))
    rw [heq] at hle
    exact hle
  have hquot (p : Vec3 × Vec3) :
      spatialHolderHalfQuotient (endpointParityPart sign f) p ≤ spatialHolderHalfSeminorm f := by
    rcases p with ⟨x, v⟩
    by_cases hv : v = 0
    · simpa [spatialHolderHalfQuotient, hv] using hzero
    · exact (div_le_iff₀ (Real.sqrt_pos_of_pos (norm_pos_iff.mpr hv))).mpr (hincr x v)
  exact ⟨⟨_, forall_mem_range.mpr hpoint⟩, ⟨_, forall_mem_range.mpr hquot⟩,
    ciSup_le hpoint, ciSup_le hquot⟩

/-- Reflection averaging costs no constants in any spatial `C^{m,1/2}` norm. -/
theorem spatialHolderHalfNorm_endpointParityPart_le {f : Vec3 → E} {m : ℕ}
    (hf : SpatialHolderHalf m f) {sign : ℝ} (hsign : |sign| ≤ 1) :
    SpatialHolderHalf m (endpointParityPart sign f) ∧
    spatialHolderHalfNorm m (endpointParityPart sign f) ≤ spatialHolderHalfNorm m f := by
  have horder (j : ℕ) (hj : j ≤ m) :=
    spatialHolderHalfEndpointParityPart_order_le
      (f := iteratedFDeriv ℝ j f) (sign := sign * (-1 : ℝ) ^ j)
      (by simpa [abs_mul, abs_pow] using hsign) (hf.2 j hj).1 (hf.2 j hj).2
  have hderiv (j : ℕ) (hj : j ≤ m) : iteratedFDeriv ℝ j (endpointParityPart sign f) =
      endpointParityPart (sign * (-1 : ℝ) ^ j) (iteratedFDeriv ℝ j f) :=
    funext (iteratedFDeriv_endpointParityPart (hf.1.of_le (by exact_mod_cast hj)) sign)
  refine ⟨⟨contDiff_endpointParityPart hf.1 sign, fun j hj => ?_⟩, ?_⟩
  · rw [hderiv j hj]
    exact ⟨(horder j hj).1, (horder j hj).2.1⟩
  · apply Finset.sum_le_sum
    intro j hj
    have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [hderiv j hjm]
    exact add_le_add (horder j hjm).2.2.1 (horder j hjm).2.2.2

theorem spatialDerivativeWord_endpointParityPart {f : Vec3 → E} (hf : ContDiff ℝ ∞ f)
    (sign : ℝ) (w : List (Fin 3)) (x : Vec3) :
    spatialDerivativeWord w (endpointParityPart sign f) x =
      endpointParityPart (sign * (-1 : ℝ) ^ w.length) (spatialDerivativeWord w f) x := by
  rw [spatialDerivativeWord_eq_iteratedFDeriv (contDiff_endpointParityPart hf sign),
    iteratedFDeriv_endpointParityPart (hf.of_le (by simp))]
  simp only [endpointParityPart, spatialDerivativeWord_eq_iteratedFDeriv hf,
    smul_apply, add_apply]

theorem hierarchyLabelWord_endpointParityPart {f : Vec3 → E} (hf : ContDiff ℝ ∞ f)
    (ell sign : ℝ) (w : List (Fin 3)) (x : Vec3) :
    phaseOperatorWord (hierarchyLabelDirection ell) w (endpointParityPart sign f) x =
      endpointParityPart (sign * (-1 : ℝ) ^ w.length)
        (phaseOperatorWord (hierarchyLabelDirection ell) w f) x := by
  rw [phaseOperatorWord_hierarchyLabelDirection_eq_smul ell (contDiff_endpointParityPart hf sign),
    spatialDerivativeWord_endpointParityPart hf]
  simp only [endpointParityPart, phaseOperatorWord_hierarchyLabelDirection_eq_smul ell hf]
  rw [smul_comm (ell ^ w.length) (1 / 2 : ℝ), smul_add,
    smul_comm (ell ^ w.length) (sign * (-1 : ℝ) ^ w.length)]

/-- The exact weighted label-word measures in the hierarchy are nonincreasing
under compatible reflection, including the spatial half-Hölder choice. -/
theorem hierarchyLabelJetValues_endpointParityPart_le {Time : Type*} {f : Time → Vec3 → E}
    (hf : ∀ t, ContDiff ℝ ∞ (f t)) (holder : Prop) (ell : ℝ) (w : List (Fin 3))
    {sign : ℝ} (hsign : |sign| ≤ 1)
    (hb : BddAbove (hierarchyJetValues holder (hierarchyLabelDirection ell) w f)) :
    let J := hierarchyJetValues holder (hierarchyLabelDirection ell) w
      (fun t => endpointParityPart sign (f t))
    BddAbove J ∧ sSup J ≤ sSup (hierarchyJetValues holder (hierarchyLabelDirection ell) w f) := by
  let R := hierarchyJetValues holder (hierarchyLabelDirection ell) w f
  let M := sSup R
  let J := hierarchyJetValues holder (hierarchyLabelDirection ell) w (fun t => endpointParityPart sign (f t))
  let a := sign * (-1 : ℝ) ^ w.length
  have ha : |a| ≤ 1 := by simpa [a, abs_mul, abs_pow] using hsign
  have hM : 0 ≤ M := le_csSup hb (Or.inl rfl)
  have hbounds : ∀ r ∈ J, r ≤ M := by
    rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hH, t, x, y, rfl⟩)
    · exact hM
    · rw [hierarchyLabelWord_endpointParityPart (hf t)]
      exact norm_endpointParityPart_le ha
        (fun z => le_csSup hb (Or.inr (Or.inl ⟨t, z, rfl⟩))) x
    · rw [hierarchyLabelWord_endpointParityPart (hf t), hierarchyLabelWord_endpointParityPart (hf t)]
      by_cases hxy : x = y
      · simpa only [hxy, sub_self, norm_zero, zero_div] using hM
      let g := phaseOperatorWord (hierarchyLabelDirection ell) w (f t)
      change ‖endpointParityPart a g x - endpointParityPart a g y‖ /
        Real.sqrt (dist x y) ≤ M
      apply (div_le_iff₀ (Real.sqrt_pos.2 (dist_pos.2 hxy))).2
      have hincr (z v : Vec3) : ‖g (z + v) - g z‖ ≤ M * Real.sqrt ‖v‖ := by
        by_cases hv : v = 0
        · simp [hv]
        apply (div_le_iff₀ (Real.sqrt_pos.2 (norm_pos_iff.2 hv))).1
        have hq : ‖g (z + v) - g z‖ / Real.sqrt (dist (z + v) z) ≤ M :=
          le_csSup hb (Or.inr (Or.inr ⟨hH, t, z + v, z, rfl⟩))
        simpa only [dist_eq_norm, add_sub_cancel_left] using hq
      simpa only [show y + (x - y) = x by abel, ← dist_eq_norm] using
        norm_increment_endpointParityPart_le ha hincr y (x - y)
  exact ⟨⟨M, hbounds⟩, csSup_le ⟨0, Or.inl rfl⟩ hbounds⟩

/-- The paper's finite weighted label norm is unchanged in its constants by
selecting the compatible parity, including when the input is time-normalized. -/
theorem hierarchyFiniteLabelNorm_endpointParityPart_le {Time : Type*} {f : Time → Vec3 → E}
    (hf : ∀ t, ContDiff ℝ ∞ (f t)) (holder : Prop) (ell : ℝ) (n : ℕ)
    {sign : ℝ} (hsign : |sign| ≤ 1)
    (hb : ∀ w ∈ hierarchyAdmissibleWords (Fin 3) n,
      BddAbove (hierarchyJetValues holder (hierarchyLabelDirection ell) w f)) :
    hierarchyFiniteWordNorm holder (hierarchyLabelDirection ell) n
      (fun t => endpointParityPart sign (f t)) ≤
        hierarchyFiniteWordNorm holder (hierarchyLabelDirection ell) n f := by
  exact Finset.sum_le_sum fun w hw =>
    (hierarchyLabelJetValues_endpointParityPart_le hf holder ell w hsign (hb w hw)).2

end Reflection

private theorem endpointParity_neg_preimage_centeredCell :
    (fun x : Vec3 => -x) ⁻¹' centeredCell = centeredCell := by
  ext x
  change (∀ i, (-x) i ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) ↔
    (∀ i, x i ∈ Icc (-(1 / 2 : ℝ)) (1 / 2))
  simp only [PiLp.neg_apply, mem_Icc, ← abs_le, abs_neg]

private theorem endpointParity_integral_reflect_centeredCell (p : Vec3 → ℝ) :
    (∫ x in centeredCell, p (-x)) = ∫ x in centeredCell, p x := by
  have hMeasure := (Measure.measurePreserving_neg (volume : Measure Vec3)).restrict_preimage
    isCompact_centeredCell.measurableSet
  rw [endpointParity_neg_preimage_centeredCell] at hMeasure
  exact hMeasure.integral_comp (Homeomorph.neg Vec3).measurableEmbedding p

theorem integral_endpointEvenPart_centeredCell {p : Vec3 → ℝ} (hp : Continuous p) :
    (∫ x in centeredCell, endpointParityPart 1 p x) = ∫ x in centeredCell, p x := by
  simp only [endpointParityPart, smul_eq_mul, one_mul]
  have hn : IntegrableOn (fun x : Vec3 => p (-x)) centeredCell :=
    (hp.comp continuous_neg).continuousOn.integrableOn_compact isCompact_centeredCell
  rw [integral_const_mul, integral_add (hp.continuousOn.integrableOn_compact isCompact_centeredCell) hn,
    endpointParity_integral_reflect_centeredCell]
  ring

theorem derivWithin_endpointTimeParityPart {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {T t : ℝ} (hT : 0 < T)
    {f : ℝ → Vec3 → E} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) LiftSlab(T))
    (ht : t ∈ TimeSlab(T)) (sign : ℝ) (x : Vec3) :
    derivWithin (fun r => endpointTimeParityPart sign f r x) TimeSlab(T) t =
      endpointParityPart sign (fun y => derivWithin (fun r => f r y) TimeSlab(T) t) x := by
  have hTime (y : Vec3) : DifferentiableWithinAt ℝ (fun r => f r y) TimeSlab(T) t := by
    have hline : ContDiffOn ℝ ∞ (fun r => f r y) TimeSlab(T) :=
      hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hr => ⟨hr, mem_univ _⟩)
    exact hline.differentiableOn (by simp) t ht
  exact (hasDerivWithinAt_endpointTimeParityPart sign (hTime x).hasDerivWithinAt
    (hTime (-x)).hasDerivWithinAt).derivWithin (uniqueDiffOn_Icc hT t ht)

set_option maxHeartbeats 700000 in
/-- The reflection projection selects odd label velocity, displacement and
physical mean velocity, and even normalized pressure. It keeps the same
forced equation and both endpoint conditions. The coefficients are the
actual periodic lifts of the deformation, inverse coframe and material
gradient. -/
theorem endpointPhysicalMean_reflectionSelection {T : ℝ} (hT : 0 < T)
    (F G M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3) (force v Z B : Velocity) (q : Pressure)
    (hF : ∀ t ∈ TimeSlab(T), Function.Even (F t))
    (hG : ∀ t ∈ TimeSlab(T), Function.Even (G t))
    (hM : ∀ t ∈ TimeSlab(T), Function.Even (M t))
    (hforce : ∀ t ∈ TimeSlab(T), Function.Odd (force t))
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) LiftSlab(T))
    (hZ : ContDiffOn ℝ ∞ (Function.uncurry Z) LiftSlab(T))
    (hB : ContDiffOn ℝ ∞ (Function.uncurry B) LiftSlab(T))
    (hq : ContDiffOn ℝ ∞ (Function.uncurry q) LiftSlab(T))
    (hPer : ∀ t ∈ TimeSlab(T), SpatiallyPeriodic (v t) ∧ SpatiallyPeriodic (Z t) ∧
      SpatiallyPeriodic (B t) ∧ SpatiallyPeriodic (q t) ∧ (∫ x in centeredCell, q t x) = 0)
    (hZero : Z 0 = 0) (hFinish : Z T = 0)
    (hEq : ∀ t ∈ TimeSlab(T), ∀ x,
      B t x = F t x (v t x) ∧
      HasDerivWithinAt (fun r => Z r x) (v t x) TimeSlab(T) t ∧
      divergence (v t) x = 0 ∧
      derivWithin (fun r => B r x) TimeSlab(T) t + M t x (B t x) +
        (G t x).adjoint (gradient (q t) x) = force t x) :
    let v' := endpointTimeParityPart (-1) v
    let Z' := endpointTimeParityPart (-1) Z
    let B' := endpointTimeParityPart (-1) B
    let q' := endpointTimeParityPart 1 q
    ContDiffOn ℝ ∞ (Function.uncurry v') LiftSlab(T) ∧
    ContDiffOn ℝ ∞ (Function.uncurry Z') LiftSlab(T) ∧
    ContDiffOn ℝ ∞ (Function.uncurry B') LiftSlab(T) ∧
    ContDiffOn ℝ ∞ (Function.uncurry q') LiftSlab(T) ∧
    (∀ t ∈ TimeSlab(T), SpatiallyPeriodic (v' t) ∧ SpatiallyPeriodic (Z' t) ∧
      SpatiallyPeriodic (B' t) ∧ SpatiallyPeriodic (q' t) ∧ (∫ x in centeredCell, q' t x) = 0) ∧
    Z' 0 = 0 ∧ Z' T = 0 ∧
    (∀ t ∈ TimeSlab(T), ∀ x,
      B' t x = F t x (v' t x) ∧
      HasDerivWithinAt (fun r => Z' r x) (v' t x) TimeSlab(T) t ∧
      divergence (v' t) x = 0 ∧
      derivWithin (fun r => B' r x) TimeSlab(T) t + M t x (B' t x) +
        (G t x).adjoint (gradient (q' t) x) = force t x) ∧
    ∀ t, Function.Odd (v' t) ∧ Function.Odd (Z' t) ∧ Function.Odd (B' t) ∧ Function.Even (q' t) := by
  let v' := endpointTimeParityPart (-1) v
  let Z' := endpointTimeParityPart (-1) Z
  let B' := endpointTimeParityPart (-1) B
  let q' := endpointTimeParityPart 1 q
  refine ⟨contDiffOn_endpointTimeParityPart hv _, contDiffOn_endpointTimeParityPart hZ _,
    contDiffOn_endpointTimeParityPart hB _, contDiffOn_endpointTimeParityPart hq _, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨hvp, hZp, hBp, hqp, hq0⟩ := hPer t ht
    exact ⟨spatiallyPeriodic_endpointParityPart hvp _, spatiallyPeriodic_endpointParityPart hZp _,
      spatiallyPeriodic_endpointParityPart hBp _, spatiallyPeriodic_endpointParityPart hqp _,
      (integral_endpointEvenPart_centeredCell
        (endpointParity_contDiff_slice hq ht).continuous).trans hq0⟩
  · funext x
    change endpointParityPart (-1) (Z 0) x = 0
    rw [hZero]
    simp [endpointParityPart]
  · funext x
    change endpointParityPart (-1) (Z T) x = 0
    rw [hFinish]
    simp [endpointParityPart]
  · intro t ht x
    obtain ⟨hBx, hZx, hdivx, hEqx⟩ := hEq t ht x
    obtain ⟨hBneg, hZneg, hdivneg, hEqneg⟩ := hEq t ht (-x)
    refine ⟨?_, hasDerivWithinAt_endpointTimeParityPart (-1) hZx hZneg, ?_, ?_⟩
    · change endpointParityPart (-1) (B t) x = F t x (endpointParityPart (-1) (v t) x)
      simp only [endpointParityPart, hBx, hBneg, hF t ht x, map_smul, map_add]
    · change divergence (endpointParityPart (-1) (v t)) x = 0
      rw [divergence_endpointOddPart ((endpointParity_contDiff_slice hv ht).differentiable (by simp)),
        hdivx, hdivneg, add_zero, mul_zero]
    · rw [derivWithin_endpointTimeParityPart hT hB ht (-1)]
      change _ + M t x (endpointParityPart (-1) (B t) x) +
        (G t x).adjoint (gradient (endpointParityPart 1 (q t)) x) = _
      rw [gradient_endpointEvenPart ((endpointParity_contDiff_slice hq ht).differentiable (by simp))]
      rw [hG t ht x, hM t ht x] at hEqneg
      have hLin := congrArg ((1 / 2 : ℝ) • ·) (congrArg₂ (· - ·) hEqx hEqneg)
      rw [hforce t ht x, sub_neg_eq_add, ← two_smul ℝ (force t x), smul_smul] at hLin
      norm_num at hLin
      convert hLin using 1
      simp only [endpointParityPart, neg_one_smul, map_smul, map_add, map_sub, map_neg,
        smul_sub, smul_add, smul_neg]
      abel
  · intro t
    exact ⟨odd_endpointParityPart _, odd_endpointParityPart _, odd_endpointParityPart _,
      even_endpointParityPart _⟩

end

end TorusEuler
