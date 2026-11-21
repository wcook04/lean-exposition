import Breakdown.FracCell.ReductionLossRotationLeaves
import Breakdown.Frac.PAxial
import Breakdown.FracCert.DriftWeakLimit

open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

namespace RowModeGradientPartsInternal

theorem turnBy_eq_rotation (φ : ℝ) (y : Space) : turnBy φ y = axialRotation φ y := by
  rw [FracInternal.Axial.axialRotation_eq_formula]
  rfl

theorem turnBy_measurePreserving (φ : ℝ) : MeasurePreserving (turnBy φ) volume volume := by
  have h : turnBy φ = axialRotation φ := funext (turnBy_eq_rotation φ)
  rw [h]
  exact (axialRotation φ).measurePreserving

theorem turnBy_measurePreserving_restrict {S : Set Space} (hS : MeasurableSet S)
    (hinv : ∀ (φ : ℝ) y, y ∈ S ↔ turnBy φ y ∈ S) (φ : ℝ) :
    MeasurePreserving (turnBy φ) (volume.restrict S) (volume.restrict S) := by
  have h := (turnBy_measurePreserving φ).restrict_preimage hS
  have hpre : turnBy φ ⁻¹' S = S := by
    ext y
    exact (hinv φ y).symm
  rwa [hpre] at h

theorem horizontalNorm_le (y : Space) : horizontalNorm y ≤ ‖y‖ := by
  rw [horizontalNorm, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg (y 2)]

theorem integral_sq_eq (F : Space → Space) (μ : Measure Space) (hF : AEStronglyMeasurable F μ) :
    (∫ y, ‖F y‖ ^ 2 ∂μ) = ((eLpNorm F 2 μ) ^ 2).toReal := by
  have h1 : eLpNorm F 2 μ ^ 2 = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ := by
    have := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := F) (p := 2) two_ne_zero
    simpa using this
  rw [h1, integral_eq_lintegral_of_nonneg_ae (f := fun y => ‖F y‖ ^ 2)
    (Eventually.of_forall fun y => by positivity) (by exact hF.norm.pow 2)]
  congr 1
  refine lintegral_congr fun y => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem turn_neg_cancel (φ : ℝ) (z : Space) : turnBy (-φ) (turnBy φ z) = z := by
  ext i
  fin_cases i
  · simp [turnBy, Real.cos_neg, Real.sin_neg]
    linear_combination (z 0) * Real.sin_sq_add_cos_sq φ
  · simp [turnBy, Real.cos_neg, Real.sin_neg]
    linear_combination (z 1) * Real.sin_sq_add_cos_sq φ
  · simp [turnBy]

theorem pair_sq_le {μ : Measure Space} {h u : Space → Space} (hh : MemLp h 2 μ) (hu : MemLp u 2 μ) :
    (∫ y, inner ℝ (h y) (u y) ∂μ) ^ 2 ≤ (∫ y, ‖h y‖ ^ 2 ∂μ) * ∫ y, ‖u y‖ ^ 2 ∂μ := by
  have e : ∀ {g k : Space → Space} (hg : MemLp g 2 μ) (hk : MemLp k 2 μ),
      inner ℝ (hg.toLp g) (hk.toLp k) = ∫ y, inner ℝ (g y) (k y) ∂μ := by
    intro g k hg hk
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp, hk.coeFn_toLp] with y h1 h2
    rw [h1, h2]
  have hn : ∀ {g : Space → Space} (hg : MemLp g 2 μ), ‖hg.toLp g‖ ^ 2 = ∫ y, ‖g y‖ ^ 2 ∂μ := by
    intro g hg
    rw [← real_inner_self_eq_norm_sq, e hg hg]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [real_inner_self_eq_norm_sq]
  rw [← e hh hu, ← hn hh, ← hn hu, ← mul_pow]
  calc inner ℝ (hh.toLp h) (hu.toLp u) ^ 2 = |inner ℝ (hh.toLp h) (hu.toLp u)| ^ 2 := (sq_abs _).symm
    _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2

end RowModeGradientPartsInternal

open RowModeGradientPartsInternal RotationLeavesInternal in
theorem rotation_pair_sq_le {C : Set Space} (hC : MeasurableSet C) (hinv : ∀ (φ : ℝ) y, y ∈ C ↔ turnBy φ y ∈ C)
    {f u : Space → Space} (hf : MemLp f 2 (volume.restrict C)) (hu : MemLp u 2 (volume.restrict C)) {X : ℝ}
    (hX : ∀ φ : ℝ, (∫ y in C, ‖f (turnBy φ y) - f y‖ ^ 2) ≤ φ ^ 2 * X) (φ : ℝ) :
    ((∫ y in C, inner ℝ (f y) (u (turnBy (-φ) y))) - ∫ y in C, inner ℝ (f y) (u y)) ^ 2 ≤
      φ ^ 2 * X * ∫ y in C, ‖u y‖ ^ 2 := by
  have hmp := turn_mp_restrict hC hinv φ
  have hfR : MemLp (fun y => f (turnBy φ y)) 2 (volume.restrict C) := hf.comp_measurePreserving hmp
  have e1 : (∫ y in C, inner ℝ (f y) (u (turnBy (-φ) y))) = ∫ z in C, inner ℝ (f (turnBy φ z)) (u z) := by
    have h := hmp.integral_comp (turn_embedding φ) (fun y => inner ℝ (f y) (u (turnBy (-φ) y)))
    simp only [turn_neg_cancel] at h
    exact h.symm
  have hint : ∀ {g k : Space → Space}, MemLp g 2 (volume.restrict C) → MemLp k 2 (volume.restrict C) →
      Integrable (fun y => inner ℝ (g y) (k y)) (volume.restrict C) := fun hg hk =>
    (MeasureTheory.L2.integrable_inner (hg.toLp _) (hk.toLp _)).congr (by
      filter_upwards [hg.coeFn_toLp, hk.coeFn_toLp] with y h1 h2
      rw [h1, h2])
  rw [e1, ← integral_sub (hint hfR hu) (hint hf hu)]
  have e2 : (fun y => inner ℝ (f (turnBy φ y)) (u y) - inner ℝ (f y) (u y)) =
      fun y => inner ℝ (f (turnBy φ y) - f y) (u y) := by
    funext y
    rw [inner_sub_left]
  rw [e2]
  refine (pair_sq_le (h := fun y => f (turnBy φ y) - f y) (by exact hfR.sub hf) hu).trans ?_
  exact mul_le_mul_of_nonneg_right (hX φ) (integral_nonneg fun _ => sq_nonneg _)

open RowModeGradientPartsInternal in
theorem rotationDifference_of (h1 : RotationSmoothStatement) (h2 : RotationApproxStatement) :
    RotationDifferenceStatement := by
  intro m v G H hv S hSm hSb hinv φ
  obtain ⟨r, hr⟩ := hSb.subset_closedBall 0
  obtain ⟨w, hw, hwv, hwG⟩ := h2 m v G H hv (Metric.closedBall 0 r) (isCompact_closedBall 0 r)
  have hmp := turnBy_measurePreserving_restrict hSm hinv φ
  have hμK : volume.restrict S ≤ volume.restrict (Metric.closedBall (0 : Space) r) :=
    Measure.restrict_mono hr le_rfl
  have hvm : AEStronglyMeasurable v (volume.restrict S) := hv.measurable_velocity.restrict
  have hJc : Continuous axialTurn := SteadyCert.Internal.DriftWeakLimit.continuous_turn
  have hGJ : AEStronglyMeasurable (fun y => G y (axialTurn y)) (volume.restrict S) :=
    (Continuous.comp_aestronglyMeasurable₂ (g := fun (L : Space →L[ℝ] Space) (x : Space) => L x)
      (by exact continuous_fst.clm_apply continuous_snd) hv.measurable_gradient
      hJc.aestronglyMeasurable).restrict
  have hwm : ∀ n, AEStronglyMeasurable (w n) (volume.restrict S) :=
    fun n => (hw n).continuous.aestronglyMeasurable
  have hwR : ∀ n, AEStronglyMeasurable (fun y => w n (turnBy φ y)) (volume.restrict S) :=
    fun n => (hwm n).comp_measurePreserving hmp
  have hvR : AEStronglyMeasurable (fun y => v (turnBy φ y)) (volume.restrict S) :=
    hvm.comp_measurePreserving hmp
  have hDw : ∀ n, AEStronglyMeasurable (fun y => fderiv ℝ (w n) y (axialTurn y)) (volume.restrict S) :=
    fun n => (((hw n).continuous_fderiv (by norm_num)).clm_apply hJc).aestronglyMeasurable
  have hbound : ∀ n, eLpNorm (fun y => v (turnBy φ y) - v y) 2 (volume.restrict S) ≤
      ENNReal.ofReal |φ| * (eLpNorm (fun y => G y (axialTurn y)) 2 (volume.restrict S) +
        eLpNorm (fun y => fderiv ℝ (w n) y (axialTurn y) - G y (axialTurn y)) 2
          (volume.restrict (Metric.closedBall 0 r))) +
      (eLpNorm (fun y => w n y - v y) 2 (volume.restrict (Metric.closedBall 0 r)) +
        eLpNorm (fun y => w n y - v y) 2 (volume.restrict (Metric.closedBall 0 r))) := by
    intro n
    have hsplit : (fun y => v (turnBy φ y) - v y) = fun y =>
        ((w n (turnBy φ y) - w n y) + (w n y - v y)) - (w n (turnBy φ y) - v (turnBy φ y)) := by
      funext y
      abel
    have hf1 : AEStronglyMeasurable (fun y => w n (turnBy φ y) - w n y) (volume.restrict S) :=
      (hwR n).sub (hwm n)
    have hf2 : AEStronglyMeasurable (fun y => w n y - v y) (volume.restrict S) := (hwm n).sub hvm
    have hf3 : AEStronglyMeasurable (fun y => w n (turnBy φ y) - v (turnBy φ y)) (volume.restrict S) :=
      (hwR n).sub hvR
    have e3 : eLpNorm (fun y => w n (turnBy φ y) - v (turnBy φ y)) 2 (volume.restrict S) =
        eLpNorm (fun y => w n y - v y) 2 (volume.restrict S) :=
      eLpNorm_comp_measurePreserving hf2 hmp
    have hsm : eLpNorm (fun y => w n y - v y) 2 (volume.restrict S) ≤
        eLpNorm (fun y => w n y - v y) 2 (volume.restrict (Metric.closedBall 0 r)) :=
      eLpNorm_mono_measure _ hμK
    have hs1 := h1 (w n) (hw n) S hSm hSb hinv φ
    have hD : eLpNorm (fun y => fderiv ℝ (w n) y (axialTurn y)) 2 (volume.restrict S) ≤
        eLpNorm (fun y => G y (axialTurn y)) 2 (volume.restrict S) +
          eLpNorm (fun y => fderiv ℝ (w n) y (axialTurn y) - G y (axialTurn y)) 2
            (volume.restrict (Metric.closedBall 0 r)) := by
      have heq : (fun y => fderiv ℝ (w n) y (axialTurn y)) =
          (fun y => G y (axialTurn y)) + (fun y => fderiv ℝ (w n) y (axialTurn y) - G y (axialTurn y)) := by
        funext y
        simp
      rw [heq]
      exact (eLpNorm_add_le hGJ ((hDw n).sub hGJ) (by norm_num)).trans
        (add_le_add le_rfl (eLpNorm_mono_measure _ hμK))
    rw [hsplit]
    calc _ ≤ eLpNorm (fun y => (w n (turnBy φ y) - w n y) + (w n y - v y)) 2 (volume.restrict S) +
          eLpNorm (fun y => w n (turnBy φ y) - v (turnBy φ y)) 2 (volume.restrict S) :=
          eLpNorm_sub_le (hf1.add hf2) hf3 (by norm_num)
      _ ≤ (eLpNorm (fun y => w n (turnBy φ y) - w n y) 2 (volume.restrict S) +
          eLpNorm (fun y => w n y - v y) 2 (volume.restrict S)) +
          eLpNorm (fun y => w n y - v y) 2 (volume.restrict S) := by
          rw [e3]
          exact add_le_add (eLpNorm_add_le hf1 hf2 (by norm_num)) le_rfl
      _ ≤ _ := by
          rw [add_assoc]
          exact add_le_add (hs1.trans (mul_le_mul_right hD _)) (add_le_add hsm hsm)
  have hlim : Tendsto (fun n => ENNReal.ofReal |φ| * (eLpNorm (fun y => G y (axialTurn y)) 2 (volume.restrict S) +
        eLpNorm (fun y => fderiv ℝ (w n) y (axialTurn y) - G y (axialTurn y)) 2
          (volume.restrict (Metric.closedBall 0 r))) +
      (eLpNorm (fun y => w n y - v y) 2 (volume.restrict (Metric.closedBall 0 r)) +
        eLpNorm (fun y => w n y - v y) 2 (volume.restrict (Metric.closedBall 0 r)))) atTop
      (𝓝 (ENNReal.ofReal |φ| * eLpNorm (fun y => G y (axialTurn y)) 2 (volume.restrict S))) := by
    have := (ENNReal.Tendsto.const_mul ((tendsto_const_nhds
      (x := eLpNorm (fun y => G y (axialTurn y)) 2 (volume.restrict S))).add hwG)
      (Or.inr (ENNReal.ofReal_ne_top (r := |φ|)))).add (hwv.add hwv)
    simpa using this
  have hmain := ge_of_tendsto' hlim hbound
  have hGmem : MemLp (fun y => G y (axialTurn y)) 2 (volume.restrict S) := by
    refine (memLp_two_iff_integrable_sq_norm hGJ).2 ?_
    refine ((hv.gradient_two.restrict (s := S)).const_mul (r ^ 2)).mono' (hGJ.norm.pow 2) ?_
    refine (ae_restrict_iff' hSm).2 (Eventually.of_forall fun y hy => ?_)
    have hyr : ‖y‖ ≤ r := by simpa using hr hy
    have hh : horizontalNorm y ≤ r := (horizontalNorm_le y).trans hyr
    have h0 : 0 ≤ horizontalNorm y := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (RowModeGradientInternal.turn_sq_le (G y) y).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hh 2) (RowModeGradientInternal.entrySq_nonneg _))
  have hEH : eLpNorm (fun y => G y (axialTurn y)) 2 (volume.restrict S) ≠ ⊤ := hGmem.eLpNorm_ne_top
  have e1 := integral_sq_eq (fun y => v (turnBy φ y) - v y) (volume.restrict S) (hvR.sub hvm)
  have e2 := integral_sq_eq (fun y => G y (axialTurn y)) (volume.restrict S) hGJ
  beta_reduce at e1 e2
  rw [e1, e2]
  have hsq := pow_le_pow_left₀ (zero_le) hmain 2
  have hfin : (ENNReal.ofReal |φ| * eLpNorm (fun y => G y (axialTurn y)) 2 (volume.restrict S)) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEH)
  calc _ ≤ ((ENNReal.ofReal |φ| * eLpNorm (fun y => G y (axialTurn y)) 2 (volume.restrict S)) ^ 2).toReal :=
        ENNReal.toReal_mono hfin hsq
    _ = φ ^ 2 * ((eLpNorm (fun y => G y (axialTurn y)) 2 (volume.restrict S)) ^ 2).toReal := by
        rw [mul_pow, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (abs_nonneg _), sq_abs]

open RotationLeavesInternal in
theorem rotation_deriv_sq_le {C : Set Space} (hC : MeasurableSet C) (hinv : ∀ (φ : ℝ) y, y ∈ C ↔ turnBy φ y ∈ C)
    {f u : Space → Space} (hf : MemLp f 2 (volume.restrict C)) (hu : MemLp u 2 (volume.restrict C)) {X : ℝ}
    (hX : ∀ φ : ℝ, (∫ y in C, ‖f (turnBy φ y) - f y‖ ^ 2) ≤ φ ^ 2 * X) {d : ℝ}
    (hd : HasDerivAt (fun φ => ∫ y in C, inner ℝ (f y) (u (turnBy (-φ) y))) d 0) :
    d ^ 2 ≤ X * ∫ y in C, ‖u y‖ ^ 2 := by
  have hs := hd.tendsto_slope
  have hsq := (hs.pow 2)
  refine le_of_tendsto hsq ?_
  filter_upwards [self_mem_nhdsWithin] with φ hφ
  have hφ0 : φ ≠ 0 := hφ
  have h0 : (∫ y in C, inner ℝ (f y) (u (turnBy (-0) y))) = ∫ y in C, inner ℝ (f y) (u y) := by
    simp only [neg_zero, turn_zero]
  rw [slope_def_field]
  beta_reduce
  rw [h0, sub_zero, div_pow]
  have hb := rotation_pair_sq_le hC hinv hf hu hX φ
  have hp : 0 < φ ^ 2 := by positivity
  rw [div_le_iff₀ hp]
  calc _ ≤ φ ^ 2 * X * ∫ y in C, ‖u y‖ ^ 2 := hb
    _ = _ := by ring

theorem rotationDifference : RotationDifferenceStatement :=
  rotationDifference_of rotationSmooth rotationApprox

namespace RowRotationCellInternal

open RotationLeavesInternal

def qv (w : Space) : Space := EuclideanSpace.single 2 (w 2)

theorem turn_add (φ : ℝ) (a b : Space) : turnBy φ (a + b) = turnBy φ a + turnBy φ b := by
  rw [← rot_eq, ← rot_eq, ← rot_eq, map_add]

theorem turn_smul (φ r : ℝ) (a : Space) : turnBy φ (r • a) = r • turnBy φ a := by
  rw [← rot_eq, ← rot_eq, map_smul]

theorem turn_inner (φ : ℝ) (a b : Space) : inner ℝ (turnBy φ a) (turnBy φ b) = inner ℝ a b := by
  rw [← rot_eq, ← rot_eq, LinearIsometryEquiv.inner_map_map]

theorem turn_zero_vec (φ : ℝ) : turnBy φ 0 = 0 := by
  rw [← rot_eq, map_zero]

theorem axialTurn_comm (φ : ℝ) (w : Space) : axialTurn (turnBy φ w) = turnBy φ (axialTurn w) := by
  ext i
  fin_cases i <;> simp [turnBy, axialTurn] <;> ring

theorem qv_comm (φ : ℝ) (w : Space) : qv (turnBy φ w) = turnBy φ (qv w) := by
  ext i
  fin_cases i <;> simp [turnBy, qv]

theorem axialTurn_add (a b : Space) : axialTurn (a + b) = axialTurn a + axialTurn b := by
  ext i
  fin_cases i <;> simp [axialTurn] <;> ring

theorem axialTurn_smul (r : ℝ) (a : Space) : axialTurn (r • a) = r • axialTurn a := by
  ext i
  fin_cases i <;> simp [axialTurn]

theorem qv_add (a b : Space) : qv (a + b) = qv a + qv b := by
  ext i
  fin_cases i <;> simp [qv]

theorem qv_smul (r : ℝ) (a : Space) : qv (r • a) = r • qv a := by
  ext i
  fin_cases i <;> simp [qv]

theorem turn_neg_formula (φ : ℝ) (w : Space) :
    turnBy (-φ) w = qv w + Real.cos φ • (w - qv w) - Real.sin φ • axialTurn w := by
  ext i
  fin_cases i <;> simp [turnBy, qv, axialTurn, Real.cos_neg, Real.sin_neg] <;> ring

theorem qv_norm_le (w : Space) : ‖qv w‖ ≤ ‖w‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp [qv, Fin.sum_univ_three]
  positivity

theorem qv_cont : Continuous qv := by
  unfold qv
  exact (single_cont 2).comp (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous

theorem axialTurn_cont : Continuous axialTurn := SteadyCert.Internal.DriftWeakLimit.continuous_turn

theorem memLp_comp {μ : Measure Space} {L : Space → Space} (hLc : Continuous L) (hLn : ∀ w, ‖L w‖ ≤ ‖w‖)
    {g : Space → Space} (hg : MemLp g 2 μ) : MemLp (fun y => L (g y)) 2 μ :=
  hg.of_le (hLc.comp_aestronglyMeasurable hg.1) (Eventually.of_forall fun y => hLn (g y))

theorem int_inner {μ : Measure Space} {g h : Space → Space} (hg : MemLp g 2 μ) (hh : MemLp h 2 μ) :
    Integrable (fun y => inner ℝ (g y) (h y)) μ :=
  (MeasureTheory.L2.integrable_inner (hg.toLp _) (hh.toLp _)).congr (by
    filter_upwards [hg.coeFn_toLp, hh.coeFn_toLp] with y h1 h2
    rw [h1, h2])

theorem axis_null : ∀ᵐ y ∂(volume : Measure Space), horizontalNorm y ≠ 0 := by
  have hs : (volume : Measure Space) (LinearMap.ker ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) : Space →ₗ[ℝ] ℝ) : Set Space) = 0 := by
    refine Measure.addHaar_submodule _ _ ?_
    intro h
    have : (EuclideanSpace.single 0 1 : Space) ∈ LinearMap.ker ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) : Space →ₗ[ℝ] ℝ) := by
      rw [h]; trivial
    simp at this
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) hs
  have hy' : horizontalNorm y = 0 := not_not.1 hy
  unfold horizontalNorm at hy'
  rw [Real.sqrt_eq_zero (by positivity)] at hy'
  show (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) y = 0
  simp
  nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]

def TurnPair (n : ℝ) (g g' : Space → Space) : Prop :=
  ∀ φ : ℝ, ∀ᵐ y ∂(volume : Measure Space),
    g (turnBy φ y) = turnBy φ (Real.cos (n * φ) • g y + Real.sin (n * φ) • g' y) ∧
    g' (turnBy φ y) = turnBy φ (Real.cos (n * φ) • g' y - Real.sin (n * φ) • g y)

theorem pair_zero (n : ℝ) : TurnPair n (fun _ => 0) (fun _ => 0) := fun φ =>
  Eventually.of_forall fun y => by simp [turn_zero_vec]

theorem pair_add {n : ℝ} {g g' h h' : Space → Space} (pg : TurnPair n g g') (ph : TurnPair n h h') :
    TurnPair n (fun y => g y + h y) (fun y => g' y + h' y) := fun φ => by
  filter_upwards [pg φ, ph φ] with y h1 h2
  rw [h1.1, h1.2, h2.1, h2.2, ← turn_add, ← turn_add]
  constructor <;> congr 1 <;> simp only [smul_add] <;> abel

theorem pair_smul {n : ℝ} (r : ℝ) {g g' : Space → Space} (pg : TurnPair n g g') :
    TurnPair n (fun y => r • g y) (fun y => r • g' y) := fun φ => by
  filter_upwards [pg φ] with y h1
  rw [h1.1, h1.2, ← turn_smul, ← turn_smul]
  constructor <;> congr 1 <;> simp only [smul_add, smul_sub, smul_comm r]

theorem pair_swap {n : ℝ} {g g' : Space → Space} (pg : TurnPair n g g') :
    TurnPair n g' (fun y => -g y) := fun φ => by
  filter_upwards [pg φ] with y h1
  rw [h1.1, h1.2]
  refine ⟨by congr 1; simp [sub_eq_add_neg], ?_⟩
  rw [← neg_one_smul ℝ (turnBy φ _), ← turn_smul]
  congr 1
  simp only [smul_add, smul_neg, neg_smul, one_smul, smul_sub]
  abel

theorem pair_neg_mode {n : ℝ} {g g' : Space → Space} (pg : TurnPair (-n) g g') :
    TurnPair n g (fun y => -g' y) := fun φ => by
  filter_upwards [pg φ] with y h1
  rw [h1.1, h1.2]
  simp only [neg_mul, Real.cos_neg, Real.sin_neg]
  refine ⟨by congr 1; simp, ?_⟩
  rw [← neg_one_smul ℝ (turnBy φ _), ← turn_smul]
  congr 1
  simp only [smul_add, smul_neg, neg_smul, one_smul, smul_sub]
  abel

theorem pair_comp {n : ℝ} {L : Space → Space} (hadd : ∀ a b, L (a + b) = L a + L b)
    (hsm : ∀ (r : ℝ) a, L (r • a) = r • L a) (hcomm : ∀ φ w, L (turnBy φ w) = turnBy φ (L w))
    {g g' : Space → Space} (pg : TurnPair n g g') :
    TurnPair n (fun y => L (g y)) (fun y => L (g' y)) := fun φ => by
  have hsub : ∀ a b, L (a - b) = L a - L b := fun a b => by
    rw [sub_eq_add_neg, hadd, ← neg_one_smul ℝ b, hsm, neg_one_smul, sub_eq_add_neg]
  filter_upwards [pg φ] with y h1
  rw [h1.1, h1.2, hcomm, hcomm, hadd, hsub, hsm, hsm, hsm, hsm]
  exact ⟨rfl, rfl⟩

theorem pair_sum {n : ℝ} {ι : Type*} (s : Finset ι) {g g' : ι → Space → Space}
    (pg : ∀ j ∈ s, TurnPair n (g j) (g' j)) :
    TurnPair n (fun y => ∑ j ∈ s, g j y) (fun y => ∑ j ∈ s, g' j y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pair_zero n
  | insert a s ha ih =>
    have h := pair_add (pg a (Finset.mem_insert_self a s)) (ih fun j hj => pg j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert ha] using h

theorem trig_hasDerivAt (n m A B C D : ℝ) :
    HasDerivAt (fun φ : ℝ => Real.cos (n * φ) * Real.cos (m * φ) * A + Real.cos (n * φ) * Real.sin (m * φ) * B +
      Real.sin (n * φ) * Real.cos (m * φ) * C + Real.sin (n * φ) * Real.sin (m * φ) * D) (m * B + n * C) 0 := by
  have hc : ∀ r : ℝ, HasDerivAt (fun φ : ℝ => Real.cos (r * φ)) (-Real.sin (r * 0) * (r * 1)) 0 :=
    fun r => ((hasDerivAt_id (0 : ℝ)).const_mul r).cos
  have hs : ∀ r : ℝ, HasDerivAt (fun φ : ℝ => Real.sin (r * φ)) (Real.cos (r * 0) * (r * 1)) 0 :=
    fun r => ((hasDerivAt_id (0 : ℝ)).const_mul r).sin
  have h := ((((hc n).mul (hc m)).mul_const A).add (((hc n).mul (hs m)).mul_const B)).add
    (((hs n).mul (hc m)).mul_const C) |>.add (((hs n).mul (hs m)).mul_const D)
  apply h.congr_deriv
  simp

theorem int_lin4 {μ : Measure Space} {I1 I2 I3 I4 : Space → ℝ} (h1 : Integrable I1 μ) (h2 : Integrable I2 μ)
    (h3 : Integrable I3 μ) (h4 : Integrable I4 μ) (c1 c2 c3 c4 : ℝ) :
    (∫ y, (c1 * I1 y + c2 * I2 y + c3 * I3 y + c4 * I4 y) ∂μ) =
      c1 * (∫ y, I1 y ∂μ) + c2 * (∫ y, I2 y ∂μ) + c3 * (∫ y, I3 y ∂μ) + c4 * (∫ y, I4 y ∂μ) := by
  have g1 := h1.const_mul c1
  have g2 := h2.const_mul c2
  have g3 := h3.const_mul c3
  have g4 := h4.const_mul c4
  rw [integral_add, integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul]
  all_goals first | exact g1 | exact g2 | exact g3 | exact g4 | exact g1.add g2 | exact (g1.add g2).add g3

theorem int_lin6 {μ : Measure Space} {I1 I2 I3 I4 I5 I6 : Space → ℝ} (h1 : Integrable I1 μ) (h2 : Integrable I2 μ)
    (h3 : Integrable I3 μ) (h4 : Integrable I4 μ) (h5 : Integrable I5 μ) (h6 : Integrable I6 μ) (c1 c2 c3 c4 c5 c6 : ℝ) :
    (∫ y, (c1 * I1 y + c2 * I2 y + c3 * I3 y + c4 * I4 y + c5 * I5 y + c6 * I6 y) ∂μ) =
      c1 * (∫ y, I1 y ∂μ) + c2 * (∫ y, I2 y ∂μ) + c3 * (∫ y, I3 y ∂μ) + c4 * (∫ y, I4 y ∂μ) +
        c5 * (∫ y, I5 y ∂μ) + c6 * (∫ y, I6 y ∂μ) := by
  have g1 := h1.const_mul c1
  have g2 := h2.const_mul c2
  have g3 := h3.const_mul c3
  have g4 := h4.const_mul c4
  have g5 := h5.const_mul c5
  have g6 := h6.const_mul c6
  rw [integral_add, integral_add, integral_add, integral_add, integral_add, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  all_goals first | exact g1 | exact g2 | exact g3 | exact g4 | exact g5 | exact g6 | exact g1.add g2 |
    exact (g1.add g2).add g3 | exact ((g1.add g2).add g3).add g4 | exact (((g1.add g2).add g3).add g4).add g5

theorem inv_integral {C : Set Space} (hC : MeasurableSet C) (hinv : ∀ (φ : ℝ) y, y ∈ C ↔ turnBy φ y ∈ C)
    (φ : ℝ) (F : Space → ℝ) : (∫ y in C, F (turnBy φ y)) = ∫ y in C, F y :=
  (turn_mp_restrict hC hinv φ).integral_comp (turn_embedding φ) F

theorem pair_inner {C : Set Space} (hC : MeasurableSet C) (hinv : ∀ (φ : ℝ) y, y ∈ C ↔ turnBy φ y ∈ C)
    {n m : ℝ} {g g' h h' : Space → Space}
    (hg : MemLp g 2 (volume.restrict C)) (hg' : MemLp g' 2 (volume.restrict C))
    (hh : MemLp h 2 (volume.restrict C)) (hh' : MemLp h' 2 (volume.restrict C))
    (pg : TurnPair n g g') (ph : TurnPair m h h') (φ : ℝ) :
    (∫ y in C, inner ℝ (g y) (h y)) =
      Real.cos (n * φ) * Real.cos (m * φ) * (∫ y in C, inner ℝ (g y) (h y)) +
      Real.cos (n * φ) * Real.sin (m * φ) * (∫ y in C, inner ℝ (g y) (h' y)) +
      Real.sin (n * φ) * Real.cos (m * φ) * (∫ y in C, inner ℝ (g' y) (h y)) +
      Real.sin (n * φ) * Real.sin (m * φ) * (∫ y in C, inner ℝ (g' y) (h' y)) := by
  refine Eq.trans (inv_integral hC hinv φ (fun y => inner ℝ (g y) (h y))).symm ?_
  beta_reduce
  have e : (fun y => inner ℝ (g (turnBy φ y)) (h (turnBy φ y))) =ᵐ[volume.restrict C] fun y =>
      Real.cos (n * φ) * Real.cos (m * φ) * inner ℝ (g y) (h y) +
      Real.cos (n * φ) * Real.sin (m * φ) * inner ℝ (g y) (h' y) +
      Real.sin (n * φ) * Real.cos (m * φ) * inner ℝ (g' y) (h y) +
      Real.sin (n * φ) * Real.sin (m * φ) * inner ℝ (g' y) (h' y) := by
    filter_upwards [ae_restrict_of_ae (pg φ), ae_restrict_of_ae (ph φ)] with y h1 h2
    rw [h1.1, h2.1, turn_inner]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [integral_congr_ae e]
  exact int_lin4 (int_inner hg hh) (int_inner hg hh') (int_inner hg' hh) (int_inner hg' hh') _ _ _ _

theorem pair_orth {C : Set Space} (hC : MeasurableSet C) (hinv : ∀ (φ : ℝ) y, y ∈ C ↔ turnBy φ y ∈ C)
    {n m : ℝ} (hnm : n ^ 2 ≠ m ^ 2) {g g' h h' : Space → Space}
    (hg : MemLp g 2 (volume.restrict C)) (hg' : MemLp g' 2 (volume.restrict C))
    (hh : MemLp h 2 (volume.restrict C)) (hh' : MemLp h' 2 (volume.restrict C))
    (pg : TurnPair n g g') (ph : TurnPair m h h') :
    (∫ y in C, inner ℝ (g y) (h' y)) = 0 := by
  set A := ∫ y in C, inner ℝ (g y) (h y) with hA
  set B := ∫ y in C, inner ℝ (g y) (h' y) with hB
  set Cc := ∫ y in C, inner ℝ (g' y) (h y) with hCc
  set D := ∫ y in C, inner ℝ (g' y) (h' y) with hD
  have k1 := pair_inner hC hinv hg hg' hh hh' pg ph
  have k2 := pair_inner hC hinv hg' hg.neg hh' hh.neg (pair_swap pg) (pair_swap ph)
  simp only [Pi.neg_apply, inner_neg_left, inner_neg_right, integral_neg, neg_neg] at k2
  rw [← hA, ← hB, ← hCc, ← hD] at k2
  have d1 : m * B + n * Cc = 0 := by
    have hd := trig_hasDerivAt n m A B Cc D
    have hf : (fun φ : ℝ => Real.cos (n * φ) * Real.cos (m * φ) * A + Real.cos (n * φ) * Real.sin (m * φ) * B +
      Real.sin (n * φ) * Real.cos (m * φ) * Cc + Real.sin (n * φ) * Real.sin (m * φ) * D) = fun _ => A :=
      funext fun φ => (k1 φ).symm
    rw [hf] at hd
    exact ((hasDerivAt_const (0 : ℝ) A).unique hd).symm
  have d2 : m * (-Cc) + n * (-B) = 0 := by
    have hd := trig_hasDerivAt n m D (-Cc) (-B) A
    have hf : (fun φ : ℝ => Real.cos (n * φ) * Real.cos (m * φ) * D + Real.cos (n * φ) * Real.sin (m * φ) * (-Cc) +
      Real.sin (n * φ) * Real.cos (m * φ) * (-B) + Real.sin (n * φ) * Real.sin (m * φ) * A) = fun _ => D :=
      funext fun φ => (k2 φ).symm
    rw [hf] at hd
    exact ((hasDerivAt_const (0 : ℝ) D).unique hd).symm
  have h3 : (n ^ 2 - m ^ 2) * B = 0 := by linear_combination (-n) * d2 - m * d1
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd (sub_eq_zero.1 h) hnm
  · exact h

theorem pair_orth' {C : Set Space} (hC : MeasurableSet C) (hinv : ∀ (φ : ℝ) y, y ∈ C ↔ turnBy φ y ∈ C)
    {n m : ℝ} (hnm : n ^ 2 ≠ m ^ 2) {g g' h h' : Space → Space}
    (hg : MemLp g 2 (volume.restrict C)) (hg' : MemLp g' 2 (volume.restrict C))
    (hh : MemLp h 2 (volume.restrict C)) (hh' : MemLp h' 2 (volume.restrict C))
    (pg : TurnPair n g g') (ph : TurnPair m h h') :
    (∫ y in C, inner ℝ (g y) (h y)) = 0 := by
  have := pair_orth hC hinv hnm hg hg' hh' hh.neg pg (pair_swap ph)
  simpa only [Pi.neg_apply, inner_neg_right, integral_neg, neg_eq_zero] using this

theorem pair_dual {C : Set Space} (hC : MeasurableSet C) (hinv : ∀ (φ : ℝ) y, y ∈ C ↔ turnBy φ y ∈ C)
    {n : ℝ} {f u u' : Space → Space} (hf : MemLp f 2 (volume.restrict C))
    (hu : MemLp u 2 (volume.restrict C)) (hu' : MemLp u' 2 (volume.restrict C)) (pu : TurnPair n u u') :
    HasDerivAt (fun φ => ∫ y in C, inner ℝ (f y) (u (turnBy (-φ) y)))
      (-(∫ y in C, inner ℝ (f y) (axialTurn (u y))) - n * ∫ y in C, inner ℝ (f y) (u' y)) 0 := by
  have mq : ∀ {g : Space → Space}, MemLp g 2 (volume.restrict C) → MemLp (fun y => qv (g y)) 2 (volume.restrict C) :=
    fun hg => memLp_comp qv_cont qv_norm_le hg
  have mj : ∀ {g : Space → Space}, MemLp g 2 (volume.restrict C) →
      MemLp (fun y => axialTurn (g y)) 2 (volume.restrict C) :=
    fun hg => memLp_comp axialTurn_cont turn_norm_le hg
  set a1 := ∫ y in C, inner ℝ (f y) (qv (u y))
  set a2 := ∫ y in C, inner ℝ (f y) (u y - qv (u y))
  set a3 := ∫ y in C, inner ℝ (f y) (axialTurn (u y))
  set b1 := ∫ y in C, inner ℝ (f y) (qv (u' y))
  set b2 := ∫ y in C, inner ℝ (f y) (u' y - qv (u' y))
  set b3 := ∫ y in C, inner ℝ (f y) (axialTurn (u' y))
  have key : ∀ φ : ℝ, (∫ y in C, inner ℝ (f y) (u (turnBy (-φ) y))) =
      Real.cos (n * φ) * a1 + (Real.cos (n * φ) * Real.cos φ) * a2 + (-(Real.cos (n * φ) * Real.sin φ)) * a3 +
      (-Real.sin (n * φ)) * b1 + (-(Real.sin (n * φ) * Real.cos φ)) * b2 + (Real.sin (n * φ) * Real.sin φ) * b3 := by
    intro φ
    have e : (fun y => inner ℝ (f y) (u (turnBy (-φ) y))) =ᵐ[volume.restrict C] fun y =>
        Real.cos (n * φ) * inner ℝ (f y) (qv (u y)) +
        (Real.cos (n * φ) * Real.cos φ) * inner ℝ (f y) (u y - qv (u y)) +
        (-(Real.cos (n * φ) * Real.sin φ)) * inner ℝ (f y) (axialTurn (u y)) +
        (-Real.sin (n * φ)) * inner ℝ (f y) (qv (u' y)) +
        (-(Real.sin (n * φ) * Real.cos φ)) * inner ℝ (f y) (u' y - qv (u' y)) +
        (Real.sin (n * φ) * Real.sin φ) * inner ℝ (f y) (axialTurn (u' y)) := by
      filter_upwards [ae_restrict_of_ae (pu (-φ))] with y h1
      rw [h1.1, turn_add, turn_smul, turn_smul, turn_neg_formula, turn_neg_formula]
      simp only [mul_neg, Real.cos_neg, Real.sin_neg, inner_add_right, inner_sub_right, real_inner_smul_right]
      ring
    rw [integral_congr_ae e]
    exact int_lin6 (int_inner hf (mq hu)) (int_inner hf (hu.sub (mq hu))) (int_inner hf (mj hu))
      (int_inner hf (mq hu')) (int_inner hf (hu'.sub (mq hu'))) (int_inner hf (mj hu')) _ _ _ _ _ _
  have hsum : b1 + b2 = ∫ y in C, inner ℝ (f y) (u' y) := by
    calc b1 + b2 = ∫ y in C, (inner ℝ (f y) (qv (u' y)) + inner ℝ (f y) (u' y - qv (u' y))) :=
          (integral_add (int_inner hf (mq hu')) (int_inner hf (hu'.sub (mq hu')))).symm
      _ = _ := by
          congr 1
          funext y
          rw [← inner_add_right, add_sub_cancel]
  rw [funext key, ← hsum]
  have hc : ∀ r : ℝ, HasDerivAt (fun φ : ℝ => Real.cos (r * φ)) (-Real.sin (r * 0) * (r * 1)) 0 :=
    fun r => ((hasDerivAt_id (0 : ℝ)).const_mul r).cos
  have hs : ∀ r : ℝ, HasDerivAt (fun φ : ℝ => Real.sin (r * φ)) (Real.cos (r * 0) * (r * 1)) 0 :=
    fun r => ((hasDerivAt_id (0 : ℝ)).const_mul r).sin
  have hc1 : HasDerivAt (fun φ : ℝ => Real.cos φ) (-Real.sin 0) 0 := Real.hasDerivAt_cos 0
  have hs1 : HasDerivAt (fun φ : ℝ => Real.sin φ) (Real.cos 0) 0 := Real.hasDerivAt_sin 0
  have h := (((((hc n).mul_const a1).add (((hc n).mul hc1).mul_const a2)).add
    (((hc n).mul hs1).neg.mul_const a3)).add ((hs n).neg.mul_const b1)).add
    (((hs n).mul hc1).neg.mul_const b2) |>.add (((hs n).mul hs1).mul_const b3)
  apply h.congr_deriv
  simp
  ring

theorem block_pt {α β γ t : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hsum : α + β = t) (hγ : γ ^ 2 ≤ α * t) (a b : Space) :
    ‖α • a + (-β) • axialTurn b + (γ - α) • qv a‖ ^ 2 ≤ α * t * ‖a‖ ^ 2 + β * t * ‖b‖ ^ 2 := by
  subst hsum
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  simp [axialTurn, qv]
  nlinarith [mul_nonneg (mul_nonneg hα hβ) (sq_nonneg (a 0 - b 1)), mul_nonneg (mul_nonneg hα hβ) (sq_nonneg (a 1 + b 0)),
    mul_le_mul_of_nonneg_right hγ (sq_nonneg (a 2)), mul_nonneg (mul_nonneg hβ (add_nonneg hα hβ)) (sq_nonneg (b 2))]

theorem gen_identity (n : ℝ) (hn : 2 ≤ n) (a b : Space) :
    b = -axialTurn ((n / (n ^ 2 - 1)) • a + (-(1 / (n ^ 2 - 1))) • axialTurn b + (1 / n - n / (n ^ 2 - 1)) • qv a) -
      n • ((n / (n ^ 2 - 1)) • (-b) + (-(1 / (n ^ 2 - 1))) • axialTurn a + (1 / n - n / (n ^ 2 - 1)) • qv (-b)) := by
  have h1 : n ^ 2 - 1 ≠ 0 := by nlinarith
  have h2 : n ≠ 0 := by linarith
  ext i
  fin_cases i <;> simp [axialTurn, qv] <;> field_simp <;> ring

theorem norm_comb {ι : Type*} [DecidableEq ι] {μ : Measure Space} (B : Finset ι) (w : ι → ℝ) (E : ι → Space → Space)
    (hm : ∀ a ∈ B, MemLp (E a) 2 μ)
    (G : ∀ a ∈ B, ∀ b ∈ B, (∫ y, inner ℝ (E a y) (E b y) ∂μ) = if a = b then 1 else 0) :
    (∫ y, ‖∑ a ∈ B, w a • E a y‖ ^ 2 ∂μ) = ∑ a ∈ B, w a ^ 2 := by
  have e1 : ∀ y, ‖∑ a ∈ B, w a • E a y‖ ^ 2 = ∑ a ∈ B, ∑ b ∈ B, w a * w b * inner ℝ (E a y) (E b y) := by
    intro y
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  simp_rw [e1]
  rw [integral_finset_sum _ (fun a ha => integrable_finset_sum _ fun b hb => (int_inner (hm a ha) (hm b hb)).const_mul _)]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [integral_finset_sum _ (fun b hb => (int_inner (hm a ha) (hm b hb)).const_mul _)]
  rw [Finset.sum_eq_single a]
  · rw [integral_const_mul, G a ha a ha]
    simp
    ring
  · intro b hb hba
    rw [integral_const_mul, G a ha b hb, if_neg (Ne.symm hba)]
    ring
  · intro h
    exact absurd ha h

theorem norm_sum_orth {ι : Type*} {μ : Measure Space} (s : Finset ι) (v : ι → Space → Space)
    (hm : ∀ n ∈ s, MemLp (v n) 2 μ)
    (ho : ∀ n ∈ s, ∀ m ∈ s, n ≠ m → (∫ y, inner ℝ (v n y) (v m y) ∂μ) = 0) :
    (∫ y, ‖∑ n ∈ s, v n y‖ ^ 2 ∂μ) = ∑ n ∈ s, ∫ y, ‖v n y‖ ^ 2 ∂μ := by
  classical
  have e1 : ∀ y, ‖∑ n ∈ s, v n y‖ ^ 2 = ∑ n ∈ s, ∑ m ∈ s, inner ℝ (v n y) (v m y) := by
    intro y
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_sum]
  simp_rw [e1]
  rw [integral_finset_sum _ (fun a ha => integrable_finset_sum _ fun b hb => int_inner (hm a ha) (hm b hb))]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [integral_finset_sum _ (fun b hb => int_inner (hm a ha) (hm b hb))]
  rw [Finset.sum_eq_single a]
  · simp only [real_inner_self_eq_norm_sq]
  · intro b hb hba
    exact ho a ha b hb (Ne.symm hba)
  · intro h
    exact absurd ha h

theorem pair_abs {k : ℝ} {g g' : Space → Space} (pg : TurnPair k g g') :
    TurnPair |k| g (fun y => (if 0 ≤ k then (1 : ℝ) else -1) • g' y) := by
  split_ifs with h
  · rw [abs_of_nonneg h]
    simpa using pg
  · rw [abs_of_neg (not_le.1 h)]
    have := pair_neg_mode (n := -k) (by rwa [neg_neg])
    simpa using this

theorem memLp_lin3 {μ : Measure Space} {g h : Space → Space} (hg : MemLp g 2 μ) (hh : MemLp h 2 μ) (r s t : ℝ) :
    MemLp (fun y => r • g y + s • axialTurn (h y) + t • qv (g y)) 2 μ := by
  have e : (fun y => r • g y + s • axialTurn (h y) + t • qv (g y)) =
      (r • g + s • (fun y => axialTurn (h y))) + t • (fun y => qv (g y)) := by
    funext y
    simp
  rw [e]
  exact ((hg.const_smul r).add ((memLp_comp axialTurn_cont turn_norm_le hh).const_smul s)).add
    ((memLp_comp qv_cont qv_norm_le hg).const_smul t)

end RowRotationCellInternal

open RowRotationCellInternal RotationLeavesInternal in
theorem rowRotationCoefEnergy : RowRotationCoefEnergyStatement := by
  intro k N c T hT i f hf X hX
  have hC : MeasurableSet (T.cellSet i) := hT.cell_measurable i
  have hinv : ∀ (φ : ℝ) y, y ∈ T.cellSet i ↔ turnBy φ y ∈ T.cellSet i := hT.cell_turn i
  obtain ⟨kk, hkk⟩ : ∃ kk : Fin N → ℝ, ∀ a, kk a = (T.modeNum a : ℝ) := ⟨_, fun _ => rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : Fin N → ℝ, ∀ a, p a = ∫ y in T.cellSet i, inner ℝ (f y) (c.row a y) := ⟨_, fun _ => rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Fin N → ℝ, ∀ a, μ a = ((|kk a| - 1) ⊔ 0) ^ 2 * p a := ⟨_, fun _ => rfl⟩
  obtain ⟨sg, hsg⟩ : ∃ sg : Fin N → ℝ, ∀ a, sg a = if 0 ≤ kk a then (1 : ℝ) else -1 := ⟨_, fun _ => rfl⟩
  set F2 := (Finset.univ.filter (fun a => T.cellOf a = i)).filter (fun a => 2 ≤ |kk a|) with hF2
  set Ns := F2.image (fun a => |kk a|) with hNs
  obtain ⟨M, hM⟩ : ∃ M : ℝ → Space → Space, ∀ n y, M n y = ∑ a ∈ F2.filter (fun a => |kk a| = n), μ a • c.row a y :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M' : ℝ → Space → Space, ∀ n y,
      M' n y = ∑ a ∈ F2.filter (fun a => |kk a| = n), (μ a * sg a) • c.row (T.partner a) y := ⟨_, fun _ _ => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ → Space → Space, ∀ n y, u n y = (n / (n ^ 2 - 1)) • M' n y +
      (-(1 / (n ^ 2 - 1))) • axialTurn (M n y) + (1 / n - n / (n ^ 2 - 1)) • qv (M' n y) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨u', hu'⟩ : ∃ u' : ℝ → Space → Space, ∀ n y, u' n y = (n / (n ^ 2 - 1)) • (-(M n y)) +
      (-(1 / (n ^ 2 - 1))) • axialTurn (M' n y) + (1 / n - n / (n ^ 2 - 1)) • qv (-(M n y)) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Space → Space, ∀ y, U y = ∑ n ∈ Ns, u n y := ⟨_, fun _ => rfl⟩
  have hmemC : ∀ a, MemLp (c.row a) 2 (volume.restrict (T.cellSet i)) := fun a => (hT.row_memLp a).restrict _
  have hsupp : ∀ a, T.cellOf a = i → ∀ g : Space → Space,
      (∫ y in T.cellSet i, inner ℝ (g y) (c.row a y)) = ∫ y, inner ℝ (g y) (c.row a y) := by
    intro a ha g
    refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
    filter_upwards [hT.row_support a] with y hy hyC
    have : c.row a y = 0 := by
      by_contra hne
      exact hyC (ha ▸ hy hne)
    rw [this, inner_zero_right]
  have hB : ∀ n a, a ∈ F2.filter (fun a => |kk a| = n) → T.cellOf a = i ∧ 2 ≤ |kk a| ∧ |kk a| = n := by
    intro n a ha
    simp only [hF2, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact ⟨ha.1.1, ha.1.2, ha.2⟩
  have hNs2 : ∀ n ∈ Ns, 2 ≤ n := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hn
    simp only [hF2, Finset.mem_filter] at ha
    exact ha.2
  have rowpair : ∀ a, TurnPair (kk a) (c.row a) (c.row (T.partner a)) := by
    intro a φ
    filter_upwards [axis_null] with y hy
    refine ⟨by rw [hkk]; exact hT.row_mode a φ y hy, ?_⟩
    rw [hT.row_mode (T.partner a) φ y hy, hT.partner_invol, hT.partner_mode, hkk]
    simp [neg_mul, Real.cos_neg, Real.sin_neg, sub_eq_add_neg]
  have pabs : ∀ a, TurnPair |kk a| (c.row a) (fun y => sg a • c.row (T.partner a) y) := by
    intro a
    have h := pair_abs (rowpair a)
    rw [← hsg a] at h
    exact h
  have pM : ∀ n, TurnPair n (M n) (M' n) := by
    intro n
    have h := pair_sum (F2.filter (fun a => |kk a| = n)) (n := n) (g := fun a y => μ a • c.row a y)
      (g' := fun a y => (μ a * sg a) • c.row (T.partner a) y) (fun a ha => by
        have h1 := pair_smul (μ a) (pabs a)
        rw [(hB n a ha).2.2] at h1
        simpa only [smul_smul] using h1)
    rw [funext (hM n), funext (hM' n)]
    exact h
  have pu : ∀ n, TurnPair n (u n) (u' n) := by
    intro n
    have h := pair_add (pair_add (pair_smul (n / (n ^ 2 - 1)) (pair_swap (pM n)))
      (pair_smul (-(1 / (n ^ 2 - 1))) (pair_comp axialTurn_add axialTurn_smul axialTurn_comm (pM n))))
      (pair_smul (1 / n - n / (n ^ 2 - 1)) (pair_comp qv_add qv_smul qv_comm (pair_swap (pM n))))
    rw [funext (hu n), funext (hu' n)]
    exact h
  have mM : ∀ n, MemLp (M n) 2 (volume.restrict (T.cellSet i)) := by
    intro n
    rw [funext (hM n)]
    exact memLp_finset_sum _ fun a _ => (hmemC a).const_smul (μ a)
  have mM' : ∀ n, MemLp (M' n) 2 (volume.restrict (T.cellSet i)) := by
    intro n
    rw [funext (hM' n)]
    exact memLp_finset_sum _ fun a _ => (hmemC (T.partner a)).const_smul (μ a * sg a)
  have mu : ∀ n, MemLp (u n) 2 (volume.restrict (T.cellSet i)) := by
    intro n
    rw [funext (hu n)]
    exact memLp_lin3 (mM' n) (mM n) _ _ _
  have mu' : ∀ n, MemLp (u' n) 2 (volume.restrict (T.cellSet i)) := by
    intro n
    rw [funext (hu' n)]
    have hneg : MemLp (fun y => -(M n y)) 2 (volume.restrict (T.cellSet i)) := (mM n).neg
    exact memLp_lin3 (g := fun y => -(M n y)) hneg (mM' n) _ _ _
  have mU : MemLp U 2 (volume.restrict (T.cellSet i)) := by
    rw [funext hU]
    exact memLp_finset_sum _ fun n _ => mu n
  have hd : HasDerivAt (fun φ => ∫ y in T.cellSet i, inner ℝ (f y) (U (turnBy (-φ) y)))
      (∑ n ∈ Ns, (-(∫ y in T.cellSet i, inner ℝ (f y) (axialTurn (u n y))) -
        n * ∫ y in T.cellSet i, inner ℝ (f y) (u' n y))) 0 := by
    have e1 : (fun φ => ∫ y in T.cellSet i, inner ℝ (f y) (U (turnBy (-φ) y))) =
        fun φ => ∑ n ∈ Ns, ∫ y in T.cellSet i, inner ℝ (f y) (u n (turnBy (-φ) y)) := by
      funext φ
      simp only [hU, inner_sum]
      exact integral_finset_sum _ fun n _ =>
        int_inner hf ((mu n).comp_measurePreserving (turn_mp_restrict hC hinv (-φ)))
    rw [e1]
    have h := HasDerivAt.sum (u := Ns) fun n _ => pair_dual hC hinv hf (mu n) (mu' n) (pu n)
    have e2 : (fun φ => ∑ n ∈ Ns, ∫ y in T.cellSet i, inner ℝ (f y) (u n (turnBy (-φ) y))) =
        ∑ n ∈ Ns, fun φ => ∫ y in T.cellSet i, inner ℝ (f y) (u n (turnBy (-φ) y)) := by
      funext φ
      rw [Finset.sum_apply]
    rw [e2]
    exact h
  have hterm : ∀ n ∈ Ns, (-(∫ y in T.cellSet i, inner ℝ (f y) (axialTurn (u n y))) -
      n * ∫ y in T.cellSet i, inner ℝ (f y) (u' n y)) = ∫ y in T.cellSet i, inner ℝ (f y) (M n y) := by
    intro n hn
    have hn2 := hNs2 n hn
    have pid : ∀ y, inner ℝ (f y) (M n y) =
        -(inner ℝ (f y) (axialTurn (u n y))) - n * inner ℝ (f y) (u' n y) := by
      intro y
      rw [hu n y, hu' n y]
      conv_lhs => rw [gen_identity n hn2 (M' n y) (M n y)]
      rw [inner_sub_right, inner_neg_right, real_inner_smul_right]
    rw [integral_congr_ae (Eventually.of_forall pid), integral_sub, integral_neg, integral_const_mul]
    · exact (int_inner hf (memLp_comp axialTurn_cont turn_norm_le (mu n))).neg
    · exact (int_inner hf (mu' n)).const_mul n
  have hMn : ∀ n, (∫ y in T.cellSet i, inner ℝ (f y) (M n y)) =
      ∑ a ∈ F2.filter (fun a => |kk a| = n), μ a * p a := by
    intro n
    simp only [hM, inner_sum, real_inner_smul_right]
    rw [integral_finset_sum _ fun a _ => (int_inner hf (hmemC a)).const_mul _]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_const_mul, hp]
  have hfib : ∑ n ∈ Ns, ∑ a ∈ F2.filter (fun a => |kk a| = n), μ a * p a = ∑ a ∈ F2, μ a * p a :=
    Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem _ ha) _
  have hpairMat : ∀ a b, T.cellOf a = i → T.cellOf b = i →
      (∫ y in T.cellSet i, inner ℝ (c.row a y) (c.row b y)) = if a = b then 1 else 0 := by
    intro a b _ hb
    rw [hsupp b hb, ← hT.row_orthonormal a b]
    rfl
  have hblock : ∀ n ∈ Ns, (∫ y in T.cellSet i, ‖u n y‖ ^ 2) ≤ ∑ a ∈ F2.filter (fun a => |kk a| = n), μ a * p a := by
    intro n hn
    have hn2 := hNs2 n hn
    have hd1 : 0 < n ^ 2 - 1 := by nlinarith
    have hd2 : 0 < n - 1 := by linarith
    have hα : 0 ≤ n / (n ^ 2 - 1) := by positivity
    have hβ : 0 ≤ 1 / (n ^ 2 - 1) := by positivity
    have hsum : n / (n ^ 2 - 1) + 1 / (n ^ 2 - 1) = 1 / (n - 1) := by
      field_simp
      ring
    have hγ : (1 / n) ^ 2 ≤ n / (n ^ 2 - 1) * (1 / (n - 1)) := by
      rw [div_pow, one_pow, div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have pt : ∀ y, ‖u n y‖ ^ 2 ≤ n / (n ^ 2 - 1) * (1 / (n - 1)) * ‖M' n y‖ ^ 2 +
        1 / (n ^ 2 - 1) * (1 / (n - 1)) * ‖M n y‖ ^ 2 := by
      intro y
      rw [hu n y]
      have := block_pt hα hβ hsum hγ (M' n y) (M n y)
      rwa [sub_eq_add_neg (1 / n)] at this ⊢
    have i1 : (∫ y in T.cellSet i, ‖M n y‖ ^ 2) = ∑ a ∈ F2.filter (fun a => |kk a| = n), μ a ^ 2 := by
      simp only [hM]
      exact norm_comb _ μ c.row (fun a _ => hmemC a)
        (fun a ha b hb => hpairMat a b (hB n a ha).1 (hB n b hb).1)
    have i2 : (∫ y in T.cellSet i, ‖M' n y‖ ^ 2) = ∑ a ∈ F2.filter (fun a => |kk a| = n), μ a ^ 2 := by
      simp only [hM']
      rw [norm_comb _ (fun a => μ a * sg a) (fun a => c.row (T.partner a)) (fun a _ => hmemC _)
        (fun a ha b hb => by
          rw [hpairMat _ _ ((hT.partner_cell a).trans (hB n a ha).1) ((hT.partner_cell b).trans (hB n b hb).1)]
          congr 1
          exact propext ⟨fun h => by simpa [hT.partner_invol] using congrArg T.partner h, fun h => h ▸ rfl⟩)]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_pow, hsg a]
      split_ifs <;> norm_num
    have hiM : Integrable (fun y => ‖M n y‖ ^ 2) (volume.restrict (T.cellSet i)) :=
      (memLp_two_iff_integrable_sq_norm (mM n).1).1 (mM n)
    have hiM' : Integrable (fun y => ‖M' n y‖ ^ 2) (volume.restrict (T.cellSet i)) :=
      (memLp_two_iff_integrable_sq_norm (mM' n).1).1 (mM' n)
    have hiu : Integrable (fun y => ‖u n y‖ ^ 2) (volume.restrict (T.cellSet i)) :=
      (memLp_two_iff_integrable_sq_norm (mu n).1).1 (mu n)
    calc (∫ y in T.cellSet i, ‖u n y‖ ^ 2)
        ≤ ∫ y in T.cellSet i, (n / (n ^ 2 - 1) * (1 / (n - 1)) * ‖M' n y‖ ^ 2 +
            1 / (n ^ 2 - 1) * (1 / (n - 1)) * ‖M n y‖ ^ 2) :=
          integral_mono hiu ((hiM'.const_mul _).add (hiM.const_mul _)) pt
      _ = (n / (n ^ 2 - 1) * (1 / (n - 1))) * (∑ a ∈ F2.filter (fun a => |kk a| = n), μ a ^ 2) +
            (1 / (n ^ 2 - 1) * (1 / (n - 1))) * ∑ a ∈ F2.filter (fun a => |kk a| = n), μ a ^ 2 := by
          rw [integral_add (hiM'.const_mul _) (hiM.const_mul _), integral_const_mul, integral_const_mul, i1, i2]
      _ = ∑ a ∈ F2.filter (fun a => |kk a| = n), μ a * p a := by
          rw [← add_mul, ← add_mul, hsum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a ha => ?_
          have ha' := (hB n a ha).2.2
          rw [hμ a, ha', max_eq_left (by linarith)]
          field_simp
  have hnormU : (∫ y in T.cellSet i, ‖U y‖ ^ 2) = ∑ n ∈ Ns, ∫ y in T.cellSet i, ‖u n y‖ ^ 2 := by
    simp only [hU]
    refine norm_sum_orth Ns u (fun n _ => mu n) fun n hn m hm hnm => ?_
    refine pair_orth' hC hinv ?_ (mu n) (mu' n) (mu m) (mu' m) (pu n) (pu m)
    intro h
    have h1 := hNs2 n hn
    have h2 := hNs2 m hm
    exact hnm (by nlinarith)
  have key := rotation_deriv_sq_le hC hinv hf mU hX hd
  rw [Finset.sum_congr rfl hterm] at key
  simp only [hMn] at key
  rw [hfib] at key
  have hUle : (∫ y in T.cellSet i, ‖U y‖ ^ 2) ≤ ∑ a ∈ F2, μ a * p a := by
    rw [hnormU, ← hfib]
    exact Finset.sum_le_sum hblock
  have hXn : 0 ≤ X := by
    have h1 := hX 1
    have h2 : 0 ≤ ∫ y in T.cellSet i, ‖f (turnBy 1 y) - f y‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
    nlinarith
  have hT0 : 0 ≤ ∑ a ∈ F2, μ a * p a := Finset.sum_nonneg fun a _ => by rw [hμ a]; nlinarith [sq_nonneg (p a), sq_nonneg ((|kk a| - 1) ⊔ 0)]
  have hL : (∑ a ∈ Finset.univ.filter (fun a => T.cellOf a = i),
      ((|(T.modeNum a : ℝ)| - 1) ⊔ 0) ^ 2 * l2Pair f (c.row a) ^ 2) = ∑ a ∈ F2, μ a * p a := by
    rw [hF2, Finset.sum_filter_of_ne (s := Finset.univ.filter (fun a => T.cellOf a = i))]
    · refine Finset.sum_congr rfl fun a ha => ?_
      have hca := (Finset.mem_filter.1 ha).2
      rw [hμ a, hp a, hsupp a hca, hkk]
      unfold l2Pair
      ring
    · intro a _ hne
      rw [hkk]
      by_contra hlt
      apply hne
      have hm0 : T.modeNum a = 0 := by
        by_contra h0
        have := hT.mode_large a h0
        have h2 : (2 : ℝ) ≤ c.order := by exact_mod_cast hT.order_ge
        exact hlt (h2.trans this)
      rw [hμ a, hkk, hm0]
      norm_num
  rw [hL]
  rcases hT0.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact hXn
  · nlinarith [mul_le_mul_of_nonneg_left hUle hXn]

theorem rowModeGradient : RowModeGradientStatement :=
  rowModeGradient_of_parts rotationDifference rowRotationCoefEnergy

end Reduction

end CellCert

end Breakdown
