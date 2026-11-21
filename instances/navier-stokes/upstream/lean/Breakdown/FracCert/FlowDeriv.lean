import Breakdown.FracCert.FlowPairing
import Breakdown.Frac.TorusSelfSimilar

open scoped ContDiff ENNReal Topology
open MeasureTheory Real Filter

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace Internal.FlowDeriv

open Internal.FlowPairing

theorem freqTurn_smul (r : ℝ) (z : Freq.CSpace) : freqTurn (r • z) = r • freqTurn z := by
  ext i; fin_cases i <;> simp [freqTurn]

theorem freqTurn_sub (z w : Freq.CSpace) : freqTurn (z - w) = freqTurn z - freqTurn w := by
  ext i
  fin_cases i <;> simp [freqTurn]
  ring

theorem axialTurn_sub (z w : Space) : axialTurn (z - w) = axialTurn z - axialTurn w := by
  ext i
  fin_cases i <;> simp [axialTurn]
  ring

theorem norm_freqTurn_le (z : Freq.CSpace) : ‖freqTurn z‖ ≤ ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp [Fin.sum_univ_three, freqTurn]
  nlinarith [sq_nonneg ‖z 2‖, sq_nonneg ‖z 0‖, sq_nonneg ‖z 1‖]

theorem norm_axialTurn_le (z : Space) : ‖axialTurn z‖ ≤ ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp [Fin.sum_univ_three, axialTurn]
  nlinarith [sq_nonneg (z 2), sq_nonneg (z 0), sq_nonneg (z 1)]

theorem continuous_freqTurn : Continuous freqTurn :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun z w => by
    rw [dist_eq_norm, dist_eq_norm, ← freqTurn_sub]
    simpa using norm_freqTurn_le (z - w)).continuous

theorem continuous_axialTurn : Continuous axialTurn :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun z w => by
    rw [dist_eq_norm, dist_eq_norm, ← axialTurn_sub]
    simpa using norm_axialTurn_le (z - w)).continuous

theorem rotC_eq_sum (R : Space ≃ₗᵢ[ℝ] Space) (w : Freq.CSpace) :
    Freq.rotC R w = ∑ j : Fin 3, (w j) • Freq.complexifyVec (R (unitVector j)) := by
  ext i
  rw [Freq.Internal.Rotation.rotC_apply]
  simp [Freq.complexifyVec, mul_comm]

theorem hasDerivAt_rotC {φ : ℝ → ℝ} {w : ℝ → Freq.CSpace} {φ' t : ℝ} {w' : Freq.CSpace}
    (hφ : HasDerivAt φ φ' t) (hw : HasDerivAt w w' t) :
    HasDerivAt (fun τ => Freq.rotC (axialRotation (φ τ)) (w τ))
      (φ' • freqTurn (Freq.rotC (axialRotation (φ t)) (w t)) +
        Freq.rotC (axialRotation (φ t)) w') t := by
  have hj : ∀ j ∈ (Finset.univ : Finset (Fin 3)), HasDerivAt
      (fun τ => (w τ j) • Freq.complexifyVec (axialRotation (φ τ) (unitVector j)))
      ((w t j) • Freq.complexifyVec (φ' • axialTurn (axialRotation (φ t) (unitVector j)) +
        axialRotation (φ t) 0) + (w' j) • Freq.complexifyVec (axialRotation (φ t) (unitVector j))) t := by
    intro j _
    have hc : HasDerivAt (fun τ => w τ j) (w' j) t := by
      have := ((EuclideanSpace.proj j : Freq.CSpace →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hw
      exact this
    have hr := Periodic.FracSelfSimilar.Internal.rot_hasDerivAt axialRotationSpec hφ
      (hasDerivAt_const t (unitVector j))
    have hf := Freq.complexifyVec.hasFDerivAt.comp_hasDerivAt t hr
    exact hc.smul hf
  have hs := HasDerivAt.sum hj
  have hfun : (fun τ => Freq.rotC (axialRotation (φ τ)) (w τ)) =
      fun τ => ∑ j ∈ (Finset.univ : Finset (Fin 3)),
        (w τ j) • Freq.complexifyVec (axialRotation (φ τ) (unitVector j)) := by
    funext τ
    rw [rotC_eq_sum]
  rw [hfun]
  refine hs.congr_deriv ?_
  rw [rotC_eq_sum, rotC_eq_sum]
  ext i
  fin_cases i <;> simp [Fin.sum_univ_three, freqTurn, axialTurn, Freq.complexifyVec] <;> ring

theorem fderiv_flowPush (α a s : ℝ) {ψ : Space → Freq.CSpace} (hψ : ContDiff ℝ ∞ ψ) (ξ v : Space) :
    fderiv ℝ (flowPush α a s ψ) ξ v = flowValue (-a) (1 - 1 / (2 * α)) s
      (fderiv ℝ ψ (flowLin (-(1 / (2 * α))) (-a) s ξ) (flowLin (-(1 / (2 * α))) (-a) s v)) := by
  have hL := (flowLin (-(1 / (2 * α))) (-a) s).hasFDerivAt (x := ξ)
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ (flowLin (-(1 / (2 * α))) (-a) s ξ))
      (flowLin (-(1 / (2 * α))) (-a) s ξ) := (hψ.differentiable (by simp) _).hasFDerivAt
  have h := (flowValue (-a) (1 - 1 / (2 * α)) s).hasFDerivAt.comp ξ (hψd.comp ξ hL)
  have e : flowPush α a s ψ = ⇑(flowValue (-a) (1 - 1 / (2 * α)) s) ∘
      (ψ ∘ ⇑(flowLin (-(1 / (2 * α))) (-a) s)) := rfl
  rw [e, h.fderiv]
  rfl

theorem hasDerivAt_flowPush (α a : ℝ) {ψ : Space → Freq.CSpace} (hψ : ContDiff ℝ ∞ ψ) (s : ℝ)
    (ξ : Space) :
    HasDerivAt (fun s => flowPush α a s ψ ξ) (flowAdjoint α a (flowPush α a s ψ) ξ) s := by
  have hfun : (fun s => flowPush α a s ψ ξ) = fun τ => Real.exp ((1 - 1 / (2 * α)) * τ) •
      Freq.rotC (axialRotation (-(-a * τ)))
        (ψ (Real.exp (-(-(1 / (2 * α)) * τ)) • axialRotation (-a * τ) ξ)) := by
    funext τ
    simp only [flowPush, flowPull, flowValue, flowLin_apply, FunLike.coe_smul,
      Pi.smul_apply]
  have hθ1 : HasDerivAt (fun τ : ℝ => -a * τ) (-a * 1) s := (hasDerivAt_id s).const_mul (-a)
  have hθ2 : HasDerivAt (fun τ : ℝ => -(-a * τ)) (-(-a * 1)) s := hθ1.neg
  have hg1 : HasDerivAt (fun τ : ℝ => -(-(1 / (2 * α)) * τ)) (-(-(1 / (2 * α)) * 1)) s :=
    ((hasDerivAt_id s).const_mul _).neg
  have he1 := hg1.exp
  have hc1 : HasDerivAt (fun τ : ℝ => (1 - 1 / (2 * α)) * τ) ((1 - 1 / (2 * α)) * 1) s :=
    (hasDerivAt_id s).const_mul _
  have he2 := hc1.exp
  have hr := Periodic.FracSelfSimilar.Internal.rot_hasDerivAt axialRotationSpec hθ1
    (hasDerivAt_const s ξ)
  have hy := he1.smul hr
  have hpsi := (hψ.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s hy
  have hrot := hasDerivAt_rotC hθ2 hpsi
  have hall := he2.smul hrot
  rw [hfun]
  refine hall.congr_deriv ?_
  unfold flowAdjoint
  rw [fderiv_flowPush α a s hψ, fderiv_flowPush α a s hψ]
  simp only [flowPush, flowPull, flowValue, flowLin_apply,
    FunLike.coe_smul, Pi.smul_apply, Function.comp_apply,
    ← Periodic.FracSelfSimilar.Internal.turn_comm axialRotationSpec, map_add, map_smul, map_zero,
    add_zero, freqTurn_smul, smul_add]
  module

theorem flowAdjoint_of_notMem (α a : ℝ) {φ : Space → Freq.CSpace} {ξ : Space}
    (hξ : ξ ∉ tsupport φ) : flowAdjoint α a φ ξ = 0 := by
  have h0 := image_eq_zero_of_notMem_tsupport hξ
  have h1 : fderiv ℝ φ ξ = 0 :=
    Function.notMem_support.1 (fun hm => hξ (support_fderiv_subset ℝ hm))
  have h2 : freqTurn 0 = 0 := by ext i; fin_cases i <;> simp [freqTurn]
  simp [flowAdjoint, h0, h1, h2]

theorem continuous_flowAdjoint (α a : ℝ) {φ : Space → Freq.CSpace} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (flowAdjoint α a φ) := by
  have hc := hφ.continuous
  have hd := hφ.continuous_fderiv (by simp)
  unfold flowAdjoint
  refine ((Continuous.add ?_ ?_).sub ?_).add ?_
  · exact hc.const_smul (1 - 1 / (2 * α))
  · have h := hd.clm_apply continuous_id
    exact h.const_smul (1 / (2 * α))
  · have h := hd.clm_apply continuous_axialTurn
    exact h.const_smul a
  · exact (continuous_freqTurn.comp hc).const_smul a

theorem norm_flowAdjoint_le (α a : ℝ) {φ : Space → Freq.CSpace} (ξ : Space) {A B : ℝ}
    (hB : 0 ≤ B) (h0 : ‖φ ξ‖ ≤ A) (hd : ∀ v, ‖fderiv ℝ φ ξ v‖ ≤ B * ‖v‖) :
    ‖flowAdjoint α a φ ξ‖ ≤ |1 - 1 / (2 * α)| * A + |1 / (2 * α)| * (B * ‖ξ‖) +
      |a| * (B * ‖ξ‖) + |a| * A := by
  unfold flowAdjoint
  refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left h0 (abs_nonneg _)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hd ξ) (abs_nonneg _)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((hd _).trans
      (mul_le_mul_of_nonneg_left (norm_axialTurn_le ξ) hB)) (abs_nonneg _)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((norm_freqTurn_le _).trans h0) (abs_nonneg _)

theorem norm_flowAdjoint_push_le (α a x : ℝ) {ψ : Space → Freq.CSpace} (hψ : ContDiff ℝ ∞ ψ)
    {Cψ Cd : ℝ} (hCψ : ∀ y, ‖ψ y‖ ≤ Cψ) (hCd : ∀ y, ‖fderiv ℝ ψ y‖ ≤ Cd) (ξ : Space) :
    ‖flowAdjoint α a (flowPush α a x ψ) ξ‖ ≤
      |1 - 1 / (2 * α)| * (Real.exp ((1 - 1 / (2 * α)) * x) * Cψ) +
      |1 / (2 * α)| * (Real.exp ((1 - 1 / (2 * α)) * x) * (Cd * Real.exp (1 / (2 * α) * x)) * ‖ξ‖) +
      |a| * (Real.exp ((1 - 1 / (2 * α)) * x) * (Cd * Real.exp (1 / (2 * α) * x)) * ‖ξ‖) +
      |a| * (Real.exp ((1 - 1 / (2 * α)) * x) * Cψ) := by
  have hCd0 : 0 ≤ Cd := (norm_nonneg _).trans (hCd 0)
  have hlin : ∀ v, ‖flowLin (-(1 / (2 * α))) (-a) x v‖ = Real.exp (1 / (2 * α) * x) * ‖v‖ := by
    intro v
    rw [norm_flowLin]
    congr 2
    ring
  refine norm_flowAdjoint_le α a ξ (by positivity) ?_ ?_
  · simp only [flowPush, flowPull]
    rw [norm_flowValue]
    exact mul_le_mul_of_nonneg_left (hCψ _) (Real.exp_pos _).le
  · intro v
    rw [fderiv_flowPush α a x hψ, norm_flowValue]
    have h1 := (fderiv ℝ ψ (flowLin (-(1 / (2 * α))) (-a) x ξ)).le_opNorm
      (flowLin (-(1 / (2 * α))) (-a) x v)
    rw [hlin] at h1
    have h2 : ‖fderiv ℝ ψ (flowLin (-(1 / (2 * α))) (-a) x ξ)‖ *
        (Real.exp (1 / (2 * α) * x) * ‖v‖) ≤ Cd * (Real.exp (1 / (2 * α) * x) * ‖v‖) :=
      mul_le_mul_of_nonneg_right (hCd _) (by positivity)
    calc Real.exp ((1 - 1 / (2 * α)) * x) *
          ‖fderiv ℝ ψ (flowLin (-(1 / (2 * α))) (-a) x ξ) (flowLin (-(1 / (2 * α))) (-a) x v)‖
        ≤ Real.exp ((1 - 1 / (2 * α)) * x) * (Cd * (Real.exp (1 / (2 * α) * x) * ‖v‖)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos _).le
      _ = _ := by ring

end Internal.FlowDeriv

open Internal.FlowPairing Internal.FlowDeriv in
theorem flowDeriv : FlowDerivStatement := by
  intro α hα1 hα2 a h h1 ψ hψ s₀
  have hα0 : 0 < α := by linarith
  have hg0 : 0 < 1 / (2 * α) := by positivity
  have hm : AEStronglyMeasurable h volume := by
    have := ((Internal.DriftPower.measurable_freqPow 1).inv.aestronglyMeasurable).smul h1.1
    refine this.congr ?_
    filter_upwards [Internal.DriftPower.ae_ne_zero] with ξ hξ
    have : freqPow 1 ξ ≠ 0 := by unfold freqPow; rw [Real.rpow_one]; positivity
    simp only [Pi.smul_apply', Pi.inv_apply, smul_smul, inv_mul_cancel₀ this, one_smul]
  obtain ⟨Cψ, hCψ⟩ := hψ.1.continuous.bounded_above_of_compact_support hψ.2.1
  obtain ⟨Cd, hCd⟩ :=
    (hψ.1.continuous_fderiv (by simp)).bounded_above_of_compact_support (hψ.2.1.fderiv ℝ)
  have hCψ0 : 0 ≤ Cψ := (norm_nonneg _).trans (hCψ 0)
  have hCd0 : 0 ≤ Cd := (norm_nonneg _).trans (hCd 0)
  obtain ⟨R0, hR0⟩ := hψ.2.1.isCompact.isBounded.subset_closedBall (0 : Space)
  obtain ⟨r0, hr0, hball⟩ :=
    Metric.mem_nhds_iff.1 ((isClosed_tsupport ψ).isOpen_compl.mem_nhds hψ.2.2)
  have hlow : ∀ y ∈ tsupport ψ, r0 ≤ ‖y‖ := by
    intro y hy
    by_contra hlt
    exact hball (mem_ball_zero_iff.2 (not_le.1 hlt)) hy
  set T : ℝ := |s₀| + 1 with hT
  set E : ℝ := Real.exp (1 / (2 * α) * T) with hE
  set E1 : ℝ := Real.exp (|1 - 1 / (2 * α)| * T) with hE1
  set K : Set Space := {ξ | r0 / E ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ R0 * E} with hK
  set B : ℝ := E1 * (Cd * E) with hB
  set M : ℝ := |1 - 1 / (2 * α)| * (E1 * Cψ) + |1 / (2 * α)| * (B * (R0 * E)) +
    |a| * (B * (R0 * E)) + |a| * (E1 * Cψ) with hM
  have hE0 : 0 < E := Real.exp_pos _
  have hE10 : 0 < E1 := Real.exp_pos _
  have hball1 : ∀ x ∈ Metric.ball s₀ 1, |x| ≤ T := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx
    have := abs_sub_abs_le_abs_sub x s₀
    rw [hT]
    linarith
  have hex : ∀ x, |x| ≤ T → Real.exp (1 / (2 * α) * x) ≤ E ∧
      1 ≤ Real.exp (1 / (2 * α) * x) * E ∧ Real.exp ((1 - 1 / (2 * α)) * x) ≤ E1 := by
    intro x hx
    have hxT := abs_le.1 hx
    refine ⟨Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hxT.2 hg0.le), ?_, Real.exp_le_exp.2 ?_⟩
    · rw [hE, ← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [hxT.1])
    · calc (1 - 1 / (2 * α)) * x ≤ |(1 - 1 / (2 * α)) * x| := le_abs_self _
        _ = |1 - 1 / (2 * α)| * |x| := abs_mul _ _
        _ ≤ |1 - 1 / (2 * α)| * T := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  have hpt : ∀ x, IsFreqTest (flowPush α a x ψ) := fun x => isFreqTest_flowPull _ _ _ x hψ
  have hsupp : ∀ x, |x| ≤ T → ∀ ξ, ξ ∉ K → ξ ∉ tsupport (flowPush α a x ψ) := by
    intro x hx ξ hξK hξs
    obtain ⟨e1, e2, -⟩ := hex x hx
    have hsub : tsupport (flowPush α a x ψ) ⊆
        (flowLin (-(1 / (2 * α))) (-a) x) ⁻¹' tsupport ψ :=
      closure_minimal (fun η hη => subset_tsupport ψ (Function.mem_support.2 fun h0 =>
        Function.mem_support.1 hη (by simp only [flowPush, flowPull, h0, map_zero])))
        ((isClosed_tsupport ψ).preimage (flowLin _ _ _).continuous)
    have hy := hsub hξs
    have u1 : ‖flowLin (-(1 / (2 * α))) (-a) x ξ‖ ≤ R0 := by
      have := hR0 hy
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have u2 := hlow _ hy
    have hn : ‖flowLin (-(1 / (2 * α))) (-a) x ξ‖ = Real.exp (1 / (2 * α) * x) * ‖ξ‖ := by
      rw [norm_flowLin]
      congr 2
      ring
    rw [hn] at u1 u2
    have p1 := mul_le_mul_of_nonneg_right e1 (norm_nonneg ξ)
    have p2 := mul_le_mul_of_nonneg_right e2 (norm_nonneg ξ)
    have p3 := mul_le_mul_of_nonneg_right u1 hE0.le
    refine hξK ⟨?_, ?_⟩
    · rw [div_le_iff₀ hE0]
      nlinarith
    · nlinarith
  have hadjb : ∀ x, |x| ≤ T → ∀ ξ ∈ K, ‖flowAdjoint α a (flowPush α a x ψ) ξ‖ ≤ M := by
    intro x hx ξ hξ
    obtain ⟨e1, -, e3⟩ := hex x hx
    have hb := norm_flowAdjoint_push_le α a x hψ.1 hCψ hCd ξ
    refine hb.trans ?_
    have hξ2 : ‖ξ‖ ≤ R0 * E := hξ.2
    have hA : Real.exp ((1 - 1 / (2 * α)) * x) * Cψ ≤ E1 * Cψ :=
      mul_le_mul_of_nonneg_right e3 hCψ0
    have hB' : Real.exp ((1 - 1 / (2 * α)) * x) * (Cd * Real.exp (1 / (2 * α) * x)) * ‖ξ‖ ≤
        B * (R0 * E) := by
      rw [hB]
      gcongr
    rw [hM]
    gcongr
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : Space)) (r := R0 * E)).subset ?_
      intro ξ hξ
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hξ.2
  have hρ1 : 0 < r0 / E := div_pos hr0 hE0
  set C0 : ℝ := M / (2 * π * (r0 / E)) with hC0
  have hbi : Integrable (K.indicator fun ξ => C0 * ‖freqPow 1 ξ • h ξ‖) volume := by
    have hl := (h1.locallyIntegrable (by norm_num)).integrableOn_isCompact hKc
    have hl' : Integrable (fun ξ => C0 * ‖freqPow 1 ξ • h ξ‖) (volume.restrict K) :=
      (Integrable.norm hl).const_mul C0
    exact IntegrableOn.integrable_indicator hl' hKc.isClosed.measurableSet
  have hbd : ∀ ξ, ∀ x ∈ Metric.ball s₀ 1,
      ‖inner ℝ (h ξ) (flowAdjoint α a (flowPush α a x ψ) ξ)‖ ≤
        K.indicator (fun ξ => C0 * ‖freqPow 1 ξ • h ξ‖) ξ := by
    intro ξ x hx
    have hxT := hball1 x hx
    by_cases hξ : ξ ∈ K
    · rw [Set.indicator_of_mem hξ]
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hadjb x hxT ξ hξ)
      have hC00 : 0 ≤ C0 := div_nonneg hM0 (by positivity)
      have hn : ‖freqPow 1 ξ • h ξ‖ = 2 * π * ‖ξ‖ * ‖h ξ‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Internal.DriftPower.freqPow_nonneg _ _)]
        unfold freqPow
        rw [Real.rpow_one]
      rw [hn]
      have hξ1 : r0 / E ≤ ‖ξ‖ := hξ.1
      calc ‖inner ℝ (h ξ) (flowAdjoint α a (flowPush α a x ψ) ξ)‖
          ≤ ‖h ξ‖ * ‖flowAdjoint α a (flowPush α a x ψ) ξ‖ := norm_inner_le_norm _ _
        _ ≤ ‖h ξ‖ * M := mul_le_mul_of_nonneg_left (hadjb x hxT ξ hξ) (norm_nonneg _)
        _ = C0 * (2 * π * (r0 / E) * ‖h ξ‖) := by
          rw [hC0]
          field_simp
        _ ≤ C0 * (2 * π * ‖ξ‖ * ‖h ξ‖) := by
          apply mul_le_mul_of_nonneg_left _ hC00
          gcongr
    · rw [Set.indicator_of_notMem hξ, flowAdjoint_of_notMem α a (hsupp x hxT ξ hξ),
        inner_zero_right, norm_zero]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun x ξ => inner ℝ (h ξ) (flowPush α a x ψ ξ))
    (F' := fun x ξ => inner ℝ (h ξ) (flowAdjoint α a (flowPush α a x ψ) ξ))
    (x₀ := s₀) (bound := K.indicator (fun ξ => C0 * ‖freqPow 1 ξ • h ξ‖))
    (Metric.ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun x => (integrable_inner_test h1 (hpt x)).aestronglyMeasurable)
    (integrable_inner_test h1 (hpt s₀))
    (hm.inner (continuous_flowAdjoint α a (hpt s₀).1).aestronglyMeasurable)
    (Eventually.of_forall fun ξ x hx => hbd ξ x hx) hbi
    (Eventually.of_forall fun ξ x _ => by
      exact (innerSL ℝ (h ξ)).hasFDerivAt.comp_hasDerivAt x (hasDerivAt_flowPush α a hψ.1 x ξ))
  exact key.2

end SteadyCert

end Breakdown
