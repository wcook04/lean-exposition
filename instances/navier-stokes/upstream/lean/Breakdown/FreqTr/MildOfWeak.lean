import Breakdown.FreqTr.Statements
import Breakdown.FreqTr.Phi
import Breakdown.FreqTr.WeakInX

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.MildOfWeak

open Internal.Phi Internal.WeakInX

def sspHeatX (τ : ℝ) : X →L[ℝ] X :=
  restrictX (fieldOp id (fun ξ => (sspFactor ξ * heatFactor τ ξ) • ContinuousLinearMap.id ℝ CSpace))

def halfFactor (ξ : Space) : ℝ := 2 * π * ‖ξ‖ / (1 + sspFactor ξ)

def halfX : X →L[ℝ] X :=
  restrictX (fieldOp id (fun ξ => halfFactor ξ • ContinuousLinearMap.id ℝ CSpace))

theorem sspFactor_nonneg (ξ : Space) : 0 ≤ sspFactor ξ := by unfold sspFactor; positivity

theorem continuous_halfFactor : Continuous halfFactor := by
  unfold halfFactor sspFactor
  exact (by fun_prop : Continuous fun ξ : Space => 2 * π * ‖ξ‖).div (by fun_prop)
    (fun ξ => by positivity)

theorem abs_halfFactor_le (ξ : Space) : |halfFactor ξ| ≤ 1 := by
  have hp : 0 < 1 + sspFactor ξ := by have := sspFactor_nonneg ξ; linarith
  unfold halfFactor
  rw [abs_of_nonneg (div_nonneg (by positivity) hp.le), div_le_one hp]
  unfold sspFactor
  nlinarith [sq_nonneg (2 * π * ‖ξ‖ - 1), mul_nonneg pi_pos.le (norm_nonneg ξ)]

theorem halfFactor_neg (ξ : Space) : halfFactor (-ξ) = halfFactor ξ := by
  simp [halfFactor, sspFactor, norm_neg]

theorem halfX_coe (h1 : FieldOpRealized) (x : X) :
    (halfX x : L2C) = fieldOp id (fun ξ => halfFactor ξ • ContinuousLinearMap.id ℝ CSpace) x := by
  unfold halfX restrictX
  rw [dif_pos (fun y hy => scalarOp_mem h1 continuous_halfFactor abs_halfFactor_le halfFactor_neg hy)]
  rfl

theorem halfX_ae (h1 : FieldOpRealized) (x : X) :
    (halfX x : Space → CSpace) =ᵐ[volume] fun ξ => halfFactor ξ • (x : L2C) ξ := by
  rw [halfX_coe h1]
  exact scalarOp_ae h1 continuous_halfFactor abs_halfFactor_le _

theorem norm_halfX_le (h1 : FieldOpRealized) (x : X) : ‖halfX x‖ ≤ ‖x‖ := by
  have h := scalarOp_norm_le h1 continuous_halfFactor abs_halfFactor_le (x : L2C)
  rw [← halfX_coe h1, one_mul] at h
  exact h

theorem isHalfSspOf_half (h1 : FieldOpRealized) {χ h : X} (hl : IsSspOf χ h) :
    IsHalfSspOf (halfX (χ + h)) h := by
  have hc : ((χ + h : X) : L2C) = (χ : L2C) + (h : L2C) := rfl
  filter_upwards [halfX_ae h1 (χ + h), hl, Lp.coeFn_add (χ : L2C) (h : L2C)] with ξ hg hh hadd
  rw [hg, hc, hadd, Pi.add_apply, hh,
    show (χ : L2C) ξ + sspFactor ξ • (χ : L2C) ξ = (1 + sspFactor ξ) • (χ : L2C) ξ by
      rw [add_smul, one_smul], smul_smul, smul_smul]
  congr 1
  have hp : 0 < 1 + sspFactor ξ := by have := sspFactor_nonneg ξ; linarith
  unfold halfFactor
  field_simp
  unfold sspFactor
  ring

theorem vel_two (h1 : FieldOpRealized) (h13 : VelocityInvertsHalfSsp) {χ h : X} (hl : IsSspOf χ h) :
    MemLp (velocity h : Space → Space) 2 volume ∧
      (eLpNorm (velocity h : Space → Space) 2 volume).toReal ≤ ‖toPhys‖ * (‖χ‖ + ‖h‖) := by
  have hv := h13 _ _ (isHalfSspOf_half h1 hl)
  refine ⟨(Lp.memLp (toPhys (halfX (χ + h)))).ae_eq hv.symm, ?_⟩
  rw [eLpNorm_congr_ae hv, ← Lp.norm_def]
  calc ‖toPhys (halfX (χ + h))‖ ≤ ‖toPhys‖ * ‖halfX (χ + h)‖ := toPhys.le_opNorm _
    _ ≤ ‖toPhys‖ * (‖χ‖ + ‖h‖) :=
      mul_le_mul_of_nonneg_left ((norm_halfX_le h1 _).trans (norm_add_le _ _)) (norm_nonneg _)

theorem vel_six (h : X) :
    MemLp (velocity h : Space → Space) 6 volume ∧
      (eLpNorm (velocity h : Space → Space) 6 volume).toReal ≤ ‖velocity‖ * ‖h‖ := by
  refine ⟨Lp.memLp _, ?_⟩
  rw [← Lp.norm_def]
  exact velocity.le_opNorm h

theorem abs_le_mul_sqrt_bound {C A B P V s a b T : ℝ} (hB : 0 ≤ B) (hP : 0 ≤ P) (hV : 0 ≤ V) (hs : 0 ≤ s)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h2 : A ≤ P * s) (h6 : B ≤ V * s)
    (hT : |T| ≤ C * a * b * Real.sqrt (A * B)) :
    |T| ≤ max C 0 * Real.sqrt (P * V) * a * b * s := by
  have hsq : Real.sqrt (A * B) ≤ Real.sqrt (P * V) * s := by
    rw [show Real.sqrt (P * V) * s = Real.sqrt (P * V * s ^ 2) by
      rw [Real.sqrt_mul (mul_nonneg hP hV), Real.sqrt_sq hs]]
    apply Real.sqrt_le_sqrt
    calc A * B ≤ (P * s) * (V * s) := mul_le_mul h2 h6 hB (mul_nonneg hP hs)
      _ = P * V * s ^ 2 := by ring
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  calc |T| ≤ C * a * b * Real.sqrt (A * B) := hT
    _ = C * (a * b * Real.sqrt (A * B)) := by ring
    _ ≤ max C 0 * (a * b * Real.sqrt (A * B)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hab (Real.sqrt_nonneg _))
    _ ≤ max C 0 * (a * b * (Real.sqrt (P * V) * s)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hab) (le_max_right _ _)
    _ = max C 0 * Real.sqrt (P * V) * a * b * s := by ring

theorem tri_bound (h1 : FieldOpRealized) (h12 : TrilinearBound) (h13 : VelocityInvertsHalfSsp) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u v χ h : X, IsSspOf χ h →
      |trilinear u v (velocity h)| ≤ K * ‖u‖ * ‖v‖ * (‖χ‖ + ‖h‖) := by
  obtain ⟨C, hC⟩ := h12
  refine ⟨max C 0 * Real.sqrt (‖toPhys‖ * ‖velocity‖),
    mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _), fun u v χ h hl => ?_⟩
  obtain ⟨m2, b2⟩ := vel_two h1 h13 hl
  obtain ⟨m6, b6⟩ := vel_six h
  exact abs_le_mul_sqrt_bound ENNReal.toReal_nonneg (norm_nonneg _) (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _) (norm_nonneg _) b2
    (b6.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg χ)) (norm_nonneg _)))
    (hC u v _ m2 m6).2

theorem tri_sub_third (h1 : FieldOpRealized) (h12 : TrilinearBound) (h13 : VelocityInvertsHalfSsp)
    (u v : X) {χ h χ' h' : X} (hl : IsSspOf χ h) (hl' : IsSspOf χ' h') :
    trilinear u v (velocity (h - h')) = trilinear u v (velocity h) - trilinear u v (velocity h') := by
  obtain ⟨C, hC⟩ := h12
  unfold trilinear
  rw [← integral_sub (hC u v _ (vel_two h1 h13 hl).1 (vel_six h).1).1
    (hC u v _ (vel_two h1 h13 hl').1 (vel_six h').1).1]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (velocity h) (velocity h')] with x hx
  simp only [map_sub]
  rw [hx]
  simp [inner_sub_right, mul_sub, Finset.sum_sub_distrib]

theorem isSspOf_sub {χ h χ' h' : X} (hl : IsSspOf χ h) (hl' : IsSspOf χ' h') :
    IsSspOf (χ - χ') (h - h') := by
  have e1 : ((χ - χ' : X) : L2C) = (χ : L2C) - (χ' : L2C) := rfl
  have e2 : ((h - h' : X) : L2C) = (h : L2C) - (h' : L2C) := rfl
  filter_upwards [hl, hl', Lp.coeFn_sub (χ : L2C) (χ' : L2C), Lp.coeFn_sub (h : L2C) (h' : L2C)]
    with ξ a b c d
  rw [e1, e2, c, d, Pi.sub_apply, Pi.sub_apply, a, b, smul_sub]

theorem tri_congr (u v : X) {w w' : Space → Space} (hw : w =ᵐ[volume] w') :
    trilinear u v w = trilinear u v w' := by
  unfold trilinear
  apply integral_congr_ae
  filter_upwards [hw] with x hx
  rw [hx]

theorem velocity_spec (h14 : VelocityExists) : VelocitySpec velocity := by
  have hh : ∃ V, VelocitySpec V := h14
  unfold velocity
  rw [dif_pos hh]
  exact hh.choose_spec

theorem velocity_negSsp (h14 : VelocityExists) {φ : Space → Space} (hφ : IsTestField φ) :
    (velocity (embedX (negSsp φ)) : Space → Space) =ᵐ[volume] negSsp φ := by
  have ht := isTestField_negSsp hφ
  have hm : MemLp (negSsp φ) 6 volume :=
    ht.1.continuous.memLp_of_hasCompactSupport ht.2.1
  rw [velocity_spec h14 _ ht]
  unfold toLpOrZero
  rw [dif_pos hm]
  exact hm.coeFn_toLp

theorem sspHeat_neg (τ : ℝ) (ξ : Space) :
    sspFactor (-ξ) * heatFactor τ (-ξ) = sspFactor ξ * heatFactor τ ξ := by
  simp [sspFactor, heatFactor, norm_neg]

theorem sspHeatX_coe (h1 : FieldOpRealized) {τ : ℝ} (hτ : 0 < τ) (x : X) :
    (sspHeatX τ x : L2C) =
      fieldOp id (fun ξ => (sspFactor ξ * heatFactor τ ξ) • ContinuousLinearMap.id ℝ CSpace) x := by
  unfold sspHeatX restrictX
  rw [dif_pos (fun y hy => scalarOp_mem h1 (continuous_sspHeat τ) (sspHeat_le hτ) (sspHeat_neg τ) hy)]
  rfl

theorem isSspOf_heat (h1 : FieldOpRealized) (h5 : HeatSemigroup) {τ : ℝ} (hτ : 0 < τ) (ψ : X) :
    IsSspOf (heatX τ ψ) (sspHeatX τ ψ) := by
  have ha := scalarOp_ae h1 (continuous_sspHeat τ) (sspHeat_le hτ) (ψ : L2C)
  have hb := scalarOp_ae h1 (continuous_heatFactor τ) (heatFactor_le τ) (ψ : L2C)
  rw [← sspHeatX_coe h1 hτ] at ha
  have e : (heatX τ ψ : L2C) =
      fieldOp id (fun ξ => heatFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) ψ := h5.2.2.2.2.2 τ ψ
  rw [← e] at hb
  filter_upwards [ha, hb] with ξ a b
  rw [a, b, smul_smul]

theorem hasDerivAt_inner_moving {u w : ℝ → X} {s d : ℝ} {w' : X} (hu : ContinuousAt u s)
    (hw : HasDerivAt w w' s) (hd : HasDerivAt (fun r => inner ℝ (u r) (w s)) d s) :
    HasDerivAt (fun r => inner ℝ (u r) (w r)) (d + inner ℝ (u s) w') s := by
  have e : (fun r => inner ℝ (u r) (w r)) = fun r => inner ℝ (u r) (w s) +
      inner ℝ (u s) (w r - w s) + inner ℝ (u r - u s) (w r - w s) := by
    funext r
    simp only [inner_sub_left, inner_sub_right]
    ring
  have h2 : HasDerivAt (fun r => inner ℝ (u s) (w r - w s)) (inner ℝ (u s) w') s := by
    have := HasDerivAt.inner ℝ (hasDerivAt_const s (u s)) (hw.sub_const (w s))
    rwa [inner_zero_left, add_zero] at this
  have h3 : HasDerivAt (fun r => inner ℝ (u r - u s) (w r - w s)) 0 s := by
    rw [hasDerivAt_iff_isLittleO]
    simp only [sub_self, inner_zero_left, sub_zero, smul_zero]
    have hO := hw.isBigO_sub
    have ho : (fun r => u r - u s) =o[nhds s] (fun _ => (1 : ℝ)) := by
      rw [Asymptotics.isLittleO_one_iff]
      exact tendsto_sub_nhds_zero_iff.2 hu
    refine Asymptotics.IsBigO.trans_isLittleO (g := fun r => ‖u r - u s‖ * ‖w r - w s‖) ?_ ?_
    · refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun r => ?_)
      rw [one_mul, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
      exact abs_real_inner_le_norm _ _
    · simpa using ho.norm_left.mul_isBigO hO.norm_left
  have := (hd.add h2).add h3
  rw [add_zero] at this
  rw [e]
  exact this

theorem tri_continuousOn (h1 : FieldOpRealized) (h12 : TrilinearBound) (h13 : VelocityInvertsHalfSsp)
    {u : ℝ → X} {S : Set ℝ} (hu : ContinuousOn u S) {χ h : X} (hl : IsSspOf χ h) :
    ContinuousOn (fun s => trilinear (u s) (u s) (velocity h)) S :=
  (continuous_trilinear_diag h12 _ (vel_two h1 h13 hl).1 (vel_six h).1).comp_continuousOn hu

theorem weak_ext (h1 : FieldOpRealized) (hW : WeakInX) (h2 : TestDenseGraph) (h12 : TrilinearBound)
    (h13 : VelocityInvertsHalfSsp) (h14 : VelocityExists) (h15 : EmbedNegSsp)
    {v : ℝ → Space → Space} {a b : ℝ} (hab : a < b) (W : IsWeakSolution v a b)
    {χ h : X} (hl : IsSspOf χ h) {t : ℝ} (ht : t ∈ Icc a b) :
    inner ℝ (embedX (v t)) χ = inner ℝ (embedX (v a)) χ -
      ∫ s in a..t, (inner ℝ (embedX (v s)) h +
        trilinear (embedX (v s)) (embedX (v s)) (velocity h)) := by
  have hu : ContinuousOn (fun s => embedX (v s)) (Icc a b) := W.2.1
  obtain ⟨K, hK0, hK⟩ := tri_bound h1 h12 h13
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  set M' := max M 0 with hM'
  have hM0 : 0 ≤ M' := le_max_right _ _
  have hsub : uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2
  have hFc : ∀ {χ' h' : X}, IsSspOf χ' h' → IntervalIntegrable (fun s => inner ℝ (embedX (v s)) h' +
      trilinear (embedX (v s)) (embedX (v s)) (velocity h')) volume a t := fun hl' =>
    (((hu.inner continuousOn_const).add (tri_continuousOn h1 h12 h13 hu hl')).mono hsub).intervalIntegrable
  choose φ hφ hχ hh using fun n : ℕ => h2 χ h hl (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
  have hssp : ∀ n, IsSspOf (embedX (φ n)) (embedX (negSsp (φ n))) := fun n => h15 _ (hφ n)
  have hw : ∀ n, inner ℝ (embedX (v t)) (embedX (φ n)) = inner ℝ (embedX (v a)) (embedX (φ n)) -
      ∫ s in a..t, (inner ℝ (embedX (v s)) (embedX (negSsp (φ n))) +
        trilinear (embedX (v s)) (embedX (v s)) (velocity (embedX (negSsp (φ n))))) := by
    intro n
    have e := (hW v a b hab W (φ n) (hφ n) t ht).2
    have htri : ∀ s, trilinear (embedX (v s)) (embedX (v s)) (negSsp (φ n)) =
        trilinear (embedX (v s)) (embedX (v s)) (velocity (embedX (negSsp (φ n)))) :=
      fun s => tri_congr _ _ (velocity_negSsp h14 (hφ n)).symm
    simp_rw [htri] at e
    exact e
  have e_lim : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hχlim : Filter.Tendsto (fun n => embedX (φ n)) Filter.atTop (nhds χ) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hχ n).le) e_lim
  have hbound : ∀ n, ∀ s ∈ Set.uIoc a t,
      ‖(inner ℝ (embedX (v s)) (embedX (negSsp (φ n))) +
        trilinear (embedX (v s)) (embedX (v s)) (velocity (embedX (negSsp (φ n))))) -
        (inner ℝ (embedX (v s)) h + trilinear (embedX (v s)) (embedX (v s)) (velocity h))‖ ≤
        (M' + 2 * K * M' * M') * (1 / ((n : ℝ) + 1)) := by
    intro n s hs
    rw [uIoc_of_le ht.1] at hs
    have hs' : s ∈ Icc a b := ⟨hs.1.le, hs.2.trans ht.2⟩
    have hus : ‖embedX (v s)‖ ≤ M' := (hM s hs').trans (le_max_left _ _)
    have e : (inner ℝ (embedX (v s)) (embedX (negSsp (φ n))) +
        trilinear (embedX (v s)) (embedX (v s)) (velocity (embedX (negSsp (φ n))))) -
        (inner ℝ (embedX (v s)) h + trilinear (embedX (v s)) (embedX (v s)) (velocity h)) =
        inner ℝ (embedX (v s)) (embedX (negSsp (φ n)) - h) +
          trilinear (embedX (v s)) (embedX (v s)) (velocity (embedX (negSsp (φ n)) - h)) := by
      rw [tri_sub_third h1 h12 h13 _ _ (hssp n) hl, inner_sub_right]
      ring
    have hc1 := (hχ n).le
    have hc2 := (hh n).le
    have hi : |inner ℝ (embedX (v s)) (embedX (negSsp (φ n)) - h)| ≤ M' * (1 / ((n : ℝ) + 1)) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul hus hc2 (norm_nonneg _) hM0)
    have ht3 : |trilinear (embedX (v s)) (embedX (v s)) (velocity (embedX (negSsp (φ n)) - h))| ≤
        K * M' * M' * (1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1)) := by
      refine (hK _ _ _ _ (isSspOf_sub (hssp n) hl)).trans ?_
      gcongr
    rw [e, Real.norm_eq_abs]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ M' * (1 / ((n : ℝ) + 1)) + K * M' * M' * (1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1)) :=
          add_le_add hi ht3
      _ = (M' + 2 * K * M' * M') * (1 / ((n : ℝ) + 1)) := by ring
  have hI : Filter.Tendsto (fun n => ∫ s in a..t, (inner ℝ (embedX (v s)) (embedX (negSsp (φ n))) +
        trilinear (embedX (v s)) (embedX (v s)) (velocity (embedX (negSsp (φ n))))))
      Filter.atTop (nhds (∫ s in a..t, (inner ℝ (embedX (v s)) h +
        trilinear (embedX (v s)) (embedX (v s)) (velocity h)))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      (((e_lim.const_mul (M' + 2 * K * M' * M')).mul_const |t - a|).trans (by simp))
    rw [← intervalIntegral.integral_sub (hFc (hssp n)) (hFc hl)]
    exact intervalIntegral.norm_integral_le_of_norm_le_const (hbound n)
  have hR := (Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := embedX (v a))) hχlim).sub hI
  have hL := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := embedX (v t))) hχlim
  exact tendsto_nhds_unique hL (hR.congr (fun n => (hw n).symm))

theorem weak_deriv (h1 : FieldOpRealized) (hW : WeakInX) (h2 : TestDenseGraph) (h12 : TrilinearBound)
    (h13 : VelocityInvertsHalfSsp) (h14 : VelocityExists) (h15 : EmbedNegSsp)
    {v : ℝ → Space → Space} {a b : ℝ} (hab : a < b) (W : IsWeakSolution v a b)
    {χ h : X} (hl : IsSspOf χ h) {s : ℝ} (hs : s ∈ Ioo a b) :
    HasDerivAt (fun r => inner ℝ (embedX (v r)) χ)
      (-(inner ℝ (embedX (v s)) h + trilinear (embedX (v s)) (embedX (v s)) (velocity h))) s := by
  have hu : ContinuousOn (fun s => embedX (v s)) (Icc a b) := W.2.1
  have hF : ContinuousOn (fun s => inner ℝ (embedX (v s)) h +
      trilinear (embedX (v s)) (embedX (v s)) (velocity h)) (Icc a b) :=
    (hu.inner continuousOn_const).add (tri_continuousOn h1 h12 h13 hu hl)
  have hnhds : Icc a b ∈ nhds s := Icc_mem_nhds hs.1 hs.2
  have hd := (intervalIntegral.integral_hasDerivAt_right
    ((hF.mono (by rw [uIcc_of_le hs.1.le]; exact Icc_subset_Icc le_rfl hs.2.le)).intervalIntegrable)
    ((hF.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs)
    (hF.continuousAt hnhds)).const_sub (inner ℝ (embedX (v a)) χ)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hnhds] with r hr
  exact weak_ext h1 hW h2 h12 h13 h14 h15 hab W hl hr

theorem bilin_diff (B : X →L[ℝ] X →L[ℝ] X) (x y : X) :
    B x x - B y y = B (x - y) x + B y (x - y) := by
  have h3 : B (x - y) x = B x x - B y x := B.map_sub₂ x y x
  have h4 : B y (x - y) = B y x - B y y := (B y).map_sub x y
  exact (by abel : B x x - B y y = (B x x - B y x) + (B y x - B y y)).trans
    (congrArg₂ (· + ·) h3.symm h4.symm)

theorem bilin_curve_continuousOn (h7 : BilinBound) (h8 : BilinContinuous) {u : ℝ → X} {g : ℝ → ℝ}
    {S : Set ℝ} (hu : ContinuousOn u S) (hg : ContinuousOn g S) (hpos : ∀ s ∈ S, 0 < g s) :
    ContinuousOn (fun s => bilinX (g s) (u s) (u s)) S := by
  obtain ⟨C, _, hC⟩ := h7
  intro s₀ hs₀
  have hD : ContinuousWithinAt (fun s => bilinX (g s) (u s₀) (u s₀)) S s₀ :=
    (h8 (u s₀) (u s₀) (g s₀) (hpos s₀ hs₀)).comp (hg s₀ hs₀) (fun s hs => hpos s hs)
  have hr : ContinuousOn (fun s => g s ^ (-(3 / 4 : ℝ))) S :=
    hg.rpow_const (fun s hs => Or.inl (hpos s hs).ne')
  have hB : ContinuousWithinAt (fun s => C * g s ^ (-(3 / 4 : ℝ)) *
      (‖u s - u s₀‖ * ‖u s‖ + ‖u s₀‖ * ‖u s - u s₀‖)) S s₀ :=
    (continuousWithinAt_const.mul (hr s₀ hs₀)).mul
      ((((hu s₀ hs₀).sub continuousWithinAt_const).norm.mul (hu s₀ hs₀).norm).add
        (continuousWithinAt_const.mul ((hu s₀ hs₀).sub continuousWithinAt_const).norm))
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Filter.Tendsto (fun s => C * g s ^ (-(3 / 4 : ℝ)) *
      (‖u s - u s₀‖ * ‖u s‖ + ‖u s₀‖ * ‖u s - u s₀‖) +
      ‖bilinX (g s) (u s₀) (u s₀) - bilinX (g s₀) (u s₀) (u s₀)‖) (nhdsWithin s₀ S) (nhds 0) := by
    have := hB.tendsto.add (tendsto_iff_norm_sub_tendsto_zero.1 hD.tendsto)
    simpa only [sub_self, norm_zero, zero_mul, mul_zero, add_zero] using this
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  have e : bilinX (g s) (u s) (u s) - bilinX (g s₀) (u s₀) (u s₀) =
      (bilinX (g s) (u s - u s₀) (u s) + bilinX (g s) (u s₀) (u s - u s₀)) +
        (bilinX (g s) (u s₀) (u s₀) - bilinX (g s₀) (u s₀) (u s₀)) :=
    (by abel : bilinX (g s) (u s) (u s) - bilinX (g s₀) (u s₀) (u s₀) =
      (bilinX (g s) (u s) (u s) - bilinX (g s) (u s₀) (u s₀)) +
        (bilinX (g s) (u s₀) (u s₀) - bilinX (g s₀) (u s₀) (u s₀))).trans
      (congrArg₂ (· + ·) (bilin_diff (bilinX (g s)) (u s) (u s₀)) rfl)
  refine (congrArg norm e).le.trans ?_
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) le_rfl)
  have hh := hC (g s) (hpos s hs)
  calc ‖bilinX (g s) (u s - u s₀) (u s)‖ + ‖bilinX (g s) (u s₀) (u s - u s₀)‖ ≤
      C * g s ^ (-(3 / 4 : ℝ)) * ‖u s - u s₀‖ * ‖u s‖ +
        C * g s ^ (-(3 / 4 : ℝ)) * ‖u s₀‖ * ‖u s - u s₀‖ := add_le_add (hh _ _) (hh _ _)
    _ = _ := by ring

theorem bilin_intervalIntegrable (h7 : BilinBound) (h8 : BilinContinuous) {u : ℝ → X} {a b : ℝ}
    (hu : ContinuousOn u (Icc a b)) {t : ℝ} (ht : t ∈ Icc a b) :
    IntervalIntegrable (fun s => bilinX (t - s) (u s) (u s)) volume a t := by
  obtain ⟨C, hC0, hC⟩ := h7
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  have hcont : ContinuousOn (fun s => bilinX (t - s) (u s) (u s)) (Ioo a t) :=
    bilin_curve_continuousOn ⟨C, hC0, hC⟩ h8
      (hu.mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2)))
      (continuousOn_const.sub continuousOn_id) (fun s hs => sub_pos.2 hs.2)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
  have hpow : IntegrableOn (fun s => (t - s) ^ (-(3 / 4 : ℝ))) (Ioo a t) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (r := -(3 / 4 : ℝ)) (by norm_num)
      (a := 0) (b := t - a)).comp_sub_left t
    rw [sub_zero, sub_sub_cancel] at this
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).1 this.symm
  refine Integrable.mono' (hpow.const_mul (C * max M 0 ^ 2))
    (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun s hs => ?_)
  have hs' : s ∈ Icc a b := ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hus : ‖u s‖ ≤ max M 0 := (hM s hs').trans (le_max_left _ _)
  have hp : 0 ≤ C * (t - s) ^ (-(3 / 4 : ℝ)) :=
    mul_nonneg hC0 (Real.rpow_nonneg (sub_pos.2 hs.2).le _)
  calc ‖bilinX (t - s) (u s) (u s)‖ ≤ C * (t - s) ^ (-(3 / 4 : ℝ)) * ‖u s‖ * ‖u s‖ :=
        hC _ (sub_pos.2 hs.2) _ _
    _ ≤ C * (t - s) ^ (-(3 / 4 : ℝ)) * max M 0 * max M 0 := by
        rw [mul_assoc _ ‖u s‖, mul_assoc _ (max M 0)]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hus hus (norm_nonneg _) (le_max_right _ _)) hp
    _ = C * max M 0 ^ 2 * (t - s) ^ (-(3 / 4 : ℝ)) := by ring

theorem exp_expansion_le (y : ℝ) : |Real.exp y - 1 - y| ≤ y ^ 2 * Real.exp |y| := by
  by_cases hy : |y| ≤ 1
  · exact (Real.abs_exp_sub_one_sub_id_le hy).trans
      (le_mul_of_one_le_right (sq_nonneg y) (Real.one_le_exp (abs_nonneg y)))
  · rw [not_le] at hy
    have h0 : 0 ≤ Real.exp y - 1 - y := by linarith [Real.add_one_le_exp y]
    rw [abs_of_nonneg h0]
    have hsq : 1 ≤ y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
    have ha : |y| + 1 ≤ Real.exp |y| := Real.add_one_le_exp _
    have hb : Real.exp y ≤ Real.exp |y| := Real.exp_le_exp.2 (le_abs_self y)
    have hc : 0 < Real.exp |y| := Real.exp_pos _
    have hd : Real.exp |y| ≤ y ^ 2 * Real.exp |y| := le_mul_of_one_le_left hc.le hsq
    rcases le_or_gt 0 y with h | h
    · linarith
    · have h1 : Real.exp y ≤ 1 := Real.exp_le_one_iff.2 h.le
      have h2 : |y| = -y := abs_of_neg h
      linarith

theorem heat_expansion {τ r x : ℝ} (hτ : 0 < τ) (hr : |r - τ| ≤ τ / 2) (hx : 0 ≤ x) :
    |Real.exp (-(r * x)) - Real.exp (-(τ * x)) + (r - τ) * (x * Real.exp (-(τ * x)))| ≤
      16 / τ ^ 2 * (r - τ) ^ 2 := by
  set k := r - τ with hk
  have e : Real.exp (-(r * x)) - Real.exp (-(τ * x)) + k * (x * Real.exp (-(τ * x))) =
      Real.exp (-(τ * x)) * (Real.exp (-(k * x)) - 1 - (-(k * x))) := by
    rw [show -(r * x) = -(τ * x) + -(k * x) by rw [hk]; ring, Real.exp_add]
    ring
  rw [e, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := exp_expansion_le (-(k * x))
  rw [abs_neg, abs_mul, abs_of_nonneg hx] at h1
  have h2 : Real.exp (-(τ * x)) * Real.exp (|k| * x) ≤ Real.exp (-(τ / 2 * x)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  have h3 : x ^ 2 * Real.exp (-(τ / 2 * x)) ≤ 16 / τ ^ 2 := by
    have hm := mul_exp_neg_le_one (τ / 4 * x)
    have hn : 0 ≤ τ / 4 * x * Real.exp (-(τ / 4 * x)) := by positivity
    have e2 : x ^ 2 * Real.exp (-(τ / 2 * x)) =
        (4 / τ) ^ 2 * (τ / 4 * x * Real.exp (-(τ / 4 * x))) ^ 2 := by
      rw [show -(τ / 2 * x) = -(τ / 4 * x) + -(τ / 4 * x) by ring, Real.exp_add]
      field_simp
    rw [e2]
    calc (4 / τ) ^ 2 * (τ / 4 * x * Real.exp (-(τ / 4 * x))) ^ 2 ≤ (4 / τ) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hn hm) (by positivity)
      _ = 16 / τ ^ 2 := by rw [div_pow]; norm_num
  calc Real.exp (-(τ * x)) * |Real.exp (-(k * x)) - 1 - -(k * x)| ≤
        Real.exp (-(τ * x)) * ((-(k * x)) ^ 2 * Real.exp (|k| * x)) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = (k ^ 2 * x ^ 2) * (Real.exp (-(τ * x)) * Real.exp (|k| * x)) := by ring
    _ ≤ (k ^ 2 * x ^ 2) * Real.exp (-(τ / 2 * x)) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = k ^ 2 * (x ^ 2 * Real.exp (-(τ / 2 * x))) := by ring
    _ ≤ k ^ 2 * (16 / τ ^ 2) := mul_le_mul_of_nonneg_left h3 (sq_nonneg k)
    _ = 16 / τ ^ 2 * k ^ 2 := by ring

set_option maxHeartbeats 1000000 in
theorem heat_expansion_norm (h1 : FieldOpRealized) (h5 : HeatSemigroup) {τ r : ℝ} (hτ : 0 < τ)
    (hr : |r - τ| ≤ τ / 2) (ψ : X) :
    ‖heatX r ψ - heatX τ ψ - (r - τ) • (-(sspHeatX τ ψ))‖ ≤ 16 / τ ^ 2 * (r - τ) ^ 2 * ‖ψ‖ := by
  have hr0 : 0 < r := by have := neg_abs_le (r - τ); linarith
  have ha := scalarOp_ae h1 (continuous_heatFactor r) (heatFactor_le r) (ψ : L2C)
  have hb := scalarOp_ae h1 (continuous_heatFactor τ) (heatFactor_le τ) (ψ : L2C)
  have hc := scalarOp_ae h1 (continuous_sspHeat τ) (sspHeat_le hτ) (ψ : L2C)
  have ea : (heatX r ψ : L2C) =
      fieldOp id (fun ξ => heatFactor r ξ • ContinuousLinearMap.id ℝ CSpace) ψ := h5.2.2.2.2.2 r ψ
  have eb : (heatX τ ψ : L2C) =
      fieldOp id (fun ξ => heatFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) ψ := h5.2.2.2.2.2 τ ψ
  rw [← ea] at ha
  rw [← eb] at hb
  rw [← sspHeatX_coe h1 hτ] at hc
  have hn : ‖heatX r ψ - heatX τ ψ - (r - τ) • (-(sspHeatX τ ψ))‖ =
      ‖(heatX r ψ : L2C) - (heatX τ ψ : L2C) - (r - τ) • (-(sspHeatX τ ψ : L2C))‖ := rfl
  rw [hn]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [ha, hb, hc,
    Lp.coeFn_sub ((heatX r ψ : L2C) - (heatX τ ψ : L2C)) ((r - τ) • (-(sspHeatX τ ψ : L2C))),
    Lp.coeFn_sub (heatX r ψ : L2C) (heatX τ ψ : L2C),
    Lp.coeFn_smul (r - τ) (-(sspHeatX τ ψ : L2C)), Lp.coeFn_neg (sspHeatX τ ψ : L2C)]
    with ξ h_a h_b h_c s1 s2 s3 s4
  rw [s1, Pi.sub_apply, s2, Pi.sub_apply, s3, Pi.smul_apply, s4, Pi.neg_apply, h_a, h_b, h_c,
    smul_neg, sub_neg_eq_add, smul_smul, ← sub_smul, ← add_smul, norm_smul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have := heat_expansion hτ hr (sspFactor_nonneg ξ)
  have hx : ∀ t, -(4 * π ^ 2 * t * ‖ξ‖ ^ 2) = -(t * sspFactor ξ) := fun t => by unfold sspFactor; ring
  unfold heatFactor
  rw [max_eq_left hr0.le, max_eq_left hτ.le, hx r, hx τ]
  exact this

set_option maxHeartbeats 1000000 in
theorem heat_hasDerivAt (h1 : FieldOpRealized) (h5 : HeatSemigroup) {τ : ℝ} (hτ : 0 < τ) (ψ : X) :
    HasDerivAt (fun r => heatX r ψ) (-(sspHeatX τ ψ)) τ := by
  rw [hasDerivAt_iff_isLittleO]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun r => ‖r - τ‖ ^ 2) ?_
    (Asymptotics.isLittleO_pow_sub_sub τ one_lt_two)
  refine Asymptotics.IsBigO.of_bound (16 / τ ^ 2 * ‖ψ‖) ?_
  have hev : ∀ᶠ r in nhds τ, |r - τ| ≤ τ / 2 := by
    filter_upwards [Metric.ball_mem_nhds τ (half_pos hτ)] with r hr
    rw [Metric.mem_ball, Real.dist_eq] at hr
    exact hr.le
  filter_upwards [hev] with r hr
  have := heat_expansion_norm h1 h5 hτ hr ψ
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), sq_abs]
  refine this.trans (le_of_eq ?_)
  ring

theorem inner_bilinX (h6 : BilinExists) {τ : ℝ} (hτ : 0 < τ) (x y ψ : X) :
    inner ℝ (bilinX τ x y) ψ = bilinForm τ x y ψ := by
  have hh : 0 < τ ∧ ∃ B, BilinSpec τ B := ⟨hτ, h6 τ hτ⟩
  unfold bilinX
  rw [dif_pos hh]
  exact hh.2.choose_spec x y ψ

theorem inner_intervalIntegral {F : ℝ → X} {a t : ℝ} (hF : IntervalIntegrable F volume a t) (χ : X) :
    inner ℝ (∫ s in a..t, F s) χ = ∫ s in a..t, inner ℝ (F s) χ := by
  have := (innerSL ℝ χ).intervalIntegral_comp_comm hF
  simp only [innerSL_apply_apply] at this
  rw [real_inner_comm, ← this]
  congr 1
  funext s
  exact real_inner_comm _ _

theorem varConst_inner (h1 : FieldOpRealized) (hW : WeakInX) (h2 : TestDenseGraph)
    (h5 : HeatSemigroup) (h6 : BilinExists) (h7 : BilinBound) (h8 : BilinContinuous)
    (h10 : PhiVelocity) (h12 : TrilinearBound) (h13 : VelocityInvertsHalfSsp)
    (h14 : VelocityExists) (h15 : EmbedNegSsp)
    {v : ℝ → Space → Space} {a b : ℝ} (hab : a < b) (W : IsWeakSolution v a b)
    {t : ℝ} (ht : t ∈ Icc a b) {ε : ℝ} (hε : 0 < ε) (ψ : X) :
    inner ℝ (embedX (v t)) (heatX ε ψ) = inner ℝ (embedX (v a)) (heatX (t - a + ε) ψ) +
      ∫ s in a..t, inner ℝ (bilinX (t - s + ε) (embedX (v s)) (embedX (v s))) ψ := by
  have hu : ContinuousOn (fun s => embedX (v s)) (Icc a b) := W.2.1
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hwc : ContinuousOn (fun s => heatX (t - s + ε) ψ) (Icc a t) := by
    refine (h5.2.2.2.1 ψ).comp (by fun_prop : Continuous fun s : ℝ => t - s + ε).continuousOn ?_
    intro s hs
    simp only [mem_Ici]
    linarith [hs.2]
  have hG : ContinuousOn (fun s => inner ℝ (embedX (v s)) (heatX (t - s + ε) ψ)) (Icc a t) :=
    (hu.mono hsub).inner hwc
  have hG' : ContinuousOn (fun s => inner ℝ (bilinX (t - s + ε) (embedX (v s)) (embedX (v s))) ψ)
      (Icc a t) :=
    (bilin_curve_continuousOn h7 h8 (hu.mono hsub) (by fun_prop)
      (fun s hs => by linarith [hs.2])).inner continuousOn_const
  have hderiv : ∀ s ∈ Ioo a t, HasDerivAt (fun s => inner ℝ (embedX (v s)) (heatX (t - s + ε) ψ))
      (inner ℝ (bilinX (t - s + ε) (embedX (v s)) (embedX (v s))) ψ) s := by
    intro s hs
    have hτ : 0 < t - s + ε := by linarith [hs.2]
    have hs' : s ∈ Ioo a b := ⟨hs.1, hs.2.trans_le ht.2⟩
    have hw : HasDerivAt (fun r => heatX (t - r + ε) ψ) (sspHeatX (t - s + ε) ψ) s := by
      have h0 : HasDerivAt (fun r : ℝ => t - r + ε) (-1) s :=
        ((hasDerivAt_id' s).const_sub t).add_const ε
      have := (heat_hasDerivAt h1 h5 hτ ψ).scomp s h0
      simpa [Function.comp_def] using this
    have hd := weak_deriv h1 hW h2 h12 h13 h14 h15 hab W (isSspOf_heat h1 h5 hτ ψ) hs'
    have hm := hasDerivAt_inner_moving (hu.continuousAt (Icc_mem_nhds hs'.1 hs'.2)) hw hd
    convert hm using 1
    rw [inner_bilinX h6 hτ]
    unfold bilinForm
    rw [tri_congr _ _ (h10 _ hτ ψ _ (isSspOf_heat h1 h5 hτ ψ))]
    ring
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hG hderiv
    (hG'.intervalIntegrable_of_Icc ht.1)
  rw [this]
  simp only [sub_self, zero_add]
  ring

end Internal.MildOfWeak

open Internal.MildOfWeak in
theorem mildOfWeak (h1 : WeakInX) (h2 : TestDenseGraph) (_h3 : TestDense) (h4 : FieldOpRealized)
    (h5 : HeatSemigroup) (h6 : BilinExists) (h7 : BilinBound) (h8 : BilinContinuous)
    (h9 : BilinShift) (h10 : PhiVelocity) (_h11 : PhiBounds) (h12 : TrilinearBound)
    (h13 : VelocityInvertsHalfSsp) (h14 : VelocityExists) (h15 : EmbedNegSsp) (_h16 : EmbedLinear) :
    MildOfWeak := by
  intro v a b hab W
  refine ⟨W.2.1, fun t ht => ⟨bilin_intervalIntegrable h7 h8 W.2.1 ht, ?_⟩⟩
  beta_reduce
  have hint : IntervalIntegrable (fun s => bilinX (t - s) (embedX (v s)) (embedX (v s))) volume a t :=
    bilin_intervalIntegrable h7 h8 W.2.1 ht
  obtain ⟨Z, hZ⟩ : ∃ Z : X, Z = embedX (v t) - heatX (t - a) (embedX (v a)) -
      ∫ s in a..t, bilinX (t - s) (embedX (v s)) (embedX (v s)) := ⟨_, rfl⟩
  have key : ∀ ε, 0 < ε → inner ℝ Z (heatX ε Z) = 0 := by
    intro ε hε
    have hd := varConst_inner h4 h1 h2 h5 h6 h7 h8 h10 h12 h13 h14 h15 hab W ht hε Z
    have e1 : inner ℝ (heatX (t - a) (embedX (v a))) (heatX ε Z) =
        inner ℝ (embedX (v a)) (heatX (t - a + ε) Z) := by
      refine (h5.2.2.2.2.1 _ _ _).trans ?_
      rw [h5.2.1 (t - a) ε (sub_nonneg.2 ht.1) hε.le, ContinuousLinearMap.comp_apply]
    have e2 : inner ℝ (∫ s in a..t, bilinX (t - s) (embedX (v s)) (embedX (v s))) (heatX ε Z) =
        ∫ s in a..t, inner ℝ (bilinX (t - s + ε) (embedX (v s)) (embedX (v s))) Z := by
      refine (inner_intervalIntegral hint (heatX ε Z)).trans ?_
      apply intervalIntegral.integral_congr_ae
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton t)] with s hs hs'
      rw [uIoc_of_le ht.1] at hs'
      have hlt : s < t := lt_of_le_of_ne hs'.2 hs
      refine (h5.2.2.2.2.1 ε _ Z).symm.trans ?_
      have hb := h9 ε (t - s) hε.le (sub_pos.2 hlt) (embedX (v s)) (embedX (v s))
      rw [add_comm ε (t - s)] at hb
      exact congrArg (fun q => inner ℝ q Z) hb
    have s0 : inner ℝ Z (heatX ε Z) = inner ℝ (embedX (v t) - heatX (t - a) (embedX (v a)) -
        ∫ s in a..t, bilinX (t - s) (embedX (v s)) (embedX (v s))) (heatX ε Z) :=
      congrArg (fun q => inner ℝ q (heatX ε Z)) hZ
    have s1 := inner_sub_left (𝕜 := ℝ) (embedX (v t) - heatX (t - a) (embedX (v a)))
      (∫ s in a..t, bilinX (t - s) (embedX (v s)) (embedX (v s))) (heatX ε Z)
    have s2 := inner_sub_left (𝕜 := ℝ) (embedX (v t)) (heatX (t - a) (embedX (v a))) (heatX ε Z)
    linarith [s0, s1, s2, e1, e2, hd]
  have hZ0 : Z = 0 := by
    have hc : ContinuousWithinAt (fun ε => heatX ε Z) (Ici 0) 0 := h5.2.2.2.1 Z 0 (mem_Ici.2 (le_refl (0 : ℝ)))
    have hlim : Filter.Tendsto (fun ε => inner ℝ Z (heatX ε Z)) (nhdsWithin 0 (Ioi 0))
        (nhds (inner ℝ Z (heatX 0 Z))) :=
      Filter.Tendsto.inner (𝕜 := ℝ) tendsto_const_nhds (hc.mono Ioi_subset_Ici_self).tendsto
    rw [h5.1, ContinuousLinearMap.id_apply] at hlim
    have h0 : Filter.Tendsto (fun ε => inner ℝ Z (heatX ε Z)) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun ε hε => (key ε hε).symm)
    exact inner_self_eq_zero.1 (tendsto_nhds_unique hlim h0)
  rw [hZ, sub_sub, sub_eq_zero] at hZ0
  exact hZ0

end Breakdown.Freq
