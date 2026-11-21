import Breakdown.Frac.RMildOfWeakHeat

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracInternal.MildWeak

open Breakdown.Freq Breakdown.Freq.Internal.Phi Breakdown.Freq.Internal.WeakInX
  Breakdown.Freq.Internal.MildOfWeak

theorem frac_weak_ext {α : ℝ} (hα : 1 ≤ α) (hW : FracWeakInX α) (hD : FracNiceGraphDense α)
    (hE : FracNiceEmbedPower α) (hN : NiceFieldProps α)
    {v : ℝ → Space → Space} {a b : ℝ} (hab : a < b) (W : FracIsWeakSolution α v a b)
    {χ h ψ : X} (hl : IsSspOf χ h) (hf : IsFracOf α χ ψ) {t : ℝ} (ht : t ∈ Icc a b) :
    inner ℝ (embedX (v t)) χ = inner ℝ (embedX (v a)) χ -
      ∫ s in a..t, (inner ℝ (embedX (v s)) ψ +
        trilinear (embedX (v s)) (embedX (v s)) (velocity h)) := by
  have h1 := fieldOpRealized_holds
  have h12 := trilinear_holds
  have h13 := velocityInverts_holds
  have hu : ContinuousOn (fun s => embedX (v s)) (Icc a b) := W.2.1
  obtain ⟨K, hK0, hK⟩ := tri_bound h1 h12 h13
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  set M' := max M 0 with hM'
  have hM0 : 0 ≤ M' := le_max_right _ _
  have hsub : uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2
  have hFc : ∀ {χ' h' : X} (ψ' : X), IsSspOf χ' h' →
      IntervalIntegrable (fun s => inner ℝ (embedX (v s)) ψ' +
        trilinear (embedX (v s)) (embedX (v s)) (velocity h')) volume a t := fun ψ' hl' =>
    (((hu.inner continuousOn_const).add (tri_continuousOn h1 h12 h13 hu hl')).mono
      hsub).intervalIntegrable
  choose φ hφ hχ hψ using fun n : ℕ => hD χ ψ hf (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
  have hssp : ∀ n, IsSspOf (embedX (φ n)) (embedX (negSsp (φ n))) := fun n => (hE _ (hφ n)).1
  have hfr : ∀ n, IsFracOf α (embedX (φ n)) (embedX (fractionalPowerAt α (φ n))) :=
    fun n => (hE _ (hφ n)).2
  have hh : ∀ n, ‖embedX (negSsp (φ n)) - h‖ ≤ 2 * (1 / ((n : ℝ) + 1)) := fun n =>
    (sq_norm_le hα (isSspOf_sub (hssp n) hl) (isFracOf_sub (hfr n) hf)).trans
      (by linarith [(hχ n).le, (hψ n).le])
  have hw : ∀ n, inner ℝ (embedX (v t)) (embedX (φ n)) = inner ℝ (embedX (v a)) (embedX (φ n)) -
      ∫ s in a..t, (inner ℝ (embedX (v s)) (embedX (fractionalPowerAt α (φ n))) +
        trilinear (embedX (v s)) (embedX (v s)) (velocity (embedX (negSsp (φ n))))) := by
    intro n
    have e := (hW v a b hab W (φ n) (hφ n) t ht).2
    have htri : ∀ s, trilinear (embedX (v s)) (embedX (v s)) (negSsp (φ n)) =
        trilinear (embedX (v s)) (embedX (v s)) (velocity (embedX (negSsp (φ n)))) :=
      fun s => tri_congr _ _ (velocity_second_nice hN (hφ n)).symm
    simp_rw [htri] at e
    exact e
  have e_lim : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hχlim : Filter.Tendsto (fun n => embedX (φ n)) Filter.atTop (nhds χ) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hχ n).le) e_lim
  have hbound : ∀ n, ∀ s ∈ Set.uIoc a t,
      ‖(inner ℝ (embedX (v s)) (embedX (fractionalPowerAt α (φ n))) +
        trilinear (embedX (v s)) (embedX (v s)) (velocity (embedX (negSsp (φ n))))) -
        (inner ℝ (embedX (v s)) ψ + trilinear (embedX (v s)) (embedX (v s)) (velocity h))‖ ≤
        (M' + 3 * K * M' * M') * (1 / ((n : ℝ) + 1)) := by
    intro n s hs
    rw [uIoc_of_le ht.1] at hs
    have hs' : s ∈ Icc a b := ⟨hs.1.le, hs.2.trans ht.2⟩
    have hus : ‖embedX (v s)‖ ≤ M' := (hM s hs').trans (le_max_left _ _)
    have e : (inner ℝ (embedX (v s)) (embedX (fractionalPowerAt α (φ n))) +
        trilinear (embedX (v s)) (embedX (v s)) (velocity (embedX (negSsp (φ n))))) -
        (inner ℝ (embedX (v s)) ψ + trilinear (embedX (v s)) (embedX (v s)) (velocity h)) =
        inner ℝ (embedX (v s)) (embedX (fractionalPowerAt α (φ n)) - ψ) +
          trilinear (embedX (v s)) (embedX (v s)) (velocity (embedX (negSsp (φ n)) - h)) := by
      rw [tri_sub_third h1 h12 h13 _ _ (hssp n) hl, inner_sub_right]
      ring
    have hc1 := (hχ n).le
    have hc2 := (hψ n).le
    have hc3 := hh n
    have hi : |inner ℝ (embedX (v s)) (embedX (fractionalPowerAt α (φ n)) - ψ)| ≤
        M' * (1 / ((n : ℝ) + 1)) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul hus hc2 (norm_nonneg _) hM0)
    have ht3 : |trilinear (embedX (v s)) (embedX (v s)) (velocity (embedX (negSsp (φ n)) - h))| ≤
        K * M' * M' * (1 / ((n : ℝ) + 1) + 2 * (1 / ((n : ℝ) + 1))) := by
      refine (hK _ _ _ _ (isSspOf_sub (hssp n) hl)).trans ?_
      gcongr
    rw [e, Real.norm_eq_abs]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ M' * (1 / ((n : ℝ) + 1)) +
          K * M' * M' * (1 / ((n : ℝ) + 1) + 2 * (1 / ((n : ℝ) + 1))) := add_le_add hi ht3
      _ = (M' + 3 * K * M' * M') * (1 / ((n : ℝ) + 1)) := by ring
  have hI : Filter.Tendsto (fun n => ∫ s in a..t,
        (inner ℝ (embedX (v s)) (embedX (fractionalPowerAt α (φ n))) +
        trilinear (embedX (v s)) (embedX (v s)) (velocity (embedX (negSsp (φ n))))))
      Filter.atTop (nhds (∫ s in a..t, (inner ℝ (embedX (v s)) ψ +
        trilinear (embedX (v s)) (embedX (v s)) (velocity h)))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      (((e_lim.const_mul (M' + 3 * K * M' * M')).mul_const |t - a|).trans (by simp))
    rw [← intervalIntegral.integral_sub (hFc (embedX (fractionalPowerAt α (φ n))) (hssp n))
      (hFc ψ hl)]
    exact intervalIntegral.norm_integral_le_of_norm_le_const (hbound n)
  have hR := (Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := embedX (v a))) hχlim).sub hI
  have hL := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := embedX (v t))) hχlim
  exact tendsto_nhds_unique hL (hR.congr (fun n => (hw n).symm))

theorem frac_weak_deriv {α : ℝ} (hα : 1 ≤ α) (hW : FracWeakInX α) (hD : FracNiceGraphDense α)
    (hE : FracNiceEmbedPower α) (hN : NiceFieldProps α)
    {v : ℝ → Space → Space} {a b : ℝ} (hab : a < b) (W : FracIsWeakSolution α v a b)
    {χ h ψ : X} (hl : IsSspOf χ h) (hf : IsFracOf α χ ψ) {s : ℝ} (hs : s ∈ Ioo a b) :
    HasDerivAt (fun r => inner ℝ (embedX (v r)) χ)
      (-(inner ℝ (embedX (v s)) ψ + trilinear (embedX (v s)) (embedX (v s)) (velocity h))) s := by
  have hu : ContinuousOn (fun s => embedX (v s)) (Icc a b) := W.2.1
  have hF : ContinuousOn (fun s => inner ℝ (embedX (v s)) ψ +
      trilinear (embedX (v s)) (embedX (v s)) (velocity h)) (Icc a b) :=
    (hu.inner continuousOn_const).add
      (tri_continuousOn fieldOpRealized_holds trilinear_holds velocityInverts_holds hu hl)
  have hnhds : Icc a b ∈ nhds s := Icc_mem_nhds hs.1 hs.2
  have hd := (intervalIntegral.integral_hasDerivAt_right
    ((hF.mono (by rw [uIcc_of_le hs.1.le]; exact Icc_subset_Icc le_rfl hs.2.le)).intervalIntegrable)
    ((hF.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs)
    (hF.continuousAt hnhds)).const_sub (inner ℝ (embedX (v a)) χ)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hnhds] with r hr
  exact frac_weak_ext hα hW hD hE hN hab W hl hf hr

theorem frac_bilin_cont {α : ℝ} (hBb : FracBilinBound α) (hBc : FracBilinContinuous α)
    {u : ℝ → X} {g : ℝ → ℝ}
    {S : Set ℝ} (hu : ContinuousOn u S) (hg : ContinuousOn g S) (hpos : ∀ s ∈ S, 0 < g s) :
    ContinuousOn (fun s => fracBilinX α (g s) (u s) (u s)) S := by
  obtain ⟨C, _, hC⟩ := hBb
  intro s₀ hs₀
  have hD : ContinuousWithinAt (fun s => fracBilinX α (g s) (u s₀) (u s₀)) S s₀ :=
    (hBc (u s₀) (u s₀) (g s₀) (hpos s₀ hs₀)).comp (hg s₀ hs₀) (fun s hs => hpos s hs)
  have hr : ContinuousOn (fun s => g s ^ (-(3 / (4 * α)))) S :=
    hg.rpow_const (fun s hs => Or.inl (hpos s hs).ne')
  have hB : ContinuousWithinAt (fun s => C * g s ^ (-(3 / (4 * α))) *
      (‖u s - u s₀‖ * ‖u s‖ + ‖u s₀‖ * ‖u s - u s₀‖)) S s₀ :=
    (continuousWithinAt_const.mul (hr s₀ hs₀)).mul
      ((((hu s₀ hs₀).sub continuousWithinAt_const).norm.mul (hu s₀ hs₀).norm).add
        (continuousWithinAt_const.mul ((hu s₀ hs₀).sub continuousWithinAt_const).norm))
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Filter.Tendsto (fun s => C * g s ^ (-(3 / (4 * α))) *
      (‖u s - u s₀‖ * ‖u s‖ + ‖u s₀‖ * ‖u s - u s₀‖) +
      ‖fracBilinX α (g s) (u s₀) (u s₀) - fracBilinX α (g s₀) (u s₀) (u s₀)‖)
      (nhdsWithin s₀ S) (nhds 0) := by
    have := hB.tendsto.add (tendsto_iff_norm_sub_tendsto_zero.1 hD.tendsto)
    simpa only [sub_self, norm_zero, zero_mul, mul_zero, add_zero] using this
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  have e : fracBilinX α (g s) (u s) (u s) - fracBilinX α (g s₀) (u s₀) (u s₀) =
      (fracBilinX α (g s) (u s - u s₀) (u s) + fracBilinX α (g s) (u s₀) (u s - u s₀)) +
        (fracBilinX α (g s) (u s₀) (u s₀) - fracBilinX α (g s₀) (u s₀) (u s₀)) :=
    (by abel : fracBilinX α (g s) (u s) (u s) - fracBilinX α (g s₀) (u s₀) (u s₀) =
      (fracBilinX α (g s) (u s) (u s) - fracBilinX α (g s) (u s₀) (u s₀)) +
        (fracBilinX α (g s) (u s₀) (u s₀) - fracBilinX α (g s₀) (u s₀) (u s₀))).trans
      (congrArg₂ (· + ·) (bilin_diff (fracBilinX α (g s)) (u s) (u s₀)) rfl)
  refine (congrArg norm e).le.trans ?_
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) le_rfl)
  have hh := hC (g s) (hpos s hs)
  calc ‖fracBilinX α (g s) (u s - u s₀) (u s)‖ + ‖fracBilinX α (g s) (u s₀) (u s - u s₀)‖ ≤
      C * g s ^ (-(3 / (4 * α))) * ‖u s - u s₀‖ * ‖u s‖ +
        C * g s ^ (-(3 / (4 * α))) * ‖u s₀‖ * ‖u s - u s₀‖ := add_le_add (hh _ _) (hh _ _)
    _ = _ := by ring

theorem frac_bilin_int {α : ℝ} (hα : 1 ≤ α) (hBb : FracBilinBound α)
    (hBc : FracBilinContinuous α) {u : ℝ → X} {a b : ℝ}
    (hu : ContinuousOn u (Icc a b)) {t : ℝ} (ht : t ∈ Icc a b) :
    IntervalIntegrable (fun s => fracBilinX α (t - s) (u s) (u s)) volume a t := by
  obtain ⟨C, hC0, hC⟩ := hBb
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  have hcont : ContinuousOn (fun s => fracBilinX α (t - s) (u s) (u s)) (Ioo a t) :=
    frac_bilin_cont ⟨C, hC0, hC⟩ hBc
      (hu.mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2)))
      (continuousOn_const.sub continuousOn_id) (fun s hs => sub_pos.2 hs.2)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
  have hexp : -1 < -(3 / (4 * α)) := by
    have : 3 / (4 * α) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    linarith
  have hpow : IntegrableOn (fun s => (t - s) ^ (-(3 / (4 * α)))) (Ioo a t) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (r := -(3 / (4 * α))) hexp
      (a := 0) (b := t - a)).comp_sub_left t
    rw [sub_zero, sub_sub_cancel] at this
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).1 this.symm
  refine Integrable.mono' (hpow.const_mul (C * max M 0 ^ 2))
    (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun s hs => ?_)
  have hs' : s ∈ Icc a b := ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hus : ‖u s‖ ≤ max M 0 := (hM s hs').trans (le_max_left _ _)
  have hp : 0 ≤ C * (t - s) ^ (-(3 / (4 * α))) :=
    mul_nonneg hC0 (Real.rpow_nonneg (sub_pos.2 hs.2).le _)
  calc ‖fracBilinX α (t - s) (u s) (u s)‖ ≤ C * (t - s) ^ (-(3 / (4 * α))) * ‖u s‖ * ‖u s‖ :=
        hC _ (sub_pos.2 hs.2) _ _
    _ ≤ C * (t - s) ^ (-(3 / (4 * α))) * max M 0 * max M 0 := by
        rw [mul_assoc _ ‖u s‖, mul_assoc _ (max M 0)]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hus hus (norm_nonneg _) (le_max_right _ _)) hp
    _ = C * max M 0 ^ 2 * (t - s) ^ (-(3 / (4 * α))) := by ring

theorem inner_fracBilinX {α : ℝ} (hB : FracBilinExists α) {τ : ℝ} (hτ : 0 < τ) (x y ψ : X) :
    inner ℝ (fracBilinX α τ x y) ψ = fracBilinForm α τ x y ψ := by
  have hh : 0 < τ ∧ ∃ B, FracBilinSpec α τ B := ⟨hτ, hB τ hτ⟩
  unfold fracBilinX
  rw [dif_pos hh]
  exact hh.2.choose_spec x y ψ

theorem frac_integral_identity {α : ℝ} (hα : 1 ≤ α) (hW : FracWeakInX α) (hD : FracNiceGraphDense α)
    (hE : FracNiceEmbedPower α) (hN : NiceFieldProps α) (hH : FracHeatSemigroup α)
    (hB : FracBilinExists α) (hBb : FracBilinBound α) (hBc : FracBilinContinuous α)
    (hPv : FracPhiVelocity α)
    {v : ℝ → Space → Space} {a b : ℝ} (hab : a < b) (W : FracIsWeakSolution α v a b)
    {t : ℝ} (ht : t ∈ Icc a b) {ε : ℝ} (hε : 0 < ε) (ψ : X) :
    inner ℝ (embedX (v t)) (fracHeatX α ε ψ) =
      inner ℝ (embedX (v a)) (fracHeatX α (t - a + ε) ψ) +
      ∫ s in a..t, inner ℝ (fracBilinX α (t - s + ε) (embedX (v s)) (embedX (v s))) ψ := by
  have h0 : (0 : ℝ) < α := by linarith
  have hu : ContinuousOn (fun s => embedX (v s)) (Icc a b) := W.2.1
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hwc : ContinuousOn (fun s => fracHeatX α (t - s + ε) ψ) (Icc a t) := by
    refine (hH.2.2.2.1 ψ).comp (by fun_prop : Continuous fun s : ℝ => t - s + ε).continuousOn ?_
    intro s hs
    simp only [mem_Ici]
    linarith [hs.2]
  have hG : ContinuousOn (fun s => inner ℝ (embedX (v s)) (fracHeatX α (t - s + ε) ψ)) (Icc a t) :=
    (hu.mono hsub).inner hwc
  have hG' : ContinuousOn
      (fun s => inner ℝ (fracBilinX α (t - s + ε) (embedX (v s)) (embedX (v s))) ψ) (Icc a t) :=
    (frac_bilin_cont hBb hBc (hu.mono hsub) (by fun_prop)
      (fun s hs => by linarith [hs.2])).inner continuousOn_const
  have hderiv : ∀ s ∈ Ioo a t,
      HasDerivAt (fun s => inner ℝ (embedX (v s)) (fracHeatX α (t - s + ε) ψ))
      (inner ℝ (fracBilinX α (t - s + ε) (embedX (v s)) (embedX (v s))) ψ) s := by
    intro s hs
    have hτ : 0 < t - s + ε := by linarith [hs.2]
    have hs' : s ∈ Ioo a b := ⟨hs.1, hs.2.trans_le ht.2⟩
    have hw : HasDerivAt (fun r => fracHeatX α (t - r + ε) ψ) (aHeatX α (t - s + ε) ψ) s := by
      have hl0 : HasDerivAt (fun r : ℝ => t - r + ε) (-1) s :=
        ((hasDerivAt_id' s).const_sub t).add_const ε
      have := (frac_heat_hasDerivAt h0 hH hτ ψ).scomp s hl0
      simpa [Function.comp_def] using this
    have hd := frac_weak_deriv hα hW hD hE hN hab W (sq_heat_rel hα hH hτ ψ)
      (isFracOf_heat h0 hH hτ ψ) hs'
    have hm := hasDerivAt_inner_moving (hu.continuousAt (Icc_mem_nhds hs'.1 hs'.2)) hw hd
    convert hm using 1
    rw [inner_fracBilinX hB hτ]
    unfold fracBilinForm
    rw [tri_congr _ _ (hPv _ hτ ψ _ (sq_heat_rel hα hH hτ ψ))]
    ring
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hG hderiv
    (hG'.intervalIntegrable_of_Icc ht.1)
  rw [this]
  simp only [sub_self, zero_add]
  ring

end Breakdown.FracInternal.MildWeak

namespace Breakdown.Freq

open Breakdown.FracInternal.MildWeak Breakdown.Freq.Internal.MildOfWeak in
theorem fracMildOfWeak_of (α : ℝ) (hα : 1 < α) (_hα2 : α < 3 / 2) (hW : FracWeakInX α)
    (hD : FracNiceGraphDense α) (hE : FracNiceEmbedPower α) (hH : FracHeatSemigroup α)
    (hB : FracBilinExists α) (hBb : FracBilinBound α) (hBc : FracBilinContinuous α)
    (hBs : FracBilinShift α) (hPv : FracPhiVelocity α) (_hPb : FracPhiBounds α)
    (hN : NiceFieldProps α) : FracMildOfWeak α := by
  have hα1 : 1 ≤ α := hα.le
  intro v a b hab W
  refine ⟨W.2.1, fun t ht => ⟨frac_bilin_int hα1 hBb hBc W.2.1 ht, ?_⟩⟩
  beta_reduce
  have hint : IntervalIntegrable (fun s => fracBilinX α (t - s) (embedX (v s)) (embedX (v s)))
      volume a t :=
    frac_bilin_int hα1 hBb hBc W.2.1 ht
  obtain ⟨Z, hZ⟩ : ∃ Z : X, Z = embedX (v t) - fracHeatX α (t - a) (embedX (v a)) -
      ∫ s in a..t, fracBilinX α (t - s) (embedX (v s)) (embedX (v s)) := ⟨_, rfl⟩
  have key : ∀ ε, 0 < ε → inner ℝ Z (fracHeatX α ε Z) = 0 := by
    intro ε hε
    have hd := frac_integral_identity hα1 hW hD hE hN hH hB hBb hBc hPv hab W ht hε Z
    have e1 : inner ℝ (fracHeatX α (t - a) (embedX (v a))) (fracHeatX α ε Z) =
        inner ℝ (embedX (v a)) (fracHeatX α (t - a + ε) Z) := by
      refine (hH.2.2.2.2.1 _ _ _).trans ?_
      rw [hH.2.1 (t - a) ε (sub_nonneg.2 ht.1) hε.le, ContinuousLinearMap.comp_apply]
    have e2 : inner ℝ (∫ s in a..t, fracBilinX α (t - s) (embedX (v s)) (embedX (v s)))
        (fracHeatX α ε Z) =
        ∫ s in a..t, inner ℝ (fracBilinX α (t - s + ε) (embedX (v s)) (embedX (v s))) Z := by
      refine (inner_intervalIntegral hint (fracHeatX α ε Z)).trans ?_
      apply intervalIntegral.integral_congr_ae
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton t)] with s hs hs'
      rw [uIoc_of_le ht.1] at hs'
      have hlt : s < t := lt_of_le_of_ne hs'.2 hs
      refine (hH.2.2.2.2.1 ε _ Z).symm.trans ?_
      have hb := hBs ε (t - s) hε.le (sub_pos.2 hlt) (embedX (v s)) (embedX (v s))
      rw [add_comm ε (t - s)] at hb
      exact congrArg (fun q => inner ℝ q Z) hb
    have s0 : inner ℝ Z (fracHeatX α ε Z) =
        inner ℝ (embedX (v t) - fracHeatX α (t - a) (embedX (v a)) -
        ∫ s in a..t, fracBilinX α (t - s) (embedX (v s)) (embedX (v s))) (fracHeatX α ε Z) :=
      congrArg (fun q => inner ℝ q (fracHeatX α ε Z)) hZ
    have s1 := inner_sub_left (𝕜 := ℝ) (embedX (v t) - fracHeatX α (t - a) (embedX (v a)))
      (∫ s in a..t, fracBilinX α (t - s) (embedX (v s)) (embedX (v s))) (fracHeatX α ε Z)
    have s2 := inner_sub_left (𝕜 := ℝ) (embedX (v t)) (fracHeatX α (t - a) (embedX (v a)))
      (fracHeatX α ε Z)
    linarith [s0, s1, s2, e1, e2, hd]
  have hZ0 : Z = 0 := by
    have hc : ContinuousWithinAt (fun ε => fracHeatX α ε Z) (Ici 0) 0 :=
      hH.2.2.2.1 Z 0 (mem_Ici.2 (le_refl (0 : ℝ)))
    have hlim : Filter.Tendsto (fun ε => inner ℝ Z (fracHeatX α ε Z)) (nhdsWithin 0 (Ioi 0))
        (nhds (inner ℝ Z (fracHeatX α 0 Z))) :=
      Filter.Tendsto.inner (𝕜 := ℝ) tendsto_const_nhds (hc.mono Ioi_subset_Ici_self).tendsto
    rw [hH.1, ContinuousLinearMap.id_apply] at hlim
    have h0 : Filter.Tendsto (fun ε => inner ℝ Z (fracHeatX α ε Z)) (nhdsWithin 0 (Ioi 0))
        (nhds 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun ε hε => (key ε hε).symm)
    exact inner_self_eq_zero.1 (tendsto_nhds_unique hlim h0)
  rw [hZ, sub_sub, sub_eq_zero] at hZ0
  exact hZ0

end Breakdown.Freq
