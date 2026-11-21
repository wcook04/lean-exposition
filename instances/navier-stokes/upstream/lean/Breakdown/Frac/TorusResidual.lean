import Breakdown.Frac.StTorusApprox
import Breakdown.Frac.StOperator
import Breakdown.Frac.OpIntegrable
import Breakdown.Torus.ApproxSizes

open MeasureTheory Set Real Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracResidualCombine.Internal

theorem freq_add' (a b : Lattice) : freq (a + b) = freq a + freq b := by
  simp [freq, add_smul, Finset.sum_add_distrib]

theorem freq_apply' (m : Lattice) (i : Fin 3) : freq m i = (m i : ℝ) := by
  simp [freq, unitVector, Pi.single_apply]

theorem center_apply' (i : Fin 3) : center i = 1 / 2 := by
  simp [center, unitVector, Pi.single_apply]

theorem latticePeriodize_add {E : Type*} [NormedAddCommGroup E] (f : Space → E) (m : Lattice)
    (x : Space) : latticePeriodize f (x + freq m) = latticePeriodize f x := by
  unfold latticePeriodize
  rw [← (Equiv.addRight m).tsum_eq (fun j => f (x + freq j))]
  congr 1
  funext j
  rw [Equiv.coe_addRight, freq_add']
  congr 1
  abel

theorem fderiv_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : Space → E}
    {c : Space} (hg : ∀ y, g (y + c) = g y) (x : Space) : fderiv ℝ g (x + c) = fderiv ℝ g x := by
  rw [← fderiv_comp_add_right]
  congr 1
  funext y
  exact hg y

theorem iteratedFDeriv_periodic {g : Space → Space} {c : Space} (hg : ∀ y, g (y + c) = g y)
    (n : ℕ) (x : Space) : iteratedFDeriv ℝ n g (x + c) = iteratedFDeriv ℝ n g x := by
  rw [← iteratedFDeriv_comp_add_right]
  congr 1
  funext y
  exact hg y

theorem fractionalPowerAt_periodic (α : ℝ) {g : Space → Space} {c : Space}
    (hg : ∀ y, g (y + c) = g y) (x : Space) :
    fractionalPowerAt α g (x + c) = fractionalPowerAt α g x := by
  unfold fractionalPowerAt secondOrderRemainder
  rw [fderiv_periodic hg, iteratedFDeriv_periodic hg, hg]
  congr 2
  funext z
  rw [add_right_comm, hg]

theorem advectionAt_periodic {g : Space → Space} {c : Space} (hg : ∀ y, g (y + c) = g y)
    (x : Space) : advectionAt g (x + c) = advectionAt g x := by
  unfold advectionAt
  rw [fderiv_periodic hg, hg]

theorem gradientAt_periodic {g : Space → ℝ} {c : Space} (hg : ∀ y, g (y + c) = g y)
    (x : Space) : gradientAt g (x + c) = gradientAt g x := by
  unfold gradientAt
  rw [fderiv_periodic hg]

theorem residual_periodic (α a : ℝ) (U : Space → Space) (P : Space → ℝ) (T t : ℝ) (m : Lattice)
    (x : Space) : fracApproxResidual α a U P T t (x + freq m) = fracApproxResidual α a U P T t x := by
  have h1 : ∀ τ y, latticePeriodize (fracApproxField α a U T τ) (y + freq m) =
      latticePeriodize (fracApproxField α a U T τ) y := fun τ y => latticePeriodize_add _ m y
  have h2 : ∀ y, latticePeriodize (fracApproxPressure α a P T t) (y + freq m) =
      latticePeriodize (fracApproxPressure α a P T t) y := fun y => latticePeriodize_add _ m y
  have hd : (fun τ => latticePeriodize (fracApproxField α a U T τ) (x + freq m)) =
      fun τ => latticePeriodize (fracApproxField α a U T τ) x := funext fun τ => h1 τ x
  unfold fracApproxResidual
  rw [hd, advectionAt_periodic (h1 t), fractionalPowerAt_periodic α (h1 t), gradientAt_periodic h2]

theorem cell_decomp (x : Space) : ∃ x₀ : Space, ∃ m : Lattice, x₀ ∈ cell ∧ x₀ + freq m = x := by
  refine ⟨x - freq (fun i => ⌊x i⌋), fun i => ⌊x i⌋, fun i => ?_, sub_add_cancel _ _⟩
  rw [PiLp.sub_apply, freq_apply']
  exact ⟨by linarith [Int.floor_le (x i)], by linarith [Int.lt_floor_add_one (x i)]⟩

theorem far_of_ne {x y : Space} (hx : x ∈ cell) (hy : dist y x < 1 / 4) {j : Lattice} (hj : j ≠ 0) :
    centralRadius / 2 ≤ dist (y + freq j) center := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hj
  have hji : (1 : ℝ) ≤ |(j i : ℝ)| := by
    have : (1 : ℤ) ≤ |j i| := Int.one_le_abs hi
    exact_mod_cast this
  have hyx : |y i - x i| < 1 / 4 := by
    have h := PiLp.norm_apply_le (y - x) i
    rw [PiLp.sub_apply, Real.norm_eq_abs] at h
    rw [dist_eq_norm] at hy
    linarith
  have hxi := hx i
  have hco : |(y + freq j - center) i| ≤ dist (y + freq j) center := by
    rw [dist_eq_norm]
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (y + freq j - center) i
  rw [PiLp.sub_apply, PiLp.add_apply, freq_apply', center_apply'] at hco
  have hr : centralRadius / 2 = 1 / 8 := by norm_num [centralRadius]
  rw [hr]
  obtain ⟨hl, hu⟩ := abs_lt.1 hyx
  rcases le_abs'.1 hji with h | h
  · have : y i + (j i : ℝ) - 1 / 2 ≤ -(1 / 4) := by linarith [hxi.2]
    have := neg_abs_le (y i + (j i : ℝ) - 1 / 2)
    linarith
  · have : 1 / 4 ≤ y i + (j i : ℝ) - 1 / 2 := by linarith [hxi.1]
    have := le_abs_self (y i + (j i : ℝ) - 1 / 2)
    linarith

theorem periodize_local {E : Type*} [NormedAddCommGroup E] {f : Space → E}
    (hf : ∀ y, centralRadius / 2 ≤ dist y center → f y = 0) {x : Space} (hx : x ∈ cell) :
    latticePeriodize f =ᶠ[𝓝 x] f := by
  filter_upwards [ball_mem_nhds x (by norm_num : (0 : ℝ) < 1 / 4)] with y hy
  unfold latticePeriodize
  rw [tsum_eq_single 0 (fun j hj => hf _ (far_of_ne hx (mem_ball.1 hy) hj))]
  simp [freq]


theorem self_similar_point {α a : ℝ} {U : Space → Space} {P : Space → ℝ} {C : ℝ}
    (hC : ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space,
      (∀ j : ℕ, j ≤ 3 → ‖iteratedFDeriv ℝ j (fracSelfSimilar α a U T t) x‖ ≤
        C * ((T - t) ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(2 * α - 1 + j))) ∧
      ‖deriv (fun τ => fracSelfSimilar α a U T τ x) t‖ ≤
        C * ((T - t) ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(4 * α - 1)) ∧
      ‖gradientAt (fracSelfSimilarPressure α a P T t) x‖ ≤
        C * ((T - t) ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(4 * α - 1)))
    (h1 : 1 < α) {T t : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (ht : 0 ≤ t) (htT : t < T) {y : Space}
    (hy : 0 < ‖y - center‖) :
    ‖fracSelfSimilar α a U T t y‖ ≤ |C| * ‖y - center‖ ^ (-(2 * α - 1)) := by
  have h := (hC T t hT hT1 ht htT y).1 0 (by norm_num)
  rw [norm_iteratedFDeriv_zero, Nat.cast_zero, add_zero] at h
  have hμ : 0 ≤ (T - t) ^ (1 / (2 * α)) := Real.rpow_nonneg (by linarith) _
  have hle : ((T - t) ^ (1 / (2 * α)) + ‖y - center‖) ^ (-(2 * α - 1)) ≤
      ‖y - center‖ ^ (-(2 * α - 1)) :=
    Real.rpow_le_rpow_of_nonpos hy (by linarith) (by linarith)
  have hpos : 0 ≤ ((T - t) ^ (1 / (2 * α)) + ‖y - center‖) ^ (-(2 * α - 1)) :=
    Real.rpow_nonneg (by positivity) _
  calc ‖fracSelfSimilar α a U T t y‖ ≤ C * ((T - t) ^ (1 / (2 * α)) + ‖y - center‖) ^ (-(2 * α - 1)) := h
    _ ≤ |C| * ((T - t) ^ (1 / (2 * α)) + ‖y - center‖) ^ (-(2 * α - 1)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hpos
    _ ≤ |C| * ‖y - center‖ ^ (-(2 * α - 1)) := mul_le_mul_of_nonneg_left hle (abs_nonneg C)

theorem potential_point {g : Space → Space} {A β : ℝ} (hβ : β < 2)
    (hg : ∀ y, 0 < ‖y - center‖ → ‖g y‖ ≤ A * ‖y - center‖ ^ (-β)) {y : Space}
    (hy : 0 < ‖y - center‖) :
    ‖homotopyPotential center g y‖ ≤
      A * ‖y - center‖ ^ (1 - β) * ∫ s in Ioc (0 : ℝ) 1, s ^ (1 - β) := by
  set r := ‖y - center‖ with hr
  have hint : IntegrableOn (fun s : ℝ => A * r ^ (1 - β) * s ^ (1 - β)) (Ioc 0 1) := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (r := 1 - β) (by linarith)).const_mul (A * r ^ (1 - β))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 h
  unfold homotopyPotential
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => norm_nonneg _) hint
    (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_))
  have hs0 : 0 < s := hs.1
  have hn : ‖center + s • (y - center) - center‖ = s * r := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
  have hsr : 0 < s * r := mul_pos hs0 hy
  have hb := hg (center + s • (y - center)) (by rw [hn]; exact hsr)
  rw [hn, Real.mul_rpow hs0.le hy.le] at hb
  have e1 : s ^ (1 - β) = s * s ^ (-β) := by
    rw [sub_eq_add_neg, Real.rpow_add hs0, Real.rpow_one]
  have e2 : r ^ (1 - β) = r * r ^ (-β) := by
    rw [sub_eq_add_neg, Real.rpow_add hy, Real.rpow_one]
  beta_reduce
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
  calc s * ‖cross (g (center + s • (y - center))) (y - center)‖
      ≤ s * (‖g (center + s • (y - center))‖ * r) :=
        mul_le_mul_of_nonneg_left (ApproxSizes.Internal.norm_cross_le _ _) hs0.le
    _ ≤ s * (A * (s ^ (-β) * r ^ (-β)) * r) := by gcongr
    _ = A * r ^ (1 - β) * s ^ (1 - β) := by rw [e1, e2]; ring

theorem field_point {g : Space → Space} {A β : ℝ} (hβ : β < 2)
    (hg : ∀ y, 0 < ‖y - center‖ → ‖g y‖ ≤ A * ‖y - center‖ ^ (-β)) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : ∀ x, |centralCut x| ≤ 1 ∧ ‖gradientAt centralCut x‖ ≤ G) {y : Space}
    (hy : 0 < ‖y - center‖) :
    ‖cutoffField centralCut center g y‖ ≤
      A * ‖y - center‖ ^ (-β) + G * (A * (∫ s in Ioc (0 : ℝ) 1, s ^ (1 - β))) * ‖y - center‖ ^ (1 - β) := by
  unfold cutoffField
  have hp := potential_point hβ hg hy
  have hc := hG y
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]
  have h1 : |centralCut y| * ‖g y‖ ≤ A * ‖y - center‖ ^ (-β) :=
    (mul_le_mul_of_nonneg_right hc.1 (norm_nonneg _)).trans (by rw [one_mul]; exact hg y hy)
  have h2 : ‖cross (gradientAt centralCut y) (homotopyPotential center g y)‖ ≤
      G * (A * ‖y - center‖ ^ (1 - β) * ∫ s in Ioc (0 : ℝ) 1, s ^ (1 - β)) :=
    (ApproxSizes.Internal.norm_cross_le _ _).trans (mul_le_mul hc.2 hp (norm_nonneg _) hG0)
  have e : G * (A * ‖y - center‖ ^ (1 - β) * ∫ s in Ioc (0 : ℝ) 1, s ^ (1 - β)) =
      G * (A * (∫ s in Ioc (0 : ℝ) 1, s ^ (1 - β))) * ‖y - center‖ ^ (1 - β) := by ring
  linarith

theorem mass_bound {α : ℝ} (h1 : 1 < α) (h2 : α < 5 / 4) (hF : FracApproxFieldProperties α)
    (hD : FracSelfSimilarDecay α) {a : ℝ} {U : Space → Space} {P : Space → ℝ}
    (hP : IsRotatingProfile α a 1 U P) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T →
      ∫ y, ‖fracApproxField α a U T t y‖ ≤ L := by
  obtain ⟨C, hC⟩ := hD a U P hP
  obtain ⟨G, hG0, hG⟩ := ApproxSizes.Internal.centralCut_bounds
  set β := 2 * α - 1 with hβ
  set Ks := ∫ s in Ioc (0 : ℝ) 1, s ^ (1 - β) with hKs
  have hKs0 : 0 ≤ Ks := setIntegral_nonneg measurableSet_Ioc fun s hs => Real.rpow_nonneg hs.1.le _
  set B := G * (|C| * Ks) with hB
  have hB0 : 0 ≤ B := mul_nonneg hG0 (mul_nonneg (abs_nonneg C) hKs0)
  set h : Space → ℝ := fun z => |C| * ‖z‖ ^ (-β) + B * ‖z‖ ^ (1 - β) with hh
  have hh0 : ∀ z, 0 ≤ h z := fun z =>
    add_nonneg (mul_nonneg (abs_nonneg C) (Real.rpow_nonneg (norm_nonneg _) _))
      (mul_nonneg hB0 (Real.rpow_nonneg (norm_nonneg _) _))
  have hhi : IntegrableOn h (ball (0 : Space) 1) :=
    ((FracInternal.integrableOn_ball_norm_rpow (s := -β) (by linarith)).const_mul |C|).add
      ((FracInternal.integrableOn_ball_norm_rpow (s := 1 - β) (by linarith)).const_mul B)
  have hgi : Integrable (fun y : Space => (ball (0 : Space) 1).indicator h (y - center)) :=
    (hhi.integrable_indicator measurableSet_ball).comp_sub_right center
  refine ⟨∫ y, (ball (0 : Space) 1).indicator h (y - center),
    integral_nonneg fun y => indicator_nonneg (fun z _ => hh0 z) _, fun T t hT hT1 ht htT => ?_⟩
  have hne : ∀ᵐ y : Space ∂volume, y ≠ center := by
    rw [ae_iff]
    simpa using measure_singleton (μ := (volume : Measure Space)) center
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hgi ?_
  filter_upwards [hne] with y hy
  have hy0 : 0 < ‖y - center‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
  have hvan := ((hF a U P hP T hT).2.2 t htT y).2.1
  rcases le_or_gt (centralRadius / 2) (dist y center) with hd | hd
  · rw [(hvan hd).1, norm_zero]
    exact indicator_nonneg (fun z _ => hh0 z) _
  · have hmem : y - center ∈ ball (0 : Space) 1 := by
      rw [mem_ball_zero_iff, ← dist_eq_norm]
      have : centralRadius / 2 < 1 := by norm_num [centralRadius]
      linarith
    rw [indicator_of_mem hmem]
    have hg : ∀ z, 0 < ‖z - center‖ → ‖fracSelfSimilar α a U T t z‖ ≤ |C| * ‖z - center‖ ^ (-β) :=
      fun z hz => self_similar_point hC h1 hT hT1 ht htT hz
    have := field_point (by linarith) hg hG0 hG hy0
    simp [hh, hB, fracApproxField, mul_assoc] at this ⊢
    exact this

end FracResidualCombine.Internal

open FracResidualCombine.Internal

theorem fracSpaceResidualBound_of (α : ℝ) (hc : FracResidualRegionBound α coreRegion)
    (hs : FracResidualRegionBound α shellRegion) (ho : FracResidualRegionBound α outerRegion) :
    FracSpaceResidualBound α := by
  intro a U P hP
  obtain ⟨K₁, h₁⟩ := hc a U P hP
  obtain ⟨K₂, h₂⟩ := hs a U P hP
  obtain ⟨K₃, h₃⟩ := ho a U P hP
  refine ⟨max K₁ (max K₂ K₃), fun T t hT hT1 ht htT x => ?_⟩
  have hq : 0 ≤ (T - t) ^ (-(2 - 3 / (2 * α))) := Real.rpow_nonneg (by linarith) _
  rcases le_total (dist x center) (centralRadius / 4) with h | h
  · exact (h₁ T t hT hT1 ht htT x h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq)
  · rcases le_total (dist x center) (centralRadius / 2) with h' | h'
    · exact (h₂ T t hT hT1 ht htT x ⟨h, h'⟩).trans
        (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hq)
    · exact (h₃ T t hT hT1 ht htT x h').trans
        (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hq)

theorem fracApproxResidualBound_of (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4)
    (hR : FracSpaceResidualBound α) (hT : FracPeriodizationTail α)
    (hF : FracApproxFieldProperties α) (hD : FracSelfSimilarDecay α) (hC : CovarianceStatement) :
    FracApproxResidualBound α := by
  intro a U P hP
  obtain ⟨K, hK⟩ := hR a U P hP
  obtain ⟨Ct, hCt, hTail⟩ := hT
  obtain ⟨L, hL0, hL⟩ := mass_bound h1 h2 hF hD hP
  refine ⟨K + Ct * L, fun T t hT0 hT1 ht htT x => ?_⟩
  obtain ⟨x₀, m, hx₀, rfl⟩ := cell_decomp x
  rw [residual_periodic]
  obtain ⟨hFs, -, hFt⟩ := hF a U P hP T hT0
  have hsmooth : ContDiff ℝ ∞ (fracApproxField α a U T t) := by
    have h := hFs.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun y _ => (⟨htT, trivial⟩ : ((t, y) : ℝ × Space) ∈ Iio T ×ˢ (univ : Set Space)))
      (s := (univ : Set Space))
    exact contDiffOn_univ.1 h
  have hsupp : ∀ y, fracApproxField α a U T t y ≠ 0 → dist y center ≤ centralRadius / 2 := by
    intro y hy
    by_contra hc
    exact hy ((hFt t htT y).2.1 (le_of_lt (not_le.1 hc))).1
  have hloc := periodize_local (fun y hy => ((hFt t htT y).2.1 hy).1) hx₀
  have hlocp := periodize_local (fun y hy => ((hFt t htT y).2.1 hy).2) hx₀
  have hloct : (fun τ => latticePeriodize (fracApproxField α a U T τ) x₀) =ᶠ[𝓝 t]
      fun τ => fracApproxField α a U T τ x₀ := by
    filter_upwards [Iio_mem_nhds htT] with τ hτ
    exact (periodize_local (fun y hy => ((hFt τ hτ y).2.1 hy).1) hx₀).eq_of_nhds
  have e : fracApproxResidual α a U P T t x₀ = fracSpaceResidual α a U P T t x₀ +
      (fractionalPowerAt α (latticePeriodize (fracApproxField α a U T t)) x₀ -
        fractionalPowerAt α (fracApproxField α a U T t) x₀) := by
    unfold fracApproxResidual fracSpaceResidual advectionAt gradientAt
    rw [hloct.deriv_eq, hloc.fderiv_eq, hloc.eq_of_nhds, hlocp.fderiv_eq]
    abel
  rw [e]
  have he : 3 / (2 * α) < 2 := by
    rw [div_lt_iff₀ (by linarith)]
    linarith
  have hq1 : 1 ≤ (T - t) ^ (-(2 - 3 / (2 * α))) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) (by linarith) (by linarith)
  have hCL : 0 ≤ Ct * L := mul_nonneg hCt.le hL0
  calc ‖fracSpaceResidual α a U P T t x₀ +
        (fractionalPowerAt α (latticePeriodize (fracApproxField α a U T t)) x₀ -
          fractionalPowerAt α (fracApproxField α a U T t) x₀)‖
      ≤ ‖fracSpaceResidual α a U P T t x₀‖ +
        ‖fractionalPowerAt α (latticePeriodize (fracApproxField α a U T t)) x₀ -
          fractionalPowerAt α (fracApproxField α a U T t) x₀‖ := norm_add_le _ _
    _ ≤ K * (T - t) ^ (-(2 - 3 / (2 * α))) + Ct * L :=
        add_le_add (hK T t hT0 hT1 ht htT x₀)
          ((hTail _ hsmooth hsupp x₀ hx₀).trans
            (mul_le_mul_of_nonneg_left (hL T t hT0 hT1 ht htT) hCt.le))
    _ ≤ (K + Ct * L) * (T - t) ^ (-(2 - 3 / (2 * α))) := by nlinarith

end Breakdown.Periodic
