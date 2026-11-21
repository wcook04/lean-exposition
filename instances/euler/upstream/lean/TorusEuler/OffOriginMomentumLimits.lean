import TorusEuler.OffOriginLimits
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-! The terminal spatial limits of the Euler momentum equation in Proposition 8.4. -/

open Filter MeasureTheory Set
open scoped ContDiff Topology

namespace TorusEuler

section BilinearJets

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem exists_uniform_jetBound_on_compact
    {U K : Set Vec3} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : Vec3 → E} {d : ℕ} (hf : ContDiffOn ℝ d f U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ d, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have h (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      (j ≤ d → ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C) := by
    by_cases hj : j ≤ d
    · have hc : ContinuousOn (iteratedFDeriv ℝ j f) K := by
        intro x hx
        exact ((hf.contDiffAt (hU.mem_nhds (hKU hx))).continuousAt_iteratedFDeriv
          (by exact_mod_cast hj)).continuousWithinAt
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
      exact ⟨max 0 C, le_max_left _ _, fun _ x hx => (hC x hx).trans (le_max_right _ _)⟩
    · exact ⟨0, le_rfl, fun h' => (hj h').elim⟩
  choose C hC₀ hC using h
  refine ⟨∑ j ∈ Finset.range (d + 1), C j, Finset.sum_nonneg (fun j _ => hC₀ j), ?_⟩
  intro j hj x hx
  exact (hC j hj x hx).trans (Finset.single_le_sum (fun j _ => hC₀ j)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

private theorem norm_iteratedFDeriv_bilinear_le_of_bounds
    (B : E →L[ℝ] F →L[ℝ] G) {U : Set Vec3} (hU : IsOpen U) {d : ℕ}
    {f : Vec3 → E} {g : Vec3 → F} (hf : ContDiffOn ℝ d f U) (hg : ContDiffOn ℝ d g U)
    {x : Vec3} (hx : x ∈ U) {C D : ℝ} (hC : 0 ≤ C)
    (hF : ∀ j ≤ d, ‖iteratedFDeriv ℝ j f x‖ ≤ C)
    (hG : ∀ j ≤ d, ‖iteratedFDeriv ℝ j g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ d (fun y => B (f y) (g y)) x‖ ≤ ‖B‖ * ((2 : ℝ) ^ d * C * D) := by
  have h := B.norm_iteratedFDerivWithin_le_of_bilinear hf hg hU.uniqueDiffOn hx (n := d) le_rfl
  simp_rw [iteratedFDerivWithin_of_isOpen _ hU hx] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ B.opNorm_nonneg)
  calc
    _ ≤ ∑ j ∈ Finset.range (d + 1), (d.choose j : ℝ) * C * D := by
      apply Finset.sum_le_sum
      intro j hj
      have h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hF j h) (Nat.cast_nonneg _))
        (hG (d - j) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = _ := by
      have h : (∑ j ∈ Finset.range (d + 1), (d.choose j : ℝ)) = (2 : ℝ) ^ d := by
        exact_mod_cast Nat.sum_range_choose d
      rw [← Finset.sum_mul, ← Finset.sum_mul, h]

set_option maxHeartbeats 800000 in
/-- Uniform convergence of the jets through order `d` on a compact set
passes through a fixed bilinear map, preserving the order of its arguments. -/
theorem tendstoUniformlyOn_iteratedFDeriv_bilinear_of_jet_limits
    {ι : Type*} {l : Filter ι} (B : E →L[ℝ] F →L[ℝ] G)
    {U K : Set Vec3} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {d : ℕ} {f : ι → Vec3 → E} {g : ι → Vec3 → F} {w : Vec3 → E} {z : Vec3 → F}
    (hf : ∀ᶠ t in l, ContDiffOn ℝ d (f t) U)
    (hg : ∀ᶠ t in l, ContDiffOn ℝ d (g t) U)
    (hw : ContDiffOn ℝ d w U) (hz : ContDiffOn ℝ d z U)
    (hF : ∀ j ≤ d, TendstoUniformlyOn (fun t => iteratedFDeriv ℝ j (f t))
      (iteratedFDeriv ℝ j w) l K)
    (hG : ∀ j ≤ d, TendstoUniformlyOn (fun t => iteratedFDeriv ℝ j (g t))
      (iteratedFDeriv ℝ j z) l K) :
    TendstoUniformlyOn (fun t => iteratedFDeriv ℝ d (fun x => B (f t x) (g t x)))
      (iteratedFDeriv ℝ d (fun x => B (w x) (z x))) l K := by
  obtain ⟨C, hC₀, hC⟩ := exists_uniform_jetBound_on_compact hU hK hKU hw
  obtain ⟨D, hD₀, hD⟩ := exists_uniform_jetBound_on_compact hU hK hKU hz
  let M := ‖B‖ * (2 : ℝ) ^ d * (C + D + 1)
  have hM : 0 ≤ M := by unfold M; positivity
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  let δ := min 1 (ε / (M + 1))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε (by positivity))
  have hδ₁ : δ ≤ 1 := min_le_left _ _
  have hsmallF : ∀ᶠ t in l, ∀ j ∈ Finset.range (d + 1), ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (f t) x - iteratedFDeriv ℝ j w x‖ < δ := by
    rw [eventually_all_finset]
    intro j hj
    filter_upwards [Metric.tendstoUniformlyOn_iff.1
      (hF j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))) δ hδ] with t ht x hx
    rw [← dist_eq_norm, dist_comm]
    exact ht x hx
  have hsmallG : ∀ᶠ t in l, ∀ j ∈ Finset.range (d + 1), ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (g t) x - iteratedFDeriv ℝ j z x‖ < δ := by
    rw [eventually_all_finset]
    intro j hj
    filter_upwards [Metric.tendstoUniformlyOn_iff.1
      (hG j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))) δ hδ] with t ht x hx
    rw [← dist_eq_norm, dist_comm]
    exact ht x hx
  filter_upwards [hf, hg, hsmallF, hsmallG] with t hft hgt hSf hSg x hx
  have hxU := hKU hx
  have hnx := hU.mem_nhds hxU
  let a := f t - w
  let b := g t - z
  have ha : ContDiffOn ℝ d a U := hft.sub hw
  have hb : ContDiffOn ℝ d b U := hgt.sub hz
  have haB (j : ℕ) (hj : j ≤ d) : ‖iteratedFDeriv ℝ j a x‖ ≤ δ := by
    unfold a
    rw [iteratedFDeriv_sub_apply ((hft.contDiffAt hnx).of_le (by exact_mod_cast hj))
      ((hw.contDiffAt hnx).of_le (by exact_mod_cast hj))]
    exact (hSf j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) x hx).le
  have hbB (j : ℕ) (hj : j ≤ d) : ‖iteratedFDeriv ℝ j b x‖ ≤ δ := by
    unfold b
    rw [iteratedFDeriv_sub_apply ((hgt.contDiffAt hnx).of_le (by exact_mod_cast hj))
      ((hz.contDiffAt hnx).of_le (by exact_mod_cast hj))]
    exact (hSg j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) x hx).le
  have hgtB (j : ℕ) (hj : j ≤ d) : ‖iteratedFDeriv ℝ j (g t) x‖ ≤ D + 1 :=
    (norm_le_norm_sub_add _ (iteratedFDeriv ℝ j z x)).trans
      (by linarith [hD j hj x hx, hSg j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) x hx])
  let A := fun y => B (a y) (g t y)
  let Q := fun y => B (w y) (b y)
  have hSplit : (fun y => B (f t y) (g t y)) - (fun y => B (w y) (z y)) = A + Q := by
    funext y
    simp only [A, Q, a, b, Pi.sub_apply, Pi.add_apply, map_sub, sub_apply]
    abel
  have hA : ContDiffAt ℝ d A x := ((B.contDiff.comp_contDiffOn ha).clm_apply hgt).contDiffAt hnx
  have hQ : ContDiffAt ℝ d Q x := ((B.contDiff.comp_contDiffOn hw).clm_apply hb).contDiffAt hnx
  have hFt : ContDiffAt ℝ d (fun y => B (f t y) (g t y)) x :=
    ((B.contDiff.comp_contDiffOn hft).clm_apply hgt).contDiffAt hnx
  have hWz : ContDiffAt ℝ d (fun y => B (w y) (z y)) x :=
    ((B.contDiff.comp_contDiffOn hw).clm_apply hz).contDiffAt hnx
  rw [dist_comm, dist_eq_norm, ← iteratedFDeriv_sub_apply hFt hWz,
    hSplit, iteratedFDeriv_add_apply hA hQ]
  calc
    _ ≤ ‖iteratedFDeriv ℝ d A x‖ + ‖iteratedFDeriv ℝ d Q x‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ((2 : ℝ) ^ d * δ * (D + 1)) + ‖B‖ * ((2 : ℝ) ^ d * C * δ) :=
      add_le_add (norm_iteratedFDeriv_bilinear_le_of_bounds B hU ha hgt hxU hδ.le haB hgtB)
        (norm_iteratedFDeriv_bilinear_le_of_bounds B hU hw hb hxU hC₀ (fun j hj => hC j hj x hx) hbB)
    _ = M * δ := by unfold M; ring
    _ < (M + 1) * δ := mul_lt_mul_of_pos_right (lt_add_one M) hδ
    _ ≤ ε := (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)).trans_eq
      (by rw [mul_comm, div_mul_cancel₀ _ (by positivity : M + 1 ≠ 0)])

end BilinearJets

section Momentum

private theorem tendstoUniformlyOn_iteratedFDeriv_fderiv_of_succ
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {l : Filter ι}
    {f : ι → Vec3 → E} {w : Vec3 → E} {K : Set Vec3} (d : ℕ)
    (h : TendstoUniformlyOn (fun t => iteratedFDeriv ℝ (d + 1) (f t))
      (iteratedFDeriv ℝ (d + 1) w) l K) :
    TendstoUniformlyOn (fun t => iteratedFDeriv ℝ d (fderiv ℝ (f t)))
      (iteratedFDeriv ℝ d (fderiv ℝ w)) l K := by
  let L := continuousMultilinearCurryRightEquiv' ℝ d Vec3 E
  have hjet (g : Vec3 → E) : iteratedFDeriv ℝ d (fderiv ℝ g) =
      L ∘ iteratedFDeriv ℝ (d + 1) g := by
    funext x
    change iteratedFDeriv ℝ d (fderiv ℝ g) x = L (iteratedFDeriv ℝ (d + 1) g x)
    rw [iteratedFDeriv_succ_eq_comp_right]
    exact (L.apply_symm_apply _).symm
  simp only [hjet]
  exact L.isometry.uniformContinuous.comp_tendstoUniformlyOn h

/-- Advection consumes one extra spatial derivative of velocity in the
off-origin terminal limit. -/
theorem hasOffOriginLimits_advection_of_velocity
    {T : ℝ} {u : Velocity} (hs : ∀ t ∈ Ico 0 T, ContDiff ℝ ∞ (u t))
    (hu : HasOffOriginLimits T u) :
    HasOffOriginLimits T (fun t x => fderiv ℝ (u t) x (u t x)) := by
  intro K hK hKo m
  obtain ⟨U, w, hU, hKU, hUo, hw, hlim⟩ := hu K hK hKo (m + 1)
  have hwD : ContDiffOn ℝ m (fderiv ℝ w) U :=
    hw.fderiv_of_isOpen hU (by exact_mod_cast (le_rfl : m + 1 ≤ m + 1))
  have hw₀ : ContDiffOn ℝ m w U := hw.of_le (by exact_mod_cast Nat.le_succ m)
  let B : (Vec3 →L[ℝ] Vec3) →L[ℝ] Vec3 →L[ℝ] Vec3 :=
    (ContinuousLinearMap.apply ℝ Vec3).flip
  refine ⟨U, fun x => fderiv ℝ w x (w x), hU, hKU, hUo, hwD.clm_apply hw₀, ?_⟩
  intro d hd
  have hD : ∀ᶠ t in 𝓝[Ico 0 T] T, ContDiffOn ℝ d (fderiv ℝ (u t)) U := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (((hs t ht).fderiv_right (m := d) (by simp))).contDiffOn
  have hC : ∀ᶠ t in 𝓝[Ico 0 T] T, ContDiffOn ℝ d (u t) U := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ((hs t ht).of_le (by simp)).contDiffOn
  have hF (j : ℕ) (hj : j ≤ d) :
      TendstoUniformlyOn (fun t => iteratedFDeriv ℝ j (fderiv ℝ (u t)))
        (iteratedFDeriv ℝ j (fderiv ℝ w)) (𝓝[Ico 0 T] T) K :=
    tendstoUniformlyOn_iteratedFDeriv_fderiv_of_succ j (hlim (j + 1) (Nat.succ_le_succ (hj.trans hd)))
  change TendstoUniformlyOn (fun t => iteratedFDeriv ℝ d (fun x => B (fderiv ℝ (u t) x) (u t x)))
    (iteratedFDeriv ℝ d (fun x => B (fderiv ℝ w x) (w x))) (𝓝[Ico 0 T] T) K
  exact tendstoUniformlyOn_iteratedFDeriv_bilinear_of_jet_limits B hU hK hKU hD hC
    (hwD.of_le (by exact_mod_cast hd)) (hw₀.of_le (by exact_mod_cast hd)) hF
    (fun j hj => hlim j (hj.trans (hd.trans (Nat.le_succ _))))

private theorem hasOffOriginLimits_neg_sub
    {T : ℝ} {a b : Velocity}
    (ha : HasOffOriginLimits T a) (hb : HasOffOriginLimits T b)
    (hAs : ∀ t ∈ Ico 0 T, ContDiff ℝ ∞ (a t))
    (hBs : ∀ t ∈ Ico 0 T, ContDiff ℝ ∞ (b t)) :
    HasOffOriginLimits T (fun t x => -a t x - b t x) := by
  intro K hK hKo m
  obtain ⟨U, g, hU, hKU, hUo, hg, hgLim⟩ := ha K hK hKo m
  obtain ⟨V, w, hV, hKV, hVo, hw, hwLim⟩ := hb K hK hKo m
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hKW : K ⊆ W := fun _ hx => ⟨hKU hx, hKV hx⟩
  refine ⟨W, -g - w, hW, hKW, inter_subset_left.trans hUo,
    ((hg.mono inter_subset_left).neg).sub (hw.mono inter_subset_right), ?_⟩
  intro d hd
  have hg' : ContDiffOn ℝ d g U := hg.of_le (by exact_mod_cast hd)
  have hw' : ContDiffOn ℝ d w V := hw.of_le (by exact_mod_cast hd)
  refine (((hgLim d hd).neg.sub (hwLim d hd)).congr ?_).congr_right ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht x _
    have hAt : ContDiffAt ℝ d (-a t) x := (((hAs t ht).of_le (by simp)).neg).contDiffAt
    have hBt : ContDiffAt ℝ d (b t) x := ((hBs t ht).of_le (by simp)).contDiffAt
    change -iteratedFDeriv ℝ d (a t) x - iteratedFDeriv ℝ d (b t) x =
      iteratedFDeriv ℝ d (-a t - b t) x
    rw [iteratedFDeriv_sub_apply hAt hBt, iteratedFDeriv_neg_apply]
  · intro x hx
    change -iteratedFDeriv ℝ d g x - iteratedFDeriv ℝ d w x = iteratedFDeriv ℝ d (-g - w) x
    have hAt : ContDiffAt ℝ d (-g) x := (hg'.contDiffAt (hU.mem_nhds (hKU hx))).neg
    have hBt : ContDiffAt ℝ d w x := hw'.contDiffAt (hV.mem_nhds (hKV hx))
    rw [iteratedFDeriv_sub_apply hAt hBt, iteratedFDeriv_neg_apply]

/-- Actual Euler momentum identifies the terminal time derivative using the
velocity and pressure-gradient spatial limits. -/
theorem IsEulerSolution.hasOffOriginLimits_timeDerivative
    {T : ℝ} {u : Velocity} {p : Pressure} (h : IsEulerSolution T u p)
    (hu : HasOffOriginLimits T u)
    (hp : HasOffOriginLimits T (fun t => gradient (p t))) :
    HasOffOriginLimits T (timeDerivative T u) := by
  have huS (t : ℝ) (ht : t ∈ Ico 0 T) : ContDiff ℝ ∞ (u t) := h.contDiff_velocity_slice ht
  have hpS (t : ℝ) (ht : t ∈ Ico 0 T) : ContDiff ℝ ∞ (gradient (p t)) := by
    let R : (Vec3 →L[ℝ] ℝ) →L[ℝ] Vec3 :=
      (InnerProductSpace.toDual ℝ Vec3).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hpT : ContDiff ℝ ∞ (p t) := by
      rw [← contDiffOn_univ]
      exact h.smooth_pressure.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun x _ => ⟨ht, mem_univ x⟩)
    exact R.contDiff.comp (hpT.fderiv_right (m := ∞) (by simp))
  have hAd (t : ℝ) (ht : t ∈ Ico 0 T) :
      ContDiff ℝ ∞ (fun x => fderiv ℝ (u t) x (u t x)) :=
    ((huS t ht).fderiv_right (m := ∞) (by simp)).clm_apply (huS t ht)
  have hlim := hasOffOriginLimits_neg_sub (hasOffOriginLimits_advection_of_velocity huS hu)
    hp hAd hpS
  refine hasOffOriginLimits_timeDerivative_of_dynamics ?_ hlim
  intro t ht x _
  have hm : timeDerivative T u t x = -fderiv ℝ (u t) x (u t x) - gradient (p t) x := by
    calc
      _ = (timeDerivative T u t x + fderiv ℝ (u t) x (u t x) + gradient (p t) x) -
        fderiv ℝ (u t) x (u t x) - gradient (p t) x := by abel
      _ = _ := by rw [h.momentum t ht x, zero_sub]
  exact hm ▸ h.hasDerivWithinAt_velocity ht x

end Momentum

end TorusEuler
