import Breakdown.FracCert.HeldStateLimitBParts

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace Internal.DriftWeakLimit

def IsBumpField (h : Space → Space) : Prop := Continuous h ∧ HasCompactSupport h

theorem coord_cont (i : Fin 3) : Continuous (fun y : Space => y i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous

def turnL : Space →L[ℝ] Space :=
  (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).smulRight (-unitVector 0) +
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 1)

theorem turnL_apply (y : Space) : turnL y = axialTurn y := by
  ext i
  fin_cases i <;> simp [turnL, axialTurn, unitVector]

theorem continuous_turn : Continuous axialTurn :=
  (funext turnL_apply : ⇑turnL = axialTurn) ▸ turnL.continuous

theorem turn_zero : axialTurn 0 = 0 := by
  rw [← turnL_apply, map_zero]

theorem vec_decomp (x : Space) : x = ∑ k : Fin 3, x k • unitVector k := by
  ext i
  fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

theorem clm_decomp (L : Space →L[ℝ] Space) (x : Space) :
    L x = ∑ k : Fin 3, x k • L (unitVector k) := by
  conv_lhs => rw [vec_decomp x]
  simp only [map_sum, map_smul]

theorem inner_turn (u w : Space) : inner ℝ (axialTurn u) w = -inner ℝ u (axialTurn w) := by
  rw [vec_decomp u, vec_decomp w]
  simp [axialTurn, unitVector, Fin.sum_univ_three, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
  ring

theorem bump_memLp {h : Space → Space} (hh : IsBumpField h) : MemLp h 2 volume :=
  hh.1.memLp_of_hasCompactSupport hh.2

theorem bump_smul {c : Space → ℝ} (hc : Continuous c) {h : Space → Space} (hh : IsBumpField h) :
    IsBumpField (fun y => c y • h y) :=
by
  refine ⟨hc.smul hh.1, hh.2.mono ?_⟩
  intro y hy
  rw [Function.mem_support] at hy ⊢
  intro h0
  exact hy (by rw [h0, smul_zero])

theorem bump_const {φ : Space → ℝ} (hφ : Continuous φ) (hs : HasCompactSupport φ) (c : Space) :
    IsBumpField (fun y => φ y • c) := by
  refine ⟨hφ.smul continuous_const, hs.mono ?_⟩
  intro y hy
  rw [Function.mem_support] at hy ⊢
  intro h0
  exact hy (by rw [h0, zero_smul])

theorem bump_turn {h : Space → Space} (hh : IsBumpField h) : IsBumpField (fun y => axialTurn (h y)) :=
by
  refine ⟨continuous_turn.comp hh.1, hh.2.mono ?_⟩
  intro y hy
  rw [Function.mem_support] at hy ⊢
  intro h0
  exact hy (by rw [h0, turn_zero])

theorem pair_int {f h : Space → Space} (hf : LocallyIntegrable f volume) (hh : IsBumpField h) :
    Integrable (fun y => inner ℝ (f y) (h y)) := by
  have hI : Integrable (fun y => ‖h y‖ • f y) :=
    hf.integrable_smul_left_of_hasCompactSupport hh.1.norm hh.2.norm
  refine hI.norm.mono' (hf.aestronglyMeasurable.inner hh.1.aestronglyMeasurable) ?_
  filter_upwards with y
  rw [norm_smul, norm_norm, mul_comm]
  exact norm_inner_le_norm _ _

theorem vel_li {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    LocallyIntegrable v volume :=
  hs.velocity_six.locallyIntegrable (by norm_num)

theorem col_memLp {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (k : Fin 3) :
    MemLp (fun y => G y (unitVector k)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => G y (unitVector k)) volume :=
    hs.measurable_gradient.apply_continuousLinearMap _
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine hs.gradient_two.mono' (hm.norm.pow 2) ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  unfold entrySq
  exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => sq_nonneg _)
    (Finset.mem_univ k)

theorem col_li {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (k : Fin 3) :
    LocallyIntegrable (fun y => G y (unitVector k)) volume :=
  (col_memLp hs k).locallyIntegrable (by norm_num)

theorem drift_pair (α a : ℝ) (v : Space → Space) (A : Space → (Space →L[ℝ] Space)) (g : Space → Space)
    (y : Space) :
    inner ℝ (driftField α a v A y) (g y) =
      inner ℝ (v y) ((1 - 1 / (2 * α)) • g y) + a * inner ℝ (v y) (axialTurn (g y)) +
        ∑ k : Fin 3, (inner ℝ (A y (unitVector k)) ((1 / (2 * α) * y k) • g y) +
          a * inner ℝ (A y (unitVector k)) ((axialTurn y) k • g y)) := by
  have h1 := clm_decomp (A y) y
  have h2 := clm_decomp (A y) (axialTurn y)
  rw [driftField, h1, h2]
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left, real_inner_smul_right,
    inner_turn, Fin.sum_univ_three]
  ring

theorem drift_int (α a : ℝ) {v : Space → Space} {A : Space → (Space →L[ℝ] Space)}
    (hv : LocallyIntegrable v volume) (hA : ∀ k, LocallyIntegrable (fun y => A y (unitVector k)) volume)
    {g : Space → Space} (hg : IsBumpField g) :
    ∫ y, inner ℝ (driftField α a v A y) (g y) =
      (∫ y, inner ℝ (v y) ((1 - 1 / (2 * α)) • g y)) + a * (∫ y, inner ℝ (v y) (axialTurn (g y))) +
        ∑ k : Fin 3, ((∫ y, inner ℝ (A y (unitVector k)) ((1 / (2 * α) * y k) • g y)) +
          a * (∫ y, inner ℝ (A y (unitVector k)) ((axialTurn y) k • g y))) := by
  have t0 : IsBumpField (fun y => (1 - 1 / (2 * α)) • g y) := bump_smul continuous_const hg
  have t1 : IsBumpField (fun y => axialTurn (g y)) := bump_turn hg
  have t2 : ∀ k : Fin 3, IsBumpField (fun y => (1 / (2 * α) * y k) • g y) :=
    fun k => bump_smul (continuous_const.mul (coord_cont k)) hg
  have t3 : ∀ k : Fin 3, IsBumpField (fun y => (axialTurn y) k • g y) :=
    fun k => bump_smul ((coord_cont k).comp continuous_turn) hg
  have i0 := pair_int hv t0
  have i1 := pair_int hv t1
  have i2 := fun k => pair_int (hA k) (t2 k)
  have i3 := fun k => pair_int (hA k) (t3 k)
  have j01 : Integrable (fun y => inner ℝ (v y) ((1 - 1 / (2 * α)) • g y) +
      a * inner ℝ (v y) (axialTurn (g y))) := i0.add (i1.const_mul a)
  have jk : ∀ k : Fin 3, Integrable (fun y => inner ℝ (A y (unitVector k)) ((1 / (2 * α) * y k) • g y) +
      a * inner ℝ (A y (unitVector k)) ((axialTurn y) k • g y)) := fun k => (i2 k).add ((i3 k).const_mul a)
  have js : Integrable (fun y => ∑ k : Fin 3, (inner ℝ (A y (unitVector k)) ((1 / (2 * α) * y k) • g y) +
      a * inner ℝ (A y (unitVector k)) ((axialTurn y) k • g y))) := integrable_finsetSum _ fun k _ => jk k
  simp_rw [drift_pair]
  rw [integral_add j01 js, integral_add i0 (i1.const_mul a), integral_const_mul,
    integral_finsetSum _ fun k _ => jk k]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_add (i2 k) ((i3 k).const_mul a), integral_const_mul]

theorem vel_tendsto {u : ℕ → Space → Space} {w₀ : Space → Space}
    (hw : ∀ g : Space → Space, MemLp g 2 volume →
      Tendsto (fun n => ∫ y, inner ℝ (‖y‖⁻¹ • u n y) (g y)) atTop (𝓝 (∫ y, inner ℝ (w₀ y) (g y))))
    {h : Space → Space} (hh : IsBumpField h) :
    Tendsto (fun n => ∫ y, inner ℝ (u n y) (h y)) atTop (𝓝 (∫ y, inner ℝ (‖y‖ • w₀ y) (h y))) := by
  have hb : IsBumpField (fun y => ‖y‖ • h y) := bump_smul continuous_norm hh
  have h0 : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
    have : (volume : Measure Space) {(0 : Space)} = 0 := measure_singleton 0
    filter_upwards [compl_mem_ae_iff.2 this] with y hy
    exact hy
  have e1 : ∀ n, ∫ y, inner ℝ (‖y‖⁻¹ • u n y) (‖y‖ • h y) = ∫ y, inner ℝ (u n y) (h y) := by
    intro n
    refine integral_congr_ae ?_
    filter_upwards [h0] with y hy
    have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  have e2 : ∫ y, inner ℝ (‖y‖ • w₀ y) (h y) = ∫ y, inner ℝ (w₀ y) (‖y‖ • h y) := by
    congr 1
    funext y
    rw [real_inner_smul_left, real_inner_smul_right]
  rw [e2]
  exact (hw _ (bump_memLp hb)).congr e1

end Internal.DriftWeakLimit

open Internal.DriftWeakLimit in
theorem driftWeakLimit_holds : DriftWeakLimitStatement := by
  intro α hα1 hα2 m a a₀ u G H w₀ G₀ H₀ D₀ ha hs hs₀ hD hw hD₀ hG hwl hDl
  have hv0 : LocallyIntegrable (fun y => ‖y‖ • w₀ y) volume := vel_li hs₀
  have hA0 : ∀ k, LocallyIntegrable (fun y => G₀ y (unitVector k)) volume := col_li hs₀
  have hpair : ∀ g, IsBumpField g → ∫ y, inner ℝ (D₀ y) (g y) =
      ∫ y, inner ℝ (driftField α a₀ (fun y => ‖y‖ • w₀ y) G₀ y) (g y) := by
    intro g hg
    have t0 : IsBumpField (fun y => (1 - 1 / (2 * α)) • g y) := bump_smul continuous_const hg
    have t1 : IsBumpField (fun y => axialTurn (g y)) := bump_turn hg
    have t2 : ∀ k : Fin 3, IsBumpField (fun y => (1 / (2 * α) * y k) • g y) :=
      fun k => bump_smul (continuous_const.mul (coord_cont k)) hg
    have t3 : ∀ k : Fin 3, IsBumpField (fun y => (axialTurn y) k • g y) :=
      fun k => bump_smul ((coord_cont k).comp continuous_turn) hg
    have lim : Tendsto (fun n => ∫ y, inner ℝ (driftField α (a n) (u n) (G n) y) (g y)) atTop
        (𝓝 (∫ y, inner ℝ (driftField α a₀ (fun y => ‖y‖ • w₀ y) G₀ y) (g y))) := by
      rw [drift_int α a₀ hv0 hA0 hg]
      refine Tendsto.congr (fun n => (drift_int α (a n) (vel_li (hs n)) (col_li (hs n)) hg).symm) ?_
      refine ((vel_tendsto hwl t0).add (ha.mul (vel_tendsto hwl t1))).add
        (tendsto_finsetSum _ fun k _ => ?_)
      exact (hG k _ (bump_memLp (t2 k))).add (ha.mul (hG k _ (bump_memLp (t3 k))))
    exact tendsto_nhds_unique (hDl g (bump_memLp hg)) lim
  have hE : LocallyIntegrable (driftField α a₀ (fun y => ‖y‖ • w₀ y) G₀) volume := by
    have hsum : ∀ x : Space → Space, Continuous x → LocallyIntegrable (fun y => G₀ y (x y)) volume := by
      intro x hx
      have e : (fun y => G₀ y (x y)) = fun y => ∑ k : Fin 3, x y k • G₀ y (unitVector k) :=
        funext fun y => clm_decomp (G₀ y) (x y)
      rw [e]
      exact locallyIntegrable_finsetSum _ fun k _ => (hA0 k).continuous_smul ((coord_cont k).comp hx)
    have hturn : LocallyIntegrable (fun y => axialTurn (‖y‖ • w₀ y)) volume := by
      have h1 := locallyIntegrableOn_univ.1 (turnL.locallyIntegrableOn_comp (hv0.locallyIntegrableOn Set.univ))
      have e : (⇑turnL ∘ fun y => ‖y‖ • w₀ y) = fun y => axialTurn (‖y‖ • w₀ y) :=
        funext fun y => turnL_apply _
      rw [e] at h1
      exact h1
    have e : driftField α a₀ (fun y => ‖y‖ • w₀ y) G₀ = fun y => (1 - 1 / (2 * α)) • (‖y‖ • w₀ y) +
        (1 / (2 * α)) • G₀ y y + a₀ • (G₀ y (axialTurn y) - axialTurn (‖y‖ • w₀ y)) := rfl
    rw [e]
    exact ((hv0.smul (1 - 1 / (2 * α))).add ((hsum id continuous_id).smul (1 / (2 * α)))).add
      (((hsum axialTurn continuous_turn).sub hturn).smul a₀)
  have hDli : LocallyIntegrable D₀ volume := hD₀.locallyIntegrable (by norm_num)
  have key : ∀ φ : Space → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ y, φ y • driftField α a₀ (fun y => ‖y‖ • w₀ y) G₀ y = ∫ y, φ y • D₀ y := by
    intro φ hφ hφs
    refine ext_inner_left ℝ fun c => ?_
    rw [← integral_inner (hE.integrable_smul_left_of_hasCompactSupport hφ.continuous hφs) c,
      ← integral_inner (hDli.integrable_smul_left_of_hasCompactSupport hφ.continuous hφs) c]
    have hb : IsBumpField (fun y => φ y • c) :=
      bump_const hφ.continuous hφs c
    have h1 := hpair _ hb
    have e : ∀ X : Space → Space, (∫ y, inner ℝ c (φ y • X y)) = ∫ y, inner ℝ (X y) (φ y • c) := by
      intro X
      congr 1
      funext y
      rw [real_inner_smul_right, real_inner_smul_right, real_inner_comm]
    rw [e, e, h1]
  have hae := ae_eq_of_integral_contDiff_smul_eq hE hDli key
  exact hD₀.ae_eq (hae.mono fun y hy => hy.symm)

end SteadyCert

end Breakdown
