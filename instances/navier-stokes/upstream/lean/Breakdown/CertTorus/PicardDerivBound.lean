import Breakdown.CertTorus.RegularStatements
import Breakdown.Weak.ContinuousVarConst
import Breakdown.Weak.BilinIntegrable
import Breakdown.FreqTr.MildOfWeak

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

noncomputable section

namespace Breakdown.FarField

open Freq SmoothFlow

namespace Internal.PicardDeriv

theorem monoSymbol_cons {n : ℕ} (j : Fin 3) (β : Fin n → Fin 3) (ξ : Space) :
    monoSymbol (Matrix.vecCons j β) ξ = monoSymbol ![j] ξ * monoSymbol β ξ := by
  simp [monoSymbol, Fin.prod_univ_succ]

theorem isDerivX_add {n : ℕ} {α : Fin n → Fin 3} {x x' y y' : X} (h : IsDerivX α x y)
    (h' : IsDerivX α x' y') : IsDerivX α (x + x') (y + y') := by
  unfold IsDerivX symX at *
  have e1 : (((x + x' : X) : L2C) : Space → CSpace) =ᵐ[volume]
      ((x : L2C) : Space → CSpace) + ((x' : L2C) : Space → CSpace) := by
    rw [Submodule.coe_add]; exact Lp.coeFn_add _ _
  have e2 : (((y + y' : X) : L2C) : Space → CSpace) =ᵐ[volume]
      ((y : L2C) : Space → CSpace) + ((y' : L2C) : Space → CSpace) := by
    rw [Submodule.coe_add]; exact Lp.coeFn_add _ _
  filter_upwards [h, h', e1, e2] with ξ a b c d
  rw [d, Pi.add_apply, a, b, c, Pi.add_apply, smul_add]

theorem isDerivX_cons {n : ℕ} {j : Fin 3} {β : Fin n → Fin 3} {x x' y : X}
    (h1 : IsDerivX ![j] x x') (h2 : IsDerivX β x' y) : IsDerivX (Matrix.vecCons j β) x y := by
  unfold IsDerivX at h1 h2 ⊢
  filter_upwards [h1, h2] with ξ e1 e2
  rw [e2, e1, smul_smul, monoSymbol_cons j β, mul_comm (monoSymbol β ξ)]

theorem isDerivX_cons' {n : ℕ} {j : Fin 3} {β : Fin n → Fin 3} {x x' y : X}
    (h1 : IsDerivX β x x') (h2 : IsDerivX ![j] x' y) : IsDerivX (Matrix.vecCons j β) x y := by
  unfold IsDerivX at h1 h2 ⊢
  filter_upwards [h1, h2] with ξ e1 e2
  rw [e2, e1, smul_smul, monoSymbol_cons j β]

theorem isDerivX_of_cons {n : ℕ} {j : Fin 3} {β : Fin n → Fin 3} {x x' y : X}
    (h1 : IsDerivX ![j] x x') (h2 : IsDerivX (Matrix.vecCons j β) x y) : IsDerivX β x' y := by
  unfold IsDerivX at h1 h2 ⊢
  filter_upwards [h1, h2] with ξ e1 e2
  rw [e2, e1, smul_smul, monoSymbol_cons j β, mul_comm (monoSymbol ![j] ξ)]

theorem bilin_deriv_bound (hA : DerivAlgebra) (hL : BilinLeibniz) {C τ : ℝ} (hC0 : 0 ≤ C)
    (hτ : 0 < τ) (hC : ∀ u v : X, ‖bilinX τ u v‖ ≤ C * τ ^ (-(3 / 4 : ℝ)) * ‖u‖ * ‖v‖) :
    ∀ (m : ℕ) (u v : X) (c : ℕ → ℝ),
      (∀ i j, i + j ≤ m → ∀ (β : Fin i → Fin 3) (γ : Fin j → Fin 3),
        ∃ y z, IsDerivX β u y ∧ IsDerivX γ v z ∧ ‖y‖ * ‖z‖ ≤ c (i + j)) →
      ∀ α : Fin m → Fin 3, ∃ w, IsDerivX α (bilinX τ u v) w ∧
        ‖w‖ ≤ C * τ ^ (-(3 / 4 : ℝ)) * 2 ^ m * c m := by
  intro m
  induction m with
  | zero =>
    intro u v c h α
    obtain ⟨y, z, hy, hz, hyz⟩ := h 0 0 le_rfl ![] ![]
    have e1 : y = u := hA.1 0 _ u y u hy (hA.2.1 _ u)
    have e2 : z = v := hA.1 0 _ v z v hz (hA.2.1 _ v)
    subst e1 e2
    refine ⟨bilinX τ y z, hA.2.1 α _, ?_⟩
    have hp : 0 ≤ C * τ ^ (-(3 / 4 : ℝ)) := mul_nonneg hC0 (rpow_nonneg hτ.le _)
    have hyz' : ‖y‖ * ‖z‖ ≤ c 0 := by simpa using hyz
    calc ‖bilinX τ y z‖ ≤ C * τ ^ (-(3 / 4 : ℝ)) * ‖y‖ * ‖z‖ := hC y z
      _ = C * τ ^ (-(3 / 4 : ℝ)) * (‖y‖ * ‖z‖) := by ring
      _ ≤ C * τ ^ (-(3 / 4 : ℝ)) * c 0 := by nlinarith [hyz', hp]
      _ = C * τ ^ (-(3 / 4 : ℝ)) * 2 ^ 0 * c 0 := by ring
  | succ m ih =>
    intro u v c h α
    have h10 : 1 + 0 ≤ m + 1 := by omega
    have h01 : 0 + 1 ≤ m + 1 := by omega
    have e1 := h 1 0 h10 (![α 0] : Fin 1 → Fin 3) (![] : Fin 0 → Fin 3)
    have e2 := h 0 1 h01 (![] : Fin 0 → Fin 3) (![α 0] : Fin 1 → Fin 3)
    obtain ⟨u', z0, hu', hz0, hb0⟩ := e1
    obtain ⟨y0, v', hy0, hv', hb0'⟩ := e2
    have hu : ∀ i j, i + j ≤ m → ∀ (β : Fin i → Fin 3) (γ : Fin j → Fin 3),
        ∃ y z, IsDerivX β u' y ∧ IsDerivX γ v z ∧ ‖y‖ * ‖z‖ ≤ c (i + j + 1) := by
      intro i j hij β γ
      obtain ⟨y, z, hy, hz, hyz⟩ := h (i + 1) j (by omega) (Matrix.vecCons (α 0) β) γ
      refine ⟨y, z, isDerivX_of_cons hu' hy, hz, ?_⟩
      rwa [Nat.add_right_comm] at hyz
    have hv : ∀ i j, i + j ≤ m → ∀ (β : Fin i → Fin 3) (γ : Fin j → Fin 3),
        ∃ y z, IsDerivX β u y ∧ IsDerivX γ v' z ∧ ‖y‖ * ‖z‖ ≤ c (i + j + 1) := by
      intro i j hij β γ
      obtain ⟨y, z, hy, hz, hyz⟩ := h i (j + 1) (by omega) β (Matrix.vecCons (α 0) γ)
      exact ⟨y, z, hy, isDerivX_of_cons hv' hz, hyz⟩
    have i1 := ih u' v (fun l => c (l + 1)) hu
    have i2 := ih u v' (fun l => c (l + 1)) hv
    have j1 := i1 (fun i => α i.succ)
    have j2 := i2 (fun i => α i.succ)
    obtain ⟨w1, hw1, hb1⟩ := j1
    obtain ⟨w2, hw2, hb2⟩ := j2
    have hs := isDerivX_add hw1 hw2
    refine ⟨w1 + w2, ?_, ?_⟩
    · have := isDerivX_cons (hL τ hτ (α 0) u u' v v' hu' hv') hs
      rwa [show (Matrix.vecCons (α 0) fun i => α i.succ) = α from Matrix.cons_head_tail α] at this
    · calc ‖w1 + w2‖ ≤ ‖w1‖ + ‖w2‖ := norm_add_le _ _
        _ ≤ C * τ ^ (-(3 / 4 : ℝ)) * 2 ^ m * c (m + 1) +
            C * τ ^ (-(3 / 4 : ℝ)) * 2 ^ m * c (m + 1) := add_le_add hb1 hb2
        _ = C * τ ^ (-(3 / 4 : ℝ)) * 2 ^ (m + 1) * c (m + 1) := by ring

theorem aestronglyMeasurable_deriv (hA : DerivAlgebra) (hQ : DiffQuotient) {μ : Measure ℝ} :
    ∀ (m : ℕ) (F : ℝ → X), AEStronglyMeasurable F μ →
      (∀ᵐ s ∂μ, ∀ l ≤ m, ∀ β : Fin l → Fin 3, ∃ y, IsDerivX β (F s) y) →
      ∀ (α : Fin m → Fin 3) (G : ℝ → X), (∀ᵐ s ∂μ, IsDerivX α (F s) (G s)) →
        AEStronglyMeasurable G μ := by
  intro m
  induction m with
  | zero =>
    intro F hF _ α G hG
    refine hF.congr ?_
    filter_upwards [hG] with s hs
    exact hA.1 0 α (F s) (F s) (G s) (hA.2.1 α (F s)) hs
  | succ m ih =>
    intro F hF hex α G hG
    classical
    let F' : ℝ → X := fun s => if h : ∃ y, IsDerivX ![α 0] (F s) y then h.choose else 0
    have hF'd : ∀ᵐ s ∂μ, IsDerivX ![α 0] (F s) (F' s) := by
      filter_upwards [hex] with s hs
      have h1 : ∃ y, IsDerivX ![α 0] (F s) y := hs 1 (by omega) ![α 0]
      simp only [F', dif_pos h1]
      exact h1.choose_spec
    have hseq : Tendsto (fun l : ℕ => 1 / ((l : ℝ) + 1)) atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun l => (show (1 / ((l : ℝ) + 1)) ≠ 0 by positivity)⟩
    have hF' : AEStronglyMeasurable F' μ := by
      refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun (l : ℕ) s =>
        (1 / ((l : ℝ) + 1))⁻¹ • (shiftX (-((1 / ((l : ℝ) + 1)) • unitVector (α 0))) (F s) - F s))
        (fun l => ?_) ?_
      · exact (((shiftX _).continuous.comp_aestronglyMeasurable hF).sub hF).const_smul ((1 / ((l : ℝ) + 1))⁻¹)
      · filter_upwards [hF'd] with s hs
        exact ((hQ (α 0) (F s) (F' s)).1 hs).comp hseq
    refine ih F' hF' ?_ (fun i => α i.succ) G ?_
    · filter_upwards [hex, hF'd] with s hs hs'
      intro l hl β
      obtain ⟨y, hy⟩ := hs (l + 1) (by omega) (Matrix.vecCons (α 0) β)
      exact ⟨y, isDerivX_of_cons hs' hy⟩
    · filter_upwards [hG, hF'd] with s hs hs'
      exact isDerivX_of_cons (β := fun i => α i.succ) hs'
        (by rw [show (Matrix.vecCons (α 0) fun i => α i.succ) = α from Matrix.cons_head_tail α]; exact hs)

theorem picardIter_self (x : X) (a : ℝ) : ∀ n, fixedPointIter x a n a = x
  | 0 => by simp [fixedPointIter, heat_holds.1]
  | n + 1 => by simp [fixedPointIter, heat_holds.1]

theorem continuousOn_picardIter (x : X) (a : ℝ) : ∀ n, ContinuousOn (fixedPointIter x a n) (Ici a)
  | 0 => by
    have h : ContinuousOn (fun t => heatX (t - a) x) (Ici a) :=
      (heat_holds.2.2.2.1 x).comp (by fun_prop) (fun t ht => mem_Ici.2 (sub_nonneg.2 (mem_Ici.1 ht)))
    exact h
  | n + 1 => by
    have hp := continuousOn_picardIter x a n
    have hyc : Continuous (fun s => fixedPointIter x a n (max s a)) :=
      hp.comp_continuous (by fun_prop) (fun s => le_max_right s a)
    intro t ht
    have hat : a ≤ t := ht
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hyc.continuousOn (s := Icc (a - 1) (t + 1)))
    have hD := WeakProfile.continuousVarConst_holds WeakProfile.bilinIntegrable_holds
      (fun s => fixedPointIter x a n (max s a)) (a - 1) (t + 1) M
      (fun s hs => hM s (Ioo_subset_Icc_self hs)) hyc.aestronglyMeasurable a
      ⟨by linarith, by linarith⟩
    have heq : EqOn (WeakProfile.varConst (fun s => fixedPointIter x a n (max s a)) a)
        (fixedPointIter x a (n + 1)) (Ico a (t + 1)) := by
      intro s hs
      have hs' : a ≤ s := hs.1
      simp only [WeakProfile.varConst, fixedPointIter, max_self, picardIter_self]
      congr 1
      refine intervalIntegral.integral_congr fun r hr => ?_
      have har : a ≤ r := by
        rw [uIcc_of_le hs'] at hr
        exact hr.1
      simp only [max_eq_left har]
    have hc := (hD.congr heq.symm) t ⟨hat, by linarith⟩
    exact hc.mono_of_mem_nhdsWithin (by
      rw [← Ici_inter_Iio]
      exact inter_mem_nhdsWithin _ (Iio_mem_nhds (by linarith)))

theorem integral_rpow_sub_left {a t r : ℝ} (hr : -1 < r) :
    ∫ s in a..t, (t - s) ^ r = (t - a) ^ (r + 1) / (r + 1) := by
  have e := intervalIntegral.integral_comp_sub_left (fun s : ℝ => s ^ r) (a := a) (b := t) t
  rw [e, sub_self, integral_rpow (Or.inl hr), zero_rpow (by linarith : (0 : ℝ) < r + 1).ne',
    sub_zero]

theorem integral_rpow_sub_right {a t r : ℝ} (hr : -1 < r) :
    ∫ s in a..t, (s - a) ^ r = (t - a) ^ (r + 1) / (r + 1) := by
  have e := intervalIntegral.integral_comp_sub_right (fun s : ℝ => s ^ r) (a := a) (b := t) a
  rw [e, sub_self, integral_rpow (Or.inl hr), zero_rpow (by linarith : (0 : ℝ) < r + 1).ne',
    sub_zero]

theorem intervalIntegrable_rpow_sub_left {a t r : ℝ} (hr : -1 < r) :
    IntervalIntegrable (fun s => (t - s) ^ r) volume a t := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t - a) hr).comp_sub_left t
  rw [sub_zero, sub_sub_cancel] at h
  exact h.symm

theorem intervalIntegrable_rpow_sub_right {a t r : ℝ} (hr : -1 < r) :
    IntervalIntegrable (fun s => (s - a) ^ r) volume a t := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t - a) hr).comp_sub_right a
  rw [zero_add, sub_add_cancel] at h
  exact h

theorem rpow_le_two_mul {u w r : ℝ} (hu : 0 < u) (hw : 0 < w) (hwu : w ≤ 2 * u) (hr : -1 ≤ r)
    (hr0 : r ≤ 0) : u ^ r ≤ 2 * w ^ r := by
  have h1 : (2 * u) ^ r ≤ w ^ r := rpow_le_rpow_of_nonpos hw hwu hr0
  rw [mul_rpow (by norm_num) hu.le] at h1
  have h2 : (2 : ℝ) ^ (-1 : ℝ) ≤ 2 ^ r := rpow_le_rpow_of_exponent_le (by norm_num) hr
  rw [rpow_neg_one] at h2
  have h3 : 0 ≤ u ^ r := rpow_nonneg hu.le r
  nlinarith [mul_le_mul_of_nonneg_right h2 h3]

theorem split_bound {a s t : ℝ} (has : a < s) (hst : s < t) :
    (t - s) ^ (-(3 / 4 : ℝ)) * (s - a) ^ (-(1 / 2 : ℝ)) ≤
      2 * (t - a) ^ (-(1 / 2 : ℝ)) * (t - s) ^ (-(3 / 4 : ℝ)) +
        2 * (t - a) ^ (-(3 / 4 : ℝ)) * (s - a) ^ (-(1 / 2 : ℝ)) := by
  have hu : 0 < s - a := sub_pos.2 has
  have hv : 0 < t - s := sub_pos.2 hst
  have hw : 0 < t - a := by linarith
  have p1 : 0 ≤ (t - s) ^ (-(3 / 4 : ℝ)) := rpow_nonneg hv.le _
  have p2 : 0 ≤ (s - a) ^ (-(1 / 2 : ℝ)) := rpow_nonneg hu.le _
  have p3 : 0 ≤ (t - a) ^ (-(1 / 2 : ℝ)) := rpow_nonneg hw.le _
  have p4 : 0 ≤ (t - a) ^ (-(3 / 4 : ℝ)) := rpow_nonneg hw.le _
  rcases le_total (t - a) (2 * (s - a)) with h | h
  · have e := rpow_le_two_mul (r := -(1 / 2 : ℝ)) hu hw h (by norm_num) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left e p1, mul_nonneg p4 p2]
  · have h' : t - a ≤ 2 * (t - s) := by linarith
    have e := rpow_le_two_mul (r := -(3 / 4 : ℝ)) hv hw h' (by norm_num) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right e p2, mul_nonneg p3 p1]

theorem integral_split {a t : ℝ} (hat : a < t) :
    ∫ s in a..t, (2 * (t - a) ^ (-(1 / 2 : ℝ)) * (t - s) ^ (-(3 / 4 : ℝ)) +
        2 * (t - a) ^ (-(3 / 4 : ℝ)) * (s - a) ^ (-(1 / 2 : ℝ))) =
      12 * ((t - a) ^ (1 / 4 : ℝ) * (t - a) ^ (-(1 / 2 : ℝ))) := by
  have hw : 0 < t - a := sub_pos.2 hat
  have i1 := (intervalIntegrable_rpow_sub_left (a := a) (t := t) (r := -(3 / 4 : ℝ))
    (by norm_num)).const_mul (2 * (t - a) ^ (-(1 / 2 : ℝ)))
  have i2 := (intervalIntegrable_rpow_sub_right (a := a) (t := t) (r := -(1 / 2 : ℝ))
    (by norm_num)).const_mul (2 * (t - a) ^ (-(3 / 4 : ℝ)))
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_rpow_sub_left (r := -(3 / 4 : ℝ)) (by norm_num),
    integral_rpow_sub_right (r := -(1 / 2 : ℝ)) (by norm_num)]
  have q1 : (-(3 / 4 : ℝ) + 1) = 1 / 4 := by norm_num
  have q2 : (-(1 / 2 : ℝ) + 1) = 1 / 2 := by norm_num
  rw [q1, q2]
  have e2 : (t - a) ^ (-(3 / 4 : ℝ)) * (t - a) ^ (1 / 2 : ℝ) =
      (t - a) ^ (1 / 4 : ℝ) * (t - a) ^ (-(1 / 2 : ℝ)) := by
    rw [← rpow_add hw, ← rpow_add hw]
    norm_num
  linear_combination 4 * e2

theorem integral_low {a t K : ℝ} :
    ∫ s in a..t, K * (t - s) ^ (-(3 / 4 : ℝ)) = K * (4 * (t - a) ^ (1 / 4 : ℝ)) := by
  rw [intervalIntegral.integral_const_mul, integral_rpow_sub_left (r := -(3 / 4 : ℝ)) (by norm_num)]
  have q1 : (-(3 / 4 : ℝ) + 1) = 1 / 4 := by norm_num
  rw [q1]
  ring

theorem heat_deriv_bounds (hH : DerivHeat) {k : ℕ} {M Ch τ : ℝ} (hτ : 0 < τ)
    (hCh : ∀ (α : Fin 1 → Fin 3) (t : ℝ), 0 < t → ∀ x : X,
      ∃ y, IsDerivX α (heatX t x) y ∧ ‖y‖ ≤ Ch * t ^ (-(((1 : ℕ) : ℝ) / 2)) * ‖x‖)
    {x : X} (hx : ∀ m ≤ k, ∀ α : Fin m → Fin 3, ∃ y, IsDerivX α x y ∧ ‖y‖ ≤ M) :
    (∀ m ≤ k, ∀ α : Fin m → Fin 3, ∃ y, IsDerivX α (heatX τ x) y ∧ ‖y‖ ≤ max M 0) ∧
      ∀ α : Fin (k + 1) → Fin 3,
        ∃ y, IsDerivX α (heatX τ x) y ∧ ‖y‖ ≤ |Ch| * max M 0 * τ ^ (-(1 / 2 : ℝ)) := by
  have hn : ∀ y : X, ‖heatX τ y‖ ≤ ‖y‖ := fun y => by
    simpa using (heatX τ).le_of_opNorm_le (heat_holds.2.2.1 τ hτ.le) y
  refine ⟨fun m hm α => ?_, fun α => ?_⟩
  · have e := hx m hm α
    obtain ⟨y, hy, hyM⟩ := e
    exact ⟨heatX τ y, hH.1 m α τ x y hy, (hn y).trans (hyM.trans (le_max_left _ _))⟩
  · have e := hx k le_rfl (fun i => α i.succ)
    obtain ⟨y, hy, hyM⟩ := e
    have e2 := hCh ![α 0] τ hτ y
    obtain ⟨z, hz, hzb⟩ := e2
    refine ⟨z, ?_, ?_⟩
    · have := isDerivX_cons' (hH.1 k (fun i => α i.succ) τ x y hy) hz
      rwa [show (Matrix.vecCons (α 0) fun i => α i.succ) = α from Matrix.cons_head_tail α] at this
    · rw [Nat.cast_one] at hzb
      have p : 0 ≤ τ ^ (-(1 / 2 : ℝ)) := rpow_nonneg hτ.le _
      have hy0 : ‖y‖ ≤ max M 0 := hyM.trans (le_max_left _ _)
      have h1 : Ch * (τ ^ (-(1 / 2 : ℝ)) * ‖y‖) ≤ |Ch| * (τ ^ (-(1 / 2 : ℝ)) * ‖y‖) :=
        mul_le_mul_of_nonneg_right (le_abs_self Ch) (mul_nonneg p (norm_nonneg y))
      have h2 : |Ch| * τ ^ (-(1 / 2 : ℝ)) * ‖y‖ ≤ |Ch| * τ ^ (-(1 / 2 : ℝ)) * max M 0 :=
        mul_le_mul_of_nonneg_left hy0 (mul_nonneg (abs_nonneg _) p)
      linarith

theorem integral_deriv (hA : DerivAlgebra) (hQ : DiffQuotient) (hI : DerivIntegral)
    {F : ℝ → X} {a t : ℝ} (hat : a < t) (hFc : ContinuousOn F (Ioo a t))
    (hFi : IntervalIntegrable F volume a t) {m : ℕ} (α : Fin m → Fin 3) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a t)
    (hex : ∀ s ∈ Ioo a t, ∀ l ≤ m, ∀ β : Fin l → Fin 3, ∃ w, IsDerivX β (F s) w)
    (hb : ∀ s ∈ Ioo a t, ∀ w, IsDerivX α (F s) w → ‖w‖ ≤ g s) :
    ∃ y, IsDerivX α (∫ s in a..t, F s) y ∧ ‖y‖ ≤ ∫ s in a..t, g s := by
  classical
  let G : ℝ → X := fun s => if h : ∃ w, IsDerivX α (F s) w then h.choose else 0
  have hGd : ∀ s ∈ Ioo a t, IsDerivX α (F s) (G s) := by
    intro s hs
    have h1 : ∃ w, IsDerivX α (F s) w := hex s hs m le_rfl α
    simp only [G, dif_pos h1]
    exact h1.choose_spec
  have hGm : AEStronglyMeasurable G (volume.restrict (Ioo a t)) :=
    aestronglyMeasurable_deriv hA hQ m F (hFc.aestronglyMeasurable measurableSet_Ioo)
      ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun s hs => hex s hs))
      α G ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun s hs => hGd s hs))
  have hGi : IntervalIntegrable G volume a t := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hat.le]
    refine Integrable.mono' ((intervalIntegrable_iff_integrableOn_Ioo_of_le hat.le).1 hg) hGm ?_
    exact (ae_restrict_iff' measurableSet_Ioo).2
      (Eventually.of_forall fun s hs => hb s hs _ (hGd s hs))
  refine ⟨∫ s in a..t, G s, hI m α F G a t hat.le hFi hGi hGd, ?_⟩
  refine intervalIntegral.norm_integral_le_of_norm_le hat.le ?_ hg
  have hne : ∀ᵐ s ∂volume, s ≠ t := by
    rw [ae_iff]
    simp
  filter_upwards [hne] with s hs hs'
  have hs2 : s ∈ Ioo a t := ⟨hs'.1, lt_of_le_of_ne hs'.2 hs⟩
  exact hb s hs2 _ (hGd s hs2)

theorem bilin_pointwise (hA : DerivAlgebra) (hL : BilinLeibniz) {Cb : ℝ} (hCb0 : 0 ≤ Cb)
    (hCb : ∀ τ, 0 < τ → ∀ u v : X, ‖bilinX τ u v‖ ≤ Cb * τ ^ (-(3 / 4 : ℝ)) * ‖u‖ * ‖v‖)
    {k : ℕ} {B : ℝ} (hB : 0 ≤ B) {q : X} {a s t : ℝ} (has : a < s) (hst : s < t) (hs1 : s - a ≤ 1)
    (hlow : ∀ m ≤ k, ∀ α : Fin m → Fin 3, ∃ y, IsDerivX α q y ∧ ‖y‖ ≤ B)
    (htop : ∀ α : Fin (k + 1) → Fin 3, ∃ y, IsDerivX α q y ∧ ‖y‖ ≤ B * (s - a) ^ (-(1 / 2 : ℝ))) :
    ∀ l ≤ k + 1, ∀ β : Fin l → Fin 3, ∃ w, IsDerivX β (bilinX (t - s) q q) w ∧
      ‖w‖ ≤ Cb * (t - s) ^ (-(3 / 4 : ℝ)) * 2 ^ l *
        (B ^ 2 * (if l ≤ k then 1 else (s - a) ^ (-(1 / 2 : ℝ)))) := by
  intro l hl β
  have hsa : 0 < s - a := sub_pos.2 has
  have hone : 1 ≤ (s - a) ^ (-(1 / 2 : ℝ)) :=
    one_le_rpow_of_pos_of_le_one_of_nonpos hsa hs1 (by norm_num)
  have hr0 : 0 ≤ (s - a) ^ (-(1 / 2 : ℝ)) := rpow_nonneg hsa.le _
  have hc : ∀ i j, i + j ≤ l → ∀ (β : Fin i → Fin 3) (γ : Fin j → Fin 3),
      ∃ y z, IsDerivX β q y ∧ IsDerivX γ q z ∧
        ‖y‖ * ‖z‖ ≤ B ^ 2 * (if i + j ≤ k then 1 else (s - a) ^ (-(1 / 2 : ℝ))) := by
    intro i j hij β γ
    by_cases hi : i ≤ k
    · by_cases hj : j ≤ k
      · have e1 := hlow i hi β
        have e2 := hlow j hj γ
        obtain ⟨y, hy, hyb⟩ := e1
        obtain ⟨z, hz, hzb⟩ := e2
        refine ⟨y, z, hy, hz, ?_⟩
        have hm := mul_le_mul hyb hzb (norm_nonneg _) hB
        have hge : B ^ 2 ≤ B ^ 2 * (if i + j ≤ k then 1 else (s - a) ^ (-(1 / 2 : ℝ))) := by
          split_ifs
          · simp
          · exact le_mul_of_one_le_right (sq_nonneg B) hone
        nlinarith [hm, hge]
      · obtain rfl : j = k + 1 := by omega
        obtain rfl : i = 0 := by omega
        have e1 := hlow 0 (Nat.zero_le _) β
        have e2 := htop γ
        obtain ⟨y, hy, hyb⟩ := e1
        obtain ⟨z, hz, hzb⟩ := e2
        refine ⟨y, z, hy, hz, ?_⟩
        have hif : ¬ (0 + (k + 1) ≤ k) := by omega
        rw [if_neg hif]
        have hm := mul_le_mul hyb hzb (norm_nonneg _) hB
        nlinarith [hm]
    · obtain rfl : i = k + 1 := by omega
      obtain rfl : j = 0 := by omega
      have e1 := htop β
      have e2 := hlow 0 (Nat.zero_le _) γ
      obtain ⟨y, hy, hyb⟩ := e1
      obtain ⟨z, hz, hzb⟩ := e2
      refine ⟨y, z, hy, hz, ?_⟩
      have hif : ¬ (k + 1 + 0 ≤ k) := by omega
      rw [if_neg hif]
      have hm := mul_le_mul hyb hzb (norm_nonneg _) (mul_nonneg hB hr0)
      nlinarith [hm]
  have e := bilin_deriv_bound hA hL hCb0 (sub_pos.2 hst) (hCb _ (sub_pos.2 hst)) l q q
    (fun i => B ^ 2 * (if i ≤ k then 1 else (s - a) ^ (-(1 / 2 : ℝ)))) hc β
  exact e

theorem duhamel_low (hA : DerivAlgebra) (hQ : DiffQuotient) (hI : DerivIntegral)
    {Cb : ℝ} (hCb0 : 0 ≤ Cb) {k : ℕ} {B : ℝ} {F : ℝ → X} {a t : ℝ} (hat : a < t)
    (hFc : ContinuousOn F (Ioo a t)) (hFi : IntervalIntegrable F volume a t)
    (hder : ∀ s ∈ Ioo a t, ∀ l ≤ k + 1, ∀ β : Fin l → Fin 3, ∃ w, IsDerivX β (F s) w ∧
      ‖w‖ ≤ Cb * (t - s) ^ (-(3 / 4 : ℝ)) * 2 ^ l *
        (B ^ 2 * (if l ≤ k then 1 else (s - a) ^ (-(1 / 2 : ℝ))))) :
    ∀ m ≤ k, ∀ α : Fin m → Fin 3, ∃ y, IsDerivX α (∫ s in a..t, F s) y ∧
      ‖y‖ ≤ ∫ s in a..t, Cb * 2 ^ (k + 1) * B ^ 2 * (t - s) ^ (-(3 / 4 : ℝ)) := by
  intro m hm α
  have hg := (intervalIntegrable_rpow_sub_left (a := a) (t := t) (r := -(3 / 4 : ℝ))
    (by norm_num)).const_mul (Cb * 2 ^ (k + 1) * B ^ 2)
  refine integral_deriv hA hQ hI hat hFc hFi α hg ?_ ?_
  · intro s hs l hl β
    have e := hder s hs l (by omega) β
    obtain ⟨w, hw, -⟩ := e
    exact ⟨w, hw⟩
  · intro s hs w hw
    have e1 := hder s hs m (by omega) α
    obtain ⟨w', hw', hb'⟩ := e1
    have hww : w = w' := hA.1 m α _ w w' hw hw'
    subst hww
    rw [if_pos hm, mul_one] at hb'
    have hq : 0 ≤ (t - s) ^ (-(3 / 4 : ℝ)) := rpow_nonneg (sub_pos.2 hs.2).le _
    have h2 : (2 : ℝ) ^ m ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 := mul_le_mul_of_nonneg_left h2
      (mul_nonneg (mul_nonneg hCb0 hq) (sq_nonneg B))
    nlinarith [h3]

theorem duhamel_top (hA : DerivAlgebra) (hQ : DiffQuotient) (hI : DerivIntegral)
    {Cb : ℝ} (hCb0 : 0 ≤ Cb) {k : ℕ} {B : ℝ} {F : ℝ → X} {a t : ℝ} (hat : a < t)
    (hFc : ContinuousOn F (Ioo a t)) (hFi : IntervalIntegrable F volume a t)
    (hder : ∀ s ∈ Ioo a t, ∀ l ≤ k + 1, ∀ β : Fin l → Fin 3, ∃ w, IsDerivX β (F s) w ∧
      ‖w‖ ≤ Cb * (t - s) ^ (-(3 / 4 : ℝ)) * 2 ^ l *
        (B ^ 2 * (if l ≤ k then 1 else (s - a) ^ (-(1 / 2 : ℝ))))) :
    ∀ α : Fin (k + 1) → Fin 3, ∃ y, IsDerivX α (∫ s in a..t, F s) y ∧
      ‖y‖ ≤ ∫ s in a..t, Cb * 2 ^ (k + 1) * B ^ 2 *
        (2 * (t - a) ^ (-(1 / 2 : ℝ)) * (t - s) ^ (-(3 / 4 : ℝ)) +
          2 * (t - a) ^ (-(3 / 4 : ℝ)) * (s - a) ^ (-(1 / 2 : ℝ))) := by
  intro α
  have hK0 : 0 ≤ Cb * 2 ^ (k + 1) * B ^ 2 := by positivity
  have hg := (((intervalIntegrable_rpow_sub_left (a := a) (t := t) (r := -(3 / 4 : ℝ))
    (by norm_num)).const_mul (2 * (t - a) ^ (-(1 / 2 : ℝ)))).add
    ((intervalIntegrable_rpow_sub_right (a := a) (t := t) (r := -(1 / 2 : ℝ))
    (by norm_num)).const_mul (2 * (t - a) ^ (-(3 / 4 : ℝ))))).const_mul
      (Cb * 2 ^ (k + 1) * B ^ 2)
  refine integral_deriv hA hQ hI hat hFc hFi α hg ?_ ?_
  · intro s hs l hl β
    have e := hder s hs l hl β
    obtain ⟨w, hw, -⟩ := e
    exact ⟨w, hw⟩
  · intro s hs w hw
    have e1 := hder s hs (k + 1) le_rfl α
    obtain ⟨w', hw', hb'⟩ := e1
    have hww : w = w' := hA.1 (k + 1) α _ w w' hw hw'
    subst hww
    have hif : ¬ (k + 1 ≤ k) := by omega
    rw [if_neg hif] at hb'
    have hsp := split_bound hs.1 hs.2
    have h3 := mul_le_mul_of_nonneg_left hsp hK0
    nlinarith [h3, hb']

theorem picard_step (hA : DerivAlgebra) (hH : DerivHeat) (hI : DerivIntegral) (hQ : DiffQuotient)
    (hL : BilinLeibniz) {Cb : ℝ} (hCb0 : 0 ≤ Cb)
    (hCb : ∀ τ, 0 < τ → ∀ u v : X, ‖bilinX τ u v‖ ≤ Cb * τ ^ (-(3 / 4 : ℝ)) * ‖u‖ * ‖v‖)
    {Ch : ℝ} (hCh : ∀ (α : Fin 1 → Fin 3) (t : ℝ), 0 < t → ∀ x : X,
      ∃ y, IsDerivX α (heatX t x) y ∧ ‖y‖ ≤ Ch * t ^ (-(((1 : ℕ) : ℝ) / 2)) * ‖x‖)
    {k : ℕ} {M B ε : ℝ} (hB : 0 ≤ B) (hStrain : max M 0 ≤ B / 2) (hM2 : |Ch| * max M 0 ≤ B / 2)
    (hP : Cb * 2 ^ (k + 1) * B * ε ≤ 1 / 32)
    {x : X} (hx : ∀ m ≤ k, ∀ α : Fin m → Fin 3, ∃ y, IsDerivX α x y ∧ ‖y‖ ≤ M)
    {a t : ℝ} (hat : a < t) (ht1 : t - a ≤ 1) (hroot : (t - a) ^ (1 / 4 : ℝ) ≤ ε) (n : ℕ)
    (ih : ∀ s ∈ Ioo a t,
      (∀ m ≤ k, ∀ α : Fin m → Fin 3, ∃ y, IsDerivX α (fixedPointIter x a n s) y ∧ ‖y‖ ≤ B) ∧
        ∀ α : Fin (k + 1) → Fin 3,
          ∃ y, IsDerivX α (fixedPointIter x a n s) y ∧ ‖y‖ ≤ B * (s - a) ^ (-(1 / 2 : ℝ))) :
    (∀ m ≤ k, ∀ α : Fin m → Fin 3, ∃ y, IsDerivX α (fixedPointIter x a (n + 1) t) y ∧ ‖y‖ ≤ B) ∧
      ∀ α : Fin (k + 1) → Fin 3,
        ∃ y, IsDerivX α (fixedPointIter x a (n + 1) t) y ∧ ‖y‖ ≤ B * (t - a) ^ (-(1 / 2 : ℝ)) := by
  have hτ : 0 < t - a := sub_pos.2 hat
  have hpc : ContinuousOn (fixedPointIter x a n) (Icc a t) :=
    (continuousOn_picardIter x a n).mono Icc_subset_Ici_self
  have hFc : ContinuousOn (fun s => bilinX (t - s) (fixedPointIter x a n s) (fixedPointIter x a n s))
      (Ioo a t) :=
    Freq.Internal.MildOfWeak.bilin_curve_continuousOn bilin_holds.2 bilinCont_holds
      (hpc.mono Ioo_subset_Icc_self) (continuousOn_const.sub continuousOn_id)
      (fun s hs => sub_pos.2 hs.2)
  have hFi : IntervalIntegrable
      (fun s => bilinX (t - s) (fixedPointIter x a n s) (fixedPointIter x a n s)) volume a t :=
    Freq.Internal.MildOfWeak.bilin_intervalIntegrable bilin_holds.2 bilinCont_holds hpc
      (right_mem_Icc.2 hat.le)
  have hder : ∀ s ∈ Ioo a t, ∀ l ≤ k + 1, ∀ β : Fin l → Fin 3, ∃ w,
      IsDerivX β ((fun s => bilinX (t - s) (fixedPointIter x a n s) (fixedPointIter x a n s)) s) w ∧
        ‖w‖ ≤ Cb * (t - s) ^ (-(3 / 4 : ℝ)) * 2 ^ l *
          (B ^ 2 * (if l ≤ k then 1 else (s - a) ^ (-(1 / 2 : ℝ)))) :=
    fun s hs => bilin_pointwise hA hL hCb0 hCb hB hs.1 hs.2 (by linarith [hs.2])
      (ih s hs).1 (ih s hs).2
  have d1 := duhamel_low hA hQ hI hCb0 hat hFc hFi hder
  have d2 := duhamel_top hA hQ hI hCb0 hat hFc hFi hder
  have hI1 : (∫ s in a..t, Cb * 2 ^ (k + 1) * B ^ 2 * (t - s) ^ (-(3 / 4 : ℝ))) =
      Cb * 2 ^ (k + 1) * B ^ 2 * (4 * (t - a) ^ (1 / 4 : ℝ)) := integral_low
  have hI2 : (∫ s in a..t, Cb * 2 ^ (k + 1) * B ^ 2 *
      (2 * (t - a) ^ (-(1 / 2 : ℝ)) * (t - s) ^ (-(3 / 4 : ℝ)) +
        2 * (t - a) ^ (-(3 / 4 : ℝ)) * (s - a) ^ (-(1 / 2 : ℝ)))) =
      Cb * 2 ^ (k + 1) * B ^ 2 * (12 * ((t - a) ^ (1 / 4 : ℝ) * (t - a) ^ (-(1 / 2 : ℝ)))) := by
    rw [intervalIntegral.integral_const_mul, integral_split hat]
  have hh := heat_deriv_bounds hH hτ hCh hx
  have hr0 : 0 ≤ (t - a) ^ (1 / 4 : ℝ) := rpow_nonneg hτ.le _
  have hp : 0 ≤ (t - a) ^ (-(1 / 2 : ℝ)) := rpow_nonneg hτ.le _
  have hK : Cb * 2 ^ (k + 1) * B ^ 2 * (t - a) ^ (1 / 4 : ℝ) ≤ B / 32 := by
    have s1 := mul_le_mul_of_nonneg_left hroot
      (by positivity : (0 : ℝ) ≤ Cb * 2 ^ (k + 1) * B ^ 2)
    have s2 := mul_le_mul_of_nonneg_left hP hB
    have s3 : Cb * 2 ^ (k + 1) * B ^ 2 * ε = B * (Cb * 2 ^ (k + 1) * B * ε) := by ring
    linarith
  have hp1 : fixedPointIter x a (n + 1) t = heatX (t - a) x +
      ∫ s in a..t, bilinX (t - s) (fixedPointIter x a n s) (fixedPointIter x a n s) := rfl
  rw [hp1]
  refine ⟨fun m hm α => ?_, fun α => ?_⟩
  · have f1 := hh.1 m hm α
    have f2 := d1 m hm α
    obtain ⟨y1, hy1, hb1⟩ := f1
    obtain ⟨y2, hy2, hb2⟩ := f2
    refine ⟨y1 + y2, isDerivX_add hy1 hy2, ?_⟩
    rw [hI1] at hb2
    have := norm_add_le y1 y2
    linarith
  · have f1 := hh.2 α
    have f2 := d2 α
    obtain ⟨y1, hy1, hb1⟩ := f1
    obtain ⟨y2, hy2, hb2⟩ := f2
    refine ⟨y1 + y2, isDerivX_add hy1 hy2, ?_⟩
    rw [hI2] at hb2
    have a1 := mul_le_mul_of_nonneg_right hM2 hp
    have a3 := mul_le_mul_of_nonneg_left hK hp
    have a4 := mul_nonneg hB hp
    have := norm_add_le y1 y2
    nlinarith

end Internal.PicardDeriv

open Internal.PicardDeriv in
theorem picardDerivBoundOfCalculus_holds : PicardDerivBoundOfCalculus := by
  intro hA hH hI hQ hL k M
  obtain ⟨Cb, hCb0, hCb⟩ := bilin_holds.2
  obtain ⟨Ch, hCh⟩ := hH.2 1
  have hM' : 0 ≤ max M 0 := le_max_right _ _
  have hChM : 0 ≤ |Ch| * max M 0 := mul_nonneg (abs_nonneg _) hM'
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 2 * ((1 + |Ch|) * max M 0) := ⟨_, rfl⟩
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  have hStrain : max M 0 ≤ B / 2 := by rw [hBdef]; nlinarith
  have hM2 : |Ch| * max M 0 ≤ B / 2 := by rw [hBdef]; nlinarith
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = (1 + Cb * 2 ^ (k + 6) * B)⁻¹ := ⟨_, rfl⟩
  have hL0 : 0 ≤ Cb * 2 ^ (k + 6) * B := by positivity
  have hε0 : 0 < ε := by rw [hεdef]; positivity
  have hε1 : ε ≤ 1 := by rw [hεdef]; exact inv_le_one_of_one_le₀ (by linarith)
  have hLε : Cb * 2 ^ (k + 6) * B * ε ≤ 1 := by
    rw [hεdef, ← div_eq_mul_inv, div_le_one (by linarith)]
    linarith
  have hP : Cb * 2 ^ (k + 1) * B * ε ≤ 1 / 32 := by
    have e : Cb * 2 ^ (k + 6) * B * ε = 32 * (Cb * 2 ^ (k + 1) * B * ε) := by ring
    linarith
  refine ⟨ε ^ 4, B, by positivity, pow_le_one₀ hε0.le hε1, ?_⟩
  intro x a hx n
  induction n with
  | zero =>
    intro t ht
    have hτ : 0 < t - a := sub_pos.2 ht.1
    have e := heat_deriv_bounds hH hτ hCh hx
    obtain ⟨e1, e2⟩ := e
    have hp0 : fixedPointIter x a 0 t = heatX (t - a) x := rfl
    rw [hp0]
    refine ⟨fun m hm α => ?_, fun α => ?_⟩
    · have f := e1 m hm α
      obtain ⟨y, hy, hyb⟩ := f
      exact ⟨y, hy, by linarith⟩
    · have f := e2 α
      obtain ⟨y, hy, hyb⟩ := f
      refine ⟨y, hy, ?_⟩
      have hp : 0 ≤ (t - a) ^ (-(1 / 2 : ℝ)) := rpow_nonneg hτ.le _
      have h1 := mul_le_mul_of_nonneg_right hM2 hp
      have h2 := mul_nonneg hB hp
      nlinarith
  | succ n ih =>
    intro t ht
    have hτ : 0 < t - a := sub_pos.2 ht.1
    have hε4 : ε ^ 4 ≤ 1 := pow_le_one₀ hε0.le hε1
    have ht1 : t - a ≤ 1 := by linarith [ht.2]
    have hroot : (t - a) ^ (1 / 4 : ℝ) ≤ ε := by
      calc (t - a) ^ (1 / 4 : ℝ) ≤ (ε ^ 4) ^ (1 / 4 : ℝ) :=
            rpow_le_rpow hτ.le (by linarith [ht.2]) (by norm_num)
        _ = ε := by
          rw [show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
          exact pow_rpow_inv_natCast hε0.le (by norm_num)
    exact picard_step hA hH hI hQ hL hCb0 hCb hCh hB hStrain hM2 hP hx ht.1 ht1 hroot n
      (fun s hs => ih s ⟨hs.1, by linarith [hs.2, ht.2]⟩)

end Breakdown.FarField
