import Breakdown.FracCell.ResolvedEnergyCore

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace ResolvedEnergyInternal

theorem poly_add {d d' : ℕ} {P T : ℝ × ℝ → ℂ} (hP : P ∈ polyFn d d') (hT : T ∈ polyFn d d') :
    (fun p => P p + T p) ∈ polyFn d d' := by
  obtain ⟨c, hc⟩ := hP
  obtain ⟨e, he⟩ := hT
  refine ⟨fun j l => c j l + e j l, fun p => ?_⟩
  show P p + T p = _
  rw [hc p, he p, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

theorem poly_smul {d d' : ℕ} {P : ℝ × ℝ → ℂ} (a : ℂ) (hP : P ∈ polyFn d d') :
    (fun p => a * P p) ∈ polyFn d d' := by
  obtain ⟨c, hc⟩ := hP
  refine ⟨fun j l => a * c j l, fun p => ?_⟩
  show a * P p = _
  rw [hc p, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

theorem poly_sum {d d' : ℕ} {ι : Type*} (s : Finset ι) {P : ι → ℝ × ℝ → ℂ} (hP : ∀ i ∈ s, P i ∈ polyFn d d') :
    (fun p => ∑ i ∈ s, P i p) ∈ polyFn d d' := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact zero_mem d d'
  | insert i s hi ih =>
    have h1 := poly_add (hP i (Finset.mem_insert_self i s)) (ih (fun k hk => hP k (Finset.mem_insert_of_mem hk)))
    simpa only [Finset.sum_insert hi] using h1

theorem poly_mono {d d' k l : ℕ} (hk : k ≤ d) (hl : l ≤ d') :
    (fun p : ℝ × ℝ => (p.1 : ℂ) ^ k * (p.2 : ℂ) ^ l) ∈ polyFn d d' := by
  classical
  refine ⟨fun j l' => if (j : ℕ) = k ∧ (l' : ℕ) = l then 1 else 0, fun p => ?_⟩
  have hk' : k < d + 1 := by omega
  have hl' : l < d' + 1 := by omega
  rw [Finset.sum_eq_single (⟨k, hk'⟩ : Fin (d + 1)), Finset.sum_eq_single (⟨l, hl'⟩ : Fin (d' + 1))]
  · simp
  · intro b _ hb
    have : (b : ℕ) ≠ l := fun h => hb (Fin.ext h)
    simp [this]
  · simp
  · intro b _ hb
    have : (b : ℕ) ≠ k := fun h => hb (Fin.ext h)
    refine Finset.sum_eq_zero (fun l' _ => ?_)
    simp [this]
  · simp

theorem hpow (n : ℕ) (r : ℝ) : HasDerivAt (fun y : ℝ => (y : ℂ) ^ n) ((n : ℂ) * (r : ℂ) ^ (n - 1)) r :=
  (hasDerivAt_pow n (r : ℂ)).comp_ofReal

def rA (K : CellBox) : ℝ := 2 / (K.r₂ - K.r₁)

def rB (K : CellBox) : ℝ := -(K.r₁ + K.r₂) / (K.r₂ - K.r₁)

theorem refR_lin (K : CellBox) (y : ℝ) : K.refR y = rA K * y + rB K := by
  unfold CellBox.refR rA rB
  ring

def sAx (K : CellBox) : ℕ := if K.r₁ = 0 then 1 else 0

def radialOp (K : CellBox) (j : ℕ) (r : ℝ) : ℂ :=
  ((j * (j - 1 : ℕ) * (1 - rB K ^ 2) : ℝ) : ℂ) * (r : ℂ) ^ (j - 2)
    + ((j * (j + sAx K) * (-2 * rA K * rB K) : ℝ) : ℂ) * (r : ℂ) ^ (j - 1)
    + ((j * (j + 1 + sAx K) * (-(rA K) ^ 2) : ℝ) : ℂ) * (r : ℂ) ^ j

theorem term_deriv (K : CellBox) (hK : IsCellBox K) (j : ℕ) (r : ℝ) :
    HasDerivAt (fun y : ℝ => ((K.lineWeight y * (1 - K.refR y ^ 2) : ℝ) : ℂ) * ((j : ℂ) * (y : ℂ) ^ (j - 1)))
      ((K.lineWeight r : ℂ) * radialOp K j r) r := by
  by_cases hax : K.r₁ = 0
  · have hb : rB K = -1 := by
      simp only [rB, hax, zero_add, sub_zero]
      have : K.r₂ ≠ 0 := by linarith [hK.r_order.2]
      field_simp
    have hW : (fun y : ℝ => ((K.lineWeight y * (1 - K.refR y ^ 2) : ℝ) : ℂ))
        = fun y : ℝ => ((2 * rA K : ℝ) : ℂ) * (y : ℂ) ^ 2 + ((-(rA K) ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 3 := by
      funext y
      rw [refR_lin, hb]
      simp only [CellBox.lineWeight, if_pos hax]
      push_cast
      ring
    have hWr : ((K.lineWeight r * (1 - K.refR r ^ 2) : ℝ) : ℂ)
        = ((2 * rA K : ℝ) : ℂ) * (r : ℂ) ^ 2 + ((-(rA K) ^ 2 : ℝ) : ℂ) * (r : ℂ) ^ 3 := congrFun hW r
    have hd : HasDerivAt (fun y : ℝ => ((K.lineWeight y * (1 - K.refR y ^ 2) : ℝ) : ℂ))
        (((2 * rA K : ℝ) : ℂ) * ((2 : ℕ) * (r : ℂ) ^ (2 - 1))
          + ((-(rA K) ^ 2 : ℝ) : ℂ) * ((3 : ℕ) * (r : ℂ) ^ (3 - 1))) r := by
      rw [hW]
      exact ((hpow 2 r).const_mul _).add ((hpow 3 r).const_mul _)
    have hq := (hpow (j - 1) r).const_mul (j : ℂ)
    have hm := hd.mul hq
    refine hm.congr_deriv ?_
    rw [hWr]
    simp only [radialOp, sAx, if_pos hax, CellBox.lineWeight, hb]
    rcases j with _ | _ | k
    · simp
    · simp; ring
    · push_cast
      have e1 : k + 1 + 1 - 1 = k + 1 := by omega
      have e3 : k + 1 + 1 - 2 = k := by omega
      have e2 : k + 1 - 1 = k := by omega
      try simp only [e1, e2, e3]
      try push_cast
      ring
  · have hW : (fun y : ℝ => ((K.lineWeight y * (1 - K.refR y ^ 2) : ℝ) : ℂ))
        = fun y : ℝ => ((1 - rB K ^ 2 : ℝ) : ℂ) + ((-2 * rA K * rB K : ℝ) : ℂ) * (y : ℂ) ^ 1
          + ((-(rA K) ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2 := by
      funext y
      rw [refR_lin]
      simp only [CellBox.lineWeight, if_neg hax]
      push_cast
      ring
    have hWr : ((K.lineWeight r * (1 - K.refR r ^ 2) : ℝ) : ℂ)
        = ((1 - rB K ^ 2 : ℝ) : ℂ) + ((-2 * rA K * rB K : ℝ) : ℂ) * (r : ℂ) ^ 1
          + ((-(rA K) ^ 2 : ℝ) : ℂ) * (r : ℂ) ^ 2 := congrFun hW r
    have hd : HasDerivAt (fun y : ℝ => ((K.lineWeight y * (1 - K.refR y ^ 2) : ℝ) : ℂ))
        (0 + ((-2 * rA K * rB K : ℝ) : ℂ) * ((1 : ℕ) * (r : ℂ) ^ (1 - 1))
          + ((-(rA K) ^ 2 : ℝ) : ℂ) * ((2 : ℕ) * (r : ℂ) ^ (2 - 1))) r := by
      rw [hW]
      exact ((hasDerivAt_const r _).add ((hpow 1 r).const_mul _)).add ((hpow 2 r).const_mul _)
    have hq := (hpow (j - 1) r).const_mul (j : ℂ)
    have hm := hd.mul hq
    refine hm.congr_deriv ?_
    rw [hWr]
    simp only [radialOp, sAx, if_neg hax, CellBox.lineWeight]
    rcases j with _ | _ | k
    · simp
    · simp; ring
    · push_cast
      have e1 : k + 1 + 1 - 1 = k + 1 := by omega
      have e3 : k + 1 + 1 - 2 = k := by omega
      have e2 : k + 1 - 1 = k := by omega
      try simp only [e1, e2, e3]
      try push_cast
      ring

theorem radialOp_conj (K : CellBox) (j : ℕ) (r : ℝ) : (starRingEnd ℂ) (radialOp K j r) = radialOp K j r := by
  have e : radialOp K j r = (((j * (j - 1 : ℕ) * (1 - rB K ^ 2)) * r ^ (j - 2)
      + (j * (j + sAx K) * (-2 * rA K * rB K)) * r ^ (j - 1)
      + (j * (j + 1 + sAx K) * (-(rA K) ^ 2)) * r ^ j : ℝ) : ℂ) := by
    simp only [radialOp]
    push_cast
    ring
  rw [e, Complex.conj_ofReal]

theorem radialOp_mem (K : CellBox) {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    (fun p : ℝ × ℝ => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), c j l * radialOp K j p.1 * (p.2 : ℂ) ^ (l : ℕ))
      ∈ polyFn Q Q := by
  refine poly_sum _ (fun j _ => poly_sum _ (fun l _ => ?_))
  have hj : (j : ℕ) ≤ Q := Nat.lt_succ_iff.1 j.2
  have hl : (l : ℕ) ≤ Q := Nat.lt_succ_iff.1 l.2
  have e : (fun p : ℝ × ℝ => c j l * radialOp K j p.1 * (p.2 : ℂ) ^ (l : ℕ))
      = fun p => (fun p => (fun p => (c j l * ((j * (j - 1 : ℕ) * (1 - rB K ^ 2) : ℝ) : ℂ)) *
              ((p.1 : ℂ) ^ ((j : ℕ) - 2) * (p.2 : ℂ) ^ (l : ℕ))) p
            + (fun p => (c j l * ((j * (j + sAx K) * (-2 * rA K * rB K) : ℝ) : ℂ)) *
              ((p.1 : ℂ) ^ ((j : ℕ) - 1) * (p.2 : ℂ) ^ (l : ℕ))) p) p
          + (fun p => (c j l * ((j * (j + 1 + sAx K) * (-(rA K) ^ 2) : ℝ) : ℂ)) *
              ((p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ))) p := by
    funext p
    simp only [radialOp]
    ring
  rw [e]
  exact poly_add (poly_add (poly_smul _ (poly_mono (by omega) hl)) (poly_smul _ (poly_mono (by omega) hl)))
    (poly_smul _ (poly_mono hj hl))

theorem weighted_deriv (K : CellBox) (hK : IsCellBox K) {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) (p : ℝ × ℝ) :
    HasDerivAt (fun r : ℝ => ((K.lineWeight r * (1 - K.refR r ^ 2) : ℝ) : ℂ) *
        ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), (starRingEnd ℂ) (c j l) *
          (((j : ℕ) : ℂ) * (r : ℂ) ^ ((j : ℕ) - 1)) * (p.2 : ℂ) ^ (l : ℕ))
      ((K.lineWeight p.1 : ℂ) * (starRingEnd ℂ)
        (∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), c j l * radialOp K j p.1 * (p.2 : ℂ) ^ (l : ℕ))) p.1 := by
  have e : (fun r : ℝ => ((K.lineWeight r * (1 - K.refR r ^ 2) : ℝ) : ℂ) *
        ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), (starRingEnd ℂ) (c j l) *
          (((j : ℕ) : ℂ) * (r : ℂ) ^ ((j : ℕ) - 1)) * (p.2 : ℂ) ^ (l : ℕ))
      = fun r : ℝ => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), ((starRingEnd ℂ) (c j l) * (p.2 : ℂ) ^ (l : ℕ)) *
          (((K.lineWeight r * (1 - K.refR r ^ 2) : ℝ) : ℂ) * (((j : ℕ) : ℂ) * (r : ℂ) ^ ((j : ℕ) - 1))) := by
    funext r
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [e]
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun (j : Fin (Q + 1)) _ => HasDerivAt.fun_sum (u := Finset.univ)
    (fun (l : Fin (Q + 1)) _ => (term_deriv K hK (j : ℕ) p.1).const_mul ((starRingEnd ℂ) (c j l) * (p.2 : ℂ) ^ (l : ℕ))))
  refine hs.congr_deriv ?_
  simp only [map_sum, map_mul, radialOp_conj, map_pow, Complex.conj_ofReal, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

def polyVal {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) (p : ℝ × ℝ) : ℂ :=
  ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), c j l * ((p.1 : ℂ) ^ (j : ℕ)) * ((p.2 : ℂ) ^ (l : ℕ))

def derVal {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) (p : ℝ × ℝ) : ℂ :=
  ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), c j l * (((j : ℕ) : ℂ) * (p.1 : ℂ) ^ ((j : ℕ) - 1)) * ((p.2 : ℂ) ^ (l : ℕ))

def opVal (K : CellBox) {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) (p : ℝ × ℝ) : ℂ :=
  ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), c j l * radialOp K j p.1 * (p.2 : ℂ) ^ (l : ℕ)

def wt (K : CellBox) (r : ℝ) : ℝ := K.lineWeight r * (1 - K.refR r ^ 2)

theorem conj_derVal {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) (p : ℝ × ℝ) :
    (starRingEnd ℂ) (derVal c p) = derVal (fun j l => (starRingEnd ℂ) (c j l)) p := by
  simp [derVal, map_sum, map_mul, Complex.conj_ofReal, map_pow, map_natCast]

theorem polyVal_deriv {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) (r z : ℝ) :
    HasDerivAt (fun y : ℝ => polyVal c (y, z)) (derVal c (r, z)) r := by
  unfold polyVal derVal
  refine HasDerivAt.fun_sum (fun j _ => HasDerivAt.fun_sum (fun l _ => ?_))
  show HasDerivAt (fun y : ℝ => c j l * (y : ℂ) ^ (j : ℕ) * (z : ℂ) ^ (l : ℕ)) _ r
  exact ((hpow (j : ℕ) r).const_mul (c j l)).mul_const _

theorem polyVal_cont {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) : Continuous (polyVal c) := by
  unfold polyVal; fun_prop

theorem derVal_cont {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) : Continuous (derVal c) := by
  unfold derVal; fun_prop

theorem opVal_cont (K : CellBox) {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) : Continuous (opVal K c) := by
  unfold opVal radialOp; fun_prop

theorem wt_cont (K : CellBox) : Continuous (wt K) := by
  unfold wt; exact (lw_cont K).mul (continuous_const.sub ((refR_cont K).pow 2))

theorem wt_left (K : CellBox) (hK : IsCellBox K) : wt K K.r₁ = 0 := by
  have : K.r₂ - K.r₁ ≠ 0 := by linarith [hK.r_order.2]
  unfold wt CellBox.refR
  rw [show 2 * K.r₁ - K.r₁ - K.r₂ = -(K.r₂ - K.r₁) by ring, neg_div, div_self this]
  ring

theorem wt_right (K : CellBox) (hK : IsCellBox K) : wt K K.r₂ = 0 := by
  have : K.r₂ - K.r₁ ≠ 0 := by linarith [hK.r_order.2]
  unfold wt CellBox.refR
  rw [show 2 * K.r₂ - K.r₁ - K.r₂ = K.r₂ - K.r₁ by ring, div_self this]
  ring

theorem rect_iterated (K : CellBox) (f : ℝ × ℝ → ℂ) (hf : Continuous f) :
    ∫ p in K.rect, f p = ∫ z in Set.Icc K.z₁ K.z₂, ∫ r in Set.Icc K.r₁ K.r₂, f (r, z) := by
  have hi : IntegrableOn f (Set.Icc K.r₁ K.r₂ ×ˢ Set.Icc K.z₁ K.z₂) (volume.prod volume) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  unfold CellBox.rect
  rw [Measure.volume_eq_prod, setIntegral_prod f hi]
  refine integral_integral_swap ?_
  rw [Measure.prod_restrict]
  exact hi

theorem interval_zero (K : CellBox) (hK : IsCellBox K) (g g' : ℝ → ℂ) (hg : ∀ r, HasDerivAt g (g' r) r)
    (hc : Continuous g') (h1 : g K.r₁ = 0) (h2 : g K.r₂ = 0) : ∫ r in Set.Icc K.r₁ K.r₂, g' r = 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hK.r_order.2.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hg r) (hc.intervalIntegrable _ _), h1, h2, sub_zero]

def partsFn (K : CellBox) {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) (p : ℝ × ℝ) : ℂ :=
  (K.lineWeight p.1 : ℂ) * (starRingEnd ℂ) (opVal K c p) * polyVal c p
    + ((wt K p.1 : ℝ) : ℂ) * derVal (fun j l => (starRingEnd ℂ) (c j l)) p * derVal c p

theorem partsFn_cont (K : CellBox) {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) : Continuous (partsFn K c) := by
  unfold partsFn
  have h1 : Continuous (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ)) :=
    Complex.continuous_ofReal.comp ((lw_cont K).comp continuous_fst)
  have h2 : Continuous (fun p : ℝ × ℝ => ((wt K p.1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((wt_cont K).comp continuous_fst)
  exact ((h1.mul (Complex.continuous_conj.comp (opVal_cont K c))).mul (polyVal_cont c)).add
    ((h2.mul (derVal_cont _)).mul (derVal_cont c))

theorem poly_parts (K : CellBox) (hK : IsCellBox K) {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    ∫ p in K.rect, partsFn K c p = 0 := by
  rw [rect_iterated K _ (partsFn_cont K c)]
  have hz : ∀ z : ℝ, ∫ r in Set.Icc K.r₁ K.r₂, partsFn K c (r, z) = 0 := by
    intro z
    refine interval_zero K hK (fun r => ((wt K r : ℝ) : ℂ) * derVal (fun j l => (starRingEnd ℂ) (c j l)) (r, z)
        * polyVal c (r, z)) (fun r => partsFn K c (r, z)) (fun r => ?_)
      ((partsFn_cont K c).comp (continuous_id.prodMk continuous_const)) ?_ ?_
    · exact (weighted_deriv K hK c (r, z)).mul (polyVal_deriv c r z)
    · simp [wt_left K hK]
    · simp [wt_right K hK]
  simp only [hz, integral_zero]

theorem lw_nonneg (K : CellBox) (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) : 0 ≤ K.lineWeight p.1 := by
  unfold CellBox.lineWeight
  split_ifs
  · exact fst_nonneg K hK hp
  · exact zero_le_one

theorem lw_int (K : CellBox) (hK : IsCellBox K) {g : ℝ × ℝ → ℂ} (hg : AEStronglyMeasurable g (volume.restrict K.rect))
    (hgi : IntegrableOn (fun p => p.1 * ‖g p‖ ^ 2) K.rect) :
    IntegrableOn (fun p => K.lineWeight p.1 * ‖g p‖ ^ 2) K.rect := by
  have hiR := iR_pos K hK
  refine mono_int K ((wcont K ((lw_cont K).comp continuous_fst)).mul (hg.norm.pow 2)) (hgi.const_mul K.innerRadius⁻¹)
    (fun p hp => ⟨mul_nonneg (lw_nonneg K hK hp) (sq_nonneg _), ?_⟩)
  have h1 : K.lineWeight p.1 ≤ K.innerRadius⁻¹ * p.1 := by
    rw [le_inv_mul_iff₀ hiR]
    unfold CellBox.innerRadius CellBox.lineWeight
    split_ifs
    · linarith
    · linarith [hp.1.1]
  calc K.lineWeight p.1 * ‖g p‖ ^ 2 ≤ (K.innerRadius⁻¹ * p.1) * ‖g p‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = K.innerRadius⁻¹ * (p.1 * ‖g p‖ ^ 2) := by ring

theorem refR_left (K : CellBox) (hK : IsCellBox K) : 1 - K.refR K.r₁ ^ 2 = 0 := by
  have : K.r₂ - K.r₁ ≠ 0 := by linarith [hK.r_order.2]
  unfold CellBox.refR
  rw [show 2 * K.r₁ - K.r₁ - K.r₂ = -(K.r₂ - K.r₁) by ring, neg_div, div_self this]
  ring

theorem refR_right (K : CellBox) (hK : IsCellBox K) : 1 - K.refR K.r₂ ^ 2 = 0 := by
  have : K.r₂ - K.r₁ ≠ 0 := by linarith [hK.r_order.2]
  unfold CellBox.refR
  rw [show 2 * K.r₂ - K.r₁ - K.r₂ = K.r₂ - K.r₁ by ring, div_self this]
  ring

theorem derVal_smooth {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) : ContDiff ℝ 1 (derVal c) := by
  unfold derVal
  have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => (p.1 : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => (p.2 : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_snd
  refine ContDiff.sum (fun j _ => ContDiff.sum (fun l _ => ?_))
  exact (contDiff_const.mul (contDiff_const.mul (h1.pow _))).mul (h2.pow _)

def zA (K : CellBox) : ℝ := 2 / (K.z₂ - K.z₁)

def zB (K : CellBox) : ℝ := -(K.z₁ + K.z₂) / (K.z₂ - K.z₁)

theorem refZ_lin (K : CellBox) (y : ℝ) : K.refZ y = zA K * y + zB K := by
  unfold CellBox.refZ zA zB
  ring

def heightOp (K : CellBox) (l : ℕ) (z : ℝ) : ℂ :=
  ((l * (l - 1 : ℕ) * (1 - zB K ^ 2) : ℝ) : ℂ) * (z : ℂ) ^ (l - 2)
    + ((l * l * (-2 * zA K * zB K) : ℝ) : ℂ) * (z : ℂ) ^ (l - 1)
    + ((l * (l + 1) * (-(zA K) ^ 2) : ℝ) : ℂ) * (z : ℂ) ^ l

theorem heightOp_conj (K : CellBox) (l : ℕ) (z : ℝ) : (starRingEnd ℂ) (heightOp K l z) = heightOp K l z := by
  have e : heightOp K l z = (((l * (l - 1 : ℕ) * (1 - zB K ^ 2)) * z ^ (l - 2)
      + (l * l * (-2 * zA K * zB K)) * z ^ (l - 1)
      + (l * (l + 1) * (-(zA K) ^ 2)) * z ^ l : ℝ) : ℂ) := by
    simp only [heightOp]
    push_cast
    ring
  rw [e, Complex.conj_ofReal]

theorem hterm_deriv (K : CellBox) (l : ℕ) (z : ℝ) :
    HasDerivAt (fun y : ℝ => ((1 - K.refZ y ^ 2 : ℝ) : ℂ) * ((l : ℂ) * (y : ℂ) ^ (l - 1))) (heightOp K l z) z := by
  have hW : (fun y : ℝ => ((1 - K.refZ y ^ 2 : ℝ) : ℂ))
      = fun y : ℝ => ((1 - zB K ^ 2 : ℝ) : ℂ) + ((-2 * zA K * zB K : ℝ) : ℂ) * (y : ℂ) ^ 1
        + ((-(zA K) ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2 := by
    funext y
    rw [refZ_lin]
    push_cast
    ring
  have hWr : ((1 - K.refZ z ^ 2 : ℝ) : ℂ)
      = ((1 - zB K ^ 2 : ℝ) : ℂ) + ((-2 * zA K * zB K : ℝ) : ℂ) * (z : ℂ) ^ 1
        + ((-(zA K) ^ 2 : ℝ) : ℂ) * (z : ℂ) ^ 2 := congrFun hW z
  have hd : HasDerivAt (fun y : ℝ => ((1 - K.refZ y ^ 2 : ℝ) : ℂ))
      (0 + ((-2 * zA K * zB K : ℝ) : ℂ) * ((1 : ℕ) * (z : ℂ) ^ (1 - 1))
        + ((-(zA K) ^ 2 : ℝ) : ℂ) * ((2 : ℕ) * (z : ℂ) ^ (2 - 1))) z := by
    rw [hW]
    exact ((hasDerivAt_const z _).add ((hpow 1 z).const_mul _)).add ((hpow 2 z).const_mul _)
  have hq := (hpow (l - 1) z).const_mul (l : ℂ)
  have hm := hd.mul hq
  refine hm.congr_deriv ?_
  rw [hWr]
  simp only [heightOp]
  rcases l with _ | _ | k
  · simp
  · simp; ring
  · push_cast
    have e1 : k + 1 + 1 - 1 = k + 1 := by omega
    have e3 : k + 1 + 1 - 2 = k := by omega
    have e2 : k + 1 - 1 = k := by omega
    try simp only [e1, e2, e3]
    try push_cast
    ring

def hOpVal (K : CellBox) {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) (p : ℝ × ℝ) : ℂ :=
  ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), c j l * (p.1 : ℂ) ^ (j : ℕ) * heightOp K l p.2

def hderVal {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) (p : ℝ × ℝ) : ℂ :=
  ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), c j l * ((p.1 : ℂ) ^ (j : ℕ)) * (((l : ℕ) : ℂ) * (p.2 : ℂ) ^ ((l : ℕ) - 1))

theorem heightOp_mem (K : CellBox) {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) : hOpVal K c ∈ polyFn Q Q := by
  refine poly_sum _ (fun j _ => poly_sum _ (fun l _ => ?_))
  have hj : (j : ℕ) ≤ Q := Nat.lt_succ_iff.1 j.2
  have hl : (l : ℕ) ≤ Q := Nat.lt_succ_iff.1 l.2
  have e : (fun p : ℝ × ℝ => c j l * (p.1 : ℂ) ^ (j : ℕ) * heightOp K l p.2)
      = fun p => (fun p => (fun p => (c j l * ((l * (l - 1 : ℕ) * (1 - zB K ^ 2) : ℝ) : ℂ)) *
              ((p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ ((l : ℕ) - 2))) p
            + (fun p => (c j l * ((l * l * (-2 * zA K * zB K) : ℝ) : ℂ)) *
              ((p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ ((l : ℕ) - 1))) p) p
          + (fun p => (c j l * ((l * (l + 1) * (-(zA K) ^ 2) : ℝ) : ℂ)) *
              ((p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ))) p := by
    funext p
    simp only [heightOp]
    ring
  rw [e]
  exact poly_add (poly_add (poly_smul _ (poly_mono hj (by omega))) (poly_smul _ (poly_mono hj (by omega))))
    (poly_smul _ (poly_mono hj hl))

theorem hweighted_deriv (K : CellBox) {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) (p : ℝ × ℝ) :
    HasDerivAt (fun z : ℝ => ((1 - K.refZ z ^ 2 : ℝ) : ℂ) * hderVal (fun j l => (starRingEnd ℂ) (c j l)) (p.1, z))
      ((starRingEnd ℂ) (hOpVal K c p)) p.2 := by
  have e : (fun z : ℝ => ((1 - K.refZ z ^ 2 : ℝ) : ℂ) * hderVal (fun j l => (starRingEnd ℂ) (c j l)) (p.1, z))
      = fun z : ℝ => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), ((starRingEnd ℂ) (c j l) * (p.1 : ℂ) ^ (j : ℕ)) *
          (((1 - K.refZ z ^ 2 : ℝ) : ℂ) * (((l : ℕ) : ℂ) * (z : ℂ) ^ ((l : ℕ) - 1))) := by
    funext z
    simp only [hderVal]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [e]
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun (j : Fin (Q + 1)) _ => HasDerivAt.fun_sum (u := Finset.univ)
    (fun (l : Fin (Q + 1)) _ => (hterm_deriv K (l : ℕ) p.2).const_mul ((starRingEnd ℂ) (c j l) * (p.1 : ℂ) ^ (j : ℕ))))
  refine hs.congr_deriv ?_
  simp only [hOpVal, map_sum, map_mul, heightOp_conj, map_pow, Complex.conj_ofReal]

theorem conj_hderVal {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) (p : ℝ × ℝ) :
    (starRingEnd ℂ) (hderVal c p) = hderVal (fun j l => (starRingEnd ℂ) (c j l)) p := by
  simp [hderVal, map_sum, map_mul, Complex.conj_ofReal, map_pow, map_natCast]

theorem hpolyVal_deriv {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) (r z : ℝ) :
    HasDerivAt (fun y : ℝ => polyVal c (r, y)) (hderVal c (r, z)) z := by
  unfold polyVal hderVal
  refine HasDerivAt.fun_sum (fun j _ => HasDerivAt.fun_sum (fun l _ => ?_))
  show HasDerivAt (fun y : ℝ => c j l * (r : ℂ) ^ (j : ℕ) * (y : ℂ) ^ (l : ℕ)) _ z
  exact (hpow (l : ℕ) z).const_mul _

theorem hderVal_cont {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) : Continuous (hderVal c) := by
  unfold hderVal; fun_prop

theorem hOpVal_cont (K : CellBox) {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) : Continuous (hOpVal K c) := by
  unfold hOpVal heightOp; fun_prop

theorem hderVal_smooth {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) : ContDiff ℝ 1 (hderVal c) := by
  unfold hderVal
  have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => (p.1 : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => (p.2 : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_snd
  refine ContDiff.sum (fun j _ => ContDiff.sum (fun l _ => ?_))
  exact (contDiff_const.mul (h1.pow _)).mul (contDiff_const.mul (h2.pow _))

def hpartsFn (K : CellBox) {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) (p : ℝ × ℝ) : ℂ :=
  (K.lineWeight p.1 : ℂ) * ((starRingEnd ℂ) (hOpVal K c p) * polyVal c p
    + ((1 - K.refZ p.2 ^ 2 : ℝ) : ℂ) * hderVal (fun j l => (starRingEnd ℂ) (c j l)) p * hderVal c p)

theorem hpartsFn_cont (K : CellBox) {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) : Continuous (hpartsFn K c) := by
  unfold hpartsFn
  have h1 : Continuous (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ)) :=
    Complex.continuous_ofReal.comp ((lw_cont K).comp continuous_fst)
  have h2 : Continuous (fun p : ℝ × ℝ => ((1 - K.refZ p.2 ^ 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.sub (((refZ_cont K).comp continuous_snd).pow 2))
  exact h1.mul (((Complex.continuous_conj.comp (hOpVal_cont K c)).mul (polyVal_cont c)).add
    ((h2.mul (hderVal_cont _)).mul (hderVal_cont c)))

theorem refZ_left (K : CellBox) (hK : IsCellBox K) : 1 - K.refZ K.z₁ ^ 2 = 0 := by
  have : K.z₂ - K.z₁ ≠ 0 := by linarith [hK.z_order.2]
  unfold CellBox.refZ
  rw [show 2 * K.z₁ - K.z₁ - K.z₂ = -(K.z₂ - K.z₁) by ring, neg_div, div_self this]
  ring

theorem refZ_right (K : CellBox) (hK : IsCellBox K) : 1 - K.refZ K.z₂ ^ 2 = 0 := by
  have : K.z₂ - K.z₁ ≠ 0 := by linarith [hK.z_order.2]
  unfold CellBox.refZ
  rw [show 2 * K.z₂ - K.z₁ - K.z₂ = K.z₂ - K.z₁ by ring, div_self this]
  ring

theorem hpoly_parts (K : CellBox) (hK : IsCellBox K) {Q : ℕ} (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    ∫ p in K.rect, hpartsFn K c p = 0 := by
  have hi : IntegrableOn (hpartsFn K c) (Set.Icc K.r₁ K.r₂ ×ˢ Set.Icc K.z₁ K.z₂) (volume.prod volume) :=
    (hpartsFn_cont K c).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  unfold CellBox.rect
  rw [Measure.volume_eq_prod, setIntegral_prod _ hi]
  have hr : ∀ r : ℝ, ∫ z in Set.Icc K.z₁ K.z₂, hpartsFn K c (r, z) = 0 := by
    intro r
    have hg : ∀ z, HasDerivAt (fun y => (K.lineWeight r : ℂ) * (((1 - K.refZ y ^ 2 : ℝ) : ℂ) *
        hderVal (fun j l => (starRingEnd ℂ) (c j l)) (r, y) * polyVal c (r, y))) (hpartsFn K c (r, z)) z := by
      intro z
      have h := ((hweighted_deriv K c (r, z)).mul (hpolyVal_deriv c r z)).const_mul (K.lineWeight r : ℂ)
      refine h.congr_deriv ?_
      simp only [hpartsFn]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hK.z_order.2.le,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hg z)
        (((hpartsFn_cont K c).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)]
    simp [refZ_left K hK, refZ_right K hK]
  simp only [hr, integral_zero]

end ResolvedEnergyInternal

open ResolvedEnergyInternal in
theorem radialCross : RadialCrossStatement := by
  intro K hK Q F Fr hF hFr hFi hFri hrp
  by_cases hex : ∃ P ∈ polyFn Q Q, ∀ T ∈ polyFn Q Q, K.pairOn K.lineWeightFn (fun p => F p - P p) T = 0
  swap
  · have e : K.proj Q Q F = 0 := by unfold CellBox.proj; rw [dif_neg hex]
    rw [e]
    simp [CellBox.radialDeriv, CellBox.pairOn]
  have eP : K.proj Q Q F = hex.choose := by unfold CellBox.proj; rw [dif_pos hex]
  obtain ⟨hPmem, horth⟩ := hex.choose_spec
  obtain ⟨c, hc⟩ := hPmem
  have hPv : hex.choose = polyVal c := funext hc
  rw [hPv] at horth
  rw [eP, hPv]
  have hD : CellBox.radialDeriv (polyVal c) = derVal c := funext (fun p => (polyVal_deriv c p.1 p.2).deriv)
  rw [hD]
  set c' : Fin (Q + 1) → Fin (Q + 1) → ℂ := fun j l => (starRingEnd ℂ) (c j l) with hc'
  set ψ : ℝ × ℝ → ℂ := fun p => ((1 - K.refR p.1 ^ 2 : ℝ) : ℂ) * derVal c' p with hψ
  have hr : ContDiff ℝ 1 (fun p : ℝ × ℝ => 1 - K.refR p.1 ^ 2) := by
    have e : (fun p : ℝ × ℝ => 1 - K.refR p.1 ^ 2) = fun p => 1 - (rA K * p.1 + rB K) ^ 2 :=
      funext (fun p => by rw [refR_lin])
    rw [e]
    exact contDiff_const.sub (((contDiff_const.mul contDiff_fst).add contDiff_const).pow 2)
  have hψc : ContDiff ℝ 1 ψ := (Complex.ofRealCLM.contDiff.comp hr).mul (derVal_smooth c')
  have hψ1 : ∀ z, ψ (K.r₁, z) = 0 := fun z => by simp only [hψ, refR_left K hK, Complex.ofReal_zero, zero_mul]
  have hψ2 : ∀ z, ψ (K.r₂, z) = 0 := fun z => by simp only [hψ, refR_right K hK, Complex.ofReal_zero, zero_mul]
  have hIBP := hrp ψ hψc hψ1 hψ2
  have hder : ∀ p : ℝ × ℝ, CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p
      = (K.lineWeight p.1 : ℂ) * (starRingEnd ℂ) (opVal K c p) := by
    intro p
    have e : (fun r : ℝ => (K.lineWeight (r, p.2).1 : ℂ) * ψ (r, p.2))
        = fun r : ℝ => ((K.lineWeight r * (1 - K.refR r ^ 2) : ℝ) : ℂ) *
          ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), (starRingEnd ℂ) (c j l) *
            (((j : ℕ) : ℂ) * (r : ℂ) ^ ((j : ℕ) - 1)) * (p.2 : ℂ) ^ (l : ℕ) := by
      funext r
      simp only [hψ, derVal, hc']
      push_cast
      ring
    unfold CellBox.radialDeriv
    rw [e]
    exact (weighted_deriv K hK c p).deriv
  simp only [hder] at hIBP
  have hlwm : AEStronglyMeasurable (fun p : ℝ × ℝ => K.lineWeight p.1) (volume.restrict K.rect) :=
    wcont K ((lw_cont K).comp continuous_fst)
  have hlw0 : ∀ p ∈ K.rect, 0 ≤ K.lineWeight p.1 := fun p hp => lw_nonneg K hK hp
  have hψcont : Continuous ψ := hψc.continuous
  have I1 : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * Fr p * ψ p) K.rect := by
    have h := cross_integrable K hlw0 hlwm hFr (P := fun p => (starRingEnd ℂ) (ψ p))
      (Complex.continuous_conj.comp hψcont).aestronglyMeasurable (lw_int K hK hFr hFri)
      (cont_integrable K ((lw_cont K).comp continuous_fst).continuousOn (Complex.continuous_conj.comp hψcont)).2
    simpa only [Complex.conj_conj] using h
  have I2 : IntegrableOn (fun p => ((wt K p.1 : ℝ) : ℂ) * derVal c' p * derVal c p) K.rect :=
    (((Complex.continuous_ofReal.comp ((wt_cont K).comp continuous_fst)).mul (derVal_cont c')).mul
      (derVal_cont c)).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have I3 : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p * (starRingEnd ℂ) (opVal K c p)) K.rect :=
    cross_integrable K hlw0 hlwm hF (opVal_cont K c).aestronglyMeasurable hFi
      (cont_integrable K ((lw_cont K).comp continuous_fst).continuousOn (opVal_cont K c)).2
  have I4 : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * (starRingEnd ℂ) (opVal K c p) * polyVal c p) K.rect :=
    (((Complex.continuous_ofReal.comp ((lw_cont K).comp continuous_fst)).mul
      (Complex.continuous_conj.comp (opVal_cont K c))).mul (polyVal_cont c)).continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)
  have E1 : K.pairOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2)) (fun p => Fr p - derVal c p) (derVal c)
      = (∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fr p * ψ p)
        - ∫ p in K.rect, ((wt K p.1 : ℝ) : ℂ) * derVal c' p * derVal c p := by
    rw [← integral_sub I1 I2]
    unfold CellBox.pairOn
    refine setIntegral_congr_fun (rect_meas K) (fun p _ => ?_)
    simp only [hψ, wt, conj_derVal, hc']
    push_cast
    ring
  have E2 := poly_parts K hK c
  unfold partsFn at E2
  rw [integral_add I4 I2] at E2
  have E4 : K.pairOn K.lineWeightFn (fun p => F p - polyVal c p) (opVal K c)
      = (∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p * (starRingEnd ℂ) (opVal K c p))
        - ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * (starRingEnd ℂ) (opVal K c p) * polyVal c p := by
    rw [← integral_sub I3 I4]
    unfold CellBox.pairOn CellBox.lineWeightFn
    refine setIntegral_congr_fun (rect_meas K) (fun p _ => ?_)
    ring
  have E5 := horth (opVal K c) (radialOp_mem K c)
  have E6 : ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fr p * ψ p
      = -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p * (starRingEnd ℂ) (opVal K c p) := by
    rw [hIBP]
    congr 1
    refine integral_congr_ae (ae_of_all _ (fun p => ?_))
    ring
  rw [E1, E6]
  linear_combination (-1 : ℂ) * E4.symm.trans E5 - E2

open ResolvedEnergyInternal in
theorem heightCross : HeightCrossStatement := by
  intro K hK Q F Fz hF hFz hFi hFzi hzp
  by_cases hex : ∃ P ∈ polyFn Q Q, ∀ T ∈ polyFn Q Q, K.pairOn K.lineWeightFn (fun p => F p - P p) T = 0
  swap
  · have e : K.proj Q Q F = 0 := by unfold CellBox.proj; rw [dif_neg hex]
    rw [e]
    simp [CellBox.heightDeriv, CellBox.pairOn]
  have eP : K.proj Q Q F = hex.choose := by unfold CellBox.proj; rw [dif_pos hex]
  obtain ⟨hPmem, horth⟩ := hex.choose_spec
  obtain ⟨c, hc⟩ := hPmem
  have hPv : hex.choose = polyVal c := funext hc
  rw [hPv] at horth
  rw [eP, hPv]
  have hD : CellBox.heightDeriv (polyVal c) = hderVal c := funext (fun p => (hpolyVal_deriv c p.1 p.2).deriv)
  rw [hD]
  set c' : Fin (Q + 1) → Fin (Q + 1) → ℂ := fun j l => (starRingEnd ℂ) (c j l) with hc'
  set ψ : ℝ × ℝ → ℂ := fun p => ((1 - K.refZ p.2 ^ 2 : ℝ) : ℂ) * hderVal c' p with hψ
  have hr : ContDiff ℝ 1 (fun p : ℝ × ℝ => 1 - K.refZ p.2 ^ 2) := by
    have e : (fun p : ℝ × ℝ => 1 - K.refZ p.2 ^ 2) = fun p => 1 - (zA K * p.2 + zB K) ^ 2 :=
      funext (fun p => by rw [refZ_lin])
    rw [e]
    exact contDiff_const.sub (((contDiff_const.mul contDiff_snd).add contDiff_const).pow 2)
  have hψc : ContDiff ℝ 1 ψ := (Complex.ofRealCLM.contDiff.comp hr).mul (hderVal_smooth c')
  have hψ1 : ∀ r, ψ (r, K.z₁) = 0 := fun r => by simp only [hψ, refZ_left K hK, Complex.ofReal_zero, zero_mul]
  have hψ2 : ∀ r, ψ (r, K.z₂) = 0 := fun r => by simp only [hψ, refZ_right K hK, Complex.ofReal_zero, zero_mul]
  have hIBP := hzp ψ hψc hψ1 hψ2
  have hder : ∀ p : ℝ × ℝ, CellBox.heightDeriv ψ p = (starRingEnd ℂ) (hOpVal K c p) := by
    intro p
    unfold CellBox.heightDeriv
    exact (hweighted_deriv K c p).deriv
  simp only [hder] at hIBP
  have hlwm : AEStronglyMeasurable (fun p : ℝ × ℝ => K.lineWeight p.1) (volume.restrict K.rect) :=
    wcont K ((lw_cont K).comp continuous_fst)
  have hlw0 : ∀ p ∈ K.rect, 0 ≤ K.lineWeight p.1 := fun p hp => lw_nonneg K hK hp
  have hψcont : Continuous ψ := hψc.continuous
  have hlwc : Continuous (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ)) :=
    Complex.continuous_ofReal.comp ((lw_cont K).comp continuous_fst)
  have I1 : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * Fz p * ψ p) K.rect := by
    have h := cross_integrable K hlw0 hlwm hFz (P := fun p => (starRingEnd ℂ) (ψ p))
      (Complex.continuous_conj.comp hψcont).aestronglyMeasurable (lw_int K hK hFz hFzi)
      (cont_integrable K ((lw_cont K).comp continuous_fst).continuousOn (Complex.continuous_conj.comp hψcont)).2
    simpa only [Complex.conj_conj] using h
  have hyc : Continuous (fun p : ℝ × ℝ => ((1 - K.refZ p.2 ^ 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.sub (((refZ_cont K).comp continuous_snd).pow 2))
  have I2 : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) *
      (((1 - K.refZ p.2 ^ 2 : ℝ) : ℂ) * hderVal c' p * hderVal c p)) K.rect :=
    (hlwc.mul ((hyc.mul (hderVal_cont c')).mul (hderVal_cont c))).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have I3 : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p * (starRingEnd ℂ) (hOpVal K c p)) K.rect :=
    cross_integrable K hlw0 hlwm hF (hOpVal_cont K c).aestronglyMeasurable hFi
      (cont_integrable K ((lw_cont K).comp continuous_fst).continuousOn (hOpVal_cont K c)).2
  have I4 : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * ((starRingEnd ℂ) (hOpVal K c p) * polyVal c p)) K.rect :=
    (hlwc.mul ((Complex.continuous_conj.comp (hOpVal_cont K c)).mul (polyVal_cont c))).continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)
  have E1 : K.pairOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2)) (fun p => Fz p - hderVal c p) (hderVal c)
      = (∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fz p * ψ p)
        - ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * (((1 - K.refZ p.2 ^ 2 : ℝ) : ℂ) * hderVal c' p * hderVal c p) := by
    rw [← integral_sub I1 I2]
    unfold CellBox.pairOn
    refine setIntegral_congr_fun (rect_meas K) (fun p _ => ?_)
    simp only [hψ, conj_hderVal, hc']
    push_cast
    ring
  have E2 := hpoly_parts K hK c
  have E2' : ∫ p in K.rect, hpartsFn K c p
      = (∫ p in K.rect, (K.lineWeight p.1 : ℂ) * ((starRingEnd ℂ) (hOpVal K c p) * polyVal c p))
        + ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * (((1 - K.refZ p.2 ^ 2 : ℝ) : ℂ) * hderVal c' p * hderVal c p) := by
    rw [← integral_add I4 I2]
    refine integral_congr_ae (ae_of_all _ (fun p => ?_))
    simp only [hpartsFn, hc']
    ring
  rw [E2'] at E2
  have E4 : K.pairOn K.lineWeightFn (fun p => F p - polyVal c p) (hOpVal K c)
      = (∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p * (starRingEnd ℂ) (hOpVal K c p))
        - ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * ((starRingEnd ℂ) (hOpVal K c p) * polyVal c p) := by
    rw [← integral_sub I3 I4]
    unfold CellBox.pairOn CellBox.lineWeightFn
    refine setIntegral_congr_fun (rect_meas K) (fun p _ => ?_)
    ring
  have E5 := horth (hOpVal K c) (heightOp_mem K c)
  have E6 : ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fz p * ψ p
      = -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p * (starRingEnd ℂ) (hOpVal K c p) := hIBP
  rw [E1, E6]
  linear_combination (-1 : ℂ) * E4.symm.trans E5 - E2

end CellAnalysis

end CellCert

end Breakdown
