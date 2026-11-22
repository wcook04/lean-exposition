module

public import QuarticQuery.ForrelationLower.Promise
public import QuarticQuery.ForrelationLower.Amplify

/-!
# The Forrelation lower bound

Blueprint lemmas M2, M3. `bansalSinhaLower` discharges the hypothesis `BansalSinhaLower`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open MeasureTheory Finset QuarticQuery.Forrelation

namespace QuarticQuery.ForrelationLower

variable {l t : ℕ}

local notation "Nm" t => Fin (mValue t)

/-- `δ = 2^(-5k)`. -/
noncomputable def dl (k : ℕ) : ℝ := ((2 : ℝ) ^ (5 * k))⁻¹

/-- Support for blueprint M2–M3. -/
theorem denom_pos (k t : ℕ) : 0 < forrelationDenominator k t := by
  unfold forrelationDenominator; positivity

/-- Support for blueprint M2–M3. -/
theorem P_yes {z : BC l (Nm t) → Bool} (h : dl (l + 1) ≤ PhiF t z) :
    P (l + 1) t z = some true := by
  rw [← Phi_eq_PhiF] at h
  have hM : (0 : ℝ) < (forrelationDenominator (l + 1) t : ℝ) := by
    exact_mod_cast denom_pos _ _
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (5 * (l + 1)) := by positivity
  unfold Phi dl at h
  rw [le_div_iff₀ hM, inv_mul_le_iff₀ h2] at h
  have : forrelationDenominator (l + 1) t ≤
      (2 : ℤ) ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t z := by
    exact_mod_cast h
  simp only [P]
  rw [if_pos this]

/-- Support for blueprint M2–M3. -/
theorem P_no {z : BC l (Nm t) → Bool} (h : |PhiF t z| ≤ dl (l + 1) / 2) :
    P (l + 1) t z = some false := by
  rw [← Phi_eq_PhiF] at h
  have hM : (0 : ℝ) < (forrelationDenominator (l + 1) t : ℝ) := by
    exact_mod_cast denom_pos _ _
  have hMi := denom_pos (l + 1) t
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (5 * (l + 1)) := by positivity
  unfold Phi dl at h
  rw [abs_div, abs_of_pos hM, div_le_iff₀ hM] at h
  have hN : ((2 : ℝ) ^ (5 * (l + 1) + 1)) * |(forrelationNumerator (l + 1) t z : ℝ)| ≤
      (forrelationDenominator (l + 1) t : ℝ) := by
    have e : (2 : ℝ) ^ (5 * (l + 1) + 1) = 2 * (2 : ℝ) ^ (5 * (l + 1)) := by ring
    rw [e]
    have : ((2 : ℝ) ^ (5 * (l + 1)))⁻¹ / 2 * (forrelationDenominator (l + 1) t : ℝ) * 2 *
        (2 : ℝ) ^ (5 * (l + 1)) = (forrelationDenominator (l + 1) t : ℝ) := by
      field_simp
    nlinarith [abs_nonneg (forrelationNumerator (l + 1) t z : ℝ)]
  have hNi : (2 : ℤ) ^ (5 * (l + 1) + 1) * |forrelationNumerator (l + 1) t z| ≤
      forrelationDenominator (l + 1) t := by
    exact_mod_cast hN
  have hnot : ¬ (2 : ℤ) ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t z ≥
      forrelationDenominator (l + 1) t := by
    intro hge
    have h1 := le_abs_self (forrelationNumerator (l + 1) t z)
    have hp : (0 : ℤ) < (2 : ℤ) ^ (5 * (l + 1)) := by positivity
    have : (2 : ℤ) ^ (5 * (l + 1) + 1) = 2 * (2 : ℤ) ^ (5 * (l + 1)) := by ring
    rw [this] at hNi
    nlinarith [abs_nonneg (forrelationNumerator (l + 1) t z)]
  simp only [P]
  rw [if_neg hnot, if_pos hNi]

/-- The core: a family of bounded trees cannot beat the gap. -/
theorem not_RLe_of_gap_sharp (hl : 0 < l) {L τ : ℕ} {Λ K A : ℝ} (hK : 0 < K)
    (hKsq : K ^ 2 = 2 * (2 * τ * L + 1 : ℕ) * 2 ^ 2 * Λ)
    (hA : ((3 / 16 : ℝ) * ((2 : ℝ) ^ t)⁻¹) ^ l * (K ^ (l + 1) +
        (Fintype.card (BC l (Nm t)) * 2) ^ (l + 1) *
        ((4 * Fintype.card (BC l (Nm t)) : ℝ) ^ (l + 1) * Real.exp (-Λ))) ≤ A)
    (hε1 : (8 / 9 : ℝ) ^ τ ≤ 1)
    (hgap : (8 / 9 : ℝ) ^ τ + 4 / dl (l + 1) ^ 2 * ((2 : ℝ) ^ (2 * t))⁻¹ + A <
      (1 - (8 / 9 : ℝ) ^ τ) * ((1 / 18 : ℝ) ^ l - dl (l + 1))) :
    ¬ RLe (P (l + 1) t) L := by
  intro h
  obtain ⟨J, _, q, T, hq0, hq1, hdepth, herr⟩ := exists_amplified h τ
  classical
  set ε : ℝ := (8 / 9 : ℝ) ^ τ with hε
  have hε0 : 0 ≤ ε := by positivity
  set δ := dl (l + 1) with hδ
  have hδ0 : 0 < δ := by simp only [hδ, dl]; positivity
  let v : Bool → ℝ := fun b => if b then 1 else 0
  have hv : ∀ b, |v b| ≤ 1 := by
    intro b
    cases b
    · show |((if (false : Bool) = true then 1 else 0 : ℝ))| ≤ 1
      norm_num
    · show |((if (true : Bool) = true then 1 else 0 : ℝ))| ≤ 1
      norm_num
  let G : J → (BC l (Nm t) → Bool) → ℝ := fun j z => v ((T j).eval z)
  let a : (BC l (Nm t) → Bool) → ℝ := fun z => ∑ j, q j * G j z
  have hG : ∀ j z, 0 ≤ G j z ∧ G j z ≤ 1 := fun j z => by
    simp only [G, v]; split_ifs <;> norm_num
  have ha0 : ∀ z, 0 ≤ a z := fun z => sum_nonneg fun j _ => mul_nonneg (hq0 j) (hG j z).1
  have ha1 : ∀ z, a z ≤ 1 := fun z => by
    rw [← hq1]
    exact sum_le_sum fun j _ => mul_le_of_le_one_right (hq0 j) (hG j z).2
  have hyes : ∀ z, P (l + 1) t z = some true → 1 - ε ≤ a z := by
    intro z hz
    have h1 := herr z true hz
    have e : a z + ∑ j, q j * (if (T j).eval z = true then 0 else 1) = 1 := by
      rw [← sum_add_distrib]
      refine (sum_congr rfl fun j _ => ?_).trans hq1
      simp only [G, v]
      cases (T j).eval z <;> simp
    linarith
  have hno : ∀ z, P (l + 1) t z = some false → a z ≤ ε := by
    intro z hz
    have h1 := herr z false hz
    refine le_trans (le_of_eq ?_) h1
    refine sum_congr rfl fun j _ => ?_
    simp only [G, v]
    cases (T j).eval z <;> simp
  have hPhi1 : ∀ z : BC l (Nm t) → Bool, |PhiF t z| ≤ 1 := fun z => by
    rw [← Phi_eq_PhiF]
    exact abs_Phi_le_one (l + 1) t (by omega) z
  -- the two pointwise comparisons
  have hup : ∀ z, a z ≤ ε + 4 / δ ^ 2 * PhiF t z ^ 2 := by
    intro z
    by_cases hz : |PhiF t z| ≤ δ / 2
    · have := hno z (P_no hz)
      have : 0 ≤ 4 / δ ^ 2 * PhiF t z ^ 2 := by positivity
      linarith
    · have h2 : (δ / 2) ^ 2 < PhiF t z ^ 2 := by
        have := sq_lt_sq' (by linarith [abs_nonneg (PhiF t z), not_le.mp hz]) (not_le.mp hz)
        rwa [sq_abs] at this
      have h3 : 1 ≤ 4 / δ ^ 2 * PhiF t z ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith
      linarith [ha1 z]
  have hlow : ∀ z, (1 - ε) * (PhiF t z - δ) ≤ a z := by
    intro z
    have hle1 : PhiF t z - δ ≤ 1 := by linarith [(abs_le.mp (hPhi1 z)).2]
    have h1e : 0 ≤ 1 - ε := by linarith
    by_cases hz : δ ≤ PhiF t z
    · have := hyes z (P_yes hz)
      nlinarith
    · have : PhiF t z - δ ≤ 0 := by linarith [not_le.mp hz]
      nlinarith [ha0 z]
  have hμ1 : ∀ (u : PC l (Nm t) → ℝ) (c : BC l (Nm t)), |wv (H t) 1 u c| ≤ 1 := fun u c => abs_wv_le (H t) (by simp) u c
  have hμ0 : ∀ c : BC l (Nm t), |(0 : BC l (Nm t) → ℝ) c| ≤ 1 := fun c => by simp
  have hbcP := bcf_ext (H t) (PhiF t : (BC l (Nm t) → Bool) → ℝ) (s := 1) (by simp)
  have hbcG : ∀ j, BCf fun u : PC l (Nm t) → ℝ => ext (G j) (wv (H t) 1 u) :=
    fun j => bcf_ext (H t) (G j) (by simp)
  have hexta : ∀ μ, ext a μ = ∑ j, q j * ext (G j) μ := fun μ => by
    simp only [a]
    rw [ext_sum]
    exact sum_congr rfl fun j _ => ext_smul _ _ _
  -- lower bound on the hard distribution
  have hE1 : (1 - ε) * (∫ u, ext (PhiF t) (wv (H t) 1 u) ∂(gP (PC l (Nm t))) - δ) ≤
      ∑ j, q j * ∫ u, ext (G j) (wv (H t) 1 u) ∂(gP (PC l (Nm t))) := by
    have hint : ∫ u : PC l (Nm t) → ℝ, (1 - ε) * (ext (PhiF t) (wv (H t) 1 u) - δ)
        ∂(gP (PC l (Nm t))) ≤ ∫ u, ∑ j, q j * ext (G j) (wv (H t) 1 u) ∂(gP (PC l (Nm t))) := by
      refine integral_mono ((hbcP.integrable.sub (integrable_const δ)).const_mul _)
        (integrable_finsetSum _ fun j _ => (hbcG j).integrable.const_mul _) fun u => ?_
      have h1 := ext_mono hlow (hμ1 u)
      have h2 : ext (fun z => (1 - ε) * (PhiF t z - δ)) (wv (H t) 1 u) =
          (1 - ε) * (ext (PhiF t) (wv (H t) 1 u) - δ) := by
        rw [ext_smul]
        congr 1
        have : (fun z : BC l (Nm t) → Bool => PhiF t z - δ) =
            fun z => PhiF t z + (fun _ => -δ) z := by
          funext z; ring
        rw [this, ext_add, ext_const]
        ring
      rw [h2, hexta] at h1
      exact h1
    rw [integral_const_mul, integral_sub hbcP.integrable (integrable_const δ),
      integral_finsetSum _ fun j _ => (hbcG j).integrable.const_mul _] at hint
    simp only [integral_const_mul] at hint
    simpa using hint
  -- upper bound on the uniform measure
  have hE0 : ∑ j, q j * ext (G j) 0 ≤ ε + 4 / δ ^ 2 * ((2 : ℝ) ^ (2 * t))⁻¹ := by
    rw [← hexta]
    have h1 := ext_mono hup hμ0
    have h2 : ext (fun z => ε + 4 / δ ^ 2 * PhiF t z ^ 2) (0 : BC l (Nm t) → ℝ) =
        ε + 4 / δ ^ 2 * ((2 : ℝ) ^ (2 * t))⁻¹ := by
      have e := ext_add (fun _ => ε) (fun z => 4 / δ ^ 2 * PhiF t z ^ 2) (0 : BC l (Nm t) → ℝ)
      rw [e, ext_const, ext_smul, ext_PhiF_sq]
    rwa [h2] at h1
  -- the advantage of each tree
  have hadv : ∀ j, ∫ u, ext (G j) (wv (H t) 1 u) ∂(gP (PC l (Nm t))) ≤ ext (G j) 0 + A := by
    intro j
    have hcard : 1 ≤ Fintype.card (BC l (Nm t)) := by
      have hne : Nonempty (BC l (Nm t)) := ⟨(0, ⟨0, by simp [mValue]⟩)⟩
      exact Fintype.card_pos
    have := advantage_le_sharp (H t) hl (rowsOrth_H t) (ε := ((2 : ℝ) ^ t)⁻¹) (by positivity) abs_H_le
      (d := 2 * τ * L + 1) (Nat.succ_pos _) hK hKsq hcard (T j) ((hdepth j).trans (Nat.le_succ _))
      v hv
    have h2 := (abs_le.mp (this.trans hA)).2
    simp only [G]
    linarith
  have hmass := mass_ge (t := t) hl
  rw [ext_PhiF_zero, sub_zero] at hmass
  have hfin : ∑ j, q j * ∫ u, ext (G j) (wv (H t) 1 u) ∂(gP (PC l (Nm t))) ≤
      ∑ j, q j * ext (G j) 0 + A := by
    calc _ ≤ ∑ j, q j * (ext (G j) 0 + A) :=
          sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hadv j) (hq0 j)
      _ = _ := by rw [sum_congr rfl fun j _ => mul_add _ _ _, sum_add_distrib, ← sum_mul, hq1,
            one_mul]
  have h1e : 0 ≤ 1 - ε := by linarith
  have hE2 := mul_le_mul_of_nonneg_left (sub_le_sub_right hmass δ) h1e
  linarith


/-- The coarse finite contradiction, retained with its original coefficient. -/
theorem not_RLe_of_gap (hl : 0 < l) {L τ : ℕ} {Λ K A : ℝ} (hK : 0 < K)
    (hKsq : K ^ 2 = 2 * (2 * τ * L + 1 : ℕ) * 2 ^ 2 * Λ)
    (hA : ((3 : ℝ) * ((2 : ℝ) ^ t)⁻¹) ^ l * (K ^ (l + 1) +
        (Fintype.card (BC l (Nm t)) * 2) ^ (l + 1) *
        ((4 * Fintype.card (BC l (Nm t)) : ℝ) ^ (l + 1) * Real.exp (-Λ))) ≤ A)
    (hε1 : (8 / 9 : ℝ) ^ τ ≤ 1)
    (hgap : (8 / 9 : ℝ) ^ τ + 4 / dl (l + 1) ^ 2 * ((2 : ℝ) ^ (2 * t))⁻¹ + A <
      (1 - (8 / 9 : ℝ) ^ τ) * ((1 / 18 : ℝ) ^ l - dl (l + 1))) :
    ¬ RLe (P (l + 1) t) L := by
  apply not_RLe_of_gap_sharp hl hK hKsq _ hε1 hgap
  refine le_trans ?_ hA
  have hinv : (0 : ℝ) ≤ ((2 : ℝ) ^ t)⁻¹ := by positivity
  have hcoeff : (3 / 16 : ℝ) * ((2 : ℝ) ^ t)⁻¹ ≤ 3 * ((2 : ℝ) ^ t)⁻¹ := by
    linarith
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hcoeff l) (by positivity)

/-! ## M2. Parameters -/

/-- Support for blueprint M2–M3. -/
theorem logb_mValue (t : ℕ) : Real.logb 2 (mValue t : ℝ) = 2 * t := by
  have : (mValue t : ℝ) = (2 : ℝ) ^ (2 * t) := by simp [mValue]
  rw [this, Real.logb_pow]
  simp

/-- Support for blueprint M2–M3. -/
theorem four_sq_le_two_pow {t : ℕ} (ht : 8 ≤ t) : (4 * t ^ 2 : ℝ) ≤ (2 : ℝ) ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
    have ht' : (8 : ℝ) ≤ t := by exact_mod_cast ht
    have e : (2 : ℝ) ^ (t + 1) = 2 * 2 ^ t := by ring
    rw [e]
    push_cast
    nlinarith

/-- `X = m^(1-1/k)/(2t)²`, with `X^k = m^l/(2t)^(2k)` and `X ≥ 1` for large `t`. -/
theorem Xk_facts (hl : 0 < l) {t : ℕ} (ht : 8 ≤ t) :
    let X := Real.rpow (mValue t : ℝ) (1 - 1 / ((l + 1 : ℕ) : ℝ)) / (2 * t : ℝ) ^ 2
    1 ≤ X ∧ X ^ (l + 1) = ((2 : ℝ) ^ (2 * t)) ^ l / ((2 * t : ℝ) ^ 2) ^ (l + 1) ∧
      (Lvalue (l + 1) t : ℝ) ≤ X := by
  intro X
  have hm : (mValue t : ℝ) = (2 : ℝ) ^ (2 * t) := by simp [mValue]
  have hm1 : (1 : ℝ) ≤ (mValue t : ℝ) := by rw [hm]; exact one_le_pow₀ (by norm_num)
  have ht0 : (0 : ℝ) < t := by
    have : (8 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have hd : (0 : ℝ) < (2 * t : ℝ) ^ 2 := by positivity
  have hk : ((l + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hexp : (1 / 2 : ℝ) ≤ 1 - 1 / ((l + 1 : ℕ) : ℝ) := by
    have : 1 / ((l + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
      push_cast
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (2 : ℝ) ^ t ≤ Real.rpow (mValue t : ℝ) (1 - 1 / ((l + 1 : ℕ) : ℝ)) := by
      have h2 : ((mValue t : ℝ)) ^ (1 / 2 : ℝ) = (2 : ℝ) ^ t := by
        rw [hm, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        rw [← Real.rpow_natCast]
        congr 1
        push_cast
        ring
      rw [← h2]
      exact Real.rpow_le_rpow_of_exponent_le hm1 hexp
    have h3 := four_sq_le_two_pow ht
    show 1 ≤ _ / _
    rw [le_div_iff₀ hd]
    nlinarith
  · simp only [X]
    rw [div_pow]
    congr 1
    show (((mValue t : ℝ) ^ (1 - 1 / ((l + 1 : ℕ) : ℝ)))) ^ (l + 1) = _
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← hm, ← Real.rpow_natCast]
    congr 1
    field_simp
    push_cast
    ring
  · unfold Lvalue
    rw [logb_mValue]
    exact Nat.floor_le (by
      have : 0 ≤ Real.rpow (mValue t : ℝ) (1 - 1 / ((l + 1 : ℕ) : ℝ)) :=
        Real.rpow_nonneg (by positivity) _
      positivity)

/-- The numeric heart of M2. -/
theorem core_bound {l k t : ℕ} (hk : k = l + 1) (hl : 0 < l) {δ η c₃ S K X : ℝ} (hδ : 0 < δ)
    (ht0 : (0 : ℝ) < t) (hη0 : 0 < η) (hS0 : 0 < S) (hKsq : K ^ 2 = S) (hK0 : 0 < K) (hX0 : 0 < X)
    (hSle : S ≤ c₃ * X * t) (hc₃0 : 0 ≤ c₃)
    (hXk : X ^ k = ((2 : ℝ) ^ (2 * t)) ^ l / ((2 * (t : ℝ)) ^ 2) ^ k)
    (hrη : c₃ / t ≤ η) (hη1 : η ≤ 1) (hη2 : 4 * 9 ^ l * η ≤ δ ^ 2) :
    3 ^ l * ((2 : ℝ) ^ t)⁻¹ ^ l * K ^ k ≤ δ / 2 := by
  have hSk : S ^ k ≤ (c₃ / t) ^ k * ((2 : ℝ) ^ (2 * t)) ^ l := by
    calc S ^ k ≤ (c₃ * X * t) ^ k := pow_le_pow_left₀ hS0.le hSle k
      _ = c₃ ^ k * X ^ k * t ^ k := by rw [mul_pow, mul_pow]
      _ = c₃ ^ k * (((2 : ℝ) ^ (2 * t)) ^ l / ((2 * (t : ℝ)) ^ 2) ^ k) * t ^ k := by rw [hXk]
      _ ≤ c₃ ^ k * (((2 : ℝ) ^ (2 * t)) ^ l / ((t : ℝ) ^ 2) ^ k) * t ^ k := by
          have h : (t : ℝ) ^ 2 ≤ (2 * (t : ℝ)) ^ 2 := by nlinarith
          gcongr
      _ = _ := by
          have e : ((t : ℝ) ^ 2) ^ k = t ^ k * t ^ k := by rw [← pow_add, ← pow_mul, two_mul]
          have ht : (t : ℝ) ^ k ≠ 0 := by positivity
          rw [e, div_pow]
          field_simp
  obtain ⟨r, hr⟩ : ∃ r, r = c₃ / (t : ℝ) := ⟨_, rfl⟩
  rw [← hr] at hSk hrη
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := hrη.trans hη1
  have hrk : r ^ k ≤ r := by
    calc r ^ k ≤ r ^ 1 := pow_le_pow_of_le_one hr0 hr1 (by omega)
      _ = r := pow_one r
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = ((2 : ℝ) ^ t)⁻¹ ^ l := ⟨_, rfl⟩
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hw2 : w ^ 2 * ((2 : ℝ) ^ (2 * t)) ^ l = 1 := by
    have e : (2 : ℝ) ^ (2 * t) = ((2 : ℝ) ^ t) ^ 2 := by rw [mul_comm, pow_mul]
    rw [hw, e, ← pow_mul, ← pow_mul, mul_comm 2 l, pow_mul, pow_mul]
    rw [← mul_pow, inv_pow, inv_mul_cancel₀ (by positivity), one_pow]
  rw [← hw]
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 3 ^ l * w * K ^ k := ⟨_, rfl⟩
  rw [← hp]
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hpsq : p ^ 2 ≤ (δ / 2) ^ 2 := by
    have e : p ^ 2 = 9 ^ l * (w ^ 2 * S ^ k) := by
      have h9 : (9 : ℝ) ^ l = (3 ^ l) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      have hKk : (K ^ k) ^ 2 = S ^ k := by rw [← pow_mul, mul_comm, pow_mul, hKsq]
      rw [hp, h9, ← hKk]
      ring
    rw [e]
    have h1 : w ^ 2 * S ^ k ≤ r ^ k := by
      calc w ^ 2 * S ^ k ≤ w ^ 2 * (r ^ k * ((2 : ℝ) ^ (2 * t)) ^ l) :=
            mul_le_mul_of_nonneg_left hSk (by positivity)
        _ = r ^ k * (w ^ 2 * ((2 : ℝ) ^ (2 * t)) ^ l) := by ring
        _ = r ^ k := by rw [hw2, mul_one]
    have h9 : (0 : ℝ) < 9 ^ l := by positivity
    have h2 : (9 : ℝ) ^ l * r ≤ 9 ^ l * η := mul_le_mul_of_nonneg_left hrη h9.le
    have h3 : (9 : ℝ) ^ l * (w ^ 2 * S ^ k) ≤ 9 ^ l * r :=
      mul_le_mul_of_nonneg_left (h1.trans hrk) h9.le
    nlinarith
  exact (sq_le_sq₀ hp0 (by positivity)).mp hpsq

set_option maxHeartbeats 1000000 in
/-- M2. The advantage bound vanishes at the Forrelation depth. -/
theorem exists_threshold (hl : 0 < l) (τ : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∃ Λ K : ℝ, 0 < K ∧
      K ^ 2 = 2 * (2 * τ * Lvalue (l + 1) t + 1 : ℕ) * 2 ^ 2 * Λ ∧
      ((3 : ℝ) * ((2 : ℝ) ^ t)⁻¹) ^ l * (K ^ (l + 1) +
        (Fintype.card (BC l (Fin (mValue t))) * 2) ^ (l + 1) *
        ((4 * Fintype.card (BC l (Fin (mValue t))) : ℝ) ^ (l + 1) * Real.exp (-Λ))) ≤ δ ∧
      4 / δ ^ 2 * ((2 : ℝ) ^ (2 * t))⁻¹ ≤ δ := by
  set c₁ : ℝ := Real.log (4 * (l + 1 : ℕ)) with hc₁
  have hc₁0 : 0 ≤ c₁ := Real.log_nonneg (by
    have : (0 : ℝ) ≤ l := by positivity
    push_cast
    linarith)
  set c₂ : ℝ := 2 * (l + 1 : ℕ) * (c₁ + 2) with hc₂
  set c₃ : ℝ := 8 * (2 * τ + 1) * c₂ with hc₃
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hc₃0 : 0 ≤ c₃ := by positivity
  set η : ℝ := min 1 (δ ^ 2 / (4 * 9 ^ l)) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  refine ⟨max 8 (max ⌈c₃ / η⌉₊ (max ⌈2 * 3 ^ l / δ⌉₊ ⌈4 / δ ^ 3⌉₊)), fun t ht => ?_⟩
  have ht8 : 8 ≤ t := (le_max_left _ _).trans ht
  have ht1 : ⌈c₃ / η⌉₊ ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have ht2 : ⌈2 * 3 ^ l / δ⌉₊ ≤ t :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
  have ht3 : ⌈4 / δ ^ 3⌉₊ ≤ t :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
  have htr : (8 : ℝ) ≤ t := by exact_mod_cast ht8
  have ht0 : (0 : ℝ) < t := by linarith
  have ht1r : c₃ / η ≤ t := (Nat.le_ceil _).trans (by exact_mod_cast ht1)
  have ht2r : 2 * 3 ^ l / δ ≤ t := (Nat.le_ceil _).trans (by exact_mod_cast ht2)
  have ht3r : 4 / δ ^ 3 ≤ t := (Nat.le_ceil _).trans (by exact_mod_cast ht3)
  have h2t : (t : ℝ) ≤ (2 : ℝ) ^ t := by
    exact_mod_cast (Nat.lt_two_pow_self (n := t)).le
  have h2t2 : (t : ℝ) ≤ (2 : ℝ) ^ (2 * t) := h2t.trans
    (pow_le_pow_right₀ (by norm_num) (by omega))
  have hcard : ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ) =
      (l + 1 : ℕ) * (2 : ℝ) ^ (2 * t) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    simp [mValue]
  generalize ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ) = cd at hcard ⊢
  have h2p : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * t) := one_le_pow₀ (by norm_num)
  have hl1 : (1 : ℝ) ≤ (l + 1 : ℕ) := by push_cast; linarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
  have hcd1 : 1 ≤ cd := by rw [hcard]; nlinarith
  obtain ⟨hX1, hXk, hLX⟩ := Xk_facts (l := l) hl ht8
  generalize Real.rpow (mValue t : ℝ) (1 - 1 / ((l + 1 : ℕ) : ℝ)) / (2 * t : ℝ) ^ 2 = X at hX1 hXk hLX
  generalize Lvalue (l + 1) t = L at hLX ⊢
  obtain ⟨k, hk⟩ : ∃ k, k = l + 1 := ⟨_, rfl⟩
  rw [← hk] at hXk ⊢
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = 4 * cd := ⟨_, rfl⟩
  have hY1 : 1 < Y := by rw [hY]; linarith
  have hY0 : 0 < Y := by linarith
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = ((2 * k : ℕ) : ℝ) * Real.log Y := ⟨_, rfl⟩
  have hlogY : 0 < Real.log Y := Real.log_pos hY1
  have hΛ0 : 0 < Λ := by
    have : (0 : ℝ) < ((2 * k : ℕ) : ℝ) := by
      have : 0 < 2 * k := by omega
      exact_mod_cast this
    rw [hΛ]; positivity
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = 2 * τ * L + 1 := ⟨_, rfl⟩
  rw [← hd]
  have hd0 : (0 : ℝ) < d := by
    have : 0 < d := by omega
    exact_mod_cast this
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = 2 * d * 2 ^ 2 * Λ := ⟨_, rfl⟩
  have hS0 : 0 < S := by rw [hS]; positivity
  have hK0 : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS0
  have hKsq : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS0.le
  refine ⟨Λ, Real.sqrt S, hK0, hKsq.trans hS, ?_, ?_⟩
  · have hexp : Real.exp Λ = Y ^ (2 * k) := by
      rw [hΛ, Real.exp_nat_mul, Real.exp_log hY0]
    have hE : Y ^ k * (Y ^ k * Real.exp (-Λ)) = 1 := by
      rw [Real.exp_neg, hexp, ← mul_assoc, ← pow_add, ← two_mul]
      exact mul_inv_cancel₀ (by positivity)
    have hterm : (cd * 2) ^ k * (Y ^ k * Real.exp (-Λ)) ≤ 1 := by
      rw [← hE]
      refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ k) (by positivity)
      rw [hY]
      linarith
    have hX0 : 0 < X := by linarith
    have hdX : (d : ℝ) ≤ (2 * τ + 1) * X := by
      have : (d : ℝ) = 2 * τ * L + 1 := by rw [hd]; push_cast; ring
      rw [this]
      have hτ : (0 : ℝ) ≤ 2 * τ := by positivity
      have h1 := mul_le_mul_of_nonneg_left hLX hτ
      have e : (2 * (τ : ℝ) + 1) * X = 2 * τ * X + X := by ring
      rw [e]
      linarith
    have hlogle : Real.log Y ≤ (c₁ + 2) * t := by
      have e : Y = (4 * (l + 1 : ℕ)) * (2 : ℝ) ^ (2 * t) := by
        rw [hY, hcard]; ring
      rw [e, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_two_lt_d9
        linarith
      have ht1' : (1 : ℝ) ≤ t := by linarith
      rw [← hc₁]
      push_cast
      have h3 : 2 * (t : ℝ) * Real.log 2 ≤ 2 * t * 1 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 : c₁ ≤ c₁ * t := le_mul_of_one_le_right hc₁0 ht1'
      have e : (c₁ + 2) * (t : ℝ) = c₁ * t + 2 * t := by ring
      rw [e]
      linarith
    have hΛle : Λ ≤ c₂ * t := by
      have : ((2 * k : ℕ) : ℝ) = 2 * (l + 1 : ℕ) := by rw [hk]; push_cast; ring
      rw [hΛ, this, hc₂, mul_assoc (2 * ((l + 1 : ℕ) : ℝ))]
      exact mul_le_mul_of_nonneg_left hlogle (by positivity)
    have hSle : S ≤ c₃ * X * t := by
      have h4 : S = 8 * ((d : ℝ) * Λ) := by rw [hS]; ring
      have h5 : (d : ℝ) * Λ ≤ ((2 * τ + 1) * X) * (c₂ * t) :=
        mul_le_mul hdX hΛle hΛ0.le (by positivity)
      rw [h4, hc₃]
      calc 8 * ((d : ℝ) * Λ) ≤ 8 * (((2 * τ + 1) * X) * (c₂ * t)) :=
            mul_le_mul_of_nonneg_left h5 (by norm_num)
        _ = _ := by ring
    have hrη : c₃ / (t : ℝ) ≤ η := by
      rw [div_le_iff₀ ht0]
      have := (div_le_iff₀ hη0).mp ht1r
      linarith
    have hη2 : 4 * 9 ^ l * η ≤ δ ^ 2 := by
      have := min_le_right 1 (δ ^ 2 / (4 * 9 ^ l))
      have h9 : (0 : ℝ) < 4 * 9 ^ l := by positivity
      calc 4 * 9 ^ l * η ≤ 4 * 9 ^ l * (δ ^ 2 / (4 * 9 ^ l)) :=
            mul_le_mul_of_nonneg_left this h9.le
        _ = δ ^ 2 := by field_simp
    have hp := core_bound hk hl hδ ht0 hη0 hS0 hKsq hK0 hX0 hSle hc₃0 hXk hrη (min_le_left _ _) hη2
    obtain ⟨w, hw⟩ : ∃ w : ℝ, w = ((2 : ℝ) ^ t)⁻¹ ^ l := ⟨_, rfl⟩
    rw [← hw] at hp
    have hw0 : 0 ≤ w := by rw [hw]; positivity
    have hq : 3 ^ l * w ≤ δ / 2 := by
      have h1 : w ≤ ((2 : ℝ) ^ t)⁻¹ := by
        rw [hw]
        calc ((2 : ℝ) ^ t)⁻¹ ^ l ≤ ((2 : ℝ) ^ t)⁻¹ ^ 1 :=
              pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
                (by omega)
          _ = _ := pow_one _
      have h2 : (0 : ℝ) < 2 ^ t := by positivity
      have h3 : 2 * 3 ^ l / δ ≤ (2 : ℝ) ^ t := ht2r.trans h2t
      rw [div_le_iff₀ hδ] at h3
      have h4 : (3 : ℝ) ^ l * ((2 : ℝ) ^ t)⁻¹ ≤ δ / 2 := by
        rw [← div_eq_mul_inv, div_le_iff₀ h2]
        linarith
      have h3p : (0 : ℝ) < 3 ^ l := by positivity
      exact (mul_le_mul_of_nonneg_left h1 h3p.le).trans h4
    have e : (3 * ((2 : ℝ) ^ t)⁻¹) ^ l = 3 ^ l * w := by rw [mul_pow, hw]
    rw [e, ← hY]
    have hsum : Real.sqrt S ^ k + (cd * 2) ^ k * (Y ^ k * Real.exp (-Λ)) ≤ Real.sqrt S ^ k + 1 := by
      linarith
    calc _ ≤ 3 ^ l * w * (Real.sqrt S ^ k + 1) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 3 ^ l * w * Real.sqrt S ^ k + 3 ^ l * w := by ring
      _ ≤ δ := by linarith
  · have h2 : (0 : ℝ) < (2 : ℝ) ^ (2 * t) := by positivity
    have h3 : 4 / δ ^ 3 ≤ (2 : ℝ) ^ (2 * t) := ht3r.trans h2t2
    rw [div_le_iff₀ (by positivity)] at h3
    have e : 4 / δ ^ 2 * ((2 : ℝ) ^ (2 * t))⁻¹ = 4 / (δ ^ 2 * (2 : ℝ) ^ (2 * t)) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith

/-- M3. The Forrelation lower bound for the exact promise problem, with no hypothesis. -/
theorem bansalSinhaLower : BansalSinhaLower := by
  intro k hk
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  have hl : 0 < l := by omega
  set δ := dl (l + 1) with hδ
  have hδ0 : 0 < δ := by simp only [hδ, dl]; positivity
  have hδs : δ ≤ 1 / 2 := by
    simp only [hδ, dl]
    have : (2 : ℝ) ≤ 2 ^ (5 * (l + 1)) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    norm_num
    linarith
  obtain ⟨τ, hτ⟩ := exists_pow_lt_of_lt_one hδ0 (by norm_num : (8 / 9 : ℝ) < 1)
  obtain ⟨t₀, ht₀⟩ := exists_threshold hl τ hδ0 (by linarith)
  refine ⟨t₀, fun t ht => ?_⟩
  obtain ⟨Λ, K, hK0, hKsq, hA, hsmall⟩ := ht₀ t ht
  refine lt_R_of_not_RLe (not_RLe_of_gap (t := t) hl hK0 hKsq hA
    (pow_le_one₀ (by norm_num) (by norm_num)) ?_)
  have h18 : 32 * δ ≤ (1 / 18 : ℝ) ^ l := by
    have e : 32 * δ = (1 / 32 : ℝ) ^ l := by
      have h : (2 : ℝ) ^ (5 * (l + 1)) = 32 ^ l * 32 := by
        rw [mul_add, pow_add, pow_mul]
        norm_num
      simp only [hδ, dl]
      rw [h, one_div, inv_pow]
      field_simp
    rw [e]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) l
  have hε := hτ.le
  set ε : ℝ := (8 / 9 : ℝ) ^ τ
  have h1 : 1 / 2 ≤ 1 - ε := by linarith
  have h2 : 31 * δ ≤ (1 / 18 : ℝ) ^ l - δ := by linarith
  have h3 : (1 / 2) * (31 * δ) ≤ (1 - ε) * ((1 / 18 : ℝ) ^ l - δ) :=
    mul_le_mul h1 h2 (by positivity) (by linarith)
  have hsm : 4 / δ ^ 2 * ((2 : ℝ) ^ (2 * t))⁻¹ ≤ δ := hsmall
  linarith

end QuarticQuery.ForrelationLower
