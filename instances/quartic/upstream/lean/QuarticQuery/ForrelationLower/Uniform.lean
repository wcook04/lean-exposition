module

public import QuarticQuery.ForrelationLower.Main

/-!
# A Forrelation lower bound uniform in `k`

The existential threshold of `bansalSinhaLower` is replaced by explicit parameters,
reusing the finite contradiction theorem `not_RLe_of_gap` with its coarse edge
constant `3`. For every `k ≥ 2` and every `t` with `15k + 2 ≤ 2t` (so `m = 4^t ≥ 2^(15k+2)`),

  `R (P k t) > m^(1-1/k) / (2332800 · k² · ln(4km))`.

Parameters: `τ = 25k` amplification rounds, `Λ = 2k ln(4km)`, padded depth `d = 50kL + 1`,
`K = √(8dΛ)`. Writing `a = 18^(-(k-1))`, the main advantage term is at most `a/48`, the
residual at most `a/4`, and the promise gap exceeds their sum. Depth zero is handled
separately: a depth-zero program has input-independent success, and `P k t` has both a
yes-instance and a no-instance.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open MeasureTheory Finset QuarticQuery.Forrelation

namespace QuarticQuery.ForrelationLower

local notation "Nm" t => Fin (mValue t)

/-! ## Depth zero -/

/-- A depth-zero randomized program has input-independent success, so a partial function
with both a yes-instance and a no-instance cannot be decided with zero queries. -/
theorem not_RLe_zero_of_yes_no {ι : Type} {f : PartialBool ι} {x₁ x₀ : BitInput ι}
    (h₁ : f x₁ = some true) (h₀ : f x₀ = some false) : ¬ RLe f 0 := by
  rintro ⟨A, hd, hs⟩
  have hleaf : ∀ j x y, (A.tree j).eval x = (A.tree j).eval y := by
    intro j x y
    have hj : (A.tree j).depth ≤ 0 :=
      (Finset.le_sup (f := fun j => (A.tree j).depth) (mem_univ j)).trans hd
    revert hj
    cases A.tree j with
    | leaf b => intro _; rfl
    | query i l r =>
      intro hj
      have h1 : 1 ≤ (QueryTree.query i l r).depth := Nat.le_add_right 1 _
      omega
  have hsucc : ∀ x y b, A.success x b = A.success y b := by
    intro x y b
    unfold RandomizedProgram.success
    exact sum_congr rfl fun j _ => by rw [hleaf j x y]
  have hsum : ∀ x, A.success x true + A.success x false = 1 := by
    intro x
    unfold RandomizedProgram.success
    rw [← sum_add_distrib, ← A.weight_sum]
    refine sum_congr rfl fun j _ => ?_
    cases (A.tree j).eval x <;> simp
  have a1 := hs x₁ true h₁
  have a0 := hs x₀ false h₀
  rw [hsucc x₁ x₀] at a1
  linarith [hsum x₀]

/-- `32 δ = 32^(-(k-1)) ≤ 18^(-(k-1))`. -/
theorem dl_le (l : ℕ) : 32 * dl (l + 1) ≤ (1 / 18 : ℝ) ^ l := by
  have e : 32 * dl (l + 1) = (1 / 32 : ℝ) ^ l := by
    have h : (2 : ℝ) ^ (5 * (l + 1)) = 32 ^ l * 32 := by
      rw [mul_add, pow_add, pow_mul]
      norm_num
    simp only [dl]
    rw [h, one_div, inv_pow]
    field_simp
  rw [e]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) l

theorem dl_pos (l : ℕ) : 0 < dl (l + 1) := by unfold dl; positivity

/-- `P k t` has a yes-instance: the hard distribution has mean Forrelation at least
`18^(-(k-1)) > δ`. -/
theorem exists_P_yes {l t : ℕ} (hl : 0 < l) :
    ∃ z : BC l (Nm t) → Bool, P (l + 1) t z = some true := by
  by_contra hno
  push_neg at hno
  have hlt : ∀ z : BC l (Nm t) → Bool, PhiF t z ≤ dl (l + 1) := fun z =>
    le_of_lt (lt_of_not_ge fun hz => hno z (P_yes hz))
  have hmass := mass_ge (t := t) hl
  rw [ext_PhiF_zero, sub_zero] at hmass
  have hbcP := bcf_ext (H t) (PhiF t : (BC l (Nm t) → Bool) → ℝ) (s := 1) (by simp)
  have hint : ∫ u, ext (PhiF t : (BC l (Nm t) → Bool) → ℝ) (wv (H t) 1 u)
      ∂(gP (PC l (Nm t))) ≤ ∫ _u, dl (l + 1) ∂(gP (PC l (Nm t))) := by
    refine integral_mono hbcP.integrable (integrable_const _) fun u => ?_
    have := ext_mono (g := (PhiF t : (BC l (Nm t) → Bool) → ℝ))
      (h := fun _ => dl (l + 1)) (μ := wv (H t) 1 u) hlt
      (fun c => abs_wv_le (H t) (s := 1) (by norm_num) u c)
    rwa [ext_const] at this
  have hc : ∫ _u, dl (l + 1) ∂(gP (PC l (Nm t))) = dl (l + 1) := by simp
  have h18 := dl_le l
  have hd0 := dl_pos l
  linarith

/-- `P k t` has a no-instance: the uniform second moment of `Φ` is `1/m < (δ/2)²`. -/
theorem exists_P_no {l t : ℕ} (ht : 10 * (l + 1) + 3 ≤ 2 * t) :
    ∃ z : BC l (Nm t) → Bool, P (l + 1) t z = some false := by
  by_contra hno
  push_neg at hno
  have h0 : 0 ≤ dl (l + 1) / 2 := (half_pos (dl_pos l)).le
  have hgt : ∀ z : BC l (Nm t) → Bool, (dl (l + 1) / 2) ^ 2 ≤ PhiF t z ^ 2 := by
    intro z
    have h1 : dl (l + 1) / 2 < |PhiF t z| := lt_of_not_ge fun hz => hno z (P_no hz)
    rw [← sq_abs (PhiF t z)]
    exact pow_le_pow_left₀ h0 h1.le 2
  have hmono := ext_mono (g := fun _ => (dl (l + 1) / 2) ^ 2)
    (h := fun z : BC l (Nm t) → Bool => PhiF t z ^ 2) hgt
    (μ := (0 : BC l (Nm t) → ℝ)) (fun c => by simp)
  rw [ext_const, ext_PhiF_sq] at hmono
  obtain ⟨e, he⟩ : ∃ e, 2 * t = 2 * (5 * (l + 1)) + 2 + (e + 1) :=
    ⟨2 * t - (10 * (l + 1) + 3), by omega⟩
  have key : (2 : ℝ) ^ (2 * t) = ((2 : ℝ) ^ (5 * (l + 1))) ^ 2 * 4 * 2 ^ (e + 1) := by
    rw [he]; ring
  rw [key] at hmono
  simp only [dl] at hmono
  have hp : (0 : ℝ) < (2 : ℝ) ^ (5 * (l + 1)) := by positivity
  have h2 : (2 : ℝ) ≤ 2 ^ (e + 1) := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have e1 : (((2 : ℝ) ^ (5 * (l + 1)))⁻¹ / 2) ^ 2 =
      (((2 : ℝ) ^ (5 * (l + 1))) ^ 2 * 4)⁻¹ := by
    field_simp <;> ring
  rw [e1, inv_le_inv₀ (by positivity) (by positivity)] at hmono
  nlinarith [pow_pos hp 2]

/-! ## Arithmetic of the parameters -/

/-- `ε = (8/9)^(25k) ≤ 18^(-k)`, from `18 · 8^25 < 9^25`. -/
theorem eps_le (k : ℕ) : (8 / 9 : ℝ) ^ (25 * k) ≤ (1 / 18 : ℝ) ^ k := by
  rw [pow_mul]
  exact pow_le_pow_left₀ (by positivity) (by norm_num) k

/-- The exceptional mass `4/(m δ²)` is at most `δ` once `m ≥ 2^(15k+2)`. -/
theorem q_le {l t : ℕ} (ht : 15 * (l + 1) + 2 ≤ 2 * t) :
    4 / dl (l + 1) ^ 2 * ((2 : ℝ) ^ (2 * t))⁻¹ ≤ dl (l + 1) := by
  obtain ⟨e, he⟩ : ∃ e, 2 * t = 3 * (5 * (l + 1)) + 2 + e :=
    ⟨2 * t - (15 * (l + 1) + 2), by omega⟩
  have key : (2 : ℝ) ^ (2 * t) = ((2 : ℝ) ^ (5 * (l + 1))) ^ 3 * 4 * 2 ^ e := by
    rw [he]; ring
  rw [key]
  simp only [dl]
  have hp : (0 : ℝ) < (2 : ℝ) ^ (5 * (l + 1)) := by positivity
  have he1 : (1 : ℝ) ≤ 2 ^ e := one_le_pow₀ (by norm_num)
  have e1 : 4 / (((2 : ℝ) ^ (5 * (l + 1)))⁻¹) ^ 2 *
      (((2 : ℝ) ^ (5 * (l + 1))) ^ 3 * 4 * 2 ^ e)⁻¹ =
      ((2 : ℝ) ^ (5 * (l + 1)))⁻¹ * (2 ^ e)⁻¹ := by
    field_simp <;> ring
  rw [e1]
  exact mul_le_of_le_one_right (inv_nonneg.2 hp.le) (inv_le_one_of_one_le₀ he1)

/-- `(1 + 1/(50k))^k ≤ e^(1/50) ≤ 50/49`. -/
theorem padding_pow_le (l : ℕ) :
    (1 + 1 / (50 * ((l + 1 : ℕ) : ℝ))) ^ (l + 1) ≤ 50 / 49 := by
  have hk0 : (0 : ℝ) < ((l + 1 : ℕ) : ℝ) := by positivity
  have h1 : 1 + 1 / (50 * ((l + 1 : ℕ) : ℝ)) ≤ Real.exp (1 / (50 * ((l + 1 : ℕ) : ℝ))) := by
    have := Real.add_one_le_exp (1 / (50 * ((l + 1 : ℕ) : ℝ)))
    linarith
  have h2 := pow_le_pow_left₀ (by positivity) h1 (l + 1)
  rw [← Real.exp_nat_mul] at h2
  have h3 : ((l + 1 : ℕ) : ℝ) * (1 / (50 * ((l + 1 : ℕ) : ℝ))) = 1 / 50 := by
    field_simp
  rw [h3] at h2
  have h4 : Real.exp (1 / 50) ≤ 50 / 49 := by
    have h5 := Real.add_one_le_exp (-(1 / 50 : ℝ))
    have h6 : Real.exp (1 / 50) * Real.exp (-(1 / 50)) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (1 / 50 : ℝ), Real.exp_pos (-(1 / 50) : ℝ)]
  linarith

/-- The main advantage term. If `1 ≤ L ≤ c · m^(1-1/k) / (k² lg)` with `c = 1/2332800`, and
`K² = 8 (50kL + 1) (2k lg)`, then `(3/√m)^(k-1) K^k ≤ 18^(-(k-1)) / 48`. -/
theorem main_term_le {l t : ℕ} {L lg K : ℝ} (hL1 : 1 ≤ L) (hlg : 0 < lg)
    (hL : L ≤ (1 / 2332800 : ℝ) * Real.rpow (mValue t : ℝ) (1 - 1 / ((l + 1 : ℕ) : ℝ)) /
      (((l + 1 : ℕ) : ℝ) ^ 2 * lg))
    (hK0 : 0 ≤ K)
    (hKsq : K ^ 2 = 16 * ((l + 1 : ℕ) : ℝ) * (50 * ((l + 1 : ℕ) : ℝ) * L + 1) * lg) :
    (3 * ((2 : ℝ) ^ t)⁻¹) ^ l * K ^ (l + 1) ≤ (1 / 18 : ℝ) ^ l / 48 := by
  obtain ⟨kr, hkr⟩ : ∃ kr : ℝ, kr = ((l + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hkr] at hL hKsq
  have hk1 : (1 : ℝ) ≤ kr := by rw [hkr]; push_cast; linarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
  have hk0 : 0 < kr := by linarith
  have hkne : kr ≠ 0 := hk0.ne'
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (2 : ℝ) ^ (2 * t) := ⟨_, rfl⟩
  have hN0 : 0 < N := by rw [hN]; positivity
  have hNne : N ≠ 0 := hN0.ne'
  have hm : (mValue t : ℝ) = N := by rw [hN]; simp [mValue]
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = Real.rpow (mValue t : ℝ) (1 - 1 / kr) := ⟨_, rfl⟩
  rw [← hY] at hL
  have hY0 : 0 ≤ Y := by rw [hY]; exact Real.rpow_nonneg (by positivity) _
  have hYk : Y ^ (l + 1) = N ^ l := by
    rw [hY, ← hm]
    show ((mValue t : ℝ) ^ (1 - 1 / kr)) ^ (l + 1) = (mValue t : ℝ) ^ l
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
    congr 1
    rw [hkr]
    field_simp
    push_cast
    ring
  have hL' : kr ^ 2 * lg * L ≤ Y / 2332800 := by
    rw [le_div_iff₀ (mul_pos (pow_pos hk0 2) hlg)] at hL
    linarith
  have hK2 : K ^ 2 ≤ (1 + 1 / (50 * kr)) * Y / 2916 := by
    have h1 : 50 * kr * L + 1 ≤ (50 * kr + 1) * L := by nlinarith
    have h2 : 0 ≤ 16 * (50 * kr + 1) / kr := div_nonneg (by linarith) hk0.le
    calc K ^ 2 = 16 * kr * (50 * kr * L + 1) * lg := hKsq
      _ ≤ 16 * kr * ((50 * kr + 1) * L) * lg := by
          have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 16 * kr)
          exact mul_le_mul_of_nonneg_right this hlg.le
      _ = 16 * (50 * kr + 1) / kr * (kr ^ 2 * lg * L) := by field_simp <;> ring
      _ ≤ 16 * (50 * kr + 1) / kr * (Y / 2332800) := mul_le_mul_of_nonneg_left hL' h2
      _ = (1 + 1 / (50 * kr)) * Y / 2916 := by field_simp <;> ring
  have hpad : (1 + 1 / (50 * kr)) ^ (l + 1) ≤ 50 / 49 := by
    rw [hkr]; exact padding_pow_le l
  have hK2k : (K ^ 2) ^ (l + 1) ≤ 50 / 49 * N ^ l / 2916 ^ (l + 1) := by
    calc (K ^ 2) ^ (l + 1) ≤ ((1 + 1 / (50 * kr)) * Y / 2916) ^ (l + 1) :=
          pow_le_pow_left₀ (by positivity) hK2 _
      _ = (1 + 1 / (50 * kr)) ^ (l + 1) * Y ^ (l + 1) / 2916 ^ (l + 1) := by
          rw [div_pow, mul_pow]
      _ ≤ 50 / 49 * N ^ l / 2916 ^ (l + 1) := by
          rw [hYk]
          have : (0 : ℝ) ≤ N ^ l := pow_nonneg hN0.le _
          have h3 := mul_le_mul_of_nonneg_right hpad this
          exact div_le_div_of_nonneg_right h3 (by positivity)
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = ((2 : ℝ) ^ t)⁻¹ := ⟨_, rfl⟩
  rw [← hw]
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hw2 : w ^ 2 = N⁻¹ := by
    rw [hw, hN, inv_pow, ← pow_mul, mul_comm t 2]
  have hM0 : 0 ≤ (3 * w) ^ l * K ^ (l + 1) :=
    mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg hK0 _)
  have hsq : ((3 * w) ^ l * K ^ (l + 1)) ^ 2 ≤ ((1 / 18 : ℝ) ^ l / 48) ^ 2 := by
    have e1 : ((3 * w) ^ l * K ^ (l + 1)) ^ 2 = ((3 * w) ^ 2) ^ l * (K ^ 2) ^ (l + 1) := by
      rw [mul_pow]
      congr 1 <;> rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have e0 : (3 * w) ^ 2 = 9 * N⁻¹ := by rw [mul_pow, hw2]; norm_num
    have e2 : (9 * N⁻¹) ^ l * N ^ l = 9 ^ l := by
      rw [← mul_pow]
      congr 1
      field_simp
    have e3 : ((1 / 18 : ℝ) ^ l / 48) ^ 2 = (1 / 324 : ℝ) ^ l / 2304 := by
      rw [div_pow, ← pow_mul, mul_comm l 2, pow_mul]
      norm_num
    have e4 : (9 : ℝ) ^ l / 2916 ^ l = (1 / 324 : ℝ) ^ l := by
      rw [← div_pow]
      norm_num
    rw [e1, e0, e3]
    have h9 : (0 : ℝ) ≤ (9 * N⁻¹) ^ l :=
      pow_nonneg (mul_nonneg (by norm_num) (inv_nonneg.2 hN0.le)) _
    calc (9 * N⁻¹) ^ l * (K ^ 2) ^ (l + 1) ≤ (9 * N⁻¹) ^ l * (50 / 49 * N ^ l / 2916 ^ (l + 1)) :=
          mul_le_mul_of_nonneg_left hK2k h9
      _ = 50 / 49 / 2916 * ((9 * N⁻¹) ^ l * N ^ l / 2916 ^ l) := by
          rw [pow_succ]
          ring
      _ = 50 / 49 / 2916 * (1 / 324 : ℝ) ^ l := by rw [e2, e4]
      _ ≤ (1 / 324 : ℝ) ^ l / 2304 := by
          have : (0 : ℝ) ≤ (1 / 324 : ℝ) ^ l := by positivity
          nlinarith
  exact (sq_le_sq₀ hM0 (by positivity)).mp hsq

/-- The sharp main term follows from the coarse arithmetic by scaling `K` and `lg`.
The edge constant is smaller by `16`, so the budget constant grows by `256`. -/
theorem main_term_le_sharp {l t : ℕ} {L lg K : ℝ} (hL1 : 1 ≤ L) (hlg : 0 < lg)
    (hL : L ≤ (2 / 18225 : ℝ) * Real.rpow (mValue t : ℝ) (1 - 1 / ((l + 1 : ℕ) : ℝ)) /
      (((l + 1 : ℕ) : ℝ) ^ 2 * lg))
    (hK0 : 0 ≤ K)
    (hKsq : K ^ 2 = 16 * ((l + 1 : ℕ) : ℝ) * (50 * ((l + 1 : ℕ) : ℝ) * L + 1) * lg) :
    ((3 / 16 : ℝ) * ((2 : ℝ) ^ t)⁻¹) ^ l * K ^ (l + 1) ≤ (1 / 18 : ℝ) ^ l / 3 := by
  have hL' : L ≤ (1 / 2332800 : ℝ) *
      Real.rpow (mValue t : ℝ) (1 - 1 / ((l + 1 : ℕ) : ℝ)) /
      (((l + 1 : ℕ) : ℝ) ^ 2 * (lg / 256)) := by
    convert hL using 1 <;> field_simp <;> ring
  have hKsq' : (K / 16) ^ 2 = 16 * ((l + 1 : ℕ) : ℝ) *
      (50 * ((l + 1 : ℕ) : ℝ) * L + 1) * (lg / 256) := by
    nlinarith [hKsq]
  have h := main_term_le (l := l) (t := t) hL1 (by positivity : 0 < lg / 256)
    hL' (by positivity : 0 ≤ K / 16) hKsq'
  have heq : ((3 / 16 : ℝ) * ((2 : ℝ) ^ t)⁻¹) ^ l * K ^ (l + 1) =
      16 * ((3 * ((2 : ℝ) ^ t)⁻¹) ^ l * (K / 16) ^ (l + 1)) := by
    simp only [mul_pow, div_pow, pow_succ]
    field_simp
  rw [heq]
  linarith

/-- The residual term. With `Λ = 2k ln(4n)` it equals `(3/√m)^(k-1) 2^(-k) ≤ 18^(-(k-1)) / 4`. -/
theorem tail_le {l t : ℕ} (ht : 6 ≤ t) (hl : 0 < l) {cd : ℝ} (hcd : 1 ≤ cd) :
    (3 * ((2 : ℝ) ^ t)⁻¹) ^ l * ((cd * 2) ^ (l + 1) * ((4 * cd) ^ (l + 1) *
      Real.exp (-(((2 * (l + 1) : ℕ) : ℝ) * Real.log (4 * cd))))) ≤ (1 / 18 : ℝ) ^ l / 4 := by
  have hY0 : 0 < 4 * cd := by linarith
  have hcd0 : cd ≠ 0 := (by linarith : (0 : ℝ) < cd).ne'
  have hexp : Real.exp (((2 * (l + 1) : ℕ) : ℝ) * Real.log (4 * cd)) =
      ((4 * cd) ^ (l + 1)) ^ 2 := by
    rw [Real.exp_nat_mul, Real.exp_log hY0]
    ring
  have htail : (cd * 2) ^ (l + 1) * ((4 * cd) ^ (l + 1) *
      Real.exp (-(((2 * (l + 1) : ℕ) : ℝ) * Real.log (4 * cd)))) = (1 / 2 : ℝ) ^ (l + 1) := by
    rw [Real.exp_neg, hexp]
    have h1 : (0 : ℝ) < (4 * cd) ^ (l + 1) := by positivity
    have e : (1 / 2 : ℝ) = (cd * 2) / (4 * cd) := by field_simp <;> ring
    rw [e, div_pow]
    field_simp <;> ring
  rw [htail]
  have h3 : 3 * ((2 : ℝ) ^ t)⁻¹ ≤ 1 / 18 := by
    have h64 : (64 : ℝ) ≤ 2 ^ t := by
      calc (64 : ℝ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num) ht
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith
  have h4 : (1 / 2 : ℝ) ^ (l + 1) ≤ 1 / 4 := by
    calc (1 / 2 : ℝ) ^ (l + 1) ≤ (1 / 2) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  calc (3 * ((2 : ℝ) ^ t)⁻¹) ^ l * (1 / 2) ^ (l + 1) ≤ (1 / 18) ^ l * (1 / 4) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) h3 l) h4 (by positivity) (by positivity)
    _ = _ := by ring

/-! ## Assembly -/

/-- Every budget `L` at most `m^(1-1/k) / (2332800 k² ln(4km))` fails, uniformly in `k`. -/
theorem not_RLe_uniform {l t L : ℕ} (hl : 0 < l) (ht : 15 * (l + 1) + 2 ≤ 2 * t)
    (hL : (L : ℝ) ≤ (1 / 2332800 : ℝ) *
        Real.rpow (mValue t : ℝ) (1 - 1 / ((l + 1 : ℕ) : ℝ)) /
        (((l + 1 : ℕ) : ℝ) ^ 2 *
          Real.log (4 * ((l + 1 : ℕ) : ℝ) * (mValue t : ℝ)))) :
    ¬ RLe (P (l + 1) t) L := by
  rcases Nat.eq_zero_or_pos L with rfl | hLpos
  · obtain ⟨z₁, h₁⟩ := exists_P_yes (t := t) hl
    obtain ⟨z₀, h₀⟩ := exists_P_no (l := l) (t := t) (by omega)
    exact not_RLe_zero_of_yes_no h₁ h₀
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hLpos
  have hcard : ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ) =
      ((l + 1 : ℕ) : ℝ) * (mValue t : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul]
  have hm1 : (1 : ℝ) ≤ (mValue t : ℝ) := by
    have : 1 ≤ mValue t := Nat.one_le_two_pow
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by
    push_cast; linarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
  have hcd1 : (1 : ℝ) ≤ ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ) := by
    rw [hcard]; nlinarith
  have h4cd : 4 * ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ) =
      4 * ((l + 1 : ℕ) : ℝ) * (mValue t : ℝ) := by
    rw [hcard]; ring
  have hlg : 0 < Real.log (4 * ((l + 1 : ℕ) : ℝ) * (mValue t : ℝ)) :=
    Real.log_pos (by nlinarith)
  have hS0 : (0 : ℝ) < 2 * ((2 * (25 * (l + 1)) * L + 1 : ℕ) : ℝ) * 2 ^ 2 *
      (((2 * (l + 1) : ℕ) : ℝ) *
        Real.log (4 * ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ))) := by
    rw [h4cd]
    exact mul_pos (by positivity) (mul_pos (by positivity) hlg)
  have hK0 := Real.sqrt_pos.mpr hS0
  have hKsq := Real.sq_sqrt hS0.le
  have hKsq' : Real.sqrt (2 * ((2 * (25 * (l + 1)) * L + 1 : ℕ) : ℝ) * 2 ^ 2 *
      (((2 * (l + 1) : ℕ) : ℝ) *
        Real.log (4 * ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ)))) ^ 2 =
      16 * ((l + 1 : ℕ) : ℝ) * (50 * ((l + 1 : ℕ) : ℝ) * L + 1) *
        Real.log (4 * ((l + 1 : ℕ) : ℝ) * (mValue t : ℝ)) := by
    rw [hKsq, h4cd]
    push_cast
    ring
  have hmain := main_term_le (t := t) hL1 hlg hL (Real.sqrt_nonneg _) hKsq'
  have htail := tail_le (l := l) (t := t) (by omega) hl hcd1
  have hA : ((3 : ℝ) * ((2 : ℝ) ^ t)⁻¹) ^ l *
      (Real.sqrt (2 * ((2 * (25 * (l + 1)) * L + 1 : ℕ) : ℝ) * 2 ^ 2 *
        (((2 * (l + 1) : ℕ) : ℝ) *
          Real.log (4 * ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ)))) ^ (l + 1) +
        (((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ) * 2) ^ (l + 1) *
        ((4 * ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ)) ^ (l + 1) *
          Real.exp (-(((2 * (l + 1) : ℕ) : ℝ) *
            Real.log (4 * ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ)))))) ≤
      (1 / 18 : ℝ) ^ l / 48 + (1 / 18 : ℝ) ^ l / 4 := by
    rw [mul_add]
    exact add_le_add hmain htail
  refine not_RLe_of_gap (t := t) (L := L) (τ := 25 * (l + 1)) hl hK0 hKsq hA
    (pow_le_one₀ (by norm_num) (by norm_num)) ?_
  -- the promise gap
  have hε0 : (0 : ℝ) ≤ (8 / 9 : ℝ) ^ (25 * (l + 1)) := by positivity
  have hε : (8 / 9 : ℝ) ^ (25 * (l + 1)) ≤ (1 / 18 : ℝ) ^ l / 18 := by
    have := eps_le (l + 1)
    have e : (1 / 18 : ℝ) ^ (l + 1) = (1 / 18 : ℝ) ^ l / 18 := by ring
    linarith
  have hδ := dl_le l
  have hδ0 := dl_pos l
  have hq := q_le (l := l) (t := t) ht
  have ha1 : (1 / 18 : ℝ) ^ l ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ha0 : (0 : ℝ) < (1 / 18 : ℝ) ^ l := by positivity
  have hεa : (8 / 9 : ℝ) ^ (25 * (l + 1)) * ((1 / 18 : ℝ) ^ l - dl (l + 1)) ≤
      (8 / 9 : ℝ) ^ (25 * (l + 1)) :=
    mul_le_of_le_one_right hε0 (by linarith)
  have e : (1 - (8 / 9 : ℝ) ^ (25 * (l + 1))) * ((1 / 18 : ℝ) ^ l - dl (l + 1)) =
      ((1 / 18 : ℝ) ^ l - dl (l + 1)) -
        (8 / 9 : ℝ) ^ (25 * (l + 1)) * ((1 / 18 : ℝ) ^ l - dl (l + 1)) := by ring
  rw [e]
  linarith


/-- The sharp edge coefficient increases the uniform budget constant by `256`. -/
theorem not_RLe_uniform_sharp {l t L : ℕ} (hl : 0 < l) (ht : 15 * (l + 1) + 2 ≤ 2 * t)
    (hL : (L : ℝ) ≤ (2 / 18225 : ℝ) *
        Real.rpow (mValue t : ℝ) (1 - 1 / ((l + 1 : ℕ) : ℝ)) /
        (((l + 1 : ℕ) : ℝ) ^ 2 *
          Real.log (4 * ((l + 1 : ℕ) : ℝ) * (mValue t : ℝ)))) :
    ¬ RLe (P (l + 1) t) L := by
  rcases Nat.eq_zero_or_pos L with rfl | hLpos
  · obtain ⟨z₁, h₁⟩ := exists_P_yes (t := t) hl
    obtain ⟨z₀, h₀⟩ := exists_P_no (l := l) (t := t) (by omega)
    exact not_RLe_zero_of_yes_no h₁ h₀
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hLpos
  have hcard : ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ) =
      ((l + 1 : ℕ) : ℝ) * (mValue t : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul]
  have hm1 : (1 : ℝ) ≤ (mValue t : ℝ) := by
    have : 1 ≤ mValue t := Nat.one_le_two_pow
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by
    push_cast; linarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
  have hcd1 : (1 : ℝ) ≤ ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ) := by
    rw [hcard]; nlinarith
  have h4cd : 4 * ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ) =
      4 * ((l + 1 : ℕ) : ℝ) * (mValue t : ℝ) := by
    rw [hcard]; ring
  have hlg : 0 < Real.log (4 * ((l + 1 : ℕ) : ℝ) * (mValue t : ℝ)) :=
    Real.log_pos (by nlinarith)
  have hS0 : (0 : ℝ) < 2 * ((2 * (25 * (l + 1)) * L + 1 : ℕ) : ℝ) * 2 ^ 2 *
      (((2 * (l + 1) : ℕ) : ℝ) *
        Real.log (4 * ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ))) := by
    rw [h4cd]
    exact mul_pos (by positivity) (mul_pos (by positivity) hlg)
  have hK0 := Real.sqrt_pos.mpr hS0
  have hKsq := Real.sq_sqrt hS0.le
  have hKsq' : Real.sqrt (2 * ((2 * (25 * (l + 1)) * L + 1 : ℕ) : ℝ) * 2 ^ 2 *
      (((2 * (l + 1) : ℕ) : ℝ) *
        Real.log (4 * ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ)))) ^ 2 =
      16 * ((l + 1 : ℕ) : ℝ) * (50 * ((l + 1 : ℕ) : ℝ) * L + 1) *
        Real.log (4 * ((l + 1 : ℕ) : ℝ) * (mValue t : ℝ)) := by
    rw [hKsq, h4cd]
    push_cast
    ring
  have hmain := main_term_le_sharp (t := t) hL1 hlg hL (Real.sqrt_nonneg _) hKsq'
  have htail_coarse := tail_le (l := l) (t := t) (by omega) hl hcd1
  have htail : ((3 / 16 : ℝ) * ((2 : ℝ) ^ t)⁻¹) ^ l *
      (((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ) * 2) ^ (l + 1) *
      ((4 * ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ)) ^ (l + 1) *
        Real.exp (-(((2 * (l + 1) : ℕ) : ℝ) *
          Real.log (4 * ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ))))) ≤
      (1 / 18 : ℝ) ^ l / 4 := by
    have hinv : (0 : ℝ) ≤ ((2 : ℝ) ^ t)⁻¹ := by positivity
    have hedge : (3 / 16 : ℝ) * ((2 : ℝ) ^ t)⁻¹ ≤
        3 * ((2 : ℝ) ^ t)⁻¹ := by linarith
    have hcoeff : ((3 / 16 : ℝ) * ((2 : ℝ) ^ t)⁻¹) ^ l ≤
        (3 * ((2 : ℝ) ^ t)⁻¹) ^ l :=
      pow_le_pow_left₀ (by positivity) hedge l
    have htail' := mul_le_mul_of_nonneg_right hcoeff
      (show (0 : ℝ) ≤
        (((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ) * 2) ^ (l + 1) *
        ((4 * ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ)) ^ (l + 1) *
          Real.exp (-(((2 * (l + 1) : ℕ) : ℝ) *
            Real.log (4 * ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ))))) by positivity)
    simpa only [mul_assoc] using htail'.trans htail_coarse
  have hA : ((3 / 16 : ℝ) * ((2 : ℝ) ^ t)⁻¹) ^ l *
      (Real.sqrt (2 * ((2 * (25 * (l + 1)) * L + 1 : ℕ) : ℝ) * 2 ^ 2 *
        (((2 * (l + 1) : ℕ) : ℝ) *
          Real.log (4 * ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ)))) ^ (l + 1) +
        (((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ) * 2) ^ (l + 1) *
        ((4 * ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ)) ^ (l + 1) *
          Real.exp (-(((2 * (l + 1) : ℕ) : ℝ) *
            Real.log (4 * ((Fintype.card (BC l (Fin (mValue t))) : ℕ) : ℝ)))))) ≤
      (1 / 18 : ℝ) ^ l / 3 + (1 / 18 : ℝ) ^ l / 4 := by
    rw [mul_add]
    simpa only [mul_assoc] using add_le_add hmain htail
  refine not_RLe_of_gap_sharp (t := t) (L := L) (τ := 25 * (l + 1)) hl hK0 hKsq hA
    (pow_le_one₀ (by norm_num) (by norm_num)) ?_
  -- the promise gap
  have hε0 : (0 : ℝ) ≤ (8 / 9 : ℝ) ^ (25 * (l + 1)) := by positivity
  have hε : (8 / 9 : ℝ) ^ (25 * (l + 1)) ≤ (1 / 18 : ℝ) ^ l / 18 := by
    have := eps_le (l + 1)
    have e : (1 / 18 : ℝ) ^ (l + 1) = (1 / 18 : ℝ) ^ l / 18 := by ring
    linarith
  have hδ := dl_le l
  have hδ0 := dl_pos l
  have hq := q_le (l := l) (t := t) ht
  have ha1 : (1 / 18 : ℝ) ^ l ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ha0 : (0 : ℝ) < (1 / 18 : ℝ) ^ l := by positivity
  have hεa : (8 / 9 : ℝ) ^ (25 * (l + 1)) * ((1 / 18 : ℝ) ^ l - dl (l + 1)) ≤
      (8 / 9 : ℝ) ^ (25 * (l + 1)) :=
    mul_le_of_le_one_right hε0 (by linarith)
  have e : (1 - (8 / 9 : ℝ) ^ (25 * (l + 1))) * ((1 / 18 : ℝ) ^ l - dl (l + 1)) =
      ((1 / 18 : ℝ) ^ l - dl (l + 1)) -
        (8 / 9 : ℝ) ^ (25 * (l + 1)) * ((1 / 18 : ℝ) ^ l - dl (l + 1)) := by ring
  rw [e]
  linarith

end QuarticQuery.ForrelationLower

namespace QuarticQuery

open ForrelationLower

/-- The Forrelation lower bound with an explicit constant, uniform in `k`:
for `k ≥ 2` and `m = 4^t ≥ 2^(15k+2)`, `R(P k t) > m^(1-1/k) / (2332800 k² ln(4km))`. -/
theorem forrelation_lower_uniform_existing_constants
    (k t : ℕ) (hk : 2 ≤ k) (ht : 15 * k + 2 ≤ 2 * t) :
    (1 / 2332800 : ℝ) *
        Real.rpow (mValue t : ℝ) (1 - 1 / (k : ℝ)) /
        ((k : ℝ) ^ 2 * Real.log (4 * (k : ℝ) * (mValue t : ℝ))) <
      (R (P k t) : ℝ) := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  by_contra h
  exact not_RLe_uniform (t := t) (L := R (P (l + 1) t)) (by omega)
    ht (le_of_not_gt h) (RLe_R _)

end QuarticQuery

namespace QuarticQuery

open ForrelationLower

/-- For every `k ≥ 2` and `m = 4^t ≥ 2^(15k+2)`, the uniform lower bound
has numerical constant `2/18225`, a factor `256` above the coarse endpoint. -/
theorem forrelation_lower_uniform_sharp
    (k t : ℕ) (hk : 2 ≤ k) (ht : 15 * k + 2 ≤ 2 * t) :
    (2 / 18225 : ℝ) *
        Real.rpow (mValue t : ℝ) (1 - 1 / (k : ℝ)) /
        ((k : ℝ) ^ 2 * Real.log (4 * (k : ℝ) * (mValue t : ℝ))) <
      (R (P k t) : ℝ) := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  by_contra h
  exact not_RLe_uniform_sharp (t := t) (L := R (P (l + 1) t)) (by omega)
    ht (le_of_not_gt h) (RLe_R _)

/-- `ln(4km) ≤ 6t` once `k ≤ t`, for `m = 4^t`. -/
theorem log_four_k_m_le {k t : ℕ} (hk : 1 ≤ k) (hkt : k ≤ t) :
    Real.log (4 * (k : ℝ) * (mValue t : ℝ)) ≤ 6 * t := by
  have hk0 : (0 : ℝ) < 4 * (k : ℝ) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hm : (mValue t : ℝ) = (2 : ℝ) ^ (2 * t) := by simp [mValue]
  rw [hm, Real.log_mul hk0.ne' (by positivity), Real.log_pow]
  have h1 : Real.log (4 * (k : ℝ)) ≤ 4 * k - 1 := Real.log_le_sub_one_of_pos hk0
  have h2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hkt' : (k : ℝ) ≤ t := by exact_mod_cast hkt
  have h3 : ((2 * t : ℕ) : ℝ) * Real.log 2 ≤ 2 * t := by
    push_cast
    nlinarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  linarith

/-- The exponential estimate used by the growing-order auxiliary cutoff.
The base `41` is stronger than the sufficient base `64` in the return. -/
theorem uniform_cutoff_power {t : ℕ} (ht : 41 ≤ t) :
    (27993600 : ℝ) * (t : ℝ) ^ 3 ≤ (2 : ℝ) ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn' : (41 : ℝ) ≤ n := by exact_mod_cast hn
    have hstep : ((n : ℝ) + 1) ^ 3 ≤ 2 * (n : ℝ) ^ 3 := by
      have hn4 : 0 ≤ (n : ℝ) - 4 := by linarith
      nlinarith [mul_nonneg hn4 (sq_nonneg (n : ℝ)),
        mul_nonneg hn4 (show (0 : ℝ) ≤ n by positivity)]
    rw [pow_succ (2 : ℝ) n]
    push_cast
    nlinarith

/-- The auxiliary classical cutoff is nonzero, at most the block size, and loses
at most a factor two to its floor. Its threshold is uniform in the order. -/
theorem uniform_budget_floor_bounds (k t : ℕ) (hk : 2 ≤ k) (hkt : k ≤ t) (ht : 41 ≤ t) :
    let X := (1 / 2332800 : ℝ) *
      Real.rpow (mValue t : ℝ) (1 - 1 / (k : ℝ)) /
      ((k : ℝ) ^ 2 * Real.log (4 * (k : ℝ) * (mValue t : ℝ)))
    2 ≤ X ∧ 1 ≤ ⌊X⌋₊ ∧ ⌊X⌋₊ ≤ mValue t ∧ X / 2 ≤ (⌊X⌋₊ : ℝ) := by
  intro X
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hkt' : (k : ℝ) ≤ t := by exact_mod_cast hkt
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hm1 : (1 : ℝ) ≤ (mValue t : ℝ) := by
    have : 1 ≤ mValue t := Nat.one_le_two_pow
    exact_mod_cast this
  have hm : (mValue t : ℝ) = (2 : ℝ) ^ (2 * t) := by simp [mValue]
  have hlg0 : 0 < Real.log (4 * (k : ℝ) * (mValue t : ℝ)) :=
    Real.log_pos (by nlinarith)
  have hlg := log_four_k_m_le (by omega) hkt
  have hYlo : (2 : ℝ) ^ t ≤ Real.rpow (mValue t : ℝ) (1 - 1 / (k : ℝ)) := by
    have hhalf : (1 / 2 : ℝ) ≤ 1 - 1 / (k : ℝ) := by
      have := one_div_le_one_div_of_le two_pos hk2
      linarith
    have hroot : (mValue t : ℝ) ^ (1 / 2 : ℝ) = (2 : ℝ) ^ t := by
      rw [hm, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    rw [← hroot]
    exact Real.rpow_le_rpow_of_exponent_le hm1 hhalf
  have hYhi : Real.rpow (mValue t : ℝ) (1 - 1 / (k : ℝ)) ≤ (mValue t : ℝ) := by
    calc _ ≤ (mValue t : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hm1 (by
          have : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
          linarith)
      _ = _ := Real.rpow_one _
  have hden0 : 0 < (k : ℝ) ^ 2 * Real.log (4 * (k : ℝ) * (mValue t : ℝ)) := by positivity
  have hdenlo : 1 ≤ (k : ℝ) ^ 2 * Real.log (4 * (k : ℝ) * (mValue t : ℝ)) := by
    have hlog2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (by nlinarith : (2 : ℝ) ≤ 4 * (k : ℝ) * (mValue t : ℝ))
    have hloghalf : (1 / 2 : ℝ) ≤ Real.log (4 * (k : ℝ) * (mValue t : ℝ)) := by
      have := Real.log_two_gt_d9
      linarith
    have hmul := mul_le_mul (show (4 : ℝ) ≤ (k : ℝ) ^ 2 by nlinarith)
      hloghalf (by norm_num : (0 : ℝ) ≤ 1 / 2) (sq_nonneg (k : ℝ))
    linarith
  have hdenhi : (k : ℝ) ^ 2 * Real.log (4 * (k : ℝ) * (mValue t : ℝ)) ≤ 6 * (t : ℝ) ^ 3 := by
    have hksq : (k : ℝ) ^ 2 ≤ (t : ℝ) ^ 2 := by nlinarith
    calc _ ≤ (k : ℝ) ^ 2 * (6 * t) := mul_le_mul_of_nonneg_left hlg (by positivity)
      _ ≤ (t : ℝ) ^ 2 * (6 * t) := mul_le_mul_of_nonneg_right hksq (by positivity)
      _ = _ := by ring
  have hX2 : 2 ≤ X := by
    dsimp only [X]
    rw [le_div_iff₀ hden0]
    have hp := uniform_cutoff_power ht
    linarith
  have hXm : X ≤ (mValue t : ℝ) := by
    dsimp only [X]
    rw [div_le_iff₀ hden0]
    have hY0 := Real.rpow_nonneg (show (0 : ℝ) ≤ (mValue t : ℝ) by positivity)
      (1 - 1 / (k : ℝ))
    have hmul := le_mul_of_one_le_right (show (0 : ℝ) ≤ (mValue t : ℝ) by positivity) hdenlo
    nlinarith
  have hfloor1 : 1 ≤ ⌊X⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_one]
    linarith
  refine ⟨hX2, hfloor1, ?_, ?_⟩
  · exact_mod_cast (Nat.floor_le (by linarith : 0 ≤ X)).trans hXm
  · have := Nat.lt_floor_add_one X
    linarith

/-- The conclusion of `BansalSinhaLower` above an explicit threshold: for every `k ≥ 2` and
every `t ≥ 3499200 k²`, `Lvalue k t < R (P k t)`. -/
theorem lvalue_lt_R_explicit (k t : ℕ) (hk : 2 ≤ k) (ht : 3499200 * k ^ 2 ≤ t) :
    Lvalue k t < R (P k t) := by
  have hkt : k ≤ t := by nlinarith
  have hmain := forrelation_lower_uniform_existing_constants k t hk (by nlinarith)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have ht0 : (0 : ℝ) < t := by
    have : 1 ≤ t := by nlinarith
    exact_mod_cast this
  have hm1 : (1 : ℝ) ≤ (mValue t : ℝ) := by
    have : 1 ≤ mValue t := Nat.one_le_two_pow
    exact_mod_cast this
  have hlg0 : 0 < Real.log (4 * (k : ℝ) * (mValue t : ℝ)) := Real.log_pos (by nlinarith)
  have hlg := log_four_k_m_le (by omega) hkt
  have htr : (3499200 : ℝ) * (k : ℝ) ^ 2 ≤ t := by exact_mod_cast ht
  have hY0 : (0 : ℝ) ≤ Real.rpow (mValue t : ℝ) (1 - 1 / (k : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hfloor : (Lvalue k t : ℝ) ≤
      Real.rpow (mValue t : ℝ) (1 - 1 / (k : ℝ)) / (2 * (t : ℝ)) ^ 2 := by
    unfold Lvalue
    rw [logb_mValue]
    exact Nat.floor_le (div_nonneg hY0 (by positivity))
  have hcmp : Real.rpow (mValue t : ℝ) (1 - 1 / (k : ℝ)) / (2 * (t : ℝ)) ^ 2 ≤
      (1 / 2332800 : ℝ) * Real.rpow (mValue t : ℝ) (1 - 1 / (k : ℝ)) /
        ((k : ℝ) ^ 2 * Real.log (4 * (k : ℝ) * (mValue t : ℝ))) := by
    rw [div_le_div_iff₀ (pow_pos (by linarith) 2) (mul_pos (pow_pos (by linarith) 2) hlg0)]
    have h1 : (k : ℝ) ^ 2 * Real.log (4 * (k : ℝ) * (mValue t : ℝ)) ≤
        (1 / 2332800 : ℝ) * (2 * (t : ℝ)) ^ 2 := by
      have h2 : (k : ℝ) ^ 2 * Real.log (4 * (k : ℝ) * (mValue t : ℝ)) ≤ (k : ℝ) ^ 2 * (6 * t) :=
        mul_le_mul_of_nonneg_left hlg (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right htr ht0.le]
    have := mul_le_mul_of_nonneg_left h1 hY0
    nlinarith
  have : (Lvalue k t : ℝ) < (R (P k t) : ℝ) := by linarith
  exact_mod_cast this

end QuarticQuery
