module

public import QuarticQuery.ForrelationLower.Cascade
public import QuarticQuery.Forrelation.Product

/-!
# Forrelation on the hard distribution

Blueprint lemmas P1–P3. `Φ` is written as a nested sum `Rs`, so that each discrete
derivative removes one layer and the Stein walk unfolds in closed form.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open MeasureTheory Finset QuarticQuery.Forrelation

namespace QuarticQuery.ForrelationLower

section Lin

variable {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
  {c : β → ι} (κ : β → ℝ) (R : β → (ι → Bool) → ℝ)

/-- A linear form in the signs at `c`, with coefficients not seeing those signs. -/
noncomputable def lin (c : β → ι) (κ : β → ℝ) (R : β → (ι → Bool) → ℝ) (z : ι → Bool) : ℝ :=
  ∑ b, κ b * sg (z (c b)) * R b z

/-- Support for blueprint P1–P3. -/
theorem D_lin (hc : Function.Injective c)
    (hR : ∀ b b' z x, R b (Function.update z (c b') x) = R b z) (b : β) :
    D (c b) (lin c κ R) = fun z => κ b * R b z := by
  funext z
  simp only [D, lin, hR, ← sum_sub_distrib, ← mul_sub, sum_div]
  rw [Finset.sum_eq_single b]
  · simp only [Function.update_self, sg_false, sg_true]; ring
  · intro b' _ hb
    have hne : c b' ≠ c b := fun h => hb (hc h)
    simp [Function.update_of_ne hne]
  · simp

/-- Support for blueprint P1–P3. -/
theorem bw_zero_flip (a : ι) (z : ι → Bool) : bw (0 : ι → ℝ) (flip a z) = bw 0 z := by
  rw [bw_eq a, bw_eq a, bwOff_flip]
  simp [piB]

/-- Support for blueprint P1–P3. -/
theorem ext_sg_mul_zero (a : ι) (r : (ι → Bool) → ℝ) (hr : ∀ z, r (flip a z) = r z) :
    ext (fun z => sg (z a) * r z) 0 = 0 := by
  unfold ext
  have h := sum_flip a (fun z => sg (z a) * r z * bw 0 z)
  simp only [hr, bw_zero_flip, flip_apply_self, sg_not] at h
  have e : ∑ z, -sg (z a) * r z * bw 0 z = - ∑ z, sg (z a) * r z * bw 0 z := by
    rw [← sum_neg_distrib]; exact sum_congr rfl fun z _ => by ring
  rw [e] at h
  linarith

/-- Support for blueprint P1–P3. -/
theorem ext_lin_zero (hR : ∀ b b' z x, R b (Function.update z (c b') x) = R b z) :
    ext (lin c κ R) 0 = 0 := by
  unfold lin
  rw [ext_sum]
  refine sum_eq_zero fun b _ => ?_
  have : (fun z => κ b * sg (z (c b)) * R b z) = fun z => κ b * (sg (z (c b)) * R b z) := by
    funext z; ring
  rw [this, ext_smul, ext_sg_mul_zero _ _ fun z => hR _ _ _ _, mul_zero]

/-- Support for blueprint P1–P3. -/
theorem ext_lin_sq_zero (hc : Function.Injective c)
    (hR : ∀ b b' z x, R b (Function.update z (c b') x) = R b z) :
    ext (fun z => lin c κ R z ^ 2) 0 = ∑ b, κ b ^ 2 * ext (fun z => R b z ^ 2) 0 := by
  have e : (fun z => lin c κ R z ^ 2) = fun z =>
      ∑ b, ∑ b', κ b * κ b' * (sg (z (c b)) * (sg (z (c b')) * (R b z * R b' z))) := by
    funext z
    simp only [lin, sq, sum_mul, mul_sum]
    exact sum_congr rfl fun b _ => sum_congr rfl fun b' _ => by ring
  rw [e, ext_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [ext_sum, Finset.sum_eq_single b]
  · have : (fun z : ι → Bool => κ b * κ b * (sg (z (c b)) * (sg (z (c b)) * (R b z * R b z)))) =
        fun z => κ b ^ 2 * R b z ^ 2 := by
      funext z
      have := sg_sq (z (c b))
      calc _ = κ b * κ b * ((sg (z (c b)) * sg (z (c b))) * (R b z * R b z)) := by ring
        _ = _ := by rw [this]; ring
    rw [this, ext_smul]
  · intro b' _ hb
    rw [ext_smul, ext_sg_mul_zero, mul_zero]
    intro z
    have hne : c b' ≠ c b := fun h => hb (hc h)
    simp only [flip, hR, Function.update_of_ne hne]
  · simp

end Lin

variable {l t : ℕ}

local notation "Nm" t => Fin (mValue t)

/-- The sign of an entry of the Walsh matrix. -/
noncomputable def ww (t : ℕ) (a b : Nm t) : ℝ := (walshSign t a b : ℝ)

/-- Support for blueprint P1–P3. -/
theorem ww_sq (a b : Nm t) : ww t a b ^ 2 = 1 := by
  rcases walshSign_eq_one_or t a b with h | h <;> simp [ww, h]

/-- Support for blueprint P1–P3. -/
theorem ww_comm (a b : Nm t) : ww t a b = ww t b a := by simp [ww, walshSign_symm t a b]

/-- Support for blueprint P1–P3. -/
theorem H_apply (a b : Nm t) : H t a b = ((2 : ℝ) ^ t)⁻¹ * ww t a b := by
  simp [H, W, walshZ, ww]

/-- Support for blueprint P1–P3. -/
theorem H_mul_ww (a b : Nm t) : H t b a * ww t a b = ((2 : ℝ) ^ t)⁻¹ := by
  rw [H_apply, ww_comm b a, mul_assoc, ← sq, ww_sq, mul_one]

/-- Support for blueprint P1–P3. -/
theorem abs_H_le (a b : Nm t) : |H t a b| ≤ ((2 : ℝ) ^ t)⁻¹ := by
  rw [H_apply, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((2 : ℝ) ^ t)⁻¹)]
  have : |ww t a b| = 1 := by
    rcases walshSign_eq_one_or t a b with h | h <;> simp [ww, h]
  rw [this, mul_one]

/-- Support for blueprint P1–P3. -/
theorem rowsOrth_H (t : ℕ) : RowsOrth (H t) := by
  intro a b
  have h := congrFun (congrFun (H_mul_H t) a) b
  have hT : ∀ i j, H t i j = H t j i := fun i j => congrFun (congrFun (H_transpose t) j) i
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [← h]
  exact sum_congr rfl fun i _ => by rw [hT i b]

/-- The nested sum of layers after block `j`. -/
noncomputable def Rs (t : ℕ) : ℕ → ℕ → (Nm t) → (BC l (Nm t) → Bool) → ℝ
  | 0, _, _, _ => 1
  | e + 1, j, a, z => lin (fun b => cn (j + 1) b) (fun b => ww t a b) (Rs t e (j + 1)) z

/-- Support for blueprint P1–P3. -/
theorem cn_inj (j : ℕ) : Function.Injective fun b : Nm t => (cn j b : BC l (Nm t)) :=
  fun _ _ h => congrArg Prod.snd h

/-- Dependence on later blocks only. -/
theorem Rs_update {e j : ℕ} (hle : j + e ≤ l) (a : Nm t) (z : BC l (Nm t) → Bool) (c : BC l (Nm t))
    (hc : c.1.val ≤ j) (x : Bool) :
    Rs t e j a (Function.update z c x) = Rs t e j a z := by
  induction e generalizing j a with
  | zero => rfl
  | succ e ih =>
    simp only [Rs, lin]
    refine sum_congr rfl fun b _ => ?_
    have hne : (cn (j + 1) b : BC l (Nm t)) ≠ c := by
      intro h
      have : (cn (j + 1) b : BC l (Nm t)).1.val = j + 1 := cn_val_of_le (by omega) b
      rw [h] at this
      omega
    rw [Function.update_of_ne hne, ih (j := j + 1) (by omega) _ (by omega)]

/-- The whole function: `M Φ = Σ_a sign(a) Rs`. -/
noncomputable def Fz (t : ℕ) (z : BC l (Nm t) → Bool) : ℝ :=
  lin (fun a => cn 0 a) (fun _ => 1) (Rs t l 0) z

/-- Support for blueprint P1–P3. -/
theorem walk_eq_Rs (z : BC l (Nm t) → Bool) (e : ℕ) : ∀ (j : ℕ), j + e = l → ∀ a : Nm t,
    ((walkN (2 * t) e (fun h => layerSign z (h + j)) a : ℤ) : ℝ) =
      sg (z (cn j a)) * Rs t e j a z := by
  have hl : ∀ (j : ℕ), j ≤ l → ∀ a : Nm t, ((layerSign z j a : ℤ) : ℝ) = sg (z (cn j a)) := by
    intro j hj a
    have hh : j < l + 1 ∧ a.val < mValue t := ⟨by omega, a.isLt⟩
    have e1 : (cn j a : BC l (Nm t)) = (⟨j, hh.1⟩, a) := by
      simp only [cn]
      congr 2
      omega
    simp only [layerSign, dite_eq_left_of_eq_true (eq_true hh), e1, sg_eq_bitSign]
  induction e with
  | zero =>
    intro j hj a
    subst hj
    simp only [walkN, Rs, mul_one]
    simpa using hl (0 + j + 0 - 0) (by omega) a
  | succ e ih =>
    intro j hj a
    simp only [walkN]
    rw [← sum_range_mValue t (fun b => walshN (2 * t) a b *
      walkN (2 * t) e (fun h => layerSign z (h + 1 + j)) b)]
    push_cast
    have hs : (fun h => layerSign z (h + 1 + j)) = fun h => layerSign z (h + (j + 1)) := by
      funext h; congr 1; omega
    simp only [hs]
    have h0 := hl (0 + j) (by omega) a
    rw [h0]
    simp only [Rs, lin, zero_add]
    congr 1
    refine sum_congr rfl fun b _ => ?_
    rw [ih (j + 1) (by omega) b]
    simp only [ww, walshSign_eq]
    push_cast
    ring

/-- Support for blueprint P1–P3. -/
theorem numerator_eq_Fz (z : BC l (Nm t) → Bool) :
    ((forrelationNumerator (l + 1) t z : ℤ) : ℝ) = Fz t z := by
  rw [numerator_eq_walk]
  rw [← sum_range_mValue t (walkN (2 * t) l (layerSign z))]
  push_cast
  simp only [Fz, lin]
  refine sum_congr rfl fun a _ => ?_
  have := walk_eq_Rs z l 0 (by omega) a
  simp only [add_zero] at this
  rw [this]
  ring

/-- `M` as a real. -/
theorem denom_cast : ((forrelationDenominator (l + 1) t : ℤ) : ℝ) =
    (2 : ℝ) ^ (2 * t) * ((2 : ℝ) ^ t) ^ l := by
  simp [forrelationDenominator]

/-- The depth-indexed resolved weight. -/
noncomputable def Yy (s : ℝ) : ℕ → ℕ → (Nm t) → (PC l (Nm t) → ℝ) → ℝ
  | 0, _, _, _ => 1
  | e + 1, j, a, u => ∑ b, H t b a * psiS (Uc u j a) * dphi (Vc (H t) u j b) *
      (ww t a b * Yy s e (j + 1) b u)

/-- Support for blueprint P1–P3. -/
theorem Int_Rs (s : ℝ) (u : PC l (Nm t) → ℝ) (e : ℕ) : ∀ (j : ℕ), j + e ≤ l →
    ∀ (a : Nm t) (K : ℝ), Int (H t) s e j a (fun z => K * Rs t e j a z) u = K * Yy s e j a u := by
  induction e with
  | zero =>
    intro j _ a K
    simp only [Int, Rs, Yy]
    exact ext_const _ _
  | succ e ih =>
    intro j hj a K
    simp only [Int, Yy, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    have e1 : (fun z : BC l (Nm t) → Bool => K * Rs t (e + 1) j a z) =
        lin (fun b => cn (j + 1) b) (fun b => K * ww t a b) (Rs t e (j + 1)) := by
      funext z
      simp only [Rs, lin, mul_sum]
      exact sum_congr rfl fun b _ => by ring
    have e2 := D_lin (c := fun b : Nm t => (cn (j + 1) b : BC l (Nm t))) (fun b => K * ww t a b)
      (Rs t e (j + 1)) (cn_inj (j + 1))
      (fun b b' z x => Rs_update (by omega) b z _ (by rw [cn_val_of_le (by omega)]) x) b
    beta_reduce at e2
    rw [e1, e2, ih (j + 1) (by omega) b (K * ww t a b)]
    ring

/-! ## The tangent bound -/

/-- Support for blueprint P1–P3. -/
theorem qf_le_exp (x : ℝ) : qf x ≤ Real.sqrt 3 * Real.exp ((x ^ 2 - 1) / 6) := by
  have hq := qf_pos x
  have h1 : (2 + x ^ 2) / 3 ≤ Real.exp ((2 + x ^ 2) / 3 - 1) := by
    have := Real.add_one_le_exp ((2 + x ^ 2) / 3 - 1)
    linarith
  have e : Real.exp ((2 + x ^ 2) / 3 - 1) = Real.exp ((x ^ 2 - 1) / 6) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [e] at h1
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine (sq_le_sq₀ hq.le (by positivity)).mp ?_
  rw [mul_pow, h3, qf_sq]
  linarith

/-- The one-pair lower bound. -/
theorem psi_dphi_ge (x y : ℝ) :
    (1 / 18) * Real.exp (-((x ^ 2 - 1) / 6 + 5 / 6 * (y ^ 2 - 1))) ≤ psiS x * dphi y := by
  have hx := qf_pos x
  have hy := qf_pos y
  have h1 := qf_le_exp x
  have h2 := qf_le_exp y
  set E1 := Real.exp ((x ^ 2 - 1) / 6)
  set E2 := Real.exp ((y ^ 2 - 1) / 6)
  have hE1 : 0 < E1 := Real.exp_pos _
  have hE2 : 0 < E2 := Real.exp_pos _
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 3 ^ 6 = 27 := by
    calc _ = (Real.sqrt 3 ^ 2) ^ 3 := by ring
      _ = 27 := by rw [h3]; norm_num
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h5 : qf y ^ 5 ≤ (Real.sqrt 3 * E2) ^ 5 := pow_le_pow_left₀ hy.le h2 5
  have hprod : qf x * qf y ^ 5 ≤ 27 * (E1 * E2 ^ 5) := by
    calc _ ≤ (Real.sqrt 3 * E1) * (Real.sqrt 3 * E2) ^ 5 := by gcongr
      _ = Real.sqrt 3 ^ 6 * (E1 * E2 ^ 5) := by ring
      _ = _ := by rw [h6]
  have eE : Real.exp (-((x ^ 2 - 1) / 6 + 5 / 6 * (y ^ 2 - 1))) = (E1 * E2 ^ 5)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_neg]
    congr 1
    push_cast
    ring
  rw [eE]
  have hval : psiS x * dphi y = (3 / 2) / (qf x * qf y ^ 5) := by
    unfold psiS dphi
    field_simp
  have e3 : (1 / 18 : ℝ) * (E1 * E2 ^ 5)⁻¹ = (3 / 2) / (27 * (E1 * E2 ^ 5)) := by
    field_simp
    norm_num
  rw [hval, e3]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hprod

/-- The exponent of one step. -/
noncomputable def ττ (t : ℕ) (u : PC l (Nm t) → ℝ) (j : ℕ) (a b : Nm t) : ℝ :=
  (Uc u j a ^ 2 - 1) / 6 + 5 / 6 * (Vc (H t) u j b ^ 2 - 1)

/-- The accumulated exponent. -/
noncomputable def TT (t : ℕ) : ℕ → ℕ → (Nm t) → (PC l (Nm t) → ℝ) → ℝ
  | 0, _, _, _ => 0
  | e + 1, j, a, u => ((2 : ℝ) ^ (2 * t))⁻¹ * ∑ b, (ττ t u j a b + TT t e (j + 1) b u)

/-- Support for blueprint P1–P3. -/
theorem card_Nm (t : ℕ) : ((Fintype.card (Nm t) : ℕ) : ℝ) = (2 : ℝ) ^ (2 * t) := by
  rw [Fintype.card_fin]
  simp [mValue]

/-- Finite Jensen for the exponential. -/
theorem sum_exp_neg_ge {β : Type} [Fintype β] [Nonempty β] (x : β → ℝ) :
    (Fintype.card β : ℝ) * Real.exp (-((Fintype.card β : ℝ)⁻¹ * ∑ b, x b)) ≤
      ∑ b, Real.exp (- x b) := by
  set N : ℝ := (Fintype.card β : ℝ)
  have hN : 0 < N := by simp [N, Fintype.card_pos]
  set m := N⁻¹ * ∑ b, x b with hm
  have h : ∀ b, Real.exp (-m) * (1 + (m - x b)) ≤ Real.exp (- x b) := by
    intro b
    have := Real.add_one_le_exp (m - x b)
    have e : Real.exp (- x b) = Real.exp (-m) * Real.exp (m - x b) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  calc N * Real.exp (-m) = ∑ b : β, Real.exp (-m) * (1 + (m - x b)) := by
        simp only [mul_add, sum_add_distrib, mul_sub, sum_sub_distrib, mul_one, ← mul_sum, sum_const,
          card_univ, nsmul_eq_mul]
        have : m * N = ∑ b, x b := by rw [hm]; field_simp
        have e2 : N * Real.exp (-m) * m = Real.exp (-m) * ∑ b, x b := by rw [← this]; ring
        linear_combination -e2
    _ ≤ _ := sum_le_sum fun b _ => h b

/-- Support for blueprint P1–P3. -/
theorem Yy_ge (s : ℝ) (u : PC l (Nm t) → ℝ) (e : ℕ) : ∀ (j : ℕ) (a : Nm t),
    ((2 : ℝ) ^ t / 18) ^ e * Real.exp (- TT t e j a u) ≤ Yy s e j a u := by
  induction e with
  | zero => intro j a; simp [TT, Yy]
  | succ e ih =>
    intro j a
    have hN : Nonempty (Nm t) := ⟨⟨0, by simp [mValue]⟩⟩
    have hc := card_Nm t
    have hstep : ∀ b, (1 / 18) * ((2 : ℝ) ^ t / 18) ^ e * ((2 : ℝ) ^ t)⁻¹ *
        Real.exp (-(ττ t u j a b + TT t e (j + 1) b u)) ≤
        H t b a * psiS (Uc u j a) * dphi (Vc (H t) u j b) * (ww t a b * Yy s e (j + 1) b u) := by
      intro b
      have h1 := psi_dphi_ge (Uc u j a) (Vc (H t) u j b)
      have h2 := ih (j + 1) b
      have e1 : H t b a * psiS (Uc u j a) * dphi (Vc (H t) u j b) * (ww t a b * Yy s e (j + 1) b u) =
          (H t b a * ww t a b) * (psiS (Uc u j a) * dphi (Vc (H t) u j b)) * Yy s e (j + 1) b u := by
        ring
      rw [e1, H_mul_ww]
      have e2 : Real.exp (-(ττ t u j a b + TT t e (j + 1) b u)) =
          Real.exp (-((Uc u j a ^ 2 - 1) / 6 + 5 / 6 * (Vc (H t) u j b ^ 2 - 1))) *
            Real.exp (- TT t e (j + 1) b u) := by
        rw [← Real.exp_add]; congr 1; simp only [ττ]; ring
      rw [e2]
      have hp : (0 : ℝ) ≤ ((2 : ℝ) ^ t)⁻¹ := by positivity
      have hA : (0 : ℝ) ≤ Real.exp (-((Uc u j a ^ 2 - 1) / 6 + 5 / 6 * (Vc (H t) u j b ^ 2 - 1))) :=
        (Real.exp_pos _).le
      have hB : (0 : ℝ) ≤ ((2 : ℝ) ^ t / 18) ^ e * Real.exp (- TT t e (j + 1) b u) := by positivity
      calc _ = ((2 : ℝ) ^ t)⁻¹ * ((1 / 18) * Real.exp (-((Uc u j a ^ 2 - 1) / 6 +
              5 / 6 * (Vc (H t) u j b ^ 2 - 1)))) *
            (((2 : ℝ) ^ t / 18) ^ e * Real.exp (- TT t e (j + 1) b u)) := by ring
        _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h1 hp) h2 hB
            (mul_nonneg hp (mul_pos (psiS_pos _) (dphi_pos _)).le)
    have hJ := sum_exp_neg_ge (β := Nm t) fun b => ττ t u j a b + TT t e (j + 1) b u
    rw [hc] at hJ
    simp only [Yy, TT]
    refine le_trans ?_ (sum_le_sum fun b _ => hstep b)
    rw [← mul_sum]
    have ht2 : (2 : ℝ) ^ (2 * t) = (2 : ℝ) ^ t * (2 : ℝ) ^ t := by rw [two_mul, pow_add]
    have hK : (0 : ℝ) ≤ (1 / 18) * ((2 : ℝ) ^ t / 18) ^ e * ((2 : ℝ) ^ t)⁻¹ := by positivity
    have h := mul_le_mul_of_nonneg_left hJ hK
    refine le_trans (le_of_eq ?_) h
    rw [pow_succ, ht2]
    field_simp

/-! ## The exponents have mean zero -/

/-- Support for blueprint P1–P3. -/
theorem Uc_eq_dot {j : ℕ} (hj : j < l) (a : Nm t) (u : PC l (Nm t) → ℝ) :
    Uc u j a = ∑ q : PC l (Nm t), (if q = (⟨j, hj⟩, a) then (1 : ℝ) else 0) * u q := by
  simp [Uc, hj]

/-- Support for blueprint P1–P3. -/
theorem integrable_Uc_sq {j : ℕ} (hj : j < l) (a : Nm t) :
    Integrable (fun u : PC l (Nm t) → ℝ => Uc u j a ^ 2) (gP (PC l (Nm t))) := by
  simp only [Uc_eq_dot hj]
  exact integrable_dot_sq _

/-- Support for blueprint P1–P3. -/
theorem integral_Uc_sq {j : ℕ} (hj : j < l) (a : Nm t) :
    ∫ u : PC l (Nm t) → ℝ, Uc u j a ^ 2 ∂(gP (PC l (Nm t))) = 1 := by
  simp only [Uc_eq_dot hj]
  exact integral_dot_sq _ (by simp)

/-- Support for blueprint P1–P3. -/
theorem integrable_Vc_sq {j : ℕ} (hj : j < l) (a : Nm t) :
    Integrable (fun u : PC l (Nm t) → ℝ => Vc (H t) u j a ^ 2) (gP (PC l (Nm t))) := by
  simp only [← sum_eV_mul (H t) hj]
  exact integrable_dot_sq _

/-- Support for blueprint P1–P3. -/
theorem integral_Vc_sq {j : ℕ} (hj : j < l) (a : Nm t) :
    ∫ u : PC l (Nm t) → ℝ, Vc (H t) u j a ^ 2 ∂(gP (PC l (Nm t))) = 1 := by
  simp only [← sum_eV_mul (H t) hj]
  exact integral_dot_sq _ (sum_eV_sq (H t) hj (rowsOrth_H t) a)

/-- Support for blueprint P1–P3. -/
theorem integrable_ττ {j : ℕ} (hj : j < l) (a b : Nm t) :
    Integrable (fun u : PC l (Nm t) → ℝ => ττ t u j a b) (gP (PC l (Nm t))) :=
  (((integrable_Uc_sq hj a).sub (integrable_const 1)).div_const 6).add
    (((integrable_Vc_sq hj b).sub (integrable_const 1)).const_mul (5 / 6))

/-- Support for blueprint P1–P3. -/
theorem integral_ττ {j : ℕ} (hj : j < l) (a b : Nm t) :
    ∫ u : PC l (Nm t) → ℝ, ττ t u j a b ∂(gP (PC l (Nm t))) = 0 := by
  unfold ττ
  have i3 : Integrable (fun u : PC l (Nm t) → ℝ => Uc u j a ^ 2 - 1) (gP (PC l (Nm t))) :=
    (integrable_Uc_sq hj a).sub (integrable_const 1)
  have i4 : Integrable (fun u : PC l (Nm t) → ℝ => Vc (H t) u j b ^ 2 - 1) (gP (PC l (Nm t))) :=
    (integrable_Vc_sq hj b).sub (integrable_const 1)
  have i1 : Integrable (fun u : PC l (Nm t) → ℝ => (Uc u j a ^ 2 - 1) / 6) (gP (PC l (Nm t))) :=
    i3.div_const 6
  have i2 : Integrable (fun u : PC l (Nm t) → ℝ => 5 / 6 * (Vc (H t) u j b ^ 2 - 1))
      (gP (PC l (Nm t))) := i4.const_mul _
  rw [integral_add i1 i2, integral_div, integral_const_mul,
    integral_sub (integrable_Uc_sq hj a) (integrable_const 1),
    integral_sub (integrable_Vc_sq hj b) (integrable_const 1), integral_Uc_sq hj,
    integral_Vc_sq hj]
  simp

/-- Support for blueprint P1–P3. -/
theorem integrable_TT (e : ℕ) : ∀ (j : ℕ), j + e ≤ l → ∀ a : Nm t,
    Integrable (TT t e j a : (PC l (Nm t) → ℝ) → ℝ) (gP (PC l (Nm t))) := by
  induction e with
  | zero => intro j _ a; exact integrable_zero _ _ _
  | succ e ih =>
    intro j hj a
    have hjl : j < l := by omega
    have hi : ∀ b ∈ (univ : Finset (Nm t)), Integrable
        (fun u : PC l (Nm t) → ℝ => ττ t u j a b + TT t e (j + 1) b u) (gP (PC l (Nm t))) :=
      fun b _ => (integrable_ττ hjl a b).add (ih (j + 1) (by omega) b)
    exact (integrable_finsetSum _ hi).const_mul _

/-- Support for blueprint P1–P3. -/
theorem integral_TT (e : ℕ) : ∀ (j : ℕ), j + e ≤ l → ∀ a : Nm t,
    ∫ u : PC l (Nm t) → ℝ, TT t e j a u ∂(gP (PC l (Nm t))) = 0 := by
  induction e with
  | zero => intro j _ a; simp [TT]
  | succ e ih =>
    intro j hj a
    have hjl : j < l := by omega
    have hj' : j + 1 + e ≤ l := by omega
    have hi : ∀ b ∈ (univ : Finset (Nm t)), Integrable
        (fun u : PC l (Nm t) → ℝ => ττ t u j a b + TT t e (j + 1) b u) (gP (PC l (Nm t))) :=
      fun b _ => (integrable_ττ hjl a b).add (integrable_TT e (j + 1) hj' b)
    simp only [TT]
    rw [integral_const_mul, integral_finsetSum _ hi]
    have : ∀ b : Nm t, ∫ u : PC l (Nm t) → ℝ, (ττ t u j a b + TT t e (j + 1) b u)
        ∂(gP (PC l (Nm t))) = 0 := fun b => by
      rw [integral_add (integrable_ττ hjl a b) (integrable_TT e (j + 1) hj' b),
        integral_ττ hjl, ih (j + 1) hj', add_zero]
    simp [this]

/-! ## P2, P3 -/

/-- `Φ`, with its denominator. -/
noncomputable def PhiF (t : ℕ) (z : BC l (Nm t) → Bool) : ℝ :=
  Fz t z / ((2 : ℝ) ^ (2 * t) * ((2 : ℝ) ^ t) ^ l)

/-- Support for blueprint P1–P3. -/
theorem Phi_eq_PhiF (z : BC l (Nm t) → Bool) : Phi (l + 1) t z = PhiF t z := by
  unfold Phi PhiF
  rw [numerator_eq_Fz, denom_cast]

/-- Support for blueprint P1–P3. -/
theorem PhiF_eq_lin : (PhiF t : (BC l (Nm t) → Bool) → ℝ) =
    lin (fun a => cn 0 a) (fun _ => ((2 : ℝ) ^ (2 * t) * ((2 : ℝ) ^ t) ^ l)⁻¹) (Rs t l 0) := by
  funext z
  simp only [PhiF, Fz, lin, div_eq_inv_mul, one_mul, mul_sum]
  exact sum_congr rfl fun a _ => by ring

/-- Support for blueprint P1–P3. -/
theorem Rs_update_cn {b : Nm t} {e j : ℕ} (hle : j + e ≤ l) (a : Nm t) (z : BC l (Nm t) → Bool)
    (x : Bool) : Rs t e j a (Function.update z (cn j b) x) = Rs t e j a z :=
  Rs_update hle a z _ (by rw [cn_val_of_le (by omega)]) x

/-- P2. The hard distribution has large Forrelation. -/
theorem mass_ge (hl : 0 < l) :
    (1 / 18 : ℝ) ^ l ≤
      ∫ u, ext (PhiF t : (BC l (Nm t) → Bool) → ℝ) (wv (H t) 1 u) ∂(gP (PC l (Nm t))) -
        ext (PhiF t : (BC l (Nm t) → Bool) → ℝ) 0 := by
  obtain ⟨s, hs, hid⟩ := exists_identity (H t) hl (PhiF t : (BC l (Nm t) → Bool) → ℝ)
  rw [integral_ext_wv_zero (H t) (rowsOrth_H t)] at hid
  rw [hid]
  have hs1 : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2.le⟩
  set K : ℝ := ((2 : ℝ) ^ (2 * t) * ((2 : ℝ) ^ t) ^ l)⁻¹ with hK
  have hK0 : 0 ≤ K := by positivity
  set cc : ℝ := ((2 : ℝ) ^ t / 18) ^ l with hcc
  have hcc0 : 0 ≤ cc := by positivity
  have hD : ∀ a : Nm t, D (cn 0 a) (PhiF t : (BC l (Nm t) → Bool) → ℝ) =
      fun z => K * Rs t l 0 a z := by
    intro a
    rw [PhiF_eq_lin]
    exact D_lin (c := fun a : Nm t => (cn 0 a : BC l (Nm t))) _ (Rs t l 0) (cn_inj 0)
      (fun b b' z x => Rs_update_cn (e := l) (j := 0) (by omega) b z x) a
  have hone : ∀ a : Nm t, K * cc ≤ ∫ u, Int (H t) s l 0 a (D (cn 0 a) (PhiF t)) u
      ∂(gP (PC l (Nm t))) := by
    intro a
    have hmono : ∫ u : PC l (Nm t) → ℝ, K * cc * (1 - TT t l 0 a u) ∂(gP (PC l (Nm t))) ≤
        ∫ u, Int (H t) s l 0 a (D (cn 0 a) (PhiF t)) u ∂(gP (PC l (Nm t))) := by
      refine integral_mono (((integrable_const 1).sub (integrable_TT l 0 (by omega) a)).const_mul _)
        (bcf_Int (H t) hs1 l 0 a _).integrable fun u => ?_
      simp only [hD]
      rw [Int_Rs s u l 0 (by omega) a K]
      have h1 := Yy_ge s u l 0 a
      have h2 := Real.add_one_le_exp (- TT t l 0 a u)
      have h3 : cc * (1 - TT t l 0 a u) ≤ Yy s l 0 a u := by
        refine le_trans (mul_le_mul_of_nonneg_left (by linarith) hcc0) h1
      calc _ = K * (cc * (1 - TT t l 0 a u)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 hK0
    have e : ∫ u : PC l (Nm t) → ℝ, K * cc * (1 - TT t l 0 a u) ∂(gP (PC l (Nm t))) = K * cc := by
      rw [integral_const_mul, integral_sub (integrable_const 1) (integrable_TT l 0 (by omega) a),
        integral_TT l 0 (by omega)]
      simp
    rwa [e] at hmono
  have hsum := sum_le_sum fun a (_ : a ∈ (univ : Finset (Nm t))) => hone a
  refine le_trans (le_of_eq ?_) hsum
  rw [sum_const, card_univ, nsmul_eq_mul, card_Nm, hK, hcc]
  have h2 : ((2 : ℝ) ^ t) ≠ 0 := by positivity
  rw [div_pow, div_pow, one_pow]
  field_simp

/-- Support for blueprint P1–P3. -/
theorem ext_Rs_sq (e : ℕ) : ∀ (j : ℕ), j + e ≤ l → ∀ a : Nm t,
    ext (fun z : BC l (Nm t) → Bool => Rs t e j a z ^ 2) 0 = ((2 : ℝ) ^ (2 * t)) ^ e := by
  induction e with
  | zero => intro j _ a; simpa [Rs] using ext_const 1 _
  | succ e ih =>
    intro j hj a
    simp only [Rs]
    rw [ext_lin_sq_zero _ _ (cn_inj (j + 1))
      (fun b b' z x => Rs_update_cn (b := b') (e := e) (j := j + 1) (by omega) b z x)]
    simp only [ww_sq, one_mul, ih (j + 1) (by omega)]
    rw [sum_const, card_univ, nsmul_eq_mul, card_Nm, pow_succ]
    ring

/-- Support for blueprint P1–P3. -/
theorem ext_PhiF_zero : ext (PhiF t : (BC l (Nm t) → Bool) → ℝ) 0 = 0 := by
  rw [PhiF_eq_lin]
  exact ext_lin_zero _ _ fun b b' z x => Rs_update_cn (e := l) (j := 0) (by omega) b z x

/-- P3. Parseval on the uniform measure. -/
theorem ext_PhiF_sq (l t : ℕ) :
    ext (fun z : BC l (Nm t) → Bool => PhiF t z ^ 2) 0 = ((2 : ℝ) ^ (2 * t))⁻¹ := by
  rw [PhiF_eq_lin]
  rw [ext_lin_sq_zero _ _ (cn_inj 0)
    (fun b b' z x => Rs_update_cn (e := l) (j := 0) (by omega) b z x)]
  simp only [ext_Rs_sq (l := l) (t := t) l 0 (by omega)]
  rw [sum_const, card_univ, nsmul_eq_mul, card_Nm]
  have h2 : ((2 : ℝ) ^ t) ≠ 0 := by positivity
  have ht : (2 : ℝ) ^ (2 * t) = (2 : ℝ) ^ t * (2 : ℝ) ^ t := by rw [two_mul, pow_add]
  simp only [ht, mul_pow]
  field_simp

end QuarticQuery.ForrelationLower
