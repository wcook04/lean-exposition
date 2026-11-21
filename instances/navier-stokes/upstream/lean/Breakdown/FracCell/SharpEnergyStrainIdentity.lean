import Breakdown.FracCell.SharpYSharpEnergyTail
import Breakdown.FracCell.SharpCoefTail
import Breakdown.FracCell.MeshFarPoly
import Breakdown.FracCell.AngularFrame
import Breakdown.FracCell.CircleWeak
import Breakdown.FracCell.EnergyDefs
import Breakdown.FracCell.ModeSquareIntegrable
import Breakdown.FracCell.ModeRadialPartsA
import Breakdown.FracCell.ModeHeightParts
import Breakdown.FracCell.ModeGradSquare

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellAnalysis

namespace SharpEnergyStrainIdentityInternal

open CellEnergy SteadyCert Assembly

def turnOp (x : Fin 3 → Fin 3 → ℂ) (a b : Fin 3) : ℂ :=
  -(∑ b' : Fin 3, (frameTurn b' b : ℂ) * x a b') - ∑ a' : Fin 3, (frameTurn a' a : ℂ) * x a' b

lemma comb_eq (k : ℝ) (c : Fin 3 → Fin 3 → ℂ) (a b : Fin 3) :
    ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb k a b a' b' * c a' b' = Complex.I * k * c a b + turnOp c a b := by
  fin_cases a <;> fin_cases b <;> simp [angularComb, turnOp, frameTurn, Fin.sum_univ_three] <;> ring

lemma sq_ge (k : ℝ) (x w : ℂ) : k ^ 2 * ‖x‖ ^ 2 + ‖w‖ ^ 2 - 2 * |k| * (‖x‖ * ‖w‖) ≤ ‖Complex.I * k * x + w‖ ^ 2 := by
  have h1 : ‖Complex.I * k * x‖ = |k| * ‖x‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
  have h2 : ‖Complex.I * k * x‖ - ‖w‖ ≤ ‖Complex.I * k * x + w‖ := by
    have := norm_sub_norm_le (Complex.I * k * x) (-w)
    simpa [sub_neg_eq_add] using this
  have h3 : ‖w‖ - ‖Complex.I * k * x‖ ≤ ‖Complex.I * k * x + w‖ := by
    have := norm_sub_norm_le w (-(Complex.I * k * x))
    rw [sub_neg_eq_add, add_comm, norm_neg] at this
    exact this
  have h4 : (|k| * ‖x‖ - ‖w‖) ^ 2 ≤ ‖Complex.I * k * x + w‖ ^ 2 := by
    rw [← h1]
    apply sq_le_sq'
    · linarith
    · exact h2
  have hk : |k| ^ 2 = k ^ 2 := sq_abs k
  nlinarith [h4]

lemma sum_ge (k : ℝ) (x w : Fin 3 → Fin 3 → ℂ) :
    k ^ 2 * (∑ a : Fin 3, ∑ b : Fin 3, ‖x a b‖ ^ 2) + (∑ a : Fin 3, ∑ b : Fin 3, ‖w a b‖ ^ 2)
      - 2 * |k| * (∑ a : Fin 3, ∑ b : Fin 3, ‖x a b‖ * ‖w a b‖)
      ≤ ∑ a : Fin 3, ∑ b : Fin 3, ‖Complex.I * k * x a b + w a b‖ ^ 2 := by
  have h := fun a b => sq_ge k (x a b) (w a b)
  simp only [Fin.sum_univ_three] at *
  linarith [h 0 0, h 0 1, h 0 2, h 1 0, h 1 1, h 1 2, h 2 0, h 2 1, h 2 2]

lemma sum_prod_sq_le (x w : Fin 3 → Fin 3 → ℂ) :
    (∑ a : Fin 3, ∑ b : Fin 3, ‖x a b‖ * ‖w a b‖) ^ 2
      ≤ (∑ a : Fin 3, ∑ b : Fin 3, ‖x a b‖ ^ 2) * (∑ a : Fin 3, ∑ b : Fin 3, ‖w a b‖ ^ 2) := by
  have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3 × Fin 3))
    (fun p => ‖x p.1 p.2‖) (fun p => ‖w p.1 p.2‖)
  simpa [Fintype.sum_prod_type] using this

lemma final (k C X Y Z P : ℝ) (hC : 0 ≤ C) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hPXY : P ^ 2 ≤ X * Y)
    (hYC : Y ≤ C ^ 2 * X) (hZ : k ^ 2 * X + Y - 2 * |k| * P ≤ Z) :
    (max (|k| - C) 0) ^ 2 * X ≤ Z := by
  have hZ0 : 0 ≤ Z := by
    have hk : |k| ^ 2 = k ^ 2 := sq_abs k
    have : P ≤ Real.sqrt X * Real.sqrt Y := by
      rw [← Real.sqrt_mul hX]; exact Real.le_sqrt_of_sq_le hPXY
    have hsx := Real.sq_sqrt hX
    have hsy := Real.sq_sqrt hY
    nlinarith [sq_nonneg (|k| * Real.sqrt X - Real.sqrt Y), abs_nonneg k, Real.sqrt_nonneg X, Real.sqrt_nonneg Y]
  rcases le_or_gt (|k|) C with h | h
  · rw [max_eq_right (by linarith)]; simpa using hZ0
  · rw [max_eq_left (by linarith)]
    have hk : |k| ^ 2 = k ^ 2 := sq_abs k
    have hsx := Real.sq_sqrt hX
    have hsy := Real.sq_sqrt hY
    have hPs : P ≤ Real.sqrt X * Real.sqrt Y := by
      rw [← Real.sqrt_mul hX]; exact Real.le_sqrt_of_sq_le hPXY
    have hyc : Real.sqrt Y ≤ C * Real.sqrt X := by
      rw [show C * Real.sqrt X = Real.sqrt (C ^ 2 * X) by
        rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]]
      exact Real.sqrt_le_sqrt hYC
    have e1 : 0 ≤ (|k| - C) * Real.sqrt X := mul_nonneg (by linarith) (Real.sqrt_nonneg X)
    have e2 : (|k| - C) * Real.sqrt X ≤ |k| * Real.sqrt X - Real.sqrt Y := by nlinarith
    have e3 : ((|k| - C) * Real.sqrt X) ^ 2 ≤ (|k| * Real.sqrt X - Real.sqrt Y) ^ 2 := pow_le_pow_left₀ e1 e2 2
    have e4 : ((|k| - C) * Real.sqrt X) ^ 2 = (|k| - C) ^ 2 * X := by rw [mul_pow, hsx]
    nlinarith [abs_nonneg k, Real.sqrt_nonneg X, Real.sqrt_nonneg Y]

lemma turn_sym (s : Fin 3 → Fin 3 → ℂ) (hs : ∀ a b, s a b = s b a) :
    ∑ a : Fin 3, ∑ b : Fin 3, ‖turnOp s a b‖ ^ 2 ≤ 2 ^ 2 * ∑ a : Fin 3, ∑ b : Fin 3, ‖s a b‖ ^ 2 := by
  simp only [turnOp, Fin.sum_univ_three, frameTurn]
  simp
  rw [hs 1 0, hs 2 0, hs 2 1]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.neg_re, Complex.neg_im]
  nlinarith [sq_nonneg ((s 0 0).re + (s 1 1).re), sq_nonneg ((s 0 0).im + (s 1 1).im),
    sq_nonneg (s 2 2).re, sq_nonneg (s 2 2).im, sq_nonneg (s 0 2).re, sq_nonneg (s 0 2).im,
    sq_nonneg (s 1 2).re, sq_nonneg (s 1 2).im, sq_nonneg (s 0 1).re, sq_nonneg (s 0 1).im]

lemma turn_anti (t : Fin 3 → Fin 3 → ℂ) (ht : ∀ a b, t a b = -t b a) :
    ∑ a : Fin 3, ∑ b : Fin 3, ‖turnOp t a b‖ ^ 2 ≤ 1 ^ 2 * ∑ a : Fin 3, ∑ b : Fin 3, ‖t a b‖ ^ 2 := by
  have h00 : t 0 0 = 0 := by have := ht 0 0; linear_combination this / 2
  have h11 : t 1 1 = 0 := by have := ht 1 1; linear_combination this / 2
  have h22 : t 2 2 = 0 := by have := ht 2 2; linear_combination this / 2
  simp only [turnOp, Fin.sum_univ_three, frameTurn]
  simp
  rw [ht 1 0, ht 2 0, ht 2 1, h00, h11, h22]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.zero_re, Complex.zero_im]
  nlinarith [sq_nonneg (t 0 1).re, sq_nonneg (t 0 1).im, sq_nonneg (t 0 2).re, sq_nonneg (t 0 2).im,
    sq_nonneg (t 1 2).re, sq_nonneg (t 1 2).im]

lemma sym_part (k : ℝ) (c : Fin 3 → Fin 3 → ℂ) (a b : Fin 3) :
    ((Complex.I * k * c a b + turnOp c a b) + (Complex.I * k * c b a + turnOp c b a)) / 2
      = Complex.I * k * ((c a b + c b a) / 2) + turnOp (fun a b => (c a b + c b a) / 2) a b := by
  fin_cases a <;> fin_cases b <;> simp [turnOp, frameTurn, Fin.sum_univ_three] <;> ring

lemma anti_part (k : ℝ) (c : Fin 3 → Fin 3 → ℂ) (a b : Fin 3) :
    ((Complex.I * k * c a b + turnOp c a b) - (Complex.I * k * c b a + turnOp c b a)) / 2
      = Complex.I * k * ((c a b - c b a) / 2) + turnOp (fun a b => (c a b - c b a) / 2) a b := by
  fin_cases a <;> fin_cases b <;> simp [turnOp, frameTurn, Fin.sum_univ_three] <;> ring

lemma split_sq (s : Fin 3 → Fin 3 → ℂ) : symSq s + antiSq s = sumSq s := by
  have h : ∀ x y : ℂ, ‖(x + y) / 2‖ ^ 2 + ‖(x - y) / 2‖ ^ 2 = (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
    intro x y
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.div_re, Complex.div_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
    norm_num
    ring
  unfold symSq antiSq sumSq
  rw [← Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib, h]
  simp only [Fin.sum_univ_three]
  ring

lemma comb_bound (k : ℝ) (c : Fin 3 → Fin 3 → ℂ) :
    (max (|k| - 2) 0) ^ 2 * symSq c + (max (|k| - 1) 0) ^ 2 * antiSq c
      ≤ ∑ a : Fin 3, ∑ b : Fin 3, ‖∑ a' : Fin 3, ∑ b' : Fin 3, angularComb k a b a' b' * c a' b'‖ ^ 2 := by
  set L : Fin 3 → Fin 3 → ℂ := fun a b => ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb k a b a' b' * c a' b' with hL
  have hL' : ∀ a b, L a b = Complex.I * k * c a b + turnOp c a b := fun a b => comb_eq k c a b
  set s : Fin 3 → Fin 3 → ℂ := fun a b => (c a b + c b a) / 2 with hs
  set t : Fin 3 → Fin 3 → ℂ := fun a b => (c a b - c b a) / 2 with ht
  have e1 : symSq L = ∑ a : Fin 3, ∑ b : Fin 3, ‖Complex.I * k * s a b + turnOp s a b‖ ^ 2 := by
    unfold symSq
    simp only [hL', sym_part k c]
    rfl
  have e2 : antiSq L = ∑ a : Fin 3, ∑ b : Fin 3, ‖Complex.I * k * t a b + turnOp t a b‖ ^ 2 := by
    unfold antiSq
    simp only [hL', anti_part k c]
    rfl
  have hsym : ∀ a b, s a b = s b a := fun a b => by simp only [hs]; ring
  have hanti : ∀ a b, t a b = -t b a := fun a b => by simp only [ht]; ring
  have f1 : (max (|k| - 2) 0) ^ 2 * symSq c ≤ symSq L := by
    rw [e1]
    have hX : symSq c = ∑ a : Fin 3, ∑ b : Fin 3, ‖s a b‖ ^ 2 := rfl
    rw [hX]
    exact final k 2 _ _ _ _ (by norm_num) (by positivity) (by positivity) (sum_prod_sq_le s (turnOp s))
      (turn_sym s hsym) (sum_ge k s (turnOp s))
  have f2 : (max (|k| - 1) 0) ^ 2 * antiSq c ≤ antiSq L := by
    rw [e2]
    have hX : antiSq c = ∑ a : Fin 3, ∑ b : Fin 3, ‖t a b‖ ^ 2 := rfl
    rw [hX]
    exact final k 1 _ _ _ _ (by norm_num) (by positivity) (by positivity) (sum_prod_sq_le t (turnOp t))
      (turn_anti t hanti) (sum_ge k t (turnOp t))
  have e3 := split_sq L
  unfold sumSq at e3
  linarith


open Classical in
lemma assemble (I : ℕ × ℕ → Prop) (cf : Fin 3 → Fin 3 → ℕ × ℕ → ℂ) (lam : ℕ × ℕ → ℝ) (hlam : ∀ jl, 0 ≤ lam jl)
    (w k : ℝ) (hw : 0 ≤ w) (RG RA : Fin 3 → Fin 3 → ℝ)
    (hG : ∀ a b, Summable (fun jl => if I jl then lam jl * ‖cf a b jl‖ ^ 2 else 0) ∧
      (∑' jl, if I jl then lam jl * ‖cf a b jl‖ ^ 2 else 0) ≤ RG a b)
    (hA : ∀ a b, Summable (fun jl => if I jl then
        ‖∑ a' : Fin 3, ∑ b' : Fin 3, angularComb k a b a' b' * cf a' b' jl‖ ^ 2 else 0) ∧
      (∑' jl, if I jl then ‖∑ a' : Fin 3, ∑ b' : Fin 3, angularComb k a b a' b' * cf a' b' jl‖ ^ 2 else 0)
        ≤ RA a b) :
    Summable (fun jl => if I jl then (lam jl + w * (max (|k| - 2) 0) ^ 2) * symSq (fun a b => cf a b jl) else 0) ∧
    Summable (fun jl => if I jl then (lam jl + w * (max (|k| - 1) 0) ^ 2) * antiSq (fun a b => cf a b jl) else 0) ∧
    (∑' jl, if I jl then (lam jl + w * (max (|k| - 2) 0) ^ 2) * symSq (fun a b => cf a b jl) else 0)
      + (∑' jl, if I jl then (lam jl + w * (max (|k| - 1) 0) ^ 2) * antiSq (fun a b => cf a b jl) else 0)
      ≤ ∑ a : Fin 3, ∑ b : Fin 3, (RG a b + w * RA a b) := by
  set f1 : ℕ × ℕ → ℝ := fun jl => if I jl then (lam jl + w * (max (|k| - 2) 0) ^ 2) * symSq (fun a b => cf a b jl)
    else 0 with hf1
  set f2 : ℕ × ℕ → ℝ := fun jl => if I jl then (lam jl + w * (max (|k| - 1) 0) ^ 2) * antiSq (fun a b => cf a b jl)
    else 0 with hf2
  set gG : Fin 3 → Fin 3 → ℕ × ℕ → ℝ := fun a b jl => if I jl then lam jl * ‖cf a b jl‖ ^ 2 else 0 with hgG
  set gA : Fin 3 → Fin 3 → ℕ × ℕ → ℝ := fun a b jl => if I jl then
    ‖∑ a' : Fin 3, ∑ b' : Fin 3, angularComb k a b a' b' * cf a' b' jl‖ ^ 2 else 0 with hgA
  set g : ℕ × ℕ → ℝ := fun jl => ∑ a : Fin 3, ∑ b : Fin 3, (gG a b jl + w * gA a b jl) with hg
  have hsG : ∀ a b, Summable (gG a b) := fun a b => (hG a b).1
  have hsA : ∀ a b, Summable (gA a b) := fun a b => (hA a b).1
  have hsum : Summable g := summable_sum fun a _ => summable_sum fun b _ => (hsG a b).add ((hsA a b).mul_left w)
  have hsymn : ∀ s : Fin 3 → Fin 3 → ℂ, 0 ≤ symSq s := fun s => by unfold symSq; positivity
  have hantin : ∀ s : Fin 3 → Fin 3 → ℂ, 0 ≤ antiSq s := fun s => by unfold antiSq; positivity
  have f1n : ∀ jl, 0 ≤ f1 jl := fun jl => by
    simp only [hf1]; split_ifs
    · exact mul_nonneg (add_nonneg (hlam jl) (mul_nonneg hw (sq_nonneg _))) (hsymn _)
    · exact le_rfl
  have f2n : ∀ jl, 0 ≤ f2 jl := fun jl => by
    simp only [hf2]; split_ifs
    · exact mul_nonneg (add_nonneg (hlam jl) (mul_nonneg hw (sq_nonneg _))) (hantin _)
    · exact le_rfl
  have hle : ∀ jl, f1 jl + f2 jl ≤ g jl := by
    intro jl
    by_cases hI : I jl
    · have e1 : f1 jl = (lam jl + w * (max (|k| - 2) 0) ^ 2) * symSq (fun a b => cf a b jl) := if_pos hI
      have e2 : f2 jl = (lam jl + w * (max (|k| - 1) 0) ^ 2) * antiSq (fun a b => cf a b jl) := if_pos hI
      have e3 : g jl = lam jl * sumSq (fun a b => cf a b jl)
          + w * ∑ a : Fin 3, ∑ b : Fin 3, ‖∑ a' : Fin 3, ∑ b' : Fin 3, angularComb k a b a' b' * cf a' b' jl‖ ^ 2 := by
        simp only [hg, hgG, hgA, if_pos hI, sumSq, Fin.sum_univ_three]
        ring
      have hsp := split_sq (fun a b => cf a b jl)
      have hcb := comb_bound k (fun a b => cf a b jl)
      rw [e1, e2, e3, ← hsp]
      nlinarith [mul_le_mul_of_nonneg_left hcb hw]
    · have e1 : f1 jl = 0 := if_neg hI
      have e2 : f2 jl = 0 := if_neg hI
      have e3 : g jl = 0 := by simp [hg, hgG, hgA, if_neg hI]
      rw [e1, e2, e3]; simp
  have hs1 : Summable f1 := Summable.of_nonneg_of_le f1n (fun jl => by linarith [hle jl, f2n jl]) hsum
  have hs2 : Summable f2 := Summable.of_nonneg_of_le f2n (fun jl => by linarith [hle jl, f1n jl]) hsum
  refine ⟨hs1, hs2, ?_⟩
  rw [← hs1.tsum_add hs2]
  refine ((hs1.add hs2).tsum_le_tsum hle hsum).trans ?_
  have et : ∑' jl, g jl = ∑ a : Fin 3, ∑ b : Fin 3, ((∑' jl, gG a b jl) + w * ∑' jl, gA a b jl) := by
    rw [hg, Summable.tsum_finsetSum fun a _ => summable_sum fun b _ => (hsG a b).add ((hsA a b).mul_left w)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Summable.tsum_finsetSum fun b _ => (hsG a b).add ((hsA a b).mul_left w)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [(hsG a b).tsum_add ((hsA a b).mul_left w), tsum_mul_left]
  rw [et]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  exact add_le_add (hG a b).2 (mul_le_mul_of_nonneg_left (hA a b).2 hw)


variable {K : CellBox} {B : CellBases} {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
  {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}

lemma proj_mem (K : CellBox) (Q : ℕ) (F : ℝ × ℝ → ℂ) : K.proj Q Q F ∈ polyFn Q Q := by
  unfold CellBox.proj
  split_ifs with h
  · exact h.choose_spec.1
  · exact ⟨fun _ _ => 0, fun p => by simp⟩

lemma sub_sq_int (K : CellBox) (F P : ℝ × ℝ → ℂ) (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hF2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect) (hP : Continuous P) :
    AEStronglyMeasurable (fun p => F p - P p) (volume.restrict K.rect) ∧
    IntegrableOn (fun p => K.lineWeight p.1 * ‖F p - P p‖ ^ 2) K.rect := by
  have hm : AEStronglyMeasurable (fun p => F p - P p) (volume.restrict K.rect) := hF.sub hP.aestronglyMeasurable
  refine ⟨hm, ?_⟩
  have hPi : IntegrableOn (fun p => K.lineWeight p.1 * ‖P p‖ ^ 2) K.rect :=
    (((CellSharpBoundInternal.lw_cont K).comp continuous_fst).mul (hP.norm.pow 2)).continuousOn.integrableOn_compact
      (CellSharpBoundInternal.rect_cpt K)
  refine Integrable.mono' ((hF2.add hPi).const_mul 2)
    ((((CellSharpBoundInternal.lw_cont K).comp continuous_fst).aestronglyMeasurable).mul (hm.norm.pow 2)) ?_
  refine (ae_restrict_iff' (CellSharpBoundInternal.rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
  have hw := CellSharpBoundInternal.lw_nonneg (K := K) hp.1.1
  rw [Real.norm_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  have h1 : ‖F p - P p‖ ≤ ‖F p‖ + ‖P p‖ := norm_sub_le _ _
  have h2 : ‖F p - P p‖ ^ 2 ≤ 2 * ‖F p‖ ^ 2 + 2 * ‖P p‖ ^ 2 := by
    nlinarith [norm_nonneg (F p - P p), norm_nonneg (F p), norm_nonneg (P p), sq_nonneg (‖F p‖ - ‖P p‖)]
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left h2 hw]

lemma coefSq_full {K : CellBox} {B : CellBases} (hB : IsCellBases K B) (F : ℝ × ℝ → ℂ)
    (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hF2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect) :
    Summable (fun jl : ℕ × ℕ => ‖B.coef K F jl.1 jl.2‖ ^ 2) ∧
    (∑' jl : ℕ × ℕ, ‖B.coef K F jl.1 jl.2‖ ^ 2) ≤ K.normSqOn K.lineWeightFn F := by
  have hs := CellSharpBoundInternal.coef_summable hB F hF hF2
  exact ⟨hs, hs.tsum_le_of_sum_le (CellSharpBoundInternal.coefEnergy_fin hB F hF hF2)⟩

lemma coefSq_tail {K : CellBox} {B : CellBases} (hB : IsCellBases K B) (Q : ℕ) (F : ℝ × ℝ → ℂ)
    (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hF2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect) :
    Summable (fun jl : ℕ × ℕ => if Q < max jl.1 jl.2 then ‖B.coef K F jl.1 jl.2‖ ^ 2 else 0) ∧
    (∑' jl : ℕ × ℕ, if Q < max jl.1 jl.2 then ‖B.coef K F jl.1 jl.2‖ ^ 2 else 0) ≤ K.tailNormSq Q F := by
  set P := K.proj Q Q F with hPdef
  have hPm := proj_mem K Q F
  have hPc : Continuous P := MeshFarPolyInternal.poly_continuous Q P hPm
  obtain ⟨hm, hi⟩ := sub_sq_int K F P hF hF2 hPc
  obtain ⟨hs, ht⟩ := coefSq_full hB (fun p => F p - P p) hm hi
  have e : ∀ jl : ℕ × ℕ, Q < max jl.1 jl.2 → B.coef K F jl.1 jl.2 = B.coef K (fun p => F p - P p) jl.1 jl.2 := by
    intro jl h
    have := MeshFarPolyInternal.coef_add_poly K B hB Q (fun p => F p - P p) P hPm jl.1 jl.2 h
    rw [← this]
    congr 1
    funext p
    ring
  have hle : ∀ jl : ℕ × ℕ, (if Q < max jl.1 jl.2 then ‖B.coef K F jl.1 jl.2‖ ^ 2 else 0)
      ≤ ‖B.coef K (fun p => F p - P p) jl.1 jl.2‖ ^ 2 := by
    intro jl
    split_ifs with h
    · rw [e jl h]
    · exact sq_nonneg _
  have hn : ∀ jl : ℕ × ℕ, 0 ≤ (if Q < max jl.1 jl.2 then ‖B.coef K F jl.1 jl.2‖ ^ 2 else 0) := by
    intro jl; split_ifs <;> positivity
  have hs' := Summable.of_nonneg_of_le hn hle hs
  exact ⟨hs', (hs'.tsum_le_tsum hle hs).trans ht⟩

lemma ang_int (hK : IsCellBox K) (hs : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3) :
    AEStronglyMeasurable (angularGradMode m n H a b) (volume.restrict K.rect) ∧
    IntegrableOn (fun p => K.lineWeight p.1 * ‖angularGradMode m n H a b p‖ ^ 2) K.rect := by
  obtain ⟨_, _, h3⟩ := modeSquareIntegrable K hK m v G H hs n (SharpCoefTailInternal.unitMat a b)
  obtain ⟨hm1, hi1⟩ := h3 1
  have eT : comboThird (SharpCoefTailInternal.unitMat a b) m n H 1 = modeThird m n H a b 1 :=
    funext (SharpCoefTailInternal.combo_third m n H a b 1)
  rw [eT] at hm1 hi1
  have he : angularGradMode m n H a b = fun p => (p.1 : ℂ) * modeThird m n H a b 1 p := rfl
  have hm : AEStronglyMeasurable (angularGradMode m n H a b) (volume.restrict K.rect) := by
    rw [he]
    exact (Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul hm1
  refine ⟨hm, ?_⟩
  refine Integrable.mono' (hi1.const_mul (max K.r₂ 1 * K.r₂))
    ((((CellSharpBoundInternal.lw_cont K).comp continuous_fst).aestronglyMeasurable).mul (hm.norm.pow 2)) ?_
  refine (ae_restrict_iff' (CellSharpBoundInternal.rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
  have hw := CellSharpBoundInternal.lw_nonneg (K := K) hp.1.1
  have hwle : K.lineWeight p.1 ≤ max K.r₂ 1 := by
    unfold CellBox.lineWeight; split_ifs
    · exact le_max_of_le_left hp.1.2
    · exact le_max_right _ _
  have hr0 : 0 ≤ p.1 := hK.r_order.1.trans hp.1.1
  have hr2 : p.1 ≤ K.r₂ := hp.1.2
  rw [Real.norm_of_nonneg (mul_nonneg hw (sq_nonneg _)), he]
  simp only
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0, mul_pow]
  have hq := sq_nonneg ‖modeThird m n H a b 1 p‖
  have hmx : 0 ≤ max K.r₂ 1 := le_max_of_le_right zero_le_one
  have k1 : K.lineWeight p.1 * p.1 ≤ max K.r₂ 1 * K.r₂ := mul_le_mul hwle hr2 hr0 hmx
  calc K.lineWeight p.1 * (p.1 ^ 2 * ‖modeThird m n H a b 1 p‖ ^ 2)
      = (K.lineWeight p.1 * p.1) * (p.1 * ‖modeThird m n H a b 1 p‖ ^ 2) := by ring
    _ ≤ (max K.r₂ 1 * K.r₂) * (p.1 * ‖modeThird m n H a b 1 p‖ ^ 2) :=
        mul_le_mul_of_nonneg_right k1 (mul_nonneg hr0 hq)

lemma tailLam_nonneg (hK : IsCellBox K) (j l : ℕ) : 0 ≤ CellScalars.tailLam K j l := by
  unfold CellScalars.tailLam
  refine mul_nonneg ?_ (add_nonneg (SharpCoefTailInternal.radialEigen_nonneg j) (SharpCoefTailInternal.heightEigen_nonneg l))
  unfold CellBox.innerRadius
  split_ifs
  · exact zero_le_one
  · exact hK.r_order.1

lemma angularWeight_nonneg (hK : IsCellBox K) (n : ℤ) : 0 ≤ K.angularWeight n := by
  unfold CellBox.angularWeight
  have h2 : 0 ≤ K.r₂ := hK.r_order.1.trans hK.r_order.2.le
  split_ifs <;> positivity

lemma radial_fin (hK : IsCellBox K) (hB : IsCellBases K B) (F Fd : ℝ × ℝ → ℂ)
    (hFd : AEStronglyMeasurable Fd (volume.restrict K.rect))
    (hFd2 : IntegrableOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) * ‖Fd p‖ ^ 2) K.rect)
    (I : ℕ × ℕ → Prop) [DecidablePred I]
    (hR : ∀ j l, I (j, l) → j ≠ 0 → ((radialEigen K j : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) : ℝ) : ℂ) * Fd p *
        ((SharpCoefTailInternal.rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) (T : Finset (ℕ × ℕ)) :
    ∑ i ∈ T, (if I i then radialEigen K i.1 * ‖B.coef K F i.1 i.2‖ ^ 2 else 0)
      ≤ ∫ p in K.rect, K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) * ‖Fd p‖ ^ 2 := by
  open SharpCoefTailInternal CellSharpBoundInternal in
  have hr := hK.r_order.2
  set W : ℝ × ℝ → ℝ := fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) with hWdef
  have hWc : Continuous W :=
    ((lw_cont K).comp continuous_fst).mul (continuous_const.sub (((refR_cont K).comp continuous_fst).pow 2))
  have hW0 : ∀ p ∈ K.rect, 0 ≤ W p := fun p hp =>
    mul_nonneg (lw_nonneg hp.1.1) (refR_sq_le hr hp.1.1 hp.1.2)
  set b : ℕ × ℕ → ℝ × ℝ → ℝ := fun i p => rd B i.1 p.1 * B.heightPoly i.2 p.2 / Real.sqrt (radialEigen K i.1)
    with hbdef
  have hbc : ∀ i, Continuous (b i) := fun i =>
    (((rd_cont B _).comp continuous_fst).mul ((hp_cont B _).comp continuous_snd)).div_const _
  set T' := T.filter (fun i => I i ∧ i.1 ≠ 0)
  have e1 : ∑ i ∈ T, (if I i then radialEigen K i.1 * ‖B.coef K F i.1 i.2‖ ^ 2 else 0)
      = ∑ i ∈ T', radialEigen K i.1 * ‖B.coef K F i.1 i.2‖ ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hI : I i
    · by_cases h0 : i.1 = 0
      · have : radialEigen K 0 = 0 := by unfold radialEigen; split_ifs <;> simp
        rw [if_pos hI, if_neg (fun h => h.2 h0), h0, this, zero_mul]
      · rw [if_pos hI, if_pos ⟨hI, h0⟩]
    · rw [if_neg hI, if_neg (fun h => hI h.1)]
  have e2 : ∀ i ∈ T', radialEigen K i.1 * ‖B.coef K F i.1 i.2‖ ^ 2
      = ‖∫ p in K.rect, (W p : ℂ) * Fd p * ((b i p : ℝ) : ℂ)‖ ^ 2 := by
    intro i hi
    have hj : i.1 ≠ 0 := (Finset.mem_filter.1 hi).2.2
    have hIi : I i := (Finset.mem_filter.1 hi).2.1
    rw [hbdef]
    simp only
    rw [int_scale K W (fun p => rd B i.1 p.1 * B.heightPoly i.2 p.2) Fd]
    exact term_eq _ (radialEigen_pos hr hj) _ _ (hR i.1 i.2 hIi hj)
  rw [e1, Finset.sum_congr rfl e2]
  refine sq_coef_le K W hWc hW0 b hbc Fd hFd hFd2 T' ?_
  intro i hi i' hi'
  have hj : i.1 ≠ 0 := (Finset.mem_filter.1 hi).2.2
  have hj' : i'.1 ≠ 0 := (Finset.mem_filter.1 hi').2.2
  have e : ∀ p : ℝ × ℝ, W p * b i p * b i' p
      = (K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) * rd B i.1 p.1 * rd B i'.1 p.1
          / (Real.sqrt (radialEigen K i.1) * Real.sqrt (radialEigen K i'.1)))
        * (B.heightPoly i.2 p.2 * B.heightPoly i'.2 p.2) := by
    intro p; simp only [hWdef, hbdef]; field_simp
  simp_rw [e]
  rw [CellBox.rect, Measure.volume_eq_prod,
    setIntegral_prod_mul (fun r => K.lineWeight r * (1 - K.refR r ^ 2) * rd B i.1 r * rd B i'.1 r
        / (Real.sqrt (radialEigen K i.1) * Real.sqrt (radialEigen K i'.1)))
      (fun z => B.heightPoly i.2 z * B.heightPoly i'.2 z),
    integral_div, rad_orth hr hB, hB.height_orthonormal]
  obtain ⟨j, l⟩ := i
  obtain ⟨j', l'⟩ := i'
  simp only [Prod.mk.injEq] at hj hj' ⊢
  have hp := radialEigen_pos (K := K) hr hj
  by_cases h1 : j = j'
  · subst h1
    rw [if_pos rfl, Real.mul_self_sqrt hp.le, div_self hp.ne', one_mul]
    by_cases h2 : l = l' <;> simp [h2]
  · simp [h1]

lemma height_fin (hK : IsCellBox K) (hB : IsCellBases K B) (F Fd : ℝ × ℝ → ℂ)
    (hFd : AEStronglyMeasurable Fd (volume.restrict K.rect))
    (hFd2 : IntegrableOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) * ‖Fd p‖ ^ 2) K.rect)
    (I : ℕ × ℕ → Prop) [DecidablePred I]
    (hZ : ∀ j l, I (j, l) → l ≠ 0 → ((heightEigen K l : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) : ℝ) : ℂ) * Fd p *
        ((B.radialPoly j p.1 * SharpCoefTailInternal.hd B l p.2 : ℝ) : ℂ)) (T : Finset (ℕ × ℕ)) :
    ∑ i ∈ T, (if I i then heightEigen K i.2 * ‖B.coef K F i.1 i.2‖ ^ 2 else 0)
      ≤ ∫ p in K.rect, K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) * ‖Fd p‖ ^ 2 := by
  open SharpCoefTailInternal CellSharpBoundInternal in
  have hz := hK.z_order.2
  set W : ℝ × ℝ → ℝ := fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) with hWdef
  have hWc : Continuous W :=
    ((lw_cont K).comp continuous_fst).mul (continuous_const.sub (((refZ_cont K).comp continuous_snd).pow 2))
  have hW0 : ∀ p ∈ K.rect, 0 ≤ W p := fun p hp =>
    mul_nonneg (lw_nonneg hp.1.1) (refZ_sq_le hz hp.2.1 hp.2.2)
  set b : ℕ × ℕ → ℝ × ℝ → ℝ := fun i p => B.radialPoly i.1 p.1 * hd B i.2 p.2 / Real.sqrt (heightEigen K i.2)
    with hbdef
  have hbc : ∀ i, Continuous (b i) := fun i =>
    (((rp_cont B _).comp continuous_fst).mul ((hd_cont B _).comp continuous_snd)).div_const _
  set T' := T.filter (fun i => I i ∧ i.2 ≠ 0)
  have e1 : ∑ i ∈ T, (if I i then heightEigen K i.2 * ‖B.coef K F i.1 i.2‖ ^ 2 else 0)
      = ∑ i ∈ T', heightEigen K i.2 * ‖B.coef K F i.1 i.2‖ ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hI : I i
    · by_cases h0 : i.2 = 0
      · have : heightEigen K 0 = 0 := by unfold heightEigen; simp
        rw [if_pos hI, if_neg (fun h => h.2 h0), h0, this, zero_mul]
      · rw [if_pos hI, if_pos ⟨hI, h0⟩]
    · rw [if_neg hI, if_neg (fun h => hI h.1)]
  have e2 : ∀ i ∈ T', heightEigen K i.2 * ‖B.coef K F i.1 i.2‖ ^ 2
      = ‖∫ p in K.rect, (W p : ℂ) * Fd p * ((b i p : ℝ) : ℂ)‖ ^ 2 := by
    intro i hi
    have hl : i.2 ≠ 0 := (Finset.mem_filter.1 hi).2.2
    have hIi : I i := (Finset.mem_filter.1 hi).2.1
    rw [hbdef]
    simp only
    rw [int_scale K W (fun p => B.radialPoly i.1 p.1 * hd B i.2 p.2) Fd]
    exact term_eq _ (heightEigen_pos hz hl) _ _ (hZ i.1 i.2 hIi hl)
  rw [e1, Finset.sum_congr rfl e2]
  refine sq_coef_le K W hWc hW0 b hbc Fd hFd hFd2 T' ?_
  intro i hi i' hi'
  have hl : i.2 ≠ 0 := (Finset.mem_filter.1 hi).2.2
  have hl' : i'.2 ≠ 0 := (Finset.mem_filter.1 hi').2.2
  have e : ∀ p : ℝ × ℝ, W p * b i p * b i' p
      = (K.lineWeight p.1 * B.radialPoly i.1 p.1 * B.radialPoly i'.1 p.1)
        * ((1 - K.refZ p.2 ^ 2) * hd B i.2 p.2 * hd B i'.2 p.2
          / (Real.sqrt (heightEigen K i.2) * Real.sqrt (heightEigen K i'.2))) := by
    intro p; simp only [hWdef, hbdef]; field_simp
  simp_rw [e]
  rw [CellBox.rect, Measure.volume_eq_prod,
    setIntegral_prod_mul (fun r => K.lineWeight r * B.radialPoly i.1 r * B.radialPoly i'.1 r)
      (fun z => (1 - K.refZ z ^ 2) * hd B i.2 z * hd B i'.2 z
          / (Real.sqrt (heightEigen K i.2) * Real.sqrt (heightEigen K i'.2))),
    integral_div, ht_orth hz hB, hB.radial_orthonormal]
  obtain ⟨j, l⟩ := i
  obtain ⟨j', l'⟩ := i'
  simp only [Prod.mk.injEq] at hl hl' ⊢
  have hp := heightEigen_pos (K := K) hz hl
  by_cases h1 : l = l'
  · subst h1
    rw [if_pos rfl, Real.mul_self_sqrt hp.le, div_self hp.ne', mul_one]
    by_cases h2 : j = j' <;> simp [h2]
  · simp [h1]

lemma grad_gen (hK : IsCellBox K) (hB : IsCellBases K B) (F Fr Fz : ℝ × ℝ → ℂ)
    (hFr : AEStronglyMeasurable Fr (volume.restrict K.rect))
    (hFr2 : IntegrableOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) * ‖Fr p‖ ^ 2) K.rect)
    (hFz : AEStronglyMeasurable Fz (volume.restrict K.rect))
    (hFz2 : IntegrableOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) * ‖Fz p‖ ^ 2) K.rect)
    (I : ℕ × ℕ → Prop) [DecidablePred I]
    (hR : ∀ j l, I (j, l) → j ≠ 0 → ((radialEigen K j : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) : ℝ) : ℂ) * Fr p *
        ((SharpCoefTailInternal.rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
    (hZ : ∀ j l, I (j, l) → l ≠ 0 → ((heightEigen K l : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) : ℝ) : ℂ) * Fz p *
        ((B.radialPoly j p.1 * SharpCoefTailInternal.hd B l p.2 : ℝ) : ℂ)) :
    Summable (fun jl : ℕ × ℕ => if I jl then CellScalars.tailLam K jl.1 jl.2 * ‖B.coef K F jl.1 jl.2‖ ^ 2 else 0) ∧
    (∑' jl : ℕ × ℕ, if I jl then CellScalars.tailLam K jl.1 jl.2 * ‖B.coef K F jl.1 jl.2‖ ^ 2 else 0)
      ≤ K.innerRadius * (K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2)) Fr
        + K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2)) Fz) := by
  have hir : 0 ≤ K.innerRadius := by
    unfold CellBox.innerRadius; split_ifs
    · exact zero_le_one
    · exact hK.r_order.1
  have hfin : ∀ T : Finset (ℕ × ℕ), ∑ i ∈ T, (if I i then CellScalars.tailLam K i.1 i.2 * ‖B.coef K F i.1 i.2‖ ^ 2 else 0)
      ≤ K.innerRadius * (K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2)) Fr
        + K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2)) Fz) := by
    intro T
    have h1 := radial_fin hK hB F Fr hFr hFr2 I hR T
    have h2 := height_fin hK hB F Fz hFz hFz2 I hZ T
    have e : ∑ i ∈ T, (if I i then CellScalars.tailLam K i.1 i.2 * ‖B.coef K F i.1 i.2‖ ^ 2 else 0)
        = K.innerRadius * (∑ i ∈ T, (if I i then radialEigen K i.1 * ‖B.coef K F i.1 i.2‖ ^ 2 else 0)
          + ∑ i ∈ T, (if I i then heightEigen K i.2 * ‖B.coef K F i.1 i.2‖ ^ 2 else 0)) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold CellScalars.tailLam
      split_ifs <;> ring
    rw [e]
    unfold CellBox.normSqOn
    exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) hir
  have hn : ∀ jl : ℕ × ℕ, 0 ≤ (if I jl then CellScalars.tailLam K jl.1 jl.2 * ‖B.coef K F jl.1 jl.2‖ ^ 2 else 0) := by
    intro jl; split_ifs
    · exact mul_nonneg (tailLam_nonneg hK _ _) (sq_nonneg _)
    · exact le_rfl
  have hs := summable_of_sum_le hn hfin
  exact ⟨hs, hs.tsum_le_of_sum_le hfin⟩

lemma third_int (hK : IsCellBox K) (hs : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3) :
    AEStronglyMeasurable (radialGradMode m n H a b) (volume.restrict K.rect) ∧
    IntegrableOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) * ‖radialGradMode m n H a b p‖ ^ 2) K.rect ∧
    AEStronglyMeasurable (heightGradMode m n H a b) (volume.restrict K.rect) ∧
    IntegrableOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) * ‖heightGradMode m n H a b p‖ ^ 2) K.rect := by
  open SharpCoefTailInternal in
  obtain ⟨_, _, h3⟩ := modeSquareIntegrable K hK m v G H hs n (unitMat a b)
  obtain ⟨hr0, hr2⟩ := h3 0
  obtain ⟨hz0, hz2⟩ := h3 2
  have eT : ∀ c : Fin 3, comboThird (unitMat a b) m n H c = modeThird m n H a b c :=
    fun c => funext (combo_third m n H a b c)
  rw [eT] at hr0 hr2 hz0 hz2
  exact ⟨hr0, wmono _ hr0 _ (continuous_const.sub (((refR_cont K).comp continuous_fst).pow 2)) (gR01 hK)
      (rmono hK _ hr0 hr2), hz0,
    wmono _ hz0 _ (continuous_const.sub (((refZ_cont K).comp continuous_snd).pow 2)) (gZ01 hK)
      (rmono hK _ hz0 hz2)⟩

lemma sub_sq_intW (K : CellBox) (W : ℝ × ℝ → ℝ) (hW : Continuous W) (hW0 : ∀ p ∈ K.rect, 0 ≤ W p)
    (F P : ℝ × ℝ → ℂ) (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hF2 : IntegrableOn (fun p => W p * ‖F p‖ ^ 2) K.rect) (hP : Continuous P) :
    AEStronglyMeasurable (fun p => F p - P p) (volume.restrict K.rect) ∧
    IntegrableOn (fun p => W p * ‖F p - P p‖ ^ 2) K.rect := by
  have hm : AEStronglyMeasurable (fun p => F p - P p) (volume.restrict K.rect) := hF.sub hP.aestronglyMeasurable
  refine ⟨hm, ?_⟩
  have hPi : IntegrableOn (fun p => W p * ‖P p‖ ^ 2) K.rect :=
    (hW.mul (hP.norm.pow 2)).continuousOn.integrableOn_compact (CellSharpBoundInternal.rect_cpt K)
  refine Integrable.mono' ((hF2.add hPi).const_mul 2) (hW.aestronglyMeasurable.mul (hm.norm.pow 2)) ?_
  refine (ae_restrict_iff' (CellSharpBoundInternal.rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
  have hw := hW0 p hp
  rw [Real.norm_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  have h1 : ‖F p - P p‖ ≤ ‖F p‖ + ‖P p‖ := norm_sub_le _ _
  have h2 : ‖F p - P p‖ ^ 2 ≤ 2 * ‖F p‖ ^ 2 + 2 * ‖P p‖ ^ 2 := by
    nlinarith [norm_nonneg (F p - P p), norm_nonneg (F p), norm_nonneg (P p), sq_nonneg (‖F p‖ - ‖P p‖)]
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left h2 hw]

lemma rad_ibp (hK : IsCellBox K) (hB : IsCellBases K B) {j : ℕ} (hj : j ≠ 0) (a : ℕ) :
    (a : ℝ) * ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * (1 - K.refR r ^ 2) * SharpCoefTailInternal.rd B j r * r ^ (a - 1)
      = radialEigen K j * ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * B.radialPoly j r * r ^ a := by
  open SharpCoefTailInternal CellSharpBoundInternal in
  have hr := hK.r_order.2
  have hu : ∀ x ∈ Set.uIcc K.r₁ K.r₂, HasDerivAt (fun r => K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r)
      (-(radialEigen K j) * K.lineWeight x * B.radialPoly j x) x := fun x _ => radial_hasDeriv hr hB hj x
  have hv : ∀ x ∈ Set.uIcc K.r₁ K.r₂, HasDerivAt (fun r : ℝ => r ^ a) ((a : ℝ) * x ^ (a - 1)) x :=
    fun x _ => hasDerivAt_pow a x
  have hu' : IntervalIntegrable (fun x => -(radialEigen K j) * K.lineWeight x * B.radialPoly j x) volume K.r₁ K.r₂ :=
    ((continuous_const.mul (lw_cont K)).mul (rp_cont B j)).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun x : ℝ => (a : ℝ) * x ^ (a - 1)) volume K.r₁ K.r₂ :=
    (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have e1 : K.lineWeight K.r₂ * (1 - K.refR K.r₂ ^ 2) * rd B j K.r₂ = 0 := by rw [refR_right K hr]; ring
  have e0 : K.lineWeight K.r₁ * (1 - K.refR K.r₁ ^ 2) * rd B j K.r₁ = 0 := by rw [refR_left K hr]; ring
  rw [e1, e0, zero_mul, zero_mul, sub_zero, zero_sub] at h
  rw [icc_interval _ hr.le, icc_interval _ hr.le, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  have l1 : ∫ r in K.r₁..K.r₂, (a : ℝ) * (K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r * r ^ (a - 1))
      = ∫ r in K.r₁..K.r₂, K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r * ((a : ℝ) * r ^ (a - 1)) := by
    congr 1; funext r; ring
  have l2 : ∫ r in K.r₁..K.r₂, radialEigen K j * (K.lineWeight r * B.radialPoly j r * r ^ a)
      = -∫ r in K.r₁..K.r₂, -(radialEigen K j) * K.lineWeight r * B.radialPoly j r * r ^ a := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext r; ring
  rw [l1, l2, h]

lemma ht_ibp (hK : IsCellBox K) (hB : IsCellBases K B) {l : ℕ} (hl : l ≠ 0) (b : ℕ) :
    (b : ℝ) * ∫ z in Set.Icc K.z₁ K.z₂, (1 - K.refZ z ^ 2) * SharpCoefTailInternal.hd B l z * z ^ (b - 1)
      = heightEigen K l * ∫ z in Set.Icc K.z₁ K.z₂, B.heightPoly l z * z ^ b := by
  open SharpCoefTailInternal CellSharpBoundInternal in
  have hz := hK.z_order.2
  have hu : ∀ x ∈ Set.uIcc K.z₁ K.z₂, HasDerivAt (fun z => (1 - K.refZ z ^ 2) * hd B l z)
      (-(heightEigen K l) * B.heightPoly l x) x := fun x _ => height_hasDeriv hz hB hl x
  have hv : ∀ x ∈ Set.uIcc K.z₁ K.z₂, HasDerivAt (fun z : ℝ => z ^ b) ((b : ℝ) * x ^ (b - 1)) x :=
    fun x _ => hasDerivAt_pow b x
  have hu' : IntervalIntegrable (fun x => -(heightEigen K l) * B.heightPoly l x) volume K.z₁ K.z₂ :=
    (continuous_const.mul (hp_cont B l)).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun x : ℝ => (b : ℝ) * x ^ (b - 1)) volume K.z₁ K.z₂ :=
    (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have e1 : (1 - K.refZ K.z₂ ^ 2) * hd B l K.z₂ = 0 := by rw [refZ_right K hz]; ring
  have e0 : (1 - K.refZ K.z₁ ^ 2) * hd B l K.z₁ = 0 := by rw [refZ_left K hz]; ring
  rw [e1, e0, zero_mul, zero_mul, sub_zero, zero_sub] at h
  rw [icc_interval _ hz.le, icc_interval _ hz.le, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  have l1 : ∫ z in K.z₁..K.z₂, (b : ℝ) * ((1 - K.refZ z ^ 2) * hd B l z * z ^ (b - 1))
      = ∫ z in K.z₁..K.z₂, (1 - K.refZ z ^ 2) * hd B l z * ((b : ℝ) * z ^ (b - 1)) := by
    congr 1; funext z; ring
  have l2 : ∫ z in K.z₁..K.z₂, heightEigen K l * (B.heightPoly l z * z ^ b)
      = -∫ z in K.z₁..K.z₂, -(heightEigen K l) * B.heightPoly l z * z ^ b := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext z; ring
  rw [l1, l2, h]

lemma rderiv_poly {d : ℕ} (cf : Fin (d + 1) → Fin (d + 1) → ℂ) (P : ℝ × ℝ → ℂ)
    (hP : ∀ p : ℝ × ℝ, P p = ∑ a, ∑ b, cf a b * ((p.1 : ℂ) ^ (a : ℕ)) * ((p.2 : ℂ) ^ (b : ℕ))) (p : ℝ × ℝ) :
    CellBox.radialDeriv P p = ∑ a, ∑ b, cf a b * (((a : ℕ) : ℂ) * (p.1 : ℂ) ^ ((a : ℕ) - 1)) * ((p.2 : ℂ) ^ (b : ℕ)) := by
  unfold CellBox.radialDeriv
  have e : (fun r : ℝ => P (r, p.2)) = fun r : ℝ => ∑ a, ∑ b, cf a b * ((r : ℂ) ^ (a : ℕ)) * ((p.2 : ℂ) ^ (b : ℕ)) :=
    funext fun r => hP (r, p.2)
  rw [e]
  refine HasDerivAt.deriv ?_
  refine HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ => ?_
  exact (((hasDerivAt_pow (a : ℕ) ((p.1 : ℝ) : ℂ)).comp_ofReal).const_mul (cf a b)).mul_const _

lemma hderiv_poly {d : ℕ} (cf : Fin (d + 1) → Fin (d + 1) → ℂ) (P : ℝ × ℝ → ℂ)
    (hP : ∀ p : ℝ × ℝ, P p = ∑ a, ∑ b, cf a b * ((p.1 : ℂ) ^ (a : ℕ)) * ((p.2 : ℂ) ^ (b : ℕ))) (p : ℝ × ℝ) :
    CellBox.heightDeriv P p = ∑ a, ∑ b, cf a b * ((p.1 : ℂ) ^ (a : ℕ)) * (((b : ℕ) : ℂ) * (p.2 : ℂ) ^ ((b : ℕ) - 1)) := by
  unfold CellBox.heightDeriv
  have e : (fun z : ℝ => P (p.1, z)) = fun z : ℝ => ∑ a, ∑ b, cf a b * ((p.1 : ℂ) ^ (a : ℕ)) * ((z : ℂ) ^ (b : ℕ)) :=
    funext fun z => hP (p.1, z)
  rw [e]
  refine HasDerivAt.deriv ?_
  refine HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ => ?_
  exact ((hasDerivAt_pow (b : ℕ) ((p.2 : ℝ) : ℂ)).comp_ofReal).const_mul (cf a b * ((p.1 : ℂ) ^ (a : ℕ)))

lemma poly_rad_zero (hK : IsCellBox K) (hB : IsCellBases K B) {Q : ℕ} (cf : Fin (Q + 1) → Fin (Q + 1) → ℂ)
    (P : ℝ × ℝ → ℂ) (hP : ∀ p : ℝ × ℝ, P p = ∑ a, ∑ b, cf a b * ((p.1 : ℂ) ^ (a : ℕ)) * ((p.2 : ℂ) ^ (b : ℕ)))
    {j l : ℕ} (hj : j ≠ 0) (hjl : Q < max j l) :
    ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) : ℝ) : ℂ) * CellBox.radialDeriv P p *
      ((SharpCoefTailInternal.rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) = 0 := by
  open SharpCoefTailInternal CellSharpBoundInternal in
  have hw := lw_cont K
  have hrr := refR_cont K
  have hrd := rd_cont B j
  have hql := hp_cont B l
  have hcomp : IsCompact K.rect := rect_cpt K
  have hfun : ∀ p : ℝ × ℝ, ((K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) : ℝ) : ℂ) * CellBox.radialDeriv P p *
      ((rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)
      = ∑ a : Fin (Q + 1), ∑ b : Fin (Q + 1), cf a b *
        (((((a : ℕ) : ℝ) * (K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) * rd B j p.1 * p.1 ^ ((a : ℕ) - 1)) : ℝ) : ℂ)
          * ((B.heightPoly l p.2 * p.2 ^ (b : ℕ) : ℝ) : ℂ)) := by
    intro p
    rw [rderiv_poly cf P hP p, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    push_cast
    ring
  simp_rw [hfun]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [integral_const_mul]
      have hprod : ∫ p in K.rect, (((((a : ℕ) : ℝ) * (K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) * rd B j p.1
            * p.1 ^ ((a : ℕ) - 1)) : ℝ) : ℂ) * ((B.heightPoly l p.2 * p.2 ^ (b : ℕ) : ℝ) : ℂ))
          = (∫ r in Set.Icc K.r₁ K.r₂, ((((a : ℕ) : ℝ) * (K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r
              * r ^ ((a : ℕ) - 1)) : ℝ) : ℂ))
            * ∫ z in Set.Icc K.z₁ K.z₂, ((B.heightPoly l z * z ^ (b : ℕ) : ℝ) : ℂ) := by
        unfold CellBox.rect
        rw [Measure.volume_eq_prod]
        exact setIntegral_prod_mul (fun r => ((((a : ℕ) : ℝ) * (K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r
              * r ^ ((a : ℕ) - 1)) : ℝ) : ℂ))
          (fun z => ((B.heightPoly l z * z ^ (b : ℕ) : ℝ) : ℂ)) _ _
      rw [hprod, integral_complex_ofReal, integral_complex_ofReal]
      rcases lt_max_iff.mp hjl with h | h
      · rw [integral_const_mul, rad_ibp hK hB hj, MeshFarPolyInternal.radial_orth K B hB a j (by omega)]
        simp
      · rw [MeshFarPolyInternal.height_orth K B hB b l (by omega)]
        simp
    · intro b _
      exact (ContinuousOn.integrableOn_compact hcomp (Continuous.continuousOn (by fun_prop)))
  · intro a _
    exact (ContinuousOn.integrableOn_compact hcomp (Continuous.continuousOn (by fun_prop)))

lemma poly_ht_zero (hK : IsCellBox K) (hB : IsCellBases K B) {Q : ℕ} (cf : Fin (Q + 1) → Fin (Q + 1) → ℂ)
    (P : ℝ × ℝ → ℂ) (hP : ∀ p : ℝ × ℝ, P p = ∑ a, ∑ b, cf a b * ((p.1 : ℂ) ^ (a : ℕ)) * ((p.2 : ℂ) ^ (b : ℕ)))
    {j l : ℕ} (hl : l ≠ 0) (hjl : Q < max j l) :
    ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) : ℝ) : ℂ) * CellBox.heightDeriv P p *
      ((B.radialPoly j p.1 * SharpCoefTailInternal.hd B l p.2 : ℝ) : ℂ) = 0 := by
  open SharpCoefTailInternal CellSharpBoundInternal in
  have hw := lw_cont K
  have hzz := refZ_cont K
  have hhd := hd_cont B l
  have hpj := rp_cont B j
  have hcomp : IsCompact K.rect := rect_cpt K
  have hfun : ∀ p : ℝ × ℝ, ((K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) : ℝ) : ℂ) * CellBox.heightDeriv P p *
      ((B.radialPoly j p.1 * hd B l p.2 : ℝ) : ℂ)
      = ∑ a : Fin (Q + 1), ∑ b : Fin (Q + 1), cf a b *
        (((K.lineWeight p.1 * B.radialPoly j p.1 * p.1 ^ (a : ℕ) : ℝ) : ℂ)
          * ((((b : ℕ) : ℝ) * ((1 - K.refZ p.2 ^ 2) * hd B l p.2 * p.2 ^ ((b : ℕ) - 1)) : ℝ) : ℂ)) := by
    intro p
    rw [hderiv_poly cf P hP p, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    push_cast
    ring
  simp_rw [hfun]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [integral_const_mul]
      have hprod : ∫ p in K.rect, (((K.lineWeight p.1 * B.radialPoly j p.1 * p.1 ^ (a : ℕ) : ℝ) : ℂ)
            * ((((b : ℕ) : ℝ) * ((1 - K.refZ p.2 ^ 2) * hd B l p.2 * p.2 ^ ((b : ℕ) - 1)) : ℝ) : ℂ))
          = (∫ r in Set.Icc K.r₁ K.r₂, ((K.lineWeight r * B.radialPoly j r * r ^ (a : ℕ) : ℝ) : ℂ))
            * ∫ z in Set.Icc K.z₁ K.z₂, ((((b : ℕ) : ℝ) * ((1 - K.refZ z ^ 2) * hd B l z * z ^ ((b : ℕ) - 1)) : ℝ) : ℂ) := by
        unfold CellBox.rect
        rw [Measure.volume_eq_prod]
        exact setIntegral_prod_mul (fun r => ((K.lineWeight r * B.radialPoly j r * r ^ (a : ℕ) : ℝ) : ℂ))
          (fun z => ((((b : ℕ) : ℝ) * ((1 - K.refZ z ^ 2) * hd B l z * z ^ ((b : ℕ) - 1)) : ℝ) : ℂ)) _ _
      rw [hprod, integral_complex_ofReal, integral_complex_ofReal]
      rcases lt_max_iff.mp hjl with h | h
      · rw [MeshFarPolyInternal.radial_orth K B hB a j (by omega)]
        simp
      · rw [integral_const_mul, ht_ibp hK hB hl, MeshFarPolyInternal.height_orth K B hB b l (by omega)]
        simp
    · intro b _
      exact (ContinuousOn.integrableOn_compact hcomp (Continuous.continuousOn (by fun_prop)))
  · intro a _
    exact (ContinuousOn.integrableOn_compact hcomp (Continuous.continuousOn (by fun_prop)))

lemma grad_tail (hK : IsCellBox K) (hB : IsCellBases K B) (hs : IsSecondOrderField m v G H) (Q : ℕ) (n : ℤ)
    (a b : Fin 3) :
    Summable (fun jl : ℕ × ℕ => if Q < max jl.1 jl.2 then
      CellScalars.tailLam K jl.1 jl.2 * ‖B.coef K (gradMode m n G a b) jl.1 jl.2‖ ^ 2 else 0) ∧
    (∑' jl : ℕ × ℕ, if Q < max jl.1 jl.2 then
      CellScalars.tailLam K jl.1 jl.2 * ‖B.coef K (gradMode m n G a b) jl.1 jl.2‖ ^ 2 else 0)
      ≤ K.tailGradWeight Q (gradMode m n G a b) (radialGradMode m n H a b) (heightGradMode m n H a b) := by
  open SharpCoefTailInternal CellSharpBoundInternal in
  set F := gradMode m n G a b with hFdef
  set P := K.proj Q Q F with hPdef
  obtain ⟨cf, hcf⟩ := proj_mem K Q F
  have hPr : Continuous (CellBox.radialDeriv P) := by
    rw [show CellBox.radialDeriv P = fun p : ℝ × ℝ => ∑ a, ∑ b, cf a b * (((a : ℕ) : ℂ) * (p.1 : ℂ) ^ ((a : ℕ) - 1))
      * ((p.2 : ℂ) ^ (b : ℕ)) from funext (rderiv_poly cf P hcf)]
    fun_prop
  have hPz : Continuous (CellBox.heightDeriv P) := by
    rw [show CellBox.heightDeriv P = fun p : ℝ × ℝ => ∑ a, ∑ b, cf a b * ((p.1 : ℂ) ^ (a : ℕ))
      * (((b : ℕ) : ℂ) * (p.2 : ℂ) ^ ((b : ℕ) - 1)) from funext (hderiv_poly cf P hcf)]
    fun_prop
  obtain ⟨hr0, hr2, hz0, hz2⟩ := third_int hK hs n a b
  have hr := hK.r_order.2
  have hz := hK.z_order.2
  set Wr : ℝ × ℝ → ℝ := fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) with hWr
  set Wz : ℝ × ℝ → ℝ := fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) with hWz
  have hWrc : Continuous Wr :=
    ((lw_cont K).comp continuous_fst).mul (continuous_const.sub (((refR_cont K).comp continuous_fst).pow 2))
  have hWzc : Continuous Wz :=
    ((lw_cont K).comp continuous_fst).mul (continuous_const.sub (((refZ_cont K).comp continuous_snd).pow 2))
  have hWr0 : ∀ p ∈ K.rect, 0 ≤ Wr p := fun p hp => mul_nonneg (lw_nonneg hp.1.1) (refR_sq_le hr hp.1.1 hp.1.2)
  have hWz0 : ∀ p ∈ K.rect, 0 ≤ Wz p := fun p hp => mul_nonneg (lw_nonneg hp.1.1) (refZ_sq_le hz hp.2.1 hp.2.2)
  obtain ⟨hm1, hi1⟩ := sub_sq_intW K Wr hWrc hWr0 _ _ hr0 hr2 hPr
  obtain ⟨hm2, hi2⟩ := sub_sq_intW K Wz hWzc hWz0 _ _ hz0 hz2 hPz
  have hR : ∀ j l, Q < max (j, l).1 (j, l).2 → j ≠ 0 → ((radialEigen K j : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) : ℝ) : ℂ) *
        (radialGradMode m n H a b p - CellBox.radialDeriv P p) * ((rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) := by
    intro j l hI hj
    rw [strain_radial hK hB modeRadialParts hs n a b j l hj]
    have i1 : IntegrableOn (fun p : ℝ × ℝ => ((Wr p : ℝ) : ℂ) * modeThird m n H a b 0 p *
        ((rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect :=
      g_int' K Wr hWrc hWr0 (fun i p => rd B i.1 p.1 * B.heightPoly i.2 p.2)
        (fun i => ((rd_cont B i.1).comp continuous_fst).mul ((hp_cont B i.2).comp continuous_snd)) _ hr0 hr2 (j, l)
    have i2 : IntegrableOn (fun p : ℝ × ℝ => ((Wr p : ℝ) : ℂ) * CellBox.radialDeriv P p *
        ((rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect :=
      (((Complex.continuous_ofReal.comp hWrc).mul hPr).mul (Complex.continuous_ofReal.comp
        (((rd_cont B j).comp continuous_fst).mul ((hp_cont B l).comp continuous_snd)))).continuousOn.integrableOn_compact
        (rect_cpt K)
    have e : (fun p : ℝ × ℝ => ((K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) : ℝ) : ℂ) *
        (radialGradMode m n H a b p - CellBox.radialDeriv P p) * ((rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
        = fun p => ((Wr p : ℝ) : ℂ) * modeThird m n H a b 0 p * ((rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)
          - ((Wr p : ℝ) : ℂ) * CellBox.radialDeriv P p * ((rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) := by
      funext p; simp only [hWr, radialGradMode]; ring
    rw [e, integral_sub i1 i2]
    have h0 := poly_rad_zero hK hB cf P hcf hj hI
    simp only [hWr] at h0 ⊢
    rw [h0, sub_zero]
  have hZ : ∀ j l, Q < max (j, l).1 (j, l).2 → l ≠ 0 → ((heightEigen K l : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) : ℝ) : ℂ) *
        (heightGradMode m n H a b p - CellBox.heightDeriv P p) * ((B.radialPoly j p.1 * hd B l p.2 : ℝ) : ℂ) := by
    intro j l hI hl
    rw [strain_height hK hB modeHeightParts hs n a b j l hl]
    have i1 : IntegrableOn (fun p : ℝ × ℝ => ((Wz p : ℝ) : ℂ) * modeThird m n H a b 2 p *
        ((B.radialPoly j p.1 * hd B l p.2 : ℝ) : ℂ)) K.rect :=
      g_int' K Wz hWzc hWz0 (fun i p => B.radialPoly i.1 p.1 * hd B i.2 p.2)
        (fun i => ((rp_cont B i.1).comp continuous_fst).mul ((hd_cont B i.2).comp continuous_snd)) _ hz0 hz2 (j, l)
    have i2 : IntegrableOn (fun p : ℝ × ℝ => ((Wz p : ℝ) : ℂ) * CellBox.heightDeriv P p *
        ((B.radialPoly j p.1 * hd B l p.2 : ℝ) : ℂ)) K.rect :=
      (((Complex.continuous_ofReal.comp hWzc).mul hPz).mul (Complex.continuous_ofReal.comp
        (((rp_cont B j).comp continuous_fst).mul ((hd_cont B l).comp continuous_snd)))).continuousOn.integrableOn_compact
        (rect_cpt K)
    have e : (fun p : ℝ × ℝ => ((K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) : ℝ) : ℂ) *
        (heightGradMode m n H a b p - CellBox.heightDeriv P p) * ((B.radialPoly j p.1 * hd B l p.2 : ℝ) : ℂ))
        = fun p => ((Wz p : ℝ) : ℂ) * modeThird m n H a b 2 p * ((B.radialPoly j p.1 * hd B l p.2 : ℝ) : ℂ)
          - ((Wz p : ℝ) : ℂ) * CellBox.heightDeriv P p * ((B.radialPoly j p.1 * hd B l p.2 : ℝ) : ℂ) := by
      funext p; simp only [hWz, heightGradMode]; ring
    rw [e, integral_sub i1 i2]
    have h0 := poly_ht_zero hK hB cf P hcf hl hI
    simp only [hWz] at h0 ⊢
    rw [h0, sub_zero]
  exact grad_gen hK hB F _ _ hm1 hi1 hm2 hi2 (fun jl => Q < max jl.1 jl.2) hR hZ

lemma grad_full (hK : IsCellBox K) (hB : IsCellBases K B) (hs : IsSecondOrderField m v G H) (n : ℤ)
    (a b : Fin 3) :
    Summable (fun jl : ℕ × ℕ => CellScalars.tailLam K jl.1 jl.2 * ‖B.coef K (gradMode m n G a b) jl.1 jl.2‖ ^ 2) ∧
    (∑' jl : ℕ × ℕ, CellScalars.tailLam K jl.1 jl.2 * ‖B.coef K (gradMode m n G a b) jl.1 jl.2‖ ^ 2)
      ≤ K.fullGradWeight (radialGradMode m n H a b) (heightGradMode m n H a b) := by
  obtain ⟨hr0, hr2, hz0, hz2⟩ := third_int hK hs n a b
  have h := grad_gen hK hB (gradMode m n G a b) _ _ hr0 hr2 hz0 hz2 (fun _ => True)
    (fun j l _ hj => SharpCoefTailInternal.strain_radial hK hB modeRadialParts hs n a b j l hj)
    (fun j l _ hl => SharpCoefTailInternal.strain_height hK hB modeHeightParts hs n a b j l hl)
  simp only [if_true] at h
  exact h



lemma ang_tail (hK : IsCellBox K) (hB : IsCellBases K B) (hs : IsSecondOrderField m v G H) (Q : ℕ) (n : ℤ)
    (a b : Fin 3) :
    Summable (fun jl : ℕ × ℕ => if Q < max jl.1 jl.2 then
      ‖B.coef K (angularGradMode m n H a b) jl.1 jl.2‖ ^ 2 else 0) ∧
    (∑' jl : ℕ × ℕ, if Q < max jl.1 jl.2 then ‖B.coef K (angularGradMode m n H a b) jl.1 jl.2‖ ^ 2 else 0)
      ≤ K.tailNormSq Q (angularGradMode m n H a b) := by
  obtain ⟨hm, hi⟩ := ang_int hK hs n a b
  exact coefSq_tail hB Q _ hm hi

lemma ang_full (hK : IsCellBox K) (hB : IsCellBases K B) (hs : IsSecondOrderField m v G H) (n : ℤ)
    (a b : Fin 3) :
    Summable (fun jl : ℕ × ℕ => ‖B.coef K (angularGradMode m n H a b) jl.1 jl.2‖ ^ 2) ∧
    (∑' jl : ℕ × ℕ, ‖B.coef K (angularGradMode m n H a b) jl.1 jl.2‖ ^ 2)
      ≤ K.normSqOn K.lineWeightFn (angularGradMode m n H a b) := by
  obtain ⟨hm, hi⟩ := ang_int hK hs n a b
  exact coefSq_full hB _ hm hi

open CellEnergy.Internal.AngularFrame in
lemma ang_ae (hK : IsCellBox K) (hF : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3) :
    ∀ᵐ p ∂(volume.restrict K.rect), angularGradMode m n H a b p =
      ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth m n) a b a' b' * gradMode m n G a' b' p := by
  have hC := CellEnergy.circleWeak
  have locG : ∀ i, LocallyIntegrable (fun y => G y (unitVector i)) volume := fun i =>
    locInt_vec (meas_G hF.measurable_gradient i) hF.gradient_two fun y => G_sq_le (G y) i
  have locH : ∀ j i, LocallyIntegrable (fun y => H y (unitVector j) (unitVector i)) volume := fun j i =>
    locInt_vec (meas_H hF.measurable_second j i) hF.second_two fun y => H_sq_le (H y) j i
  have locf : ∀ i l, LocallyIntegrable (fun y => inner ℝ (G y (unitVector i)) (unitVector l)) volume :=
    fun i l => locInt_sq ((meas_G hF.measurable_gradient i).inner aestronglyMeasurable_const)
      hF.gradient_two fun y => (inner_sq_le _ l).trans (G_sq_le (G y) i)
  have locs : ∀ j i l, LocallyIntegrable (fun y => inner ℝ (H y (unitVector j) (unitVector i)) (unitVector l))
      volume := fun j i l => locInt_sq ((meas_H hF.measurable_second j i).inner aestronglyMeasurable_const)
      hF.second_two fun y => (inner_sq_le _ l).trans (H_sq_le (H y) j i)
  have locg : ∀ i l, LocallyIntegrable (fun y => gv (H y) i l) volume := by
    intro i l
    unfold gv
    refine locallyIntegrable_finsetSum Finset.univ fun j _ => ?_
    exact locallyIntegrable_iff.2 fun C hC' => ((locs j i l).integrableOn_isCompact hC').smul_const _
  have hweak : ∀ i l, ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (G y (unitVector i)) (unitVector l) =
        -∫ y, φ y * inner ℝ (gv (H y) i l) (unitVector j) := by
    intro i l φ hφ j
    have hw := hF.weak_second φ hφ i j
    have hcont : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hsupp : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector j)) (by simp)
    have hi1 := (locG i).integrable_smul_left_of_hasCompactSupport hcont hsupp
    have hi2 := (locH j i).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    set L : Space →L[ℝ] ℝ := innerSL ℝ (unitVector l)
    calc ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (G y (unitVector i)) (unitVector l)
        = ∫ y, L (fderiv ℝ φ y (unitVector j) • G y (unitVector i)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp [L, innerSL_apply_apply, real_inner_comm]
      _ = L (∫ y, fderiv ℝ φ y (unitVector j) • G y (unitVector i)) := L.integral_comp_comm hi1
      _ = -L (∫ y, φ y • H y (unitVector j) (unitVector i)) := by rw [hw, map_neg]
      _ = -∫ y, L (φ y • H y (unitVector j) (unitVector i)) := by rw [L.integral_comp_comm hi2]
      _ = -∫ y, φ y * inner ℝ (gv (H y) i l) (unitVector j) := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only [gv_inner]
          simp [L, innerSL_apply_apply, real_inner_comm]
  have hKer := fun i l => hC (fun y => inner ℝ (G y (unitVector i)) (unitVector l)) (fun y => gv (H y) i l)
    (locf i l) (locg i l) (hweak i l)
  have hk : azimuth m n = ((n * m : ℤ) : ℝ) := by
    simp [azimuth]
  have hint := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun l => (hKer i l).1
  have hid := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun l =>
    (hKer i l).2 (wgt (azimuth m n) a b i l) (wgt_smooth _ a b i l) (hk ▸ wgt_periodic _ a b i l)
  have h0 : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
    have hnull : volume ((Prod.fst ⁻¹' ({0} : Set ℝ)) : Set (ℝ × ℝ)) = 0 := by
      rw [show ((Prod.fst ⁻¹' ({0} : Set ℝ)) : Set (ℝ × ℝ)) = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) by
        ext p; simp, Measure.volume_eq_prod, Measure.prod_prod]
      simp
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with p hp
    simpa using hp
  rw [ae_restrict_iff' (CellSharpBoundInternal.rect_meas K)]
  filter_upwards [hint, hid, h0] with p h1 h2 h3 hp
  have hr : 0 < p.1 := lt_of_le_of_ne (hK.r_order.1.trans hp.1.1) (Ne.symm h3)
  obtain ⟨r, z⟩ := p
  exact point m n G H a b r z (fun i l => (h1 i l hr).1) (fun i l => (h1 i l hr).2) (fun i l => h2 i l hr)

lemma ang_coef (hK : IsCellBox K) (hs : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3) (j l : ℕ) :
    B.coef K (angularGradMode m n H a b) j l =
      ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth m n) a b a' b' * B.coef K (gradMode m n G a' b') j l := by
  have hae := ang_ae (K := K) hK hs n a b
  have hInt : ∀ a' b', IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * gradMode m n G a' b' p *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect := by
    intro a' b'
    obtain ⟨hm, hi⟩ := modeGradSquare K hK m v G H hs n a' b'
    exact SharpCoefTailInternal.g_int' K K.lineWeightFn ((CellSharpBoundInternal.lw_cont K).comp continuous_fst)
      (fun p hp => CellSharpBoundInternal.lw_nonneg (K := K) hp.1.1)
      (fun i p => B.radialPoly i.1 p.1 * B.heightPoly i.2 p.2)
      (fun i => ((MeshFarPolyInternal.radialPoly_continuous B i.1).comp continuous_fst).mul
        ((MeshFarPolyInternal.heightPoly_continuous B i.2).comp continuous_snd)) _ hm hi (j, l)
  unfold CellBases.coef
  calc ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * angularGradMode m n H a b p *
        ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)
      = ∫ p in K.rect, ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth m n) a b a' b' *
          ((K.lineWeight p.1 : ℂ) * gradMode m n G a' b' p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with p hp
        rw [hp, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b' _ => ?_
        ring
    _ = _ := by
        rw [integral_finsetSum _ fun a' _ => integrable_finsetSum _ fun b' _ => (hInt a' b').const_mul _]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [integral_finsetSum _ fun b' _ => (hInt a' b').const_mul _]
        refine Finset.sum_congr rfl fun b' _ => ?_
        rw [integral_const_mul]


end SharpEnergyStrainIdentityInternal

open SharpEnergyStrainIdentityInternal SharpEnergyTailParts CellEnergy SteadyCert Assembly in
theorem modeStrainIdentity_holds : ModeStrainIdentityStatement := by
  intro α _ _ k N c _ K S B Cl slots R hD _ x hx n
  classical
  have hK := hD.box
  have hB := hD.bases
  have hs := hx.1
  have hlam : ∀ jl : ℕ × ℕ, 0 ≤ CellScalars.tailLam K jl.1 jl.2 := fun jl => tailLam_nonneg hK jl.1 jl.2
  have hw := angularWeight_nonneg hK n
  by_cases hn : n ∈ S.resolved
  · have hI : ∀ jl : ℕ × ℕ, strainIdx S n jl ↔ S.degHigh < max jl.1 jl.2 := fun jl => by simp [strainIdx, hn]
    have hG : ∀ a b, Summable (fun jl : ℕ × ℕ => if strainIdx S n jl then CellScalars.tailLam K jl.1 jl.2 *
          ‖B.coef K (gradMode c.order n x.2.1 a b) jl.1 jl.2‖ ^ 2 else 0) ∧
        (∑' jl : ℕ × ℕ, if strainIdx S n jl then CellScalars.tailLam K jl.1 jl.2 *
          ‖B.coef K (gradMode c.order n x.2.1 a b) jl.1 jl.2‖ ^ 2 else 0)
          ≤ K.tailGradWeight S.degHigh (gradMode c.order n x.2.1 a b) (radialGradMode c.order n x.2.2.1 a b)
              (heightGradMode c.order n x.2.2.1 a b) := by
      intro a b
      simp only [hI]
      exact grad_tail hK hB hs S.degHigh n a b
    have hA : ∀ a b, Summable (fun jl : ℕ × ℕ => if strainIdx S n jl then
          ‖∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth c.order n) a b a' b' *
            B.coef K (gradMode c.order n x.2.1 a' b') jl.1 jl.2‖ ^ 2 else 0) ∧
        (∑' jl : ℕ × ℕ, if strainIdx S n jl then
          ‖∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth c.order n) a b a' b' *
            B.coef K (gradMode c.order n x.2.1 a' b') jl.1 jl.2‖ ^ 2 else 0)
          ≤ K.tailNormSq S.degHigh (angularGradMode c.order n x.2.2.1 a b) := by
      intro a b
      simp only [hI, ← ang_coef (B := B) hK hs n a b]
      exact ang_tail hK hB hs S.degHigh n a b
    obtain ⟨h1, h2, h3⟩ := assemble (strainIdx S n) (fun a b jl => B.coef K (gradMode c.order n x.2.1 a b) jl.1 jl.2)
      (fun jl => CellScalars.tailLam K jl.1 jl.2) hlam (K.angularWeight n) (azimuth c.order n) hw _ _ hG hA
    refine ⟨?_, ?_, fun _ => ?_, fun h => absurd hn h⟩
    · simp only [symShift, symCoefSq, modeNumber]
      exact h1
    · simp only [antiShift, antiCoefSq, modeNumber]
      exact h2
    · simp only [symShift, antiShift, symCoefSq, antiCoefSq, modeNumber]
      exact h3
  · have hI : ∀ jl : ℕ × ℕ, strainIdx S n jl := fun jl => Or.inl hn
    have hG : ∀ a b, Summable (fun jl : ℕ × ℕ => if strainIdx S n jl then CellScalars.tailLam K jl.1 jl.2 *
          ‖B.coef K (gradMode c.order n x.2.1 a b) jl.1 jl.2‖ ^ 2 else 0) ∧
        (∑' jl : ℕ × ℕ, if strainIdx S n jl then CellScalars.tailLam K jl.1 jl.2 *
          ‖B.coef K (gradMode c.order n x.2.1 a b) jl.1 jl.2‖ ^ 2 else 0)
          ≤ K.fullGradWeight (radialGradMode c.order n x.2.2.1 a b) (heightGradMode c.order n x.2.2.1 a b) := by
      intro a b
      simp only [hI, if_true]
      exact grad_full hK hB hs n a b
    have hA : ∀ a b, Summable (fun jl : ℕ × ℕ => if strainIdx S n jl then
          ‖∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth c.order n) a b a' b' *
            B.coef K (gradMode c.order n x.2.1 a' b') jl.1 jl.2‖ ^ 2 else 0) ∧
        (∑' jl : ℕ × ℕ, if strainIdx S n jl then
          ‖∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth c.order n) a b a' b' *
            B.coef K (gradMode c.order n x.2.1 a' b') jl.1 jl.2‖ ^ 2 else 0)
          ≤ K.normSqOn K.lineWeightFn (angularGradMode c.order n x.2.2.1 a b) := by
      intro a b
      simp only [hI, if_true, ← ang_coef (B := B) hK hs n a b]
      exact ang_full hK hB hs n a b
    obtain ⟨h1, h2, h3⟩ := assemble (strainIdx S n) (fun a b jl => B.coef K (gradMode c.order n x.2.1 a b) jl.1 jl.2)
      (fun jl => CellScalars.tailLam K jl.1 jl.2) hlam (K.angularWeight n) (azimuth c.order n) hw _ _ hG hA
    refine ⟨?_, ?_, fun h => absurd h hn, fun _ => ?_⟩
    · simp only [symShift, symCoefSq, modeNumber]
      exact h1
    · simp only [antiShift, antiCoefSq, modeNumber]
      exact h2
    · simp only [symShift, antiShift, symCoefSq, antiCoefSq, modeNumber]
      exact h3

end Breakdown.CellCert.CellAnalysis
