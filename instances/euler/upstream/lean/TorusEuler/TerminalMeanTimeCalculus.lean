import TorusEuler.EndpointTimeRegularity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Time differentiation of the spatially projected endpoint equation. -/

open Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

/-- Iterated within-time derivative on the closed endpoint slab. -/
abbrev terminalTimeJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ) (n : ℕ) (f : ℝ → E) := iteratedDerivWithin n f (Icc 0 T)

section ProductRule

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A continuous linear map commutes with within-set time derivatives at every
order on a set with unique derivatives. -/
theorem terminalIteratedDerivWithin_clm {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (A : F →L[ℝ] G) {f : ℝ → F}
    (hf : ContDiffOn ℝ ∞ f s) (n : ℕ) :
    EqOn (iteratedDerivWithin n (fun t => A (f t)) s)
      (fun t => A (iteratedDerivWithin n f s t)) s := by
  intro t ht
  change iteratedDerivWithin n (A ∘ f) s t = A (iteratedDerivWithin n f s t)
  simp only [iteratedDerivWithin_eq_iteratedFDerivWithin, A.iteratedFDerivWithin_comp_left
    (hf t ht) hs ht (by simp : (n : ℕ∞ω) ≤ ∞)]
  rfl

/-- The within-slab Leibniz rule for an operator-valued coefficient and a
Banach-valued curve. -/
theorem terminalIteratedDerivWithin_clm_apply {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    {C : ℝ → E →L[ℝ] F} {u : ℝ → E}
    (hC : ContDiffOn ℝ ∞ C s) (hu : ContDiffOn ℝ ∞ u s)
    (n : ℕ) {t : ℝ} (ht : t ∈ s) :
    iteratedDerivWithin n (fun z => C z (u z)) s t =
      ∑ i ∈ Finset.range (n + 1), n.choose i •
        iteratedDerivWithin i C s t (iteratedDerivWithin (n - i) u s t) := by
  induction n generalizing C u with
  | zero => simp
  | succ n ih =>
    have hc : ContDiffOn ℝ ∞ (derivWithin C s) s :=
      hC.derivWithin hs (by simp)
    have hv : ContDiffOn ℝ ∞ (derivWithin u s) s :=
      hu.derivWithin hs (by simp)
    have heq : EqOn (derivWithin (fun z => C z (u z)) s)
        (fun z => C z (derivWithin u s z) + derivWithin C s z (u z)) s := by
      intro z hz
      rw [derivWithin_clm_apply
        ((hC.differentiableOn (by simp)) z hz)
        ((hu.differentiableOn (by simp)) z hz), add_comm]
    rw [iteratedDerivWithin_succ', iteratedDerivWithin_congr heq ht,
      iteratedDerivWithin_fun_add ht hs
        ((hC.clm_apply hv) t ht |>.of_le (by simp))
        ((hc.clm_apply hu) t ht |>.of_le (by simp)),
      Finset.sum_range_succ', ih hC hv, Finset.sum_range_succ', ih hc hu]
    simp only [Nat.choose_succ_succ', add_smul, Finset.sum_add_distrib]
    nth_rw 3 [Finset.sum_range_succ]
    have hpos : ∀ i ∈ Finset.range n, 1 ≤ n - i := by simp; omega
    simp +contextual [← iteratedDerivWithin_succ', ← n.sub_sub, Nat.sub_add_cancel, hpos]
    abel

end ProductRule

section ProjectedEquation

variable {X B : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

/-- Differentiation of the integrated equation spends one fewer time
derivative on the source. This formula uses the coefficient curves of the
original solution. -/
theorem terminalProjectedTimeDerivative_of_integrated {T : ℝ} (hT : 0 < T)
    (P : B →L[ℝ] X) (c : X) (K Ω : ℝ → X →L[ℝ] B) (v : ℝ → X) (g : ℝ → B)
    (hK : ContDiffOn ℝ ∞ K (Icc 0 T)) (hΩ : ContinuousOn Ω (Icc 0 T))
    (hv : ContDiffOn ℝ ∞ v (Icc 0 T))
    (hg : ContinuousOn g (Icc 0 T))
    (hEq : ∀ t ∈ Icc 0 T, P (K t (v t)) =
      c + P (endpointPrimitive (fun r => Ω r (v r)) t) +
        P (endpointPrimitive g t)) :
    EqOn (fun t => P (derivWithin (fun r => K r (v r)) (Icc 0 T) t))
      (fun t => P (Ω t (v t) + g t)) (Icc 0 T) := by
  intro t ht
  have h₁ := hasDerivWithinAt_endpointPrimitive_of_continuousOn (hΩ.clm_apply hv.continuousOn) ht
  have h₂ := hasDerivWithinAt_endpointPrimitive_of_continuousOn hg ht
  have hh := ((P.hasFDerivAt.comp_hasDerivWithinAt t h₁).const_add c).add
    (P.hasFDerivAt.comp_hasDerivWithinAt t h₂)
  have hDer := hh.congr_of_mem hEq ht
  rw [← map_add] at hDer
  have hProd := (((hK.clm_apply hv).differentiableOn (by simp)) t ht).hasDerivWithinAt
  exact ((P.hasFDerivAt.comp_hasDerivWithinAt t hProd).derivWithin
    (uniqueDiffOn_Icc hT t ht)).symm.trans (hDer.derivWithin (uniqueDiffOn_Icc hT t ht))

/-- The projected kinetic operator acts on the highest velocity derivative.
Every product on the right uses the velocity and forcing through order `n`. -/
theorem terminalProjectedHigherTimeDerivative {T : ℝ} (hT : 0 < T)
    (P : B →L[ℝ] X) (c : X) (K Ω : ℝ → X →L[ℝ] B) (v : ℝ → X) (g : ℝ → B)
    (hK : ContDiffOn ℝ ∞ K (Icc 0 T)) (hΩ : ContDiffOn ℝ ∞ Ω (Icc 0 T))
    (hv : ContDiffOn ℝ ∞ v (Icc 0 T)) (hg : ContDiffOn ℝ ∞ g (Icc 0 T))
    (hEq : ∀ t ∈ Icc 0 T, P (K t (v t)) =
      c + P (endpointPrimitive (fun r => Ω r (v r)) t) + P (endpointPrimitive g t))
    (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) :
    P (K t (terminalTimeJet T (n + 1) v t)) = P
      ((∑ i ∈ Finset.range (n + 1), n.choose i • (terminalTimeJet T i Ω t)
        (terminalTimeJet T (n - i) v t)) + terminalTimeJet T n g t -
        ∑ i ∈ Finset.range (n + 1), (n + 1).choose (i + 1) • (terminalTimeJet T (i + 1) K t)
          (terminalTimeJet T (n - i) v t)) := by
  let I := Icc (0 : ℝ) T
  have hI := uniqueDiffOn_Icc hT
  have hKV := hK.clm_apply hv
  have hΩV := hΩ.clm_apply hv
  have hODE := terminalProjectedTimeDerivative_of_integrated hT P c K Ω v g hK hΩ.continuousOn
    hv hg.continuousOn hEq
  have hdEq := iteratedDerivWithin_congr (n := n) hODE ht
  change iteratedDerivWithin n (fun r => P (derivWithin (fun s => K s (v s)) I r)) I t =
    iteratedDerivWithin n (fun r => P (Ω r (v r) + g r)) I t at hdEq
  rw [terminalIteratedDerivWithin_clm hI P (hKV.derivWithin hI (by simp)) n ht,
    terminalIteratedDerivWithin_clm hI P (hΩV.add hg) n ht] at hdEq
  change P (iteratedDerivWithin n (derivWithin (fun r => K r (v r)) I) I t) =
    P (iteratedDerivWithin n (fun r => Ω r (v r) + g r) I t) at hdEq
  rw [← iteratedDerivWithin_succ', iteratedDerivWithin_fun_add ht hI
      ((hΩV t ht).of_le (by simp)) ((hg t ht).of_le (by simp)),
    terminalIteratedDerivWithin_clm_apply hI hK hv (n + 1) ht,
    terminalIteratedDerivWithin_clm_apply hI hΩ hv n ht,
    Finset.sum_range_succ'] at hdEq
  simpa only [Nat.choose_zero_right, one_smul, iteratedDerivWithin_zero, Nat.sub_zero,
    Nat.add_sub_add_right, map_add, map_sub, eq_sub_iff_add_eq, add_comm, terminalTimeJet, I] using hdEq

end ProjectedEquation

/-- A finite triangular time estimate with uniform inverse and coefficient
bounds. Its exponent is controlled by the time order alone. -/
theorem terminalMeanTimeBound {q : ℕ} {V : ℕ → ℝ → Prop} {A B G : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hMono : ∀ i {C C' : ℝ}, C ≤ C' → V i C → V i C') (hBase : V 0 (A * G))
    (hStep : ∀ n < q, ∀ C ≥ 0, (∀ j ≤ n, V j C) → V (n + 1) (A * (G + B * C))) :
    ∀ i ≤ q, V i ((1 + A * (1 + B)) ^ (i + 1) * G) := by
  let R := 1 + A * (1 + B)
  have hR : 1 ≤ R := le_add_of_nonneg_right (mul_nonneg hA (by positivity))
  have hAR : A ≤ R := by
    dsimp only [R]
    nlinarith only [mul_nonneg hA hB]
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hi
      cases i with
      | zero =>
          simpa only [zero_add, pow_one] using hMono 0 (mul_le_mul_of_nonneg_right hAR hG) hBase
      | succ n =>
          let C := R ^ (n + 1) * G
          have hC : 0 ≤ C := mul_nonneg (pow_nonneg (zero_le_one.trans hR) _) hG
          have hGC : G ≤ C := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hR) hG
          have hLower (j : ℕ) (hj : j ≤ n) : V j C :=
            hMono j (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR (Nat.succ_le_succ hj)) hG)
              (ih j (Nat.lt_succ_of_le hj) ((Nat.le_succ_of_le hj).trans hi))
          refine hMono _ ?_ (hStep n (by omega) C hC hLower)
          calc
            _ ≤ A * (C + B * C) := mul_le_mul_of_nonneg_left (add_le_add hGC le_rfl) hA
            _ = (A * (1 + B)) * C := by ring
            _ ≤ R * C := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hC
            _ = _ := by
              change R * (R ^ (n + 1) * G) = R ^ (n + 1 + 1) * G
              simp only [pow_succ', mul_assoc]

end

end TorusEuler
