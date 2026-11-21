import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoercivePerturbationFacts
import Breakdown.Cert.CoerciveModeRotation
import Breakdown.Cert.CoerciveRotation
import Breakdown.Cert.CoerciveStretchIntegrable
import Breakdown.Cert.CoerciveStretchTorus
import Breakdown.Cert.CoerciveStretchFibre

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace StretchInternal

def bilin (g : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → ℝ) (s : Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∑ j : Fin 3, (∑ m : Fin 3, v m * g j m) * (∑ a : Fin 3, ∑ b : Fin 3, alternatingSymbol j a b * s b a)
    + (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * g j m * s i j * v l

def matVec (g : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ) (j : Fin 3) : ℝ := ∑ m : Fin 3, g j m * x m

def crossVec (v : Fin 3 → ℝ) (l : Fin 3) (m : Fin 3) : ℝ := ∑ n : Fin 3, alternatingSymbol l m n * v n

def kernel (g : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → ℝ) (l j : Fin 3) : ℝ :=
  ∑ i : Fin 3, alternatingSymbol i j l * matVec g v i + (1 / 2 : ℝ) * matVec g (crossVec v l) j

theorem bilin_eq_sum (g : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → ℝ) (s : Fin 3 → Fin 3 → ℝ) :
    bilin g v s = ∑ l : Fin 3, ∑ j : Fin 3, kernel g v l j * s l j := by
  simp only [bilin, kernel, matVec, crossVec, alternatingSymbol, Fin.sum_univ_three]
  norm_num
  ring

theorem kernel_sq_eq (g : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → ℝ) (htr : g 0 0 + g 1 1 + g 2 2 = 0) :
    ∑ l : Fin 3, ∑ j : Fin 3, kernel g v l j ^ 2
      = 2 * ∑ i : Fin 3, matVec g v i ^ 2 + ∑ i : Fin 3, v i * matVec g (matVec g v) i
        + (1 / 4 : ℝ) * ∑ l : Fin 3, ∑ j : Fin 3, matVec g (crossVec v l) j ^ 2 := by
  simp only [kernel, matVec, crossVec, alternatingSymbol, Fin.sum_univ_three]
  norm_num
  linear_combination (-(v 0 * (g 0 0 * v 0 + g 0 1 * v 1 + g 0 2 * v 2)
    + v 1 * (g 1 0 * v 0 + g 1 1 * v 1 + g 1 2 * v 2) + v 2 * (g 2 0 * v 0 + g 2 1 * v 1 + g 2 2 * v 2))) * htr

theorem crossVec_sq_sum (v : Fin 3 → ℝ) :
    ∑ l : Fin 3, ∑ m : Fin 3, crossVec v l m ^ 2 = 2 * ∑ m : Fin 3, v m ^ 2 := by
  simp only [crossVec, alternatingSymbol, Fin.sum_univ_three]
  norm_num
  ring

theorem le_of_sq_le_sq_of_nonneg {a c : ℝ} (h : a ^ 2 ≤ c ^ 2) (hc : 0 ≤ c) : a ≤ c := by
  by_contra hne
  have hlt : c < a := lt_of_not_ge hne
  nlinarith

theorem sum_sq_prod_le (f g : Fin 3 → Fin 3 → ℝ) :
    (∑ l : Fin 3, ∑ j : Fin 3, f l j * g l j) ^ 2
      ≤ (∑ l : Fin 3, ∑ j : Fin 3, f l j ^ 2) * ∑ l : Fin 3, ∑ j : Fin 3, g l j ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3 × Fin 3))
    (fun p => f p.1 p.2) (fun p => g p.1 p.2)
  simpa only [Fintype.sum_prod_type] using h

theorem sum_sq_le (v w : Fin 3 → ℝ) :
    (∑ i : Fin 3, v i * w i) ^ 2 ≤ (∑ i : Fin 3, v i ^ 2) * ∑ i : Fin 3, w i ^ 2 :=
  Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem kernel_sq_le (g : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → ℝ) (htr : g 0 0 + g 1 1 + g 2 2 = 0)
    {K : ℝ} (hK : ∀ x : Fin 3 → ℝ, ∑ j : Fin 3, matVec g x j ^ 2 ≤ K ^ 2 * ∑ m : Fin 3, x m ^ 2) :
    ∑ l : Fin 3, ∑ j : Fin 3, kernel g v l j ^ 2 ≤ (7 / 2 : ℝ) * K ^ 2 * ∑ m : Fin 3, v m ^ 2 := by
  rw [kernel_sq_eq g v htr]
  set nv := ∑ m : Fin 3, v m ^ 2 with hnv
  have hnv0 : 0 ≤ nv := Finset.sum_nonneg (fun m _ => sq_nonneg (v m))
  have h1 := hK v
  have h2 : ∑ i : Fin 3, v i * matVec g (matVec g v) i ≤ K ^ 2 * nv := by
    have hcs := sum_sq_le v (matVec g (matVec g v))
    have hgg := hK (matVec g v)
    have hb : (∑ i : Fin 3, v i * matVec g (matVec g v) i) ^ 2 ≤ (K ^ 2 * nv) ^ 2 := by
      calc (∑ i : Fin 3, v i * matVec g (matVec g v) i) ^ 2
          ≤ nv * ∑ i : Fin 3, matVec g (matVec g v) i ^ 2 := hcs
        _ ≤ nv * (K ^ 2 * (K ^ 2 * nv)) := by
          refine mul_le_mul_of_nonneg_left (hgg.trans ?_) hnv0
          exact mul_le_mul_of_nonneg_left h1 (sq_nonneg K)
        _ = (K ^ 2 * nv) ^ 2 := by ring
    exact le_of_sq_le_sq_of_nonneg hb (mul_nonneg (sq_nonneg K) hnv0)
  have h3 : ∑ l : Fin 3, ∑ j : Fin 3, matVec g (crossVec v l) j ^ 2 ≤ K ^ 2 * (2 * nv) := by
    calc ∑ l : Fin 3, ∑ j : Fin 3, matVec g (crossVec v l) j ^ 2
        ≤ ∑ l : Fin 3, K ^ 2 * ∑ m : Fin 3, crossVec v l m ^ 2 :=
          Finset.sum_le_sum (fun l _ => hK (crossVec v l))
      _ = K ^ 2 * (2 * nv) := by rw [← Finset.mul_sum, crossVec_sq_sum]
  nlinarith [h1, h2, h3]

theorem bilin_abs_le (g : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → ℝ) (s : Fin 3 → Fin 3 → ℝ)
    (htr : g 0 0 + g 1 1 + g 2 2 = 0) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x : Fin 3 → ℝ, ∑ j : Fin 3, matVec g x j ^ 2 ≤ K ^ 2 * ∑ m : Fin 3, x m ^ 2) :
    |bilin g v s| ≤ (Real.sqrt 2 + 1 / 2) * K * Real.sqrt (∑ m : Fin 3, v m ^ 2)
      * Real.sqrt (∑ l : Fin 3, ∑ j : Fin 3, s l j ^ 2) := by
  set nv := ∑ m : Fin 3, v m ^ 2 with hnv
  set ns := ∑ l : Fin 3, ∑ j : Fin 3, s l j ^ 2 with hns
  have hnv0 : 0 ≤ nv := Finset.sum_nonneg (fun m _ => sq_nonneg (v m))
  have hns0 : 0 ≤ ns := Finset.sum_nonneg (fun l _ => Finset.sum_nonneg (fun j _ => sq_nonneg (s l j)))
  have hB : bilin g v s ^ 2 ≤ (7 / 2 : ℝ) * K ^ 2 * nv * ns := by
    rw [bilin_eq_sum]
    refine (sum_sq_prod_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (kernel_sq_le g v htr hK) hns0
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2' : (5 / 4 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hc : (7 / 2 : ℝ) ≤ (Real.sqrt 2 + 1 / 2) ^ 2 := by nlinarith
  have hsv := Real.sq_sqrt hnv0
  have hss := Real.sq_sqrt hns0
  have hR0 : 0 ≤ (Real.sqrt 2 + 1 / 2) * K * Real.sqrt nv * Real.sqrt ns := by positivity
  rw [abs_le]
  have hsq : bilin g v s ^ 2 ≤ ((Real.sqrt 2 + 1 / 2) * K * Real.sqrt nv * Real.sqrt ns) ^ 2 := by
    have e : ((Real.sqrt 2 + 1 / 2) * K * Real.sqrt nv * Real.sqrt ns) ^ 2
        = (Real.sqrt 2 + 1 / 2) ^ 2 * K ^ 2 * nv * ns := by
      rw [mul_pow, mul_pow, mul_pow, hsv, hss]
    rw [e]
    refine hB.trans ?_
    have hk : 0 ≤ K ^ 2 * nv * ns := by positivity
    nlinarith
  constructor
  · have := le_of_sq_le_sq_of_nonneg (a := -bilin g v s) (by rw [neg_sq]; exact hsq) hR0
    linarith
  · exact le_of_sq_le_sq_of_nonneg hsq hR0

theorem bilin_add (g h : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → ℝ) (s : Fin 3 → Fin 3 → ℝ) :
    bilin (fun j m => g j m + h j m) v s = bilin g v s + bilin h v s := by
  simp only [bilin, Fin.sum_univ_three]
  ring

theorem curlVec_apply (A : Space →L[ℝ] Space) (j : Fin 3) :
    curlVec A j = ∑ a : Fin 3, ∑ b : Fin 3, alternatingSymbol j a b * A (unitVector a) b := by
  fin_cases j <;> simp [curlVec, unitVector, Fin.sum_univ_three]

theorem stretchForm_eq (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space) :
    stretchForm W v G σ y =
      -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (G σ y) i
          * ((fderiv ℝ (W σ) y (unitVector j) i + fderiv ℝ (W σ) y (unitVector i) j) / 2) * curlVec (G σ y) j)
        + bilin (fun j m => vortGrad (fderiv ℝ (fun x => fderiv ℝ (W σ) x) y) j m) (fun m => v σ y m)
            (fun i j => G σ y (unitVector j) i) := by
  simp only [stretchForm, bilin, curlVec_apply]
  ring

theorem matVec_le_opNorm (A : Space →L[ℝ] Space) (x : Fin 3 → ℝ) :
    ∑ j : Fin 3, matVec (fun j m => A (unitVector m) j) x j ^ 2 ≤ ‖A‖ ^ 2 * ∑ m : Fin 3, x m ^ 2 := by
  set z : Space := ∑ m : Fin 3, x m • unitVector m with hz
  have hzi : ∀ i, z i = x i := by
    intro i
    fin_cases i <;> simp [hz, unitVector, Fin.sum_univ_three]
  have hAz : ∀ j, A z j = matVec (fun j m => A (unitVector m) j) x j := by
    intro j
    simp [hz, matVec, map_smul, Fin.sum_univ_three, mul_comm]
  have hn1 : ‖A z‖ ^ 2 = ∑ j : Fin 3, matVec (fun j m => A (unitVector m) j) x j ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl (fun j _ => by rw [hAz j])
  have hn2 : ‖z‖ ^ 2 = ∑ m : Fin 3, x m ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl (fun m _ => by rw [hzi m])
  rw [← hn1, ← hn2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm z) 2

theorem neg_stretchForm_le (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space)
    {lam Kw : ℝ} (g0 gw : Fin 3 → Fin 3 → ℝ)
    (hS : ∀ u : Fin 3 → ℝ, ∑ i : Fin 3, ∑ j : Fin 3, u i
        * ((fderiv ℝ (W σ) y (unitVector j) i + fderiv ℝ (W σ) y (unitVector i) j) / 2) * u j
      ≤ lam * ∑ i : Fin 3, u i ^ 2)
    (hsplit : ∀ j m, vortGrad (fderiv ℝ (fun x => fderiv ℝ (W σ) x) y) j m = g0 j m + gw j m)
    (htr : gw 0 0 + gw 1 1 + gw 2 2 = 0) (hKw0 : 0 ≤ Kw)
    (hKw : ∀ x : Fin 3 → ℝ, ∑ j : Fin 3, matVec gw x j ^ 2 ≤ Kw ^ 2 * ∑ m : Fin 3, x m ^ 2) :
    -stretchForm W v G σ y ≤ lam * ∑ i : Fin 3, curlVec (G σ y) i ^ 2
      - bilin g0 (fun m => v σ y m) (fun i j => G σ y (unitVector j) i)
      + (Real.sqrt 2 + 1 / 2) * Kw * Real.sqrt (∑ m : Fin 3, v σ y m ^ 2)
        * Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, G σ y (unitVector j) i ^ 2) := by
  rw [stretchForm_eq]
  have hg : (fun j m => vortGrad (fderiv ℝ (fun x => fderiv ℝ (W σ) x) y) j m)
      = fun j m => g0 j m + gw j m := by
    funext j m
    exact hsplit j m
  rw [hg, bilin_add]
  have h1 := hS (fun i => curlVec (G σ y) i)
  have h2 := bilin_abs_le gw (fun m => v σ y m) (fun i j => G σ y (unitVector j) i) htr hKw0 hKw
  have h3 := neg_abs_le (bilin gw (fun m => v σ y m) (fun i j => G σ y (unitVector j) i))
  linarith

def modeBilin (g : Fin 3 → Fin 3 → ℝ) (a : Fin 3 → ℂ) (s : Fin 3 × Fin 3 → ℂ) : ℝ :=
  bilin g (fun m => (a m).re) (fun i j => (s (i, j)).re) + bilin g (fun m => (a m).im) (fun i j => (s (i, j)).im)

def meanVortCoord (W : ℝ → Space → Space) (y : Space) (j m : Fin 3) : ℝ :=
  fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y (unitVector m) j

def fibreTerm {C : Type} (m : ModeWeights C) (b : FlowBounds C) (W v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (ι : ℤ × ℤ) (y : Space) : ℝ :=
  (b.meanStretch y + b.waveStretch y) * cnormSq (curlOfGrad (modeGrad ι G 0 y))
    - modeBilin (meanVortCoord W y) (modeVel ι v 0 y) (modeGrad ι G 0 y)
    + (1 / 2) * (Real.sqrt 2 + 1 / 2) * b.waveVortGrad y
        * (m.len y * cnormSq (modeGrad ι G 0 y) + cnormSq (modeVel ι v 0 y) / m.len y)

theorem cnormSq_eq_vec (a : Fin 3 → ℂ) :
    cnormSq a = ∑ m : Fin 3, (a m).re ^ 2 + ∑ m : Fin 3, (a m).im ^ 2 := by
  simp only [cnormSq, Fin.sum_univ_three, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem cnormSq_eq_mat (s : Fin 3 × Fin 3 → ℂ) :
    cnormSq s = ∑ i : Fin 3, ∑ j : Fin 3, (s (i, j)).re ^ 2 + ∑ i : Fin 3, ∑ j : Fin 3, (s (i, j)).im ^ 2 := by
  simp only [cnormSq, Fintype.sum_prod_type, Fin.sum_univ_three, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem two_term_le {p q r t : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    Real.sqrt p * Real.sqrt r + Real.sqrt q * Real.sqrt t ≤ Real.sqrt (p + q) * Real.sqrt (r + t) := by
  rw [← Real.sqrt_mul (add_nonneg hp hq)]
  apply Real.le_sqrt_of_sq_le
  have h1 := Real.sq_sqrt hp
  have h2 := Real.sq_sqrt hq
  have h3 := Real.sq_sqrt hr
  have h4 := Real.sq_sqrt ht
  nlinarith [sq_nonneg (Real.sqrt p * Real.sqrt t - Real.sqrt q * Real.sqrt r),
    Real.sqrt_nonneg p, Real.sqrt_nonneg q, Real.sqrt_nonneg r, Real.sqrt_nonneg t]

theorem modeBilin_abs_le (g : Fin 3 → Fin 3 → ℝ) (a : Fin 3 → ℂ) (s : Fin 3 × Fin 3 → ℂ)
    (htr : g 0 0 + g 1 1 + g 2 2 = 0) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x : Fin 3 → ℝ, ∑ j : Fin 3, matVec g x j ^ 2 ≤ K ^ 2 * ∑ m : Fin 3, x m ^ 2) :
    |modeBilin g a s| ≤ (Real.sqrt 2 + 1 / 2) * K * Real.sqrt (cnormSq a) * Real.sqrt (cnormSq s) := by
  have h1 := bilin_abs_le g (fun m => (a m).re) (fun i j => (s (i, j)).re) htr hK0 hK
  have h2 := bilin_abs_le g (fun m => (a m).im) (fun i j => (s (i, j)).im) htr hK0 hK
  have hc : 0 ≤ (Real.sqrt 2 + 1 / 2) * K := by positivity
  have h3 := two_term_le (Finset.sum_nonneg (fun m (_ : m ∈ Finset.univ) => sq_nonneg (a m).re))
    (Finset.sum_nonneg (fun m (_ : m ∈ Finset.univ) => sq_nonneg (a m).im))
    (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (s (i, j)).re)))
    (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (s (i, j)).im)))
  rw [cnormSq_eq_vec, cnormSq_eq_mat]
  refine (abs_add_le _ _).trans ?_
  have h4 := mul_le_mul_of_nonneg_left h3 hc
  nlinarith [h1, h2, h4]

theorem fibreTerm_le_charge {C : Type} (m : ModeWeights C) (b : FlowBounds C) (W v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (ι : ℤ × ℤ) (y : Space)
    (hmvg : ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ ≤ b.meanVortGrad y)
    (htr : meanVortCoord W y 0 0 + meanVortCoord W y 1 1 + meanVortCoord W y 2 2 = 0) :
    fibreTerm m b W v G ι y ≤ m.stretchCharge b v G ι 0 y := by
  have hK0 : 0 ≤ b.meanVortGrad y := (norm_nonneg _).trans hmvg
  have hK : ∀ x : Fin 3 → ℝ, ∑ j : Fin 3, matVec (meanVortCoord W y) x j ^ 2
      ≤ b.meanVortGrad y ^ 2 * ∑ m : Fin 3, x m ^ 2 := by
    intro x
    refine (matVec_le_opNorm (fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y) x).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun m _ => sq_nonneg (x m)))
    exact pow_le_pow_left₀ (norm_nonneg _) hmvg 2
  have hb := modeBilin_abs_le (meanVortCoord W y) (modeVel ι v 0 y) (modeGrad ι G 0 y) htr hK0 hK
  have hn := neg_abs_le (modeBilin (meanVortCoord W y) (modeVel ι v 0 y) (modeGrad ι G 0 y))
  simp only [fibreTerm, ModeWeights.stretchCharge]
  linarith

theorem ofReal_le_of_tsum_le {X : ℝ} {Q c : ℤ × ℤ → ℝ} (hQ : Summable Q)
    (hX : X ≤ 2 * Real.pi * ∑' ι, Q ι) (hle : ∀ ι, Q ι ≤ c ι) :
    ENNReal.ofReal X ≤ ENNReal.ofReal (2 * Real.pi) * ∑' ι, ENNReal.ofReal (c ι) := by
  have hQp : Summable (fun ι => max (Q ι) 0) :=
    hQ.abs.of_nonneg_of_le (fun _ => le_max_right _ _) (fun ι => max_le (le_abs_self _) (abs_nonneg _))
  have hs : ENNReal.ofReal (∑' ι, Q ι) ≤ ∑' ι, ENNReal.ofReal (c ι) := by
    calc ENNReal.ofReal (∑' ι, Q ι) ≤ ENNReal.ofReal (∑' ι, max (Q ι) 0) :=
          ENNReal.ofReal_le_ofReal (Summable.tsum_le_tsum (fun ι => le_max_left _ _) hQ hQp)
      _ = ∑' ι, ENNReal.ofReal (max (Q ι) 0) :=
          ENNReal.ofReal_tsum_of_nonneg (fun ι => le_max_right _ _) hQp
      _ ≤ ∑' ι, ENNReal.ofReal (c ι) := by
          refine ENNReal.tsum_le_tsum (fun ι => ?_)
          rcases le_total (Q ι) 0 with h | h
          · rw [max_eq_right h, ENNReal.ofReal_zero]
            exact bot_le
          · rw [max_eq_left h]
            exact ENNReal.ofReal_le_ofReal (hle ι)
  calc ENNReal.ofReal X ≤ ENNReal.ofReal (2 * Real.pi * ∑' ι, Q ι) := ENNReal.ofReal_le_ofReal hX
    _ = ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (∑' ι, Q ι) :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (2 * Real.pi) * ∑' ι, ENNReal.ofReal (c ι) := by gcongr

def curlCLM : (Space →L[ℝ] Space) →L[ℝ] Space :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l •
    ((EuclideanSpace.proj l).comp (ContinuousLinearMap.apply ℝ Space (unitVector j))).smulRight (unitVector i)

theorem curlCLM_apply (A : Space →L[ℝ] Space) : curlCLM A = curlVec A := by
  ext k
  fin_cases k <;> simp [curlCLM, curlVec, unitVector, Fin.sum_univ_three]

theorem vortTrace_eq_zero (f : Space → Space) (hf : ContDiff ℝ 2 f) (y : Space) :
    fderiv ℝ (fun x => curlVec (fderiv ℝ f x)) y (unitVector 0) 0
      + fderiv ℝ (fun x => curlVec (fderiv ℝ f x)) y (unitVector 1) 1
      + fderiv ℝ (fun x => curlVec (fderiv ℝ f x)) y (unitVector 2) 2 = 0 := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hfun : (fun x => curlVec (fderiv ℝ f x)) = fun x => curlCLM (fderiv ℝ f x) := by
    funext x
    rw [curlCLM_apply]
  have hD : fderiv ℝ (fun x => curlVec (fderiv ℝ f x)) y = curlCLM.comp (fderiv ℝ (fderiv ℝ f) y) := by
    rw [hfun]
    exact (curlCLM.hasFDerivAt.comp y (hd y).hasFDerivAt).fderiv
  have hs : IsSymmSndFDerivAt ℝ f y :=
    hf.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  rw [hD]
  simp only [ContinuousLinearMap.comp_apply, curlCLM_apply, curlVec_apply, Fin.sum_univ_three, alternatingSymbol]
  have e01 := congrArg (fun z : Space => z 2) (hs (unitVector 0) (unitVector 1))
  have e02 := congrArg (fun z : Space => z 1) (hs (unitVector 0) (unitVector 2))
  have e12 := congrArg (fun z : Space => z 0) (hs (unitVector 1) (unitVector 2))
  simp only at e01 e02 e12
  norm_num
  linarith

universe u

theorem contDiff_intervalIntegral_param {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (a b : ℝ) (n : ℕ) :
    ∀ (f : E → ℝ → F), ContDiff ℝ n (fun p : E × ℝ => f p.1 p.2) →
      ContDiff ℝ n (fun x => ∫ t in a..b, f x t) := by
  induction n generalizing F with
  | zero =>
    intro f hf
    simp only [CharP.cast_eq_zero, contDiff_zero] at hf ⊢
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf a b
  | succ n ih =>
    intro f hf
    set g : E × ℝ → F := fun p => f p.1 p.2 with hg
    have hd : Differentiable ℝ g := hf.differentiable (by simp)
    set f' : E → ℝ → (E →L[ℝ] F) := fun x t => (fderiv ℝ g (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)
      with hf'
    have hf'c : ContDiff ℝ n (fun p : E × ℝ => f' p.1 p.2) := by
      have h1 : ContDiff ℝ n (fderiv ℝ g) := hf.fderiv_right (by push_cast; exact le_rfl)
      exact h1.clm_comp contDiff_const
    have hder : ∀ x t, HasFDerivAt (fun x => f x t) (f' x t) x := by
      intro x t
      have h := (hd (x, t)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
      exact h
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl]
    rw [contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun x => ∫ t in a..b, f' x t, ih f' hf'c, fun x₀ => ?_⟩
    have hcont : Continuous (fun p : E × ℝ => f' p.1 p.2) := hf'c.continuous
    have hK : IsCompact (Metric.closedBall x₀ 1 ×ˢ Set.uIcc a b) :=
      (isCompact_closedBall x₀ 1).prod isCompact_uIcc
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    have hgc : Continuous g := hf.continuous
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
      (Metric.closedBall_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
    · exact Filter.Eventually.of_forall (fun x =>
        (hgc.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable)
    · exact (hgc.comp (Continuous.prodMk continuous_const continuous_id)).intervalIntegrable a b
    · exact (hcont.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun t ht x hx => hC (x, t) ⟨hx, ?_⟩)
      exact Set.uIoc_subset_uIcc ht
    · exact Filter.Eventually.of_forall (fun t _ x _ => hder x t)

theorem contDiff_component {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : X → Space)
    (hf : ContDiff ℝ 2 f) (i : Fin 3) : ContDiff ℝ 2 (fun x => f x i) := by
  have h := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hf
  exact h

theorem axialRot_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (a : X → ℝ) (b : X → Space)
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) : ContDiff ℝ 2 (fun x => axialRot (a x) (b x)) := by
  have h0 : ContDiff ℝ 2 (fun x => b x 0) := contDiff_component _ hb 0
  have h1 : ContDiff ℝ 2 (fun x => b x 1) := contDiff_component _ hb 1
  have h2 : ContDiff ℝ 2 (fun x => b x 2) := contDiff_component _ hb 2
  have hc : ContDiff ℝ 2 (fun x => Real.cos (a x)) := Real.contDiff_cos.comp ha
  have hs : ContDiff ℝ 2 (fun x => Real.sin (a x)) := Real.contDiff_sin.comp ha
  unfold axialRot
  exact (((hc.mul h0).sub (hs.mul h1)).smul contDiff_const).add
    (((hs.mul h0).add (hc.mul h1)).smul contDiff_const) |>.add (h2.smul contDiff_const)

theorem meanField_contDiff (W : ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) : ContDiff ℝ 2 (meanField W) := by
  have hint : ∀ i : Fin 3, ContDiff ℝ 2
      (fun q : (Space × ℝ) × ℝ => axialRot (-q.2) (W q.1.2 (axialRot q.2 q.1.1)) i) := by
    intro i
    have hin : ContDiff ℝ 2 (fun q : (Space × ℝ) × ℝ => axialRot q.2 q.1.1) :=
      axialRot_comp _ _ contDiff_snd (contDiff_fst.comp contDiff_fst)
    have hWq : ContDiff ℝ 2 (fun q : (Space × ℝ) × ℝ => W q.1.2 (axialRot q.2 q.1.1)) :=
      hW.comp ((contDiff_snd.comp contDiff_fst).prodMk hin)
    have hout : ContDiff ℝ 2 (fun q : (Space × ℝ) × ℝ => axialRot (-q.2) (W q.1.2 (axialRot q.2 q.1.1))) :=
      axialRot_comp _ _ contDiff_snd.neg hWq
    exact contDiff_component _ hout i
  have hmode : ∀ i : Fin 3, ContDiff ℝ 2 (fun y => modeVel (0, 0) W 0 y i) := by
    intro i
    unfold modeVel modeAverage
    simp only [Int.cast_zero, mul_zero, zero_mul, add_zero, Complex.ofReal_zero, neg_zero,
      Complex.exp_zero, one_mul, zero_add]
    refine contDiff_const.mul ?_
    refine contDiff_intervalIntegral_param (E := Space) (F := ℂ) 0 1 2
      (fun y τ => ∫ φ in (0 : ℝ)..(2 * Real.pi), ((axialRot (-φ) (W τ (axialRot φ y)) i : ℝ) : ℂ)) ?_
    refine contDiff_intervalIntegral_param (E := Space × ℝ) (F := ℂ) 0 (2 * Real.pi) 2
      (fun p φ => ((axialRot (-φ) (W p.2 (axialRot φ p.1)) i : ℝ) : ℂ)) ?_
    exact Complex.ofRealCLM.contDiff.comp (hint i)
  unfold meanField
  refine ContDiff.sum (fun i _ => ?_)
  exact (Complex.reCLM.contDiff.comp (hmode i)).smul contDiff_const

private theorem meanVortCoord_trace (W : ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (y : Space) :
    meanVortCoord W y 0 0 + meanVortCoord W y 1 1 + meanVortCoord W y 2 2 = 0 :=
  vortTrace_eq_zero (meanField W) (meanField_contDiff W hW) y

def fibVel (v : ℝ → Space → Space) (y : Space) (τ φ : ℝ) (i : Fin 3) : ℝ :=
  axialRot (-φ) (v τ (axialRot φ y)) i

def fibGrad (G : ℝ → Space → (Space →L[ℝ] Space)) (y : Space) (τ φ : ℝ) (i j : Fin 3) : ℝ :=
  axialRot (-φ) (G τ (axialRot φ y) (axialRot φ (unitVector j))) i

def curlMat (s : Fin 3 → Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * s l j

def fibreBound {C : Type} (m : ModeWeights C) (b : FlowBounds C) (W v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (y : Space) (τ φ : ℝ) : ℝ :=
  (b.meanStretch y + b.waveStretch y) * ∑ i : Fin 3, curlMat (fibGrad G y τ φ) i ^ 2
    - bilin (meanVortCoord W y) (fibVel v y τ φ) (fibGrad G y τ φ)
    + (1 / 2) * (Real.sqrt 2 + 1 / 2) * b.waveVortGrad y
        * (m.len y * ∑ i : Fin 3, ∑ j : Fin 3, fibGrad G y τ φ i j ^ 2
          + (∑ i : Fin 3, fibVel v y τ φ i ^ 2) / m.len y)


def rm (φ : ℝ) (a b : Fin 3) : ℝ := axialRot φ (unitVector b) a

theorem rm_eq (φ : ℝ) : rm φ = ![![Real.cos φ, -Real.sin φ, 0], ![Real.sin φ, Real.cos φ, 0], ![0, 0, 1]] := by
  funext a b
  fin_cases a <;> fin_cases b <;> simp [rm, axialRot, unitVector]

def conjM (φ : ℝ) (M : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  ∑ a : Fin 3, ∑ c : Fin 3, rm φ i a * M a c * rm φ j c

def rotVec (φ : ℝ) (x : Fin 3 → ℝ) (i : Fin 3) : ℝ := ∑ a : Fin 3, rm φ i a * x a

def rotT (φ : ℝ) (x : Fin 3 → ℝ) (a : Fin 3) : ℝ := ∑ i : Fin 3, rm φ i a * x i

theorem curlMat_conjM (φ : ℝ) (M : Fin 3 → Fin 3 → ℝ) (k : Fin 3) :
    curlMat (conjM φ M) k = rotVec φ (curlMat M) k := by
  have h := Real.sin_sq_add_cos_sq φ
  fin_cases k <;> simp [curlMat, conjM, rotVec, rm_eq, alternatingSymbol, Fin.sum_univ_three] <;> grind

theorem sq_rotVec (φ : ℝ) (x : Fin 3 → ℝ) : ∑ i : Fin 3, rotVec φ x i ^ 2 = ∑ i : Fin 3, x i ^ 2 := by
  have h := Real.sin_sq_add_cos_sq φ
  simp [rotVec, rm_eq, Fin.sum_univ_three]
  grind

theorem sq_rotT (φ : ℝ) (x : Fin 3 → ℝ) : ∑ i : Fin 3, rotT φ x i ^ 2 = ∑ i : Fin 3, x i ^ 2 := by
  have h := Real.sin_sq_add_cos_sq φ
  simp [rotT, rm_eq, Fin.sum_univ_three]
  grind

theorem sq_conjM (φ : ℝ) (M : Fin 3 → Fin 3 → ℝ) :
    ∑ i : Fin 3, ∑ j : Fin 3, conjM φ M i j ^ 2 = ∑ i : Fin 3, ∑ j : Fin 3, M i j ^ 2 := by
  have h := Real.sin_sq_add_cos_sq φ
  simp [conjM, rm_eq, Fin.sum_univ_three]
  grind

theorem quad_conjM (φ : ℝ) (M : Fin 3 → Fin 3 → ℝ) (u : Fin 3 → ℝ) :
    ∑ i : Fin 3, ∑ j : Fin 3, u i * conjM φ M i j * u j
      = ∑ a : Fin 3, ∑ c : Fin 3, rotT φ u a * M a c * rotT φ u c := by
  simp only [conjM, rotT, Fin.sum_univ_three]
  ring

theorem bilin_conjM (φ : ℝ) (g : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → ℝ) (s : Fin 3 → Fin 3 → ℝ) :
    bilin (conjM φ g) (rotVec φ v) (conjM φ s) = bilin g v s := by
  have h := Real.sin_sq_add_cos_sq φ
  simp [bilin, conjM, rotVec, rm_eq, alternatingSymbol, Fin.sum_univ_three]
  grind

theorem clm_coord_conj (φ : ℝ) (A : Space →L[ℝ] Space) (i j : Fin 3) :
    A (unitVector j) i = conjM φ (fun a c => axialRot (-φ) (A (axialRot φ (unitVector c))) a) i j := by
  have h := Real.sin_sq_add_cos_sq φ
  fin_cases i <;> fin_cases j <;>
    simp [conjM, rm_eq, axialRot, unitVector, Fin.sum_univ_three, map_add, map_smul] <;> grind

theorem vec_coord_rot (φ : ℝ) (x : Space) (i : Fin 3) :
    x i = rotVec φ (fun a => axialRot (-φ) x a) i := by
  have h := Real.sin_sq_add_cos_sq φ
  fin_cases i <;> simp [rotVec, rm_eq, axialRot, unitVector, Fin.sum_univ_three] <;> grind

def rotCLM (φ : ℝ) : Space →L[ℝ] Space :=
  ((RotationInternal.axialRotEquiv φ).toContinuousLinearEquiv : Space →L[ℝ] Space)

theorem rotCLM_apply (φ : ℝ) (x : Space) : rotCLM φ x = axialRot φ x := rfl

theorem fderiv_equivariant (φ : ℝ) (f : Space → Space) (hf : Differentiable ℝ f)
    (heq : ∀ x, f (axialRot φ x) = axialRot φ (f x)) (y : Space) (a b : Fin 3) :
    fderiv ℝ f (axialRot φ y) (unitVector b) a = conjM φ (fun a c => fderiv ℝ f y (unitVector c) a) a b := by
  have h1 : HasFDerivAt (fun x => f (axialRot φ x)) ((fderiv ℝ f (axialRot φ y)).comp (rotCLM φ)) y := by
    have := (hf (axialRot φ y)).hasFDerivAt.comp y (rotCLM φ).hasFDerivAt
    exact this
  have h2 : HasFDerivAt (fun x => axialRot φ (f x)) ((rotCLM φ).comp (fderiv ℝ f y)) y := by
    have := (rotCLM φ).hasFDerivAt.comp y (hf y).hasFDerivAt
    exact this
  have hfun : (fun x => f (axialRot φ x)) = fun x => axialRot φ (f x) := funext heq
  rw [hfun] at h1
  have heqD := h1.unique h2
  rw [clm_coord_conj φ (fderiv ℝ f (axialRot φ y)) a b]
  congr 1
  funext a' c
  have := congrArg (fun L : Space →L[ℝ] Space => L (unitVector c)) heqD
  simp only [ContinuousLinearMap.comp_apply, rotCLM_apply] at this
  rw [this, RotationInternal.axialRot_neg_self]

def coordMat (A : Space →L[ℝ] Space) (i j : Fin 3) : ℝ := A (unitVector j) i

theorem curlVec_eq_curlMat (A : Space →L[ℝ] Space) (j : Fin 3) : curlVec A j = curlMat (coordMat A) j := by
  rw [curlVec_apply]
  simp only [curlMat, coordMat]

theorem axialRot_eq_rotVec (φ : ℝ) (w : Space) (k : Fin 3) : axialRot φ w k = rotVec φ (fun a => w a) k := by
  fin_cases k <;> simp [rotVec, rm_eq, axialRot, unitVector, Fin.sum_univ_three] <;> ring

theorem box_ae_mem : ∀ᵐ p ∂Internal.ModeRotation.boxMeasure,
    p ∈ Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi) := by
  show ∀ᵐ p ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
    (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))), _
  rw [Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)

theorem integrable_box_of_continuous {E : Type*} [NormedAddCommGroup E] {f : ℝ × ℝ → E} (hf : Continuous f) :
    Integrable f Internal.ModeRotation.boxMeasure := by
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi))).exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) hf.continuousOn
  refine Integrable.mono' (integrable_const K) hf.aestronglyMeasurable ?_
  filter_upwards [box_ae_mem] with p hp
  exact hK p ⟨Set.Ioc_subset_Icc_self hp.1, Set.Ioc_subset_Icc_self hp.2⟩

theorem meanField_rot (hRot : AxialRotationHolds) (W : ℝ → Space → Space)
    (hWc : Continuous (fun z : ℝ × Space => W z.1 z.2)) (ψ : ℝ) (y : Space) :
    meanField W (axialRot ψ y) = axialRot ψ (meanField W y) := by
  have hc : Continuous (fun p : ℝ × ℝ => W (((0 : ℝ), y).1 + p.1) (axialRot p.2 ((0 : ℝ), y).2)) :=
    hWc.comp ((continuous_const.add continuous_fst).prodMk
      (Internal.ModeRotation.continuous_axialRot.comp (continuous_snd.prodMk continuous_const)))
  have hm := Internal.ModeRotation.modeVel_rotation_of hRot (v := W) (0, 0) ψ (z := ((0 : ℝ), y))
    (integrable_box_of_continuous hc)
  simp only at hm
  unfold meanField
  rw [hm]
  ext k
  rw [axialRot_eq_rotVec]
  fin_cases k <;> simp [rotC, rotVec, rm_eq, unitVector, Fin.sum_univ_three, axialRot, Complex.mul_re]

theorem meanGrad_rot (hRot : AxialRotationHolds) (W : ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (φ : ℝ) (y : Space) :
    coordMat (fderiv ℝ (meanField W) (axialRot φ y)) = conjM φ (coordMat (fderiv ℝ (meanField W) y)) := by
  funext a b
  exact fderiv_equivariant φ _ ((meanField_contDiff W hW).differentiable (by norm_num))
    (meanField_rot hRot W hW.continuous φ) y a b

theorem differentiable_curl_fderiv (f : Space → Space) (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (fun x => curlVec (fderiv ℝ f x)) := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hfun : (fun x => curlVec (fderiv ℝ f x)) = fun x => curlCLM (fderiv ℝ f x) := by
    funext x
    rw [curlCLM_apply]
  rw [hfun]
  exact curlCLM.differentiable.comp hd

theorem meanCurl_rot (hRot : AxialRotationHolds) (W : ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (φ : ℝ) (x : Space) :
    curlVec (fderiv ℝ (meanField W) (axialRot φ x)) = axialRot φ (curlVec (fderiv ℝ (meanField W) x)) := by
  ext k
  rw [curlVec_eq_curlMat, meanGrad_rot hRot W hW φ x, curlMat_conjM, axialRot_eq_rotVec]
  congr 1
  funext a
  rw [curlVec_eq_curlMat]

theorem meanVortCoord_rot (hRot : AxialRotationHolds) (W : ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (φ : ℝ) (y : Space) :
    meanVortCoord W (axialRot φ y) = conjM φ (meanVortCoord W y) := by
  funext j m
  exact fderiv_equivariant φ _ (differentiable_curl_fderiv _ (meanField_contDiff W hW))
    (meanCurl_rot hRot W hW φ) y j m

theorem vortGrad_eq (f : Space → Space) (hf : ContDiff ℝ 2 f) (y : Space) (j m : Fin 3) :
    vortGrad (fderiv ℝ (fun x => fderiv ℝ f x) y) j m
      = fderiv ℝ (fun x => curlVec (fderiv ℝ f x)) y (unitVector m) j := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hfun : (fun x => curlVec (fderiv ℝ f x)) = fun x => curlCLM (fderiv ℝ f x) := by
    funext x
    rw [curlCLM_apply]
  have hD : fderiv ℝ (fun x => curlVec (fderiv ℝ f x)) y = curlCLM.comp (fderiv ℝ (fderiv ℝ f) y) := by
    rw [hfun]
    exact (curlCLM.hasFDerivAt.comp y (hd y).hasFDerivAt).fderiv
  rw [hD, ContinuousLinearMap.comp_apply, curlCLM_apply, curlVec_apply]
  rfl

theorem symPartForm_coord (A : Space →L[ℝ] Space) (u : Fin 3 → ℝ) :
    symPartForm A (∑ k : Fin 3, u k • unitVector k) = ∑ i : Fin 3, ∑ j : Fin 3, u i * A (unitVector j) i * u j := by
  simp [symPartForm, Fin.sum_univ_three, map_add, map_smul, PiLp.inner_apply, unitVector]
  ring

theorem norm_sq_coord (u : Fin 3 → ℝ) : ‖∑ k : Fin 3, u k • unitVector k‖ ^ 2 = ∑ i : Fin 3, u i ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_three, unitVector]

private theorem mul_le_half_sq_add (x y : ℝ) {t : ℝ} (ht : 0 < t) : x * y ≤ (t * x ^ 2 + y ^ 2 / t) / 2 := by
  have h : (t * x ^ 2 + y ^ 2 / t) / 2 - x * y = (t * x - y) ^ 2 / (2 * t) := by
    field_simp
    ring
  have h2 : 0 ≤ (t * x - y) ^ 2 / (2 * t) := by positivity
  linarith

private theorem fibre_pointwise (hRot : AxialRotationHolds) {C : Type} (m : ModeWeights C)
    (b : FlowBounds C) (W : ℝ → Space → Space) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hlen : ∀ y, 0 < m.len y)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (y : Space) (τ φ : ℝ) :
    -stretchForm W v G τ (axialRot φ y) ≤ fibreBound m b W v G y τ φ := by
  have hWτ : ContDiff ℝ 2 (fun x => W τ x) := hW.comp ((contDiff_const (c := τ)).prodMk contDiff_id)
  set Ry := axialRot φ y with hRy
  set A : Space →L[ℝ] Space := fderiv ℝ (fun x => curlVec (fderiv ℝ (W τ) x)) Ry
    - fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) Ry with hA
  set gw : Fin 3 → Fin 3 → ℝ := fun j m =>
    vortGrad (fderiv ℝ (fun x => fderiv ℝ (W τ) x) Ry) j m - meanVortCoord W Ry j m with hgw
  have hgwA : gw = fun j m => A (unitVector m) j := by
    funext j m
    simp only [hgw, hA, ContinuousLinearMap.sub_apply, PiLp.sub_apply, vortGrad_eq _ hWτ, meanVortCoord]
  have hKw0 : 0 ≤ b.waveVortGrad y := (norm_nonneg _).trans (hb.waveVortGrad_ge τ φ y)
  have hKw : ∀ x : Fin 3 → ℝ, ∑ j : Fin 3, matVec gw x j ^ 2 ≤ b.waveVortGrad y ^ 2 * ∑ m : Fin 3, x m ^ 2 := by
    intro x
    rw [hgwA]
    refine (matVec_le_opNorm A x).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun m _ => sq_nonneg (x m)))
    exact pow_le_pow_left₀ (norm_nonneg _) (hb.waveVortGrad_ge τ φ y) 2
  have htr : gw 0 0 + gw 1 1 + gw 2 2 = 0 := by
    have h1 := vortTrace_eq_zero (fun x => W τ x) hWτ Ry
    have h2 := meanVortCoord_trace W hW Ry
    simp only [hgw, vortGrad_eq _ hWτ, meanVortCoord]
    simp only [meanVortCoord] at h2
    linarith
  have hS : ∀ u : Fin 3 → ℝ, ∑ i : Fin 3, ∑ j : Fin 3, u i
        * ((fderiv ℝ (W τ) Ry (unitVector j) i + fderiv ℝ (W τ) Ry (unitVector i) j) / 2) * u j
      ≤ (b.meanStretch y + b.waveStretch y) * ∑ i : Fin 3, u i ^ 2 := by
    intro u
    set D := fderiv ℝ (W τ) Ry with hD
    set M := fderiv ℝ (meanField W) Ry with hM
    have e1 : ∑ i : Fin 3, ∑ j : Fin 3, u i * ((D (unitVector j) i + D (unitVector i) j) / 2) * u j
        = ∑ i : Fin 3, ∑ j : Fin 3, u i * M (unitVector j) i * u j
          + ∑ i : Fin 3, ∑ j : Fin 3, u i * (D - M) (unitVector j) i * u j := by
      simp only [Fin.sum_univ_three, ContinuousLinearMap.sub_apply, PiLp.sub_apply]
      ring
    have hmean : ∑ i : Fin 3, ∑ j : Fin 3, u i * M (unitVector j) i * u j
        ≤ b.meanStretch y * ∑ i : Fin 3, u i ^ 2 := by
      have e2 : ∑ i : Fin 3, ∑ j : Fin 3, u i * M (unitVector j) i * u j
          = ∑ i : Fin 3, ∑ j : Fin 3, u i * coordMat M i j * u j := rfl
      rw [e2, hM, meanGrad_rot hRot W hW φ y, quad_conjM, ← sq_rotT φ u]
      have hh := hb.meanStretch_ge y (∑ k : Fin 3, rotT φ u k • unitVector k)
      rw [symPartForm_coord, norm_sq_coord] at hh
      exact hh
    have hwave : ∑ i : Fin 3, ∑ j : Fin 3, u i * (D - M) (unitVector j) i * u j
        ≤ b.waveStretch y * ∑ i : Fin 3, u i ^ 2 := by
      have hh := hb.waveStretch_ge τ φ y (∑ k : Fin 3, u k • unitVector k)
      rw [symPartForm_coord, norm_sq_coord] at hh
      exact (le_abs_self _).trans hh
    rw [e1]
    linarith
  have key := neg_stretchForm_le W v G τ Ry (lam := b.meanStretch y + b.waveStretch y)
    (Kw := b.waveVortGrad y) (meanVortCoord W Ry) gw hS
    (fun j m => by simp only [hgw]; ring) htr hKw0 hKw
  have hs : (fun i j => G τ Ry (unitVector j) i) = conjM φ (fibGrad G y τ φ) := by
    funext i j
    exact clm_coord_conj φ (G τ Ry) i j
  have hvv : (fun m => v τ Ry m) = rotVec φ (fibVel v y τ φ) := by
    funext i
    exact vec_coord_rot φ (v τ Ry) i
  have hcurl : ∑ i : Fin 3, curlVec (G τ Ry) i ^ 2 = ∑ i : Fin 3, curlMat (fibGrad G y τ φ) i ^ 2 := by
    have hc : ∀ i, curlVec (G τ Ry) i = rotVec φ (curlMat (fibGrad G y τ φ)) i := by
      intro i
      rw [curlVec_eq_curlMat, ← curlMat_conjM]
      congr 1
    simp only [hc]
    exact sq_rotVec φ _
  have hbil : bilin (meanVortCoord W Ry) (fun m => v τ Ry m) (fun i j => G τ Ry (unitVector j) i)
      = bilin (meanVortCoord W y) (fibVel v y τ φ) (fibGrad G y τ φ) := by
    rw [hvv, hs, hRy, meanVortCoord_rot hRot W hW φ y, bilin_conjM]
  have hnv : ∑ m : Fin 3, v τ Ry m ^ 2 = ∑ m : Fin 3, fibVel v y τ φ m ^ 2 := by
    have hc : ∀ m, v τ Ry m = rotVec φ (fibVel v y τ φ) m := fun m => congrFun hvv m
    simp only [hc]
    exact sq_rotVec φ _
  have hns : ∑ i : Fin 3, ∑ j : Fin 3, G τ Ry (unitVector j) i ^ 2
      = ∑ i : Fin 3, ∑ j : Fin 3, fibGrad G y τ φ i j ^ 2 := by
    have hc : ∀ i j, G τ Ry (unitVector j) i = conjM φ (fibGrad G y τ φ) i j :=
      fun i j => congrFun (congrFun hs i) j
    simp only [hc]
    exact sq_conjM φ _
  rw [hcurl, hbil, hnv, hns] at key
  set a := ∑ m : Fin 3, fibVel v y τ φ m ^ 2 with ha
  set bb := ∑ i : Fin 3, ∑ j : Fin 3, fibGrad G y τ φ i j ^ 2 with hbb
  have ha0 : 0 ≤ a := Finset.sum_nonneg (fun m _ => sq_nonneg _)
  have hb0 : 0 ≤ bb := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hy := mul_le_half_sq_add (Real.sqrt bb) (Real.sqrt a) (hlen y)
  rw [Real.sq_sqrt ha0, Real.sq_sqrt hb0] at hy
  have hc0 : 0 ≤ (Real.sqrt 2 + 1 / 2) * b.waveVortGrad y := by positivity
  have hy2 := mul_le_mul_of_nonneg_left hy hc0
  have e3 : (Real.sqrt 2 + 1 / 2) * b.waveVortGrad y * Real.sqrt a * Real.sqrt bb
      = (Real.sqrt 2 + 1 / 2) * b.waveVortGrad y * (Real.sqrt bb * Real.sqrt a) := by ring
  unfold fibreBound
  rw [← ha, ← hbb]
  nlinarith [key, hy2, e3]

private theorem continuous_rm (i a : Fin 3) : Continuous (fun φ : ℝ => rm φ i a) := by
  fin_cases i <;> fin_cases a <;> simp [rm_eq] <;> fun_prop

private theorem abs_rm_le (φ : ℝ) (i a : Fin 3) : |rm φ i a| ≤ 1 := by
  rw [rm_eq]
  fin_cases i <;> fin_cases a <;> simp [Real.abs_cos_le_one, Real.abs_sin_le_one]

private theorem fibVel_eq (v : ℝ → Space → Space) (y : Space) (τ φ : ℝ) (i : Fin 3) :
    fibVel v y τ φ i = ∑ a : Fin 3, rm (-φ) i a * v τ (axialRot φ y) a := by
  rw [fibVel, axialRot_eq_rotVec]
  rfl

private theorem fibGrad_eq (G : ℝ → Space → (Space →L[ℝ] Space)) (y : Space) (τ φ : ℝ) (i j : Fin 3) :
    fibGrad G y τ φ i j = ∑ a : Fin 3, ∑ k : Fin 3,
      rm (-φ) i a * rm φ k j * G τ (axialRot φ y) (unitVector k) a := by
  fin_cases i <;> fin_cases j <;>
    simp [fibGrad, rm_eq, axialRot, unitVector, Fin.sum_univ_three, map_add, map_smul] <;> ring

open Internal.ModeRotation in
private theorem memLp_coeff_mul {f c : ℝ × ℝ → ℝ} (hf : MemLp f 2 boxMeasure) (hc : Continuous c)
    (hb : ∀ p, |c p| ≤ 1) : MemLp (fun p => c p * f p) 2 boxMeasure := by
  refine MemLp.of_le hf (hc.aestronglyMeasurable.mul hf.1) (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (hb p)

open Internal.ModeRotation in
private theorem memLp_coord {u : ℝ × ℝ → Space} (hu : MemLp u 2 boxMeasure) (a : Fin 3) :
    MemLp (fun p => u p a) 2 boxMeasure := by
  refine MemLp.of_le hu ?_ (Filter.Eventually.of_forall fun p => PiLp.norm_apply_le (u p) a)
  exact (EuclideanSpace.proj a : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hu.1

open Internal.ModeRotation in
private theorem memLp_fibVel {v : ℝ → Space → Space} {y : Space}
    (hV : MemLp (fun p : ℝ × ℝ => v p.1 (axialRot p.2 y)) 2 boxMeasure) (i : Fin 3) :
    MemLp (fun p : ℝ × ℝ => fibVel v y p.1 p.2 i) 2 boxMeasure := by
  have e : (fun p : ℝ × ℝ => fibVel v y p.1 p.2 i)
      = fun p => ∑ a : Fin 3, rm (-p.2) i a * v p.1 (axialRot p.2 y) a := by
    funext p
    exact fibVel_eq v y p.1 p.2 i
  rw [e]
  refine memLp_finsetSum _ (fun a _ => ?_)
  exact memLp_coeff_mul (memLp_coord hV a) ((continuous_rm i a).comp continuous_snd.neg)
    (fun p => abs_rm_le _ i a)

open Internal.ModeRotation in
private theorem memLp_fibGrad {G : ℝ → Space → (Space →L[ℝ] Space)} {y : Space}
    (hG : ∀ k, MemLp (fun p : ℝ × ℝ => G p.1 (axialRot p.2 y) (unitVector k)) 2 boxMeasure) (i j : Fin 3) :
    MemLp (fun p : ℝ × ℝ => fibGrad G y p.1 p.2 i j) 2 boxMeasure := by
  have e : (fun p : ℝ × ℝ => fibGrad G y p.1 p.2 i j)
      = fun p => ∑ a : Fin 3, ∑ k : Fin 3,
        rm (-p.2) i a * rm p.2 k j * G p.1 (axialRot p.2 y) (unitVector k) a := by
    funext p
    exact fibGrad_eq G y p.1 p.2 i j
  rw [e]
  refine memLp_finsetSum _ (fun a _ => memLp_finsetSum _ (fun k _ => ?_))
  refine memLp_coeff_mul (memLp_coord (hG k) a)
    (((continuous_rm i a).comp continuous_snd.neg).mul ((continuous_rm k j).comp continuous_snd)) ?_
  intro p
  rw [abs_mul]
  exact mul_le_one₀ (abs_rm_le _ i a) (abs_nonneg _) (abs_rm_le _ k j)

open Internal.ModeRotation in
private theorem memLp_fibCurl {G : ℝ → Space → (Space →L[ℝ] Space)} {y : Space}
    (hs : ∀ i j, MemLp (fun p : ℝ × ℝ => fibGrad G y p.1 p.2 i j) 2 boxMeasure) (i : Fin 3) :
    MemLp (fun p : ℝ × ℝ => curlMat (fibGrad G y p.1 p.2) i) 2 boxMeasure := by
  unfold curlMat
  exact memLp_finsetSum _ (fun j _ => memLp_finsetSum _ (fun l _ => (hs l j).const_mul _))

private theorem modeVel_eq_fib (ι : ℤ × ℤ) (v : ℝ → Space → Space) (y : Space) (i : Fin 3) :
    modeVel ι v 0 y i = modeAverage ι (fun τ φ (_ : Unit) => fibVel v y τ φ i) () := by
  simp only [modeVel, modeAverage, fibVel, zero_add]

private theorem modeGrad_eq_fib (ι : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (y : Space)
    (ij : Fin 3 × Fin 3) :
    modeGrad ι G 0 y ij = modeAverage ι (fun τ φ (_ : Unit) => fibGrad G y τ φ ij.1 ij.2) () := by
  simp only [modeGrad, modeAverage, fibGrad, zero_add]

open Internal.ModeRotation in
private theorem curlMode_eq_fib (ι : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (y : Space)
    (hint : ∀ l j, Integrable (fun p : ℝ × ℝ => fibGrad G y p.1 p.2 l j) boxMeasure) (i : Fin 3) :
    curlOfGrad (modeGrad ι G 0 y) i
      = modeAverage ι (fun τ φ (_ : Unit) => curlMat (fibGrad G y τ φ) i) () := by
  have hs := modeAverage_sum ι (κ := Fin 3 × Fin 3) (fun jl => alternatingSymbol i jl.1 jl.2)
    (fun jl τ φ => fibGrad G y τ φ jl.2 jl.1) (fun jl => hint jl.2 jl.1)
  have hc : ∀ τ φ, curlMat (fibGrad G y τ φ) i
      = ∑ jl : Fin 3 × Fin 3, alternatingSymbol i jl.1 jl.2 * fibGrad G y τ φ jl.2 jl.1 := by
    intro τ φ
    rw [curlMat, Fintype.sum_prod_type]
  rw [modeAverage_eq]
  simp only [hc]
  rw [hs, Finset.mul_sum, Fintype.sum_prod_type]
  simp only [curlOfGrad, modeGrad_eq_fib, modeAverage_eq]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

private theorem norm_sq_eq_re (z : ℂ) : ‖z‖ ^ 2 = (z * (starRingEnd ℂ) z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

open Internal.ModeRotation in
private theorem hasSum_bil (hTorus : TorusSquareSumHolds) {κ κ' : Type*} [Fintype κ] [Fintype κ']
    (F : κ → ℝ → ℝ → ℝ) (F' : κ' → ℝ → ℝ → ℝ)
    (hF : ∀ k, MemLp (fun p : ℝ × ℝ => F k p.1 p.2) 2 boxMeasure)
    (hF' : ∀ k, MemLp (fun p : ℝ × ℝ => F' k p.1 p.2) 2 boxMeasure) (c : κ → κ' → ℝ) :
    HasSum (fun ι => ∑ k, ∑ k', c k k' * (modeAverage ι (fun τ φ (_ : Unit) => F k τ φ) ()
        * (starRingEnd ℂ) (modeAverage ι (fun τ φ (_ : Unit) => F' k' τ φ) ())).re)
      ((1 / (2 * Real.pi)) * ∫ p, ∑ k, ∑ k', c k k' * (F k p.1 p.2 * F' k' p.1 p.2) ∂boxMeasure) := by
  have hint : ∀ k k', Integrable (fun p : ℝ × ℝ => F k p.1 p.2 * F' k' p.1 p.2) boxMeasure :=
    fun k k' => (hF k).integrable_mul (hF' k')
  have h := hasSum_sum (s := Finset.univ) (fun k _ => hasSum_sum (s := Finset.univ) (fun k' _ =>
    (StretchTorusInternal.torus_hasSum_mul hTorus (hF k) (hF' k')).mul_left (c k k')))
  have hv : ∑ k, ∑ k', c k k' * (1 / (2 * Real.pi) * ∫ p, F k p.1 p.2 * F' k' p.1 p.2 ∂boxMeasure)
      = (1 / (2 * Real.pi)) * ∫ p, ∑ k, ∑ k', c k k' * (F k p.1 p.2 * F' k' p.1 p.2) ∂boxMeasure := by
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun k' _ => (hint k k').const_mul _)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [integral_finsetSum _ (fun k' _ => (hint k k').const_mul _), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k' _ => ?_)
    rw [integral_const_mul]
    ring
  rw [hv] at h
  exact h

open Internal.ModeRotation in
private theorem hasSum_sqsum (hTorus : TorusSquareSumHolds) {κ : Type*} [Fintype κ]
    (F : κ → ℝ → ℝ → ℝ) (hF : ∀ k, MemLp (fun p : ℝ × ℝ => F k p.1 p.2) 2 boxMeasure) :
    HasSum (fun ι => ∑ k, ‖modeAverage ι (fun τ φ (_ : Unit) => F k τ φ) ()‖ ^ 2)
      ((1 / (2 * Real.pi)) * ∫ p, ∑ k, F k p.1 p.2 ^ 2 ∂boxMeasure) := by
  have h := hasSum_sum (s := Finset.univ) (fun k _ => StretchTorusInternal.torus_hasSum_mul hTorus (hF k) (hF k))
  convert h using 1
  · funext ι
    exact Finset.sum_congr rfl (fun k _ => norm_sq_eq_re _)
  · rw [integral_finsetSum _ (fun k _ => (hF k).integrable_sq), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [sq]

def bc (g : Fin 3 → Fin 3 → ℝ) (m : Fin 3) (lj : Fin 3 × Fin 3) : ℝ :=
  kernel g (fun k => if k = m then 1 else 0) lj.1 lj.2

private theorem bilin_coeff (g : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → ℝ) (s : Fin 3 → Fin 3 → ℝ) :
    bilin g v s = ∑ m : Fin 3, ∑ lj : Fin 3 × Fin 3, bc g m lj * (v m * s lj.1 lj.2) := by
  have hk : ∀ l j, kernel g v l j = ∑ m : Fin 3, v m * bc g m (l, j) := by
    intro l j
    fin_cases l <;> fin_cases j <;>
      simp [bc, kernel, matVec, crossVec, Fin.sum_univ_three, alternatingSymbol] <;> ring
  rw [bilin_eq_sum]
  simp only [hk, Fintype.sum_prod_type, Fin.sum_univ_three]
  ring

private theorem modeBilin_coeff (g : Fin 3 → Fin 3 → ℝ) (a : Fin 3 → ℂ) (s : Fin 3 × Fin 3 → ℂ) :
    modeBilin g a s = ∑ m : Fin 3, ∑ lj : Fin 3 × Fin 3, bc g m lj * (a m * (starRingEnd ℂ) (s lj)).re := by
  rw [modeBilin, bilin_coeff, bilin_coeff, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun lj _ => ?_)
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem fibre_squareSum (hTorus : TorusSquareSumHolds) (hRot : AxialRotationHolds)
    (hLoc : PerturbationLocalSquareIntegrabilityHolds) {C : Type} (m : ModeWeights C) (P : ℝ)
    (b : FlowBounds C) (Γ : Set Symmetry) (W : ℝ → Space → Space) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) :
    ∀ᵐ y : Space, Integrable (fun p : ℝ × ℝ => fibreBound m b W v G y p.1 p.2)
        Internal.ModeRotation.boxMeasure ∧
      HasSum (fun ι => fibreTerm m b W v G ι y)
        ((1 / (2 * Real.pi)) * ∫ p, fibreBound m b W v G y p.1 p.2 ∂Internal.ModeRotation.boxMeasure) := by
  filter_upwards [StretchFibreInternal.ae_memLp_fibre_vel hRot hLoc hv,
    StretchFibreInternal.ae_memLp_fibre_grad hRot hv 0, StretchFibreInternal.ae_memLp_fibre_grad hRot hv 1,
    StretchFibreInternal.ae_memLp_fibre_grad hRot hv 2] with y hV h0 h1 h2
  have hG : ∀ k : Fin 3, MemLp (fun p : ℝ × ℝ => G p.1 (axialRot p.2 y) (unitVector k)) 2
      Internal.ModeRotation.boxMeasure := by
    intro k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
  have hfv := memLp_fibVel hV
  have hfs := memLp_fibGrad hG
  have hfc := memLp_fibCurl hfs
  have hint : ∀ l j, Integrable (fun p : ℝ × ℝ => fibGrad G y p.1 p.2 l j) Internal.ModeRotation.boxMeasure :=
    fun l j => (hfs l j).integrable one_le_two
  set c1 := b.meanStretch y + b.waveStretch y with hc1
  set c2 := (1 / 2) * (Real.sqrt 2 + 1 / 2) * b.waveVortGrad y with hc2
  set L := m.len y with hL
  have HA := hasSum_sqsum hTorus (fun i τ φ => curlMat (fibGrad G y τ φ) i) hfc
  have HB := hasSum_sqsum hTorus (κ := Fin 3 × Fin 3) (fun ij τ φ => fibGrad G y τ φ ij.1 ij.2)
    (fun ij => hfs ij.1 ij.2)
  have HC := hasSum_sqsum hTorus (fun i τ φ => fibVel v y τ φ i) hfv
  have HD := hasSum_bil hTorus (fun i τ φ => fibVel v y τ φ i) (κ' := Fin 3 × Fin 3)
    (fun lj τ φ => fibGrad G y τ φ lj.1 lj.2) hfv (fun lj => hfs lj.1 lj.2) (bc (meanVortCoord W y))
  have hT := ((HA.mul_left c1).sub HD).add (((HB.mul_left L).add (HC.div_const L)).mul_left c2)
  have iA : Integrable (fun p : ℝ × ℝ => ∑ k : Fin 3, curlMat (fibGrad G y p.1 p.2) k ^ 2)
      Internal.ModeRotation.boxMeasure :=
    integrable_finsetSum _ (fun k _ => (hfc k).integrable_sq)
  have iB : Integrable (fun p : ℝ × ℝ => ∑ k : Fin 3 × Fin 3, fibGrad G y p.1 p.2 k.1 k.2 ^ 2)
      Internal.ModeRotation.boxMeasure :=
    integrable_finsetSum _ (fun k _ => (hfs k.1 k.2).integrable_sq)
  have iC : Integrable (fun p : ℝ × ℝ => ∑ k : Fin 3, fibVel v y p.1 p.2 k ^ 2)
      Internal.ModeRotation.boxMeasure :=
    integrable_finsetSum _ (fun k _ => (hfv k).integrable_sq)
  have iD : Integrable (fun p : ℝ × ℝ => ∑ k : Fin 3, ∑ k' : Fin 3 × Fin 3,
      bc (meanVortCoord W y) k k' * (fibVel v y p.1 p.2 k * fibGrad G y p.1 p.2 k'.1 k'.2))
      Internal.ModeRotation.boxMeasure :=
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun k' _ =>
      ((hfv k).integrable_mul (hfs k'.1 k'.2)).const_mul _))
  have hpt : (fun p : ℝ × ℝ => fibreBound m b W v G y p.1 p.2)
      = fun p => c1 * (∑ k : Fin 3, curlMat (fibGrad G y p.1 p.2) k ^ 2)
        - (∑ k : Fin 3, ∑ k' : Fin 3 × Fin 3,
            bc (meanVortCoord W y) k k' * (fibVel v y p.1 p.2 k * fibGrad G y p.1 p.2 k'.1 k'.2))
        + c2 * (L * (∑ k : Fin 3 × Fin 3, fibGrad G y p.1 p.2 k.1 k.2 ^ 2)
          + (∑ k : Fin 3, fibVel v y p.1 p.2 k ^ 2) / L) := by
    funext p
    simp only [fibreBound, bilin_coeff, Fintype.sum_prod_type]
    rfl
  have hBI : Integrable (fun p : ℝ × ℝ => fibreBound m b W v G y p.1 p.2) Internal.ModeRotation.boxMeasure := by
    rw [hpt]
    exact ((iA.const_mul c1).sub iD).add (((iB.const_mul L).add (iC.div_const L)).const_mul c2)
  refine ⟨hBI, ?_⟩
  have hval : (1 / (2 * Real.pi)) * ∫ p, fibreBound m b W v G y p.1 p.2 ∂Internal.ModeRotation.boxMeasure
      = c1 * ((1 / (2 * Real.pi)) * ∫ p, ∑ k : Fin 3, curlMat (fibGrad G y p.1 p.2) k ^ 2
            ∂Internal.ModeRotation.boxMeasure)
        - (1 / (2 * Real.pi)) * ∫ p, ∑ k : Fin 3, ∑ k' : Fin 3 × Fin 3,
            bc (meanVortCoord W y) k k' * (fibVel v y p.1 p.2 k * fibGrad G y p.1 p.2 k'.1 k'.2)
            ∂Internal.ModeRotation.boxMeasure
        + c2 * (L * ((1 / (2 * Real.pi)) * ∫ p, ∑ k : Fin 3 × Fin 3, fibGrad G y p.1 p.2 k.1 k.2 ^ 2
            ∂Internal.ModeRotation.boxMeasure)
          + ((1 / (2 * Real.pi)) * ∫ p, ∑ k : Fin 3, fibVel v y p.1 p.2 k ^ 2
            ∂Internal.ModeRotation.boxMeasure) / L) := by
    have j1 : Integrable (fun p : ℝ × ℝ => c1 * (∑ k : Fin 3, curlMat (fibGrad G y p.1 p.2) k ^ 2)
        - (∑ k : Fin 3, ∑ k' : Fin 3 × Fin 3,
            bc (meanVortCoord W y) k k' * (fibVel v y p.1 p.2 k * fibGrad G y p.1 p.2 k'.1 k'.2)))
        Internal.ModeRotation.boxMeasure := (iA.const_mul c1).sub iD
    have j2 : Integrable (fun p : ℝ × ℝ => c2 * (L * (∑ k : Fin 3 × Fin 3, fibGrad G y p.1 p.2 k.1 k.2 ^ 2)
          + (∑ k : Fin 3, fibVel v y p.1 p.2 k ^ 2) / L)) Internal.ModeRotation.boxMeasure :=
      ((iB.const_mul L).add (iC.div_const L)).const_mul c2
    have e1 := integral_add j1 j2
    have e2 := integral_sub (iA.const_mul c1) iD
    have e3 := integral_const_mul (μ := Internal.ModeRotation.boxMeasure) c1
      (fun p : ℝ × ℝ => ∑ k : Fin 3, curlMat (fibGrad G y p.1 p.2) k ^ 2)
    have e4 := integral_const_mul (μ := Internal.ModeRotation.boxMeasure) c2
      (fun p : ℝ × ℝ => L * (∑ k : Fin 3 × Fin 3, fibGrad G y p.1 p.2 k.1 k.2 ^ 2)
          + (∑ k : Fin 3, fibVel v y p.1 p.2 k ^ 2) / L)
    have e5 := integral_add (iB.const_mul L) (iC.div_const L)
    have e6 := integral_const_mul (μ := Internal.ModeRotation.boxMeasure) L
      (fun p : ℝ × ℝ => ∑ k : Fin 3 × Fin 3, fibGrad G y p.1 p.2 k.1 k.2 ^ 2)
    have e7 := integral_div (μ := Internal.ModeRotation.boxMeasure) L
      (fun p : ℝ × ℝ => ∑ k : Fin 3, fibVel v y p.1 p.2 k ^ 2)
    rw [hpt]
    linear_combination (1 / (2 * Real.pi)) * (e1 + e2 + e3 + e4 + c2 * (e5 + e6 + e7))
  have hfun : ∀ ι, fibreTerm m b W v G ι y
      = c1 * ∑ k : Fin 3, ‖modeAverage ι (fun τ φ (_ : Unit) => curlMat (fibGrad G y τ φ) k) ()‖ ^ 2
        - ∑ k : Fin 3, ∑ k' : Fin 3 × Fin 3, bc (meanVortCoord W y) k k'
            * (modeAverage ι (fun τ φ (_ : Unit) => fibVel v y τ φ k) ()
              * (starRingEnd ℂ) (modeAverage ι (fun τ φ (_ : Unit) => fibGrad G y τ φ k'.1 k'.2) ())).re
        + c2 * (L * ∑ k : Fin 3 × Fin 3, ‖modeAverage ι (fun τ φ (_ : Unit) => fibGrad G y τ φ k.1 k.2) ()‖ ^ 2
          + (∑ k : Fin 3, ‖modeAverage ι (fun τ φ (_ : Unit) => fibVel v y τ φ k) ()‖ ^ 2) / L) := by
    intro ι
    simp only [fibreTerm, cnormSq, modeBilin_coeff, curlMode_eq_fib ι G y hint, modeVel_eq_fib,
      modeGrad_eq_fib]
    rfl
  rw [funext hfun, hval]
  exact hT

private theorem fibre_reduction (hTorus : TorusSquareSumHolds) (hRot : AxialRotationHolds)
    (hLoc : PerturbationLocalSquareIntegrabilityHolds) {C : Type} (m : ModeWeights C) (P : ℝ)
    (b : FlowBounds C) (Γ : Set Symmetry) (W : ℝ → Space → Space) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hlen : ∀ y, 0 < m.len y) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) :
    ∀ᵐ y : Space, Summable (fun ι => fibreTerm m b W v G ι y) ∧
      -(∫ σ in Set.Icc (0 : ℝ) 1, ∫ φ in (0 : ℝ)..(2 * Real.pi), stretchForm W v G σ (axialRot φ y))
        ≤ 2 * Real.pi * ∑' ι, fibreTerm m b W v G ι y := by
  filter_upwards [StretchIntegrableInternal.fibre_stretch_integrable hRot hLoc Γ P W hW v G H g hv,
    fibre_squareSum hTorus hRot hLoc m P b Γ W v G H g hv] with y hI hP
  obtain ⟨hBI, hS⟩ := hP
  refine ⟨hS.summable, ?_⟩
  rw [hS.tsum_eq]
  have hiter : ∫ σ in Set.Icc (0 : ℝ) 1, ∫ φ in (0 : ℝ)..(2 * Real.pi), stretchForm W v G σ (axialRot φ y)
      = ∫ p, stretchForm W v G p.1 (axialRot p.2 y) ∂Internal.ModeRotation.boxMeasure := by
    rw [integral_prod _ hI, integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Ioc (fun σ _ => ?_)
    exact intervalIntegral.integral_of_le (by positivity)
  have hle : ∫ p, -stretchForm W v G p.1 (axialRot p.2 y) ∂Internal.ModeRotation.boxMeasure
      ≤ ∫ p, fibreBound m b W v G y p.1 p.2 ∂Internal.ModeRotation.boxMeasure :=
    integral_mono hI.neg hBI (fun p => fibre_pointwise hRot m b W hb hW hlen v G y p.1 p.2)
  have hpi : 2 * Real.pi * (1 / (2 * Real.pi)) = 1 := by
    field_simp
  rw [hiter, ← integral_neg, ← mul_assoc, hpi, one_mul]
  exact hle

end StretchInternal

open StretchInternal in
theorem stretchMeanBoundHolds_proof_of (hTorus : TorusSquareSumHolds) (hRot : AxialRotationHolds)
    (hLoc : PerturbationLocalSquareIntegrabilityHolds) : StretchMeanBoundHolds := by
  intro C m P b Γ W hb hW hWdiv hlen v G H g hv
  filter_upwards [fibre_reduction hTorus hRot hLoc m P b Γ W hb hW hWdiv hlen v G H g hv] with y hy
  exact ofReal_le_of_tsum_le hy.1 hy.2
    (fun ι => fibreTerm_le_charge m b W v G ι y (hb.meanVortGrad_ge y) (meanVortCoord_trace W hW y))

end Coercive

end Breakdown
