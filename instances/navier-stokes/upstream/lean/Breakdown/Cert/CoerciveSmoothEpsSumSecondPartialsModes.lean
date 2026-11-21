import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoerciveSmoothPieceEpsSumSecondPartialsMode
import Breakdown.Cert.CoerciveSmoothEpsSumSecondPartialsSquare

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothEpsSumSecondPartials

def vortRe (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : Space :=
  ∑ i : Fin 3, (curlOfGrad (modeGrad ι (gradField v) σ y) i).re • unitVector i

def vortIm (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : Space :=
  ∑ i : Fin 3, (curlOfGrad (modeGrad ι (gradField v) σ y) i).im • unitVector i

def sspOf (f : Space → Space) (y : Space) : Space :=
  secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ f x) y)

theorem vortRe_contDiff {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ)
    (σ : ℝ) : ContDiff ℝ 2 (vortRe v ι σ) := by
  exact Internal.SmoothPieceEpsSumSecondPartials.vortRe_contDiff hv ι σ

theorem vortIm_contDiff {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ)
    (σ : ℝ) : ContDiff ℝ 2 (vortIm v ι σ) := by
  exact Internal.SmoothPieceEpsSumSecondPartials.vortIm_contDiff hv ι σ

theorem fderiv_vortRe_apply {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ)
    (σ : ℝ) (y : Space) (l : Fin 3) :
    fderiv ℝ (vortRe v ι σ) y (unitVector l) =
      ∑ i : Fin 3, (curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) σ y) (i, l)).re • unitVector i := by
  exact Internal.SmoothPieceEpsSumSecondPartials.fderiv_vortRe_apply hv ι σ y l

theorem fderiv_vortIm_apply {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ)
    (σ : ℝ) (y : Space) (l : Fin 3) :
    fderiv ℝ (vortIm v ι σ) y (unitVector l) =
      ∑ i : Fin 3, (curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) σ y) (i, l)).im • unitVector i := by
  exact Internal.SmoothPieceEpsSumSecondPartials.fderiv_vortIm_apply hv ι σ y l

theorem curl_sumSecondPartials_mode {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ)
    (σ : ℝ) (y : Space) (i : Fin 3) :
    curlOfGrad (modeGrad ι (gradField (fun s x => -secondDerivTrace (secondDerivField v s x))) σ y) i =
      -(((sspOf (vortRe v ι σ) y i : ℝ) : ℂ) + ((sspOf (vortIm v ι σ) y i : ℝ) : ℂ) * Complex.I) := by
  exact Internal.SmoothPieceEpsSumSecondPartials.curl_sumSecondPartials_mode hv ι σ y i

theorem sum_unit_apply (c : Fin 3 → ℝ) (i : Fin 3) : (∑ j : Fin 3, c j • unitVector j) i = c i := by
  fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

theorem norm_sq_space (x : Space) : ‖x‖ ^ 2 = ∑ i : Fin 3, x i ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

theorem inner_space (x z : Space) : inner ℝ x z = ∑ i : Fin 3, x i * z i := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

theorem norm_sq_sum_unit (c : Fin 3 → ℝ) : ‖∑ j : Fin 3, c j • unitVector j‖ ^ 2 = ∑ j : Fin 3, c j ^ 2 := by
  rw [norm_sq_space]
  simp only [sum_unit_apply]

theorem re_I_cdot (a : ℝ) (z L : Fin 3 → ℂ) (P Q DP DQ : Space)
    (hz : ∀ i, z i = ((P i : ℝ) : ℂ) + ((Q i : ℝ) : ℂ) * Complex.I)
    (hL : ∀ i, L i = -(((DP i : ℝ) : ℂ) + ((DQ i : ℝ) : ℂ) * Complex.I)) :
    (Complex.I * (a : ℂ) * cdot z L).re = a * (inner ℝ DP Q - inner ℝ DQ P) := by
  simp only [cdot, Fin.sum_univ_three, hz, hL, inner_space]
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem grad_pair_le (D : Space →L[ℝ] ℝ) (P Q : Space) (A B : Fin 3 → Space) :
    |∑ l : Fin 3, D (unitVector l) * (inner ℝ (A l) Q - inner ℝ (B l) P)|
      ≤ ‖D‖ * (Real.sqrt (∑ l : Fin 3, (‖A l‖ ^ 2 + ‖B l‖ ^ 2)) * Real.sqrt (‖P‖ ^ 2 + ‖Q‖ ^ 2)) := by
  set X : Fin 3 → ℝ := fun l => inner ℝ (A l) Q - inner ℝ (B l) P with hX
  have e : ∑ l : Fin 3, D (unitVector l) * X l = D (∑ l : Fin 3, X l • unitVector l) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hXl : ∀ l, X l ^ 2 ≤ (‖A l‖ ^ 2 + ‖B l‖ ^ 2) * (‖P‖ ^ 2 + ‖Q‖ ^ 2) := by
    intro l
    have h1 : |X l| ≤ ‖A l‖ * ‖Q‖ + ‖B l‖ * ‖P‖ :=
      (abs_sub _ _).trans (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))
    have h2 : X l ^ 2 ≤ (‖A l‖ * ‖Q‖ + ‖B l‖ * ‖P‖) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith [sq_nonneg (‖A l‖ * ‖P‖ - ‖B l‖ * ‖Q‖)]
  have hS : ‖∑ l : Fin 3, X l • unitVector l‖
      ≤ Real.sqrt (∑ l : Fin 3, (‖A l‖ ^ 2 + ‖B l‖ ^ 2)) * Real.sqrt (‖P‖ ^ 2 + ‖Q‖ ^ 2) := by
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun l _ => by positivity), ← Real.sqrt_sq (norm_nonneg _),
      norm_sq_sum_unit]
    refine Real.sqrt_le_sqrt ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun l _ => hXl l
  show |∑ l : Fin 3, D (unitVector l) * X l| ≤ _
  rw [e, ← Real.norm_eq_abs]
  exact (D.le_opNorm _).trans (mul_le_mul_of_nonneg_left hS (norm_nonneg _))

theorem vortRe_apply (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) (i : Fin 3) :
    vortRe v ι σ y i = (curlOfGrad (modeGrad ι (gradField v) σ y) i).re := by
  unfold vortRe
  exact sum_unit_apply _ i

theorem vortIm_apply (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) (i : Fin 3) :
    vortIm v ι σ y i = (curlOfGrad (modeGrad ι (gradField v) σ y) i).im := by
  unfold vortIm
  exact sum_unit_apply _ i

theorem norm_sq_complex (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem vortAmp_eq (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    vortAmp (gradField v) ι σ y = Real.sqrt (‖vortRe v ι σ y‖ ^ 2 + ‖vortIm v ι σ y‖ ^ 2) := by
  unfold vortAmp cnormSq
  congr 1
  rw [norm_sq_space, norm_sq_space, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [vortRe_apply, vortIm_apply, norm_sq_complex]

theorem vortGradAmp_eq {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ)
    (σ : ℝ) (y : Space) :
    vortGradAmp (secondDerivField v) ι σ y = Real.sqrt (∑ l : Fin 3,
      (‖fderiv ℝ (vortRe v ι σ) y (unitVector l)‖ ^ 2 + ‖fderiv ℝ (vortIm v ι σ) y (unitVector l)‖ ^ 2)) := by
  unfold vortGradAmp cnormSq
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [fderiv_vortRe_apply hv, fderiv_vortIm_apply hv, norm_sq_sum_unit, norm_sq_sum_unit,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_sq_complex]

theorem continuous_sspOf {f : Space → Space} (hf : ContDiff ℝ 2 f) : Continuous (sspOf f) := by
  have h1 : ContDiff ℝ 1 (fun x => fderiv ℝ f x) := hf.fderiv_right (by norm_num)
  have h2 : Continuous (fun x => fderiv ℝ (fun x => fderiv ℝ f x) x) := h1.continuous_fderiv (by norm_num)
  unfold sspOf secondDerivTrace
  exact continuous_finsetSum _ fun j _ => (h2.clm_apply continuous_const).clm_apply continuous_const

def sspAmp (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  Real.sqrt (cnormSq (curlOfGrad (modeGrad ι (gradField (fun s x => -secondDerivTrace (secondDerivField v s x))) σ y)))

theorem norm_le_sqrt_add (x z : ℝ) (hx : 0 ≤ x) : x ≤ Real.sqrt (x ^ 2 + z ^ 2) := by
  calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx).symm
    _ ≤ Real.sqrt (x ^ 2 + z ^ 2) := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))

theorem norm_vortRe_le (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    ‖vortRe v ι σ y‖ ≤ vortAmp (gradField v) ι σ y := by
  rw [vortAmp_eq]
  exact norm_le_sqrt_add _ _ (norm_nonneg _)

theorem norm_vortIm_le (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    ‖vortIm v ι σ y‖ ≤ vortAmp (gradField v) ι σ y := by
  rw [vortAmp_eq, add_comm]
  exact norm_le_sqrt_add _ _ (norm_nonneg _)

theorem vec_expand (h : Space) : h = ∑ l : Fin 3, h l • unitVector l := by
  ext i
  exact (sum_unit_apply (fun l => h l) i).symm

theorem opNorm_le_cols (D : Space →L[ℝ] Space) :
    ‖D‖ ≤ Real.sqrt (∑ l : Fin 3, ‖D (unitVector l)‖ ^ 2) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun h => ?_
  have e : D h = ∑ l : Fin 3, h l • D (unitVector l) := by
    conv_lhs => rw [vec_expand h]
    rw [map_sum]
    exact Finset.sum_congr rfl fun l _ => map_smul _ _ _
  have hn : Real.sqrt (∑ l : Fin 3, |h l| ^ 2) = ‖h‖ := by
    rw [← Real.sqrt_sq (norm_nonneg h), norm_sq_space]
    simp only [sq_abs]
  calc ‖D h‖ ≤ ∑ l : Fin 3, ‖h l • D (unitVector l)‖ := by rw [e]; exact norm_sum_le _ _
    _ = ∑ l : Fin 3, |h l| * ‖D (unitVector l)‖ := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ Real.sqrt (∑ l : Fin 3, |h l| ^ 2) * Real.sqrt (∑ l : Fin 3, ‖D (unitVector l)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt (∑ l : Fin 3, ‖D (unitVector l)‖ ^ 2) * ‖h‖ := by rw [hn, mul_comm]

theorem norm_fderiv_vortRe_le {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ)
    (σ : ℝ) (y : Space) : ‖fderiv ℝ (vortRe v ι σ) y‖ ≤ vortGradAmp (secondDerivField v) ι σ y := by
  refine (opNorm_le_cols _).trans ?_
  rw [vortGradAmp_eq hv]
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun l _ => le_add_of_nonneg_right (sq_nonneg _))

theorem norm_fderiv_vortIm_le {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ)
    (σ : ℝ) (y : Space) : ‖fderiv ℝ (vortIm v ι σ) y‖ ≤ vortGradAmp (secondDerivField v) ι σ y := by
  refine (opNorm_le_cols _).trans ?_
  rw [vortGradAmp_eq hv]
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun l _ => le_add_of_nonneg_left (sq_nonneg _))

theorem norm_sspOf_vortRe_le {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ)
    (σ : ℝ) (y : Space) : ‖sspOf (vortRe v ι σ) y‖ ≤ sspAmp v ι σ y := by
  rw [← Real.sqrt_sq (norm_nonneg _), sspAmp]
  refine Real.sqrt_le_sqrt ?_
  rw [norm_sq_space, cnormSq]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_sq_complex, curl_sumSecondPartials_mode hv]
  simp
  try positivity

theorem norm_sspOf_vortIm_le {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ)
    (σ : ℝ) (y : Space) : ‖sspOf (vortIm v ι σ) y‖ ≤ sspAmp v ι σ y := by
  rw [← Real.sqrt_sq (norm_nonneg _), sspAmp]
  refine Real.sqrt_le_sqrt ?_
  rw [norm_sq_space, cnormSq]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_sq_complex, curl_sumSecondPartials_mode hv]
  simp
  try positivity

theorem abs_alternatingSymbol_le (i j l : Fin 3) : |alternatingSymbol i j l| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> norm_num [alternatingSymbol]

theorem norm_symbol_mul_le {κ : Type*} [Fintype κ] (i j l : Fin 3) (x : κ → ℂ) (k : κ) :
    ‖(alternatingSymbol i j l : ℂ) * x k‖ ≤ ∑ t, ‖x t‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_of_le_one_left (norm_nonneg _) (abs_alternatingSymbol_le _ _ _)).trans
    (Finset.single_le_sum (fun t _ => norm_nonneg (x t)) (Finset.mem_univ k))

theorem norm_curlOfGrad_le (g : Fin 3 × Fin 3 → ℂ) (i : Fin 3) : ‖curlOfGrad g i‖ ≤ 9 * ∑ t, ‖g t‖ := by
  unfold curlOfGrad
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun l _ => norm_symbol_mul_le i j l g (l, j))).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num
  ring_nf
  exact le_rfl

theorem norm_curlGradOfSecondDeriv_le (h : Fin 3 × Fin 3 × Fin 3 → ℂ) (il : Fin 3 × Fin 3) :
    ‖curlGradOfSecondDeriv h il‖ ≤ 9 * ∑ t, ‖h t‖ := by
  unfold curlGradOfSecondDeriv
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun m _ => norm_symbol_mul_le il.1 j m h (m, il.2, j))).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num
  ring_nf
  exact le_rfl

theorem sqrt_cnormSq_le {κ : Type*} [Fintype κ] (x : κ → ℂ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ k, ‖x k‖ ≤ B) :
    Real.sqrt (cnormSq x) ≤ Real.sqrt (Fintype.card κ) * B := by
  calc Real.sqrt (cnormSq x) ≤ Real.sqrt (∑ _k : κ, B ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hB k) 2)
    _ = Real.sqrt (Fintype.card κ) * B := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hB0]

theorem memLp_vortAmp {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ) :
    MemLp (vortAmp (gradField v) ι σ) 2 volume := by
  have hS : MemLp (fun y => ∑ t, ‖modeGrad ι (gradField v) σ y t‖) 2 volume :=
    memLp_finsetSum _ fun t _ => (Internal.SmoothEpsSumSecondPartialsSquare.memLp_grad_entry hv ι σ t).norm
  have hB := (hS.const_mul 9).const_mul (Real.sqrt (Fintype.card (Fin 3)))
  have hc : Continuous (vortAmp (gradField v) ι σ) := by
    have e : vortAmp (gradField v) ι σ = fun y => Real.sqrt (‖vortRe v ι σ y‖ ^ 2 + ‖vortIm v ι σ y‖ ^ 2) :=
      funext fun y => vortAmp_eq v ι σ y
    rw [e]
    exact (((vortRe_contDiff hv ι σ).continuous.norm.pow 2).add
      ((vortIm_contDiff hv ι σ).continuous.norm.pow 2)).sqrt
  refine hB.of_le hc.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ ∑ t, ‖modeGrad ι (gradField v) σ y t‖ := Finset.sum_nonneg fun t _ => norm_nonneg _
  have hA : 0 ≤ vortAmp (gradField v) ι σ y := Real.sqrt_nonneg _
  rw [Real.norm_of_nonneg hA, Real.norm_of_nonneg (by positivity)]
  exact sqrt_cnormSq_le _ (by positivity) fun i => norm_curlOfGrad_le _ i

theorem memLp_vortGradAmp {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ)
    (σ : ℝ) : MemLp (vortGradAmp (secondDerivField v) ι σ) 2 volume := by
  have hS : MemLp (fun y => ∑ t, ‖modeSecondDeriv ι (secondDerivField v) σ y t‖) 2 volume :=
    memLp_finsetSum _ fun t _ => (Internal.SmoothEpsSumSecondPartialsSquare.memLp_secondDeriv_entry hv ι σ t).norm
  have hB := (hS.const_mul 9).const_mul (Real.sqrt (Fintype.card (Fin 3 × Fin 3)))
  have hc : Continuous (vortGradAmp (secondDerivField v) ι σ) := by
    have e : vortGradAmp (secondDerivField v) ι σ = fun y => Real.sqrt (∑ l : Fin 3,
        (‖fderiv ℝ (vortRe v ι σ) y (unitVector l)‖ ^ 2 + ‖fderiv ℝ (vortIm v ι σ) y (unitVector l)‖ ^ 2)) :=
      funext fun y => vortGradAmp_eq hv ι σ y
    rw [e]
    have hpd := (vortRe_contDiff hv ι σ).continuous_fderiv (by norm_num)
    have hqd := (vortIm_contDiff hv ι σ).continuous_fderiv (by norm_num)
    exact (continuous_finsetSum _ fun l _ => ((hpd.clm_apply continuous_const).norm.pow 2).add
      ((hqd.clm_apply continuous_const).norm.pow 2)).sqrt
  refine hB.of_le hc.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ ∑ t, ‖modeSecondDeriv ι (secondDerivField v) σ y t‖ := Finset.sum_nonneg fun t _ => norm_nonneg _
  have hA : 0 ≤ vortGradAmp (secondDerivField v) ι σ y := Real.sqrt_nonneg _
  rw [Real.norm_of_nonneg hA, Real.norm_of_nonneg (by positivity)]
  exact sqrt_cnormSq_le _ (by positivity) fun il => norm_curlGradOfSecondDeriv_le _ il

theorem sspAmp_eq {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) : sspAmp v ι σ y = Real.sqrt (‖sspOf (vortRe v ι σ) y‖ ^ 2 + ‖sspOf (vortIm v ι σ) y‖ ^ 2) := by
  unfold sspAmp cnormSq
  congr 1
  rw [norm_sq_space, norm_sq_space, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_sq_complex, curl_sumSecondPartials_mode hv]
  simp

theorem memLp_sspAmp {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ) :
    MemLp (sspAmp v ι σ) 2 volume := by
  have hS : MemLp (fun y => ∑ t, ‖modeGrad ι (gradField (fun s x => -secondDerivTrace (secondDerivField v s x))) σ y t‖)
      2 volume :=
    memLp_finsetSum _ fun t _ => (Internal.SmoothEpsSumSecondPartialsSquare.memLp_sspGrad_entry hv ι σ t).norm
  have hB := (hS.const_mul 9).const_mul (Real.sqrt (Fintype.card (Fin 3)))
  have hc : Continuous (sspAmp v ι σ) := by
    rw [funext fun y => sspAmp_eq hv ι σ y]
    exact (((continuous_sspOf (vortRe_contDiff hv ι σ)).norm.pow 2).add
      ((continuous_sspOf (vortIm_contDiff hv ι σ)).norm.pow 2)).sqrt
  refine hB.of_le hc.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ ∑ t, ‖modeGrad ι (gradField (fun s x => -secondDerivTrace (secondDerivField v s x))) σ y t‖ :=
    Finset.sum_nonneg fun t _ => norm_nonneg _
  have hA : 0 ≤ sspAmp v ι σ y := Real.sqrt_nonneg _
  rw [Real.norm_of_nonneg hA, Real.norm_of_nonneg (by positivity)]
  exact sqrt_cnormSq_le _ (by positivity) fun i => norm_curlOfGrad_le _ i

theorem integrable_amp_pair {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ)
    (σ : ℝ) :
    Integrable (fun y => vortGradAmp (secondDerivField v) ι σ y * vortAmp (gradField v) ι σ y) :=
  (memLp_vortGradAmp hv ι σ).integrable_mul (memLp_vortAmp hv ι σ)

theorem integrable_grad_pair {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ)
    (σ : ℝ) :
    Integrable (fun y => ‖fderiv ℝ (vortRe v ι σ) y‖ * ‖vortIm v ι σ y‖
      + ‖fderiv ℝ (vortIm v ι σ) y‖ * ‖vortRe v ι σ y‖) := by
  have hp := vortRe_contDiff hv ι σ
  have hq := vortIm_contDiff hv ι σ
  refine ((integrable_amp_pair hv ι σ).const_mul 2).mono'
    (((hp.continuous_fderiv (by norm_num)).norm.mul hq.continuous.norm).add
      ((hq.continuous_fderiv (by norm_num)).norm.mul hp.continuous.norm)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have hA := Real.sqrt_nonneg (cnormSq (curlOfGrad (modeGrad ι (gradField v) σ y)))
  have hG := Real.sqrt_nonneg (cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) σ y)))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), two_mul]
  exact add_le_add (mul_le_mul (norm_fderiv_vortRe_le hv ι σ y) (norm_vortIm_le v ι σ y) (norm_nonneg _) hG)
    (mul_le_mul (norm_fderiv_vortIm_le hv ι σ y) (norm_vortRe_le v ι σ y) (norm_nonneg _) hG)

theorem integrable_ssp_pair {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ)
    (σ : ℝ) :
    Integrable (fun y => ‖sspOf (vortRe v ι σ) y‖ * ‖vortIm v ι σ y‖
      + ‖sspOf (vortIm v ι σ) y‖ * ‖vortRe v ι σ y‖) := by
  have hp := vortRe_contDiff hv ι σ
  have hq := vortIm_contDiff hv ι σ
  have hI : Integrable (fun y => sspAmp v ι σ y * vortAmp (gradField v) ι σ y) :=
    (memLp_sspAmp hv ι σ).integrable_mul (memLp_vortAmp hv ι σ)
  refine (hI.const_mul 2).mono'
    (((continuous_sspOf hp).norm.mul hq.continuous.norm).add
      ((continuous_sspOf hq).norm.mul hp.continuous.norm)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have hL : 0 ≤ sspAmp v ι σ y := Real.sqrt_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), two_mul]
  exact add_le_add (mul_le_mul (norm_sspOf_vortRe_le hv ι σ y) (norm_vortIm_le v ι σ y) (norm_nonneg _) hL)
    (mul_le_mul (norm_sspOf_vortIm_le hv ι σ y) (norm_vortRe_le v ι σ y) (norm_nonneg _) hL)

theorem mode_lower (hSsp : WeightedSumSecondPartialsPairingHolds) {P : ℝ} {v : ℝ → Space → Space}
    (hv : IsSmoothPerturbation P v) {a : Space → ℝ} {K : NNReal} (ha : LipschitzWith K a) {A Ad : ℝ}
    (haB : ∀ y, |a y| ≤ A) (hgB : ∀ y, ‖fderiv ℝ a y‖ ≤ Ad) (ι : ℤ × ℤ) (σ : ℝ) :
    -(∫ y, ‖fderiv ℝ a y‖ * vortGradAmp (secondDerivField v) ι σ y * vortAmp (gradField v) ι σ y) ≤
      ∫ y, (Complex.I * (a y : ℂ) * cdot (curlOfGrad (modeGrad ι (gradField v) σ y))
        (curlOfGrad (modeGrad ι (gradField (fun s x => -secondDerivTrace (secondDerivField v s x))) σ y))).re := by
  have hp := vortRe_contDiff hv ι σ
  have hq := vortIm_contDiff hv ι σ
  have hac : Continuous a := ha.continuous
  have hpc : Continuous (vortRe v ι σ) := hp.continuous
  have hqc : Continuous (vortIm v ι σ) := hq.continuous
  have hpd : Continuous (fun y => fderiv ℝ (vortRe v ι σ) y) := hp.continuous_fderiv (by norm_num)
  have hqd : Continuous (fun y => fderiv ℝ (vortIm v ι σ) y) := hq.continuous_fderiv (by norm_num)
  have hpl := continuous_sspOf hp
  have hql := continuous_sspOf hq
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (haB 0)
  have hAd0 : 0 ≤ Ad := (norm_nonneg _).trans (hgB 0)
  have e1 : ∀ y, (Complex.I * (a y : ℂ) * cdot (curlOfGrad (modeGrad ι (gradField v) σ y))
      (curlOfGrad (modeGrad ι (gradField (fun s x => -secondDerivTrace (secondDerivField v s x))) σ y))).re =
      a y * (inner ℝ (sspOf (vortRe v ι σ) y) (vortIm v ι σ y)
        - inner ℝ (sspOf (vortIm v ι σ) y) (vortRe v ι σ y)) := by
    intro y
    refine re_I_cdot _ _ _ (vortRe v ι σ y) (vortIm v ι σ y) _ _ (fun i => ?_)
      (fun i => curl_sumSecondPartials_mode hv ι σ y i)
    rw [vortRe_apply, vortIm_apply, Complex.re_add_im]
  have hX : ∀ (D E : Space → Space) y, |inner ℝ (D y) (vortIm v ι σ y) - inner ℝ (E y) (vortRe v ι σ y)|
      ≤ ‖D y‖ * ‖vortIm v ι σ y‖ + ‖E y‖ * ‖vortRe v ι σ y‖ := fun D E y =>
    (abs_sub _ _).trans (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))
  have int1 : Integrable (fun y => a y * (inner ℝ (secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ (vortRe v ι σ) x) y))
      (vortIm v ι σ y) - inner ℝ (secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ (vortIm v ι σ) x) y)) (vortRe v ι σ y))) := by
    refine ((integrable_ssp_pair hv ι σ).const_mul A).mono'
      (hac.mul (((continuous_inner).comp (hpl.prodMk hqc)).sub
        ((continuous_inner).comp (hql.prodMk hpc)))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (haB y) (hX (sspOf (vortRe v ι σ)) (sspOf (vortIm v ι σ)) y) (abs_nonneg _) hA0
  have hgm : AEStronglyMeasurable (fun y => ‖fderiv ℝ a y‖) volume :=
    (measurable_fderiv ℝ a).norm.aestronglyMeasurable
  have hXc : Continuous (fun y => ‖fderiv ℝ (vortRe v ι σ) y‖ * ‖vortIm v ι σ y‖
      + ‖fderiv ℝ (vortIm v ι σ) y‖ * ‖vortRe v ι σ y‖) :=
    (hpd.norm.mul hqc.norm).add (hqd.norm.mul hpc.norm)
  have hXn : ∀ y, 0 ≤ ‖fderiv ℝ (vortRe v ι σ) y‖ * ‖vortIm v ι σ y‖
      + ‖fderiv ℝ (vortIm v ι σ) y‖ * ‖vortRe v ι σ y‖ := fun y => by positivity
  have int2 : Integrable (fun y => ‖fderiv ℝ a y‖ * (‖fderiv ℝ (vortRe v ι σ) y‖ * ‖vortIm v ι σ y‖
      + ‖fderiv ℝ (vortIm v ι σ) y‖ * ‖vortRe v ι σ y‖)) := by
    refine ((integrable_grad_pair hv ι σ).const_mul Ad).mono' (hgm.mul hXc.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hXn y))]
    exact mul_le_mul_of_nonneg_right (hgB y) (hXn y)
  have int3 : Integrable (fun y => |a y| * (‖fderiv ℝ (vortRe v ι σ) y‖ * ‖vortIm v ι σ y‖
      + ‖fderiv ℝ (vortIm v ι σ) y‖ * ‖vortRe v ι σ y‖) / (1 + ‖y‖)) := by
    refine ((integrable_grad_pair hv ι σ).const_mul A).mono'
      (((hac.abs.mul hXc).div (continuous_const.add continuous_norm)
        (fun y => (add_pos_of_pos_of_nonneg one_pos (norm_nonneg y)).ne')).aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_)
    have h1 : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg _)
    have h0 : 0 ≤ |a y| * (‖fderiv ℝ (vortRe v ι σ) y‖ * ‖vortIm v ι σ y‖
      + ‖fderiv ℝ (vortIm v ι σ) y‖ * ‖vortRe v ι σ y‖) := mul_nonneg (abs_nonneg _) (hXn y)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h0 (by positivity))]
    exact (div_le_self h0 h1).trans (mul_le_mul_of_nonneg_right (haB y) (hXn y))
  have hL := hSsp a K (vortRe v ι σ) (vortIm v ι σ) ha hp hq int1 int2 int3
  have eR : (∫ y, (Complex.I * (a y : ℂ) * cdot (curlOfGrad (modeGrad ι (gradField v) σ y))
      (curlOfGrad (modeGrad ι (gradField (fun s x => -secondDerivTrace (secondDerivField v s x))) σ y))).re) =
      ∫ y, a y * (inner ℝ (secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ (vortRe v ι σ) x) y))
      (vortIm v ι σ y) - inner ℝ (secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ (vortIm v ι σ) x) y)) (vortRe v ι σ y)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => e1 y)
  rw [eR, hL, neg_le_neg_iff]
  have hamp := integrable_amp_pair hv ι σ
  have hpt : ∀ y, |∑ l : Fin 3, fderiv ℝ a y (unitVector l)
      * (inner ℝ (fderiv ℝ (vortRe v ι σ) y (unitVector l)) (vortIm v ι σ y)
        - inner ℝ (fderiv ℝ (vortIm v ι σ) y (unitVector l)) (vortRe v ι σ y))|
      ≤ ‖fderiv ℝ a y‖ * vortGradAmp (secondDerivField v) ι σ y * vortAmp (gradField v) ι σ y := by
    intro y
    rw [vortGradAmp_eq hv, vortAmp_eq, mul_assoc]
    exact grad_pair_le _ _ _ _ _
  have hampn : ∀ y, 0 ≤ vortGradAmp (secondDerivField v) ι σ y * vortAmp (gradField v) ι σ y := fun y =>
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have intE : Integrable (fun y => ‖fderiv ℝ a y‖ * vortGradAmp (secondDerivField v) ι σ y * vortAmp (gradField v) ι σ y) := by
    refine (hamp.const_mul Ad).mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · have := hgm.mul hamp.aestronglyMeasurable
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp only [Pi.mul_apply, mul_assoc]
    · rw [Real.norm_eq_abs, mul_assoc, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hampn y))]
      exact mul_le_mul_of_nonneg_right (hgB y) (hampn y)
  have hSm : AEStronglyMeasurable (fun y => ∑ l : Fin 3, fderiv ℝ a y (unitVector l)
      * (inner ℝ (fderiv ℝ (vortRe v ι σ) y (unitVector l)) (vortIm v ι σ y)
        - inner ℝ (fderiv ℝ (vortIm v ι σ) y (unitVector l)) (vortRe v ι σ y))) volume := by
    refine Finset.aestronglyMeasurable_fun_sum _ fun l _ => ?_
    refine (measurable_fderiv_apply_const ℝ a (unitVector l)).aestronglyMeasurable.mul ?_
    exact (((continuous_inner).comp ((hpd.clm_apply continuous_const).prodMk hqc)).sub
      ((continuous_inner).comp ((hqd.clm_apply continuous_const).prodMk hpc))).aestronglyMeasurable
  have intS := intE.mono' hSm (Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]
    exact hpt y)
  exact integral_mono intS intE fun y => (le_abs_self _).trans (hpt y)

end Internal.SmoothEpsSumSecondPartials

end Coercive

end Breakdown
