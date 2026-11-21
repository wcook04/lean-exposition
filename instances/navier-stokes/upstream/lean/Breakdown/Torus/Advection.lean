import Breakdown.Torus.StatementsCoeff

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace Advection.Internal

theorem isCompact_cell : IsCompact cell := by
  have h : cell = (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph ⁻¹'
      Set.pi univ (fun _ => Icc (0 : ℝ) 1) := by
    ext x
    simp [cell, Pi.le_def, forall_and]
  rw [h, Homeomorph.isCompact_preimage]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

theorem complexify_apply (x : Space) (i : Fin 3) : complexify x i = ((x i : ℝ) : ℂ) := rfl

theorem continuous_complexify : Continuous complexify := by
  unfold complexify
  fun_prop

theorem continuous_character (k : Lattice) : Continuous (character k) := by
  unfold character
  fun_prop

theorem norm_character (k : Lattice) (x : Space) : ‖character k x‖ = 1 := by
  unfold character
  have h : -(2 * π * Complex.I * ((inner ℝ (freq k) x : ℝ) : ℂ)) =
      ((-(2 * π * inner ℝ (freq k) x) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem freq_add (a b : Lattice) : freq (a + b) = freq a + freq b := by
  simp [freq, add_smul, Finset.sum_add_distrib]

theorem character_mul (a b : Lattice) (x : Space) :
    character a x * character b x = character (a + b) x := by
  simp only [character, ← Complex.exp_add, freq_add, inner_add_left]
  congr 1
  push_cast
  ring

theorem complexify_sum_smul (a : Fin 3 → ℝ) (v : Fin 3 → Space) :
    complexify (∑ i, a i • v i) = ∑ i, ((a i : ℝ) : ℂ) • complexify (v i) := by
  ext j
  rw [complexify_apply]
  have h1 : (∑ i, a i • v i) j = ∑ i, a i * v i j := by
    change (EuclideanSpace.proj j : Space →L[ℝ] ℝ) (∑ i, a i • v i) = _
    simp [map_sum]
  have h2 : (∑ i, ((a i : ℝ) : ℂ) • complexify (v i)) j =
      ∑ i, ((a i : ℝ) : ℂ) * complexify (v i) j := by
    change (EuclideanSpace.proj j : Coef →L[ℂ] ℂ) (∑ i, ((a i : ℝ) : ℂ) • complexify (v i)) = _
    simp [map_sum]
  rw [h1, h2]
  push_cast
  simp [complexify_apply]

theorem advectionAt_eq (f : Space → Space) (x : Space) :
    advectionAt f x = ∑ i, (f x i) • fderiv ℝ f x (unitVector i) := by
  unfold advectionAt
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (f x)]
  simp [map_sum, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr, unitVector]

theorem contDiff_one_of_smooth {f : Space → Space} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 1 f :=
  hf.of_le (mod_cast le_top)

theorem continuous_partial {f : Space → Space} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    Continuous (fun x => complexify (fderiv ℝ f x (unitVector i))) :=
  continuous_complexify.comp ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)

theorem hasSum_component (hD : CoefDeriv) (hF : FreqTrSeriesSpec) (f : Space → Space)
    (hf : ContDiff ℝ ∞ f) (hp : IsPeriodic f) (hdiv : ∀ x, divergenceAt f x = 0)
    (k : Lattice) (i : Fin 3) :
    HasSum (fun j => freqTrCoef f (k - j) i •
        ((2 * π * Complex.I * ((j i : ℤ) : ℂ)) • freqTrCoef f j))
      (∫ x in cell, ((f x i : ℝ) : ℂ) •
        (character k x • complexify (fderiv ℝ f x (unitVector i)))) := by
  obtain ⟨-, hsum, hser⟩ := hF f hf hp hdiv
  set c := freqTrCoef f with hcdef
  set H := fun x => complexify (fderiv ℝ f x (unitVector i)) with hH
  have hHc : Continuous H := continuous_partial hf i
  have hci : Summable (fun l => ‖c l i‖) :=
    hsum.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => PiLp.norm_apply_le (c l) i)
  have key : HasSum (fun l => ∫ x in cell, c l i • (character (k - l) x • H x))
      (∫ x in cell, ((f x i : ℝ) : ℂ) • (character k x • H x)) := by
    refine hasSum_integral_of_dominated_convergence (fun l x => ‖c l i‖ * ‖H x‖) ?_ ?_ ?_ ?_ ?_
    · intro l
      exact ((continuous_const : Continuous fun _ : Space => c l i).smul
        ((continuous_character (k - l)).smul hHc)).aestronglyMeasurable
    · intro l
      refine Filter.Eventually.of_forall (fun x => ?_)
      rw [norm_smul, norm_smul, norm_character, one_mul]
    · exact Filter.Eventually.of_forall (fun x => hci.mul_right _)
    · simp_rw [tsum_mul_right]
      exact (continuous_const.mul hHc.norm).continuousOn.integrableOn_compact isCompact_cell
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have h1 := (hser x).mapL (EuclideanSpace.proj i : Coef →L[ℂ] ℂ)
      have h2 : HasSum (fun l => character (-l) x * c l i) ((f x i : ℝ) : ℂ) := by
        simpa [complexify_apply] using h1
      have h3 := h2.smul_const (character k x • H x)
      have e : (fun l => c l i • (character (k - l) x • H x)) =
          fun l => (character (-l) x * c l i) • (character k x • H x) := by
        funext l
        rw [smul_smul, smul_smul, sub_eq_neg_add, ← character_mul]
        ring_nf
      rw [e]
      exact h3
  have hint : ∀ l, ∫ x in cell, c l i • (character (k - l) x • H x) =
      c l i • ((2 * π * Complex.I * (((k - l) i : ℤ) : ℂ)) • c (k - l)) := by
    intro l
    rw [integral_smul]
    congr 1
    exact hD f (contDiff_one_of_smooth hf) hp i (k - l)
  rw [funext hint] at key
  have key2 := (Equiv.subLeft k).hasSum_iff.mpr key
  convert key2 using 1
  funext j
  simp [Equiv.subLeft_apply, sub_sub_cancel]

end Advection.Internal

theorem coefAdvection (hD : CoefDeriv) (hF : FreqTrSeriesSpec) : CoefAdvection := by
  intro f hf hp hdiv k
  have hc := (hF f hf hp hdiv).1
  have hall := hasSum_sum (s := Finset.univ)
    (fun i _ => Advection.Internal.hasSum_component hD hF f hf hp hdiv k i)
  have hadv : advCoef (toV f) (toV f) k = ∑' j, ∑ i : Fin 3, freqTrCoef f (k - j) i •
      ((2 * π * Complex.I * ((j i : ℤ) : ℂ)) • freqTrCoef f j) := by
    unfold advCoef
    congr 1
    funext j
    rw [hc, hc, divPairing, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_smul]
    congr 1
    push_cast
    ring
  rw [hadv, hall.tsum_eq, ← integral_finsetSum]
  · unfold freqTrCoef
    congr 1
    funext x
    rw [Advection.Internal.advectionAt_eq, Advection.Internal.complexify_sum_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_comm]
  · intro i _
    exact ((Complex.continuous_ofReal.comp ((EuclideanSpace.proj i).continuous.comp
      hf.continuous)).smul ((Advection.Internal.continuous_character k).smul
      (Advection.Internal.continuous_partial hf i))).continuousOn.integrableOn_compact Advection.Internal.isCompact_cell

end Breakdown.Periodic
