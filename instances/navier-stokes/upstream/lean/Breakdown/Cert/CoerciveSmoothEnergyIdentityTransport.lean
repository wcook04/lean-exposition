import Breakdown.Cert.CoerciveSmoothEnergyIdentityDefs

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEnergyIdentityInternal

open EnergyIdentityInternal

namespace Transport

theorem slice_contDiff (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (σ : ℝ) :
    ContDiff ℝ ∞ (v σ) := by
  have h := hv.smooth.comp ((contDiff_const (c := σ)).prodMk (contDiff_id (𝕜 := ℝ) (E := Space)))
  exact h

theorem time_contDiff (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (σ : ℝ) :
    ContDiff ℝ ∞ (fun x => deriv (fun s => v s x) σ) := by
  have hd : Differentiable ℝ (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.differentiable (by simp)
  have e : (fun x => deriv (fun s => v s x) σ) = fun x =>
      fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (σ, x) (1, 0) := by
    funext x
    exact (time_hasDeriv v hd σ x).deriv
  rw [e]
  exact ((hv.smooth.fderiv_right (m := ∞) (by simp)).comp
    ((contDiff_const (c := σ)).prodMk (contDiff_id (𝕜 := ℝ) (E := Space)))).clm_apply contDiff_const

theorem transport_contDiff (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (σ : ℝ) :
    ContDiff ℝ ∞ (transportPart P v σ) := by
  have hu := slice_contDiff P v hv σ
  have hτ := time_contDiff P v hv σ
  have hw : ContDiff ℝ ∞ (fun x => fderiv ℝ (v σ) x x) :=
    (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_id
  have e : transportPart P v σ = fun x => (1 / P) • deriv (fun s => v s x) σ + (1 / 2 : ℝ) • v σ x
      + (1 / 2 : ℝ) • fderiv ℝ (v σ) x x := rfl
  rw [e]
  exact ((hτ.const_smul _).add (hu.const_smul _)).add (hw.const_smul _)

theorem transport_fderiv (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (σ : ℝ)
    (y w : Space) :
    fderiv ℝ (transportPart P v σ) y w = (1 / P) • fderiv ℝ (fun x => deriv (fun s => v s x) σ) y w
      + fderiv ℝ (v σ) y w + (1 / 2 : ℝ) • fderiv ℝ (fun x => fderiv ℝ (v σ) x) y w y := by
  have hu := slice_contDiff P v hv σ
  have hτ := time_contDiff P v hv σ
  have d1 : HasFDerivAt (v σ) (fderiv ℝ (v σ) y) y := (hu.differentiable (by simp) y).hasFDerivAt
  have d0 : HasFDerivAt (fun x => deriv (fun s => v s x) σ)
      (fderiv ℝ (fun x => deriv (fun s => v s x) σ) y) y :=
    (hτ.differentiable (by simp) y).hasFDerivAt
  have d2 : HasFDerivAt (fun x => fderiv ℝ (v σ) x) (fderiv ℝ (fun x => fderiv ℝ (v σ) x) y) y :=
    ((hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp) y).hasFDerivAt
  have d3 := d2.clm_apply (hasFDerivAt_id y)
  have hT := ((d0.const_smul (1 / P)).add (d1.const_smul (1 / 2 : ℝ))).add (d3.const_smul (1 / 2 : ℝ))
  have hT' : HasFDerivAt (transportPart P v σ) _ y := hT
  rw [hT'.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, id]
  module

theorem energy_fderiv (u : Space → Space) (hu : ContDiff ℝ 2 u) (y w : Space) :
    fderiv ℝ (fun x => matSq (fderiv ℝ u x)) y w = ∑ j : Fin 3,
      2 * inner ℝ (fderiv ℝ u y (unitVector j)) (fderiv ℝ (fun x => fderiv ℝ u x) y w (unitVector j)) := by
  have d2 : HasFDerivAt (fun x => fderiv ℝ u x) (fderiv ℝ (fun x => fderiv ℝ u x) y) y :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) y).hasFDerivAt
  have hj : ∀ j ∈ (Finset.univ : Finset (Fin 3)), HasFDerivAt (fun x => ‖fderiv ℝ u x (unitVector j)‖ ^ 2)
      (2 • (innerSL ℝ (fderiv ℝ u y (unitVector j))).comp
        ((ContinuousLinearMap.apply ℝ Space (unitVector j)).comp (fderiv ℝ (fun x => fderiv ℝ u x) y))) y := by
    intro j _
    have h1 := ((ContinuousLinearMap.apply ℝ Space (unitVector j)).hasFDerivAt).comp y d2
    exact h1.norm_sq
  have hs := HasFDerivAt.fun_sum hj
  have e : (fun x => matSq (fderiv ℝ u x)) = fun x => ∑ j : Fin 3, ‖fderiv ℝ u x (unitVector j)‖ ^ 2 := rfl
  rw [e, hs.fderiv]
  simp [innerSL_apply_apply]

theorem pointwise_pair (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (σ : ℝ) (y : Space) :
    ∑ j : Fin 3, inner ℝ (fderiv ℝ (transportPart P v σ) y (unitVector j)) (fderiv ℝ (v σ) y (unitVector j)) =
      (1 / P) * timePair v σ y + matSq (fderiv ℝ (v σ) y)
        + (1 / 4 : ℝ) * fderiv ℝ (fun x => matSq (fderiv ℝ (v σ) x)) y y := by
  have hu := slice_contDiff P v hv σ
  have hu2 : ContDiff ℝ 2 (v σ) := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [energy_fderiv (v σ) hu2]
  simp only [transport_fderiv P v hv σ, timePair, matSq, Fin.sum_univ_three]
  rw [d2_symm (v σ) hu y y (unitVector 0), d2_symm (v σ) hu y y (unitVector 1),
    d2_symm (v σ) hu y y (unitVector 2)]
  simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  simp only [real_inner_comm]
  ring

theorem int_mul_of_sq {f g A B : Space → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hA : Integrable (fun y => A y ^ 2)) (hB : Integrable (fun y => B y ^ 2))
    (hfA : ∀ y, |f y| ≤ A y) (hgB : ∀ y, |g y| ≤ B y) : Integrable (fun y => f y * g y) := by
  refine Integrable.mono' ((hA.add hB).div_const 2) (hf.mul hg).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  show ‖f y * g y‖ ≤ (A y ^ 2 + B y ^ 2) / 2
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := hfA y
  have h2 := hgB y
  have h3 := abs_nonneg (f y)
  have h4 := abs_nonneg (g y)
  nlinarith [sq_nonneg (A y - B y), mul_le_mul h1 h2 h4 (h3.trans h1)]

theorem abs_apply_le (x : Space) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x i
  rwa [Real.norm_eq_abs] at this

theorem clm_entry_le (G : Space →L[ℝ] Space) (j i : Fin 3) : |G (unitVector j) i| ≤ ‖G‖ := by
  refine (abs_apply_le _ i).trans ?_
  have := G.le_opNorm (unitVector j)
  simpa [unitVector_norm] using this

theorem clm2_entry_le (H : Space →L[ℝ] Space →L[ℝ] Space) (j k i : Fin 3) :
    |H (unitVector j) (unitVector k) i| ≤ ‖H‖ := by
  refine (abs_apply_le _ i).trans ?_
  have := H.le_opNorm₂ (unitVector j) (unitVector k)
  simpa [unitVector_norm] using this

theorem matNorm_le (G : Space →L[ℝ] Space) : matSq G ≤ 3 * ‖G‖ ^ 2 := by
  have h : ∀ i : Fin 3, ‖G (unitVector i)‖ ^ 2 ≤ ‖G‖ ^ 2 := fun i => by
    have := G.le_opNorm (unitVector i)
    have h' : ‖G (unitVector i)‖ ≤ ‖G‖ := by simpa [unitVector_norm] using this
    exact pow_le_pow_left₀ (norm_nonneg _) h' 2
  simp only [matSq, Fin.sum_univ_three]
  linarith [h 0, h 1, h 2]

end Transport

namespace Transport

theorem int_inner_of_sq {a b : Space → Space} {A B : Space → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hA : Integrable (fun y => A y ^ 2)) (hB : Integrable (fun y => B y ^ 2))
    (haA : ∀ y, ‖a y‖ ≤ A y) (hbB : ∀ y, ‖b y‖ ≤ B y) : Integrable (fun y => inner ℝ (a y) (b y)) := by
  refine Integrable.mono' ((hA.add hB).div_const 2) (ha.inner hb).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  show ‖inner ℝ (a y) (b y)‖ ≤ (A y ^ 2 + B y ^ 2) / 2
  rw [Real.norm_eq_abs]
  have h0 := abs_real_inner_le_norm (a y) (b y)
  have h1 := haA y
  have h2 := hbB y
  have h3 := norm_nonneg (a y)
  have h4 := norm_nonneg (b y)
  nlinarith [sq_nonneg (A y - B y), mul_le_mul h1 h2 h4 (h3.trans h1)]

theorem div_id (y : Space) : divergenceAt (fun x : Space => x) y = 3 := by
  simp only [divergenceAt, fderiv_fun_id, ContinuousLinearMap.id_apply, Fin.sum_univ_three]
  simp [unitVector]
  norm_num

theorem step_one (T u : Space → Space) (hT : ContDiff ℝ 1 T) (hu : ContDiff ℝ ∞ u)
    (i0 : Integrable (fun y => ‖T y‖ ^ 2)) (i1 : Integrable (fun y => ‖fderiv ℝ T y‖ ^ 2))
    (j1 : Integrable (fun y => ‖fderiv ℝ u y‖ ^ 2))
    (j2 : Integrable (fun y => ‖fderiv ℝ (fun x => fderiv ℝ u x) y‖ ^ 2)) :
    ∫ y, inner ℝ (T y) (-secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ u x) y)) =
      ∫ y, ∑ j : Fin 3, inner ℝ (fderiv ℝ T y (unitVector j)) (fderiv ℝ u y (unitVector j)) := by
  have hdT : Differentiable ℝ T := hT.differentiable (by norm_num)
  have hdu : Differentiable ℝ u := hu.differentiable (by simp)
  have hTi : ∀ i : Fin 3, ContDiff ℝ 1 (fun x => T x i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hT
  have hg : ∀ i j : Fin 3, ContDiff ℝ 1 (fun x => fderiv ℝ u x (unitVector j) i) := fun i j =>
    (d1_smooth u hu j i).of_le one_le_inf
  have pL : ∀ y, inner ℝ (T y) (-secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ u x) y)) =
      -∑ i : Fin 3, ∑ j : Fin 3, T y i * fderiv ℝ (fun x => fderiv ℝ u x (unitVector j) i) y (unitVector j) := by
    intro y
    simp only [d2_eq u hu]
    rw [inner_coord]
    simp [secondDerivTrace, Fin.sum_univ_three]
    ring
  have pR : ∀ y, ∑ j : Fin 3, inner ℝ (fderiv ℝ T y (unitVector j)) (fderiv ℝ u y (unitVector j)) =
      ∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ (fun x => T x i) y (unitVector j) * fderiv ℝ u y (unitVector j) i := by
    intro y
    simp only [fderiv_component T (hdT y), inner_coord]
    exact Finset.sum_comm
  have cT : Continuous T := hT.continuous
  have cdT : Continuous (fun y => fderiv ℝ T y) := hT.continuous_fderiv (by norm_num)
  have cdu : Continuous (fun y => fderiv ℝ u y) := hu.continuous_fderiv (by simp)
  have iA : ∀ i j : Fin 3, Integrable (fun y => T y i *
      fderiv ℝ (fun x => fderiv ℝ u x (unitVector j) i) y (unitVector j)) := fun i j =>
    int_mul_of_sq (A := fun y => ‖T y‖) (B := fun y => ‖fderiv ℝ (fun x => fderiv ℝ u x) y‖)
      (hTi i).continuous (((hg i j).continuous_fderiv (by norm_num)).clm_apply continuous_const) i0 j2
      (fun y => abs_apply_le _ i) (fun y => by rw [d2_eq u hu]; exact clm2_entry_le _ _ _ _)
  have iB : ∀ i j : Fin 3, Integrable (fun y => fderiv ℝ (fun x => T x i) y (unitVector j) *
      fderiv ℝ u y (unitVector j) i) := fun i j =>
    int_mul_of_sq (A := fun y => ‖fderiv ℝ T y‖) (B := fun y => ‖fderiv ℝ u y‖)
      (((hTi i).continuous_fderiv (by norm_num)).clm_apply continuous_const)
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp (cdu.clm_apply continuous_const)) i1 j1
      (fun y => by rw [fderiv_component T (hdT y)]; exact clm_entry_le _ _ _)
      (fun y => clm_entry_le _ _ _)
  have iC : ∀ i j : Fin 3, Integrable (fun y => T y i * fderiv ℝ u y (unitVector j) i) := fun i j =>
    int_mul_of_sq (A := fun y => ‖T y‖) (B := fun y => ‖fderiv ℝ u y‖)
      (hTi i).continuous
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp (cdu.clm_apply continuous_const)) i0 j1
      (fun y => abs_apply_le _ i) (fun y => clm_entry_le _ _ _)
  simp_rw [pL, pR]
  rw [integral_neg, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => iA i j)),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => iB i j)), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_finsetSum _ (fun j _ => iA i j), integral_finsetSum _ (fun j _ => iB i j),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (iB i j) (iA i j) (iC i j)
    (fun x _ => (hTi i).differentiable (by norm_num) x) (fun x _ => (hg i j).differentiable (by norm_num) x),
    neg_neg]

end Transport

open Transport in
theorem transport_slice (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (σ : ℝ)
    (hs : SliceBounds P v σ) :
    ∫ y, inner ℝ (transportPart P v σ y) (-secondDerivTrace (secondDerivField v σ y)) =
      (1 / P) * (∫ y, timePair v σ y) + ∫ y, (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2 := by
  have hu := slice_contDiff P v hv σ
  have hu2 : ContDiff ℝ 2 (v σ) := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hT := transport_contDiff P v hv σ
  have hτ := time_contDiff P v hv σ
  have s1 := step_one (transportPart P v σ) (v σ) (hT.of_le one_le_inf) hu hs.transport hs.transport_first
    hs.first hs.second
  have cdu : Continuous (fun y => fderiv ℝ (v σ) y) := hu.continuous_fderiv (by simp)
  have cdT : Continuous (fun y => fderiv ℝ (transportPart P v σ) y) := hT.continuous_fderiv (by simp)
  have cdτ : Continuous (fun y => fderiv ℝ (fun x => deriv (fun s => v s x) σ) y) :=
    hτ.continuous_fderiv (by simp)
  have hF : ContDiff ℝ 1 (fun x => matSq (fderiv ℝ (v σ) x)) := by
    show ContDiff ℝ 1 (fun x => ∑ j : Fin 3, ‖fderiv ℝ (v σ) x (unitVector j)‖ ^ 2)
    exact (ContDiff.sum (fun j _ => ((hu.fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const).norm_sq ℝ)).of_le one_le_inf
  have iF : Integrable (fun y => matSq (fderiv ℝ (v σ) y)) := by
    refine Integrable.mono' (hs.first.const_mul 3) hF.continuous.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (matSq_nonneg _)]
    exact matSq_le _
  have unit_le : ∀ (G : Space →L[ℝ] Space) (j : Fin 3), ‖G (unitVector j)‖ ≤ ‖G‖ := fun G j => by
    have := G.le_opNorm (unitVector j)
    simpa [unitVector_norm] using this
  have itp : Integrable (fun y => timePair v σ y) := by
    unfold timePair
    exact integrable_finsetSum _ (fun j _ => int_inner_of_sq
      (A := fun y => ‖fderiv ℝ (fun x => deriv (fun s => v s x) σ) y‖) (B := fun y => ‖fderiv ℝ (v σ) y‖)
      (cdτ.clm_apply continuous_const) (cdu.clm_apply continuous_const) hs.time_first hs.first
      (fun y => unit_le _ j) (fun y => unit_le _ j))
  have ipair : Integrable (fun y => ∑ j : Fin 3, inner ℝ (fderiv ℝ (transportPart P v σ) y (unitVector j))
      (fderiv ℝ (v σ) y (unitVector j))) :=
    integrable_finsetSum _ (fun j _ => int_inner_of_sq
      (A := fun y => ‖fderiv ℝ (transportPart P v σ) y‖) (B := fun y => ‖fderiv ℝ (v σ) y‖)
      (cdT.clm_apply continuous_const) (cdu.clm_apply continuous_const) hs.transport_first hs.first
      (fun y => unit_le _ j) (fun y => unit_le _ j))
  have iD : Integrable (fun y => fderiv ℝ (fun x => matSq (fderiv ℝ (v σ) x)) y y) := by
    have h4 : Integrable (fun y => 4 * ((∑ j : Fin 3, inner ℝ (fderiv ℝ (transportPart P v σ) y (unitVector j))
        (fderiv ℝ (v σ) y (unitVector j))) - (1 / P) * timePair v σ y - matSq (fderiv ℝ (v σ) y))) :=
      ((ipair.sub (itp.const_mul (1 / P))).sub iF).const_mul 4
    refine h4.congr (Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [pointwise_pair P v hv σ y]
    ring
  have i2 : Integrable (fun y => divergenceAt (fun x : Space => x) y * matSq (fderiv ℝ (v σ) y)) := by
    simp only [div_id]
    exact iF.const_mul 3
  have i3 : Integrable (fun y : Space => ‖y‖ * |matSq (fderiv ℝ (v σ) y)| / (1 + ‖y‖)) := by
    refine Integrable.mono' iF.norm
      ((continuous_norm.mul hF.continuous.abs).div (continuous_const.add continuous_norm)
        (fun y => (by positivity : (0 : ℝ) < 1 + ‖y‖).ne')).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    have hy := norm_nonneg y
    have hf := abs_nonneg (matSq (fderiv ℝ (v σ) y))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  have sc := weighted_ibp (fun x : Space => x) (fun x => matSq (fderiv ℝ (v σ) x)) contDiff_id hF iD i2 i3
  simp only [div_id] at sc
  rw [integral_const_mul] at sc
  have ce := curl_energy (v σ) hu2 (hv.divergence_free σ) hs.first hs.weighted
  have ipw : ∀ y, ∑ j : Fin 3, inner ℝ (fderiv ℝ (transportPart P v σ) y (unitVector j))
      (fderiv ℝ (v σ) y (unitVector j)) = (1 / P) * timePair v σ y + matSq (fderiv ℝ (v σ) y)
        + (1 / 4 : ℝ) * fderiv ℝ (fun x => matSq (fderiv ℝ (v σ) x)) y y := pointwise_pair P v hv σ
  show ∫ y, inner ℝ (transportPart P v σ y) (-secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ (v σ) x) y)) = _
  rw [s1]
  simp_rw [ipw]
  rw [integral_add _ (iD.const_mul _), integral_add (itp.const_mul _) iF,
    integral_const_mul, integral_const_mul, integral_const_mul, sc, ce]
  all_goals first | exact (itp.const_mul _).add iF | ring

end SmoothEnergyIdentityInternal

end Coercive

end Breakdown
