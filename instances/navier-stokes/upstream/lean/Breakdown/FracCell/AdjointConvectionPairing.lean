import Breakdown.FracCell.ReductionAdjointDefs
import Breakdown.FracCell.AdjointConvectionPairingParts

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Breakdown

namespace FracInternal

namespace ConvectionPairing

open SteadyCert CellCert

theorem inner_int {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun y => inner ℝ (f y) (g y)) := by
  have h := hf.norm.integrable_mul hg.norm
  refine h.mono' (hf.1.inner hg.1) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs]
  exact abs_real_inner_le_norm _ _

theorem col_memLp {A : Space → (Space →L[ℝ] Space)} (hA : AEStronglyMeasurable A volume)
    (h2 : Integrable (fun y => entrySq (A y))) (j : Fin 3) : MemLp (fun y => A y (unitVector j)) 2 volume := by
  have hcol : AEStronglyMeasurable (fun y => A y (unitVector j)) volume :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable (hA.prodMk aestronglyMeasurable_const)
  refine (memLp_two_iff_integrable_sq_norm hcol).2 (h2.mono' (hcol.norm.pow 2) (ae_of_all _ fun y => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  unfold entrySq
  exact Finset.single_le_sum (f := fun i => ‖A y (unitVector i)‖ ^ 2) (fun i _ => by positivity)
    (Finset.mem_univ j)

theorem memLp_of_bound {f : Space → Space} {g : Space → ℝ} (hg : MemLp g 2 volume)
    (hf : AEStronglyMeasurable f volume) (h : ∀ᵐ y ∂volume, ‖f y‖ ≤ g y) : MemLp f 2 volume :=
  hg.of_le hf (h.mono fun y hy => hy.trans ((le_abs_self _).trans_eq (Real.norm_eq_abs _).symm))

theorem coord_le (w : Space) (i : Fin 3) : |w i| ≤ ‖w‖ := by
  simpa using PiLp.norm_apply_le w i

theorem unit_norm (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem apply_coord_le (A : Space →L[ℝ] Space) (i j : Fin 3) : |A (unitVector i) j| ≤ ‖A‖ := by
  refine (coord_le _ j).trans ?_
  have := A.le_opNorm (unitVector i)
  rwa [unit_norm, mul_one] at this

theorem coord_fderiv {φ : Space → Space} (hφ : Differentiable ℝ φ) (i : Fin 3) (y w : Space) :
    fderiv ℝ (fun x => φ x i) y w = fderiv ℝ φ y w i := by
  have h : HasFDerivAt (fun x => φ x i)
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (fderiv ℝ φ y)) y :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y (hφ y).hasFDerivAt
  rw [h.fderiv]
  rfl

theorem sum_unit (x : Space) : ∑ j : Fin 3, x j • unitVector j = x := by
  ext i
  fin_cases i <;> simp [unitVector, Fin.sum_univ_three, EuclideanSpace.single_apply]

theorem inner_unit (x : Space) (i : Fin 3) : inner ℝ x (unitVector i) = x i := by
  simp [unitVector, EuclideanSpace.inner_single_right]

theorem weak_smul_left {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hv : LocallyIntegrable v volume)
    (k : Fin 3) (hG : LocallyIntegrable (fun y => G y (unitVector k)) volume) (hw : IsWeakGradientOf v G)
    {s : Space → ℝ} (hs : ContDiff ℝ 1 s) (φ : Space → ℝ) (hφ : IsTestScalar φ) :
    ∫ y, fderiv ℝ φ y (unitVector k) • (s y • v y) =
      -∫ y, φ y • (fderiv ℝ s y (unitVector k) • v y + s y • G y (unitVector k)) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.1.of_le (by simp)
  have hψ : ContDiff ℝ 1 (fun y => φ y * s y) := hφ1.mul hs
  have hψc : HasCompactSupport (fun y => φ y * s y) := hφ.2.mul_right
  have key := weak_of_C1 hv k hG hw hψ hψc
  have hder : ∀ y, fderiv ℝ (fun y => φ y * s y) y (unitVector k) =
      fderiv ℝ φ y (unitVector k) * s y + φ y * fderiv ℝ s y (unitVector k) := by
    intro y
    have hd := ((hφ1.differentiable one_ne_zero) y).hasFDerivAt.mul ((hs.differentiable one_ne_zero) y).hasFDerivAt
    rw [show (fun y => φ y * s y) = φ * s from rfl, hd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have cφ : Continuous (fun y => fderiv ℝ φ y (unitVector k)) :=
    (hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have cs : Continuous (fun y => fderiv ℝ s y (unitVector k)) :=
    (hs.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have sφ : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector k)) := hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector k)
  have I1 : Integrable (fun y => (fderiv ℝ φ y (unitVector k) * s y) • v y) :=
    hv.integrable_smul_left_of_hasCompactSupport (cφ.mul hs.continuous) sφ.mul_right
  have I2 : Integrable (fun y => (φ y * fderiv ℝ s y (unitVector k)) • v y) :=
    hv.integrable_smul_left_of_hasCompactSupport (hφ1.continuous.mul cs) hφ.2.mul_right
  have I3 : Integrable (fun y => (φ y * s y) • G y (unitVector k)) :=
    hG.integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
  simp only [hder, add_smul] at key
  rw [integral_add I1 I2] at key
  have key' : (∫ y, (fderiv ℝ φ y (unitVector k) * s y) • v y) + ∫ y, (φ y * fderiv ℝ s y (unitVector k)) • v y =
      -∫ y, (φ y * s y) • G y (unitVector k) := key
  have e1 : ∫ y, fderiv ℝ φ y (unitVector k) • (s y • v y) = ∫ y, (fderiv ℝ φ y (unitVector k) * s y) • v y := by
    congr 1
    funext y
    rw [smul_smul]
  have e2 : ∫ y, φ y • (fderiv ℝ s y (unitVector k) • v y + s y • G y (unitVector k)) =
      (∫ y, (φ y * fderiv ℝ s y (unitVector k)) • v y) + ∫ y, (φ y * s y) • G y (unitVector k) := by
    refine Eq.trans ?_ (integral_add I2 I3)
    congr 1
    funext y
    rw [smul_add, smul_smul, smul_smul]
  rw [e1, e2, eq_sub_of_add_eq key']
  abel

theorem integral_coord {f : Space → Space} (hf : Integrable f volume) (l : Fin 3) :
    (∫ y, f y) l = ∫ y, f y l := by
  have := (EuclideanSpace.proj l : Space →L[ℝ] ℝ).integral_comp_comm hf
  simpa using this.symm

theorem loc_coord {v : Space → Space} (hv : LocallyIntegrable v volume) (j : Fin 3) :
    LocallyIntegrable (fun y => v y j) volume :=
  (locallyIntegrable_iff).2 fun K hK =>
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).integrable_comp ((locallyIntegrable_iff.1 hv) K hK)

theorem weak_smul_right {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hv : LocallyIntegrable v volume)
    (k : Fin 3) (hG : LocallyIntegrable (fun y => G y (unitVector k)) volume) (hw : IsWeakGradientOf v G)
    {X : Space → Space} (hX : ContDiff ℝ 1 X) (j : Fin 3) (φ : Space → ℝ) (hφ : IsTestScalar φ) :
    ∫ y, fderiv ℝ φ y (unitVector k) • (v y j • X y) =
      -∫ y, φ y • (G y (unitVector k) j • X y + v y j • fderiv ℝ X y (unitVector k)) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.1.of_le (by simp)
  have hXd : Differentiable ℝ X := hX.differentiable one_ne_zero
  have hφ' : ContDiff ℝ 0 (fun y => fderiv ℝ φ y (unitVector k)) :=
    (hφ.1.fderiv_right (m := 0) (by simp)).clm_apply contDiff_const
  have hX' : ContDiff ℝ 0 (fun y => fderiv ℝ X y (unitVector k)) :=
    (hX.fderiv_right (m := 0) (by simp)).clm_apply contDiff_const
  have sφ : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector k)) := hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector k)
  have cφ : Continuous (fun y => fderiv ℝ φ y (unitVector k)) :=
    (hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have cX : Continuous (fun y => fderiv ℝ X y (unitVector k)) :=
    (hX.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hvj : LocallyIntegrable (fun y => v y j) volume := loc_coord hv j
  have hGj : LocallyIntegrable (fun y => G y (unitVector k) j) volume := loc_coord hG j
  have J1 : Integrable (fun y => fderiv ℝ φ y (unitVector k) • (v y j • X y)) volume := by
    have := hvj.integrable_smul_right_of_hasCompactSupport (cφ.smul hX.continuous) (sφ.smul_right)
    refine this.congr (ae_of_all _ fun y => ?_)
    simp only [Pi.smul_apply', Pi.smul_apply, Pi.mul_apply, Pi.add_apply, smul_smul, mul_comm]
  have J2 : Integrable (fun y => φ y • (G y (unitVector k) j • X y + v y j • fderiv ℝ X y (unitVector k))) volume := by
    have a1 := hGj.integrable_smul_right_of_hasCompactSupport (hφ1.continuous.smul hX.continuous) (hφ.2.smul_right)
    have a2 := hvj.integrable_smul_right_of_hasCompactSupport (hφ1.continuous.smul cX) (hφ.2.smul_right)
    refine (a1.add a2).congr (ae_of_all _ fun y => ?_)
    simp only [Pi.smul_apply', Pi.smul_apply, Pi.mul_apply, Pi.add_apply, smul_add, smul_smul, mul_comm]
  ext l
  rw [integral_coord J1, PiLp.neg_apply, integral_coord J2]
  have hXl : ContDiff ℝ 1 (fun y => X y l) := (EuclideanSpace.proj l : Space →L[ℝ] ℝ).contDiff.comp hX
  have hA := weak_smul_left hv k hG hw hXl φ hφ
  have K1 : Integrable (fun y => fderiv ℝ φ y (unitVector k) • (X y l • v y)) volume := by
    have := hv.integrable_smul_left_of_hasCompactSupport (cφ.mul hXl.continuous) sφ.mul_right
    refine this.congr (ae_of_all _ fun y => ?_)
    simp only [Pi.smul_apply', Pi.smul_apply, Pi.mul_apply, Pi.add_apply, smul_smul]
  have c1 : Continuous (fun y => fderiv ℝ (fun y => X y l) y (unitVector k)) :=
    (hXl.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have K2 : Integrable (fun y => φ y • (fderiv ℝ (fun y => X y l) y (unitVector k) • v y +
      X y l • G y (unitVector k))) volume := by
    have a1 := hv.integrable_smul_left_of_hasCompactSupport (hφ1.continuous.mul c1) hφ.2.mul_right
    have a2 := hG.integrable_smul_left_of_hasCompactSupport (hφ1.continuous.mul hXl.continuous) hφ.2.mul_right
    refine (a1.add a2).congr (ae_of_all _ fun y => ?_)
    simp only [Pi.smul_apply', Pi.smul_apply, Pi.mul_apply, Pi.add_apply, smul_add, smul_smul]
  have hAj := congrArg (fun x : Space => x j) hA
  simp only [PiLp.neg_apply] at hAj
  rw [integral_coord K1, integral_coord K2] at hAj
  simp only [coord_fderiv hXd] at hAj
  convert hAj using 2
  · funext y
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  · congr 1
    funext y
    simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    ring

theorem cross_alg (M : Space →L[ℝ] Space) (v S : Space) :
    inner ℝ v (-crossVec (curlOf M) S) =
      ∑ j : Fin 3, (inner ℝ (M (unitVector j)) (v j • S) - inner ℝ (M (unitVector j)) (S j • v)) := by
  simp only [inner_smul_right, inner_neg_right, curlOf, crossVec, entry, PiLp.inner_apply, Fin.sum_univ_three,
    permSign, RCLike.inner_apply, conj_trivial, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    EuclideanSpace.single_apply, unitVector]
  simp
  ring

end ConvectionPairing

end FracInternal

namespace CellCert

namespace Reduction

open SteadyCert FracInternal.ConvectionPairing

theorem convectionPairing_eq {m : ℕ} {ζ : Space → Space} {Dζ : Space → (Space →L[ℝ] Space)}
    {Hζ : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hreg : IsAdjointRegular ζ Dζ Hζ)
    (hζm : AEStronglyMeasurable ζ volume)
    {S : Space → Space} {DS : Space → (Space →L[ℝ] Space)} (hS : ContDiff ℝ 1 S)
    (hDS : ∀ y, DS y = fderiv ℝ S y) (hdiv : ∀ y, divergenceAt S y = 0)
    (hdec : ∃ C : ℝ, ∀ y, ‖S y‖ ≤ C * (1 + ‖y‖)⁻¹ ∧ ‖DS y‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ))
    {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hv : IsSecondOrderField m v G H) (hinv : Integrable (fun y => ‖v y‖ ^ 2 / ‖y‖ ^ 2)) :
    Integrable (fun y => inner ℝ (v y) (convectionAdjointField S DS ζ Dζ y)) ∧
      ∫ y, inner ℝ (v y) (convectionAdjointField S DS ζ Dζ y) =
        (∫ y, inner ℝ (ζ y) (G y (S y))) + ∫ y, inner ℝ (ζ y) (DS y (v y)) := by
  classical
  obtain ⟨C, hC⟩ := hdec
  obtain ⟨hζ2, -, -, hDζm, hζw, hDζ2, -, -, -, -⟩ := hreg
  have hvm := hv.measurable_velocity
  have hGm := hv.measurable_gradient
  have hvl : LocallyIntegrable v volume := hv.velocity_six.locallyIntegrable (by norm_num)
  have hGc : ∀ j, MemLp (fun y => G y (unitVector j)) 2 volume := col_memLp hGm hv.gradient_two
  have hGl : ∀ j, LocallyIntegrable (fun y => G y (unitVector j)) volume := fun j =>
    (hGc j).locallyIntegrable (by norm_num)
  have hZ : ∀ j, MemLp (fun y => Dζ y (unitVector j)) 2 volume := col_memLp hDζm hDζ2
  have hSc : Continuous S := hS.continuous
  have hDSf : DS = fun y => fderiv ℝ S y := funext hDS
  have hDSc : Continuous DS := by rw [hDSf]; exact hS.continuous_fderiv one_ne_zero
  have hSd : Differentiable ℝ S := hS.differentiable one_ne_zero
  have hC0 : 0 ≤ C := by
    have h := (hC 0).1
    rw [norm_zero, add_zero, inv_one, mul_one] at h
    exact (norm_nonneg _).trans h
  have hSb : ∀ y, ‖S y‖ ≤ C := fun y =>
    (hC y).1.trans (mul_le_of_le_one_right hC0 (inv_le_one_of_one_le₀ (by linarith [norm_nonneg y])))
  have hSy : ∀ y, ‖y‖ * ‖S y‖ ≤ C := by
    intro y
    have h1 : 0 < 1 + ‖y‖ := by positivity
    calc ‖y‖ * ‖S y‖ ≤ ‖y‖ * (C * (1 + ‖y‖)⁻¹) := mul_le_mul_of_nonneg_left (hC y).1 (norm_nonneg _)
      _ = C * (‖y‖ / (1 + ‖y‖)) := by ring
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left ((div_le_one h1).2 (by linarith)) hC0
      _ = C := mul_one C
  have hDSy : ∀ y, ‖y‖ * ‖DS y‖ ≤ C := by
    intro y
    have h1 : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
    have h2 : (1 + ‖y‖) ^ (-2 : ℝ) ≤ (1 + ‖y‖)⁻¹ := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    have h3 : 0 < 1 + ‖y‖ := by positivity
    calc ‖y‖ * ‖DS y‖ ≤ ‖y‖ * (C * (1 + ‖y‖)⁻¹) :=
          mul_le_mul_of_nonneg_left ((hC y).2.trans (mul_le_mul_of_nonneg_left h2 hC0)) (norm_nonneg _)
      _ = C * (‖y‖ / (1 + ‖y‖)) := by ring
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left ((div_le_one h3).2 (by linarith)) hC0
      _ = C := mul_one C
  have hne : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  set q : Space → ℝ := fun y => ‖v y‖ / ‖y‖ with hq_def
  have hqm : AEStronglyMeasurable q volume :=
    (hvm.norm.aemeasurable.div measurable_norm.aemeasurable).aestronglyMeasurable
  have hq : MemLp q 2 volume := (memLp_two_iff_integrable_sq hqm).2 (by simpa only [hq_def, div_pow] using hinv)
  have hCq : MemLp (fun y => C * q y) 2 volume := hq.const_mul C
  have bS : ∀ y, y ≠ 0 → ‖S y‖ * ‖v y‖ ≤ C * q y := by
    intro y hy
    have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
    simp only [hq_def]
    rw [mul_div_assoc', le_div_iff₀ hy']
    nlinarith [hSy y, norm_nonneg (v y)]
  have bDS : ∀ y, y ≠ 0 → ‖DS y‖ * ‖v y‖ ≤ C * q y := by
    intro y hy
    have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
    simp only [hq_def]
    rw [mul_div_assoc', le_div_iff₀ hy']
    nlinarith [hDSy y, norm_nonneg (v y)]
  have col_le : ∀ y j, ‖DS y (unitVector j)‖ ≤ ‖DS y‖ := fun y j => by
    have := (DS y).le_opNorm (unitVector j)
    rwa [unit_norm, mul_one] at this
  have cSj : ∀ j, Continuous (fun y => S y j) := fun j =>
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp hSc
  have cDSj : ∀ j, Continuous (fun y => DS y (unitVector j)) := fun j => hDSc.clm_apply continuous_const
  have mvj : ∀ j, AEStronglyMeasurable (fun y => v y j) volume := fun j =>
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hvm
  have mGj : ∀ j, AEStronglyMeasurable (fun y => G y (unitVector j) j) volume := fun j =>
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable (hGc j).1
  have mA : ∀ j, MemLp (fun y => S y j • v y) 2 volume := fun j =>
    memLp_of_bound hCq ((cSj j).aestronglyMeasurable.smul hvm) (hne.mono fun y hy => by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right (coord_le _ j) (norm_nonneg _)).trans (bS y hy))
  have mWA : ∀ j, MemLp (fun y => DS y (unitVector j) j • v y + S y j • G y (unitVector j)) 2 volume := by
    intro j
    refine MemLp.add (memLp_of_bound hCq
      (((EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp (cDSj j)).aestronglyMeasurable.smul hvm)
      (hne.mono fun y hy => ?_)) (memLp_of_bound ((hGc j).norm.const_mul C)
      ((cSj j).aestronglyMeasurable.smul (hGc j).1) (ae_of_all _ fun y => ?_))
    · rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right (apply_coord_le _ j j) (norm_nonneg _)).trans (bDS y hy)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right ((coord_le _ j).trans (hSb y)) (norm_nonneg _)
  have mB : ∀ j, MemLp (fun y => v y j • S y) 2 volume := fun j =>
    memLp_of_bound hCq ((mvj j).smul hSc.aestronglyMeasurable) (hne.mono fun y hy => by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right (coord_le _ j) (norm_nonneg _)).trans (by linarith [bS y hy]))
  have mWB : ∀ j, MemLp (fun y => G y (unitVector j) j • S y + v y j • DS y (unitVector j)) 2 volume := by
    intro j
    refine MemLp.add (memLp_of_bound ((hGc j).norm.const_mul C)
      ((mGj j).smul hSc.aestronglyMeasurable) (ae_of_all _ fun y => ?_))
      (memLp_of_bound hCq ((mvj j).smul (cDSj j).aestronglyMeasurable) (hne.mono fun y hy => ?_))
    · rw [norm_smul, Real.norm_eq_abs]
      calc |G y (unitVector j) j| * ‖S y‖ ≤ ‖G y (unitVector j)‖ * C :=
            mul_le_mul (coord_le _ j) (hSb y) (norm_nonneg _) (norm_nonneg _)
        _ = C * ‖G y (unitVector j)‖ := mul_comm _ _
    · rw [norm_smul, Real.norm_eq_abs]
      calc |v y j| * ‖DS y (unitVector j)‖ ≤ ‖v y‖ * ‖DS y‖ :=
            mul_le_mul (coord_le _ j) (col_le y j) (norm_nonneg _) (norm_nonneg _)
        _ = ‖DS y‖ * ‖v y‖ := mul_comm _ _
        _ ≤ C * q y := bDS y hy
  have hDSv : MemLp (fun y => DS y (v y)) 2 volume :=
    memLp_of_bound hCq (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hDSc.aestronglyMeasurable.prodMk hvm)) (hne.mono fun y hy => ((DS y).le_opNorm (v y)).trans (bDS y hy))
  have dA : ∀ j, ∀ φ : Space → ℝ, IsTestScalar φ →
      ∫ y, fderiv ℝ φ y (unitVector j) • (S y j • v y) =
        -∫ y, φ y • (DS y (unitVector j) j • v y + S y j • G y (unitVector j)) := by
    intro j φ hφ
    have h := weak_smul_left hvl j (hGl j) hv.weak_gradient (s := fun y => S y j)
      (by exact (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp hS) φ hφ
    simp only [coord_fderiv hSd, ← hDS] at h
    exact h
  have dB : ∀ j, ∀ φ : Space → ℝ, IsTestScalar φ →
      ∫ y, fderiv ℝ φ y (unitVector j) • (v y j • S y) =
        -∫ y, φ y • (G y (unitVector j) j • S y + v y j • DS y (unitVector j)) := by
    intro j φ hφ
    have h := weak_smul_right hvl j (hGl j) hv.weak_gradient hS j φ hφ
    simp only [← hDS] at h
    exact h
  have pA : ∀ j, ∫ y, inner ℝ (Dζ y (unitVector j)) (S y j • v y) =
      -∫ y, inner ℝ (ζ y) (DS y (unitVector j) j • v y + S y j • G y (unitVector j)) := fun j =>
    pair_of_dir j hζ2 (hZ j) (mA j) (mWA j) (fun φ hφ => hζw φ hφ j) (dA j)
  have pB : ∀ j, ∫ y, inner ℝ (Dζ y (unitVector j)) (v y j • S y) =
      -∫ y, inner ℝ (ζ y) (G y (unitVector j) j • S y + v y j • DS y (unitVector j)) := fun j =>
    pair_of_dir j hζ2 (hZ j) (mB j) (mWB j) (fun φ hφ => hζw φ hφ j) (dB j)
  have hpt : ∀ y, inner ℝ (v y) (convectionAdjointField S DS ζ Dζ y) =
      (∑ j : Fin 3, (inner ℝ (Dζ y (unitVector j)) (v y j • S y) - inner ℝ (Dζ y (unitVector j)) (S y j • v y)))
        + 2 * inner ℝ (ζ y) (DS y (v y)) := by
    intro y
    simp only [convectionAdjointField, inner_add_right, cross_alg, real_inner_smul_right,
      ContinuousLinearMap.adjoint_inner_right]
    rw [real_inner_comm (ζ y) (DS y (v y))]
  have iA : ∀ j, Integrable (fun y => inner ℝ (Dζ y (unitVector j)) (S y j • v y)) volume := fun j =>
    inner_int (hZ j) (mA j)
  have iB : ∀ j, Integrable (fun y => inner ℝ (Dζ y (unitVector j)) (v y j • S y)) volume := fun j =>
    inner_int (hZ j) (mB j)
  have ic : Integrable (fun y => inner ℝ (ζ y) (DS y (v y))) volume := inner_int hζ2 hDSv
  have iWA : ∀ j, Integrable (fun y => inner ℝ (ζ y)
      (DS y (unitVector j) j • v y + S y j • G y (unitVector j))) volume := fun j => inner_int hζ2 (mWA j)
  have iWB : ∀ j, Integrable (fun y => inner ℝ (ζ y)
      (G y (unitVector j) j • S y + v y j • DS y (unitVector j))) volume := fun j => inner_int hζ2 (mWB j)
  have iBA : ∀ j : Fin 3, Integrable (fun y => inner ℝ (Dζ y (unitVector j)) (v y j • S y) -
      inner ℝ (Dζ y (unitVector j)) (S y j • v y)) volume := fun j => (iB j).sub (iA j)
  have iWAB : ∀ j : Fin 3, Integrable (fun y => inner ℝ (ζ y)
      (DS y (unitVector j) j • v y + S y j • G y (unitVector j)) - inner ℝ (ζ y)
      (G y (unitVector j) j • S y + v y j • DS y (unitVector j))) volume := fun j => (iWA j).sub (iWB j)
  have iS1 : Integrable (fun y => ∑ j : Fin 3,
      (inner ℝ (Dζ y (unitVector j)) (v y j • S y) - inner ℝ (Dζ y (unitVector j)) (S y j • v y))) volume :=
    integrable_finsetSum _ fun j _ => iBA j
  have iS2 : Integrable (fun y => ∑ j : Fin 3, (inner ℝ (ζ y)
      (DS y (unitVector j) j • v y + S y j • G y (unitVector j)) - inner ℝ (ζ y)
      (G y (unitVector j) j • S y + v y j • DS y (unitVector j)))) volume :=
    integrable_finsetSum _ fun j _ => iWAB j
  refine ⟨(iS1.add (ic.const_mul 2)).congr (ae_of_all _ fun y => (hpt y).symm), ?_⟩
  have e1 : ∫ y, inner ℝ (v y) (convectionAdjointField S DS ζ Dζ y) =
      (∑ j : Fin 3, ((∫ y, inner ℝ (ζ y) (DS y (unitVector j) j • v y + S y j • G y (unitVector j))) -
        ∫ y, inner ℝ (ζ y) (G y (unitVector j) j • S y + v y j • DS y (unitVector j))))
        + 2 * ∫ y, inner ℝ (ζ y) (DS y (v y)) := by
    rw [integral_congr_ae (ae_of_all _ hpt), integral_add iS1 (ic.const_mul 2),
      integral_finsetSum _ fun j _ => iBA j, integral_const_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_sub (iB j) (iA j), pA j, pB j]
    ring
  have hpt2 : ∀ᵐ y ∂volume, inner ℝ (ζ y) (G y (S y)) = (∑ j : Fin 3, (inner ℝ (ζ y)
      (DS y (unitVector j) j • v y + S y j • G y (unitVector j)) - inner ℝ (ζ y)
      (G y (unitVector j) j • S y + v y j • DS y (unitVector j)))) + inner ℝ (ζ y) (DS y (v y)) := by
    filter_upwards [hv.divergence] with y hy
    have hd : ∑ j : Fin 3, DS y (unitVector j) j = 0 := by rw [hDS y]; exact hdiv y
    have hdv : ∑ j : Fin 3, G y (unitVector j) j = 0 := by simpa only [inner_unit] using hy
    have hWA : ∑ j : Fin 3, (DS y (unitVector j) j • v y + S y j • G y (unitVector j)) = G y (S y) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_smul, hd, zero_smul, zero_add]
      conv_rhs => rw [← sum_unit (S y)]
      rw [map_sum]
      simp only [map_smul]
    have hWB : ∑ j : Fin 3, (G y (unitVector j) j • S y + v y j • DS y (unitVector j)) = DS y (v y) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_smul, hdv, zero_smul, zero_add]
      conv_rhs => rw [← sum_unit (v y)]
      rw [map_sum]
      simp only [map_smul]
    rw [Finset.sum_sub_distrib, ← inner_sum, ← inner_sum, hWA, hWB]
    ring
  rw [e1, integral_congr_ae hpt2, integral_add iS2 ic, integral_finsetSum _ fun j _ => iWAB j]
  have e2 : ∀ j : Fin 3, ∫ y, (inner ℝ (ζ y) (DS y (unitVector j) j • v y + S y j • G y (unitVector j)) -
      inner ℝ (ζ y) (G y (unitVector j) j • S y + v y j • DS y (unitVector j))) =
      (∫ y, inner ℝ (ζ y) (DS y (unitVector j) j • v y + S y j • G y (unitVector j))) -
        ∫ y, inner ℝ (ζ y) (G y (unitVector j) j • S y + v y j • DS y (unitVector j)) := fun j =>
    integral_sub (iWA j) (iWB j)
  simp only [e2]
  ring

end Reduction

end CellCert

end Breakdown
