import Breakdown.FracCell.StCoordsProof
import Breakdown.FracCell.CylIntegral

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.CellCert.CellFormula

namespace Internal.RelZeroMode

open SteadyCert Assembly CellAnalysis

def turnVec (y : Space) : Space :=
  EuclideanSpace.single 0 (-(y 1)) + EuclideanSpace.single 1 (y 0)

def planeVec (y : Space) : Space :=
  EuclideanSpace.single 0 (y 0) + EuclideanSpace.single 1 (y 1)

def turnAt (t : ℝ) (y : Space) : Space :=
  Real.cos t • planeVec y + Real.sin t • turnVec y + EuclideanSpace.single 2 (y 2)

def rad (y : Space) : ℝ := Real.sqrt (y 0 ^ 2 + y 1 ^ 2)

def lift (g : ℝ × ℝ → ℝ) (y : Space) : ℝ := g (rad y, y 2)

def axialPart (G : Space → (Space →L[ℝ] Space)) (y : Space) : ℝ :=
  inner ℝ (G y (turnVec y)) (unitVector 2)

def halfPlane : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)

def fiberValue (G : Space → (Space →L[ℝ] Space)) (q : ℝ × ℝ) : ℝ :=
  q.1 * ∫ θ in (-Real.pi)..Real.pi, axialPart G (Spectral.cylPoint q.1 θ q.2)

theorem halfPlane_open : IsOpen halfPlane := isOpen_Ioi.prod isOpen_univ

theorem halfPlane_meas : MeasurableSet halfPlane := measurableSet_Ioi.prod MeasurableSet.univ

theorem turnVec_eq (y : Space) : turnVec y = (-(y 1)) • unitVector 0 + (y 0) • unitVector 1 := by
  ext i; fin_cases i <;> simp [turnVec, unitVector]

theorem turnAt_zero (y : Space) : turnAt 0 y = y := by
  ext i; fin_cases i <;> simp [turnAt, planeVec, turnVec]

theorem turnAt_apply0 (t : ℝ) (y : Space) : turnAt t y 0 = Real.cos t * y 0 - Real.sin t * y 1 := by
  simp [turnAt, planeVec, turnVec]; ring

theorem turnAt_apply1 (t : ℝ) (y : Space) : turnAt t y 1 = Real.sin t * y 0 + Real.cos t * y 1 := by
  simp [turnAt, planeVec, turnVec]; ring

theorem turnAt_apply2 (t : ℝ) (y : Space) : turnAt t y 2 = y 2 := by
  simp [turnAt, planeVec, turnVec]

theorem lift_turnAt (g : ℝ × ℝ → ℝ) (t : ℝ) (y : Space) : lift g (turnAt t y) = lift g y := by
  have h : rad (turnAt t y) = rad y := by
    unfold rad; congr 1; rw [turnAt_apply0, turnAt_apply1]
    linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq t
  simp only [lift, h, turnAt_apply2]

theorem hasDerivAt_turnAt (y : Space) : HasDerivAt (fun t => turnAt t y) (turnVec y) 0 := by
  have h := (((Real.hasDerivAt_cos 0).smul_const (planeVec y)).add
    ((Real.hasDerivAt_sin 0).smul_const (turnVec y))).add_const (EuclideanSpace.single 2 (y 2) : Space)
  unfold turnAt
  refine h.congr_deriv ?_
  simp

theorem fderiv_turnVec {φ : Space → ℝ} (hd : Differentiable ℝ φ) (hinv : ∀ t y, φ (turnAt t y) = φ y)
    (y : Space) : fderiv ℝ φ y (turnVec y) = 0 := by
  have hd0 : HasFDerivAt φ (fderiv ℝ φ y) (turnAt 0 y) := by
    rw [turnAt_zero]; exact (hd y).hasFDerivAt
  have h1 := HasFDerivAt.comp_hasDerivAt (hl := hd0) (hf := hasDerivAt_turnAt y)
  have h2 : HasDerivAt (φ ∘ fun t => turnAt t y) 0 0 := by
    have : (φ ∘ fun t => turnAt t y) = fun _ => φ y := by funext t; exact hinv t y
    rw [this]; exact hasDerivAt_const _ _
  exact h1.unique h2

theorem coord_contDiff (i : Fin 3) : ContDiff ℝ ∞ (fun y : Space => y i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff

theorem rad_contDiffAt {y : Space} (h : 0 < rad y) : ContDiffAt ℝ ∞ rad y := by
  have hp : ContDiff ℝ ∞ (fun y : Space => y 0 ^ 2 + y 1 ^ 2) :=
    ((coord_contDiff 0).pow 2).add ((coord_contDiff 1).pow 2)
  exact hp.contDiffAt.sqrt (Real.sqrt_pos.mp h).ne'

theorem rad_continuous : Continuous rad :=
  Real.continuous_sqrt.comp (((coord_contDiff 0).continuous.pow 2).add ((coord_contDiff 1).continuous.pow 2))

theorem lift_contDiff {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hs : tsupport g ⊆ halfPlane) :
    ContDiff ℝ ∞ (lift g) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : (rad y, y 2) ∈ tsupport g
  · have hr : 0 < rad y := (hs hy).1
    exact hg.contDiffAt.comp y ((rad_contDiffAt hr).prodMk (coord_contDiff 2).contDiffAt)
  · have hopen : IsOpen {w : Space | (rad w, w 2) ∉ tsupport g} :=
      (isClosed_tsupport g).isOpen_compl.preimage (rad_continuous.prodMk (coord_contDiff 2).continuous)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hy] with w hw
    simp only [lift]
    exact image_eq_zero_of_notMem_tsupport hw

theorem lift_hasCompactSupport {g : ℝ × ℝ → ℝ} (hg : HasCompactSupport g) : HasCompactSupport (lift g) := by
  obtain ⟨R, hR⟩ := hg.isCompact.isBounded.subset_closedBall (0 : ℝ × ℝ)
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * R)) ?_
  intro y hy
  by_contra hne
  apply hy
  have hm : (rad y, y 2) ∈ tsupport g := subset_tsupport g hne
  have hb := hR hm
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at hb
  have h1 : |rad y| ≤ R := (max_le_iff.mp hb).1
  have h2 : |y 2| ≤ R := (max_le_iff.mp hb).2
  have hR0 : 0 ≤ R := (abs_nonneg _).trans h2
  have hr2 : rad y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
  have e1 : rad y ^ 2 ≤ R ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e2 : y 2 ^ 2 ≤ R ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.mpr ⟨by linarith, ?_⟩
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  nlinarith

theorem col_memLp {G : Space → (Space →L[ℝ] Space)} (hGm : AEStronglyMeasurable G volume)
    (hG2 : Integrable (fun y => entrySq (G y))) (j : Fin 3) :
    MemLp (fun y => G y (unitVector j)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => G y (unitVector j)) volume :=
    (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable hGm
  refine (memLp_two_iff_integrable_sq_norm hm).mpr ?_
  refine hG2.mono' (hm.norm.pow 2) (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  unfold entrySq
  exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => by positivity)
    (Finset.mem_univ j)

theorem col_li {G : Space → (Space →L[ℝ] Space)} (hGm : AEStronglyMeasurable G volume)
    (hG2 : Integrable (fun y => entrySq (G y))) (j : Fin 3) :
    LocallyIntegrable (fun y => G y (unitVector j)) volume :=
  (col_memLp hGm hG2 j).locallyIntegrable (by norm_num)

theorem axial_eq (G : Space → (Space →L[ℝ] Space)) (y : Space) :
    axialPart G y = y 0 * inner ℝ (unitVector 2) (G y (unitVector 1))
      - y 1 * inner ℝ (unitVector 2) (G y (unitVector 0)) := by
  unfold axialPart
  rw [turnVec_eq]
  simp only [map_add, map_smul, inner_add_left, real_inner_smul_left]
  rw [real_inner_comm (unitVector 2) (G y (unitVector 0)), real_inner_comm (unitVector 2) (G y (unitVector 1))]
  ring

theorem axial_li {G : Space → (Space →L[ℝ] Space)} (hGm : AEStronglyMeasurable G volume)
    (hG2 : Integrable (fun y => entrySq (G y))) : LocallyIntegrable (axialPart G) volume := by
  have a1 : LocallyIntegrable (fun y => inner ℝ (unitVector 2) (G y (unitVector 1))) volume :=
    ((col_memLp hGm hG2 1).const_inner (unitVector 2)).locallyIntegrable (by norm_num)
  have a0 : LocallyIntegrable (fun y => inner ℝ (unitVector 2) (G y (unitVector 0))) volume :=
    ((col_memLp hGm hG2 0).const_inner (unitVector 2)).locallyIntegrable (by norm_num)
  have e : axialPart G = fun y => y 0 * inner ℝ (unitVector 2) (G y (unitVector 1))
      - y 1 * inner ℝ (unitVector 2) (G y (unitVector 0)) := funext (axial_eq G)
  rw [e]
  exact (a1.continuous_mul (coord_contDiff 0).continuous).sub (a0.continuous_mul (coord_contDiff 1).continuous)

theorem fderiv_coord_mul {φ : Space → ℝ} (hφ : Differentiable ℝ φ) (i j : Fin 3) (y : Space) :
    fderiv ℝ (fun w : Space => w i * φ w) y (unitVector j) =
      y i * fderiv ℝ φ y (unitVector j) + φ y * (if i = j then 1 else 0) := by
  have hc : HasFDerivAt (fun w : Space => w i) (EuclideanSpace.proj i : Space →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt
  rw [HasFDerivAt.fderiv (f := fun w : Space => w i * φ w) (hc.mul (hφ y).hasFDerivAt)]
  simp [unitVector]

theorem weak_axial {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hv : MemLp v 6 volume)
    (hGm : AEStronglyMeasurable G volume) (hG2 : Integrable (fun y => entrySq (G y)))
    (hw : IsWeakGradientOf v G) {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ)
    (hrot : ∀ y, fderiv ℝ φ y (turnVec y) = 0) : ∫ y, φ y * axialPart G y = 0 := by
  have hvl : LocallyIntegrable v volume := hv.locallyIntegrable (by norm_num)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have t0 : IsTestScalar (fun y : Space => y 0 * φ y) := ⟨(coord_contDiff 0).mul hφ, hφs.mul_left⟩
  have t1 : IsTestScalar (fun y : Space => y 1 * φ y) := ⟨(coord_contDiff 1).mul hφ, hφs.mul_left⟩
  have E0 := hw _ t0 1
  have E1 := hw _ t1 0
  simp only [fderiv_coord_mul hφd] at E0 E1
  simp only [Fin.reduceEq, if_false, mul_zero, add_zero] at E0 E1
  have fc : ∀ j : Fin 3, Continuous (fun y => fderiv ℝ φ y (unitVector j)) := fun j =>
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have iA : Integrable (fun y => (y 1 * φ y) • G y (unitVector 0)) :=
    (col_li hGm hG2 0).integrable_smul_left_of_hasCompactSupport t1.1.continuous t1.2
  have iB : Integrable (fun y => (y 0 * φ y) • G y (unitVector 1)) :=
    (col_li hGm hG2 1).integrable_smul_left_of_hasCompactSupport t0.1.continuous t0.2
  have key : (∫ y, (y 0 * fderiv ℝ φ y (unitVector 1)) • v y) =
      ∫ y, (y 1 * fderiv ℝ φ y (unitVector 0)) • v y := by
    congr 1; funext y
    have h := hrot y
    rw [turnVec_eq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
    congr 1; linarith
  have A : (∫ y, (y 0 * φ y) • G y (unitVector 1)) = ∫ y, (y 1 * φ y) • G y (unitVector 0) := by
    rw [← neg_neg (∫ y, (y 0 * φ y) • G y (unitVector 1)), ← E0, key, E1, neg_neg]
  have hpt : ∀ y, φ y * axialPart G y = inner ℝ (unitVector 2)
      ((y 0 * φ y) • G y (unitVector 1) - (y 1 * φ y) • G y (unitVector 0)) := by
    intro y
    rw [axial_eq, inner_sub_right, real_inner_smul_right, real_inner_smul_right]
    ring
  calc (∫ y, φ y * axialPart G y)
      = ∫ y, inner ℝ (unitVector 2) ((y 0 * φ y) • G y (unitVector 1) - (y 1 * φ y) • G y (unitVector 0)) :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = inner ℝ (unitVector 2) ((∫ y, (y 0 * φ y) • G y (unitVector 1)) - ∫ y, (y 1 * φ y) • G y (unitVector 0)) := by
        have hi := integral_inner (𝕜 := ℝ) (iB.sub iA) (unitVector 2)
        simp only [Pi.sub_apply] at hi
        rw [hi, integral_sub iB iA]
    _ = 0 := by rw [A, sub_self, inner_zero_right]

theorem cyl_apply0 (r θ z : ℝ) : Spectral.cylPoint r θ z 0 = r * Real.cos θ := by simp [Spectral.cylPoint]

theorem cyl_apply1 (r θ z : ℝ) : Spectral.cylPoint r θ z 1 = r * Real.sin θ := by simp [Spectral.cylPoint]

theorem cyl_apply2 (r θ z : ℝ) : Spectral.cylPoint r θ z 2 = z := by simp [Spectral.cylPoint]

theorem rad_cyl {r : ℝ} (hr : 0 < r) (θ z : ℝ) : rad (Spectral.cylPoint r θ z) = r := by
  unfold rad
  rw [cyl_apply0, cyl_apply1, show (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 by
    linear_combination r ^ 2 * Real.sin_sq_add_cos_sq θ, Real.sqrt_sq hr.le]

theorem norm_cyl (r θ z : ℝ) : ‖Spectral.cylPoint r θ z‖ ^ 2 = r ^ 2 + z ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, cyl_apply0, cyl_apply1, cyl_apply2]
  linear_combination r ^ 2 * Real.sin_sq_add_cos_sq θ

open Spectral.Internal.CylIntegral in
theorem fiber_integrable {f : Space → ℝ} (hf : Integrable f) :
    IntegrableOn (fun q : ℝ × ℝ => q.1 * ∫ θ in (-Real.pi)..Real.pi, f (Spectral.cylPoint q.1 θ q.2))
      halfPlane := by
  set g : (ℝ × ℝ) × ℝ → ℝ := fun w => f (toSpace w) with hg_def
  have hg : Integrable g := (toSpace_mp.integrable_comp_emb toSpace.measurableEmbedding).mpr hf
  have hH := change_integrable hg
  set H : (ℝ × ℝ) × ℝ → ℝ := fun x => x.1.1 * g (cylMap.symm x) with hH_def
  have hHσ : IntegrableOn (H ∘ swapEquiv) (halfPlane ×ˢ Ioo (-Real.pi) Real.pi) := by
    unfold halfPlane
    rw [← swapEquiv_preimage]
    exact (swapEquiv_mp.integrableOn_comp_preimage swapEquiv.measurableEmbedding).mpr hH
  have hprod : Integrable (H ∘ swapEquiv)
      ((volume.restrict halfPlane).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hHσ
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  refine hprod.integral_prod_left.congr (Eventually.of_forall fun q => ?_)
  show (∫ θ in Ioo (-Real.pi) Real.pi, (H ∘ swapEquiv) (q, θ)) =
    q.1 * ∫ θ in (-Real.pi)..Real.pi, f (Spectral.cylPoint q.1 θ q.2)
  rw [intervalIntegral.integral_of_le hpi, integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
  obtain ⟨r, z⟩ := q
  simp only [Function.comp_apply, swapEquiv_apply, hH_def, hg_def]
  rw [← toSpace_apply]
  rfl

theorem fiberValue_integrableOn {G : Space → (Space →L[ℝ] Space)} (hGm : AEStronglyMeasurable G volume)
    (hG2 : Integrable (fun y => entrySq (G y))) (R : ℝ) :
    IntegrableOn (fiberValue G) (halfPlane ∩ Metric.closedBall 0 R) := by
  have hfR : Integrable ((Metric.closedBall (0 : Space) (2 * R)).indicator (axialPart G)) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      ((axial_li hGm hG2).integrableOn_isCompact (isCompact_closedBall _ _))
  refine ((fiber_integrable hfR).mono_set inter_subset_left).congr_fun (fun q hq => ?_)
    (halfPlane_meas.inter measurableSet_closedBall)
  have hb := hq.2
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at hb
  have h1 : |q.1| ≤ R := (max_le_iff.mp hb).1
  have h2 : |q.2| ≤ R := (max_le_iff.mp hb).2
  have hR0 : 0 ≤ R := (abs_nonneg _).trans h2
  have e1 : q.1 ^ 2 ≤ R ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e2 : q.2 ^ 2 ≤ R ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  unfold fiberValue
  dsimp only
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  refine indicator_of_mem ?_ _
  rw [Metric.mem_closedBall, dist_zero_right]
  have hn := norm_cyl q.1 θ q.2
  nlinarith [norm_nonneg (Spectral.cylPoint q.1 θ q.2)]

theorem fiberValue_loc {G : Space → (Space →L[ℝ] Space)} (hGm : AEStronglyMeasurable G volume)
    (hG2 : Integrable (fun y => entrySq (G y))) : LocallyIntegrableOn (fiberValue G) halfPlane := by
  intro x _
  refine ⟨halfPlane ∩ Metric.closedBall 0 (‖x‖ + 1), inter_mem_nhdsWithin _ ?_, fiberValue_integrableOn hGm hG2 _⟩
  exact Metric.closedBall_mem_nhds_of_mem (by rw [mem_ball_zero_iff]; linarith)

theorem lift_cyl {G : Space → (Space →L[ℝ] Space)} (hGm : AEStronglyMeasurable G volume)
    (hG2 : Integrable (fun y => entrySq (G y))) {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : HasCompactSupport g) (hsub : tsupport g ⊆ halfPlane) :
    ∫ y, lift g y * axialPart G y = ∫ q in halfPlane, g q • fiberValue G q := by
  have hint : Integrable (fun y => lift g y * axialPart G y) :=
    (axial_li hGm hG2).integrable_smul_left_of_hasCompactSupport (lift_contDiff hg hsub).continuous
      (lift_hasCompactSupport hgs)
  rw [Spectral.cylIntegral _ hint]
  refine setIntegral_congr_fun halfPlane_meas (fun q hq => ?_)
  have hr : 0 < q.1 := hq.1
  have hl : ∀ θ, lift g (Spectral.cylPoint q.1 θ q.2) = g q := by
    intro θ; simp only [lift]; rw [rad_cyl hr, cyl_apply2]
  simp only [hl, fiberValue, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul]
  ring

theorem fiberValue_ae {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hv : MemLp v 6 volume)
    (hGm : AEStronglyMeasurable G volume) (hG2 : Integrable (fun y => entrySq (G y)))
    (hw : IsWeakGradientOf v G) : ∀ᵐ q ∂(volume : Measure (ℝ × ℝ)), q ∈ halfPlane → fiberValue G q = 0 := by
  refine halfPlane_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero (fiberValue_loc hGm hG2) ?_
  intro g hg hgs hsub
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := halfPlane) (fun q hq => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hq (hsub h)), zero_smul])]
  rw [← lift_cyl hGm hG2 hg hgs hsub]
  exact weak_axial hv hGm hG2 hw (lift_contDiff hg hsub) (lift_hasCompactSupport hgs)
    (fderiv_turnVec ((lift_contDiff hg hsub).differentiable (by simp)) (lift_turnAt g))

theorem turnVec_cyl (r θ z : ℝ) : turnVec (Spectral.cylPoint r θ z) = r • angularUnit θ := by
  ext i; fin_cases i <;> simp [turnVec, Spectral.cylPoint, angularUnit]

theorem axial_cyl (G : Space → (Space →L[ℝ] Space)) (r θ z : ℝ) :
    axialPart G (Spectral.cylPoint r θ z) = r * frameMat θ (G (CellAnalysis.cylPoint r θ z)) 2 1 := by
  unfold axialPart
  rw [turnVec_cyl, map_smul, real_inner_smul_left]
  rfl

theorem frame_periodic (G : Space → (Space →L[ℝ] Space)) (r z : ℝ) :
    Function.Periodic (fun θ => frameMat θ (G (CellAnalysis.cylPoint r θ z)) 2 1) (2 * Real.pi) := by
  intro θ
  simp only [frameMat, CellAnalysis.cylPoint, radialUnit, angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem mode_zero {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hv : MemLp v 6 volume)
    (hGm : AEStronglyMeasurable G volume) (hG2 : Integrable (fun y => entrySq (G y)))
    (hw : IsWeakGradientOf v G) (m : ℕ) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), 0 < p.1 → modeMat m 0 G p.1 p.2 2 1 = 0 := by
  filter_upwards [fiberValue_ae hv hGm hG2 hw] with q hq hpos
  have h0 := hq ⟨hpos, mem_univ _⟩
  have hI : ∫ θ in (-Real.pi)..Real.pi, frameMat θ (G (CellAnalysis.cylPoint q.1 θ q.2)) 2 1 = 0 := by
    unfold fiberValue at h0
    simp only [axial_cyl] at h0
    rw [intervalIntegral.integral_const_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hpos.ne'
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hpos.ne'
      · exact h'
  have h2 : ∫ θ in (0 : ℝ)..(2 * Real.pi), frameMat θ (G (CellAnalysis.cylPoint q.1 θ q.2)) 2 1 = 0 := by
    have := (frame_periodic G q.1 q.2).intervalIntegral_add_eq (-Real.pi) 0
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at this
    rw [← this, hI]
  unfold modeMat
  simp only [azimuth, Int.cast_zero, zero_mul, Complex.ofReal_zero, neg_zero, Complex.exp_zero, one_mul]
  rw [intervalIntegral.integral_ofReal, h2]
  simp

end Internal.RelZeroMode

open SteadyCert Assembly CellAnalysis Internal.RelZeroMode

private theorem ae_fst_ne_zero : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.1 ≠ 0 := by
  rw [ae_iff]
  have hs : {p : ℝ × ℝ | ¬ p.1 ≠ 0} = ({0} : Set ℝ) ×ˢ (univ : Set ℝ) := by
    ext p; simp
  rw [hs, Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem relZeroMode_holds : RelZeroModeStatement := by
  intro k N c K S B L hL x hx ρ
  have hsec := hx.1
  have hr0 : 0 ≤ L.box.r₁ := by rw [hL.box_eq]; exact hL.box_valid.r_order.1
  simp only [CellLayout.relationRow, Sum.elim_inr, Sum.elim_inl]
  cases hz : L.zeroMode with
  | none => simp
  | some n0 =>
    have hn0 : (n0 : ℤ) = 0 := by
      unfold CellLayout.zeroMode at hz
      split_ifs at hz with hm
      rw [← Option.some.inj hz]
    simp only [CellLayout.strainAt, dif_pos (And.intro ρ.1.isLt ρ.2.isLt), CellLayout.unitAt,
      Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [CellLayout.trueData, CellDatum.lowStrain, Sum.elim_inl, CellBases.coef,
      CellLayout.gradModeOf, gradMode, hn0]
    refine integral_eq_zero_of_ae ?_
    rw [EventuallyEq]
    refine (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc : MeasurableSet L.box.rect)).mpr ?_
    filter_upwards [mode_zero hsec.velocity_six hsec.measurable_gradient hsec.gradient_two hsec.weak_gradient
      L.order, ae_fst_ne_zero] with p hp hne hpr
    have hpos : 0 < p.1 := lt_of_le_of_ne (hr0.trans hpr.1.1) (Ne.symm hne)
    simp [hp hpos]

end Breakdown.CellCert.CellFormula
