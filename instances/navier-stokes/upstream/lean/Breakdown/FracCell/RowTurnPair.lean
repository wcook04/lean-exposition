import Breakdown.FracCell.ReductionLossDefs
import Breakdown.FracCert.DriftWeakLimit
import Breakdown.Frac.PMomentum
import Breakdown.Frac.PAxial
import Breakdown.Cert.CoerciveSmoothApproxPeriodBound

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal Convolution Pointwise

noncomputable section

namespace Breakdown.FracInternal.RowTurnPair

open SteadyCert

theorem unit_expand (u : Space) : u = ∑ j : Fin 3, u j • unitVector j := by
  ext i
  fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

theorem units_sum (A : Space →L[ℝ] Space) (w : Space) : ∑ k : Fin 3, w k • A (unitVector k) = A w := by
  conv_rhs => rw [unit_expand w]
  simp only [map_sum, map_smul]

def turnCoord (j : Fin 3) : Space →L[ℝ] ℝ :=
  (EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp SteadyCert.Internal.DriftWeakLimit.turnL

theorem turnCoord_apply (j : Fin 3) (y : Space) : turnCoord j y = axialTurn y j := by
  simp [turnCoord, SteadyCert.Internal.DriftWeakLimit.turnL_apply]

theorem turnCoord_unit (j : Fin 3) : turnCoord j (unitVector j) = 0 := by
  rw [turnCoord_apply]
  fin_cases j <;> simp [axialTurn, unitVector]

def testPiece (ψ : Space → Space) (i j : Fin 3) (y : Space) : ℝ := turnCoord j y * ψ y i

theorem testPiece_hasFDerivAt {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) (i j : Fin 3) (y : Space) :
    HasFDerivAt (testPiece ψ i j)
      (turnCoord j y • ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (fderiv ℝ ψ y))
        + ψ y i • turnCoord j) y := by
  have h1 : HasFDerivAt (fun z => turnCoord j z) (turnCoord j) y := (turnCoord j).hasFDerivAt
  have h2 : HasFDerivAt (fun z => ψ z i) ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (fderiv ℝ ψ y)) y := by
    have hd : HasFDerivAt ψ (fderiv ℝ ψ y) y := ((hψ.differentiable (by simp)) y).hasFDerivAt
    exact (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y hd
  exact h1.mul h2

theorem testPiece_deriv {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) (i j : Fin 3) (y : Space) :
    fderiv ℝ (testPiece ψ i j) y (unitVector j) = axialTurn y j * fderiv ℝ ψ y (unitVector j) i := by
  have hu : axialTurn (unitVector j) j = 0 := by rw [← turnCoord_apply]; exact turnCoord_unit j
  rw [(testPiece_hasFDerivAt hψ i j y).fderiv]
  simp [turnCoord_apply, hu]

theorem testPiece_test {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (i j : Fin 3) :
    IsTestScalar (testPiece ψ i j) := by
  refine ⟨(turnCoord j).contDiff.mul ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hψ), ?_⟩
  have hc : HasCompactSupport (fun y => ψ y i) := hψc.comp_left (g := fun w : Space => w i) (by simp)
  exact hc.mul_left

theorem coord_weak {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hw : IsWeakGradientOf v G)
    (hvl : LocallyIntegrable v volume) (hGl : ∀ j, LocallyIntegrable (fun y => G y (unitVector j)) volume)
    {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (i j : Fin 3) :
    Integrable (fun y => axialTurn y j * fderiv ℝ ψ y (unitVector j) i * v y i) ∧
      Integrable (fun y => testPiece ψ i j y * G y (unitVector j) i) ∧
      ∫ y, axialTurn y j * fderiv ℝ ψ y (unitVector j) i * v y i =
        -∫ y, testPiece ψ i j y * G y (unitVector j) i := by
  have ht := testPiece_test hψ hψc i j
  have i1 : Integrable (fun y => fderiv ℝ (testPiece ψ i j) y (unitVector j) • v y) :=
    hvl.integrable_smul_left_of_hasCompactSupport
      ((ht.1.continuous_fderiv (by simp)).clm_apply continuous_const) (ht.2.fderiv_apply ℝ (unitVector j))
  have i2 : Integrable (fun y => testPiece ψ i j y • G y (unitVector j)) :=
    (hGl j).integrable_smul_left_of_hasCompactSupport ht.1.continuous ht.2
  have p1 := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integrable_comp i1
  have p2 := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integrable_comp i2
  have e1 : (fun y => (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (fderiv ℝ (testPiece ψ i j) y (unitVector j) • v y))
      = fun y => axialTurn y j * fderiv ℝ ψ y (unitVector j) i * v y i := by
    funext y; simp [testPiece_deriv hψ]
  have e2 : (fun y => (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (testPiece ψ i j y • G y (unitVector j)))
      = fun y => testPiece ψ i j y * G y (unitVector j) i := by
    funext y; simp
  refine ⟨e1 ▸ p1, e2 ▸ p2, ?_⟩
  have hk := congrArg (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (hw _ ht j)
  rw [← (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm i1, map_neg,
    ← (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm i2, e1, e2] at hk
  exact hk

theorem integrable_turnInner {v : Space → Space} (hvl : LocallyIntegrable v volume)
    {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun y => ∑ k : Fin 3, axialTurn (ψ y) k * v y k) := by
  refine integrable_finsetSum _ fun k _ => ?_
  have hc : Continuous (fun y => axialTurn (ψ y) k) := by
    have := (turnCoord k).continuous.comp hψ.continuous
    simpa [Function.comp_def, turnCoord_apply] using this
  have hs : HasCompactSupport (fun y => axialTurn (ψ y) k) :=
    hψc.comp_left (g := fun w : Space => axialTurn w k) (by simp [axialTurn])
  have h1 := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integrable_comp
    (hvl.integrable_smul_left_of_hasCompactSupport hc hs)
  simpa using h1

theorem skew_smooth {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hw : IsWeakGradientOf v G)
    (hvl : LocallyIntegrable v volume) (hGl : ∀ j, LocallyIntegrable (fun y => G y (unitVector j)) volume)
    {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    l2Pair (fun y => G y (axialTurn y) - axialTurn (v y)) ψ =
      -l2Pair v (fun y => fderiv ℝ ψ y (axialTurn y) - axialTurn (ψ y)) := by
  have hA : (fun y => inner ℝ (G y (axialTurn y) - axialTurn (v y)) (ψ y)) = fun y =>
      (∑ i : Fin 3, ∑ j : Fin 3, testPiece ψ i j y * G y (unitVector j) i)
        + ∑ k : Fin 3, axialTurn (ψ y) k * v y k := by
    funext y
    rw [← units_sum (G y) (axialTurn y)]
    simp [testPiece, turnCoord_apply, PiLp.inner_apply, Fin.sum_univ_three, axialTurn]
    ring
  have hB : (fun y => inner ℝ (v y) (fderiv ℝ ψ y (axialTurn y) - axialTurn (ψ y))) = fun y =>
      (∑ i : Fin 3, ∑ j : Fin 3, axialTurn y j * fderiv ℝ ψ y (unitVector j) i * v y i)
        - ∑ k : Fin 3, axialTurn (ψ y) k * v y k := by
    funext y
    rw [← units_sum (fderiv ℝ ψ y) (axialTurn y)]
    simp [PiLp.inner_apply, Fin.sum_univ_three, axialTurn]
    ring
  have hc := coord_weak hw hvl hGl hψ hψc
  have hQ := integrable_turnInner hvl hψ hψc
  have hS1 : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, testPiece ψ i j y * G y (unitVector j) i) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hc i j).2.1
  have hS2 : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, axialTurn y j * fderiv ℝ ψ y (unitVector j) i * v y i) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hc i j).1
  unfold l2Pair
  rw [hA, hB, integral_add hS1 hQ, integral_sub hS2 hQ,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hc i j).2.1,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hc i j).1]
  have hin : ∀ i : Fin 3, ∫ y, ∑ j : Fin 3, axialTurn y j * fderiv ℝ ψ y (unitVector j) i * v y i
      = -∫ y, ∑ j : Fin 3, testPiece ψ i j y * G y (unitVector j) i := by
    intro i
    rw [integral_finsetSum _ fun j _ => (hc i j).1, integral_finsetSum _ fun j _ => (hc i j).2.1,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => (hc i j).2.2
  simp only [hin, Finset.sum_neg_distrib]
  ring


theorem pair_tendsto {F : Space → Space} {K : Set Space} (hF : MemLp (K.indicator F) 2 volume)
    {ψ : ℕ → Space → Space} {e : Space → Space} (hψK : ∀ n y, y ∉ K → ψ n y = 0)
    (heK : ∀ᵐ y ∂volume, y ∉ K → e y = 0) (hψ2 : ∀ n, MemLp (ψ n) 2 volume) (he : MemLp e 2 volume)
    (hconv : Tendsto (fun n => eLpNorm (ψ n - e) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => l2Pair F (ψ n)) atTop (𝓝 (l2Pair F e)) := by
  have hpair : ∀ (g : Space → Space) (hg : MemLp g 2 volume), (∀ᵐ y ∂volume, y ∉ K → g y = 0) →
      l2Pair F g = inner ℝ (hF.toLp _) (hg.toLp g) := by
    intro g hg hgK
    rw [MeasureTheory.L2.inner_def]
    unfold l2Pair
    refine integral_congr_ae ?_
    filter_upwards [hF.coeFn_toLp, hg.coeFn_toLp, hgK] with y h1 h2 h3
    show inner ℝ (F y) (g y) = inner ℝ ((hF.toLp _) y) ((hg.toLp g) y)
    rw [h1, h2]
    by_cases hy : y ∈ K
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy, h3 hy]
  have hlim : Tendsto (fun n => (hψ2 n).toLp (ψ n)) atTop (𝓝 (he.toLp e)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hn : ∀ n, ‖(hψ2 n).toLp (ψ n) - he.toLp e‖ = (eLpNorm (ψ n - e) 2 volume).toReal := by
      intro n
      rw [← MemLp.toLp_sub, Lp.norm_toLp]
    simp_rw [hn]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
    simpa [Function.comp_def] using this
  have hin := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := hF.toLp (K.indicator F))) hlim
  rw [hpair e he heK]
  exact hin.congr fun n => (hpair _ (hψ2 n) (Eventually.of_forall (hψK n))).symm

theorem col_memLp {G : Space → (Space →L[ℝ] Space)} (hm : AEStronglyMeasurable G volume)
    (hi : Integrable (fun y => entrySq (G y))) (j : Fin 3) : MemLp (fun y => G y (unitVector j)) 2 volume := by
  have hmj : AEStronglyMeasurable (fun y => G y (unitVector j)) volume := hm.apply_continuousLinearMap (unitVector j)
  refine (memLp_two_iff_integrable_sq_norm hmj).2 (hi.mono' (hmj.norm.pow 2) (Eventually.of_forall fun y => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)

theorem indicator_memLp_six {K : Set Space} (hK : IsCompact K) {v : Space → Space} (hv : MemLp v 6 volume) :
    MemLp (K.indicator v) 2 volume := by
  rw [memLp_indicator_iff_restrict hK.measurableSet]
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact (hv.restrict K).mono_exponent (by norm_num)

theorem indicator_memLp_turnGrad {K : Set Space} (hK : IsCompact K) {G : Space → (Space →L[ℝ] Space)}
    (hm : AEStronglyMeasurable G volume) (hi : Integrable (fun y => entrySq (G y))) :
    MemLp (K.indicator (fun y => G y (axialTurn y))) 2 volume := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  have hfun : K.indicator (fun y => G y (axialTurn y)) =
      fun y => ∑ j : Fin 3, K.indicator (fun z => turnCoord j z) y • G y (unitVector j) := by
    funext y
    by_cases hy : y ∈ K
    · simp only [Set.indicator_of_mem hy, turnCoord_apply]
      exact (units_sum (G y) (axialTurn y)).symm
    · simp [Set.indicator_of_notMem hy]
  rw [hfun]
  refine memLp_finsetSum _ fun j _ => ?_
  have hb : MemLp (K.indicator (fun z => turnCoord j z)) ∞ volume := by
    refine memLp_top_of_bound (((turnCoord j).continuous.aestronglyMeasurable).indicator hK.measurableSet)
      (‖turnCoord j‖ * max r 0) (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
      have h1 := (turnCoord j).le_opNorm y
      have h2 : ‖y‖ ≤ max r 0 := le_max_of_le_left (by simpa using hr hy)
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    · rw [Set.indicator_of_notMem hy, norm_zero]
      exact mul_nonneg (norm_nonneg _) (le_max_right _ _)
  exact (col_memLp hm hi j).smul hb

theorem indicator_memLp_turnField {K : Set Space} (hK : IsCompact K) {m : ℕ} {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hv : IsSecondOrderField m v G H) :
    MemLp (K.indicator (fun y => G y (axialTurn y) - axialTurn (v y))) 2 volume := by
  have h1 := indicator_memLp_turnGrad hK hv.measurable_gradient hv.gradient_two
  have h2 : MemLp (K.indicator (fun y => axialTurn (v y))) 2 volume := by
    have hc := SteadyCert.Internal.DriftWeakLimit.turnL.comp_memLp' (indicator_memLp_six hK hv.velocity_six)
    have he : (SteadyCert.Internal.DriftWeakLimit.turnL ∘ K.indicator v) = K.indicator (fun y => axialTurn (v y)) := by
      funext y
      by_cases hy : y ∈ K
      · simp [Set.indicator_of_mem hy, SteadyCert.Internal.DriftWeakLimit.turnL_apply]
      · simp [Set.indicator_of_notMem hy]
    rwa [he] at hc
  rw [Set.indicator_sub]
  exact h1.sub h2


def kernRaw (n : ℕ) (y : Space) : ℝ := Real.smoothTransition (1 - ((n : ℝ) + 1) ^ 2 * ‖y‖ ^ 2)

theorem kernRaw_contDiff (n : ℕ) : ContDiff ℝ ∞ (kernRaw n) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ)))

theorem kernRaw_nonneg (n : ℕ) (y : Space) : 0 ≤ kernRaw n y := Real.smoothTransition.nonneg _

theorem kernRaw_zero (n : ℕ) {y : Space} (hy : 1 ≤ ((n : ℝ) + 1) * ‖y‖) : kernRaw n y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith

theorem kernRaw_support (n : ℕ) {y : Space} (hy : kernRaw n y ≠ 0) : ‖y‖ ≤ 1 := by
  by_contra h
  have h := not_le.mp h
  apply hy
  apply kernRaw_zero
  have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  nlinarith

theorem kernRaw_compact (n : ℕ) : HasCompactSupport (kernRaw n) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) 1) fun y hy => by
    by_contra h
    exact hy (by simpa using kernRaw_support n h)

theorem kernRaw_integral_pos (n : ℕ) : 0 < ∫ y, kernRaw n y := by
  have hc : Continuous (kernRaw n) := (kernRaw_contDiff n).continuous
  have hi : Integrable (kernRaw n) := hc.integrable_of_hasCompactSupport (kernRaw_compact n)
  rw [integral_pos_iff_support_of_nonneg (kernRaw_nonneg n) hi]
  have ho : IsOpen (Function.support (kernRaw n)) := hc.isOpen_support
  have h0 : (0 : Space) ∈ Function.support (kernRaw n) := by
    simp [kernRaw, Function.mem_support]
  exact ho.measure_pos volume ⟨0, h0⟩

def kern (n : ℕ) (y : Space) : ℝ := (∫ z, kernRaw n z)⁻¹ * kernRaw n y

theorem kern_contDiff (n : ℕ) : ContDiff ℝ ∞ (kern n) := contDiff_const.mul (kernRaw_contDiff n)

theorem kern_compact (n : ℕ) : HasCompactSupport (kern n) := (kernRaw_compact n).mul_left

theorem kern_support (n : ℕ) {y : Space} (hy : kern n y ≠ 0) : ‖y‖ ≤ 1 :=
  kernRaw_support n fun h => hy (by simp [kern, h])

theorem kern_iso (n : ℕ) (R : Space ≃ₗᵢ[ℝ] Space) (y : Space) : kern n (R y) = kern n y := by
  simp [kern, kernRaw]

theorem axis_null : ∀ᵐ w ∂(volume : Measure Space), CellCert.Reduction.horizontalNorm w ≠ 0 := by
  let L : Space →ₗ[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).toLinearMap
  have hne : LinearMap.ker L ≠ ⊤ := by
    intro h
    have : unitVector 0 ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    simp [L, unitVector] at this
  have h0 : volume (LinearMap.ker L : Set Space) = 0 := Measure.addHaar_submodule volume _ hne
  refine measure_mono_null (fun w hw => ?_) h0
  have hw0 : CellCert.Reduction.horizontalNorm w = 0 := by
    by_contra h
    exact hw h
  simp only [SetLike.mem_coe, LinearMap.mem_ker, L]
  unfold CellCert.Reduction.horizontalNorm at hw0
  have hs : w 0 ^ 2 + w 1 ^ 2 = 0 := by
    have := Real.sqrt_eq_zero'.mp hw0
    nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
  have : w 0 ^ 2 = 0 := by nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

theorem rot_eq (θ : ℝ) (y : Space) : axialRotation θ y = CellCert.Reduction.turnBy θ y :=
  axialRotationSpec.1 θ y

theorem conv_turn (n : ℕ) {e e' : Space → Space} (he : LocallyIntegrable e volume)
    (he' : LocallyIntegrable e' volume) (k : ℝ)
    (hcov : ∀ᵐ w ∂volume, ∀ θ : ℝ, e (axialRotation θ w) =
      axialRotation θ (Real.cos (k * θ) • e w + Real.sin (k * θ) • e' w)) (θ : ℝ) (y : Space) :
    (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] e) (axialRotation θ y) =
      axialRotation θ (Real.cos (k * θ) • (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] e) y
        + Real.sin (k * θ) • (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] e') y) := by
  set R := axialRotation θ
  have hi : Integrable (fun s => kern n s • e (y - s)) := by
    have := (kern_compact n).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) (kern_contDiff n).continuous he y
    simpa [ConvolutionExistsAt] using this
  have hi' : Integrable (fun s => kern n s • e' (y - s)) := by
    have := (kern_compact n).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) (kern_contDiff n).continuous he' y
    simpa [ConvolutionExistsAt] using this
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply]
  rw [← (R.measurePreserving).integral_comp R.toHomeomorph.measurableEmbedding
    (fun t => kern n t • e (R y - t))]
  simp only [kern_iso, ← map_sub]
  have hae : ∀ᵐ s ∂volume, kern n s • e (R (y - s)) =
      R.toContinuousLinearEquiv (Real.cos (k * θ) • (kern n s • e (y - s)) + Real.sin (k * θ) • (kern n s • e' (y - s))) := by
    filter_upwards [(quasiMeasurePreserving_sub_left volume y).ae hcov] with s hs
    rw [hs θ]
    simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, map_add, map_smul, smul_add, smul_smul]
    rw [mul_comm (kern n s), mul_comm (kern n s)]
  rw [integral_congr_ae hae, ContinuousLinearEquiv.integral_comp_comm, integral_add (f := fun x => Real.cos (k * θ) • (kern n x • e (y - x)))
    (g := fun x => Real.sin (k * θ) • (kern n x • e' (y - x))) (hi.smul (Real.cos (k * θ))) (hi'.smul (Real.sin (k * θ))),
    integral_smul, integral_smul]
  rfl

theorem rot_zero (z : Space) : axialRotation 0 z = z := by
  rw [axialRotationSpec.2.1]
  rfl

theorem turn_deriv {ψ ψ' : Space → Space} (hψ : ContDiff ℝ ∞ ψ) (k : ℝ)
    (hcov : ∀ θ y, ψ (axialRotation θ y) =
      axialRotation θ (Real.cos (k * θ) • ψ y + Real.sin (k * θ) • ψ' y)) (y : Space) :
    fderiv ℝ ψ y (axialTurn y) - axialTurn (ψ y) = k • ψ' y := by
  have h1 : HasDerivAt (fun θ => ψ (axialRotation θ y)) (fderiv ℝ ψ y (axialTurn y)) 0 := by
    have hd := axialRotationSpec.2.2.2.2.2 0 y
    rw [rot_zero] at hd
    have hf : HasFDerivAt ψ (fderiv ℝ ψ y) (axialRotation 0 y) := by
      rw [rot_zero]
      exact ((hψ.differentiable (by simp)) y).hasFDerivAt
    exact hf.comp_hasDerivAt 0 hd
  have hu : HasDerivAt (fun θ : ℝ => Real.cos (k * θ) • ψ y + Real.sin (k * θ) • ψ' y)
      ((-Real.sin (k * 0) * (k * 1)) • ψ y + (Real.cos (k * 0) * (k * 1)) • ψ' y) 0 := by
    have hk : HasDerivAt (fun θ : ℝ => k * θ) (k * 1) 0 := (hasDerivAt_id' 0).const_mul k
    exact (hk.cos.smul_const (ψ y)).add (hk.sin.smul_const (ψ' y))
  have h2 := FracInternal.Momentum.rot_hasDerivAt axialRotationSpec (θ := fun τ => τ) (hasDerivAt_id' 0) hu
  have heq : (fun τ : ℝ => axialRotation τ (Real.cos (k * τ) • ψ y + Real.sin (k * τ) • ψ' y)) =
      fun θ => ψ (axialRotation θ y) := by
    funext τ
    exact (hcov τ y).symm
  rw [heq] at h2
  have := h1.unique h2
  rw [this]
  simp [rot_zero]

theorem conv_vanish (n : ℕ) {e : Space → Space} {r : ℝ} (he : ∀ w, r < ‖w‖ → e w = 0) {y : Space}
    (hy : r + 1 < ‖y‖) : (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] e) y = 0 := by
  rw [convolution_def]
  have hz : ∀ t, (ContinuousLinearMap.lsmul ℝ ℝ) (kern n t) (e (y - t)) = 0 := by
    intro t
    simp only [ContinuousLinearMap.lsmul_apply]
    by_cases hk : kern n t = 0
    · simp [hk]
    · have ht := kern_support n hk
      have h1 : ‖y‖ - ‖t‖ ≤ ‖y - t‖ := norm_sub_norm_le y t
      rw [he (y - t) (by linarith), smul_zero]
  simp [hz]

theorem conv_smooth (n : ℕ) {e : Space → Space} (he : LocallyIntegrable e volume) :
    ContDiff ℝ ∞ (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] e) :=
  (kern_compact n).contDiff_convolution_left _ (kern_contDiff n) he

theorem kern_nonneg (n : ℕ) (y : Space) : 0 ≤ kern n y :=
  mul_nonneg (inv_nonneg.2 (kernRaw_integral_pos n).le) (kernRaw_nonneg n y)

theorem kern_integral (n : ℕ) : ∫ y, kern n y = 1 := by
  simp only [kern]
  rw [integral_const_mul]
  exact inv_mul_cancel₀ (kernRaw_integral_pos n).ne'

theorem kern_lintegral (n : ℕ) : ∫⁻ t, ‖kern n t‖ₑ = 1 := by
  have hi : Integrable (kern n) := (kern_contDiff n).continuous.integrable_of_hasCompactSupport (kern_compact n)
  calc ∫⁻ t, ‖kern n t‖ₑ = ∫⁻ t, ENNReal.ofReal (kern n t) :=
        lintegral_congr fun t => by rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (kern_nonneg n t)]
    _ = ENNReal.ofReal (∫ t, kern n t) :=
        (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (kern_nonneg n))).symm
    _ = 1 := by rw [kern_integral, ENNReal.ofReal_one]

theorem kern_support_small (n : ℕ) : Function.support (kern n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1)) := by
  intro y hy
  have hr : kernRaw n y ≠ 0 := fun h => hy (by simp [kern, h])
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlt : ((n : ℝ) + 1) * ‖y‖ < 1 := by
    by_contra h
    exact hr (kernRaw_zero n (not_lt.mp h))
  rw [Metric.mem_ball, dist_zero_right, lt_div_iff₀ hn]
  linarith

theorem kern_support_tendsto : Tendsto (fun n => Function.support (kern n)) atTop (𝓝 (0 : Space)).smallSets := by
  rw [tendsto_smallSets_iff]
  intro t ht
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 ht
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop N] with n hn
  refine (kern_support_small n).trans ((Metric.ball_subset_ball ?_).trans hball)
  have h1 : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hn 1
  have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) h1
  linarith

theorem conv_sq_le (n : ℕ) {h : Space → Space} (hh : AEStronglyMeasurable h volume) :
    ∫⁻ x, ‖∫ t, kern n t • h (x - t)‖ₑ ^ 2 ≤ ∫⁻ x, ‖h x‖ₑ ^ 2 := by
  set ρ := kern n
  set F : Space → ℝ≥0∞ := fun z => ‖h z‖ₑ ^ 2 with hFdef
  have hF : AEMeasurable F volume := hh.enorm.pow_const 2
  have hρc : Continuous ρ := (kern_contDiff n).continuous
  have hone : ∫⁻ t, ‖ρ t‖ₑ = 1 := kern_lintegral n
  have hpt : ∀ x : Space, ‖∫ t, ρ t • h (x - t)‖ₑ ^ 2 ≤ (∫⁻ t, ‖ρ t‖ₑ) * ∫⁻ t, ‖ρ t‖ₑ * F (x - t) := by
    intro x
    have h1 : ‖∫ t, ρ t • h (x - t)‖ₑ ≤ ∫⁻ t, ‖ρ t‖ₑ * ‖h (x - t)‖ₑ :=
      (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (by simp only [enorm_smul]))
    have hm : AEMeasurable (fun t => ‖h (x - t)‖ₑ) volume :=
      hh.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume x)
    calc ‖∫ t, ρ t • h (x - t)‖ₑ ^ 2 ≤ (∫⁻ t, ‖ρ t‖ₑ * ‖h (x - t)‖ₑ) ^ 2 := by gcongr
      _ ≤ (∫⁻ t, ‖ρ t‖ₑ) * ∫⁻ t, ‖ρ t‖ₑ * ‖h (x - t)‖ₑ ^ 2 :=
          Coercive.Internal.SmoothApprox.sq_lintegral_mul_le_prod hρc.enorm.aemeasurable hm
  have hK0 : AEMeasurable (fun p : Space × Space => ‖ρ p.2‖ₑ * F (p.1 - p.2)) ((volume : Measure Space).prod volume) :=
    (hρc.enorm.measurable.comp measurable_snd).aemeasurable.mul
      (hF.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant volume volume))
  calc ∫⁻ x, ‖∫ t, ρ t • h (x - t)‖ₑ ^ 2
      ≤ ∫⁻ x, (∫⁻ t, ‖ρ t‖ₑ) * ∫⁻ t, ‖ρ t‖ₑ * F (x - t) := lintegral_mono hpt
    _ = (∫⁻ t, ‖ρ t‖ₑ) * ∫⁻ t, ∫⁻ x, ‖ρ t‖ₑ * F (x - t) := by
        rw [lintegral_const_mul' _ _ (by rw [hone]; exact ENNReal.one_ne_top),
          lintegral_lintegral_swap (f := fun x t => ‖ρ t‖ₑ * F (x - t)) hK0]
    _ = (∫⁻ t, ‖ρ t‖ₑ) * ∫⁻ t, ‖ρ t‖ₑ * ∫⁻ x, F x := by
        congr 1
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_sub_right_eq_self]
    _ = ∫⁻ x, ‖h x‖ₑ ^ 2 := by
        rw [lintegral_mul_const _ hρc.enorm.measurable, ← mul_assoc, hone, one_mul, one_mul]

theorem eLpNorm_two_sq (f : Space → Space) : eLpNorm f 2 volume ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  have := eLpNorm_nnreal_pow_eq_lintegral (μ := (volume : Measure Space)) (f := f) (p := 2) two_ne_zero
  simpa using this

theorem conv_sub_le (n : ℕ) {f g : Space → Space} (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume) :
    eLpNorm (fun x => (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x
      - (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) 2 volume ≤ eLpNorm (f - g) 2 volume := by
  have hcc : Continuous (kern n) := (kern_contDiff n).continuous
  have e : ∀ x, (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x
      - (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x = ∫ t, kern n t • (f - g) (x - t) := by
    intro x
    have I1 : Integrable (fun t => kern n t • f (x - t)) volume :=
      (kern_compact n).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hcc hf x
    have I2 : Integrable (fun t => kern n t • g (x - t)) volume :=
      (kern_compact n).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hcc hg x
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, Pi.sub_apply, smul_sub]
    exact (integral_sub I1 I2).symm
  have hy := conv_sq_le n (hf.aestronglyMeasurable.sub hg.aestronglyMeasurable)
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, eLpNorm_two_sq, eLpNorm_two_sq]
  simp only [e]
  exact hy

theorem conv_sq_tendsto_cont {g : Space → Space} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun n => ∫⁻ x, ‖(kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x‖ₑ ^ 2) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  set S : Set Space := Metric.closedBall (0 : Space) 1 + tsupport g with hSdef
  have hS : IsCompact S := (isCompact_closedBall (0 : Space) 1).add hgc
  have hconv : ∀ n, Continuous (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := fun n =>
    (conv_smooth n hg.locallyIntegrable).continuous
  have hsupp : ∀ n x, x ∉ S → (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x = 0 := by
    intro n x hx
    have h1 : (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x = 0 := by
      by_contra h
      exact hx (Set.add_subset_add (fun t ht => Metric.mem_closedBall.2 (by simpa using kern_support n ht)) (subset_tsupport g)
        (support_convolution_subset _ h))
    have h2 : g x = 0 := by
      by_contra h
      exact hx ⟨0, Metric.mem_closedBall_self (by norm_num), x, subset_tsupport g h, zero_add x⟩
    simp [h1, h2]
  have hbd : ∀ n x, ‖(kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x‖ ≤ M := by
    intro n x
    have hi : Integrable (fun t => kern n t * M) :=
      ((kern_contDiff n).continuous.integrable_of_hasCompactSupport (kern_compact n)).mul_const M
    rw [convolution_def]
    refine (norm_integral_le_of_norm_le hi (Eventually.of_forall fun t => ?_)).trans (le_of_eq ?_)
    · simp only [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (kern_nonneg n t)]
      exact mul_le_mul_of_nonneg_left (hM _) (kern_nonneg n t)
    · rw [integral_mul_const, kern_integral, one_mul]
  have hlim := tendsto_lintegral_of_dominated_convergence (μ := volume)
    (F := fun n x => ‖(kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x‖ₑ ^ 2)
    (f := fun _ => 0) (S.indicator fun _ => ENNReal.ofReal ((M + M) ^ 2))
    (fun n => (((hconv n).sub hg).enorm.measurable.pow_const 2))
    (fun n => Eventually.of_forall fun x => by
      by_cases hx : x ∈ S
      · dsimp only
        rw [Set.indicator_of_mem hx, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le_of_le (hbd n x) (hM x)) 2)
      · simp [hsupp n x hx])
    (by
      rw [lintegral_indicator_const hS.measurableSet]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS.measure_lt_top.ne)
    (Eventually.of_forall fun x => by
      have hc := convolution_tendsto_right (μ := volume) (g := fun _ : ℕ => g) (l := atTop) (x₀ := x)
        (z₀ := g x) (φ := kern) (k := fun _ => x)
        (Eventually.of_forall fun n => kern_nonneg n) (Eventually.of_forall kern_integral) kern_support_tendsto
        (Eventually.of_forall fun _ => hg.aestronglyMeasurable) ((hg.tendsto x).comp tendsto_snd)
        tendsto_const_nhds
      have := ((ENNReal.continuous_pow 2).tendsto _).comp ((hc.sub (tendsto_const_nhds (x := g x))).enorm)
      simpa [Function.comp_def] using this)
  simpa using hlim

theorem kern_approx {f : Space → Space} (hf : MemLp f 2 volume) :
    Tendsto (fun n => eLpNorm (fun x => (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) 2 volume)
      atTop (𝓝 0) := by
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' (by norm_num)).ne'
  obtain ⟨g, hgc, hfg, hgcont, hgm⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hε3
  have hgl : LocallyIntegrable g volume := hgcont.locallyIntegrable
  have hsq := conv_sq_tendsto_cont hgcont hgc
  have hlim : Tendsto (fun n => eLpNorm (fun x => (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x) 2 volume)
      atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero] at hsq ⊢
    intro δ hδ
    filter_upwards [hsq (δ ^ 2) (ENNReal.pow_pos hδ 2)] with n hn
    rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, eLpNorm_two_sq]
    exact hn
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hlim (ε / 3) (pos_iff_ne_zero.2 hε3)] with n hn
  have hcf : Continuous (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) := (conv_smooth n hfl).continuous
  have hcg : Continuous (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := (conv_smooth n hgl).continuous
  have e : (fun x => (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) =
      (fun x => (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
        + (fun x => (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x) + (g - f) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  rw [e]
  calc _ ≤ eLpNorm (fun x => (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x
          - (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) 2 volume +
        eLpNorm (fun x => (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x) 2 volume
          + eLpNorm (g - f) 2 volume := by
        refine (eLpNorm_add_le (((hcf.sub hcg).aestronglyMeasurable).add
          (hcg.sub hgcont).aestronglyMeasurable) (hgm.1.sub hf.1) (by norm_num)).trans ?_
        gcongr
        exact eLpNorm_add_le (hcf.sub hcg).aestronglyMeasurable (hcg.sub hgcont).aestronglyMeasurable (by norm_num)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact (conv_sub_le n hfl hgl).trans hfg
        · rw [eLpNorm_sub_comm]
          exact hfg
    _ = ε := ENNReal.add_thirds ε


end Breakdown.FracInternal.RowTurnPair

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert FracInternal.RowTurnPair

theorem row_smooth_approx {k N : ℕ} (c : FracCellData k N) (T : RowTurnData N) (hT : IsRowTurnData c T) (a : Fin N) :
    ∃ (K : Set Space) (ψ ψ' : ℕ → Space → Space), IsCompact K ∧ T.cellSet (T.cellOf a) ⊆ K ∧
      (∀ n, ContDiff ℝ ∞ (ψ n) ∧ HasCompactSupport (ψ n) ∧ MemLp (ψ n) 2 volume ∧ MemLp (ψ' n) 2 volume ∧
        (∀ y, y ∉ K → ψ n y = 0) ∧ (∀ y, y ∉ K → ψ' n y = 0) ∧
        ∀ y, fderiv ℝ (ψ n) y (axialTurn y) - axialTurn (ψ n y) = (T.modeNum a : ℝ) • ψ' n y) ∧
      Tendsto (fun n => eLpNorm (ψ n - c.row a) 2 volume) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (ψ' n - c.row (T.partner a)) 2 volume) atTop (𝓝 0) := by
  set C := T.cellSet (T.cellOf a) with hC
  obtain ⟨r, hr⟩ := (hT.cell_bounded (T.cellOf a)).subset_closedBall 0
  set e := C.indicator (c.row a) with he
  set e' := C.indicator (c.row (T.partner a)) with he'
  have hCm : MeasurableSet C := hT.cell_measurable _
  have he2 : MemLp e 2 volume := (hT.row_memLp a).indicator hCm
  have he2' : MemLp e' 2 volume := (hT.row_memLp (T.partner a)).indicator hCm
  have hel : LocallyIntegrable e volume := he2.locallyIntegrable (by norm_num)
  have hel' : LocallyIntegrable e' volume := he2'.locallyIntegrable (by norm_num)
  have hout : ∀ g : Space → Space, ∀ w, r < ‖w‖ → C.indicator g w = 0 := by
    intro g w hw
    apply Set.indicator_of_notMem
    intro hwC
    have := hr hwC
    simp at this
    linarith
  have hvan : ∀ n y, y ∉ Metric.closedBall (0 : Space) (r + 1) →
      (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] e) y = 0 ∧
        (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] e') y = 0 := by
    intro n y hy
    have hy' : r + 1 < ‖y‖ := by simpa using hy
    exact ⟨conv_vanish n (hout _) hy', conv_vanish n (hout _) hy'⟩
  have hcov : ∀ᵐ w ∂volume, ∀ θ : ℝ, e (axialRotation θ w) =
      axialRotation θ (Real.cos ((T.modeNum a : ℝ) * θ) • e w + Real.sin ((T.modeNum a : ℝ) * θ) • e' w) := by
    filter_upwards [axis_null] with w hw θ
    rw [rot_eq, rot_eq]
    by_cases hwC : w ∈ C
    · have hrC : turnBy θ w ∈ C := (hT.cell_turn _ θ w).mp hwC
      simp only [he, he', Set.indicator_of_mem hrC, Set.indicator_of_mem hwC]
      exact hT.row_mode a θ w hw
    · have hrC : turnBy θ w ∉ C := fun h => hwC ((hT.cell_turn _ θ w).mpr h)
      simp only [he, he', Set.indicator_of_notMem hrC, Set.indicator_of_notMem hwC, smul_zero, add_zero]
      ext i
      fin_cases i <;> simp [turnBy]
  have hae : ∀ b, T.cellOf b = T.cellOf a → c.row b =ᵐ[volume] C.indicator (c.row b) := by
    intro b hb
    filter_upwards [hT.row_support b] with y hy
    by_cases hyC : y ∈ C
    · rw [Set.indicator_of_mem hyC]
    · rw [Set.indicator_of_notMem hyC]
      by_contra hne
      have h1 := hy hne
      rw [hb] at h1
      exact hyC h1
  refine ⟨Metric.closedBall 0 (r + 1), fun n => kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] e,
    fun n => kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] e', isCompact_closedBall 0 (r + 1),
    hr.trans (Metric.closedBall_subset_closedBall (by linarith)), fun n => ?_, ?_, ?_⟩
  · have hs := conv_smooth n hel
    have hs' := conv_smooth n hel'
    have hc : HasCompactSupport (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] e) :=
      HasCompactSupport.intro (isCompact_closedBall 0 (r + 1)) fun y hy => (hvan n y hy).1
    have hc' : HasCompactSupport (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] e') :=
      HasCompactSupport.intro (isCompact_closedBall 0 (r + 1)) fun y hy => (hvan n y hy).2
    refine ⟨hs, hc, hs.continuous.memLp_of_hasCompactSupport hc, hs'.continuous.memLp_of_hasCompactSupport hc',
      fun y hy => (hvan n y hy).1, fun y hy => (hvan n y hy).2, fun y => ?_⟩
    exact turn_deriv hs _ (conv_turn n hel hel' _ hcov) y
  · have h := kern_approx he2
    refine h.congr fun n => ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [hae a rfl] with y hy
    simp [hy, he]
  · have h := kern_approx he2'
    refine h.congr fun n => ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [hae (T.partner a) (hT.partner_cell a)] with y hy
    simp [hy, he']


theorem turnPair_row {k N : ℕ} (c : FracCellData k N) (T : RowTurnData N) (hT : IsRowTurnData c T)
    {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hv : IsSecondOrderField c.order v G H) (a : Fin N) :
    l2Pair (fun y => G y (axialTurn y) - axialTurn (v y)) (c.row a) =
      -((T.modeNum a : ℝ) * l2Pair v (c.row (T.partner a))) := by
  obtain ⟨K, ψ, ψ', hK, hCK, hψ, h1, h2⟩ := row_smooth_approx c T hT a
  have hvl : LocallyIntegrable v volume := hv.velocity_six.locallyIntegrable (by norm_num)
  have hGl : ∀ j, LocallyIntegrable (fun y => G y (unitVector j)) volume := fun j =>
    (col_memLp hv.measurable_gradient hv.gradient_two j).locallyIntegrable (by norm_num)
  have hseq : ∀ n, l2Pair (fun y => G y (axialTurn y) - axialTurn (v y)) (ψ n) =
      -((T.modeNum a : ℝ) * l2Pair v (ψ' n)) := by
    intro n
    rw [skew_smooth hv.weak_gradient hvl hGl (hψ n).1 (hψ n).2.1]
    congr 1
    unfold l2Pair
    simp_rw [(hψ n).2.2.2.2.2.2, inner_smul_right]
    exact integral_const_mul _ _
  have hsupp : ∀ b, T.cellOf b = T.cellOf a → ∀ᵐ y ∂volume, y ∉ K → c.row b y = 0 := by
    intro b hb
    filter_upwards [hT.row_support b] with y hy hyK
    by_contra hne
    exact hyK (hCK (hb ▸ hy hne))
  have hA : Tendsto (fun n => l2Pair (fun y => G y (axialTurn y) - axialTurn (v y)) (ψ n)) atTop
      (𝓝 (l2Pair (fun y => G y (axialTurn y) - axialTurn (v y)) (c.row a))) :=
    pair_tendsto (indicator_memLp_turnField hK hv) (fun n => (hψ n).2.2.2.2.1) (hsupp a rfl)
      (fun n => (hψ n).2.2.1) (hT.row_memLp a) h1
  have hB : Tendsto (fun n => l2Pair v (ψ' n)) atTop (𝓝 (l2Pair v (c.row (T.partner a)))) :=
    pair_tendsto (indicator_memLp_six hK hv.velocity_six) (fun n => (hψ n).2.2.2.2.2.1)
      (hsupp (T.partner a) (hT.partner_cell a)) (fun n => (hψ n).2.2.2.1) (hT.row_memLp (T.partner a)) h2
  have hC : Tendsto (fun n => l2Pair (fun y => G y (axialTurn y) - axialTurn (v y)) (ψ n)) atTop
      (𝓝 (-((T.modeNum a : ℝ) * l2Pair v (c.row (T.partner a))))) := by
    simp_rw [hseq]
    exact (hB.const_mul _).neg
  exact tendsto_nhds_unique hA hC

end Reduction

end CellCert

end Breakdown
