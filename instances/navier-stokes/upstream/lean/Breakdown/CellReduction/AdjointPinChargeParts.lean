import Breakdown.CellReduction.AdjointAssemblyMeasure
import Breakdown.CertCell.InstancePairByPartsMollify

open scoped ENNReal ContDiff
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace Internal.PinCharge

open CertCell.InstancePair.Internal.ByPartsMollify

theorem coord_inner (x : Space) (j : Fin 3) : x j = inner ℝ (unitVector j) x := by
  simp [unitVector, EuclideanSpace.inner_single_left]

theorem adjoint_entry (A : Space →L[ℝ] Space) (i j : Fin 3) :
    ContinuousLinearMap.adjoint A (unitVector i) j = A (unitVector j) i := by
  rw [coord_inner, ContinuousLinearMap.adjoint_inner_right, real_inner_comm, ← coord_inner]

theorem inner_coords (x y : Space) : inner ℝ x y = ∑ m : Fin 3, x m * y m := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

theorem pairMatrix_adjoint_right (A B : Space →L[ℝ] Space) :
    matInner A (ContinuousLinearMap.adjoint B) =
      ∑ m : Fin 3, ∑ i : Fin 3, A (unitVector i) m * B (unitVector m) i := by
  unfold matInner
  simp only [inner_coords, adjoint_entry]
  exact Finset.sum_comm

theorem pairMatrix_adjoint_left (A B : Space →L[ℝ] Space) :
    matInner (ContinuousLinearMap.adjoint A) B =
      ∑ m : Fin 3, ∑ i : Fin 3, A (unitVector i) m * B (unitVector m) i := by
  unfold matInner
  simp only [inner_coords, adjoint_entry]

theorem weak_coord {v : Space → Space} {G0 : Space → (Space →L[ℝ] Space)} (hv : IsWeakGradient v G0)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (i m : Fin 3) :
    ∫ y, ψ y * G0 y (unitVector i) m = -∫ y, fderiv ℝ ψ y (unitVector i) * v y m := by
  have hw := hv.2.2 ψ ⟨hψ, hψc⟩ i
  have hP : Integrable (fun y => ψ y • G0 y (unitVector i)) volume := by
    have h := (hv.2.1.integrable_smul_left_of_hasCompactSupport hψ.continuous hψc).apply_continuousLinearMap
      (unitVector i)
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp
  have hdc : Continuous (fun y => fderiv ℝ ψ y (unitVector i)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdcs : HasCompactSupport (fun y => fderiv ℝ ψ y (unitVector i)) :=
    (hψc.fderiv ℝ).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector i)) (by simp)
  have hQ : Integrable (fun y => fderiv ℝ ψ y (unitVector i) • v y) volume :=
    hv.1.integrable_smul_left_of_hasCompactSupport hdc hdcs
  have hk := congrArg (EuclideanSpace.proj m : Space →L[ℝ] ℝ) hw
  rw [← (EuclideanSpace.proj m : Space →L[ℝ] ℝ).integral_comp_comm hP, map_neg,
    ← (EuclideanSpace.proj m : Space →L[ℝ] ℝ).integral_comp_comm hQ] at hk
  simpa using hk

theorem fderiv_entry {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (y : Space) (i m j : Fin 3) :
    fderiv ℝ (fun z => fderiv ℝ φ z (unitVector m) i) y (unitVector j) =
      fderiv ℝ (fderiv ℝ φ) y (unitVector j) (unitVector m) i := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) y :=
    ((hφ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) y
  let L : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (ContinuousLinearMap.apply ℝ Space (unitVector m))
  have h := (L.hasFDerivAt.comp y hd.hasFDerivAt).fderiv
  have e : (fun z => fderiv ℝ φ z (unitVector m) i) = L ∘ fderiv ℝ φ := rfl
  rw [e, h]
  rfl

theorem entry_contDiff {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (m i : Fin 3) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ φ z (unitVector m) i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp
    ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)

theorem entry_hasCompactSupport {φ : Space → Space} (hφc : HasCompactSupport φ) (m i : Fin 3) :
    HasCompactSupport (fun z => fderiv ℝ φ z (unitVector m) i) :=
  (hφc.fderiv ℝ).comp_left (g := fun L : Space →L[ℝ] Space => L (unitVector m) i) (by simp)

theorem fderiv_trace {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (y : Space) (m : Fin 3) :
    fderiv ℝ (fun z => ∑ i : Fin 3, fderiv ℝ φ z (unitVector i) i) y (unitVector m) =
      ∑ i : Fin 3, fderiv ℝ (fderiv ℝ φ) y (unitVector m) (unitVector i) i := by
  have hdi : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      DifferentiableAt ℝ (fun z => fderiv ℝ φ z (unitVector i) i) y :=
    fun i _ => ((entry_contDiff hφ i i).differentiable (by simp)) y
  rw [fderiv_fun_sum hdi, ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => fderiv_entry hφ y i i m

theorem transpose_column_smooth {v : Space → Space} {G0 : Space → (Space →L[ℝ] Space)}
    (hv : IsWeakGradient v G0) {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (m : Fin 3) :
    ∑ i : Fin 3, ∫ y, fderiv ℝ φ y (unitVector m) i * G0 y (unitVector i) m =
      ∫ y, (∑ i : Fin 3, fderiv ℝ φ y (unitVector i) i) * G0 y (unitVector m) m := by
  have hd : ContDiff ℝ ∞ (fun z => ∑ i : Fin 3, fderiv ℝ φ z (unitVector i) i) :=
    ContDiff.sum fun i _ => entry_contDiff hφ i i
  have hdc : HasCompactSupport (fun z => ∑ i : Fin 3, fderiv ℝ φ z (unitVector i) i) := by
    exact (hφc.fderiv ℝ).comp_left (g := fun L : Space →L[ℝ] Space => ∑ i : Fin 3, L (unitVector i) i) (by simp)
  rw [weak_coord hv hd hdc m m]
  simp only [fun i => weak_coord hv (entry_contDiff hφ m i) (entry_hasCompactSupport hφc m i) i m]
  rw [Finset.sum_neg_distrib]
  congr 1
  have hint : ∀ i : Fin 3, Integrable (fun y =>
      fderiv ℝ (fun z => fderiv ℝ φ z (unitVector m) i) y (unitVector i) * v y m) volume := by
    intro i
    refine integrable_coord_smul hv.1 ?_ ?_ m
    · exact ((entry_contDiff hφ m i).continuous_fderiv (by simp)).clm_apply continuous_const
    · exact ((entry_hasCompactSupport hφc m i).fderiv ℝ).comp_left
        (g := fun L : Space →L[ℝ] ℝ => L (unitVector i)) (by simp)
  rw [← integral_finsetSum _ fun i _ => hint i]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [← Finset.sum_mul, fderiv_trace hφ y m]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_entry hφ y i m i, (hφ.contDiffAt.isSymmSndFDerivAt (by simp; norm_cast)) (unitVector i) (unitVector m)]

theorem transpose_pairing_smooth {v : Space → Space} {G0 : Space → (Space →L[ℝ] Space)}
    (hv : IsWeakGradient v G0) (hdiv : ∀ᵐ y, ∑ i : Fin 3, G0 y (unitVector i) i = 0)
    {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ y, ∑ m : Fin 3, ∑ i : Fin 3, G0 y (unitVector i) m * fderiv ℝ φ y (unitVector m) i = 0 := by
  have hcol : ∀ i, LocallyIntegrable (fun y => G0 y (unitVector i)) volume :=
    Cert.Internal.ReadingEnergy.locallyIntegrable_column hv.2.1
  have hint : ∀ m i : Fin 3, Integrable (fun y => fderiv ℝ φ y (unitVector m) i * G0 y (unitVector i) m) volume :=
    fun m i => integrable_coord_smul (hcol i) (entry_contDiff hφ m i).continuous (entry_hasCompactSupport hφc m i) m
  have e1 : ∀ y, ∑ m : Fin 3, ∑ i : Fin 3, G0 y (unitVector i) m * fderiv ℝ φ y (unitVector m) i =
      ∑ m : Fin 3, ∑ i : Fin 3, fderiv ℝ φ y (unitVector m) i * G0 y (unitVector i) m := fun y => by
    simp only [mul_comm]
  simp_rw [e1]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun i _ => hint m i]
  simp_rw [integral_finsetSum _ fun i _ => hint _ i]
  simp_rw [transpose_column_smooth hv hφ hφc]
  have hd : Continuous (fun z => ∑ i : Fin 3, fderiv ℝ φ z (unitVector i) i) :=
    (ContDiff.sum fun i _ => entry_contDiff hφ i i).continuous
  have hdc : HasCompactSupport (fun z => ∑ i : Fin 3, fderiv ℝ φ z (unitVector i) i) := by
    exact (hφc.fderiv ℝ).comp_left (g := fun L : Space →L[ℝ] Space => ∑ i : Fin 3, L (unitVector i) i) (by simp)
  rw [← integral_finsetSum _ fun m _ => integrable_coord_smul (hcol m) hd hdc m]
  refine (integral_congr_ae ?_).trans (integral_zero Space ℝ)
  filter_upwards [hdiv] with y hy
  rw [← Finset.mul_sum, hy, mul_zero]

theorem mollified {f : Space → Space} {Df : Space → (Space →L[ℝ] Space)} (hf : IsWeakGradient f Df)
    {R : ℝ} (hR : ∀ y, R < ‖y‖ → f y = 0) (hfL : MemLp f 2 volume)
    (hDL : ∀ j, MemLp (fun y => Df y (unitVector j)) 2 volume) :
    ∃ φ : ℕ → Space → Space, (∀ n, ContDiff ℝ ∞ (φ n)) ∧ (∀ n, HasCompactSupport (φ n)) ∧
      (∀ n, MemLp (φ n) 2 volume) ∧ (∀ n j, MemLp (fun y => fderiv ℝ (φ n) y (unitVector j)) 2 volume) ∧
      Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
      ∀ j, Tendsto (fun n => eLpNorm (fun x => fderiv ℝ (φ n) x (unitVector j) - Df x (unitVector j)) 2 volume)
        atTop (𝓝 0) := by
  obtain ⟨ρ, hρs, hρc, hρ1, hρL⟩ := CellCert.Reduction.rotationMollifier
  have hout : ∀ y, y ∉ Metric.closedBall (0 : Space) R → f y = 0 := fun y hy =>
    hR y (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy)
  have hfcs : HasCompactSupport f := HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) hout
  set φ : ℕ → Space → Space := fun n => convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume with hφdef
  have hφs : ∀ n, ContDiff ℝ ∞ (φ n) := fun n => (hρc n).contDiff_convolution_left _ (hρs n) hf.1
  have hφc : ∀ n, HasCompactSupport (φ n) := fun n => (hρc n).convolution _ hfcs
  have hcol : ∀ j, LocallyIntegrable (fun y => Df y (unitVector j)) volume :=
    Cert.Internal.ReadingEnergy.locallyIntegrable_column hf.2.1
  have hweak : SteadyCert.IsWeakGradientOf f Df := by
    intro ψ hψ j
    rw [hf.2.2 ψ ⟨hψ.1, hψ.2⟩ j, neg_neg]
  have hder : ∀ n y j, fderiv ℝ (φ n) y (unitVector j) =
      convolution (ρ n) (fun z => Df z (unitVector j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume y := by
    intro n y j
    have h := CellCert.Reduction.convGradient (ρ n) (hρs n) (hρc n) (hρ1 n) f Df hf.1 hcol hweak Set.univ
      MeasurableSet.univ y (Set.subset_univ _) j
    simpa only [Set.indicator_univ] using h
  refine ⟨φ, hφs, hφc, fun n => (hφs n).continuous.memLp_of_hasCompactSupport (hφc n), fun n j => ?_,
    hρL f hfL, fun j => ?_⟩
  · exact (((hφs n).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (((hφc n).fderiv ℝ).comp_left (g := fun L : Space →L[ℝ] Space => L (unitVector j)) (by simp))
  · have e : ∀ n, (fun x => fderiv ℝ (φ n) x (unitVector j) - Df x (unitVector j)) =
        fun x => convolution (ρ n) (fun z => Df z (unitVector j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x
          - Df x (unitVector j) :=
      fun n => funext fun x => by rw [hder]
    simp_rw [e]
    exact hρL _ (hDL j)

theorem trace_by_parts {f : Space → Space} {Df : Space → (Space →L[ℝ] Space)}
    {G0 : Space → (Space →L[ℝ] Space)} {H0 : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hf : IsWeakGradient f Df) {R : ℝ} (hR : ∀ y, R < ‖y‖ → f y = 0) (hfL : MemLp f 2 volume)
    (hDL : ∀ j, MemLp (fun y => Df y (unitVector j)) 2 volume)
    (hG : ∀ j, IsWeakGradient (fun y => G0 y (unitVector j)) (fun y => (H0 y).flip (unitVector j)))
    (hGL : ∀ j, MemLp (fun y => G0 y (unitVector j)) 2 volume)
    (hTL : MemLp (fun y => secondDerivTrace (H0 y)) 2 volume) :
    ∫ y, matInner (G0 y) (Df y) = -∫ y, inner ℝ (secondDerivTrace (H0 y)) (f y) := by
  obtain ⟨φ, hφs, hφc, hφL, hdL, hlim0, hlim1⟩ := mollified hf hR hfL hDL
  have ha := tendsto_integral_inner hφL hfL hTL hlim0
  have hb : ∀ j, Tendsto (fun n => ∫ y, inner ℝ (G0 y (unitVector j)) (fderiv ℝ (φ n) y (unitVector j)))
      atTop (𝓝 (∫ y, inner ℝ (G0 y (unitVector j)) (Df y (unitVector j)))) :=
    fun j => tendsto_integral_inner (fun n => hdL n j) (hDL j) (hGL j) (hlim1 j)
  have hsum := (tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun j _ => hb j).neg
  have heq : ∀ n, ∫ y, inner ℝ (secondDerivTrace (H0 y)) (φ n y) =
      -∑ j, ∫ y, inner ℝ (G0 y (unitVector j)) (fderiv ℝ (φ n) y (unitVector j)) :=
    fun n => trace_pairing_test hG (hφs n) (hφc n)
  have hlim := tendsto_nhds_unique ha (hsum.congr fun n => (heq n).symm)
  have hfi : ∀ y, matInner (G0 y) (Df y) = ∑ j, inner ℝ (G0 y (unitVector j)) (Df y (unitVector j)) :=
    fun y => rfl
  simp_rw [hfi]
  rw [integral_finsetSum _ fun j _ => integrable_inner_of_memLp (hGL j) (hDL j), hlim, neg_neg]

theorem adjoint_column_memLp {G0 : Space → (Space →L[ℝ] Space)}
    (hGL : ∀ j, MemLp (fun y => G0 y (unitVector j)) 2 volume) (m : Fin 3) :
    MemLp (fun y => ∑ i : Fin 3, G0 y (unitVector i) m • unitVector i) 2 volume := by
  have h := memLp_finsetSum' (Finset.univ : Finset (Fin 3)) fun i _ => (hGL i).continuousLinearMap_comp
    ((EuclideanSpace.proj m : Space →L[ℝ] ℝ).smulRight (unitVector i))
  refine h.ae_eq (Eventually.of_forall fun y => ?_)
  simp [Finset.sum_apply]

theorem pair_adjoint_column (A B : Space →L[ℝ] Space) :
    ∑ m : Fin 3, inner ℝ (∑ i : Fin 3, A (unitVector i) m • unitVector i) (B (unitVector m)) =
      ∑ m : Fin 3, ∑ i : Fin 3, A (unitVector i) m * B (unitVector m) i := by
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, ← coord_inner]

theorem transpose_pairing_zero {v : Space → Space} {G0 : Space → (Space →L[ℝ] Space)}
    (hv : IsWeakGradient v G0) (hdiv : ∀ᵐ y, ∑ i : Fin 3, G0 y (unitVector i) i = 0)
    (hGL : ∀ j, MemLp (fun y => G0 y (unitVector j)) 2 volume)
    {f : Space → Space} {Df : Space → (Space →L[ℝ] Space)} (hf : IsWeakGradient f Df)
    {R : ℝ} (hR : ∀ y, R < ‖y‖ → f y = 0) (hfL : MemLp f 2 volume)
    (hDL : ∀ j, MemLp (fun y => Df y (unitVector j)) 2 volume) :
    ∫ y, matInner (G0 y) (ContinuousLinearMap.adjoint (Df y)) = 0 := by
  obtain ⟨φ, hφs, hφc, -, hdL, -, hlim1⟩ := mollified hf hR hfL hDL
  have hb : ∀ m, Tendsto (fun n => ∫ y, inner ℝ (∑ i : Fin 3, G0 y (unitVector i) m • unitVector i)
      (fderiv ℝ (φ n) y (unitVector m))) atTop
      (𝓝 (∫ y, inner ℝ (∑ i : Fin 3, G0 y (unitVector i) m • unitVector i) (Df y (unitVector m)))) :=
    fun m => tendsto_integral_inner (fun n => hdL n m) (hDL m) (adjoint_column_memLp hGL m) (hlim1 m)
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun m _ => hb m
  have heq : ∀ n, ∑ m : Fin 3, ∫ y, inner ℝ (∑ i : Fin 3, G0 y (unitVector i) m • unitVector i)
      (fderiv ℝ (φ n) y (unitVector m)) = 0 := by
    intro n
    rw [← integral_finsetSum _ fun m _ => integrable_inner_of_memLp (adjoint_column_memLp hGL m) (hdL n m)]
    simp_rw [pair_adjoint_column]
    exact transpose_pairing_smooth hv hdiv (hφs n) (hφc n)
  have hlim := tendsto_nhds_unique hsum (tendsto_const_nhds.congr fun n => (heq n).symm)
  simp_rw [pairMatrix_adjoint_right, ← pair_adjoint_column]
  rw [integral_finsetSum _ fun m _ => integrable_inner_of_memLp (adjoint_column_memLp hGL m) (hDL m)]
  exact hlim

end Internal.PinCharge

end AdjointDefect

end Breakdown
