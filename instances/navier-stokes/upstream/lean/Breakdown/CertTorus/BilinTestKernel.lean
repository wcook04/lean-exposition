import Breakdown.CertTorus.KernelStatementsIntegral

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

open Freq

namespace Internal.KernelPairing

theorem eq_of_inner_test {A B : X}
    (h : ∀ ψ, IsTestField ψ → inner ℝ A (embedX ψ) = inner ℝ B (embedX ψ)) : A = B := by
  have hsub : (testSpan : Set X) ⊆ {x | inner ℝ (A - B) x = 0} := by
    intro x hx
    obtain ⟨ψ, hψ, rfl⟩ := testSpan_holds x hx
    show inner ℝ (A - B) (embedX ψ) = 0
    rw [inner_sub_left, h ψ hψ, sub_self]
  have hcl : IsClosed {x : X | inner ℝ (A - B) x = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hall := hcl.closure_subset_iff.mpr hsub
  rw [testDense_holds.2.closure_eq] at hall
  have h0 : inner ℝ (A - B) (A - B) = 0 := hall (mem_univ _)
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)

theorem isLapOf_heat_embed (hHT : HeatConvTest) {τ : ℝ} (hτ : 0 < τ) {ψ : Space → Space}
    (hψ : IsTestField ψ) :
    IsSspOf (heatX τ (embedX ψ)) (embedX (heatConv τ (negSsp ψ))) := by
  have hχ := Freq.Internal.EmbedNegSsp.isTestField_negSsp hψ
  rw [← (hHT (negSsp ψ) hχ τ hτ).2]
  have e1 : ((heatX τ (embedX (negSsp ψ)) : X) : L2C) = heatL2 τ (embedX (negSsp ψ)) :=
    heat_holds.2.2.2.2.2 τ _
  have e2 : ((heatX τ (embedX ψ) : X) : L2C) = heatL2 τ (embedX ψ) :=
    heat_holds.2.2.2.2.2 τ _
  have a1 := Freq.Internal.Heat.heat_ae fieldOpRealized_holds τ ((embedX (negSsp ψ) : X) : L2C)
  have a2 := Freq.Internal.Heat.heat_ae fieldOpRealized_holds τ ((embedX ψ : X) : L2C)
  have a3 := embedNegSsp_holds ψ hψ
  unfold IsSspOf at a3 ⊢
  rw [e1, e2]
  filter_upwards [a1, a2, a3] with ξ h1 h2 h3
  rw [h1, h2, h3, smul_comm]

theorem phi_ae (hHT : HeatConvTest) {τ : ℝ} (hτ : 0 < τ) {ψ : Space → Space}
    (hψ : IsTestField ψ) :
    (phiX τ (embedX ψ) : Space → Space) =ᵐ[volume] heatConv τ (negSsp ψ) := by
  have hχ := Freq.Internal.EmbedNegSsp.isTestField_negSsp hψ
  have hd := (hHT (negSsp ψ) hχ τ hτ).1
  exact (phi_holds.2 τ hτ (embedX ψ) _ (isLapOf_heat_embed hHT hτ hψ)).trans
    (velocityDecay_holds _ hd)

theorem inner_bilin_test (hHT : HeatConvTest) {τ : ℝ} (hτ : 0 < τ) {φ ψ : Space → Space}
    (hφ : IsTestField φ) (hψ : IsTestField ψ) :
    inner ℝ (bilinX τ (embedX φ) (embedX φ)) (embedX ψ) =
      -∫ x, ∑ j : Fin 3, φ x j * inner ℝ (partialField φ j x) (heatConv τ (negSsp ψ) x) := by
  rw [Freq.Internal.BilinTestFormula.bilinX_spec bilin_holds.1 hτ]
  unfold bilinForm trilinear
  have hv := Freq.Internal.BilinTestFormula.velocity_test velocity_holds hφ
  have hp : ∀ᵐ x ∂volume, ∀ j : Fin 3,
      (partialX j (embedX φ) : Space → Space) x = partialField φ j x := by
    rw [ae_all_iff]
    intro j
    exact partial_holds.1 φ (Freq.Internal.EmbedNegSsp.isDecayField_of_isTestField hφ) j
  have hw := phi_ae hHT hτ hψ
  have e : (∫ x, ∑ j : Fin 3, (velocity (embedX φ) : Space → Space) x j *
      inner ℝ ((partialX j (embedX φ) : Space → Space) x) ((phiX τ (embedX ψ) : Space → Space) x)) =
      ∫ x, ∑ j : Fin 3, φ x j * inner ℝ (partialField φ j x) (heatConv τ (negSsp ψ) x) := by
    apply integral_congr_ae
    filter_upwards [hv, hp, hw] with x a b c
    simp only [a, b, c]
  rw [e]
  ring

theorem coord_fderiv {f : Space → Space} {x : Space} (hf : DifferentiableAt ℝ f x) (j : Fin 3)
    (v : Space) : fderiv ℝ (fun y => f y j) x v = fderiv ℝ f x v j := by
  have h := ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  exact congrArg (fun L => L v) h

theorem inner_eq_sum (u v : Space) : inner ℝ u v = ∑ j : Fin 3, u j * v j := by
  simp [PiLp.inner_apply, mul_comm]

theorem advect_by_parts {φ g : Space → Space} (hφ : IsTestField φ) (hg : ContDiff ℝ ∞ g) :
    ∫ x, ∑ j : Fin 3, φ x j * inner ℝ (partialField φ j x) (g x) =
      -∫ x, ∑ k : Fin 3, φ x k * inner ℝ (fderiv ℝ g x (unitVector k)) (φ x) := by
  have hφs := hφ.1
  have hφc := hφ.2.1
  have hcj : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y => φ y j) := fun j =>
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp hφs
  have hfj : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y => φ y j • g y) := fun j => (hcj j).smul hg
  have hderiv : ∀ (j : Fin 3) (x : Space), fderiv ℝ (fun y => φ y j • g y) x (unitVector j) =
      fderiv ℝ φ x (unitVector j) j • g x + φ x j • fderiv ℝ g x (unitVector j) := by
    intro j x
    have hc : DifferentiableAt ℝ (fun y => φ y j) x := (hcj j).differentiable (by simp) x
    have hd : DifferentiableAt ℝ g x := hg.differentiable (by simp) x
    rw [fderiv_fun_smul hc hd, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, coord_fderiv (hφs.differentiable (by simp) x), add_comm]
  have hibp : ∀ j : Fin 3, ∫ x, inner ℝ (φ x j • g x) (fderiv ℝ φ x (unitVector j)) =
      -∫ x, inner ℝ (fderiv ℝ (fun y => φ y j • g y) x (unitVector j)) (φ x) := by
    intro j
    have hgc : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
      hφc.fderiv_apply (𝕜 := ℝ) _
    have key := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
      (μ := volume) (B := innerSL ℝ) (v := unitVector j) (f := fun y => φ y j • g y) (g := φ)
      (Freq.Internal.PairingByParts.integrable_inner_of_compact
        (Freq.Internal.PairingByParts.dirDeriv_contDiff (hfj j) _).continuous hφs.continuous hφc)
      (Freq.Internal.PairingByParts.integrable_inner_of_compact (hfj j).continuous
        (Freq.Internal.PairingByParts.dirDeriv_contDiff hφs _).continuous hgc)
      (Freq.Internal.PairingByParts.integrable_inner_of_compact (hfj j).continuous
        hφs.continuous hφc)
      (fun x _ => ((hfj j).differentiable (by simp)) x)
      (fun x _ => (hφs.differentiable (by simp)) x)
    exact key
  have hint1 : ∀ j : Fin 3,
      Integrable (fun x => inner ℝ (φ x j • g x) (fderiv ℝ φ x (unitVector j))) := fun j =>
    Freq.Internal.PairingByParts.integrable_inner_of_compact (hfj j).continuous
      (Freq.Internal.PairingByParts.dirDeriv_contDiff hφs _).continuous
      (hφc.fderiv_apply (𝕜 := ℝ) _)
  have hint2 : ∀ j : Fin 3,
      Integrable (fun x => inner ℝ (fderiv ℝ (fun y => φ y j • g y) x (unitVector j)) (φ x)) :=
    fun j => Freq.Internal.PairingByParts.integrable_inner_of_compact
      (Freq.Internal.PairingByParts.dirDeriv_contDiff (hfj j) _).continuous hφs.continuous hφc
  have e1 : (fun x => ∑ j : Fin 3, φ x j * inner ℝ (partialField φ j x) (g x)) =
      fun x => ∑ j : Fin 3, inner ℝ (φ x j • g x) (fderiv ℝ φ x (unitVector j)) := by
    funext x
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [real_inner_smul_left, real_inner_comm]
    rfl
  rw [e1, integral_finsetSum _ (fun j _ => hint1 j)]
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun j _ => hint2 j)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hdiv := hφ.2.2 x
  unfold divergenceAt at hdiv
  simp only [hderiv, inner_add_left, real_inner_smul_left, Finset.sum_add_distrib,
    ← Finset.sum_mul, hdiv, zero_mul, zero_add]

theorem inner_unitVector (i : Fin 3) (v : Space) : inner ℝ (unitVector i) v = v i := by
  simp [unitVector, EuclideanSpace.inner_single_left]

theorem kernel_pair (hKC : KernelContraction) (hOdd : LerayKernelOdd) (hB : LerayKernelBound)
    (hM : LerayKernelMeasurable) {τ : ℝ} (hτ : 0 < τ) {φ χ : Space → Space}
    (hφ : IsTestField φ) (hχ : IsTestField χ) :
    ∫ y, inner ℝ (kernelConv τ (tensorField φ φ) y) (χ y) =
      -∫ z, ∑ k : Fin 3, φ z k * inner ℝ (fderiv ℝ (heatConv τ χ) z (unitVector k)) (φ z) := by
  obtain ⟨C, hC⟩ := hB
  have hMb : ∀ (i j k : Fin 3) (x : Space), |lerayKernel i j k τ x| ≤ |C| / Real.sqrt τ ^ 4 := by
    intro i j k x
    have hs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
    have hle : Real.sqrt τ ^ 4 ≤ (‖x‖ + Real.sqrt τ) ^ 4 :=
      pow_le_pow_left₀ hs.le (le_add_of_nonneg_left (norm_nonneg x)) 4
    calc |lerayKernel i j k τ x| ≤ C / (‖x‖ + Real.sqrt τ) ^ 4 := hC i j k τ x hτ
      _ ≤ |C| / (‖x‖ + Real.sqrt τ) ^ 4 :=
        div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| / Real.sqrt τ ^ 4 := div_le_div_of_nonneg_left (abs_nonneg C) (by positivity) hle
  have hKm : ∀ i j k : Fin 3, Measurable (lerayKernel i j k τ) := fun i j k =>
    (hM i j k).comp measurable_prodMk_left
  have hcont : ∀ {f : Space → Space}, Continuous f → ∀ j : Fin 3, Continuous (fun z => f z j) :=
    fun hf j => (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp hf
  have hcs : ∀ {f : Space → Space}, HasCompactSupport f → ∀ j : Fin 3,
      HasCompactSupport (fun z => f z j) :=
    fun hf j => hf.comp_left (g := fun v : Space => v j) (by simp)
  have hχi : ∀ i : Fin 3, Integrable (fun y => χ y i) := fun i =>
    (hcont hχ.1.continuous i).integrable_of_hasCompactSupport (hcs hχ.2.1 i)
  have hΦ : ∀ j k : Fin 3, Integrable (fun z => φ z j * φ z k) := fun j k =>
    ((hcont hφ.1.continuous j).mul (hcont hφ.1.continuous k)).integrable_of_hasCompactSupport
      (hcs hφ.2.1 j).mul_right
  have hKy : ∀ (i j k : Fin 3) (a : Space) (f : Space → ℝ), Integrable f →
      Integrable (fun z => lerayKernel i j k τ (a - z) * f z) := fun i j k a f hf =>
    hf.bdd_mul (f := fun z => lerayKernel i j k τ (a - z))
      ((hKm i j k).comp (continuous_const.sub continuous_id).measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hMb i j k _)
  have hKz : ∀ (i j k : Fin 3) (a : Space) (f : Space → ℝ), Integrable f →
      Integrable (fun y => lerayKernel i j k τ (y - a) * f y) := fun i j k a f hf =>
    hf.bdd_mul (f := fun y => lerayKernel i j k τ (y - a))
      ((hKm i j k).comp (continuous_id.sub continuous_const).measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hMb i j k _)
  let F : Space → Space → ℝ := fun y z => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      lerayKernel i j k τ (y - z) * (χ y i * (φ z j * φ z k))
  have hF : Integrable (Function.uncurry F) (volume.prod volume) := by
    show Integrable (fun p : Space × Space => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      lerayKernel i j k τ (p.1 - p.2) * (χ p.1 i * (φ p.2 j * φ p.2 k))) (volume.prod volume)
    refine integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      integrable_finsetSum _ (fun k _ => ?_)))
    exact ((hχi i).mul_prod (hΦ j k)).bdd_mul
      (f := fun p : Space × Space => lerayKernel i j k τ (p.1 - p.2))
      ((hKm i j k).comp (continuous_fst.sub continuous_snd).measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hMb i j k _)
  have step1 : ∀ y, inner ℝ (kernelConv τ (tensorField φ φ) y) (χ y) = ∫ z, F y z := by
    intro y
    have hI : ∀ i : Fin 3, Integrable (fun z => (∑ j : Fin 3, ∑ k : Fin 3,
        lerayKernel i j k τ (y - z) * tensorField φ φ z j k) * χ y i) := fun i =>
      (integrable_finsetSum _ (fun j _ => integrable_finsetSum _
        (fun k _ => hKy i j k y _ (hΦ j k)))).mul_const _
    unfold kernelConv
    rw [sum_inner]
    simp only [real_inner_smul_left, inner_unitVector]
    rw [Finset.sum_congr rfl (fun i _ => (integral_mul_const (χ y i) _).symm),
      ← integral_finsetSum _ (fun i _ => hI i)]
    congr 1
    funext z
    simp only [F, tensorField, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun k _ => by ring)))
  have hcontr : ∀ (j k : Fin 3) (z : Space),
      ∫ y, ∑ i : Fin 3, lerayKernel i j k τ (y - z) * χ y i =
        -fderiv ℝ (heatConv τ χ) z (unitVector k) j := by
    intro j k z
    rw [← hKC τ hτ χ hχ j k z, ← integral_neg]
    congr 1
    funext y
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← neg_sub z y, hOdd i j k τ (z - y)]
    ring
  have step3 : ∀ z, ∫ y, F y z =
      -∑ k : Fin 3, φ z k * inner ℝ (fderiv ℝ (heatConv τ χ) z (unitVector k)) (φ z) := by
    intro z
    have hre : (fun y => F y z) = fun y => ∑ j : Fin 3, ∑ k : Fin 3, (φ z j * φ z k) *
        ∑ i : Fin 3, lerayKernel i j k τ (y - z) * χ y i := by
      funext y
      simp only [F, Fin.sum_univ_three]
      ring
    have hint : ∀ j k : Fin 3,
        Integrable (fun y => ∑ i : Fin 3, lerayKernel i j k τ (y - z) * χ y i) :=
      fun j k => integrable_finsetSum _ (fun i _ => hKz i j k z _ (hχi i))
    rw [hre, integral_finsetSum _ (fun j _ => integrable_finsetSum _
      (fun k _ => (hint j k).const_mul _))]
    rw [Finset.sum_congr rfl (fun j _ => integral_finsetSum _ (fun k _ => (hint j k).const_mul _))]
    simp only [integral_const_mul, hcontr]
    simp only [inner_eq_sum, Fin.sum_univ_three]
    ring
  calc ∫ y, inner ℝ (kernelConv τ (tensorField φ φ) y) (χ y) = ∫ y, ∫ z, F y z := by
        congr 1
        funext y
        exact step1 y
    _ = ∫ z, ∫ y, F y z := integral_integral_swap hF
    _ = ∫ z, -∑ k : Fin 3, φ z k * inner ℝ (fderiv ℝ (heatConv τ χ) z (unitVector k)) (φ z) := by
        congr 1
        funext z
        exact step3 z
    _ = _ := integral_neg _

end Internal.KernelPairing

open Internal.KernelPairing in
theorem bilinTestKernel_of_kernel :
    HeatConvTest → KernelContraction → KernelConvTestDecay → LerayKernelOdd →
      LerayKernelBound → LerayKernelMeasurable → BilinTestKernel := by
  intro hHT hKC hTD hOdd hB hM τ hτ φ hφ
  apply eq_of_inner_test
  intro ψ hψ
  have hχ := Freq.Internal.EmbedNegSsp.isTestField_negSsp hψ
  have hgd := (hHT (negSsp ψ) hχ τ hτ).1
  have hfd := hTD τ hτ φ hφ
  rw [inner_bilin_test hHT hτ hφ hψ, advect_by_parts hφ hgd.1,
    pairingEmbed embedNormLinear_holds.1 embedNormLinear_holds.2 _ _ hfd
      (Freq.Internal.EmbedNegSsp.isDecayField_of_isTestField hψ),
    pairingByParts _ _ hfd hψ]
  unfold fieldPairing
  simp only [inner_neg_left, integral_neg]
  rw [kernel_pair hKC hOdd hB hM hτ hφ hχ]

end Breakdown.FarField
