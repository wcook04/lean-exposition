import TorusEuler.PaperAppendixB

/-! The real normed-space case of the Bernstein estimate in Appendix B. -/

open MeasureTheory UnitAddTorus
open scoped ContDiff SchwartzMap

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A real linear measurement viewed as a complex-valued torus function. -/
def realFourierScalarization (l : E →L[ℝ] ℝ) (g : C(Labels, E)) : C(Labels, ℂ) :=
  ⟨fun z => (l (g z) : ℂ), Complex.continuous_ofReal.comp (l.continuous.comp g.continuous)⟩

/-- Fourier support of a real normed-space-valued field, measured by its continuous
dual. This definition also applies when the target space is incomplete. -/
def RealNormedTorusFourierBand (R : ℝ) (g : C(Labels, E)) : Prop :=
  ∀ (l : E →L[ℝ] ℝ) (k : Fin 3 → ℤ), R < ‖latticeVector k‖ →
    mFourierCoeff (realFourierScalarization l g) k = 0

private def realFourierMode {R : ℝ} (i : (frequencyBand R) × Bool) : Labels → ℝ :=
  fun z => if i.2 then (mFourier i.1.1 z).re else (mFourier i.1.1 z).im

private def realFourierSpace (R : ℝ) : Submodule ℝ (Labels → ℝ) :=
  Submodule.span ℝ (Set.range (realFourierMode (R := R)))

private instance {R : ℝ} : FiniteDimensional ℝ (realFourierSpace R) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range (realFourierMode (R := R)))

private theorem contDiff_lift_of_realFourierSpace {R : ℝ} {w : Labels → ℝ}
    (hw : w ∈ realFourierSpace R) : ContDiff ℝ ∞ (fun x => w (toUnitTorus x)) := by
  change w ∈ Submodule.span ℝ (Set.range (realFourierMode (R := R))) at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨k, part⟩, rfl⟩ := hw
    cases part
    · exact Complex.imCLM.contDiff.comp (contDiff_fourierMode k)
    · exact Complex.reCLM.contDiff.comp (contDiff_fourierMode k)
  | zero => exact contDiff_const
  | add a b _ _ ha hb => exact ha.add hb
  | smul c a _ ha => exact contDiff_const.smul ha

private theorem scalar_mem_realFourierSpace {R : ℝ} {g : C(Labels, E)}
    (hband : RealNormedTorusFourierBand R g) (l : E →L[ℝ] ℝ) :
    (fun z => l (g z)) ∈ realFourierSpace R := by
  classical
  let a := mFourierCoeff (realFourierScalarization l g)
  have ha := finiteFourierSum_mFourierCoeff_eq_of_band
    (realFourierScalarization l g) R (hband l)
  have hre (k : Fin 3 → ℤ) (hk : k ∈ frequencyBand R) :
      (fun z => (mFourier k z).re) ∈ realFourierSpace R :=
    Submodule.subset_span ⟨(⟨k, hk⟩, true), rfl⟩
  have him (k : Fin 3 → ℤ) (hk : k ∈ frequencyBand R) :
      (fun z => (mFourier k z).im) ∈ realFourierSpace R :=
    Submodule.subset_span ⟨(⟨k, hk⟩, false), rfl⟩
  have hexpand : (fun z => l (g z)) =
      ∑ k ∈ frequencyBand R, ((a k).re • (fun z => (mFourier k z).re) -
        (a k).im • (fun z => (mFourier k z).im)) := by
    funext z
    have hz := (congrArg Complex.re (congrFun ha z)).symm
    simpa only [finiteFourierSum, smul_eq_mul, Complex.re_sum, Complex.mul_re,
      realFourierScalarization, ContinuousMap.coe_mk, Complex.ofReal_re, Finset.sum_apply,
      Pi.sub_apply, Pi.smul_apply, mul_comm, a] using hz
  rw [hexpand]
  exact Submodule.sum_mem _ fun k hk =>
    Submodule.sub_mem _ (Submodule.smul_mem _ _ (hre k hk))
      (Submodule.smul_mem _ _ (him k hk))

private def evaluationOnSubmodule {X : Type*} (W : Submodule ℝ (X → ℝ)) (z : X) :
    Module.Dual ℝ W :=
  (LinearMap.proj z).comp W.subtype

private theorem exists_evaluation_sum {X : Type*} (W : Submodule ℝ (X → ℝ))
    [FiniteDimensional ℝ W] (d : Module.Dual ℝ W) :
    ∃ c : X →₀ ℝ, (c.sum fun z a => a • evaluationOnSubmodule W z) = d := by
  apply Finsupp.mem_span_range_iff_exists_finsupp.mp
  apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
  intro w hw
  have hwz := (Submodule.mem_iInf _).mp hw
  have hwzero : w = 0 := Subtype.ext (funext fun z => (LinearMap.mem_ker.mp (hwz z)))
  rw [hwzero, LinearMap.mem_ker, map_zero]

private theorem eq_sum_evaluated_basis {X : Type*} (W : Submodule ℝ (X → ℝ))
    [FiniteDimensional ℝ W] (g : X → E)
    (h : ∀ l : E →L[ℝ] ℝ, (fun z => l (g z)) ∈ W) :
    ∃ v : Fin (Module.finrank ℝ W) → E, ∀ z,
      g z = ∑ i, ((Module.finBasis ℝ W i : W) : X → ℝ) z • v i := by
  classical
  let b := Module.finBasis ℝ W
  let ev := evaluationOnSubmodule W
  choose c hc using fun i => exists_evaluation_sum W (b.coord i)
  let v (i : Fin (Module.finrank ℝ W)) : E := (c i).sum fun z a => a • g z
  refine ⟨v, fun z => ?_⟩
  change g z = ∑ i, ev z (b i) • v i
  have hscalar (l : E →L[ℝ] ℝ) : l (g z) = l (∑ i, ev z (b i) • v i) := by
    let w : W := ⟨fun x => l (g x), h l⟩
    have hv (i : Fin (Module.finrank ℝ W)) : l (v i) = b.repr w i := by
      have hi := LinearMap.congr_fun (hc i) w
      simpa only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
        map_smul, smul_eq_mul, Module.Basis.coord_apply, evaluationOnSubmodule, LinearMap.comp_apply,
        LinearMap.proj_apply, Submodule.subtype_apply, v, w] using hi
    change ev z w = l (∑ i, ev z (b i) • v i)
    rw [map_sum]
    simp only [map_smul, hv, smul_eq_mul]
    simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using
      (congrArg (ev z) (b.sum_repr w)).symm
  obtain ⟨l, -, hl⟩ := exists_dual_vector'' ℝ (g z - ∑ i, ev z (b i) • v i)
  change l (g z - ∑ i, ev z (b i) • v i) = ‖g z - ∑ i, ev z (b i) • v i‖ at hl
  rw [map_sub, hscalar, sub_self] at hl
  exact sub_eq_zero.mp (norm_eq_zero.mp hl.symm)

/-- Finite Fourier support gives a smooth lift even for an incomplete real target. -/
theorem RealNormedTorusFourierBand.contDiff_lift {R : ℝ} {g : C(Labels, E)}
    (hband : RealNormedTorusFourierBand R g) :
    ContDiff ℝ ∞ (fun x => g (toUnitTorus x)) := by
  obtain ⟨v, h⟩ := eq_sum_evaluated_basis (realFourierSpace R) g
    (scalar_mem_realFourierSpace hband)
  simp only [h]
  apply ContDiff.sum
  intro i _
  exact (contDiff_lift_of_realFourierSpace ((Module.finBasis ℝ
    (realFourierSpace R) i).property)).smul contDiff_const

private theorem norm_realFourierScalarization_le (l : E →L[ℝ] ℝ) (hl : ‖l‖ ≤ 1)
    (g : C(Labels, E)) : ‖realFourierScalarization l g‖ ≤ ‖g‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro z
  change ‖(l (g z) : ℂ)‖ ≤ ‖g‖
  rw [Complex.norm_real]
  exact (l.le_opNorm (g z)).trans
    ((mul_le_of_le_one_left (norm_nonneg _) hl).trans (g.norm_coe_le_norm z))

/-- A directional Bernstein bound with the scalar kernel constant for every real
normed-space target. -/
theorem bernstein_lift_of_real_band
    {ψ : Vec3 → ℝ} (hsupp : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hsmooth : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 0 < Λ)
    (g : C(Labels, E)) (hband : RealNormedTorusFourierBand (4 * Λ) g)
    {j : ℕ} (v : Fin j → Vec3) (x : Vec3) :
    ‖iteratedFDeriv ℝ j (fun z => g (toUnitTorus z)) x v‖ ≤
      (4 * Λ) ^ j * (∫ y, ‖iteratedFDeriv ℝ j
        (cutoffSchwartzKernel hsupp hsmooth : Vec3 → ℂ) y v‖) * ‖g‖ := by
  let f : Vec3 → E := fun z => g (toUnitTorus z)
  let y := iteratedFDeriv ℝ j f x v
  obtain ⟨l, hl, hy⟩ := exists_dual_vector'' ℝ y
  change l y = ‖y‖ at hy
  let L := Complex.ofRealCLM.comp l
  have hd : iteratedFDeriv ℝ j (fun z => realFourierScalarization l g (toUnitTorus z)) x v = L y := by
    change iteratedFDeriv ℝ j (L ∘ f) x v = L y
    rw [L.iteratedFDeriv_comp_left hband.contDiff_lift.contDiffAt (by simp)]
    rfl
  have hn : ‖L y‖ = ‖y‖ := by
    change ‖(l y : ℂ)‖ = ‖y‖
    rw [Complex.norm_real, hy, Real.norm_of_nonneg (norm_nonneg _)]
  calc
    ‖y‖ = ‖iteratedFDeriv ℝ j (fun z => realFourierScalarization l g (toUnitTorus z)) x v‖ := by
      rw [hd, hn]
    _ ≤ (4 * Λ) ^ j * (∫ y, ‖iteratedFDeriv ℝ j
        (cutoffSchwartzKernel hsupp hsmooth : Vec3 → ℂ) y v‖) * ‖realFourierScalarization l g‖ :=
      bernstein_lift_of_band hsupp hsmooth hunit hΛ (realFourierScalarization l g) (hband l) v x
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_realFourierScalarization_le l hl g)
      (mul_nonneg (pow_nonneg (by positivity) _) (integral_nonneg fun _ => norm_nonneg _))

private theorem bernstein_real_finset
    {ψ : Vec3 → ℝ} (hsupp : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hsmooth : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) (m : ℕ) (words : Finset (Fin m → Fin 3)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
      {Λ : ℝ}, 1 ≤ Λ → ∀ g : C(Labels, V), RealNormedTorusFourierBand (4 * Λ) g →
      (∑ β ∈ words, ⨆ x : Vec3,
        ‖iteratedFDeriv ℝ m (fun z => g (toUnitTorus z)) x
          (fun i => EuclideanSpace.single (β i) 1)‖) ≤ C * Λ ^ m * ‖g‖ := by
  let b (β : Fin m → Fin 3) : ℝ :=
    ∫ y, ‖iteratedFDeriv ℝ m (cutoffSchwartzKernel hsupp hsmooth : Vec3 → ℂ) y
      (fun i => EuclideanSpace.single (β i) 1)‖
  refine ⟨(4 : ℝ) ^ m * ∑ β ∈ words, b β, ?_, ?_⟩
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ =>
      integral_nonneg (fun _ => norm_nonneg _))
  · intro V _ _ Λ hΛ g hband
    calc
      _ ≤ ∑ β ∈ words, (4 * Λ) ^ m * b β * ‖g‖ := by
        apply Finset.sum_le_sum
        intro β _
        exact ciSup_le (bernstein_lift_of_real_band hsupp hsmooth hunit
          (zero_lt_one.trans_le hΛ) g hband (fun i => EuclideanSpace.single (β i) 1))
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum, mul_pow]; ring

/-- The Bernstein estimate over all coordinate words, with a constant common to
all real normed spaces. -/
theorem paperLemmaB1_bernstein_real
    {ψ : Vec3 → ℝ} (hsupp : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hsmooth : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
      {Λ : ℝ}, 1 ≤ Λ → ∀ g : C(Labels, V), RealNormedTorusFourierBand (4 * Λ) g →
      (∑ β : Fin m → Fin 3, ⨆ x : Vec3,
        ‖iteratedFDeriv ℝ m (fun z => g (toUnitTorus z)) x
          (fun i => EuclideanSpace.single (β i) 1)‖) ≤ C * Λ ^ m * ‖g‖ :=
  bernstein_real_finset hsupp hsmooth hunit m Finset.univ

/-- The real Bernstein estimate of Lemma B.1 with one nondecreasing word for each
ordinary multi-index of order \(m\). -/
theorem paperLemmaB1_bernstein_real_multiIndex
    {ψ : Vec3 → ℝ} (hsupp : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hsmooth : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
      {Λ : ℝ}, 1 ≤ Λ → ∀ g : C(Labels, V), RealNormedTorusFourierBand (4 * Λ) g →
      (∑ β ∈ Finset.univ.filter (fun β : Fin m → Fin 3 => Monotone β), ⨆ x : Vec3,
        ‖iteratedFDeriv ℝ m (fun z => g (toUnitTorus z)) x
          (fun i => EuclideanSpace.single (β i) 1)‖) ≤ C * Λ ^ m * ‖g‖ := by
  classical
  exact bernstein_real_finset hsupp hsmooth hunit m (Finset.univ.filter Monotone)

end

end TorusEuler
