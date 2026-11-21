import TorusEuler.TruncatedParentAdmissibility
import TorusEuler.TruncationFourierCommutation
import TorusEuler.PhysicalCutoffEstimates
import TorusEuler.PeriodicLerayHolderLift

/-! The Fourier cutoff bounds and commutations of Lemma B.1. -/

open MeasureTheory Set UnitAddTorus
open scoped ContDiff SchwartzMap

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)

section ComplexCutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {ψ : Vec3 → ℝ} (hsupp : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hsmooth : ContDiff ℝ ∞ ψ)
variable {Λ : ℝ} (hΛ : 0 < Λ)

local notation "K" => cutoffSchwartzKernel hsupp hsmooth

include hΛ in
/-- The cutoff is bounded on the sup norm by the scale-independent kernel mass. -/
theorem paperLemmaB1_cutoff_sup (g : C(Labels, E)) :
    spatialSupNorm (fun x => smoothFourierCutoff ψ Λ g (toUnitTorus x)) ≤
      (∫ y, ‖(K : Vec3 → ℂ) y‖) * ‖g‖ := by
  apply ciSup_le
  intro x
  change ‖smoothFourierCutoff ψ Λ g (toUnitTorus x)‖ ≤ _
  rw [← liftConvolution_cutoffSchwartzKernel hsupp hsmooth hΛ g,
    ← integral_norm_scaledLiftKernel hΛ]
  exact norm_liftConvolution_le (integrable_scaledLiftKernel hΛ (K).integrable)
    (fun y => g.norm_coe_le_norm (toUnitTorus y)) x

include hΛ in
/-- The same kernel mass controls the full spatial half-Hölder norm. -/
theorem paperLemmaB1_cutoff_holder (g : C(Labels, E))
    (hg : SpatialHolderHalf 0 (fun x => g (toUnitTorus x))) :
    let f := fun x => g (toUnitTorus x)
    let Sf := fun x => smoothFourierCutoff ψ Λ g (toUnitTorus x)
    SpatialHolderHalf 0 Sf ∧
      spatialHolderHalfNorm 0 Sf ≤ (∫ y, ‖(K : Vec3 → ℂ) y‖) * spatialHolderHalfNorm 0 f := by
  let f := fun x => g (toUnitTorus x)
  let S := fun x => smoothFourierCutoff ψ Λ g (toUnitTorus x)
  let C := ∫ y, ‖(K : Vec3 → ℂ) y‖
  obtain ⟨hf, hBound, hHolder⟩ := (spatialHolderHalf_zero_iff f).1 hg
  have hL : Integrable (scaledLiftKernel Λ K) := integrable_scaledLiftKernel hΛ (K).integrable
  have hrep (x : Vec3) : S x = liftConvolution (scaledLiftKernel Λ K) f x :=
    (liftConvolution_cutoffSchwartzKernel hsupp hsmooth hΛ g x).symm
  have hSup (x : Vec3) : ‖S x‖ ≤ C * spatialSupNorm f := by
    rw [hrep, show C = ∫ y, ‖(K : Vec3 → ℂ) y‖ from rfl, ← integral_norm_scaledLiftKernel hΛ]
    exact norm_liftConvolution_le hL (norm_le_spatialSupNorm hBound) x
  have hInc (x v : Vec3) : ‖S (x + v) - S x‖ ≤ C * spatialHolderHalfSeminorm f * Real.sqrt ‖v‖ := by
    rw [hrep, hrep, show C = ∫ y, ‖(K : Vec3 → ℂ) y‖ from rfl,
      ← integral_norm_scaledLiftKernel hΛ, mul_assoc]
    exact norm_liftConvolution_increment_le hL hf (norm_le_spatialSupNorm hBound)
      x v (fun z => norm_increment_le_spatialHolderHalfSeminorm hHolder z v)
  have hQ (p : Vec3 × Vec3) : spatialHolderHalfQuotient S p ≤ C * spatialHolderHalfSeminorm f := by
    rcases p with ⟨x, v⟩
    by_cases hv : v = 0
    · subst v
      have h : 0 ≤ spatialHolderHalfSeminorm f := by
        have h0 := le_ciSup hHolder ((0 : Vec3), (0 : Vec3))
        change spatialHolderHalfQuotient f ((0 : Vec3), (0 : Vec3)) ≤ spatialHolderHalfSeminorm f at h0
        rw [show spatialHolderHalfQuotient f ((0 : Vec3), (0 : Vec3)) = 0 by
          simp [spatialHolderHalfQuotient]] at h0
        exact h0
      simpa [spatialHolderHalfQuotient] using mul_nonneg (integral_nonneg fun _ => norm_nonneg _) h
    · exact (div_le_iff₀ (Real.sqrt_pos_of_pos (norm_pos_iff.mpr hv))).2 (hInc x v)
  refine ⟨(spatialHolderHalf_zero_iff S).2
    ⟨(contDiff_lift_smoothFourierCutoff ψ Λ g).continuous,
      ⟨C * spatialSupNorm f, ?_⟩, ⟨C * spatialHolderHalfSeminorm f, ?_⟩⟩, ?_⟩
  · rintro y ⟨x, hx⟩
    simpa only [hx] using hSup x
  · rintro y ⟨p, hp⟩
    rw [← hp]
    exact hQ p
  ·
    change spatialHolderHalfNorm 0 S ≤ C * spatialHolderHalfNorm 0 f
    rw [spatialHolderHalfNorm_zero_eq, spatialHolderHalfNorm_zero_eq, mul_add]
    exact add_le_add (ciSup_le hSup) (ciSup_le hQ)

include hsupp hsmooth hΛ in
/-- The spatial derivatives commute with the actual convolution cutoff. -/
theorem paperLemmaB1_cutoff_derivative (g : C(Labels, E)) {m : ℕ}
    (hg : SpatialHolderHalf m (fun x => g (toUnitTorus x))) :
    iteratedFDeriv ℝ m (fun x => smoothFourierCutoff ψ Λ g (toUnitTorus x)) =
      liftConvolution (scaledLiftKernel Λ K) (iteratedFDeriv ℝ m (fun x => g (toUnitTorus x))) := by
  have hrep : (fun x => smoothFourierCutoff ψ Λ g (toUnitTorus x)) =
      liftConvolution (scaledLiftKernel Λ K) (fun x => g (toUnitTorus x)) :=
    funext fun x => (liftConvolution_cutoffSchwartzKernel hsupp hsmooth hΛ g x).symm
  rw [hrep]
  exact iteratedFDeriv_liftConvolution_eq_liftConvolution_iteratedFDeriv
    (integrable_scaledLiftKernel hΛ (K).integrable) hg.1
    (fun i => spatialSupNorm (iteratedFDeriv ℝ i (fun x => g (toUnitTorus x))))
    (fun i hi x => norm_le_spatialSupNorm (hg.2 i hi).1 x)

include hsupp hsmooth hΛ in
/-- The spatial cutoff commutes with all continuous derivatives, at
every finite order and with no Hölder assumption on the last derivative. -/
theorem paperLemmaB1_cutoff_commutes_contDiff (g : C(Labels, E)) {m : ℕ}
    (hg : ContDiff ℝ m (fun x => g (toUnitTorus x))) :
    iteratedFDeriv ℝ m (fun x => smoothFourierCutoff ψ Λ g (toUnitTorus x)) =
      liftConvolution (scaledLiftKernel Λ K) (iteratedFDeriv ℝ m (fun x => g (toUnitTorus x))) := by
  let f := fun x => g (toUnitTorus x)
  have hRep : (fun x => smoothFourierCutoff ψ Λ g (toUnitTorus x)) =
      liftConvolution (scaledLiftKernel Λ K) f :=
    funext fun x => (liftConvolution_cutoffSchwartzKernel hsupp hsmooth hΛ g x).symm
  have hPer : SpatiallyPeriodic f := by
    intro n x
    exact congrArg g ((toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩)
  have hBounds (j : ℕ) (hj : j ≤ m) :
      BddAbove (range fun x => ‖iteratedFDeriv ℝ j f x‖) := by
    obtain ⟨M, hM⟩ := isCompact_centeredCell.exists_bound_of_continuousOn
      (hg.continuous_iteratedFDeriv (by exact_mod_cast hj)).continuousOn
    refine ⟨M, ?_⟩
    rintro _ ⟨x, rfl⟩
    obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell x
    have hEq : iteratedFDeriv ℝ j f x = iteratedFDeriv ℝ j f (x - latticeVector n) := by
      calc
        _ = iteratedFDeriv ℝ j f (x - latticeVector n + latticeVector n) := by rw [sub_add_cancel]
        _ = iteratedFDeriv ℝ j (fun y => f (y + latticeVector n)) (x - latticeVector n) :=
          (iteratedFDeriv_comp_add_right j (latticeVector n) (x - latticeVector n)).symm
        _ = _ := by rw [funext (hPer n)]
    exact (congrArg norm hEq).le.trans (hM _ hn)
  rw [hRep]
  exact iteratedFDeriv_liftConvolution_eq_liftConvolution_iteratedFDeriv
    (integrable_scaledLiftKernel hΛ (K).integrable) hg
    (fun j => spatialSupNorm (iteratedFDeriv ℝ j f))
    (fun j hj x => norm_le_spatialSupNorm (hBounds j hj) x)

/-- The cutoff support and both signs of spatial parity in the complex realization. -/
theorem paperLemmaB1_cutoff_support_parity (g : C(Labels, E))
    (heven : Function.Even ψ) :
    (∀ k ∉ frequencyBand (2 * Λ), mFourierCoeff (smoothFourierCutoff ψ Λ g) k = 0) ∧
      ∀ c : ℝ, (∀ x, g (-x) = c • g x) →
        ∀ z, smoothFourierCutoff ψ Λ g (-z) = c • smoothFourierCutoff ψ Λ g z := by
  exact ⟨fun k hk => mFourierCoeff_smoothFourierCutoff_eq_zero ψ Λ g
      (lt_of_not_ge fun h => hk (mem_frequencyBand _ _ |>.2 h)),
    fun c hc => smoothFourierCutoff_neg_arg heven Λ c hc⟩

include hsupp hsmooth in
/-- Bernstein's bound for the coordinate sums, with one fixed constant at each order. -/
theorem paperLemmaB1_bernstein (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ : ℝ}, 1 ≤ Λ → ∀ g : C(Labels, E),
      (∀ k, 4 * Λ < ‖latticeVector k‖ → mFourierCoeff g k = 0) →
      (∑ β : Fin m → Fin 3, ⨆ x : Vec3,
        ‖iteratedFDeriv ℝ m (fun z => g (toUnitTorus z)) x
          (fun i => EuclideanSpace.single (β i) 1)‖) ≤
        C * Λ ^ m * ‖g‖ := by
  refine ⟨(4 : ℝ) ^ m * ∑ β : Fin m → Fin 3, ∫ y,
    ‖iteratedFDeriv ℝ m (K : Vec3 → ℂ) y (fun i => EuclideanSpace.single (β i) 1)‖, ?_, ?_⟩
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _)
  · intro Λ hΛ g hband
    exact bernstein_lift_coordinate_sum_of_band hsupp hsmooth hunit (zero_lt_one.trans_le hΛ) g hband m

include hsupp hsmooth in
/-- The full range of cutoff tail orders in Lemma B.1, including equal
regularity orders and the top half-Hölder seminorm. -/
theorem paperLemmaB1_cutoff_tail (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ : ℝ}, 1 ≤ Λ → ∀ (g : C(Labels, E)) {s : ℕ}, s ≤ M →
      SpatialHolderHalf M (fun x => g (toUnitTorus x)) →
      let f : Vec3 → E := fun x => g (toUnitTorus x)
      let R : Vec3 → E := fun x => f x - smoothFourierCutoff ψ Λ g (toUnitTorus x)
      SpatialHolderHalf s R ∧ spatialHolderHalfNorm s R ≤ C * Λ ^ ((s : ℤ) - M) * spatialHolderHalfNorm M f := by
  refine ⟨cutoffHolderTailUniformConstant K M, ?_, ?_⟩
  · unfold cutoffHolderTailUniformConstant cutoffKernelAbsoluteMoment
    positivity
  · intro Λ hΛ g s hs hg
    exact spatialHolderHalfNorm_cutoffTail hsupp hsmooth hunit (zero_lt_one.trans_le hΛ) g hs hg

end ComplexCutoff

/-- The actual real cutoff preserves either sign of spatial parity. -/
theorem paperLemmaB1_realCutoff_parity {ψ : Vec3 → ℝ} (heven : Function.Even ψ)
    (Λ c : ℝ) (g : C(Labels, Vec3)) (hg : ∀ z, g (-z) = c • g z) :
    ∀ z, realVectorFourierCutoff ψ Λ g (-z) = c • realVectorFourierCutoff ψ Λ g z := by
  have hc (z : Labels) : endpointComplexifyContinuous g (-z) = c • endpointComplexifyContinuous g z := by
    change periodicComplexifyVector (g (-z)) = c • periodicComplexifyVector (g z)
    rw [hg, map_smul]
  intro z
  change periodicRealPartVector (smoothFourierCutoff ψ Λ (endpointComplexifyContinuous g) (-z)) =
    c • periodicRealPartVector (smoothFourierCutoff ψ Λ (endpointComplexifyContinuous g) z)
  rw [smoothFourierCutoff_neg_arg heven Λ c hc, map_smul]

/-- The cutoff on real velocities has the same supremum bound as its
complex realization. -/
theorem paperLemmaB1_realCutoff_sup {ψ : Vec3 → ℝ}
    (hsupp : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hsmooth : ContDiff ℝ ∞ ψ) {Λ : ℝ} (hΛ : 0 < Λ)
    (g : C(Labels, Vec3)) :
    spatialSupNorm (fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)) ≤
      (∫ y, ‖(cutoffSchwartzKernel hsupp hsmooth : Vec3 → ℂ) y‖) * ‖g‖ := by
  apply ciSup_le
  intro x
  have h := norm_iteratedFDeriv_realVectorFourierCutoff_le hsupp hsmooth hΛ g
    (fun y => g.norm_coe_le_norm (toUnitTorus y)) (fun i : Fin 0 => Fin.elim0 i) x
  simpa only [iteratedFDeriv_zero_apply, pow_zero, one_mul] using h

/-- The physical real cutoff preserves oddness and divergence-freeness
and is supported on the exact band of radius `2Λ`. -/
theorem paperLemmaB1_realCutoff_admissible {ψ : Vec3 → ℝ} (heven : Function.Even ψ)
    (Λ : ℝ) (g : C(Labels, Vec3)) (hg : ContDiff ℝ ∞ (fun x => g (toUnitTorus x))) :
    let u := fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)
    (Function.Odd (fun x => g (toUnitTorus x)) → Function.Odd u) ∧
      ((∀ x, divergence (fun y => g (toUnitTorus y)) x = 0) → ∀ x, divergence u x = 0) ∧
      ∀ k ∉ frequencyBand (2 * Λ),
        mFourierCoeff (fun z => periodicComplexifyVector (realVectorFourierCutoff ψ Λ g z)) k = 0 := by
  exact ⟨odd_lift_realVectorFourierCutoff heven Λ g,
    divergence_free_lift_realVectorFourierCutoff heven Λ g hg, fun k hk => by
      rw [mFourierCoeff_realVectorFourierCutoff_of_even heven, ite_eq_right hk]⟩

end

end TorusEuler
