import TorusEuler.EndpointConcreteProjection
import TorusEuler.ParentResidualEstimates
import TorusEuler.ResidualGradient

/-! The parent gradient and time-gradient bounds in (7.5). -/

open ContinuousLinearMap Filter MeasureTheory Set UnitAddTorus
open scoped ContDiff Topology

namespace TorusEuler

noncomputable section

set_option maxHeartbeats 900000

local notation "Labels" => UnitAddTorus (Fin 3)
/-- Vanishing of the complexified Fourier coefficients outside a Euclidean band. -/
def RealTorusFourierBand (D : ℝ) (f : C(Labels, Vec3)) : Prop :=
  ∀ k, D < ‖latticeVector k‖ → mFourierCoeff (fun z => periodicComplexifyVector (f z)) k = 0

/-- Spatial and temporal derivatives commute for a jointly smooth velocity on
a closed time slab, including at its endpoints. -/
theorem hasFDerivAt_slabVelocityTimeDerivative {u : Velocity} {T t : ℝ}
    (hT : 0 < T) (ht : t ∈ Icc 0 T)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (x : Vec3) :
    HasFDerivAt (fun y => derivWithin (fun r => u r y) (Icc 0 T) t)
      (derivWithin (fun r => fderiv ℝ (u r) x) (Icc 0 T) t) x := by
  let I := Icc (0 : ℝ) T
  let S := I ×ˢ (univ : Set Vec3)
  let dU := fderivWithin ℝ (Function.uncurry u) S
  let d₂U := fderivWithin ℝ dU S (t, x)
  let et : ℝ × Vec3 := (1, 0)
  let ex := inr ℝ ℝ Vec3
  let timePart := ContinuousLinearMap.apply ℝ Vec3 et
  let spacePart := (compL ℝ Vec3 (ℝ × Vec3) Vec3).flip ex
  have hI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hT
  have hS : UniqueDiffOn ℝ S := hI.prod uniqueDiffOn_univ
  have hpt : (t, x) ∈ S := ⟨ht, mem_univ _⟩
  have hAccum : (t, x) ∈ closure (interior S) := by
    rw [show S = I ×ˢ (univ : Set Vec3) from rfl, interior_prod_eq, closure_prod_eq,
      interior_univ, closure_univ, show I = Icc 0 T from rfl, closure_interior_Icc hT.ne]
    exact hpt
  have hSym : ∀ v w, d₂U v w = d₂U w v :=
    (hu _ hpt).isSymmSndFDerivWithinAt (by rw [minSmoothness_of_isRCLikeNormedField]) hS hAccum hpt
  have hdu (r : ℝ) (hr : r ∈ I) (y : Vec3) :
      HasFDerivWithinAt (Function.uncurry u) (dU (r, y)) S (r, y) :=
    (hu.differentiableOn (by norm_num) _ (mem_prod.mpr ⟨hr, mem_univ y⟩)).hasFDerivWithinAt
  have h₂u : HasFDerivWithinAt dU d₂U S (t, x) :=
    ((hu.fderivWithin hS (m := 1) (by norm_num)).differentiableOn (by norm_num) _ hpt).hasFDerivWithinAt
  have hspace (r : ℝ) (hr : r ∈ I) :
      HasFDerivAt (u r) (spacePart (dU (r, x))) x :=
    (hdu r hr x).comp_hasFDerivAt x (hasFDerivAt_prodMk_right (𝕜 := ℝ) r x)
      (Eventually.of_forall fun z => ⟨hr, mem_univ z⟩)
  have htime (y : Vec3) : derivWithin (fun r => u r y) I t = timePart (dU (t, y)) := by
    have h := (hdu t ht y).comp_hasDerivWithinAt t
      ((hasDerivWithinAt_id t I).prodMk (hasDerivWithinAt_const t I y))
      (fun _ hr => mem_prod.mpr ⟨hr, mem_univ y⟩)
    exact h.derivWithin (hI t ht)
  have h₂space := h₂u.comp_hasFDerivAt x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
    (Eventually.of_forall fun y => ⟨ht, mem_univ y⟩)
  have hdxTime : HasFDerivAt (fun y => derivWithin (fun r => u r y) I t)
      (timePart.comp (d₂U.comp ex)) x :=
    (timePart.hasFDerivAt.comp x h₂space).congr_of_eventuallyEq (Eventually.of_forall htime)
  have h₂time := h₂u.comp_hasDerivWithinAt t
    ((hasDerivWithinAt_id t I).prodMk (hasDerivWithinAt_const t I x))
    (fun _ hr => mem_prod.mpr ⟨hr, mem_univ x⟩)
  have hdtSpace : HasDerivWithinAt (fun r => fderiv ℝ (u r) x)
      (spacePart (d₂U et)) I t :=
    (spacePart.hasFDerivAt.comp_hasDerivWithinAt t h₂time).congr_of_mem
      (fun r hr => (hspace r hr).fderiv) ht
  rw [hdtSpace.derivWithin (hI t ht)]
  exact hdxTime.congr_fderiv (ContinuousLinearMap.ext fun v => hSym (0, v) et)

private theorem norm_fderiv_selfAdvection_le {u : Vec3 → Vec3}
    (hu : ContDiff ℝ 2 u) (x : Vec3) :
    ‖fderiv ℝ (fun y => fderiv ℝ u y (u y)) x‖ ≤
      ‖fderiv ℝ u x‖ ^ 2 + ‖iteratedFDeriv ℝ 2 u x‖ * ‖u x‖ := by
  have h₁ := (hu.differentiable (by norm_num) x).hasFDerivAt
  have h₂ := ((hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt
  let M := fderiv ℝ u x
  let G := fderiv ℝ (fderiv ℝ u) x
  have hG : ‖G‖ = ‖iteratedFDeriv ℝ 2 u x‖ := by
    simpa only [norm_iteratedFDeriv_one] using
      (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := u) (x := x) (n := 1))
  rw [(h₂.clm_apply h₁).fderiv, ← hG]
  change ‖M.comp M + G.flip (u x)‖ ≤ _
  exact (norm_add_le _ _).trans (add_le_add
    ((M.opNorm_comp_le M).trans_eq (pow_two _).symm)
    (by simpa only [ContinuousLinearMap.opNorm_flip] using G.flip.le_opNorm (u x)))


/-- A derivative column of a real continuous torus field in a finite
Fourier band has a continuous torus representative with the same band.
Its complexified Fourier coefficients have the exact derivative symbol. -/
theorem gradientColumnFourierBand
    (g : C(UnitAddTorus (Fin 3), Vec3)) (R : ℝ)
    (hband : ∀ k ∉ frequencyBand R, mFourierCoeff (endpointComplexifyContinuous g) k = 0)
    (i : Fin 3) :
    ∃ d : C(UnitAddTorus (Fin 3), Vec3),
      (∀ x, d (toUnitTorus x) =
        fderiv ℝ (fun y => g (toUnitTorus y)) x (coordinateDirection i)) ∧
      (∀ k ∉ frequencyBand R, mFourierCoeff (endpointComplexifyContinuous d) k = 0) ∧
      ∀ k, mFourierCoeff (endpointComplexifyContinuous d) k =
        fourierDerivativeSymbol k i • mFourierCoeff (endpointComplexifyContinuous g) k := by
  let gc := endpointComplexifyContinuous g
  let S := frequencyBand R
  let a (k : Fin 3 → ℤ) := fourierDerivativeSymbol k i • mFourierCoeff gc k
  let dc := finiteFourierSum S a
  have hDcCont : Continuous dc := by
    dsimp only [dc, finiteFourierSum]
    exact continuous_finsetSum _ fun k _ => (mFourier k).continuous.smul continuous_const
  let d : C(UnitAddTorus (Fin 3), Vec3) :=
    ⟨fun z => periodicRealPartVector (dc z),
      periodicRealPartVector.continuous.comp hDcCont⟩
  have hsyn : finiteFourierSum S (mFourierCoeff gc) = gc :=
    finiteFourierSum_mFourierCoeff_eq_of_band gc R fun k hk =>
      hband k fun hm => (not_lt_of_ge ((mem_frequencyBand R k).mp hm)) hk
  have hGCeq : (fun x => gc (toUnitTorus x)) =
      fun x => finiteFourierSum S (mFourierCoeff gc) (toUnitTorus x) := by rw [hsyn]
  have hGC : ContDiff ℝ ∞ (fun x => gc (toUnitTorus x)) := by
    rw [hGCeq]
    exact contDiff_lift_finiteFourierSum S (mFourierCoeff gc)
  have hDC (x : Vec3) : dc (toUnitTorus x) =
      fderiv ℝ (fun y => gc (toUnitTorus y)) x (coordinateDirection i) := by
    rw [hGCeq, coordinateDirection, fderiv_lift_finiteFourierSum_single]
  have hLift : (fun x => g (toUnitTorus x)) =
      periodicRealPartVector ∘ fun x => gc (toUnitTorus x) :=
    funext fun x => (periodicRealPartVector_complexifyVector (g (toUnitTorus x))).symm
  have hG : ContDiff ℝ ∞ (fun x => g (toUnitTorus x)) := by
    rw [hLift]
    exact periodicRealPartVector.contDiff.comp hGC
  have hder (x : Vec3) : d (toUnitTorus x) =
      fderiv ℝ (fun y => g (toUnitTorus y)) x (coordinateDirection i) := by
    have hchain := (periodicRealPartVector.hasFDerivAt.comp x
      ((hGC.differentiable (by simp)) x).hasFDerivAt).fderiv
    rw [hLift, hchain]
    change periodicRealPartVector (dc (toUnitTorus x)) =
      periodicRealPartVector (fderiv ℝ (fun y => gc (toUnitTorus y)) x (coordinateDirection i))
    rw [hDC]
  have hreal : (endpointComplexifyContinuous d : UnitAddTorus (Fin 3) → ComplexEuclideanVec3) =
      dc := by
    funext z
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
    have hchain : fderiv ℝ (fun y => gc (toUnitTorus y)) x =
        periodicComplexifyVector.comp (fderiv ℝ (fun y => g (toUnitTorus y)) x) :=
      (periodicComplexifyVector.hasFDerivAt.comp x
        ((hG.differentiable (by simp)) x).hasFDerivAt).fderiv
    change periodicComplexifyVector (d (toUnitTorus x)) = dc (toUnitTorus x)
    rw [hder, hDC, hchain]
    rfl
  have hcoeff (k : Fin 3 → ℤ) : mFourierCoeff (endpointComplexifyContinuous d) k =
      fourierDerivativeSymbol k i • mFourierCoeff gc k := by
    rw [hreal]
    change mFourierCoeff (finiteFourierSum S a) k = _
    rw [mFourierCoeff_finiteFourierSum]
    by_cases hk : k ∈ S
    · rw [ite_eq_left hk]
    · rw [ite_eq_right hk, show mFourierCoeff gc k = 0 from hband k hk, smul_zero]
  refine ⟨d, hder, ?_, hcoeff⟩
  intro k hk
  rw [hcoeff, show mFourierCoeff gc k = 0 from hband k hk, smul_zero]


private theorem norm_linearMap_le_of_coordinateBounds {A : Vec3 →L[ℝ] Vec3} {M : ℝ}
    (hM : 0 ≤ M) (hA : ∀ i, ‖A (coordinateDirection i)‖ ≤ M) : ‖A‖ ≤ 3 * M := by
  refine ContinuousLinearMap.opNorm_le_bound A (mul_nonneg (by norm_num) hM) fun x => ?_
  have hx : ∑ i : Fin 3, x i • coordinateDirection i = x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, coordinateDirection]
      using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
  calc
    ‖A x‖ = ‖∑ i : Fin 3, x i • A (coordinateDirection i)‖ := by
      have heq := congrArg A hx
      simp only [map_sum, map_smul] at heq
      exact congrArg norm heq.symm
    _ ≤ ∑ i : Fin 3, ‖x i • A (coordinateDirection i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, M * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, mul_comm]
      exact mul_le_mul (hA i) (PiLp.norm_apply_le x i) (norm_nonneg _) hM
    _ = _ := by simp; ring

/-- Bernstein applied to the actual gradient columns yields the velocity jet
budget of Proposition 5.1 from the band and a first-gradient bound alone. -/
theorem exists_parentVelocityJetBounds :
    ∃ V : ℕ → ℝ, (∀ n, 0 ≤ V n) ∧
      ∀ (g : C(Labels, Vec3)) {D : ℝ}, 1 ≤ D → RealTorusFourierBand (4 * D) g →
        (∀ x, ‖fderiv ℝ (fun y => g (toUnitTorus y)) x‖ ≤ D) →
        ∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ x,
          ‖iteratedFDeriv ℝ k (fun y => g (toUnitTorus y)) x‖ ≤ V n * D ^ k := by
  obtain ⟨K, hK, hBernstein⟩ := exists_bandBernsteinJetBounds
  let V (n : ℕ) := 3 * ∑ j ∈ Finset.range n, K j
  have hV (n : ℕ) : 0 ≤ V n := mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun j _ => hK j)
  refine ⟨V, hV, ?_⟩
  intro g D hD hband hgradient n k hk hkn x
  have hD₀ : 0 < D := zero_lt_one.trans_le hD
  let u := fun y => g (toUnitTorus y)
  have hu := (hBernstein g hD₀ (norm_nonneg _) le_rfl hband).1
  have hcol (i : Fin 3) : ∃ d : C(Labels, Vec3),
      ((fun y => d (toUnitTorus y)) = fun y => fderiv ℝ u y (coordinateDirection i)) ∧
      ∀ m : ℕ, ‖iteratedFDeriv ℝ m (fun y => d (toUnitTorus y)) x‖ ≤ K m * D * D ^ m := by
    obtain ⟨d, hd, hdband, _⟩ := gradientColumnFourierBand g (4 * D) (fun j hj =>
      hband j (lt_of_not_ge fun hj' => hj ((mem_frequencyBand _ _).mpr hj'))) i
    have hdNorm : ‖d‖ ≤ D := (ContinuousMap.norm_le d hD₀.le).mpr fun z => by
      obtain ⟨y, rfl⟩ := toUnitTorus_surjective z
      rw [hd]
      exact ((fderiv ℝ u y).le_opNorm (coordinateDirection i)).trans
        (by simpa [coordinateDirection] using hgradient y)
    exact ⟨d, funext hd, (fun m => (hBernstein d hD₀ hD₀.le hdNorm
      (fun j hj => hdband j (fun hj' => (not_lt_of_ge ((mem_frequencyBand _ _).mp hj')) hj))).2 m x)⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  change ‖iteratedFDeriv ℝ (m + 1) u x‖ ≤ _
  rw [← norm_iteratedFDeriv_fderiv]
  refine ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (hV n) (pow_nonneg hD₀.le _))
    fun v => ?_
  let J := iteratedFDeriv ℝ m (fderiv ℝ u) x
  have hdf : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hProd : 0 ≤ ∏ a, ‖v a‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hColJet (i : Fin 3) : ‖J v (coordinateDirection i)‖ ≤
      (K m * D * D ^ m) * ∏ a, ‖v a‖ := by
    obtain ⟨d, hd, hbound⟩ := hcol i
    let E := ContinuousLinearMap.apply ℝ Vec3 (coordinateDirection i)
    have heq : iteratedFDeriv ℝ m (fun y => d (toUnitTorus y)) x v =
        J v (coordinateDirection i) := by
      rw [show (fun y => d (toUnitTorus y)) = E ∘ fderiv ℝ u from hd]
      rw [E.iteratedFDeriv_comp_left hdf.contDiffAt (by simp)]
      rfl
    rw [← heq]
    exact ((iteratedFDeriv ℝ m (fun y => d (toUnitTorus y)) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hbound m) hProd)
  have hKsum : K m ≤ ∑ j ∈ Finset.range n, K j :=
    Finset.single_le_sum (f := K) (fun j _ => hK j) (Finset.mem_range.mpr (by omega))
  calc
    ‖J v‖ ≤ 3 * ((K m * D * D ^ m) * ∏ a, ‖v a‖) :=
      norm_linearMap_le_of_coordinateBounds
        (mul_nonneg (mul_nonneg (mul_nonneg (hK m) hD₀.le) (pow_nonneg hD₀.le _)) hProd)
        hColJet
    _ = (3 * K m * D ^ (m + 1)) * ∏ a, ‖v a‖ := by rw [pow_succ]; ring
    _ ≤ (V n * D ^ (m + 1)) * ∏ a, ‖v a‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hKsum (by norm_num)) (pow_nonneg hD₀.le _)) hProd


local notation "Frequency" => (Fin 3 → ℤ)

private theorem parent_latticeVector_add (a b : Frequency) :
    latticeVector (a + b) = latticeVector a + latticeVector b := by
  apply PiLp.ext
  intro i
  exact Int.cast_add (a i) (b i)

private theorem parent_norm_latticeVector_add_le (a b : Frequency) :
    ‖latticeVector (a + b)‖ ≤ ‖latticeVector a‖ + ‖latticeVector b‖ := by
  rw [parent_latticeVector_add]
  exact norm_add_le _ _

private theorem integrable_character_smul_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : Labels → E} (hf : Continuous f) (k : Frequency) :
    Integrable (fun z => mFourier (-k) z • f z) unitTorusMeasure := by
  have hcont : Continuous (fun z => mFourier (-k) z • f z) :=
    (mFourier (-k)).continuous.smul hf
  simpa only [integrableOn_univ] using
    hcont.continuousOn.integrableOn_compact (μ := unitTorusMeasure) isCompact_univ

private theorem mFourierCoeff_finsetSum_continuous
    {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (s : Finset I) (f : I → Labels → E) (hf : ∀ i ∈ s, Continuous (f i))
    (k : Frequency) :
    mFourierCoeff (fun z => ∑ i ∈ s, f i z) k = ∑ i ∈ s, mFourierCoeff (f i) k := by
  unfold mFourierCoeff
  simp only [Finset.smul_sum]
  exact integral_finsetSum s (fun i hi => integrable_character_smul_continuous (hf i hi) k)

private theorem continuous_parentFiniteFourierSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset Frequency) (a : Frequency → E) : Continuous (finiteFourierSum s a) := by
  unfold finiteFourierSum
  exact continuous_finsetSum _ fun j _ => (mFourier j).continuous.smul continuous_const

private theorem mFourierCoeff_single_mode_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (e : E) (a k : Frequency) (hk : k ≠ a) :
    mFourierCoeff (fun z => mFourier a z • e) k = 0 := by
  classical
  change (∫ z, mFourier (-k) z • (mFourier a z • e) ∂unitTorusMeasure) = _
  simp only [smul_smul, integral_smul_const, integral_fourier_pair, ite_eq_right hk, zero_smul]

private theorem mFourierCoeff_smul_finiteFourierSum_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (s t : Finset Frequency) (a : Frequency → ℂ) (b : Frequency → E)
    (k : Frequency) (hk : ∀ j ∈ s, ∀ l ∈ t, k ≠ j + l) :
    mFourierCoeff (fun z => finiteFourierSum s a z • finiteFourierSum t b z) k = 0 := by
  have hprod (z : Labels) : finiteFourierSum s a z • finiteFourierSum t b z =
      ∑ j ∈ s, ∑ l ∈ t, mFourier (j + l) z • (a j • b l) := by
    rw [finiteFourierSum, finiteFourierSum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [mFourier_add, smul_eq_mul, smul_smul]
    rw [mul_right_comm]
  simp_rw [hprod]
  rw [mFourierCoeff_finsetSum_continuous]
  · apply Finset.sum_eq_zero
    intro j hj
    rw [mFourierCoeff_finsetSum_continuous]
    · exact Finset.sum_eq_zero fun l hl => mFourierCoeff_single_mode_eq_zero _ _ _ (hk j hj l hl)
    · exact fun l _ => (mFourier (j + l)).continuous.smul continuous_const
  · exact fun j _ => continuous_finsetSum _ fun l _ =>
      (mFourier (j + l)).continuous.smul continuous_const

/-- The advective momentum of a real velocity in the `2 * Λ` Fourier band is
supported in the `4 * Λ` Fourier band. -/
theorem mFourierCoeff_advection_eq_zero_outside_band
    {Λ : ℝ} (g A : C(Labels, Vec3))
    (hband : ∀ k, 2 * Λ < ‖latticeVector k‖ →
      mFourierCoeff (fun z => periodicComplexifyVector (g z)) k = 0)
    (hA : ∀ x : Vec3, A (toUnitTorus x) =
      fderiv ℝ (fun y => g (toUnitTorus y)) x (g (toUnitTorus x)))
    (k : Frequency) (hk : 4 * Λ < ‖latticeVector k‖) :
    mFourierCoeff (fun z => periodicComplexifyVector (A z)) k = 0 := by
  let gC : C(Labels, ComplexEuclideanVec3) :=
    ⟨fun z => periodicComplexifyVector (g z), periodicComplexifyVector.continuous.comp g.continuous⟩
  let s := frequencyBand (2 * Λ)
  let a := mFourierCoeff gC
  have hFourier : finiteFourierSum s a = (gC : Labels → ComplexEuclideanVec3) :=
    finiteFourierSum_mFourierCoeff_eq_of_band gC (2 * Λ) hband
  have hDerivative (x : Vec3) (i : Fin 3) :
      periodicComplexifyVector (fderiv ℝ (fun y => g (toUnitTorus y)) x
        (EuclideanSpace.single i 1)) =
      finiteFourierSum s (fun j => fourierDerivativeSymbol j i • a j) (toUnitTorus x) := by
    obtain ⟨d, hd, hdB, hdC⟩ := gradientColumnFourierBand g (2 * Λ) (fun j hj =>
      hband j (lt_of_not_ge fun hj' => hj ((mem_frequencyBand _ _).mpr hj'))) i
    have hdsyn := finiteFourierSum_mFourierCoeff_eq_of_band (endpointComplexifyContinuous d)
      (2 * Λ) (fun j hj => hdB j (fun hj' => (not_lt_of_ge ((mem_frequencyBand _ _).mp hj')) hj))
    change periodicComplexifyVector (fderiv ℝ (fun y => g (toUnitTorus y)) x
      (coordinateDirection i)) = _
    rw [← hd x]
    change endpointComplexifyContinuous d (toUnitTorus x) = _
    rw [← show finiteFourierSum s (mFourierCoeff (endpointComplexifyContinuous d)) =
      (endpointComplexifyContinuous d : Labels → _) from hdsyn]
    unfold finiteFourierSum
    exact Finset.sum_congr rfl fun j _ => congrArg (mFourier j (toUnitTorus x) • ·) (hdC j)
  have hExpr (z : Labels) :
      periodicComplexifyVector (A z) =
        ∑ i : Fin 3, finiteFourierSum s (fun j => a j i) z •
          finiteFourierSum s (fun j => fourierDerivativeSymbol j i • a j) z := by
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
    rw [hA]
    have hBasis : ∑ i : Fin 3, (g (toUnitTorus x) i) • EuclideanSpace.single i 1 =
        g (toUnitTorus x) := by
      simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (g (toUnitTorus x))
    have hMap := congrArg (fderiv ℝ (fun y => g (toUnitTorus y)) x) hBasis
    simp only [map_sum, map_smul] at hMap
    rw [← hMap]
    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hVal : finiteFourierSum s (fun j => a j i) (toUnitTorus x) =
        (g (toUnitTorus x) i : ℂ) := by
      calc
        _ = finiteFourierSum s a (toUnitTorus x) i := by
          let L : ComplexEuclideanVec3 →L[ℂ] ℂ := EuclideanSpace.proj i
          change ∑ j ∈ s, mFourier j (toUnitTorus x) • L (a j) =
            L (∑ j ∈ s, mFourier j (toUnitTorus x) • a j)
          simp only [map_sum, map_smul]
        _ = _ := by rw [hFourier]; rfl
    rw [hDerivative, hVal]
    exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
  simp_rw [hExpr]
  rw [mFourierCoeff_finsetSum_continuous]
  · apply Finset.sum_eq_zero
    intro i _
    apply mFourierCoeff_smul_finiteFourierSum_eq_zero
    intro j hj l hl hkl
    apply (not_lt_of_ge (le_trans (parent_norm_latticeVector_add_le j l) ?_))
    · rw [← hkl]
      exact hk
    · have hJ := (mem_frequencyBand (2 * Λ) j).mp hj
      have hL := (mem_frequencyBand (2 * Λ) l).mp hl
      linarith
  · exact fun i _ => (continuous_parentFiniteFourierSum s (fun j => a j i)).smul
      (continuous_parentFiniteFourierSum s (fun j => fourierDerivativeSymbol j i • a j))


private def continuousRealHalfHolder (f : HalfHolder Labels Vec3) : C(Labels, Vec3) :=
  f.val.1.toContinuousMap

/-- The Leray projection preserves every Fourier band. -/
theorem RealTorusFourierBand.endpointStrongSpatialLeray {r : ℝ} {f : HalfHolder Labels Vec3}
    (hf : RealTorusFourierBand r (continuousRealHalfHolder f)) :
    RealTorusFourierBand r (continuousRealHalfHolder (TorusEuler.endpointStrongSpatialLeray f)) := by
  intro k hk
  change complexifiedHalfHolderFourierCoeff endpointSpatialComplexification
    (TorusEuler.endpointStrongSpatialLeray f) k = 0
  rw [endpointStrongSpatialLeray_complexCoefficient]
  change endpointSpatialComplexification.extendOperator (angularLeray (latticeVector k))
    (mFourierCoeff (fun z => periodicComplexifyVector (HalfHolder.eval z f)) k) = 0
  have hz : mFourierCoeff (fun z => periodicComplexifyVector (HalfHolder.eval z f)) k = 0 := hf k hk
  rw [hz, map_zero]

/-- The time derivative of a velocity in a fixed finite Fourier band has
the same band on the entire closed time interval. -/
theorem mFourierCoeff_timeDerivative_eq_zero_outside_band
    {a b R : ℝ} (hab : a < b) (g : ℝ → C(Labels, Vec3))
    (hs : ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => g q.1 (toUnitTorus q.2))
      (Icc a b ×ˢ (univ : Set Vec3)))
    (hband : ∀ t ∈ Icc a b, ∀ k, R < ‖latticeVector k‖ →
      mFourierCoeff (fun z => periodicComplexifyVector (g t z)) k = 0)
    {t : ℝ} (ht : t ∈ Icc a b) (d : C(Labels, Vec3))
    (hd : ∀ x : Vec3, HasDerivWithinAt
      (fun r => g r (toUnitTorus x)) (d (toUnitTorus x)) (Icc a b) t)
    (k : Frequency) (hk : R < ‖latticeVector k‖) :
    mFourierCoeff (fun z => periodicComplexifyVector (d z)) k = 0 := by
  classical
  let gC (r : ℝ) : C(Labels, ComplexEuclideanVec3) :=
    ⟨fun z => periodicComplexifyVector (g r z),
      periodicComplexifyVector.continuous.comp (g r).continuous⟩
  let c (j : Frequency) (r : ℝ) := mFourierCoeff (gC r) j
  let c' (j : Frequency) := derivWithin (c j) (Icc a b) t
  have hCoeff (j : Frequency) : ContDiffOn ℝ ∞ (c j) (Icc a b) :=
    contDiffOn_mFourierCoeff_of_truncatedParentLift (V := fun r x => g r (toUnitTorus x))
      hab hs (fun r => g r) (fun _ _ _ => rfl) j
  have hDeriv (j : Frequency) : HasDerivWithinAt (c j) (c' j) (Icc a b) t :=
    ((hCoeff j).differentiableOn (by simp) t ht).hasDerivWithinAt
  let s := frequencyBand R
  have hRep (r : ℝ) (hr : r ∈ Icc a b) (z : Labels) :
      finiteFourierSum s (fun j => c j r) z = gC r z :=
    congrFun (finiteFourierSum_mFourierCoeff_eq_of_band (gC r) R (hband r hr)) z
  have heq (x : Vec3) :
      finiteFourierSum s c' (toUnitTorus x) = periodicComplexifyVector (d (toUnitTorus x)) := by
    have hFin : HasDerivWithinAt
        (fun r => finiteFourierSum s (fun j => c j r) (toUnitTorus x))
        (finiteFourierSum s c' (toUnitTorus x)) (Icc a b) t := by
      unfold finiteFourierSum
      exact HasDerivWithinAt.fun_sum fun j _ => (hDeriv j).const_smul (mFourier j (toUnitTorus x))
    have hFin' := hFin.congr_of_mem (fun r hr => (hRep r hr (toUnitTorus x)).symm) ht
    have hDC : HasDerivWithinAt (fun r => gC r (toUnitTorus x))
        (periodicComplexifyVector (d (toUnitTorus x))) (Icc a b) t := by
      have h := (periodicComplexifyVector.hasFDerivAt.comp_hasFDerivWithinAt t
        (hd x).hasFDerivWithinAt).hasDerivWithinAt
      change HasDerivWithinAt (fun r => periodicComplexifyVector (g r (toUnitTorus x)))
        (periodicComplexifyVector (d (toUnitTorus x))) (Icc a b) t
      simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply, one_smul] using h
    have hUnique := uniqueDiffOn_Icc hab t ht
    exact (hFin'.derivWithin hUnique).symm.trans (hDC.derivWithin hUnique)
  have hField : (fun z => periodicComplexifyVector (d z)) = finiteFourierSum s c' := by
    funext z
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
    exact (heq x).symm
  rw [hField, mFourierCoeff_finiteFourierSum, ite_eq_right]
  exact fun h => (not_lt_of_ge ((mem_frequencyBand R k).mp h)) hk


/-- Sums of fields supported in the same band retain that band. -/
theorem RealTorusFourierBand.add {r : ℝ} {f g : C(Labels, Vec3)}
    (hf : RealTorusFourierBand r f) (hg : RealTorusFourierBand r g) :
    RealTorusFourierBand r (f + g) := by
  intro k hk
  have hc : endpointComplexifyContinuous (f + g) =
      endpointComplexifyContinuous f + endpointComplexifyContinuous g := by
    apply ContinuousMap.ext
    intro z
    exact map_add periodicComplexifyVector (f z) (g z)
  change mFourierCoeff (endpointComplexifyContinuous (f + g)) k = 0
  rw [hc, ← continuousFourierCoefficient_apply, map_add]
  have hf' : continuousFourierCoefficient k (endpointComplexifyContinuous f) = 0 := hf k hk
  have hg' : continuousFourierCoefficient k (endpointComplexifyContinuous g) = 0 := hg k hk
  rw [hf', hg', add_zero]

/-- The projected momentum residual for a velocity in the `2 * D` band
is supported in the `4 * D` band. -/
theorem parentResidualFourierBand_of_projectedMomentum
    {T D t : ℝ} (hT : 0 < T) (hD : 0 ≤ D) (ht : t ∈ Icc 0 T)
    (U : ℝ → C(Labels, Vec3)) (R : C(Labels, Vec3)) (A : HalfHolder Labels Vec3)
    (hSmooth : ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => U q.1 (toUnitTorus q.2))
      (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hU : ∀ s ∈ Icc 0 T, RealTorusFourierBand (2 * D) (U s))
    (hA : ∀ x, HalfHolder.eval (toUnitTorus x) A =
      fderiv ℝ (fun y => U t (toUnitTorus y)) x (U t (toUnitTorus x)))
    (hEq : ∀ x, HasDerivWithinAt (fun r => U r (toUnitTorus x))
      (-HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray A) + R (toUnitTorus x))
      (Icc 0 T) t) :
    RealTorusFourierBand (4 * D) R := by
  let p := continuousRealHalfHolder (endpointStrongSpatialLeray A)
  let d := -p + R
  have hd : RealTorusFourierBand (2 * D) d :=
    mFourierCoeff_timeDerivative_eq_zero_outside_band hT U hSmooth hU ht d hEq
  have hd' : RealTorusFourierBand (4 * D) d := fun k hk =>
    hd k ((show 2 * D ≤ 4 * D by linarith).trans_lt hk)
  have hAB : RealTorusFourierBand (4 * D) (continuousRealHalfHolder A) :=
    mFourierCoeff_advection_eq_zero_outside_band (U t) (continuousRealHalfHolder A) (hU t ht) hA
  have hp : RealTorusFourierBand (4 * D) p := hAB.endpointStrongSpatialLeray
  have heq : d + p = R := by
    dsimp only [d]
    abel
  rw [← heq]
  exact hd'.add hp

private theorem norm_continuousRealHalfHolder_le (f : HalfHolder Labels Vec3) :
    ‖continuousRealHalfHolder f‖ ≤ ‖f‖ :=
  (ContinuousMap.norm_le (continuousRealHalfHolder f) (norm_nonneg f)).mpr
    ((HalfHolder.norm_le_iff (norm_nonneg f)).mp le_rfl).1

private theorem norm_advectionHalfHolder_le {u : Vec3 → Vec3} (hu : ContDiff ℝ 2 u)
    (A : HalfHolder Labels Vec3) {M B H : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hVal : ∀ x, ‖u x‖ ≤ M) (hGrad : ∀ x, ‖fderiv ℝ u x‖ ≤ B)
    (hJet : ∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ H)
    (hA : ∀ x, HalfHolder.eval (toUnitTorus x) A = fderiv ℝ u x (u x)) :
    ‖A‖ ≤ 2 * (B * M + (B ^ 2 + H * M)) := by
  let adv := fun x => fderiv ℝ u x (u x)
  have hAdvBound (x : Vec3) : ‖adv x‖ ≤ B * M :=
    ((fderiv ℝ u x).le_opNorm _).trans
      (mul_le_mul (hGrad x) (hVal x) (norm_nonneg _) hB)
  have hDerivBound (x : Vec3) : ‖fderiv ℝ adv x‖ ≤ B ^ 2 + H * M := by
    exact (norm_fderiv_selfAdvection_le hu x).trans
      (add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hGrad x) 2)
        (mul_le_mul (hJet x) (hVal x) (norm_nonneg _) hH))
  have hAdv (z : Labels) : ‖HalfHolder.eval z A‖ ≤ B * M := by
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
    rw [hA]
    exact hAdvBound x
  have hdiff : Differentiable ℝ adv :=
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply (hu.of_le (by norm_num))).differentiable
      (by norm_num)
  have hAdvLip (x y : Vec3) : ‖adv x - adv y‖ ≤ (B ^ 2 + H * M) * ‖x - y‖ := by
    simpa only [dist_eq_norm] using
      (convex_univ : Convex ℝ (univ : Set Vec3)).norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => hdiff z) (fun z _ => hDerivBound z) (mem_univ y) (mem_univ x)
  have hB₀ : 0 ≤ B * M := mul_nonneg hB hM
  have hD₀ : 0 ≤ B ^ 2 + H * M := add_nonneg (sq_nonneg _) (mul_nonneg hH hM)
  apply (HalfHolder.norm_le_iff (by positivity)).mpr
  constructor
  · intro z
    exact (hAdv z).trans (by linarith)
  · intro z w
    change ‖HalfHolder.eval z A - HalfHolder.eval w A‖ ≤
      2 * (B * M + (B ^ 2 + H * M)) * Real.sqrt (dist z w)
    by_cases hdist : dist z w ≤ 1
    · obtain ⟨x, y, hx, hy, hd⟩ := exists_close_lifts z w
      have hsmall : dist z w ≤ Real.sqrt (dist z w) := by
        exact (Real.le_sqrt dist_nonneg dist_nonneg).mpr (by nlinarith [dist_nonneg (x := z) (y := w)])
      have hxA : HalfHolder.eval z A = adv x := hx ▸ hA x
      have hyA : HalfHolder.eval w A = adv y := hy ▸ hA y
      rw [hxA, hyA]
      calc
        _ ≤ (B ^ 2 + H * M) * ‖x - y‖ := hAdvLip x y
        _ ≤ (B ^ 2 + H * M) * (2 * dist z w) := mul_le_mul_of_nonneg_left hd hD₀
        _ ≤ (B ^ 2 + H * M) * (2 * Real.sqrt (dist z w)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsmall zero_le_two) hD₀
        _ ≤ _ := by nlinarith [mul_nonneg hB₀ (Real.sqrt_nonneg (dist z w))]
    · have hdist' : 1 ≤ Real.sqrt (dist z w) := by
        simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (le_of_lt (lt_of_not_ge hdist))
      calc
        _ ≤ ‖HalfHolder.eval z A‖ + ‖HalfHolder.eval w A‖ := norm_sub_le _ _
        _ ≤ B * M + B * M := add_le_add (hAdv z) (hAdv w)
        _ ≤ _ := by
          calc
            _ ≤ 2 * (B * M + (B ^ 2 + H * M)) := by linarith
            _ ≤ _ := le_mul_of_one_le_right (by positivity) hdist'

/-- The concrete Leray bound, the velocity Fourier band, and the
projected momentum equation give (7.5) on the entire time slab. -/
theorem exists_parentDerivedLowBounds :
    ∃ N : ℝ, 1 ≤ N ∧
      ∀ {T freq freqnext : ℝ}, 0 < T → N ≤ freq → 1 ≤ freqnext →
        ∀ (U R : ℝ → C(Labels, Vec3)) (A : ℝ → HalfHolder Labels Vec3),
          let u : Velocity := fun t x => U t (toUnitTorus x)
          ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)) →
          (∀ t ∈ Icc 0 T, ‖U t‖ ≤ freq ∧ RealTorusFourierBand (2 * freq ^ 5) (U t)) →
          (∀ t ∈ Icc 0 T, ‖R t‖ ≤ freqnext ^ (-3 : ℝ)) →
          (∀ t ∈ Icc 0 T, ∀ x, HalfHolder.eval (toUnitTorus x) (A t) = fderiv ℝ (u t) x (u t x)) →
          (∀ t ∈ Icc 0 T, ∀ x, HasDerivWithinAt (fun r => u r x)
            (-HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray (A t)) +
              R t (toUnitTorus x)) (Icc 0 T) t) →
          ∀ t ∈ Icc 0 T, ∀ x : Vec3,
            ‖fderiv ℝ (u t) x‖ ≤ freq ^ 9 ∧
            ‖derivWithin (fun r => fderiv ℝ (u r) x) (Icc 0 T) t‖ ≤ freq ^ 18 := by
  obtain ⟨K, hK, hBernstein⟩ := exists_bandBernsteinJetBounds
  let C₁ := K 1
  let C₂ := K 2
  let Cₐ := 2 * (C₁ + C₁ ^ 2 + C₂)
  let P := endpointStrongSpatialLeray
  let Cₜ := C₁ * (‖P‖ * Cₐ + 1)
  have hC₁ : 0 ≤ C₁ := hK 1
  have hC₂ : 0 ≤ C₂ := hK 2
  have hCₐ : 0 ≤ Cₐ := by positivity
  refine ⟨max 1 (max C₁ Cₜ), le_max_left _ _, ?_⟩
  intro T freq freqnext hT hfreq hnext U R A u hSmooth hU hR hA hEq t ht x
  have hfreq₁ : 1 ≤ freq := (le_max_left (1 : ℝ) _).trans hfreq
  have hfreqpos : 0 < freq := zero_lt_one.trans_le hfreq₁
  have hC₁freq : C₁ ≤ freq := ((le_max_left C₁ Cₜ).trans (le_max_right _ _)).trans hfreq
  have hCₜfreq : Cₜ ≤ freq := ((le_max_right C₁ Cₜ).trans (le_max_right _ _)).trans hfreq
  let D := freq ^ 5
  have hD : 1 ≤ D := one_le_pow₀ hfreq₁
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hUB : RealTorusFourierBand (4 * D) (U t) := fun k hk =>
    (hU t ht).2 k ((show 2 * D ≤ 4 * D by linarith).trans_lt hk)
  obtain ⟨hUsmooth, hUjet⟩ := hBernstein (U t) hDpos hfreqpos.le (hU t ht).1 hUB
  have huVal (y : Vec3) : ‖u t y‖ ≤ freq := ((U t).norm_coe_le_norm _).trans (hU t ht).1
  have huGrad (y : Vec3) : ‖fderiv ℝ (u t) y‖ ≤ C₁ * freq * D := by
    simpa only [norm_iteratedFDeriv_one, pow_one] using hUjet 1 y
  have hPnorm : ‖P (A t)‖ ≤ ‖P‖ * (Cₐ * (D ^ 2 * freq ^ 2)) := by
    apply (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left _ (norm_nonneg _))
    have hb := norm_advectionHalfHolder_le (hUsmooth.of_le (by simp)) (A t)
      hfreqpos.le (show 0 ≤ C₁ * freq * D by positivity) (show 0 ≤ C₂ * freq * D ^ 2 by positivity)
      huVal huGrad (hUjet 2) (hA t ht)
    refine hb.trans ?_
    calc
      _ ≤ 2 * (C₁ * (D ^ 2 * freq ^ 2) + ((C₁ * freq * D) ^ 2 + C₂ * freq * D ^ 2 * freq)) := by
        apply mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) zero_le_two
        have hl : D ≤ D ^ 2 := by
          simpa only [pow_one] using (pow_le_pow_right₀ hD (show (1 : ℕ) ≤ 2 by decide))
        calc
          C₁ * freq * D * freq = C₁ * (D * freq ^ 2) := by ring
          _ ≤ C₁ * (D ^ 2 * freq ^ 2) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hl (sq_nonneg _)) hC₁
      _ = _ := by dsimp only [Cₐ]; ring
  let p : C(Labels, Vec3) := continuousRealHalfHolder (P (A t))
  have hAB : RealTorusFourierBand (4 * D) (continuousRealHalfHolder (A t)) :=
    mFourierCoeff_advection_eq_zero_outside_band (U t) (continuousRealHalfHolder (A t))
      (hU t ht).2 (hA t ht)
  have hpBand : RealTorusFourierBand (4 * D) p := hAB.endpointStrongSpatialLeray
  have hpA : 0 ≤ ‖P‖ * (Cₐ * (D ^ 2 * freq ^ 2)) := by positivity
  obtain ⟨hpsmooth, hpJet⟩ := hBernstein p hDpos hpA
    ((norm_continuousRealHalfHolder_le _).trans hPnorm) hpBand
  have hRA : 0 ≤ freqnext ^ (-3 : ℝ) := Real.rpow_nonneg (zero_le_one.trans hnext) _
  have hRB : RealTorusFourierBand (4 * D) (R t) :=
    parentResidualFourierBand_of_projectedMomentum hT hDpos.le ht U (R t) (A t)
      hSmooth (fun r hr => (hU r hr).2) (hA t ht) (hEq t ht)
  obtain ⟨hRsmooth, hRJet⟩ := hBernstein (R t) hDpos hRA (hR t ht) hRB
  constructor
  · calc
      _ ≤ C₁ * freq * D := huGrad x
      _ ≤ freq * freq * D := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC₁freq hfreqpos.le) hDpos.le
      _ ≤ freq ^ 9 := by
        rw [show freq * freq * D = freq ^ 7 by dsimp only [D]; ring]
        exact pow_le_pow_right₀ hfreq₁ (by decide)
  · let q := fun y : Vec3 => -(p (toUnitTorus y)) + R t (toUnitTorus y)
    have hq : (fun y => derivWithin (fun r => u r y) (Icc 0 T) t) = q :=
      funext fun y => (hEq t ht y).derivWithin (uniqueDiffOn_Icc hT t ht)
    have hTime := (hasFDerivAt_slabVelocityTimeDerivative hT ht (hSmooth.of_le (by simp)) x).fderiv
    rw [hq] at hTime
    rw [← hTime]
    have hqder := (((hpsmooth.differentiable (by simp)) x).hasFDerivAt.neg.add
      ((hRsmooth.differentiable (by simp)) x).hasFDerivAt).fderiv
    rw [show fderiv ℝ q x = _ from hqder]
    have hrSmall : freqnext ^ (-3 : ℝ) ≤ D ^ 2 * freq ^ 2 := by
      calc
        _ ≤ freqnext ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hnext (by norm_num)
        _ = 1 := Real.rpow_zero _
        _ ≤ _ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD) (one_le_pow₀ hfreq₁)
    calc
      _ ≤ ‖fderiv ℝ (fun y => p (toUnitTorus y)) x‖ +
            ‖fderiv ℝ (fun y => R t (toUnitTorus y)) x‖ := by
        simpa only [norm_neg] using norm_add_le
          (-fderiv ℝ (fun y => p (toUnitTorus y)) x) (fderiv ℝ (fun y => R t (toUnitTorus y)) x)
      _ ≤ C₁ * (‖P‖ * (Cₐ * (D ^ 2 * freq ^ 2))) * D + C₁ * (freqnext ^ (-3 : ℝ)) * D :=
        add_le_add (by simpa only [norm_iteratedFDeriv_one, pow_one] using hpJet 1 x)
          (by simpa only [norm_iteratedFDeriv_one, pow_one] using hRJet 1 x)
      _ ≤ C₁ * (‖P‖ * (Cₐ * (D ^ 2 * freq ^ 2))) * D + C₁ * (D ^ 2 * freq ^ 2) * D :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrSmall hC₁) hDpos.le)
      _ = Cₜ * freq ^ 17 := by dsimp only [D, Cₜ]; ring
      _ ≤ freq ^ 18 := by
        rw [show (18 : ℕ) = 1 + 17 by decide, pow_add, pow_one]
        exact mul_le_mul_of_nonneg_right hCₜfreq (by positivity)

end

end TorusEuler
