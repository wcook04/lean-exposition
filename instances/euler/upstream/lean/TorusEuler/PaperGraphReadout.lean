import TorusEuler.HierarchyGraphReadoutBounds

/-! Physical graph estimates in Lemma 5.7, for each of the three norms. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem smooth_graph_slice (f : HierarchyTwistedProfile T k E) {A : Velocity} {t : ℝ}
    (ht : t ∈ Icc 0 T) (hA : ContDiff ℝ ∞ (A t)) : ContDiff ℝ ∞ (graphRead A f t) := by
  let L : Vec3 →L[ℝ] ℝ := innerSL ℝ k
  exact (contDiff_slice f ht).comp (hA.prodMk (L.contDiff.comp hA))

/-- The explicit order prefactor for the oscillatory graph readout. -/
def oscillatoryGraphJetCost (L : ℝ) (m : ℕ) : ℝ :=
  ((3 : ℝ) * (2 : ℝ) ^ m * (2 * L)) ^ m * (4 : ℝ) ^ m

/-- The explicit order prefactor for the phase-independent graph readout. -/
def meanGraphJetCost (L : ℝ) (m : ℕ) : ℝ :=
  ((3 : ℝ) * (2 : ℝ) ^ m * L) ^ m * (4 : ℝ) ^ m

/-- The weighted graph estimates in (5.44) and (5.45). The ordered spatial
word sum controls the multi-index sum, and the Hölder bound spends one
additional spatial derivative. -/
theorem paperLemma57_graphWeighted (hT : 0 < T) (f : HierarchyTwistedProfile T k E)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hγpos : ∀ r ∈ Icc t₀ T, 0 < γ r)
    {A : Velocity} {t ell h D freq L : ℝ} {m a : ℕ} {B : Vec3 → Vec3 →L[ℝ] Vec3}
    (ht : t ∈ Icc t₀ T) (hell : 0 < ell) (hh : 0 < h) (hD : 1 ≤ D) (hf : 1 ≤ freq) (hL : 1 ≤ L)
    (hLabel : ell⁻¹ ≤ D ^ a) (hWidth : h = freq ^ (-1 / 2 : ℝ)) (hCarrier : ‖k‖ ≤ D * freq)
    (hA : ContDiff ℝ ∞ (A t)) (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x) (hBreg : ContDiff ℝ ∞ B)
    (hcoeff : ∀ j ≤ m + 1, ∀ x, ell ^ j * ‖iteratedFDeriv ℝ j B x‖ ≤ L * D) :
    let N (n : ℕ) := amplitudeSeminorm False ell h n hT ht₀ htT γ hγ hγpos f
    let factor (n : ℕ) := oscillatoryGraphJetCost L n * D ^ ((max a 1 + 1) * n) *
      freq ^ ((3 : ℝ) * n / 2)
    (∑ i : Fin m → Fin 3, spatialSupNorm (spatialDerivativeWord (List.ofFn i) (graphRead A f t))) ≤
        (3 : ℝ) ^ m * factor m * γ t * N m ∧
      SpatialHolderHalf m (graphRead A f t) ∧
      spatialHolderHalfNorm m (graphRead A f t) ≤
        (3 * (m + 1) : ℝ) * factor (m + 1) * γ t * N (m + 1) := by
  intro N factor
  have hN (n : ℕ) : 0 ≤ N n := apply_nonneg (amplitudeSeminorm False ell h n hT ht₀ htT γ hγ hγpos) f
  have hJets (n : ℕ) (hn : n ≤ m + 1) :
      PhaseJetBound n (factor n * γ t * N n) (graphRead A f t) := by
    have h := graphRead_frequency_jetBound_weighted hT ht₀ htT γ hγ hγpos f
      (t := t) (A := A) (B := B) (ℓ := ell) (D := D) (L := L)
      (n := n) (a := a) (p := 0) (α := 0) (C := N n)
      ht hell hh hD hf hL (hN n) hLabel hWidth hCarrier hA hB hBreg
      (fun j hj => hcoeff j (hj.trans hn)) (by simp only [N, pow_zero, Real.rpow_zero, mul_one, le_refl])
    intro j hj x
    refine (h j hj x).trans_eq ?_
    simp only [add_zero, factor, oscillatoryGraphJetCost]
    ring
  have hg := smooth_graph_slice f ⟨ht₀.trans ht.1, ht.2⟩ hA
  refine ⟨(sum_spatialDerivativeWord_sup_le_of_jetBound hg (hJets m (by omega))).trans_eq (by ring), ?_⟩
  have hNonneg : 0 ≤ factor (m + 1) * γ t * N (m + 1) := by
    have hD₀ := zero_le_one.trans hD
    have hfreq₀ := zero_le_one.trans hf
    have hγ₀ := (hγpos t ht).le
    have hL₀ := zero_le_one.trans hL
    have hn := hN (m + 1)
    dsimp only [factor, oscillatoryGraphJetCost]
    positivity
  obtain ⟨hHolder, hSize⟩ := spatialHolderHalfNorm_le_of_uniformJets hg hNonneg (hJets (m + 1) le_rfl)
  exact ⟨hHolder, hSize.trans_eq (by ring)⟩

/-- The full closed-slab form of Lemma 5.7 uses the unit weight. -/
theorem paperLemma57_graphUnweighted (hT : 0 < T) (f : HierarchyTwistedProfile T k E)
    {A : Velocity} {t ell h D freq L : ℝ} {m a : ℕ} {B : Vec3 → Vec3 →L[ℝ] Vec3}
    (ht : t ∈ Icc 0 T) (hell : 0 < ell) (hh : 0 < h) (hD : 1 ≤ D) (hf : 1 ≤ freq) (hL : 1 ≤ L)
    (hLabel : ell⁻¹ ≤ D ^ a) (hWidth : h = freq ^ (-1 / 2 : ℝ)) (hCarrier : ‖k‖ ≤ D * freq)
    (hA : ContDiff ℝ ∞ (A t)) (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x) (hBreg : ContDiff ℝ ∞ B)
    (hcoeff : ∀ j ≤ m + 1, ∀ x, ell ^ j * ‖iteratedFDeriv ℝ j B x‖ ≤ L * D) :
    let N (n : ℕ) := unweightedSeminorm False ell h n hT f
    let factor (n : ℕ) := oscillatoryGraphJetCost L n * D ^ ((max a 1 + 1) * n) *
      freq ^ ((3 : ℝ) * n / 2)
    (∑ i : Fin m → Fin 3, spatialSupNorm (spatialDerivativeWord (List.ofFn i) (graphRead A f t))) ≤
        (3 : ℝ) ^ m * factor m * N m ∧
      SpatialHolderHalf m (graphRead A f t) ∧
      spatialHolderHalfNorm m (graphRead A f t) ≤
        (3 * (m + 1) : ℝ) * factor (m + 1) * N (m + 1) := by
  simpa only [amplitudeSeminorm_apply, unweightedSeminorm, boundedWeightSeminorm_apply, inv_one, mul_one] using
    paperLemma57_graphWeighted hT f le_rfl hT.le (fun _ => 1) continuousOn_const
      (fun _ _ => zero_lt_one) ht hell hh hD hf hL hLabel hWidth hCarrier hA hB hBreg hcoeff

/-- A phase-independent field loses only label derivative powers in the
physical graph estimate, also in the weighted version. -/
theorem paperLemma57_graphMeanWeighted (hT : 0 < T) (f : HierarchyTwistedProfile T k E)
    (hmean : HierarchyPeriodicProfile.PhaseIndependent f.val.val)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hγpos : ∀ r ∈ Icc t₀ T, 0 < γ r)
    {A : Velocity} {t ell h D L : ℝ} {m a : ℕ} {B : Vec3 → Vec3 →L[ℝ] Vec3}
    (ht : t ∈ Icc t₀ T) (hell : 0 < ell) (hD : 1 ≤ D) (hL : 1 ≤ L)
    (hLabel : ell⁻¹ ≤ D ^ a)
    (hA : ContDiff ℝ ∞ (A t)) (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x) (hBreg : ContDiff ℝ ∞ B)
    (hcoeff : ∀ j ≤ m + 1, ∀ x, ell ^ j * ‖iteratedFDeriv ℝ j B x‖ ≤ L * D) :
    let N (n : ℕ) := amplitudeSeminorm False ell h n hT ht₀ htT γ hγ hγpos f
    let factor (n : ℕ) := meanGraphJetCost L n * D ^ ((a + 1) * n)
    (∑ i : Fin m → Fin 3, spatialSupNorm (spatialDerivativeWord (List.ofFn i) (graphRead A f t))) ≤
        (3 : ℝ) ^ m * factor m * γ t * N m ∧
      SpatialHolderHalf m (graphRead A f t) ∧
      spatialHolderHalfNorm m (graphRead A f t) ≤
        (3 * (m + 1) : ℝ) * factor (m + 1) * γ t * N (m + 1) := by
  intro N factor
  have ht' : t ∈ Icc 0 T := ⟨ht₀.trans ht.1, ht.2⟩
  let mean (a : Vec3) := slice f t a 0
  have hReg : ContDiff ℝ ∞ mean := (contDiff_slice f ht').comp (contDiff_id.prodMk contDiff_const)
  have hScaled : scaledPhaseProfile ell h (slice f t) = scaledPhaseProfile ell 1 (fun x _ => mean x) := by
    funext z
    exact hmean (t, ell • z.1, 0) ⟨ht', mem_univ _⟩ (h * z.2)
  have hGraph : graphRead A f t = mean ∘ A t := by
    funext x
    exact hmean (t, A t x, 0) ⟨ht', mem_univ _⟩ _
  have hN (n : ℕ) : 0 ≤ N n := apply_nonneg (amplitudeSeminorm False ell h n hT ht₀ htT γ hγ hγpos) f
  have hNonneg (n : ℕ) : 0 ≤ factor n * γ t * N n := by
    have hD₀ := zero_le_one.trans hD
    have hγ₀ := (hγpos t ht).le
    have hL₀ := zero_le_one.trans hL
    have hn := hN n
    dsimp only [factor, meanGraphJetCost]
    positivity
  have hJets (n : ℕ) (hn : n ≤ m + 1) :
      PhaseJetBound n (factor n * γ t * N n) (graphRead A f t) := by
    have hRaw := scaledPhaseProfile_jetBound_weighted hT ell h n ht₀ htT γ hγ hγpos f ht
    rw [hScaled] at hRaw
    let C := γ t * ((4 : ℝ) ^ n * N n)
    have hC : 0 ≤ C := mul_nonneg (hγpos t ht).le (mul_nonneg (by positivity) (hN n))
    have h :=
      transportedHierarchyMean_frequency_jetBound (a := a) (p := 0) (freq := 1) (alpha := 0) (C := C)
        hell hD zero_lt_one hL hC hLabel hA hB hBreg hReg
        (fun j hj => hcoeff j (hj.trans hn)) (by simpa only [pow_zero, Real.rpow_zero, mul_one] using hRaw)
    rw [hGraph]
    intro j hj x
    refine (h j hj x).trans_eq ?_
    simp only [Real.rpow_zero, add_zero, mul_one, C, factor, meanGraphJetCost]
    ring
  have hg := smooth_graph_slice f ht' hA
  obtain ⟨hHolder, hSize⟩ := spatialHolderHalfNorm_le_of_uniformJets hg (hNonneg (m + 1)) (hJets (m + 1) le_rfl)
  exact ⟨(sum_spatialDerivativeWord_sup_le_of_jetBound hg (hJets m (by omega))).trans_eq (by ring),
    hHolder, hSize.trans_eq (by ring)⟩

/-- The full-slab estimate for a phase-independent field. -/
theorem paperLemma57_graphMean (hT : 0 < T) (f : HierarchyTwistedProfile T k E)
    (hmean : HierarchyPeriodicProfile.PhaseIndependent f.val.val)
    {A : Velocity} {t ell h D L : ℝ} {m a : ℕ} {B : Vec3 → Vec3 →L[ℝ] Vec3}
    (ht : t ∈ Icc 0 T) (hell : 0 < ell) (hD : 1 ≤ D) (hL : 1 ≤ L) (hLabel : ell⁻¹ ≤ D ^ a)
    (hA : ContDiff ℝ ∞ (A t)) (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x) (hBreg : ContDiff ℝ ∞ B)
    (hcoeff : ∀ j ≤ m + 1, ∀ x, ell ^ j * ‖iteratedFDeriv ℝ j B x‖ ≤ L * D) :
    let N (n : ℕ) := unweightedSeminorm False ell h n hT f
    let factor (n : ℕ) := meanGraphJetCost L n * D ^ ((a + 1) * n)
    (∑ i : Fin m → Fin 3, spatialSupNorm (spatialDerivativeWord (List.ofFn i) (graphRead A f t))) ≤
        (3 : ℝ) ^ m * factor m * N m ∧
      SpatialHolderHalf m (graphRead A f t) ∧
      spatialHolderHalfNorm m (graphRead A f t) ≤
        (3 * (m + 1) : ℝ) * factor (m + 1) * N (m + 1) := by
  simpa only [amplitudeSeminorm_apply, unweightedSeminorm, boundedWeightSeminorm_apply, inv_one, mul_one] using
    paperLemma57_graphMeanWeighted (h := h) hT f hmean le_rfl hT.le (fun _ => 1) continuousOn_const
      (fun _ _ => zero_lt_one) ht hell hD hL hLabel hA hB hBreg hcoeff

end

end TorusEuler.HierarchyTwistedProfile

namespace TorusEuler

open HierarchyTwistedProfile

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For data given on the centered label cell, extend the mean and
oscillation to the physical periodic graph with the same jet budgets,
including at the cell faces. This is the collar formulation of Lemma 5.7. -/
theorem paperLemma57_periodicGraphFromCell
    {A : Velocity} {X : Vec3 → Vec3} {k : Vec3}
    {t δ ell h D freq L γ : ℝ} {f : ℝ → Vec3 → ℝ → E} {mean : ℝ → Vec3 → E}
    {m a : ℕ} {B : Vec3 → Vec3 →L[ℝ] Vec3} {N : ℕ → ℝ}
    (hA : ContDiff ℝ ∞ (A t)) (hX : Continuous X)
    (hLeft : Function.LeftInverse X (A t)) (hRight : Function.LeftInverse (A t) X)
    (hAper : ∀ n : Fin 3 → ℤ, ∀ x, A t (x + latticeVector n) = A t x + latticeVector n)
    (hf : ContDiff ℝ ∞ (Function.uncurry (f t))) (hmean : ContDiff ℝ ∞ (mean t))
    (hmeanPer : SpatiallyPeriodic (mean t)) (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2)
    (hcollar : ∀ x, (∃ i : Fin 3, 1 / 2 - δ < |x i|) → ∀ q, f t x q = mean t x)
    (hell : 0 < ell) (hh : 0 < h) (hD : 1 ≤ D) (hfreq : 1 ≤ freq) (hL : 1 ≤ L)
    (hγ : 0 ≤ γ) (hN : ∀ n, 0 ≤ N n) (hLabel : ell⁻¹ ≤ D ^ a)
    (hWidth : h = freq ^ (-1 / 2 : ℝ)) (hCarrier : ‖k‖ ≤ D * freq)
    (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x) (hBreg : ContDiff ℝ ∞ B)
    (hcoeff : ∀ j ≤ m + 1, ∀ x, ell ^ j * ‖iteratedFDeriv ℝ j B x‖ ≤ L * D)
    (hprofile : ∀ n ≤ m + 1, PhaseJetBound n (γ * N n) (scaledPhaseProfile ell h (f t))) :
    let g := periodicHierarchyProfile A k f mean t
    let K (n : ℕ) := ((3 : ℝ) * (2 : ℝ) ^ n * (2 * L)) ^ n * N n *
      D ^ ((max a 1 + 1) * n) * (γ * freq ^ ((3 : ℝ) * n / 2))
    ContDiff ℝ ∞ g ∧ SpatiallyPeriodic g ∧
      (∑ i : Fin m → Fin 3, spatialSupNorm (spatialDerivativeWord (List.ofFn i) g)) ≤ (3 : ℝ) ^ m * K m ∧
      SpatialHolderHalf m g ∧ spatialHolderHalfNorm m g ≤ (3 * (m + 1) : ℝ) * K (m + 1) := by
  intro g K
  have hj (n : ℕ) (hn : n ≤ m + 1) : PhaseJetBound n (K n) (transportedProfile A k f t) := by
    have hRaw := transportedHierarchyProfile_frequency_jetBound (a := a) (n := n) (p := 0)
      (alpha := 0) (C := N n) (gamma := γ) (f := f)
      hell hh hD hfreq hL (hN n) hγ hLabel hWidth hCarrier hA hB hBreg hf
      (fun j hj => hcoeff j (hj.trans hn))
      (by simpa only [pow_zero, Real.rpow_zero, mul_one] using hprofile n hn)
    simpa only [pow_zero, add_zero, K] using hRaw
  obtain ⟨hg, hPer, hm⟩ := periodicHierarchyProfile_jetBound hA hX hLeft hRight
    hAper hf hmean hmeanPer hδ hδ₁ hcollar (hj m (by omega))
  obtain ⟨_, _, hm₁⟩ := periodicHierarchyProfile_jetBound hA hX hLeft hRight
    hAper hf hmean hmeanPer hδ hδ₁ hcollar (hj (m + 1) le_rfl)
  have hK : 0 ≤ K (m + 1) := by
    have hD₀ := zero_le_one.trans hD
    have hf₀ := zero_le_one.trans hfreq
    have hL₀ := zero_le_one.trans hL
    have hn := hN (m + 1)
    dsimp only [K]
    positivity
  exact ⟨hg, hPer, sum_spatialDerivativeWord_sup_le_of_jetBound hg hm,
    spatialHolderHalfNorm_le_of_uniformJets hg hK hm₁⟩

end

end TorusEuler
