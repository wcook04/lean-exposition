import TorusEuler.HierarchyTwistedCoefficientNorms
import TorusEuler.HierarchyTwistedRelayCoefficientBudget
import TorusEuler.HierarchyTwistedSlowSourceBounds
import TorusEuler.InductiveParentGeometry
import TorusEuler.InductiveStageVelocityJetBounds
import TorusEuler.PhysicalHierarchyProfileBounds

/-! Uniform coefficient budgets for the actual restricted inductive parent. -/

open Set
open scoped ContDiff

namespace TorusEuler.InductiveEulerStage

noncomputable section

local notation "Time(" T ")" => Icc (0 : ℝ) T

/-- One finite-order constant for all normalized coefficient seminorms. -/
def stageCoefficientOrderConstant (C : ℕ → ℝ) (m : ℕ) : ℝ :=
  (hierarchyAdmissibleWords (Fin 4) m).card * ∑ j ∈ Finset.range (m + 1), C j

/-- The graph readout uses a common constant through the requested order. -/
def stageCoframeOrderConstant (C : ℕ → ℝ) (m : ℕ) : ℝ :=
  1 + ∑ j ∈ Finset.range (m + 1), C j

theorem stageCoefficientOrderConstant_nonneg (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (m : ℕ) :
    0 ≤ stageCoefficientOrderConstant C m :=
  mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun j _ => hC j)

theorem stageCoframeOrderConstant_ge_one (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (m : ℕ) :
    1 ≤ stageCoframeOrderConstant C m := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hC j)

variable {P : InductiveEulerParameters} {n : ℕ} {activation T : ℝ}
  {s : InductiveEulerStage P n activation} {hT : 0 < T} {k : Vec3}

local notation "G(" s "," t ")" => (fun a : Vec3 => fderiv ℝ (InductiveEulerStage.flow s t 0) (InductiveEulerStage.flow s 0 t a))
local notation "D(" P "," n ")" => (InductiveEulerParameters.frequency P n ^ (9 : ℕ))

/-- The actual coframe controls the slow rows, the normalized covector
controls fast advection, and the inverse chart gives the graph bounds. -/
structure StageCoefficientCaps (d : s.OnSlab hT k) (a : ℕ) (D ℓ h freq : ℝ) (C : ℕ → ℝ) : Prop where
  label_pos : 0 < ℓ
  label_le_one : ℓ ≤ 1
  label_scale : ℓ * D ^ (7 : ℕ) ≤ 1
  label_inverse : ℓ⁻¹ = D ^ a
  phase_pos : 0 < h
  carrier : ‖k‖ ≤ D * freq
  deformation : ∀ t ∈ Time(T), ∀ x : Vec3,
    ‖fderiv ℝ (s.flow 0 t) x‖ ≤ D ∧ ‖fderiv ℝ (s.flow t 0) x‖ ≤ D
  forwardSmooth : ∀ t ∈ Time(T), ContDiff ℝ ∞ (s.flow 0 t)
  inverseSmooth : ∀ t ∈ Time(T), ContDiff ℝ ∞ (s.flow t 0)
  coframeSmooth : ∀ t ∈ Time(T), ContDiff ℝ ∞ (G(s,t))
  coframeGraph : ∀ t ∈ Time(T), ∀ x : Vec3, G(s,t) (s.flow t 0 x) = fderiv ℝ (s.flow t 0) x
  rawCoframe : ∀ m, ∀ t ∈ Time(T), ∀ x : Vec3,
    ‖iteratedFDeriv ℝ m (G(s,t)) x‖ ≤ C m * D ^ (7 * m + 1)
  coframeDerivative : ∀ t ∈ Time(T), ∀ x : Vec3,
    ‖fderiv ℝ (G(s,t)) x‖ ≤ C 1 * D ^ (8 : ℕ)
  scaledCoframe : ∀ m, ∀ t ∈ Time(T), ∀ j ≤ m, ∀ x : Vec3,
    ℓ ^ j * ‖iteratedFDeriv ℝ j (G(s,t)) x‖ ≤ stageCoframeOrderConstant C m * D
  rowCap : ∀ m (i : Fin 3), HierarchyTwistedProfile.unweightedSeminorm False ℓ h m hT
    (HierarchyTwistedProfile.scaledCoframeRowProfile ℓ d.geometry.inverse i) ≤
      stageCoefficientOrderConstant C m * D ^ (a + 1)
  fastCap : ∀ m, HierarchyTwistedProfile.unweightedSeminorm False ℓ h m hT
    (HierarchyTwistedProfile.scaledPhaseCoefficientProfile h d.geometry.covector) ≤
      stageCoefficientOrderConstant C m * D ^ (2 : ℕ) * freq ^ (3 / 2 : ℝ)

private theorem contDiff_slab_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → Vec3 → E} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Time(T) ×ˢ (univ : Set Vec3)))
    {t : ℝ} (ht : t ∈ Time(T)) : ContDiff ℝ ∞ (f t) :=
  contDiffOn_univ.mp <| hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩)

set_option maxHeartbeats 2500000 in
/-- The finite Fourier band of the actual stage supplies all coefficient
orders uniformly, with `D = μ^9`, `ℓ = D^(-a)` and the prescribed phase width. -/
theorem exists_stageCoefficientCaps :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {activation T : ℝ}
        {s : InductiveEulerStage P n activation} {hT : 0 < T} {k : Vec3}
        (d : s.OnSlab hT k), T ≤ 1 → 1 ≤ P.frequency n →
        ∀ {freq t₀ : ℝ}, 0 < freq → t₀ ∈ Time(T) → ‖labelWaveVector s.flow 0 0 k t₀‖ = freq →
        ∀ (a : ℕ), 7 ≤ a →
        StageCoefficientCaps d a (D(P,n)) ((D(P,n) ^ a)⁻¹) (freq ^ (-1 / 2 : ℝ)) freq C := by
  obtain ⟨R, hR, hVelocity⟩ := exists_velocity_jet_bounds
  obtain ⟨C, hC, hParent⟩ := exists_parent_coefficientJetBounds R hR
  refine ⟨C, hC, ?_⟩
  intro P n activation T s hT k d hT₁ hμ freq t₀ hfreq ht₀ hCenter a ha
  let D := D(P,n)
  let ℓ := (D ^ a)⁻¹
  let h := freq ^ (-1 / 2 : ℝ)
  have hD : 1 ≤ D := one_le_pow₀ hμ
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have haD : 1 ≤ D ^ a := one_le_pow₀ hD
  have hℓ : 0 < ℓ := inv_pos.mpr (pow_pos hDpos _)
  have hℓone : ℓ ≤ 1 := inv_le_one_of_one_le₀ haD
  have hScale : ℓ * D ^ (7 : ℕ) ≤ 1 := by
    calc
      _ ≤ ℓ * D ^ a := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD ha) hℓ.le
      _ = _ := inv_mul_cancel₀ (pow_pos hDpos _).ne'
  have hLabel : ℓ⁻¹ = D ^ a := inv_inv _
  have hμD : P.frequency n ≤ D := by
    simpa only [pow_one] using pow_le_pow_right₀ hμ (show (1 : ℕ) ≤ 9 by decide)
  let hX := d.deformationOn.flow
  have hPer (t : ℝ) (_ : t ∈ Time(T)) : SpatiallyPeriodic (s.velocity t) := s.periodic_velocity t
  have hSB (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) :
      ‖fderiv ℝ (s.flow 0 t) x‖ ≤ D ∧ ‖fderiv ℝ (s.flow t 0) x‖ ≤ D :=
    ⟨((d.deformationOn.bounds t ht).2.1 x).2.trans hμD,
      ((d.deformationOn.bounds t ht).2.2 x).2.trans hμD⟩
  have hF (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) : ‖fderiv ℝ (s.flow 0 t) x‖ ≤ D := (hSB t ht x).1
  have hG (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) : ‖G(s,t) x‖ ≤ D := (hSB t ht (s.flow 0 t x)).2
  have hJets := hParent hT hT₁ hD hX d.smooth_velocity hPer hF hG
    (fun m j hj hjm t ht x => hVelocity s hμ m j hj hjm t (d.subset ht) x) k hfreq ht₀ hCenter
  have hGval (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) :
      d.geometry.inverse.val.val.val (t,x,0) = G(s,t) x :=
    d.geometry.inverse_value (t,x,0) ⟨ht, mem_univ _⟩
  have hκval (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) :
      d.geometry.covector.val.val.val (t,x,0) = labelWaveVector s.flow 0 x k t :=
    d.geometry.covector_value (t,x,0) ⟨ht, mem_univ _⟩
  have hGjet (m : ℕ) (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) :
      ‖iteratedFDeriv ℝ m (G(s,t)) x‖ ≤ C m * D ^ (7 * m + 1) := (hJets m t ht x).2.1
  have hcarrier : ‖k‖ ≤ D * freq := (div_le_iff₀ hfreq).mp
    (hX.norm_normalizedLabelWaveVector_bounds hT (d.smooth_velocity.of_le (by simp)) hPer
      ht₀ ht₀ 0 k hD hfreq hCenter (hF t₀ ht₀ 0) (hG t₀ ht₀ 0) (hF t₀ ht₀ 0) (hG t₀ ht₀ 0)).1
  refine ⟨hℓ, hℓone, hScale, hLabel, Real.rpow_pos_of_pos hfreq _, hcarrier, hSB, ?_, ?_, ?_,
    ?_, hGjet, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact contDiff_slab_slice (hX.contDiffOn_forwardLabelFlow hT d.smooth_velocity hPer) ht
  · intro t ht
    exact contDiff_slab_slice (f := fun r => s.flow r 0)
      (hX.contDiffOn_inverseLabelFlow hT d.smooth_velocity hPer) ht
  · intro t ht
    exact contDiff_slab_slice (f := fun r => G(s,r))
      (hX.contDiffOn_inverseLabelDerivative hT d.smooth_velocity hPer) ht
  · intro t ht x
    exact (hGval t ht (s.flow t 0 x)).symm.trans
      ((d.geometry.inverseGraph_values hX d.smooth_velocity hPer).2 t ht x 0).1
  · intro t ht x
    simpa only [norm_iteratedFDeriv_one, Nat.reduceMul, Nat.reduceAdd] using hGjet 1 t ht x
  · intro m t ht
    have hConst : 0 ≤ stageCoframeOrderConstant C m := by
      unfold stageCoframeOrderConstant
      exact add_nonneg zero_le_one (Finset.sum_nonneg fun j _ => hC j)
    refine scaledCoframe_jet_bound hℓ.le hD hConst hScale ?_
    intro j hj x
    have hCj : C j ≤ stageCoframeOrderConstant C m := by
      unfold stageCoframeOrderConstant
      have hsum : C j ≤ ∑ i ∈ Finset.range (m + 1), C i :=
        Finset.single_le_sum (fun i _ => hC i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
      exact hsum.trans (le_add_of_nonneg_left zero_le_one)
    exact (hGjet j t ht x).trans (mul_le_mul_of_nonneg_right hCj (pow_nonneg hD₀ _))
  · intro m i
    refine (HierarchyTwistedProfile.unweightedSeminorm_scaledCoframeRowProfile_le_of_parent_power_bound
      (n := m) (h := h) (D := D) (L := 1) (q := 7) (p := 1) (C := C) hT d.geometry.inverse
      d.geometry.mean.inverse_independent hℓ.le hD₀ zero_le_one hScale (fun j _ => hC j) ?_ i).trans_eq ?_
    · intro t ht j _ x
      simpa only [hGval t ht, mul_one] using hGjet j t ht x
    · rw [hLabel, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hD₀ _), mul_one, pow_one,
        stageCoefficientOrderConstant, pow_succ]
      ring
  · intro m
    refine HierarchyTwistedProfile.unweightedSeminorm_scaledPhaseCoefficient_le_of_normalizedJets
      hT d.geometry.covector d.geometry.oscillation.covector_independent hℓ.le hD₀ hScale hfreq rfl
      m C (fun j _ => hC j) ?_
    intro j _ t ht x
    simpa only [hκval t ht] using (hJets j t ht x).2.2.2.2.1


/-- The slow and fast advection terms are covered by one fixed-order cost. -/
def stageSourceCoefficientCost (C : ℕ → ℝ) (m : ℕ) : ℝ :=
  6 * hierarchyQuadraticConstant (Fin 4) m ^ 2 * stageCoefficientOrderConstant C m

theorem stageSourceCoefficientCost_nonneg (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (m : ℕ) :
    0 ≤ stageSourceCoefficientCost C m :=
  mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (stageCoefficientOrderConstant_nonneg C hC m)

/-- Promote the raw coframe and phase norms to the common recurrence budget.
The parent exponent is independent of the order and frequency. -/
theorem StageCoefficientCaps.sourceCaps {d : s.OnSlab hT k} {a b : ℕ} {D ℓ h freq K : ℝ}
    {C : ℕ → ℝ} (cap : StageCoefficientCaps d a D ℓ h freq C)
    (hD : 1 ≤ D) (hfreq : 0 ≤ freq) (ha : 7 ≤ a) (hb : a + 1 ≤ b)
    (hC : ∀ j, 0 ≤ C j) (m : ℕ) (hK : stageSourceCoefficientCost C m ≤ K) :
    2 * (3 * hierarchyQuadraticConstant (Fin 4) m ^ 2 *
      (stageCoefficientOrderConstant C m * D ^ (a + 1))) ≤ K * D ^ b ∧
    (2 * hierarchyQuadraticConstant (Fin 4) m ^ 2) *
      HierarchyTwistedProfile.unweightedSeminorm False ℓ h m hT
        (HierarchyTwistedProfile.scaledPhaseCoefficientProfile h d.geometry.covector) ≤
      K * D ^ b * freq ^ (3 / 2 : ℝ) := by
  let Q := hierarchyQuadraticConstant (Fin 4) m
  let J := stageCoefficientOrderConstant C m
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hJ : 0 ≤ J := stageCoefficientOrderConstant_nonneg C hC m
  have hK₀ : 0 ≤ K := (stageSourceCoefficientCost_nonneg C hC m).trans hK
  have hK' : 2 * Q ^ 2 * J ≤ K :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 6) (sq_nonneg Q)) hJ).trans hK
  constructor
  · calc
      _ = stageSourceCoefficientCost C m * D ^ (a + 1) := by unfold stageSourceCoefficientCost; ring
      _ ≤ _ := mul_le_mul hK (pow_le_pow_right₀ hD hb) (pow_nonneg hD₀ _) hK₀
  · calc
      _ ≤ (2 * Q ^ 2) * (J * D ^ (2 : ℕ) * freq ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (cap.fastCap m) (mul_nonneg zero_le_two (sq_nonneg Q))
      _ = (2 * Q ^ 2 * J) * D ^ (2 : ℕ) * freq ^ (3 / 2 : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul hK' (pow_le_pow_right₀ hD (by omega)) (pow_nonneg hD₀ _) hK₀)
        (Real.rpow_nonneg hfreq _)

/-- The cutoff tail needs only the first unscaled inverse-coframe jet. -/
theorem StageCoefficientCaps.cutoffTailCoframeBudget {d : s.OnSlab hT k} {a : ℕ}
    {D ℓ h freq : ℝ} {C : ℕ → ℝ} (_cap : StageCoefficientCaps d a D ℓ h freq C)
    (hD : 1 ≤ D) (hC : 0 ≤ C 1) :
    max D (D * D + C 1 * D ^ (8 : ℕ)) ≤ (1 + C 1) * D ^ (8 : ℕ) := by
  have hD₂ : D ^ (2 : ℕ) ≤ D ^ (8 : ℕ) := pow_le_pow_right₀ hD (by decide)
  have hD₁ : D ≤ D ^ (8 : ℕ) := by
    simpa only [pow_one] using pow_le_pow_right₀ hD (show (1 : ℕ) ≤ 8 by decide)
  refine max_le ?_ ?_
  · exact hD₁.trans (le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans hD) _) (le_add_of_nonneg_right hC))
  · rw [add_mul, one_mul, ← pow_two]
    exact add_le_add hD₂ le_rfl


set_option maxHeartbeats 1500000 in
/-- The normalized linear-relay coefficient budget follows from the same
actual stage, on any closed or open portion of the parent slab. -/
theorem exists_stageRelayCoefficientBudgets :
    ∃ L : ℕ → ℝ, (∀ m, 0 ≤ L m) ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {activation T : ℝ}
        {s : InductiveEulerStage P n activation} {hT : 0 < T} {k : Vec3}
        (d : s.OnSlab hT k), T ≤ 1 → 1 ≤ P.frequency n →
        ∀ {freq t₀ : ℝ}, 0 < freq → t₀ ∈ Time(T) → ‖labelWaveVector s.flow 0 0 k t₀‖ = freq →
        ∀ (a : ℕ), 16 ≤ a → ∀ {S : Set ℝ}, S ⊆ Time(T) → ∀ m,
        HierarchyTwistedProfile.WaveRelayCoefficientBudget ((D(P,n) ^ a)⁻¹) (freq ^ (-1 / 2 : ℝ))
          m (2 * L m * D(P,n) ^ (15 + a))
          (fun (t : S) x => d.geometry.inverse.val.val.val (t,x,0))
          (fun (t : S) x => d.geometry.strain.val.val.val (t,x,0))
          (fun (t : S) x => freq⁻¹ • d.geometry.covector.val.val.val (t,x,0)) := by
  obtain ⟨R, hR, hVelocity⟩ := exists_velocity_jet_bounds
  obtain ⟨L, hL, hRelay⟩ := HierarchyTwistedProfile.exists_transportedWaveRelayCoefficientBudget R hR
  refine ⟨L, hL, ?_⟩
  intro P n activation T s hT k d hT₁ hμ freq t₀ hfreq ht₀ hCenter a ha S hS m
  let D := D(P,n)
  let ℓ := (D ^ a)⁻¹
  let h := freq ^ (-1 / 2 : ℝ)
  have hD : 1 ≤ D := one_le_pow₀ hμ
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hℓ : 0 ≤ ℓ := inv_nonneg.mpr (pow_nonneg hDpos.le _)
  have hScale : ℓ * D ^ (16 : ℕ) ≤ 1 := by
    calc
      _ ≤ ℓ * D ^ a := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD ha) hℓ
      _ = _ := inv_mul_cancel₀ (pow_pos hDpos _).ne'
  have hμD : P.frequency n ≤ D := by
    simpa only [pow_one] using pow_le_pow_right₀ hμ (show (1 : ℕ) ≤ 9 by decide)
  have hF (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) : ‖fderiv ℝ (s.flow 0 t) x‖ ≤ D :=
    ((d.deformationOn.bounds t ht).2.1 x).2.trans hμD
  have hG (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) : ‖G(s,t) x‖ ≤ D :=
    ((d.deformationOn.bounds t ht).2.2 (s.flow 0 t x)).2.trans hμD
  have hInv : ‖ℓ⁻¹‖ ≤ D ^ a := by
    rw [show ℓ⁻¹ = D ^ a from inv_inv _, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hDpos.le _)]
  exact HierarchyTwistedProfile.WaveRelayCoefficientBudget.absorb_inverse_width hD (hL m) hInv
    (hRelay hT hT₁ hD d.deformationOn.flow d.smooth_velocity (fun t _ => s.periodic_velocity t) hF hG
      (fun j i hi hj t ht x => hVelocity s hμ j i hi hj t (d.subset ht) x)
      hfreq ht₀ hCenter d.geometry.inverse d.geometry.strain d.geometry.covector
      (fun t ht x => d.geometry.inverse_value (t,x,0) ⟨ht, mem_univ _⟩)
      (fun t ht x => d.geometry.strain_value (t,x,0) ⟨ht, mem_univ _⟩)
      (fun t ht x => d.geometry.covector_value (t,x,0) ⟨ht, mem_univ _⟩) hS (h := h) hℓ hScale m)

end

end TorusEuler.InductiveEulerStage
