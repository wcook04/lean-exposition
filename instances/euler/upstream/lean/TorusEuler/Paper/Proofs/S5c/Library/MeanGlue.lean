import TorusEuler.Paper.Proofs.S5c.Library.MeanEuler
import TorusEuler.Paper.Proofs.S5a.Proposition51
import TorusEuler.MeanPressureHessian

/-!
# Glue for the mean pressure of Lemma 5.9

For the proof of the Hessian bound of the mean pressures (`sections/08_exact_wave.tex:233-255`):

* `meanSolution_sum`: finite sums of solutions of (5.11) are solutions with the summed
  source ("add the mean equations (5.11) of the levels `2 ≤ p ≤ P`", `:233-235`);
* `meanSolution_source_phaseIndependent`: the source of a solution of (5.11) is phase
  independent (the other terms of the equation are);
* `fderivWithin_slab_direction`: the material derivative `∂_{(1,u)}` of (4.12) on the closed
  slab is `∂_t b + (Db)u`;
* `parentGradient_halfHolder_of_B1`: `‖∇U‖_{C^{0,1/2}} ≤ C 𝖣²` for a field with frequencies at
  most `4𝖣` and `‖∇U‖_∞ ≤ 𝖣`, from Bernstein's inequality (B.1) (`hB_1`) through
  `Lib.S5a.exists_velocityJets_of_lemmaB1` (`08_exact_wave.tex:247-250`).
-/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

local notation "Labels" => UnitAddTorus (Fin 3)

namespace TorusEuler.Paper.Lib.S5c

open HierarchyTwistedProfile Lib.S5a

noncomputable section

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ

/-- Evaluation of a finite sum of profiles. -/
theorem profile_sum_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Finset ℕ)
    (F : ℕ → HierarchyTwistedProfile T k E) (x : HierarchyProfilePoint) :
    (∑ p ∈ s, F p).val.val.val x = ∑ p ∈ s, (F p).val.val.val x := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    rfl

/-- The divergence is additive on differentiable fields. -/
theorem divergence_add_of_differentiable {f g : Vec3 → Vec3} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    divergence (f + g) x = divergence f x + divergence g x := by
  simp only [divergence, fderiv_add hf hg, add_apply, PiLp.add_apply,
    Finset.sum_add_distrib]

/-- `(0, 0, 0)` solves (5.11) with source `0`. -/
theorem meanSolution_zero (d : ParentGeometry hT U X k) : S5.MeanSolution d 0 0 0 := by
  refine ⟨?_, ?_, ?_, ⟨0, 0, contDiffOn_const, contDiffOn_const, fun t _ => ?_, rfl, rfl,
    fun t ht a => ?_, fun t ht a => ?_, fun t ht a s => ?_⟩⟩
  · rw [map_zero, map_zero, zero_add]
  · rw [map_zero]
  · rw [map_zero]
  · exact ⟨fun n a => rfl, fun n a => rfl⟩
  · exact hasDerivWithinAt_const t _ _
  · simp [divergence]
  · rw [show ((0 : VP).val.val.val (t, a, s)) = 0 from rfl]
    simp

/-- Sums of two solutions of (5.11) are solutions with the summed source. -/
theorem meanSolution_add (d : ParentGeometry hT U X k) {f₁ f₂ B₁ B₂ : VP} {q₁ q₂ : SP}
    (h₁ : S5.MeanSolution d f₁ B₁ q₁) (h₂ : S5.MeanSolution d f₂ B₂ q₂) :
    S5.MeanSolution d (f₁ + f₂) (B₁ + B₂) (q₁ + q₂) := by
  obtain ⟨v₁, z₁, hv₁, hz₁, hp₁, h01, hT1, hd1, hdiv1, hB1⟩ := h₁.endpoint
  obtain ⟨v₂, z₂, hv₂, hz₂, hp₂, h02, hT2, hd2, hdiv2, hB2⟩ := h₂.endpoint
  refine ⟨?_, ?_, ?_, ⟨v₁ + v₂, z₁ + z₂, hv₁.add hv₂, hz₁.add hz₂, fun t ht => ?_, ?_, ?_,
    fun t ht a => (hd1 t ht a).add (hd2 t ht a), fun t ht a => ?_, fun t ht a s => ?_⟩⟩
  · rw [map_add, map_add, add_add_add_comm, h₁.momentum, h₂.momentum]
  · rw [map_add, h₁.phase_independent, h₂.phase_independent]
  · rw [map_add, h₁.pressure_phase_independent, h₂.pressure_phase_independent, add_zero]
  · refine ⟨fun n a => ?_, fun n a => ?_⟩
    · change v₁ t (a + latticeVector n) + v₂ t (a + latticeVector n) = v₁ t a + v₂ t a
      rw [(hp₁ t ht).1 n a, (hp₂ t ht).1 n a]
    · change z₁ t (a + latticeVector n) + z₂ t (a + latticeVector n) = z₁ t a + z₂ t a
      rw [(hp₁ t ht).2 n a, (hp₂ t ht).2 n a]
  · change z₁ 0 + z₂ 0 = 0
    rw [h01, h02, add_zero]
  · change z₁ T + z₂ T = 0
    rw [hT1, hT2, add_zero]
  · change divergence (v₁ t + v₂ t) a = 0
    rw [divergence_add_of_differentiable
      (((meanInt_slice_spatial hv₁ ht).differentiable (by simp)) a)
      (((meanInt_slice_spatial hv₂ ht).differentiable (by simp)) a), hdiv1 t ht a, hdiv2 t ht a,
      add_zero]
  · change B₁.val.val.val (t, a, s) + B₂.val.val.val (t, a, s) = fderiv ℝ (X 0 t) a (v₁ t a + v₂ t a)
    rw [hB1 t ht a s, hB2 t ht a s, map_add]

/-- Finite sums of solutions of (5.11) are solutions with the summed source (`08_exact_wave.tex:233-235`). -/
theorem meanSolution_sum (d : ParentGeometry hT U X k) (s : Finset ℕ) (f B : ℕ → VP)
    (q : ℕ → SP) (h : ∀ p ∈ s, S5.MeanSolution d (f p) (B p) (q p)) :
    S5.MeanSolution d (∑ p ∈ s, f p) (∑ p ∈ s, B p) (∑ p ∈ s, q p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using meanSolution_zero d
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi]
    exact meanSolution_add d (h i (Finset.mem_insert_self i s))
      (ih fun p hp => h p (Finset.mem_insert_of_mem hp))

/-- The source of a solution of (5.11) is independent of the phase. -/
theorem meanSolution_source_phaseIndependent (d : ParentGeometry hT U X k) {f B : VP} {q : SP}
    (hs : S5.MeanSolution d f B q) : (S5.ops d).average f = f := by
  refine HierarchyTwistedProfile.ext fun x hx => ?_
  obtain ⟨t, a, s⟩ := x
  rw [Bridge.ops_average_eval d f hx]
  have hc : (fun z => f.val.val.val (t, a, z)) = fun _ => f.val.val.val (t, a, s) :=
    funext fun z => (momentum_eval d hs hx.1 a z).trans (momentum_eval d hs hx.1 a s).symm
  change phaseMean (fun z => f.val.val.val (t, a, z)) = f.val.val.val (t, a, s)
  rw [hc, phaseMean_const]

/-- **The material derivative of (4.12) on the closed slab**: for `b` smooth on `[0,T] × ℝ³`,
`∂_{(1,u)} b(t,x) = ∂_t b(t,x) + (Db)(t,x) u` (time derivative within `[0,T]`). -/
theorem fderivWithin_slab_direction (hT : 0 < T) {b : Velocity}
    (hb : ContDiffOn ℝ ∞ (Function.uncurry b) (Icc 0 T ×ˢ (univ : Set Vec3))) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x u : Vec3) :
    fderivWithin ℝ (Function.uncurry b) (Icc 0 T ×ˢ (univ : Set Vec3)) (t, x) (1, u) =
      derivWithin (fun r => b r x) (Icc 0 T) t + fderiv ℝ (b t) x u := by
  have hmem : ((t, x) : ℝ × Vec3) ∈ Icc 0 T ×ˢ (univ : Set Vec3) := ⟨ht, mem_univ _⟩
  have hdw : DifferentiableWithinAt ℝ (Function.uncurry b) (Icc 0 T ×ˢ (univ : Set Vec3)) (t, x) :=
    hb.differentiableOn (by simp) _ hmem
  have hL := hdw.hasFDerivWithinAt
  set L := fderivWithin ℝ (Function.uncurry b) (Icc 0 T ×ˢ (univ : Set Vec3)) (t, x) with hLdef
  have hc1 : HasDerivWithinAt (fun r : ℝ => (r, x)) ((1 : ℝ), (0 : Vec3)) (Icc 0 T) t :=
    (hasDerivWithinAt_id t _).prodMk (hasDerivWithinAt_const t _ x)
  have hmaps1 : MapsTo (fun r : ℝ => (r, x)) (Icc 0 T) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    fun r hr => ⟨hr, mem_univ _⟩
  have h1₀ := hL.comp_hasDerivWithinAt t hc1 hmaps1
  have h1 : HasDerivWithinAt (fun r => b r x) (L (1, 0)) (Icc 0 T) t := h1₀
  have hc2 : HasFDerivAt (fun y : Vec3 => (t, y)) (ContinuousLinearMap.inr ℝ ℝ Vec3) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hmaps2 : MapsTo (fun y : Vec3 => (t, y)) univ (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    fun y _ => ⟨ht, mem_univ _⟩
  have h2 : HasFDerivWithinAt (b t) (L.comp (ContinuousLinearMap.inr ℝ ℝ Vec3)) univ x :=
    hL.comp x hc2.hasFDerivWithinAt hmaps2
  rw [h1.derivWithin (uniqueDiffOn_Icc hT t ht), (hasFDerivWithinAt_univ.mp h2).fderiv,
    ContinuousLinearMap.comp_apply, ← map_add]
  congr 1
  refine Prod.ext (by simp) (by simp)

/-- **`‖∇U‖_{C^{0,1/2}} ≤ C𝖣²`** for a smooth field with frequencies at most `4𝖣` and
`‖∇U‖_∞ ≤ 𝖣`, from Bernstein's inequality (B.1) (`hB_1`), as in `08_exact_wave.tex:247-250`
(copy of `exists_parentGradient_halfHolder_bound` with the Bernstein step from `hB_1`). -/
theorem parentGradient_halfHolder_of_B1 (hB_1 : Statement.lemma_B_1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : C(Labels, Vec3)) {D : ℝ}, 1 ≤ D →
      RealTorusFourierBand (4 * D) g → ContDiff ℝ ∞ (fun y => g (toUnitTorus y)) →
      (∀ x, ‖fderiv ℝ (fun y => g (toUnitTorus y)) x‖ ≤ D) →
      let DU := fderiv ℝ (fun y => g (toUnitTorus y))
      SpatialHolderHalf 0 DU ∧ spatialHolderHalfNorm 0 DU ≤ C * D ^ 2 := by
  obtain ⟨K, hK, hJet⟩ := exists_velocityJets_of_lemmaB1 hB_1
  refine ⟨1 + Real.sqrt (2 * K 2), by positivity, ?_⟩
  intro g D hD hBand hu hGrad DU
  let u : Vec3 → Vec3 := fun x => g (toUnitTorus x)
  have hDU : ContDiff ℝ ∞ DU := hu.fderiv_right (m := ∞) (by simp)
  let B (n : ℕ) := if n = 0 then D else K 2 * D ^ 2
  have hBounds (j : ℕ) (hj : j ≤ 0 + 1) (x : Vec3) : ‖iteratedFDeriv ℝ j DU x‖ ≤ B j := by
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · simpa only [norm_iteratedFDeriv_zero, B, ite_true] using hGrad x
    · change ‖iteratedFDeriv ℝ 1 (fderiv ℝ u) x‖ ≤ B 1
      rw [norm_iteratedFDeriv_fderiv]
      simpa [B] using hJet g hD hBand hu hGrad 2 2 (by norm_num) le_rfl x
  obtain ⟨hHolder, hHolderNorm⟩ := spatialHolderHalf_of_bounded_jets hDU B hBounds
  refine ⟨hHolder, hHolderNorm.trans ?_⟩
  simp only [Finset.range_one, Finset.sum_singleton, B, ite_true, zero_add, one_ne_zero, ite_false]
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hpow : D ^ 3 ≤ D ^ 4 := pow_le_pow_right₀ hD (by norm_num)
  have hK₀ : 0 ≤ 2 * K 2 := mul_nonneg (by norm_num) (hK 2)
  have hsqrt : Real.sqrt (2 * D * (K 2 * D ^ 2)) ≤ Real.sqrt (2 * K 2) * D ^ 2 := by
    calc
      _ = Real.sqrt ((2 * K 2) * D ^ 3) := by congr 1; ring
      _ ≤ Real.sqrt ((2 * K 2) * D ^ 4) := Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left hpow hK₀)
      _ = _ := by rw [Real.sqrt_mul hK₀, show D ^ 4 = (D ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg D)]
  calc
    _ ≤ D ^ 2 + Real.sqrt (2 * K 2) * D ^ 2 := add_le_add (le_self_pow₀ hD (by norm_num)) hsqrt
    _ = _ := by ring

end

end TorusEuler.Paper.Lib.S5c
