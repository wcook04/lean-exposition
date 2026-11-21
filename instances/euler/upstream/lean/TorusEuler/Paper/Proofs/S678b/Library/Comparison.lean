import TorusEuler.Paper.Proofs.S678b.Library.CurlBound
import TorusEuler.LaterPhysicalAmplification
import TorusEuler.FrameCouplingVariation
import TorusEuler.InductionAmplificationSmallness
import TorusEuler.ParentVelocityEstimates
import TorusEuler.InductiveActivationClock
import TorusEuler.TruncatedParentProjectedMomentum

/-! # Glue for item 2 of the proof of Theorem 7.1: the comparison hypotheses (2.7) and the window bound

Used by no row of package S678b; imported by package S678a, which proves the fields `comparison`
and `window_upper` of `Theorem71Conclusions` (sections/08b_induction.tex:304-326). The hypotheses
(2.7) of wave `j` were checked in item 2 of the proof of Theorem 7.1 for the absolute constant
`C₀` of Subsection 2.2; this module re-runs that check for an arbitrary `C₀` and all large `j`
(`eventually_finiteSmallness`), with

* Lemma B.1 (Bernstein (B.1)) giving (7.6) (08b:205-219): `parent_derived_low_bounds`, a copy of
  the library's `exists_parentDerivedLowBounds` with `hB_1` in place of
  `exists_bandBernsteinJetBounds`;
* Lemma 2.2 (the frame equations (2.2)) giving the error estimate (6.6) (08b:39-50):
  `errorSize_le`, a copy of `PhysicalAmplification.errorSize_le_of_older_gradient` with `h2_2` in
  place of `hasDerivWithinAt_movingFrame`;
* Lemma 1.3 ((1.15), 08b:320-321) through `lemma13_schedule`.

The scalar absorption (08b:316-324) is the library's
`exists_induction_amplification_step_comparison`. The window bound `windowConstant`,
`physical_window_upper` (08b:304-311) is also here. -/

open Filter MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper.Lib.S678b

open MovingWaveVector (PhysicalAmplification frame entry amplificationPhysicalError)

local notation "Labels" => UnitAddTorus (Fin 3)

noncomputable section

/-! ## Bernstein's inequality (B.1) at orders one and two -/

/-- One coordinate derivative of order `m` of a field with frequencies at most `4D`: Bernstein's
inequality (B.1) of `hB_1` (with `Λ = D` and any admissible symbol). -/
theorem bernstein_coordinate (hB_1 : Statement.lemma_B_1) :
    ∃ Cb : ℕ → ℝ, (∀ m, 0 ≤ Cb m) ∧
      ∀ (m : ℕ) (g : C(Labels, Vec3)) {D : ℝ}, 0 < D → RealTorusFourierBand (4 * D) g →
        ∀ β : Fin m → Fin 3, Monotone β → ∀ x : Vec3,
          ‖iteratedFDeriv ℝ m (fun z => g (toUnitTorus z)) x
            (fun i => EuclideanSpace.single (β i) 1)‖ ≤ Cb m * D ^ m * ‖g‖ := by
  obtain ⟨Cop, Cb, Ct, -, hCb, -, hB⟩ := hB_1 _ AppendixB.cutoffSymbol_dyadicMultiplierCutoff
  refine ⟨Cb, hCb, fun m g D hD hband β hβ x => ?_⟩
  have hb := (hB D hD).2.2 m Vec3 g (realNormedBand_of_realTorusBand hband)
  have hmem : β ∈ Finset.univ.filter (fun β : Fin m → Fin 3 => Monotone β) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hβ
  have h1 := le_ciSup (hb.1 β) x
  have h2 := Finset.single_le_sum (f := fun β : Fin m → Fin 3 => ⨆ x : Vec3,
      ‖iteratedFDeriv ℝ m (fun z => g (toUnitTorus z)) x
        (fun j => EuclideanSpace.single (β j) 1)‖)
    (fun β _ => Real.iSup_nonneg fun _ => norm_nonneg _) hmem
  exact (h1.trans h2).trans hb.2

/-- Bernstein bounds for the first and second derivatives of a `C²` field with frequencies at
most `4D` and sup norm at most `A`, from (B.1) (`hB_1`): the operator norms are bounded by the
coordinate derivatives (the second derivative is symmetric, so nondecreasing coordinate words
suffice). Replaces, at orders one and two, the library's `exists_bandBernsteinJetBounds`
(content of Lemma B.1). -/
theorem bernstein_jets (hB_1 : Statement.lemma_B_1) :
    ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧
      ∀ (g : C(Labels, Vec3)) {D A : ℝ}, 0 < D → ‖g‖ ≤ A → RealTorusFourierBand (4 * D) g →
        ContDiff ℝ 2 (fun z => g (toUnitTorus z)) → ∀ x : Vec3,
          ‖fderiv ℝ (fun z => g (toUnitTorus z)) x‖ ≤ K₁ * A * D ∧
            ‖iteratedFDeriv ℝ 2 (fun z => g (toUnitTorus z)) x‖ ≤ K₂ * A * D ^ 2 := by
  obtain ⟨Cb, hCb, hcoord⟩ := bernstein_coordinate hB_1
  have hCb1 := hCb 1
  have hCb2 := hCb 2
  refine ⟨3 * Cb 1, 9 * Cb 2, by positivity, by positivity, ?_⟩
  intro g D A hD hgA hband hsmooth x
  set f : Vec3 → Vec3 := fun z => g (toUnitTorus z) with hf
  have h1 (i : Fin 3) : ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ≤ Cb 1 * D * A := by
    have h := hcoord 1 g hD hband (fun _ => i) (fun _ _ _ => le_rfl) x
    rw [iteratedFDeriv_one_apply, pow_one] at h
    exact h.trans (mul_le_mul_of_nonneg_left hgA (by positivity))
  have hsymm : IsSymmSndFDerivAt ℝ f x := hsmooth.contDiffAt.isSymmSndFDerivAt (by simp)
  have hkey (a b : Fin 3) (hab : a ≤ b) :
      ‖fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)‖ ≤
        Cb 2 * D ^ 2 * A := by
    let β : Fin 2 → Fin 3 := ![a, b]
    have hmono : Monotone β := by
      intro p q hpq
      fin_cases p <;> fin_cases q
      · exact le_rfl
      · exact hab
      · exact absurd hpq (by decide)
      · exact le_rfl
    have h := hcoord 2 g hD hband β hmono x
    rw [iteratedFDeriv_two_apply] at h
    have hβ0 : β 0 = a := rfl
    have hβ1 : β 1 = b := rfl
    simp only [hβ0, hβ1] at h
    exact h.trans (mul_le_mul_of_nonneg_left hgA (by positivity))
  have h2 (i j : Fin 3) :
      ‖fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)‖ ≤
        Cb 2 * D ^ 2 * A := by
    rcases le_total i j with hij | hji
    · exact hkey i j hij
    · rw [hsymm]
      exact hkey j i hji
  have hG : ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
    simpa only [norm_iteratedFDeriv_one] using
      (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := x) (n := 1))
  constructor
  · calc ‖fderiv ℝ f x‖ ≤ ∑ i : Fin 3, ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ :=
          opNorm_le_sum_single _
      _ ≤ ∑ _i : Fin 3, Cb 1 * D * A := Finset.sum_le_sum fun i _ => h1 i
      _ = 3 * Cb 1 * A * D := by simp; ring
  · rw [← hG]
    calc ‖fderiv ℝ (fderiv ℝ f) x‖
        ≤ ∑ i : Fin 3, ‖fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)‖ :=
          opNorm_le_sum_single _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
            ‖fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)‖ :=
          Finset.sum_le_sum fun i _ => opNorm_le_sum_single _
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, Cb 2 * D ^ 2 * A :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h2 i j
      _ = 9 * Cb 2 * A * D ^ 2 := by simp; ring

/-! ## (7.6) from Lemma B.1 -/

/-- Copy of the library's private `norm_fderiv_selfAdvection_le` (ParentVelocityEstimates.lean:75),
unchanged. -/
theorem norm_fderiv_selfAdvection_le {u : Vec3 → Vec3} (hu : ContDiff ℝ 2 u) (x : Vec3) :
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

/-- A `C^{0,1/2}` torus field as a continuous field (copy of the library's private
`continuousRealHalfHolder`, ParentVelocityEstimates.lean:388, unchanged). -/
def realHalfHolder (f : HalfHolder Labels Vec3) : C(Labels, Vec3) :=
  f.val.1.toContinuousMap

/-- Copy of the library's private `norm_continuousRealHalfHolder_le`
(ParentVelocityEstimates.lean), unchanged. -/
theorem norm_realHalfHolder_le (f : HalfHolder Labels Vec3) :
    ‖realHalfHolder f‖ ≤ ‖f‖ :=
  (ContinuousMap.norm_le (realHalfHolder f) (norm_nonneg f)).mpr
    ((HalfHolder.norm_le_iff (norm_nonneg f)).mp le_rfl).1

/-- Copy of the library's private `norm_advectionHalfHolder_le` (ParentVelocityEstimates.lean:508),
unchanged: the `C^{0,1/2}` norm of the advection `∇u·u`. -/
theorem norm_advectionHalfHolder_le {u : Vec3 → Vec3} (hu : ContDiff ℝ 2 u)
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
        exact (Real.le_sqrt dist_nonneg dist_nonneg).mpr
          (by nlinarith [dist_nonneg (x := z) (y := w)])
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

set_option maxHeartbeats 900000 in
/-- (7.6) for a parent in the projected momentum form (sections/08b_induction.tex:205-219):
`‖∇U‖_∞ ≤ λ^9` and `‖∂_t∇U‖_∞ ≤ λ^{18}` on the slab. Copy of the library's
`exists_parentDerivedLowBounds` (ParentVelocityEstimates.lean:567) with Bernstein's inequality
(B.1) from `hB_1` (`bernstein_jets`) in place of `exists_bandBernsteinJetBounds`, and with
(B.1) applied once to the time derivative `∂_tU = -ℙ(∇U·U) + R` (frequencies at most `2λ^5`)
instead of separately to `ℙ(∇U·U)` and `R`. -/
theorem parent_derived_low_bounds (hB_1 : Statement.lemma_B_1) :
    ∃ N : ℝ, 1 ≤ N ∧
      ∀ {T freq freqnext : ℝ}, 0 < T → N ≤ freq → 1 ≤ freqnext →
        ∀ (U R : ℝ → C(Labels, Vec3)) (A : ℝ → HalfHolder Labels Vec3),
          let u : Velocity := fun t x => U t (toUnitTorus x)
          ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)) →
          (∀ t ∈ Icc 0 T, ‖U t‖ ≤ freq ∧ RealTorusFourierBand (2 * freq ^ 5) (U t)) →
          (∀ t ∈ Icc 0 T, ‖R t‖ ≤ freqnext ^ (-3 : ℝ)) →
          (∀ t ∈ Icc 0 T, ∀ x,
            HalfHolder.eval (toUnitTorus x) (A t) = fderiv ℝ (u t) x (u t x)) →
          (∀ t ∈ Icc 0 T, ∀ x, HasDerivWithinAt (fun r => u r x)
            (-HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray (A t)) +
              R t (toUnitTorus x)) (Icc 0 T) t) →
          ∀ t ∈ Icc 0 T, ∀ x : Vec3,
            ‖fderiv ℝ (u t) x‖ ≤ freq ^ 9 ∧
            ‖derivWithin (fun r => fderiv ℝ (u r) x) (Icc 0 T) t‖ ≤ freq ^ 18 := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hBernstein⟩ := bernstein_jets hB_1
  let Cₐ := 2 * (C₁ + C₁ ^ 2 + C₂)
  let Ler := endpointStrongSpatialLeray
  let Cₜ := C₁ * (‖Ler‖ * Cₐ + 1)
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
  have hUs : ContDiff ℝ ∞ (u t) := by
    let e : Vec3 → ℝ × Vec3 := fun x => (t, x)
    exact hSmooth.comp_contDiff (f := e) (contDiff_const.prodMk contDiff_id)
      (fun x => ⟨ht, mem_univ x⟩)
  have hUs2 : ContDiff ℝ 2 (u t) := hUs.of_le (by simp)
  have hUjet (y : Vec3) := hBernstein (U t) hDpos (hU t ht).1 hUB hUs2 y
  have huVal (y : Vec3) : ‖u t y‖ ≤ freq := ((U t).norm_coe_le_norm _).trans (hU t ht).1
  have huGrad (y : Vec3) : ‖fderiv ℝ (u t) y‖ ≤ C₁ * freq * D := (hUjet y).1
  have hPnorm : ‖Ler (A t)‖ ≤ ‖Ler‖ * (Cₐ * (D ^ 2 * freq ^ 2)) := by
    apply (Ler.le_opNorm _).trans (mul_le_mul_of_nonneg_left _ (norm_nonneg _))
    have hb := norm_advectionHalfHolder_le hUs2 (A t)
      hfreqpos.le (show 0 ≤ C₁ * freq * D by positivity)
      (show 0 ≤ C₂ * freq * D ^ 2 by positivity)
      huVal huGrad (fun y => (hUjet y).2) (hA t ht)
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
  constructor
  · calc
      _ ≤ C₁ * freq * D := huGrad x
      _ ≤ freq * freq * D := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC₁freq hfreqpos.le) hDpos.le
      _ ≤ freq ^ 9 := by
        rw [show freq * freq * D = freq ^ 7 by dsimp only [D]; ring]
        exact pow_le_pow_right₀ hfreq₁ (by decide)
  · -- the time derivative `d = ∂_tU(t) = -ℙ(∇U·U) + R` on the torus
    let p : C(Labels, Vec3) := realHalfHolder (Ler (A t))
    let d : C(Labels, Vec3) := -p + R t
    have hdEq (y : Vec3) : HasDerivWithinAt (fun r => U r (toUnitTorus y)) (d (toUnitTorus y))
        (Icc 0 T) t := hEq t ht y
    have hdBand : RealTorusFourierBand (2 * D) d :=
      mFourierCoeff_timeDerivative_eq_zero_outside_band hT U hSmooth
        (fun s hs => (hU s hs).2) ht d hdEq
    have hdBand4 : RealTorusFourierBand (4 * D) d := fun k hk =>
      hdBand k ((show 2 * D ≤ 4 * D by linarith).trans_lt hk)
    have hlift : (fun y => d (toUnitTorus y)) =
        fun y => derivWithin (fun r => u r y) (Icc 0 T) t :=
      funext fun y => ((hdEq y).derivWithin (uniqueDiffOn_Icc hT t ht)).symm
    have hWt : ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => derivWithin (fun r => u r q.2) (Icc 0 T) q.1)
        (Icc 0 T ×ˢ (univ : Set Vec3)) :=
      contDiffOn_sliceTimeDerivWithin_Icc hT hSmooth
    have hdSmooth : ContDiff ℝ 2 (fun y => d (toUnitTorus y)) := by
      rw [hlift]
      let e : Vec3 → ℝ × Vec3 := fun x => (t, x)
      exact (hWt.comp_contDiff (f := e) (contDiff_const.prodMk contDiff_id)
        (fun x => ⟨ht, mem_univ x⟩)).of_le (by simp)
    have hrSmall : freqnext ^ (-3 : ℝ) ≤ D ^ 2 * freq ^ 2 := by
      calc
        _ ≤ freqnext ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hnext (by norm_num)
        _ = 1 := Real.rpow_zero _
        _ ≤ _ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD) (one_le_pow₀ hfreq₁)
    have hdNorm : ‖d‖ ≤ (‖Ler‖ * Cₐ + 1) * (D ^ 2 * freq ^ 2) := by
      calc ‖d‖ ≤ ‖-p‖ + ‖R t‖ := norm_add_le _ _
        _ = ‖p‖ + ‖R t‖ := by rw [norm_neg]
        _ ≤ ‖Ler‖ * (Cₐ * (D ^ 2 * freq ^ 2)) + D ^ 2 * freq ^ 2 :=
          add_le_add ((norm_realHalfHolder_le _).trans hPnorm) ((hR t ht).trans hrSmall)
        _ = _ := by ring
    have hTime := (hasFDerivAt_slabVelocityTimeDerivative hT ht (hSmooth.of_le (by simp)) x).fderiv
    rw [← hlift] at hTime
    rw [← hTime]
    calc
      _ ≤ C₁ * ((‖Ler‖ * Cₐ + 1) * (D ^ 2 * freq ^ 2)) * D :=
        (hBernstein d hDpos hdNorm hdBand4 hdSmooth x).1
      _ = Cₜ * freq ^ 17 := by dsimp only [D, Cₜ]; ring
      _ ≤ freq ^ 18 := by
        rw [show (18 : ℕ) = 1 + 17 by decide, pow_add, pow_one]
        exact mul_le_mul_of_nonneg_right hCₜfreq (by positivity)

/-- (7.6) at the origin for a parent given by its closed-slab projected momentum identity and
residual bound (the data (T1), (T2) of a stage): the construction of the momentum form
`∂_tU = -ℙ(∇U·U) + R` is copied from the library's `exists_parent_projectedMomentum_bounds`
(LaterPhysicalAmplification.lean:545), without its residual-gradient clause (the only place
where it used `exists_bandBernsteinJetBounds`); the bounds are `parent_derived_low_bounds`. -/
theorem stage_derived_low_bounds (hB_1 : Statement.lemma_B_1) :
    ∃ N : ℝ, 1 ≤ N ∧
      ∀ {T old μ : ℝ}, 0 < T → N ≤ old → 1 ≤ μ →
        ∀ (U : ℝ → C(Labels, Vec3)) (R : Velocity),
          let u : Velocity := fun t x => U t (toUnitTorus x)
          ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)) →
          (∀ t ∈ Icc 0 T, ‖U t‖ ≤ old ∧ RealTorusFourierBand (2 * old ^ 5) (U t)) →
          (∀ t ∈ Icc 0 T, ∀ x, divergence (u t) x = 0) →
          (∀ t ∈ Icc 0 T, closedSlabLerayMomentum 0 T u t = R t) →
          (∀ t ∈ Icc 0 T, ∀ x, ‖R t x‖ ≤ (μ⁻¹) ^ (3 : ℕ)) →
          ∀ t ∈ Icc 0 T,
            ‖fderiv ℝ (u t) 0‖ ≤ old ^ 9 ∧
            ‖derivWithin (fun s => fderiv ℝ (u s) 0) (Icc 0 T) t‖ ≤ old ^ 18 := by
  classical
  obtain ⟨N, hN, hLow⟩ := parent_derived_low_bounds hB_1
  refine ⟨N, hN, ?_⟩
  intro T old μ hT hOld hμ₁ U R u hSmooth hU hDiv hMom hR
  let I := Icc (0 : ℝ) T
  let W : Velocity := fun t x => derivWithin (fun s => u s x) I t
  have hPer (t : ℝ) (_ht : t ∈ I) : SpatiallyPeriodic (u t) := fun n x =>
    congrArg (U t) ((toUnitTorus_eq_iff _ _).2 ⟨n, rfl⟩)
  have hSlice {f : Velocity} (h : ContDiffOn ℝ ∞ (Function.uncurry f) (I ×ˢ (univ : Set Vec3)))
      (t : ℝ) (ht : t ∈ I) : ContDiff ℝ ∞ (f t) := by
    let e : Vec3 → ℝ × Vec3 := fun x => (t, x)
    exact h.comp_contDiff (f := e) (contDiff_const.prodMk contDiff_id)
      (fun x => ⟨ht, mem_univ x⟩)
  have hWt : ContDiffOn ℝ ∞ (Function.uncurry W) (I ×ˢ (univ : Set Vec3)) :=
    contDiffOn_sliceTimeDerivWithin_Icc hT hSmooth
  let adv : Velocity := fun t x => fderiv ℝ (u t) x (u t x)
  have hExistsA (t : ℝ) : ∃ a : HalfHolder Labels Vec3,
      t ∈ I → ∀ x, HalfHolder.eval (toUnitTorus x) a = adv t x := by
    by_cases ht : t ∈ I
    · have hUs := hSlice hSmooth t ht
      have hA : ContDiff ℝ ∞ (adv t) := (hUs.fderiv_right (m := ∞) (by simp)).clm_apply hUs
      have hAPer : SpatiallyPeriodic (adv t) := by
        intro n x
        change fderiv ℝ (u t) (x + latticeVector n) (u t (x + latticeVector n)) =
          fderiv ℝ (u t) x (u t x)
        rw [(hPer t ht).fderiv (hUs.differentiable (by simp)) n x, hPer t ht n x]
      obtain ⟨a, ha, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hAPer
        (spatialHolderHalf_zero_of_contDiff_spatiallyPeriodic (hA.of_le (by simp)) hAPer)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => (ht h).elim⟩
  choose A hA using hExistsA
  let S : Velocity := fun t x =>
    HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray (A t))
  have hEq (t : ℝ) (ht : t ∈ I) (x : Vec3) :
      HasDerivWithinAt (fun s => u s x) (R t x - S t x) I t := by
    have hU_s := hSlice hSmooth t ht
    have hX := hasDerivWithinAt_of_closedSlabLerayMomentum hT hSmooth hPer hDiv hMom ht x
    have hAdv : momentumTensorDivergence ∘ fderiv ℝ (fun y => momentumTensor (u t y) (u t y)) =
        adv t :=
      momentumTensorDivergence_self_eq_advection (hU_s.differentiable (by simp)) (hDiv t ht)
    have hTor : periodicLerayHolderLift (adv t) = S t := by
      rw [← funext (hA t ht), periodicLerayHolderLift_pullback]
    rwa [hAdv, hTor] at hX
  have hExistsR (t : ℝ) : ∃ z : C(Labels, Vec3), t ∈ I →
      (∀ x, z (toUnitTorus x) = R t x) ∧ ‖z‖ ≤ μ ^ (-3 : ℝ) := by
    by_cases ht : t ∈ I
    · have hWc : Continuous (W t) := (hSlice hWt t ht).continuous
      have hWper : SpatiallyPeriodic (W t) := fun n x =>
        derivWithin_congr (fun s hs => hPer s hs n x) (hPer t ht n x)
      have hSc : Continuous (S t) :=
        (endpointStrongSpatialLeray (A t)).val.1.continuous.comp
          isOpenQuotientMap_toUnitTorus.continuous
      have hSper : SpatiallyPeriodic (S t) := fun n x =>
        congrArg (fun y => HalfHolder.eval y (endpointStrongSpatialLeray (A t)))
          ((toUnitTorus_eq_iff _ _).2 ⟨n, rfl⟩)
      have hRep : R t = W t + S t := by
        funext x
        exact (sub_eq_iff_eq_add.mp ((hEq t ht x).derivWithin
          (uniqueDiffOn_Icc hT t ht)).symm)
      have hSumPer : SpatiallyPeriodic (W t + S t) := by
        intro n x
        change W t (x + latticeVector n) + S t (x + latticeVector n) = W t x + S t x
        rw [hWper n x, hSper n x]
      obtain ⟨z, hz⟩ := hSumPer.exists_continuousTorusFunction (hWc.add hSc)
      have hzR : ∀ x, z (toUnitTorus x) = R t x := fun x =>
        (hz x).trans (congrFun hRep x).symm
      have hPow : (μ⁻¹) ^ (3 : ℕ) = μ ^ (-3 : ℝ) := by
        rw [inv_pow, Real.rpow_neg (zero_le_one.trans hμ₁), Real.rpow_ofNat]
      have hzBound : ‖z‖ ≤ μ ^ (-3 : ℝ) := by
        apply (ContinuousMap.norm_le z (Real.rpow_nonneg (zero_le_one.trans hμ₁) _)).2
        intro a
        obtain ⟨x, rfl⟩ := isOpenQuotientMap_toUnitTorus.surjective a
        rw [hzR, ← hPow]
        exact hR t ht x
      exact ⟨z, fun _ => ⟨hzR, hzBound⟩⟩
    · exact ⟨0, fun h => (ht h).elim⟩
  choose Rtor hRtor using hExistsR
  have hMomentum (t : ℝ) (ht : t ∈ I) (x : Vec3) :
      HasDerivWithinAt (fun s => u s x)
        (-HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray (A t)) +
          Rtor t (toUnitTorus x)) I t := by
    rw [(hRtor t ht).1 x]
    exact (hEq t ht x).congr_deriv (sub_eq_neg_add _ _)
  intro t ht
  exact hLow hT hOld hμ₁ U Rtor A hSmooth hU (fun s hs => (hRtor s hs).2) hA hMomentum t ht 0

/-! ## The stages of the construction -/

/-- Every slab has positive length: `S_0 = 1` and `S_{j+1} = t_{j+1} + 2τ_j` with `t_{j+1} ≥ 0`,
`τ_j > 0`. -/
theorem slab_pos {P : InductiveEulerParameters} (c : InductiveEulerConstruction P) (n : ℕ) :
    0 < c.stages.slab n := by
  cases n with
  | zero => rw [c.stages.slab_base]; exact one_pos
  | succ n =>
    rw [c.stages.slab_step n]
    have ha : 0 ≤ c.stages.activation (n + 1) := by
      rw [← c.stages.activation_zero]; exact Stages.activation_mono c.stages (Nat.zero_le _)
    have hτ : 0 < inductionHalfLength c.stages.frequency n := (c.lifetime.step n).1
    linarith

/-- The slabs are nested from `S_1` on: `S_{i+2} ≤ S_{i+1}`, since
`t_{i+2} - t_{i+1} ≤ τ_i` and `4τ_{i+1} ≤ τ_i` (sections/08b_induction.tex:258-264). -/
theorem slab_succ_le {P : InductiveEulerParameters} (c : InductiveEulerConstruction P) (i : ℕ) :
    c.stages.slab (i + 2) ≤ c.stages.slab (i + 1) := by
  have h1 := c.stages.slab_step (i + 1)
  have h2 := c.stages.slab_step i
  have ha := (c.stages.activation_step i).2
  have hτ : 0 < inductionHalfLength c.stages.frequency i := (c.lifetime.step i).1
  have h4 : 4 * inductionHalfLength c.stages.frequency (i + 1) ≤
      inductionHalfLength c.stages.frequency i := (c.lifetime.step i).2.2
  rw [h1, h2]
  linarith

/-- (7.6) at the origin for the stages of the construction, for all large `n`: from (T1), (T2)
(the fields of `c.stages`) and Lemma B.1 (`stage_derived_low_bounds hB_1`). -/
theorem eventually_stage_gradient_bounds (hB_1 : Statement.lemma_B_1)
    {P : InductiveEulerParameters} (c : InductiveEulerConstruction P) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc 0 (c.stages.slab n),
      ‖fderiv ℝ (c.stages.velocity n t) 0‖ ≤ c.stages.frequency n ^ 9 ∧
        ‖derivWithin (fun s => fderiv ℝ (c.stages.velocity n s) 0) (Icc 0 (c.stages.slab n)) t‖ ≤
          c.stages.frequency n ^ 18 := by
  obtain ⟨N, -, hBounds⟩ := stage_derived_low_bounds hB_1
  have hinit : 2 ≤ c.stages.frequency 0 := two_le_frequency_zero P
  have hfreq : Tendsto c.stages.frequency atTop atTop :=
    frequencySchedule_frequency_tendsto_atTop c.stages.exponentParameter c.stages.order
      c.stages.frequency c.stages.exponentParameter_ge (one_lt_two.trans_le hinit)
      c.stages.frequency_step
  filter_upwards [hfreq.eventually_ge_atTop N] with n hn
  exact hBounds (slab_pos c n) hn
    (one_le_two.trans (Stages.frequency_lower c.stages hinit (n + 1)))
    (c.stages.torusVelocity n) (c.stages.residual n) (c.stages.smooth n)
    (fun t ht => ⟨c.stages.velocity_bound n t ht, c.stages.velocity_band n t ht⟩)
    (fun t ht x => c.stages.divergence_free n t ht x)
    (fun t ht => c.stages.projected_residual n t ht)
    (fun t ht x => c.stages.residual_bound n t ht x)

/-! ## The comparison error (6.6), from Lemma 2.2 -/

/-- Each frame axis moves with speed at most `2|B|`: copy of the library's
`movingFrame_axis_derivative_bound` (FrameCouplingVariation.lean:12) with the frame equations
(2.2) and the orthonormality of the frame from `h2_2` in place of
`hasDerivWithinAt_movingFrame`. -/
theorem frame_axis_derivative_bound (h2_2 : Statement.lemma_2_2) {J : Set ℝ}
    {B : ℝ → Vec3 →L[ℝ] Vec3} {k a : ℝ → Vec3}
    (htrace : ∀ t ∈ J, LinearMap.trace ℝ Vec3 (B t).toLinearMap = 0) (hWave : WaveOn J B k a)
    (hframe : ∀ t ∈ J, k t ≠ 0 ∧ a t ≠ 0 ∧ ⟪k t, a t⟫_ℝ = 0) {t : ℝ} (ht : t ∈ J)
    (i : Fin 3) :
    ∃ v : Vec3, HasDerivWithinAt (fun u => frame k a u i) v J t ∧ ‖v‖ ≤ 2 * ‖B t‖ := by
  obtain ⟨he, h₁, h₂, h₃, -⟩ := h2_2 htrace hWave hframe t ht
  have hs {c : ℝ} {j : Fin 3} (hc : |c| ≤ ‖B t‖) : ‖c • frame k a t j‖ ≤ ‖B t‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, he.norm_eq_one j, mul_one] using hc
  have hν := MovingWaveVector.coefficient_abs_le_norm he (B t) 0 1
  have hγ := MovingWaveVector.coefficient_abs_le_norm he (B t) 0 2
  have hη := MovingWaveVector.coefficient_abs_le_norm he (B t) 2 1
  fin_cases i
  · refine ⟨_, h₁, (norm_sub_le _ _).trans ?_⟩
    have hneg : |-entry (frame k a t) (B t) 0 1| ≤ ‖B t‖ := by rwa [abs_neg]
    linarith only [hs (j := 1) hneg, hs (j := 2) hγ]
  · refine ⟨_, h₂, (norm_sub_le _ _).trans ?_⟩
    linarith only [hs (j := 0) hν, hs (j := 2) hη]
  · refine ⟨_, h₃, (norm_add_le _ _).trans ?_⟩
    linarith only [hs (j := 0) hγ, hs (j := 1) hη]

/-- The comparison error (2.6) is nonnegative. -/
theorem errorSize_nonneg {I : Set ℝ} {t₀ : ℝ} (w : PhysicalAmplification I t₀) :
    0 ≤ w.errorSize := by
  have hν := w.first_coupling_positive
  have hr := w.rate_pos
  unfold PhysicalAmplification.errorSize amplificationPhysicalError
  refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) (div_nonneg ?_ hr.le)) (div_nonneg ?_ hν.le) <;>
    exact Real.sSup_nonneg (by rintro _ ⟨s, -, rfl⟩; positivity)

/-- The error estimate (6.6) (sections/08b_induction.tex:39-50) for a physical amplification
window with the older gradient `B`, its time derivative `B_t` and the perturbation `E_c`
bounded: `δ ≤ 8[(T-t_0)(|B|^2 + |B_t|)/η + |B|/r + |E_c|/ν]`. Copy of the library's
`PhysicalAmplification.errorSize_le_of_older_gradient` (LaterPhysicalAmplification.lean:123),
with the frame equations (2.2) from `h2_2` (`frame_axis_derivative_bound`) in place of
`hasDerivWithinAt_movingFrame`; only the upper bound is kept. -/
theorem errorSize_le (h2_2 : Statement.lemma_2_2) {t₀ finish Bmax Btmax Emax : ℝ}
    (w : PhysicalAmplification (Icc t₀ finish) t₀) (hRatio : w.ratio ≤ 1)
    (Bt : ℝ → Vec3 →L[ℝ] Vec3)
    (hBd : ∀ t ∈ Icc t₀ finish, HasDerivWithinAt w.B (Bt t) (Icc t₀ finish) t)
    (hB : ∀ t ∈ Icc t₀ finish, ‖w.B t‖ ≤ Bmax)
    (hBt : ∀ t ∈ Icc t₀ finish, ‖Bt t‖ ≤ Btmax)
    (hE : ∀ t ∈ Icc t₀ finish, ‖w.E t‖ ≤ Emax) :
    w.errorSize ≤ 8 * ((finish - t₀) * (Bmax ^ 2 + Btmax) / w.thirdCoupling +
      Bmax / w.rate + Emax / w.firstCoupling) := by
  have hWave : WaveOn (Icc t₀ finish) w.B w.kp w.ap :=
    ⟨w.preceding_vector, fun s hs => by
      simpa only [affineWaveAmplitudeOperator_apply, affineWavePressureCoeff] using
        w.preceding_amplitude s hs⟩
  have hη : w.thirdCoupling ≤ w.firstCoupling := by
    have h := (div_le_iff₀ w.first_coupling_positive).mp hRatio
    rwa [one_mul] at h
  exact MovingWaveVector.amplificationPhysicalError_le_of_frame_rate w.activation.2 w.rate_pos
    (fun u hu => (h2_2 w.trace_zero hWave w.preceding_data u hu).1)
    (fun u hu i => by
      obtain ⟨v, hv, hn⟩ :=
        frame_axis_derivative_bound h2_2 w.trace_zero hWave w.preceding_data hu i
      exact ⟨v, hv, hn.trans (mul_le_mul_of_nonneg_left (hB u hu) (by norm_num))⟩)
    hBd hB hBt hE w.third_coupling_positive hη

/-! ## (2.7) for wave `j` at every constant -/

set_option maxHeartbeats 900000 in
/-- **The comparison hypotheses (2.7) of every later wave, for every constant `C₀` and all large
`j`** (item 2 of the proof of Theorem 7.1, sections/08b_induction.tex:312-326, read by the proof
of Proposition 8.2 at 09b:25-27). For the physical amplification `w.physical j` of wave `j + 2`
(older gradient `B = ∇U_j(t,0)` on `[t_{j+2}, S_{j+2}]`, `μ = λ_{j+1}`):

* (7.6) at `j` (`eventually_stage_gradient_bounds hB_1`): `|B| ≤ λ_j^9`, `|B_t| ≤ λ_j^{18}`;
  `|E_c| ≤ μ^{-1/4}` from (T4) (`error_bound`);
* (6.6) (`errorSize_le h2_2`) with `T - t_0 = 2τ_{j+1}` and `η = εν`;
* the frozen strength and coupling (7.3) give `cμ^{1/8} ≤ r ≤ Cμ^{1/8}L`
  (`activationGrowthRate_bounds`), and the window is `2rτ_{j+1}` (`physical_window`);
* (1.15) from `h1_3` gives `LNext ≤ (log μ)^2`;
* the absorption `C₀(2rτ)^{C₀}δ ≤ ε`, `C₀ε ≤ 1` for `μ` above a threshold depending on `C₀`
  is `exists_induction_amplification_step_comparison`. -/
theorem eventually_finiteSmallness (h1_3 : Statement.lemma_1_3) (h2_2 : Statement.lemma_2_2)
    (hB_1 : Statement.lemma_B_1) {P : InductiveEulerParameters} (c : InductiveEulerConstruction P)
    (C₀ : ℕ) :
    ∀ᶠ j in atTop, FiniteSmallness (c.centralWaves.physical j) (c.centralWaves.window j) C₀ := by
  set s := c.stages with hs
  set w := c.centralWaves with hw
  have hinit : 2 ≤ s.frequency 0 := two_le_frequency_zero P
  have hC := zero_lt_two.trans_le w.strengthConstant_ge
  obtain ⟨N₀, -, hcomp⟩ := exists_induction_amplification_step_comparison C₀ 8
    (Real.sqrt (2 * w.strengthConstant⁻¹ * Real.pi)) (Real.sqrt (8 * w.strengthConstant * Real.pi))
    (by norm_num) (Real.sqrt_pos.mpr (by positivity [Real.pi_pos])) (Real.sqrt_nonneg _)
  obtain ⟨-, hlog⟩ := lemma13_schedule h1_3 P
  have hfreq : Tendsto s.frequency atTop atTop :=
    frequencySchedule_frequency_tendsto_atTop s.exponentParameter s.order s.frequency
      s.exponentParameter_ge (one_lt_two.trans_le hinit) s.frequency_step
  filter_upwards [eventually_stage_gradient_bounds hB_1 c,
    (hfreq.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop N₀, eventually_ge_atTop 1]
    with j hOld hμN hj1
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  set Pj := w.physical (i + 1) with hPj
  have hlow := Stages.frequency_lower s hinit
  have hmono := Stages.frequency_mono s hinit
  set μ := s.frequency (i + 2) with hμdef
  set L := 4 * Real.log (s.frequency (i + 4)) with hLdef
  set LNext := 4 * Real.log (s.frequency (i + 5)) with hLNextdef
  have hμ : 0 < μ := zero_lt_two.trans_le (hlow _)
  have hlogpos (n : ℕ) : 0 ≤ Real.log (s.frequency n) :=
    Real.log_nonneg (one_le_two.trans (hlow n))
  have hlogmono {m n : ℕ} (h : m ≤ n) : Real.log (s.frequency m) ≤ Real.log (s.frequency n) :=
    Real.log_le_log (zero_lt_two.trans_le (hlow m)) (hmono h)
  have hL : 0 ≤ L := mul_nonneg (by norm_num) (hlogpos _)
  -- the rate `r` of the frozen strength and coupling (7.3)
  have hStrength := w.strength_at_crossing (i + 1)
  rw [← CentralWaves.initial_strength_eq] at hStrength
  have hCoupling := w.coupling_at_crossing (i + 1)
  dsimp only at hCoupling
  rw [← CentralWaves.first_coupling_eq] at hCoupling
  obtain ⟨hrLo, hrHi⟩ := activationGrowthRate_bounds hμ hL (inv_pos.mpr hC) hC
    hStrength.1 hStrength.2 hCoupling.1 hCoupling.2
  -- the window is `2rτ_{j+1}`
  have hSlab : s.slab (i + 3) = s.activation (i + 3) + 2 * inductionHalfLength s.frequency (i + 2) :=
    s.slab_step (i + 2)
  have hTime : w.window (i + 1) = 2 * Pj.rate * inductionHalfLength s.frequency (i + 2) := by
    have h := (w.physical_window (i + 1)).trans hSlab
    have hd : w.window (i + 1) / Pj.rate = 2 * inductionHalfLength s.frequency (i + 2) := by
      change s.activation (i + 3) + w.window (i + 1) / Pj.rate =
        s.activation (i + 3) + 2 * inductionHalfLength s.frequency (i + 2) at h
      exact add_left_cancel h
    calc
      w.window (i + 1) = (w.window (i + 1) / Pj.rate) * Pj.rate :=
        (div_mul_cancel₀ _ Pj.rate_pos.ne').symm
      _ = _ := by rw [hd]; ring
  -- the window lies in the slabs of `U_{j}` and of the preceding wave
  have hact (n : ℕ) : 0 ≤ s.activation n := by
    rw [← s.activation_zero]; exact Stages.activation_mono s (Nat.zero_le n)
  have hactmono := Stages.activation_mono s
  have hS32 : s.slab (i + 3) ≤ s.slab (i + 2) := slab_succ_le c (i + 1)
  have hS21 : s.slab (i + 2) ≤ s.slab (i + 1) := slab_succ_le c i
  have hI : Icc (s.activation (i + 3)) (s.slab (i + 3)) ⊆ Icc 0 (s.slab (i + 1)) :=
    Icc_subset_Icc (hact _) (hS32.trans hS21)
  have hIE : Icc (s.activation (i + 3)) (s.slab (i + 3)) ⊆
      Icc (s.activation (i + 2)) (s.slab (i + 2)) :=
    Icc_subset_Icc (hactmono (by omega)) hS32
  have htI : s.activation (i + 3) ≤ s.slab (i + 3) := Pj.activation.2
  -- the older gradient `B = ∇U_j(t,0)` and its time derivative on the window
  have hRaw := older_central_gradient_raw_bounds_of_derivedLowBounds
    (u := s.velocity (i + 1)) (slab_pos c (i + 1)) (hact (i + 3)) (hS32.trans hS21)
    ((s.smooth (i + 1)).of_le (by simp)) hOld
  set Bt : ℝ → Vec3 →L[ℝ] Vec3 := fun t =>
    derivWithin (fun r => fderiv ℝ (s.velocity (i + 1) r) 0) (Icc 0 (s.slab (i + 1))) t with hBt
  have hBd : ∀ t ∈ Icc (s.activation (i + 3)) (s.slab (i + 3)),
      HasDerivWithinAt Pj.B (Bt t) (Icc (s.activation (i + 3)) (s.slab (i + 3))) t := fun t ht =>
    (hRaw t ht).1.congr_of_mem (fun r hr => w.older_gradient (i + 1) r hr) ht
  have hB : ∀ t ∈ Icc (s.activation (i + 3)) (s.slab (i + 3)),
      ‖Pj.B t‖ ≤ s.frequency (i + 1) ^ 9 := fun t ht => by
    rw [w.older_gradient (i + 1) t ht]; exact (hRaw t ht).2.1
  have hBtb : ∀ t ∈ Icc (s.activation (i + 3)) (s.slab (i + 3)),
      ‖Bt t‖ ≤ s.frequency (i + 1) ^ 18 := fun t ht => (hRaw t ht).2.2
  have hE : ∀ t ∈ Icc (s.activation (i + 3)) (s.slab (i + 3)),
      ‖Pj.E t‖ ≤ μ ^ (-1 / 4 : ℝ) := fun t ht => by
    rw [w.preceding_error (i + 1) t ht]; exact w.error_bound (i + 1) t (hIE ht)
  -- the ratio `ε = η/ν`
  have hεdef : Pj.ratio = couplingRatioOfGain L := w.prescribed_ratio (i + 1)
  have hεpos : 0 < Pj.ratio := Pj.ratio_pos
  have hRatio : Pj.ratio ≤ 1 := by
    have h := w.comparison_ratio (i + 1)
    have hcc : (1 : ℝ) ≤ w.comparisonConstant := by
      exact_mod_cast (show 1 ≤ w.comparisonConstant by have := w.comparisonConstant_ge; omega)
    nlinarith
  have hν := Pj.first_coupling_positive
  have hν0 : Pj.firstCoupling ≠ 0 := hν.ne'
  have hηeq : Pj.thirdCoupling = Pj.firstCoupling * couplingRatioOfGain L := by
    rw [← hεdef]
    unfold MovingWaveVector.PhysicalAmplification.ratio
    field_simp
  -- (6.6)
  have hδ := errorSize_le h2_2 Pj hRatio Bt hBd hB hBtb hE
  have hδ' : Pj.errorSize ≤ 8 * (2 * (μ ^ (-1 / 8 : ℝ) * LNext ^ 3) *
      ((s.frequency (i + 1) ^ 9) ^ 2 + s.frequency (i + 1) ^ 18) /
        (Pj.firstCoupling * couplingRatioOfGain L) +
      s.frequency (i + 1) ^ 9 / Pj.rate + μ ^ (-1 / 4 : ℝ) / Pj.firstCoupling) := by
    have hlen : s.slab (i + 3) - s.activation (i + 3) = 2 * (μ ^ (-1 / 8 : ℝ) * LNext ^ 3) := by
      rw [hSlab]; unfold inductionHalfLength; ring
    rw [hlen, hηeq] at hδ
    exact hδ
  -- the gains
  have hlogL : Real.log μ ≤ L := by
    have h := hlogmono (show i + 2 ≤ i + 4 by omega)
    have h0 := hlogpos (i + 2)
    rw [hLdef]; linarith
  have hLL : L ≤ LNext := by
    rw [hLdef, hLNextdef]
    exact mul_le_mul_of_nonneg_left (hlogmono (by omega)) (by norm_num)
  have hLNext : LNext ≤ Real.log μ ^ 2 := hlog (i + 2)
  have hν1 : 1 ≤ Pj.firstCoupling := by linarith [hCoupling.1, Real.pi_gt_three]
  obtain ⟨-, h1, h2⟩ := hcomp (old := s.frequency (i + 1)) (μ := μ) (ν := Pj.firstCoupling)
    (r := Pj.rate) (L := L) (LNext := LNext) (B := s.frequency (i + 1) ^ 9)
    (Bt := s.frequency (i + 1) ^ 18) (E := μ ^ (-1 / 4 : ℝ)) (δ := Pj.errorSize)
    (b := s.exponentParameter) (q := s.order (i + 2)) hμN s.exponentParameter_ge
    (one_le_two.trans (hlow _)) (s.frequency_step (i + 1)) hν1 hrLo hrHi hlogL hLL hLNext
    (pow_nonneg (zero_le_two.trans (hlow _)) _) le_rfl le_rfl le_rfl (errorSize_nonneg Pj) hδ'
  refine ⟨?_, ?_⟩
  · rw [hεdef]; exact h1
  · rw [hεdef, hTime]
    have hhalf : inductionHalfLength s.frequency (i + 2) = μ ^ (-1 / 8 : ℝ) * LNext ^ 3 := rfl
    rw [hhalf]
    exact h2


/-! ## The window bound of item 2 (08b:304-311), read by 09b:28

Glue for the field `window_upper` of `Theorem71Conclusions` (package S678a): unchanged copies of the
library's private declarations, moved here from `CurlBound.lean`. -/

namespace CentralWaves

variable {s : InductiveEulerStages} (w : InductiveEulerCentralWaves s)

/-- Copy of the library's private `windowConstant`: `2(8Cπ)^{1/2}`. -/
noncomputable def windowConstant : ℝ := 2 * Real.sqrt (8 * w.strengthConstant * Real.pi)

/-- The window constant is positive. -/
theorem windowConstant_pos : 0 < windowConstant w := by
  have h : 0 < w.strengthConstant := zero_lt_two.trans_le w.strengthConstant_ge
  unfold windowConstant
  positivity [Real.pi_pos]

/-- Copy of the library's private `physical_window_upper`: the normalized length of
`[t_j, S_j]` is at most `C L_{j+1}^4` (item 2 of the proof of Theorem 7.1, 08b:304-311, read
by 09b:28). -/
theorem physical_window_upper (hinit : 2 ≤ s.frequency 0) (j : ℕ) :
    w.window j ≤ windowConstant w * (4 * Real.log (s.frequency (j + 4))) ^ 4 := by
  let μ := s.frequency (j + 1)
  let L := 4 * Real.log (s.frequency (j + 3))
  let LNext := 4 * Real.log (s.frequency (j + 4))
  let P := w.physical j
  have hμ : 0 < μ := zero_lt_two.trans_le (Stages.frequency_lower s hinit (j + 1))
  have hL : 0 ≤ L := mul_nonneg (by norm_num)
    (Real.log_nonneg (one_le_two.trans (Stages.frequency_lower s hinit (j + 3))))
  have hLNext : 0 ≤ LNext := mul_nonneg (by norm_num)
    (Real.log_nonneg (one_le_two.trans (Stages.frequency_lower s hinit (j + 4))))
  have hLle : L ≤ LNext := mul_le_mul_of_nonneg_left
    (Real.log_le_log (zero_lt_two.trans_le (Stages.frequency_lower s hinit (j + 3)))
      (Stages.frequency_mono s hinit (by omega))) (by norm_num)
  have hC := zero_lt_two.trans_le w.strengthConstant_ge
  have hStrength := w.strength_at_crossing j
  rw [← initial_strength_eq] at hStrength
  have hCoupling := w.coupling_at_crossing j
  dsimp only at hCoupling
  rw [← first_coupling_eq] at hCoupling
  obtain ⟨hrLo, hrHi⟩ := activationGrowthRate_bounds hμ hL (inv_pos.mpr hC) hC
    hStrength.1 hStrength.2 hCoupling.1 hCoupling.2
  have hTime : w.window j = 2 * P.rate * inductionHalfLength s.frequency (j + 1) := by
    have h := (w.physical_window j).trans (s.slab_step (j + 1))
    have hd : w.window j / P.rate = 2 * inductionHalfLength s.frequency (j + 1) := by
      change s.activation (j + 2) + w.window j / P.rate =
        s.activation (j + 2) + 2 * inductionHalfLength s.frequency (j + 1) at h
      exact add_left_cancel h
    calc
      w.window j = (w.window j / P.rate) * P.rate := (div_mul_cancel₀ _ P.rate_pos.ne').symm
      _ = _ := by rw [hd]; ring
  rw [hTime]
  exact (induction_normalized_comparison_window hμ (Real.sqrt_nonneg _) hLNext hLle hrLo hrHi).2

end CentralWaves

end

end TorusEuler.Paper.Lib.S678b
