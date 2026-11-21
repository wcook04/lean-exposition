import TorusEuler.PhaseJetBounds
import TorusEuler.ParentCoframeEstimates
import TorusEuler.FourierHolderTail
import TorusEuler.WaveDivergence
import TorusEuler.HierarchyLinearRelayBounds

/-!
The Eulerian evaluation and quantitative bounds in frozen Lemmas 5.7 and
5.8, in `paper/craik_criminale_rewrite/sections/08_exact_wave.tex`.
-/

open ContinuousLinearMap Filter Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform Eulerian jets through order `m+1` give the full spatial
half-Hölder norm through order `m`. -/
theorem spatialHolderHalfNorm_le_of_uniformJets {g : Vec3 → E} {m : ℕ} {B : ℝ}
    (hg : ContDiff ℝ ∞ g) (hB : 0 ≤ B)
    (hjet : ∀ j ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    SpatialHolderHalf m g ∧ spatialHolderHalfNorm m g ≤ (3 * (m + 1) : ℝ) * B := by
  have hroot : Real.sqrt (2 * B * B) ≤ 2 * B :=
    (Real.sqrt_le_left (by positivity)).mpr (by nlinarith [sq_nonneg B])
  have hq (j : ℕ) (hj : j ≤ m) (p : Vec3 × Vec3) :
      spatialHolderHalfQuotient (iteratedFDeriv ℝ j g) p ≤ 2 * B := by
    by_cases hp : p.2 = 0
    · simp only [spatialHolderHalfQuotient, hp, add_zero, sub_self, norm_zero, zero_div]
      positivity
    · have h := norm_iteratedFDeriv_sub_le_sqrt hg hB hB
        (hjet j (by omega)) (hjet (j + 1) (Nat.succ_le_succ hj)) (p.1 + p.2) p.1
      rw [add_sub_cancel_left] at h
      exact (div_le_iff₀ (Real.sqrt_pos_of_pos (norm_pos_iff.mpr hp))).2
        (h.trans (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)))
  refine ⟨⟨hg.of_le (by simp), fun j hj => ⟨
    ⟨B, forall_mem_range.mpr (hjet j (by omega))⟩, ⟨2 * B, forall_mem_range.mpr (hq j hj)⟩⟩⟩, ?_⟩
  unfold spatialHolderHalfNorm
  calc
    _ ≤ ∑ _ ∈ Finset.range (m + 1), (B + 2 * B) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hj' : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact add_le_add (ciSup_le (hjet j (by omega))) (ciSup_le (hq j hj'))
    _ = _ := by simp; ring

/-- The inverse coframe bound from Proposition 5.1 loses only one fixed
power of the parent parameter after label derivatives are weighted. -/
theorem scaledCoframe_jet_bound {B : Vec3 → Vec3 →L[ℝ] Vec3} {ell D L : ℝ} {n : ℕ}
    (hell : 0 ≤ ell) (hD : 1 ≤ D) (hL : 0 ≤ L) (hscale : ell * D ^ (7 : ℕ) ≤ 1)
    (hB : ∀ j ≤ n, ∀ a, ‖iteratedFDeriv ℝ j B a‖ ≤ L * D ^ (7 * j + 1)) :
    ∀ j ≤ n, ∀ a, ell ^ j * ‖iteratedFDeriv ℝ j B a‖ ≤ L * D := by
  intro j hj a
  have hpos : 0 ≤ D := zero_le_one.trans hD
  calc
    _ ≤ ell ^ j * (L * D ^ (7 * j + 1)) :=
      mul_le_mul_of_nonneg_left (hB j hj a) (pow_nonneg hell _)
    _ = (ell * D ^ (7 : ℕ)) ^ j * (L * D) := by
      rw [pow_add, pow_one, mul_pow, ← pow_mul]
      ring
    _ ≤ _ := mul_le_of_le_one_left (mul_nonneg hL hpos)
      (pow_le_one₀ (by positivity) hscale)

/-- The transported derivative has a label cost and a phase cost. The
frozen carrier and width bounds put both at one fixed parent power times
`λ^(3/2)`. -/
theorem physicalHierarchy_graph_cost {ell h D freq : ℝ} {a : ℕ} {k : Vec3}
    (hD : 1 ≤ D) (hf : 1 ≤ freq)
    (hLabel : ell⁻¹ ≤ D ^ a) (hWidth : h = freq ^ (-1 / 2 : ℝ))
    (hCarrier : ‖k‖ ≤ D * freq) :
    ell⁻¹ + h⁻¹ * ‖k‖ ≤ 2 * D ^ max a 1 * freq ^ (3 / 2 : ℝ) := by
  have hf₀ := zero_lt_one.trans_le hf
  have hwidth : h⁻¹ = freq ^ (1 / 2 : ℝ) := by
    rw [hWidth, show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hf₀.le, inv_inv]
  have hDpow : D ≤ D ^ max a 1 := by
    conv_lhs => rw [← pow_one D]
    exact pow_le_pow_right₀ hD (le_max_right _ _)
  have hfreq : 1 ≤ freq ^ (3 / 2 : ℝ) := Real.one_le_rpow hf (by norm_num)
  have hLabel' : ell⁻¹ ≤ D ^ max a 1 * freq ^ (3 / 2 : ℝ) :=
    (hLabel.trans (pow_le_pow_right₀ hD (le_max_left _ _))).trans
      (le_mul_of_one_le_right (by positivity) hfreq)
  have hPhase : h⁻¹ * ‖k‖ ≤ D ^ max a 1 * freq ^ (3 / 2 : ℝ) := calc
    _ ≤ freq ^ (1 / 2 : ℝ) * (D ^ max a 1 * freq) := by
      rw [hwidth]
      gcongr
      exact hCarrier.trans (mul_le_mul_of_nonneg_right hDpow hf₀.le)
    _ = _ := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hf₀, Real.rpow_one]
      ring
  linarith only [hLabel', hPhase]

/-- A common jet bound for the actual phase graph. The constants in front
of the graph cost depend only on the derivative order. -/
theorem transportedHierarchyProfile_jetBound {A : Velocity} {k : Vec3}
    {t ell h C gamma M Q : ℝ} {B : Vec3 → Vec3 →L[ℝ] Vec3}
    {f : ℝ → Vec3 → ℝ → E} {n : ℕ}
    (hell : 0 < ell) (hh : 0 < h) (hC : 0 ≤ C) (hgamma : 0 ≤ gamma) (hM : 0 ≤ M)
    (hQ : 1 ≤ Q) (hcost : (ell⁻¹ + h⁻¹ * ‖k‖) * C ≤ Q)
    (hA : ContDiff ℝ ∞ (A t))
    (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x) (hBreg : ContDiff ℝ ∞ B)
    (hf : ContDiff ℝ ∞ (Function.uncurry (f t)))
    (hcoeff : ∀ j ≤ n, ∀ a, ell ^ j * ‖iteratedFDeriv ℝ j B a‖ ≤ C)
    (hprofile : PhaseJetBound n (gamma * M) (scaledPhaseProfile ell h (f t))) :
    PhaseJetBound n (((3 : ℝ) * (2 : ℝ) ^ n) ^ n * Q ^ n * (gamma * M))
      (transportedProfile A k f t) := by
  intro j hj x
  have hraw := norm_iteratedFDeriv_transportedProfile_le (k := k)
    hell hh hC hgamma hM hA hB hBreg hf j
    (fun i hi => hcoeff i (hi.trans hj)) (hprofile.mono_order hj) x
  have hbase : (2 : ℝ) ^ j * ((ell⁻¹ + h⁻¹ * ‖k‖) * C) ≤ (2 : ℝ) ^ n * Q :=
    mul_le_mul (pow_le_pow_right₀ (by norm_num) hj) hcost (by positivity) (by positivity)
  have hbase' : 1 ≤ (2 : ℝ) ^ n * Q :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hQ
  have hpower : ((2 : ℝ) ^ j * ((ell⁻¹ + h⁻¹ * ‖k‖) * C)) ^ j ≤ ((2 : ℝ) ^ n * Q) ^ n :=
    (pow_le_pow_left₀ (by positivity) hbase _).trans (pow_le_pow_right₀ hbase' hj)
  calc
    _ ≤ (3 : ℝ) ^ j * (((2 : ℝ) ^ j * ((ell⁻¹ + h⁻¹ * ‖k‖) * C)) ^ j * (gamma * M)) := hraw
    _ ≤ (3 : ℝ) ^ n * (((2 : ℝ) ^ n * Q) ^ n * (gamma * M)) :=
      mul_le_mul (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hj)
        (mul_le_mul_of_nonneg_right hpower (by positivity)) (by positivity) (by positivity)
    _ = _ := by rw [mul_pow, mul_pow]; ring

/-- The Eulerian evaluation on the torus. The mean is periodic in the
labels and the oscillation is extended from the centered cell. -/
def periodicHierarchyProfile (A : Velocity) (k : Vec3)
    (f : ℝ → Vec3 → ℝ → E) (mean : ℝ → Vec3 → E) (t : ℝ) : Vec3 → E :=
  mean t ∘ A t + localizedTransportedProfile A k (fun s a q => f s a q - mean s a) t

private theorem closure_interior_centeredCell : closure (interior centeredCell) = centeredCell := by
  have hconv : Convex ℝ centeredCell := by
    have heq : centeredCell = ⋂ i : Fin 3, (fun x : Vec3 => x i) ⁻¹' Icc (-(1 / 2 : ℝ)) (1 / 2) := by
      ext x
      simp [centeredCell]
    rw [heq]
    exact convex_iInter fun i => (convex_Icc _ _).linear_preimage
      (EuclideanSpace.proj (𝕜 := ℝ) i).toLinearMap
  have hz : (0 : Vec3) ∈ interior centeredCell := by
    apply mem_interior_iff_mem_nhds.mpr
    apply mem_of_superset (Metric.ball_mem_nhds (0 : Vec3) (show 0 < 1 / 2 by norm_num))
    intro x hx i
    have hnorm : ‖x‖ < (1 : ℝ) / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact abs_le.mp ((PiLp.norm_apply_le x i).trans hnorm.le)
  rw [hconv.closure_interior_eq_closure_of_nonempty_interior ⟨0, hz⟩,
    isCompact_centeredCell.isClosed.closure_eq]

/-- The Eulerian jet bound passes to the actual smooth periodic extension
without any loss in the constant, including at cell faces. -/
theorem periodicHierarchyProfile_jetBound {A : Velocity} {X : Vec3 → Vec3} {k : Vec3}
    {t delta M : ℝ} {f : ℝ → Vec3 → ℝ → E} {mean : ℝ → Vec3 → E} {m : ℕ}
    (hA : ContDiff ℝ ∞ (A t)) (hX : Continuous X)
    (hLeft : Function.LeftInverse X (A t)) (hRight : Function.LeftInverse (A t) X)
    (hAper : ∀ n : Fin 3 → ℤ, ∀ x, A t (x + latticeVector n) = A t x + latticeVector n)
    (hf : ContDiff ℝ ∞ (Function.uncurry (f t))) (hmean : ContDiff ℝ ∞ (mean t))
    (hmeanPer : SpatiallyPeriodic (mean t))
    (hdelta : 0 < delta) (hdelta' : delta ≤ 1 / 2)
    (hcollar : ∀ a, (∃ i : Fin 3, 1 / 2 - delta < |a i|) → ∀ q, f t a q = mean t a)
    (hjet : PhaseJetBound m M (transportedProfile A k f t)) :
    ContDiff ℝ ∞ (periodicHierarchyProfile A k f mean t) ∧
      SpatiallyPeriodic (periodicHierarchyProfile A k f mean t) ∧
      PhaseJetBound m M (periodicHierarchyProfile A k f mean t) := by
  let osc := fun s a q => f s a q - mean s a
  let g := periodicHierarchyProfile A k f mean t
  have hzero (a : Vec3) (ha : ∃ i : Fin 3, 1 / 2 - delta < |a i|) :
      osc t a ⟪k, a⟫_ℝ = 0 := sub_eq_zero.mpr (hcollar a ha _)
  have hosc : ContDiff ℝ ∞ (fun a => osc t a ⟪k, a⟫_ℝ) := by
    exact (hf.sub (hmean.comp contDiff_fst)).comp (contDiff_id.prodMk (innerSL ℝ k).contDiff)
  have hg : ContDiff ℝ ∞ g := (hmean.comp hA).add
    (contDiff_localizedTransportedProfile hA hdelta hdelta' hosc hzero)
  have hperMean : SpatiallyPeriodic (mean t ∘ A t) := by
    intro n x
    simp only [Function.comp_apply, hAper n x, hmeanPer n (A t x)]
  have hperOsc := spatiallyPeriodic_localizedTransportedProfile hAper k osc
  have hper : SpatiallyPeriodic g := by
    intro n x
    exact congrArg₂ (· + ·) (hperMean n x) (hperOsc n x)
  have hLocal (x : Vec3) (hx : A t x ∈ interior centeredCell) :
      g =ᶠ[𝓝 x] transportedProfile A k f t := by
    have heq := localizedTransportedProfile_eventuallyEq hA.continuous.continuousAt hx hdelta hzero
    filter_upwards [heq] with y hy
    change mean t (A t y) + localizedTransportedProfile A k osc t y = _
    rw [hy]
    change mean t (A t y) + (f t (A t y) ⟪k, A t y⟫_ℝ - mean t (A t y)) =
      f t (A t y) ⟪k, A t y⟫_ℝ
    abel
  refine ⟨hg, hper, fun j hj x => ?_⟩
  let S : Set Vec3 := {z | ‖iteratedFDeriv ℝ j g z‖ ≤ M}
  have hS : IsClosed S :=
    isClosed_le (hg.continuous_iteratedFDeriv (m := j) (by simp)).norm continuous_const
  have hImage : X '' interior centeredCell ⊆ S := by
    rintro _ ⟨a, ha, rfl⟩
    have h := ((hLocal (X a) (by rwa [hRight])).iteratedFDeriv ℝ j).eq_of_nhds
    change ‖iteratedFDeriv ℝ j g (X a)‖ ≤ M
    rw [h]
    exact hjet j hj _
  obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell (A t x)
  have hArep : A t (x - latticeVector n) = A t x - latticeVector n := by
    have heq := hAper n (x - latticeVector n)
    rw [sub_add_cancel] at heq
    rw [heq, add_sub_cancel_right]
  have hrep : x - latticeVector n ∈ S := by
    have hnear : A t (x - latticeVector n) ∈ closure (interior centeredCell) := by
      rwa [closure_interior_centeredCell, hArep]
    have himg : X (A t (x - latticeVector n)) ∈ closure (X '' interior centeredCell) :=
      image_closure_subset_closure_image hX (mem_image_of_mem X hnear)
    rw [hLeft] at himg
    exact closure_minimal hImage hS himg
  have hperiodicDeriv : iteratedFDeriv ℝ j g x = iteratedFDeriv ℝ j g (x - latticeVector n) := by
    have hcomp : (fun y => g (y + latticeVector n)) = g := funext (hper n)
    have h := congrArg (fun F : Vec3 → E => iteratedFDeriv ℝ j F (x - latticeVector n)) hcomp
    rw [iteratedFDeriv_comp_add_right, sub_add_cancel] at h
    exact h
  change ‖iteratedFDeriv ℝ j g x‖ ≤ M
  rw [hperiodicDeriv]
  exact hrep

/-- The improved estimate for a phase-independent component follows
from the same chain rule with zero carrier. -/
theorem transportedHierarchyMean_jetBound {A : Velocity}
    {t ell C M Q : ℝ} {B : Vec3 → Vec3 →L[ℝ] Vec3}
    {mean : Vec3 → E} {n : ℕ}
    (hell : 0 < ell) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hQ : 1 ≤ Q) (hcost : ell⁻¹ * C ≤ Q)
    (hA : ContDiff ℝ ∞ (A t))
    (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x) (hBreg : ContDiff ℝ ∞ B)
    (hmean : ContDiff ℝ ∞ mean)
    (hcoeff : ∀ j ≤ n, ∀ a, ell ^ j * ‖iteratedFDeriv ℝ j B a‖ ≤ C)
    (hprofile : PhaseJetBound n M (scaledPhaseProfile ell 1 (fun a _ => mean a))) :
    PhaseJetBound n (((3 : ℝ) * (2 : ℝ) ^ n) ^ n * Q ^ n * M) (mean ∘ A t) := by
  have h := transportedHierarchyProfile_jetBound
    (t := t) (k := 0) (h := 1) (gamma := 1) (f := fun _ a _ => mean a)
    hell zero_lt_one hC zero_le_one hM hQ
    (by simpa only [norm_zero, mul_zero, add_zero] using hcost) hA hB hBreg
    (hmean.comp contDiff_fst) hcoeff (by simpa only [one_mul] using hprofile)
  have heq : transportedProfile A 0 (fun _ a _ => mean a) t = mean ∘ A t := by
    funext x
    simp [transportedProfile]
  rw [heq, one_mul] at h
  exact h

/-- The Hölder version of Lemma 5.7 for the actual torus evaluation.
Here the bound on the weighted label profile is at order `m+1`. -/
theorem periodicHierarchyProfile_holder_of_jetBound {A : Velocity} {X : Vec3 → Vec3} {k : Vec3}
    {t delta M : ℝ} {f : ℝ → Vec3 → ℝ → E} {mean : ℝ → Vec3 → E} {m : ℕ}
    (hA : ContDiff ℝ ∞ (A t)) (hX : Continuous X)
    (hLeft : Function.LeftInverse X (A t)) (hRight : Function.LeftInverse (A t) X)
    (hAper : ∀ n : Fin 3 → ℤ, ∀ x, A t (x + latticeVector n) = A t x + latticeVector n)
    (hf : ContDiff ℝ ∞ (Function.uncurry (f t))) (hmean : ContDiff ℝ ∞ (mean t))
    (hmeanPer : SpatiallyPeriodic (mean t))
    (hdelta : 0 < delta) (hdelta' : delta ≤ 1 / 2)
    (hcollar : ∀ a, (∃ i : Fin 3, 1 / 2 - delta < |a i|) → ∀ q, f t a q = mean t a)
    (hM : 0 ≤ M) (hjet : PhaseJetBound (m + 1) M (transportedProfile A k f t)) :
    let g := periodicHierarchyProfile A k f mean t
    SpatiallyPeriodic g ∧ SpatialHolderHalf m g ∧
      spatialHolderHalfNorm m g ≤ (3 * (m + 1) : ℝ) * M := by
  obtain ⟨hg, hper, hj⟩ := periodicHierarchyProfile_jetBound (k := k) hA hX hLeft hRight
    hAper hf hmean hmeanPer hdelta hdelta' hcollar hjet
  exact ⟨hper, spatialHolderHalfNorm_le_of_uniformJets hg hM hj⟩

omit [NormedSpace ℝ E] in
/-- The Eulerian oscillatory supremum uses the label zeroth-order bound
directly. No carrier-dependent differentiation factor enters (5.47). -/
theorem norm_localizedHierarchyOscillation_le {A : Velocity} {k : Vec3} {t gamma B : ℝ}
    {f : ℝ → Vec3 → ℝ → E}
    (hB : 0 ≤ B) (hgamma : gamma ≤ 1) (hzero : ∀ a s, ‖f t a s‖ ≤ gamma * B)
    (x : Vec3) : ‖localizedTransportedProfile A k f t x‖ ≤ B :=
  (hzero _ _).trans (mul_le_of_le_one_left hB hgamma)

/-- The frozen powers of the wave frequency in the two velocity bounds
of (5.48), expressed with the real carrier scale. -/
theorem physicalHierarchy_velocity_holder_rates
    {osc mean : Vec3 → E} {freq D Cosc Cmean gamma : ℝ} {b m : ℕ}
    (hf : 1 ≤ freq) (hD : 0 ≤ D) (hCosc : 0 ≤ Cosc) (hCmean : 0 ≤ Cmean)
    (hgamma : 0 ≤ gamma) (hgammaOne : gamma ≤ 1)
    (hoscReg : ContDiff ℝ ∞ osc) (hmeanReg : ContDiff ℝ ∞ mean)
    (hosc : PhaseJetBound (m + 1)
      (Cosc * D ^ (b * (m + 2)) * (freq ^ ((3 : ℝ) * (m + 1) / 2) *
        (gamma * freq ^ (-5 / 4 : ℝ)))) osc)
    (hmean : PhaseJetBound (m + 1) (Cmean * D ^ (b * (m + 2)) * freq ^ (-5 / 2 : ℝ)) mean) :
    SpatialHolderHalf m osc ∧ SpatialHolderHalf m mean ∧
      spatialHolderHalfNorm m osc ≤
        (3 * (m + 1) : ℝ) * Cosc * D ^ (b * (m + 2)) *
          freq ^ ((3 : ℝ) * (m + 1) / 2 - 5 / 4) ∧
      spatialHolderHalfNorm m mean ≤
        (3 * (m + 1) : ℝ) * Cmean * D ^ (b * (m + 2)) * freq ^ (-5 / 2 : ℝ) := by
  have hf₀ := zero_lt_one.trans_le hf
  obtain ⟨hO, hOB⟩ := spatialHolderHalfNorm_le_of_uniformJets hoscReg (by positivity) hosc
  obtain ⟨hM, hMB⟩ := spatialHolderHalfNorm_le_of_uniformJets hmeanReg (by positivity) hmean
  refine ⟨hO, hM, hOB.trans ?_, hMB.trans_eq (by ring)⟩
  calc
    _ ≤ (3 * (m + 1) : ℝ) *
        (Cosc * D ^ (b * (m + 2)) * (freq ^ ((3 : ℝ) * (m + 1) / 2) *
          freq ^ (-5 / 4 : ℝ))) := by
      gcongr
      exact mul_le_of_le_one_left (by positivity) hgammaOne
    _ = _ := by
      rw [← Real.rpow_add hf₀]
      ring

/-- Adding the unweighted depth remainder and differentiated switch
remainder gives the residual bound in (5.48). The common two-jet bounds
carry `λ^(7/4)`, which is bounded by `λ²`. -/
theorem physicalHierarchy_residual_holder_rate
    {depthTail primary RV : Vec3 → E} {freq Ctail Cprimary Cstep chiPrime gamma S : ℝ}
    {P : ℕ}
    (hf : 1 ≤ freq) (hCt : 0 ≤ Ctail) (hCp : 0 ≤ Cprimary) (hgamma : 0 ≤ gamma)
    (hCtail : 6 * Ctail ≤ Cstep) (hCprimary : 6 * Cprimary ≤ Cstep)
    (hSwitch : |chiPrime| * gamma ≤ S)
    (hRV : RV = depthTail + chiPrime • primary)
    (hTailReg : ContDiff ℝ ∞ depthTail) (hPrimaryReg : ContDiff ℝ ∞ primary)
    (hTail : PhaseJetBound 2 (Ctail * (freq ^ (7 / 4 : ℝ) * freq ^ (-2 * (P : ℝ) / 3))) depthTail)
    (hPrimary : PhaseJetBound 2 (Cprimary * freq ^ (7 / 4 : ℝ) * gamma) primary) :
    SpatialHolderHalf 1 RV ∧ spatialHolderHalfNorm 1 RV ≤
      Cstep * freq ^ (2 : ℝ) * (freq ^ (-2 * (P : ℝ) / 3) + S) := by
  let A := Ctail * (freq ^ (7 / 4 : ℝ) * freq ^ (-2 * (P : ℝ) / 3))
  let B := Cprimary * freq ^ (7 / 4 : ℝ) * gamma
  have hjets (j : ℕ) (hj : j ≤ 1 + 1) (x : Vec3) :
      ‖iteratedFDeriv ℝ j RV x‖ ≤ A + |chiPrime| * B := by
    have hD := iteratedFDeriv_add
      (hTailReg.of_le (show (j : WithTop ℕ∞) ≤ ∞ by simp))
      ((hPrimaryReg.const_smul chiPrime).of_le (show (j : WithTop ℕ∞) ≤ ∞ by simp))
    change iteratedFDeriv ℝ j (depthTail + chiPrime • primary) =
      iteratedFDeriv ℝ j depthTail + iteratedFDeriv ℝ j (chiPrime • primary) at hD
    rw [hRV, hD, Pi.add_apply]
    change ‖iteratedFDeriv ℝ j depthTail x + iteratedFDeriv ℝ j (fun y => chiPrime • primary y) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hPrimaryReg.contDiffAt.of_le (by simp))]
    exact (norm_add_le _ _).trans (add_le_add (hTail j hj x)
      (by rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hPrimary j hj x) (abs_nonneg _)))
  have hreg : ContDiff ℝ ∞ RV := hRV.symm ▸ hTailReg.add (hPrimaryReg.const_smul _)
  obtain ⟨hR, hNorm⟩ := spatialHolderHalfNorm_le_of_uniformJets hreg
    (show 0 ≤ A + |chiPrime| * B by dsimp [A, B]; positivity) hjets
  refine ⟨hR, hNorm.trans ?_⟩
  have hPower : freq ^ (7 / 4 : ℝ) ≤ freq ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hf (by norm_num)
  have hC : 0 ≤ Cstep := (by positivity : 0 ≤ 6 * Ctail).trans hCtail
  have hnon : 0 ≤ S := (by positivity : 0 ≤ |chiPrime| * gamma).trans hSwitch
  calc
    _ = (6 * Ctail) * freq ^ (7 / 4 : ℝ) * freq ^ (-2 * (P : ℝ) / 3) +
        (6 * Cprimary) * freq ^ (7 / 4 : ℝ) * (|chiPrime| * gamma) := by
      dsimp [A, B]
      ring
    _ ≤ Cstep * freq ^ (2 : ℝ) * freq ^ (-2 * (P : ℝ) / 3) +
        Cstep * freq ^ (2 : ℝ) * S := by gcongr
    _ = _ := by ring

private theorem constantPhaseWord_eq_iteratedFDeriv {f : Vec3 × ℝ → E}
    (hf : ContDiff ℝ ∞ f) (d : Fin 4 → Vec3 × ℝ) (w : List (Fin 4)) (x : Vec3 × ℝ) :
    phaseOperatorWord (fun i _ => d i) w f x =
      iteratedFDeriv ℝ w.length f x (fun i => d (w.get i)) := by
  induction w generalizing x with
  | nil => simp [phaseOperatorWord]
  | cons i w ih =>
    have hw : phaseOperatorWord (fun i _ => d i) w f =
        fun y => iteratedFDeriv ℝ w.length f y (fun j => d (w.get j)) := funext ih
    change fderiv ℝ (phaseOperatorWord (fun i _ => d i) w f) x (d i) =
      iteratedFDeriv ℝ (w.length + 1) f x (fun j => d ((i :: w).get j))
    rw [hw]
    have hd := hf.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top w.length) x
    rw [hd.iteratedFDeriv_succ_apply_left']
    rfl

/-- The actual finite weighted mixed-derivative norm can be used as input
to the Eulerian Fréchet jet estimates. Smoothness permits sorting every
coordinate word without changing its value. -/
theorem scaledPhaseProfile_jetBound_of_hierarchyRelayWordBound
    {T : Type*} {f : T → Vec3 → ℝ → E} {ell h M : ℝ} {n : ℕ}
    (hW : HierarchyRelayWordBound ell h n M (fun t => Function.uncurry (f t)))
    (t : T) (hf : ContDiff ℝ ∞ (Function.uncurry (f t))) :
    PhaseJetBound n ((4 : ℝ) ^ n * M) (scaledPhaseProfile ell h (f t)) := by
  apply scaledPhaseProfile_jetBound_of_coordinateBounds hf hW.1 ell h
  intro j hj p i
  let index : Fin 3 ⊕ Unit → Fin 4 := Sum.elim Fin.castSucc (fun _ => Fin.last 3)
  let d (a : Fin 4) := hierarchyMixedDirection ell h a 0
  have hdir (a : Fin 3 ⊕ Unit) : phaseCoordinateWeight ell h a • phaseCoordinateDirection a =
      d (index a) := by
    cases a with
    | inl k => simp [index, d, hierarchyMixedDirection, phaseCoordinateWeight]
    | inr u =>
      cases u
      simp only [index, d, hierarchyMixedDirection, phaseCoordinateWeight, Sum.elim_inr,
        Fin.lastCases_last]
  have hweight :
      (∏ r, phaseCoordinateWeight ell h (i r)) •
        iteratedFDeriv ℝ j (Function.uncurry (f t)) p (fun r => phaseCoordinateDirection (i r)) =
      iteratedFDeriv ℝ j (Function.uncurry (f t)) p (fun r => d (index (i r))) := by
    have hmap := (iteratedFDeriv ℝ j (Function.uncurry (f t)) p).toMultilinearMap.map_smul_univ
      (fun r => phaseCoordinateWeight ell h (i r)) (fun r => phaseCoordinateDirection (i r))
    simp_rw [← hdir]
    exact hmap.symm
  rw [hweight]
  let w := List.ofFn (fun r => index (i r))
  have hsort : w.mergeSort.Perm w := List.mergeSort_perm _ _
  have hw : w.mergeSort ∈ hierarchyAdmissibleWords (Fin 4) n := by
    refine mem_hierarchyAdmissibleWords.mpr ⟨?_, List.pairwise_mergeSort' _ _⟩
    rw [hsort.length_eq]
    simpa only [w, List.length_ofFn] using hj
  have h := hW.2 _ hw t p
  change ‖phaseOperatorWord (fun i _ => d i) w.mergeSort (Function.uncurry (f t)) p‖ ≤ M at h
  rw [phaseOperatorWord_constantDirections_perm d hf hsort] at h
  rw [constantPhaseWord_eq_iteratedFDeriv hf] at h
  have hc {l : ℕ} (hl : l = j) :
      iteratedFDeriv ℝ l (Function.uncurry (f t)) p (fun r => d (index (i (Fin.cast hl r)))) =
        iteratedFDeriv ℝ j (Function.uncurry (f t)) p (fun r => d (index (i r))) := by
    subst l
    rfl
  simp only [w, List.get_ofFn] at h
  rw [hc List.length_ofFn] at h
  exact h

/-- Reading the finite norm on the normalized profile restores exactly
the time weight on every Eulerian jet. -/
theorem scaledPhaseProfile_jetBound_of_weightedFiniteNorm
    {T : Type*} {f : T → Vec3 → ℝ → E} {gamma : T → ℝ} {ell h M : ℝ} {n : ℕ}
    (hW : HierarchyRelayWordBound ell h n M
      (fun t => (gamma t)⁻¹ • Function.uncurry (f t)))
    (t : T) (hgamma : 0 < gamma t) (hf : ContDiff ℝ ∞ (Function.uncurry (f t))) :
    PhaseJetBound n (gamma t * ((4 : ℝ) ^ n * M)) (scaledPhaseProfile ell h (f t)) := by
  let normalized : T → Vec3 → ℝ → E := fun t a q => (gamma t)⁻¹ • f t a q
  have hNormReg : ContDiff ℝ ∞ (Function.uncurry (normalized t)) := hf.const_smul _
  have hNormJet := scaledPhaseProfile_jetBound_of_hierarchyRelayWordBound (f := normalized) hW t hNormReg
  intro j hj x
  have hy := hNormJet j hj x
  have hscale : scaledPhaseProfile ell h (normalized t) =
      fun p => (gamma t)⁻¹ • scaledPhaseProfile ell h (f t) p := rfl
  have hfscale : ContDiff ℝ ∞ (scaledPhaseProfile ell h (f t)) :=
    hf.comp (labelPhaseScale ell h).contDiff
  rw [hscale, iteratedFDeriv_const_smul_apply' (hfscale.contDiffAt.of_le (by simp)),
    norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hgamma.le)] at hy
  rwa [← div_eq_inv_mul, div_le_iff₀ hgamma, mul_comm] at hy

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The label support of the oscillatory component gives the collar
needed by the periodic transport theorem. -/
theorem hierarchy_collar_of_support_ball {f : Vec3 → ℝ → E} {mean : Vec3 → E}
    {ell : ℝ} (hell : 0 ≤ ell) (hsmall : 2 * ell < 1 / 2)
    (hsupport : ∀ a, 2 * ell < ‖a‖ → ∀ q, f a q = mean a) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 / 2 ∧
      ∀ a, (∃ i : Fin 3, 1 / 2 - delta < |a i|) → ∀ q, f a q = mean a := by
  refine ⟨1 / 2 - 2 * ell, by linarith, by linarith, ?_⟩
  intro a ha
  obtain ⟨i, hi⟩ := ha
  have hi' : 2 * ell < |a i| := by linarith only [hi]
  exact hsupport a (hi'.trans_le (PiLp.norm_apply_le a i))

/-- The graph bound with explicit dependence on the fixed parent power
and on the carrier frequency. The exponent `alpha` is the frequency
power of the supplied weighted hierarchy profile. -/
theorem transportedHierarchyProfile_frequency_jetBound {A : Velocity} {k : Vec3}
    {t ell h D freq L C gamma alpha : ℝ} {B : Vec3 → Vec3 →L[ℝ] Vec3}
    {f : ℝ → Vec3 → ℝ → E} {a p n : ℕ}
    (hell : 0 < ell) (hh : 0 < h) (hD : 1 ≤ D) (hfreq : 1 ≤ freq)
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hgamma : 0 ≤ gamma)
    (hLabel : ell⁻¹ ≤ D ^ a) (hWidth : h = freq ^ (-1 / 2 : ℝ))
    (hCarrier : ‖k‖ ≤ D * freq)
    (hA : ContDiff ℝ ∞ (A t))
    (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x) (hBreg : ContDiff ℝ ∞ B)
    (hf : ContDiff ℝ ∞ (Function.uncurry (f t)))
    (hcoeff : ∀ j ≤ n, ∀ x, ell ^ j * ‖iteratedFDeriv ℝ j B x‖ ≤ L * D)
    (hprofile : PhaseJetBound n (gamma * (C * D ^ p * freq ^ alpha))
      (scaledPhaseProfile ell h (f t))) :
    PhaseJetBound n
      (((3 : ℝ) * (2 : ℝ) ^ n * (2 * L)) ^ n * C *
        D ^ ((max a 1 + 1) * n + p) * (gamma * freq ^ ((3 : ℝ) * n / 2 + alpha)))
      (transportedProfile A k f t) := by
  let cap := 2 * L * D ^ (max a 1 + 1) * freq ^ (3 / 2 : ℝ)
  have hCap : 1 ≤ cap := by
    have hbase : 1 ≤ 2 * L := by linarith
    dsimp only [cap]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hbase (one_le_pow₀ hD))
      (Real.one_le_rpow hfreq (by norm_num))
  have hcost : (ell⁻¹ + h⁻¹ * ‖k‖) * (L * D) ≤ cap := calc
    _ ≤ (2 * D ^ max a 1 * freq ^ (3 / 2 : ℝ)) * (L * D) :=
      mul_le_mul_of_nonneg_right (physicalHierarchy_graph_cost hD hfreq hLabel hWidth hCarrier)
        (by positivity)
    _ = _ := by dsimp only [cap]; rw [pow_succ]; ring
  have hJ := transportedHierarchyProfile_jetBound (k := k) hell hh
    (show 0 ≤ L * D by positivity) hgamma
    (show 0 ≤ C * D ^ p * freq ^ alpha by positivity)
    hCap hcost hA hB hBreg hf hcoeff hprofile
  intro j hj x
  have hf₀ := zero_lt_one.trans_le hfreq
  have hp : (freq ^ (3 / 2 : ℝ)) ^ n = freq ^ ((3 : ℝ) * n / 2) := by
    rw [← Real.rpow_natCast (freq ^ (3 / 2 : ℝ)) n, ← Real.rpow_mul hf₀.le]
    congr 1
    ring
  refine (hJ j hj x).trans_eq ?_
  dsimp only [cap]
  rw [mul_pow ((3 : ℝ) * (2 : ℝ) ^ n) (2 * L) n,
    mul_pow (2 * L * D ^ (max a 1 + 1)), mul_pow (2 * L), ← pow_mul, hp,
    pow_add, Real.rpow_add hf₀]
  ring

/-- A phase-independent field loses only the fixed parent power at
every physical derivative and retains its exact frequency exponent. -/
theorem transportedHierarchyMean_frequency_jetBound {A : Velocity}
    {t ell D freq L C alpha : ℝ} {B : Vec3 → Vec3 →L[ℝ] Vec3}
    {mean : Vec3 → E} {a p n : ℕ}
    (hell : 0 < ell) (hD : 1 ≤ D) (hfreq : 0 < freq)
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hLabel : ell⁻¹ ≤ D ^ a)
    (hA : ContDiff ℝ ∞ (A t))
    (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x) (hBreg : ContDiff ℝ ∞ B)
    (hmean : ContDiff ℝ ∞ mean)
    (hcoeff : ∀ j ≤ n, ∀ x, ell ^ j * ‖iteratedFDeriv ℝ j B x‖ ≤ L * D)
    (hprofile : PhaseJetBound n (C * D ^ p * freq ^ alpha)
      (scaledPhaseProfile ell 1 (fun a _ => mean a))) :
    PhaseJetBound n
      (((3 : ℝ) * (2 : ℝ) ^ n * L) ^ n * C * D ^ ((a + 1) * n + p) * freq ^ alpha)
      (mean ∘ A t) := by
  let cap := L * D ^ (a + 1)
  have hCap : 1 ≤ cap := one_le_mul_of_one_le_of_one_le hL (one_le_pow₀ hD)
  have hcost : ell⁻¹ * (L * D) ≤ cap := calc
    _ ≤ D ^ a * (L * D) := mul_le_mul_of_nonneg_right hLabel (by positivity)
    _ = _ := by dsimp only [cap]; rw [pow_succ]; ring
  have hJ := transportedHierarchyMean_jetBound hell
    (show 0 ≤ L * D by positivity) (show 0 ≤ C * D ^ p * freq ^ alpha by positivity)
    hCap hcost hA hB hBreg hmean hcoeff hprofile
  intro j hj x
  refine (hJ j hj x).trans_eq ?_
  dsimp only [cap]
  rw [mul_pow L, ← pow_mul, mul_pow, pow_add]
  ring

/-- The ordered coordinate words dominate the multi-index sum in (5.44).
Each word is bounded by the Fréchet jet at the same order. -/
theorem sum_spatialDerivativeWord_sup_le_of_jetBound
    {g : Vec3 → E} {m : ℕ} {M : ℝ} (hg : ContDiff ℝ ∞ g)
    (hjet : PhaseJetBound m M g) :
    (∑ i : Fin m → Fin 3, spatialSupNorm (spatialDerivativeWord (List.ofFn i) g)) ≤
      (3 : ℝ) ^ m * M := by
  have hword (i : Fin m → Fin 3) (x : Vec3) :
      spatialDerivativeWord (List.ofFn i) g x =
        iteratedFDeriv ℝ m g x (fun j => coordinateDirection (i j)) := by
    rw [spatialDerivativeWord_eq_iteratedFDeriv hg]
    simp only [List.get_ofFn]
    have hcast {l : ℕ} (hl : l = m) :
        iteratedFDeriv ℝ l g x (fun j => coordinateDirection (i (Fin.cast hl j))) =
          iteratedFDeriv ℝ m g x (fun j => coordinateDirection (i j)) := by
      subst l
      rfl
    exact hcast List.length_ofFn
  have hpoint (i : Fin m → Fin 3) (x : Vec3) :
      ‖spatialDerivativeWord (List.ofFn i) g x‖ ≤ M := by
    rw [hword]
    have hEval := (iteratedFDeriv ℝ m g x).le_opNorm (fun j => coordinateDirection (i j))
    simpa [coordinateDirection] using
      hEval.trans (mul_le_mul_of_nonneg_right (hjet m le_rfl x)
        (Finset.prod_nonneg fun j _ => norm_nonneg _))
  calc
    _ ≤ ∑ _i : Fin m → Fin 3, M := Finset.sum_le_sum fun i _ => ciSup_le (hpoint i)
    _ = _ := by simp

/-- The normalized finite directional norm itself supplies the graph
input. Its boundedness is explicit, since a real supremum requires it. -/
theorem scaledPhaseProfile_jetBound_of_actual_weightedWordNorm
    {T : Type*} {f : T → Vec3 → ℝ → E} {gamma : T → ℝ} {ell h : ℝ} {n : ℕ}
    (hbdd : ∀ w ∈ hierarchyAdmissibleWords (Fin 4) n,
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ell h) w
        (fun t => (gamma t)⁻¹ • Function.uncurry (f t))))
    (t : T) (hgamma : 0 < gamma t) (hf : ContDiff ℝ ∞ (Function.uncurry (f t))) :
    PhaseJetBound n (gamma t * ((4 : ℝ) ^ n *
      hierarchyFiniteWordNorm False (hierarchyMixedDirection ell h) n
        (fun t => (gamma t)⁻¹ • Function.uncurry (f t))))
      (scaledPhaseProfile ell h (f t)) :=
  scaledPhaseProfile_jetBound_of_weightedFiniteNorm
    (hierarchyRelayWordBound_of_finiteNorm hbdd) t hgamma hf

end

end TorusEuler
