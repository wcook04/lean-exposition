import Breakdown.CellReduction.PotThetaScalar
import Breakdown.CertCell.ShapeAngularFactor
import Breakdown.CertCell.ShapeSplineSmooth
import Breakdown.CertCell.ShapeSplineSlope
import Breakdown.CertCell.ShapeJetValid
import Breakdown.CertCell.ShapeJetJoin
import Breakdown.FracCell.GivenProfilePowerFieldJumpsPieces

open scoped ContDiff Topology
open Set Filter

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape
open CellCert.GivenFields (Spline heightRatio weightPoly cellIndex cellCount)

namespace Internal.AwayFromOrigin

def BoundedSlopeNear {F : Type*} [PseudoMetricSpace F] (u : Space → F) (y : Space) : Prop :=
  ∃ K : NNReal, ∃ U ∈ 𝓝 y, LipschitzOnWith K u U

def SlopeNear (f : Space → ℂ) (y : Space) : Prop :=
  ContDiffAt ℝ 1 f y ∧ BoundedSlopeNear (fderiv ℝ f) y

theorem BoundedSlopeNear.congr {F : Type*} [PseudoMetricSpace F] {u v : Space → F} {y : Space} (h : BoundedSlopeNear u y)
    (he : u =ᶠ[𝓝 y] v) : BoundedSlopeNear v y := by
  obtain ⟨K, U, hU, hK⟩ := h
  refine ⟨K, U ∩ {z | u z = v z}, inter_mem hU he, ?_⟩
  intro a ha b hb
  have h1 : u a = v a := ha.2
  have h2 : u b = v b := hb.2
  rw [← h1, ← h2]
  exact hK ha.1 hb.1

theorem boundedSlopeNear_of_contDiffAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {u : Space → F} {y : Space}
    (h : ContDiffAt ℝ 1 u y) : BoundedSlopeNear u y := by
  obtain ⟨K, t, ht, hK⟩ := h.exists_lipschitzOnWith
  exact ⟨K, t, ht, hK⟩

theorem BoundedSlopeNear.add {F : Type*} [SeminormedAddCommGroup F] {u v : Space → F} {y : Space} (hu : BoundedSlopeNear u y)
    (hv : BoundedSlopeNear v y) : BoundedSlopeNear (fun z => u z + v z) y := by
  obtain ⟨Ku, U, hU, hKu⟩ := hu
  obtain ⟨Kv, V, hV, hKv⟩ := hv
  exact ⟨Ku + Kv, U ∩ V, inter_mem hU hV, (hKu.mono inter_subset_left).add (hKv.mono inter_subset_right)⟩

theorem BoundedSlopeNear.bilin {E₁ E₂ G : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {u : Space → E₁} {v : Space → E₂} {y : Space} (hu : BoundedSlopeNear u y) (B : E₁ →L[ℝ] E₂ →L[ℝ] G)
    (hv : BoundedSlopeNear v y) : BoundedSlopeNear (fun z => B (u z) (v z)) y := by
  obtain ⟨Ku, U, hU, hKu⟩ := hu
  obtain ⟨Kv, V, hV, hKv⟩ := hv
  have hcu : ContinuousAt u y := hKu.continuousOn.continuousAt hU
  have hcv : ContinuousAt v y := hKv.continuousOn.continuousAt hV
  have hbu : ∀ᶠ z in 𝓝 y, ‖u z‖ < ‖u y‖ + 1 := hcu.norm.eventually (eventually_lt_nhds (lt_add_one _))
  have hbv : ∀ᶠ z in 𝓝 y, ‖v z‖ < ‖v y‖ + 1 := hcv.norm.eventually (eventually_lt_nhds (lt_add_one _))
  have hCu : 0 ≤ ‖u y‖ + 1 := by positivity
  have hCv : 0 ≤ ‖v y‖ + 1 := by positivity
  have hc : 0 ≤ ‖B‖ * (Ku * (‖v y‖ + 1) + (‖u y‖ + 1) * Kv) := by positivity
  refine ⟨Real.toNNReal (‖B‖ * (Ku * (‖v y‖ + 1) + (‖u y‖ + 1) * Kv)),
    U ∩ V ∩ {z | ‖u z‖ < ‖u y‖ + 1 ∧ ‖v z‖ < ‖v y‖ + 1}, inter_mem (inter_mem hU hV) (hbu.and hbv),
    LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_⟩
  rw [Real.coe_toNNReal _ hc]
  have hua : dist (u a) (u b) ≤ Ku * dist a b := hKu.dist_le_mul a ha.1.1 b hb.1.1
  have hvb : dist (v a) (v b) ≤ Kv * dist a b := hKv.dist_le_mul a ha.1.2 b hb.1.2
  have hva : ‖v a‖ ≤ ‖v y‖ + 1 := ha.2.2.le
  have hub : ‖u b‖ ≤ ‖u y‖ + 1 := hb.2.1.le
  rw [dist_eq_norm] at hua hvb
  rw [dist_eq_norm]
  have key : B (u a) (v a) - B (u b) (v b) = B (u a - u b) (v a) + B (u b) (v a - v b) := by
    simp only [map_sub, sub_apply]
    abel
  rw [key]
  have hd : 0 ≤ dist a b := dist_nonneg
  calc ‖B (u a - u b) (v a) + B (u b) (v a - v b)‖
      ≤ ‖B (u a - u b) (v a)‖ + ‖B (u b) (v a - v b)‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖u a - u b‖ * ‖v a‖ + ‖B‖ * ‖u b‖ * ‖v a - v b‖ :=
        add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
    _ ≤ ‖B‖ * (Ku * dist a b) * (‖v y‖ + 1) + ‖B‖ * (‖u y‖ + 1) * (Kv * dist a b) := by
        gcongr
    _ = ‖B‖ * (Ku * (‖v y‖ + 1) + (‖u y‖ + 1) * Kv) * dist a b := by ring

theorem slopeNear_of_two {f : Space → ℂ} {y : Space} (h : ContDiffAt ℝ 2 f y) : SlopeNear f y :=
  ⟨h.of_le (by norm_num), boundedSlopeNear_of_contDiffAt (h.fderiv_right (m := 1) (by norm_num))⟩

theorem SlopeNear.congr {f g : Space → ℂ} {y : Space} (hf : SlopeNear f y) (he : f =ᶠ[𝓝 y] g) :
    SlopeNear g y := by
  refine ⟨hf.1.congr_of_eventuallyEq he.symm, hf.2.congr ?_⟩
  filter_upwards [he.eventuallyEq_nhds] with z hz
  exact hz.fderiv_eq

theorem SlopeNear.mul {f g : Space → ℂ} {y : Space} (hf : SlopeNear f y) (hg : SlopeNear g y) :
    SlopeNear (fun z => f z * g z) y := by
  refine ⟨hf.1.mul hg.1, ?_⟩
  have h1 := (boundedSlopeNear_of_contDiffAt hf.1).bilin
    (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] (Space →L[ℝ] ℂ) →L[ℝ] Space →L[ℝ] ℂ) hg.2
  have h2 := (boundedSlopeNear_of_contDiffAt hg.1).bilin
    (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] (Space →L[ℝ] ℂ) →L[ℝ] Space →L[ℝ] ℂ) hf.2
  refine (h1.add h2).congr ?_
  filter_upwards [hf.1.eventually (by simp), hg.1.eventually (by simp)] with z hfz hgz
  rw [fderiv_fun_mul (hfz.differentiableAt one_ne_zero) (hgz.differentiableAt one_ne_zero)]
  simp [ContinuousLinearMap.lsmul_apply]

theorem SlopeNear.comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {R : E → ℂ} (hR : ContDiff ℝ 1 R)
    (hL : ∀ r : ℝ, ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ R) (Metric.closedBall 0 r))
    {χ : Space → E} {y : Space} (hχ : ContDiffAt ℝ 2 χ y) : SlopeNear (fun z => R (χ z)) y := by
  have hχ1 : ContDiffAt ℝ 1 χ y := hχ.of_le (by norm_num)
  refine ⟨hR.contDiffAt.comp y hχ1, ?_⟩
  have hu : BoundedSlopeNear (fun z => fderiv ℝ R (χ z)) y := by
    obtain ⟨L, hL'⟩ := hL (‖χ y‖ + 1)
    obtain ⟨K, U, hU, hK⟩ := boundedSlopeNear_of_contDiffAt hχ1
    refine ⟨L * K, U ∩ χ ⁻¹' Metric.ball (χ y) 1,
      inter_mem hU (hχ1.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ one_pos)), ?_⟩
    refine hL'.comp (hK.mono inter_subset_left) ?_
    intro z hz
    have h1 : dist (χ z) (χ y) < 1 := hz.2
    rw [Metric.mem_closedBall, dist_zero_right]
    have h2 := norm_le_insert' (χ z) (χ y)
    rw [dist_eq_norm] at h1
    linarith
  have hv : BoundedSlopeNear (fun z => fderiv ℝ χ z) y := boundedSlopeNear_of_contDiffAt (hχ.fderiv_right (m := 1) (by norm_num))
  refine (hu.bilin (ContinuousLinearMap.compL ℝ Space E ℂ) hv).congr ?_
  filter_upwards [hχ1.eventually (by simp)] with z hz
  show _ = fderiv ℝ (R ∘ χ) z
  rw [fderiv_comp z ((hR.differentiable one_ne_zero) (χ z)) (hz.differentiableAt one_ne_zero),
    ContinuousLinearMap.compL_apply]

theorem slopeBound_of_derivBound_offZero {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {g : E → G} {K : NNReal} (hc : Continuous g)
    (hd : ∀ z, z ≠ 0 → DifferentiableAt ℝ g z) (hb : ∀ z, z ≠ 0 → ‖fderiv ℝ g z‖ ≤ K) : LipschitzWith K g := by
  have hrad : ∀ u : E, dist (g u) (g 0) ≤ K * dist u 0 := by
    intro u
    rw [dist_eq_norm, dist_eq_norm, sub_zero]
    by_cases hu : u = 0
    · simp [hu]
    have hφ : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => g ((1 - s) • u))
        (fderiv ℝ g ((1 - t) • u) ((-1 : ℝ) • u)) (Ici t) t := by
      intro t ht
      have hne : (1 - t) • u ≠ 0 := smul_ne_zero (by linarith [ht.2]) hu
      have h1 : HasDerivAt (fun s : ℝ => (1 - s) • u) ((-1 : ℝ) • u) t :=
        ((hasDerivAt_id' t).const_sub 1).smul_const u
      exact ((hd _ hne).hasFDerivAt.comp_hasDerivAt t h1).hasDerivWithinAt
    have hcont : ContinuousOn (fun s : ℝ => g ((1 - s) • u)) (Icc 0 1) :=
      (hc.comp ((continuous_const.sub continuous_id).smul continuous_const)).continuousOn
    have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖fderiv ℝ g ((1 - t) • u) ((-1 : ℝ) • u)‖ ≤ K * ‖u‖ := by
      intro t ht
      have hne : (1 - t) • u ≠ 0 := smul_ne_zero (by linarith [ht.2]) hu
      calc ‖fderiv ℝ g ((1 - t) • u) ((-1 : ℝ) • u)‖ ≤ ‖fderiv ℝ g ((1 - t) • u)‖ * ‖(-1 : ℝ) • u‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ K * ‖u‖ := by
            rw [neg_one_smul, norm_neg]
            exact mul_le_mul_of_nonneg_right (hb _ hne) (norm_nonneg _)
    have := norm_image_sub_le_of_norm_deriv_right_le_segment hcont hφ hbound 1 ⟨zero_le_one, le_rfl⟩
    simp only [sub_self, zero_smul, sub_zero, one_smul, mul_one] at this
    rw [norm_sub_rev]
    exact this
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  by_cases h0 : (0 : E) ∈ segment ℝ u v
  · have hs := dist_add_dist_of_mem_segment h0
    calc dist (g u) (g v) ≤ dist (g u) (g 0) + dist (g 0) (g v) := dist_triangle _ _ _
      _ ≤ K * dist u 0 + K * dist 0 v := by
          rw [dist_comm (g 0), dist_comm (0 : E)]
          exact add_le_add (hrad u) (hrad v)
      _ = K * dist u v := by rw [← mul_add, hs]
  · have hs : ∀ x ∈ segment ℝ u v, x ≠ 0 := fun x hx h => h0 (by rw [← h]; exact hx)
    have := (convex_segment u v).norm_image_sub_le_of_norm_fderiv_le (fun x hx => hd x (hs x hx))
      (fun x hx => hb x (hs x hx)) (left_mem_segment ℝ u v) (right_mem_segment ℝ u v)
    rw [dist_eq_norm, dist_eq_norm, norm_sub_rev, norm_sub_rev u]
    exact this

def planeMap : Space →L[ℝ] ℂ :=
  (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).smulRight (1 : ℂ) +
    (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).smulRight Complex.I

theorem planeMap_apply (y : Space) : planeMap y = ((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I := by
  simp [planeMap, Complex.real_smul]

def planePower (M : ℤ) (D : ℕ) (z : ℂ) : ℂ := (‖z‖ ^ D) • (‖z‖⁻¹ • z) ^ M

theorem zpow_contDiffAt {n : WithTop ℕ∞} (M : ℤ) {w : ℂ} (hw : w ≠ 0) :
    ContDiffAt ℂ n (fun v : ℂ => v ^ M) w := by
  cases M with
  | ofNat m => simpa using (contDiffAt_id (x := w)).pow m
  | negSucc m =>
    have h := ((contDiffAt_id (𝕜 := ℂ) (n := n) (x := w)).pow (m + 1)).inv (pow_ne_zero _ hw)
    rw [show (fun v : ℂ => v ^ Int.negSucc m) = fun v => (v ^ (m + 1))⁻¹ from funext fun v => zpow_negSucc v m]
    exact h

theorem planePower_contDiffAt_ne {n : WithTop ℕ∞} (M : ℤ) (D : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ n (planePower M D) z := by
  have hn : ContDiffAt ℝ n (fun w : ℂ => ‖w‖) z := contDiffAt_norm ℝ hz
  have hw : ContDiffAt ℝ n (fun w : ℂ => ‖w‖⁻¹ • w) z := (hn.inv (norm_ne_zero_iff.2 hz)).smul contDiffAt_id
  have hw0 : ‖z‖⁻¹ • z ≠ 0 := smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 hz)) hz
  have hp : ContDiffAt ℝ n (fun w : ℂ => w ^ M) (‖z‖⁻¹ • z) :=
    (zpow_contDiffAt M hw0).restrict_scalars ℝ
  exact (hn.pow D).smul (ContDiffAt.comp (g := fun w : ℂ => w ^ M) (f := fun w : ℂ => ‖w‖⁻¹ • w) z hp hw)

theorem planePower_homog (M : ℤ) (D : ℕ) : ∀ t : ℝ, 0 < t → ∀ z : ℂ,
    planePower M D (t • z) = t ^ D • planePower M D z := by
  intro t ht z
  have hn : ‖t • z‖ = t * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hu : (t * ‖z‖)⁻¹ • (t • z) = ‖z‖⁻¹ • z := by
    rw [smul_smul, mul_inv, mul_comm t⁻¹, mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]
  unfold planePower
  rw [hn, hu, mul_pow, smul_smul]

theorem planePower_zero (M : ℤ) {D : ℕ} (hD : 1 ≤ D) : planePower M D 0 = 0 := by
  simp [planePower, zero_pow (by omega : D ≠ 0)]

theorem planePower_factor (M : ℤ) (k d : ℕ) (z : ℂ) :
    planePower M (2 * k + d) z = ((‖z‖ ^ 2) ^ k : ℝ) • planePower M d z := by
  unfold planePower
  rw [smul_smul, ← pow_mul, ← pow_add]

theorem planePower_offZero (M : ℤ) (D n : ℕ) : ContDiffOn ℝ n (planePower M D) {0}ᶜ :=
  fun _ hz => (planePower_contDiffAt_ne M D hz).contDiffWithinAt

theorem planePower_three_contDiff (M : ℤ) : ContDiff ℝ 2 (planePower M 3) := by
  have h := CertCell.GivenShape.Internal.contDiff_of_homogeneous 2 (planePower M 3)
    (planePower_offZero M 3 2) (planePower_zero M (by norm_num)) (planePower_homog M 3)
  exact_mod_cast h

theorem planePower_two_contDiff (M : ℤ) : ContDiff ℝ 1 (planePower M 2) := by
  have h := CertCell.GivenShape.Internal.contDiff_of_homogeneous 1 (planePower M 2)
    (planePower_offZero M 2 1) (planePower_zero M (by norm_num)) (planePower_homog M 2)
  exact_mod_cast h

theorem planePower_two_slope (M : ℤ) : ∃ L : NNReal, LipschitzWith L (fderiv ℝ (planePower M 2)) := by
  obtain ⟨C, hC⟩ := CertCell.GivenShape.Internal.norm_iteratedFDeriv_le_of_homogeneous 2 2 le_rfl
    (planePower M 2) (planePower_offZero M 2 2) (planePower_homog M 2)
  refine ⟨C.toNNReal, slopeBound_of_derivBound_offZero ((planePower_two_contDiff M).continuous_fderiv one_ne_zero)
    (fun z hz => ?_) (fun z hz => ?_)⟩
  · exact ((planePower_contDiffAt_ne (n := 2) M 2 hz).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  · have h1 := hC z hz
    calc ‖fderiv ℝ (fderiv ℝ (planePower M 2)) z‖ = ‖iteratedFDeriv ℝ 2 (planePower M 2) z‖ := by
          rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
      _ ≤ C * ‖z‖ ^ (2 - 2) := h1
      _ ≤ C.toNNReal := by simp

theorem planePower_one_contDiff (M : ℤ) (hM : |M| = 1) : ContDiff ℝ 2 (planePower M 1) := by
  rcases (abs_eq zero_le_one).1 hM with h | h
  · subst h
    have he : planePower 1 1 = id := by
      funext z
      by_cases hz : z = 0
      · subst hz
        exact planePower_zero 1 le_rfl
      · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
        simp only [planePower, pow_one, zpow_one, smul_smul, mul_inv_cancel₀ hn, one_smul, id]
    rw [he]
    exact contDiff_id
  · subst h
    have he : planePower (-1) 1 = fun z => starRingEnd ℂ z := by
      funext z
      by_cases hz : z = 0
      · subst hz
        simp [planePower_zero (-1) le_rfl]
      · have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
        simp only [planePower, pow_one, zpow_neg, zpow_one, Complex.real_smul, Complex.ofReal_inv]
        rw [mul_inv, inv_inv, Complex.inv_def, Complex.normSq_eq_norm_sq]
        push_cast
        field_simp
    rw [he]
    have hc := (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff (n := 2)
    convert hc using 1
    funext z
    simp

theorem planePower_factor_contDiff (M : ℤ) (k : ℕ) {d : ℕ} (h : ContDiff ℝ 2 (planePower M d)) :
    ContDiff ℝ 2 (planePower M (2 * k + d)) := by
  have he : planePower M (2 * k + d) = fun w => (((‖w‖ ^ 2) ^ k : ℝ) : ℂ) * planePower M d w :=
    funext fun w => by rw [planePower_factor, Complex.real_smul]
  rw [he]
  exact (Complex.ofRealCLM.contDiff.comp ((contDiff_norm_sq ℝ).pow k)).mul h

def angDegree (s : Bool) (a : ℕ) : ℕ := 2 * a + (if s then 1 else 0)

def angPart (M : ℤ) (s : Bool) (a : ℕ) (y : Space) : ℂ :=
  Complex.exp ((((M : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I) *
    (((1 - heightRatio y ^ 2) ^ a * (if s then polarSine y else 1) : ℝ) : ℂ)

theorem ang_eq (M : ℤ) (s : Bool) (a : ℕ) {y : Space} (hy : y ≠ 0)
    (hD : planeMap y ≠ 0 ∨ 1 ≤ angDegree s a) :
    angPart M s a y = (((‖y‖ ^ angDegree s a)⁻¹ : ℝ) : ℂ) * planePower M (angDegree s a) (planeMap y) := by
  have hr0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hrpos : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hr2 : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [Real.norm_eq_abs, sq_abs]
  have hρ2 : ‖planeMap y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [planeMap_apply, Complex.sq_norm, Complex.normSq_add_mul_I]
  have hq : 1 - heightRatio y ^ 2 = (‖planeMap y‖ / ‖y‖) ^ 2 := by
    unfold heightRatio
    rw [div_pow, div_pow, eq_div_iff (pow_ne_zero 2 hr0), sub_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hr0),
      one_mul, hρ2, hr2]
    ring
  have hsin : polarSine y = ‖planeMap y‖ / ‖y‖ := by
    unfold polarSine
    rw [hq, Real.sqrt_sq (by positivity)]
  have hfac : (1 - heightRatio y ^ 2) ^ a * (if s then polarSine y else 1) =
      (‖planeMap y‖ / ‖y‖) ^ angDegree s a := by
    rw [hq, hsin]
    unfold angDegree
    cases s <;> simp [pow_add, pow_mul]
  have hsplit : (‖planeMap y‖ / ‖y‖) ^ angDegree s a =
      (‖y‖ ^ angDegree s a)⁻¹ * ‖planeMap y‖ ^ angDegree s a := by
    rw [div_pow, div_eq_inv_mul]
  unfold angPart
  rw [hfac, hsplit]
  by_cases hζ : planeMap y = 0
  · have hD1 : 1 ≤ angDegree s a := hD.resolve_left (not_not.2 hζ)
    rw [hζ, planePower_zero M hD1]
    simp [zero_pow (by omega : angDegree s a ≠ 0)]
  · have hexp : Complex.exp ((((M : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I) =
        (‖planeMap y‖⁻¹ • planeMap y) ^ M := by
      have h1 : ((((M : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I) =
          (M : ℂ) * ((Complex.arg (planeMap y) : ℂ) * Complex.I) := by
        rw [planeMap_apply]
        unfold pointAngle
        push_cast
        ring
      rw [h1, Complex.exp_int_mul]
      congr 1
      have h2 := Complex.norm_mul_exp_arg_mul_I (planeMap y)
      have hn : (‖planeMap y‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hζ)
      rw [Complex.real_smul]
      push_cast
      rw [eq_inv_mul_iff_mul_eq₀ hn, h2]
    rw [hexp]
    unfold planePower
    generalize (‖planeMap y‖⁻¹ • planeMap y) ^ M = w
    rw [Complex.real_smul, Complex.ofReal_mul]
    ring

theorem ang_eventually (M : ℤ) (s : Bool) (a : ℕ) {y : Space} (hy : y ≠ 0)
    (hD : planeMap y ≠ 0 ∨ 1 ≤ angDegree s a) :
    angPart M s a =ᶠ[𝓝 y] fun z => (((‖z‖ ^ angDegree s a)⁻¹ : ℝ) : ℂ) * planePower M (angDegree s a) (planeMap z) := by
  have h1 : ∀ᶠ z in 𝓝 y, z ≠ 0 := isOpen_ne.mem_nhds hy
  rcases hD with hζ | hD1
  · have h2 : ∀ᶠ z in 𝓝 y, planeMap z ≠ 0 := planeMap.continuous.continuousAt.eventually_ne hζ
    filter_upwards [h1, h2] with z hz hz2 using ang_eq M s a hz (Or.inl hz2)
  · filter_upwards [h1] with z hz using ang_eq M s a hz (Or.inr hD1)

theorem invPow_contDiffAt (D : ℕ) {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ 2 (fun z : Space => (((‖z‖ ^ D)⁻¹ : ℝ) : ℂ)) y :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp y
    (((contDiffAt_norm ℝ hy).pow D).inv (pow_ne_zero _ (norm_ne_zero_iff.2 hy)))

theorem ang_slopeNear_smooth (M : ℤ) (s : Bool) (a : ℕ) (hsm : ContDiff ℝ 2 (planePower M (angDegree s a)))
    (hD1 : 1 ≤ angDegree s a) {y : Space} (hy : y ≠ 0) : SlopeNear (angPart M s a) y :=
  (slopeNear_of_two ((invPow_contDiffAt _ hy).mul (hsm.contDiffAt.comp y planeMap.contDiff.contDiffAt))).congr
    (ang_eventually M s a hy (Or.inr hD1)).symm

theorem ang_slopeNear_off (M : ℤ) (s : Bool) (a : ℕ) {y : Space} (hy : y ≠ 0) (hζ : planeMap y ≠ 0) :
    SlopeNear (angPart M s a) y :=
  (slopeNear_of_two ((invPow_contDiffAt _ hy).mul
    ((planePower_contDiffAt_ne M (angDegree s a) hζ).comp y planeMap.contDiff.contDiffAt))).congr
    (ang_eventually M s a hy (Or.inl hζ)).symm

theorem ang_slopeNear_plain (a : ℕ) {y : Space} (hy : y ≠ 0) : SlopeNear (angPart 0 false a) y := by
  have hh : ContDiffAt ℝ 2 heightRatio y :=
    (FracInternal.ProfilePowerJumpsPieces.heightRatio_contDiffOn.contDiffAt (isOpen_ne.mem_nhds hy)).of_le
      (by norm_num)
  have hc : ContDiffAt ℝ 2 (fun z : Space => (((1 - heightRatio z ^ 2) ^ a : ℝ) : ℂ)) y :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp y ((contDiffAt_const.sub (hh.pow 2)).pow a)
  refine (slopeNear_of_two hc).congr (Eventually.of_forall fun z => ?_)
  simp [angPart]

theorem ang_slopeNear_square (M : ℤ) (a : ℕ) (ha : 1 ≤ a) {y : Space} (hy : y ≠ 0) :
    SlopeNear (angPart M false a) y := by
  have hdeg : angDegree false a = 2 * (a - 1) + 2 := by simp [angDegree]; omega
  have hr : ContDiffAt ℝ 2 (fun z : Space => (((‖z‖ ^ angDegree false a)⁻¹ : ℝ) : ℂ) *
      (((‖planeMap z‖ ^ 2) ^ (a - 1) : ℝ) : ℂ)) y :=
    (invPow_contDiffAt _ hy).mul (Complex.ofRealCLM.contDiff.contDiffAt.comp y
      (((contDiff_norm_sq ℝ).comp planeMap.contDiff).contDiffAt.pow (a - 1)))
  obtain ⟨L, hL⟩ := planePower_two_slope M
  have hq := SlopeNear.comp (planePower_two_contDiff M) (fun _ => ⟨L, hL.lipschitzOnWith⟩)
    (χ := planeMap) planeMap.contDiff.contDiffAt (y := y)
  refine ((slopeNear_of_two hr).mul hq).congr ?_
  filter_upwards [ang_eventually M false a hy (Or.inr (by rw [hdeg]; omega))] with z hz
  rw [hz, hdeg, planePower_factor, Complex.real_smul]
  ring

theorem chartCoord_contDiffAt (P : ShapeParams) (hP : 0 < P.chartLength) {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ 2 (chartCoord P) y := by
  have hn : ContDiffAt ℝ 2 (fun z : Space => ‖z‖) y := contDiffAt_norm ℝ hy
  have hd : 0 < ‖y‖ + P.chartLength := by have := norm_nonneg y; linarith
  exact hn.div (hn.add contDiffAt_const) hd.ne'

theorem heightRatio_contDiffAt {y : Space} (hy : y ≠ 0) : ContDiffAt ℝ 2 heightRatio y :=
  (FracInternal.ProfilePowerJumpsPieces.heightRatio_contDiffOn.contDiffAt (isOpen_ne.mem_nhds hy)).of_le
    (by norm_num)

theorem spline_slopeNear (H : JetSpline) (hH : IsJetClass 1 1 H) (P : ShapeParams) (hP : 0 < P.chartLength)
    {y : Space} (hy : y ≠ 0) : SlopeNear (fun z => H.toSpline.evalHalf (chartCoord P z) (heightRatio z)) y := by
  have hJ : IsJoinedSpline 1 1 H.toSpline :=
    CertCell.GivenShape.Internal.joinedSpline_of_jetClass jetSplineJoined hH
  have hR : ContDiff ℝ 1 (fun z : ℝ × ℝ => H.toSpline.evalHalf z.1 z.2) :=
    (joinedSplineSmooth 1 1 _ hJ).of_le (by simp)
  have hL := joinedSplineGradSlopeBound_of_smooth joinedSplineSmooth 1 1 _ hJ le_rfl le_rfl
  exact SlopeNear.comp (R := fun z : ℝ × ℝ => H.toSpline.evalHalf z.1 z.2) hR hL
    (χ := fun z => (chartCoord P z, heightRatio z)) ((chartCoord_contDiffAt P hP hy).prodMk (heightRatio_contDiffAt hy))

theorem exists_margin (L : List ℝ) (h : ∀ b ∈ L, |b| < 1) : ∃ δ > 0, ∀ b ∈ L, |b| < 1 - δ := by
  induction L with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons b L ih =>
    obtain ⟨δ, hδ, hL⟩ := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    have hb : |b| < 1 := h b (by simp)
    refine ⟨min δ ((1 - |b|) / 2), lt_min hδ (by linarith), ?_⟩
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · have := min_le_right δ ((1 - |c|) / 2)
      linarith
    · have := min_le_left δ ((1 - |b|) / 2)
      have := hL c hc
      linarith

theorem interior_abs_lt (l : List ℝ) (hs : l.Pairwise (· < ·)) (h0 : l.head? = some (-1))
    (h1 : l.getLast? = some 1) : ∀ b ∈ (l.drop 1).dropLast, |b| < 1 := by
  intro b hb
  cases l with
  | nil => simp at h0
  | cons a r =>
    simp only [List.head?_cons, Option.some.injEq] at h0
    simp only [List.drop_succ_cons, List.drop_zero] at hb
    have hr : r ≠ [] := by
      rintro rfl
      simp at hb
    have hbr : b ∈ r := List.mem_of_mem_dropLast hb
    have hlo : a < b := (List.pairwise_cons.1 hs).1 b hbr
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil a r), List.getLast_cons hr] at h1
    have hlast : r.getLast hr = 1 := by simpa using h1
    have hs' : r.Pairwise (· < ·) := hs.of_cons
    have e := List.dropLast_append_getLast hr
    rw [← e, List.pairwise_append] at hs'
    have hhi := hs'.2.2 b hb (r.getLast hr) (by simp)
    rw [hlast] at hhi
    rw [abs_lt]
    constructor <;> linarith

theorem end_dof (A : JetAxis) (j : ℕ) (hj : j = 0 ∨ j = cellCount A.breaks - 1) (e : JetDof) :
    dofMeetsEndCells (cellCount A.breaks) e ∨ A.dofPoly j e = 0 := by
  cases e with
  | node k p =>
    by_cases h : k ≤ 1 ∨ cellCount A.breaks - 1 ≤ k
    · left
      exact h
    · right
      have hk1 : k ≠ j := by omega
      have hk2 : k ≠ j + 1 := by omega
      simp [JetAxis.dofPoly, hk1, hk2]
  | bubble i s =>
    by_cases h : i = 0 ∨ cellCount A.breaks - 1 ≤ i
    · left
      exact h
    · right
      have hi : i ≠ j := by omega
      simp [JetAxis.dofPoly, hi]

theorem piece_zero_of_end (H : JetSpline) (hv : AxisCellsVanish H) (i j : ℕ)
    (hj : j = 0 ∨ j = cellCount H.xAxis.breaks - 1) : H.toSpline.piece i j = 0 := by
  simp only [JetSpline.toSpline]
  apply Finset.sum_eq_zero
  intro d _
  apply Finset.sum_eq_zero
  intro e he
  rcases end_dof H.xAxis j hj e with hm | hp
  · rw [hv d e he hm]
    simp
  · rw [hp]
    simp [embedSecond]

theorem evalHalf_zero_of_abs (H : JetSpline) (hx : IsJetAxis H.xAxis (-1) 1) (hv : AxisCellsVanish H) :
    ∃ δ > 0, ∀ t x : ℝ, 1 - δ < |x| → H.toSpline.evalHalf t x = 0 := by
  obtain ⟨δ, hδ, hm⟩ := exists_margin _ (interior_abs_lt _ hx.sorted hx.first hx.last)
  refine ⟨δ, hδ, fun t x hxabs => ?_⟩
  have hidx : cellIndex H.xAxis.breaks x = 0 ∨ cellIndex H.xAxis.breaks x = cellCount H.xAxis.breaks - 1 := by
    rcases le_or_gt 0 x with h0 | h0
    · right
      rw [abs_of_nonneg h0] at hxabs
      unfold cellIndex cellCount
      rw [List.filter_eq_self.2 (fun b hb => decide_eq_true (by
        have := hm b hb
        have := le_abs_self b
        linarith))]
      simp [List.length_dropLast]
    · left
      rw [abs_of_neg h0] at hxabs
      unfold cellIndex
      rw [List.filter_eq_nil_iff.2 (fun b hb => by
        simp only [decide_eq_true_eq, not_le]
        have := hm b hb
        have := neg_abs_le b
        linarith)]
      rfl
  show MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (H.toSpline.piece _ (cellIndex H.xAxis.breaks x)) = 0
  rw [piece_zero_of_end H hv _ _ hidx, map_zero]

theorem spline_zero_near_axis (P : ShapeParams) (H : JetSpline) (hx : IsJetAxis H.xAxis (-1) 1)
    (hv : AxisCellsVanish H) {y : Space} (hy : y ≠ 0) (hζ : planeMap y = 0) :
    ∀ᶠ z in 𝓝 y, H.toSpline.evalHalf (chartCoord P z) (heightRatio z) = 0 := by
  obtain ⟨δ, hδ, hvan⟩ := evalHalf_zero_of_abs H hx hv
  have h01 : y 0 = 0 ∧ y 1 = 0 := by
    have h := hζ
    rw [planeMap_apply] at h
    simpa [Complex.ext_iff] using h
  have hn2 : ‖y‖ ^ 2 = y 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [Real.norm_eq_abs, sq_abs, h01.1, h01.2]
  have hn : ‖y‖ = |y 2| := by
    rw [← Real.sqrt_sq (norm_nonneg y), hn2, Real.sqrt_sq_eq_abs]
  have hne : |y 2| ≠ 0 := by
    rw [← hn]
    exact norm_ne_zero_iff.2 hy
  have habs : |heightRatio y| = 1 := by
    unfold heightRatio
    rw [abs_div, abs_norm, hn, div_self hne]
  have hc : ContinuousAt (fun z => |heightRatio z|) y :=
    continuous_abs.continuousAt.comp (heightRatio_contDiffAt hy).continuousAt
  filter_upwards [hc.eventually (eventually_gt_nhds (by rw [habs]; linarith : 1 - δ < |heightRatio y|))]
    with z hz
  exact hvan _ _ hz

theorem angSpline_slopeNear (P : ShapeParams) (hP : 0 < P.chartLength) (M : ℤ) (s : Bool) (S : PotScalar)
    (hS : IsJetClass 1 1 S.amp) (hA : AxisAdmissible M s S) {y : Space} (hy : y ≠ 0) :
    SlopeNear (fun z => angPart M s S.axisPower z * S.amp.toSpline.evalHalf (chartCoord P z) (heightRatio z)) y := by
  have hG := spline_slopeNear S.amp hS P hP hy
  by_cases hA0 : M = 0 ∧ s = false
  · obtain ⟨rfl, rfl⟩ := hA0
    exact (ang_slopeNear_plain S.axisPower hy).mul hG
  by_cases hB : s = true ∧ |M| = 1
  · obtain ⟨rfl, hM⟩ := hB
    have hdeg : angDegree true S.axisPower = 2 * S.axisPower + 1 := by
      rw [angDegree, if_pos rfl]
    have hsm : ContDiff ℝ 2 (planePower M (angDegree true S.axisPower)) := by
      rw [hdeg]
      exact planePower_factor_contDiff M S.axisPower (planePower_one_contDiff M hM)
    exact (ang_slopeNear_smooth M true S.axisPower hsm (by rw [hdeg]; omega) hy).mul hG
  have hC : 1 ≤ S.axisPower ∨ AxisCellsVanish S.amp := by
    cases s with
    | false =>
      have hM : M ≠ 0 := fun h => hA0 ⟨h, rfl⟩
      exact hA.1 hM rfl
    | true =>
      have hM : |M| ≠ 1 := fun h => hB ⟨rfl, h⟩
      exact hA.2 rfl hM
  rcases hC with ha | hv
  · cases s with
    | false => exact (ang_slopeNear_square M S.axisPower ha hy).mul hG
    | true =>
      have hdeg : angDegree true S.axisPower = 2 * (S.axisPower - 1) + 3 := by
        rw [angDegree, if_pos rfl]
        omega
      have hsm : ContDiff ℝ 2 (planePower M (angDegree true S.axisPower)) := by
        rw [hdeg]
        exact planePower_factor_contDiff M (S.axisPower - 1) (planePower_three_contDiff M)
      exact (ang_slopeNear_smooth M true S.axisPower hsm (by rw [hdeg]; omega) hy).mul hG
  · by_cases hζ : planeMap y = 0
    · have hz := spline_zero_near_axis P S.amp hS.x_axis hv hy hζ
      refine (slopeNear_of_two (contDiffAt_const (c := (0 : ℂ)))).congr ?_
      filter_upwards [hz] with z hz'
      rw [hz', mul_zero]
    · exact (ang_slopeNear_off M s S.axisPower hy hζ).mul hG

theorem front_contDiffAt (P : ShapeParams) (hP : IsShapeParams P) (A c : ℝ) (e0 e1 : ℕ) {y : Space}
    (hy : y ≠ 0) : ContDiffAt ℝ 2 (fun z : Space => Complex.exp (((A + c * P.radialPhase (‖z‖ ^ 2) : ℝ) : ℂ) *
      Complex.I) * weightPoly e0 e1 (chartCoord P z)) y := by
  obtain ⟨δ, hδ, hf⟩ := hP.phase.smooth
  have hph : ContDiffAt ℝ 2 (fun z : Space => P.radialPhase (‖z‖ ^ 2)) y := by
    have h1 : ContDiffAt ℝ 2 P.radialPhase (‖y‖ ^ 2) :=
      (hf.contDiffAt (Ioi_mem_nhds (by nlinarith [sq_nonneg ‖y‖] : -δ < ‖y‖ ^ 2))).of_le (by norm_num)
    exact h1.comp y (contDiff_norm_sq ℝ).contDiffAt
  have hre : ContDiffAt ℝ 2 (fun z : Space => ((A + c * P.radialPhase (‖z‖ ^ 2) : ℝ) : ℂ) * Complex.I) y :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp y (contDiffAt_const.add (contDiffAt_const.mul hph))).mul
      contDiffAt_const
  have hex := Complex.contDiff_exp.contDiffAt.comp y hre
  have hw0 : ContDiff ℝ 2 (weightPoly e0 e1) := by
    have h : ContDiff ℝ 2 (fun t : ℝ => (((t ^ e0 * (1 - t) ^ e1 : ℝ)) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((contDiff_id.pow e0).mul ((contDiff_const.sub contDiff_id).pow e1))
    exact h
  have hw : ContDiffAt ℝ 2 (fun z => weightPoly e0 e1 (chartCoord P z)) y :=
    hw0.contDiffAt.comp y (chartCoord_contDiffAt P hP.chartLength_pos hy)
  exact hex.mul hw

theorem scalarValue_slopeNear (P : ShapeParams) (κ : FieldKey) (M : ℤ) (s : Bool) (S : PotScalar) (σ : ℝ)
    (hP : IsShapeParams P) (hS : IsJetClass 1 1 S.amp) (hA : AxisAdmissible M s S) {y : Space} (hy : y ≠ 0) :
    SlopeNear (scalarValue P κ M s S σ) y := by
  have hsplit : scalarValue P κ M s S σ = fun z =>
      (Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ + (κ.phaseIndex : ℝ) * P.radialPhase (‖z‖ ^ 2) :
        ℝ) : ℂ) * Complex.I) * weightPoly S.lowOrder S.highOrder (chartCoord P z)) *
      (angPart M s S.axisPower z * S.amp.toSpline.evalHalf (chartCoord P z) (heightRatio z)) := by
    funext z
    unfold scalarValue angPart
    have he : Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ + (M : ℝ) * pointAngle z +
        (κ.phaseIndex : ℝ) * P.radialPhase (‖z‖ ^ 2) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ + (κ.phaseIndex : ℝ) * P.radialPhase (‖z‖ ^ 2) :
          ℝ) : ℂ) * Complex.I) * Complex.exp ((((M : ℝ) * pointAngle z : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    ring
  rw [hsplit]
  exact (slopeNear_of_two (front_contDiffAt P hP _ _ _ _ hy)).mul
    (angSpline_slopeNear P hP.chartLength_pos M s S hS hA hy)

end Internal.AwayFromOrigin

theorem scalarSmoothAwayFromOrigin : ScalarSmoothAwayFromOrigin := by
  intro P κ M s S σ hP hS hA
  refine ⟨fun y hy => (Internal.AwayFromOrigin.scalarValue_slopeNear P κ M s S σ hP hS hA hy).1, fun r R hr => ?_⟩
  have hcpt : IsCompact {y : Space | r ≤ ‖y‖ ∧ ‖y‖ ≤ R} := by
    have hc : IsCompact (Metric.closedBall (0 : Space) R ∩ {y : Space | r ≤ ‖y‖}) :=
      (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_norm)
    convert hc using 1
    ext y
    simp only [mem_ofPred_eq, mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
    tauto
  have hloc : LocallyLipschitzOn {y : Space | r ≤ ‖y‖ ∧ ‖y‖ ≤ R} (fderiv ℝ (scalarValue P κ M s S σ)) := by
    intro y hy
    have hy0 : y ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hr hy.1)
    obtain ⟨K, U, hU, hK⟩ := (Internal.AwayFromOrigin.scalarValue_slopeNear P κ M s S σ hP hS hA hy0).2
    exact ⟨K, U, nhdsWithin_le_nhds hU, hK⟩
  exact hloc.exists_lipschitzOnWith_of_compact hcpt

end PotentialShape

end Breakdown
