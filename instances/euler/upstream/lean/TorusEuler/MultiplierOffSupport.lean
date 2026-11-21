import TorusEuler.DyadicMultiplierKernel
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Normed.Group.AddCircle

/-! Off-support estimates for the dyadic multiplier in Appendix A.2. -/

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped ContDiff SchwartzMap

namespace TorusEuler

noncomputable section

private theorem dyadic_tail_split {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ k : ℕ, 1 ≤ ρ * (2 : ℝ) ^ k ∧ (k = 0 ∨ ρ * (2 : ℝ) ^ k ≤ 2) := by
  have hex : ∃ n : ℕ, 1 ≤ ρ * (2 : ℝ) ^ n := by
    obtain ⟨n, hn⟩ := eventually_atTop.1
      ((tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)).eventually_ge_atTop ρ⁻¹)
    exact ⟨n, (inv_le_iff_one_le_mul₀ hρ).1 (hn n le_rfl) |>.trans_eq (mul_comm _ _)⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  cases hfind : Nat.find hex with
  | zero => exact Or.inl rfl
  | succ n =>
    right
    have hprevious : ρ * (2 : ℝ) ^ n < 1 := lt_of_not_ge
      (Nat.find_min hex (show n < Nat.find hex by rw [hfind]; omega))
    rw [pow_succ, ← mul_assoc]
    linarith

/-- The sum of the first derivatives of dyadic kernels behaves like
distance to the power minus four, uniformly in the number of blocks. -/
theorem dyadicDerivativeWeight_sum_le {ρ : ℝ} (hρ : 0 < ρ) (N : ℕ) :
    (∑ j ∈ Finset.range N, ((2 : ℝ) ^ j) ^ 4 / (1 + (2 : ℝ) ^ j * ρ) ^ 5) ≤
      18 / ρ ^ 4 := by
  let b (j : ℕ) := (2 : ℝ) ^ j
  let w (j : ℕ) := (b j) ^ 4 / (1 + b j * ρ) ^ 5
  have hb (j : ℕ) : 0 < b j := by dsimp [b]; positivity
  have hw (j : ℕ) : 0 ≤ w j := by dsimp [w]; positivity
  obtain ⟨k, hk, hkUpper⟩ := dyadic_tail_split hρ
  change 1 ≤ ρ * b k at hk
  have hLow : (∑ j ∈ Finset.range k, w j) ≤ 16 / ρ ^ 4 := by
    rcases hkUpper with rfl | hUpper
    · simp only [Finset.range_zero, Finset.sum_empty]
      positivity
    have hbound (j : ℕ) : w j ≤ (b j) ^ 4 := by
      unfold w
      apply div_le_self (by positivity)
      apply one_le_pow₀
      linarith [mul_nonneg (hb j).le hρ.le]
    have hgeom : (∑ j ∈ Finset.range k, (b j) ^ 4) ≤ (b k) ^ 4 := by
      have hpower (j : ℕ) : (b j) ^ 4 = (16 : ℝ) ^ j := by
        dsimp only [b]
        rw [← pow_mul, Nat.mul_comm j 4, pow_mul]
        norm_num
      simp_rw [hpower]
      have h := geom_sum_mul (16 : ℝ) k
      have hsum : 0 ≤ ∑ j ∈ Finset.range k, (16 : ℝ) ^ j :=
        Finset.sum_nonneg fun _ _ => by positivity
      norm_num at h
      linarith
    calc
      _ ≤ ∑ j ∈ Finset.range k, (b j) ^ 4 := Finset.sum_le_sum fun _ _ => hbound _
      _ ≤ (b k) ^ 4 := hgeom
      _ ≤ (2 / ρ) ^ 4 := pow_le_pow_left₀ (hb k).le
        ((le_div_iff₀ hρ).mpr (by simpa only [b, mul_comm] using hUpper)) _
      _ = _ := by norm_num [div_pow]
  have hHigh (m : ℕ) : (∑ j ∈ Finset.range m, w (k + j)) ≤ 2 / ρ ^ 4 := by
    have hterm (j : ℕ) : w (k + j) ≤ ((b k)⁻¹ / ρ ^ 5) * (1 / 2 : ℝ) ^ j := by
      calc
        _ ≤ (b (k + j)) ^ 4 / (b (k + j) * ρ) ^ 5 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact pow_le_pow_left₀ (by positivity) (by linarith) _
        _ = _ := by
          simp only [b, pow_add, div_pow, one_pow]
          field_simp
    have hgeom : (∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ j) ≤ 2 := by
      have h := geom_sum_mul (1 / 2 : ℝ) m
      have hpow : 0 ≤ (1 / 2 : ℝ) ^ m := by positivity
      linarith
    have hkinv : (b k)⁻¹ ≤ ρ :=
      (inv_le_iff_one_le_mul₀ (hb k)).mpr (by simpa only [mul_comm] using hk)
    calc
      _ ≤ ∑ j ∈ Finset.range m, ((b k)⁻¹ / ρ ^ 5) * (1 / 2 : ℝ) ^ j :=
        Finset.sum_le_sum fun _ _ => hterm _
      _ ≤ ((b k)⁻¹ / ρ ^ 5) * 2 := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ ≤ (ρ / ρ ^ 5) * 2 :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hkinv (by positivity)) (by norm_num)
      _ = _ := by field_simp
  let n := max N k
  have hNn : N ≤ n := le_max_left _ _
  have hkn : k ≤ n := le_max_right _ _
  change (∑ j ∈ Finset.range N, w j) ≤ _
  calc
    _ ≤ ∑ j ∈ Finset.range n, w j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNn) fun _ _ _ => hw _
    _ = (∑ j ∈ Finset.range k, w j) + ∑ j ∈ Finset.range (n - k), w (k + j) := by
      conv_lhs => rw [← Nat.add_sub_of_le hkn, Finset.sum_range_add]
    _ ≤ 16 / ρ ^ 4 + 2 / ρ ^ 4 := add_le_add hLow (hHigh _)
    _ = _ := by ring

/-- The radial integration constant for the tail of the summed
dyadic derivative bound. -/
def unitInverseFourthPowerTail : ℝ :=
  ∫ z : Vec3 in {z | 1 ≤ ‖z‖}, (‖z‖ ^ 4)⁻¹

private theorem integrable_inverseFourthPower_tail_one :
    Integrable ({z : Vec3 | 1 ≤ ‖z‖}.indicator (fun z => (‖z‖ ^ 4)⁻¹)) := by
  let s : Set Vec3 := {z | 1 ≤ ‖z‖}
  have hmeas : MeasurableSet s := (isClosed_le continuous_const continuous_norm).measurableSet
  have hbracket : Integrable (fun z : Vec3 => (1 + ‖z‖) ^ (-(4 : ℝ))) := by
    apply integrable_one_add_norm
    norm_num [finrank_euclideanSpace_fin]
  apply (hbracket.const_mul 16).mono'
    ((measurable_norm.pow_const 4).inv.indicator hmeas).aestronglyMeasurable
  refine Filter.Eventually.of_forall fun z => ?_
  by_cases hz : z ∈ s
  · rw [Set.indicator_of_mem hz]
    change ‖(‖z‖ ^ 4)⁻¹‖ ≤ _
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
    rw [Real.rpow_neg (by positivity), Real.rpow_ofNat]
    change 1 ≤ ‖z‖ at hz
    have hp : (1 + ‖z‖) ^ 4 ≤ 16 * ‖z‖ ^ 4 := by
      have := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖z‖)
        (show 1 + ‖z‖ ≤ 2 * ‖z‖ by linarith) 4
      simpa only [mul_pow, show (2 : ℝ) ^ 4 = 16 by norm_num] using this
    have hdiv : 1 / ‖z‖ ^ 4 ≤ 16 / (1 + ‖z‖) ^ 4 :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        (by simpa only [one_mul] using hp)
    simpa only [div_eq_mul_inv, one_mul] using hdiv
  · rw [Set.indicator_of_notMem hz, norm_zero]
    positivity

theorem unitInverseFourthPowerTail_nonneg : 0 ≤ unitInverseFourthPowerTail :=
  integral_nonneg (fun _ => inv_nonneg.mpr (by positivity))

private theorem inverseFourthPower_tail_scaled {r : ℝ} (hr : 0 < r) :
    let tail (z : Vec3) := ({z | r ≤ ‖z‖} : Set Vec3).indicator (fun z => (‖z‖ ^ 4)⁻¹) z
    Integrable tail ∧ (∫ z, tail z) = r⁻¹ * unitInverseFourthPowerTail := by
  dsimp only
  let J (z : Vec3) := ({z | 1 ≤ ‖z‖} : Set Vec3).indicator (fun z => (‖z‖ ^ 4)⁻¹) z
  have hscale (z : Vec3) : ‖r⁻¹ • z‖ = ‖z‖ / r := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), div_eq_mul_inv, mul_comm]
  have heq : ({z | r ≤ ‖z‖} : Set Vec3).indicator (fun z => (‖z‖ ^ 4)⁻¹) =
      ((r ^ 4)⁻¹ : ℝ) • (fun z : Vec3 => J (r⁻¹ • z)) := by
    funext z
    by_cases hz : r ≤ ‖z‖
    · have hmem : z ∈ {w : Vec3 | r ≤ ‖w‖} := hz
      rw [Set.indicator_of_mem hmem]
      have hscaled : 1 ≤ ‖r⁻¹ • z‖ := by rw [hscale, le_div_iff₀ hr, one_mul]; exact hz
      have hscaledMem : r⁻¹ • z ∈ {w : Vec3 | 1 ≤ ‖w‖} := hscaled
      change (‖z‖ ^ 4)⁻¹ = (r ^ 4)⁻¹ * J (r⁻¹ • z)
      dsimp only [J]
      rw [Set.indicator_of_mem hscaledMem]
      rw [hscale]
      have hzpos : 0 < ‖z‖ := hr.trans_le hz
      field_simp
    · have hscaled : ¬ 1 ≤ ‖r⁻¹ • z‖ := by rwa [hscale, le_div_iff₀ hr, one_mul]
      have hnotmem : z ∉ {w : Vec3 | r ≤ ‖w‖} := hz
      have hscaledNotmem : r⁻¹ • z ∉ {w : Vec3 | 1 ≤ ‖w‖} := hscaled
      rw [Set.indicator_of_notMem hnotmem]
      change 0 = (r ^ 4)⁻¹ * J (r⁻¹ • z)
      dsimp only [J]
      rw [Set.indicator_of_notMem hscaledNotmem]
      exact (mul_zero _).symm
  rw [heq]
  constructor
  · exact ((integrable_comp_smul_iff volume J (inv_ne_zero hr.ne')).mpr
      integrable_inverseFourthPower_tail_one).smul _
  · change (∫ z : Vec3, (r ^ 4)⁻¹ • J (r⁻¹ • z)) = _
    rw [integral_smul, integral_comp_smul_of_nonneg volume J (r⁻¹) (hR := inv_nonneg.mpr hr.le),
      finrank_euclideanSpace_fin, smul_smul]
    change _ * (∫ z, J z) = _
    have hJ : (∫ z, J z) = unitInverseFourthPowerTail := by
      exact integral_indicator (isClosed_le continuous_const continuous_norm).measurableSet
    rw [hJ]
    congr 1
    field_simp

/-- The Euclidean geodesic distance on the flat unit torus, using the
shortest distances in each coordinate. -/
def torusEuclideanDistance (a b : UnitAddTorus (Fin 3)) : ℝ :=
  Real.sqrt (∑ i : Fin 3, dist (a i) (b i) ^ 2)

theorem dist_le_torusEuclideanDistance (a b : UnitAddTorus (Fin 3)) :
    dist a b ≤ torusEuclideanDistance a b := by
  unfold torusEuclideanDistance
  apply (dist_pi_le_iff (Real.sqrt_nonneg _)).mpr
  intro i
  apply (Real.le_sqrt dist_nonneg (by positivity)).mpr
  exact Finset.single_le_sum (f := fun j => dist (a j) (b j) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem torusEuclideanDistance_le_two_dist (a b : UnitAddTorus (Fin 3)) :
    torusEuclideanDistance a b ≤ 2 * dist a b := by
  unfold torusEuclideanDistance
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have hcoord : ∀ i, dist (a i) (b i) ≤ dist a b :=
    (dist_pi_le_iff dist_nonneg).mp le_rfl
  calc
    _ ≤ ∑ _ : Fin 3, dist a b ^ 2 :=
      Finset.sum_le_sum fun i _ => pow_le_pow_left₀ dist_nonneg (hcoord i) _
    _ = 3 * dist a b ^ 2 := by simp [nsmul_eq_mul]
    _ ≤ _ := by nlinarith only [sq_nonneg (dist a b)]

private theorem torusEuclideanDistance_lifts (x a : Vec3) :
    torusEuclideanDistance (toUnitTorus x) (toUnitTorus a) =
      Real.sqrt (∑ i : Fin 3, |x i - a i - (round (x i - a i) : ℝ)| ^ 2) := by
  unfold torusEuclideanDistance
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change dist ((x i : ℝ) : UnitAddCircle) ((a i : ℝ) : UnitAddCircle) = _
  rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq]
  simp

theorem torusEuclideanDistance_le_lift (x a : Vec3) :
    torusEuclideanDistance (toUnitTorus x) (toUnitTorus a) ≤ ‖x - a‖ := by
  rw [torusEuclideanDistance_lifts, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  apply pow_le_pow_left₀ (abs_nonneg _)
  change |x i - a i - (round (x i - a i) : ℝ)| ≤ ‖x i - a i‖
  simpa only [Int.cast_zero, sub_zero, Real.norm_eq_abs] using round_le (x i - a i) 0

/-- Rounding translates a point to a nearest lattice representative. -/
theorem exists_nearestTorusLift (x a : Vec3) :
    ∃ x' : Vec3, toUnitTorus x' = toUnitTorus x ∧
      ‖x' - a‖ = torusEuclideanDistance (toUnitTorus x) (toUnitTorus a) := by
  let n : Fin 3 → ℤ := fun i => round (x i - a i)
  let x' := x - latticeVector n
  refine ⟨x', ((toUnitTorus_eq_iff x x').mpr ⟨n, by dsimp only [x']; abel⟩).symm, ?_⟩
  rw [torusEuclideanDistance_lifts, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change ‖x i - (n i : ℝ) - a i‖ ^ 2 = |x i - a i - (n i : ℝ)| ^ 2
  rw [Real.norm_eq_abs, show x i - (n i : ℝ) - a i = x i - a i - (n i : ℝ) by abel]

section OperatorKernel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

private theorem operatorLiftConvolution_swap (K : Vec3 → E →L[ℂ] F) (f : Vec3 → E) (x : Vec3) :
    operatorLiftConvolution K f x = ∫ z, K (x - z) (f z) := by
  unfold operatorLiftConvolution
  rw [← integral_sub_left_eq_self _ volume x]
  simp only [sub_sub_cancel]

private theorem operatorLiftConvolution_sum {ι : Type*} (s : Finset ι)
    (K : ι → Vec3 → E →L[ℂ] F) (hK : ∀ i ∈ s, Integrable (K i))
    {f : Vec3 → E} (hf : Continuous f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) (x : Vec3) :
    operatorLiftConvolution (fun z => ∑ j ∈ s, K j z) f x =
      ∑ j ∈ s, operatorLiftConvolution (K j) f x := by
  have heq (y : Vec3) : (∑ j ∈ s, K j y) (f (x - y)) = ∑ j ∈ s, K j y (f (x - y)) :=
    _root_.map_sum (ContinuousLinearMap.apply ℂ F (f (x - y))) (fun j => K j y) s
  have hI (i : ι) (hi : i ∈ s) : Integrable (fun y => K i y (f (x - y))) :=
    integrable_operatorLiftConvolution (hK i hi) hf hM x
  simp only [operatorLiftConvolution, heq]
  exact integral_finsetSum s hI

private theorem norm_kernel_sub_le_away
    {K : Vec3 → E →L[ℂ] F} (hD : Differentiable ℝ K) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ w, 0 < ‖w‖ → ‖fderiv ℝ K w‖ ≤ C * (‖w‖ ^ 4)⁻¹)
    {a x y z : Vec3} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ Metric.closedBall a (r / 2)) (hy : y ∈ Metric.closedBall a (r / 2))
    (hz : r ≤ ‖z - a‖) :
    ‖K (x - z) - K (y - z)‖ ≤ (16 * C) * (‖z - a‖ ^ 4)⁻¹ * ‖x - y‖ := by
  let g (p : Vec3) := K (p - z)
  have hDeriv (p : Vec3) : HasFDerivAt g (fderiv ℝ K (p - z)) p := by
    simpa only [g, Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      ((hD (p - z)).hasFDerivAt.comp p ((hasFDerivAt_id p).sub_const z))
  have hpoint (p : Vec3) (hp : p ∈ Metric.closedBall a (r / 2)) :
      ‖fderiv ℝ g p‖ ≤ (16 * C) * (‖z - a‖ ^ 4)⁻¹ := by
    have hp' : ‖p - a‖ ≤ r / 2 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hp
    have htri : ‖z - a‖ ≤ ‖p - z‖ + ‖p - a‖ := by
      simpa only [dist_eq_norm, norm_sub_rev z p] using dist_triangle z p a
    have hhalf : ‖z - a‖ / 2 ≤ ‖p - z‖ := by linarith
    have hhalfpos : 0 < ‖z - a‖ / 2 := half_pos (hr.trans_le hz)
    have hpz : 0 < ‖p - z‖ := hhalfpos.trans_le hhalf
    rw [(hDeriv p).fderiv]
    calc
      _ ≤ C * (‖p - z‖ ^ 4)⁻¹ := hbound _ hpz
      _ ≤ C * ((‖z - a‖ / 2) ^ 4)⁻¹ :=
        mul_le_mul_of_nonneg_left
          (inv_anti₀ (pow_pos hhalfpos _) (pow_le_pow_left₀ hhalfpos.le hhalf _)) hC
      _ = _ := by
        have hzpos : 0 < ‖z - a‖ := hr.trans_le hz
        rw [div_pow]
        field_simp
        norm_num
  exact (convex_closedBall a (r / 2)).norm_image_sub_le_of_norm_fderiv_le
    (fun p _ => (hDeriv p).differentiableAt) hpoint hy hx

/-- Integration against a source vanishing on the radius-`r` ball gives
an off-support Lipschitz estimate on the entire concentric half-ball. -/
theorem norm_sub_operatorLiftConvolution_le_off_support
    {K : Vec3 → E →L[ℂ] F} (hK : Integrable K) (hD : Differentiable ℝ K) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ w, 0 < ‖w‖ → ‖fderiv ℝ K w‖ ≤ C * (‖w‖ ^ 4)⁻¹)
    {f : Vec3 → E} (hf : Continuous f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M)
    {a x y : Vec3} {r : ℝ} (hr : 0 < r) (hzero : ∀ z ∈ Metric.closedBall a r, f z = 0)
    (hx : x ∈ Metric.closedBall a (r / 2)) (hy : y ∈ Metric.closedBall a (r / 2)) :
    ‖operatorLiftConvolution K f x - operatorLiftConvolution K f y‖ ≤
      (16 * C * unitInverseFourthPowerTail / r) * M * ‖x - y‖ := by
  let R (z : Vec3) := ({w | r ≤ ‖w‖} : Set Vec3).indicator (fun w => (‖w‖ ^ 4)⁻¹) z
  obtain ⟨hR, hRInt⟩ := inverseFourthPower_tail_scaled hr
  change Integrable R at hR
  change (∫ z, R z) = _ at hRInt
  let A := 16 * C * M * ‖x - y‖
  have hmajor : Integrable (fun z => A * R (z - a)) :=
    (hR.comp_sub_right a).const_mul A
  have hSwapIntegrable (p : Vec3) : Integrable (fun z => K (p - z) (f z)) := by
    have h :=
      (integrable_operatorLiftConvolution hK hf hM p).comp_sub_left p
    simpa only [sub_sub_cancel] using h
  rw [operatorLiftConvolution_swap, operatorLiftConvolution_swap,
    ← integral_sub (hSwapIntegrable x) (hSwapIntegrable y)]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc
    _ ≤ ∫ z, A * R (z - a) := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hmajor
      refine Eventually.of_forall fun z => ?_
      change ‖K (x - z) (f z) - K (y - z) (f z)‖ ≤ A * R (z - a)
      by_cases hz : r ≤ ‖z - a‖
      · have hnorm := norm_kernel_sub_le_away hD hC hbound hr hx hy hz
        have hmem : z - a ∈ {w : Vec3 | r ≤ ‖w‖} := hz
        have hRz : R (z - a) = (‖z - a‖ ^ 4)⁻¹ := Set.indicator_of_mem hmem _
        rw [hRz]
        calc
          ‖K (x - z) (f z) - K (y - z) (f z)‖ ≤ ‖K (x - z) - K (y - z)‖ * M :=
            (K (x - z) - K (y - z)).le_opNorm_of_le (hM _)
          _ ≤ ((16 * C) * (‖z - a‖ ^ 4)⁻¹ * ‖x - y‖) * M :=
            mul_le_mul_of_nonneg_right hnorm ((norm_nonneg _).trans (hM z))
          _ = A * (‖z - a‖ ^ 4)⁻¹ := by unfold A; ring
      · have hz' : z ∈ Metric.closedBall a r := by
          rw [Metric.mem_closedBall, dist_eq_norm]
          exact le_of_lt (lt_of_not_ge hz)
        have hnotmem : z - a ∉ {w : Vec3 | r ≤ ‖w‖} := hz
        have hRz : R (z - a) = 0 := Set.indicator_of_notMem hnotmem _
        simp only [hzero z hz', hRz, map_zero, sub_self, norm_zero, mul_zero, le_refl]
    _ = _ := by
      rw [integral_const_mul, integral_sub_right_eq_self, hRInt]
      unfold A
      ring_nf

set_option maxHeartbeats 500000 in
/-- The common far-field bound is uniform over all finite dyadic sums. -/
theorem norm_sub_operatorLiftConvolution_dyadicPartialSum_le_off_support
    (K : ℕ → Vec3 → E →L[ℂ] F) (hK : ∀ j, Integrable (K j))
    (hD : ∀ j, Differentiable ℝ (K j)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ j (w : Vec3),
      (1 + (2 : ℝ) ^ j * ‖w‖) ^ 5 * ‖fderiv ℝ (K j) w‖ ≤ C * ((2 : ℝ) ^ j) ^ 4)
    {f : Vec3 → E} (hf : Continuous f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M)
    {a x y : Vec3} {r : ℝ} (hr : 0 < r) (hzero : ∀ z ∈ Metric.closedBall a r, f z = 0)
    (hx : x ∈ Metric.closedBall a (r / 2)) (hy : y ∈ Metric.closedBall a (r / 2)) (N : ℕ) :
    ‖(∑ j ∈ Finset.range N, operatorLiftConvolution (K j) f x) -
      (∑ j ∈ Finset.range N, operatorLiftConvolution (K j) f y)‖ ≤
      (16 * (18 * C) * unitInverseFourthPowerTail / r) * M * ‖x - y‖ := by
  let KN (z : Vec3) := ∑ j ∈ Finset.range N, K j z
  have hKN : Integrable KN :=
    integrable_finsetSum (μ := (volume : Measure Vec3)) (f := K) (Finset.range N) fun j _ => hK j
  have hND : Differentiable ℝ KN := Differentiable.fun_sum fun j _ => hD j
  have hNDiff (w : Vec3) (hw : 0 < ‖w‖) :
      ‖fderiv ℝ KN w‖ ≤ (18 * C) * (‖w‖ ^ 4)⁻¹ := by
    have hstep (j : ℕ) : ‖fderiv ℝ (K j) w‖ ≤ C *
        (((2 : ℝ) ^ j) ^ 4 / (1 + (2 : ℝ) ^ j * ‖w‖) ^ 5) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (by positivity)).mpr
      simpa only [mul_comm] using hbound j w
    rw [show fderiv ℝ KN w = ∑ j ∈ Finset.range N, fderiv ℝ (K j) w from
      fderiv_fun_sum fun j _ => hD j w]
    calc
      _ ≤ ∑ j ∈ Finset.range N, ‖fderiv ℝ (K j) w‖ :=
        norm_sum_le (E := Vec3 →L[ℝ] (E →L[ℂ] F)) (Finset.range N) (fun j => fderiv ℝ (K j) w)
      _ ≤ ∑ j ∈ Finset.range N, C *
          (((2 : ℝ) ^ j) ^ 4 / (1 + (2 : ℝ) ^ j * ‖w‖) ^ 5) :=
        Finset.sum_le_sum fun _ _ => hstep _
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact (mul_le_mul_of_nonneg_left (dyadicDerivativeWeight_sum_le hw N) hC).trans_eq (by ring)
  have hconv (p : Vec3) :
      operatorLiftConvolution KN f p = ∑ j ∈ Finset.range N, operatorLiftConvolution (K j) f p :=
    operatorLiftConvolution_sum (Finset.range N) K (fun j _ => hK j) hf hM p
  rw [← hconv x, ← hconv y]
  exact norm_sub_operatorLiftConvolution_le_off_support hKN hND (by positivity) hNDiff
    hf hM hr hzero hx hy

/-- Pointwise limits inherit the uniform off-support estimate. -/
theorem norm_sub_operatorLiftConvolution_dyadicLimit_le_off_support
    (K : ℕ → Vec3 → E →L[ℂ] F) (hK : ∀ j, Integrable (K j))
    (hD : ∀ j, Differentiable ℝ (K j)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ j (w : Vec3),
      (1 + (2 : ℝ) ^ j * ‖w‖) ^ 5 * ‖fderiv ℝ (K j) w‖ ≤ C * ((2 : ℝ) ^ j) ^ 4)
    {f : Vec3 → E} (hf : Continuous f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M)
    {u : Vec3 → F} (hLimit : ∀ p,
      Tendsto (fun N => ∑ j ∈ Finset.range N, operatorLiftConvolution (K j) f p) atTop (nhds (u p)))
    {a x y : Vec3} {r : ℝ} (hr : 0 < r) (hzero : ∀ z ∈ Metric.closedBall a r, f z = 0)
    (hx : x ∈ Metric.closedBall a (r / 2)) (hy : y ∈ Metric.closedBall a (r / 2)) :
    ‖u x - u y‖ ≤ (16 * (18 * C) * unitInverseFourthPowerTail / r) * M * ‖x - y‖ :=
  le_of_tendsto ((hLimit x).sub (hLimit y)).norm (Eventually.of_forall
    (norm_sub_operatorLiftConvolution_dyadicPartialSum_le_off_support K hK hD hC hbound hf hM
      hr hzero hx hy))

/-- The far-field quotient bound on the torus uses a shortest lifted
segment from the center to the neighboring point. -/
theorem norm_sub_dyadicLimit_torus_le_off_support
    (K : ℕ → Vec3 → E →L[ℂ] F) (hK : ∀ j, Integrable (K j))
    (hD : ∀ j, Differentiable ℝ (K j)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ j (w : Vec3),
      (1 + (2 : ℝ) ^ j * ‖w‖) ^ 5 * ‖fderiv ℝ (K j) w‖ ≤ C * ((2 : ℝ) ^ j) ^ 4)
    {f : UnitAddTorus (Fin 3) → E} (hf : Continuous (fun z => f (toUnitTorus z)))
    {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M)
    {u : UnitAddTorus (Fin 3) → F} (hLimit : ∀ p,
      Tendsto (fun N => ∑ j ∈ Finset.range N,
        operatorLiftConvolution (K j) (fun z => f (toUnitTorus z)) p) atTop (nhds (u (toUnitTorus p))))
    {a b : UnitAddTorus (Fin 3)} {r : ℝ} (hr : 0 < r)
    (hzero : ∀ z, torusEuclideanDistance z a ≤ r → f z = 0)
    (hb : torusEuclideanDistance b a ≤ r / 2) :
    ‖u a - u b‖ ≤ (16 * (18 * C) * unitInverseFourthPowerTail / r) * M *
      torusEuclideanDistance b a := by
  obtain ⟨a', ha⟩ := toUnitTorus_surjective a
  obtain ⟨b', hb'⟩ := toUnitTorus_surjective b
  obtain ⟨b'', hb'', hmin⟩ := exists_nearestTorusLift b' a'
  rw [hb', ha] at hmin
  have hvanish (z : Vec3) (hz : z ∈ Metric.closedBall a' r) : f (toUnitTorus z) = 0 := by
    apply hzero
    rw [← ha]
    exact (torusEuclideanDistance_le_lift z a').trans
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz)
  have haClose : a' ∈ Metric.closedBall a' (r / 2) :=
    Metric.mem_closedBall_self (half_pos hr).le
  have hbClose : b'' ∈ Metric.closedBall a' (r / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm, hmin]
    exact hb
  have h := norm_sub_operatorLiftConvolution_dyadicLimit_le_off_support K hK hD hC hbound
    hf (fun z => hM (toUnitTorus z)) hLimit hr hvanish haClose hbClose
  simpa only [ha, hb'', hb', norm_sub_rev a' b'', hmin] using h

/-- The same bound for the product metric used by the torus Hölder space. -/
theorem norm_sub_dyadicLimit_torus_productMetric_le_off_support
    (K : ℕ → Vec3 → E →L[ℂ] F) (hK : ∀ j, Integrable (K j))
    (hD : ∀ j, Differentiable ℝ (K j)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ j (w : Vec3),
      (1 + (2 : ℝ) ^ j * ‖w‖) ^ 5 * ‖fderiv ℝ (K j) w‖ ≤ C * ((2 : ℝ) ^ j) ^ 4)
    {f : UnitAddTorus (Fin 3) → E} (hf : Continuous (fun z => f (toUnitTorus z)))
    {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M)
    {u : UnitAddTorus (Fin 3) → F} (hLimit : ∀ p,
      Tendsto (fun N => ∑ j ∈ Finset.range N,
        operatorLiftConvolution (K j) (fun z => f (toUnitTorus z)) p) atTop (nhds (u (toUnitTorus p))))
    {a b : UnitAddTorus (Fin 3)} {r : ℝ} (hr : 0 < r)
    (hzero : ∀ z, dist z a ≤ r → f z = 0) (hb : dist b a ≤ r / 4) :
    ‖u a - u b‖ ≤ (32 * (18 * C) * unitInverseFourthPowerTail / r) * M * dist b a := by
  have hClose : torusEuclideanDistance b a ≤ r / 2 := by
    have := torusEuclideanDistance_le_two_dist b a
    linarith
  have hFar (z : UnitAddTorus (Fin 3)) (hz : torusEuclideanDistance z a ≤ r) : f z = 0 :=
    hzero z ((dist_le_torusEuclideanDistance z a).trans hz)
  have hM₀ := (norm_nonneg (f a)).trans (hM a)
  have hTail := unitInverseFourthPowerTail_nonneg
  calc
    _ ≤ (16 * (18 * C) * unitInverseFourthPowerTail / r) * M *
        torusEuclideanDistance b a :=
      norm_sub_dyadicLimit_torus_le_off_support K hK hD hC hbound hf hM hLimit hr hFar hClose
    _ ≤ (16 * (18 * C) * unitInverseFourthPowerTail / r) * M * (2 * dist b a) :=
      mul_le_mul_of_nonneg_left (torusEuclideanDistance_le_two_dist b a) (by positivity)
    _ = _ := by ring

/-- The concrete dyadic kernels of a fixed smooth localized symbol give the
off-support estimate once their sum represents the torus multiplier. -/
theorem norm_sub_compactMultiplierDyadicLimit_le_off_support [CompleteSpace F]
    {symbol : Vec3 → E →L[ℂ] F} (hSupport : HasCompactSupport symbol) (hs : ContDiff ℝ ∞ symbol)
    {f : UnitAddTorus (Fin 3) → E} (hf : Continuous (fun z => f (toUnitTorus z)))
    {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M)
    {u : UnitAddTorus (Fin 3) → F} (hLimit : ∀ p,
      Tendsto (fun N => ∑ j ∈ Finset.range N,
        operatorLiftConvolution (scaledMultiplierKernel ((2 : ℝ) ^ j) (compactMultiplierKernel hSupport hs))
          (fun z => f (toUnitTorus z)) p) atTop (nhds (u (toUnitTorus p))))
    {a b : UnitAddTorus (Fin 3)} {r : ℝ} (hr : 0 < r)
    (hzero : ∀ z, dist z a ≤ r → f z = 0) (hb : dist b a ≤ r / 4) :
    let C := 32 * ((1 + 2 * Real.pi) * (4 : ℝ) ^ 5 * multiplierDerivativeMass symbol)
    ‖u a - u b‖ ≤ (32 * (18 * C) * unitInverseFourthPowerTail / r) * M * dist b a := by
  let K₀ : 𝓢(Vec3, E →L[ℂ] F) := compactMultiplierKernel hSupport hs
  let K (j : ℕ) := scaledMultiplierKernel ((2 : ℝ) ^ j) K₀
  have hInt (j : ℕ) : Integrable (K j) :=
    integrable_scaledMultiplierKernel (by positivity) K₀.integrable
  have hDiff (j : ℕ) : Differentiable ℝ (K j) :=
    (K₀.differentiable.comp (differentiable_id.const_smul ((2 : ℝ) ^ j))).const_smul _
  let C := 32 * ((1 + 2 * Real.pi) * (4 : ℝ) ^ 5 * multiplierDerivativeMass symbol)
  have hMass := multiplierDerivativeMass_nonneg symbol
  have hC : 0 ≤ C := by unfold C; positivity
  have hKernel (j : ℕ) (w : Vec3) :
      (1 + (2 : ℝ) ^ j * ‖w‖) ^ 5 * ‖fderiv ℝ (K j) w‖ ≤ C * ((2 : ℝ) ^ j) ^ 4 := by
    have h := scaledMultiplierKernel_decay (hSupport.toSchwartzMap hs)
      (Λ := (2 : ℝ) ^ j) (by positivity) (d := 1) le_rfl w
    rw [norm_iteratedFDeriv_one] at h
    change _ ≤ ((2 : ℝ) ^ j) ^ 4 * C at h
    exact h.trans_eq (mul_comm _ _)
  exact norm_sub_dyadicLimit_torus_productMetric_le_off_support K hInt hDiff hC hKernel
    hf hM hLimit hr hzero hb

end OperatorKernel

end

end TorusEuler
