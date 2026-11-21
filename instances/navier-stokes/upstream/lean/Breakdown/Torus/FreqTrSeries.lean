import Breakdown.Torus.StatementsCoeff

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FreqTrSeries.Internal

theorem cell_eq_image : cell = WithLp.toLp 2 '' Icc (0 : Fin 3 → ℝ) 1 := by
  ext x
  constructor
  · intro hx
    refine ⟨x.ofLp, ⟨fun i => (hx i).1, fun i => (hx i).2⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩ i
    exact ⟨hy.1 i, hy.2 i⟩

theorem isCompact_cell : IsCompact cell := by
  rw [cell_eq_image]
  exact isCompact_Icc.image (PiLp.continuous_toLp 2 _)

theorem continuous_complexify : Continuous complexify := by
  unfold complexify
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ i))

theorem continuous_character (k : Lattice) : Continuous (character k) := by
  unfold character
  fun_prop

theorem norm_character (k : Lattice) (x : Space) : ‖character k x‖ = 1 := by
  simp [character, Complex.norm_exp]

theorem integrableOn_coef {g : Space → Space} (hg : Continuous g) (k : Lattice) :
    IntegrableOn (fun x => character k x • complexify (g x)) cell := by
  exact ((continuous_character k).smul (continuous_complexify.comp hg)).continuousOn.integrableOn_compact
    isCompact_cell

theorem complexify_sub (a b : Space) : complexify (a - b) = complexify a - complexify b := by
  ext i
  simp [complexify]

theorem freqTrCoef_sub {g h : Space → Space} (hg : Continuous g) (hh : Continuous h) (k : Lattice) :
    freqTrCoef (fun x => g x - h x) k = freqTrCoef g k - freqTrCoef h k := by
  unfold freqTrCoef
  rw [← integral_sub (integrableOn_coef hg k) (integrableOn_coef hh k)]
  congr 1
  funext x
  rw [complexify_sub, smul_sub]

theorem norm_freqTrCoef_le {g : Space → Space} (k : Lattice) :
    ‖freqTrCoef g k‖ ≤ ∫ x in cell, ‖complexify (g x)‖ := by
  unfold freqTrCoef
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext x
  rw [norm_smul, norm_character, one_mul]

def partialD (i : Fin 3) (g : Space → Space) : Space → Space := fun x => fderiv ℝ g x (unitVector i)

theorem contDiff_partialD (i : Fin 3) {g : Space → Space} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (partialD i g) :=
  (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem isPeriodic_partialD (i : Fin 3) {g : Space → Space} (hg : IsPeriodic g) :
    IsPeriodic (partialD i g) := by
  intro j x
  have h : (fun y => g (y + unitVector j)) = g := funext (hg j)
  simp only [partialD]
  rw [← fderiv_comp_add_right, h]

theorem contDiff_one {g : Space → Space} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ 1 g :=
  hg.of_le (by exact_mod_cast le_top)

theorem freqTrCoef_partialD (hD : CoefDeriv) (i : Fin 3) {g : Space → Space} (hg : ContDiff ℝ ∞ g)
    (hp : IsPeriodic g) (k : Lattice) :
    freqTrCoef (partialD i g) k = (2 * π * Complex.I * (k i : ℂ)) • freqTrCoef g k :=
  hD g (contDiff_one hg) hp i k

def sspOp (i : Fin 3) (g : Space → Space) : Space → Space := fun x => g x - partialD i (partialD i g) x

theorem contDiff_sspOp (i : Fin 3) {g : Space → Space} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (sspOp i g) :=
  hg.sub (contDiff_partialD i (contDiff_partialD i hg))

theorem isPeriodic_sspOp (i : Fin 3) {g : Space → Space} (hg : IsPeriodic g) :
    IsPeriodic (sspOp i g) := by
  intro j x
  simp only [sspOp]
  rw [hg j x, isPeriodic_partialD i (isPeriodic_partialD i hg) j x]

theorem freqTrCoef_sspOp (hD : CoefDeriv) (i : Fin 3) {g : Space → Space} (hg : ContDiff ℝ ∞ g)
    (hp : IsPeriodic g) (k : Lattice) :
    freqTrCoef (sspOp i g) k = ((1 + 4 * π ^ 2 * (k i : ℝ) ^ 2 : ℝ) : ℂ) • freqTrCoef g k := by
  unfold sspOp
  rw [freqTrCoef_sub hg.continuous (contDiff_partialD i (contDiff_partialD i hg)).continuous,
    freqTrCoef_partialD hD i (contDiff_partialD i hg) (isPeriodic_partialD i hp),
    freqTrCoef_partialD hD i hg hp, smul_smul]
  conv_lhs => rw [← one_smul ℂ (freqTrCoef g k)]
  rw [smul_smul, ← sub_smul, mul_one]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem decay (hD : CoefDeriv) {f : Space → Space} (hf : ContDiff ℝ ∞ f) (hp : IsPeriodic f) :
    ∃ B : ℝ, ∀ k : Lattice, ‖freqTrCoef f k‖ * ∏ i, (1 + 4 * π ^ 2 * (k i : ℝ) ^ 2) ≤ B := by
  refine ⟨∫ x in cell, ‖complexify (sspOp 0 (sspOp 1 (sspOp 2 f)) x)‖, fun k => ?_⟩
  refine le_of_eq_of_le ?_ (norm_freqTrCoef_le k)
  rw [freqTrCoef_sspOp hD 0 (contDiff_sspOp 1 (contDiff_sspOp 2 hf))
      (isPeriodic_sspOp 1 (isPeriodic_sspOp 2 hp)),
    freqTrCoef_sspOp hD 1 (contDiff_sspOp 2 hf) (isPeriodic_sspOp 2 hp),
    freqTrCoef_sspOp hD 2 hf hp, norm_smul, norm_smul, norm_smul, Fin.prod_univ_three]
  simp only [Complex.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + 4 * π ^ 2 * (k _ : ℝ) ^ 2)]
  ring

theorem summable_inv_int : Summable (fun n : ℤ => (1 + 4 * π ^ 2 * (n : ℝ) ^ 2)⁻¹) := by
  have hs : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2 + if n = 0 then 1 else 0) :=
    (Real.summable_one_div_int_pow.mpr one_lt_two).add (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  refine hs.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  by_cases h : n = 0
  · subst h
    simp
  · have hn : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    simp only [h, if_false, add_zero, one_div]
    apply inv_anti₀ hn
    have h4 : 1 ≤ 4 * π ^ 2 := by nlinarith [pi_gt_three]
    nlinarith [mul_le_mul_of_nonneg_right h4 hn.le]

theorem summable_prod_of_nonneg {g : ℤ → ℝ} (h0 : ∀ n, 0 ≤ g n) (hs : Summable g) :
    Summable (fun k : Lattice => ∏ i, g (k i)) := by
  classical
  refine summable_of_sum_le (c := ∏ _i : Fin 3, ∑' n, g n)
    (fun k => Finset.prod_nonneg fun i _ => h0 _) (fun u => ?_)
  have hsub : u ⊆ Fintype.piFinset (fun i => u.image (fun k : Lattice => k i)) := by
    intro k hk
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image_of_mem _ hk
  calc ∑ k ∈ u, ∏ i, g (k i)
      ≤ ∑ k ∈ Fintype.piFinset (fun i => u.image (fun k : Lattice => k i)), ∏ i, g (k i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun k _ _ => Finset.prod_nonneg fun i _ => h0 _)
    _ = ∏ i, ∑ n ∈ u.image (fun k : Lattice => k i), g n := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ _i : Fin 3, ∑' n, g n :=
        Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun n _ => h0 n)
          (fun i _ => hs.sum_le_tsum _ (fun n _ => h0 n))

theorem freq_apply (k : Lattice) (i : Fin 3) : (freq k).ofLp i = (k i : ℝ) := by
  simp [freq, unitVector, WithLp.ofLp_sum, Pi.single_apply]

theorem norm_freq_sq (k : Lattice) : ‖freq k‖ ^ 2 = ∑ i, (k i : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [freq_apply]

theorem weight_le_prod (k : Lattice) : weight k ≤ ∏ i, (1 + 4 * π ^ 2 * (k i : ℝ) ^ 2) := by
  rw [weight, norm_freq_sq, Fin.sum_univ_three, Fin.prod_univ_three]
  have h0 : 0 ≤ 4 * π ^ 2 * (k 0 : ℝ) ^ 2 := by positivity
  have h1 : 0 ≤ 4 * π ^ 2 * (k 1 : ℝ) ^ 2 := by positivity
  have h2 : 0 ≤ 4 * π ^ 2 * (k 2 : ℝ) ^ 2 := by positivity
  nlinarith [mul_nonneg h0 h1, mul_nonneg (mul_nonneg h0 h1) h2, mul_nonneg h1 h2, mul_nonneg h0 h2]

theorem weight_pos (k : Lattice) : 0 < weight k := by
  unfold weight
  positivity

theorem summable_bounds (hD : CoefDeriv) {f : Space → Space} (hf : ContDiff ℝ ∞ f) (hp : IsPeriodic f) :
    Summable (fun k => ‖freqTrCoef f k‖) ∧ Summable (fun k => weight k * ‖freqTrCoef f k‖ ^ 2) := by
  obtain ⟨B, hB⟩ := decay hD hf hp
  have hg := summable_prod_of_nonneg (fun n => by positivity) summable_inv_int
  have hP : ∀ k : Lattice, 0 < ∏ i, (1 + 4 * π ^ 2 * (k i : ℝ) ^ 2) :=
    fun k => Finset.prod_pos fun i _ => by positivity
  have hc : ∀ k : Lattice,
      ‖freqTrCoef f k‖ ≤ B * ∏ i, (1 + 4 * π ^ 2 * (k i : ℝ) ^ 2)⁻¹ := by
    intro k
    rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ (hP k)]
    exact hB k
  have hB0 : 0 ≤ B := le_trans (by positivity) (hB 0)
  refine ⟨(hg.mul_left B).of_nonneg_of_le (fun k => norm_nonneg _) hc,
    (hg.mul_left (B * B)).of_nonneg_of_le (fun k => mul_nonneg (weight_pos k).le (by positivity))
      (fun k => ?_)⟩
  have hck := hc k
  have hBk := hB k
  have hw := weight_le_prod k
  have hPk := hP k
  have hn := norm_nonneg (freqTrCoef f k)
  rw [Finset.prod_inv_distrib] at hck ⊢
  set P := ∏ i, (1 + 4 * π ^ 2 * (k i : ℝ) ^ 2)
  set c := ‖freqTrCoef f k‖
  have hPi : P * P⁻¹ = 1 := mul_inv_cancel₀ hPk.ne'
  calc weight k * c ^ 2 ≤ P * c ^ 2 := by gcongr
    _ = (c * P) * c := by ring
    _ ≤ B * (B * P⁻¹) := mul_le_mul hBk hck hn hB0
    _ = B * B * P⁻¹ := by ring

theorem character_neg (k : Lattice) (x : Space) : character (-k) x = starRingEnd ℂ (character k x) := by
  have h : freq (-k) = -freq k := by
    simp [freq, Finset.sum_neg_distrib, neg_smul]
  simp only [character, h, inner_neg_left, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  congr 1
  push_cast
  ring

theorem freqTrCoef_apply {g : Space → Space} (hg : Continuous g) (k : Lattice) (i : Fin 3) :
    (freqTrCoef g k).ofLp i = ∫ x in cell, character k x * ((g x).ofLp i : ℂ) := by
  have h := (EuclideanSpace.proj (𝕜 := ℂ) i).integral_comp_comm (integrableOn_coef hg k)
  unfold freqTrCoef
  change EuclideanSpace.proj (𝕜 := ℂ) i _ = _
  rw [← h]
  rfl

theorem freqTrCoef_neg_apply {g : Space → Space} (hg : Continuous g) (k : Lattice) (i : Fin 3) :
    (freqTrCoef g (-k)).ofLp i = starRingEnd ℂ ((freqTrCoef g k).ofLp i) := by
  rw [freqTrCoef_apply hg, freqTrCoef_apply hg, ← integral_conj]
  congr 1
  funext x
  rw [character_neg, map_mul, Complex.conj_ofReal]

theorem divPairing_freqTrCoef (hD : CoefDeriv) {f : Space → Space} (hf : ContDiff ℝ ∞ f)
    (hp : IsPeriodic f) (hdiv : ∀ x, divergenceAt f x = 0) (k : Lattice) :
    divPairing k (freqTrCoef f k) = 0 := by
  have hsum : ∑ i : Fin 3, (freqTrCoef (partialD i f) k).ofLp i = 0 := by
    simp only [freqTrCoef_apply (contDiff_partialD _ hf).continuous]
    rw [← integral_finsetSum]
    · have : ∀ x, ∑ i : Fin 3, character k x * (((partialD i f x)).ofLp i : ℂ) = 0 := by
        intro x
        rw [← Finset.mul_sum, ← Complex.ofReal_sum]
        have := hdiv x
        unfold divergenceAt at this
        simp only [partialD, this, Complex.ofReal_zero, mul_zero]
      simp [this]
    · intro i _
      exact ((continuous_character k).mul (Complex.continuous_ofReal.comp
        ((PiLp.continuous_apply 2 _ i).comp (contDiff_partialD i hf).continuous))).continuousOn.integrableOn_compact
        isCompact_cell
  simp only [freqTrCoef_partialD hD _ hf hp, PiLp.smul_apply, smul_eq_mul] at hsum
  have hne : (2 * π * Complex.I : ℂ) ≠ 0 := by
    simp [pi_ne_zero, Complex.I_ne_zero]
  have : (2 * π * Complex.I : ℂ) * divPairing k (freqTrCoef f k) = 0 := by
    rw [divPairing, Finset.mul_sum, ← hsum]
    congr 1
    funext i
    ring
  exact (mul_eq_zero.mp this).resolve_left hne

theorem freq_neg (k : Lattice) : freq (-k) = -freq k := by
  simp [freq, Finset.sum_neg_distrib, neg_smul]

theorem weight_neg (k : Lattice) : weight (-k) = weight k := by
  simp [weight, freq_neg, norm_neg]

theorem mem_fieldSpace (hD : CoefDeriv) {f : Space → Space} (hf : ContDiff ℝ ∞ f) (hp : IsPeriodic f)
    (hdiv : ∀ x, divergenceAt f x = 0) :
    ∃ hm : Memℓp (weightedCoef f) 2, (⟨weightedCoef f, hm⟩ : Seq) ∈ fieldSpace := by
  obtain ⟨_, hs⟩ := summable_bounds hD hf hp
  have hm : Memℓp (weightedCoef f) 2 := by
    rw [memℓp_gen_iff (by norm_num)]
    refine hs.congr (fun k => ?_)
    rw [weightedCoef, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, mul_pow, Real.sq_sqrt (weight_pos k).le]
  refine ⟨hm, ?_⟩
  change (∀ k i, (weightedCoef f (-k)).ofLp i = starRingEnd ℂ ((weightedCoef f k).ofLp i)) ∧
    ∀ k, divPairing k (weightedCoef f k) = 0
  refine ⟨fun k i => ?_, fun k => ?_⟩
  · simp only [weightedCoef, weight_neg, PiLp.smul_apply, freqTrCoef_neg_apply hf.continuous,
      Complex.real_smul, map_mul, Complex.conj_ofReal]
  · have h := divPairing_freqTrCoef hD hf hp hdiv k
    simp only [divPairing, weightedCoef, PiLp.smul_apply, Complex.real_smul] at h ⊢
    calc ∑ i, (k i : ℂ) * ((Real.sqrt (weight k) : ℂ) * (freqTrCoef f k).ofLp i)
        = (Real.sqrt (weight k) : ℂ) * ∑ i, (k i : ℂ) * (freqTrCoef f k).ofLp i := by
          rw [Finset.mul_sum]
          congr 1
          funext i
          ring
      _ = 0 := by rw [h, mul_zero]

theorem coeff_toV (hD : CoefDeriv) {f : Space → Space} (hf : ContDiff ℝ ∞ f) (hp : IsPeriodic f)
    (hdiv : ∀ x, divergenceAt f x = 0) (k : Lattice) : coeff (toV f) k = freqTrCoef f k := by
  have h := mem_fieldSpace hD hf hp hdiv
  unfold toV
  rw [dif_pos h]
  change (Real.sqrt (weight k))⁻¹ • weightedCoef f k = freqTrCoef f k
  rw [weightedCoef, inv_smul_smul₀ (Real.sqrt_pos.mpr (weight_pos k)).ne']

theorem periodic_int_smul {f : Space → Space} (hp : IsPeriodic f) (i : Fin 3) (m : ℤ) (x : Space) :
    f (x + (m : ℝ) • unitVector i) = f x := by
  induction m using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    calc f (x + ((n + 1 : ℤ) : ℝ) • unitVector i) = f ((x + ((n : ℤ) : ℝ) • unitVector i) + unitVector i) := by
          congr 1
          push_cast
          rw [add_smul, one_smul, add_assoc]
      _ = f x := by rw [hp i, ih]
  | pred n ih =>
    rw [← hp i]
    convert ih x using 2
    push_cast
    rw [sub_smul, one_smul]
    abel

theorem periodic_freq {f : Space → Space} (hp : IsPeriodic f) (n : Lattice) (x : Space) :
    f (x + freq n) = f x := by
  rw [freq, Fin.sum_univ_three, ← add_assoc, ← add_assoc, periodic_int_smul hp 2,
    periodic_int_smul hp 1, periodic_int_smul hp 0]

def torusMap (y : Fin 3 → ℝ) : UnitAddTorus (Fin 3) := fun i => (y i : UnitAddCircle)

theorem isQuotientMap_torusMap : Topology.IsQuotientMap torusMap :=
  (IsOpenQuotientMap.piMap fun _ : Fin 3 =>
    (QuotientAddGroup.isOpenQuotientMap_mk :
      IsOpenQuotientMap (QuotientAddGroup.mk : ℝ → ℝ ⧸ AddSubgroup.zmultiples (1 : ℝ)))).isQuotientMap

theorem eq_of_torusMap_eq {f : Space → Space} (hp : IsPeriodic f) {y y' : Fin 3 → ℝ}
    (h : torusMap y = torusMap y') : f (WithLp.toLp 2 y) = f (WithLp.toLp 2 y') := by
  have hex : ∀ i, ∃ n : ℤ, y' i = y i + n := by
    intro i
    have hi := congrFun h i
    simp only [torusMap] at hi
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp hi)
    refine ⟨n, ?_⟩
    rw [zsmul_eq_mul, mul_one] at hn
    linarith
  choose n hn using hex
  have : WithLp.toLp 2 y' = WithLp.toLp 2 y + freq n := by
    ext i
    simp [freq_apply, hn i]
  rw [this, periodic_freq hp]

def torusLift (q : UnitAddTorus (Fin 3)) : Fin 3 → ℝ := fun i => ((AddCircle.equivIco (1 : ℝ) 0 (q i)) : ℝ)

theorem torusMap_torusLift (q : UnitAddTorus (Fin 3)) : torusMap (torusLift q) = q :=
  funext fun _ => AddCircle.coe_equivIco

def compFun (f : Space → Space) (j : Fin 3) (q : UnitAddTorus (Fin 3)) : ℂ :=
  ((f (WithLp.toLp 2 (torusLift q))).ofLp j : ℂ)

theorem compFun_torusMap {f : Space → Space} (hp : IsPeriodic f) (j : Fin 3) (y : Fin 3 → ℝ) :
    compFun f j (torusMap y) = ((f (WithLp.toLp 2 y)).ofLp j : ℂ) := by
  unfold compFun
  rw [eq_of_torusMap_eq hp (torusMap_torusLift (torusMap y))]

theorem continuous_compFun {f : Space → Space} (hf : Continuous f) (hp : IsPeriodic f) (j : Fin 3) :
    Continuous (compFun f j) := by
  rw [isQuotientMap_torusMap.continuous_iff]
  have : compFun f j ∘ torusMap = fun y => ((f (WithLp.toLp 2 y)).ofLp j : ℂ) :=
    funext fun y => compFun_torusMap hp j y
  rw [this]
  exact Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ j).comp
    (hf.comp (PiLp.continuous_toLp 2 _)))

def compMap {f : Space → Space} (hf : Continuous f) (hp : IsPeriodic f) (j : Fin 3) :
    C(UnitAddTorus (Fin 3), ℂ) :=
  ⟨compFun f j, continuous_compFun hf hp j⟩

theorem mFreqTr_torusMap (n : Lattice) (y : Fin 3 → ℝ) :
    UnitAddTorus.mFourier n (torusMap y) = character (-n) (WithLp.toLp 2 y) := by
  have hinner : inner ℝ (freq (-n)) (WithLp.toLp 2 y) = ∑ i, (-(n i : ℝ)) * y i := by
    rw [PiLp.inner_apply]
    simp [freq_apply, mul_comm]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, torusMap, fourier_coe_apply, character,
    hinner, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  congr 1
  funext i
  ring

theorem mFreqTrCoeff_compMap {f : Space → Space} (hf : Continuous f) (hp : IsPeriodic f) (j : Fin 3)
    (k : Lattice) : UnitAddTorus.mFourierCoeff (compMap hf hp j) k = (freqTrCoef f k).ofLp j := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ k 0, freqTrCoef_apply hf,
    ← (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
      (fun x => character k x * ((f x).ofLp j : ℂ)) cell]
  have e1 : (WithLp.toLp 2 ⁻¹' cell : Set (Fin 3 → ℝ)) = Icc 0 1 := by
    ext y
    simp [cell, Pi.le_def, forall_and]
  have e2 : {y : Fin 3 → ℝ | ∀ i, y i ∈ Ioc ((0 : Fin 3 → ℝ) i) ((0 : Fin 3 → ℝ) i + 1)} =
      Set.univ.pi fun i => Ioc ((0 : Fin 3 → ℝ) i) ((1 : Fin 3 → ℝ) i) := by
    ext y
    simp
  have hset : (WithLp.toLp 2 ⁻¹' cell : Set (Fin 3 → ℝ)) =ᵐ[volume]
      {y : Fin 3 → ℝ | ∀ i, y i ∈ Ioc ((0 : Fin 3 → ℝ) i) ((0 : Fin 3 → ℝ) i + 1)} := by
    rw [e1, e2, volume_pi]
    exact Measure.univ_pi_Ioc_ae_eq_Icc.symm
  rw [setIntegral_congr_set hset]
  congr 1
  funext y
  change UnitAddTorus.mFourier (-k) (torusMap y) • compFun f j (torusMap y) = _
  rw [mFreqTr_torusMap, neg_neg, compFun_torusMap hp, smul_eq_mul]

theorem hasSum_apply (hD : CoefDeriv) {f : Space → Space} (hf : ContDiff ℝ ∞ f) (hp : IsPeriodic f)
    (x : Space) : HasSum (fun k => character (-k) x • freqTrCoef f k) (complexify (f x)) := by
  have hsum := (summable_bounds hD hf hp).1
  have hj : ∀ j, HasSum (fun k => character (-k) x * (freqTrCoef f k).ofLp j) ((f x).ofLp j : ℂ) := by
    intro j
    have hs : Summable (UnitAddTorus.mFourierCoeff (compMap hf.continuous hp j)) := by
      refine Summable.of_norm_bounded hsum (fun k => ?_)
      rw [mFreqTrCoeff_compMap]
      exact PiLp.norm_apply_le _ _
    have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs (torusMap x.ofLp)
    simp only [mFreqTrCoeff_compMap, mFreqTr_torusMap, smul_eq_mul, WithLp.toLp_ofLp] at h
    have h2 : compMap hf.continuous hp j (torusMap x.ofLp) = ((f x).ofLp j : ℂ) := by
      change compFun f j (torusMap x.ofLp) = _
      rw [compFun_torusMap hp, WithLp.toLp_ofLp]
    rw [h2] at h
    simpa [mul_comm] using h
  rw [← (EuclideanSpace.equiv (Fin 3) ℂ).symm_apply_apply (complexify (f x))]
  refine (ContinuousLinearEquiv.hasSum _).mp (Pi.hasSum.mpr fun j => ?_)
  change HasSum (fun k => (character (-k) x • freqTrCoef f k).ofLp j) ((complexify (f x)).ofLp j)
  simpa [complexify] using hj j

end FreqTrSeries.Internal

open FreqTrSeries.Internal in
theorem freqTrSeriesSpec (hD : CoefDeriv) : FreqTrSeriesSpec := fun _ hf hp hdiv =>
  ⟨coeff_toV hD hf hp hdiv, (summable_bounds hD hf hp).1, hasSum_apply hD hf hp⟩

end Breakdown.Periodic
