import Breakdown.Torus.StatementsCoeff

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace TimeCoef.Internal

abbrev halfSpace : Set (ℝ × Space) := Ici (0 : ℝ) ×ˢ (univ : Set Space)

theorem uniqueDiffOn_halfSpace : UniqueDiffOn ℝ halfSpace :=
  (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

theorem infty_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  exact_mod_cast le_top

theorem isCompact_cell : IsCompact cell := by
  have h := (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
    (isCompact_univ_pi fun _ : Fin 3 => isCompact_Icc (a := (0 : ℝ)) (b := 1))
  convert h using 1
  ext x
  simp only [cell, mem_ofPred_eq, mem_preimage, mem_univ_pi]
  rfl

theorem measurableSet_cell : MeasurableSet cell := isCompact_cell.isClosed.measurableSet

instance : IsFiniteMeasure (volume.restrict cell) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_cell.measure_lt_top⟩

theorem continuous_character (k : Lattice) : Continuous (character k) := by
  unfold character
  fun_prop

theorem norm_character (k : Lattice) (x : Space) : ‖character k x‖ = 1 := by
  simp [character, Complex.norm_exp]

theorem norm_complexify (y : Space) : ‖complexify y‖ = ‖y‖ := by
  simp [complexify, EuclideanSpace.norm_eq]

def complexifyL : Space →L[ℝ] Coef :=
  LinearMap.toContinuousLinearMap
    { toFun := complexify
      map_add' := fun a b => by ext i; simp [complexify]
      map_smul' := fun r a => by ext i; simp [complexify] }

theorem complexifyL_apply (y : Space) : complexifyL y = complexify y := rfl

theorem hasDerivAt_complexify {f : ℝ → Space} {f' : Space} {τ : ℝ} (h : HasDerivAt f f' τ) :
    HasDerivAt (fun σ => complexify (f σ)) (complexify f') τ :=
  complexifyL.hasFDerivAt.comp_hasDerivAt τ h

theorem continuous_integrand (k : Lattice) {f : Space → Space} (hf : Continuous f) :
    Continuous fun x => character k x • complexify (f x) :=
  (continuous_character k).smul (complexifyL.continuous.comp hf)

theorem norm_freqTrCoef_le {f : Space → Space} {C : ℝ} (hC : ∀ x ∈ cell, ‖f x‖ ≤ C)
    (k : Lattice) : ‖freqTrCoef f k‖ ≤ C * volume.real cell := by
  unfold freqTrCoef
  refine norm_setIntegral_le_of_norm_le_const isCompact_cell.measure_lt_top fun x hx => ?_
  rw [norm_smul, norm_character, norm_complexify, one_mul]
  exact hC x hx

theorem continuous_slice {E : Type*} [TopologicalSpace E] {h : ℝ × Space → E}
    (hc : ContinuousOn h halfSpace) {τ : ℝ} (hτ : 0 ≤ τ) : Continuous fun x => h (τ, x) :=
  hc.comp_continuous (by fun_prop) fun x => ⟨hτ, mem_univ x⟩

theorem hasFDerivAt_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ × Space → E} (hg : ContDiffOn ℝ ∞ g halfSpace) {τ : ℝ} (hτ : 0 ≤ τ) (x : Space) :
    HasFDerivAt (fun y => g (τ, y))
      ((fderivWithin ℝ g halfSpace (τ, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) x := by
  have hd : DifferentiableWithinAt ℝ g halfSpace (τ, x) :=
    (hg.differentiableOn (by simp)) _ ⟨hτ, mem_univ _⟩
  have h := hd.hasFDerivWithinAt.comp x (hasFDerivAt_prodMk_right τ x).hasFDerivWithinAt
    (s := univ) (fun y _ => ⟨hτ, mem_univ y⟩)
  exact hasFDerivWithinAt_univ.mp h

theorem fderiv_slice_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ × Space → E} (hg : ContDiffOn ℝ ∞ g halfSpace) {τ : ℝ} (hτ : 0 ≤ τ) (x v : Space) :
    fderiv ℝ (fun y => g (τ, y)) x v = fderivWithin ℝ g halfSpace (τ, x) (0, v) := by
  rw [(hasFDerivAt_slice hg hτ x).fderiv]
  rfl

theorem contDiff_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ × Space → E} (hg : ContDiffOn ℝ ∞ g halfSpace) {τ : ℝ} (hτ : 0 ≤ τ) :
    ContDiff ℝ ∞ (fun y => g (τ, y)) :=
  contDiffOn_univ.mp (hg.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun y _ => ⟨hτ, mem_univ y⟩))

theorem hasDerivAt_time {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ × Space → E} (hg : ContDiffOn ℝ ∞ g halfSpace) {τ : ℝ} (hτ : 0 < τ) (x : Space) :
    HasDerivAt (fun σ => g (σ, x)) (fderivWithin ℝ g halfSpace (τ, x) (1, 0)) τ := by
  have hd : DifferentiableWithinAt ℝ g halfSpace (τ, x) :=
    (hg.differentiableOn (by simp)) _ ⟨hτ.le, mem_univ _⟩
  have hp : HasDerivAt (fun σ : ℝ => (σ, x)) ((1 : ℝ), (0 : Space)) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ x)
  have h := hd.hasFDerivWithinAt.comp_hasDerivWithinAt τ hp.hasDerivWithinAt
    (show MapsTo (fun σ : ℝ => (σ, x)) (Ici 0) halfSpace from fun σ hσ => ⟨hσ, mem_univ x⟩)
  exact h.hasDerivAt (Ici_mem_nhds hτ)


def partialOp (v : Space) (h : ℝ × Space → Space) (z : ℝ × Space) : Space :=
  fderivWithin ℝ h halfSpace z (0, v)

theorem contDiffOn_partialOp {h : ℝ × Space → Space} (hh : ContDiffOn ℝ ∞ h halfSpace)
    (v : Space) : ContDiffOn ℝ ∞ (partialOp v h) halfSpace :=
  (hh.fderivWithin uniqueDiffOn_halfSpace infty_add_one_le).clm_apply contDiffOn_const

theorem isPeriodic_fderiv {f : Space → Space} (hf : IsPeriodic f) (v : Space) :
    IsPeriodic (fun x => fderiv ℝ f x v) := by
  intro i x
  have h : (fun y => f (y + unitVector i)) = f := funext fun y => hf i y
  simp only
  rw [← fderiv_comp_add_right (unitVector i), h]

theorem slice_partialOp {h : ℝ × Space → Space} (hh : ContDiffOn ℝ ∞ h halfSpace) {τ : ℝ}
    (hτ : 0 ≤ τ) (v : Space) :
    (fun x => partialOp v h (τ, x)) = fun x => fderiv ℝ (fun y => h (τ, y)) x v :=
  funext fun x => (fderiv_slice_apply hh hτ x v).symm

def SmoothPeriodicSlices (h : ℝ × Space → Space) : Prop :=
  ContDiffOn ℝ ∞ h halfSpace ∧ ∀ τ, 0 ≤ τ → IsPeriodic (fun x => h (τ, x))

theorem smoothPeriodicSlices_partialOp {h : ℝ × Space → Space} (hh : SmoothPeriodicSlices h) (v : Space) :
    SmoothPeriodicSlices (partialOp v h) :=
  ⟨contDiffOn_partialOp hh.1 v, fun τ hτ => by
    rw [slice_partialOp hh.1 hτ]
    exact isPeriodic_fderiv (hh.2 τ hτ) v⟩

theorem freqTrCoef_partialOp (hD : CoefDeriv) {h : ℝ × Space → Space} (hh : SmoothPeriodicSlices h) {τ : ℝ}
    (hτ : 0 ≤ τ) (i : Fin 3) (k : Lattice) :
    freqTrCoef (fun x => partialOp (unitVector i) h (τ, x)) k =
      (2 * π * Complex.I * (k i : ℂ)) • freqTrCoef (fun x => h (τ, x)) k := by
  rw [slice_partialOp hh.1 hτ]
  exact hD _ ((contDiff_slice hh.1 hτ).of_le (by simp)) (hh.2 τ hτ) i k

theorem smoothPeriodicSlices_iterate {h : ℝ × Space → Space} (hh : SmoothPeriodicSlices h) (v : Space) (n : ℕ) :
    SmoothPeriodicSlices ((partialOp v)^[n] h) := by
  induction n with
  | zero => exact hh
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact smoothPeriodicSlices_partialOp ih v

theorem freqTrCoef_iterate (hD : CoefDeriv) {h : ℝ × Space → Space} (hh : SmoothPeriodicSlices h) {τ : ℝ}
    (hτ : 0 ≤ τ) (i : Fin 3) (k : Lattice) (n : ℕ) :
    freqTrCoef (fun x => (partialOp (unitVector i))^[n] h (τ, x)) k =
      (2 * π * Complex.I * (k i : ℂ)) ^ n • freqTrCoef (fun x => h (τ, x)) k := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [freqTrCoef_partialOp hD (smoothPeriodicSlices_iterate hh _ n) hτ i k, ih, smul_smul, pow_succ']

theorem exists_bound_freqTrCoef {h : ℝ × Space → Space} (hh : ContinuousOn h halfSpace)
    (T : ℝ) : ∃ C, ∀ τ ∈ Icc 0 T, ∀ k, ‖freqTrCoef (fun x => h (τ, x)) k‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_cell).exists_bound_of_continuousOn
    (hh.mono (prod_mono Icc_subset_Ici_self (subset_univ _)))
  exact ⟨C * volume.real cell, fun τ hτ k =>
    norm_freqTrCoef_le (fun x hx => hC (τ, x) ⟨hτ, hx⟩) k⟩

theorem norm_freq_sq (k : Lattice) : ‖freq k‖ ^ 2 = ∑ i, ((k i : ℝ)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [freq, unitVector, Real.norm_eq_abs, sq_abs, Pi.single_apply]

theorem norm_two_pi_I_mul (n : ℤ) : ‖(2 * π * Complex.I * (n : ℂ))‖ = 2 * π * |(n : ℝ)| := by
  simp [abs_of_pos pi_pos]

def decayBound (k : Lattice) : ℝ :=
  (1 + ((k 0 : ℝ)) ^ 2)⁻¹ * ((1 + ((k 1 : ℝ)) ^ 2)⁻¹ * (1 + ((k 2 : ℝ)) ^ 2)⁻¹)

theorem weight_sq_le (k : Lattice) :
    weight k ^ 2 ≤ 6 * (1 + ∑ i, (2 * π * |(k i : ℝ)|) ^ 4) := by
  have e : ∀ r : ℝ, (2 * π * |r|) ^ 4 = (4 * π ^ 2 * r ^ 2) ^ 2 := fun r => by
    calc (2 * π * |r|) ^ 4 = (4 * π ^ 2 * |r| ^ 2) ^ 2 := by ring
      _ = _ := by rw [sq_abs]
  simp only [weight, norm_freq_sq, Fin.sum_univ_three, e]
  have ha : 0 ≤ 4 * π ^ 2 * ((k 0 : ℝ)) ^ 2 := by positivity
  have hb : 0 ≤ 4 * π ^ 2 * ((k 1 : ℝ)) ^ 2 := by positivity
  have hc : 0 ≤ 4 * π ^ 2 * ((k 2 : ℝ)) ^ 2 := by positivity
  set a := 4 * π ^ 2 * ((k 0 : ℝ)) ^ 2
  set b := 4 * π ^ 2 * ((k 1 : ℝ)) ^ 2
  set c := 4 * π ^ 2 * ((k 2 : ℝ)) ^ 2
  have : 1 + 4 * π ^ 2 * (((k 0 : ℝ)) ^ 2 + ((k 1 : ℝ)) ^ 2 + ((k 2 : ℝ)) ^ 2) = 1 + a + b + c := by
    simp only [a, b, c]; ring
  rw [this]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a - 1),
    sq_nonneg (b - 1), sq_nonneg (c - 1)]

theorem one_le_weight (k : Lattice) : 1 ≤ weight k := by
  unfold weight
  have : 0 ≤ 4 * π ^ 2 * ‖freq k‖ ^ 2 := by positivity
  linarith

theorem prod_le_weight_cube (k : Lattice) :
    (1 + ((k 0 : ℝ)) ^ 2) * ((1 + ((k 1 : ℝ)) ^ 2) * (1 + ((k 2 : ℝ)) ^ 2)) ≤ weight k ^ 3 := by
  have hpi : 1 ≤ 4 * π ^ 2 := by nlinarith [pi_gt_three]
  have hW0 : 0 ≤ weight k := by linarith [one_le_weight k]
  have hq : 1 + (((k 0 : ℝ)) ^ 2 + ((k 1 : ℝ)) ^ 2 + ((k 2 : ℝ)) ^ 2) ≤ weight k := by
    rw [weight, norm_freq_sq, Fin.sum_univ_three]
    have : 0 ≤ ((k 0 : ℝ)) ^ 2 + ((k 1 : ℝ)) ^ 2 + ((k 2 : ℝ)) ^ 2 := by positivity
    nlinarith
  have h0 : 1 + ((k 0 : ℝ)) ^ 2 ≤ weight k := by nlinarith [sq_nonneg ((k 1 : ℝ)), sq_nonneg ((k 2 : ℝ))]
  have h1 : 1 + ((k 1 : ℝ)) ^ 2 ≤ weight k := by nlinarith [sq_nonneg ((k 0 : ℝ)), sq_nonneg ((k 2 : ℝ))]
  have h2 : 1 + ((k 2 : ℝ)) ^ 2 ≤ weight k := by nlinarith [sq_nonneg ((k 1 : ℝ)), sq_nonneg ((k 0 : ℝ))]
  calc (1 + ((k 0 : ℝ)) ^ 2) * ((1 + ((k 1 : ℝ)) ^ 2) * (1 + ((k 2 : ℝ)) ^ 2))
      ≤ weight k * (weight k * weight k) := by gcongr
    _ = weight k ^ 3 := by ring


theorem weight_mul_sq_le {c : Coef} {k : Lattice} {A : ℝ}
    (h : ‖c‖ * (1 + ∑ i, (2 * π * |(k i : ℝ)|) ^ 4) ≤ A) :
    weight k * ‖c‖ ^ 2 ≤ 36 * A ^ 2 * decayBound k := by
  have hW := one_le_weight k
  have hP := prod_le_weight_cube k
  have hS := weight_sq_le k
  set P := (1 + ((k 0 : ℝ)) ^ 2) * ((1 + ((k 1 : ℝ)) ^ 2) * (1 + ((k 2 : ℝ)) ^ 2)) with hPdef
  have hPpos : 0 < P := by positivity
  have hdb : decayBound k = P⁻¹ := by
    rw [hPdef, decayBound, mul_inv, mul_inv]
  rw [hdb]
  have hc := norm_nonneg c
  have h1 : weight k ^ 2 * ‖c‖ ≤ 6 * A := by
    calc weight k ^ 2 * ‖c‖ ≤ 6 * (1 + ∑ i, (2 * π * |(k i : ℝ)|) ^ 4) * ‖c‖ := by gcongr
      _ ≤ 6 * A := by nlinarith
  have h2 : 0 ≤ weight k ^ 2 * ‖c‖ := by positivity
  have h3 : weight k * ‖c‖ ^ 2 * P ≤ 36 * A ^ 2 := by
    calc weight k * ‖c‖ ^ 2 * P ≤ weight k * ‖c‖ ^ 2 * weight k ^ 3 := by gcongr
      _ = (weight k ^ 2 * ‖c‖) ^ 2 := by ring
      _ ≤ (6 * A) ^ 2 := by gcongr
      _ = 36 * A ^ 2 := by ring
  rw [← div_eq_mul_inv, le_div_iff₀ hPpos]
  exact h3

theorem exists_decay (hD : CoefDeriv) {h : ℝ × Space → Space} (hh : SmoothPeriodicSlices h) (T : ℝ) :
    ∃ M, ∀ τ ∈ Icc 0 T, ∀ k,
      weight k * ‖freqTrCoef (fun x => h (τ, x)) k‖ ^ 2 ≤ M * decayBound k := by
  obtain ⟨C0, hC0⟩ := exists_bound_freqTrCoef hh.1.continuousOn T
  choose C hC using fun i : Fin 3 =>
    exists_bound_freqTrCoef (smoothPeriodicSlices_iterate hh (unitVector i) 4).1.continuousOn T
  refine ⟨36 * (C0 + ∑ i, C i) ^ 2, fun τ hτ k => weight_mul_sq_le ?_⟩
  rw [mul_add, mul_one, Finset.mul_sum]
  gcongr with i
  · exact hC0 τ hτ k
  · have := hC i τ hτ k
    rw [freqTrCoef_iterate hD hh hτ.1 i k 4, norm_smul, norm_pow, norm_two_pi_I_mul] at this
    linarith

theorem summable_inv_one_add_sq : Summable fun n : ℤ => (1 + (n : ℝ) ^ 2)⁻¹ := by
  refine Summable.of_norm_bounded_eventually (summable_one_div_int_pow.mpr one_lt_two) ?_
  filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [Real.norm_of_nonneg (by positivity), one_div]
  exact inv_anti₀ (by positivity) (by linarith)

def tripleEquiv : Lattice ≃ ℤ × ℤ × ℤ where
  toFun k := (k 0, k 1, k 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv k := by ext i; fin_cases i <;> rfl
  right_inv p := rfl

theorem summable_decayBound : Summable decayBound := by
  have h1 := summable_inv_one_add_sq
  have h := h1.mul_of_nonneg (h1.mul_of_nonneg h1 (fun _ => by positivity) (fun _ => by positivity))
    (fun _ => by positivity) (fun _ => by positivity)
  exact tripleEquiv.summable_iff.mpr h

theorem Icc_mem_nhdsWithin_Ici_zero (τ : ℝ) : Icc 0 (τ + 1) ∈ 𝓝[Ici 0] τ := by
  rw [← Ici_inter_Iic]
  exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))

theorem continuousOn_freqTrCoef_Icc {g : ℝ × Space → Space} (hg : ContinuousOn g halfSpace)
    (k : Lattice) (T : ℝ) :
    ContinuousOn (fun τ => freqTrCoef (fun x => g (τ, x)) k) (Icc 0 T) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_cell).exists_bound_of_continuousOn
    (hg.mono (prod_mono Icc_subset_Ici_self (subset_univ _)))
  unfold freqTrCoef
  refine continuousOn_of_dominated (bound := fun _ => C) (fun τ hτ => ?_) (fun τ hτ => ?_)
    (integrable_const C) (Eventually.of_forall fun x => ?_)
  · exact (continuous_integrand k (continuous_slice hg hτ.1)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_cell fun x hx => ?_
    rw [norm_smul, norm_character, one_mul, norm_complexify]
    exact hC _ ⟨hτ, hx⟩
  · exact (continuousOn_const (c := character k x)).smul (complexifyL.continuous.comp_continuousOn
      (hg.comp (Continuous.continuousOn (by fun_prop))
        (show MapsTo (fun τ : ℝ => (τ, x)) (Icc 0 T) halfSpace from fun τ hτ => ⟨hτ.1, mem_univ x⟩)))

theorem continuousOn_freqTrCoef {g : ℝ × Space → Space} (hg : ContinuousOn g halfSpace)
    (k : Lattice) : ContinuousOn (fun τ => freqTrCoef (fun x => g (τ, x)) k) (Ici 0) := by
  intro τ hτ
  exact (continuousOn_freqTrCoef_Icc hg k (τ + 1) τ ⟨hτ, by linarith⟩).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsWithin_Ici_zero τ)

theorem hasDerivAt_freqTrCoef {g : ℝ × Space → Space} (hg : ContDiffOn ℝ ∞ g halfSpace)
    (k : Lattice) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun τ => freqTrCoef (fun x => g (τ, x)) k)
      (freqTrCoef (fun x => deriv (fun τ => g (τ, x)) t) k) t := by
  set D : ℝ × Space → Space := fun z => fderivWithin ℝ g halfSpace z (1, 0) with hDdef
  have hDc : ContinuousOn D halfSpace :=
    ((hg.fderivWithin uniqueDiffOn_halfSpace infty_add_one_le).clm_apply
      contDiffOn_const).continuousOn
  have e : (fun x => deriv (fun τ => g (τ, x)) t) = fun x => D (t, x) :=
    funext fun x => (hasDerivAt_time hg ht x).deriv
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := t / 2) (b := 2 * t)).prod
    isCompact_cell).exists_bound_of_continuousOn
    (hDc.mono (prod_mono (fun σ hσ => (show (0 : ℝ) ≤ σ by linarith [hσ.1])) (subset_univ _)))
  have hgc := hg.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict cell)
    (F := fun τ x => character k x • complexify (g (τ, x)))
    (F' := fun τ x => character k x • complexify (D (τ, x)))
    (x₀ := t) (bound := fun _ => C)
    (Ioo_mem_nhds (by linarith : t / 2 < t) (by linarith : t < 2 * t)) ?_ ?_ ?_ ?_
    (integrable_const C) ?_
  · rw [e]
    exact key.2
  · filter_upwards [lt_mem_nhds ht] with τ hτ
    exact (continuous_integrand k (continuous_slice hgc hτ.le)).aestronglyMeasurable
  · exact (continuous_integrand k (continuous_slice hgc ht.le)).continuousOn.integrableOn_compact
      isCompact_cell
  · exact (continuous_integrand k (continuous_slice hDc ht.le)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_cell fun x hx τ hτ => ?_
    rw [norm_smul, norm_character, one_mul, norm_complexify]
    exact hC (τ, x) ⟨Ioo_subset_Icc_self hτ, hx⟩
  · refine Eventually.of_forall fun x τ hτ => ?_
    exact (hasDerivAt_complexify
      (hasDerivAt_time hg (by linarith [hτ.1] : 0 < τ) x)).const_smul (character k x)

theorem seq_norm_sq (a : Seq) : ‖a‖ ^ 2 = ∑' k, ‖a k‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) a
  simpa [Real.rpow_two] using h

theorem toV_apply (hF : FreqTrSeriesSpec) {f : Space → Space} (hf : ContDiff ℝ ∞ f)
    (hp : IsPeriodic f) (hd : ∀ x, divergenceAt f x = 0) (k : Lattice) :
    ((toV f : V) : Seq) k = Real.sqrt (weight k) • freqTrCoef f k := by
  rw [← (hF f hf hp hd).1 k]
  unfold coeff
  rw [smul_inv_smul₀]
  exact (Real.sqrt_pos.mpr (by linarith [one_le_weight k])).ne'

theorem norm_sq_sqrt_weight_smul (k : Lattice) (c : Coef) :
    ‖Real.sqrt (weight k) • c‖ ^ 2 = weight k * ‖c‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (by linarith [one_le_weight k])]

theorem norm_sub_sq_le (a b : Coef) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_sub_le a b
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hab := norm_nonneg (a - b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

end TimeCoef.Internal

open TimeCoef.Internal in
theorem coefTimeDeriv : CoefTimeDeriv := by
  intro u hu _ k
  exact ⟨continuousOn_freqTrCoef (g := fun z => u z.1 z.2) hu.continuousOn k,
    fun t ht => hasDerivAt_freqTrCoef (g := fun z => u z.1 z.2) hu k ht⟩

open TimeCoef.Internal in
theorem toVContinuous (hD : CoefDeriv) (hF : FreqTrSeriesSpec) : ToVContinuous := by
  intro u hu hper hdiv τ₀ hτ₀
  have hgood : SmoothPeriodicSlices (fun z => u z.1 z.2) := ⟨hu, fun τ hτ => hper τ hτ⟩
  have hslice : ∀ τ, 0 ≤ τ → ∀ k, ((toV (u τ) : V) : Seq) k =
      Real.sqrt (weight k) • freqTrCoef (u τ) k := fun τ hτ k =>
    toV_apply hF (contDiff_slice (g := fun z => u z.1 z.2) hu hτ) (hper τ hτ) (hdiv τ hτ) k
  obtain ⟨M, hM⟩ := exists_decay hD hgood (τ₀ + 1)
  have hM' : ∀ τ ∈ Icc 0 (τ₀ + 1), ∀ k,
      weight k * ‖freqTrCoef (u τ) k‖ ^ 2 ≤ M * decayBound k := hM
  have hmain : Tendsto (fun τ => ∑' k, ‖Real.sqrt (weight k) • freqTrCoef (u τ) k -
      Real.sqrt (weight k) • freqTrCoef (u τ₀) k‖ ^ 2) (𝓝[Ici 0] τ₀) (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[Ici 0] τ₀)
      (f := fun τ k => ‖Real.sqrt (weight k) • freqTrCoef (u τ) k -
        Real.sqrt (weight k) • freqTrCoef (u τ₀) k‖ ^ 2)
      (g := fun _ : Lattice => (0 : ℝ)) (bound := fun k => 4 * M * decayBound k)
      (summable_decayBound.mul_left _) ?_ ?_
    · simpa using h
    · intro k
      have hc : ContinuousWithinAt (fun τ => freqTrCoef (u τ) k) (Ici 0) τ₀ :=
        continuousOn_freqTrCoef (g := fun z => u z.1 z.2) hu.continuousOn k τ₀ hτ₀
      simpa using (tendsto_iff_norm_sub_tendsto_zero.mp
        (hc.const_smul (Real.sqrt (weight k)))).pow 2
    · filter_upwards [Icc_mem_nhdsWithin_Ici_zero τ₀] with τ hτ k
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h1 := hM' τ hτ k
      have h2 := hM' τ₀ ⟨hτ₀, by linarith⟩ k
      have h3 := norm_sub_sq_le (Real.sqrt (weight k) • freqTrCoef (u τ) k)
        (Real.sqrt (weight k) • freqTrCoef (u τ₀) k)
      rw [norm_sq_sqrt_weight_smul, norm_sq_sqrt_weight_smul] at h3
      linarith
  have hsq : Tendsto (fun τ => ‖toV (u τ) - toV (u τ₀)‖ ^ 2) (𝓝[Ici 0] τ₀) (𝓝 0) := by
    refine hmain.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    symm
    show ‖((toV (u τ) - toV (u τ₀) : V) : Seq)‖ ^ 2 = _
    rw [Submodule.coe_sub, seq_norm_sq]
    refine tsum_congr fun k => ?_
    rw [lp.coeFn_sub, Pi.sub_apply, hslice τ hτ k, hslice τ₀ hτ₀ k]
  have hn : Tendsto (fun τ => ‖toV (u τ) - toV (u τ₀)‖) (𝓝[Ici 0] τ₀) (𝓝 0) := by
    have hs := (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at hs
    refine hs.congr fun τ => ?_
    exact Real.sqrt_sq (norm_nonneg _)
  show Tendsto (fun τ => toV (u τ)) (𝓝[Ici 0] τ₀) (𝓝 (toV (u τ₀)))
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

end Breakdown.Periodic
