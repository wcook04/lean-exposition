import Breakdown.FracCert.StHeldParts
import Breakdown.FracCert.StQuadratic

open scoped ContDiff ENNReal
open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace ActiveEnclosureInternal

theorem pair_integrable {X Y : Space → Space} (hX : MemLp X 2 volume) (hY : MemLp Y 2 volume) :
    Integrable (fun y => inner ℝ (X y) (Y y)) volume := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hX.toLp X) (hY.toLp Y)).congr ?_
  filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with y a b
  rw [a, b]

theorem sq_integral_eq {X : Space → Space} (hX : MemLp X 2 volume) :
    ∫ y, ‖X y‖ ^ 2 = ‖hX.toLp X‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hX.coeFn_toLp] with y hy
  rw [hy, real_inner_self_eq_norm_sq]

theorem abs_pair_le {X Y : Space → Space} (hX : MemLp X 2 volume) (hY : MemLp Y 2 volume) :
    |∫ y, inner ℝ (X y) (Y y)| ≤ Real.sqrt (∫ y, ‖X y‖ ^ 2) * Real.sqrt (∫ y, ‖Y y‖ ^ 2) := by
  have e : ∫ y, inner ℝ (X y) (Y y) = inner ℝ (hX.toLp X) (hY.toLp Y) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with y a b
    rw [a, b]
  rw [e, sq_integral_eq hX, sq_integral_eq hY, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]
  exact abs_real_inner_le_norm _ _

theorem sum_mul_le_sqrt {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    ∑ j, f j * g j ≤ Real.sqrt (∑ j, f j ^ 2) * Real.sqrt (∑ j, g j ^ 2) := by
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun j _ => sq_nonneg (f j))]
  exact (le_abs_self _).trans (Real.abs_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _))

theorem two_mul_le (a b c e : ℝ) :
    a * b + c * e ≤ Real.sqrt (a ^ 2 + c ^ 2) * Real.sqrt (b ^ 2 + e ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  nlinarith [sq_nonneg (a * e - c * b)]

theorem col_memLp {G : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume)
    (hI : Integrable (fun y => entrySq (G y))) (i : Fin 3) :
    MemLp (fun y => G y (unitVector i)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => G y (unitVector i)) volume :=
    (ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable hG
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine hI.mono' (hm.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)

theorem entry_pair {G χ : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume)
    (hGI : Integrable (fun y => entrySq (G y))) (hχ : AEStronglyMeasurable χ volume)
    (hχI : Integrable (fun y => entrySq (χ y))) :
    Integrable (fun y => entryInner (G y) (χ y)) ∧
      |∫ y, entryInner (G y) (χ y)| ≤
        Real.sqrt (∫ y, entrySq (G y)) * Real.sqrt (∫ y, entrySq (χ y)) := by
  have hc := fun i => col_memLp hG hGI i
  have hd := fun i => col_memLp hχ hχI i
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun y => inner ℝ (G y (unitVector i)) (χ y (unitVector i))) volume :=
    fun i _ => pair_integrable (hc i) (hd i)
  have hsqG : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun y => ‖G y (unitVector i)‖ ^ 2) volume :=
    fun i _ => (memLp_two_iff_integrable_sq_norm (hc i).1).1 (hc i)
  have hsqχ : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun y => ‖χ y (unitVector i)‖ ^ 2) volume :=
    fun i _ => (memLp_two_iff_integrable_sq_norm (hd i).1).1 (hd i)
  refine ⟨by unfold entryInner; exact integrable_finsetSum _ hint, ?_⟩
  have e1 : ∫ y, entryInner (G y) (χ y) =
      ∑ i, ∫ y, inner ℝ (G y (unitVector i)) (χ y (unitVector i)) := by
    unfold entryInner; exact integral_finsetSum _ hint
  have e2 : ∫ y, entrySq (G y) = ∑ i, ∫ y, ‖G y (unitVector i)‖ ^ 2 := by
    unfold entrySq; exact integral_finsetSum _ hsqG
  have e3 : ∫ y, entrySq (χ y) = ∑ i, ∫ y, ‖χ y (unitVector i)‖ ^ 2 := by
    unfold entrySq; exact integral_finsetSum _ hsqχ
  have ha : ∀ i : Fin 3, Real.sqrt (∫ y, ‖G y (unitVector i)‖ ^ 2) ^ 2 = ∫ y, ‖G y (unitVector i)‖ ^ 2 :=
    fun i => Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  have hb : ∀ i : Fin 3, Real.sqrt (∫ y, ‖χ y (unitVector i)‖ ^ 2) ^ 2 = ∫ y, ‖χ y (unitVector i)‖ ^ 2 :=
    fun i => Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  rw [e1, e2, e3]
  calc |∑ i, ∫ y, inner ℝ (G y (unitVector i)) (χ y (unitVector i))|
      ≤ ∑ i, |∫ y, inner ℝ (G y (unitVector i)) (χ y (unitVector i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, Real.sqrt (∫ y, ‖G y (unitVector i)‖ ^ 2) * Real.sqrt (∫ y, ‖χ y (unitVector i)‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => abs_pair_le (hc i) (hd i)
    _ ≤ _ := by
        have := sum_mul_le_sqrt (fun i : Fin 3 => Real.sqrt (∫ y, ‖G y (unitVector i)‖ ^ 2))
          (fun i : Fin 3 => Real.sqrt (∫ y, ‖χ y (unitVector i)‖ ^ 2))
        simpa only [ha, hb] using this

theorem trace_memLp {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    MemLp (fun y => secondTrace (H y)) 2 volume := by
  have hj : ∀ j : Fin 3, MemLp (fun y => H y (unitVector j) (unitVector j)) 2 volume := by
    intro j
    have hm : AEStronglyMeasurable (fun y => H y (unitVector j) (unitVector j)) volume :=
      ((ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp
        (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector j)).continuous).comp_aestronglyMeasurable
          hs.measurable_second
    rw [memLp_two_iff_integrable_sq_norm hm]
    refine hs.second_two.mono' (hm.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc ‖H y (unitVector j) (unitVector j)‖ ^ 2
        ≤ ∑ j' : Fin 3, ‖H y (unitVector j) (unitVector j')‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖H y (unitVector j) (unitVector j')‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i : Fin 3, ∑ j' : Fin 3, ‖H y (unitVector i) (unitVector j')‖ ^ 2 :=
          Finset.single_le_sum (f := fun i => ∑ j' : Fin 3, ‖H y (unitVector i) (unitVector j')‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have e : (fun y => secondTrace (H y)) = fun y => H y (unitVector 0) (unitVector 0) +
      H y (unitVector 1) (unitVector 1) + H y (unitVector 2) (unitVector 2) := by
    funext y
    simp [secondTrace, Fin.sum_univ_three]
  rw [e]
  exact ((hj 0).add (hj 1)).add (hj 2)

theorem decay_six : Integrable (fun y : Space => ((1 + ‖y‖)⁻¹) ^ 6) volume := by
  have h := integrable_one_add_norm (E := Space) (μ := volume) (r := 6) (by simp; norm_num)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  have hy : 0 < 1 + ‖y‖ := by positivity
  simp only []
  rw [Real.rpow_neg hy.le, inv_pow]
  norm_cast

theorem pointwise_split (t b : ℝ) (ht : 0 ≤ t) (hb : 0 ≤ b) : t ^ 4 * b ^ 2 ≤ t ^ 6 + b ^ 6 := by
  rcases le_total b t with h | h
  · have h2 : b ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hb h 2
    have : t ^ 4 * b ^ 2 ≤ t ^ 4 * t ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith [pow_nonneg hb 6]
  · have h4 : t ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ ht h 4
    have : t ^ 4 * b ^ 2 ≤ b ^ 4 * b ^ 2 := mul_le_mul_of_nonneg_right h4 (by positivity)
    nlinarith [pow_nonneg ht 6]

theorem decay_apply_memLp {A : Space → (Space →L[ℝ] Space)} (hA : Continuous A) {C : ℝ}
    (hAb : ∀ y, ‖A y‖ ≤ C * ((1 + ‖y‖)⁻¹) ^ 2) {v : Space → Space}
    (hv : AEStronglyMeasurable v volume) (hv6 : Integrable (fun y => ‖v y‖ ^ 6) volume) :
    MemLp (fun y => A y (v y)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => A y (v y)) volume :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun (L : Space →L[ℝ] Space) (x : Space) => L x)
      (continuous_fst.clm_apply continuous_snd) hA.aestronglyMeasurable hv
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine ((decay_six.add hv6).const_mul (C ^ 2)).mono' (hm.norm.pow 2)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have ht : 0 ≤ (1 + ‖y‖)⁻¹ := by positivity
  have h1 : ‖A y (v y)‖ ≤ C * ((1 + ‖y‖)⁻¹) ^ 2 * ‖v y‖ :=
    (A y).le_opNorm (v y) |>.trans (mul_le_mul_of_nonneg_right (hAb y) (norm_nonneg _))
  have h2 : ‖A y (v y)‖ ^ 2 ≤ (C * ((1 + ‖y‖)⁻¹) ^ 2 * ‖v y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 := pointwise_split ((1 + ‖y‖)⁻¹) ‖v y‖ ht (norm_nonneg _)
  have h4 : (C * ((1 + ‖y‖)⁻¹) ^ 2 * ‖v y‖) ^ 2 = C ^ 2 * (((1 + ‖y‖)⁻¹) ^ 4 * ‖v y‖ ^ 2) := by ring
  simp only [Pi.add_apply]
  rw [h4] at h2
  exact h2.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg C))

theorem apply_expand (A : Space →L[ℝ] Space) (x : Space) :
    A x = ∑ i : Fin 3, x i • A (unitVector i) := by
  have hx := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] at hx
  conv_lhs => rw [← hx]
  simp [map_sum, map_smul, unitVector]

theorem bounded_apply_memLp {G : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume)
    (hGI : Integrable (fun y => entrySq (G y))) {W : Space → Space} (hW : Continuous W) {C : ℝ}
    (hWb : ∀ y, ‖W y‖ ≤ C) : MemLp (fun y => G y (W y)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => G y (W y)) volume :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun (L : Space →L[ℝ] Space) (x : Space) => L x)
      (continuous_fst.clm_apply continuous_snd) hG hW.aestronglyMeasurable
  have hc := fun i => col_memLp hG hGI i
  have hg : MemLp (fun y => C * (‖G y (unitVector 0)‖ + ‖G y (unitVector 1)‖ + ‖G y (unitVector 2)‖))
      2 volume :=
    ((((hc 0).norm.add (hc 1).norm).add (hc 2).norm).const_mul C)
  refine hg.of_le hm (Filter.Eventually.of_forall fun y => ?_)
  refine le_trans ?_ (le_abs_self _)
  rw [apply_expand (G y) (W y)]
  calc ‖∑ i : Fin 3, W y i • G y (unitVector i)‖ ≤ ∑ i : Fin 3, ‖W y i • G y (unitVector i)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, C * ‖G y (unitVector i)‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le (W y) i).trans (hWb y)) (norm_nonneg _)
    _ = C * (‖G y (unitVector 0)‖ + ‖G y (unitVector 1)‖ + ‖G y (unitVector 2)‖) := by
        rw [Fin.sum_univ_three]; ring


theorem profile_bounds_of {k N : ℕ} {α : ℝ} {d : FracCertData k N} (hd : IsFracCert α d) :
    ∃ C : ℝ, ∀ p ∈ box d.radius, ∀ y,
      ‖d.profile p y‖ ≤ C * (1 + ‖y‖)⁻¹ ∧ ‖d.gradProfile p y‖ ≤ C * ((1 + ‖y‖)⁻¹) ^ 2 := by
  obtain ⟨C, hC⟩ := hd.profile_bounds
  refine ⟨C, fun p hp y => ?_⟩
  obtain ⟨h1, h2, -⟩ := hC p hp y
  have hy : 0 < 1 + ‖y‖ := by positivity
  rw [Real.rpow_neg_one] at h1
  rw [Real.rpow_neg hy.le, Real.rpow_two, ← inv_pow] at h2
  exact ⟨h1, h2⟩

theorem profile_le {k N : ℕ} {d : FracCertData k N} {C : ℝ} {p : Fin k → ℝ}
    (hC : ∀ y, ‖d.profile p y‖ ≤ C * (1 + ‖y‖)⁻¹) (y : Space) : ‖d.profile p y‖ ≤ |C| := by
  have h0 : 0 ≤ (1 + ‖y‖)⁻¹ := by positivity
  have h1 : (1 + ‖y‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg y])
  have := hC y
  nlinarith [le_abs_self C, abs_nonneg C]

theorem sum_smul_memLp {k : ℕ} (c : Fin k → ℝ) {b : Fin k → Space → Space}
    (hb : ∀ i, MemLp (b i) 2 volume) : MemLp (fun y => ∑ i, c i • b i y) 2 volume := by
  exact memLp_finsetSum (Finset.univ : Finset (Fin k)) fun i _ => (hb i).const_smul (c i)

theorem local_memLp {k N : ℕ} {α : ℝ} {d : FracCertData k N} (hd : IsFracCert α d)
    {p : Fin k → ℝ} (hp : p ∈ box d.radius) {u : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {P : Space → Space}
    (hst : d.IsLinearState α p u G H P) : MemLp (d.localField α p u G H 0) 2 volume := by
  have hs := hst.second
  obtain ⟨C, hC⟩ := profile_bounds_of hd
  have hW : Continuous (d.profile p) := (hd.profile_smooth p hp).continuous
  have hDW : Continuous (d.gradProfile p) :=
    (hd.profile_smooth p hp).continuous_fderiv one_ne_zero
  have hu6 : Integrable (fun y => ‖u y‖ ^ 6) volume :=
    hs.velocity_six.integrable_norm_pow (p := 6) (by norm_num)
  have h1 : MemLp (fun y => G y (d.profile p y)) 2 volume :=
    bounded_apply_memLp hs.measurable_gradient hs.gradient_two hW
      (profile_le (fun y => (hC p hp y).1))
  have h2 : MemLp (fun y => d.gradProfile p y (u y)) 2 volume :=
    decay_apply_memLp hDW (fun y => (hC p hp y).2) hs.measurable_velocity hu6
  have htr := trace_memLp hs
  have e : d.localField α p u G H 0 = fun y => driftField α (d.rotationRate p) u G y -
      d.splitVisc • secondTrace (H y) + (2 : ℝ) • ((1 / 2 : ℝ) • (G y (d.profile p y) +
        d.gradProfile p y (u y))) := by
    funext y
    simp [FracCertData.localField, symProduct]
  rw [e]
  exact (hst.drift.sub (htr.const_smul d.splitVisc)).add ((h1.add h2).const_smul (1 / 2 : ℝ)
    |>.const_smul (2 : ℝ))

theorem defect_memLp {k N : ℕ} {α : ℝ} {d : FracCertData k N} (hd : IsFracCert α d)
    {p : Fin k → ℝ} (hp : p ∈ box d.radius) : MemLp (d.defect α p) 2 volume := by
  obtain ⟨C, hC⟩ := profile_bounds_of hd
  have hW : Continuous (d.profile p) := (hd.profile_smooth p hp).continuous
  have hDW : Continuous (d.gradProfile p) :=
    (hd.profile_smooth p hp).continuous_fderiv one_ne_zero
  have hW6 : Integrable (fun y => ‖d.profile p y‖ ^ 6) volume := by
    refine (decay_six.const_mul (|C| ^ 6)).mono' (hW.aestronglyMeasurable.norm.pow 6)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h0 : 0 ≤ (1 + ‖y‖)⁻¹ := by positivity
    have h1 : ‖d.profile p y‖ ≤ |C| * (1 + ‖y‖)⁻¹ :=
      (hC p hp y).1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) h0)
    calc ‖d.profile p y‖ ^ 6 ≤ (|C| * (1 + ‖y‖)⁻¹) ^ 6 := pow_le_pow_left₀ (norm_nonneg _) h1 6
      _ = |C| ^ 6 * ((1 + ‖y‖)⁻¹) ^ 6 := by ring
  have h3 : MemLp (fun y => d.gradProfile p y (d.profile p y)) 2 volume :=
    decay_apply_memLp hDW (fun y => (hC p hp y).2) hW.aestronglyMeasurable hW6
  have hs := sum_smul_memLp (d.multiplier p) hd.actuator_two
  have e : d.defect α p = fun y => driftField α (d.rotationRate p) (d.profile p) (d.gradProfile p) y +
      d.profilePower p y + d.gradProfile p y (d.profile p y) + ∑ i, d.multiplier p i • d.actuator i y := by
    funext y
    rfl
  rw [e]
  exact (((hd.profile_drift p hp).add (hd.profile_power p hp).1).add h3).add hs

theorem norm_sub_sq_le (a b : Space) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_sub_le a b
  have h0 := norm_nonneg (a - b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

theorem entrySq_sub_le (A B : Space →L[ℝ] Space) : entrySq (A - B) ≤ 2 * (entrySq A + entrySq B) := by
  unfold entrySq
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [_root_.sub_apply]
  nlinarith [norm_sub_sq_le (A (unitVector i)) (B (unitVector i))]

theorem energy_facts {k N : ℕ} {α : ℝ} {d : FracCertData k N} (hd : IsFracCert α d)
    {m : ℕ} {u : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m u G H) :
    0 ≤ d.energy G H ∧ d.weightMin * ∫ y, entrySq (G y) ≤ d.energy G H := by
  have hGI := hs.gradient_two
  have hwm : AEStronglyMeasurable (fun y => d.weight y * entrySq (G y)) volume :=
    hd.weight_measurable.aestronglyMeasurable.mul hGI.aestronglyMeasurable
  have hwI : Integrable (fun y => d.weight y * entrySq (G y)) volume := by
    refine (hGI.const_mul d.weightMax).mono' hwm (Filter.Eventually.of_forall fun y => ?_)
    have he : 0 ≤ entrySq (G y) := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hw0 : 0 ≤ d.weight y := hd.weightMin_pos.le.trans (hd.weight_lower y)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 he)]
    exact mul_le_mul_of_nonneg_right (hd.weight_upper y) he
  have hmono : d.weightMin * ∫ y, entrySq (G y) ≤ ∫ y, d.weight y * entrySq (G y) := by
    rw [← integral_const_mul]
    exact integral_mono (hGI.const_mul _) hwI fun y =>
      mul_le_mul_of_nonneg_right (hd.weight_lower y) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have htr : 0 ≤ ∫ y, ‖secondTrace (H y)‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hA : 0 ≤ ∫ y, entrySq (G y) :=
    integral_nonneg fun y => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmA : 0 ≤ d.weightMin * ∫ y, entrySq (G y) := mul_nonneg hd.weightMin_pos.le hA
  unfold FracCertData.energy weightedEnergy
  constructor <;> linarith

theorem pin_bound {k N : ℕ} {α : ℝ} {d : FracCertData k N} (hd : IsFracCert α d)
    {m : ℕ} {u : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m u G H)
    (hpin : ∀ i, d.pins G i = 0) (c : Fin k → ℝ) :
    |∑ l, c l * pinValue (d.smoothPin l) G| ≤
      vecNorm c * d.pinGap * Real.sqrt (∫ y, entrySq (G y)) := by
  have hG := hs.measurable_gradient
  have hGI := hs.gradient_two
  have hent : Continuous entrySq := by unfold entrySq; fun_prop
  have hχm : ∀ l, AEStronglyMeasurable (fun y => d.smoothPin l y - d.pin l y) volume :=
    fun l => (hd.pin_measurable l).2.sub (hd.pin_measurable l).1
  have hχI : ∀ l, Integrable (fun y => entrySq (d.smoothPin l y - d.pin l y)) volume := by
    intro l
    refine (((hd.pin_two l).2.add (hd.pin_two l).1).const_mul 2).mono'
      (hent.comp_aestronglyMeasurable (hχm l)) (Filter.Eventually.of_forall fun y => ?_)
    have h0 : 0 ≤ entrySq (d.smoothPin l y - d.pin l y) := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact entrySq_sub_le _ _
  have hx : ∀ l, |pinValue (d.smoothPin l) G| ≤
      Real.sqrt (∫ y, entrySq (G y)) * Real.sqrt (∫ y, entrySq (d.smoothPin l y - d.pin l y)) := by
    intro l
    have hS := (entry_pair hG hGI (hd.pin_measurable l).2 (hd.pin_two l).2).1
    have hP := (entry_pair hG hGI (hd.pin_measurable l).1 (hd.pin_two l).1).1
    have hz : pinValue (d.pin l) G = 0 := hpin l
    have e : pinValue (d.smoothPin l) G = ∫ y, entryInner (G y) (d.smoothPin l y - d.pin l y) := by
      rw [← sub_zero (pinValue (d.smoothPin l) G), ← hz]
      unfold pinValue
      rw [← integral_sub hS hP]
      congr 1
      funext y
      simp only [entryInner, _root_.sub_apply, inner_sub_right, Finset.sum_sub_distrib]
    rw [e]
    exact (entry_pair hG hGI (hχm l) (hχI l)).2
  set A := ∫ y, entrySq (G y)
  set g : Fin k → ℝ := fun l => ∫ y, entrySq (d.smoothPin l y - d.pin l y) with hg
  have hg0 : ∀ l, 0 ≤ g l := fun l => integral_nonneg fun y => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hgsum : ∑ l, g l ≤ d.pinGap ^ 2 := hd.pinGap_bound
  have hsA := Real.sqrt_nonneg A
  calc |∑ l, c l * pinValue (d.smoothPin l) G| ≤ ∑ l, |c l * pinValue (d.smoothPin l) G| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, |c l| * (Real.sqrt A * Real.sqrt (g l)) := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hx l) (abs_nonneg _)
    _ = Real.sqrt A * ∑ l, |c l| * Real.sqrt (g l) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ Real.sqrt A * (Real.sqrt (∑ l, |c l| ^ 2) * Real.sqrt (∑ l, Real.sqrt (g l) ^ 2)) :=
        mul_le_mul_of_nonneg_left (sum_mul_le_sqrt _ _) hsA
    _ ≤ Real.sqrt A * (vecNorm c * d.pinGap) := by
        refine mul_le_mul_of_nonneg_left ?_ hsA
        have e1 : ∑ l, |c l| ^ 2 = ∑ l, c l ^ 2 := Finset.sum_congr rfl fun l _ => sq_abs _
        have e2 : ∑ l, Real.sqrt (g l) ^ 2 = ∑ l, g l :=
          Finset.sum_congr rfl fun l _ => Real.sq_sqrt (hg0 l)
        rw [e1, e2]
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        calc Real.sqrt (∑ l, g l) ≤ Real.sqrt (d.pinGap ^ 2) := Real.sqrt_le_sqrt hgsum
          _ = d.pinGap := Real.sqrt_sq hd.pinGap_nonneg
    _ = vecNorm c * d.pinGap * Real.sqrt A := by ring

end ActiveEnclosureInternal

theorem activeEnclosure (h1 : GradientOrthogonalStatement) (h2 : TestBoxSubsetStatement)
    (h3 : QuadraticSquareIntegrableStatement) : ActiveEnclosureStatement := by
  intro α hα1 hα2 k N d hd p hp u G H P κ hsol hsize j hj
  have hpb : p ∈ box d.radius := h2 α d hd hp
  have hζs := (hd.adjoint_solenoidal j hj p hpb).1
  have hζ2 : MemLp (d.adjoint j p) 2 volume := hζs.1
  have hst := hsol.state
  have hs := hst.second
  obtain ⟨Q, hQg, hQeq⟩ := hsol.equation
  have hT1 := ActiveEnclosureInternal.local_memLp hd hpb hst
  have hT2 : MemLp (d.splitField P H) 2 volume :=
    hst.power.1.add ((ActiveEnclosureInternal.trace_memLp hs).const_smul d.splitVisc)
  have hT3 := ActiveEnclosureInternal.sum_smul_memLp κ hd.actuator_two
  have hT4 : MemLp (fun y => G y (u y)) 2 volume := h3 d.order u G H hs
  have hT5 := ActiveEnclosureInternal.defect_memLp hd hpb
  have hsplit : ∀ y, d.fullField α p u G H P κ y = d.localField α p u G H 0 y + d.splitField P H y +
      ∑ i, κ i • d.actuator i y := by
    intro y
    simp only [FracCertData.fullField, FracCertData.localField, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, add_zero]
    abel
  have hQ : Q =ᵐ[volume] fun y => -(d.localField α p u G H 0 y + d.splitField P H y +
      (∑ i, κ i • d.actuator i y) + G y (u y) + d.defect α p y) := by
    filter_upwards [hQeq] with y hy
    rw [hsplit] at hy
    exact (neg_eq_of_add_eq_zero_right hy).symm
  have hQ2 : MemLp Q 2 volume := (((((hT1.add hT2).add hT3).add hT4).add hT5).neg).ae_eq hQ.symm
  have h0 := h1 Q (d.adjoint j p) hQg hQ2 hζs
  have i1 := ActiveEnclosureInternal.pair_integrable hT1 hζ2
  have i2 := ActiveEnclosureInternal.pair_integrable hT2 hζ2
  have i3 := ActiveEnclosureInternal.pair_integrable hT3 hζ2
  have i4 := ActiveEnclosureInternal.pair_integrable hT4 hζ2
  have i5 := ActiveEnclosureInternal.pair_integrable hT5 hζ2
  have i12 : Integrable (fun y => inner ℝ (d.localField α p u G H 0 y) (d.adjoint j p y) +
      inner ℝ (d.splitField P H y) (d.adjoint j p y)) volume := i1.add i2
  have i123 : Integrable (fun y => inner ℝ (d.localField α p u G H 0 y) (d.adjoint j p y) +
      inner ℝ (d.splitField P H y) (d.adjoint j p y) +
      inner ℝ (∑ i, κ i • d.actuator i y) (d.adjoint j p y)) volume := i12.add i3
  have i1234 : Integrable (fun y => inner ℝ (d.localField α p u G H 0 y) (d.adjoint j p y) +
      inner ℝ (d.splitField P H y) (d.adjoint j p y) +
      inner ℝ (∑ i, κ i • d.actuator i y) (d.adjoint j p y) +
      inner ℝ (G y (u y)) (d.adjoint j p y)) volume := i123.add i4
  have hb : ∀ i, Integrable (fun y => inner ℝ (d.actuator i y) (d.adjoint j p y)) volume :=
    fun i => ActiveEnclosureInternal.pair_integrable (hd.actuator_two i) hζ2
  have e3 : ∫ y, inner ℝ (∑ i, κ i • d.actuator i y) (d.adjoint j p y) =
      ∑ i, κ i * l2Pair (d.actuator i) (d.adjoint j p) := by
    simp only [sum_inner, real_inner_smul_left]
    rw [integral_finsetSum _ fun i _ => (hb i).const_mul (κ i)]
    simp only [integral_const_mul, l2Pair]
  have hpairs : l2Pair (d.localField α p u G H 0) (d.adjoint j p) + l2Pair (d.splitField P H) (d.adjoint j p) +
      ∑ i, κ i * l2Pair (d.actuator i) (d.adjoint j p) + l2Pair (fun y => G y (u y)) (d.adjoint j p) +
      l2Pair (d.defect α p) (d.adjoint j p) = 0 := by
    have e : ∫ y, inner ℝ (Q y) (d.adjoint j p y) = -∫ y, (inner ℝ (d.localField α p u G H 0 y) (d.adjoint j p y) +
        inner ℝ (d.splitField P H y) (d.adjoint j p y) +
        inner ℝ (∑ i, κ i • d.actuator i y) (d.adjoint j p y) +
        inner ℝ (G y (u y)) (d.adjoint j p y) + inner ℝ (d.defect α p y) (d.adjoint j p y)) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [hQ] with y hy
      rw [hy]
      simp only [inner_neg_left, inner_add_left]
    rw [integral_add i1234 i5, integral_add i123 i4, integral_add i12 i3, integral_add i1 i2, e3] at e
    simp only [l2Pair] at e ⊢
    linarith
  have hloc := hd.adjoint_local j hj p hpb u G H hs P hst.power hst.drift
  have hspr := hd.adjoint_spread j hj p hpb u G H hs P hst.power
  have hquad := hd.adjoint_quad j hj p hpb u G H hs
  have hqn := hd.adjointQuad_nonneg j hj p hpb
  have hpin := ActiveEnclosureInternal.pin_bound hd hs hsol.pins (d.adjointPin j p)
  obtain ⟨hE0, hEw⟩ := ActiveEnclosureInternal.energy_facts hd hs
  have hwm := hd.weightMin_pos
  have hA0 : 0 ≤ ∫ y, entrySq (G y) :=
    integral_nonneg fun y => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hAE : Real.sqrt (∫ y, entrySq (G y)) ≤ Real.sqrt (d.energy G H) / Real.sqrt d.weightMin := by
    rw [le_div_iff₀ (Real.sqrt_pos.2 hwm), ← Real.sqrt_mul hA0]
    exact Real.sqrt_le_sqrt (by linarith [hEw])
  have hvn : 0 ≤ vecNorm (d.adjointPin j p) * d.pinGap :=
    mul_nonneg (Real.sqrt_nonneg _) hd.pinGap_nonneg
  have hpin2 : |∑ l, d.adjointPin j p l * pinValue (d.smoothPin l) G| ≤
      vecNorm (d.adjointPin j p) * d.pinGap / Real.sqrt d.weightMin * Real.sqrt (d.energy G H) := by
    refine hpin.trans ?_
    calc vecNorm (d.adjointPin j p) * d.pinGap * Real.sqrt (∫ y, entrySq (G y))
        ≤ vecNorm (d.adjointPin j p) * d.pinGap * (Real.sqrt (d.energy G H) / Real.sqrt d.weightMin) :=
          mul_le_mul_of_nonneg_left hAE hvn
      _ = _ := by ring
  set δ := d.adjointLocal j p + d.adjointSpread j p +
    vecNorm (d.adjointPin j p) * d.pinGap / Real.sqrt d.weightMin with hδ
  have hAbound : |l2Pair (d.localField α p u G H 0) (d.adjoint j p) + l2Pair (d.splitField P H) (d.adjoint j p)| ≤
      δ * Real.sqrt (d.energy G H) := by
    have a1 := abs_le.1 hloc
    have a2 := abs_le.1 hspr
    have a3 := abs_le.1 hpin2
    rw [abs_le, hδ]
    constructor <;> nlinarith
  set e := d.adjointError j p with he
  have hact : ∑ i, κ i * l2Pair (d.actuator i) (d.adjoint j p) = (d.frameᵀ *ᵥ κ) j + ∑ i, κ i * e i := by
    have : ∀ i, l2Pair (d.actuator i) (d.adjoint j p) = d.frame i j + e i := by
      intro i
      simp [he, FracCertData.adjointError]
    simp only [this, mul_add, Finset.sum_add_distrib, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  set S := ∑ i, κ i ^ 2 with hS
  set T := ∑ i, e i ^ 2 with hT
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hke : |∑ i, κ i * e i| ≤ Real.sqrt S * Real.sqrt T := by
    rw [← Real.sqrt_mul hS0]
    exact Real.abs_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  set μ := d.multiplierScale with hμ
  have hμ0 : 0 < μ := hd.multiplierScale_pos
  set r := d.heldRadius with hr
  set E := d.energy G H with hEdef
  have hsz : Real.sqrt (E + μ ^ 2 * S) ≤ r := hsize
  have hX0 : 0 ≤ E + μ ^ 2 * S := by positivity
  have hr0 : 0 ≤ r := (Real.sqrt_nonneg _).trans hsz
  have hEr : E ≤ r ^ 2 := by
    have h := Real.sq_sqrt hX0
    have h' := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsz 2
    nlinarith [mul_nonneg (sq_nonneg μ) hS0]
  have hcs : δ * Real.sqrt E + Real.sqrt S * Real.sqrt T ≤
      r * Real.sqrt (δ ^ 2 + vecNorm e ^ 2 / μ ^ 2) := by
    have h := ActiveEnclosureInternal.two_mul_le δ (Real.sqrt E) (Real.sqrt T / μ) (μ * Real.sqrt S)
    have e1 : Real.sqrt T / μ * (μ * Real.sqrt S) = Real.sqrt S * Real.sqrt T := by
      field_simp
    have e2 : (Real.sqrt T / μ) ^ 2 = vecNorm e ^ 2 / μ ^ 2 := by
      rw [div_pow]
      rfl
    have e3 : Real.sqrt E ^ 2 + (μ * Real.sqrt S) ^ 2 = E + μ ^ 2 * S := by
      rw [mul_pow, Real.sq_sqrt hE0, Real.sq_sqrt hS0]
    rw [e1, e2, e3] at h
    refine h.trans ?_
    rw [mul_comm r]
    exact mul_le_mul_of_nonneg_left hsz (Real.sqrt_nonneg _)
  have hX : |(d.frameᵀ *ᵥ κ) j + l2Pair (d.defect α p) (d.adjoint j p)| ≤
      d.adjointQuad j p * r ^ 2 + r * Real.sqrt (δ ^ 2 + vecNorm e ^ 2 / μ ^ 2) := by
    have hq2 : d.adjointQuad j p * E ≤ d.adjointQuad j p * r ^ 2 := mul_le_mul_of_nonneg_left hEr hqn
    have key : (d.frameᵀ *ᵥ κ) j + l2Pair (d.defect α p) (d.adjoint j p) =
        -(l2Pair (d.localField α p u G H 0) (d.adjoint j p) + l2Pair (d.splitField P H) (d.adjoint j p)) -
          ∑ i, κ i * e i - l2Pair (fun y => G y (u y)) (d.adjoint j p) := by
      linarith [hpairs, hact]
    have a1 := abs_le.1 hAbound
    have a2 := abs_le.1 hke
    have a3 := abs_le.1 hquad
    rw [key, abs_le]
    constructor <;> linarith
  have hincl := hd.active_inclusion j hj p hpb p hp
  have hm : d.heldMultiplier p κ = d.multiplier p + κ := by
    funext i
    rfl
  rw [hm, Matrix.mulVec_add, Pi.add_apply]
  have ha : (d.frameᵀ *ᵥ d.multiplier p) j + (d.frameᵀ *ᵥ κ) j - d.slope j * p j =
      d.adjustedMultiplier α p j + ((d.frameᵀ *ᵥ κ) j + l2Pair (d.defect α p) (d.adjoint j p)) := by
    unfold FracCertData.adjustedMultiplier
    ring
  rw [ha]
  refine (abs_add_le _ _).trans ?_
  linarith

end SteadyCert

end Breakdown
