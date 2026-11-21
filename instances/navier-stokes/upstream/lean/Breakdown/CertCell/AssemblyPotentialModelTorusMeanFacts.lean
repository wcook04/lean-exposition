import Breakdown.CertCell.AssemblyPotentialModelTorusMean

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation

namespace TorusMean

theorem torusMean_eq_box (f : ℝ → ℝ → ℂ) (hf : IsTorusIntegrable f) :
    torusMean f = (1 / (2 * Real.pi) : ℂ) * ∫ z, f z.1 z.2 ∂boxMeasure := by
  unfold torusMean
  rw [iter_eq_prod f hf]

theorem torusMean_const_mul (c : ℂ) (f : ℝ → ℝ → ℂ) :
    torusMean (fun τ φ => c * f τ φ) = c * torusMean f := by
  unfold torusMean
  simp only [intervalIntegral.integral_const_mul]
  ring

theorem isTorusIntegrable_add {f g : ℝ → ℝ → ℂ} (hf : IsTorusIntegrable f) (hg : IsTorusIntegrable g) :
    IsTorusIntegrable (fun τ φ => f τ φ + g τ φ) :=
  Integrable.add hf hg

theorem isTorusIntegrable_sum {κ : Type*} (S : Finset κ) (f : κ → ℝ → ℝ → ℂ)
    (hf : ∀ s ∈ S, IsTorusIntegrable (f s)) :
    IsTorusIntegrable (fun τ φ => ∑ s ∈ S, f s τ φ) := by
  unfold IsTorusIntegrable
  have h := integrable_finsetSum S (f := fun s (z : ℝ × ℝ) => f s z.1 z.2) hf
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only

theorem torusMean_add (f g : ℝ → ℝ → ℂ) (hf : IsTorusIntegrable f) (hg : IsTorusIntegrable g) :
    torusMean (fun τ φ => f τ φ + g τ φ) = torusMean f + torusMean g := by
  rw [torusMean_eq_box _ (isTorusIntegrable_add hf hg), torusMean_eq_box f hf, torusMean_eq_box g hg,
    integral_add hf hg, mul_add]

theorem torusMean_sum {κ : Type*} (S : Finset κ) (f : κ → ℝ → ℝ → ℂ)
    (hf : ∀ s ∈ S, IsTorusIntegrable (f s)) :
    torusMean (fun τ φ => ∑ s ∈ S, f s τ φ) = ∑ s ∈ S, torusMean (f s) := by
  rw [torusMean_eq_box _ (isTorusIntegrable_sum S f hf), integral_finsetSum S hf, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s hs => (torusMean_eq_box (f s) (hf s hs)).symm

theorem ae_box : ∀ᵐ z ∂boxMeasure, z ∈ Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi) := by
  unfold boxMeasure
  rw [Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)

theorem re_torusMean (f : ℝ → ℝ → ℂ) (hf : IsTorusIntegrable f) :
    (torusMean f).re = (1 / (2 * Real.pi)) * ∫ z, (f z.1 z.2).re ∂boxMeasure := by
  rw [torusMean_eq_box f hf]
  have hc : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; ring
  rw [hc, Complex.re_ofReal_mul]
  congr 1
  exact (integral_re hf).symm

theorem torusMean_re_mono (f g : ℝ → ℝ → ℂ) (hf : IsTorusIntegrable f) (hg : IsTorusIntegrable g)
    (hfg : ∀ τ φ : ℝ, 0 < τ → τ ≤ 1 → 0 < φ → φ ≤ 2 * Real.pi → (f τ φ).re ≤ (g τ φ).re) :
    (torusMean f).re ≤ (torusMean g).re := by
  rw [re_torusMean f hf, re_torusMean g hg]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine integral_mono_ae hf.re hg.re ?_
  filter_upwards [ae_box] with z hz
  exact hfg z.1 z.2 hz.1.1 hz.1.2 hz.2.1 hz.2.2

theorem bounded_integrable (f : ℝ → ℝ → ℂ)
    (hm : AEStronglyMeasurable (fun z : ℝ × ℝ => f z.1 z.2) boxMeasure)
    (hb : ∃ C : ℝ, ∀ τ φ : ℝ, 0 < τ → τ ≤ 1 → 0 < φ → φ ≤ 2 * Real.pi → ‖f τ φ‖ ≤ C) :
    IsTorusIntegrable f := by
  obtain ⟨C, hC⟩ := hb
  refine (integrable_const C).mono' hm ?_
  filter_upwards [ae_box] with z hz
  exact hC z.1 z.2 hz.1.1 hz.1.2 hz.2.1 hz.2.2

theorem integral_exp_line (a L : ℝ) (k : ℤ) (ha : a ≠ 0) (hk : a * L = 2 * Real.pi * k) :
    ∫ x in (0 : ℝ)..L, Complex.exp (((a * x : ℝ) : ℂ) * Complex.I) = 0 := by
  have hc : (a : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ha) Complex.I_ne_zero
  have hfun : (fun x : ℝ => Complex.exp (((a * x : ℝ) : ℂ) * Complex.I))
      = fun x : ℝ => Complex.exp ((a : ℂ) * Complex.I * (x : ℂ)) := by
    funext x
    congr 1
    push_cast
    ring
  rw [hfun, integral_exp_mul_complex hc]
  have hL : (a : ℂ) * Complex.I * (L : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) hk
    push_cast at h
    linear_combination Complex.I * h
  rw [hL, Complex.exp_int_mul_two_pi_mul_I, Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self,
    zero_div]

theorem integral_exp_line_zero (L : ℝ) :
    ∫ x in (0 : ℝ)..L, Complex.exp ((((0 : ℝ) * x : ℝ) : ℂ) * Complex.I) = L := by
  simp

theorem inner_phase (β : ℤ × ℤ) (τ : ℝ) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), phase β τ φ
      = Complex.exp (((2 * Real.pi * (β.1 : ℝ) * τ : ℝ) : ℂ) * Complex.I)
        * (if β.2 = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0) := by
  have hfun : (fun φ => phase β τ φ) = fun φ =>
      Complex.exp (((2 * Real.pi * (β.1 : ℝ) * τ : ℝ) : ℂ) * Complex.I)
        * Complex.exp ((((β.2 : ℝ) * φ : ℝ) : ℂ) * Complex.I) := by
    funext φ
    unfold phase waveArg
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfun, intervalIntegral.integral_const_mul]
  congr 1
  split_ifs with h
  · rw [h, Int.cast_zero]
    exact integral_exp_line_zero _
  · refine integral_exp_line _ _ β.2 (Int.cast_ne_zero.mpr h) ?_
    ring

theorem torusMean_phase (β : ℤ × ℤ) :
    torusMean (fun τ φ => phase β τ φ) = if β = 0 then 1 else 0 := by
  unfold torusMean
  simp only [inner_phase, intervalIntegral.integral_mul_const]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  by_cases h1 : β.1 = 0
  · by_cases h2 : β.2 = 0
    · have hβ : β = 0 := Prod.ext h1 h2
      rw [if_pos h2, if_pos hβ, h1, Int.cast_zero]
      have h0 := integral_exp_line_zero 1
      simp only [mul_zero, zero_mul] at h0 ⊢
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
        sub_zero, one_smul, one_mul]
      push_cast
      field_simp
    · have hβ : β ≠ 0 := fun h => h2 (by rw [h]; rfl)
      rw [if_neg h2, if_neg hβ]
      simp
  · have hβ : β ≠ 0 := fun h => h1 (by rw [h]; rfl)
    rw [if_neg hβ]
    have hz : ∫ τ in (0 : ℝ)..1, Complex.exp (((2 * Real.pi * (β.1 : ℝ) * τ : ℝ) : ℂ) * Complex.I) = 0 := by
      have := integral_exp_line (2 * Real.pi * (β.1 : ℝ)) 1 β.1
        (mul_ne_zero hpi (Int.cast_ne_zero.mpr h1)) (by ring)
      exact this
    rw [hz]
    simp

theorem conj_labelPhase (m : ℕ) (α : ℤ × ℤ) (τ φ : ℝ) :
    (starRingEnd ℂ) (labelPhase m α τ φ) = phase (-(labelHarmonic m α)) τ φ := by
  unfold labelPhase phase waveArg labelHarmonic
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  push_cast
  ring

theorem conj_labelPhase_sub (m : ℕ) (ι ι' : ℤ × ℤ) (τ φ : ℝ) :
    (starRingEnd ℂ) (labelPhase m (ι - ι') τ φ)
      = (starRingEnd ℂ) (labelPhase m ι τ φ) * labelPhase m ι' τ φ := by
  unfold labelPhase labelTime labelAzimuth
  rw [← Complex.exp_conj, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Prod.fst_sub, Prod.snd_sub]
  push_cast
  ring

theorem labelHarmonic_eq_zero_iff {m : ℕ} (hm : 1 ≤ m) (α : ℤ × ℤ) :
    labelHarmonic m α = 0 ↔ α = 0 := by
  constructor
  · intro h
    have h1 : labelTime α = 0 := congrArg Prod.fst h
    have h2 : labelAzimuth m α = 0 := congrArg Prod.snd h
    unfold labelTime at h1
    unfold labelAzimuth at h2
    have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have ha : α.1 = 0 := (mul_eq_zero.mp h2).resolve_right hm'
    exact Prod.ext ha (by simp only [Prod.snd_zero]; omega)
  · intro h
    subst h
    simp [labelHarmonic, labelTime, labelAzimuth]

theorem torusMean_label (m : ℕ) (hm : 1 ≤ m) (α : ℤ × ℤ) :
    torusMean (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ)) = if α = 0 then 1 else 0 := by
  simp only [conj_labelPhase]
  rw [torusMean_phase]
  simp only [neg_eq_zero, labelHarmonic_eq_zero_iff hm]

theorem isTorusIntegrable_conj_label_mul (m : ℕ) (α : ℤ × ℤ) {g : ℝ → ℝ → ℂ} (hg : IsTorusIntegrable g) :
    IsTorusIntegrable (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * g τ φ) := by
  unfold IsTorusIntegrable at hg ⊢
  have hcont : Continuous (fun z : ℝ × ℝ => (starRingEnd ℂ) (labelPhase m α z.1 z.2)) := by
    unfold labelPhase
    fun_prop
  refine hg.norm.mono' (hcont.aestronglyMeasurable.mul hg.1) (Filter.Eventually.of_forall fun z => ?_)
  rw [norm_mul, Complex.norm_conj]
  unfold labelPhase
  rw [Complex.norm_exp_ofReal_mul_I, one_mul]

theorem pairSesq_waveSum (m : ℕ) (A : Matrix (Fin 12) (Fin 12) ℂ) (S T : Finset (ℤ × ℤ))
    (X Y : ℤ × ℤ → Fin 12 → ℂ) (τ φ : ℝ) :
    pairSesq A (waveSum m S X τ φ) (waveSum m T Y τ φ)
      = ∑ ι ∈ S, ∑ ι' ∈ T, ∑ i, ∑ j, (starRingEnd ℂ) (X ι i) * Y ι' j
          * ((starRingEnd ℂ) (labelPhase m (ι - ι') τ φ) * A i j) := by
  have e1 : pairSesq A (waveSum m S X τ φ) (waveSum m T Y τ φ)
      = ∑ i, ∑ j, ∑ ι ∈ S, ∑ ι' ∈ T, (starRingEnd ℂ) (X ι i) * Y ι' j
          * ((starRingEnd ℂ) (labelPhase m (ι - ι') τ φ) * A i j) := by
    unfold pairSesq waveSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ι _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ι' _ => ?_
    rw [conj_labelPhase_sub, map_mul]
    ring
  rw [e1]
  calc (∑ i, ∑ j, ∑ ι ∈ S, ∑ ι' ∈ T, (starRingEnd ℂ) (X ι i) * Y ι' j
          * ((starRingEnd ℂ) (labelPhase m (ι - ι') τ φ) * A i j))
      = ∑ i, ∑ ι ∈ S, ∑ j, ∑ ι' ∈ T, (starRingEnd ℂ) (X ι i) * Y ι' j
          * ((starRingEnd ℂ) (labelPhase m (ι - ι') τ φ) * A i j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ ι ∈ S, ∑ i, ∑ j, ∑ ι' ∈ T, (starRingEnd ℂ) (X ι i) * Y ι' j
          * ((starRingEnd ℂ) (labelPhase m (ι - ι') τ φ) * A i j) := Finset.sum_comm
    _ = ∑ ι ∈ S, ∑ i, ∑ ι' ∈ T, ∑ j, (starRingEnd ℂ) (X ι i) * Y ι' j
          * ((starRingEnd ℂ) (labelPhase m (ι - ι') τ φ) * A i j) :=
        Finset.sum_congr rfl fun ι _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ ι ∈ S, ∑ ι' ∈ T, ∑ i, ∑ j, (starRingEnd ℂ) (X ι i) * Y ι' j
          * ((starRingEnd ℂ) (labelPhase m (ι - ι') τ φ) * A i j) :=
        Finset.sum_congr rfl fun ι _ => Finset.sum_comm

theorem torusMean_product (m : ℕ) (M : ℝ → ℝ → Matrix (Fin 12) (Fin 12) ℂ) (S T : Finset (ℤ × ℤ))
    (X Y : ℤ × ℤ → Fin 12 → ℂ) (hM : ∀ i j, IsTorusIntegrable (fun τ φ => M τ φ i j)) :
    torusMean (fun τ φ => pairSesq (M τ φ) (waveSum m S X τ φ) (waveSum m T Y τ φ))
      = ∑ ι ∈ S, ∑ ι' ∈ T, pairSesq (torusCoef m M (ι - ι')) (X ι) (Y ι') := by
  simp only [pairSesq_waveSum]
  have hterm : ∀ ι ι' : ℤ × ℤ, ∀ i j : Fin 12, IsTorusIntegrable (fun τ φ =>
      (starRingEnd ℂ) (X ι i) * Y ι' j * ((starRingEnd ℂ) (labelPhase m (ι - ι') τ φ) * M τ φ i j)) :=
    fun ι ι' i j => (isTorusIntegrable_conj_label_mul m (ι - ι') (hM i j)).const_mul _
  have hj : ∀ ι ι' : ℤ × ℤ, ∀ i : Fin 12, IsTorusIntegrable (fun τ φ => ∑ j, (starRingEnd ℂ) (X ι i) * Y ι' j
      * ((starRingEnd ℂ) (labelPhase m (ι - ι') τ φ) * M τ φ i j)) :=
    fun ι ι' i => isTorusIntegrable_sum _ _ fun j _ => hterm ι ι' i j
  have hi : ∀ ι ι' : ℤ × ℤ, IsTorusIntegrable (fun τ φ => ∑ i, ∑ j, (starRingEnd ℂ) (X ι i) * Y ι' j
      * ((starRingEnd ℂ) (labelPhase m (ι - ι') τ φ) * M τ φ i j)) :=
    fun ι ι' => isTorusIntegrable_sum _ _ fun i _ => hj ι ι' i
  have hι' : ∀ ι : ℤ × ℤ, IsTorusIntegrable (fun τ φ => ∑ ι' ∈ T, ∑ i, ∑ j, (starRingEnd ℂ) (X ι i) * Y ι' j
      * ((starRingEnd ℂ) (labelPhase m (ι - ι') τ φ) * M τ φ i j)) :=
    fun ι => isTorusIntegrable_sum _ _ fun ι' _ => hi ι ι'
  rw [torusMean_sum S _ fun ι _ => hι' ι]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [torusMean_sum T _ fun ι' _ => hi ι ι']
  refine Finset.sum_congr rfl fun ι' _ => ?_
  rw [torusMean_sum Finset.univ _ fun i _ => hj ι ι' i]
  unfold pairSesq
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [torusMean_sum Finset.univ _ fun j _ => hterm ι ι' i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [torusMean_const_mul]
  unfold torusCoef
  ring

end TorusMean

theorem torusFacts : TorusFacts where
  add := TorusMean.torusMean_add
  sum := fun S f hf => TorusMean.torusMean_sum S f hf
  re_mono := TorusMean.torusMean_re_mono
  bounded := TorusMean.bounded_integrable
  harmonic_mean := TorusMean.torusMean_phase
  label_mean := TorusMean.torusMean_label
  product := TorusMean.torusMean_product

end Internal

end Assembly

end CertCell

end Breakdown
