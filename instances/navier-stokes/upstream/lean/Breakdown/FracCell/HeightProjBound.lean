import Breakdown.FracCell.HeightProjBoundSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace HeightProjBoundInternal

section Gen

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem sq_add {a b : α → ℂ} (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hai : Integrable (fun x => ‖a x‖ ^ 2) μ) (hbi : Integrable (fun x => ‖b x‖ ^ 2) μ) :
    Integrable (fun x => ‖a x + b x‖ ^ 2) μ := by
  refine Integrable.mono' ((hai.const_mul 2).add (hbi.const_mul 2)) ((ha.add hb).norm.pow 2) ?_
  refine ae_of_all _ (fun x => ?_)
  have h1 : ‖a x + b x‖ ≤ ‖a x‖ + ‖b x‖ := norm_add_le _ _
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  simp only [Real.norm_eq_abs, abs_pow, abs_norm, Pi.add_apply]
  nlinarith [norm_nonneg (a x), norm_nonneg (b x), sq_nonneg (‖a x‖ - ‖b x‖)]

theorem sq_sub {a b : α → ℂ} (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hai : Integrable (fun x => ‖a x‖ ^ 2) μ) (hbi : Integrable (fun x => ‖b x‖ ^ 2) μ) :
    Integrable (fun x => ‖a x - b x‖ ^ 2) μ := by
  have h := sq_add ha hb.neg hai (by simpa using hbi)
  simpa [sub_eq_add_neg] using h

theorem cross_int {a b : α → ℂ} (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hai : Integrable (fun x => ‖a x‖ ^ 2) μ) (hbi : Integrable (fun x => ‖b x‖ ^ 2) μ) :
    Integrable (fun x => a x * (starRingEnd ℂ) (b x)) μ := by
  refine Integrable.mono' (hai.add hbi) (ha.mul (Complex.continuous_conj.comp_aestronglyMeasurable hb)) ?_
  refine ae_of_all _ (fun x => ?_)
  simp only [norm_mul, Complex.norm_conj, Pi.add_apply]
  nlinarith [sq_nonneg (‖a x‖ - ‖b x‖), norm_nonneg (a x), norm_nonneg (b x)]

theorem sq_sum {ι : Type*} (S : Finset ι) (F : ι → α → ℂ) (hm : ∀ i, AEStronglyMeasurable (F i) μ)
    (hi : ∀ i, Integrable (fun x => ‖F i x‖ ^ 2) μ) :
    AEStronglyMeasurable (fun x => ∑ i ∈ S, F i x) μ ∧ Integrable (fun x => ‖∑ i ∈ S, F i x‖ ^ 2) μ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, norm_zero]
    exact ⟨aestronglyMeasurable_const, by simpa using (integrable_zero α ℝ μ)⟩
  | insert i S hiS ih =>
    simp only [Finset.sum_insert hiS]
    exact ⟨(hm i).add ih.1, sq_add (hm i) ih.1 (hi i) ih.2⟩

theorem weighted_le {w : α → ℝ} {C : ℝ} (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x) (hwm : AEStronglyMeasurable w μ)
    (hwb : ∀ᵐ x ∂μ, ‖w x‖ ≤ C) {a b : α → ℂ} (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hai : Integrable (fun x => ‖a x‖ ^ 2) μ) (hbi : Integrable (fun x => ‖b x‖ ^ 2) μ)
    (horth : ∫ x, (w x : ℂ) * (a x * (starRingEnd ℂ) (b x)) ∂μ = 0) :
    ∫ x, w x * ‖a x‖ ^ 2 ∂μ ≤ ∫ x, w x * ‖a x + b x‖ ^ 2 ∂μ := by
  have hA : Integrable (fun x => w x * ‖a x‖ ^ 2) μ := hai.bdd_mul hwm hwb
  have hB : Integrable (fun x => w x * ‖b x‖ ^ 2) μ := hbi.bdd_mul hwm hwb
  have hX : Integrable (fun x => (w x : ℂ) * (a x * (starRingEnd ℂ) (b x))) μ :=
    (cross_int ha hb hai hbi).bdd_mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hwm)
      (hwb.mono (fun x hx => by simpa using hx))
  have e : ∀ x, w x * ‖a x + b x‖ ^ 2 = w x * ‖a x‖ ^ 2 + w x * ‖b x‖ ^ 2
      + 2 * RCLike.re ((w x : ℂ) * (a x * (starRingEnd ℂ) (b x))) := fun x => by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add, RCLike.re_to_complex,
      Complex.re_ofReal_mul]
    ring
  have hre : ∫ x, RCLike.re ((w x : ℂ) * (a x * (starRingEnd ℂ) (b x))) ∂μ = 0 := by
    rw [integral_re hX, horth]
    simp
  simp only [e]
  rw [integral_add (f := fun x => w x * ‖a x‖ ^ 2 + w x * ‖b x‖ ^ 2) (hA.add hB) (hX.re.const_mul 2),
    integral_add hA hB, integral_const_mul, hre]
  have h0 : 0 ≤ ∫ x, w x * ‖b x‖ ^ 2 ∂μ :=
    integral_nonneg_of_ae (hw0.mono (fun x hx => mul_nonneg hx (sq_nonneg _)))
  linarith

end Gen

theorem sum_swap {m n : ℕ} (e : Fin m → Fin n → ℂ) (R : Fin m → ℂ) (Z : Fin n → ℂ) :
    ∑ l, (∑ j, e j l * R j) * Z l = ∑ j, (∑ l, e j l * Z l) * R j := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => by ring))

theorem lineProj_poly (ρ : ℝ → ℝ) (a b : ℝ) (d : ℕ) (f : ℝ → ℂ) :
    ∃ e : Fin (d + 1) → ℂ, ∀ x, lineProj ρ a b d f x = ∑ j, e j * (x : ℂ) ^ (j : ℕ) := by
  classical
  by_cases h : ∃ c : Fin (d + 1) → ℂ, ∀ t : Fin (d + 1),
      ∫ r in Set.Icc a b, (ρ r : ℂ) * (f r - ∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0
  · refine ⟨h.choose, fun x => ?_⟩
    unfold lineProj
    rw [dif_pos h]
  · refine ⟨0, fun x => ?_⟩
    unfold lineProj
    rw [dif_neg h]
    simp

open Classical in
theorem dite_pred {d : ℕ} (p q : (Fin (d + 1) → ℂ) → Prop) (h : p = q) (x : ℝ) :
    (if h : ∃ c, p c then ∑ j, h.choose j * (x : ℂ) ^ (j : ℕ) else 0)
      = (if h : ∃ c, q c then ∑ j, h.choose j * (x : ℂ) ^ (j : ℕ) else 0) := by
  subst h
  rfl

theorem lineProj_congr (ρ : ℝ → ℝ) (a b : ℝ) (d : ℕ) {f g : ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (Set.Icc a b)] g) : lineProj ρ a b d f = lineProj ρ a b d g := by
  have e : ∀ c : Fin (d + 1) → ℂ, ∀ t : Fin (d + 1),
      (∫ r in Set.Icc a b, (ρ r : ℂ) * (f r - ∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)))
        = ∫ r in Set.Icc a b, (ρ r : ℂ) * (g r - ∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) := by
    intro c t
    refine integral_congr_ae ?_
    filter_upwards [h] with r hr
    rw [hr]
  funext x
  exact dite_pred _ _ (funext (fun c => propext (forall_congr' (fun t => by rw [e c t])))) x

theorem dsum {m n : ℕ} (e : Fin m → Fin n → ℂ) (R : Fin m → ℂ) (Z : Fin n → ℂ) :
    ∑ l, (∑ j, e j l * R j) * Z l = ∑ j, ∑ l, e j l * R j * Z l := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

theorem proj_mem' (K : CellBox) (d d' : ℕ) (F : ℝ × ℝ → ℂ) : K.proj d d' F ∈ polyFn d d' := by
  unfold CellBox.proj
  split_ifs with h
  · exact h.choose_spec.1
  · exact ⟨fun _ _ => 0, fun p => by simp⟩

theorem poly_cont {d d' : ℕ} {P : ℝ × ℝ → ℂ} (hP : P ∈ polyFn d d') : Continuous P := by
  obtain ⟨c, hc⟩ := hP
  have : P = fun p : ℝ × ℝ => ∑ j : Fin (d + 1), ∑ l : Fin (d' + 1), c j l * ((p.1 : ℂ) ^ (j : ℕ)) * ((p.2 : ℂ) ^ (l : ℕ)) :=
    funext hc
  rw [this]
  fun_prop

variable (K : CellBox)

theorem rect_prod : volume.restrict K.rect
    = (volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
  rw [CellBox.rect, Measure.volume_eq_prod, Measure.prod_restrict]

theorem lw_cont : Continuous (fun r => K.lineWeight r) := by
  by_cases h : K.r₁ = 0
  · simp only [CellBox.lineWeight, h, if_true]
    exact continuous_id
  · simp only [CellBox.lineWeight, h, if_false]
    exact continuous_const

theorem lw_nonneg (hK : IsCellBox K) {r : ℝ} (hr : K.r₁ ≤ r) : 0 ≤ K.lineWeight r := by
  unfold CellBox.lineWeight
  split_ifs
  · linarith [hK.r_order.1]
  · norm_num

theorem lw_le (hK : IsCellBox K) {r : ℝ} (hr : r ∈ Set.Icc K.r₁ K.r₂) : ‖K.lineWeight r‖ ≤ K.r₂ + 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (lw_nonneg K hK hr.1)]
  unfold CellBox.lineWeight
  split_ifs
  · linarith [hr.2]
  · linarith [hK.r_order.1, hK.r_order.2]

theorem term_sq (j : ℕ) (e : ℝ → ℂ) (hem : AEStronglyMeasurable e (volume.restrict (Set.Icc K.z₁ K.z₂)))
    (hei : Integrable (fun z => ‖e z‖ ^ 2) (volume.restrict (Set.Icc K.z₁ K.z₂))) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => e p.2 * (p.1 : ℂ) ^ j) (volume.restrict K.rect) ∧
      Integrable (fun p : ℝ × ℝ => ‖e p.2 * (p.1 : ℂ) ^ j‖ ^ 2) (volume.restrict K.rect) := by
  rw [rect_prod]
  refine ⟨hem.comp_snd.mul (by fun_prop : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) ^ j)).aestronglyMeasurable, ?_⟩
  have h1 : Integrable (fun r : ℝ => ‖(r : ℂ) ^ j‖ ^ 2) (volume.restrict (Set.Icc K.r₁ K.r₂)) :=
    (by fun_prop : Continuous (fun r : ℝ => ‖(r : ℂ) ^ j‖ ^ 2)).integrableOn_Icc
  have h2 := h1.mul_prod hei
  refine h2.congr (ae_of_all _ (fun p => ?_))
  simp only [norm_mul, mul_pow]
  ring

theorem cont_sq {F : ℝ × ℝ → ℂ} (hF : Continuous F) :
    AEStronglyMeasurable F (volume.restrict K.rect) ∧ Integrable (fun p => ‖F p‖ ^ 2) (volume.restrict K.rect) :=
  ⟨hF.aestronglyMeasurable, ((hF.norm.pow 2).continuousOn).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)⟩

end HeightProjBoundInternal

open HeightProjBoundInternal in
theorem heightProjBound_of (hA : LineProjSpecStatement) (hB : ProjRCoeffStatement) (hD : RadialTopBoundStatement) :
    HeightProjBoundStatement := by
  intro K hK Q hQ s hs hsi
  obtain ⟨c, hc, hcz⟩ := hB K hK (Q - 1) s hs hsi
  have hz := hA K.z₁ K.z₂ (fun _ => 1) hK.z_order.1 hK.z_order.2 (Or.inl rfl) (Q - 2)
  have hzf : ∀ f : ℝ → ℂ, AEStronglyMeasurable f (volume.restrict (Set.Icc K.z₁ K.z₂)) →
      Integrable (fun z => ‖f z‖ ^ 2) (volume.restrict (Set.Icc K.z₁ K.z₂)) →
      (∀ t : Fin (Q - 2 + 1), ∫ z in Set.Icc K.z₁ K.z₂,
          (f z - lineProj (fun _ => 1) K.z₁ K.z₂ (Q - 2) f z) * (starRingEnd ℂ) ((z : ℂ) ^ (t : ℕ)) = 0) ∧
      ∀ e : Fin (Q - 2 + 1) → ℂ, (∀ t : Fin (Q - 2 + 1), ∫ z in Set.Icc K.z₁ K.z₂,
          (f z - ∑ j, e j * (z : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) ((z : ℂ) ^ (t : ℕ)) = 0) →
        ∀ x, lineProj (fun _ => 1) K.z₁ K.z₂ (Q - 2) f x = ∑ j, e j * (x : ℂ) ^ (j : ℕ) := by
    intro f hm hi
    have h := hz f hm (by simp only [one_mul]; exact hi)
    simp only [Complex.ofReal_one, one_mul] at h
    exact h
  have hpow : ∀ t : ℕ, AEStronglyMeasurable (fun z : ℝ => (z : ℂ) ^ t) (volume.restrict (Set.Icc K.z₁ K.z₂)) ∧
      Integrable (fun z : ℝ => ‖(z : ℂ) ^ t‖ ^ 2) (volume.restrict (Set.Icc K.z₁ K.z₂)) := fun t =>
    ⟨(by fun_prop : Continuous (fun z : ℝ => (z : ℂ) ^ t)).aestronglyMeasurable,
      (by fun_prop : Continuous (fun z : ℝ => ‖(z : ℂ) ^ t‖ ^ 2)).integrableOn_Icc⟩
  let b : Fin (Q - 1 + 1) → ℝ → ℂ := fun j => lineProj (fun _ => 1) K.z₁ K.z₂ (Q - 2) (c j)
  have hb_poly : ∀ j, ∃ e : Fin (Q - 2 + 1) → ℂ, ∀ x, b j x = ∑ l, e l * (x : ℂ) ^ (l : ℕ) :=
    fun j => lineProj_poly _ _ _ _ _
  choose eb heb using hb_poly
  have hbc : ∀ j, Continuous (b j) := by
    intro j
    rw [show b j = fun x : ℝ => ∑ l, eb j l * (x : ℂ) ^ (l : ℕ) from funext (heb j)]
    fun_prop
  have hbm : ∀ j, AEStronglyMeasurable (b j) (volume.restrict (Set.Icc K.z₁ K.z₂)) :=
    fun j => (hbc j).aestronglyMeasurable
  have hbi : ∀ j, Integrable (fun z => ‖b j z‖ ^ 2) (volume.restrict (Set.Icc K.z₁ K.z₂)) :=
    fun j => ((hbc j).norm.pow 2).integrableOn_Icc
  have hcbi : ∀ j, Integrable (fun z => ‖c j z - b j z‖ ^ 2) (volume.restrict (Set.Icc K.z₁ K.z₂)) :=
    fun j => sq_sub (hc j).1 (hbm j) (hc j).2 (hbi j)
  have hcorth : ∀ j, ∀ t : Fin (Q - 2 + 1), ∫ z in Set.Icc K.z₁ K.z₂,
      (c j z - b j z) * (starRingEnd ℂ) ((z : ℂ) ^ (t : ℕ)) = 0 :=
    fun j => (hzf (c j) (hc j).1 (hc j).2).1
  have hfr : ∀ r : ℝ, AEStronglyMeasurable (fun z => ∑ j, c j z * (r : ℂ) ^ (j : ℕ)) (volume.restrict (Set.Icc K.z₁ K.z₂)) ∧
      Integrable (fun z => ‖∑ j, c j z * (r : ℂ) ^ (j : ℕ)‖ ^ 2) (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
    intro r
    refine sq_sum Finset.univ (fun j z => c j z * (r : ℂ) ^ (j : ℕ)) (fun j => (hc j).1.mul_const _) (fun j => ?_)
    have e : (fun z => ‖c j z * (r : ℂ) ^ (j : ℕ)‖ ^ 2) = fun z => ‖(r : ℂ) ^ (j : ℕ)‖ ^ 2 * ‖c j z‖ ^ 2 := by
      funext z
      rw [norm_mul, mul_pow, mul_comm]
    rw [e]
    exact (hc j).2.const_mul _
  have step1 : ∀ r x : ℝ, lineProj (fun _ => 1) K.z₁ K.z₂ (Q - 2) (fun z => ∑ j, c j z * (r : ℂ) ^ (j : ℕ)) x
      = ∑ j, b j x * (r : ℂ) ^ (j : ℕ) := by
    intro r x
    have key := (hzf _ (hfr r).1 (hfr r).2).2 (fun l => ∑ j, eb j l * (r : ℂ) ^ (j : ℕ)) ?_ x
    · rw [key, sum_swap]
      exact Finset.sum_congr rfl (fun j _ => by rw [heb j x])
    · intro t
      have e : ∀ z : ℝ, ((∑ j : Fin (Q - 1 + 1), c j z * (r : ℂ) ^ (j : ℕ))
          - ∑ l : Fin (Q - 2 + 1), (∑ j : Fin (Q - 1 + 1), eb j l * (r : ℂ) ^ (j : ℕ)) * (z : ℂ) ^ (l : ℕ))
          * (starRingEnd ℂ) ((z : ℂ) ^ (t : ℕ))
          = ∑ j : Fin (Q - 1 + 1), (r : ℂ) ^ (j : ℕ) * ((c j z - b j z) * (starRingEnd ℂ) ((z : ℂ) ^ (t : ℕ))) := by
        intro z
        rw [sum_swap]
        simp only [← heb, ← Finset.sum_sub_distrib, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      simp only [e]
      rw [integral_finsetSum]
      · refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [integral_const_mul, hcorth j t, mul_zero]
      · intro j _
        exact (cross_int ((hc j).1.sub (hbm j)) (hpow t).1 (hcbi j) (hpow t).2).const_mul _
  have step1b : ∀ r x : ℝ, lineProj (fun _ => 1) K.z₁ K.z₂ (Q - 2) (fun z => K.projR (Q - 1) s (r, z)) x
      = ∑ j, b j x * (r : ℂ) ^ (j : ℕ) := by
    intro r x
    rw [lineProj_congr _ _ _ _ (hcz.mono (fun z hz => hz r))]
    exact step1 r x
  let D : ℝ × ℝ → ℂ := fun p => ∑ j : Fin (Q - 1 + 1), (c j p.2 - b j p.2) * (p.1 : ℂ) ^ (j : ℕ)
  have hDeq : ∀ p : ℝ × ℝ, D p = (∑ j : Fin (Q - 1 + 1), c j p.2 * (p.1 : ℂ) ^ (j : ℕ)) - ∑ j : Fin (Q - 1 + 1), b j p.2 * (p.1 : ℂ) ^ (j : ℕ) := by
    intro p
    simp only [D, ← Finset.sum_sub_distrib, sub_mul]
  have hD2 := sq_sum Finset.univ (fun j (p : ℝ × ℝ) => (c j p.2 - b j p.2) * (p.1 : ℂ) ^ (j : ℕ))
    (fun j => (term_sq K j _ ((hc j).1.sub (hbm j)) (hcbi j)).1) (fun j => (term_sq K j _ ((hc j).1.sub (hbm j)) (hcbi j)).2)
  have hwm : AEStronglyMeasurable (fun p : ℝ × ℝ => K.lineWeight p.1) (volume.restrict K.rect) :=
    ((lw_cont K).comp continuous_fst).aestronglyMeasurable
  have hwb : ∀ᵐ p ∂(volume.restrict K.rect), ‖K.lineWeight p.1‖ ≤ K.r₂ + 1 := by
    filter_upwards [ae_restrict_mem ((measurableSet_Icc.prod measurableSet_Icc))] with p hp
    exact lw_le K hK hp.1
  have hw0 : ∀ᵐ p ∂(volume.restrict K.rect), 0 ≤ K.lineWeight p.1 := by
    filter_upwards [ae_restrict_mem ((measurableSet_Icc.prod measurableSet_Icc))] with p hp
    exact lw_nonneg K hK hp.1.1
  let H : ℝ × ℝ → ℝ := fun p => K.lineWeight p.1 * ‖D p‖ ^ 2
  have hH : Integrable H ((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))) := by
    rw [← rect_prod]
    exact hD2.2.bdd_mul hwm hwb
  have hL : ∀ r, K.lineWeight r * ∫ z in Set.Icc K.z₁ K.z₂, (1 : ℝ) * ‖K.projR (Q - 1) s (r, z)
        - lineProj (fun _ => 1) K.z₁ K.z₂ (Q - 2) (fun z => K.projR (Q - 1) s (r, z)) z‖ ^ 2
      = ∫ z in Set.Icc K.z₁ K.z₂, H (r, z) := by
    intro r
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hcz] with z hz
    simp only [H, one_mul, step1b, hz r, hDeq]
  have hLfun : (fun r => K.lineWeight r * ∫ z in Set.Icc K.z₁ K.z₂, (1 : ℝ) * ‖K.projR (Q - 1) s (r, z)
        - lineProj (fun _ => 1) K.z₁ K.z₂ (Q - 2) (fun z => K.projR (Q - 1) s (r, z)) z‖ ^ 2)
      = fun r => ∫ z in Set.Icc K.z₁ K.z₂, H (r, z) := funext hL
  refine ⟨?_, ?_⟩
  · rw [hLfun]
    exact hH.integral_prod_left
  · rw [hLfun, ← integral_prod H hH, ← rect_prod]
    have hP := proj_mem' K (Q - 1) (Q - 2) s
    obtain ⟨pc, hpc⟩ := hP
    have hPc : Continuous (K.proj (Q - 1) (Q - 2) s) := poly_cont (proj_mem' K (Q - 1) (Q - 2) s)
    let Y : ℝ × ℝ → ℂ := fun p => (∑ j : Fin (Q - 1 + 1), b j p.2 * (p.1 : ℂ) ^ (j : ℕ)) - K.proj (Q - 1) (Q - 2) s p
    have hB2 := sq_sum Finset.univ (fun j (p : ℝ × ℝ) => b j p.2 * (p.1 : ℂ) ^ (j : ℕ))
      (fun j => (term_sq K j _ (hbm j) (hbi j)).1) (fun j => (term_sq K j _ (hbm j) (hbi j)).2)
    have hY2 : AEStronglyMeasurable Y (volume.restrict K.rect) ∧ Integrable (fun p => ‖Y p‖ ^ 2) (volume.restrict K.rect) :=
      ⟨hB2.1.sub (cont_sq K hPc).1, sq_sub hB2.1 (cont_sq K hPc).1 hB2.2 (cont_sq K hPc).2⟩
    have hY : ∀ r z : ℝ, Y (r, z) = ∑ l : Fin (Q - 2 + 1),
        (∑ j : Fin (Q - 1 + 1), (eb j l - pc j l) * (r : ℂ) ^ (j : ℕ)) * (z : ℂ) ^ (l : ℕ) := by
      intro r z
      rw [dsum]
      simp only [Y, hpc, heb, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    have hDr : ∀ r : ℝ, AEStronglyMeasurable (fun z => D (r, z)) (volume.restrict (Set.Icc K.z₁ K.z₂)) ∧
        Integrable (fun z => ‖D (r, z)‖ ^ 2) (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
      intro r
      refine sq_sum Finset.univ (fun j z => (c j z - b j z) * (r : ℂ) ^ (j : ℕ))
        (fun j => ((hc j).1.sub (hbm j)).mul_const _) (fun j => ?_)
      have e : (fun z => ‖(c j z - b j z) * (r : ℂ) ^ (j : ℕ)‖ ^ 2)
          = fun z => ‖(r : ℂ) ^ (j : ℕ)‖ ^ 2 * ‖c j z - b j z‖ ^ 2 := by
        funext z
        rw [norm_mul, mul_pow, mul_comm]
      rw [e]
      exact (hcbi j).const_mul _
    have hinner : ∀ r : ℝ, ∫ z in Set.Icc K.z₁ K.z₂, D (r, z) * (starRingEnd ℂ) (Y (r, z)) = 0 := by
      intro r
      have horth : ∀ l : Fin (Q - 2 + 1), ∫ z in Set.Icc K.z₁ K.z₂,
          D (r, z) * (starRingEnd ℂ) ((z : ℂ) ^ (l : ℕ)) = 0 := by
        intro l
        have h := (hzf _ (hfr r).1 (hfr r).2).1 l
        simp only [step1] at h
        rw [← h]
        refine integral_congr_ae (ae_of_all _ (fun z => ?_))
        simp only [hDeq]
      have e : ∀ z : ℝ, D (r, z) * (starRingEnd ℂ) (Y (r, z))
          = ∑ l : Fin (Q - 2 + 1), (starRingEnd ℂ) (∑ j : Fin (Q - 1 + 1), (eb j l - pc j l) * (r : ℂ) ^ (j : ℕ))
            * (D (r, z) * (starRingEnd ℂ) ((z : ℂ) ^ (l : ℕ))) := by
        intro z
        rw [hY, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [map_mul]
        ring
      simp only [e]
      rw [integral_finsetSum]
      · refine Finset.sum_eq_zero (fun l _ => ?_)
        rw [integral_const_mul, horth l, mul_zero]
      · intro l _
        exact (cross_int (hDr r).1 (hpow l).1 (hDr r).2 (hpow l).2).const_mul _
    have hX : Integrable (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * (D p * (starRingEnd ℂ) (Y p)))
        (volume.restrict K.rect) :=
      (cross_int hD2.1 hY2.1 hD2.2 hY2.2).bdd_mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hwm)
        (hwb.mono (fun x hx => by simpa using hx))
    have horth2 : ∫ p, (K.lineWeight p.1 : ℂ) * (D p * (starRingEnd ℂ) (Y p)) ∂(volume.restrict K.rect) = 0 := by
      rw [rect_prod] at hX ⊢
      rw [integral_prod _ hX]
      refine integral_eq_zero_of_ae (ae_of_all _ (fun r => ?_))
      simp only [Pi.zero_apply]
      rw [integral_const_mul, hinner r, mul_zero]
    have step3 := weighted_le hw0 hwm hwb hD2.1 hY2.1 hD2.2 hY2.2 horth2
    have hae : ∀ᵐ p ∂(volume.restrict K.rect), K.projR (Q - 1) s p = ∑ j : Fin (Q - 1 + 1), c j p.2 * (p.1 : ℂ) ^ (j : ℕ) := by
      rw [rect_prod]
      have h := (Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Set.Icc K.r₁ K.r₂))
        (ν := volume.restrict (Set.Icc K.z₁ K.z₂))).ae hcz
      filter_upwards [h] with p hp
      simpa using hp p.1
    have step4 : ∫ p, K.lineWeight p.1 * ‖D p + Y p‖ ^ 2 ∂(volume.restrict K.rect)
        = K.normSqOn K.lineWeightFn (fun p => K.projR (Q - 1) s p - K.proj (Q - 1) (Q - 2) s p) := by
      unfold CellBox.normSqOn CellBox.lineWeightFn
      refine integral_congr_ae ?_
      filter_upwards [hae] with p hp
      rw [hp, hDeq]
      simp only [Y, sub_add_sub_cancel]
    calc ∫ p, H p ∂(volume.restrict K.rect)
        ≤ ∫ p, K.lineWeight p.1 * ‖D p + Y p‖ ^ 2 ∂(volume.restrict K.rect) := step3
      _ = _ := step4
      _ ≤ _ := hD K hK Q hQ s hs hsi

namespace HeightProjBoundInternal

def momentMatrix (ρ : ℝ → ℝ) (a b : ℝ) (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  fun t j => ∫ r in Set.Icc a b, (ρ r : ℂ) * (r : ℂ) ^ (j : ℕ) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))

theorem cont_int {E : Type*} [NormedAddCommGroup E] {a b : ℝ} {g : ℝ → E} (hg : Continuous g) : Integrable g (volume.restrict (Set.Icc a b)) :=
  hg.integrableOn_Icc

theorem poly_moment {a b : ℝ} {ρ : ℝ → ℝ} (hρc : Continuous ρ) (d : ℕ) (c : Fin (d + 1) → ℂ) (t : Fin (d + 1)) :
    ∫ r in Set.Icc a b, (ρ r : ℂ) * (∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))
      = ((momentMatrix ρ a b d).mulVec c) t := by
  simp only [Matrix.mulVec, dotProduct, momentMatrix]
  have e : ∀ r : ℝ, (ρ r : ℂ) * (∑ j : Fin (d + 1), c j * (r : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))
      = ∑ j : Fin (d + 1), ((ρ r : ℂ) * (r : ℂ) ^ (j : ℕ) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))) * c j := by
    intro r
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  simp only [e]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl (fun j _ => by rw [integral_mul_const])
  · intro j _
    exact cont_int (by fun_prop)

theorem poly_zero {a b : ℝ} {ρ : ℝ → ℝ} (hab : a < b) (hρc : Continuous ρ) (hρ0 : ∀ x ∈ Set.Icc a b, 0 ≤ ρ x)
    (hρpos : ∀ x ∈ Set.Ioo a b, 0 < ρ x) {d : ℕ} (c : Fin (d + 1) → ℂ) (h : (momentMatrix ρ a b d).mulVec c = 0) :
    c = 0 := by
  have hp : Continuous (fun r : ℝ => ∑ j, c j * (r : ℂ) ^ (j : ℕ)) := by fun_prop
  have h1 : ∫ r in Set.Icc a b, (ρ r : ℂ) * (∑ j, c j * (r : ℂ) ^ (j : ℕ))
      * (starRingEnd ℂ) (∑ j, c j * (r : ℂ) ^ (j : ℕ)) = 0 := by
    have e : ∀ r : ℝ, (ρ r : ℂ) * (∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) (∑ j, c j * (r : ℂ) ^ (j : ℕ))
        = ∑ t : Fin (d + 1), (starRingEnd ℂ) (c t) * ((ρ r : ℂ) * (∑ j, c j * (r : ℂ) ^ (j : ℕ))
          * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))) := by
      intro r
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [map_mul]
      ring
    simp only [e]
    rw [integral_finsetSum]
    · refine Finset.sum_eq_zero (fun t _ => ?_)
      rw [integral_const_mul, poly_moment hρc, h]
      simp
    · intro t _
      exact cont_int (by fun_prop)
  have h2 : ∫ r in Set.Icc a b, ρ r * ‖∑ j, c j * (r : ℂ) ^ (j : ℕ)‖ ^ 2 = 0 := by
    have e : ∀ r : ℝ, (((ρ r * ‖∑ j, c j * (r : ℂ) ^ (j : ℕ)‖ ^ 2 : ℝ)) : ℂ)
        = (ρ r : ℂ) * (∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) (∑ j, c j * (r : ℂ) ^ (j : ℕ)) := by
      intro r
      rw [mul_assoc, Complex.mul_conj, Complex.sq_norm]
      push_cast
      ring
    have h3 := integral_complex_ofReal (μ := volume.restrict (Set.Icc a b))
      (f := fun r => ρ r * ‖∑ j, c j * (r : ℂ) ^ (j : ℕ)‖ ^ 2)
    simp only [e, h1] at h3
    exact_mod_cast h3.symm
  have hc : Continuous (fun r : ℝ => ρ r * ‖∑ j, c j * (r : ℂ) ^ (j : ℕ)‖ ^ 2) := by fun_prop
  have h3 : (fun r : ℝ => ρ r * ‖∑ j, c j * (r : ℂ) ^ (j : ℕ)‖ ^ 2) =ᵐ[volume.restrict (Set.Icc a b)] 0 := by
    refine (integral_eq_zero_iff_of_nonneg_ae ?_ (cont_int hc)).1 h2
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact mul_nonneg (hρ0 r hr) (sq_nonneg _)
  have h4 := ae_restrict_of_ae_restrict_of_subset Set.Ioo_subset_Icc_self h3
  have h5 := Measure.eqOn_open_of_ae_eq h4 isOpen_Ioo hc.continuousOn continuousOn_const
  have h6 : ∀ x ∈ Set.Ioo a b, ∑ j, c j * (x : ℂ) ^ (j : ℕ) = 0 := by
    intro x hx
    have := h5 hx
    simp only [Pi.zero_apply, mul_eq_zero, (hρpos x hx).ne', false_or, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] at this
    exact this
  let P : Polynomial ℂ := ∑ j : Fin (d + 1), Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)
  have hP : ∀ x : ℝ, P.eval (x : ℂ) = ∑ j, c j * (x : ℂ) ^ (j : ℕ) := by
    intro x
    simp [P, Polynomial.eval_finset_sum]
  have hP0 : P = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot P ?_
    refine Set.Infinite.mono ?_ ((Set.Ioo_infinite hab).image Complex.ofReal_injective.injOn)
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, hP]
    exact h6 x hx
  funext j
  have := congrArg (fun P : Polynomial ℂ => P.coeff (j : ℕ)) hP0
  simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single j] at this
  · simpa using this
  · intro i _ hij
    rw [if_neg]
    intro h'
    exact hij (Fin.ext h'.symm)
  · simp

theorem moment_int {a b : ℝ} {ρ : ℝ → ℝ} (hρc : Continuous ρ) (hρ0 : ∀ x ∈ Set.Icc a b, 0 ≤ ρ x)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc a b)))
    (hfi : IntegrableOn (fun r => ρ r * ‖f r‖ ^ 2) (Set.Icc a b)) (t : ℕ) :
    Integrable (fun r => (ρ r : ℂ) * f r * (starRingEnd ℂ) ((r : ℂ) ^ t)) (volume.restrict (Set.Icc a b)) := by
  have hg : Integrable (fun r : ℝ => ρ r * ‖(r : ℂ) ^ t‖ ^ 2) (volume.restrict (Set.Icc a b)) :=
    cont_int (by fun_prop)
  refine Integrable.mono' (hfi.add hg) (((Complex.continuous_ofReal.comp hρc).aestronglyMeasurable.mul hf).mul
    (by fun_prop : Continuous (fun r : ℝ => (starRingEnd ℂ) ((r : ℂ) ^ t))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  have h0 := hρ0 r hr
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0, Complex.norm_conj, Pi.add_apply]
  nlinarith [mul_nonneg h0 (sq_nonneg (‖f r‖ - ‖(r : ℂ) ^ t‖)), norm_nonneg (f r), norm_nonneg ((r : ℂ) ^ t)]

theorem lineProj_gen {a b : ℝ} {ρ : ℝ → ℝ} (hab : a < b) (hρc : Continuous ρ) (hρ0 : ∀ x ∈ Set.Icc a b, 0 ≤ ρ x)
    (hρpos : ∀ x ∈ Set.Ioo a b, 0 < ρ x) (d : ℕ) (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc a b)))
    (hfi : IntegrableOn (fun r => ρ r * ‖f r‖ ^ 2) (Set.Icc a b)) :
      (∀ t : Fin (d + 1), ∫ r in Set.Icc a b, (ρ r : ℂ) * (f r - lineProj ρ a b d f r)
          * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0) ∧
      ∀ c : Fin (d + 1) → ℂ, (∀ t : Fin (d + 1), ∫ r in Set.Icc a b, (ρ r : ℂ) * (f r - ∑ j, c j * (r : ℂ) ^ (j : ℕ))
          * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0) →
        ∀ x, lineProj ρ a b d f x = ∑ j, c j * (x : ℂ) ^ (j : ℕ) := by
  have hfint : ∀ t : ℕ, Integrable (fun r => (ρ r : ℂ) * f r * (starRingEnd ℂ) ((r : ℂ) ^ t))
      (volume.restrict (Set.Icc a b)) := by
    intro t
    have hg : Integrable (fun r : ℝ => ρ r * ‖(r : ℂ) ^ t‖ ^ 2) (volume.restrict (Set.Icc a b)) :=
      cont_int (by fun_prop)
    refine Integrable.mono' (hfi.add hg) (((Complex.continuous_ofReal.comp hρc).aestronglyMeasurable.mul hf).mul
      (by fun_prop : Continuous (fun r : ℝ => (starRingEnd ℂ) ((r : ℂ) ^ t))).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have h0 := hρ0 r hr
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0, Complex.norm_conj, Pi.add_apply]
    nlinarith [mul_nonneg h0 (sq_nonneg (‖f r‖ - ‖(r : ℂ) ^ t‖)), norm_nonneg (f r), norm_nonneg ((r : ℂ) ^ t)]
  let m : Fin (d + 1) → ℂ := fun t => ∫ r in Set.Icc a b, (ρ r : ℂ) * f r * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))
  have hcond : ∀ c : Fin (d + 1) → ℂ, (∀ t : Fin (d + 1), ∫ r in Set.Icc a b, (ρ r : ℂ) * (f r - ∑ j, c j * (r : ℂ) ^ (j : ℕ))
      * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0) ↔ (momentMatrix ρ a b d).mulVec c = m := by
    intro c
    have e : ∀ t : Fin (d + 1), ∫ r in Set.Icc a b, (ρ r : ℂ) * (f r - ∑ j, c j * (r : ℂ) ^ (j : ℕ))
        * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = m t - ((momentMatrix ρ a b d).mulVec c) t := by
      intro t
      rw [← poly_moment hρc, ← integral_sub (hfint t) (cont_int (by fun_prop))]
      refine integral_congr_ae (ae_of_all _ (fun r => ?_))
      ring
    simp only [e, sub_eq_zero]
    constructor
    · intro h
      funext t
      exact (h t).symm
    · intro h t
      rw [h]
  have hinj : Function.Injective (momentMatrix ρ a b d).mulVecLin := by
    intro x y hxy
    have hxy' : (momentMatrix ρ a b d).mulVec x = (momentMatrix ρ a b d).mulVec y := hxy
    have := poly_zero hab hρc hρ0 hρpos (x - y) (by rw [Matrix.mulVec_sub, hxy', sub_self])
    exact sub_eq_zero.1 this
  obtain ⟨c0, hc0⟩ := (LinearMap.injective_iff_surjective.1 hinj) m
  have hex : ∃ c : Fin (d + 1) → ℂ, ∀ t : Fin (d + 1),
      ∫ r in Set.Icc a b, (ρ r : ℂ) * (f r - ∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0 :=
    ⟨c0, (hcond c0).2 hc0⟩
  have hlp : ∀ x, lineProj ρ a b d f x = ∑ j, hex.choose j * (x : ℂ) ^ (j : ℕ) := by
    intro x
    unfold lineProj
    rw [dif_pos hex]
  refine ⟨fun t => ?_, fun c hc x => ?_⟩
  · simp only [hlp]
    exact hex.choose_spec t
  · rw [hlp]
    have h1 := (hcond _).1 hex.choose_spec
    have h2 := (hcond c).1 hc
    have : hex.choose = c := hinj (by simp only [Matrix.mulVecLin_apply, h1, h2])
    rw [this]

end HeightProjBoundInternal

open HeightProjBoundInternal in
theorem lineProjSpec : LineProjSpecStatement := by
  intro a b ρ ha hab hρ d f hf hfi
  rcases hρ with rfl | ⟨rfl, rfl⟩
  · exact lineProj_gen hab continuous_const (fun _ _ => zero_le_one) (fun _ _ => one_pos) d f hf hfi
  · exact lineProj_gen hab continuous_id (fun x hx => hx.1) (fun x hx => hx.1) d f hf hfi


namespace HeightProjBoundInternal

theorem weightedInner_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {w : α → ℝ} (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hwm : AEStronglyMeasurable w μ) {g P : α → ℂ}
    (hg : AEStronglyMeasurable g μ) (hP : AEStronglyMeasurable P μ)
    (hgi : Integrable (fun x => w x * ‖g x‖ ^ 2) μ) (hPi : Integrable (fun x => w x * ‖P x‖ ^ 2) μ) :
    ‖∫ x, (w x : ℂ) * g x * (starRingEnd ℂ) (P x) ∂μ‖ ^ 2
      ≤ (∫ x, w x * ‖g x‖ ^ 2 ∂μ) * ∫ x, w x * ‖P x‖ ^ 2 ∂μ := by
  have hXi : Integrable (fun x => w x * (‖g x‖ * ‖P x‖)) μ := by
    refine Integrable.mono' (hgi.add hPi) (hwm.mul (hg.norm.mul hP.norm)) ?_
    filter_upwards [hw0] with x h0
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg h0, abs_norm, Pi.add_apply]
    nlinarith [mul_nonneg h0 (sq_nonneg (‖g x‖ - ‖P x‖)), norm_nonneg (g x), norm_nonneg (P x),
      mul_nonneg h0 (mul_nonneg (norm_nonneg (g x)) (norm_nonneg (P x)))]
  set X := ∫ x, w x * (‖g x‖ * ‖P x‖) ∂μ
  have hle : ‖∫ x, (w x : ℂ) * g x * (starRingEnd ℂ) (P x) ∂μ‖ ≤ X := by
    refine norm_integral_le_of_norm_le hXi ?_
    filter_upwards [hw0] with x h0
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0, Complex.norm_conj]
    ring_nf
    exact le_refl _
  have hquad : ∀ t : ℝ, 0 ≤ (∫ x, w x * ‖P x‖ ^ 2 ∂μ) * (t * t) + (-2 * X) * t + ∫ x, w x * ‖g x‖ ^ 2 ∂μ := by
    intro t
    have h1 : 0 ≤ ∫ x, w x * (‖g x‖ - t * ‖P x‖) ^ 2 ∂μ :=
      integral_nonneg_of_ae (hw0.mono (fun x hx => mul_nonneg hx (sq_nonneg _)))
    have h2 : ∫ x, w x * (‖g x‖ - t * ‖P x‖) ^ 2 ∂μ
        = (∫ x, w x * ‖g x‖ ^ 2 ∂μ) - 2 * t * X + t * t * ∫ x, w x * ‖P x‖ ^ 2 ∂μ := by
      have e : ∀ x, w x * (‖g x‖ - t * ‖P x‖) ^ 2
          = w x * ‖g x‖ ^ 2 - (2 * t) * (w x * (‖g x‖ * ‖P x‖)) + (t * t) * (w x * ‖P x‖ ^ 2) := fun x => by ring
      simp only [e]
      rw [integral_add (f := fun x => w x * ‖g x‖ ^ 2 - 2 * t * (w x * (‖g x‖ * ‖P x‖)))
        (hgi.sub (hXi.const_mul _)) (hPi.const_mul _), integral_sub hgi (hXi.const_mul _),
        integral_const_mul, integral_const_mul]
    linarith
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  have hX0 : 0 ≤ ‖∫ x, (w x : ℂ) * g x * (starRingEnd ℂ) (P x) ∂μ‖ := norm_nonneg _
  nlinarith

variable (K : CellBox)

theorem lw_pos (hK : IsCellBox K) {r : ℝ} (hr : r ∈ Set.Ioo K.r₁ K.r₂) : 0 < K.lineWeight r := by
  unfold CellBox.lineWeight
  split_ifs with h
  · rw [h] at hr
    exact hr.1
  · norm_num

end HeightProjBoundInternal

open HeightProjBoundInternal in
theorem projRCoeff : ProjRCoeffStatement := by
  intro K hK d s hs hsi
  have hρc := lw_cont K
  have hρ0 : ∀ x ∈ Set.Icc K.r₁ K.r₂, 0 ≤ K.lineWeight x := fun x hx => lw_nonneg K hK hx.1
  have hρpos : ∀ x ∈ Set.Ioo K.r₁ K.r₂, 0 < K.lineWeight x := fun x hx => lw_pos K hK hx
  have hab := hK.r_order.2
  let M := momentMatrix (fun r => K.lineWeight r) K.r₁ K.r₂ d
  have hinj : Function.Injective M.mulVec := by
    intro x y hxy
    have := poly_zero hab hρc hρ0 hρpos (x - y) (by rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 hxy)
    exact sub_eq_zero.1 this
  have hU : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 (Matrix.mulVec_injective_iff_isUnit.1 hinj)
  let m : Fin (d + 1) → ℝ → ℂ := fun t z =>
    ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * s (r, z) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))
  have hs' : AEStronglyMeasurable s ((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))) := by
    rw [← rect_prod]
    exact hs
  have hsi' : Integrable (fun p => K.lineWeight p.1 * ‖s p‖ ^ 2)
      ((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))) := by
    rw [← rect_prod]
    exact hsi
  have hmm : ∀ t : Fin (d + 1), AEStronglyMeasurable (m t) (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
    intro t
    have hF : AEStronglyMeasurable (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * s p * (starRingEnd ℂ) ((p.1 : ℂ) ^ (t : ℕ)))
        ((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))) :=
      ((Complex.continuous_ofReal.comp (hρc.comp continuous_fst)).aestronglyMeasurable.mul hs').mul
        (by fun_prop : Continuous (fun p : ℝ × ℝ => (starRingEnd ℂ) ((p.1 : ℂ) ^ (t : ℕ)))).aestronglyMeasurable
    exact hF.prod_swap.integral_prod_right'
  have hA := hsi'.integral_prod_right
  have hslice := hsi'.prod_left_ae
  have hsm := hs'.prodMk_right
  have hmi : ∀ t : Fin (d + 1), Integrable (fun z => ‖m t z‖ ^ 2) (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
    intro t
    refine Integrable.mono' (hA.const_mul (∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ‖(r : ℂ) ^ (t : ℕ)‖ ^ 2))
      ((hmm t).norm.pow 2) ?_
    filter_upwards [hslice, hsm] with z hz hzm
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_comm]
    refine weightedInner_le (ae_restrict_of_forall_mem measurableSet_Icc hρ0) (hρc.aestronglyMeasurable) hzm
      (by fun_prop : Continuous (fun r : ℝ => (r : ℂ) ^ (t : ℕ))).aestronglyMeasurable hz (cont_int (by fun_prop))
  let c : Fin (d + 1) → ℝ → ℂ := fun j z => (M⁻¹.mulVec (fun t => m t z)) j
  have hcsum : ∀ j z, c j z = ∑ t, M⁻¹ j t * m t z := fun j z => rfl
  refine ⟨c, fun j => ?_, ?_⟩
  · have hsum := sq_sum Finset.univ (fun t z => M⁻¹ j t * m t z) (fun t => (hmm t).const_mul _) (fun t => by
      have e : (fun z => ‖M⁻¹ j t * m t z‖ ^ 2) = fun z => ‖M⁻¹ j t‖ ^ 2 * ‖m t z‖ ^ 2 := by
        funext z
        rw [norm_mul, mul_pow]
      rw [e]
      exact (hmi t).const_mul _)
    exact ⟨hsum.1, hsum.2⟩
  · filter_upwards [hslice, hsm] with z hz hzm
    intro r
    have hspec := lineProj_gen hab hρc hρ0 hρpos d (fun r => s (r, z)) hzm hz
    have key : ∀ t : Fin (d + 1), ∫ x in Set.Icc K.r₁ K.r₂, (K.lineWeight x : ℂ) * (s (x, z) - ∑ j, c j z * (x : ℂ) ^ (j : ℕ))
        * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ)) = 0 := by
      intro t
      have h1 := poly_moment (a := K.r₁) (b := K.r₂) hρc d (fun j => c j z) t
      have h2 : M.mulVec (fun j => c j z) = fun t => m t z := by
        show M.mulVec (M⁻¹.mulVec (fun t => m t z)) = _
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hU, Matrix.one_mulVec]
      have h3 : ∫ x in Set.Icc K.r₁ K.r₂, (K.lineWeight x : ℂ) * (s (x, z) - ∑ j, c j z * (x : ℂ) ^ (j : ℕ))
          * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ))
          = m t z - ∫ x in Set.Icc K.r₁ K.r₂, (K.lineWeight x : ℂ) * (∑ j, c j z * (x : ℂ) ^ (j : ℕ))
            * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ)) := by
        rw [← integral_sub (moment_int hρc hρ0 hzm hz t) (cont_int (by fun_prop))]
        refine integral_congr_ae (ae_of_all _ (fun x => ?_))
        ring
      rw [h3]
      have h1' : ∫ x in Set.Icc K.r₁ K.r₂, (K.lineWeight x : ℂ) * (∑ j, c j z * (x : ℂ) ^ (j : ℕ))
            * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ)) = M.mulVec (fun j => c j z) t := h1
      rw [h1', h2, sub_self]
    exact hspec.2 (fun j => c j z) key r


namespace HeightProjBoundInternal

variable (K : CellBox)

def WL2 (F : ℝ × ℝ → ℂ) : Prop :=
  AEStronglyMeasurable F (volume.restrict K.rect) ∧
    Integrable (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) (volume.restrict K.rect)

theorem w_meas : AEStronglyMeasurable (fun p : ℝ × ℝ => K.lineWeight p.1) (volume.restrict K.rect) :=
  ((lw_cont K).comp continuous_fst).aestronglyMeasurable

theorem w_bound (hK : IsCellBox K) : ∀ᵐ p ∂(volume.restrict K.rect), ‖K.lineWeight p.1‖ ≤ K.r₂ + 1 := by
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
  exact lw_le K hK hp.1

theorem w_nonneg (hK : IsCellBox K) : ∀ᵐ p ∂(volume.restrict K.rect), 0 ≤ K.lineWeight p.1 := by
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
  exact lw_nonneg K hK hp.1.1

theorem wl2_of_sq (hK : IsCellBox K) {F : ℝ × ℝ → ℂ} (h : AEStronglyMeasurable F (volume.restrict K.rect) ∧
    Integrable (fun p => ‖F p‖ ^ 2) (volume.restrict K.rect)) : WL2 K F :=
  ⟨h.1, h.2.bdd_mul (w_meas K) (w_bound K hK)⟩

theorem wl2_add (hK : IsCellBox K) {F G : ℝ × ℝ → ℂ} (hF : WL2 K F) (hG : WL2 K G) :
    WL2 K (fun p => F p + G p) := by
  refine ⟨hF.1.add hG.1, ?_⟩
  refine Integrable.mono' ((hF.2.const_mul 2).add (hG.2.const_mul 2))
    ((w_meas K).mul ((hF.1.add hG.1).norm.pow 2)) ?_
  filter_upwards [w_nonneg K hK] with p h0
  have h1 : ‖F p + G p‖ ≤ ‖F p‖ + ‖G p‖ := norm_add_le _ _
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : ‖F p + G p‖ ^ 2 ≤ 2 * ‖F p‖ ^ 2 + 2 * ‖G p‖ ^ 2 := by
    nlinarith [norm_nonneg (F p), norm_nonneg (G p), sq_nonneg (‖F p‖ - ‖G p‖)]
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg h0, abs_pow, abs_norm, Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left h3 h0]

theorem wl2_smul (c : ℂ) {F : ℝ × ℝ → ℂ} (hF : WL2 K F) : WL2 K (fun p => c * F p) := by
  refine ⟨hF.1.const_mul c, ?_⟩
  have e : (fun p : ℝ × ℝ => K.lineWeight p.1 * ‖c * F p‖ ^ 2) = fun p => ‖c‖ ^ 2 * (K.lineWeight p.1 * ‖F p‖ ^ 2) := by
    funext p
    rw [norm_mul, mul_pow]
    ring
  rw [e]
  exact hF.2.const_mul _

theorem wl2_sub (hK : IsCellBox K) {F G : ℝ × ℝ → ℂ} (hF : WL2 K F) (hG : WL2 K G) :
    WL2 K (fun p => F p - G p) := by
  have h := wl2_add K hK hF (wl2_smul K (-1) hG)
  have e : (fun p => F p + -1 * G p) = fun p => F p - G p := by
    funext p
    ring
  rw [e] at h
  exact h

theorem wl2_sum (hK : IsCellBox K) {ι : Type*} (S : Finset ι) (F : ι → ℝ × ℝ → ℂ) (h : ∀ i, WL2 K (F i)) :
    WL2 K (fun p => ∑ i ∈ S, F i p) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨aestronglyMeasurable_const, ?_⟩
    simpa using (integrable_zero (ℝ × ℝ) ℝ (volume.restrict K.rect))
  | insert i S hiS ih =>
    simp only [Finset.sum_insert hiS]
    exact wl2_add K hK (h i) ih

theorem wl2_cont (hK : IsCellBox K) {F : ℝ × ℝ → ℂ} (hF : Continuous F) : WL2 K F :=
  wl2_of_sq K hK (cont_sq K hF)

theorem wcross (hK : IsCellBox K) {F G : ℝ × ℝ → ℂ} (hF : WL2 K F) (hG : WL2 K G) :
    Integrable (fun p => (K.lineWeight p.1 : ℂ) * F p * (starRingEnd ℂ) (G p)) (volume.restrict K.rect) := by
  refine Integrable.mono' (hF.2.add hG.2)
    (((Complex.continuous_ofReal.comp_aestronglyMeasurable (w_meas K)).mul hF.1).mul
      (Complex.continuous_conj.comp_aestronglyMeasurable hG.1)) ?_
  filter_upwards [w_nonneg K hK] with p h0
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0, Complex.norm_conj, Pi.add_apply]
  nlinarith [mul_nonneg h0 (sq_nonneg (‖F p‖ - ‖G p‖)), norm_nonneg (F p), norm_nonneg (G p)]

theorem pair_sub_left (hK : IsCellBox K) {F₁ F₂ G : ℝ × ℝ → ℂ} (h₁ : WL2 K F₁) (h₂ : WL2 K F₂) (hG : WL2 K G) :
    K.pairOn K.lineWeightFn (fun p => F₁ p - F₂ p) G = K.pairOn K.lineWeightFn F₁ G - K.pairOn K.lineWeightFn F₂ G := by
  unfold CellBox.pairOn CellBox.lineWeightFn
  rw [← integral_sub (wcross K hK h₁ hG) (wcross K hK h₂ hG)]
  refine integral_congr_ae (ae_of_all _ (fun p => ?_))
  ring

theorem pair_sub_right (hK : IsCellBox K) {F G₁ G₂ : ℝ × ℝ → ℂ} (hF : WL2 K F) (h₁ : WL2 K G₁) (h₂ : WL2 K G₂) :
    K.pairOn K.lineWeightFn F (fun p => G₁ p - G₂ p) = K.pairOn K.lineWeightFn F G₁ - K.pairOn K.lineWeightFn F G₂ := by
  unfold CellBox.pairOn CellBox.lineWeightFn
  rw [← integral_sub (wcross K hK hF h₁) (wcross K hK hF h₂)]
  refine integral_congr_ae (ae_of_all _ (fun p => ?_))
  simp only [map_sub]
  ring

theorem pair_self (F : ℝ × ℝ → ℂ) :
    K.pairOn K.lineWeightFn F F = (K.normSqOn K.lineWeightFn F : ℂ) := by
  unfold CellBox.pairOn CellBox.normSqOn
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ (fun p => ?_))
  show (K.lineWeightFn p : ℂ) * F p * (starRingEnd ℂ) (F p) = ((K.lineWeightFn p * ‖F p‖ ^ 2 : ℝ) : ℂ)
  rw [mul_assoc, Complex.mul_conj, Complex.sq_norm]
  push_cast
  ring

theorem normSq_add' (hK : IsCellBox K) {a b : ℝ × ℝ → ℂ} (ha : WL2 K a) (hb : WL2 K b) :
    K.normSqOn K.lineWeightFn (fun p => a p + b p)
      = K.normSqOn K.lineWeightFn a + K.normSqOn K.lineWeightFn b + 2 * (K.pairOn K.lineWeightFn a b).re := by
  have hX := wcross K hK ha hb
  have e : ∀ p : ℝ × ℝ, K.lineWeight p.1 * ‖a p + b p‖ ^ 2 = K.lineWeight p.1 * ‖a p‖ ^ 2 + K.lineWeight p.1 * ‖b p‖ ^ 2
      + 2 * RCLike.re ((K.lineWeight p.1 : ℂ) * a p * (starRingEnd ℂ) (b p)) := fun p => by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add, RCLike.re_to_complex, mul_assoc,
      Complex.re_ofReal_mul]
    ring
  unfold CellBox.normSqOn CellBox.lineWeightFn
  simp only [e]
  rw [integral_add (f := fun p => K.lineWeight p.1 * ‖a p‖ ^ 2 + K.lineWeight p.1 * ‖b p‖ ^ 2) (ha.2.add hb.2)
    (hX.re.const_mul 2), integral_add ha.2 hb.2, integral_const_mul, integral_re hX]
  rfl

theorem orth_poly (hK : IsCellBox K) {F : ℝ × ℝ → ℂ} (hF : WL2 K F) {d d' : ℕ} {T : ℝ × ℝ → ℂ}
    (hT : T ∈ polyFn d d') {D D' : ℕ} (hd : d ≤ D) (hd' : d' ≤ D')
    (h : ∀ j l : ℕ, j ≤ D → l ≤ D' → K.pairOn K.lineWeightFn F (fun p => (p.1 : ℂ) ^ j * (p.2 : ℂ) ^ l) = 0) :
    K.pairOn K.lineWeightFn F T = 0 := by
  obtain ⟨c, hc⟩ := hT
  have hm : ∀ j l : ℕ, WL2 K (fun p : ℝ × ℝ => (p.1 : ℂ) ^ j * (p.2 : ℂ) ^ l) := fun j l => wl2_cont K hK (by fun_prop)
  unfold CellBox.pairOn CellBox.lineWeightFn
  have e : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * F p * (starRingEnd ℂ) (T p)
      = ∑ j : Fin (d + 1), ∑ l : Fin (d' + 1), (starRingEnd ℂ) (c j l) *
        ((K.lineWeight p.1 : ℂ) * F p * (starRingEnd ℂ) ((p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ))) := by
    intro p
    rw [hc p, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp only [map_mul]
    ring
  simp only [e]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_eq_zero (fun l _ => ?_)
      rw [integral_const_mul]
      have := h j l (by omega) (by omega)
      unfold CellBox.pairOn CellBox.lineWeightFn at this
      rw [this, mul_zero]
    · intro l _
      exact (wcross K hK hF (hm j l)).const_mul _
  · intro j _
    exact integrable_finset_sum _ (fun l _ => (wcross K hK hF (hm j l)).const_mul _)

theorem slice_eq (hK : IsCellBox K) {F : ℝ × ℝ → ℂ} (hF : WL2 K F) (φ : ℝ → ℂ)
    (hφ : AEStronglyMeasurable φ (volume.restrict (Set.Icc K.z₁ K.z₂)))
    (hφi : Integrable (fun z => ‖φ z‖ ^ 2) (volume.restrict (Set.Icc K.z₁ K.z₂))) (k : ℕ) :
    K.pairOn K.lineWeightFn F (fun p => φ p.2 * (p.1 : ℂ) ^ k)
      = ∫ z in Set.Icc K.z₁ K.z₂, (starRingEnd ℂ) (φ z) *
          ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * F (r, z) * (starRingEnd ℂ) ((r : ℂ) ^ k) := by
  have hG : WL2 K (fun p : ℝ × ℝ => φ p.2 * (p.1 : ℂ) ^ k) := wl2_of_sq K hK (term_sq K k φ hφ hφi)
  have e : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * F p * (starRingEnd ℂ) (φ p.2 * (p.1 : ℂ) ^ k)
      = (starRingEnd ℂ) (φ p.2) * ((K.lineWeight p.1 : ℂ) * F p * (starRingEnd ℂ) ((p.1 : ℂ) ^ k)) := by
    intro p
    rw [map_mul]
    ring
  have hI := (wcross K hK hF hG).congr (ae_of_all _ e)
  unfold CellBox.pairOn CellBox.lineWeightFn
  simp only [e]
  rw [rect_prod] at hI ⊢
  rw [integral_prod_symm _ hI]
  refine integral_congr_ae (ae_of_all _ (fun z => ?_))
  simp only
  rw [integral_const_mul]

theorem slice_zero (hK : IsCellBox K) {F : ℝ × ℝ → ℂ} (hF : WL2 K F) {n : ℕ} (φ : Fin n → ℝ → ℂ)
    (hφ : ∀ j, AEStronglyMeasurable (φ j) (volume.restrict (Set.Icc K.z₁ K.z₂)))
    (hφi : ∀ j, Integrable (fun z => ‖φ j z‖ ^ 2) (volume.restrict (Set.Icc K.z₁ K.z₂)))
    (hψ : ∀ j : Fin n, ∀ᵐ z ∂(volume.restrict (Set.Icc K.z₁ K.z₂)),
      ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * F (r, z) * (starRingEnd ℂ) ((r : ℂ) ^ (j : ℕ)) = 0) :
    K.pairOn K.lineWeightFn F (fun p => ∑ j, φ j p.2 * (p.1 : ℂ) ^ (j : ℕ)) = 0 := by
  have hG : ∀ j : Fin n, WL2 K (fun p : ℝ × ℝ => φ j p.2 * (p.1 : ℂ) ^ (j : ℕ)) :=
    fun j => wl2_of_sq K hK (term_sq K j (φ j) (hφ j) (hφi j))
  have e : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * F p * (starRingEnd ℂ) (∑ j, φ j p.2 * (p.1 : ℂ) ^ (j : ℕ))
      = ∑ j, (K.lineWeight p.1 : ℂ) * F p * (starRingEnd ℂ) (φ j p.2 * (p.1 : ℂ) ^ (j : ℕ)) := by
    intro p
    rw [map_sum, Finset.mul_sum]
  unfold CellBox.pairOn CellBox.lineWeightFn
  simp only [e]
  rw [integral_finsetSum _ (fun j _ => wcross K hK hF (hG j))]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have h1 := slice_eq K hK hF (φ j) (hφ j) (hφi j) j
  unfold CellBox.pairOn CellBox.lineWeightFn at h1
  rw [h1]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hψ j] with z hz
  rw [hz, mul_zero]
  rfl

end HeightProjBoundInternal


namespace HeightProjBoundInternal

variable (K : CellBox)

theorem pair_add_left (hK : IsCellBox K) {F₁ F₂ G : ℝ × ℝ → ℂ} (h₁ : WL2 K F₁) (h₂ : WL2 K F₂) (hG : WL2 K G) :
    K.pairOn K.lineWeightFn (fun p => F₁ p + F₂ p) G = K.pairOn K.lineWeightFn F₁ G + K.pairOn K.lineWeightFn F₂ G := by
  unfold CellBox.pairOn CellBox.lineWeightFn
  rw [← integral_add (wcross K hK h₁ hG) (wcross K hK h₂ hG)]
  refine integral_congr_ae (ae_of_all _ (fun p => ?_))
  ring

theorem slice_poly {d d' : ℕ} {T : ℝ × ℝ → ℂ} (hT : T ∈ polyFn d d') (j : ℕ) :
    ∃ β : Fin (d' + 1) → ℂ, ∀ z : ℝ, ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * T (r, z) * (starRingEnd ℂ) ((r : ℂ) ^ j)
      = ∑ l, β l * (z : ℂ) ^ (l : ℕ) := by
  obtain ⟨c, hc⟩ := hT
  refine ⟨fun l => ∑ k : Fin (d + 1), c k l *
    ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * (r : ℂ) ^ (k : ℕ) * (starRingEnd ℂ) ((r : ℂ) ^ j), fun z => ?_⟩
  have e : ∀ r : ℝ, (K.lineWeight r : ℂ) * T (r, z) * (starRingEnd ℂ) ((r : ℂ) ^ j)
      = ∑ l : Fin (d' + 1), ∑ k : Fin (d + 1), (c k l * (z : ℂ) ^ (l : ℕ)) *
        ((K.lineWeight r : ℂ) * (r : ℂ) ^ (k : ℕ) * (starRingEnd ℂ) ((r : ℂ) ^ j)) := by
    intro r
    rw [hc, Finset.sum_comm, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  simp only [e]
  have hint : ∀ k : ℕ, Integrable (fun r : ℝ => (K.lineWeight r : ℂ) * (r : ℂ) ^ k * (starRingEnd ℂ) ((r : ℂ) ^ j))
      (volume.restrict (Set.Icc K.r₁ K.r₂)) := fun k =>
    cont_int ((Complex.continuous_ofReal.comp (lw_cont K)).mul (by fun_prop) |>.mul (by fun_prop))
  have hI : ∀ l : Fin (d' + 1), Integrable (fun r : ℝ => ∑ k : Fin (d + 1), c k l * (z : ℂ) ^ (l : ℕ) *
      ((K.lineWeight r : ℂ) * (r : ℂ) ^ (k : ℕ) * (starRingEnd ℂ) ((r : ℂ) ^ j))) (volume.restrict (Set.Icc K.r₁ K.r₂)) :=
    fun l => integrable_finset_sum _ (fun k _ => (hint k).const_mul _)
  rw [integral_finsetSum _ (fun l _ => hI l)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine (integral_finsetSum _ (fun (k : Fin (d + 1)) _ => (hint (k : ℕ)).const_mul (c k l * (z : ℂ) ^ (l : ℕ)))).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [integral_const_mul]
  ring

end HeightProjBoundInternal

open HeightProjBoundInternal in
theorem radialTopBound_of (hC : ProjOrthStatement) : RadialTopBoundStatement := by
  intro K hK Q hQ s hs hsi
  have hsW : WL2 K s := ⟨hs, hsi⟩
  obtain ⟨c, hc, hcz⟩ := projRCoeff K hK (Q - 1) s hs hsi
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ × ℝ → ℂ, A = fun p => ∑ j : Fin (Q - 1 + 1), c j p.2 * (p.1 : ℂ) ^ (j : ℕ) := ⟨_, rfl⟩
  have hAW : WL2 K A := by
    rw [hAdef]
    exact wl2_sum K hK _ _ (fun j => wl2_of_sq K hK (term_sq K j (c j) (hc j).1 (hc j).2))
  obtain ⟨V, hVdef⟩ : ∃ V, V = K.proj (Q - 1) Q s := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P, P = K.proj (Q - 1) (Q - 2) s := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E, E = K.proj Q Q s := ⟨_, rfl⟩
  have hVm : V ∈ polyFn (Q - 1) Q := hVdef ▸ proj_mem' K _ _ s
  have hPm : P ∈ polyFn (Q - 1) (Q - 2) := hPdef ▸ proj_mem' K _ _ s
  have hEm : E ∈ polyFn Q Q := hEdef ▸ proj_mem' K _ _ s
  have hVW : WL2 K V := wl2_cont K hK (poly_cont hVm)
  have hPW : WL2 K P := wl2_cont K hK (poly_cont hPm)
  have hEW : WL2 K E := wl2_cont K hK (poly_cont hEm)
  have hCV : ∀ j l : ℕ, j ≤ Q - 1 → l ≤ Q → K.pairOn K.lineWeightFn (fun p => s p - V p)
      (fun p => (p.1 : ℂ) ^ j * (p.2 : ℂ) ^ l) = 0 := by
    rw [hVdef]; exact hC K hK (Q - 1) Q s hs hsi
  have hCP : ∀ j l : ℕ, j ≤ Q - 1 → l ≤ Q - 2 → K.pairOn K.lineWeightFn (fun p => s p - P p)
      (fun p => (p.1 : ℂ) ^ j * (p.2 : ℂ) ^ l) = 0 := by
    rw [hPdef]; exact hC K hK (Q - 1) (Q - 2) s hs hsi
  have hCE : ∀ j l : ℕ, j ≤ Q → l ≤ Q → K.pairOn K.lineWeightFn (fun p => s p - E p)
      (fun p => (p.1 : ℂ) ^ j * (p.2 : ℂ) ^ l) = 0 := by
    rw [hEdef]; exact hC K hK Q Q s hs hsi
  have hsV := wl2_sub K hK hsW hVW
  have hsP := wl2_sub K hK hsW hPW
  have hsE := wl2_sub K hK hsW hEW
  have hsA := wl2_sub K hK hsW hAW
  have hρc := lw_cont K
  have hρ0 : ∀ x ∈ Set.Icc K.r₁ K.r₂, 0 ≤ K.lineWeight x := fun x hx => lw_nonneg K hK hx.1
  have hρpos : ∀ x ∈ Set.Ioo K.r₁ K.r₂, 0 < K.lineWeight x := fun x hx => lw_pos K hK hx
  have hs' : AEStronglyMeasurable s ((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))) := by
    rw [← rect_prod]; exact hs
  have hsi' : Integrable (fun p => K.lineWeight p.1 * ‖s p‖ ^ 2)
      ((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))) := by
    rw [← rect_prod]; exact hsi
  have hperz : ∀ j : Fin (Q - 1 + 1), ∀ᵐ z ∂(volume.restrict (Set.Icc K.z₁ K.z₂)),
      ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * (s (r, z) - A (r, z)) * (starRingEnd ℂ) ((r : ℂ) ^ (j : ℕ)) = 0 := by
    intro j
    filter_upwards [hsi'.prod_left_ae, hs'.prodMk_right, hcz] with z hz hzm hzc
    have h := (lineProj_gen hK.r_order.2 hρc hρ0 hρpos (Q - 1) (fun r => s (r, z)) hzm hz).1 j
    have e : ∀ r, lineProj (fun r => K.lineWeight r) K.r₁ K.r₂ (Q - 1) (fun r => s (r, z)) r = A (r, z) := by
      intro r
      rw [hAdef]
      exact hzc r
    simp only [e] at h
    exact h
  have hslices : ∀ φ : Fin (Q - 1 + 1) → ℝ → ℂ, (∀ j, AEStronglyMeasurable (φ j) (volume.restrict (Set.Icc K.z₁ K.z₂))) →
      (∀ j, Integrable (fun z => ‖φ j z‖ ^ 2) (volume.restrict (Set.Icc K.z₁ K.z₂))) →
      K.pairOn K.lineWeightFn (fun p => s p - A p) (fun p => ∑ j, φ j p.2 * (p.1 : ℂ) ^ (j : ℕ)) = 0 :=
    fun φ hφ hφi => slice_zero K hK hsA φ hφ hφi hperz
  obtain ⟨cv, hcv⟩ := hVm
  obtain ⟨cp, hcp⟩ := hPm
  let φV : Fin (Q - 1 + 1) → ℝ → ℂ := fun j z => ∑ l : Fin (Q + 1), cv j l * (z : ℂ) ^ (l : ℕ)
  let φP : Fin (Q - 1 + 1) → ℝ → ℂ := fun j z => ∑ l : Fin (Q - 2 + 1), cp j l * (z : ℂ) ^ (l : ℕ)
  have hφV : ∀ j, Continuous (φV j) := fun j => by fun_prop
  have hφP : ∀ j, Continuous (φP j) := fun j => by fun_prop
  have hVs : V = fun p => ∑ j, φV j p.2 * (p.1 : ℂ) ^ (j : ℕ) := by
    funext p
    rw [hcv p]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [φV, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  have hPs : P = fun p => ∑ j, φP j p.2 * (p.1 : ℂ) ^ (j : ℕ) := by
    funext p
    rw [hcp p]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [φP, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  have hcm : ∀ (f : ℝ → ℂ), Continuous f → AEStronglyMeasurable f (volume.restrict (Set.Icc K.z₁ K.z₂)) ∧
      Integrable (fun z => ‖f z‖ ^ 2) (volume.restrict (Set.Icc K.z₁ K.z₂)) :=
    fun f hf => ⟨hf.aestronglyMeasurable, cont_int (hf.norm.pow 2)⟩
  have hAV0 : K.pairOn K.lineWeightFn (fun p => s p - A p) V = 0 := by
    rw [hVs]
    exact hslices φV (fun j => (hcm _ (hφV j)).1) (fun j => (hcm _ (hφV j)).2)
  have hAP0 : K.pairOn K.lineWeightFn (fun p => s p - A p) P = 0 := by
    rw [hPs]
    exact hslices φP (fun j => (hcm _ (hφP j)).1) (fun j => (hcm _ (hφP j)).2)
  have hX : (fun p => A p - V p) = fun p => ∑ j, (c j p.2 - φV j p.2) * (p.1 : ℂ) ^ (j : ℕ) := by
    funext p
    rw [hAdef, hVs]
    simp only [← Finset.sum_sub_distrib, sub_mul]
  have hAX0 : K.pairOn K.lineWeightFn (fun p => s p - A p) (fun p => A p - V p) = 0 := by
    rw [hX]
    exact hslices (fun j z => c j z - φV j z) (fun j => (hc j).1.sub (hcm _ (hφV j)).1)
      (fun j => sq_sub (hc j).1 (hcm _ (hφV j)).1 (hc j).2 (hcm _ (hφV j)).2)
  have hEV : WL2 K (fun p => E p - V p) := wl2_sub K hK hEW hVW
  have hψ : ∀ j : Fin (Q - 1 + 1), ∀ᵐ z ∂(volume.restrict (Set.Icc K.z₁ K.z₂)),
      ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * (E (r, z) - V (r, z)) * (starRingEnd ℂ) ((r : ℂ) ^ (j : ℕ)) = 0 := by
    intro j
    obtain ⟨βE, hβE⟩ := slice_poly K hEm (j : ℕ)
    obtain ⟨βV, hβV⟩ := slice_poly K (show V ∈ polyFn (Q - 1) Q from ⟨cv, hcv⟩) (j : ℕ)
    have hint : ∀ (T : ℝ × ℝ → ℂ), Continuous T → ∀ z : ℝ,
        Integrable (fun r : ℝ => (K.lineWeight r : ℂ) * T (r, z) * (starRingEnd ℂ) ((r : ℂ) ^ (j : ℕ)))
          (volume.restrict (Set.Icc K.r₁ K.r₂)) := fun T hT z =>
      cont_int ((Complex.continuous_ofReal.comp hρc).mul (hT.comp (by fun_prop : Continuous (fun r : ℝ => (r, z))))
        |>.mul (by fun_prop))
    obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℝ → ℂ, ψ = fun z : ℝ => ∑ l : Fin (Q + 1), (βE l - βV l) * (z : ℂ) ^ (l : ℕ) := ⟨_, rfl⟩
    have hψeq : ∀ z, ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * (E (r, z) - V (r, z))
        * (starRingEnd ℂ) ((r : ℂ) ^ (j : ℕ)) = ψ z := by
      intro z
      have e : ∀ r : ℝ, (K.lineWeight r : ℂ) * (E (r, z) - V (r, z)) * (starRingEnd ℂ) ((r : ℂ) ^ (j : ℕ))
          = (K.lineWeight r : ℂ) * E (r, z) * (starRingEnd ℂ) ((r : ℂ) ^ (j : ℕ))
            - (K.lineWeight r : ℂ) * V (r, z) * (starRingEnd ℂ) ((r : ℂ) ^ (j : ℕ)) := fun r => by ring
      simp only [e]
      rw [integral_sub (hint E (poly_cont hEm) z) (hint V (poly_cont ⟨cv, hcv⟩) z), hβE, hβV, hψdef,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    have hψc : Continuous ψ := by rw [hψdef]; fun_prop
    have horth : ∀ l : Fin (Q + 1), ∫ z in Set.Icc K.z₁ K.z₂, (starRingEnd ℂ) ((z : ℂ) ^ (l : ℕ)) * ψ z = 0 := by
      intro l
      have h1 := slice_eq K hK hEV (fun z => (z : ℂ) ^ (l : ℕ)) (hcm _ (by fun_prop)).1 (hcm _ (by fun_prop)).2 (j : ℕ)
      simp only [hψeq] at h1
      rw [← h1]
      have e1 : (fun p : ℝ × ℝ => E p - V p) = fun p => (s p - V p) - (s p - E p) := by
        funext p; ring
      have e2 : (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (l : ℕ) * (p.1 : ℂ) ^ (j : ℕ))
          = fun p => (p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ) := by
        funext p; ring
      have hmono : WL2 K (fun p : ℝ × ℝ => (p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ)) := wl2_cont K hK (by fun_prop)
      rw [e1, e2, pair_sub_left K hK hsV hsE hmono, hCV j l (by omega) (by omega), hCE j l (by omega) (by omega),
        sub_self]
    have hsq : ∫ z in Set.Icc K.z₁ K.z₂, ‖ψ z‖ ^ 2 = 0 := by
      have h2 : ∫ z in Set.Icc K.z₁ K.z₂, (starRingEnd ℂ) (ψ z) * ψ z = 0 := by
        have e : ∀ z : ℝ, (starRingEnd ℂ) (ψ z) * ψ z
            = ∑ l : Fin (Q + 1), (starRingEnd ℂ) (βE l - βV l) * ((starRingEnd ℂ) ((z : ℂ) ^ (l : ℕ)) * ψ z) := by
          intro z
          have hz : (starRingEnd ℂ) (ψ z) = ∑ l : Fin (Q + 1), (starRingEnd ℂ) (βE l - βV l) * (starRingEnd ℂ) ((z : ℂ) ^ (l : ℕ)) := by
            rw [hψdef]
            simp only [map_sum, map_mul]
          rw [hz, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun l _ => by ring)
        simp only [e]
        rw [integral_finsetSum _ (fun l _ => (cont_int (by fun_prop)).const_mul _)]
        refine Finset.sum_eq_zero (fun l _ => ?_)
        rw [integral_const_mul, horth l, mul_zero]
      have h3 := integral_complex_ofReal (μ := volume.restrict (Set.Icc K.z₁ K.z₂)) (f := fun z => ‖ψ z‖ ^ 2)
      have e : ∀ z, (((‖ψ z‖ ^ 2 : ℝ)) : ℂ) = (starRingEnd ℂ) (ψ z) * ψ z := by
        intro z
        rw [mul_comm, Complex.mul_conj, Complex.sq_norm]
      simp only [e, h2] at h3
      exact_mod_cast h3.symm
    have h4 : (fun z => ‖ψ z‖ ^ 2) =ᵐ[volume.restrict (Set.Icc K.z₁ K.z₂)] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg _) (cont_int (hψc.norm.pow 2))).1 hsq
    filter_upwards [h4] with z hz
    rw [hψeq]
    simpa using hz
  have hEVX : K.pairOn K.lineWeightFn (fun p => E p - V p) (fun p => A p - V p) = 0 := by
    rw [hX]
    exact slice_zero K hK hEV (fun j z => c j z - φV j z) (fun j => (hc j).1.sub (hcm _ (hφV j)).1)
      (fun j => sq_sub (hc j).1 (hcm _ (hφV j)).1 (hc j).2 (hcm _ (hφV j)).2) hψ
  have hXW : WL2 K (fun p => A p - V p) := wl2_sub K hK hAW hVW
  have hVPW : WL2 K (fun p => V p - P p) := wl2_sub K hK hVW hPW
  have hVV : K.pairOn K.lineWeightFn (fun p => s p - V p) V = 0 :=
    orth_poly K hK hsV ⟨cv, hcv⟩ le_rfl le_rfl hCV
  have hVP : K.pairOn K.lineWeightFn (fun p => s p - V p) P = 0 :=
    orth_poly K hK hsV ⟨cp, hcp⟩ le_rfl (by omega) hCV
  have hPP : K.pairOn K.lineWeightFn (fun p => s p - P p) P = 0 :=
    orth_poly K hK hsP ⟨cp, hcp⟩ le_rfl le_rfl hCP
  have h1 : K.pairOn K.lineWeightFn (fun p => A p - V p) (fun p => V p - P p) = 0 := by
    have e : (fun p => A p - V p) = fun p => (s p - V p) - (s p - A p) := by funext p; ring
    rw [e, pair_sub_left K hK hsV hsA hVPW, pair_sub_right K hK hsV hVW hPW, pair_sub_right K hK hsA hVW hPW,
      hVV, hVP, hAV0, hAP0]
    simp
  have h2 : K.pairOn K.lineWeightFn (fun p => V p - P p) P = 0 := by
    have e : (fun p => V p - P p) = fun p => (s p - P p) - (s p - V p) := by funext p; ring
    rw [e, pair_sub_left K hK hsP hsV hPW, hPP, hVP]
    simp
  have hNV : K.normSqOn K.lineWeightFn V = K.normSqOn K.lineWeightFn (fun p => V p - P p) + K.normSqOn K.lineWeightFn P := by
    have h := normSq_add' K hK hVPW hPW
    rw [h2] at h
    have e : (fun p => V p - P p + P p) = V := by funext p; ring
    rw [e] at h
    rw [h]
    simp
  have hNAP : K.normSqOn K.lineWeightFn (fun p => A p - P p)
      = K.normSqOn K.lineWeightFn (fun p => A p - V p) + K.normSqOn K.lineWeightFn (fun p => V p - P p) := by
    have h := normSq_add' K hK hXW hVPW
    rw [h1] at h
    have e : (fun p => A p - V p + (V p - P p)) = fun p => A p - P p := by funext p; ring
    rw [e] at h
    rw [h]
    simp
  have hXX : K.pairOn K.lineWeightFn (fun p => A p - V p) (fun p => A p - V p)
      = K.pairOn K.lineWeightFn (fun p => s p - E p) (fun p => A p - V p) := by
    have e : (fun p => A p - V p) = fun p => ((s p - E p) + (E p - V p)) - (s p - A p) := by funext p; ring
    rw [show K.pairOn K.lineWeightFn (fun p => A p - V p) (fun p => A p - V p)
      = K.pairOn K.lineWeightFn (fun p => ((s p - E p) + (E p - V p)) - (s p - A p)) (fun p => A p - V p) by rw [← e]]
    rw [pair_sub_left K hK (wl2_add K hK hsE hEV) hsA hXW, pair_add_left K hK hsE hEV hXW, hEVX, hAX0]
    simp
  have hNX : K.normSqOn K.lineWeightFn (fun p => A p - V p) ≤ K.normSqOn K.lineWeightFn (fun p => s p - E p) := by
    have hcs := weightedInner_le (w_nonneg K hK) (w_meas K) hsE.1 hXW.1 hsE.2 hXW.2
    have e1 : ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * (s p - E p) * (starRingEnd ℂ) (A p - V p)
        = K.pairOn K.lineWeightFn (fun p => s p - E p) (fun p => A p - V p) := rfl
    rw [e1, ← hXX, pair_self] at hcs
    have hN0 : 0 ≤ K.normSqOn K.lineWeightFn (fun p => A p - V p) :=
      integral_nonneg_of_ae ((w_nonneg K hK).mono (fun p hp => mul_nonneg hp (sq_nonneg _)))
    have hE0 : 0 ≤ K.normSqOn K.lineWeightFn (fun p => s p - E p) :=
      integral_nonneg_of_ae ((w_nonneg K hK).mono (fun p hp => mul_nonneg hp (sq_nonneg _)))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN0] at hcs
    change K.normSqOn K.lineWeightFn (fun p => A p - V p) ^ 2
      ≤ K.normSqOn K.lineWeightFn (fun p => s p - E p) * K.normSqOn K.lineWeightFn (fun p => A p - V p) at hcs
    nlinarith
  have hae : ∀ᵐ p ∂(volume.restrict K.rect), K.projR (Q - 1) s p = A p := by
    rw [rect_prod]
    have h := (Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Set.Icc K.r₁ K.r₂))
      (ν := volume.restrict (Set.Icc K.z₁ K.z₂))).ae hcz
    filter_upwards [h] with p hp
    rw [hAdef]
    simpa using hp p.1
  have hN : K.normSqOn K.lineWeightFn (fun p => K.projR (Q - 1) s p - K.proj (Q - 1) (Q - 2) s p)
      = K.normSqOn K.lineWeightFn (fun p => A p - P p) := by
    unfold CellBox.normSqOn
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    rw [hp, hPdef]
  rw [hN, ← hVdef, ← hPdef]
  unfold CellBox.tailNormSq
  rw [← hEdef]
  linarith [hNAP, hNV, hNX]


namespace HeightProjBoundInternal

theorem poly_vanish {a b : ℝ} (hab : a < b) {n : ℕ} (e : Fin (n + 1) → ℂ)
    (h : ∀ x ∈ Set.Ioo a b, ∑ j, e j * (x : ℂ) ^ (j : ℕ) = 0) : e = 0 := by
  let P : Polynomial ℂ := ∑ j : Fin (n + 1), Polynomial.C (e j) * Polynomial.X ^ (j : ℕ)
  have hP : ∀ x : ℝ, P.eval (x : ℂ) = ∑ j, e j * (x : ℂ) ^ (j : ℕ) := by
    intro x
    simp [P, Polynomial.eval_finset_sum]
  have hP0 : P = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot P ?_
    refine Set.Infinite.mono ?_ ((Set.Ioo_infinite hab).image Complex.ofReal_injective.injOn)
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, hP]
    exact h x hx
  funext j
  have := congrArg (fun P : Polynomial ℂ => P.coeff (j : ℕ)) hP0
  simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single j] at this
  · simpa using this
  · intro i _ hij
    rw [if_neg]
    intro h'
    exact hij (Fin.ext h'.symm)
  · simp

theorem mono_mem {d d' j l : ℕ} (hj : j ≤ d) (hl : l ≤ d') :
    (fun p : ℝ × ℝ => (p.1 : ℂ) ^ j * (p.2 : ℂ) ^ l) ∈ polyFn d d' := by
  refine ⟨fun a b => if (a : ℕ) = j ∧ (b : ℕ) = l then 1 else 0, fun p => ?_⟩
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (⟨j, by omega⟩ : Fin (d + 1))]
  · rw [Finset.sum_eq_single (⟨l, by omega⟩ : Fin (d' + 1))]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext h.2)
    · simp
  · intro a _ ha
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rw [if_neg]
    intro h
    exact ha (Fin.ext h.1)
  · simp

end HeightProjBoundInternal

open HeightProjBoundInternal in
theorem projOrth : ProjOrthStatement := by
  intro K hK d d' s hs hsi
  have hsW : WL2 K s := ⟨hs, hsi⟩
  let mono : Fin (d + 1) × Fin (d' + 1) → ℝ × ℝ → ℂ := fun i p => (p.1 : ℂ) ^ (i.1 : ℕ) * (p.2 : ℂ) ^ (i.2 : ℕ)
  have hmc : ∀ i, Continuous (mono i) := fun i => by fun_prop
  have hmW : ∀ i, WL2 K (mono i) := fun i => wl2_cont K hK (hmc i)
  let M : Matrix (Fin (d + 1) × Fin (d' + 1)) (Fin (d + 1) × Fin (d' + 1)) ℂ :=
    fun t i => K.pairOn K.lineWeightFn (mono i) (mono t)
  let pc : ((Fin (d + 1) × Fin (d' + 1)) → ℂ) → ℝ × ℝ → ℂ := fun c p => ∑ i, c i * mono i p
  have hpcc : ∀ c, Continuous (pc c) := fun c => by
    simp only [pc]
    fun_prop
  have hpcW : ∀ c, WL2 K (pc c) := fun c => wl2_cont K hK (hpcc c)
  have hlin : ∀ c t, K.pairOn K.lineWeightFn (pc c) (mono t) = M.mulVec c t := by
    intro c t
    simp only [Matrix.mulVec, dotProduct, M]
    unfold CellBox.pairOn CellBox.lineWeightFn
    have e : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * pc c p * (starRingEnd ℂ) (mono t p)
        = ∑ i, c i * ((K.lineWeight p.1 : ℂ) * mono i p * (starRingEnd ℂ) (mono t p)) := by
      intro p
      simp only [pc, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    simp only [e]
    rw [integral_finsetSum _ (fun i _ => (wcross K hK (hmW i) (hmW t)).const_mul _)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_const_mul, mul_comm]
  have hinj : Function.Injective M.mulVec := by
    intro x y hxy
    rw [← sub_eq_zero]
    set c := x - y with hcdef
    have hMc : M.mulVec c = 0 := by rw [hcdef, Matrix.mulVec_sub, hxy, sub_self]
    have hself : K.pairOn K.lineWeightFn (pc c) (pc c) = 0 := by
      unfold CellBox.pairOn CellBox.lineWeightFn
      have e : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * pc c p * (starRingEnd ℂ) (pc c p)
          = ∑ t, (starRingEnd ℂ) (c t) * ((K.lineWeight p.1 : ℂ) * pc c p * (starRingEnd ℂ) (mono t p)) := by
        intro p
        conv_lhs => rw [show (starRingEnd ℂ) (pc c p) = ∑ t, (starRingEnd ℂ) (c t) * (starRingEnd ℂ) (mono t p) by
          simp only [pc, map_sum, map_mul]]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun t _ => by ring)
      simp only [e]
      rw [integral_finsetSum _ (fun t _ => (wcross K hK (hpcW c) (hmW t)).const_mul _)]
      refine Finset.sum_eq_zero (fun t _ => ?_)
      rw [integral_const_mul]
      have h1 := hlin c t
      unfold CellBox.pairOn CellBox.lineWeightFn at h1
      rw [h1, hMc]
      simp
    rw [pair_self] at hself
    have hN : ∫ p in K.rect, K.lineWeight p.1 * ‖pc c p‖ ^ 2 = 0 := by exact_mod_cast hself
    have hcont : Continuous (fun p : ℝ × ℝ => K.lineWeight p.1 * ‖pc c p‖ ^ 2) :=
      ((lw_cont K).comp continuous_fst).mul ((hpcc c).norm.pow 2)
    have h3 : (fun p : ℝ × ℝ => K.lineWeight p.1 * ‖pc c p‖ ^ 2) =ᵐ[volume.restrict K.rect] 0 := by
      refine (integral_eq_zero_iff_of_nonneg_ae ?_ (hpcW c).2).1 hN
      filter_upwards [w_nonneg K hK] with p hp
      exact mul_nonneg hp (sq_nonneg _)
    have h4 := ae_restrict_of_ae_restrict_of_subset
      (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self : Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂ ⊆ K.rect) h3
    have h5 := Measure.eqOn_open_of_ae_eq h4 (isOpen_Ioo.prod isOpen_Ioo) hcont.continuousOn continuousOn_const
    have h6 : ∀ r ∈ Set.Ioo K.r₁ K.r₂, ∀ z ∈ Set.Ioo K.z₁ K.z₂, pc c (r, z) = 0 := by
      intro r hr z hz
      have := h5 (Set.mk_mem_prod hr hz)
      simp only [Pi.zero_apply, mul_eq_zero, (lw_pos K hK hr).ne', false_or, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] at this
      exact this
    have h7 : ∀ z ∈ Set.Ioo K.z₁ K.z₂, ∀ j : Fin (d + 1), ∑ l : Fin (d' + 1), c (j, l) * (z : ℂ) ^ (l : ℕ) = 0 := by
      intro z hz
      have := poly_vanish hK.r_order.2 (fun j : Fin (d + 1) => ∑ l : Fin (d' + 1), c (j, l) * (z : ℂ) ^ (l : ℕ))
        (fun r hr => by
          rw [← h6 r hr z hz]
          simp only [pc, mono, Fintype.sum_prod_type, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => by ring)))
      intro j
      exact congrFun this j
    funext ⟨j, l⟩
    have := poly_vanish hK.z_order.2 (fun l : Fin (d' + 1) => c (j, l)) (fun z hz => h7 z hz j)
    exact congrFun this l
  let m : Fin (d + 1) × Fin (d' + 1) → ℂ := fun t => K.pairOn K.lineWeightFn s (mono t)
  obtain ⟨c0, hc0⟩ := (LinearMap.injective_iff_surjective.1 (show Function.Injective M.mulVecLin from hinj)) m
  have hc0' : M.mulVec c0 = m := hc0
  have horth : ∀ t, K.pairOn K.lineWeightFn (fun p => s p - pc c0 p) (mono t) = 0 := by
    intro t
    rw [pair_sub_left K hK hsW (hpcW c0) (hmW t), hlin, hc0', sub_self]
  have hpcmem : pc c0 ∈ polyFn d d' := by
    refine ⟨fun j l => c0 (j, l), fun p => ?_⟩
    simp only [pc, mono, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => by ring))
  have hex : ∃ P ∈ polyFn d d', ∀ T ∈ polyFn d d', K.pairOn K.lineWeightFn (fun p => s p - P p) T = 0 := by
    refine ⟨pc c0, hpcmem, fun T hT => ?_⟩
    refine orth_poly K hK (wl2_sub K hK hsW (hpcW c0)) hT le_rfl le_rfl (fun j l hj hl => ?_)
    exact horth (⟨j, by omega⟩, ⟨l, by omega⟩)
  intro j l hj hl
  have hP : K.proj d d' s = hex.choose := by
    unfold CellBox.proj
    rw [dif_pos hex]
  rw [hP]
  exact hex.choose_spec.2 _ (mono_mem hj hl)

open HeightProjBoundInternal in
theorem heightProjBound : HeightProjBoundStatement :=
  heightProjBound_of lineProjSpec projRCoeff (radialTopBound_of projOrth)

end CellAnalysis

end CellCert

end Breakdown
