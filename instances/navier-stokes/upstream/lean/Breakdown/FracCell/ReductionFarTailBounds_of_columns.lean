import Breakdown.FracCell.ReductionFarDefs

open MeasureTheory ComplexConjugate

noncomputable section

namespace Breakdown.CellCert.Reduction.TailColumnInternal

def Good {E : Type*} [NormedAddCommGroup E] (a b : ℝ) (f : ℝ → E) : Prop :=
  AEStronglyMeasurable f (volume.restrict (Set.Icc a b)) ∧ ∃ C : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ C

variable {a b : ℝ}

lemma good_integrable {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} (hf : Good a b f) :
    Integrable f (volume.restrict (Set.Icc a b)) := by
  obtain ⟨hm, C, hC⟩ := hf
  exact Integrable.of_bound hm C (ae_restrict_of_forall_mem measurableSet_Icc hC)

lemma good_mul {E : Type*} [NormedRing E] {f g : ℝ → E} (hf : Good a b f) (hg : Good a b g) :
    Good a b (fun x => f x * g x) := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, C', hC'⟩ := hg
  refine ⟨hfm.mul hgm, C * C', fun x hx => ?_⟩
  calc ‖f x * g x‖ ≤ ‖f x‖ * ‖g x‖ := norm_mul_le _ _
    _ ≤ C * C' := mul_le_mul (hC x hx) (hC' x hx) (norm_nonneg _) ((norm_nonneg _).trans (hC x hx))

lemma good_add {E : Type*} [NormedAddCommGroup E] {f g : ℝ → E} (hf : Good a b f) (hg : Good a b g) :
    Good a b (fun x => f x + g x) := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, C', hC'⟩ := hg
  exact ⟨hfm.add hgm, C + C', fun x hx => (norm_add_le _ _).trans (add_le_add (hC x hx) (hC' x hx))⟩

lemma good_sub {E : Type*} [NormedAddCommGroup E] {f g : ℝ → E} (hf : Good a b f) (hg : Good a b g) :
    Good a b (fun x => f x - g x) := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, C', hC'⟩ := hg
  exact ⟨hfm.sub hgm, C + C', fun x hx => (norm_sub_le _ _).trans (add_le_add (hC x hx) (hC' x hx))⟩

lemma good_const {E : Type*} [NormedAddCommGroup E] (c : E) : Good a b (fun _ => c) :=
  ⟨aestronglyMeasurable_const, ‖c‖, fun _ _ => le_rfl⟩

lemma good_sum {E : Type*} [NormedAddCommGroup E] {ι : Type*} (s : Finset ι) {f : ι → ℝ → E}
    (hf : ∀ i, Good a b (f i)) : Good a b (fun x => ∑ i ∈ s, f i x) := by
  unfold Good at hf
  choose hm C hC using hf
  exact ⟨Finset.aestronglyMeasurable_fun_sum s (fun i _ => hm i), ∑ i ∈ s, C i,
    fun x hx => (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hC i x hx)⟩

lemma good_ofReal {f : ℝ → ℝ} (hf : Good a b f) : Good a b (fun x => ((f x : ℝ) : ℂ)) := by
  obtain ⟨hm, C, hC⟩ := hf
  exact ⟨Complex.continuous_ofReal.comp_aestronglyMeasurable hm, C,
    fun x hx => by rw [Complex.norm_real]; exact hC x hx⟩

lemma good_conj {f : ℝ → ℂ} (hf : Good a b f) : Good a b (fun x => conj (f x)) := by
  obtain ⟨hm, C, hC⟩ := hf
  exact ⟨Complex.continuous_conj.comp_aestronglyMeasurable hm, C,
    fun x hx => by rw [Complex.norm_conj]; exact hC x hx⟩

lemma good_normSq {f : ℝ → ℂ} (hf : Good a b f) : Good a b (fun x => ‖f x‖ ^ 2) := by
  obtain ⟨hm, C, hC⟩ := hf
  refine ⟨hm.norm.pow 2, C ^ 2, fun x hx => ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC x hx) 2

lemma good_cont {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} (hf : Continuous f) : Good a b f :=
  ⟨hf.aestronglyMeasurable, isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn⟩

def pr (ρ : ℝ → ℝ) (a b : ℝ) (f g : ℝ → ℂ) : ℂ :=
  ∫ x in Set.Icc a b, (ρ x : ℂ) * (conj (f x) * g x)

def coefA (ρ : ℝ → ℝ) (a b : ℝ) (P : ℕ → ℝ → ℝ) (g : ℝ → ℂ) (j : ℕ) : ℂ :=
  ∫ x in Set.Icc a b, (ρ x : ℂ) * g x * (P j x : ℂ)

def tailW (ρ : ℝ → ℝ) (a b : ℝ) (D : ℕ) (P : ℕ → ℝ → ℝ) (g : ℝ → ℂ) : ℝ :=
  (∫ x in Set.Icc a b, ρ x * ‖g x‖ ^ 2) - ∑ j ∈ Finset.range (D + 1), ‖coefA ρ a b P g j‖ ^ 2

variable {ρ : ℝ → ℝ}

lemma pr_int (hρ : Good a b ρ) {f g : ℝ → ℂ} (hf : Good a b f) (hg : Good a b g) :
    Integrable (fun x => (ρ x : ℂ) * (conj (f x) * g x)) (volume.restrict (Set.Icc a b)) :=
  good_integrable (good_mul (good_ofReal hρ) (good_mul (good_conj hf) hg))

lemma pr_sub_left (hρ : Good a b ρ) {f₁ f₂ g : ℝ → ℂ} (h₁ : Good a b f₁) (h₂ : Good a b f₂)
    (hg : Good a b g) : pr ρ a b (fun x => f₁ x - f₂ x) g = pr ρ a b f₁ g - pr ρ a b f₂ g := by
  unfold pr
  rw [← integral_sub (pr_int hρ h₁ hg) (pr_int hρ h₂ hg)]
  congr 1
  funext x
  rw [map_sub]
  ring

lemma pr_sub_right (hρ : Good a b ρ) {f g₁ g₂ : ℝ → ℂ} (hf : Good a b f) (h₁ : Good a b g₁)
    (h₂ : Good a b g₂) : pr ρ a b f (fun x => g₁ x - g₂ x) = pr ρ a b f g₁ - pr ρ a b f g₂ := by
  unfold pr
  rw [← integral_sub (pr_int hρ hf h₁) (pr_int hρ hf h₂)]
  congr 1
  funext x
  ring

lemma pr_sum_right (hρ : Good a b ρ) {ι : Type*} (s : Finset ι) (c : ι → ℂ) (H : ι → ℝ → ℂ)
    (hH : ∀ i, Good a b (H i)) {f : ℝ → ℂ} (hf : Good a b f) :
    pr ρ a b f (fun x => ∑ i ∈ s, c i * H i x) = ∑ i ∈ s, c i * pr ρ a b f (H i) := by
  unfold pr
  have e : (fun x => (ρ x : ℂ) * (conj (f x) * ∑ i ∈ s, c i * H i x))
      = fun x => ∑ i ∈ s, c i * ((ρ x : ℂ) * (conj (f x) * H i x)) := by
    funext x
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, integral_finsetSum s (fun i _ => (pr_int hρ hf (hH i)).const_mul (c i))]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

lemma pr_swap (f g : ℝ → ℂ) : pr ρ a b g f = conj (pr ρ a b f g) := by
  unfold pr
  rw [← integral_conj]
  congr 1
  funext x
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

lemma pr_sum_left (hρ : Good a b ρ) {ι : Type*} (s : Finset ι) (c : ι → ℂ) (H : ι → ℝ → ℂ)
    (hH : ∀ i, Good a b (H i)) {g : ℝ → ℂ} (hg : Good a b g) :
    pr ρ a b (fun x => ∑ i ∈ s, c i * H i x) g = ∑ i ∈ s, conj (c i) * pr ρ a b (H i) g := by
  rw [pr_swap, pr_sum_right hρ s c H hH hg, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← pr_swap]

lemma pr_self (f : ℝ → ℂ) :
    pr ρ a b f f = ((∫ x in Set.Icc a b, ρ x * ‖f x‖ ^ 2 : ℝ) : ℂ) := by
  unfold pr
  rw [← integral_complex_ofReal]
  congr 1
  funext x
  rw [Complex.conj_mul']
  push_cast
  ring

lemma pr_poly_left (P : ℕ → ℝ → ℝ) (j : ℕ) (g : ℝ → ℂ) :
    pr ρ a b (fun x => ((P j x : ℝ) : ℂ)) g = coefA ρ a b P g j := by
  unfold pr coefA
  congr 1
  funext x
  rw [Complex.conj_ofReal]
  ring

lemma pr_poly_poly (P : ℕ → ℝ → ℝ)
    (horth : ∀ j j', ∫ x in Set.Icc a b, ρ x * P j x * P j' x = if j = j' then 1 else 0) (j j' : ℕ) :
    pr ρ a b (fun x => ((P j x : ℝ) : ℂ)) (fun x => ((P j' x : ℝ) : ℂ)) = if j = j' then 1 else 0 := by
  unfold pr
  have e : (fun x => (ρ x : ℂ) * (conj ((P j x : ℝ) : ℂ) * ((P j' x : ℝ) : ℂ)))
      = fun x => ((ρ x * P j x * P j' x : ℝ) : ℂ) := by
    funext x
    rw [Complex.conj_ofReal]
    push_cast
    ring
  rw [e, integral_complex_ofReal, horth]
  split_ifs <;> simp

lemma resid (hρ : Good a b ρ) {P : ℕ → ℝ → ℝ} (hP : ∀ j, Good a b (P j))
    (horth : ∀ j j', ∫ x in Set.Icc a b, ρ x * P j x * P j' x = if j = j' then 1 else 0)
    {g : ℝ → ℂ} (hg : Good a b g) (D : ℕ) :
    (∫ x in Set.Icc a b, ρ x * ‖g x - ∑ j ∈ Finset.range (D + 1), coefA ρ a b P g j * (P j x : ℂ)‖ ^ 2)
      = tailW ρ a b D P g := by
  have hPc : ∀ j, Good a b (fun x => ((P j x : ℝ) : ℂ)) := fun j => good_ofReal (hP j)
  have hs : Good a b (fun x => ∑ j ∈ Finset.range (D + 1), coefA ρ a b P g j * (P j x : ℂ)) :=
    good_sum _ fun j => good_mul (good_const _) (hPc j)
  have h1 := pr_self (ρ := ρ) (a := a) (b := b)
    (fun x => g x - ∑ j ∈ Finset.range (D + 1), coefA ρ a b P g j * (P j x : ℂ))
  beta_reduce at h1
  apply Complex.ofReal_injective
  rw [← h1, pr_sub_left hρ hg hs (good_sub hg hs), pr_sub_right hρ hg hg hs, pr_sub_right hρ hs hg hs]
  have e_gs : pr ρ a b g (fun x => ∑ j ∈ Finset.range (D + 1), coefA ρ a b P g j * (P j x : ℂ))
      = ∑ j ∈ Finset.range (D + 1), coefA ρ a b P g j * conj (coefA ρ a b P g j) := by
    rw [pr_sum_right hρ (Finset.range (D + 1)) (coefA ρ a b P g) (fun j x => ((P j x : ℝ) : ℂ)) hPc hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pr_swap, pr_poly_left]
  have e_sg : pr ρ a b (fun x => ∑ j ∈ Finset.range (D + 1), coefA ρ a b P g j * (P j x : ℂ)) g
      = ∑ j ∈ Finset.range (D + 1), conj (coefA ρ a b P g j) * coefA ρ a b P g j := by
    rw [pr_sum_left hρ (Finset.range (D + 1)) (coefA ρ a b P g) (fun j x => ((P j x : ℝ) : ℂ)) hPc hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pr_poly_left]
  have e_ss : pr ρ a b (fun x => ∑ j ∈ Finset.range (D + 1), coefA ρ a b P g j * (P j x : ℂ))
      (fun x => ∑ j ∈ Finset.range (D + 1), coefA ρ a b P g j * (P j x : ℂ))
      = ∑ j ∈ Finset.range (D + 1), conj (coefA ρ a b P g j) * coefA ρ a b P g j := by
    rw [pr_sum_left hρ (Finset.range (D + 1)) (coefA ρ a b P g) (fun j x => ((P j x : ℝ) : ℂ)) hPc hs]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [pr_sum_right hρ (Finset.range (D + 1)) (coefA ρ a b P g) (fun j x => ((P j x : ℝ) : ℂ)) hPc (hPc j)]
    simp only [pr_poly_poly P horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, if_pos hj]
  rw [e_gs, e_sg, e_ss, pr_self, tailW]
  simp only [Complex.mul_conj', Complex.conj_mul']
  push_cast
  ring

lemma col (hρ : Good a b ρ) (hρ0 : ∀ x ∈ Set.Icc a b, 0 ≤ ρ x) {P : ℕ → ℝ → ℝ} (hP : ∀ j, Good a b (P j))
    (horth : ∀ j j', ∫ x in Set.Icc a b, ρ x * P j x * P j' x = if j = j' then 1 else 0)
    {ι : Type*} [Fintype ι] (h : ι → ℝ → ℂ) (hh : ∀ c, Good a b (h c)) (u : ι → ℂ) (D : ℕ) :
    tailW ρ a b D P (fun x => ∑ c, u c * h c x) ≤ (∑ c, ‖u c‖ ^ 2) * ∑ c, tailW ρ a b D P (h c) := by
  have hPc : ∀ j, Good a b (fun x => ((P j x : ℝ) : ℂ)) := fun j => good_ofReal (hP j)
  set e : ι → ℝ → ℂ := fun c x => h c x - ∑ j ∈ Finset.range (D + 1), coefA ρ a b P (h c) j * (P j x : ℂ)
    with he_def
  have he : ∀ c, Good a b (e c) := fun c =>
    good_sub (hh c) (good_sum _ fun j => good_mul (good_const _) (hPc j))
  have hg : Good a b (fun x => ∑ c, u c * h c x) := good_sum _ fun c => good_mul (good_const _) (hh c)
  have hcoef : ∀ j, coefA ρ a b P (fun x => ∑ c, u c * h c x) j = ∑ c, u c * coefA ρ a b P (h c) j := by
    intro j
    have h1 := pr_sum_right hρ Finset.univ u h hh (hPc j)
    simp only [pr_poly_left] at h1
    exact h1
  have hres : ∀ x, (∑ c, u c * h c x) - ∑ j ∈ Finset.range (D + 1),
      coefA ρ a b P (fun x => ∑ c, u c * h c x) j * (P j x : ℂ) = ∑ c, u c * e c x := by
    intro x
    simp only [hcoef, he_def, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => by ring
  have hcs : ∀ x, ‖∑ c, u c * e c x‖ ^ 2 ≤ (∑ c, ‖u c‖ ^ 2) * ∑ c, ‖e c x‖ ^ 2 := by
    intro x
    calc ‖∑ c, u c * e c x‖ ^ 2 ≤ (∑ c, ‖u c‖ * ‖e c x‖) ^ 2 := by
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun c _ => norm_mul _ _
      _ ≤ (∑ c, ‖u c‖ ^ 2) * ∑ c, ‖e c x‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hue : Good a b (fun x => ∑ c, u c * e c x) := good_sum _ fun c => good_mul (good_const _) (he c)
  rw [← resid hρ hP horth hg D]
  simp only [hres]
  calc (∫ x in Set.Icc a b, ρ x * ‖∑ c, u c * e c x‖ ^ 2)
      ≤ ∫ x in Set.Icc a b, (∑ c, ‖u c‖ ^ 2) * ∑ c, ρ x * ‖e c x‖ ^ 2 := by
        refine integral_mono_ae (good_integrable (good_mul hρ (good_normSq hue)))
          (good_integrable (good_mul (good_const _) (good_sum _ fun c => good_mul hρ (good_normSq (he c)))))
          (ae_restrict_of_forall_mem measurableSet_Icc fun x hx => ?_)
        beta_reduce
        rw [← Finset.mul_sum, mul_left_comm]
        exact mul_le_mul_of_nonneg_left (hcs x) (hρ0 x hx)
    _ = (∑ c, ‖u c‖ ^ 2) * ∑ c, ∫ x in Set.Icc a b, ρ x * ‖e c x‖ ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ fun c _ => good_integrable (good_mul hρ (good_normSq (he c)))]
    _ = (∑ c, ‖u c‖ ^ 2) * ∑ c, tailW ρ a b D P (h c) := by
        congr 1
        exact Finset.sum_congr rfl fun c _ => resid hρ hP horth (hh c) D

lemma sumo {O : Type*} [Fintype O] {ι : Type*} [Fintype ι] (w : O → ℝ) (hw : ∀ o, 0 ≤ w o) (t : O → ℝ)
    (tc : O → ι → ℝ) (S R : ℝ) (hS : 0 ≤ S) (ht : ∀ o, t o ≤ S * ∑ c, tc o c)
    (hcol : ∑ o, w o * ∑ c, tc o c ≤ R) : ∑ o, w o * t o ≤ R * S := by
  calc ∑ o, w o * t o ≤ ∑ o, w o * (S * ∑ c, tc o c) :=
        Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_left (ht o) (hw o)
    _ = S * ∑ o, w o * ∑ c, tc o c := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun o _ => by ring
    _ ≤ S * R := mul_le_mul_of_nonneg_left hcol hS
    _ = R * S := mul_comm _ _

end Breakdown.CellCert.Reduction.TailColumnInternal

namespace Breakdown.CellCert.Reduction

open SteadyCert Assembly CellAnalysis TailColumnInternal

private lemma heightTail_eq (K : CellBox) (B : CellBases) (D : ℕ) (g : ℝ → ℂ) :
    K.heightTail B D g = tailW (fun _ => 1) K.z₁ K.z₂ D B.heightPoly g := by
  simp only [CellBox.heightTail, tailW, coefA, one_mul, Complex.ofReal_one]

private lemma poly_cont (c : ℕ → ℕ → ℝ) (j : ℕ) :
    Continuous (fun r : ℝ => ∑ i ∈ Finset.range (j + 1), c j i * r ^ i) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_pow i)

private lemma lineWeight_cont (K : CellBox) : Continuous K.lineWeight := by
  by_cases h0 : K.r₁ = 0
  · have e : K.lineWeight = fun r => r := by
      funext r
      simp [CellBox.lineWeight, h0]
    rw [e]
    exact continuous_id
  · have e : K.lineWeight = fun _ => 1 := by
      funext r
      simp [CellBox.lineWeight, h0]
    rw [e]
    exact continuous_const

private lemma lineWeight_nonneg (K : CellBox) :
    ∀ r ∈ Set.Icc K.r₁ K.r₂, 0 ≤ K.lineWeight r := by
  intro r hr
  by_cases h0 : K.r₁ = 0
  · simp only [CellBox.lineWeight, h0, if_true]
    linarith [hr.1]
  · simp [CellBox.lineWeight, h0]

theorem tailBounds_of_columns : TailColumnBoundStatement := by
  intro K B hK hB D I O _ _ T hT hC
  refine ⟨hC.outWeight_nonneg, hC.radialBound_nonneg, hC.heightBound_nonneg, ?_, ?_⟩
  · intro i j hj z hz θ u
    have hρ : Good K.r₁ K.r₂ K.lineWeight := good_cont (lineWeight_cont K)
    have hP : ∀ j, Good K.r₁ K.r₂ (B.radialPoly j) := fun j => good_cont (poly_cont B.radialCoef j)
    have hh : ∀ o c, Good K.r₁ K.r₂ (fun r => T.mult i o c (r, z) θ * (B.radialPoly j r : ℂ)) := by
      intro o c
      obtain ⟨C, hCb⟩ := hT.mult_bounded i o c
      exact good_mul ⟨hC.radial_sections i o c z (Set.Ioo_subset_Icc_self hz) θ, C, fun r hr => hCb (r, z) (Set.mk_mem_prod hr (Set.Ioo_subset_Icc_self hz)) θ⟩
        (good_ofReal (hP j))
    refine sumo _ hC.outWeight_nonneg _ _ _ _ (Finset.sum_nonneg fun c _ => by positivity) (fun o => ?_)
      (hC.radial_columns i j hj z hz θ)
    have e1 : (fun r => (∑ c, T.mult i o c (r, z) θ * u c) * (B.radialPoly j r : ℂ))
        = fun r => ∑ c, u c * (T.mult i o c (r, z) θ * (B.radialPoly j r : ℂ)) := by
      funext r
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [e1]
    exact col hρ (lineWeight_nonneg K) hP hB.radial_orthonormal
      (fun c r => T.mult i o c (r, z) θ * (B.radialPoly j r : ℂ)) (hh o) u D
  · intro i l hl r hr θ u
    have hρ : Good K.z₁ K.z₂ (fun _ : ℝ => (1 : ℝ)) := good_const 1
    have hP : ∀ l, Good K.z₁ K.z₂ (B.heightPoly l) := fun l => good_cont (poly_cont B.heightCoef l)
    have horth : ∀ l l', ∫ z in Set.Icc K.z₁ K.z₂, (fun _ : ℝ => (1 : ℝ)) z * B.heightPoly l z * B.heightPoly l' z
        = if l = l' then 1 else 0 := by
      intro l l'
      simp only [one_mul]
      exact hB.height_orthonormal l l'
    have hh : ∀ o c, Good K.z₁ K.z₂ (fun z => T.mult i o c (r, z) θ * (B.heightPoly l z : ℂ)) := by
      intro o c
      obtain ⟨C, hCb⟩ := hT.mult_bounded i o c
      exact good_mul ⟨hC.height_sections i o c r (Set.Ioo_subset_Icc_self hr) θ, C, fun z hz => hCb (r, z) (Set.mk_mem_prod (Set.Ioo_subset_Icc_self hr) hz) θ⟩
        (good_ofReal (hP l))
    have hcol := hC.height_columns i l hl r hr θ
    simp only [heightTail_eq] at hcol ⊢
    refine sumo _ hC.outWeight_nonneg _ _ _ _ (Finset.sum_nonneg fun c _ => by positivity) (fun o => ?_) hcol
    have e1 : (fun z => (∑ c, T.mult i o c (r, z) θ * u c) * (B.heightPoly l z : ℂ))
        = fun z => ∑ c, u c * (T.mult i o c (r, z) θ * (B.heightPoly l z : ℂ)) := by
      funext z
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [e1]
    exact col hρ (fun _ _ => zero_le_one) hP horth
      (fun c z => T.mult i o c (r, z) θ * (B.heightPoly l z : ℂ)) (hh o) u D

end Breakdown.CellCert.Reduction
