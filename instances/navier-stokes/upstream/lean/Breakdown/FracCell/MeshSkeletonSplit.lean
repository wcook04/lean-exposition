import Breakdown.FracCell.MeshSkeletonPair

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

namespace MeshSkeletonSplitInternal

theorem prod_split_right (A : Set ℝ) (hA : MeasurableSet A) {lo mid hi : ℝ} (h1 : lo ≤ mid) (h2 : mid ≤ hi)
    (g : ℝ × ℝ → ℂ) (hg : IntegrableOn g (A ×ˢ Set.Icc lo hi)) :
    ∫ p in A ×ˢ Set.Icc lo hi, g p = (∫ p in A ×ˢ Set.Icc lo mid, g p) + ∫ p in A ×ˢ Set.Icc mid hi, g p := by
  have hs1 : A ×ˢ Set.Icc lo mid ⊆ A ×ˢ Set.Icc lo hi := Set.prod_mono le_rfl (Set.Icc_subset_Icc le_rfl h2)
  have hs2 : A ×ˢ Set.Icc mid hi ⊆ A ×ˢ Set.Icc lo hi := Set.prod_mono le_rfl (Set.Icc_subset_Icc h1 le_rfl)
  have hi1 := hg.mono_set hs1
  have hi2 := hg.mono_set hs2
  rw [← Set.Icc_union_Icc_eq_Icc h1 h2, Set.prod_union]
  refine setIntegral_union₀ ?_ (hA.prod measurableSet_Icc).nullMeasurableSet hi1 hi2
  unfold AEDisjoint
  apply measure_mono_null (t := Set.univ ×ˢ {mid})
  · rintro ⟨a, b⟩ ⟨⟨_, hb1⟩, ⟨_, hb2⟩⟩
    exact ⟨trivial, le_antisymm hb1.2 hb2.1⟩
  · rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp

theorem prod_split_left (B : Set ℝ) (hB : MeasurableSet B) {lo mid hi : ℝ} (h1 : lo ≤ mid) (h2 : mid ≤ hi)
    (g : ℝ × ℝ → ℂ) (hg : IntegrableOn g (Set.Icc lo hi ×ˢ B)) :
    ∫ p in Set.Icc lo hi ×ˢ B, g p = (∫ p in Set.Icc lo mid ×ˢ B, g p) + ∫ p in Set.Icc mid hi ×ˢ B, g p := by
  have hs1 : Set.Icc lo mid ×ˢ B ⊆ Set.Icc lo hi ×ˢ B := Set.prod_mono (Set.Icc_subset_Icc le_rfl h2) le_rfl
  have hs2 : Set.Icc mid hi ×ˢ B ⊆ Set.Icc lo hi ×ˢ B := Set.prod_mono (Set.Icc_subset_Icc h1 le_rfl) le_rfl
  have hi1 := hg.mono_set hs1
  have hi2 := hg.mono_set hs2
  rw [← Set.Icc_union_Icc_eq_Icc h1 h2, Set.union_prod]
  refine setIntegral_union₀ ?_ (measurableSet_Icc.prod hB).nullMeasurableSet hi1 hi2
  unfold AEDisjoint
  apply measure_mono_null (t := {mid} ×ˢ Set.univ)
  · rintro ⟨a, b⟩ ⟨⟨ha1, _⟩, ⟨ha2, _⟩⟩
    exact ⟨le_antisymm ha1.2 ha2.1, trivial⟩
  · rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp

theorem box_sub (a b : ℝ) : Set.Icc a b ⊆ Set.Icc (-(|a| + |b|)) (|a| + |b|) := by
  intro s hs
  constructor
  · linarith [neg_abs_le a, abs_nonneg b, hs.1]
  · linarith [le_abs_self b, abs_nonneg a, hs.2]

theorem radial_int {F dF : ℝ × ℝ → ℂ} (h : IsRadialWeakPair F dF) {c o : ℝ} (hm : 0 < min c o) {f : ℝ → ℝ}
    (hf : Continuous f) (a b : ℝ) :
    IntegrableOn (radialStripTerm c o F dF f) (Set.Icc (min c o) (max c o) ×ˢ Set.Icc a b) := by
  have hS : IsCompact (Set.Icc (min c o) (max c o) ×ˢ Set.Icc a b) := isCompact_Icc.prod isCompact_Icc
  have hsub : Set.Icc (min c o) (max c o) ×ˢ Set.Icc a b ⊆
      Set.Icc (min c o) (max c o) ×ˢ Set.Icc (-(|a| + |b|)) (|a| + |b|) := Set.prod_mono le_rfl (box_sub a b)
  have hF : IntegrableOn F (Set.Icc (min c o) (max c o) ×ˢ Set.Icc a b) :=
    ((h.1 (max c o) (|a| + |b|)).1).mono_set (hsub.trans (Set.prod_mono (Set.Icc_subset_Icc hm.le le_rfl) le_rfl))
  have hdF : IntegrableOn dF (Set.Icc (min c o) (max c o) ×ˢ Set.Icc a b) :=
    (h.2.1 (min c o) (max c o) (|a| + |b|) hm).mono_set hsub
  have h1 : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p)
      (Set.Icc (min c o) (max c o) ×ˢ Set.Icc a b) := by
    refine Integrable.add (Integrable.const_mul hF _) ?_
    exact IntegrableOn.continuousOn_mul (by fun_prop) hdF hS
  exact h1.mul_continuousOn (by fun_prop) hS

theorem height_term_eq (c o : ℝ) (wt : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ) (f : ℝ → ℝ) :
    heightStripTerm c o wt F dF f = fun p => ((((1 / (c - o) : ℝ)) : ℂ) * ((wt p.1 : ℂ) * F p)
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * ((wt p.1 : ℂ) * dF p)) * ((f p.1 : ℝ) : ℂ) := by
  funext p
  simp only [heightStripTerm]
  push_cast
  ring

theorem height_int {wt : ℝ → ℝ} {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair wt F dF) (c o : ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) (a b : ℝ) :
    IntegrableOn (heightStripTerm c o wt F dF f) (Set.Icc a b ×ˢ Set.Icc (min c o) (max c o)) := by
  have hS : IsCompact (Set.Icc a b ×ˢ Set.Icc (min c o) (max c o)) := isCompact_Icc.prod isCompact_Icc
  have hsub : Set.Icc a b ×ˢ Set.Icc (min c o) (max c o) ⊆
      Set.Icc (-(|a| + |b|)) (|a| + |b|) ×ˢ Set.Icc (-(|min c o| + |max c o|)) (|min c o| + |max c o|) :=
    Set.prod_mono (box_sub a b) (box_sub _ _)
  have hF := ((h.1 (|a| + |b|) (|min c o| + |max c o|)).1).mono_set hsub
  have hdF := ((h.1 (|a| + |b|) (|min c o| + |max c o|)).2).mono_set hsub
  rw [height_term_eq]
  have h1 : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ)) : ℂ) * ((wt p.1 : ℂ) * F p)
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * ((wt p.1 : ℂ) * dF p))
      (Set.Icc a b ×ˢ Set.Icc (min c o) (max c o)) := by
    refine Integrable.add (Integrable.const_mul hF _) ?_
    exact IntegrableOn.continuousOn_mul (by fun_prop) hdF hS
  exact h1.mul_continuousOn (by fun_prop) hS

end MeshSkeletonSplitInternal

namespace MeshSkeletonSplitInternal

theorem rsm_eq (c o lo hi : ℝ) (F dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ) :
    radialStripMoment c o lo hi F dF t =
      edgeSign c o * ∫ p in Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi, radialStripTerm c o F dF t p := rfl

theorem hsm_eq (c o lo hi : ℝ) (wt : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ) :
    heightStripMoment c o lo hi wt F dF t =
      edgeSign c o * ∫ p in Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o), heightStripTerm c o wt F dF t p := rfl

section radial

variable {F dF : ℝ × ℝ → ℂ} (h : IsRadialWeakPair F dF) {c o : ℝ} (hm : 0 < min c o)
include h hm

theorem rsm_add {lo mid hi : ℝ} (h1 : lo ≤ mid) (h2 : mid ≤ hi) {f : ℝ → ℝ} (hf : Continuous f) :
    radialStripMoment c o lo hi F dF f = radialStripMoment c o lo mid F dF f + radialStripMoment c o mid hi F dF f := by
  rw [rsm_eq, rsm_eq, rsm_eq, prod_split_right _ measurableSet_Icc h1 h2 _ (radial_int h hm hf lo hi), mul_add]

theorem rsm_lin (a b : ℝ) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    radialStripMoment c o a b F dF (fun s => f s + g s) =
      radialStripMoment c o a b F dF f + radialStripMoment c o a b F dF g := by
  rw [rsm_eq, rsm_eq, rsm_eq, ← mul_add, ← integral_add (radial_int h hm hf a b) (radial_int h hm hg a b)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  simp only [radialStripTerm]
  push_cast
  ring

end radial

theorem rsm_smul (c o a b : ℝ) (F dF : ℝ × ℝ → ℂ) (w : ℝ) (f : ℝ → ℝ) :
    radialStripMoment c o a b F dF (fun s => w * f s) = (w : ℂ) * radialStripMoment c o a b F dF f := by
  rw [rsm_eq, rsm_eq, mul_left_comm, ← integral_const_mul (w : ℂ)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  simp only [radialStripTerm]
  push_cast
  ring

theorem rsm_congr (c o a b : ℝ) (F dF : ℝ × ℝ → ℂ) {f g : ℝ → ℝ} (hfg : ∀ s ∈ Set.Icc a b, f s = g s) :
    radialStripMoment c o a b F dF f = radialStripMoment c o a b F dF g := by
  rw [rsm_eq, rsm_eq]
  congr 1
  refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) (fun p hp => ?_)
  simp only [radialStripTerm]
  rw [hfg p.2 hp.2]

section height

variable {wt : ℝ → ℝ} {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair wt F dF) (c o : ℝ)
include h

theorem hsm_add {lo mid hi : ℝ} (h1 : lo ≤ mid) (h2 : mid ≤ hi) {f : ℝ → ℝ} (hf : Continuous f) :
    heightStripMoment c o lo hi wt F dF f =
      heightStripMoment c o lo mid wt F dF f + heightStripMoment c o mid hi wt F dF f := by
  rw [hsm_eq, hsm_eq, hsm_eq, prod_split_left _ measurableSet_Icc h1 h2 _ (height_int h c o hf lo hi), mul_add]

theorem hsm_lin (a b : ℝ) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    heightStripMoment c o a b wt F dF (fun s => f s + g s) =
      heightStripMoment c o a b wt F dF f + heightStripMoment c o a b wt F dF g := by
  rw [hsm_eq, hsm_eq, hsm_eq, ← mul_add, ← integral_add (height_int h c o hf a b) (height_int h c o hg a b)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  simp only [heightStripTerm]
  push_cast
  ring

end height

theorem hsm_smul (c o a b : ℝ) (wt : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ) (w : ℝ) (f : ℝ → ℝ) :
    heightStripMoment c o a b wt F dF (fun s => w * f s) = (w : ℂ) * heightStripMoment c o a b wt F dF f := by
  rw [hsm_eq, hsm_eq, mul_left_comm, ← integral_const_mul (w : ℂ)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  simp only [heightStripTerm]
  push_cast
  ring

theorem hsm_congr (c o a b : ℝ) (wt : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ) {f g : ℝ → ℝ}
    (hfg : ∀ s ∈ Set.Icc a b, f s = g s) :
    heightStripMoment c o a b wt F dF f = heightStripMoment c o a b wt F dF g := by
  rw [hsm_eq, hsm_eq]
  congr 1
  refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) (fun p hp => ?_)
  simp only [heightStripTerm]
  rw [hfg p.1 hp.1]

theorem list_cont {β : Type*} (l : List β) (G : β → ℝ → ℝ) (hG : ∀ p ∈ l, Continuous (G p)) :
    Continuous (fun s => (l.map (fun p => G p s)).sum) := by
  induction l with
  | nil => simpa using continuous_const
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hG p List.mem_cons_self).add (ih (fun q hq => hG q (List.mem_cons_of_mem _ hq)))

theorem list_lin {β : Type*} (J : (ℝ → ℝ) → ℂ)
    (hlin : ∀ f g, Continuous f → Continuous g → J (fun s => f s + g s) = J f + J g)
    (hsmul : ∀ (w : ℝ) f, J (fun s => w * f s) = (w : ℂ) * J f)
    (l : List β) (G : β → ℝ → ℝ) (hG : ∀ p ∈ l, Continuous (G p)) :
    J (fun s => (l.map (fun p => G p s)).sum) = (l.map (fun p => J (G p))).sum := by
  induction l with
  | nil =>
    have := hsmul 0 (fun _ => 0)
    simp only [zero_mul, Complex.ofReal_zero] at this
    simpa using this
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [hlin _ _ (hG p List.mem_cons_self) (list_cont ps G (fun q hq => hG q (List.mem_cons_of_mem _ hq))),
      ih (fun q hq => hG q (List.mem_cons_of_mem _ hq))]

theorem split_core (J : ℝ → ℝ → (ℝ → ℝ) → ℂ) {lo mid hi : ℝ} (hlm : lo < mid) (t : ℝ → ℝ)
    (l : List (SkeletonKey × ℝ)) (G : ℝ → ℝ → SkeletonKey × ℝ → ℝ → ℝ) (V : SkeletonKey → ℂ)
    (hadd : J lo hi t = J lo mid t + J mid hi t)
    (hlin : ∀ a b f g, Continuous f → Continuous g → J a b (fun s => f s + g s) = J a b f + J a b g)
    (hsmul : ∀ a b (w : ℝ) f, J a b (fun s => w * f s) = (w : ℂ) * J a b f)
    (hpart : ∀ p ∈ l, ∃ lo' hi' f, ((lo' = lo ∧ hi' = mid) ∨ (lo' = mid ∧ hi' = hi)) ∧ Continuous f ∧
      V p.1 = J lo' hi' f ∧ ∀ a b s, G a b p s = if lo' = a ∧ hi' = b then p.2 * f s else 0)
    (hcongr : ∀ lo' hi', ((lo' = lo ∧ hi' = mid) ∨ (lo' = mid ∧ hi' = hi)) →
      J lo' hi' t = J lo' hi' (fun s => (l.map (fun p => G lo' hi' p s)).sum)) :
    J lo hi t = (l.map (fun p => (p.2 : ℂ) * V p.1)).sum := by
  have hzero : ∀ a b, J a b (fun _ => 0) = 0 := by
    intro a b
    have := hsmul a b 0 (fun _ => 0)
    simp only [zero_mul, Complex.ofReal_zero] at this
    exact this
  have hGc : ∀ a b, ∀ p ∈ l, Continuous (G a b p) := by
    intro a b p hp
    obtain ⟨lo', hi', f, _, hf, _, hG⟩ := hpart p hp
    have : G a b p = fun s => if lo' = a ∧ hi' = b then p.2 * f s else 0 := funext (hG a b)
    rw [this]
    split_ifs
    · exact continuous_const.mul hf
    · exact continuous_const
  have hpt : ∀ p ∈ l, (p.2 : ℂ) * V p.1 = J lo mid (G lo mid p) + J mid hi (G mid hi p) := by
    intro p hp
    obtain ⟨lo', hi', f, hh, hf, hV, hG⟩ := hpart p hp
    rw [hV]
    rcases hh with ⟨r1, r2⟩ | ⟨r1, r2⟩
    · have e1 : G lo mid p = fun s => p.2 * f s := funext fun s => by rw [hG, if_pos ⟨r1, r2⟩]
      have e2 : G mid hi p = fun _ => 0 := funext fun s => by
        rw [hG, if_neg (fun h => absurd (r1.symm.trans h.1) (ne_of_lt hlm))]
      rw [e1, e2, hsmul, hzero, add_zero, r1, r2]
    · have e1 : G lo mid p = fun _ => 0 := funext fun s => by
        rw [hG, if_neg (fun h => absurd (h.1.symm.trans r1) (ne_of_lt hlm))]
      have e2 : G mid hi p = fun s => p.2 * f s := funext fun s => by rw [hG, if_pos ⟨r1, r2⟩]
      rw [e1, e2, hsmul, hzero, zero_add, r1, r2]
  rw [List.map_congr_left hpt, List.sum_map_add, hadd, hcongr lo mid (Or.inl ⟨rfl, rfl⟩),
    hcongr mid hi (Or.inr ⟨rfl, rfl⟩), list_lin (J lo mid) (hlin lo mid) (hsmul lo mid) l _ (hGc lo mid),
    list_lin (J mid hi) (hlin mid hi) (hsmul mid hi) l _ (hGc mid hi)]

end MeshSkeletonSplitInternal

namespace MeshSkeletonSplitInternal

def momJ (weighted : Bool) (F dFr dFz : ℝ × ℝ → ℂ) (rad : Bool) (lev a b : ℝ) (f : ℝ → ℝ) : ℂ :=
  if rad then radialStripMoment lev (lev + 1) a b F dFr f
  else heightStripMoment lev (lev + 1) a b (fun r => if weighted then r else 1) F dFz f

section mom

variable {weighted : Bool} {F dFr dFz : ℝ × ℝ → ℂ} {rad : Bool} {lev : ℝ}
  (hr : rad = true → IsRadialWeakPair F dFr)
  (hh : rad = false → IsHeightWeakPair (fun r => if weighted then r else 1) F dFz) (hlev : rad = true → 0 < lev)
include hr hh hlev

theorem momJ_add {lo mid hi : ℝ} (h1 : lo ≤ mid) (h2 : mid ≤ hi) {f : ℝ → ℝ} (hf : Continuous f) :
    momJ weighted F dFr dFz rad lev lo hi f =
      momJ weighted F dFr dFz rad lev lo mid f + momJ weighted F dFr dFz rad lev mid hi f := by
  cases rad
  · exact hsm_add (hh rfl) _ _ h1 h2 hf
  · have hm : 0 < min lev (lev + 1) := by rw [min_eq_left (by linarith)]; exact hlev rfl
    exact rsm_add (hr rfl) hm h1 h2 hf

theorem momJ_lin (a b : ℝ) (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    momJ weighted F dFr dFz rad lev a b (fun s => f s + g s) =
      momJ weighted F dFr dFz rad lev a b f + momJ weighted F dFr dFz rad lev a b g := by
  cases rad
  · exact hsm_lin (hh rfl) _ _ a b hf hg
  · have hm : 0 < min lev (lev + 1) := by rw [min_eq_left (by linarith)]; exact hlev rfl
    exact rsm_lin (hr rfl) hm a b hf hg

end mom

theorem momJ_smul (weighted : Bool) (F dFr dFz : ℝ × ℝ → ℂ) (rad : Bool) (lev a b w : ℝ) (f : ℝ → ℝ) :
    momJ weighted F dFr dFz rad lev a b (fun s => w * f s) = (w : ℂ) * momJ weighted F dFr dFz rad lev a b f := by
  cases rad <;> simp only [momJ, Bool.false_eq_true, ↓reduceIte]
  · exact hsm_smul _ _ _ _ _ _ _ _ _
  · exact rsm_smul _ _ _ _ _ _ _ _

theorem momJ_congr (weighted : Bool) (F dFr dFz : ℝ × ℝ → ℂ) (rad : Bool) (lev a b : ℝ) {f g : ℝ → ℝ}
    (hfg : ∀ s ∈ Set.Icc a b, f s = g s) :
    momJ weighted F dFr dFz rad lev a b f = momJ weighted F dFr dFz rad lev a b g := by
  cases rad <;> simp only [momJ, Bool.false_eq_true, ↓reduceIte]
  · exact hsm_congr _ _ _ _ _ _ _ hfg
  · exact rsm_congr _ _ _ _ _ _ hfg

theorem poly_cont (t : ℕ → ℕ → ℝ) (d : ℕ) : Continuous (fun s : ℝ => ∑ i ∈ Finset.range (d + 1), t d i * s ^ i) :=
  continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_pow i))

theorem split_mom (weighted : Bool) (F dFr dFz : ℝ × ℝ → ℂ) {rad : Bool} {lev : ℝ}
    (hr : rad = true → IsRadialWeakPair F dFr)
    (hh : rad = false → IsHeightWeakPair (fun r => if weighted then r else 1) F dFz) (hlev : rad = true → 0 < lev)
    {lo mid hi : ℝ} (hlm : lo < mid) (hmh : mid < hi) {t : ℝ → ℝ} (ht : Continuous t)
    (l : List (SkeletonKey × ℝ)) (G : ℝ → ℝ → SkeletonKey × ℝ → ℝ → ℝ) (V : SkeletonKey → ℂ)
    (hpart : ∀ p ∈ l, ∃ lo' hi' f, ((lo' = lo ∧ hi' = mid) ∨ (lo' = mid ∧ hi' = hi)) ∧ Continuous f ∧
      V p.1 = momJ weighted F dFr dFz rad lev lo' hi' f ∧ ∀ a b s, G a b p s = if lo' = a ∧ hi' = b then p.2 * f s else 0)
    (hid : ∀ lo' hi', ((lo' = lo ∧ hi' = mid) ∨ (lo' = mid ∧ hi' = hi)) → ∀ s ∈ Set.Icc lo' hi',
      t s = (l.map (fun p => G lo' hi' p s)).sum) :
    momJ weighted F dFr dFz rad lev lo hi t = (l.map (fun p => (p.2 : ℂ) * V p.1)).sum :=
  split_core (momJ weighted F dFr dFz rad lev) hlm t l G V (momJ_add hr hh hlev hlm.le hmh.le ht)
    (momJ_lin hr hh hlev) (momJ_smul weighted F dFr dFz rad lev) hpart
    (fun lo' hi' h => momJ_congr _ _ _ _ _ _ _ _ (hid lo' hi' h))

end MeshSkeletonSplitInternal

namespace MeshSkeletonSplitInternal

def IsPolyFun (f : ℝ → ℝ) : Prop := ∃ P : Polynomial ℝ, ∀ s, f s = P.eval s

theorem polyFun_cont {f : ℝ → ℝ} (h : IsPolyFun f) : Continuous f := by
  obtain ⟨P, hP⟩ := h
  have : f = fun s => P.eval s := funext hP
  rw [this]
  exact P.continuous

theorem polyFun_sum (t : ℕ → ℕ → ℝ) (d : ℕ) : IsPolyFun (fun s => ∑ i ∈ Finset.range (d + 1), t d i * s ^ i) :=
  ⟨∑ i ∈ Finset.range (d + 1), Polynomial.C (t d i) * Polynomial.X ^ i, fun s => by
    simp [Polynomial.eval_finsetSum]⟩

theorem polyFun_list {β : Type*} (l : List β) (G : β → ℝ → ℝ) (hG : ∀ p ∈ l, IsPolyFun (G p)) :
    IsPolyFun (fun s => (l.map (fun p => G p s)).sum) := by
  induction l with
  | nil => exact ⟨0, fun s => by simp⟩
  | cons p ps ih =>
    obtain ⟨P, hP⟩ := hG p List.mem_cons_self
    obtain ⟨Q, hQ⟩ := ih (fun q hq => hG q (List.mem_cons_of_mem _ hq))
    exact ⟨P + Q, fun s => by
      have h2 := hQ s
      beta_reduce at h2 ⊢
      rw [List.map_cons, List.sum_cons, hP, h2, Polynomial.eval_add]⟩

theorem polyFun_ext {f g : ℝ → ℝ} (hf : IsPolyFun f) (hg : IsPolyFun g) {a b : ℝ} (hab : a < b)
    (h : ∀ s ∈ Set.Icc a b, f s = g s) (s : ℝ) : f s = g s := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  have hz : P - Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.Icc_infinite hab).mono
    intro u hu
    show Polynomial.IsRoot (P - Q) u
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, ← hP, ← hQ, h u hu, sub_self]
  rw [hP, hQ, ← sub_eq_zero, ← Polynomial.eval_sub, hz, Polynomial.eval_zero]

theorem rwi_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (r : ℝ) :
    radialWeightIntegral (fun s => f s + g s) r = radialWeightIntegral f r + radialWeightIntegral g r := by
  simp only [radialWeightIntegral]
  rw [← intervalIntegral.integral_add ((by fun_prop : Continuous (fun ρ : ℝ => ρ * f ρ)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun ρ : ℝ => ρ * g ρ)).intervalIntegrable _ _)]
  congr 1
  funext ρ
  ring

theorem rwi_smul (w : ℝ) (f : ℝ → ℝ) (r : ℝ) :
    radialWeightIntegral (fun s => w * f s) r = w * radialWeightIntegral f r := by
  simp only [radialWeightIntegral]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext ρ
  ring

def presJ (ν : ℝ → ℝ) (n : ℤ) (rad : Bool) (lev a b : ℝ) (f : ℝ → ℝ) : ℂ :=
  if n = 0 then ((if rad then ν lev * ∫ z in a..b, f z
    else ν b * radialWeightIntegral f b - ν a * radialWeightIntegral f a : ℝ) : ℂ) else 0

theorem presJ_add (ν : ℝ → ℝ) (n : ℤ) (rad : Bool) (lev lo mid hi : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    presJ ν n rad lev lo hi f = presJ ν n rad lev lo mid f + presJ ν n rad lev mid hi f := by
  simp only [presJ]
  split_ifs
  · rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable lo mid)
      (hf.intervalIntegrable mid hi)]
    push_cast
    ring
  · push_cast
    ring
  · simp

theorem presJ_lin (ν : ℝ → ℝ) (n : ℤ) (rad : Bool) (lev a b : ℝ) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    presJ ν n rad lev a b (fun s => f s + g s) = presJ ν n rad lev a b f + presJ ν n rad lev a b g := by
  simp only [presJ]
  split_ifs
  · rw [intervalIntegral.integral_add (hf.intervalIntegrable a b) (hg.intervalIntegrable a b)]
    push_cast
    ring
  · rw [rwi_add hf hg, rwi_add hf hg]
    push_cast
    ring
  · simp

theorem presJ_smul (ν : ℝ → ℝ) (n : ℤ) (rad : Bool) (lev a b w : ℝ) (f : ℝ → ℝ) :
    presJ ν n rad lev a b (fun s => w * f s) = (w : ℂ) * presJ ν n rad lev a b f := by
  simp only [presJ]
  split_ifs
  · rw [intervalIntegral.integral_const_mul]
    push_cast
    ring
  · rw [rwi_smul, rwi_smul]
    push_cast
    ring
  · simp

theorem pres_split (F dFr dFz : ℝ × ℝ → ℂ) {rad : Bool} {lev : ℝ}
    (hr : rad = true → IsRadialWeakPair F dFr)
    (hh : rad = false → IsHeightWeakPair (fun r => if true then r else 1) F dFz) (hlev : rad = true → 0 < lev)
    (ν : ℝ → ℝ) (n : ℤ) {lo mid hi : ℝ} (hlm : lo < mid) (hmh : mid < hi) {t : ℝ → ℝ} (ht : IsPolyFun t)
    (l : List (SkeletonKey × ℝ)) (G : ℝ → ℝ → SkeletonKey × ℝ → ℝ → ℝ) (V : SkeletonKey → ℂ)
    (hpart : ∀ p ∈ l, ∃ lo' hi' f, ((lo' = lo ∧ hi' = mid) ∨ (lo' = mid ∧ hi' = hi)) ∧ IsPolyFun f ∧
      V p.1 = momJ true F dFr dFz rad lev lo' hi' f + presJ ν n rad lev lo' hi' f ∧
      ∀ a b s, G a b p s = if lo' = a ∧ hi' = b then p.2 * f s else 0)
    (hid : ∀ lo' hi', ((lo' = lo ∧ hi' = mid) ∨ (lo' = mid ∧ hi' = hi)) → ∀ s ∈ Set.Icc lo' hi',
      t s = (l.map (fun p => G lo' hi' p s)).sum) :
    momJ true F dFr dFz rad lev lo hi t + presJ ν n rad lev lo hi t =
      (l.map (fun p => (p.2 : ℂ) * V p.1)).sum := by
  have hpoly : ∀ a b, IsPolyFun (fun s => (l.map (fun p => G a b p s)).sum) := by
    intro a b
    apply polyFun_list
    intro p hp
    obtain ⟨lo', hi', f, _, ⟨P, hP⟩, _, hG⟩ := hpart p hp
    by_cases hc : lo' = a ∧ hi' = b
    · exact ⟨Polynomial.C p.2 * P, fun s => by rw [hG, if_pos hc, Polynomial.eval_mul, Polynomial.eval_C, hP]⟩
    · exact ⟨0, fun s => by rw [hG, if_neg hc, Polynomial.eval_zero]⟩
  have hglob : ∀ lo' hi', ((lo' = lo ∧ hi' = mid) ∨ (lo' = mid ∧ hi' = hi)) →
      t = fun s => (l.map (fun p => G lo' hi' p s)).sum := by
    intro lo' hi' hh'
    have hlt : lo' < hi' := by
      rcases hh' with ⟨r1, r2⟩ | ⟨r1, r2⟩
      · rw [r1, r2]; exact hlm
      · rw [r1, r2]; exact hmh
    funext s
    exact polyFun_ext ht (hpoly lo' hi') hlt (hid lo' hi' hh') s
  refine split_core (fun a b f => momJ true F dFr dFz rad lev a b f + presJ ν n rad lev a b f) hlm t l G V
    ?_ ?_ ?_ (fun p hp => ?_) (fun lo' hi' hh' => by rw [hglob lo' hi' hh'])
  · rw [momJ_add hr hh hlev hlm.le hmh.le (polyFun_cont ht), presJ_add ν n rad lev lo mid hi (polyFun_cont ht)]
    ring
  · intro a b f g hf hg
    rw [momJ_lin hr hh hlev a b f g hf hg, presJ_lin ν n rad lev a b hf hg]
    ring
  · intro a b w f
    rw [momJ_smul, presJ_smul]
    ring
  · obtain ⟨lo', hi', f, h1, h2, h3, h4⟩ := hpart p hp
    exact ⟨lo', hi', f, h1, polyFun_cont h2, h3, h4⟩

end MeshSkeletonSplitInternal

namespace MeshSkeletonSplitInternal

open MeshSkeletonInternal

variable {k N : ℕ} {c : FracCellData k N} {x : FieldTuple k}

theorem vel_keyData (hx : IsAdmissible c x) (L₀ : CellLayout) (h₀ : L₀.order = c.order) (ν : ℝ → ℝ)
    (n : ℤ) (rad : Bool) (lev lo hi : ℝ) (t : ℕ → ℕ → ℝ) (a : Fin 3) (d : ℕ) (l : List (SkeletonKey × ℝ))
    (hsplit : SegmentSplit (SkeletonKey.velocity n rad lev lo hi t a d) l)
    (hlev : rad = true → 0 < lev) :
    keyData L₀ x ν (SkeletonKey.velocity n rad lev lo hi t a d) =
      (l.map (fun p => (p.2 : ℂ) * keyData L₀ x ν p.1)).sum := by
  have e1 : (fun r : ℝ => if (false = true) then r else (1 : ℝ)) = fun _ => 1 := by funext r; simp
  obtain ⟨mid, hlm, hmh, hmem, hid⟩ := hsplit
  have hw := segment_modes_weak c x hx L₀ h₀ n a
  refine split_mom false (L₀.velMode n x a) (L₀.gradModeOf n x a 0) (L₀.gradModeOf n x a 2)
    (fun _ => hw.1) (fun _ => by rw [e1]; exact hw.2.1) hlev hlm hmh (poly_cont t d) l _ (keyData L₀ x ν) ?_ hid
  intro p hp
  obtain ⟨lo', hi', t', d', he, hh⟩ := hmem p hp
  refine ⟨lo', hi', _, hh, poly_cont t' d', by rw [he]; rfl, fun a' b' s => ?_⟩
  simp only [he]

theorem grad_key_false (L : CellLayout) (ν : ℝ → ℝ) (n : ℤ) (lev lo hi : ℝ) (t : ℕ → ℕ → ℝ) (a : Fin 3)
    (d : ℕ) : keyData L x ν (SkeletonKey.gradient n false lev lo hi t a d) =
      momJ true (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 0) (L.secondModeOf n x a 2 2) false lev lo hi
        (fun s => ∑ i ∈ Finset.range (d + 1), t d i * s ^ i) := by
  simp only [keyData, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem grad_key_true (L : CellLayout) (ν : ℝ → ℝ) (n : ℤ) (lev lo hi : ℝ) (t : ℕ → ℕ → ℝ) (a : Fin 3)
    (d : ℕ) : keyData L x ν (SkeletonKey.gradient n true lev lo hi t a d) =
      momJ true (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 0) (L.secondModeOf n x a 0 2) true lev lo hi
        (fun s => ∑ i ∈ Finset.range (d + 1), t d i * s ^ i) := by
  simp only [keyData, ↓reduceIte]
  rfl

theorem grad_keyData (hx : IsAdmissible c x) (L₀ : CellLayout) (h₀ : L₀.order = c.order) (ν : ℝ → ℝ)
    (n : ℤ) (rad : Bool) (lev lo hi : ℝ) (t : ℕ → ℕ → ℝ) (a : Fin 3) (d : ℕ) (l : List (SkeletonKey × ℝ))
    (hsplit : SegmentSplit (SkeletonKey.gradient n rad lev lo hi t a d) l)
    (hlev : rad = true → 0 < lev) :
    keyData L₀ x ν (SkeletonKey.gradient n rad lev lo hi t a d) =
      (l.map (fun p => (p.2 : ℂ) * keyData L₀ x ν p.1)).sum := by
  have e2 : (fun r : ℝ => if (true = true) then r else (1 : ℝ)) = fun r => r := by funext r; simp
  obtain ⟨mid, hlm, hmh, hmem, hid⟩ := hsplit
  have hw := segment_modes_weak c x hx L₀ h₀ n a
  cases rad
  · rw [grad_key_false]
    refine split_mom true (L₀.gradModeOf n x a 2) (L₀.secondModeOf n x a 2 0) (L₀.secondModeOf n x a 2 2)
      (fun h => absurd h (by simp)) (fun _ => by rw [e2]; exact hw.2.2.2.1) hlev hlm hmh (poly_cont t d) l _
      (keyData L₀ x ν) ?_ hid
    intro p hp
    obtain ⟨lo', hi', t', d', he, hh⟩ := hmem p hp
    refine ⟨lo', hi', _, hh, poly_cont t' d', by rw [he, grad_key_false], fun a' b' s => ?_⟩
    simp only [he]
  · rw [grad_key_true]
    refine split_mom true (L₀.gradModeOf n x a 0) (L₀.secondModeOf n x a 0 0) (L₀.secondModeOf n x a 0 2)
      (fun _ => hw.2.2.1) (fun h => absurd h (by simp)) hlev hlm hmh (poly_cont t d) l _
      (keyData L₀ x ν) ?_ hid
    intro p hp
    obtain ⟨lo', hi', t', d', he, hh⟩ := hmem p hp
    refine ⟨lo', hi', _, hh, poly_cont t' d', by rw [he, grad_key_true], fun a' b' s => ?_⟩
    simp only [he]

theorem pres_keyData (hx : IsAdmissible c x) (L₀ : CellLayout) (h₀ : L₀.order = c.order) (ν : ℝ → ℝ)
    (n : ℤ) (rad : Bool) (lev lo hi : ℝ) (t : ℕ → ℕ → ℝ) (d : ℕ) (l : List (SkeletonKey × ℝ))
    (hsplit : SegmentSplit (SkeletonKey.pressure n rad lev lo hi t d) l)
    (hlev : rad = true → 0 < lev) :
    keyData L₀ x ν (SkeletonKey.pressure n rad lev lo hi t d) =
      (l.map (fun p => (p.2 : ℂ) * keyData L₀ x ν p.1)).sum := by
  have e2 : (fun r : ℝ => if (true = true) then r else (1 : ℝ)) = fun r => r := by funext r; simp
  obtain ⟨mid, hlm, hmh, hmem, hid⟩ := hsplit
  have hw := segment_modes_weak c x hx L₀ h₀ n 0
  refine pres_split (L₀.pressMode n x) (L₀.pressureGradMode n x 0) (L₀.pressureGradMode n x 2)
    (fun _ => hw.2.2.2.2.1) (fun _ => by rw [e2]; exact hw.2.2.2.2.2) hlev ν n hlm hmh (polyFun_sum t d) l _
    (keyData L₀ x ν) ?_ hid
  intro p hp
  obtain ⟨lo', hi', t', d', he, hh⟩ := hmem p hp
  refine ⟨lo', hi', _, hh, polyFun_sum t' d', by rw [he]; rfl, fun a' b' s => ?_⟩
  simp only [he]

end MeshSkeletonSplitInternal

namespace MeshSkeletonInternal

open MeshSkeletonSplitInternal

variable {k N : ℕ} {c : FracCellData k N} {x : FieldTuple k}

theorem segmentSplit_keyData (hx : IsAdmissible c x) (L₀ : CellLayout) (h₀ : L₀.order = c.order) (ν : ℝ → ℝ)
    (key : SkeletonKey) (l : List (SkeletonKey × ℝ)) (hsplit : SegmentSplit key l) (hlev : keyLevelPos key) :
    keyData L₀ x ν key = (l.map (fun p => (p.2 : ℂ) * keyData L₀ x ν p.1)).sum := by
  cases key with
  | velocity n rad lev lo hi t a d => exact vel_keyData hx L₀ h₀ ν n rad lev lo hi t a d l hsplit hlev
  | gradient n rad lev lo hi t a d => exact grad_keyData hx L₀ h₀ ν n rad lev lo hi t a d l hsplit hlev
  | pressure n rad lev lo hi t d => exact pres_keyData hx L₀ h₀ ν n rad lev lo hi t d l hsplit hlev
  | corner _ _ _ => exact hsplit.elim
  | stream _ => exact hsplit.elim
  | private_ => exact hsplit.elim

end MeshSkeletonInternal

namespace MeshSkeletonSplitInternal

open MeshSkeletonInternal

theorem fin_lin (J : (ℝ → ℝ) → ℂ)
    (hlin : ∀ f g, Continuous f → Continuous g → J (fun s => f s + g s) = J f + J g)
    (hsmul : ∀ (w : ℝ) f, J (fun s => w * f s) = (w : ℂ) * J f)
    (e : ℕ → ℝ) (g : ℕ → ℝ → ℝ) (hg : ∀ i, Continuous (g i)) (D : ℕ) :
    J (fun s => ∑ i ∈ Finset.range (D + 1), e i * g i s) = ∑ i ∈ Finset.range (D + 1), (e i : ℂ) * J (g i) := by
  induction D with
  | zero => simp only [zero_add, Finset.sum_range_one]; exact hsmul _ _
  | succ D ih =>
    have h1 : (fun s => ∑ i ∈ Finset.range (D + 1 + 1), e i * g i s) =
        fun s => (fun s => ∑ i ∈ Finset.range (D + 1), e i * g i s) s + (fun s => e (D + 1) * g (D + 1) s) s :=
      funext fun s => Finset.sum_range_succ _ _
    have hc1 : Continuous (fun s => ∑ i ∈ Finset.range (D + 1), e i * g i s) :=
      continuous_finsetSum _ (fun i _ => continuous_const.mul (hg i))
    have hc2 : Continuous (fun s => e (D + 1) * g (D + 1) s) := continuous_const.mul (hg _)
    rw [h1, hlin _ _ hc1 hc2, ih, hsmul]
    exact (Finset.sum_range_succ (fun i => (e i : ℂ) * J (g i)) (D + 1)).symm

def streamC (L : CellLayout) {k : ℕ} (x : FieldTuple k) (ν : ℝ → ℝ) (q : ℝ × ℝ) : ℂ :=
  if q.1 = 0 ∨ q.2 = 0 then 0 else keyData L x ν (SkeletonKey.stream q)

variable {k N : ℕ} {c : FracCellData k N} {x : FieldTuple k}

theorem hsm_zero_width (c' o : ℝ) (wt : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ) :
    heightStripMoment c' o 0 0 wt F dF t = 0 := by
  rw [hsm_eq, setIntegral_measure_zero, mul_zero]
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem streamC_eq (hF : FluxStreamStatement) (hx : IsAdmissible c x) (L : CellLayout) (h₀ : L.order = c.order)
    (ν : ℝ → ℝ) (q : ℝ × ℝ) (hq : 0 ≤ q.1) : streamC L x ν q = keyData L x ν (SkeletonKey.stream q) := by
  unfold streamC
  split_ifs with h
  · rcases h with h | h
    · obtain ⟨q1, q2⟩ := q
      simp only at h
      subst h
      simp only [keyData]
      rw [hsm_zero_width]
    · obtain ⟨q1, q2⟩ := q
      simp only at h hq
      subst h
      have := ((hF c x hx L h₀ ⟨true, 1, 2, 0, 1, fun _ _ => 1⟩ ⟨by norm_num, by norm_num, by simp⟩ 0 0).2.2 q1 (0 + 1)
        hq (by norm_num))
      rw [← this]
      rfl
  · rfl

end MeshSkeletonSplitInternal

namespace MeshSkeletonSplitInternal

open MeshSkeletonInternal

variable {k N : ℕ} {c : FracCellData k N} {x : FieldTuple k}

theorem vel_key_eq (L : CellLayout) (ν : ℝ → ℝ) (n : ℤ) (rad : Bool) (lev lo hi : ℝ) (t : ℕ → ℕ → ℝ) (a : Fin 3)
    (d : ℕ) : keyData L x ν (SkeletonKey.velocity n rad lev lo hi t a d) =
      momJ false (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2) rad lev lo hi
        (fun s => ∑ i ∈ Finset.range (d + 1), t d i * s ^ i) := rfl

theorem flux_vel_split (hx : IsAdmissible c x) (L₀ : CellLayout) (h₀ : L₀.order = c.order) (ν : ℝ → ℝ) (n : ℤ)
    (rad : Bool) (lev lo mid hi : ℝ) (t : ℕ → ℕ → ℝ) (a : Fin 3) (d : ℕ) (hlev : rad = true → 0 < lev)
    (hlm : lo < mid) (hmh : mid < hi) (th : Bool → ℕ → ℕ → ℝ) (D : ℕ) (e : Bool → ℕ → ℝ)
    (hid : ∀ b : Bool, ∀ s ∈ Set.Icc (if b then mid else lo) (if b then hi else mid),
      (∑ i ∈ Finset.range (d + 1), t d i * s ^ i) =
        ∑ d' ∈ Finset.range (D + 1), e b d' * ∑ i ∈ Finset.range (d' + 1), th b d' i * s ^ i) :
    keyData L₀ x ν (SkeletonKey.velocity n rad lev lo hi t a d) =
      ∑ b : Bool, ∑ d' ∈ Finset.range (D + 1), (e b d' : ℂ) *
        keyData L₀ x ν (SkeletonKey.velocity n rad lev (if b then mid else lo) (if b then hi else mid) (th b) a d') := by
  have e1 : (fun r : ℝ => if (false = true) then r else (1 : ℝ)) = fun _ => 1 := by funext r; simp
  have hw := segment_modes_weak c x hx L₀ h₀ n a
  have hr : rad = true → IsRadialWeakPair (L₀.velMode n x a) (L₀.gradModeOf n x a 0) := fun _ => hw.1
  have hh : rad = false → IsHeightWeakPair (fun r => if false then r else 1) (L₀.velMode n x a)
      (L₀.gradModeOf n x a 2) := fun _ => by rw [e1]; exact hw.2.1
  have h0 := hid false
  have h1 := hid true
  simp only [Bool.false_eq_true, ↓reduceIte] at h0 h1
  simp only [vel_key_eq, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  rw [momJ_add hr hh hlev hlm.le hmh.le (poly_cont t d), momJ_congr _ _ _ _ _ _ _ _ h0,
    momJ_congr _ _ _ _ _ _ _ _ h1]
  have f0 := fin_lin (momJ false (L₀.velMode n x a) (L₀.gradModeOf n x a 0) (L₀.gradModeOf n x a 2) rad lev lo mid)
    (momJ_lin hr hh hlev lo mid) (momJ_smul _ _ _ _ _ _ _ _) (e false)
    (fun d' s => ∑ i ∈ Finset.range (d' + 1), th false d' i * s ^ i) (fun d' => poly_cont (th false) d') D
  have f1 := fin_lin (momJ false (L₀.velMode n x a) (L₀.gradModeOf n x a 0) (L₀.gradModeOf n x a 2) rad lev mid hi)
    (momJ_lin hr hh hlev mid hi) (momJ_smul _ _ _ _ _ _ _ _) (e true)
    (fun d' s => ∑ i ∈ Finset.range (d' + 1), th true d' i * s ^ i) (fun d' => poly_cont (th true) d') D
  beta_reduce at f0 f1
  rw [f0, f1, add_comm]

theorem flux_rad_rel (hF : FluxStreamStatement) (hx : IsAdmissible c x) (L₀ : CellLayout) (h₀ : L₀.order = c.order)
    (ν : ℝ → ℝ) (lev lo' hi' : ℝ) (th : ℕ → ℕ → ℝ) (c0 : ℝ) (hlev : 0 < lev) (hlo : 0 ≤ lo') (hlt : lo' < hi')
    (hn : ∀ s ∈ Set.Icc lo' hi', (1 : ℝ) = c0 * th 0 0) :
    ((lev * c0 : ℝ) : ℂ) * keyData L₀ x ν (SkeletonKey.velocity 0 true lev lo' hi' th 0 0) =
      streamC L₀ x ν (lev, lo') - streamC L₀ x ν (lev, hi') := by
  have h00 : th 0 0 ≠ 0 := by
    intro h
    have := hn lo' ⟨le_rfl, hlt.le⟩
    rw [h, mul_zero] at this
    exact one_ne_zero this
  let S : FaceSegment := ⟨true, lev, lev + 1, lo', hi', fun d i => if d = 0 then th 0 i else if i = d then 1 else 0⟩
  have hS : IsFaceSegment S := by
    refine ⟨by simp [S], hlt, fun d => ?_⟩
    by_cases hd : d = 0
    · subst hd; simp [S, h00]
    · simp [S, hd]
  have key := (hF c x hx L₀ h₀ S hS (lo' + 1) (hi' + 1)).1 rfl hlev hlo
    (by show lo' + 1 ≠ lo'; exact ne_of_gt (by linarith)) (by show hi' + 1 ≠ hi'; exact ne_of_gt (by linarith)) c0
    (fun z hz => by simpa [S, FaceSegment.test] using hn z hz)
  have hm : S.moment false (L₀.velMode 0 x 0) (L₀.gradModeOf 0 x 0 0) (L₀.gradModeOf 0 x 0 2) 0 =
      keyData L₀ x ν (SkeletonKey.velocity 0 true lev lo' hi' th 0 0) := by
    rw [vel_key_eq]
    simp only [FaceSegment.moment, momJ, S, ↓reduceIte]
    congr 1
  rw [streamC_eq hF hx L₀ h₀ ν _ hlev.le, streamC_eq hF hx L₀ h₀ ν _ hlev.le, ← hm]
  exact key

theorem flux_hgt_rel (hF : FluxStreamStatement) (hx : IsAdmissible c x) (L₀ : CellLayout) (h₀ : L₀.order = c.order)
    (ν : ℝ → ℝ) (lev lo' hi' : ℝ) (th : ℕ → ℕ → ℝ) (c0 c1 : ℝ) (hlo : 0 ≤ lo') (hlt : lo' < hi')
    (hn : ∀ s ∈ Set.Icc lo' hi', s = c0 * th 0 0 + c1 * (th 1 0 + th 1 1 * s)) :
    (c0 : ℂ) * keyData L₀ x ν (SkeletonKey.velocity 0 false lev lo' hi' th 2 0)
      + (c1 : ℂ) * keyData L₀ x ν (SkeletonKey.velocity 0 false lev lo' hi' th 2 1) =
      streamC L₀ x ν (hi', lev) - streamC L₀ x ν (lo', lev) := by
  have e1 := hn lo' ⟨le_rfl, hlt.le⟩
  have e2 := hn hi' ⟨hlt.le, le_rfl⟩
  have hd : (c1 * th 1 1 - 1) * (hi' - lo') = 0 := by linear_combination e1 - e2
  have h11 : c1 * th 1 1 = 1 := by
    rcases mul_eq_zero.1 hd with h | h
    · linarith
    · exact absurd h (by linarith)
  have h11' : th 1 1 ≠ 0 := by
    intro h
    rw [h, mul_zero] at h11
    exact zero_ne_one h11
  let S : FaceSegment := ⟨false, lev, lev + 1, lo', hi', fun d i => if d = 0 then
      (if th 0 0 = 0 then (if i = 0 then 1 else 0) else th 0 i) else if d = 1 then th 1 i else if i = d then 1 else 0⟩
  have hS : IsFaceSegment S := by
    refine ⟨by simp [S], hlt, fun d => ?_⟩
    by_cases hd0 : d = 0
    · subst hd0
      by_cases h00 : th 0 0 = 0 <;> simp [S, h00]
    · by_cases hd1 : d = 1
      · subst hd1; simp [S, h11']
      · simp [S, hd0, hd1]
  have key := (hF c x hx L₀ h₀ S hS (lev + 1) (lev + 1)).2.1 rfl hlo
    (by show lev + 1 ≠ lev; exact ne_of_gt (by linarith)) (by show lev + 1 ≠ lev; exact ne_of_gt (by linarith))
    (if th 0 0 = 0 then 0 else c0) c1 (fun r hr => by
      have := hn r hr
      by_cases h00 : th 0 0 = 0
      · simp [S, FaceSegment.test, Finset.sum_range_succ, h00] at this ⊢
        linarith
      · simp [S, FaceSegment.test, Finset.sum_range_succ, h00] at this ⊢
        linarith)
  have hm1 : S.moment false (L₀.velMode 0 x 2) (L₀.gradModeOf 0 x 2 0) (L₀.gradModeOf 0 x 2 2) 1 =
      keyData L₀ x ν (SkeletonKey.velocity 0 false lev lo' hi' th 2 1) := by
    rw [vel_key_eq]
    simp only [FaceSegment.moment, momJ, S, Bool.false_eq_true, ↓reduceIte]
    congr 1
  have hm0 : ((if th 0 0 = 0 then 0 else c0 : ℝ) : ℂ) *
      S.moment false (L₀.velMode 0 x 2) (L₀.gradModeOf 0 x 2 0) (L₀.gradModeOf 0 x 2 2) 0 =
      (c0 : ℂ) * keyData L₀ x ν (SkeletonKey.velocity 0 false lev lo' hi' th 2 0) := by
    by_cases h00 : th 0 0 = 0
    · rw [if_pos h00, Complex.ofReal_zero, zero_mul, vel_key_eq]
      have : momJ false (L₀.velMode 0 x 2) (L₀.gradModeOf 0 x 2 0) (L₀.gradModeOf 0 x 2 2) false lev lo' hi'
          (fun s => ∑ i ∈ Finset.range (0 + 1), th 0 i * s ^ i) =
          momJ false (L₀.velMode 0 x 2) (L₀.gradModeOf 0 x 2 0) (L₀.gradModeOf 0 x 2 2) false lev lo' hi'
            (fun s => (0 : ℝ) * s) := momJ_congr _ _ _ _ _ _ _ _ (fun s _ => by simp [h00])
      rw [this, momJ_smul, Complex.ofReal_zero, zero_mul, mul_zero]
    · rw [if_neg h00, vel_key_eq]
      congr 1
      simp only [FaceSegment.moment, momJ, S, Bool.false_eq_true, ↓reduceIte]
      congr 1
      funext s
      simp [FaceSegment.test, h00]
  rw [streamC_eq hF hx L₀ h₀ ν _ (hlo.trans hlt.le), streamC_eq hF hx L₀ h₀ ν _ hlo, ← hm0, ← hm1]
  exact key

end MeshSkeletonSplitInternal

namespace MeshSkeletonSplitInternal

open MeshSkeletonInternal

def ptOf (b0 : Fin 2) (z : ℂ) : ℝ := if b0 = 0 then z.re else z.im

theorem ptOf_add (b0 : Fin 2) (z w : ℂ) : ptOf b0 (z + w) = ptOf b0 z + ptOf b0 w := by
  unfold ptOf; split_ifs <;> simp

theorem ptOf_sub (b0 : Fin 2) (z w : ℂ) : ptOf b0 (z - w) = ptOf b0 z - ptOf b0 w := by
  unfold ptOf; split_ifs <;> simp

theorem ptOf_ofReal_mul (b0 : Fin 2) (r : ℝ) (z : ℂ) : ptOf b0 ((r : ℂ) * z) = r * ptOf b0 z := by
  unfold ptOf; split_ifs <;> simp

theorem ptOf_sum {ι : Type*} (b0 : Fin 2) (s : Finset ι) (f : ι → ℂ) :
    ptOf b0 (∑ i ∈ s, f i) = ∑ i ∈ s, ptOf b0 (f i) := by
  unfold ptOf; split_ifs <;> simp [Complex.re_sum, Complex.im_sum]

theorem ptOf_streamC (L : CellLayout) {k : ℕ} (x : FieldTuple k) (ν : ℝ → ℝ) (b0 : Fin 2) (q : ℝ × ℝ) :
    ptOf b0 (streamC L x ν q) = streamEval (fun q => ptOf b0 (keyData L x ν q)) q := by
  unfold streamC streamEval
  split_ifs <;> simp_all [ptOf]

def keyLoNonneg : SkeletonKey → Prop
  | SkeletonKey.velocity _ _ _ lo _ _ _ _ => 0 ≤ lo
  | _ => True

variable {k N : ℕ} {c : FracCellData k N} {x : FieldTuple k}

theorem flux_keyData (hF : FluxStreamStatement) (hx : IsAdmissible c x) (L₀ : CellLayout) (h₀ : L₀.order = c.order)
    (ν : ℝ → ℝ) (key : SkeletonKey) (l : List (SkeletonKey × ℝ)) (hsplit : FluxSplit key l)
    (hlev : keyLevelPos key) (hlo : keyLoNonneg key) (b0 : Fin 2) :
    ptOf b0 (keyData L₀ x ν key) = (l.map (fun p => p.2 * ptOf b0 (keyData L₀ x ν p.1))).sum := by
  cases key with
  | velocity n rad lev lo hi t a d =>
    obtain ⟨hn, ha, _, mid, hlm, hmh, th, D, e, c0, c1, hid, hnorm, huniv⟩ := hsplit
    subst hn
    have hlo' : (0 : ℝ) ≤ lo := hlo
    have hb : ∀ b : Bool, 0 ≤ (if b then mid else lo) ∧ (if b then mid else lo) < (if b then hi else mid) := by
      intro b
      cases b
      · exact ⟨hlo', hlm⟩
      · exact ⟨by simp only [↓reduceIte]; linarith, hmh⟩
    have hrel := huniv (fun q => ptOf b0 (keyData L₀ x ν q)) (by
      intro b
      have hn := hnorm b
      cases rad
      · simp only [Bool.false_eq_true, ↓reduceIte] at ha hn ⊢
        subst ha
        have r := congrArg (ptOf b0) (flux_hgt_rel hF hx L₀ h₀ ν lev _ _ (th b) (c0 b) (c1 b) (hb b).1 (hb b).2 hn)
        rw [ptOf_add, ptOf_ofReal_mul, ptOf_ofReal_mul, ptOf_sub, ptOf_streamC, ptOf_streamC] at r
        exact r
      · simp only [↓reduceIte, add_zero] at ha hn ⊢
        subst ha
        have r := congrArg (ptOf b0) (flux_rad_rel hF hx L₀ h₀ ν lev _ _ (th b) (c0 b) (hlev rfl) (hb b).1 (hb b).2 hn)
        rw [ptOf_ofReal_mul, ptOf_sub, ptOf_streamC, ptOf_streamC] at r
        exact r)
    rw [flux_vel_split hx L₀ h₀ ν 0 rad lev lo mid hi t a d hlev hlm hmh th D e hid]
    simp only [ptOf_sum, ptOf_ofReal_mul]
    exact hrel
  | gradient _ _ _ _ _ _ _ _ => exact hsplit.elim
  | pressure _ _ _ _ _ _ _ => exact hsplit.elim
  | corner _ _ _ => exact hsplit.elim
  | stream _ => exact hsplit.elim
  | private_ => exact hsplit.elim

theorem flux_kinds (key : SkeletonKey) (l : List (SkeletonKey × ℝ)) (h : FluxSplit key l) :
    key ≠ SkeletonKey.private_ ∧ (∀ n p a, key ≠ SkeletonKey.corner n p a) ∧ (∀ v, keyScale v key = 1) ∧
    ∀ q ∈ l, q.1 ≠ SkeletonKey.private_ ∧ (∀ n p a, q.1 ≠ SkeletonKey.corner n p a) ∧ (∀ v, keyScale v q.1 = 1) ∧
      ∀ rad lev lo hi t dd, q.1 ≠ SkeletonKey.pressure 0 rad lev lo hi t dd := by
  cases key with
  | velocity n rad lev lo hi t a d =>
    obtain ⟨_, _, hall, _⟩ := h
    refine ⟨by simp, by simp, fun v => rfl, fun q hq => ?_⟩
    rcases hall q hq with ⟨lo', hi', t', a', d', he⟩ | ⟨qq, he⟩ <;> rw [he] <;>
      exact ⟨by simp, by simp, fun v => rfl, by simp⟩
  | gradient _ _ _ _ _ _ _ _ => exact h.elim
  | pressure _ _ _ _ _ _ _ => exact h.elim
  | corner _ _ _ => exact h.elim
  | stream _ => exact h.elim
  | private_ => exact h.elim

theorem lo_nonneg {α : ℝ} {Sp : CellSplit k N} {M : MeshData k N Sp} (hM : IsMeshData α c Sp M)
    (K : Fin Sp.cellCount) (d : (M.coords K).layout.Datum) : keyLoNonneg (keyOf (M.coords K).layout d) := by
  rcases d with q|q|q|q|q|q|q|q <;> simp only [keyOf, Sum.elim_inl, Sum.elim_inr, keyLoNonneg]
  all_goals first | trivial | exact (hM.segments_nonneg K).1 _

end MeshSkeletonSplitInternal

open MeshSkeletonInternal MeshSkeletonSplitInternal

theorem fluxSplitRow (hS : StreamIndependenceStatement) (hF : FluxStreamStatement) {α : ℝ} {k N : ℕ}
    {c : FracCellData k N} {Sp : CellSplit k N} {M : MeshData k N Sp}
    (hM : IsMeshData α c Sp M) {x : FieldTuple k} (hx : IsAdmissible c x) (K : Fin Sp.cellCount)
    (j : Fin (systemSkeletonCoords (M.coords K).layout (M.coords K).param).card) (parts : List (Fin Sp.slots × ℝ))
    (extra : List ((K' : Fin Sp.cellCount) × (M.coords K').layout.Datum × ℝ))
    (hkap : ∀ p ∈ parts, ∀ a, Sp.kappaSlot a ≠ p.1)
    (hdel : ∀ p ∈ parts, ¬ M.IsDelaySlot p.1)
    (hpart : ∀ p ∈ parts, (M.rowDatum (M.ownerCell p.1) (M.ownerRow p.1)).2 = (M.rowDatum K j).2)
    (hext : ∀ e ∈ extra, (M.coords e.1).layout.IsGaugeDeleted e.2.1)
    (hsplit : FluxSplit (M.rowKey K j) (parts.map (fun p => (M.ownerKey p.1, p.2)) ++ M.extraKeys extra))
    (hnodes : ∀ u ∈ M.participantNodes K j parts ++ M.extraNodes extra,
      ∀ v ∈ M.participantNodes K j parts ++ M.extraNodes extra, u.1 = v.1 → u.2 = v.2) :
    (parts.map (fun p => p.2 * M.canonicalMoment c x p.1)).sum = M.localValue c K x j := by
  classical
  obtain ⟨hrp, hrc, hrs, hq⟩ := flux_kinds _ _ hsplit
  have hex : extra = [] := by
    cases extra with
    | nil => rfl
    | cons e es =>
      exfalso
      have hmem : (keyOf (M.coords e.1).layout e.2.1, e.2.2) ∈
          parts.map (fun p => (M.ownerKey p.1, p.2)) ++ M.extraKeys (e :: es) :=
        List.mem_append_right _ (List.mem_map.2 ⟨e, List.mem_cons_self, rfl⟩)
      obtain ⟨rad, lev, lo, hi, t, dd, hkey⟩ := deleted_key _ (hext e List.mem_cons_self)
      exact (hq _ hmem).2.2.2 rad lev lo hi t dd hkey
  subst hex
  set Ls := M.participantNodes K j parts ++ M.extraNodes [] with hLs
  set ν : ℝ → ℝ := fun r => if h : ∃ u ∈ Ls, u.1 = r then M.classValue x (Classical.choose h).2 else 0
    with hνdef
  have hν : ∀ u ∈ Ls, M.classValue x u.2 = ν u.1 := by
    intro u hu
    have h : ∃ u' ∈ Ls, u'.1 = u.1 := ⟨u, hu, rfl⟩
    rw [hνdef]
    dsimp only
    rw [dif_pos h]
    obtain ⟨h1', h2'⟩ := Classical.choose_spec h
    exact congrArg _ (hnodes u hu _ h1' h2'.symm)
  have glue : ∀ (K' : Fin Sp.cellCount) (d : (M.coords K').layout.Datum), keyOf _ d ≠ SkeletonKey.private_ →
      (∀ n p a, keyOf _ d ≠ SkeletonKey.corner n p a) →
      (∀ u ∈ (pressurePositions (M.coords K').layout d).map (fun q => (q.1, M.nodeClass K' q.2)), u ∈ Ls) →
      (M.coords K').layout.shiftedData
          ((M.coords K').layout.gaugeShiftOf (M.canonicalLeft K') (M.canonicalRight K')) x d
        = keyData (M.coords K).layout x ν (keyOf _ d) := by
    intro K' d hp hcn hin
    refine shifted_key hS hx (hM.same_order K) (layoutValid hM K') (hM.same_gauge K K') _ _ ν d hp hcn ?_
    intro u hu
    rw [side_value]
    exact hν _ (hin _ (List.mem_map.2 ⟨u, hu, rfl⟩))
  set b := (M.rowDatum K j).2 with hb
  set V := keyData (M.coords K).layout x ν with hV
  have hrow : M.localValue c K x j = ptOf b (V (M.rowKey K j)) / keyScale c.splitVisc (M.rowKey K j) := by
    unfold MeshData.localValue
    simp only [CellLayout.realPart]
    rw [glue K _ hrp hrc (fun u hu => List.mem_append_left _ (List.mem_append_left _ hu)), scale_key]
    rfl
  have hown : ∀ p ∈ parts, M.canonicalMoment c x p.1 =
      ptOf b (V (M.ownerKey p.1)) / keyScale c.splitVisc (M.rowKey K j) := by
    intro p hp
    have hnk : ¬ ∃ a, Sp.kappaSlot a = p.1 := fun ⟨a, ha⟩ => hkap p hp a ha
    have hmem : (M.ownerKey p.1, p.2) ∈ parts.map (fun p => (M.ownerKey p.1, p.2)) ++ M.extraKeys [] :=
      List.mem_append_left _ (List.mem_map.2 ⟨p, hp, rfl⟩)
    obtain ⟨hp1, hp2, hp3, _⟩ := hq _ hmem
    unfold MeshData.canonicalMoment
    rw [if_neg (hdel p hp)]
    unfold MeshData.baseMoment
    rw [dif_neg hnk]
    unfold MeshData.localValue
    simp only [CellLayout.realPart]
    rw [glue _ _ hp1 hp2 (fun u hu => List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨p, hp, rfl⟩, hu⟩))), scale_key, hpart p hp]
    have e1 : keyScale c.splitVisc
        (keyOf (M.coords (M.ownerCell p.1)).layout (M.rowDatum (M.ownerCell p.1) (M.ownerRow p.1)).1) = 1 :=
      hp3 c.splitVisc
    rw [e1, hrs c.splitVisc]
    rfl
  have hsum := flux_keyData hF hx (M.coords K).layout (hM.same_order K) ν _ _ hsplit
    (level_pos (layoutValid hM K) _) (lo_nonneg hM K _) b
  simp only [MeshData.extraKeys, List.map_nil, List.append_nil, List.map_map] at hsum
  rw [hrow, List.map_congr_left (fun p hp => by rw [hown p hp]), list_div]
  congr 1
  exact hsum.symm

end Breakdown.CellCert.CellCoordinates
