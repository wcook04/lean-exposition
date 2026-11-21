import Breakdown.CertCell.RowsMatchKeyRows
import Breakdown.CertCell.GaugePlaneFlipFacts
import Breakdown.FracCell.MeshDataAffineModes
import Breakdown.FracCell.MeshSkeletonSplit
import Breakdown.CertCell.LocalModeIntegrable

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus CellCert.CellCoordinates LocalField

variable {k : ℕ} {C : Type} {nE nM : ℕ}

namespace Internal.KeySplit

open CellCert.CellCoordinates.MeshSkeletonSplitInternal

def stripJ (wt : ℝ → ℝ) (F dFr dFz : ℝ × ℝ → ℂ) (rad : Bool) (lev a b : ℝ) (f : ℝ → ℝ) : ℂ :=
  if rad then radialStripMoment lev (lev + 1) a b F dFr f else heightStripMoment lev (lev + 1) a b wt F dFz f

theorem moment_eq (w : Bool) (F dFr dFz : ℝ × ℝ → ℂ) (rad : Bool) (lev lo hi : ℝ) (t : ℕ → ℕ → ℝ) (d : ℕ) :
    (keySeg rad lev lo hi t).moment w F dFr dFz d
      = stripJ (fun r => if w then r else 1) F dFr dFz rad lev lo hi ((keySeg rad lev lo hi t).test d) := rfl

theorem test_cont (rad : Bool) (lev lo hi : ℝ) (t : ℕ → ℕ → ℝ) (d : ℕ) :
    Continuous ((keySeg rad lev lo hi t).test d) := by
  unfold FaceSegment.test
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_pow i))

def StripInt (wt : ℝ → ℝ) (F dFr dFz : ℝ × ℝ → ℂ) (rad : Bool) (lev lo : ℝ) : Prop :=
  ∀ a b : ℝ, lo ≤ a →
    (rad = true → IntegrableOn F (Icc lev (lev + 1) ×ˢ Icc a b) ∧ IntegrableOn dFr (Icc lev (lev + 1) ×ˢ Icc a b)) ∧
    (rad = false → IntegrableOn (fun p : ℝ × ℝ => (wt p.1 : ℂ) * F p) (Icc a b ×ˢ Icc lev (lev + 1)) ∧
      IntegrableOn (fun p : ℝ × ℝ => (wt p.1 : ℂ) * dFz p) (Icc a b ×ˢ Icc lev (lev + 1)))

theorem min_max_succ (lev : ℝ) : min lev (lev + 1) = lev ∧ max lev (lev + 1) = lev + 1 :=
  ⟨min_eq_left (by linarith), max_eq_right (by linarith)⟩

theorem radial_term_int {F dF : ℝ × ℝ → ℂ} {lev a b : ℝ}
    (hF : IntegrableOn F (Icc lev (lev + 1) ×ˢ Icc a b)) (hdF : IntegrableOn dF (Icc lev (lev + 1) ×ˢ Icc a b))
    {f : ℝ → ℝ} (hf : Continuous f) :
    IntegrableOn (radialStripTerm lev (lev + 1) F dF f)
      (Icc (min lev (lev + 1)) (max lev (lev + 1)) ×ˢ Icc a b) := by
  rw [(min_max_succ lev).1, (min_max_succ lev).2]
  have hS : IsCompact (Icc lev (lev + 1) ×ˢ Icc a b) := isCompact_Icc.prod isCompact_Icc
  have h1 : IntegrableOn (fun p : ℝ × ℝ => (((1 / (lev - (lev + 1)) : ℝ)) : ℂ) * F p
      + (((p.1 - (lev + 1)) / (lev - (lev + 1)) : ℝ) : ℂ) * dF p) (Icc lev (lev + 1) ×ˢ Icc a b) :=
    Integrable.add (Integrable.const_mul hF _) (IntegrableOn.continuousOn_mul (by fun_prop) hdF hS)
  exact h1.mul_continuousOn (by fun_prop) hS

theorem height_term_int {wt : ℝ → ℝ} {F dF : ℝ × ℝ → ℂ} {lev a b : ℝ}
    (hF : IntegrableOn (fun p : ℝ × ℝ => (wt p.1 : ℂ) * F p) (Icc a b ×ˢ Icc lev (lev + 1)))
    (hdF : IntegrableOn (fun p : ℝ × ℝ => (wt p.1 : ℂ) * dF p) (Icc a b ×ˢ Icc lev (lev + 1)))
    {f : ℝ → ℝ} (hf : Continuous f) :
    IntegrableOn (heightStripTerm lev (lev + 1) wt F dF f)
      (Icc a b ×ˢ Icc (min lev (lev + 1)) (max lev (lev + 1))) := by
  rw [(min_max_succ lev).1, (min_max_succ lev).2, height_term_eq]
  have hS : IsCompact (Icc a b ×ˢ Icc lev (lev + 1)) := isCompact_Icc.prod isCompact_Icc
  have h1 : IntegrableOn (fun p : ℝ × ℝ => (((1 / (lev - (lev + 1)) : ℝ)) : ℂ) * ((wt p.1 : ℂ) * F p)
      + (((p.2 - (lev + 1)) / (lev - (lev + 1)) : ℝ) : ℂ) * ((wt p.1 : ℂ) * dF p))
      (Icc a b ×ˢ Icc lev (lev + 1)) :=
    Integrable.add (Integrable.const_mul hF _) (IntegrableOn.continuousOn_mul (by fun_prop) hdF hS)
  exact h1.mul_continuousOn (by fun_prop) hS

section Strip

variable {wt : ℝ → ℝ} {F dFr dFz : ℝ × ℝ → ℂ} {rad : Bool} {lev lo : ℝ}

theorem term_int (hI : StripInt wt F dFr dFz rad lev lo) (a b : ℝ) (ha : lo ≤ a) {f : ℝ → ℝ}
    (hf : Continuous f) :
    (rad = true → IntegrableOn (radialStripTerm lev (lev + 1) F dFr f)
      (Icc (min lev (lev + 1)) (max lev (lev + 1)) ×ˢ Icc a b)) ∧
    (rad = false → IntegrableOn (heightStripTerm lev (lev + 1) wt F dFz f)
      (Icc a b ×ˢ Icc (min lev (lev + 1)) (max lev (lev + 1)))) :=
  ⟨fun h => radial_term_int ((hI a b ha).1 h).1 ((hI a b ha).1 h).2 hf,
    fun h => height_term_int ((hI a b ha).2 h).1 ((hI a b ha).2 h).2 hf⟩

theorem stripJ_add (hI : StripInt wt F dFr dFz rad lev lo) {a m b : ℝ} (ha : lo ≤ a) (h1 : a ≤ m) (h2 : m ≤ b)
    {f : ℝ → ℝ} (hf : Continuous f) :
    stripJ wt F dFr dFz rad lev a b f = stripJ wt F dFr dFz rad lev a m f + stripJ wt F dFr dFz rad lev m b f := by
  have hi := term_int hI a b ha hf
  cases rad
  · simp only [stripJ, Bool.false_eq_true, ↓reduceIte]
    rw [hsm_eq, hsm_eq, hsm_eq, prod_split_left _ measurableSet_Icc h1 h2 _ (hi.2 rfl), mul_add]
  · simp only [stripJ, ↓reduceIte]
    rw [rsm_eq, rsm_eq, rsm_eq, prod_split_right _ measurableSet_Icc h1 h2 _ (hi.1 rfl), mul_add]

theorem stripJ_lin (hI : StripInt wt F dFr dFz rad lev lo) (a b : ℝ) (ha : lo ≤ a) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    stripJ wt F dFr dFz rad lev a b (fun s => f s + g s)
      = stripJ wt F dFr dFz rad lev a b f + stripJ wt F dFr dFz rad lev a b g := by
  have hif := term_int hI a b ha hf
  have hig := term_int hI a b ha hg
  cases rad
  · simp only [stripJ, Bool.false_eq_true, ↓reduceIte]
    rw [hsm_eq, hsm_eq, hsm_eq, ← mul_add, ← integral_add (hif.2 rfl) (hig.2 rfl)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    simp only [heightStripTerm]
    push_cast
    ring
  · simp only [stripJ, ↓reduceIte]
    rw [rsm_eq, rsm_eq, rsm_eq, ← mul_add, ← integral_add (hif.1 rfl) (hig.1 rfl)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    simp only [radialStripTerm]
    push_cast
    ring

end Strip

theorem stripJ_smul (wt : ℝ → ℝ) (F dFr dFz : ℝ × ℝ → ℂ) (rad : Bool) (lev a b w : ℝ) (f : ℝ → ℝ) :
    stripJ wt F dFr dFz rad lev a b (fun s => w * f s) = (w : ℂ) * stripJ wt F dFr dFz rad lev a b f := by
  cases rad <;> simp only [stripJ, Bool.false_eq_true, ↓reduceIte]
  · exact hsm_smul _ _ _ _ _ _ _ _ _
  · exact rsm_smul _ _ _ _ _ _ _ _

theorem tile_sum (J : ℝ → ℝ → ℂ) {lo hi : ℝ} (hadd : ∀ a m b, lo ≤ a → a ≤ m → m ≤ b → J a b = J a m + J m b)
    {N : ℕ} (tlo thi : Fin N → ℝ) (hN : 0 < N) (hlt : ∀ j, tlo j < thi j)
    (hadj : ∀ j j' : Fin N, j.val + 1 = j'.val → thi j = tlo j')
    (hfirst : ∀ j : Fin N, j.val = 0 → tlo j = lo) (hlast : ∀ j : Fin N, j.val + 1 = N → thi j = hi) :
    J lo hi = ∑ j, J (tlo j) (thi j) ∧ ∀ j, lo ≤ tlo j := by
  set x : ℕ → ℝ := fun i => if h : i < N then tlo ⟨i, h⟩ else hi with hx
  have hx0 : x 0 = lo := by
    simp only [hx, dif_pos hN]
    exact hfirst _ rfl
  have hxt : ∀ i (h : i < N), tlo ⟨i, h⟩ = x i := by
    intro i h
    simp only [hx, dif_pos h]
  have hxs : ∀ i (h : i < N), thi ⟨i, h⟩ = x (i + 1) := by
    intro i h
    by_cases h' : i + 1 < N
    · simp only [hx, dif_pos h']
      exact hadj _ _ rfl
    · have e : i + 1 = N := by omega
      simp only [hx, dif_neg h']
      exact hlast _ e
  have key : ∀ m, m ≤ N → lo ≤ x m ∧ J lo (x m) = ∑ i ∈ Finset.range m, J (x i) (x (i + 1)) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨hx0.ge, ?_⟩
      rw [hx0, Finset.sum_range_zero]
      have h := hadd lo lo lo le_rfl le_rfl le_rfl
      linear_combination -h
    | succ m ih =>
      intro hm
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hlt' : x m < x (m + 1) := by
        rw [← hxt m (by omega), ← hxs m (by omega)]
        exact hlt _
      refine ⟨h1.trans hlt'.le, ?_⟩
      rw [Finset.sum_range_succ, ← h2]
      exact hadd _ _ _ le_rfl h1 hlt'.le
  have hxn : x N = hi := by simp [hx]
  refine ⟨?_, fun j => ?_⟩
  · rw [← hxn, (key N le_rfl).2, ← Fin.sum_univ_eq_sum_range (fun i => J (x i) (x (i + 1)))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← hxt j.val j.isLt, ← hxs j.val j.isLt]
  · have h := (key j.val j.isLt.le).1
    rwa [← hxt j.val j.isLt] at h

theorem tile_expand (J : ℝ → ℝ → (ℝ → ℝ) → ℂ) {lo hi : ℝ}
    (hadd : ∀ a m b, lo ≤ a → a ≤ m → m ≤ b → ∀ f, Continuous f → J a b f = J a m f + J m b f)
    (hlin : ∀ a b, lo ≤ a → ∀ f g, Continuous f → Continuous g → J a b (fun s => f s + g s) = J a b f + J a b g)
    (hsmul : ∀ a b (w : ℝ) f, J a b (fun s => w * f s) = (w : ℂ) * J a b f)
    {N : ℕ} (tlo thi : Fin N → ℝ) (hN : 0 < N) (hlt : ∀ j, tlo j < thi j)
    (hadj : ∀ j j' : Fin N, j.val + 1 = j'.val → thi j = tlo j')
    (hfirst : ∀ j : Fin N, j.val = 0 → tlo j = lo) (hlast : ∀ j : Fin N, j.val + 1 = N → thi j = hi)
    (T : ℝ → ℝ) (hT : Continuous T) (tdeg : ℕ) (coef : Fin N → ℕ → ℝ) (g : Fin N → ℕ → ℝ → ℝ)
    (hg : ∀ j i, Continuous (g j i)) (hid : ∀ j s, T s = ∑ i ∈ Finset.range (tdeg + 1), coef j i * g j i s) :
    J lo hi T = ∑ j, ∑ i ∈ Finset.range (tdeg + 1), (coef j i : ℂ) * J (tlo j) (thi j) (g j i) := by
  obtain ⟨hs, hle⟩ := tile_sum (fun a b => J a b T) (fun a m b ha h1 h2 => hadd a m b ha h1 h2 T hT)
    tlo thi hN hlt hadj hfirst hlast
  have hs' : J lo hi T = ∑ j, J (tlo j) (thi j) T := hs
  rw [hs']
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hT' : T = fun s => ∑ i ∈ Finset.range (tdeg + 1), coef j i * g j i s := funext (hid j)
  rw [hT']
  exact fin_lin (J (tlo j) (thi j)) (hlin _ _ (hle j)) (hsmul _ _) (coef j) (g j) (hg j) tdeg

theorem strip_split {wt : ℝ → ℝ} {F dFr dFz : ℝ × ℝ → ℂ} {rad : Bool} {lev lo hi : ℝ}
    (hI : StripInt wt F dFr dFz rad lev lo) (t : ℕ → ℕ → ℝ) (deg : ℕ)
    {N : ℕ} (tlo thi : Fin N → ℝ) (ttest : Fin N → ℕ → ℕ → ℝ) (tdeg : ℕ) (coef : Fin N → ℕ → ℝ)
    (hN : 0 < N) (hlt : ∀ j, tlo j < thi j) (hadj : ∀ j j' : Fin N, j.val + 1 = j'.val → thi j = tlo j')
    (hfirst : ∀ j : Fin N, j.val = 0 → tlo j = lo) (hlast : ∀ j : Fin N, j.val + 1 = N → thi j = hi)
    (htest : ∀ j (s : ℝ), (keySeg rad lev lo hi t).test deg s
        = ∑ i ∈ Finset.range (tdeg + 1), coef j i * (keySeg rad lev (tlo j) (thi j) (ttest j)).test i s) :
    stripJ wt F dFr dFz rad lev lo hi ((keySeg rad lev lo hi t).test deg)
      = ∑ j, ∑ i ∈ Finset.range (tdeg + 1), (coef j i : ℂ) *
          stripJ wt F dFr dFz rad lev (tlo j) (thi j) ((keySeg rad lev (tlo j) (thi j) (ttest j)).test i) :=
  tile_expand (stripJ wt F dFr dFz rad lev) (fun _ _ _ ha h1 h2 _ hf => stripJ_add hI ha h1 h2 hf)
    (fun a b ha f g hf hg => stripJ_lin hI a b ha f g hf hg) (fun a b w f => stripJ_smul wt F dFr dFz rad lev a b w f)
    tlo thi hN hlt hadj hfirst hlast _ (test_cont _ _ _ _ _ _) tdeg coef _
    (fun _ _ => test_cont _ _ _ _ _ _) htest

theorem unweight {f : ℝ × ℝ → ℂ} {δ R z₁ z₂ : ℝ} (hδ : 0 < δ)
    (h : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * f p) (Icc δ R ×ˢ Icc z₁ z₂)) :
    IntegrableOn f (Icc δ R ×ˢ Icc z₁ z₂) := by
  have hS : IsCompact (Icc δ R ×ˢ Icc z₁ z₂) := isCompact_Icc.prod isCompact_Icc
  have hc : ContinuousOn (fun p : ℝ × ℝ => ((p.1 : ℂ))⁻¹) (Icc δ R ×ˢ Icc z₁ z₂) := by
    refine ContinuousOn.inv₀ (by fun_prop) (fun p hp => ?_)
    exact Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le hδ hp.1.1).ne'
  refine (IntegrableOn.continuousOn_mul hc h hS).congr_fun (fun p hp => ?_)
    (measurableSet_Icc.prod measurableSet_Icc)
  have hne : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le hδ hp.1.1).ne'
  simp only
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

theorem third_weighted {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hm : AEStronglyMeasurable H volume)
    (h2 : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2))
    (m : ℕ) (n : ℤ) (a b c : Fin 3) {r₁ r₂ z₁ z₂ : ℝ} (hr : 0 ≤ r₁) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeThird m n H a b c p) (Icc r₁ r₂ ×ˢ Icc z₁ z₂) := by
  have h := FracInternal.MeshDataAffineModes.weighted_strip (FracInternal.MeshDataAffineModes.second_locInt hm h2) _
    (FracInternal.MeshDataAffineModes.thirdKernel_cont m n a b c)
    (FracInternal.MeshDataAffineModes.thirdKernel_bound m n a b c)
    (FracInternal.MeshDataAffineModes.thirdKernel_per m n a b c) (|r₂| + |z₁| + |z₂|)
  refine h.mono_set ?_
  rintro ⟨r, z⟩ ⟨⟨h1, h3⟩, h4, h5⟩
  refine ⟨⟨hr.trans h1, ?_⟩, ?_, ?_⟩
  · linarith [le_abs_self r₂, abs_nonneg z₁, abs_nonneg z₂]
  · linarith [neg_abs_le z₁, abs_nonneg r₂, abs_nonneg z₂]
  · linarith [le_abs_self z₂, abs_nonneg r₂, abs_nonneg z₁]

variable (L : CellLayout) {j : ℕ} (x : CellCert.Assembly.FieldTuple j)

theorem vel_int (hs : IsLocalSecondOrderField x.1 x.2.1 x.2.2.1) (m : ℤ) (a : Fin 3) (rad : Bool) (lev lo : ℝ)
    (hpos : if rad then 0 < lev else 0 ≤ lo) :
    StripInt (fun _ => 1) (L.velMode m x a) (L.gradModeOf m x a 0) (L.gradModeOf m x a 2) rad lev lo := by
  intro a' b' ha
  have hst := fun R z₁ z₂ => localModeStripIntegrable L.order x.1 x.2.1 x.2.2.1 hs m R z₁ z₂
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · subst hr
    have hlev : 0 < lev := by simpa using hpos
    have hsub : Icc lev (lev + 1) ×ˢ Icc a' b' ⊆ Icc 0 (lev + 1) ×ˢ Icc a' b' :=
      prod_mono (Icc_subset_Icc hlev.le le_rfl) le_rfl
    exact ⟨((hst (lev + 1) a' b').1 a).mono_set hsub, ((hst (lev + 1) a' b').2 a 0).mono_set hsub⟩
  · subst hr
    have hlo : 0 ≤ lo := by simpa using hpos
    have hsub : Icc a' b' ×ˢ Icc lev (lev + 1) ⊆ Icc 0 b' ×ˢ Icc lev (lev + 1) :=
      prod_mono (Icc_subset_Icc (hlo.trans ha) le_rfl) le_rfl
    simp only [Complex.ofReal_one, one_mul]
    exact ⟨((hst b' lev (lev + 1)).1 a).mono_set hsub, ((hst b' lev (lev + 1)).2 a 2).mono_set hsub⟩

theorem grad_radial_int (hs : IsLocalSecondOrderField x.1 x.2.1 x.2.2.1) (m : ℤ) (a : Fin 3) (lev lo : ℝ)
    (hlev : 0 < lev) :
    StripInt (fun r => r) (L.gradModeOf m x a 0) (L.secondModeOf m x a 0 0) (L.secondModeOf m x a 0 2)
      true lev lo := by
  intro a' b' _
  refine ⟨fun _ => ?_, fun h => by cases h⟩
  have hsub : Icc lev (lev + 1) ×ˢ Icc a' b' ⊆ Icc 0 (lev + 1) ×ˢ Icc a' b' :=
    prod_mono (Icc_subset_Icc hlev.le le_rfl) le_rfl
  exact ⟨((localModeStripIntegrable L.order x.1 x.2.1 x.2.2.1 hs m (lev + 1) a' b').2 a 0).mono_set hsub,
    unweight hlev (third_weighted hs.measurable_second hs.second_two L.order m a 0 0 hlev.le)⟩

theorem grad_height_int (hs : IsLocalSecondOrderField x.1 x.2.1 x.2.2.1) (m : ℤ) (a : Fin 3) (lev lo : ℝ)
    (hlo : 0 ≤ lo) :
    StripInt (fun r => r) (L.gradModeOf m x a 2) (L.secondModeOf m x a 2 0) (L.secondModeOf m x a 2 2)
      false lev lo := by
  intro a' b' ha
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  have ha0 : 0 ≤ a' := hlo.trans ha
  have hsub : Icc a' b' ×ˢ Icc lev (lev + 1) ⊆ Icc 0 b' ×ˢ Icc lev (lev + 1) :=
    prod_mono (Icc_subset_Icc ha0 le_rfl) le_rfl
  have hS : IsCompact (Icc a' b' ×ˢ Icc lev (lev + 1)) := isCompact_Icc.prod isCompact_Icc
  exact ⟨IntegrableOn.continuousOn_mul (by fun_prop)
      (((localModeStripIntegrable L.order x.1 x.2.1 x.2.2.1 hs m b' lev (lev + 1)).2 a 2).mono_set hsub) hS,
    third_weighted hs.measurable_second hs.second_two L.order m a 2 2 ha0⟩

theorem pres_radial_int (hQ : SteadyCert.IsGradientField x.2.2.2.2) (m : ℤ) (lev lo : ℝ) (hlev : 0 < lev) :
    StripInt (fun r => r) (headPressure L m x) (L.pressureGradMode m x 0) (L.pressureGradMode m x 2)
      true lev lo := by
  intro a' b' _
  refine ⟨fun _ => ?_, fun h => by cases h⟩
  have hg := CellCert.CellFormula.MeshDataAffineModes.gradient_modes_integrable L.order x.2.2.2.2 hQ m
    (⨍ z in Metric.ball (0 : Space) 1, potentialOf x.2.2.2.2 z) lev (lev + 1) a' b'
  exact ⟨hg.1, unweight hlev (hg.2 0)⟩

theorem pres_height_int (hQ : SteadyCert.IsGradientField x.2.2.2.2) (m : ℤ) (lev lo : ℝ) :
    StripInt (fun r => r) (headPressure L m x) (L.pressureGradMode m x 0) (L.pressureGradMode m x 2)
      false lev lo := by
  intro a' b' _
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  have hS : IsCompact (Icc a' b' ×ˢ Icc lev (lev + 1)) := isCompact_Icc.prod isCompact_Icc
  have hg := CellCert.CellFormula.MeshDataAffineModes.gradient_modes_integrable L.order x.2.2.2.2 hQ m
    (⨍ z in Metric.ball (0 : Space) 1, potentialOf x.2.2.2.2 z) a' b' lev (lev + 1)
  exact ⟨IntegrableOn.continuousOn_mul (by fun_prop) hg.1 hS, hg.2 2⟩

theorem keyValue_split (hs : IsLocalSecondOrderField x.1 x.2.1 x.2.2.1) (hQ : SteadyCert.IsGradientField x.2.2.2.2)
    (key : SkeletonKey) (rad : Bool) (lev lo hi : ℝ) (t : ℕ → ℕ → ℝ) (deg : ℕ)
    (hgeom : sideKeyGeom key = some (rad, lev, lo, hi, t, deg)) (hhalf : GaugeKey.KeyInHalfPlane key)
    {N : ℕ} (tlo thi : Fin N → ℝ) (ttest : Fin N → ℕ → ℕ → ℝ) (tdeg : ℕ) (coef : Fin N → ℕ → ℝ)
    (hN : 0 < N) (hlt : ∀ j, tlo j < thi j) (hadj : ∀ j j' : Fin N, j.val + 1 = j'.val → thi j = tlo j')
    (hfirst : ∀ j : Fin N, j.val = 0 → tlo j = lo) (hlast : ∀ j : Fin N, j.val + 1 = N → thi j = hi)
    (htest : ∀ j (s : ℝ), (keySeg rad lev lo hi t).test deg s
        = ∑ i ∈ Finset.range (tdeg + 1), coef j i * (keySeg rad lev (tlo j) (thi j) (ttest j)).test i s) :
    keyValue L x key = ∑ j, ∑ i ∈ Finset.range (tdeg + 1),
      (coef j i : ℂ) * keyValue L x (retileKey (tlo j) (thi j) (ttest j) i key) := by
  cases key with
  | velocity n r l lo' hi' t' a d =>
    simp only [sideKeyGeom, Option.some.injEq, Prod.mk.injEq] at hgeom
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hgeom
    simp only [keyValue, retileKey]
    exact strip_split (vel_int L x hs n a r l lo' hhalf) t' d tlo thi ttest tdeg coef hN hlt hadj hfirst
      hlast htest
  | gradient n r l lo' hi' t' a d =>
    simp only [sideKeyGeom, Option.some.injEq, Prod.mk.injEq] at hgeom
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hgeom
    cases r
    · have hlo : 0 ≤ lo' := by simpa [GaugeKey.KeyInHalfPlane] using hhalf
      simp only [keyValue, retileKey, Bool.false_eq_true, ↓reduceIte]
      exact strip_split (grad_height_int L x hs n a l lo' hlo) t' d tlo thi ttest tdeg coef hN hlt hadj
        hfirst hlast htest
    · have hlev : 0 < l := by simpa [GaugeKey.KeyInHalfPlane] using hhalf
      simp only [keyValue, retileKey, ↓reduceIte]
      exact strip_split (grad_radial_int L x hs n a l lo' hlev) t' d tlo thi ttest tdeg coef hN hlt hadj
        hfirst hlast htest
  | pressure n r l lo' hi' t' d =>
    simp only [sideKeyGeom, Option.some.injEq, Prod.mk.injEq] at hgeom
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hgeom
    simp only [keyValue, retileKey]
    cases r
    · exact strip_split (pres_height_int L x hQ n l lo') t' d tlo thi ttest tdeg coef hN hlt hadj
        hfirst hlast htest
    · have hlev : 0 < l := by simpa [GaugeKey.KeyInHalfPlane] using hhalf
      exact strip_split (pres_radial_int L x hQ n l lo' hlev) t' d tlo thi ttest tdeg coef hN hlt hadj
        hfirst hlast htest
  | corner _ _ _ => simp [sideKeyGeom] at hgeom
  | stream _ => simp [sideKeyGeom] at hgeom
  | private_ => simp [sideKeyGeom] at hgeom

end Internal.KeySplit

theorem keySplitAdditive_of_lift (hP : PlaneFlipFacts.PeriodicSecondOrderHolds) (hL : HarmonicLiftStatement)
    (D : CellLayerData k C nE nM) (L : CellLayout) : KeySplitAdditive D L := by
  intro q v G H g Pg hfh ν key rad lev lo hi t deg hgeom hhalf n tlo thi ttest tdeg coef hn hlt hadj hfirst
    hlast htest
  obtain ⟨hc, hs, -⟩ := hL 0 v G H (hP _ _ v G H g hfh.2.2.1) ν
  have hPg := hfh.2.2.2.1
  have ec := Internal.KeySplit.keyValue_split L (cosTuple ν v G H Pg) hc (hPg.harmonic_gradient ν).1 key rad lev
    lo hi t deg hgeom hhalf tlo thi ttest tdeg coef hn hlt hadj hfirst hlast htest
  have es := Internal.KeySplit.keyValue_split L (sinTuple ν v G H Pg) hs (hPg.harmonic_gradient ν).2 key rad lev
    lo hi t deg hgeom hhalf tlo thi ttest tdeg coef hn hlt hadj hfirst hlast htest
  unfold keyHarmonic
  rw [ec, es, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

end Assembly

end CertCell

end Breakdown
