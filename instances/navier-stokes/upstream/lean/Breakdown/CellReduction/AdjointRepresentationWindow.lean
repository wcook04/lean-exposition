import Breakdown.Cert.Statement

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace RepresentationParts

def windowBump (s : ℝ) : ℝ := Real.smoothTransition (s + 1) - Real.smoothTransition s

def stripCutoff (s : ℝ) : ℝ := Real.smoothTransition (s + 2) * Real.smoothTransition (2 - s)

theorem Internal.transition_contDiff : ContDiff ℝ ∞ Real.smoothTransition :=
  Real.smoothTransition.contDiff (n := ⊤)

theorem Internal.transition_differentiable : Differentiable ℝ Real.smoothTransition :=
  (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)

theorem Internal.deriv_transition_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    deriv Real.smoothTransition x = 0 := by
  refine IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall (fun y => ?_))
  rw [Real.smoothTransition.zero_of_nonpos hx]
  exact Real.smoothTransition.nonneg y

theorem Internal.deriv_transition_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  refine IsLocalMax.deriv_eq_zero (Filter.Eventually.of_forall (fun y => ?_))
  rw [Real.smoothTransition.one_of_one_le hx]
  exact Real.smoothTransition.le_one y

theorem Internal.deriv_eq_zero_off_closed {f : ℝ → ℝ} {K : Set ℝ} (hK : IsClosed K)
    (hf : ∀ x, x ∉ K → f x = 0) {s : ℝ} (hs : s ∉ K) : deriv f s = 0 := by
  have h : f =ᶠ[nhds s] fun _ => (0 : ℝ) :=
    Filter.eventuallyEq_of_mem (hK.isOpen_compl.mem_nhds hs) (fun x hx => hf x hx)
  rw [h.deriv_eq]
  simp

theorem Internal.windowBump_eq_zero_of_le {s : ℝ} (hs : s ≤ -1) : windowBump s = 0 := by
  unfold windowBump
  rw [Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

theorem Internal.windowBump_eq_zero_of_ge {s : ℝ} (hs : 1 ≤ s) : windowBump s = 0 := by
  unfold windowBump
  rw [Real.smoothTransition.one_of_one_le (by linarith), Real.smoothTransition.one_of_one_le hs]
  ring

theorem Internal.windowBump_pair {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    windowBump (u - 1) + windowBump u = 1 := by
  unfold windowBump
  rw [sub_add_cancel, Real.smoothTransition.zero_of_nonpos (by linarith : u - 1 ≤ 0),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ u + 1)]
  ring

theorem Internal.deriv_windowBump (s : ℝ) :
    deriv windowBump s =
      deriv Real.smoothTransition (s + 1) - deriv Real.smoothTransition s := by
  have h1 : HasDerivAt (fun x => Real.smoothTransition (x + 1))
      (deriv Real.smoothTransition (s + 1)) s :=
    HasDerivAt.comp_add_const s 1 (Internal.transition_differentiable (s + 1)).hasDerivAt
  exact (h1.sub (Internal.transition_differentiable s).hasDerivAt).deriv

theorem Internal.deriv_windowBump_eq_zero_of_le {s : ℝ} (hs : s ≤ -1) :
    deriv windowBump s = 0 := by
  rw [Internal.deriv_windowBump, Internal.deriv_transition_of_nonpos (by linarith),
    Internal.deriv_transition_of_nonpos (by linarith)]
  ring

theorem Internal.deriv_windowBump_eq_zero_of_ge {s : ℝ} (hs : 1 ≤ s) :
    deriv windowBump s = 0 := by
  rw [Internal.deriv_windowBump, Internal.deriv_transition_of_one_le (by linarith),
    Internal.deriv_transition_of_one_le hs]
  ring

theorem Internal.deriv_windowBump_pair {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    deriv windowBump (u - 1) + deriv windowBump u = 0 := by
  rw [Internal.deriv_windowBump, Internal.deriv_windowBump, sub_add_cancel,
    Internal.deriv_transition_of_nonpos (by linarith : u - 1 ≤ 0),
    Internal.deriv_transition_of_one_le (by linarith : 1 ≤ u + 1)]
  ring

theorem Internal.not_mem_Ioo_cases {s : ℝ} (hs : s ∉ Set.Ioo (-1 : ℝ) 1) : s ≤ -1 ∨ 1 ≤ s := by
  rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hs
  exact hs

theorem windowBump_contDiff : ContDiff ℝ ∞ windowBump := by
  have h := Internal.transition_contDiff
  have h1 : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (s + 1)) :=
    h.comp (contDiff_id.add contDiff_const)
  exact h1.sub h

theorem windowBump_eq_zero {s : ℝ} (hs : s ∉ Set.Icc (-1 : ℝ) 1) : windowBump s = 0 := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
  rcases hs with hs | hs
  · exact Internal.windowBump_eq_zero_of_le hs.le
  · exact Internal.windowBump_eq_zero_of_ge hs.le

theorem windowBump_hasCompactSupport : HasCompactSupport windowBump :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx => windowBump_eq_zero hx)

theorem deriv_windowBump_eq_zero {s : ℝ} (hs : s ∉ Set.Icc (-1 : ℝ) 1) : deriv windowBump s = 0 :=
  Internal.deriv_eq_zero_off_closed isClosed_Icc (fun _ hx => windowBump_eq_zero hx) hs

theorem abs_windowBump_le (s : ℝ) : |windowBump s| ≤ 1 := by
  unfold windowBump
  have h1 := Real.smoothTransition.monotone (show s ≤ s + 1 by linarith)
  have h2 := Real.smoothTransition.le_one (s + 1)
  have h3 := Real.smoothTransition.nonneg s
  rw [abs_le]
  constructor <;> linarith

theorem Internal.exists_abs_deriv_le_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : ∃ M : ℝ, 0 ≤ M ∧ ∀ s, |deriv f s| ≤ M := by
  obtain ⟨C, hC⟩ := (hf.continuous_deriv (by norm_num)).bounded_above_of_compact_support hs.deriv
  refine ⟨max C 0, le_max_right _ _, fun s => ?_⟩
  have h := hC s
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

theorem exists_abs_deriv_windowBump_le : ∃ M : ℝ, 0 ≤ M ∧ ∀ s, |deriv windowBump s| ≤ M :=
  Internal.exists_abs_deriv_le_of_contDiff windowBump_contDiff windowBump_hasCompactSupport

theorem stripCutoff_contDiff : ContDiff ℝ ∞ stripCutoff := by
  have h := Internal.transition_contDiff
  have h1 : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (s + 2)) :=
    h.comp (contDiff_id.add contDiff_const)
  have h2 : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (2 - s)) :=
    h.comp (contDiff_const.sub contDiff_id)
  exact h1.mul h2

theorem stripCutoff_eq_zero {s : ℝ} (hs : s ∉ Set.Icc (-2 : ℝ) 2) : stripCutoff s = 0 := by
  unfold stripCutoff
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
  rcases hs with hs | hs
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2 - s ≤ 0), mul_zero]

theorem deriv_stripCutoff_eq_zero {s : ℝ} (hs : s ∉ Set.Icc (-2 : ℝ) 2) : deriv stripCutoff s = 0 :=
  Internal.deriv_eq_zero_off_closed isClosed_Icc (fun _ hx => stripCutoff_eq_zero hx) hs

theorem abs_stripCutoff_le (s : ℝ) : |stripCutoff s| ≤ 1 := by
  unfold stripCutoff
  have h1 := Real.smoothTransition.nonneg (s + 2)
  have h2 := Real.smoothTransition.le_one (s + 2)
  have h3 := Real.smoothTransition.nonneg (2 - s)
  have h4 := Real.smoothTransition.le_one (2 - s)
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg h1 h3]

theorem exists_abs_deriv_stripCutoff_le : ∃ M : ℝ, 0 ≤ M ∧ ∀ s, |deriv stripCutoff s| ≤ M :=
  Internal.exists_abs_deriv_le_of_contDiff stripCutoff_contDiff
    (HasCompactSupport.intro isCompact_Icc (fun _ hx => stripCutoff_eq_zero hx))

theorem stripCutoff_mul_windowBump (s : ℝ) : stripCutoff s * windowBump s = windowBump s := by
  by_cases hs : s ∈ Set.Icc (-1 : ℝ) 1
  · unfold stripCutoff
    rw [Real.smoothTransition.one_of_one_le (by linarith [hs.1]),
      Real.smoothTransition.one_of_one_le (by linarith [hs.2]), one_mul, one_mul]
  · rw [windowBump_eq_zero hs, mul_zero]

theorem Internal.integral_mul_periodic {g : ℝ → ℝ} (hg : Continuous g)
    (hz : ∀ s, s ∉ Set.Ioo (-1 : ℝ) 1 → g s = 0) {a : ℝ → ℝ} (ha : ∀ s, a (s + 1) = a s)
    (hi : IntegrableOn a (Set.Icc (0 : ℝ) 1)) :
    ∫ s, g s * a s = ∫ s in (0 : ℝ)..1, (g (s - 1) + g s) * a s := by
  have hI : IntervalIntegrable a volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    exact hi
  have hI' : IntervalIntegrable a volume (-1) 0 := by
    have h := hI.comp_add_right 1
    rw [show (fun x => a (x + 1)) = a from funext ha, zero_sub, sub_self] at h
    exact h
  have hA : IntervalIntegrable (fun s => g s * a s) volume (-1) 0 :=
    hI'.continuousOn_mul hg.continuousOn
  have hB : IntervalIntegrable (fun s => g s * a s) volume 0 1 :=
    hI.continuousOn_mul hg.continuousOn
  have hC : IntervalIntegrable (fun s => g (s - 1) * a s) volume 0 1 :=
    hI.continuousOn_mul (hg.comp (continuous_sub_right 1)).continuousOn
  have hzero : ∫ s, g s * a s = ∫ s in (-1 : ℝ)..1, g s * a s := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)).symm
    rw [hz x (fun h' => hx ⟨h'.1, h'.2.le⟩), zero_mul]
  have hshift : ∫ s in (-1 : ℝ)..0, g s * a s = ∫ s in (0 : ℝ)..1, g (s - 1) * a s := by
    have h := intervalIntegral.integral_comp_sub_right (fun s => g s * a s) (a := 0) (b := 1) 1
    simp only [zero_sub, sub_self] at h
    rw [← h]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    have e := ha (s - 1)
    rw [sub_add_cancel] at e
    simp only [e]
  rw [hzero, ← intervalIntegral.integral_add_adjacent_intervals hA hB, hshift,
    ← intervalIntegral.integral_add hC hB]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  ring

theorem integral_windowBump_mul {a : ℝ → ℝ} (ha : ∀ s, a (s + 1) = a s)
    (hi : IntegrableOn a (Set.Icc (0 : ℝ) 1)) :
    ∫ s, windowBump s * a s = ∫ s in Set.Icc (0 : ℝ) 1, a s := by
  have hz : ∀ s, s ∉ Set.Ioo (-1 : ℝ) 1 → windowBump s = 0 := fun s hs => by
    rcases Internal.not_mem_Ioo_cases hs with h | h
    · exact Internal.windowBump_eq_zero_of_le h
    · exact Internal.windowBump_eq_zero_of_ge h
  rw [Internal.integral_mul_periodic windowBump_contDiff.continuous hz ha hi,
    intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc (fun s hs => ?_)
  rw [Internal.windowBump_pair hs.1 hs.2, one_mul]

theorem integral_deriv_windowBump_mul {a : ℝ → ℝ} (ha : ∀ s, a (s + 1) = a s)
    (hi : IntegrableOn a (Set.Icc (0 : ℝ) 1)) :
    ∫ s, deriv windowBump s * a s = 0 := by
  have hz : ∀ s, s ∉ Set.Ioo (-1 : ℝ) 1 → deriv windowBump s = 0 := fun s hs => by
    rcases Internal.not_mem_Ioo_cases hs with h | h
    · exact Internal.deriv_windowBump_eq_zero_of_le h
    · exact Internal.deriv_windowBump_eq_zero_of_ge h
  rw [Internal.integral_mul_periodic (windowBump_contDiff.continuous_deriv (by norm_num)) hz ha hi]
  have e : ∫ s in (0 : ℝ)..1, (deriv windowBump (s - 1) + deriv windowBump s) * a s =
      ∫ _ in (0 : ℝ)..1, (0 : ℝ) := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hs
    rw [Internal.deriv_windowBump_pair hs.1 hs.2, zero_mul]
  rw [e]
  simp

theorem Internal.setLIntegral_shift {h : ℝ → ℝ≥0∞} (c : ℝ) (hc : ∀ s, h (s + c) = h s) :
    ∫⁻ s in Set.Icc c (c + 1), h s = ∫⁻ s in Set.Icc (0 : ℝ) 1, h s := by
  have hm : MeasurePreserving (fun x : ℝ => x + c) volume volume :=
    measurePreserving_add_right volume c
  have he : MeasurableEmbedding (fun x : ℝ => x + c) :=
    (MeasurableEquiv.addRight c).measurableEmbedding
  have e := hm.setLIntegral_comp_emb he h (Set.Icc (0 : ℝ) 1)
  rw [Set.image_add_const_Icc, zero_add, add_comm 1 c] at e
  rw [← e]
  simp only [hc]

theorem setLIntegral_strip_le {h : ℝ → ℝ≥0∞} (hh : ∀ s, h (s + 1) = h s) :
    ∫⁻ s in Set.Icc (-2 : ℝ) 2, h s ≤ 4 * ∫⁻ s in Set.Icc (0 : ℝ) 1, h s := by
  have hm1 : ∀ s, h (s + -1) = h s := fun s => by
    rw [← hh (s + -1)]
    congr 1
    ring
  have hm2 : ∀ s, h (s + -2) = h s := fun s => by
    rw [← hh (s + -2), show s + -2 + 1 = s + -1 by ring, hm1]
  have h0 : ∀ s, h (s + 0) = h s := fun s => by rw [add_zero]
  have cover : Set.Icc (-2 : ℝ) 2 ⊆ Set.Icc (-2 : ℝ) (-2 + 1) ∪ Set.Icc (-1 : ℝ) (-1 + 1) ∪
      Set.Icc (0 : ℝ) (0 + 1) ∪ Set.Icc (1 : ℝ) (1 + 1) := by
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    simp only [Set.mem_union, Set.mem_Icc]
    rcases le_or_gt x (-1) with h1 | h1
    · exact Or.inl (Or.inl (Or.inl ⟨hx1, by linarith⟩))
    rcases le_or_gt x 0 with h2 | h2
    · exact Or.inl (Or.inl (Or.inr ⟨h1.le, by linarith⟩))
    rcases le_or_gt x 1 with h3 | h3
    · exact Or.inl (Or.inr ⟨h2.le, by linarith⟩)
    · exact Or.inr ⟨h3.le, by linarith⟩
  have e1 := lintegral_union_le (μ := volume) h (Set.Icc (-2 : ℝ) (-2 + 1) ∪ Set.Icc (-1 : ℝ) (-1 + 1) ∪
      Set.Icc (0 : ℝ) (0 + 1)) (Set.Icc (1 : ℝ) (1 + 1))
  have e2 := lintegral_union_le (μ := volume) h (Set.Icc (-2 : ℝ) (-2 + 1) ∪ Set.Icc (-1 : ℝ) (-1 + 1))
    (Set.Icc (0 : ℝ) (0 + 1))
  have e3 := lintegral_union_le (μ := volume) h (Set.Icc (-2 : ℝ) (-2 + 1)) (Set.Icc (-1 : ℝ) (-1 + 1))
  rw [Internal.setLIntegral_shift 1 hh] at e1
  rw [Internal.setLIntegral_shift 0 h0] at e2
  rw [Internal.setLIntegral_shift (-2) hm2, Internal.setLIntegral_shift (-1) hm1] at e3
  exact (lintegral_mono_set cover).trans (e1.trans ((add_le_add (e2.trans
    (add_le_add e3 le_rfl)) le_rfl).trans (le_of_eq (by ring))))

end RepresentationParts

end Breakdown
