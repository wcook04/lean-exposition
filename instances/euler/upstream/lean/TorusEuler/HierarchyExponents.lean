import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
The exponents in `cc:uf:hier:eq:Vbound` through `cc:uf:hier:eq:Cbound`,
the induction in `cc:uf:hier:eq:induction`, and a finite-sum model of the
partition and tail in `cc:uf:hier:prop:identity`.
-/

namespace TorusEuler

/-- Exponent for the oscillation and transverse source at level `p`. -/
noncomputable def hierarchyOscExponent (p : ℕ) : ℝ := -5 / 4 - 2 * ((p : ℝ) - 1) / 3

/-- Exponent for the mean and its source at level `p ≥ 2`. -/
noncomputable def hierarchyMeanExponent (p : ℕ) : ℝ := -5 / 2 - 2 * ((p : ℝ) - 2) / 3

/-- Exponent for the divergence correction to a level-`p` oscillation. -/
noncomputable def hierarchyCompletionExponent (p : ℕ) : ℝ := hierarchyOscExponent p - 1

/-- Mean exponent used in the induction without a parent-scale factor. -/
noncomputable def hierarchyInductiveMeanExponent (p : ℕ) : ℝ := hierarchyOscExponent p - 1 / 2

theorem hierarchyOscExponent_antitone : Antitone hierarchyOscExponent := by
  intro i j hij
  have h : (i : ℝ) ≤ j := by exact_mod_cast hij
  unfold hierarchyOscExponent
  linarith

theorem hierarchy_completion_previous {p : ℕ} (hp : 1 ≤ p) :
    hierarchyCompletionExponent (p - 1) = hierarchyOscExponent p - 1 / 3 := by
  unfold hierarchyCompletionExponent hierarchyOscExponent
  rw [Nat.cast_sub hp]
  norm_num
  ring

theorem hierarchy_mean_inductive_shift (p : ℕ) :
    hierarchyMeanExponent p + 1 / 12 = hierarchyInductiveMeanExponent p := by
  unfold hierarchyMeanExponent hierarchyInductiveMeanExponent hierarchyOscExponent
  ring

theorem hierarchy_label_product_exponent (i j : ℕ) :
    hierarchyOscExponent i + hierarchyOscExponent j =
      hierarchyMeanExponent (i + j) ∧
    hierarchyOscExponent i + hierarchyOscExponent j =
      hierarchyOscExponent (i + j) - 7 / 12 := by
  unfold hierarchyMeanExponent hierarchyOscExponent
  push_cast
  constructor <;> ring

theorem hierarchy_mean_product_exponent (i j : ℕ) :
    hierarchyInductiveMeanExponent i + hierarchyInductiveMeanExponent j =
      hierarchyMeanExponent (i + j) - 1 := by
  unfold hierarchyInductiveMeanExponent hierarchyMeanExponent hierarchyOscExponent
  push_cast
  ring

/-- The phase derivative of the correction has the smallest spare exponent. -/
theorem hierarchy_fast_completion_exponent {i j p : ℕ} (hi : 1 ≤ i) (hij : i + j = p + 1) :
    3 / 2 + hierarchyCompletionExponent (i - 1) + hierarchyOscExponent j =
      hierarchyOscExponent p - 1 / 12 := by
  have h : (i : ℝ) + j = p + 1 := by exact_mod_cast hij
  unfold hierarchyCompletionExponent hierarchyOscExponent
  rw [Nat.cast_sub hi]
  norm_num
  linarith

/-- The term (B_i) in the supplemental transverse source may have the
same level as the source when (j=1). -/
theorem hierarchy_fast_mean_exponent {i j p : ℕ} (hij : i + j = p + 1) :
    3 / 2 + hierarchyInductiveMeanExponent i + hierarchyOscExponent j =
      hierarchyOscExponent p - 1 / 4 := by
  have h : (i : ℝ) + j = p + 1 := by exact_mod_cast hij
  unfold hierarchyInductiveMeanExponent hierarchyOscExponent
  linarith

/-- Absorb the bounded number of parent-scale factors in each term.
Here `loss` stands for the factor `D^C` in the induction hypothesis. -/
theorem hierarchy_absorb_parent_loss {freq loss exponent spare : ℝ}
    (hfreq : 1 ≤ freq) (hloss : 0 ≤ loss)
    (hsmall : loss * freq ^ (-1 / 12 : ℝ) ≤ 1) (hspare : 1 / 12 ≤ spare) :
    loss * freq ^ (exponent - spare) ≤ freq ^ exponent := by
  have hf : 0 < freq := zero_lt_one.trans_le hfreq
  calc
    _ ≤ loss * freq ^ (exponent - 1 / 12) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hfreq (by linarith)) hloss
    _ = (loss * freq ^ (-1 / 12 : ℝ)) * freq ^ exponent := by
      rw [show exponent - 1 / 12 = (-1 / 12 : ℝ) + exponent by ring, Real.rpow_add hf]
      ring
    _ ≤ _ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hf.le _)

/-- The positive index pairs at depth `P`. Phase advection uses `shift=1`
and omits the zero first inputs `C₀` and `B₁`. Label advection uses
`shift=0`. -/
def hierarchyAdvectionPairs (P shift : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc (shift + 1) (P + 1)).product (Finset.Icc 1 (P + 1))

/-- A quadratic interaction loses one level when it differentiates the
phase and loses zero levels when it differentiates the labels. -/
def hierarchyAdvectionLevel (shift : ℕ) (ij : ℕ × ℕ) : ℕ := ij.1 + ij.2 - shift

theorem hierarchyAdvectionLevel_at_least_two {P shift : ℕ} {ij : ℕ × ℕ}
    (hij : ij ∈ hierarchyAdvectionPairs P shift) :
    2 ≤ hierarchyAdvectionLevel shift ij := by
  have hi := (Finset.mem_product (s := Finset.Icc (shift + 1) (P + 1))
    (t := Finset.Icc 1 (P + 1))).1 hij
  rw [Finset.mem_Icc, Finset.mem_Icc] at hi
  unfold hierarchyAdvectionLevel
  omega

/-- Interactions strictly above the retained hierarchy depth. -/
def hierarchyTailPairs (P shift : ℕ) : Finset (ℕ × ℕ) :=
  (hierarchyAdvectionPairs P shift).filter fun ij => P + shift < ij.1 + ij.2

/-- The diagonal filtration of the two quadratic sums in
`cc:uf:hier:eq:tail`. The tail condition becomes `i+j ≥ P+1` for label
advection and `i+j ≥ P+2` for phase advection. -/
theorem hierarchy_advection_filtration {E : Type*} [AddCommMonoid E]
    (P shift : ℕ) (a : ℕ × ℕ → E) :
    (∑ ij ∈ hierarchyAdvectionPairs P shift, a ij) =
      (∑ p ∈ Finset.Icc 2 P,
        ∑ ij ∈ hierarchyAdvectionPairs P shift with hierarchyAdvectionLevel shift ij = p, a ij) +
      ∑ ij ∈ hierarchyTailPairs P shift, a ij := by
  let s := hierarchyAdvectionPairs P shift
  let g := hierarchyAdvectionLevel shift
  rw [Finset.sum_fiberwise_eq_sum_filter s _ g a]
  have hprefix : s.filter (fun ij => g ij ∈ Finset.Icc 2 P) =
      s.filter (fun ij => g ij ≤ P) := by
    ext ij
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hm, _, hp⟩
      exact ⟨hm, hp⟩
    · rintro ⟨hm, hp⟩
      exact ⟨hm, hierarchyAdvectionLevel_at_least_two hm, hp⟩
  rw [hprefix]
  have htail : s.filter (fun ij => P + shift < ij.1 + ij.2) =
      s.filter (fun ij => ¬ g ij ≤ P) := by
    ext ij
    simp only [Finset.mem_filter, g, hierarchyAdvectionLevel]
    constructor <;> rintro ⟨hm, hp⟩ <;> exact ⟨hm, by omega⟩
  rw [hierarchyTailPairs, htail]
  exact (Finset.sum_filter_add_sum_filter_not s _ a).symm

/-- Label advection only uses previous levels. -/
theorem hierarchy_label_inputs_previous {i j p : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hij : i + j = p) : i < p ∧ j < p := by
  omega

/-- Fast advection by a completion uses previous levels. Fast advection
by a mean reaches the current level only when it acts on the leading wave. -/
theorem hierarchy_phase_inputs_previous {i j p : ℕ} (hi : 2 ≤ i) (hj : 1 ≤ j)
    (hij : i + j = p + 1) :
    i - 1 < p ∧ j < p ∧ i ≤ p ∧ (i = p ↔ j = 1) := by
  omega

/-- The mean solve returns to the parent-factor-free bound used in the
next transverse source. -/
theorem hierarchy_absorb_mean_parent_loss {freq loss : ℝ}
    (hfreq : 1 ≤ freq) (hloss : 0 ≤ loss)
    (hsmall : loss * freq ^ (-1 / 12 : ℝ) ≤ 1) (p : ℕ) :
    loss * freq ^ hierarchyMeanExponent p ≤ freq ^ hierarchyInductiveMeanExponent p := by
  have h := hierarchy_absorb_parent_loss hfreq hloss hsmall
    (exponent := hierarchyInductiveMeanExponent p) (spare := 1 / 12) le_rfl
  rw [← hierarchy_mean_inductive_shift, add_sub_cancel_right] at h
  simpa only [hierarchy_mean_inductive_shift] using h

private theorem hierarchy_tail_pair_bounds {P shift : ℕ} {ij : ℕ × ℕ}
    (hij : ij ∈ hierarchyTailPairs P shift) :
    shift + 1 ≤ ij.1 ∧ P + 1 ≤ hierarchyAdvectionLevel shift ij ∧
      ij.1 + ij.2 = hierarchyAdvectionLevel shift ij + shift := by
  have h := Finset.mem_filter.mp hij
  have hm := (Finset.mem_product (s := Finset.Icc (shift + 1) (P + 1))
    (t := Finset.Icc 1 (P + 1))).1 h.1
  have hi := (Finset.mem_Icc.mp hm.1).1
  have ht := h.2
  unfold hierarchyAdvectionLevel
  omega

/-- Given the termwise norm bounds from label and phase advection and the
linear bound, the finite sum has the remainder exponent in
`cc:uf:hier:eq:tail-est`. The constants count the terms of each type. -/
theorem norm_hierarchy_tail_model {E : Type*} [SeminormedAddCommGroup E]
    (P : ℕ) (linear : E) (slow fastCompletion fastMean : ℕ × ℕ → E)
    {freq loss A : ℝ} (hfreq : 1 ≤ freq) (hloss : 0 ≤ loss) (hA : 0 ≤ A)
    (hsmall : loss * freq ^ (-1 / 12 : ℝ) ≤ 1)
    (hlinear : ‖linear‖ ≤ A * (loss * freq ^ hierarchyCompletionExponent P))
    (hslow : ∀ ij ∈ hierarchyTailPairs P 0, ‖slow ij‖ ≤ A *
      (loss * freq ^ (hierarchyOscExponent ij.1 + hierarchyOscExponent ij.2)))
    (hfastCompletion : ∀ ij ∈ hierarchyTailPairs P 1, ‖fastCompletion ij‖ ≤ A *
      (loss * freq ^ (3 / 2 + hierarchyCompletionExponent (ij.1 - 1) + hierarchyOscExponent ij.2)))
    (hfastMean : ∀ ij ∈ hierarchyTailPairs P 1, ‖fastMean ij‖ ≤ A *
      (loss * freq ^ (3 / 2 + hierarchyInductiveMeanExponent ij.1 + hierarchyOscExponent ij.2))) :
    ‖linear + (∑ ij ∈ hierarchyTailPairs P 0, slow ij) +
      (∑ ij ∈ hierarchyTailPairs P 1, (fastCompletion ij + fastMean ij))‖ ≤
      A * (1 + ((hierarchyTailPairs P 0).card : ℝ) + 2 * ((hierarchyTailPairs P 1).card : ℝ)) *
        freq ^ hierarchyOscExponent (P + 1) := by
  let M := A * freq ^ hierarchyOscExponent (P + 1)
  have hbound {p : ℕ} {spare : ℝ} (hp : P + 1 ≤ p) (hs : 1 / 12 ≤ spare) :
      A * (loss * freq ^ (hierarchyOscExponent p - spare)) ≤ M := by
    apply mul_le_mul_of_nonneg_left _ hA
    exact (hierarchy_absorb_parent_loss hfreq hloss hsmall hs).trans
      (Real.rpow_le_rpow_of_exponent_le hfreq (hierarchyOscExponent_antitone hp))
  have hlin : ‖linear‖ ≤ M := by
    have he : hierarchyCompletionExponent P = hierarchyOscExponent (P + 1) - 1 / 3 := by
      simpa using hierarchy_completion_previous (p := P + 1) (by omega : 1 ≤ P + 1)
    rw [he] at hlinear
    exact hlinear.trans (hbound le_rfl (by norm_num))
  have hlabel : ‖∑ ij ∈ hierarchyTailPairs P 0, slow ij‖ ≤
      ((hierarchyTailPairs P 0).card : ℝ) * M := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _ij ∈ hierarchyTailPairs P 0, M := by
        refine Finset.sum_le_sum fun ij hij => ?_
        obtain ⟨_, hp, hgrade⟩ := hierarchy_tail_pair_bounds hij
        have hterm := hslow ij hij
        rw [(hierarchy_label_product_exponent ij.1 ij.2).2, hgrade, Nat.add_zero] at hterm
        exact hterm.trans (hbound hp (by norm_num))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hphase : ‖∑ ij ∈ hierarchyTailPairs P 1, (fastCompletion ij + fastMean ij)‖ ≤
      ((hierarchyTailPairs P 1).card : ℝ) * (2 * M) := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _ij ∈ hierarchyTailPairs P 1, 2 * M := by
        refine Finset.sum_le_sum fun ij hij => ?_
        obtain ⟨hi, hp, hgrade⟩ := hierarchy_tail_pair_bounds hij
        have hc := hfastCompletion ij hij
        rw [hierarchy_fast_completion_exponent (by omega : 1 ≤ ij.1) hgrade] at hc
        have hb := hfastMean ij hij
        rw [hierarchy_fast_mean_exponent hgrade] at hb
        have hc' := hc.trans (hbound hp (by norm_num))
        have hb' := hb.trans (hbound hp (by norm_num))
        exact (norm_add_le _ _).trans (by linarith)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ M + ((hierarchyTailPairs P 0).card : ℝ) * M +
        ((hierarchyTailPairs P 1).card : ℝ) * (2 * M) :=
      (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hlin hlabel)) hphase)
    _ = _ := by dsimp [M]; ring

end TorusEuler
