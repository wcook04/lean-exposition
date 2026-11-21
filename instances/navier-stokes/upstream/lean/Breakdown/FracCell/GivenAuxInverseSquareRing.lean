import Breakdown.FracCell.ReductionAdjointDefs
import Breakdown.Frac.OpIntegrable

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

def IsRingTrigSum (S : Finset ℤ) (F : Space → Space) : Prop :=
  ∀ ρ z : ℝ, ∃ a b : ℤ → ℂ, ∀ θ : ℝ,
    Reduction.horizontalPart F (Reduction.ringPoint ρ θ z) =
        ∑ n ∈ S, a n * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I) ∧
      Reduction.verticalPart F (Reduction.ringPoint ρ θ z) =
        ∑ n ∈ S, b n * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)

def HasRingRep (F : Space → Space) : Prop :=
  ∃ S : Finset ℤ, ∃ G : Space → Space, (∀ᵐ y ∂volume, G y = F y) ∧ IsRingTrigSum S G

private theorem integral_exp_int (m : ℤ) (hm : m ≠ 0) :
    ∫ θ in (-Real.pi)..Real.pi, Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I) = 0 := by
  have hc : (m : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hm) Complex.I_ne_zero
  have hfun : (fun θ : ℝ => Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I)) =
      fun θ : ℝ => Complex.exp ((m : ℂ) * Complex.I * (θ : ℂ)) := by
    funext θ
    ring_nf
  rw [hfun, integral_exp_mul_complex hc]
  have h2 : Complex.exp ((m : ℂ) * Complex.I * ((Real.pi : ℝ) : ℂ)) =
      Complex.exp ((m : ℂ) * Complex.I * ((-Real.pi : ℝ) : ℂ)) := by
    have hsplit : (m : ℂ) * Complex.I * ((Real.pi : ℝ) : ℂ) =
        (m : ℂ) * Complex.I * ((-Real.pi : ℝ) : ℂ) + (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h2, sub_self, zero_div]

theorem angularMode_eq_zero_of_trig (S : Finset ℤ) (a : ℤ → ℂ) (u : Space → ℂ) (ρ z : ℝ)
    (hu : ∀ θ : ℝ, u (Reduction.ringPoint ρ θ z) = ∑ n ∈ S, a n * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I))
    (k : ℤ) (hk : k ∉ S) : Reduction.angularMode u k ρ z = 0 := by
  unfold Reduction.angularMode
  have hpt : ∀ θ : ℝ, Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) * u (Reduction.ringPoint ρ θ z) =
      ∑ n ∈ S, a n * Complex.exp (((n - k : ℤ) : ℂ) * (θ : ℂ) * Complex.I) := by
    intro θ
    rw [hu θ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.sum_eq_zero, mul_zero]
    intro n hn
    have hne : n - k ≠ 0 := sub_ne_zero.mpr (fun h => hk (h ▸ hn))
    rw [intervalIntegral.integral_const_mul, integral_exp_int (n - k) hne, mul_zero]
  · intro n _
    exact (continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))).intervalIntegrable _ _

theorem IsRingTrigSum.mono {S T : Finset ℤ} (hST : S ⊆ T) {F : Space → Space} (hF : IsRingTrigSum S F) :
    IsRingTrigSum T F := by
  classical
  intro ρ z
  obtain ⟨a, b, h⟩ := hF ρ z
  refine ⟨fun n => if n ∈ S then a n else 0, fun n => if n ∈ S then b n else 0, fun θ => ⟨?_, ?_⟩⟩
  · rw [(h θ).1, ← Finset.sum_subset hST (fun n _ hn => by simp [hn])]
    exact Finset.sum_congr rfl fun n hn => by simp [hn]
  · rw [(h θ).2, ← Finset.sum_subset hST (fun n _ hn => by simp [hn])]
    exact Finset.sum_congr rfl fun n hn => by simp [hn]

theorem IsRingTrigSum.add {S : Finset ℤ} {F G : Space → Space} (hF : IsRingTrigSum S F)
    (hG : IsRingTrigSum S G) : IsRingTrigSum S (fun y => F y + G y) := by
  intro ρ z
  obtain ⟨a, b, h⟩ := hF ρ z
  obtain ⟨a', b', h'⟩ := hG ρ z
  refine ⟨fun n => a n + a' n, fun n => b n + b' n, fun θ => ⟨?_, ?_⟩⟩
  · have e1 := (h θ).1
    have e2 := (h' θ).1
    simp only [Reduction.horizontalPart, PiLp.add_apply, Complex.ofReal_add] at e1 e2 ⊢
    simp only [add_mul, Finset.sum_add_distrib, ← e1, ← e2]
    ring
  · have e1 := (h θ).2
    have e2 := (h' θ).2
    simp only [Reduction.verticalPart, PiLp.add_apply, Complex.ofReal_add] at e1 e2 ⊢
    simp only [add_mul, Finset.sum_add_distrib, ← e1, ← e2]

theorem IsRingTrigSum.smul {S : Finset ℤ} {F : Space → Space} (c : ℝ) (hF : IsRingTrigSum S F) :
    IsRingTrigSum S (fun y => c • F y) := by
  intro ρ z
  obtain ⟨a, b, h⟩ := hF ρ z
  refine ⟨fun n => (c : ℂ) * a n, fun n => (c : ℂ) * b n, fun θ => ⟨?_, ?_⟩⟩
  · have e1 := (h θ).1
    have hsum : (∑ n ∈ S, (c : ℂ) * a n * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)) =
        (c : ℂ) * ∑ n ∈ S, a n * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    simp only [Reduction.horizontalPart, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul] at e1 ⊢
    rw [hsum, ← e1]
    ring
  · have e1 := (h θ).2
    have hsum : (∑ n ∈ S, (c : ℂ) * b n * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)) =
        (c : ℂ) * ∑ n ∈ S, b n * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    simp only [Reduction.verticalPart, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul] at e1 ⊢
    rw [hsum, ← e1]

theorem IsRingTrigSum.zero : IsRingTrigSum ∅ (fun _ => 0) := by
  intro ρ z
  refine ⟨fun _ => 0, fun _ => 0, fun θ => ⟨?_, ?_⟩⟩ <;>
    simp [Reduction.horizontalPart, Reduction.verticalPart]

theorem HasRingRep.add {F G : Space → Space} (hF : HasRingRep F) (hG : HasRingRep G) :
    HasRingRep (fun y => F y + G y) := by
  classical
  obtain ⟨S, F', hF', hS⟩ := hF
  obtain ⟨T, G', hG', hT⟩ := hG
  refine ⟨S ∪ T, fun y => F' y + G' y, ?_, (hS.mono Finset.subset_union_left).add (hT.mono Finset.subset_union_right)⟩
  filter_upwards [hF', hG'] with y h1 h2
  rw [h1, h2]

theorem HasRingRep.smul {F : Space → Space} (c : ℝ) (hF : HasRingRep F) : HasRingRep (fun y => c • F y) := by
  obtain ⟨S, F', hF', hS⟩ := hF
  refine ⟨S, fun y => c • F' y, ?_, hS.smul c⟩
  filter_upwards [hF'] with y h1
  rw [h1]

theorem HasRingRep.sub {F G : Space → Space} (hF : HasRingRep F) (hG : HasRingRep G) :
    HasRingRep (fun y => F y - G y) := by
  have h := hF.add (hG.smul (-1))
  simp only [neg_one_smul, ← sub_eq_add_neg] at h
  exact h

theorem HasRingRep.sum {ι : Type*} (s : Finset ι) (f : ι → Space → Space) (hf : ∀ i ∈ s, HasRingRep (f i)) :
    HasRingRep (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨∅, fun _ => 0, Filter.Eventually.of_forall fun y => ?_, IsRingTrigSum.zero⟩
    simp
  | insert i s hi ih =>
    have h := (hf i (Finset.mem_insert_self i s)).add (ih fun l hl => hf l (Finset.mem_insert_of_mem hl))
    simp only [Finset.sum_insert hi]
    exact h

theorem HasRingRep.modes {F : Space → Space} (hF : HasRingRep F) :
    ∃ part : Space → Space, (∀ᵐ y ∂volume, part y = F y) ∧
      ∃ S : Finset ℤ, ∀ n ∉ S, ∀ ρ z : ℝ,
        Reduction.angularMode (Reduction.horizontalPart part) n ρ z = 0 ∧
          Reduction.angularMode (Reduction.verticalPart part) n ρ z = 0 := by
  obtain ⟨S, G, hG, hS⟩ := hF
  refine ⟨G, hG, S, fun n hn ρ z => ?_⟩
  obtain ⟨a, b, h⟩ := hS ρ z
  exact ⟨angularMode_eq_zero_of_trig S a _ ρ z (fun θ => (h θ).1) n hn,
    angularMode_eq_zero_of_trig S b _ ρ z (fun θ => (h θ).2) n hn⟩

theorem HasRingRep.of_ae {F G : Space → Space} (h : ∀ᵐ y ∂volume, F y = G y) (hG : HasRingRep G) :
    HasRingRep F := by
  obtain ⟨S, G', hG', hS⟩ := hG
  refine ⟨S, G', ?_, hS⟩
  filter_upwards [h, hG'] with y h1 h2
  rw [h2, h1]

theorem ae_eq_of_test_pairing (L L' : Space → Space) (hloc : LocallyIntegrable L volume)
    (hloc' : LocallyIntegrable L' volume)
    (h : ∀ φ : Space → Space, IsTestVectorField φ → ∫ y, inner ℝ (L y) (φ y) = ∫ y, inner ℝ (L' y) (φ y)) :
    ∀ᵐ y ∂volume, L y = L' y := by
  refine ae_eq_of_integral_contDiff_smul_eq hloc hloc' (fun g hg hgs => ?_)
  have hi : Integrable (fun y => g y • L y) volume :=
    hloc.integrable_smul_left_of_hasCompactSupport hg.continuous hgs
  have hi' : Integrable (fun y => g y • L' y) volume :=
    hloc'.integrable_smul_left_of_hasCompactSupport hg.continuous hgs
  have hsub : ∫ y, (g y • L y - g y • L' y) = 0 := by
    refine integral_eq_zero_of_forall_integral_inner_eq_zero ℝ _ (hi.sub hi') (fun w => ?_)
    have htest : IsTestVectorField (fun y => g y • w) :=
      ⟨hg.smul contDiff_const, by exact hgs.smul_right (f' := fun _ : Space => w)⟩
    have h12 := h _ htest
    have hc : ∀ (M : Space → Space) (y : Space), inner ℝ w (g y • M y) = inner ℝ (M y) (g y • w) := by
      intro M y
      rw [inner_smul_right, inner_smul_right, real_inner_comm]
    have hsplit : (fun y => inner ℝ w (g y • L y - g y • L' y)) =
        fun y => inner ℝ w (g y • L y) - inner ℝ w (g y • L' y) := by
      funext y
      rw [inner_sub_right]
    show ∫ y, inner ℝ w (g y • L y - g y • L' y) = 0
    rw [hsplit, integral_sub (hi.const_inner w) (hi'.const_inner w)]
    simp only [hc]
    rw [h12, sub_self]
  rw [integral_sub hi hi'] at hsub
  exact sub_eq_zero.mp hsub

theorem weakNegTrace_ae_unique (X L L' : Space → Space) (hL : Reduction.IsWeakNegTraceOf X L)
    (hL' : Reduction.IsWeakNegTraceOf X L') (hloc : LocallyIntegrable L volume)
    (hloc' : LocallyIntegrable L' volume) : ∀ᵐ y ∂volume, L y = L' y :=
  ae_eq_of_test_pairing L L' hloc hloc' fun φ hφ => (hL φ hφ).symm.trans (hL' φ hφ)

theorem weakMatrixDivergence_ae_unique (Y : Space → (Space →L[ℝ] Space)) (L L' : Space → Space)
    (hL : Reduction.IsWeakMatrixDivergenceOf Y L) (hL' : Reduction.IsWeakMatrixDivergenceOf Y L')
    (hloc : LocallyIntegrable L volume) (hloc' : LocallyIntegrable L' volume) :
    ∀ᵐ y ∂volume, L y = L' y :=
  ae_eq_of_test_pairing L L' hloc hloc' fun φ hφ => neg_injective ((hL φ hφ).symm.trans (hL' φ hφ))

theorem weakScalarGradient_ae_unique (q : Space → ℝ) (Q Q' : Space → Space)
    (hQ : Reduction.IsWeakScalarGradientOf q Q) (hQ' : Reduction.IsWeakScalarGradientOf q Q')
    (hloc : LocallyIntegrable Q volume) (hloc' : LocallyIntegrable Q' volume) :
    ∀ᵐ y ∂volume, Q y = Q' y := by
  refine ae_eq_of_test_pairing Q Q' hloc hloc' fun φ hφ => ?_
  have hc : ∀ j : Fin 3, IsTestScalar (fun y => φ y j) := fun j =>
    ⟨(EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp hφ.1,
      hφ.2.comp_left (g := fun v : Space => v j) rfl⟩
  have hint : ∀ (M : Space → Space), LocallyIntegrable M volume → ∀ j : Fin 3,
      Integrable (fun y => φ y j * inner ℝ (M y) (unitVector j)) volume := by
    intro M hM j
    have hl : LocallyIntegrable (fun y => inner ℝ (M y) (unitVector j)) volume :=
      locallyIntegrable_iff.2 fun _ hK => (hM.integrableOn_isCompact hK).inner_const _
    exact hl.integrable_smul_left_of_hasCompactSupport (hc j).1.continuous (hc j).2
  have hexp : ∀ (M : Space → Space) (y : Space),
      inner ℝ (M y) (φ y) = ∑ j : Fin 3, φ y j * inner ℝ (M y) (unitVector j) := by
    intro M y
    simp [unitVector, PiLp.inner_apply, Fin.sum_univ_three]
  have hj : ∀ j : Fin 3, ∫ y, φ y j * inner ℝ (Q y) (unitVector j) = ∫ y, φ y j * inner ℝ (Q' y) (unitVector j) :=
    fun j => neg_injective ((hQ _ (hc j) j).symm.trans (hQ' _ (hc j) j))
  simp only [hexp]
  rw [integral_finsetSum _ (fun j _ => hint Q hloc j), integral_finsetSum _ (fun j _ => hint Q' hloc' j)]
  exact Finset.sum_congr rfl fun j _ => hj j

theorem weighted_locallyIntegrable {L : Space → Space} (hLm : AEStronglyMeasurable L volume)
    (hw : MemLp (fun y => ‖y‖ • L y) 2 volume) : LocallyIntegrable L volume := by
  have hB : MeasurableSet (Metric.ball (0 : Space) 1) := measurableSet_ball
  have hφm : AEStronglyMeasurable ((Metric.ball (0 : Space) 1).indicator (fun y : Space => ‖y‖⁻¹)) volume :=
    ((measurable_norm.inv).indicator hB).aestronglyMeasurable
  have hφ2 : Integrable (fun y => ‖(Metric.ball (0 : Space) 1).indicator (fun y : Space => ‖y‖⁻¹) y‖ ^ 2) volume := by
    have hI : IntegrableOn (fun z : Space => ‖z‖ ^ (-2 : ℝ)) (Metric.ball (0 : Space) 1) :=
      FracInternal.integrableOn_ball_norm_rpow (by norm_num)
    have heq : (fun y => ‖(Metric.ball (0 : Space) 1).indicator (fun y : Space => ‖y‖⁻¹) y‖ ^ 2) =
        (Metric.ball (0 : Space) 1).indicator (fun z : Space => ‖z‖ ^ (-2 : ℝ)) := by
      funext y
      by_cases hy : y ∈ Metric.ball (0 : Space) 1
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, Real.norm_eq_abs, sq_abs,
          Real.rpow_neg (norm_nonneg y), Real.rpow_two, inv_pow]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, norm_zero]
        norm_num
    rw [heq, integrable_indicator_iff hB]
    exact hI
  have hw2 : Integrable (fun y => ‖‖y‖ • L y‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).1 hw
  have hprod : Integrable (fun y => (Metric.ball (0 : Space) 1).indicator (fun y : Space => ‖y‖⁻¹) y •
      (‖y‖ • L y)) volume := by
    refine Integrable.mono' ((hφ2.add hw2).div_const 2) (hφm.smul hw.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_smul]
    have h2 := two_mul_le_add_sq ‖(Metric.ball (0 : Space) 1).indicator (fun y : Space => ‖y‖⁻¹) y‖ ‖‖y‖ • L y‖
    simp only [Pi.add_apply]
    linarith
  have hout : LocallyIntegrable ((Metric.ball (0 : Space) 1)ᶜ.indicator L) volume := by
    refine (hw.locallyIntegrable (by norm_num)).mono (hLm.indicator hB.compl)
      (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ Metric.ball (0 : Space) 1
    · rw [Set.indicator_of_notMem (show y ∉ (Metric.ball (0 : Space) 1)ᶜ from fun h => h hy), norm_zero]
      exact norm_nonneg _
    · rw [Set.indicator_of_mem hy, norm_smul, Real.norm_eq_abs, abs_norm]
      have h1 : 1 ≤ ‖y‖ := by
        simpa [Metric.mem_ball, dist_zero_right] using hy
      nlinarith [norm_nonneg (L y)]
  have hne : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
    exact measure_singleton 0
  refine (hprod.locallyIntegrable.add hout).mono hLm ?_
  filter_upwards [hne] with y hy0
  refine le_of_eq (congrArg norm ?_)
  show L y = (Metric.ball (0 : Space) 1).indicator (fun y : Space => ‖y‖⁻¹) y • (‖y‖ • L y) +
    (Metric.ball (0 : Space) 1)ᶜ.indicator L y
  by_cases hy : y ∈ Metric.ball (0 : Space) 1
  · rw [Set.indicator_of_notMem (show y ∉ (Metric.ball (0 : Space) 1)ᶜ from fun h => h hy), add_zero, Set.indicator_of_mem hy, smul_smul,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy0), one_smul]
  · rw [Set.indicator_of_mem (show y ∈ (Metric.ball (0 : Space) 1)ᶜ from hy), Set.indicator_of_notMem hy,
      zero_smul, zero_add]

end GivenFields

end CellCert

end Breakdown
