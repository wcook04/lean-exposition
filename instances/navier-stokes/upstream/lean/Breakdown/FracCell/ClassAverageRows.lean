import Breakdown.FracCell.StClauses
import Breakdown.FracCert.GradientAdd
import Breakdown.FracCert.LinearSolveCore

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace ClassAverageRowsInternal

open SteadyCert

lemma measurable_potential {Q : Space → Space} (hQ : IsGradientField Q) :
    ∃ q : Space → ℝ, AEStronglyMeasurable q volume ∧ IsLocalSquareIntegrable (fun y => q y ^ 2) ∧
      IsLocalSquareIntegrable (fun y => ‖Q y‖ ^ 2) ∧ AEStronglyMeasurable Q volume ∧
      ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
        ∫ y, fderiv ℝ φ y (unitVector j) * q y = -∫ y, φ y * inner ℝ (Q y) (unitVector j) := by
  obtain ⟨q, hq2, hQ2, hQm, hw⟩ := hQ
  by_cases hqm : AEStronglyMeasurable q volume
  · exact ⟨q, hqm, hq2, hQ2, hQm, hw⟩
  · refine ⟨fun _ => 0, aestronglyMeasurable_const, ?_, hQ2, hQm, ?_⟩
    · intro K _
      simp
    · intro φ hφ j
      rw [GradientAddInternal.pairing_zero hQm hQ2 hw hqm φ hφ j]
      simp

lemma unit_expand (v : Space) : v = v 0 • unitVector 0 + v 1 • unitVector 1 + v 2 • unitVector 2 := by
  ext i
  fin_cases i <;> simp [unitVector]

lemma integral_add3 {a b c : Space → ℝ} (ha : Integrable a volume) (hb : Integrable b volume)
    (hc : Integrable c volume) : ∫ y, (a y + b y + c y) = (∫ y, a y) + (∫ y, b y) + ∫ y, c y := by
  rw [integral_add (f := fun y => a y + b y) (ha.add hb) hc, integral_add ha hb]

lemma weak_dir {Q : Space → Space} {q : Space → ℝ} (hqm : AEStronglyMeasurable q volume)
    (hq2 : IsLocalSquareIntegrable (fun y => q y ^ 2)) (hQm : AEStronglyMeasurable Q volume)
    (hQ2 : IsLocalSquareIntegrable (fun y => ‖Q y‖ ^ 2))
    (hw : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
        ∫ y, fderiv ℝ φ y (unitVector j) * q y = -∫ y, φ y * inner ℝ (Q y) (unitVector j))
    (φ : Space → ℝ) (hφ : IsTestScalar φ) (v : Space) :
    ∫ y, fderiv ℝ φ y v * q y = -∫ y, φ y * inner ℝ (Q y) v := by
  have hqi := GradientAddInternal.locInt_of_bound (g := q) hqm hq2 (fun y => le_rfl)
  have hL : ∀ j, Integrable (fun y => fderiv ℝ φ y (unitVector j) * q y) volume := fun j =>
    GradientAddInternal.pair_integrable hqi (GradientAddInternal.deriv_continuous hφ _)
      (GradientAddInternal.deriv_support hφ _)
  have hR : ∀ j, Integrable (fun y => φ y * inner ℝ (Q y) (unitVector j)) volume := fun j =>
    GradientAddInternal.pair_integrable (GradientAddInternal.comp_locInt hQm hQ2 j) hφ.1.continuous hφ.2
  have e1 : (fun y => fderiv ℝ φ y v * q y) = fun y => v 0 * (fderiv ℝ φ y (unitVector 0) * q y)
      + v 1 * (fderiv ℝ φ y (unitVector 1) * q y) + v 2 * (fderiv ℝ φ y (unitVector 2) * q y) := by
    ext y
    conv_lhs => rw [unit_expand v]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  have e2 : (fun y => φ y * inner ℝ (Q y) v) = fun y => v 0 * (φ y * inner ℝ (Q y) (unitVector 0))
      + v 1 * (φ y * inner ℝ (Q y) (unitVector 1)) + v 2 * (φ y * inner ℝ (Q y) (unitVector 2)) := by
    ext y
    conv_lhs => rw [unit_expand v]
    simp only [inner_add_right, real_inner_smul_right]
    ring
  rw [e1, e2, integral_add3 ((hL 0).const_mul (v 0)) ((hL 1).const_mul (v 1)) ((hL 2).const_mul (v 2)),
    integral_add3 ((hR 0).const_mul (v 0)) ((hR 1).const_mul (v 1)) ((hR 2).const_mul (v 2))]
  simp only [integral_const_mul, hw φ hφ]
  ring

lemma grad_conj (L : Space ≃ₗᵢ[ℝ] Space) {Q : Space → Space} (hQ : IsGradientField Q) :
    IsGradientField (fun y => L.symm (Q (L y))) := by
  obtain ⟨q, hqm, hq2, hQ2, hQm, hw⟩ := measurable_potential hQ
  have hmp := L.measurePreserving
  have hemb : MeasurableEmbedding L := L.toMeasurableEquiv.measurableEmbedding
  have loc : ∀ f : Space → ℝ, IsLocalSquareIntegrable f → IsLocalSquareIntegrable (fun y => f (L y)) := by
    intro f hf K hK
    have h := (hmp.integrableOn_comp_preimage hemb (f := f) (s := L '' K)).2 (hf _ (hK.image L.continuous))
    rwa [Set.preimage_image_eq _ L.injective] at h
  refine ⟨fun y => q (L y), loc _ hq2, ?_, ?_, ?_⟩
  · have := loc _ hQ2
    simpa only [LinearIsometryEquiv.norm_map] using this
  · exact L.symm.continuous.comp_aestronglyMeasurable (hQm.comp_measurePreserving hmp)
  · intro φ hφ j
    set ψ : Space → ℝ := fun z => φ (L.symm z) with hψdef
    have hψ : IsTestScalar ψ := ⟨hφ.1.comp L.symm.contDiff, hφ.2.comp_homeomorph L.symm.toHomeomorph⟩
    have hder : ∀ y, fderiv ℝ φ y (unitVector j) = fderiv ℝ ψ (L y) (L (unitVector j)) := by
      intro y
      have hφψ : φ = fun z => ψ (L z) := by
        ext z
        simp [hψdef]
      have hd := ((hψ.1.differentiable (by simp)) (L y)).hasFDerivAt.comp y
        (L.toContinuousLinearEquiv.hasFDerivAt (x := y))
      have hd' : HasFDerivAt φ ((fderiv ℝ ψ (L y)).comp (L.toContinuousLinearEquiv : Space →L[ℝ] Space)) y := by
        rw [hφψ]
        exact hd
      rw [hd'.fderiv]
      rfl
    have lhs : ∫ y, fderiv ℝ φ y (unitVector j) * q (L y) =
        ∫ z, fderiv ℝ ψ z (L (unitVector j)) * q z := by
      simp_rw [hder]
      exact hmp.integral_comp' (f := L.toMeasurableEquiv) (fun z => fderiv ℝ ψ z (L (unitVector j)) * q z)
    have rhs : ∫ y, φ y * inner ℝ (L.symm (Q (L y))) (unitVector j) =
        ∫ z, ψ z * inner ℝ (Q z) (L (unitVector j)) := by
      have hpt : ∀ y, φ y * inner ℝ (L.symm (Q (L y))) (unitVector j) =
          ψ (L y) * inner ℝ (Q (L y)) (L (unitVector j)) := by
        intro y
        simp only [hψdef, LinearIsometryEquiv.symm_apply_apply]
        congr 1
        rw [← L.symm.inner_map_map (Q (L y)) (L (unitVector j)), LinearIsometryEquiv.symm_apply_apply]
      simp_rw [hpt]
      exact hmp.integral_comp' (f := L.toMeasurableEquiv) (fun z => ψ z * inner ℝ (Q z) (L (unitVector j)))
    rw [lhs, rhs]
    exact weak_dir hqm hq2 hQm hQ2 hw ψ hψ _

lemma grad_zero : IsGradientField (fun _ => (0 : Space)) := by
  refine ⟨fun _ => 0, fun K _ => by simp, fun K _ => by simp, aestronglyMeasurable_const, ?_⟩
  intro φ _ j
  simp

lemma grad_smul (a : ℝ) {Q : Space → Space} (hQ : IsGradientField Q) :
    IsGradientField (fun y => a • Q y) := by
  obtain ⟨q, hq2, hQ2, hQm, hw⟩ := hQ
  refine ⟨fun y => a * q y, ?_, ?_, hQm.const_smul a, ?_⟩
  · intro K hK
    have e : (fun y => (a * q y) ^ 2) = fun y => a ^ 2 * q y ^ 2 := by
      ext y
      ring
    rw [e]
    exact (hq2 K hK).const_mul _
  · intro K hK
    have e : (fun y => ‖a • Q y‖ ^ 2) = fun y => a ^ 2 * ‖Q y‖ ^ 2 := by
      ext y
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [e]
    exact (hQ2 K hK).const_mul _
  · intro φ hφ j
    have e1 : (fun y => fderiv ℝ φ y (unitVector j) * (a * q y)) =
        fun y => a * (fderiv ℝ φ y (unitVector j) * q y) := by
      ext y
      ring
    have e2 : (fun y => φ y * inner ℝ (a • Q y) (unitVector j)) =
        fun y => a * (φ y * inner ℝ (Q y) (unitVector j)) := by
      ext y
      rw [real_inner_smul_left]
      ring
    rw [e1, e2, integral_const_mul, integral_const_mul, hw φ hφ j]
    ring

lemma grad_sum (f : ℕ → Space → Space) (hf : ∀ j, IsGradientField (f j)) (n : ℕ) :
    IsGradientField (fun y => ∑ j ∈ Finset.range n, f j y) := by
  induction n with
  | zero => simpa using grad_zero
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    exact gradientAdd _ _ ih (hf n)

lemma pair_int {X e : Space → Space} (hX : AEStronglyMeasurable X volume)
    (h2 : IsLocalSquareIntegrable (fun y => ‖X y‖ ^ 2)) (he : MemLp e 2 volume)
    (hs : ∃ R : ℝ, ∀ y, R < ‖y‖ → e y = 0) : Integrable (fun y => inner ℝ (X y) (e y)) volume := by
  obtain ⟨R, hR⟩ := hs
  have hB : Integrable ((Metric.closedBall (0 : Space) R).indicator (fun y => ‖X y‖ ^ 2)) volume :=
    (h2 _ (isCompact_closedBall 0 R)).integrable_indicator Metric.isClosed_closedBall.measurableSet
  have hE : Integrable (fun y => ‖e y‖ ^ 2) volume := (memLp_two_iff_integrable_sq_norm he.1).1 he
  refine Integrable.mono' (hB.add hE) (hX.inner he.1) (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ Metric.closedBall (0 : Space) R
  · rw [Pi.add_apply, Set.indicator_of_mem hy, Real.norm_eq_abs]
    calc |inner ℝ (X y) (e y)| ≤ ‖X y‖ * ‖e y‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖X y‖ ^ 2 + ‖e y‖ ^ 2 := by
        nlinarith [norm_nonneg (X y), norm_nonneg (e y), sq_nonneg (‖X y‖ - ‖e y‖)]
  · have hlt : R < ‖y‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
    rw [hR y hlt, inner_zero_right, norm_zero]
    exact add_nonneg (Set.indicator_nonneg (fun _ _ => by positivity) _) (by positivity)

lemma pair_conj (L : Space ≃ₗᵢ[ℝ] Space) (X E : Space → Space) (hE : ∀ᵐ y ∂volume, E (L y) = L (E y)) :
    ∫ y, inner ℝ (L.symm (X (L y))) (E y) = ∫ y, inner ℝ (X y) (E y) := by
  have h1 : (fun y => inner ℝ (L.symm (X (L y))) (E y)) =ᵐ[volume]
      fun y => inner ℝ (X (L y)) (E (L y)) := by
    filter_upwards [hE] with y hy
    rw [hy, ← L.inner_map_map (L.symm (X (L y))) (E y), LinearIsometryEquiv.apply_symm_apply]
  rw [integral_congr_ae h1]
  exact L.measurePreserving.integral_comp' (f := L.toMeasurableEquiv) (fun z => inner ℝ (X z) (E z))

lemma pow_apply_succ (L : Space ≃ₗᵢ[ℝ] Space) (j : ℕ) (y : Space) : (L ^ (j + 1)) y = (L ^ j) (L y) := by
  rw [pow_succ, LinearIsometryEquiv.coe_mul]
  rfl

lemma symm_pow_succ (L : Space ≃ₗᵢ[ℝ] Space) (j : ℕ) (w : Space) :
    L ((L ^ (j + 1)).symm w) = (L ^ j).symm w := by
  rw [LinearIsometryEquiv.eq_symm_apply, ← pow_apply_succ, LinearIsometryEquiv.apply_symm_apply]

lemma class_pow (L : Space ≃ₗᵢ[ℝ] Space) (E : Space → Space) (hE : ∀ᵐ y ∂volume, E (L y) = L (E y))
    (j : ℕ) : ∀ᵐ y ∂volume, E ((L ^ j) y) = (L ^ j) (E y) := by
  induction j with
  | zero => exact Filter.Eventually.of_forall fun y => by simp
  | succ j ih =>
    have h2 := L.measurePreserving.quasiMeasurePreserving.ae ih
    filter_upwards [h2, hE] with y h1 h3
    rw [pow_apply_succ, pow_apply_succ, h1, h3]

lemma turn_pow_apply (m j : ℕ) (y : Space) :
    ((LinearSolveCore.turnStepIsometry m ^ j) y) 0 =
        Real.cos (j * (2 * Real.pi / m)) * y 0 - Real.sin (j * (2 * Real.pi / m)) * y 1 ∧
    ((LinearSolveCore.turnStepIsometry m ^ j) y) 1 =
        Real.sin (j * (2 * Real.pi / m)) * y 0 + Real.cos (j * (2 * Real.pi / m)) * y 1 ∧
    ((LinearSolveCore.turnStepIsometry m ^ j) y) 2 = y 2 := by
  induction j generalizing y with
  | zero => simp
  | succ j ih =>
    rw [pow_apply_succ]
    obtain ⟨h0, h1, h2⟩ := ih (LinearSolveCore.turnStepIsometry m y)
    obtain ⟨t0, t1, t2⟩ := LinearSolveCore.turnStep_apply m y
    have e : ∀ z, LinearSolveCore.turnStepIsometry m z = turnStep m z := fun z => rfl
    rw [h0, h1, h2, e, t0, t1, t2]
    push_cast
    simp only [add_mul, one_mul, Real.cos_add, Real.sin_add]
    exact ⟨by ring, by ring, trivial⟩

lemma turn_pow_order (m : ℕ) (hm : m ≠ 0) : LinearSolveCore.turnStepIsometry m ^ m = 1 := by
  ext y i
  obtain ⟨h0, h1, h2⟩ := turn_pow_apply m m y
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hθ : (m : ℝ) * (2 * Real.pi / m) = 2 * Real.pi := by field_simp
  rw [hθ, Real.cos_two_pi, Real.sin_two_pi] at h0 h1
  fin_cases i <;> simp [h0, h1, h2]

lemma avg_equivariant (L : Space ≃ₗᵢ[ℝ] Space) (m : ℕ) (hL : L ^ m = 1) (Q : Space → Space) (y : Space) :
    (∑ j ∈ Finset.range m, (L ^ j).symm (Q ((L ^ j) (L y)))) =
      L (∑ j ∈ Finset.range m, (L ^ j).symm (Q ((L ^ j) y))) := by
  set g : ℕ → Space := fun j => (L ^ j).symm (Q ((L ^ j) y)) with hg
  have h1 : ∀ j, (L ^ j).symm (Q ((L ^ j) (L y))) = L (g (j + 1)) := by
    intro j
    simp only [hg]
    rw [symm_pow_succ, pow_apply_succ]
  have hm0 : g m = g 0 := by simp only [hg, hL, pow_zero]
  simp only [h1, map_sum]
  have e1 := Finset.sum_range_succ' (fun j => L (g j)) m
  have e2 := Finset.sum_range_succ (fun j => L (g j)) m
  rw [e2, hm0] at e1
  exact (add_right_cancel e1).symm

def turnAverage (m : ℕ) (Q : Space → Space) (y : Space) : Space :=
  (1 / (m : ℝ)) • ∑ j ∈ Finset.range m,
    (LinearSolveCore.turnStepIsometry m ^ j).symm (Q ((LinearSolveCore.turnStepIsometry m ^ j) y))

def fullAverage (m : ℕ) (Q : Space → Space) (y : Space) : Space :=
  (1 / 2 : ℝ) • (turnAverage m Q y +
    LinearSolveCore.mirrorIsometry.symm (turnAverage m Q (LinearSolveCore.mirrorIsometry y)))

lemma grad_turn (m : ℕ) {Q : Space → Space} (hQ : IsGradientField Q) : IsGradientField (turnAverage m Q) :=
  grad_smul _ (grad_sum (fun j y => (LinearSolveCore.turnStepIsometry m ^ j).symm
    (Q ((LinearSolveCore.turnStepIsometry m ^ j) y))) (fun _ => grad_conj _ hQ) m)

lemma grad_full (m : ℕ) {Q : Space → Space} (hQ : IsGradientField Q) : IsGradientField (fullAverage m Q) :=
  grad_smul _ (gradientAdd _ _ (grad_turn m hQ) (grad_conj _ (grad_turn m hQ)))

lemma turn_equivariant (m : ℕ) (hm : m ≠ 0) (Q : Space → Space) (y : Space) :
    turnAverage m Q (turnStep m y) = turnStep m (turnAverage m Q y) := by
  have h := avg_equivariant (LinearSolveCore.turnStepIsometry m) m (turn_pow_order m hm) Q y
  have e : ∀ z, LinearSolveCore.turnStepIsometry m z = turnStep m z := fun z => rfl
  unfold turnAverage
  rw [← e, ← e, h, map_smul]

lemma mirror_turn (m : ℕ) (y : Space) : mirror (turnStep m y) = turnStep m (mirror y) := by
  ext i
  fin_cases i <;> simp [turnStep, mirror]

lemma mirror_mirror (y : Space) : mirror (mirror y) = y := by
  ext i
  fin_cases i <;> simp [mirror]

lemma mirror_symm (z : Space) : LinearSolveCore.mirrorIsometry.symm z = mirror z := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  exact (mirror_mirror z).symm

lemma class_full (m : ℕ) (hm : m ≠ 0) (Q : Space → Space) : IsClassField m (fullAverage m Q) := by
  have eM : ∀ z, LinearSolveCore.mirrorIsometry z = mirror z := fun z => rfl
  have eR : ∀ z, LinearSolveCore.turnStepIsometry m z = turnStep m z := fun z => rfl
  have lin : ∀ (a : ℝ) (u w : Space), turnStep m (a • (u + w)) = a • (turnStep m u + turnStep m w) := by
    intro a u w
    rw [← eR, ← eR, ← eR, map_smul, map_add]
  have linM : ∀ (a : ℝ) (u w : Space), mirror (a • (u + w)) = a • (mirror u + mirror w) := by
    intro a u w
    rw [← eM, ← eM, ← eM, map_smul, map_add]
  refine ⟨Filter.Eventually.of_forall fun y => ?_, Filter.Eventually.of_forall fun y => ?_⟩
  · simp only [fullAverage, mirror_symm, eM]
    rw [mirror_turn, turn_equivariant m hm, turn_equivariant m hm, mirror_turn, lin]
  · simp only [fullAverage, mirror_symm, eM]
    rw [mirror_mirror, linM, mirror_mirror, add_comm]

lemma turn_pair (m : ℕ) (hm : m ≠ 0) {Q e : Space → Space} (hQ : IsGradientField Q) (he : MemLp e 2 volume)
    (hs : ∃ R : ℝ, ∀ y, R < ‖y‖ → e y = 0) (hec : IsClassField m e) :
    ∫ y, inner ℝ (turnAverage m Q y) (e y) = ∫ y, inner ℝ (Q y) (e y) := by
  set L := LinearSolveCore.turnStepIsometry m with hLdef
  have hER : ∀ᵐ y ∂volume, e (L y) = L (e y) := hec.1
  have hint : ∀ j, Integrable (fun y => inner ℝ ((L ^ j).symm (Q ((L ^ j) y))) (e y)) volume := by
    intro j
    obtain ⟨_, _, h2, hm', _⟩ := grad_conj (L ^ j) hQ
    exact pair_int hm' h2 he hs
  have hpt : ∀ y, inner ℝ (turnAverage m Q y) (e y) =
      (1 / (m : ℝ)) * ∑ j ∈ Finset.range m, inner ℝ ((L ^ j).symm (Q ((L ^ j) y))) (e y) := by
    intro y
    simp only [turnAverage, real_inner_smul_left, sum_inner, hLdef]
  simp_rw [hpt]
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => hint j)]
  have hj : ∀ j, ∫ y, inner ℝ ((L ^ j).symm (Q ((L ^ j) y))) (e y) = ∫ y, inner ℝ (Q y) (e y) :=
    fun j => pair_conj (L ^ j) Q e (class_pow L e hER j)
  simp_rw [hj]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  field_simp

lemma pair_full (m : ℕ) (hm : m ≠ 0) {F Q e : Space → Space} (hFm : AEStronglyMeasurable F volume)
    (hF2 : IsLocalSquareIntegrable (fun y => ‖F y‖ ^ 2)) (hQ : IsGradientField Q)
    (he : MemLp e 2 volume) (hs : ∃ R : ℝ, ∀ y, R < ‖y‖ → e y = 0) (hec : IsClassField m e) :
    l2Pair (fun y => F y + fullAverage m Q y) e = l2Pair (fun y => F y + Q y) e := by
  have int_of : ∀ X : Space → Space, IsGradientField X → Integrable (fun y => inner ℝ (X y) (e y)) volume := by
    intro X hX
    obtain ⟨_, _, h2, hm', _⟩ := hX
    exact pair_int hm' h2 he hs
  have iF := pair_int hFm hF2 he hs
  have gT := grad_turn m hQ
  have gM := grad_conj LinearSolveCore.mirrorIsometry gT
  have hEM : ∀ᵐ y ∂volume, e (LinearSolveCore.mirrorIsometry y) = LinearSolveCore.mirrorIsometry (e y) := hec.2
  unfold l2Pair
  simp only [inner_add_left]
  rw [integral_add iF (int_of _ (grad_full m hQ)), integral_add iF (int_of _ hQ)]
  congr 1
  simp only [fullAverage, real_inner_smul_left, inner_add_left]
  rw [integral_const_mul, integral_add (int_of _ gT) (int_of _ gM),
    pair_conj LinearSolveCore.mirrorIsometry (turnAverage m Q) e hEM, turn_pair m hm hQ he hs hec]
  ring

end ClassAverageRowsInternal

open SteadyCert ClassAverageRowsInternal

theorem classAverageRows : ClassAverageRowsStatement := by
  intro α k N c hc F hFm hF2 Q hQ
  have hb := hc.base
  have hm : c.order ≠ 0 := by
    have := hb.order_ge
    omega
  refine ⟨fullAverage c.order Q, grad_full c.order hQ, class_full c.order hm Q, ?_⟩
  unfold FracCertData.rows rowSize
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [pair_full c.order hm hFm hF2 hQ (hb.row_two a) (hb.row_support a) (hb.row_class a)]

end CellCert

end Breakdown
