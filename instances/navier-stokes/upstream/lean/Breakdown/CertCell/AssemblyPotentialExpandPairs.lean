import Breakdown.CertCell.AssemblyPotentialParts

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

namespace Internal.StretchPairs


abbrev Profiles := ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ

structure Good (S : Set (ℝ × ℝ)) (X : Profiles) : Prop where
  meas : ∀ ι j, AEStronglyMeasurable (fun p => X ι p j) (volume.restrict S)
  integ : ∀ ι, IntegrableOn (fun p : ℝ × ℝ => p.1 * ∑ j, ‖X ι p j‖ ^ 2) S
  summ : Summable (fun ι => ∫ p in S, p.1 * ∑ j, ‖X ι p j‖ ^ 2)

def pairTerm (M : ℤ × ℤ → ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ) (X Y : Profiles) (α ι : ℤ × ℤ) (p : ℝ × ℝ) : ℝ :=
  p.1 * (sesq12 (M α p) (X ι p) (Y (ι - α) p)).re

def pairSum (S : Set (ℝ × ℝ)) (H : Finset (ℤ × ℤ)) (M : ℤ × ℤ → ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ)
    (X Y : Profiles) : ℝ :=
  ∑' ι, ∑ α ∈ H, ∫ p in S, pairTerm M X Y α ι p

structure CouplingOK (S : Set (ℝ × ℝ)) (H : Finset (ℤ × ℤ)) (M : ℤ × ℤ → ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ) :
    Prop where
  set_meas : MeasurableSet S
  first_nonneg : ∀ p ∈ S, 0 ≤ p.1
  meas : ∀ α ∈ H, ∀ i j, AEStronglyMeasurable (fun p => M α p i j) (volume.restrict S)
  bound : ∀ α ∈ H, ∃ c : ℝ, ∀ p ∈ S, ∀ i j, ‖M α p i j‖ ≤ c

theorem norm_sesq12_le (A : Matrix (Fin 12) (Fin 12) ℂ) (U V : Fin 12 → ℂ) (c : ℝ) (hA : ∀ i j, ‖A i j‖ ≤ c) :
    ‖sesq12 A U V‖ ≤ 6 * c * (∑ j, ‖U j‖ ^ 2 + ∑ j, ‖V j‖ ^ 2) := by
  have hc : 0 ≤ c := (norm_nonneg _).trans (hA 0 0)
  unfold sesq12
  calc ‖∑ i, ∑ j, (starRingEnd ℂ) (U i) * A i j * V j‖
      ≤ ∑ i, ∑ j, ‖(starRingEnd ℂ) (U i) * A i j * V j‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i : Fin 12, ∑ j : Fin 12, c * ((‖U i‖ ^ 2 + ‖V j‖ ^ 2) / 2) := by
        gcongr with i _ j _
        rw [norm_mul, norm_mul, Complex.norm_conj]
        have h1 := hA i j
        have h2 : ‖U i‖ * ‖V j‖ ≤ (‖U i‖ ^ 2 + ‖V j‖ ^ 2) / 2 := by
          nlinarith [sq_nonneg (‖U i‖ - ‖V j‖)]
        have h3 : 0 ≤ ‖U i‖ * ‖V j‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        calc ‖U i‖ * ‖A i j‖ * ‖V j‖ = ‖A i j‖ * (‖U i‖ * ‖V j‖) := by ring
          _ ≤ c * (‖U i‖ * ‖V j‖) := mul_le_mul_of_nonneg_right h1 h3
          _ ≤ c * ((‖U i‖ ^ 2 + ‖V j‖ ^ 2) / 2) := mul_le_mul_of_nonneg_left h2 hc
    _ = 6 * c * (∑ j, ‖U j‖ ^ 2 + ∑ j, ‖V j‖ ^ 2) := by
        simp only [← Finset.mul_sum, add_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, ← Finset.sum_div, nsmul_eq_mul]
        push_cast
        ring

theorem pairTerm_meas {S : Set (ℝ × ℝ)} {H : Finset (ℤ × ℤ)} {M : ℤ × ℤ → ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ}
    (hM : CouplingOK S H M) {X Y : Profiles} (hX : Good S X) (hY : Good S Y) {α : ℤ × ℤ} (hα : α ∈ H) (ι : ℤ × ℤ) :
    AEStronglyMeasurable (pairTerm M X Y α ι) (volume.restrict S) := by
  unfold pairTerm sesq12
  refine continuous_fst.aestronglyMeasurable.mul (Complex.continuous_re.comp_aestronglyMeasurable ?_)
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
  exact ((Complex.continuous_conj.comp_aestronglyMeasurable (hX.meas ι i)).mul (hM.meas α hα i j)).mul (hY.meas _ j)


theorem pairTerm_bound {S : Set (ℝ × ℝ)} {H : Finset (ℤ × ℤ)} {M : ℤ × ℤ → ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ}
    (hM : CouplingOK S H M) {X Y : Profiles} {α : ℤ × ℤ} {c : ℝ} (hc : ∀ p ∈ S, ∀ i j, ‖M α p i j‖ ≤ c)
    (ι : ℤ × ℤ) : ∀ p ∈ S, ‖pairTerm M X Y α ι p‖
      ≤ 6 * c * (p.1 * ∑ j, ‖X ι p j‖ ^ 2 + p.1 * ∑ j, ‖Y (ι - α) p j‖ ^ 2) := by
  intro p hp
  have h1 := hM.first_nonneg p hp
  unfold pairTerm
  rw [norm_mul, Real.norm_of_nonneg h1]
  have h2 := (Complex.abs_re_le_norm (sesq12 (M α p) (X ι p) (Y (ι - α) p))).trans
    (norm_sesq12_le _ _ _ c (hc p hp))
  rw [Real.norm_eq_abs]
  calc p.1 * |(sesq12 (M α p) (X ι p) (Y (ι - α) p)).re|
      ≤ p.1 * (6 * c * (∑ j, ‖X ι p j‖ ^ 2 + ∑ j, ‖Y (ι - α) p j‖ ^ 2)) := mul_le_mul_of_nonneg_left h2 h1
    _ = 6 * c * (p.1 * ∑ j, ‖X ι p j‖ ^ 2 + p.1 * ∑ j, ‖Y (ι - α) p j‖ ^ 2) := by ring

theorem pairTerm_integrable {S : Set (ℝ × ℝ)} {H : Finset (ℤ × ℤ)} {M : ℤ × ℤ → ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ}
    (hM : CouplingOK S H M) {X Y : Profiles} (hX : Good S X) (hY : Good S Y) {α : ℤ × ℤ} (hα : α ∈ H)
    (ι : ℤ × ℤ) : IntegrableOn (pairTerm M X Y α ι) S := by
  obtain ⟨c, hc⟩ := hM.bound α hα
  refine Integrable.mono' (((hX.integ ι).add (hY.integ (ι - α))).const_mul (6 * c)) (pairTerm_meas hM hX hY hα ι) ?_
  filter_upwards [ae_restrict_mem hM.set_meas] with p hp
  exact pairTerm_bound hM hc ι p hp

theorem pairTerm_summable {S : Set (ℝ × ℝ)} {H : Finset (ℤ × ℤ)} {M : ℤ × ℤ → ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ}
    (hM : CouplingOK S H M) {X Y : Profiles} (hX : Good S X) (hY : Good S Y) {α : ℤ × ℤ} (hα : α ∈ H) :
    Summable (fun ι => ∫ p in S, pairTerm M X Y α ι p) := by
  obtain ⟨c, hc⟩ := hM.bound α hα
  have hYs : Summable (fun ι => ∫ p in S, p.1 * ∑ j, ‖Y (ι - α) p j‖ ^ 2) :=
    (Equiv.subRight α).summable_iff.2 hY.summ
  refine Summable.of_norm_bounded ((hX.summ.add hYs).mul_left (6 * c)) fun ι => ?_
  have h := norm_integral_le_of_norm_le (((hX.integ ι).add (hY.integ (ι - α))).const_mul (6 * c))
    (by filter_upwards [ae_restrict_mem hM.set_meas] with p hp; exact pairTerm_bound hM hc ι p hp)
  refine h.trans (le_of_eq ?_)
  rw [integral_const_mul]
  simp only [Pi.add_apply]
  rw [integral_add (hX.integ ι) (hY.integ (ι - α))]

theorem pairTerm_add_left (M : ℤ × ℤ → ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ) (X X' Y : Profiles) (α ι : ℤ × ℤ)
    (p : ℝ × ℝ) : pairTerm M (fun ι p j => X ι p j + X' ι p j) Y α ι p
      = pairTerm M X Y α ι p + pairTerm M X' Y α ι p := by
  unfold pairTerm sesq12
  simp only [map_add, add_mul, Finset.sum_add_distrib, Complex.add_re]
  try ring

theorem pairTerm_add_right (M : ℤ × ℤ → ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ) (X Y Y' : Profiles) (α ι : ℤ × ℤ)
    (p : ℝ × ℝ) : pairTerm M X (fun ι p j => Y ι p j + Y' ι p j) α ι p
      = pairTerm M X Y α ι p + pairTerm M X Y' α ι p := by
  unfold pairTerm sesq12
  simp only [mul_add, Finset.sum_add_distrib, Complex.add_re]
  try ring

theorem pairSum_add_left {S : Set (ℝ × ℝ)} {H : Finset (ℤ × ℤ)} {M : ℤ × ℤ → ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ}
    (hM : CouplingOK S H M) {X X' Y : Profiles} (hX : Good S X) (hX' : Good S X') (hY : Good S Y) :
    pairSum S H M (fun ι p j => X ι p j + X' ι p j) Y = pairSum S H M X Y + pairSum S H M X' Y := by
  unfold pairSum
  have e : ∀ ι, ∑ α ∈ H, ∫ p in S, pairTerm M (fun ι p j => X ι p j + X' ι p j) Y α ι p
      = (∑ α ∈ H, ∫ p in S, pairTerm M X Y α ι p) + ∑ α ∈ H, ∫ p in S, pairTerm M X' Y α ι p := by
    intro ι
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α hα => ?_
    simp only [pairTerm_add_left]
    exact integral_add (pairTerm_integrable hM hX hY hα ι) (pairTerm_integrable hM hX' hY hα ι)
  simp only [e]
  exact (summable_sum fun α hα => pairTerm_summable hM hX hY hα).tsum_add
    (summable_sum fun α hα => pairTerm_summable hM hX' hY hα)

theorem pairSum_add_right {S : Set (ℝ × ℝ)} {H : Finset (ℤ × ℤ)} {M : ℤ × ℤ → ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ}
    (hM : CouplingOK S H M) {X Y Y' : Profiles} (hX : Good S X) (hY : Good S Y) (hY' : Good S Y') :
    pairSum S H M X (fun ι p j => Y ι p j + Y' ι p j) = pairSum S H M X Y + pairSum S H M X Y' := by
  unfold pairSum
  have e : ∀ ι, ∑ α ∈ H, ∫ p in S, pairTerm M X (fun ι p j => Y ι p j + Y' ι p j) α ι p
      = (∑ α ∈ H, ∫ p in S, pairTerm M X Y α ι p) + ∑ α ∈ H, ∫ p in S, pairTerm M X Y' α ι p := by
    intro ι
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α hα => ?_
    simp only [pairTerm_add_right]
    exact integral_add (pairTerm_integrable hM hX hY hα ι) (pairTerm_integrable hM hX hY' hα ι)
  simp only [e]
  exact (summable_sum fun α hα => pairTerm_summable hM hX hY hα).tsum_add
    (summable_sum fun α hα => pairTerm_summable hM hX hY' hα)

theorem pairSum_symm {S : Set (ℝ × ℝ)} {H : Finset (ℤ × ℤ)} {M : ℤ × ℤ → ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ}
    (hM : CouplingOK S H M) (hneg : ∀ α ∈ H, -α ∈ H)
    (hsym : ∀ α p U V, (sesq12 (M (-α) p) V U).re = (sesq12 (M α p) U V).re)
    {X Y : Profiles} (hX : Good S X) (hY : Good S Y) : pairSum S H M Y X = pairSum S H M X Y := by
  unfold pairSum
  rw [Summable.tsum_finsetSum fun α hα => pairTerm_summable hM hY hX hα,
    Summable.tsum_finsetSum fun α hα => pairTerm_summable hM hX hY hα]
  have e1 : ∀ α, ∑' ι, ∫ p in S, pairTerm M X Y α ι p = ∑' κ, ∫ p in S, pairTerm M Y X (-α) κ p := by
    intro α
    rw [← (Equiv.addRight α).tsum_eq]
    refine tsum_congr fun κ => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [pairTerm, Equiv.coe_addRight, add_sub_cancel_right, sub_neg_eq_add]
    rw [hsym]
  simp only [e1]
  refine Finset.sum_nbij' (fun α => -α) (fun α => -α) (fun α hα => hneg α hα) (fun α hα => hneg α hα)
    (fun α _ => neg_neg α) (fun α _ => neg_neg α) (fun α _ => ?_)
  rw [neg_neg]

theorem sqMass_meas {S : Set (ℝ × ℝ)} {X : Profiles} {ι : ℤ × ℤ} (hX : ∀ j, AEStronglyMeasurable (fun p => X ι p j) (volume.restrict S)) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => p.1 * ∑ j, ‖X ι p j‖ ^ 2) (volume.restrict S) :=
  continuous_fst.aestronglyMeasurable.mul (Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hX j).norm.pow 2)

theorem sqMass_nonneg {S : Set (ℝ × ℝ)} (h0 : ∀ p ∈ S, 0 ≤ p.1) (hS : MeasurableSet S) (X : Profiles) (ι : ℤ × ℤ) :
    0 ≤ ∫ p in S, p.1 * ∑ j, ‖X ι p j‖ ^ 2 :=
  setIntegral_nonneg hS fun p hp => mul_nonneg (h0 p hp) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem good_comb {S : Set (ℝ × ℝ)} (h0 : ∀ p ∈ S, 0 ≤ p.1) (hS : MeasurableSet S) {X Y Z : Profiles}
    (hX : Good S X) (hY : Good S Y) (hZ : ∀ ι j, AEStronglyMeasurable (fun p => Z ι p j) (volume.restrict S))
    (hle : ∀ ι p j, ‖Z ι p j‖ ^ 2 ≤ 2 * ‖X ι p j‖ ^ 2 + 2 * ‖Y ι p j‖ ^ 2) : Good S Z := by
  have hpt : ∀ ι, ∀ p ∈ S, p.1 * ∑ j, ‖Z ι p j‖ ^ 2
      ≤ 2 * (p.1 * ∑ j, ‖X ι p j‖ ^ 2) + 2 * (p.1 * ∑ j, ‖Y ι p j‖ ^ 2) := by
    intro ι p hp
    have h1 : ∑ j, ‖Z ι p j‖ ^ 2 ≤ 2 * ∑ j, ‖X ι p j‖ ^ 2 + 2 * ∑ j, ‖Y ι p j‖ ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun j _ => hle ι p j
    have h2 := mul_le_mul_of_nonneg_left h1 (h0 p hp)
    linarith
  have hint : ∀ ι, IntegrableOn (fun p : ℝ × ℝ => p.1 * ∑ j, ‖Z ι p j‖ ^ 2) S := by
    intro ι
    refine Integrable.mono' (((hX.integ ι).const_mul 2).add ((hY.integ ι).const_mul 2)) (sqMass_meas (hZ ι)) ?_
    filter_upwards [ae_restrict_mem hS] with p hp
    rw [Real.norm_of_nonneg (mul_nonneg (h0 p hp) (Finset.sum_nonneg fun _ _ => sq_nonneg _))]
    exact hpt ι p hp
  refine ⟨hZ, hint, ?_⟩
  refine Summable.of_nonneg_of_le (fun ι => sqMass_nonneg h0 hS Z ι) (fun ι => ?_)
    ((hX.summ.mul_left 2).add (hY.summ.mul_left 2))
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hX.integ ι).const_mul 2) ((hY.integ ι).const_mul 2)]
  exact setIntegral_mono_on (hint ι) (((hX.integ ι).const_mul 2).add ((hY.integ ι).const_mul 2)) hS (hpt ι)

theorem good_add {S : Set (ℝ × ℝ)} (h0 : ∀ p ∈ S, 0 ≤ p.1) (hS : MeasurableSet S) {X Y : Profiles}
    (hX : Good S X) (hY : Good S Y) : Good S (fun ι p j => X ι p j + Y ι p j) := by
  refine good_comb h0 hS hX hY (fun ι j => (hX.meas ι j).add (hY.meas ι j)) fun ι p j => ?_
  have h := norm_add_le (X ι p j) (Y ι p j)
  nlinarith [norm_nonneg (X ι p j + Y ι p j), sq_nonneg (‖X ι p j‖ - ‖Y ι p j‖), norm_nonneg (X ι p j),
    norm_nonneg (Y ι p j)]

theorem good_sub {S : Set (ℝ × ℝ)} (h0 : ∀ p ∈ S, 0 ≤ p.1) (hS : MeasurableSet S) {X Y : Profiles}
    (hX : Good S X) (hY : Good S Y) : Good S (fun ι p j => X ι p j - Y ι p j) := by
  refine good_comb h0 hS hX hY (fun ι j => (hX.meas ι j).sub (hY.meas ι j)) fun ι p j => ?_
  have h := norm_sub_le (X ι p j) (Y ι p j)
  nlinarith [norm_nonneg (X ι p j - Y ι p j), sq_nonneg (‖X ι p j‖ - ‖Y ι p j‖), norm_nonneg (X ι p j),
    norm_nonneg (Y ι p j)]

theorem good_restrict {S : Set (ℝ × ℝ)} (h0 : ∀ p ∈ S, 0 ≤ p.1) (hS : MeasurableSet S) {X : Profiles}
    (hX : Good S X) (T : Set (ℤ × ℤ)) : Good S (restrictTo T X) := by
  classical
  have hz : ∀ ι, ι ∉ T → ∀ p j, restrictTo T X ι p j = 0 := fun ι h p j => by simp [restrictTo, h]
  have hx : ∀ ι, ι ∈ T → ∀ p j, restrictTo T X ι p j = X ι p j := fun ι h p j => by simp [restrictTo, h]
  refine ⟨fun ι j => ?_, fun ι => ?_, ?_⟩
  · by_cases h : ι ∈ T
    · simpa only [hx ι h] using hX.meas ι j
    · simp only [hz ι h]
      exact aestronglyMeasurable_const
  · by_cases h : ι ∈ T
    · simpa only [hx ι h] using hX.integ ι
    · simp only [hz ι h, norm_zero]
      simp
  · refine Summable.of_nonneg_of_le (fun ι => sqMass_nonneg h0 hS _ ι) (fun ι => ?_) hX.summ
    by_cases h : ι ∈ T
    · simp only [hx ι h, le_refl]
    · simp only [hz ι h, norm_zero]
      simpa using sqMass_nonneg h0 hS X ι

theorem good_finite {S : Set (ℝ × ℝ)} (hK : IsCompact S) {X : Profiles}
    (hc : ∀ ι j, Continuous (fun p => X ι p j)) (F : Finset (ℤ × ℤ)) (hF : ∀ ι, ι ∉ F → ∀ p j, X ι p j = 0) :
    Good S X := by
  refine ⟨fun ι j => (hc ι j).aestronglyMeasurable, fun ι => ?_, ?_⟩
  · refine ContinuousOn.integrableOn_compact hK (Continuous.continuousOn ?_)
    exact continuous_fst.mul (continuous_finsetSum _ fun j _ => (hc ι j).norm.pow 2)
  · refine summable_of_ne_finset_zero (s := F) fun ι hι => ?_
    simp [hF ι hι]

section Split

theorem split_core {S : Set (ℝ × ℝ)} {Hs : Finset (ℤ × ℤ)} {M : ℤ × ℤ → ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ}
    (hM : CouplingOK S Hs M) (hneg : ∀ α ∈ Hs, -α ∈ Hs)
    (hsym : ∀ α p U V, (sesq12 (M (-α) p) V U).re = (sesq12 (M α p) U V).re)
    (t U : Profiles) (Rs Bs : Finset (ℤ × ℤ)) (hU0 : ∀ ι, ι ∉ Rs → ∀ p, U ι p = 0) (hRB : Disjoint Rs Bs)
    (ht : Good S t) (hU : Good S U) :
    pairSum S Hs M t t = pairSum S Hs M U U
      + 2 * pairSum S Hs M U (restrictTo (Rs : Set (ℤ × ℤ)) (fun ι p => t ι p - U ι p))
      + 2 * pairSum S Hs M U (restrictTo (Bs : Set (ℤ × ℤ)) t)
      + 2 * pairSum S Hs M U (restrictTo {ι | ι ∉ Rs ∧ ι ∉ Bs} t)
      + pairSum S Hs M (fun ι p => t ι p - U ι p) (fun ι p => t ι p - U ι p) := by
  classical
  have h0 := hM.first_nonneg
  have hS := hM.set_meas
  have hO : Good S (fun ι p => t ι p - U ι p) := good_sub h0 hS ht hU
  have hR := good_restrict h0 hS hO (Rs : Set (ℤ × ℤ))
  have hB := good_restrict h0 hS ht (Bs : Set (ℤ × ℤ))
  have hD := good_restrict h0 hS ht {ι | ι ∉ Rs ∧ ι ∉ Bs}
  have e1 : t = fun ι p j => U ι p j + (fun ι p => t ι p - U ι p) ι p j := by
    funext ι p j
    simp only [Pi.sub_apply]
    ring
  have e2 : (fun ι p => t ι p - U ι p) = fun ι p j => restrictTo (Rs : Set (ℤ × ℤ)) (fun ι p => t ι p - U ι p) ι p j
      + (fun ι p j => restrictTo (Bs : Set (ℤ × ℤ)) t ι p j + restrictTo {ι | ι ∉ Rs ∧ ι ∉ Bs} t ι p j) ι p j := by
    funext ι p j
    by_cases h1 : ι ∈ Rs
    · have h2 : ι ∉ Bs := Finset.disjoint_left.1 hRB h1
      simp [restrictTo, h1, h2]
    · by_cases h2 : ι ∈ Bs
      · simp [restrictTo, h1, h2, hU0 ι h1 p]
      · simp [restrictTo, h1, h2, hU0 ι h1 p]
  have hUO : Good S (fun ι p j => U ι p j + (fun ι p => t ι p - U ι p) ι p j) := good_add h0 hS hU hO
  have hBD : Good S (fun ι p j => restrictTo (Bs : Set (ℤ × ℤ)) t ι p j + restrictTo {ι | ι ∉ Rs ∧ ι ∉ Bs} t ι p j) :=
    good_add h0 hS hB hD
  have s1 : pairSum S Hs M t t = pairSum S Hs M U U + pairSum S Hs M U (fun ι p => t ι p - U ι p)
      + (pairSum S Hs M (fun ι p => t ι p - U ι p) U
        + pairSum S Hs M (fun ι p => t ι p - U ι p) (fun ι p => t ι p - U ι p)) := by
    conv_lhs => rw [e1]
    rw [pairSum_add_left hM hU hO hUO, pairSum_add_right hM hU hU hO, pairSum_add_right hM hO hU hO]
  have s2 : pairSum S Hs M (fun ι p => t ι p - U ι p) U = pairSum S Hs M U (fun ι p => t ι p - U ι p) :=
    pairSum_symm hM hneg hsym hU hO
  have s3 : pairSum S Hs M U (fun ι p => t ι p - U ι p)
      = pairSum S Hs M U (restrictTo (Rs : Set (ℤ × ℤ)) (fun ι p => t ι p - U ι p))
        + pairSum S Hs M U (restrictTo (Bs : Set (ℤ × ℤ)) t)
        + pairSum S Hs M U (restrictTo {ι | ι ∉ Rs ∧ ι ∉ Bs} t) := by
    conv_lhs => rw [e2]
    rw [pairSum_add_right hM hU hR hBD, pairSum_add_right hM hU hB hD]
    ring
  rw [s1, s2, s3]
  ring

end Split

section Integrate

theorem pairTerm_normSummable {S : Set (ℝ × ℝ)} {H : Finset (ℤ × ℤ)}
    {M : ℤ × ℤ → ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ} (hM : CouplingOK S H M) {X Y : Profiles} (hX : Good S X)
    (hY : Good S Y) {α : ℤ × ℤ} (hα : α ∈ H) :
    Summable (fun ι => ∫ p in S, ‖pairTerm M X Y α ι p‖) := by
  obtain ⟨c, hc⟩ := hM.bound α hα
  have hYs : Summable (fun ι => ∫ p in S, p.1 * ∑ j, ‖Y (ι - α) p j‖ ^ 2) :=
    (Equiv.subRight α).summable_iff.2 hY.summ
  refine Summable.of_nonneg_of_le (fun ι => integral_nonneg fun p => norm_nonneg _) (fun ι => ?_)
    ((hX.summ.add hYs).mul_left (6 * c))
  have h := setIntegral_mono_on (pairTerm_integrable hM hX hY hα ι).norm
    (((hX.integ ι).add (hY.integ (ι - α))).const_mul (6 * c)) hM.set_meas (pairTerm_bound hM hc ι)
  refine h.trans (le_of_eq ?_)
  rw [integral_const_mul]
  simp only [Pi.add_apply]
  rw [integral_add (hX.integ ι) (hY.integ (ι - α))]

theorem pairSum_integral {S : Set (ℝ × ℝ)} {H : Finset (ℤ × ℤ)}
    {M : ℤ × ℤ → ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ} (hM : CouplingOK S H M) {X Y : Profiles} (hX : Good S X)
    (hY : Good S Y) : ∫ p in S, ∑' ι, ∑ α ∈ H, pairTerm M X Y α ι p = pairSum S H M X Y := by
  have hi : ∀ ι, Integrable (fun p => ∑ α ∈ H, pairTerm M X Y α ι p) (volume.restrict S) :=
    fun ι => integrable_finsetSum _ fun α hα => pairTerm_integrable hM hX hY hα ι
  have hn : Summable (fun ι => ∫ p in S, ‖∑ α ∈ H, pairTerm M X Y α ι p‖) := by
    refine Summable.of_nonneg_of_le (fun ι => integral_nonneg fun p => norm_nonneg _) (fun ι => ?_)
      (summable_sum fun α hα => pairTerm_normSummable hM hX hY hα)
    rw [← integral_finsetSum _ fun α hα => (pairTerm_integrable hM hX hY hα ι).norm]
    exact integral_mono (hi ι).norm (integrable_finsetSum _ fun α hα => (pairTerm_integrable hM hX hY hα ι).norm)
      fun p => norm_sum_le _ _
  rw [← integral_tsum_of_summable_integral_norm hi hn]
  unfold pairSum
  exact tsum_congr fun ι => integral_finsetSum _ fun α hα => pairTerm_integrable hM hX hY hα ι

end Integrate

end Internal.StretchPairs

end Assembly

end CertCell

end Breakdown
