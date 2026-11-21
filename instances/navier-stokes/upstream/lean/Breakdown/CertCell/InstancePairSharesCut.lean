import Breakdown.CertCell.InstancePairStatements
import Breakdown.CertCell.ModeFlip

open scoped ENNReal ComplexOrder
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace InstancePair

open Instance

namespace Internal

open Coercive.RotationInternal (axialRot_apply_zero axialRot_apply_one axialRot_apply_two)

def cylFold (y : Space) : ℝ × ℝ := (Real.sqrt (y 0 ^ 2 + y 1 ^ 2), |y 2|)

def firstCover {n : ℕ} (rect : Fin n → Set (ℝ × ℝ)) (K : Fin n) : Set (ℝ × ℝ) :=
  rect K \ ⋃ (L : Fin n) (_ : L < K), rect L

def cutField {n : ℕ} (rect : Fin n → Set (ℝ × ℝ)) (K : Fin n) (B : ℝ → Space → (Space →L[ℝ] Space)) :
    ℝ → Space → (Space →L[ℝ] Space) :=
  fun σ y => (cylFold ⁻¹' firstCover rect K).indicator (B σ) y

def rectPair (m : ℕ) (L : Finset (ℤ × ℤ)) (G B : ℝ → Space → (Space →L[ℝ] Space)) (S : Set (ℝ × ℝ)) : ℝ :=
  ∑ ι ∈ L, (∫ p in S, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
    CellCalculus.gradAt m ι G a b p * starRingEnd ℂ (CellCalculus.gradAt m ι B a b p)).re

def pairing (G B : ℝ → Space → (Space →L[ℝ] Space)) : ℝ :=
  ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, matInner (G σ y) (B σ y)

structure PairInput (m : ℕ) (L : Finset (ℤ × ℤ)) {n : ℕ} (rect : Fin n → Set (ℝ × ℝ))
    (B : ℝ → Space → (Space →L[ℝ] Space)) : Prop where
  meas : AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2) volume
  periodic : IsTimePeriodic B
  finite : periodLIntegral (fun σ y => matSq (B σ y)) < ⊤
  flip : ∀ᵐ z : ℝ × Space, ∀ u : Space, B z.1 (flipPoint z.2) u = flipPoint (B z.1 z.2 (flipPoint u))
  modes : ∀ ξ : ℤ × ℤ, (∀ ι ∈ L, labelHarmonic m ι ≠ ξ) →
    ∀ᵐ p : ℝ × ℝ, p ∈ halfPlane → modeGrad ξ B 0 (planePoint p) = 0
  support : ∀ σ y, B σ y ≠ 0 → ∃ K, cylFold y ∈ rect K

theorem continuous_cylFold : Continuous cylFold := by
  unfold cylFold
  fun_prop

theorem cylFold_axialRot (φ : ℝ) (y : Space) : cylFold (axialRot φ y) = cylFold y := by
  unfold cylFold
  rw [axialRot_apply_zero, axialRot_apply_one, axialRot_apply_two]
  congr 2
  have h := Real.sin_sq_add_cos_sq φ
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * h

theorem flipPoint_coord (y : Space) : flipPoint y 0 = y 0 ∧ flipPoint y 1 = -y 1 ∧ flipPoint y 2 = -y 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [flipPoint, unitVector]

theorem cylFold_flipPoint (y : Space) : cylFold (flipPoint y) = cylFold y := by
  obtain ⟨h0, h1, h2⟩ := flipPoint_coord y
  simp only [cylFold, h0, h1, h2, neg_sq, abs_neg]

theorem flipPoint_zero : flipPoint 0 = 0 := by
  simp [flipPoint]

theorem axialRot_zero (φ : ℝ) : axialRot φ 0 = 0 := by
  simp [axialRot]

theorem cylFold_planePoint {p : ℝ × ℝ} (hp : p ∈ halfPlane) : cylFold (planePoint p) = p := by
  have h0 : planePoint p 0 = p.1 := by simp [planePoint, CellCert.CellAnalysis.cylPoint]
  have h1 : planePoint p 1 = 0 := by simp [planePoint, CellCert.CellAnalysis.cylPoint]
  have h2 : planePoint p 2 = p.2 := by simp [planePoint, CellCert.CellAnalysis.cylPoint]
  have hp1 : 0 < p.1 := hp.1
  have hp2 : 0 < p.2 := hp.2
  simp only [cylFold, h0, h1, h2]
  ext
  · simp [Real.sqrt_sq hp1.le]
  · simp [abs_of_pos hp2]

theorem measurableSet_firstCover {n : ℕ} {rect : Fin n → Set (ℝ × ℝ)} (hc : ∀ K, IsClosed (rect K)) (K : Fin n) :
    MeasurableSet (firstCover rect K) :=
  (hc K).measurableSet.diff (MeasurableSet.iUnion fun L => MeasurableSet.iUnion fun _ => (hc L).measurableSet)

theorem firstCover_subset {n : ℕ} (rect : Fin n → Set (ℝ × ℝ)) (K : Fin n) : firstCover rect K ⊆ rect K :=
  Set.sdiff_subset

theorem firstCover_disjoint {n : ℕ} (rect : Fin n → Set (ℝ × ℝ)) {K K' : Fin n} (h : K ≠ K') {x : ℝ × ℝ}
    (hx : x ∈ firstCover rect K) (hx' : x ∈ firstCover rect K') : False := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact hx'.2 (Set.mem_iUnion₂.2 ⟨K, hlt, hx.1⟩)
  · exact hx.2 (Set.mem_iUnion₂.2 ⟨K', hlt, hx'.1⟩)

theorem exists_firstCover {n : ℕ} (rect : Fin n → Set (ℝ × ℝ)) {K : Fin n} {x : ℝ × ℝ} (hx : x ∈ rect K) :
    ∃ K', x ∈ firstCover rect K' := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun L => x ∈ rect L
  have hs : s.Nonempty := ⟨K, by simp [s, hx]⟩
  refine ⟨s.min' hs, ?_, ?_⟩
  · exact (Finset.mem_filter.1 (s.min'_mem hs)).2
  · intro h
    obtain ⟨L, hL, hxL⟩ := Set.mem_iUnion₂.1 h
    exact absurd (s.min'_le L (by simp [s, hxL])) (not_le.2 hL)

theorem sum_cutField {n : ℕ} (rect : Fin n → Set (ℝ × ℝ)) (B : ℝ → Space → (Space →L[ℝ] Space))
    (hB : ∀ σ y, B σ y ≠ 0 → ∃ K, cylFold y ∈ rect K) (σ : ℝ) (y : Space) :
    ∑ K, cutField rect K B σ y = B σ y := by
  by_cases h0 : B σ y = 0
  · rw [h0]
    refine Finset.sum_eq_zero fun K _ => ?_
    simp only [cutField]
    by_cases hy : y ∈ cylFold ⁻¹' firstCover rect K
    · rw [Set.indicator_of_mem hy, h0]
    · exact Set.indicator_of_notMem hy _
  · obtain ⟨K, hK⟩ := hB σ y h0
    obtain ⟨K', hK'⟩ := exists_firstCover rect hK
    rw [Finset.sum_eq_single K']
    · simp only [cutField]
      exact Set.indicator_of_mem (show y ∈ cylFold ⁻¹' firstCover rect K' from hK') _
    · intro L _ hL
      simp only [cutField]
      exact Set.indicator_of_notMem (show y ∉ cylFold ⁻¹' firstCover rect L from
        fun hy => firstCover_disjoint rect hL hy hK') _
    · intro h
      exact absurd (Finset.mem_univ K') h

open Classical in
theorem modeGrad_indicator (T : Set Space) (hT : ∀ φ y, axialRot φ y ∈ T ↔ y ∈ T)
    (B : ℝ → Space → (Space →L[ℝ] Space)) (ξ : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeGrad ξ (fun σ y => T.indicator (B σ) y) σ y = if y ∈ T then modeGrad ξ B σ y else 0 := by
  split_ifs with hy
  · unfold modeGrad
    congr 1
    funext τ φ ij
    beta_reduce
    rw [Set.indicator_of_mem ((hT φ y).2 hy)]
  · funext ij
    simp only [modeGrad, modeAverage, Pi.zero_apply]
    have h : ∀ τ φ, T.indicator (B (σ + τ)) (axialRot φ y) = 0 := fun τ φ =>
      Set.indicator_of_notMem (fun h => hy ((hT φ y).1 h)) _
    simp [h, axialRot_zero]

theorem matSq_nonneg' (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem matSq_zero' : matSq (0 : Space →L[ℝ] Space) = 0 := by
  simp [matSq]

theorem continuous_matSq'' : Continuous matSq :=
  continuous_finsetSum _ fun _ _ => ((continuous_id.clm_apply continuous_const).norm).pow 2

theorem continuous_matInner :
    Continuous (fun x : (Space →L[ℝ] Space) × (Space →L[ℝ] Space) => matInner x.1 x.2) :=
  continuous_finsetSum _ fun _ _ =>
    (continuous_fst.clm_apply continuous_const).inner (continuous_snd.clm_apply continuous_const)

theorem matInner_sum {ι : Type*} (s : Finset ι) (A : Space →L[ℝ] Space) (C : ι → Space →L[ℝ] Space) :
    matInner A (∑ i ∈ s, C i) = ∑ i ∈ s, matInner A (C i) := by
  unfold matInner
  simp only [_root_.sum_apply, inner_sum]
  exact Finset.sum_comm

theorem abs_matInner_le (A C : Space →L[ℝ] Space) : |matInner A C| ≤ matSq A + matSq C := by
  unfold matInner matSq
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := abs_real_inner_le_norm (A (unitVector i)) (C (unitVector i))
  nlinarith [norm_nonneg (A (unitVector i)), norm_nonneg (C (unitVector i)),
    sq_nonneg (‖A (unitVector i)‖ - ‖C (unitVector i)‖)]

theorem periodMeasure_eq :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)
      = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem integrable_matInner {G C : ℝ → Space → (Space →L[ℝ] Space)}
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hG2 : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤)
    (hC : AEStronglyMeasurable (fun z : ℝ × Space => C z.1 z.2) volume)
    (hC2 : periodLIntegral (fun σ y => matSq (C σ y)) < ⊤) :
    Integrable (fun z : ℝ × Space => matInner (G z.1 z.2) (C z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  have hGa : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (matSq (G z.1 z.2)))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    rw [periodMeasure_eq]
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      (continuous_matSq''.comp_aestronglyMeasurable hG).aemeasurable).restrict
  refine ⟨?_, ?_⟩
  · rw [periodMeasure_eq]
    exact (continuous_matInner.comp_aestronglyMeasurable (hG.prodMk hC)).restrict
  · unfold HasFiniteIntegral
    calc ∫⁻ z, ‖matInner (G z.1 z.2) (C z.1 z.2)‖ₑ ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume)
        ≤ ∫⁻ z, (ENNReal.ofReal (matSq (G z.1 z.2)) + ENNReal.ofReal (matSq (C z.1 z.2)))
            ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
          refine lintegral_mono fun z => ?_
          rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (matSq_nonneg' _) (matSq_nonneg' _)]
          exact ENNReal.ofReal_le_ofReal (abs_matInner_le _ _)
      _ = ∫⁻ z, ENNReal.ofReal (matSq (G z.1 z.2)) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume)
          + ∫⁻ z, ENNReal.ofReal (matSq (C z.1 z.2)) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) :=
          lintegral_add_left' hGa _
      _ ≤ periodLIntegral (fun σ y => matSq (G σ y)) + periodLIntegral (fun σ y => matSq (C σ y)) :=
          add_le_add (lintegral_prod_le _) (lintegral_prod_le _)
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hG2, hC2⟩

theorem pairing_sum {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hG2 : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤) {n : ℕ}
    (C : Fin n → ℝ → Space → (Space →L[ℝ] Space))
    (hC : ∀ K, AEStronglyMeasurable (fun z : ℝ × Space => C K z.1 z.2) volume)
    (hC2 : ∀ K, periodLIntegral (fun σ y => matSq (C K σ y)) < ⊤) :
    pairing G (fun σ y => ∑ K, C K σ y) = ∑ K, pairing G (C K) := by
  have hI := fun K => integrable_matInner hG hG2 (hC K) (hC2 K)
  unfold pairing
  have h1 : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∫ y, matInner (G σ y) (∑ K, C K σ y) = ∑ K, ∫ y, matInner (G σ y) (C K σ y) := by
    have hae : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        ∀ K, Integrable (fun y => matInner (G σ y) (C K σ y)) volume :=
      ae_all_iff.2 fun K => (hI K).prod_right_ae
    filter_upwards [hae] with σ hσ
    simp_rw [matInner_sum]
    exact integral_finsetSum _ fun K _ => hσ K
  rw [integral_congr_ae h1]
  exact integral_finsetSum _ fun K _ => (hI K).integral_prod_left

theorem null_fst_zero : volume {p : ℝ × ℝ | p.1 = 0} = 0 := by
  have e : {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ Set.univ := by
    ext p
    simp
  rw [e, Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem null_snd_zero : volume {p : ℝ × ℝ | p.2 = 0} = 0 := by
  have e : {p : ℝ × ℝ | p.2 = 0} = Set.univ ×ˢ ({0} : Set ℝ) := by
    ext p
    simp
  rw [e, Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem measurableSet_halfPlane' : MeasurableSet halfPlane :=
  measurableSet_Ioi.prod measurableSet_Ioi

theorem firstCover_ae {n : ℕ} {rect : Fin n → Set (ℝ × ℝ)} (hq : ∀ K, rect K ⊆ Set.Ici 0 ×ˢ Set.Ici 0)
    (hapart : ∀ K K', K ≠ K' → volume (rect K ∩ rect K') = 0) (K : Fin n) :
    (rect K ∩ halfPlane ∩ firstCover rect K : Set (ℝ × ℝ)) =ᵐ[volume] rect K := by
  let N : Set (ℝ × ℝ) := {p | p.1 = 0} ∪ {p | p.2 = 0} ∪ ⋃ (L : Fin n) (_ : L ≠ K), rect K ∩ rect L
  have hN : volume N = 0 :=
    measure_union_null (measure_union_null null_fst_zero null_snd_zero)
      (measure_iUnion_null fun L => measure_iUnion_null fun h => hapart K L (Ne.symm h))
  refine Filter.eventuallyEq_set.2 ((measure_eq_zero_iff_ae_notMem.1 hN).mono fun p hpN => ?_)
  refine ⟨fun h => h.1.1, fun h => ⟨⟨h, ?_⟩, h, ?_⟩⟩
  · have h0 := hq K h
    have h1 : p.1 ≠ 0 := fun e => hpN (Or.inl (Or.inl e))
    have h2 : p.2 ≠ 0 := fun e => hpN (Or.inl (Or.inr e))
    exact ⟨lt_of_le_of_ne h0.1 (Ne.symm h1), lt_of_le_of_ne h0.2 (Ne.symm h2)⟩
  · intro hU
    obtain ⟨L, hL, hpL⟩ := Set.mem_iUnion₂.1 hU
    exact hpN (Or.inr (Set.mem_iUnion₂.2 ⟨L, ne_of_lt hL, h, hpL⟩))

theorem pairing_eq_sum (hhalf : HalfPlanePairing) {m : ℕ} {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hclass : Bridge.IsModeClass Γ m) (hp : IsPerturbation Γ P v G H g)
    {n : ℕ} {rect : Fin n → Set (ℝ × ℝ)} (hq : ∀ K, rect K ⊆ Set.Ici 0 ×ˢ Set.Ici 0)
    (hc : ∀ K, IsClosed (rect K)) (hapart : ∀ K K', K ≠ K' → volume (rect K ∩ rect K') = 0)
    {L : Finset (ℤ × ℤ)} {B : ℝ → Space → (Space →L[ℝ] Space)} (hB : PairInput m L rect B) :
    pairing G B = 4 * Real.pi * ∑ K, rectPair m L G B (rect K) := by
  classical
  have hbT : ∀ K, MeasurableSet (cylFold ⁻¹' firstCover rect K) := fun K =>
    continuous_cylFold.measurable (measurableSet_firstCover hc K)
  have hTrot : ∀ K φ y, axialRot φ y ∈ cylFold ⁻¹' firstCover rect K ↔ y ∈ cylFold ⁻¹' firstCover rect K := by
    intro K φ y
    simp only [Set.mem_preimage, cylFold_axialRot]
  have hCm : ∀ K, AEStronglyMeasurable (fun z : ℝ × Space => cutField rect K B z.1 z.2) volume := by
    intro K
    have e : (fun z : ℝ × Space => cutField rect K B z.1 z.2)
        = (Set.univ ×ˢ (cylFold ⁻¹' firstCover rect K)).indicator (fun z : ℝ × Space => B z.1 z.2) := by
      funext z
      simp only [cutField, Set.indicator_apply, Set.mem_prod, Set.mem_univ, true_and]
    rw [e]
    exact hB.meas.indicator (MeasurableSet.univ.prod (hbT K))
  have hC2 : ∀ K, periodLIntegral (fun σ y => matSq (cutField rect K B σ y)) < ⊤ := by
    intro K
    refine lt_of_le_of_lt ?_ hB.finite
    unfold periodLIntegral
    refine lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
    simp only [cutField]
    by_cases hy : y ∈ cylFold ⁻¹' firstCover rect K
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, matSq_zero']
      exact matSq_nonneg' _
  have hdec : pairing G B = ∑ K, pairing G (cutField rect K B) := by
    have e : B = fun σ y => ∑ K, cutField rect K B σ y := by
      funext σ y
      exact (sum_cutField rect B hB.support σ y).symm
    conv_lhs => rw [e]
    exact pairing_sum hp.measurable_gradient hp.gradient_finite _ hCm hC2
  rw [hdec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  have hper : IsTimePeriodic (cutField rect K B) := by
    intro σ y
    have e : B (σ + 1) = B σ := funext (hB.periodic σ)
    simp only [cutField, e]
  have hflip : ∀ᵐ z : ℝ × Space, ∀ u : Space,
      cutField rect K B z.1 (flipPoint z.2) u = flipPoint (cutField rect K B z.1 z.2 (flipPoint u)) := by
    filter_upwards [hB.flip] with z hz u
    simp only [cutField]
    by_cases hy : z.2 ∈ cylFold ⁻¹' firstCover rect K
    · have hy' : flipPoint z.2 ∈ cylFold ⁻¹' firstCover rect K := by
        simpa only [Set.mem_preimage, cylFold_flipPoint] using hy
      rw [Set.indicator_of_mem hy', Set.indicator_of_mem hy, hz u]
    · have hy' : flipPoint z.2 ∉ cylFold ⁻¹' firstCover rect K := by
        simpa only [Set.mem_preimage, cylFold_flipPoint] using hy
      rw [Set.indicator_of_notMem hy', Set.indicator_of_notMem hy]
      simp [flipPoint_zero]
  have hmg : ∀ ξ p, p ∈ halfPlane → modeGrad ξ (cutField rect K B) 0 (planePoint p)
      = if p ∈ firstCover rect K then modeGrad ξ B 0 (planePoint p) else 0 := by
    intro ξ p hp'
    rw [show cutField rect K B = fun σ y => (cylFold ⁻¹' firstCover rect K).indicator (B σ) y from rfl,
      modeGrad_indicator _ (hTrot K)]
    simp only [Set.mem_preimage, cylFold_planePoint hp']
  have hmodes : ∀ ξ : ℤ × ℤ, (∀ ι ∈ L, labelHarmonic m ι ≠ ξ) →
      ∀ᵐ p : ℝ × ℝ, p ∈ halfPlane → modeGrad ξ (cutField rect K B) 0 (planePoint p) = 0 := by
    intro ξ hξ
    filter_upwards [hB.modes ξ hξ] with p hpm hp'
    rw [hmg ξ p hp', hpm hp']
    split_ifs <;> rfl
  have hsupp : ∀ σ y, cutField rect K B σ y ≠ 0 → cylFold y ∈ rect K := by
    intro σ y h
    by_cases hy : y ∈ cylFold ⁻¹' firstCover rect K
    · exact firstCover_subset rect K hy
    · exact absurd (Set.indicator_of_notMem hy _) h
  have hh := hhalf m Γ P L v G H g (cutField rect K B) (rect K) hclass hp (hCm K) hper (hC2 K) hflip hmodes
    hsupp
  unfold pairing
  rw [hh]
  congr 1
  unfold rectPair
  refine Finset.sum_congr rfl fun ι _ => ?_
  congr 1
  have hgr : ∀ p ∈ halfPlane, ∀ a b, CellCalculus.gradAt m ι (cutField rect K B) a b p
      = if p ∈ firstCover rect K then CellCalculus.gradAt m ι B a b p else 0 := by
    intro p hp' a b
    simp only [CellCalculus.gradAt, labelGrad, hmg _ p hp']
    split_ifs <;> rfl
  calc (∫ p in rect K ∩ halfPlane, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
          CellCalculus.gradAt m ι G a b p * starRingEnd ℂ (CellCalculus.gradAt m ι (cutField rect K B) a b p))
      = ∫ p in rect K ∩ halfPlane, (firstCover rect K).indicator (fun p => (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
          CellCalculus.gradAt m ι G a b p * starRingEnd ℂ (CellCalculus.gradAt m ι B a b p)) p := by
        refine setIntegral_congr_fun ((hc K).measurableSet.inter measurableSet_halfPlane') fun p hp' => ?_
        by_cases h : p ∈ firstCover rect K
        · rw [Set.indicator_of_mem h]
          simp only [hgr p hp'.2, h, if_true]
        · rw [Set.indicator_of_notMem h]
          simp only [hgr p hp'.2, h, if_false, map_zero, mul_zero, Finset.sum_const_zero]
    _ = ∫ p in rect K ∩ halfPlane ∩ firstCover rect K, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
          CellCalculus.gradAt m ι G a b p * starRingEnd ℂ (CellCalculus.gradAt m ι B a b p) :=
        setIntegral_indicator (measurableSet_firstCover hc K)
    _ = ∫ p in rect K, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
          CellCalculus.gradAt m ι G a b p * starRingEnd ℂ (CellCalculus.gradAt m ι B a b p) :=
        setIntegral_congr_set (firstCover_ae hq hapart K)

end Internal

end InstancePair

end CertCell

end Breakdown
