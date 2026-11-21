import Breakdown.FracCell.UnresolvedRowClassSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

namespace UnresolvedRowClass

open CellCert CellCert.CellAnalysis SteadyCert Assembly

def allClassModes (Cl : CellClasses) : Finset ℤ := Finset.univ.biUnion Cl.modes

def pairSupport {k N slots : ℕ} (R : CellRows N slots k) (Cl : CellClasses) : Finset ℤ :=
  R.rowSet.biUnion (fun a => (allClassModes Cl).image (fun β => R.rowModeOf a - β)
    ∪ (allClassModes Cl).image (fun β => -R.rowModeOf a - β))

lemma rect_meas (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem axis_null_ae : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
  rw [ae_iff]
  have e : {p : ℝ × ℝ | ¬ p.1 ≠ 0} = ({0} : Set ℝ) ×ˢ Set.univ := by
    ext p
    simp
  rw [e, Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem open_rect_ae (K : CellBox) :
    ∀ᵐ p ∂(volume.restrict K.rect), p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂ ∧ p.1 ≠ 0 := by
  have h : (Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂ : Set (ℝ × ℝ)) =ᵐ[volume] K.rect := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc
  rw [← Measure.restrict_congr_set h]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo), ae_restrict_of_ae axis_null_ae]
    with p hp h0
  exact ⟨hp, h0⟩

lemma coupling_zero {α : ℝ} {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {Cl : CellClasses} {slots : ℕ} {R : CellRows N slots k} (hd : IsCellData α c K S B Cl R)
    {a : Fin N} (ha : a ∈ R.rowSet) {n : ℤ} (hn : n ∉ S.resolved ∪ S.band) (hF : n ∉ pairSupport R Cl)
    {p : ℝ × ℝ} (hpK : p ∈ K.rect) (hp : p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂) (hp1 : p.1 ≠ 0)
    (m : ℤ) :
    crossC (conjVec3 (modeVec c.order (m - n) c.modelVelocity p.1 p.2)) (CellScalars.rowMode c a m p) = 0 ∧
    crossC (CellScalars.rowMode c a m p) (conjVec3 (modeVec c.order (m - n) c.modelCurl p.1 p.2)) = 0 := by
  by_cases h1 : m = R.rowModeOf a ∨ m = -R.rowModeOf a
  · have hmr : m ∈ S.resolved := by
      rcases h1 with h | h
      · rw [h]; exact hd.row_mode_resolved a ha
      · rw [h]; exact (hd.scalars.resolved_symm _).1 (hd.row_mode_resolved a ha)
    have hv : modeVec c.order (m - n) c.modelVelocity p.1 p.2 = 0 ∧
        modeVec c.order (m - n) c.modelCurl p.1 p.2 = 0 := by
      by_contra hne
      rw [not_and_or] at hne
      obtain ⟨i, hi⟩ := hd.class_cover m hmr n hn ⟨p, hp, hp1, by tauto⟩
      apply hF
      simp only [pairSupport, Finset.mem_biUnion, Finset.mem_union, Finset.mem_image, allClassModes,
        Finset.mem_univ, true_and]
      refine ⟨a, ha, ?_⟩
      rcases h1 with h | h
      · exact Or.inl ⟨m - n, ⟨i, hi⟩, by rw [h]; ring⟩
      · exact Or.inr ⟨m - n, ⟨i, hi⟩, by rw [h]; ring⟩
    rw [hv.1, hv.2]
    constructor <;> funext j <;> fin_cases j <;> simp [crossC, conjVec3]
  · rw [not_or] at h1
    rw [hd.row_mode_of a ha m h1.1 h1.2 p hpK]
    constructor <;> funext j <;> fin_cases j <;> simp [crossC, conjVec3]

lemma pairAt_zero {α : ℝ} {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {Cl : CellClasses} {slots : ℕ} {R : CellRows N slots k} (hd : IsCellData α c K S B Cl R) (x : FieldTuple k)
    {a : Fin N} (ha : a ∈ R.rowSet) {n : ℤ} (hn : n ∉ S.resolved ∪ S.band) (hF : n ∉ pairSupport R Cl)
    {p : ℝ × ℝ} (hpK : p ∈ K.rect) (hp : p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂) (hp1 : p.1 ≠ 0) :
    CellScalars.unresolvedPairAt c K R x a n p = 0 := by
  have hs : CellScalars.rowCouplingStrain c K R a n p = 0 := by
    funext i l
    simp only [CellScalars.rowCouplingStrain, Pi.zero_apply]
    rw [Finset.sum_eq_zero (fun m _ => by rw [(coupling_zero hd ha hn hF hpK hp hp1 m).1]; simp [curlAdj]), mul_zero]
  have hv : CellScalars.rowCouplingVelocity c K R a n p = 0 := by
    funext i
    simp only [CellScalars.rowCouplingVelocity, Pi.zero_apply]
    rw [Finset.sum_eq_zero (fun m _ => by rw [(coupling_zero hd ha hn hF hpK hp hp1 m).2]; rfl), mul_zero]
  simp [CellScalars.unresolvedPairAt, hs, hv, entryPairing, CellScalars.vecPair]

lemma rowPair_eq {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {slots : ℕ} {R : CellRows N slots k} (x : FieldTuple k) (a : Fin N) (n : ℤ)
    (hI : n ∉ S.resolved ∪ S.band → IntegrableOn (CellScalars.unresolvedPairAt c K R x a n) K.rect) :
    CellScalars.unresolvedRowPair c K S R x a n = ∫ p in K.rect, CellScalars.unresolvedPairPoint c K S R x a n p := by
  by_cases hn : n ∈ S.resolved ∪ S.band
  · simp [CellScalars.unresolvedRowPair, CellScalars.unresolvedPairPoint, hn]
  · simp only [CellScalars.unresolvedRowPair, CellScalars.unresolvedPairPoint, hn, if_false]
    exact (integral_re (hI hn)).symm

lemma point_integrable {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {slots : ℕ} {R : CellRows N slots k} (x : FieldTuple k) (a : Fin N) (n : ℤ)
    (hI : n ∉ S.resolved ∪ S.band → IntegrableOn (CellScalars.unresolvedPairAt c K R x a n) K.rect) :
    IntegrableOn (fun p => CellScalars.unresolvedPairPoint c K S R x a n p) K.rect := by
  by_cases hn : n ∈ S.resolved ∪ S.band
  · simp only [CellScalars.unresolvedPairPoint, hn, if_true]
    exact integrableOn_zero
  · simp only [CellScalars.unresolvedPairPoint, hn, if_false]
    exact (hI hn).re

end UnresolvedRowClass

end FracInternal

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly FracInternal.UnresolvedRowClass

theorem unresolvedRowClass_of (hP : UnresolvedRowPointStatement) (hI : UnresolvedPairIntegrableStatement)
    (hQ : ClassRowSqStatement) (hC : UnresolvedChargeFiniteStatement) : UnresolvedRowClassStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx μ hμ
  have hmeas := rect_meas K
  have hI' : ∀ a ∈ R.rowSet, ∀ n, n ∉ S.resolved ∪ S.band →
      IntegrableOn (CellScalars.unresolvedPairAt c K R x a n) K.rect :=
    fun a ha n hn => hI α h1 h2 c hc K S B Cl R hd hw x hx a ha n hn
  have hts : ∀ a ∈ R.rowSet, ∑' n : ℤ, CellScalars.unresolvedRowPair c K S R x a n
      = ∑ n ∈ pairSupport R Cl, ∫ p in K.rect, CellScalars.unresolvedPairPoint c K S R x a n p := by
    intro a ha
    rw [tsum_eq_sum (s := pairSupport R Cl)]
    · exact Finset.sum_congr rfl fun n _ => rowPair_eq x a n (hI' a ha n)
    · intro n hF
      by_cases hn : n ∈ S.resolved ∪ S.band
      · simp [CellScalars.unresolvedRowPair, hn]
      · simp only [CellScalars.unresolvedRowPair, hn, if_false]
        show (∫ p in K.rect, CellScalars.unresolvedPairAt c K R x a n p).re = 0
        have hz : (fun p => CellScalars.unresolvedPairAt c K R x a n p) =ᵐ[volume.restrict K.rect] fun _ => 0 := by
          filter_upwards [open_rect_ae K, ae_restrict_mem hmeas] with p hp hpK
          exact pairAt_zero hd x ha hn hF hpK hp.1 hp.2
        rw [integral_congr_ae hz]
        simp
  have hpi : ∀ a ∈ R.rowSet, ∀ n,
      IntegrableOn (fun p => CellScalars.unresolvedPairPoint c K S R x a n p) K.rect :=
    fun a ha n => point_integrable x a n (hI' a ha n)
  set G : ℝ × ℝ → ℝ := fun p => ∑ a ∈ R.rowSet, μ a * ∑ n ∈ pairSupport R Cl,
    CellScalars.unresolvedPairPoint c K S R x a n p with hG
  have hGi : IntegrableOn G K.rect :=
    integrable_finsetSum _ fun a ha => (integrable_finsetSum _ fun n _ => hpi a ha n).const_mul (μ a)
  have hL : ∑ a ∈ R.rowSet, μ a * ∑' n : ℤ, CellScalars.unresolvedRowPair c K S R x a n
      = ∫ p in K.rect, G p := by
    rw [hG, integral_finsetSum _ fun a ha => (integrable_finsetSum _ fun n _ => hpi a ha n).const_mul (μ a)]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hts a ha, integral_const_mul, integral_finsetSum _ fun n _ => hpi a ha n]
  obtain ⟨hCi, hCle⟩ := hC α h1 h2 c hc K S B Cl R hd hw x hx (pairSupport R Cl)
  have hQi : ∀ i, IntegrableOn (fun p => p.1 * CellScalars.classRowSq c R Cl μ i p / Cl.rowWeight i) K.rect :=
    fun i => (hQ α h1 h2 c hc K S B Cl R hd hw μ i).1.div_const _
  have hRi : IntegrableOn (fun p => p.1 * ∑ n ∈ pairSupport R Cl, CellScalars.unresolvedChargePoint c S Cl x n p
      + ∑ i, p.1 * CellScalars.classRowSq c R Cl μ i p / Cl.rowWeight i) K.rect :=
    hCi.add (integrable_finsetSum _ fun i _ => hQi i)
  have hmono : ∫ p in K.rect, -(2 * G p) ≤ ∫ p in K.rect,
      (p.1 * ∑ n ∈ pairSupport R Cl, CellScalars.unresolvedChargePoint c S Cl x n p
        + ∑ i, p.1 * CellScalars.classRowSq c R Cl μ i p / Cl.rowWeight i) :=
    integral_mono_ae (hGi.const_mul 2).neg hRi (by
      filter_upwards [open_rect_ae K] with p hp
      exact hP α h1 h2 c hc K S B Cl R hd hw x hx μ hμ p hp.1 hp.2 (pairSupport R Cl))
  rw [integral_add hCi (integrable_finsetSum _ fun i _ => hQi i), integral_finsetSum _ fun i _ => hQi i] at hmono
  have hneg : ∫ p in K.rect, -(2 * G p) = -(2 * ∫ p in K.rect, G p) := by
    rw [integral_neg, integral_const_mul]
  rw [hneg] at hmono
  have hcls : ∑ i, ∫ p in K.rect, p.1 * CellScalars.classRowSq c R Cl μ i p / Cl.rowWeight i
      ≤ ∑ a ∈ R.rowSet, R.classRowWeight a * μ a ^ 2 := by
    calc ∑ i, ∫ p in K.rect, p.1 * CellScalars.classRowSq c R Cl μ i p / Cl.rowWeight i
        ≤ ∑ i, (∑ a ∈ R.rowSet.filter (fun a => R.rowModeOf a ∈ Cl.resolvedPart i), μ a ^ 2 / (4 * Real.pi))
            / Cl.rowWeight i := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [integral_div]
          exact div_le_div_of_nonneg_right (hQ α h1 h2 c hc K S B Cl R hd hw μ i).2
            (hd.class_weights_pos i).2.le
      _ = ∑ a ∈ R.rowSet, μ a ^ 2 * ∑ i, (if R.rowModeOf a ∈ Cl.resolvedPart i then
            1 / (4 * Real.pi * Cl.rowWeight i) else 0) := by
          simp_rw [Finset.sum_filter, Finset.sum_div, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
          split_ifs
          · have := (hd.class_weights_pos i).2
            field_simp
          · simp
      _ ≤ ∑ a ∈ R.rowSet, R.classRowWeight a * μ a ^ 2 := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [mul_comm (R.classRowWeight a)]
          exact mul_le_mul_of_nonneg_left (hd.classRowWeight_ge a ha) (sq_nonneg _)
  rw [hL]
  linarith

end CellAnalysis

end CellCert

end Breakdown
