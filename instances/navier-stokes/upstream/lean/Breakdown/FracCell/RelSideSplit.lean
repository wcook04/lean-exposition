import Breakdown.FracCell.StCoordsProof

open MeasureTheory Set

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

namespace RelSideSplit.Internal

theorem icc_ae_union {ι : Type*} (Z : Finset ι) (lo hi : ι → ℝ) (z₁ z₂ : ℝ)
    (hin : ∀ s ∈ Z, z₁ ≤ lo s ∧ hi s ≤ z₂)
    (hcov : ∀ u, z₁ ≤ u ∧ u ≤ z₂ → ∃ s ∈ Z, lo s ≤ u ∧ u ≤ hi s) :
    (Icc z₁ z₂ : Set ℝ) =ᵐ[volume] ⋃ s ∈ Z, Ioc (lo s) (hi s) := by
  classical
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null (t := ((Z.image lo : Finset ℝ) : Set ℝ))
    · intro u hu
      obtain ⟨hu1, hu2⟩ := hu
      obtain ⟨s, hs, h1, h2⟩ := hcov u hu1
      by_cases h : lo s = u
      · exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨s, hs, h⟩)
      · exact absurd (mem_iUnion₂.2 ⟨s, hs, (show u ∈ Ioc (lo s) (hi s) from ⟨lt_of_le_of_ne h1 h, h2⟩)⟩) hu2
    · exact (Z.image lo).finite_toSet.measure_zero _
  · have : (⋃ s ∈ Z, Ioc (lo s) (hi s)) \ Icc z₁ z₂ = ∅ := by
      ext u
      simp only [mem_sdiff, mem_iUnion, mem_Ioc, mem_Icc, mem_empty_iff_false, iff_false, not_and]
      rintro ⟨s, hs, h1, h2⟩
      have := hin s hs
      exact fun h => h (by linarith) (by linarith)
    rw [this, measure_empty]

theorem split_snd {ι : Type*} (Z : Finset ι) (lo hi : ι → ℝ) (z₁ z₂ : ℝ) (A : Set ℝ) (hA : MeasurableSet A)
    (f : ℝ × ℝ → ℂ) (hin : ∀ s ∈ Z, z₁ ≤ lo s ∧ hi s ≤ z₂)
    (hcov : ∀ u, z₁ ≤ u ∧ u ≤ z₂ → ∃ s ∈ Z, lo s ≤ u ∧ u ≤ hi s)
    (hdis : ∀ s ∈ Z, ∀ s' ∈ Z, s ≠ s' → hi s ≤ lo s' ∨ hi s' ≤ lo s)
    (hf : IntegrableOn f (A ×ˢ Icc z₁ z₂)) :
    ∫ p in A ×ˢ Icc z₁ z₂, f p = ∑ s ∈ Z, ∫ p in A ×ˢ Icc (lo s) (hi s), f p := by
  have h1 : (A ×ˢ Icc z₁ z₂ : Set (ℝ × ℝ)) =ᵐ[volume] A ×ˢ ⋃ s ∈ Z, Ioc (lo s) (hi s) := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq (ae_eq_refl _) (icc_ae_union Z lo hi z₁ z₂ hin hcov)
  rw [setIntegral_congr_set h1, prod_iUnion₂, integral_biUnion_finset]
  · refine Finset.sum_congr rfl fun s _ => setIntegral_congr_set ?_
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq (ae_eq_refl _) Ioc_ae_eq_Icc
  · exact fun s _ => hA.prod measurableSet_Ioc
  · intro s hs s' hs' hne
    show Disjoint (A ×ˢ Ioc (lo s) (hi s)) (A ×ˢ Ioc (lo s') (hi s'))
    refine Set.disjoint_prod.2 (Or.inr ?_)
    refine Set.disjoint_left.2 fun u h1 h2 => ?_
    rcases hdis s hs s' hs' hne with h | h
    · exact absurd (h1.2.trans h) (not_le.2 h2.1)
    · exact absurd (h2.2.trans h) (not_le.2 h1.1)
  · intro s hs
    refine hf.mono_set (prod_mono le_rfl fun u hu => ⟨?_, ?_⟩)
    · exact (hin s hs).1.trans hu.1.le
    · exact hu.2.trans (hin s hs).2

theorem split_fst {ι : Type*} (Z : Finset ι) (lo hi : ι → ℝ) (z₁ z₂ : ℝ) (A : Set ℝ) (hA : MeasurableSet A)
    (f : ℝ × ℝ → ℂ) (hin : ∀ s ∈ Z, z₁ ≤ lo s ∧ hi s ≤ z₂)
    (hcov : ∀ u, z₁ ≤ u ∧ u ≤ z₂ → ∃ s ∈ Z, lo s ≤ u ∧ u ≤ hi s)
    (hdis : ∀ s ∈ Z, ∀ s' ∈ Z, s ≠ s' → hi s ≤ lo s' ∨ hi s' ≤ lo s)
    (hf : IntegrableOn f (Icc z₁ z₂ ×ˢ A)) :
    ∫ p in Icc z₁ z₂ ×ˢ A, f p = ∑ s ∈ Z, ∫ p in Icc (lo s) (hi s) ×ˢ A, f p := by
  have h1 : (Icc z₁ z₂ ×ˢ A : Set (ℝ × ℝ)) =ᵐ[volume] (⋃ s ∈ Z, Ioc (lo s) (hi s)) ×ˢ A := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq (icc_ae_union Z lo hi z₁ z₂ hin hcov) (ae_eq_refl _)
  rw [setIntegral_congr_set h1, iUnion₂_prod_const, integral_biUnion_finset]
  · refine Finset.sum_congr rfl fun s _ => setIntegral_congr_set ?_
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioc_ae_eq_Icc (ae_eq_refl _)
  · exact fun s _ => measurableSet_Ioc.prod hA
  · intro s hs s' hs' hne
    show Disjoint (Ioc (lo s) (hi s) ×ˢ A) (Ioc (lo s') (hi s') ×ˢ A)
    refine Set.disjoint_prod.2 (Or.inl ?_)
    refine Set.disjoint_left.2 fun u h1 h2 => ?_
    rcases hdis s hs s' hs' hne with h | h
    · exact absurd (h1.2.trans h) (not_le.2 h2.1)
    · exact absurd (h2.2.trans h) (not_le.2 h1.1)
  · intro s hs
    refine hf.mono_set (prod_mono (fun u hu => ⟨?_, ?_⟩) le_rfl)
    · exact (hin s hs).1.trans hu.1.le
    · exact hu.2.trans (hin s hs).2

def polyOf (C : ℕ → ℕ → ℝ) (d : ℕ) (u : ℝ) : ℝ := ∑ i ∈ Finset.range (d + 1), C d i * u ^ i

theorem test_cont (C : ℕ → ℕ → ℝ) (d : ℕ) : Continuous (polyOf C d) := by
  unfold polyOf
  fun_prop

theorem mono_mem (C : ℕ → ℕ → ℝ) (hlead : ∀ d, C d d ≠ 0) (M : ℕ) :
    ∀ m ≤ M, (fun u : ℝ => u ^ m) ∈ Submodule.span ℝ (range fun d : Fin (M + 1) => polyOf C d) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hfun : (fun u : ℝ => u ^ m) = (C m m)⁻¹ •
        (polyOf C m - ∑ i ∈ Finset.range m, C m i • fun u : ℝ => u ^ i) := by
      funext u
      simp only [polyOf, Finset.sum_range_succ, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply,
        smul_eq_mul, add_sub_cancel_left]
      field_simp [hlead m]
    rw [hfun]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
    · exact Submodule.subset_span ⟨⟨m, by omega⟩, rfl⟩
    · refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (ih i (Finset.mem_range.1 hi) ?_)
      have := Finset.mem_range.1 hi
      omega

theorem poly_mem (C : ℕ → ℕ → ℝ) (hlead : ∀ d, C d d ≠ 0) (M m j : ℕ) (hm : m + j ≤ M)
    (a : ℕ → ℝ) (t : ℝ → ℝ) (ht : ∀ u, t u = ∑ i ∈ Finset.range (m + 1), a i * u ^ (i + j)) :
    t ∈ Submodule.span ℝ (range fun d : Fin (M + 1) => polyOf C d) := by
  have : t = ∑ i ∈ Finset.range (m + 1), a i • fun u : ℝ => u ^ (i + j) := by
    funext u
    simp only [ht, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [this]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (mono_mem C hlead M _ ?_)
  have := Finset.mem_range.1 hi
  omega

theorem expand (C : ℕ → ℕ → ℝ) (lo hi : ℝ) (M : ℕ)
    (horth : ∀ d d', d ≤ M → d' ≤ M →
      ∫ u in Icc lo hi, polyOf C d u * polyOf C d' u = if d = d' then 1 else 0)
    (t : ℝ → ℝ) (ht : t ∈ Submodule.span ℝ (range fun d : Fin (M + 1) => polyOf C d)) (u : ℝ) :
    t u = ∑ d : Fin (M + 1), (∫ v in Icc lo hi, t v * polyOf C d v) * polyOf C d u := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 ht
  have hpt : ∀ v, t v = ∑ d : Fin (M + 1), c d * polyOf C d v := by
    intro v
    rw [← hc]
    simp [Finset.sum_apply]
  have hcoef : ∀ d' : Fin (M + 1), ∫ v in Icc lo hi, t v * polyOf C d' v = c d' := by
    intro d'
    simp_rw [hpt, Finset.sum_mul]
    rw [integral_finsetSum]
    · simp_rw [mul_assoc, integral_const_mul]
      rw [Finset.sum_eq_single d']
      · rw [horth _ _ (Nat.lt_succ_iff.1 d'.isLt) (Nat.lt_succ_iff.1 d'.isLt)]
        simp
      · intro b _ hb
        rw [horth _ _ (Nat.lt_succ_iff.1 b.isLt) (Nat.lt_succ_iff.1 d'.isLt), if_neg (fun h => hb (Fin.ext h))]
        simp
      · simp
    · intro d _
      have h1 := test_cont C d
      have h2 := test_cont C d'
      exact Continuous.integrableOn_Icc (by fun_prop)
  rw [hpt u]
  simp_rw [hcoef]

theorem seg_snd (C : ℕ → ℕ → ℝ) (lo hi : ℝ) (M : ℕ)
    (horth : ∀ d d', d ≤ M → d' ≤ M →
      ∫ u in Icc lo hi, polyOf C d u * polyOf C d' u = if d = d' then 1 else 0)
    (t : ℝ → ℝ) (ht : t ∈ Submodule.span ℝ (range fun d : Fin (M + 1) => polyOf C d))
    (A : Set ℝ) (hA : IsCompact A) (g : ℝ × ℝ → ℂ) (hg : IntegrableOn g (A ×ˢ Icc lo hi)) :
    ∫ p in A ×ˢ Icc lo hi, g p * ((t p.2 : ℝ) : ℂ) =
      ∑ d : Fin (M + 1), (((∫ v in Icc lo hi, t v * polyOf C d v : ℝ)) : ℂ) *
        ∫ p in A ×ˢ Icc lo hi, g p * ((polyOf C d p.2 : ℝ) : ℂ) := by
  have hK : IsCompact (A ×ˢ Icc lo hi) := hA.prod isCompact_Icc
  have h1 : ∀ p : ℝ × ℝ, g p * ((t p.2 : ℝ) : ℂ) = ∑ d : Fin (M + 1),
      (((∫ v in Icc lo hi, t v * polyOf C d v : ℝ)) : ℂ) * (g p * ((polyOf C d p.2 : ℝ) : ℂ)) := by
    intro p
    rw [expand C lo hi M horth t ht p.2, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Complex.ofReal_mul]
    ring
  simp_rw [h1]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro d _
    have hc := test_cont C d
    exact (hg.mul_continuousOn (by fun_prop) hK).const_mul _

theorem seg_fst (C : ℕ → ℕ → ℝ) (lo hi : ℝ) (M : ℕ)
    (horth : ∀ d d', d ≤ M → d' ≤ M →
      ∫ u in Icc lo hi, polyOf C d u * polyOf C d' u = if d = d' then 1 else 0)
    (t : ℝ → ℝ) (ht : t ∈ Submodule.span ℝ (range fun d : Fin (M + 1) => polyOf C d))
    (A : Set ℝ) (hA : IsCompact A) (g : ℝ × ℝ → ℂ) (hg : IntegrableOn g (Icc lo hi ×ˢ A)) :
    ∫ p in Icc lo hi ×ˢ A, g p * ((t p.1 : ℝ) : ℂ) =
      ∑ d : Fin (M + 1), (((∫ v in Icc lo hi, t v * polyOf C d v : ℝ)) : ℂ) *
        ∫ p in Icc lo hi ×ˢ A, g p * ((polyOf C d p.1 : ℝ) : ℂ) := by
  have hK : IsCompact (Icc lo hi ×ˢ A) := isCompact_Icc.prod hA
  have h1 : ∀ p : ℝ × ℝ, g p * ((t p.1 : ℝ) : ℂ) = ∑ d : Fin (M + 1),
      (((∫ v in Icc lo hi, t v * polyOf C d v : ℝ)) : ℂ) * (g p * ((polyOf C d p.1 : ℝ) : ℂ)) := by
    intro p
    rw [expand C lo hi M horth t ht p.1, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Complex.ofReal_mul]
    ring
  simp_rw [h1]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro d _
    have hc := test_cont C d
    exact (hg.mul_continuousOn (by fun_prop) hK).const_mul _

theorem strip_snd {ι : Type*} (Z : Finset ι) (C : ι → ℕ → ℕ → ℝ) (lo hi : ι → ℝ) (M : ℕ) (z₁ z₂ : ℝ)
    (hin : ∀ s ∈ Z, z₁ ≤ lo s ∧ hi s ≤ z₂)
    (hcov : ∀ u, z₁ ≤ u ∧ u ≤ z₂ → ∃ s ∈ Z, lo s ≤ u ∧ u ≤ hi s)
    (hdis : ∀ s ∈ Z, ∀ s' ∈ Z, s ≠ s' → hi s ≤ lo s' ∨ hi s' ≤ lo s)
    (horth : ∀ s ∈ Z, ∀ d d', d ≤ M → d' ≤ M →
      ∫ u in Icc (lo s) (hi s), polyOf (C s) d u * polyOf (C s) d' u = if d = d' then 1 else 0)
    (t : ℝ → ℝ) (htc : Continuous t)
    (ht : ∀ s ∈ Z, t ∈ Submodule.span ℝ (range fun d : Fin (M + 1) => polyOf (C s) d))
    (A : Set ℝ) (hA : IsCompact A) (g : ℝ × ℝ → ℂ) (hg : IntegrableOn g (A ×ˢ Icc z₁ z₂)) :
    ∫ p in A ×ˢ Icc z₁ z₂, g p * ((t p.2 : ℝ) : ℂ) =
      ∑ s ∈ Z, ∑ d : Fin (M + 1), (((∫ v in Icc (lo s) (hi s), t v * polyOf (C s) d v : ℝ)) : ℂ) *
        ∫ p in A ×ˢ Icc (lo s) (hi s), g p * ((polyOf (C s) d p.2 : ℝ) : ℂ) := by
  rw [split_snd Z lo hi z₁ z₂ A hA.measurableSet _ hin hcov hdis
    (hg.mul_continuousOn (by fun_prop) (hA.prod isCompact_Icc))]
  refine Finset.sum_congr rfl fun s hs => ?_
  refine seg_snd (C s) (lo s) (hi s) M (horth s hs) t (ht s hs) A hA g (hg.mono_set ?_)
  exact prod_mono le_rfl fun u hu => ⟨(hin s hs).1.trans hu.1, hu.2.trans (hin s hs).2⟩

theorem strip_fst {ι : Type*} (Z : Finset ι) (C : ι → ℕ → ℕ → ℝ) (lo hi : ι → ℝ) (M : ℕ) (z₁ z₂ : ℝ)
    (hin : ∀ s ∈ Z, z₁ ≤ lo s ∧ hi s ≤ z₂)
    (hcov : ∀ u, z₁ ≤ u ∧ u ≤ z₂ → ∃ s ∈ Z, lo s ≤ u ∧ u ≤ hi s)
    (hdis : ∀ s ∈ Z, ∀ s' ∈ Z, s ≠ s' → hi s ≤ lo s' ∨ hi s' ≤ lo s)
    (horth : ∀ s ∈ Z, ∀ d d', d ≤ M → d' ≤ M →
      ∫ u in Icc (lo s) (hi s), polyOf (C s) d u * polyOf (C s) d' u = if d = d' then 1 else 0)
    (t : ℝ → ℝ) (htc : Continuous t)
    (ht : ∀ s ∈ Z, t ∈ Submodule.span ℝ (range fun d : Fin (M + 1) => polyOf (C s) d))
    (A : Set ℝ) (hA : IsCompact A) (g : ℝ × ℝ → ℂ) (hg : IntegrableOn g (Icc z₁ z₂ ×ˢ A)) :
    ∫ p in Icc z₁ z₂ ×ˢ A, g p * ((t p.1 : ℝ) : ℂ) =
      ∑ s ∈ Z, ∑ d : Fin (M + 1), (((∫ v in Icc (lo s) (hi s), t v * polyOf (C s) d v : ℝ)) : ℂ) *
        ∫ p in Icc (lo s) (hi s) ×ˢ A, g p * ((polyOf (C s) d p.1 : ℝ) : ℂ) := by
  rw [split_fst Z lo hi z₁ z₂ A hA.measurableSet _ hin hcov hdis
    (hg.mul_continuousOn (by fun_prop) (isCompact_Icc.prod hA))]
  refine Finset.sum_congr rfl fun s hs => ?_
  refine seg_fst (C s) (lo s) (hi s) M (horth s hs) t (ht s hs) A hA g (hg.mono_set ?_)
  exact prod_mono (fun u hu => ⟨(hin s hs).1.trans hu.1, hu.2.trans (hin s hs).2⟩) le_rfl


theorem test_eq (S : FaceSegment) (d : ℕ) (u : ℝ) : S.test d u = polyOf S.testCoef d u := rfl

theorem radial_side (L : CellLayout) (Z : Finset (Fin L.segCount)) (c₀ o₀ z₁ z₂ : ℝ)
    (hseg : ∀ s ∈ Z, (L.segment s).radial = true ∧ (L.segment s).level = c₀ ∧ (L.segment s).other = o₀ ∧
      z₁ ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ z₂)
    (hcov : ∀ u, z₁ ≤ u ∧ u ≤ z₂ → ∃ s ∈ Z, (L.segment s).lo ≤ u ∧ u ≤ (L.segment s).hi)
    (hdis : ∀ s ∈ Z, ∀ s' ∈ Z, s ≠ s' →
      (L.segment s).hi ≤ (L.segment s').lo ∨ (L.segment s').hi ≤ (L.segment s).lo)
    (horth : ∀ s d d', d ≤ L.degSide + 1 → d' ≤ L.degSide + 1 →
      ∫ u in Icc (L.segment s).lo (L.segment s).hi, (L.segment s).test d u * (L.segment s).test d' u =
        if d = d' then 1 else 0)
    (t : ℝ → ℝ) (htc : Continuous t)
    (ht : ∀ s ∈ Z, t ∈ Submodule.span ℝ (range fun d : Fin (L.degSide + 1 + 1) => polyOf (L.segment s).testCoef d))
    (F dF dFz : ℝ × ℝ → ℂ)
    (hg : IntegrableOn (fun p => ((1 / (c₀ - o₀) : ℝ) : ℂ) * F p + (((p.1 - o₀) / (c₀ - o₀) : ℝ) : ℂ) * dF p)
      (Icc (min c₀ o₀) (max c₀ o₀) ×ˢ Icc z₁ z₂)) :
    radialStripMoment c₀ o₀ z₁ z₂ F dF t = ∑ s ∈ Z, ∑ d' : Fin (L.degSide + 2),
      ((L.segmentTestPair s t d' : ℝ) : ℂ) * (L.segment s).moment false F dF dFz d' := by
  unfold radialStripMoment
  rw [strip_snd Z (fun s => (L.segment s).testCoef) (fun s => (L.segment s).lo) (fun s => (L.segment s).hi)
    (L.degSide + 1) z₁ z₂ (fun s hs => ⟨(hseg s hs).2.2.2.1, (hseg s hs).2.2.2.2⟩) hcov hdis
    (fun s _ d d' hd hd' => horth s d d' hd hd') t htc ht _ isCompact_Icc _ hg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  obtain ⟨hr, hlv, hot, -, -⟩ := hseg s hs
  simp only [FaceSegment.moment, hr, if_true, radialStripMoment, hlv, hot, CellLayout.segmentTestPair, test_eq]
  ring

theorem height_side (L : CellLayout) (Z : Finset (Fin L.segCount)) (c₀ o₀ r₁ r₂ : ℝ)
    (hseg : ∀ s ∈ Z, (L.segment s).radial = false ∧ (L.segment s).level = c₀ ∧ (L.segment s).other = o₀ ∧
      r₁ ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ r₂)
    (hcov : ∀ u, r₁ ≤ u ∧ u ≤ r₂ → ∃ s ∈ Z, (L.segment s).lo ≤ u ∧ u ≤ (L.segment s).hi)
    (hdis : ∀ s ∈ Z, ∀ s' ∈ Z, s ≠ s' →
      (L.segment s).hi ≤ (L.segment s').lo ∨ (L.segment s').hi ≤ (L.segment s).lo)
    (horth : ∀ s d d', d ≤ L.degSide + 1 → d' ≤ L.degSide + 1 →
      ∫ u in Icc (L.segment s).lo (L.segment s).hi, (L.segment s).test d u * (L.segment s).test d' u =
        if d = d' then 1 else 0)
    (t : ℝ → ℝ) (htc : Continuous t)
    (ht : ∀ s ∈ Z, t ∈ Submodule.span ℝ (range fun d : Fin (L.degSide + 1 + 1) => polyOf (L.segment s).testCoef d))
    (F dF dFz : ℝ × ℝ → ℂ)
    (hg : IntegrableOn (fun p => ((1 / (c₀ - o₀) : ℝ) : ℂ) * F p + (((p.2 - o₀) / (c₀ - o₀) : ℝ) : ℂ) * dFz p)
      (Icc r₁ r₂ ×ˢ Icc (min c₀ o₀) (max c₀ o₀))) :
    heightStripMoment c₀ o₀ r₁ r₂ (fun _ => 1) F dFz t = ∑ s ∈ Z, ∑ d' : Fin (L.degSide + 2),
      ((L.segmentTestPair s t d' : ℝ) : ℂ) * (L.segment s).moment false F dF dFz d' := by
  unfold heightStripMoment
  simp only [one_mul]
  rw [strip_fst Z (fun s => (L.segment s).testCoef) (fun s => (L.segment s).lo) (fun s => (L.segment s).hi)
    (L.degSide + 1) r₁ r₂ (fun s hs => ⟨(hseg s hs).2.2.2.1, (hseg s hs).2.2.2.2⟩) hcov hdis
    (fun s _ d d' hd hd' => horth s d d' hd hd') t htc ht _ isCompact_Icc _ hg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  obtain ⟨hr, hlv, hot, -, -⟩ := hseg s hs
  simp only [FaceSegment.moment, hr, Bool.false_eq_true, if_false, heightStripMoment, hlv, hot,
    CellLayout.segmentTestPair, test_eq, one_mul]
  ring

theorem pair_row (L : CellLayout) (f : L.Datum → ℂ) (n : L.modes) (e : Fin 4) (a : Fin 3)
    (d : Fin (L.degCoef + 1)) (w : Fin L.segCount → Fin (L.degSide + 2) → ℝ) (Z : Finset (Fin L.segCount)) :
    ∑ D, (L.extraAt n e a d - ∑ s ∈ Z, ∑ d' : Fin (L.degSide + 2), ((w s d' : ℝ) : ℂ) •
      L.unitAt (CellDatum.sideVelocity n s a d')) D * f D =
    f (CellDatum.extraVelocity n e a d) -
      ∑ s ∈ Z, ∑ d' : Fin (L.degSide + 2), ((w s d' : ℝ) : ℂ) * f (CellDatum.sideVelocity n s a d') := by
  have h1 : L.extraAt n e a d = L.unitAt (CellDatum.extraVelocity n e a d) := by
    simp [CellLayout.extraAt, d.isLt]
  rw [h1]
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, CellLayout.unitAt]
  congr 1
  · simp [Pi.single_apply]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d' _ => ?_
    simp [Pi.single_apply]

theorem sideTest_cont (L : CellLayout) (e : Fin 4) (d : ℕ) : Continuous (L.sideTest e d) := by
  unfold CellLayout.sideTest CellBases.heightPoly CellBases.radialPoly
  split_ifs <;> fun_prop

theorem mem_lo (L : CellLayout) (S : FaceSegment) (hlead : ∀ d, S.testCoef d d ≠ 0) (e : Fin 4) (he : e.val < 2)
    (d : ℕ) (hd : d ≤ L.degSide) :
    L.sideTest e d ∈ Submodule.span ℝ (range fun d : Fin (L.degSide + 1 + 1) => polyOf S.testCoef d) :=
  poly_mem S.testCoef hlead (L.degSide + 1) d 0 (by omega) (L.bases.heightCoef d) _
    (fun u => by simp [CellLayout.sideTest, he, CellBases.heightPoly])

theorem mem_hi (L : CellLayout) (S : FaceSegment) (hlead : ∀ d, S.testCoef d d ≠ 0) (e : Fin 4)
    (he : ¬ e.val < 2) (d : ℕ)
    (hd : if L.box.r₁ = 0 then d ≤ L.degSide else d ≤ L.degSide + 1) :
    L.sideTest e d ∈ Submodule.span ℝ (range fun d : Fin (L.degSide + 1 + 1) => polyOf S.testCoef d) := by
  by_cases h0 : L.box.r₁ = 0
  · rw [if_pos h0] at hd
    refine poly_mem S.testCoef hlead (L.degSide + 1) d 1 (by omega) (L.bases.radialCoef d) _ (fun u => ?_)
    simp only [CellLayout.sideTest, he, if_false, if_pos h0, CellBases.radialPoly, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [if_neg h0] at hd
    refine poly_mem S.testCoef hlead (L.degSide + 1) d 0 (by omega) (L.bases.radialCoef d) _ (fun u => ?_)
    simp [CellLayout.sideTest, he, h0, CellBases.radialPoly]

end RelSideSplit.Internal

def ModeRectIntegrableStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x → ∀ (n : ℤ) (a b : Fin 3),
      IntegrableOn (L.velMode n x a) K.rect ∧ IntegrableOn (L.gradModeOf n x a b) K.rect

namespace RelSideSplit.Internal

theorem seg_radial {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hL : IsCellLayout c K S B L) (s : Fin L.segCount) (hr : (L.segment s).radial = true) :
    K.z₁ ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ K.z₂ ∧ (L.segment s).other = K.r₁ + K.r₂ - (L.segment s).level := by
  rcases hL.segment_on_side s with h | h
  · exact ⟨h.2.2.1, h.2.2.2.1, (hL.segment_other_in_box s).1 hr⟩
  · exact absurd hr h.1

theorem seg_height {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hL : IsCellLayout c K S B L) (s : Fin L.segCount) (hr : (L.segment s).radial = false) :
    K.r₁ ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ K.r₂ ∧ (L.segment s).other = K.z₁ + K.z₂ - (L.segment s).level := by
  rcases hL.segment_on_side s with h | h
  · exact absurd h.1 (by simp [hr])
  · exact ⟨h.2.2.1, h.2.2.2, (hL.segment_other_in_box s).2 (by simp [hr])⟩

theorem extra_split (hI : ModeRectIntegrableStatement) {k N : ℕ} (c : FracCellData k N) (K : CellBox)
    (S : CellScalars) (B : CellBases) (L : CellLayout) (hL : IsCellLayout c K S B L) (x : FieldTuple k)
    (hx : IsAdmissible c x) (n : L.modes) (e : Fin 4) (a : Fin 3) (d : Fin (L.degCoef + 1))
    (hdeg : ¬ (e.val = 0 ∧ L.box.r₁ = 0) ∧ (if e.val < 2 then d.val ≤ L.degSide
      else if L.box.r₁ = 0 then d.val ≤ L.degSide else d.val ≤ L.degSide + 1)) :
    L.trueData x (CellDatum.extraVelocity n e a d) = ∑ s ∈ L.sideSegments e, ∑ d' : Fin (L.degSide + 2),
      ((L.segmentTestPair s (L.sideTest e d) d' : ℝ) : ℂ) * L.trueData x (CellDatum.sideVelocity n s a d') := by
  have hb := hL.box_eq
  subst hb
  simp only [CellLayout.trueData, CellDatum.extraVelocity, CellDatum.sideVelocity, Sum.elim_inr, Sum.elim_inl]
  have hbox := hL.box_valid
  have hr12 : L.box.r₁ ≤ L.box.r₂ := hbox.r_order.2.le
  have hz12 : L.box.z₁ ≤ L.box.z₂ := hbox.z_order.2.le
  obtain ⟨hF, hF0⟩ := hI c L.box S B L hL x hx n a 0
  obtain ⟨-, hF2⟩ := hI c L.box S B L hL x hx n a 2
  have hF' : IntegrableOn (L.velMode n x a) (Icc L.box.r₁ L.box.r₂ ×ˢ Icc L.box.z₁ L.box.z₂) := hF
  have hF0' : IntegrableOn (L.gradModeOf n x a 0) (Icc L.box.r₁ L.box.r₂ ×ˢ Icc L.box.z₁ L.box.z₂) := hF0
  have hF2' : IntegrableOn (L.gradModeOf n x a 2) (Icc L.box.r₁ L.box.r₂ ×ˢ Icc L.box.z₁ L.box.z₂) := hF2
  have hK : IsCompact (Icc L.box.r₁ L.box.r₂ ×ˢ Icc L.box.z₁ L.box.z₂) := isCompact_Icc.prod isCompact_Icc
  have hlead : ∀ s, ∀ d, (L.segment s).testCoef d d ≠ 0 := fun s => (hL.segment_valid s).test_leading
  have he4 : e.val = 0 ∨ e.val = 1 ∨ e.val = 2 ∨ e.val = 3 := by omega
  rcases he4 with he | he | he | he
  · have hr1 : L.box.r₁ ≠ 0 := fun h => hdeg.1 ⟨he, h⟩
    have hd : d.val ≤ L.degSide := by
      have := hdeg.2
      rwa [if_pos (by omega)] at this
    rw [CellLayout.extraValue, if_pos he]
    refine radial_side L _ L.box.r₁ L.box.r₂ L.box.z₁ L.box.z₂ (fun s hs => ?_) (fun u hu => ?_)
      (hL.sideSegments_disjoint e) hL.segment_orthonormal _ (sideTest_cont L e d)
      (fun s _ => mem_lo L _ (hlead s) e (by omega) d hd) _ _ _ ?_
    · obtain ⟨h1, h2⟩ := hL.sideSegments_spec e s hs
      have hr : (L.segment s).radial = true := h1.2 (by omega)
      obtain ⟨hz1, hz2, hot⟩ := seg_radial hL s hr
      rw [if_pos he] at h2
      exact ⟨hr, h2, by rw [hot, h2]; ring, hz1, hz2⟩
    · exact hL.sideSegments_cover e (fun _ => hr1) u (by rw [if_pos (by omega)]; exact hu)
    · rw [min_eq_left hr12, max_eq_right hr12]
      exact (hF'.const_mul _).add (hF0'.continuousOn_mul (by fun_prop) hK)
  · have hd : d.val ≤ L.degSide := by
      have := hdeg.2
      rwa [if_pos (by omega)] at this
    rw [CellLayout.extraValue, if_neg (by omega), if_pos he]
    refine radial_side L _ L.box.r₂ L.box.r₁ L.box.z₁ L.box.z₂ (fun s hs => ?_) (fun u hu => ?_)
      (hL.sideSegments_disjoint e) hL.segment_orthonormal _ (sideTest_cont L e d)
      (fun s _ => mem_lo L _ (hlead s) e (by omega) d hd) _ _ _ ?_
    · obtain ⟨h1, h2⟩ := hL.sideSegments_spec e s hs
      have hr : (L.segment s).radial = true := h1.2 (by omega)
      obtain ⟨hz1, hz2, hot⟩ := seg_radial hL s hr
      rw [if_neg (by omega), if_pos he] at h2
      exact ⟨hr, h2, by rw [hot, h2]; ring, hz1, hz2⟩
    · exact hL.sideSegments_cover e (fun h => absurd h (by omega)) u (by rw [if_pos (by omega)]; exact hu)
    · rw [min_eq_right hr12, max_eq_left hr12]
      exact (hF'.const_mul _).add (hF0'.continuousOn_mul (by fun_prop) hK)
  · have hd := hdeg.2
    rw [if_neg (by omega)] at hd
    rw [CellLayout.extraValue, if_neg (by omega), if_neg (by omega), if_pos he]
    refine height_side L _ L.box.z₁ L.box.z₂ L.box.r₁ L.box.r₂ (fun s hs => ?_) (fun u hu => ?_)
      (hL.sideSegments_disjoint e) hL.segment_orthonormal _ (sideTest_cont L e d)
      (fun s _ => mem_hi L _ (hlead s) e (by omega) d hd) _ _ _ ?_
    · obtain ⟨h1, h2⟩ := hL.sideSegments_spec e s hs
      have hr : (L.segment s).radial = false := Bool.eq_false_iff.2 (fun h => absurd (h1.1 h) (by omega))
      obtain ⟨hz1, hz2, hot⟩ := seg_height hL s hr
      rw [if_neg (by omega), if_neg (by omega), if_pos he] at h2
      exact ⟨hr, h2, by rw [hot, h2]; ring, hz1, hz2⟩
    · exact hL.sideSegments_cover e (fun h => absurd h (by omega)) u (by rw [if_neg (by omega)]; exact hu)
    · rw [min_eq_left hz12, max_eq_right hz12]
      exact (hF'.const_mul _).add (hF2'.continuousOn_mul (by fun_prop) hK)
  · have hd := hdeg.2
    rw [if_neg (by omega)] at hd
    rw [CellLayout.extraValue, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    refine height_side L _ L.box.z₂ L.box.z₁ L.box.r₁ L.box.r₂ (fun s hs => ?_) (fun u hu => ?_)
      (hL.sideSegments_disjoint e) hL.segment_orthonormal _ (sideTest_cont L e d)
      (fun s _ => mem_hi L _ (hlead s) e (by omega) d hd) _ _ _ ?_
    · obtain ⟨h1, h2⟩ := hL.sideSegments_spec e s hs
      have hr : (L.segment s).radial = false := Bool.eq_false_iff.2 (fun h => absurd (h1.1 h) (by omega))
      obtain ⟨hz1, hz2, hot⟩ := seg_height hL s hr
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h2
      exact ⟨hr, h2, by rw [hot, h2]; ring, hz1, hz2⟩
    · exact hL.sideSegments_cover e (fun h => absurd h (by omega)) u (by rw [if_neg (by omega)]; exact hu)
    · rw [min_eq_right hz12, max_eq_left hz12]
      exact (hF'.const_mul _).add (hF2'.continuousOn_mul (by fun_prop) hK)

end RelSideSplit.Internal

theorem relSideSplit_of_integrable (hI : ModeRectIntegrableStatement) : RelSideSplitStatement := by
  intro k N c K S B L hL x hx ρ
  obtain ⟨n, e, a, d⟩ := ρ
  simp only [CellLayout.relationRow, Sum.elim_inr]
  by_cases hdeg : ¬ (e.val = 0 ∧ L.box.r₁ = 0) ∧ (if e.val < 2 then d.val ≤ L.degSide
      else if L.box.r₁ = 0 then d.val ≤ L.degSide else d.val ≤ L.degSide + 1)
  · rw [if_pos hdeg, RelSideSplit.Internal.pair_row, sub_eq_zero]
    exact RelSideSplit.Internal.extra_split hI c K S B L hL x hx n e a d hdeg
  · rw [if_neg hdeg]
    simp

end Breakdown.CellCert.CellFormula
