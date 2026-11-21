import Breakdown.CertCell.RowLowPartBasisDefs

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula

namespace Internal

def triPoly (c : ℕ → ℕ → ℝ) (d : ℕ) (u : ℝ) : ℂ := ((∑ i ∈ Finset.range (d + 1), c d i * u ^ i : ℝ) : ℂ)

def triSpan (c : ℕ → ℕ → ℝ) (n : ℕ) : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ (Set.range (fun d : Fin n => triPoly c d))

theorem triPoly_continuous (c : ℕ → ℕ → ℝ) (d : ℕ) : Continuous (triPoly c d) :=
  Complex.continuous_ofReal.comp
    (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_pow i))

theorem triSpan_mono (c : ℕ → ℕ → ℝ) {n m : ℕ} (h : n ≤ m) : triSpan c n ≤ triSpan c m := by
  apply Submodule.span_mono
  rintro _ ⟨d, rfl⟩
  exact ⟨Fin.castLE h d, rfl⟩

theorem triPoly_mem (c : ℕ → ℕ → ℝ) {d n : ℕ} (h : d < n) : triPoly c d ∈ triSpan c n :=
  Submodule.subset_span ⟨⟨d, h⟩, rfl⟩

theorem pow_mem (c : ℕ → ℕ → ℝ) (hc : ∀ d, c d d ≠ 0) (n : ℕ) :
    (fun u : ℝ => (u : ℂ) ^ n) ∈ triSpan c (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn : (c n n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hc n)
    have e : (fun u : ℝ => (u : ℂ) ^ n) = ((c n n : ℂ))⁻¹ • (triPoly c n -
        ∑ i ∈ Finset.range n, (c n i : ℂ) • (fun u : ℝ => (u : ℂ) ^ i)) := by
      funext u
      simp only [triPoly, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul]
      push_cast
      rw [Finset.sum_range_succ]
      field_simp
      ring
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ (triPoly_mem c (Nat.lt_succ_self n)) ?_)
    exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
      (triSpan_mono c (by have := Finset.mem_range.mp hi; omega) (ih i (Finset.mem_range.mp hi)))

theorem expand_of_mem (c : ℕ → ℕ → ℝ) (N : ℕ) (g : ℝ → ℂ) (hg : g ∈ triSpan c N) :
    ∃ b : ℕ → ℂ, ∀ u, g u = ∑ d ∈ Finset.range N, b d * triPoly c d u := by
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hg
  refine ⟨fun d => if h : d < N then b ⟨d, h⟩ else 0, fun u => ?_⟩
  rw [← hb, Finset.sum_apply,
    ← Fin.sum_univ_eq_sum_range (fun d => (if h : d < N then b ⟨d, h⟩ else 0) * triPoly c d u)]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [d.isLt]

theorem pow_expand (c : ℕ → ℕ → ℝ) (hc : ∀ d, c d d ≠ 0) (N i : ℕ) (hi : i < N) :
    ∃ b : ℕ → ℂ, ∀ u : ℝ, (u : ℂ) ^ i = ∑ d ∈ Finset.range N, b d * triPoly c d u :=
  expand_of_mem c N _ (triSpan_mono c hi (pow_mem c hc i))

theorem poly_expand (c : ℕ → ℕ → ℝ) (hc : ∀ d, c d d ≠ 0) (N : ℕ) (f : ℝ → ℂ)
    (hf : IsUnivariatePoly N f) :
    ∃ b : ℕ → ℂ, ∀ u, f u = ∑ d ∈ Finset.range N, b d * triPoly c d u := by
  obtain ⟨a, ha⟩ := hf
  apply expand_of_mem
  have e : f = ∑ i ∈ Finset.range N, a i • (fun u : ℝ => (u : ℂ) ^ i) := by
    funext u
    rw [ha u, Finset.sum_apply]
    rfl
  rw [e]
  exact Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ (triSpan_mono c (Finset.mem_range.mp hi) (pow_mem c hc i))

theorem coef_extract {α ι : Type*} [MeasurableSpace α] [DecidableEq ι] (μ : Measure α) (s : Set α)
    (I : Finset ι) (g : α → ℂ) (e : ι → α → ℂ)
    (hint : ∀ i ∈ I, ∀ k ∈ I, IntegrableOn (fun x => g x * e i x * e k x) s μ)
    (hON : ∀ i ∈ I, ∀ k ∈ I, ∫ x in s, g x * e i x * e k x ∂μ = if i = k then 1 else 0)
    (b : ι → ℂ) (k : ι) (hk : k ∈ I) :
    ∫ x in s, g x * (∑ i ∈ I, b i * e i x) * e k x ∂μ = b k := by
  have h : (fun x => g x * (∑ i ∈ I, b i * e i x) * e k x) =
      fun x => ∑ i ∈ I, b i * (g x * e i x * e k x) := by
    funext x
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h, integral_finsetSum _ fun i hi => (hint i hi k hk).const_mul (b i)]
  rw [Finset.sum_eq_single k]
  · rw [integral_const_mul, hON k hk k hk, if_pos rfl, mul_one]
  · intro i hi hik
    rw [integral_const_mul, hON i hi k hk, if_neg hik, mul_zero]
  · intro h
    exact absurd hk h

theorem ofReal_ite (p : Prop) [Decidable p] : (((if p then 1 else 0 : ℝ)) : ℂ) = if p then 1 else 0 := by
  split_ifs <;> simp

theorem lineWeight_continuous (K : CellBox) : Continuous K.lineWeight := by
  unfold CellBox.lineWeight
  split_ifs
  · exact continuous_id
  · exact continuous_const

theorem basisValue_eq (B : CellBases) (j l : ℕ) (q : ℝ × ℝ) :
    basisValue B j l q = triPoly B.radialCoef j q.1 * triPoly B.heightCoef l q.2 := by
  unfold basisValue triPoly CellBases.radialPoly CellBases.heightPoly
  push_cast
  rfl

theorem basisValue_continuous (B : CellBases) (j l : ℕ) : Continuous (basisValue B j l) := by
  have e : basisValue B j l = fun q => triPoly B.radialCoef j q.1 * triPoly B.heightCoef l q.2 :=
    funext (basisValue_eq B j l)
  rw [e]
  exact ((triPoly_continuous _ j).comp continuous_fst).mul ((triPoly_continuous _ l).comp continuous_snd)

theorem cell_orthonormal (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (i k : ℕ × ℕ) :
    ∫ x in K.rect, (K.lineWeight x.1 : ℂ) * basisValue B i.1 i.2 x * basisValue B k.1 k.2 x =
      if i = k then 1 else 0 := by
  have e : (fun x : ℝ × ℝ => (K.lineWeight x.1 : ℂ) * basisValue B i.1 i.2 x * basisValue B k.1 k.2 x) =
      fun x => (fun r => ((K.lineWeight r * B.radialPoly i.1 r * B.radialPoly k.1 r : ℝ) : ℂ)) x.1 *
        (fun z => ((B.heightPoly i.2 z * B.heightPoly k.2 z : ℝ) : ℂ)) x.2 := by
    funext x
    unfold basisValue
    push_cast
    ring
  have hprod := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun r => ((K.lineWeight r * B.radialPoly i.1 r * B.radialPoly k.1 r : ℝ) : ℂ))
    (fun z => ((B.heightPoly i.2 z * B.heightPoly k.2 z : ℝ) : ℂ)) (Set.Icc K.r₁ K.r₂) (Set.Icc K.z₁ K.z₂)
  rw [e, CellBox.rect, Measure.volume_eq_prod, hprod, integral_complex_ofReal,
    integral_complex_ofReal, hB.radial_orthonormal, hB.height_orthonormal, ofReal_ite, ofReal_ite]
  obtain ⟨i1, i2⟩ := i
  obtain ⟨k1, k2⟩ := k
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

theorem cell_extract (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (N : ℕ)
    (b : ℕ × ℕ → ℂ) (jl : ℕ × ℕ) (hjl : jl ∈ Finset.range N ×ˢ Finset.range N) :
    ∫ x in K.rect, (K.lineWeight x.1 : ℂ) *
      (∑ i ∈ Finset.range N ×ˢ Finset.range N, b i * basisValue B i.1 i.2 x) *
        basisValue B jl.1 jl.2 x = b jl := by
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  refine coef_extract (volume : Measure (ℝ × ℝ)) K.rect (Finset.range N ×ˢ Finset.range N)
    (fun x => (K.lineWeight x.1 : ℂ)) (fun i x => basisValue B i.1 i.2 x) ?_
    (fun i _ k _ => cell_orthonormal K B hB i k) b jl hjl
  intro i _ k _
  exact (((Complex.continuous_ofReal.comp ((lineWeight_continuous K).comp continuous_fst)).mul
      (basisValue_continuous B i.1 i.2)).mul
        (basisValue_continuous B k.1 k.2)).continuousOn.integrableOn_compact hcomp

end Internal

open Internal

theorem cellBasisExpansion : CellBasisExpansionStatement := by
  intro K B _ hB N h hh p
  obtain ⟨a, ha⟩ := hh
  have hr : ∀ d, B.radialCoef d d ≠ 0 := fun d => (hB.radial_leading d).ne'
  have hz : ∀ d, B.heightCoef d d ≠ 0 := fun d => (hB.height_leading d).ne'
  choose! α hα using fun i (hi : i < N) => pow_expand B.radialCoef hr N i hi
  choose! β hβ using fun k (hk : k < N) => pow_expand B.heightCoef hz N k hk
  obtain ⟨b, hbdef⟩ : ∃ b : ℕ × ℕ → ℂ, b = fun jl =>
      ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N, a i k * α i jl.1 * β k jl.2 := ⟨_, rfl⟩
  have hexp : ∀ q : ℝ × ℝ,
      h q = ∑ jl ∈ Finset.range N ×ˢ Finset.range N, b jl * basisValue B jl.1 jl.2 q := by
    intro q
    have hterm : ∀ i ∈ Finset.range N, ∀ k ∈ Finset.range N,
        a i k * (q.1 : ℂ) ^ i * (q.2 : ℂ) ^ k = ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
          a i k * α i j * β k l * basisValue B j l q := by
      intro i hi k hk
      rw [hα i (Finset.mem_range.mp hi), hβ k (Finset.mem_range.mp hk), mul_assoc,
        Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [basisValue_eq]
      ring
    rw [ha q, Finset.sum_product]
    simp only [hbdef, Finset.sum_mul]
    calc ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N, a i k * (q.1 : ℂ) ^ i * (q.2 : ℂ) ^ k
        = ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
            a i k * α i j * β k l * basisValue B j l q :=
          Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k hk => hterm i hi k hk
      _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
            a i k * α i j * β k l * basisValue B j l q :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
            a i k * α i j * β k l * basisValue B j l q := Finset.sum_comm
      _ = ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N, ∑ l ∈ Finset.range N, ∑ k ∈ Finset.range N,
            a i k * α i j * β k l * basisValue B j l q :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N, ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N,
            a i k * α i j * β k l * basisValue B j l q :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
  have hcoef : ∀ jl ∈ Finset.range N ×ˢ Finset.range N,
      ∫ x in K.rect, (K.lineWeight x.1 : ℂ) * h x * basisValue B jl.1 jl.2 x = b jl := by
    intro jl hjl
    simp only [hexp]
    exact cell_extract K B hB N b jl hjl
  rw [hexp p, Finset.sum_product]
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => ?_
  rw [hcoef (j, l) (Finset.mem_product.mpr ⟨hj, hl⟩)]

theorem segmentTestExpansion : SegmentTestExpansionStatement := by
  intro S N hc hON f hf u
  obtain ⟨b, hb⟩ := poly_expand S.testCoef hc N f hf
  have hT : ∀ d w, (S.test d w : ℂ) = triPoly S.testCoef d w := fun _ _ => rfl
  have hint : ∀ i ∈ Finset.range N, ∀ k ∈ Finset.range N,
      IntegrableOn (fun x => (1 : ℂ) * triPoly S.testCoef i x * triPoly S.testCoef k x)
        (Set.Icc S.lo S.hi) volume := fun i _ k _ =>
    ((continuous_const.mul (triPoly_continuous _ i)).mul
      (triPoly_continuous _ k)).continuousOn.integrableOn_compact isCompact_Icc
  have hON' : ∀ i ∈ Finset.range N, ∀ k ∈ Finset.range N,
      ∫ x in Set.Icc S.lo S.hi, (1 : ℂ) * triPoly S.testCoef i x * triPoly S.testCoef k x =
        if i = k then 1 else 0 := by
    intro i hi k hk
    have h1 : (fun x => (1 : ℂ) * triPoly S.testCoef i x * triPoly S.testCoef k x) =
        fun x => ((S.test i x * S.test k x : ℝ) : ℂ) := by
      funext x
      rw [← hT, ← hT]
      push_cast
      ring
    rw [h1, integral_complex_ofReal, hON i k (Finset.mem_range.mp hi) (Finset.mem_range.mp hk), ofReal_ite]
  have hcoef : ∀ d ∈ Finset.range N,
      ∫ w in Set.Icc S.lo S.hi, f w * (S.test d w : ℂ) = b d := by
    intro d hd
    have h2 : (fun w => f w * (S.test d w : ℂ)) =
        fun w => (1 : ℂ) * (∑ i ∈ Finset.range N, b i * triPoly S.testCoef i w) * triPoly S.testCoef d w := by
      funext w
      rw [hb w, hT, one_mul]
    rw [h2]
    exact coef_extract volume _ _ _ _ hint hON' b d hd
  rw [Finset.sum_congr rfl fun d hd => by rw [hcoef d hd], hb u]
  rfl

end CellCalculus

end CertCell

end Breakdown
