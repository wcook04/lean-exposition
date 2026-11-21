import Breakdown.FracCell.MeshDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

namespace MeshRowFar

namespace Internal

theorem triangular_orth (s : Set ℝ) (ρ : ℝ → ℝ) (Q : ℕ → ℝ → ℝ) (cf : ℕ → ℕ → ℝ)
    (hQ : ∀ j r, Q j r = ∑ i ∈ Finset.range (j + 1), cf j i * r ^ i) (hlead : ∀ j, 0 < cf j j)
    (horth : ∀ j j', ∫ r in s, ρ r * Q j r * Q j' r = if j = j' then 1 else 0)
    (hint : ∀ i j, IntegrableOn (fun r => ρ r * r ^ i * Q j r) s) :
    ∀ a j, a < j → ∫ r in s, ρ r * r ^ a * Q j r = 0 := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro j haj
    have hexp : ∀ r, ρ r * Q a r * Q j r =
        ∑ i ∈ Finset.range (a + 1), cf a i * (ρ r * r ^ i * Q j r) := by
      intro r
      rw [hQ a r, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    have h1 : ∫ r in s, ρ r * Q a r * Q j r =
        ∑ i ∈ Finset.range (a + 1), cf a i * ∫ r in s, ρ r * r ^ i * Q j r := by
      simp_rw [hexp]
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl ?_
        intro i _
        rw [integral_const_mul]
      · intro i _
        exact Integrable.const_mul (hint i j) _
    rw [horth a j, if_neg (Nat.ne_of_lt haj), Finset.sum_range_succ] at h1
    have h2 : ∑ i ∈ Finset.range a, cf a i * ∫ r in s, ρ r * r ^ i * Q j r = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      rw [ih i (Finset.mem_range.mp hi) j (lt_trans (Finset.mem_range.mp hi) haj), mul_zero]
    rw [h2, zero_add] at h1
    have := hlead a
    rcases mul_eq_zero.mp h1.symm with h | h
    · linarith
    · exact h

theorem lineWeight_continuous (K : CellBox) : Continuous K.lineWeight := by
  by_cases h : K.r₁ = 0
  · have e : K.lineWeight = fun r => r := by
      funext r
      simp [CellBox.lineWeight, h]
    rw [e]
    exact continuous_id
  · have e : K.lineWeight = fun _ => 1 := by
      funext r
      simp [CellBox.lineWeight, h]
    rw [e]
    exact continuous_const

theorem radialPoly_continuous (B : CellBases) (j : ℕ) : Continuous (B.radialPoly j) := by
  unfold CellBases.radialPoly
  fun_prop

theorem heightPoly_continuous (B : CellBases) (l : ℕ) : Continuous (B.heightPoly l) := by
  unfold CellBases.heightPoly
  fun_prop

theorem radial_orth (K : CellBox) (B : CellBases) (hB : IsCellBases K B) :
    ∀ a j, a < j → ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * r ^ a * B.radialPoly j r = 0 := by
  refine triangular_orth _ _ _ B.radialCoef (fun j r => rfl) hB.radial_leading hB.radial_orthonormal ?_
  intro i j
  have hw := lineWeight_continuous K
  have hR := radialPoly_continuous B j
  exact Continuous.integrableOn_Icc (by fun_prop)

theorem height_orth (K : CellBox) (B : CellBases) (hB : IsCellBases K B) :
    ∀ a l, a < l → ∫ z in Set.Icc K.z₁ K.z₂, z ^ a * B.heightPoly l z = 0 := by
  intro a l hal
  have h := triangular_orth (Set.Icc K.z₁ K.z₂) (fun _ => 1) B.heightPoly B.heightCoef (fun j r => rfl)
    hB.height_leading (by intro l l'; simpa using hB.height_orthonormal l l') ?_ a l hal
  · simpa using h
  · intro i j
    have hH := heightPoly_continuous B j
    exact Continuous.integrableOn_Icc (by fun_prop)

end Internal

end MeshRowFar



namespace MeshRowFar

namespace Internal

theorem axis_null : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
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
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo), ae_restrict_of_ae axis_null]
    with p hp h0
  exact ⟨hp, h0⟩

theorem coef_eq_zero (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (E : ℕ)
    (F P : ℝ × ℝ → ℂ) (hP : P ∈ polyFn E E) (hFP : ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 → F p = P p)
    (j l : ℕ) (hjl : E < max j l) : B.coef K F j l = 0 := by
  obtain ⟨cc, hcc⟩ := hP
  have hrect : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hae : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * F p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
      =ᵐ[volume.restrict K.rect] (fun p => ∑ a : Fin (E + 1), ∑ b : Fin (E + 1), cc a b *
        (((K.lineWeight p.1 * p.1 ^ (a : ℕ) * B.radialPoly j p.1 : ℝ) : ℂ) *
          ((p.2 ^ (b : ℕ) * B.heightPoly l p.2 : ℝ) : ℂ))) := by
    filter_upwards [open_rect_ae K] with p hp
    rw [hFP p hp.1 hp.2, hcc p, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    push_cast
    ring
  have hw := lineWeight_continuous K
  have hR := radialPoly_continuous B j
  have hH := heightPoly_continuous B l
  have hcpt : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  unfold CellBases.coef
  rw [integral_congr_ae hae, integral_finsetSum]
  · refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [integral_const_mul]
      have hprod := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (fun r : ℝ => ((K.lineWeight r * r ^ (a : ℕ) * B.radialPoly j r : ℝ) : ℂ))
        (fun z : ℝ => ((z ^ (b : ℕ) * B.heightPoly l z : ℝ) : ℂ)) (Set.Icc K.r₁ K.r₂) (Set.Icc K.z₁ K.z₂)
      have hz : (∫ r in Set.Icc K.r₁ K.r₂, ((K.lineWeight r * r ^ (a : ℕ) * B.radialPoly j r : ℝ) : ℂ)) *
          (∫ z in Set.Icc K.z₁ K.z₂, ((z ^ (b : ℕ) * B.heightPoly l z : ℝ) : ℂ)) = 0 := by
        rw [integral_complex_ofReal, integral_complex_ofReal]
        rcases lt_max_iff.mp hjl with h | h
        · rw [radial_orth K B hB a j (lt_of_le_of_lt (Nat.le_of_lt_succ a.isLt) h)]
          simp
        · rw [height_orth K B hB b l (lt_of_le_of_lt (Nat.le_of_lt_succ b.isLt) h)]
          simp
      rw [hz] at hprod
      unfold CellBox.rect
      rw [Measure.volume_eq_prod, hprod, mul_zero]
    · intro b _
      refine ContinuousOn.integrableOn_compact hcpt (Continuous.continuousOn ?_)
      fun_prop
  · intro a _
    refine integrable_finsetSum _ (fun b _ => ?_)
    refine ContinuousOn.integrableOn_compact hcpt (Continuous.continuousOn ?_)
    fun_prop

end Internal

end MeshRowFar



namespace MeshRowFar

namespace Internal

theorem sum_regroup (d : ℕ) (s t : Finset ℤ) (u : Finset ℕ) (f g : ℤ → ℕ → ℕ → ℝ) :
    ∑ j ∈ u, ∑ l ∈ u, (if d < max j l then ∑ n ∈ s, f n j l + ∑ n ∈ t, g n j l else 0) =
      (∑ n ∈ s, ∑ j ∈ u, ∑ l ∈ u, if d < max j l then f n j l else 0)
        + ∑ n ∈ t, ∑ j ∈ u, ∑ l ∈ u, if d < max j l then g n j l else 0 := by
  have h1 : ∀ (h : ℤ → ℕ → ℕ → ℝ) (w : Finset ℤ), ∑ n ∈ w, ∑ j ∈ u, ∑ l ∈ u, (if d < max j l then h n j l else 0)
      = ∑ j ∈ u, ∑ l ∈ u, if d < max j l then ∑ n ∈ w, h n j l else 0 := by
    intro h w
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    split_ifs <;> simp
  rw [h1, h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  split_ifs <;> simp

end Internal

end MeshRowFar

open MeshRowFar.Internal in
theorem rowFarFinite_holds : RowFarFiniteStatement := by
  intro k N c K S B slots R E hK hB hR μ
  have hF : ∀ n' ∈ S.resolved ∪ S.band, ∀ j l, E < max j l →
      (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) *
        B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n' p i q) j l) = 0 := by
    intro n' hn j l hjl
    funext i q
    refine Finset.sum_eq_zero (fun a ha => ?_)
    obtain ⟨P, hP, hFP⟩ := hR.folded_poly a ha n' hn i q
    rw [coef_eq_zero K B hB E _ P hP hFP j l hjl, mul_zero]
  have hV : ∀ n' ∈ S.resolved, ∀ j l, E < max j l →
      (fun i => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) *
        B.coef K (fun p => CellScalars.rowCouplingVelocity c K R a n' p i) j l) = 0 := by
    intro n' hn j l hjl
    funext i
    refine Finset.sum_eq_zero (fun a ha => ?_)
    obtain ⟨P, hP, hFP⟩ := hR.velocity_poly a ha n' hn i
    rw [coef_eq_zero K B hB E _ P hP hFP j l hjl, mul_zero]
  unfold CellScalars.rowSquareFar CellScalars.rowSquareUpTo
  rw [tsum_eq_sum (s := Finset.range (E + 1) ×ˢ Finset.range (E + 1)), Finset.sum_product]
  · exact sum_regroup _ _ _ _ _ _
  · rintro ⟨j, l⟩ hjl
    have hlt : E < max j l := by
      simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hjl
      rcases hjl with h | h
      · exact lt_max_of_lt_left (by omega)
      · exact lt_max_of_lt_right (by omega)
    simp only []
    split_ifs with hd
    · rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
      · intro n' hn
        rw [hV n' hn j l hlt]
        simp [vecSq]
      · intro n' hn
        rw [hF n' hn j l hlt]
        simp [CellScalars.sigmaWeightedPair, entryPairing]
    · rfl


end CellAnalysis

end CellCert

end Breakdown
