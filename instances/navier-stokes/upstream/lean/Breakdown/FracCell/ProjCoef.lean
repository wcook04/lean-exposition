import Breakdown.FracCell.SharpRowIdentity
import Breakdown.FracCell.EnergyHeightProj
import Breakdown.FracCell.FormulaSynthesis
import Breakdown.FracCell.ProjCompose

open MeasureTheory

namespace Breakdown.CellCert.CellAnalysis

open CellFormula CellEnergy

private theorem sum_pick (d j l : ℕ) (g : ℕ → ℕ → ℂ) :
    ∑ j' : Fin (d + 1), ∑ l' : Fin (d + 1), g j' l' * (if (j' : ℕ) = j ∧ (l' : ℕ) = l then 1 else 0)
      = if max j l ≤ d then g j l else 0 := by
  by_cases h : max j l ≤ d
  · rw [if_pos h, Finset.sum_eq_single (⟨j, by omega⟩ : Fin (d + 1))]
    · rw [Finset.sum_eq_single (⟨l, by omega⟩ : Fin (d + 1))]
      · simp
      · intro b _ hb
        have : (b : ℕ) ≠ l := fun e => hb (Fin.ext e)
        simp [this]
      · simp
    · intro b _ hb
      have : (b : ℕ) ≠ j := fun e => hb (Fin.ext e)
      refine Finset.sum_eq_zero fun l' _ => ?_
      simp [this]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun j' _ => Finset.sum_eq_zero fun l' _ => ?_
    have h1 := j'.isLt
    have h2 := l'.isLt
    have : ¬ ((j' : ℕ) = j ∧ (l' : ℕ) = l) := by omega
    simp [this]

theorem projCoef_holds : ProjCoefStatement := by
  intro K B hK hB F hF d
  obtain ⟨hFm, hFi⟩ := hF
  have hw := ProjCompose.Internal.lw_cont K
  have hint : ∀ t s : ℝ → ℝ, Continuous t → Continuous s →
      IntegrableOn (fun p => ((K.lineWeight p.1 * t p.1 * s p.2 : ℝ) : ℂ) * F p) K.rect := by
    intro t s ht hs
    have hT : Continuous (fun p : ℝ × ℝ => ((t p.1 * s p.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((ht.comp continuous_fst).mul (hs.comp continuous_snd))
    refine (ProjCompose.Internal.cross_int K hFm hFi hT).congr (ae_of_all _ fun p => ?_)
    simp only [Complex.conj_ofReal]
    push_cast
    ring
  have hP := HeightProj.proj_eq_basis K B hB d F hint
  have hbc : ∀ j l : ℕ, Continuous (fun p : ℝ × ℝ => ((basisFn B j l p : ℝ) : ℂ)) := fun j l =>
    FormulaSynthesis.Internal.basisVal_continuous B j l
  have hPc : Continuous (K.proj d d F) := by
    rw [hP]
    exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun l _ => continuous_const.mul (hbc j l)
  refine ⟨⟨hFm.sub hPc.aestronglyMeasurable, ?_⟩, fun j l => ?_⟩
  · have hPi : IntegrableOn (fun p => K.lineWeight p.1 * ‖K.proj d d F p‖ ^ 2) K.rect :=
      ((hw.comp continuous_fst).mul (hPc.norm.pow 2)).continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)
    refine Integrable.mono' ((hFi.add hPi).const_mul 2) ?_ ?_
    · exact ((hw.comp continuous_fst).aestronglyMeasurable).mul
        ((hFm.sub hPc.aestronglyMeasurable).norm.pow 2)
    · refine (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).2 (ae_of_all _ (fun p hp => ?_))
      have h0 : 0 ≤ K.lineWeight p.1 := ProjCompose.Internal.lw_nonneg K hp.1
      have hn := norm_sub_le (F p) (K.proj d d F p)
      simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg h0, sq_abs, Pi.add_apply]
      nlinarith [mul_nonneg h0 (sq_nonneg (‖F p‖ - ‖K.proj d d F p‖)), norm_nonneg (F p - K.proj d d F p),
        norm_nonneg (F p), norm_nonneg (K.proj d d F p),
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) h0]
  · unfold CellBases.coef
    have i1 : IntegrableOn (fun p => ((K.lineWeight p.1 : ℝ) : ℂ) * F p
        * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect := by
      refine (hint (B.radialPoly j) (B.heightPoly l) (FormulaSynthesis.Internal.radialPoly_continuous B j)
        (FormulaSynthesis.Internal.heightPoly_continuous B l)).congr (ae_of_all _ fun p => ?_)
      push_cast
      ring
    have i2 : IntegrableOn (fun p => ((K.lineWeight p.1 : ℝ) : ℂ) * K.proj d d F p
        * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect :=
      (((Complex.continuous_ofReal.comp (hw.comp continuous_fst)).mul hPc).mul
        (FormulaSynthesis.Internal.basisVal_continuous B j l)).continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)
    have e : (fun p => ((K.lineWeight p.1 : ℝ) : ℂ) * (F p - K.proj d d F p)
        * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
        = fun p => ((K.lineWeight p.1 : ℝ) : ℂ) * F p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)
          - ((K.lineWeight p.1 : ℝ) : ℂ) * K.proj d d F p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) := by
      funext p
      ring
    rw [e, integral_sub i1 i2]
    have hcoefP : (∫ p in K.rect, ((K.lineWeight p.1 : ℝ) : ℂ) * K.proj d d F p
        * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
        = ∑ j' : Fin (d + 1), ∑ l' : Fin (d + 1), B.coef K F j' l' * (if (j' : ℕ) = j ∧ (l' : ℕ) = l then 1 else 0) := by
      rw [hP]
      have hm : ∀ j' l' : ℕ, IntegrableOn (fun p : ℝ × ℝ => B.coef K F j' l' * (((K.lineWeight p.1 : ℝ) : ℂ)
          * basisVal B j' l' p * basisVal B j l p)) K.rect := fun j' l' =>
        (continuous_const.mul (((Complex.continuous_ofReal.comp (hw.comp continuous_fst)).mul
          (FormulaSynthesis.Internal.basisVal_continuous B j' l')).mul
            (FormulaSynthesis.Internal.basisVal_continuous B j l))).continuousOn.integrableOn_compact
          (isCompact_Icc.prod isCompact_Icc)
      have e2 : ∀ p : ℝ × ℝ, ((K.lineWeight p.1 : ℝ) : ℂ)
          * (∑ j' : Fin (d + 1), ∑ l' : Fin (d + 1), B.coef K F j' l' * ((basisFn B j' l' p : ℝ) : ℂ))
          * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)
          = ∑ j' : Fin (d + 1), ∑ l' : Fin (d + 1), B.coef K F j' l' * (((K.lineWeight p.1 : ℝ) : ℂ)
            * basisVal B j' l' p * basisVal B j l p) := by
        intro p
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun l' _ => ?_
        unfold basisVal basisFn
        ring
      simp_rw [e2]
      rw [integral_finsetSum _ fun (j' : Fin (d + 1)) _ => integrable_finsetSum _ fun (l' : Fin (d + 1)) _ => hm j' l']
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [integral_finsetSum _ fun (l' : Fin (d + 1)) _ => hm j' l']
      refine Finset.sum_congr rfl fun l' _ => ?_
      rw [integral_const_mul, FormulaSynthesis.Internal.basis_orth K B hB]
    rw [hcoefP, sum_pick d j l (fun j' l' => B.coef K F j' l')]
    unfold CellBases.coef
    split_ifs <;> simp

end Breakdown.CellCert.CellAnalysis
