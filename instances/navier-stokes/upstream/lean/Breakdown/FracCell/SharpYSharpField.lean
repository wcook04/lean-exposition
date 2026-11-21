import Breakdown.FracCell.SharpYChargeSt
import Breakdown.FracCell.AngularMode
import Breakdown.FracCell.CircleWeak
import Breakdown.FracCell.StrainFaceFaceTraceFree
import Breakdown.FracCell.EnergyHeightProj

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly SharpParts

private theorem low_trace {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H)
    (K : CellBox) (hK : IsCellBox K) (B : CellBases) (hB : IsCellBases K B) (n : ℤ) (Q : ℕ) (p : ℝ × ℝ) :
    ∑ a : Fin 3, K.lowStrainAt m n Q G p a a = 0 := by
  have hw : ∀ a b : Fin 3, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * gradMode m n G a b p) K.rect :=
    fun a b => LowEntry.Internal.gradMode_int K hK m n hs.measurable_gradient hs.gradient_two a b
  have hF : ∀ a : Fin 3, ∀ t s : ℝ → ℝ, Continuous t → Continuous s →
      IntegrableOn (fun p => ((K.lineWeight p.1 * t p.1 * s p.2 : ℝ) : ℂ) * gradMode m n G a a p) K.rect := by
    intro a t s ht hs'
    have hc : Continuous (fun p : ℝ × ℝ => ((t p.1 * s p.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((ht.comp continuous_fst).mul (hs'.comp continuous_snd))
    have h := (hw a a).continuousOn_mul hc.continuousOn (LowEntry.Internal.rect_compact K)
    refine h.congr_fun (fun p _ => ?_) (LowEntry.Internal.rect_meas K)
    push_cast
    ring
  have hsum := CellFormula.Internal.StrainFaceFaceTraceFree.grad_sum K hK hs n
  have hc : ∀ j l : ℕ, ∑ a : Fin 3, B.coef K (gradMode m n G a a) j l = 0 := by
    intro j l
    have hb : Continuous (fun p : ℝ × ℝ => ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (((LowEntry.Internal.radialPoly_cont B j).comp continuous_fst).mul
        ((LowEntry.Internal.heightPoly_cont B l).comp continuous_snd))
    have hI : ∀ a : Fin 3, Integrable (fun p => (K.lineWeight p.1 : ℂ) * gradMode m n G a a p *
        ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) (volume.restrict K.rect) :=
      fun a => (hw a a).mul_continuousOn hb.continuousOn (LowEntry.Internal.rect_compact K)
    simp only [CellBases.coef]
    rw [← integral_finsetSum _ (fun a _ => hI a)]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hsum] with q hq
    rw [← Finset.sum_mul, ← Finset.mul_sum, hq]
    simp
  simp only [CellBox.lowStrainAt, CellBox.lowStrain]
  rw [Finset.sum_congr rfl (fun a _ => congrFun (CellEnergy.HeightProj.proj_eq_basis K B hB Q _ (hF a)) p)]
  calc ∑ a : Fin 3, ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
        B.coef K (gradMode m n G a a) j l * ((CellEnergy.basisFn B j l p : ℝ) : ℂ)
      = ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
          (∑ a : Fin 3, B.coef K (gradMode m n G a a) j l) * ((CellEnergy.basisFn B j l p : ℝ) : ℂ) := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
    _ = 0 := by simp [hc]

private theorem pos_ae (K : CellBox) (hK : IsCellBox K) : ∀ᵐ p ∂(volume.restrict K.rect), 0 < p.1 := by
  have hnull : volume ({(0 : ℝ)} ×ˢ (Set.univ : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have h1 : ∀ᵐ p : ℝ × ℝ ∂volume, p ∉ ({(0 : ℝ)} ×ˢ (Set.univ : Set ℝ)) :=
    measure_eq_zero_iff_ae_notMem.1 hnull
  filter_upwards [ae_restrict_of_ae h1, ae_restrict_mem (LowEntry.Internal.rect_meas K)] with p hp hm
  have h0 : 0 ≤ p.1 := hK.r_order.1.trans hm.1.1
  have hne : p.1 ≠ 0 := fun h => hp ⟨h, Set.mem_univ _⟩
  exact lt_of_le_of_ne h0 (Ne.symm hne)

theorem sharpField : SharpFieldStatement := by
  intro α _ _ k N c _ K S B Cl slots R hD _ x hx
  refine ⟨fun n => ?_, fun n _ => ?_⟩
  · filter_upwards [CellFormula.Internal.StrainFaceFaceTraceFree.grad_sum K hD.box hx.1 n] with p hp
    unfold IsTraceFree
    simp only [sharpGrad, Finset.sum_sub_distrib, hp, zero_sub, neg_eq_zero]
    unfold lowGrad
    split_ifs
    · exact low_trace hx.1 K hD.box B hD.bases n S.degHigh p
    · simp
  · filter_upwards [ae_restrict_of_ae (CellFormula.angularMode CellEnergy.circleWeak c.order x.1 x.2.1 x.2.2.1 hx.1 n),
      pos_ae K hD.box] with p hp hpos
    obtain ⟨h1, h2, h3⟩ := hp hpos
    funext a
    fin_cases a <;> simp [turnVec, h1, h2, h3]

end Breakdown.CellCert.CellAnalysis
