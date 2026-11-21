import Breakdown.CertCell.AssemblyRowExpansionLowOrbit
import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.RowCouplingLow
import Breakdown.CertCell.RowLowPartLift
import Breakdown.CertCell.HarmonicProfiles
import Breakdown.CertCell.CellRowFormula
import Breakdown.FracCell.EnergyHeightProj
import Breakdown.FracCell.ResolvedEnergyCore
import Breakdown.FracCell.SharpYDensityRegular

open scoped ENNReal NNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.Assembly.Internal.RowIdentity

open Breakdown Breakdown.CertCell CellCalculus CellCert CellCert.CellAnalysis CellCert.CellFormula

private theorem cross_pair (x : Fin 3 → Fin 3 → ℂ) (y W Ω φ : Fin 3 → ℂ) :
    ∑ j : Fin 12, pairVec x y j * (starRingEnd ℂ) (crossTest W Ω φ j)
      = ∑ i : Fin 3, (∑ j : Fin 3, ∑ l : Fin 3, (alternatingSymbol i j l : ℂ) *
          (curlComp x j * W l + Ω j * y l)) * (starRingEnd ℂ) (φ i) := by
  simp only [crossTest, pairVec, Fin.sum_univ_succ, Fin.sum_univ_zero, curlComp, alternatingSymbol, permSign]
  norm_num
  simp only [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl]
  ring

private theorem pairVec_split (x x' : Fin 3 → Fin 3 → ℂ) (y y' : Fin 3 → ℂ) (j : Fin 12) :
    pairVec x y j = pairVec x' y' j + pairVec (fun a b => x a b - x' a b) (fun a => y a - y' a) j := by
  unfold pairVec
  split_ifs <;> ring

private theorem pairVec_int {S : Set (ℝ × ℝ)} (x : Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (y : Fin 3 → ℝ × ℝ → ℂ)
    (hx : ∀ a b, IntegrableOn (x a b) S) (hy : ∀ a, IntegrableOn (y a) S) (j : Fin 12) :
    IntegrableOn (fun p => pairVec (fun a b => x a b p) (fun a => y a p) j) S := by
  by_cases h : j.val < 9
  · simp only [pairVec, dif_pos h]
    exact hx _ _
  · simp only [pairVec, dif_neg h]
    exact hy _

private theorem crossTest_cont (W Ω : ℝ × ℝ → Fin 3 → ℂ) (hW : ∀ a, Continuous fun p => W p a)
    (hΩ : ∀ a, Continuous fun p => Ω p a) (K : CellBox) (φ : Fin 3 → CellPoly) (j : Fin 12) :
    Continuous (fun p => crossTest (W p) (Ω p) (testValue K φ p) j) := by
  have hT := CellCalculus.Internal.RowForm.testValue_cont K φ
  have hT' : ∀ a, Continuous fun p => testValue K φ p a := fun a => continuous_pi_iff.1 hT a
  have hc := Complex.continuous_conj
  by_cases h : j.val < 9
  · simp only [crossTest, pairVec, dif_pos h]
    refine hc.comp ?_
    refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
    refine continuous_finsetSum _ fun j' _ => continuous_finsetSum _ fun l' _ => ?_
    exact (continuous_const.mul (hW j')).mul (hc.comp (hT' l'))
  · simp only [crossTest, pairVec, dif_neg h]
    refine hc.comp ?_
    refine continuous_finsetSum _ fun j' _ => continuous_finsetSum _ fun l' _ => ?_
    exact (continuous_const.mul (hc.comp (hT' j'))).mul (hΩ l')

private theorem weight_split (K : CellBox) (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
    (p.1 : ℂ) = (K.lineWeight p.1 : ℂ) * ((CellScalars.rHat K p : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul]
  congr 1
  unfold CellScalars.rHat CellBox.lineWeight
  split_ifs
  · rw [mul_div_cancel₀ _ hp]
  · rw [div_one, one_mul]

private theorem orth_zero (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (Q : ℕ) (F : ℝ × ℝ → ℂ)
    (hF : IntegrableOn F K.rect) (T : ℝ × ℝ → ℂ) (hT : T ∈ polyFn Q Q) :
    ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * (F p - K.proj Q Q F p) * (starRingEnd ℂ) (T p) = 0 := by
  have hF' : ∀ t s : ℝ → ℝ, Continuous t → Continuous s →
      IntegrableOn (fun p => ((K.lineWeight p.1 * t p.1 * s p.2 : ℝ) : ℂ) * F p) K.rect := by
    intro t s ht hs
    have hl := CellEnergy.HeightProj.continuous_lineWeight K
    have hg : Continuous (fun p : ℝ × ℝ => ((K.lineWeight p.1 * t p.1 * s p.2 : ℝ) : ℂ)) := by
      refine Complex.continuous_ofReal.comp ?_
      exact ((hl.comp continuous_fst).mul (ht.comp continuous_fst)).mul (hs.comp continuous_snd)
    exact hF.continuousOn_mul hg.continuousOn (CellCalculus.Internal.RowCouplingLow.rect_compact K)
  have e := CellEnergy.HeightProj.proj_eq_basis K B hB Q F hF'
  have o := CellEnergy.HeightProj.proj_orth K B hB Q F hF' T hT
  unfold CellBox.pairOn CellBox.lineWeightFn at o
  rw [e]
  exact o


private theorem low_part (m : ℕ) (K : CellBox) (Bs : CellBases) (L : CellLayout) (ι' : ℤ × ℤ)
    (hL : IsHarmonicLayout m K Bs {ι'.1} L) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space)
    (hv : IsPeriodicSecondOrder v G H) (W Ω : ℝ × ℝ → Fin 3 → ℂ)
    (hWc : ∀ a, Continuous fun p => W p a) (hΩc : ∀ a, Continuous fun p => Ω p a) (φ : Fin 3 → CellPoly) :
    rowPairing K (lowCoupling K L.degCoef W Ω (fun a b p => gradAt m ι' G a b p) (fun a p => velAt m ι' v a p)) φ
      = ∑ d, couplingRowVector L W Ω φ d * harmonicData L (labelTime ι') v G H Pg d := by
  obtain ⟨c, S, hco, hres, hcl⟩ := hL
  have hmodes : L.modes = {ι'.1} := hcl.modes_eq.trans hres
  have hK := hcl.box_valid
  have hB := hcl.bases_valid
  have hQ : 1 ≤ L.degCoef := by
    have := hcl.degSide_pos
    have := hcl.degSide_le
    omega
  have hord : L.order = m := hcl.order_eq.trans hco
  have hmode : harmonicMode (labelTime ι') ι'.1 = ι' := RowLow.Internal.harmonicMode_label ι'
  have heven : Even (ι'.1 + labelTime ι') := ⟨ι'.2, by unfold labelTime; ring⟩
  obtain ⟨hcF, hsF, hae⟩ := harmonicLift_holds m v G H hv (labelTime ι')
  have hae' := hae ι'.1 heven
  rw [hmode] at hae'
  have hr := ae_restrict_of_ae (μ := (volume : Measure (ℝ × ℝ))) (s := K.rect) hae'
  have hIc := fun a => LocalField.localModeIntegrable m _ _ _ hcF K hK ι'.1 a
  have hIs := fun a => LocalField.localModeIntegrable m _ _ _ hsF K hK ι'.1 a
  have hS := fun a b => CellCalculus.Internal.RowCouplingLow.coef_lift K Bs (F := fun p => gradAt m ι' G a b p)
    ((hIc a).2 b) ((hIs a).2 b)
    (by filter_upwards [hr, CellCalculus.Internal.RowCouplingLow.ae_rect_pos K hK] with p hp hp'
          using (hp hp').2.1 a b)
  have hV := fun a => CellCalculus.Internal.RowCouplingLow.coef_lift K Bs (F := fun p => velAt m ι' v a p)
    (Fc := fun p => modeVec m ι'.1 (harmonicCos (labelTime ι') v) p.1 p.2 a)
    (Fs := fun p => modeVec m ι'.1 (harmonicSin (labelTime ι') v) p.1 p.2 a) (hIc a).1 (hIs a).1
    (by filter_upwards [hr, CellCalculus.Internal.RowCouplingLow.ae_rect_pos K hK] with p hp hp'
          using (hp hp').1 a)
  have hΩv : Continuous (fun p => Ω p) := continuous_pi hΩc
  obtain ⟨C, hC⟩ := (CellCalculus.Internal.RowCouplingLow.rect_compact K).exists_bound_of_continuousOn
    hΩv.continuousOn
  have hb : ∃ C : ℝ, ∀ p ∈ K.rect, ∀ a, ‖Ω p a‖ ≤ C :=
    ⟨C, fun p hp a => (norm_le_pi_norm (Ω p) a).trans (hC p hp)⟩
  have hg : ∀ a, Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * W p a) := fun a =>
    (Complex.continuous_ofReal.comp continuous_fst).mul (hWc a)
  rw [CellCalculus.Internal.RowCouplingLow.pairing_expand K hK Bs hB L.degCoef hQ _ _ (fun a b => (hS a b).2)
    (fun a => (hV a).2) W Ω (fun a p => (p.1 : ℂ) * W p a) hg (fun a p _ => rfl)
    (fun a => (hΩc a).aestronglyMeasurable) hb φ]
  obtain ⟨hbox, hbas⟩ := And.intro hcl.box_eq hcl.bases_eq
  subst hbox hbas hord
  simp only [Fintype.sum_sum_type, couplingRowVector, Sum.elim_inl, Sum.elim_inr, zero_mul,
    Finset.sum_const_zero, add_zero, Fintype.sum_prod_type, harmonicData, CellLayout.trueData,
    CellLayout.gradModeOf, cosTuple, sinTuple]
  congr 1
  · symm
    refine CellCalculus.Internal.RowCouplingLow.sum_single_mode hmodes _ _ fun x hx => ?_
    rw [hx]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => ?_
    exact (mul_comm _ _).trans (congrArg (· * _) ((hS a b).1 j l))
  · symm
    refine CellCalculus.Internal.RowCouplingLow.sum_single_mode hmodes _ _ fun x hx => ?_
    rw [hx]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    exact (mul_comm _ _).trans (congrArg (· * _) ((hV a).1 j l))

private theorem tail_split (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (Q : ℕ)
    (s : Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (u : Fin 3 → ℝ × ℝ → ℂ)
    (hs : ∀ a b, IntegrableOn (s a b) K.rect) (hu : ∀ a, IntegrableOn (u a) K.rect)
    (c : Fin 12 → ℝ × ℝ → ℂ) (hc : ∀ j, Continuous (c j)) (T : Fin 12 → ℝ × ℝ → ℂ)
    (hTc : ∀ j, Continuous (T j))
    (hT : ∀ j, T j ∈ polyFn (if j.val < 9 then Q else Q - 1) (if j.val < 9 then Q else Q - 1)) :
    (∫ p in K.rect, (p.1 : ℂ) * ∑ j : Fin 12, pairVec (fun a b => s a b p) (fun a => u a p) j
        * (starRingEnd ℂ) (c j p))
      = (∫ p in K.rect, (p.1 : ℂ) * ∑ j : Fin 12, pairVec (fun a b => K.proj Q Q (s a b) p)
            (fun a => K.proj (Q - 1) (Q - 1) (u a) p) j * (starRingEnd ℂ) (c j p))
        + ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * ∑ j : Fin 12,
            pairVec (fun a b => s a b p - K.proj Q Q (s a b) p) (fun a => u a p - K.proj (Q - 1) (Q - 1) (u a) p) j
            * (starRingEnd ℂ) (((CellScalars.rHat K p : ℝ) : ℂ) * c j p - T j p) := by
  have hcomp := CellCalculus.Internal.RowCouplingLow.rect_compact K
  have hmeas := CellCalculus.Internal.RowCouplingLow.rect_meas K
  have hPs : ∀ a b, IntegrableOn (K.proj Q Q (s a b)) K.rect := fun a b =>
    (SharpYDensityRegular.Internal.proj_cont K Q Q (s a b)).continuousOn.integrableOn_compact hcomp
  have hPu : ∀ a, IntegrableOn (K.proj (Q - 1) (Q - 1) (u a)) K.rect := fun a =>
    (SharpYDensityRegular.Internal.proj_cont K (Q - 1) (Q - 1) (u a)).continuousOn.integrableOn_compact hcomp
  have hts : ∀ a b, IntegrableOn (fun p => s a b p - K.proj Q Q (s a b) p) K.rect := fun a b =>
    (hs a b).sub (hPs a b)
  have htu : ∀ a, IntegrableOn (fun p => u a p - K.proj (Q - 1) (Q - 1) (u a) p) K.rect := fun a =>
    (hu a).sub (hPu a)
  have hl := CellEnergy.HeightProj.continuous_lineWeight K
  have hw : ∀ j, Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * (starRingEnd ℂ) (c j p)) := fun j =>
    (Complex.continuous_ofReal.comp continuous_fst).mul (Complex.continuous_conj.comp (hc j))
  have iLow : IntegrableOn (fun p => ∑ j : Fin 12, pairVec (fun a b => K.proj Q Q (s a b) p)
      (fun a => K.proj (Q - 1) (Q - 1) (u a) p) j * ((p.1 : ℂ) * (starRingEnd ℂ) (c j p))) K.rect :=
    integrable_finsetSum _ fun j _ =>
      (pairVec_int (fun a b => K.proj Q Q (s a b)) (fun a => K.proj (Q - 1) (Q - 1) (u a)) hPs hPu j).mul_continuousOn
        (hw j).continuousOn hcomp
  have iTail : IntegrableOn (fun p => ∑ j : Fin 12, pairVec (fun a b => s a b p - K.proj Q Q (s a b) p)
      (fun a => u a p - K.proj (Q - 1) (Q - 1) (u a) p) j * ((p.1 : ℂ) * (starRingEnd ℂ) (c j p))) K.rect :=
    integrable_finsetSum _ fun j _ =>
      (pairVec_int (fun a b p => s a b p - K.proj Q Q (s a b) p) (fun a p => u a p - K.proj (Q - 1) (Q - 1) (u a) p)
        hts htu j).mul_continuousOn (hw j).continuousOn hcomp
  have iOrth : ∀ j : Fin 12, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ)
      * pairVec (fun a b => s a b p - K.proj Q Q (s a b) p) (fun a => u a p - K.proj (Q - 1) (Q - 1) (u a) p) j
      * (starRingEnd ℂ) (T j p)) K.rect := by
    intro j
    have hg : Continuous (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * (starRingEnd ℂ) (T j p)) :=
      (Complex.continuous_ofReal.comp (hl.comp continuous_fst)).mul (Complex.continuous_conj.comp (hTc j))
    refine ((pairVec_int (fun a b p => s a b p - K.proj Q Q (s a b) p)
      (fun a p => u a p - K.proj (Q - 1) (Q - 1) (u a) p) hts htu j).mul_continuousOn
        hg.continuousOn hcomp).congr_fun (fun p _ => ?_) hmeas
    dsimp only
    ring
  have hzero : ∀ j : Fin 12, ∫ p in K.rect, (K.lineWeight p.1 : ℂ)
      * pairVec (fun a b => s a b p - K.proj Q Q (s a b) p) (fun a => u a p - K.proj (Q - 1) (Q - 1) (u a) p) j
      * (starRingEnd ℂ) (T j p) = 0 := by
    intro j
    have hTj := hT j
    by_cases h : j.val < 9
    · rw [if_pos h] at hTj
      simp only [pairVec, dif_pos h]
      exact orth_zero K B hB Q _ (hs _ _) _ hTj
    · rw [if_neg h] at hTj
      simp only [pairVec, dif_neg h]
      exact orth_zero K B hB (Q - 1) _ (hu _) _ hTj
  have e1 : (fun p : ℝ × ℝ => (p.1 : ℂ) * ∑ j : Fin 12, pairVec (fun a b => s a b p) (fun a => u a p) j
        * (starRingEnd ℂ) (c j p))
      = fun p => (∑ j : Fin 12, pairVec (fun a b => K.proj Q Q (s a b) p)
          (fun a => K.proj (Q - 1) (Q - 1) (u a) p) j * ((p.1 : ℂ) * (starRingEnd ℂ) (c j p)))
        + ∑ j : Fin 12, pairVec (fun a b => s a b p - K.proj Q Q (s a b) p)
          (fun a => u a p - K.proj (Q - 1) (Q - 1) (u a) p) j * ((p.1 : ℂ) * (starRingEnd ℂ) (c j p)) := by
    funext p
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pairVec_split _ (fun a b => K.proj Q Q (s a b) p) _ (fun a => K.proj (Q - 1) (Q - 1) (u a) p) j]
    ring
  have e2 : (fun p : ℝ × ℝ => (p.1 : ℂ) * ∑ j : Fin 12, pairVec (fun a b => K.proj Q Q (s a b) p)
        (fun a => K.proj (Q - 1) (Q - 1) (u a) p) j * (starRingEnd ℂ) (c j p))
      = fun p => ∑ j : Fin 12, pairVec (fun a b => K.proj Q Q (s a b) p)
          (fun a => K.proj (Q - 1) (Q - 1) (u a) p) j * ((p.1 : ℂ) * (starRingEnd ℂ) (c j p)) := by
    funext p
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have e3 : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * ∑ j : Fin 12,
            pairVec (fun a b => s a b p - K.proj Q Q (s a b) p) (fun a => u a p - K.proj (Q - 1) (Q - 1) (u a) p) j
            * (starRingEnd ℂ) (((CellScalars.rHat K p : ℝ) : ℂ) * c j p - T j p))
      =ᵐ[volume.restrict K.rect] fun p => (∑ j : Fin 12, pairVec (fun a b => s a b p - K.proj Q Q (s a b) p)
          (fun a => u a p - K.proj (Q - 1) (Q - 1) (u a) p) j * ((p.1 : ℂ) * (starRingEnd ℂ) (c j p)))
        - ∑ j : Fin 12, (K.lineWeight p.1 : ℂ)
          * pairVec (fun a b => s a b p - K.proj Q Q (s a b) p) (fun a => u a p - K.proj (Q - 1) (Q - 1) (u a) p) j
          * (starRingEnd ℂ) (T j p) := by
    filter_upwards [ae_restrict_of_ae CellCalculus.Internal.RowCouplingLow.fst_ne_zero_ae] with p hp
    rw [weight_split K p hp, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_sub, map_mul, Complex.conj_ofReal]
    ring
  rw [e1, e2, integral_add iLow iTail, integral_congr_ae e3,
    integral_sub iTail (integrable_finsetSum _ fun j _ => iOrth j), integral_finsetSum _ fun j _ => iOrth j,
    Finset.sum_eq_zero fun j _ => hzero j, sub_zero]


theorem resolved_model_pairing (m : ℕ) (K : CellBox) (Bs : CellBases) (L : CellLayout) (ι' : ℤ × ℤ)
    (hL : IsHarmonicLayout m K Bs {ι'.1} L) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space)
    (hv : IsPeriodicSecondOrder v G H) (hp : IsPeriodicPressure Pg) (hax : K.IsAxis → ι'.1 = 0)
    (Wα Ωα : ℝ × ℝ → Fin 3 → ℂ)
    (hW : ∃ W' : ℝ × ℝ → Fin 3 → ℂ, (∀ a, Continuous fun p => W' p a) ∧ ∀ p ∈ K.rect, Wα p = W' p)
    (hΩ : ∃ Ω' : ℝ × ℝ → Fin 3 → ℂ, (∀ a, Continuous fun p => Ω' p a) ∧ ∀ p ∈ K.rect, Ωα p = Ω' p)
    (φ : Fin 3 → CellPoly) :
    (∫ p in K.rect, (p.1 : ℂ) * ∑ j : Fin 12, pairVec (gradArray m ι' G p) (velArray m ι' v p) j
        * (starRingEnd ℂ) (crossTest (Wα p) (Ωα p) (testValue K φ p) j))
      = ∑ d, couplingRowVector L Wα Ωα φ d * harmonicData L (labelTime ι') v G H Pg d
        + ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * ∑ j : Fin 12,
            pairVec (fun a b => gradAt m ι' G a b p - K.proj L.degCoef L.degCoef (fun p' => gradAt m ι' G a b p') p)
              (fun a => velAt m ι' v a p - K.proj (L.degCoef - 1) (L.degCoef - 1) (fun p' => velAt m ι' v a p') p) j
            * (starRingEnd ℂ) (((CellScalars.rHat K p : ℝ) : ℂ) * crossTest (Wα p) (Ωα p) (testValue K φ p) j
                - K.proj (if j.val < 9 then L.degCoef else L.degCoef - 1)
                    (if j.val < 9 then L.degCoef else L.degCoef - 1)
                    (fun p' => ((CellScalars.rHat K p' : ℝ) : ℂ) * crossTest (Wα p') (Ωα p') (testValue K φ p') j) p) := by
  have hL' := hL
  obtain ⟨c, S, -, -, hcl⟩ := hL'
  have hK := hcl.box_valid
  have hB := hcl.bases_valid
  obtain ⟨W', hW'c, hW'e⟩ := hW
  obtain ⟨Ω', hΩ'c, hΩ'e⟩ := hΩ
  have hmeas := CellCalculus.Internal.RowCouplingLow.rect_meas K
  have hsI : ∀ a b, IntegrableOn (fun p => gradAt m ι' G a b p) K.rect := fun a b =>
    RowLow.Internal.gradAt_int harmonicLift_holds hv m ι' hK a b
  have huI : ∀ a, IntegrableOn (fun p => velAt m ι' v a p) K.rect := fun a =>
    RowLow.Internal.velAt_int harmonicLift_holds hv m ι' hK a
  have hlow := low_part m K Bs L ι' hL v G H Pg hv W' Ω' hW'c hΩ'c φ
  have hcore := tail_split K Bs hB L.degCoef (fun a b p => gradAt m ι' G a b p) (fun a p => velAt m ι' v a p) hsI huI
    (fun j p => crossTest (W' p) (Ω' p) (testValue K φ p) j) (fun j => crossTest_cont W' Ω' hW'c hΩ'c K φ j)
    (fun j => K.proj (if j.val < 9 then L.degCoef else L.degCoef - 1) (if j.val < 9 then L.degCoef else L.degCoef - 1)
      (fun p' => ((CellScalars.rHat K p' : ℝ) : ℂ) * crossTest (Wα p') (Ωα p') (testValue K φ p') j))
    (fun j => SharpYDensityRegular.Internal.proj_cont K _ _ _)
    (fun j => ResolvedEnergyInternal.proj_mem K _ _ _)
  have hrow : couplingRowVector L Wα Ωα φ = couplingRowVector L W' Ω' φ := by
    have hbox := hcl.box_eq
    funext d
    rcases d with i | i | i
    · simp only [couplingRowVector, Sum.elim_inl]
      unfold couplingStrainRow
      rw [hbox]
      refine setIntegral_congr_fun hmeas fun p hp => ?_
      simp only [hW'e p hp]
    · simp only [couplingRowVector, Sum.elim_inr, Sum.elim_inl]
      unfold couplingVelocityRow
      rw [hbox]
      refine setIntegral_congr_fun hmeas fun p hp => ?_
      simp only [hΩ'e p hp]
    · rfl
  have hLHS : (∫ p in K.rect, (p.1 : ℂ) * ∑ j : Fin 12, pairVec (gradArray m ι' G p) (velArray m ι' v p) j
        * (starRingEnd ℂ) (crossTest (Wα p) (Ωα p) (testValue K φ p) j))
      = ∫ p in K.rect, (p.1 : ℂ) * ∑ j : Fin 12, pairVec (gradArray m ι' G p) (velArray m ι' v p) j
        * (starRingEnd ℂ) (crossTest (W' p) (Ω' p) (testValue K φ p) j) :=
    setIntegral_congr_fun hmeas fun p hp => by simp only [hW'e p hp, hΩ'e p hp]
  have hTail : (∫ p in K.rect, (K.lineWeight p.1 : ℂ) * ∑ j : Fin 12,
            pairVec (fun a b => gradAt m ι' G a b p - K.proj L.degCoef L.degCoef (fun p' => gradAt m ι' G a b p') p)
              (fun a => velAt m ι' v a p - K.proj (L.degCoef - 1) (L.degCoef - 1) (fun p' => velAt m ι' v a p') p) j
            * (starRingEnd ℂ) (((CellScalars.rHat K p : ℝ) : ℂ) * crossTest (Wα p) (Ωα p) (testValue K φ p) j
                - K.proj (if j.val < 9 then L.degCoef else L.degCoef - 1)
                    (if j.val < 9 then L.degCoef else L.degCoef - 1)
                    (fun p' => ((CellScalars.rHat K p' : ℝ) : ℂ) * crossTest (Wα p') (Ωα p') (testValue K φ p') j) p))
      = ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * ∑ j : Fin 12,
            pairVec (fun a b => gradAt m ι' G a b p - K.proj L.degCoef L.degCoef (fun p' => gradAt m ι' G a b p') p)
              (fun a => velAt m ι' v a p - K.proj (L.degCoef - 1) (L.degCoef - 1) (fun p' => velAt m ι' v a p') p) j
            * (starRingEnd ℂ) (((CellScalars.rHat K p : ℝ) : ℂ) * crossTest (W' p) (Ω' p) (testValue K φ p) j
                - K.proj (if j.val < 9 then L.degCoef else L.degCoef - 1)
                    (if j.val < 9 then L.degCoef else L.degCoef - 1)
                    (fun p' => ((CellScalars.rHat K p' : ℝ) : ℂ) * crossTest (Wα p') (Ωα p') (testValue K φ p') j) p) :=
    setIntegral_congr_fun hmeas fun p hp => by rw [hW'e p hp, hΩ'e p hp]
  have hlowint : (∫ p in K.rect, (p.1 : ℂ) * ∑ j : Fin 12, pairVec (fun a b => K.proj L.degCoef L.degCoef
          (fun p' => gradAt m ι' G a b p') p)
        (fun a => K.proj (L.degCoef - 1) (L.degCoef - 1) (fun p' => velAt m ι' v a p') p) j
        * (starRingEnd ℂ) (crossTest (W' p) (Ω' p) (testValue K φ p) j))
      = rowPairing K (lowCoupling K L.degCoef W' Ω' (fun a b p => gradAt m ι' G a b p)
          (fun a p => velAt m ι' v a p)) φ := by
    unfold rowPairing
    congr 1
    funext p
    rw [cross_pair]
    rfl
  rw [hrow, hTail]
  refine hLHS.trans (hcore.trans ?_)
  congr 1
  exact hlowint.trans hlow

end Breakdown.CertCell.Assembly.Internal.RowIdentity
