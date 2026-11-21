import Breakdown.CertCell.LocalFieldDefs2
import Breakdown.FracCell.EnergyHeight

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy

namespace Internal

open CellCert.CellEnergy.EnergyHeightInternal

variable {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}

theorem heightLowRowValue (K : CellBox) (B : CellBases) (I : LowIndex D modes Q q) (hK : IsCellBox K)
    (m : ℕ) (F : modes → Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (T : modes → Fin 3 → Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (u : D → ℂ) (hd : IsModeData m K B I F T u) (n : modes) (C : Fin 3 → Fin 3 → ℂ) (j l : Fin (Q + 1)) :
    rowApply (lowRow I n C j l) u = B.coef K (modeSum C (F n)) j l := by
  have h1 : rowApply (lowRow I n C j l) u = ∑ a, ∑ b, C a b * u (I.strainSlot n a b j l) := by
    simp only [rowApply, lowRow, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp [mul_ite, ite_mul]
  rw [h1]
  simp only [hd.strain]
  unfold CellBases.coef modeSum
  have hint : ∀ a b, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F n a b p *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect := by
    intro a b
    have h := (hd.height_weak n a b (fun r => K.lineWeight r * B.radialPoly j r) (B.heightPoly l)
      ((HeightProj.continuous_lineWeight K).mul (continuous_radialPoly B j)) (continuous_heightPoly B l)
      (side_lw K hK _ (continuous_radialPoly B j))).1
    refine h.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
    push_cast; ring
  have e : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * (∑ a, ∑ b, C a b * F n a b p) *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) = fun p => ∑ a, ∑ b, C a b *
      ((K.lineWeight p.1 : ℂ) * F n a b p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) := by
    funext p
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  rw [e, comb_integral _ C _ hint]

theorem heightFaceCompValue (K : CellBox) (B : CellBases) (I : LowIndex D modes Q q) (hK : IsCellBox K)
    (m : ℕ) (F : modes → Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (T : modes → Fin 3 → Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (u : D → ℂ) (hd : IsModeData m K B I F T u) (n : modes) (C : Fin 3 → Fin 3 → ℂ)
    (e : Fin 2) (j : Fin (q + 1)) :
    rowApply (heightFaceComp I n C e j) u =
      heightFaceMoment K (modeSum C (F n)) (modeSum C (fun a b => T n a b 2)) e (B.radialPoly j) := by
  have h1 : rowApply (heightFaceComp I n C e j) u = ∑ a, ∑ b, C a b * rowApply (I.heightFaceRow n e a b j) u := by
    simp only [rowApply, heightFaceComp, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun _ _ => by ring))
  rw [h1]
  simp only [hd.height_face]
  exact face_comb K hK C _ _ (fun a b => hd.height_weak n a b) e _ (continuous_radialPoly B j)

end Internal

open Breakdown.CertCell.LocalField.Internal CellCert.CellEnergy.EnergyHeightInternal in
theorem localComponentHeight : LocalComponentHeightStatement := by
  intro D _ _ modes Q q m K B I F T u hK hB hq1 hqQ hd n C
  have hpair : HeightWeakPair K (modeSum C (F n)) (modeSum C (fun a b => T n a b 2)) :=
    pair_comb K C _ _ (fun a b => hd.height_weak n a b)
  have hrow := heightLowRowValue K B I hK m F T u hd n C
  have hface := heightFaceCompValue K B I hK m F T u hd n C
  have hrect : ∀ p ∈ K.rect, K.r₁ ≤ p.1 ∧ K.refZ p.2 ^ 2 ≤ 1 := fun p hp =>
    ⟨hp.1.1, refZ_sq_le K hK hp.2⟩
  have h3 : quadFormValue (heightOuterForm K B I n C) u =
      K.testSupremum (fun p => p.1) (polyFn q Q)
        (fun p => (K.refZ p.2 : ℂ) * modeSum C (fun a b => T n a b 2) p) := by
    symm
    unfold heightOuterForm
    refine HeightParts.testSup_polyFn K hK (fun p => p.1) continuous_fst
      (fun p hp => le_trans hK.r_order.1 (hrect p hp).1)
      (fun p hp => lt_of_le_of_lt hK.r_order.1 hp.1.1) q Q _ _ u (fun i => ?_) (fun i => ?_)
    · have h := (hpair (fun r => r * r ^ (i.1 : ℕ)) (fun z => K.refZ z * z ^ (i.2 : ℕ)) (by fun_prop)
        ((continuous_refZ K).mul (continuous_pow _)) (Or.inr ⟨fun r => r ^ (i.1 : ℕ), by fun_prop, fun r => rfl⟩)).2.1
      refine h.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
      simp only [monomial]; push_cast; ring
    · exact HeightRows.outer_rows K B I hK hB hqQ n C _ _ hpair u hrow hface i
  have h2 : quadFormValue (if K.r₁ = 0 then 0 else heightInnerForm K B I n C) u =
      (if K.r₁ = 0 then 0 else
        K.testSupremum (fun p => (p.1 - K.r₁) * (1 - K.refZ p.2 ^ 2)) (polyFn (Q - 1) (Q - 1))
          (modeSum C (fun a b => T n a b 2))) := by
    split_ifs with h0
    · exact RadialForm.value_zero u
    · have hr : 0 < K.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h0)
      obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      symm
      unfold heightInnerForm
      refine HeightParts.testSup_polyFn K hK (heightInnerWeight K) ?_ ?_ ?_ Q' Q' _ _ u (fun i => ?_) (fun i => ?_)
      · unfold heightInnerWeight; exact (continuous_fst.sub continuous_const).mul
          (continuous_const.sub (((continuous_refZ K).comp continuous_snd).pow 2))
      · intro p hp
        unfold heightInnerWeight
        exact mul_nonneg (by linarith [(hrect p hp).1]) (by linarith [(hrect p hp).2])
      · intro p hp
        unfold heightInnerWeight
        exact mul_pos (by linarith [hp.1.1]) (by linarith [refZ_sq_lt K hK hp.2])
      · have h := (hpair (fun r => (r - K.r₁) * r ^ (i.1 : ℕ)) (fun z => (1 - K.refZ z ^ 2) * z ^ (i.2 : ℕ))
          (by fun_prop) ((continuous_const.sub ((continuous_refZ K).pow 2)).mul (continuous_pow _))
          (Or.inl hr)).2.1
        refine h.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
        simp only [monomial, heightInnerWeight]; push_cast; ring
      · exact HeightRows.inner_rows K B I hK hB hr n C _ _ hpair u hrow i
  rw [RadialForm.value_add, RadialForm.value_add, proj_value K B I hK hB n C _ _ hpair u hrow, h2, h3]
  rfl

end LocalField

end CertCell

end Breakdown
