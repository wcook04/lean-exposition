import Breakdown.CertCell.InstanceStatements
import Breakdown.Cert.CoercivePieceDensityPassageLimit

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Instance

namespace Internal.RowOrthonormal

open Coercive.Internal.PassageLimit

theorem normalizer_sandwich {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ) (hG : G.PosDef) :
    hG.isHermitian.cfc (fun x => (Real.sqrt x)⁻¹) * G *
      (hG.isHermitian.cfc (fun x => (Real.sqrt x)⁻¹)).transpose = 1 := by
  have hH := hG.isHermitian
  rw [← hH.cfc_eq]
  have hsa : IsSelfAdjoint (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) G) := cfc_predicate _ _
  have htr : (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) G).transpose = cfc (fun x : ℝ => (Real.sqrt x)⁻¹) G := by
    have h := hsa.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hfin : (spectrum ℝ G).Finite := Matrix.finite_real_spectrum
  have hsG : IsSelfAdjoint G := hH
  rw [htr]
  calc cfc (fun x : ℝ => (Real.sqrt x)⁻¹) G * G * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) G
      = cfc (fun x : ℝ => (Real.sqrt x)⁻¹) G * cfc (fun x : ℝ => x) G *
          cfc (fun x : ℝ => (Real.sqrt x)⁻¹) G := by
        rw [cfc_id' ℝ G]
    _ = cfc (fun x : ℝ => (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹) G := by
        rw [← cfc_mul (fun x : ℝ => (Real.sqrt x)⁻¹) (fun x : ℝ => x) G (hfin.continuousOn _)
            (hfin.continuousOn _),
          ← cfc_mul (fun x : ℝ => (Real.sqrt x)⁻¹ * x) (fun x : ℝ => (Real.sqrt x)⁻¹) G
            (hfin.continuousOn _) (hfin.continuousOn _)]
    _ = cfc (fun _ : ℝ => (1 : ℝ)) G := by
        refine cfc_congr fun x hx => ?_
        obtain ⟨i, rfl⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hx
        have h0 := hG.eigenvalues_pos i
        have hss := Real.mul_self_sqrt h0.le
        have e : (Real.sqrt (hH.eigenvalues i))⁻¹ * hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i))⁻¹ =
            hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i) * Real.sqrt (hH.eigenvalues i))⁻¹ := by
          rw [mul_inv]; ring
        show (Real.sqrt (hH.eigenvalues i))⁻¹ * hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i))⁻¹ = 1
        rw [e, hss, mul_inv_cancel₀ h0.ne']
    _ = 1 := cfc_const_one ℝ G

theorem pairing_of_combinations {ι : Type*} [Fintype ι] (c d : ι → ℝ) (g : ι → ℝ → Space → Space)
    (hint : ∀ i j, Integrable (fun z : ℝ × Space => inner ℝ (g i z.1 z.2) (g j z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume)) :
    periodPairing (fun σ y => ∑ i, c i • g i σ y) (fun σ y => ∑ j, d j • g j σ y) =
      ∑ i, ∑ j, c i * d j * periodPairing (g i) (g j) := by
  have hpt : ∀ z : ℝ × Space, inner ℝ (∑ i, c i • g i z.1 z.2) (∑ j, d j • g j z.1 z.2) =
      ∑ i, ∑ j, c i * d j * inner ℝ (g i z.1 z.2) (g j z.1 z.2) := by
    intro z
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  have hI : Integrable (fun z : ℝ × Space => ∑ i, ∑ j, c i * d j * inner ℝ (g i z.1 z.2) (g j z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _
  have hI' : Integrable (fun z : ℝ × Space => inner ℝ (∑ i, c i • g i z.1 z.2) (∑ j, d j • g j z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) :=
    hI.congr (ae_of_all _ fun z => (hpt z).symm)
  rw [periodPairing_eq_integral (A := fun σ y => ∑ i, c i • g i σ y) (B := fun σ y => ∑ j, d j • g j σ y) hI']
  rw [integral_congr_ae (ae_of_all _ hpt)]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, periodPairing_eq_integral (hint i j)]

end Internal.RowOrthonormal

open Internal.RowOrthonormal Coercive.Internal.PassageLimit

theorem rowFieldsOrthonormal (hreg : CellVecFieldRegular) : RowFieldsOrthonormal := by
  intro rowCount M R m tauMax hR hG a b
  have hM := hR.mesh_valid
  have hint : ∀ i j, Integrable
      (fun z : ℝ × Space => inner ℝ (R.generatorField M.box m i z.1 z.2) (R.generatorField M.box m j z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := fun i j =>
    period_integrable_inner (hreg M (R.generator i) m hM).1 (hreg M (R.generator j) m hM).1
      (hreg M (R.generator i) m hM).2.2.2 (hreg M (R.generator j) m hM).2.2.2
  have key := pairing_of_combinations (R.mix M.box m a) (R.mix M.box m b) (R.generatorField M.box m) hint
  have hmix : R.mix M.box m = hG.isHermitian.cfc (fun x => (Real.sqrt x)⁻¹) := by
    unfold RowValues.mix
    rw [dif_pos hG.isHermitian]
  have hs := normalizer_sandwich _ hG
  rw [← hmix] at hs
  have hab := congrFun (congrFun hs a) b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hab
  show periodPairing (fun σ y => ∑ i, R.mix M.box m a i • R.generatorField M.box m i σ y)
    (fun σ y => ∑ j, R.mix M.box m b j • R.generatorField M.box m j σ y) = if a = b then 1 else 0
  rw [key, ← hab, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold RowValues.fieldPairingMatrix
  ring

end Instance

end CertCell

end Breakdown
