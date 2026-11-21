import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

private lemma norm_unitVector_eq_one (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

private lemma abs_clm_entry_le (L : Space →L[ℝ] Space) (i j : Fin 3) :
    |L (unitVector i) j| ≤ ‖L‖ := by
  calc |L (unitVector i) j| = ‖L (unitVector i) j‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖L (unitVector i)‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖L‖ * ‖unitVector i‖ := L.le_opNorm _
    _ = ‖L‖ := by rw [norm_unitVector_eq_one, mul_one]

private lemma abs_pressureSource_le (W : ℝ → Space → Space) (s : ℝ) (z : Space) :
    |pressureSource W s z| ≤ 9 * ‖fderiv ℝ (W s) z‖ ^ 2 := by
  unfold pressureSource
  set L := fderiv ℝ (W s) z
  calc |∑ i : Fin 3, ∑ j : Fin 3, L (unitVector i) j * L (unitVector j) i|
      ≤ ∑ i : Fin 3, ∑ j : Fin 3, |L (unitVector i) j * L (unitVector j) i| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖L‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, sq]
        exact mul_le_mul (abs_clm_entry_le L i j) (abs_clm_entry_le L j i) (abs_nonneg _)
          (norm_nonneg _)
    _ = 9 * ‖L‖ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

private lemma contDiff_pressureSource (W : ℝ → Space → Space)
    (hW : ContDiff ℝ ∞ (fun p : ℝ × Space => W p.1 p.2)) (s : ℝ) :
    ContDiff ℝ ∞ (pressureSource W s) := by
  have hs : ContDiff ℝ ∞ (W s) := hW.comp (contDiff_const.prodMk contDiff_id)
  have hD : ContDiff ℝ ∞ (fderiv ℝ (W s)) := hs.fderiv_right (m := ∞) (by simp)
  have hcol : ∀ a b : Fin 3, ContDiff ℝ ∞ (fun y => fderiv ℝ (W s) y (unitVector a) b) :=
    fun a b => (EuclideanSpace.proj b : Space →L[ℝ] ℝ).contDiff.comp (hD.clm_apply contDiff_const)
  unfold pressureSource
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => (hcol i j).mul (hcol j i)

theorem pressureSourceBound_holds : PressureSourceBound := by
  intro W hW A hA
  refine ⟨9 * A ^ 2, fun s => ⟨contDiff_pressureSource W hW s, fun z => ?_⟩⟩
  have hpos : 0 < 1 + ‖z‖ := by positivity
  have h1 : (1 + ‖z‖) ^ (2 : ℝ) * ‖fderiv ℝ (W s) z‖ ≤ A := hA s z
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
  have hN : ‖fderiv ℝ (W s) z‖ ≤ A / (1 + ‖z‖) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  calc |pressureSource W s z| ≤ 9 * ‖fderiv ℝ (W s) z‖ ^ 2 := abs_pressureSource_le W s z
    _ ≤ 9 * (A / (1 + ‖z‖) ^ 2) ^ 2 := by gcongr
    _ = 9 * A ^ 2 / (1 + ‖z‖) ^ 4 := by
        generalize 1 + ‖z‖ = B
        ring

end Breakdown.FarField
