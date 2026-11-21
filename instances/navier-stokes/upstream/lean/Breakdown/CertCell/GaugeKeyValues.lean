import Breakdown.CertCell.GaugeKeyDefs
import Breakdown.CertCell.Defs
import Breakdown.CertCell.StatementDefs

noncomputable section

namespace Breakdown.CertCell.GaugeKey

open Breakdown.CellCert.CellCoordinates

def keyPart (imag : Bool) (z : ℂ) : ℝ := if imag then z.im else z.re

namespace GaugeKeyValues

variable (G : GaugeKeyValues)

theorem dir_support {c : Fin G.count} {ι : ℤ × ℤ} {key : SkeletonKey} (h : G.dir c ι key ≠ 0) :
    ι = G.classLabel c ∧ ∃ rad lev lo hi t d, key = SkeletonKey.pressure 0 rad lev lo hi t d := by
  cases key with
  | pressure n rad lev lo hi t d =>
      by_cases hc : ι = G.classLabel c ∧ n = 0
      · exact ⟨hc.1, rad, lev, lo, hi, t, d, by rw [hc.2]⟩
      · exfalso; apply h; simp [dir, dirReal, hc]
  | _ => exfalso; apply h; simp [dir, dirReal]

theorem matrix_mul_inverse (hG : G.Conditions) : G.matrix * G.inverse = 1 := by
  ext e e'
  have hw : ∀ e, (G.deletedWeight e : ℂ) ≠ 0 := fun e => by exact_mod_cast hG.weight_ne e
  simp only [Matrix.mul_apply, Matrix.one_apply, hG.matrix_eq, weightedIncidence, inverse]
  have key : ∑ c, (G.incidence e c : ℂ) * (G.incidenceInv c e' : ℂ) = if e = e' then 1 else 0 := by
    have := congrArg (fun q : ℚ => (q : ℂ)) (hG.inv_right e e')
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast] at this
    rw [this]; split_ifs <;> simp
  calc ∑ c, (G.deletedWeight e : ℂ) * (G.incidence e c : ℂ) * ((G.incidenceInv c e' : ℂ) / (G.deletedWeight e' : ℂ))
      = (G.deletedWeight e : ℂ) / (G.deletedWeight e' : ℂ) *
          ∑ c, (G.incidence e c : ℂ) * (G.incidenceInv c e' : ℂ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun c _ => ?_); ring
    _ = if e = e' then 1 else 0 := by
        rw [key]; split_ifs with h
        · subst h; simp [hw e]
        · simp

theorem conj_weight (hG : G.Conditions) (e : Fin G.count) : G.deletedWeight (G.conjClass e) = G.deletedWeight e := by
  simp only [deletedWeight, hG.deleted_conj]

theorem inverse_conj (hG : G.Conditions) (c e : Fin G.count) :
    G.inverse (G.conjClass c) (G.conjClass e) = G.inverse c e := by
  simp only [inverse, hG.inv_conj, conj_weight G hG]

theorem inverse_star (c e : Fin G.count) : (starRingEnd ℂ) (G.inverse c e) = G.inverse c e := by
  simp only [inverse, map_div₀, Complex.conj_ofReal, map_ratCast]

def shiftValue (kh : Fin G.count → ℂ) (c : Fin G.count) : ℂ := -∑ e, G.inverse c e * kh e

theorem deleted_shift_zero (hG : G.Conditions) (kh : Fin G.count → ℂ) (e : Fin G.count) :
    kh e + ∑ c, G.shiftValue kh c * G.matrix e c = 0 := by
  have hM := G.matrix_mul_inverse hG
  have h1 : ∑ c, G.shiftValue kh c * G.matrix e c = -∑ e', (G.matrix * G.inverse) e e' * kh e' := by
    simp only [shiftValue, Matrix.mul_apply, Finset.sum_mul, neg_mul, Finset.sum_neg_distrib, neg_inj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e' _ => Finset.sum_congr rfl (fun c _ => ?_))
    ring
  rw [h1, hM]
  simp [Matrix.one_apply]

theorem shift_conj (hG : G.Conditions) (kh : Fin G.count → ℂ)
    (hkh : ∀ e, kh (G.conjClass e) = (starRingEnd ℂ) (kh e)) (c : Fin G.count) :
    G.shiftValue kh (G.conjClass c) = (starRingEnd ℂ) (G.shiftValue kh c) := by
  have hinv : Function.Involutive G.conjClass := hG.conj_invol
  simp only [shiftValue, map_neg, map_sum, map_mul, inverse_star, neg_inj]
  rw [← Equiv.sum_comp hinv.toPerm]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  simp only [Function.Involutive.coe_toPerm, inverse_conj G hG, hkh]

theorem shift_real (hG : G.Conditions) (kh : Fin G.count → ℂ)
    (hkh : ∀ e, kh (G.conjClass e) = (starRingEnd ℂ) (kh e)) (c : Fin G.count) (hc : G.conjClass c = c) :
    (G.shiftValue kh c).im = 0 := by
  have h := G.shift_conj hG kh hkh c
  rw [hc] at h
  exact Complex.conj_eq_iff_im.mp h.symm

end GaugeKeyValues

end Breakdown.CertCell.GaugeKey
