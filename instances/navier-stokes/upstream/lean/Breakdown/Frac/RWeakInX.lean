import Breakdown.Frac.StRealize
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

theorem fracWeakInX_of (α : ℝ) (_hα : 1 < α) (_hα2 : α < 3 / 2) (h1 : NiceFieldProps α)
    (h2 : NicePairingByParts) (h3 : NiceAdvectionTrilinear) : FracWeakInX α := by
  have hE : PairingEmbed := pairingEmbed embedNormLinear_holds.1 embedNormLinear_holds.2
  intro v a b hab hw φ hφ t ht
  obtain ⟨hdec, hcont, -, -, hder, hpc⟩ := hw
  obtain ⟨-, hφd, hψn, hAn, hcomm⟩ := h1 φ hφ
  obtain ⟨⟨S, hS⟩, -, -, -, -⟩ := h1 _ hψn
  obtain ⟨-, hAd, -, -, -⟩ := h1 _ hAn
  have hm2 : MemLp (negSsp φ) 2 volume := by rw [← hS]; exact S.memLp 2 volume
  have hm6 : MemLp (negSsp φ) 6 volume := by rw [← hS]; exact S.memLp 6 volume
  have hGc : ContinuousOn (fun s => inner ℝ (embedX (v s)) (embedX (fractionalPowerAt α φ)) +
      trilinear (embedX (v s)) (embedX (v s)) (negSsp φ)) (Icc a b) := by
    have hq := Internal.WeakInX.continuous_trilinear_diag trilinear_holds (negSsp φ) hm2 hm6
    exact (hcont.inner continuousOn_const).add (hq.comp_continuousOn hcont)
  have hta : a ≤ t := ht.1
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hGi := (hGc.mono hsub).intervalIntegrable_of_Icc (μ := volume) hta
  refine ⟨hGi, ?_⟩
  have hF : ∀ s ∈ Icc a b, fieldPairing (v s) (negSsp φ) = inner ℝ (embedX (v s)) (embedX φ) := by
    intro s hs
    rw [hE _ _ (hdec s hs) hφd, h2 _ _ (hdec s hs) hφ]
  have hd' : ∀ s ∈ Ioo a t, HasDerivAt (fun τ => fieldPairing (v τ) (negSsp φ))
      (-(inner ℝ (embedX (v s)) (embedX (fractionalPowerAt α φ)) +
        trilinear (embedX (v s)) (embedX (v s)) (negSsp φ))) s := by
    intro s hs
    have hs' : s ∈ Ioo a b := ⟨hs.1, hs.2.trans_le ht.2⟩
    have hsI : s ∈ Icc a b := Ioo_subset_Icc_self hs'
    refine (hder _ hψn s hs').congr_deriv ?_
    rw [hcomm, ← h2 _ _ (hdec s hsI) hAn, ← hE _ _ (hdec s hsI) hAd, h3 _ _ (hdec s hsI) hψn]
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hta ((hpc _ hψn).mono hsub)
    hd' hGi.neg
  rw [intervalIntegral.integral_neg, hF t ht, hF a ⟨le_rfl, hab.le⟩] at hftc
  linarith

end Breakdown.Freq
