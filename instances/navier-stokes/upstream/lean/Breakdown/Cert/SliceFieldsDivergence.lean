import Breakdown.FreqTr.Realization
import Breakdown.FreqTr.EmbedMem
import Breakdown.FreqTr.VelocityExists

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.SliceFieldsDivergence

def divMap : X →L[ℝ] L2R :=
  ∑ i : Fin 3, (ContinuousLinearMap.compLpL 2 volume (Freq.Internal.EmbedMem.coordReal i)).comp
    (partialX i)

theorem divMap_ae (x : X) :
    (divMap x : Space → Space) =ᵐ[volume]
      fun y => (∑ i : Fin 3, (partialX i x : Space → Space) y i) •
        EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := by
  have hs : divMap x = ∑ i : Fin 3, ContinuousLinearMap.compLpL 2 volume
      (Freq.Internal.EmbedMem.coordReal i) (partialX i x) := by
    simp [divMap]
  rw [hs]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin 3 => ContinuousLinearMap.compLpL 2
      volume (Freq.Internal.EmbedMem.coordReal i) (partialX i x)),
    ae_all_iff.2 fun i : Fin 3 => ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume)
      (Freq.Internal.EmbedMem.coordReal i) (partialX i x)] with y hs hi
  rw [hs, Finset.sum_apply]
  simp only [hi, Freq.Internal.EmbedMem.coordReal_apply]
  rw [← Finset.sum_smul]

theorem divMap_embed {φ : Space → Space} (hφ : IsTestField φ) : divMap (embedX φ) = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hd := Freq.Internal.VelocityExists.isDecayField_of_isTestField hφ
  filter_upwards [divMap_ae (embedX φ), ae_all_iff.2 fun i => partial_holds.1 φ hd i] with y h1 h2
  rw [h1]
  simp only [h2]
  have h3 : ∑ i : Fin 3, partialField φ i y i = 0 := hφ.2.2 y
  rw [h3, zero_smul]
  rfl

theorem divMap_apply_eq_zero (x : X) : divMap x = 0 := by
  have hsub : (testSpan : Set X) ⊆ {z : X | divMap z = 0} := by
    intro z hz
    obtain ⟨ψ, hψ, rfl⟩ := testSpan_holds z hz
    exact divMap_embed hψ
  have hcl := closure_minimal hsub (isClosed_eq divMap.continuous continuous_const)
  rw [testDense_holds.2.closure_eq] at hcl
  exact hcl (mem_univ x)

end Internal.SliceFieldsDivergence

theorem partialX_divergence (x : X) :
    ∀ᵐ y ∂volume, ∑ i : Fin 3, (partialX i x : Space → Space) y i = 0 := by
  have h0 := Internal.SliceFieldsDivergence.divMap_ae x
  rw [Internal.SliceFieldsDivergence.divMap_apply_eq_zero x] at h0
  filter_upwards [h0, Lp.coeFn_zero Space 2 volume] with y h1 h2
  have h3 := congrArg (fun w : Space => w 0) (h1.symm.trans h2)
  simpa using h3

end Breakdown.Cert
