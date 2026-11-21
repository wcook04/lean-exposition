import Breakdown.CertTorus.RegularStatements

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace Breakdown.FarField

open Freq Freq.Internal.H1Consistency

namespace Internal.DerivClosedProof

theorem tendsto_coe_of_tendsto {xs : ℕ → X} {x : X} (h : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun m => ((xs m : X) : L2C)) atTop (𝓝 (x : L2C)) :=
  (continuous_subtype_val.tendsto x).comp h

theorem mem_sig_of_ae_tendsto {g : ℕ → L2C} (hg : ∀ i, g i ∈ Sig) {G : Space → CSpace}
    (hlim : ∀ᵐ ξ ∂volume, Tendsto (fun i => (g i : Space → CSpace) ξ) atTop (𝓝 (G ξ)))
    {h : L2C} (hh : (h : Space → CSpace) =ᵐ[volume] G) : h ∈ Sig := by
  have h1 := fieldOpRealized_holds
  have hS : ∀ i, reflConj (g i) = g i ∧ fieldOp id longitudinal (g i) = 0 :=
    fun i => (mem_sig_iff _).1 (hg i)
  have hR : ∀ᵐ ξ ∂volume, ∀ i,
      conjVec ((g i : Space → CSpace) (-ξ)) = (g i : Space → CSpace) ξ := by
    rw [ae_all_iff]
    intro i
    have e0 := reflConj_ae h1 (g i)
    rw [(hS i).1] at e0
    filter_upwards [e0] with ξ e
    exact e.symm
  have hL : ∀ᵐ ξ ∂volume, ∀ i, longitudinal ξ ((g i : Space → CSpace) ξ) = 0 := by
    rw [ae_all_iff]
    intro i
    have e0 := longitudinal_ae h1 (g i)
    rw [(hS i).2] at e0
    filter_upwards [e0, Lp.coeFn_zero CSpace 2 (volume : Measure Space)] with ξ e z
    rw [← e, z, Pi.zero_apply]
  have hlimneg : ∀ᵐ ξ ∂volume,
      Tendsto (fun i => (g i : Space → CSpace) (-ξ)) atTop (𝓝 (G (-ξ))) :=
    (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae hlim
  rw [mem_sig_iff]
  constructor
  · apply Lp.ext
    filter_upwards [reflConj_ae h1 h, ae_comp_neg hh, hh, hR, hlim, hlimneg]
      with ξ e1 e2 e3 e4 e5 e6
    rw [e1, e2, e3]
    have t1 : Tendsto (fun i => conjVec ((g i : Space → CSpace) (-ξ))) atTop
        (𝓝 (conjVec (G (-ξ)))) :=
      (conjVec.continuous.tendsto _).comp e6
    simp only [e4] at t1
    exact tendsto_nhds_unique t1 e5
  · apply Lp.ext
    filter_upwards [longitudinal_ae h1 h, hh, hL, hlim,
      Lp.coeFn_zero CSpace 2 (volume : Measure Space)] with ξ e1 e2 e3 e4 z
    rw [e1, e2, z, Pi.zero_apply]
    have t1 : Tendsto (fun i => longitudinal ξ ((g i : Space → CSpace) ξ)) atTop
        (𝓝 (longitudinal ξ (G ξ))) :=
      ((longitudinal ξ).continuous.tendsto _).comp e4
    simp only [e3] at t1
    exact tendsto_nhds_unique t1 tendsto_const_nhds

end Internal.DerivClosedProof

open Internal.DerivClosedProof

theorem derivClosed_holds : DerivClosed := by
  intro n α x xs ys B hx hder hB
  obtain ⟨ns, -, hns⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (tendsto_coe_of_tendsto hx)).exists_seq_tendsto_ae
  have hall : ∀ᵐ ξ ∂volume, ∀ m, symX (ys m) ξ = monoSymbol α ξ • symX (xs m) ξ :=
    ae_all_iff.2 hder
  have hlim : ∀ᵐ ξ ∂volume, Tendsto (fun i => symX (ys (ns i)) ξ) atTop
      (𝓝 (monoSymbol α ξ • symX x ξ)) := by
    filter_upwards [hns, hall] with ξ e1 e2
    simp only [e2]
    exact e1.const_smul (monoSymbol α ξ)
  have hmeas : ∀ i, AEStronglyMeasurable (fun ξ => symX (ys (ns i)) ξ) volume :=
    fun i => Lp.aestronglyMeasurable _
  have hGm : AEStronglyMeasurable (fun ξ => monoSymbol α ξ • symX x ξ) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hle : eLpNorm (fun ξ => monoSymbol α ξ • symX x ξ) 2 volume ≤ ENNReal.ofReal B := by
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm hmeas _ hlim).trans ?_
    refine Filter.liminf_le_of_frequently_le (Frequently.of_forall fun i => ?_)
    show eLpNorm ((ys (ns i) : L2C) : Space → CSpace) 2 volume ≤ ENNReal.ofReal B
    rw [← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hB _)
  have hm : MemLp (fun ξ => monoSymbol α ξ • symX x ξ) 2 volume :=
    ⟨hGm, lt_of_le_of_lt hle ENNReal.ofReal_lt_top⟩
  have hsig : hm.toLp _ ∈ Sig :=
    mem_sig_of_ae_tendsto (fun i => (ys (ns i)).2) hlim hm.coeFn_toLp
  refine ⟨⟨hm.toLp _, hsig⟩, ?_, ?_⟩
  · show ∀ᵐ ξ ∂volume, ((hm.toLp _ : L2C) : Space → CSpace) ξ = monoSymbol α ξ • symX x ξ
    exact hm.coeFn_toLp
  · show ‖hm.toLp _‖ ≤ B
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal hB0 hle

end Breakdown.FarField
