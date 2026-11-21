import TorusEuler.Paper.S34A.Statements
import TorusEuler.LabelFlowGeometry
import TorusEuler.LocalizedSeedRegularity

/-! Conditional proof of **Lemma 4.1** of the latest manuscript (package S34A). -/

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

/-- Proof of **Lemma 4.1** (`cc:uf:mean:hardy`, sections/06b_mean_inverse.tex:104–113),
following the TeX proof at sections/06b_mean_inverse.tex:114–125 and the identities
before it. Fix the label `a` and work with the time functions `F = D_aX(·,a)`,
`M = (∇u)∘X(·,a)` and `M_t`.

* The flow identity `∂_t D_aX = M D_aX` of (4.2) (sections/06b_mean_inverse.tex:19–22) is
  `IsLabelFlowOn.labelDerivative_evolves`; it gives (4.4) `ξ_t = Mξ + D_aX z_t`.
* `M` is smooth in time along the flow (`IsLabelFlowOn.contDiffOn_materialGradient`), so
  `M_t` exists within `[0,T]` and is continuous.
* With these, the row's own content `paper_mean_hardy` carries the TeX argument: the
  Poincaré inequality (4.5) for `ξ` and `T ≤ 1` give `∫H^#ξ·ξ ≤ ∫|ξ|² ≤ ½∫|ξ_t|²` from
  `H^# ≤ Id`, and the Jacobi identity (4.7) turns this into (4.8).

The lemma cites no numbered result, so the proof has no hypotheses. -/
theorem Proof.lemma_4_1 : Statement.lemma_4_1 := by
  intro T U X hP hH a v hv
  have hT := hP.time_pos
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hU2 : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hP.smooth.of_le (by simp)
  have hMsm := hP.flow.contDiffOn_materialGradient hT hP.smooth hP.periodic
  have hMtime : ContDiffOn ℝ ∞ (fun r => meanGradient U X r a) (Icc 0 T) :=
    hMsm.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hr => ⟨hr, mem_univ a⟩)
  exact paper_mean_hardy (E := Vec3) hT hP.time_le_one
    (F := fun t => meanDeformation X t a) (M := fun t => meanGradient U X t a)
    (Mt := fun t => meanGradientRate T U X t a)
    (fun t ht => (hP.flow.labelDerivative_evolves hT hU2 hP.periodic h0 a).2 t ht)
    (fun t ht => ((hMtime.differentiableOn (by simp) t ht).hasDerivWithinAt))
    (hMtime.continuousOn_derivWithin (uniqueDiffOn_Icc hT) (by simp))
    (fun t ht x => hH t ht a x) v hv

end TorusEuler.Paper
