import Breakdown.Frac.StProfile
import Breakdown.Frac.RExports
import Breakdown.Frac.PSlice
import Breakdown.Frac.PFlow
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private theorem rotatingSlice_add_period (h5 : AxialRotationSpec) (a : ℝ) (U : Space → Space)
    (s P' : ℝ) :
    rotatingSlice a U (s + P') =
      pushForward (axialRotation (-(a * P'))) (rotatingSlice a U s) := by
  obtain ⟨-, -, hadd, hsymm, -, -⟩ := h5
  funext y
  simp only [rotatingSlice, pushForward]
  rw [hsymm, hsymm, hsymm, ← hadd, ← hadd]
  have e1 : -(a * P') + -(a * s) = -(a * (s + P')) := by ring
  have e2 : -(-(a * s)) + -(-(a * P')) = -(-(a * (s + P'))) := by ring
  rw [e1, e2]

theorem fracProfileOrbit_of (h1 : SelfSimilarWeak)
    (h2 : ∀ α : ℝ, 1 < α → α < 5 / 4 → Freq.FracMildOfWeak α) (h3 : ScaledFlowOfMild)
    (h4 : RotatingSliceContinuous) (h5 : AxialRotationSpec) : FracProfileOrbit := by
  intro α hα1 hα2 a U P hprof F hG hK hD P' hP'
  have hdec : ∀ s, IsDecayField (rotatingSlice a U s) := fun s =>
    (rotatingSliceDecay α hα1 hα2 a U P hprof s).1
  have hER : Freq.EmbedRot :=
    Freq.embedRot Freq.fieldOpRealized_holds Freq.rotation_holds Freq.embedMem_holds
      Freq.gradCompatible
  have hED : Freq.FracEmbedDilate α :=
    Freq.fracEmbedDilate α (by linarith) (Freq.fracDilationAlgebra_holds α hα1)
      (Freq.decayFieldScale α (by linarith))
  refine ⟨h4 α hα1 hα2 a U P hprof, ?_, hP', ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hprof.nonzero
    refine ⟨0, Freq.embedNeZero Freq.embedNormLinear_holds.1 _ (hdec 0)
      ⟨axialRotation (-(a * 0)) y, ?_⟩⟩
    simpa [rotatingSlice, pushForward] using hy
  · intro s
    show Freq.embedX (rotatingSlice a U (s + P')) =
      Freq.rotX (axialRotation (-(a * P'))) (Freq.embedX (rotatingSlice a U s))
    rw [rotatingSlice_add_period h5, hER _ _ (hdec s)]
  · intro s' s hss
    rcases eq_or_lt_of_le hss with heq | hlt
    · subst heq
      refine ⟨IntervalIntegrable.refl, ?_⟩
      simp [ScaledMildFramework.S, F.D_one, F.G_zero]
    · have hT0 : 0 < 1 - exp (-(s - s')) := by
        rw [sub_pos]
        exact Real.exp_lt_one_iff.mpr (by linarith)
      have hT1 : 1 - exp (-(s - s')) < 1 := by
        have := Real.exp_pos (-(s - s'))
        linarith
      have hw := h1 α hα1 hα2 a U P hprof s' _ hT0 hT1
      have hm := h2 α hα1 hα2 _ 0 _ hT0 hw
      have hm' : F.IsMildOnIcc (fun t => Freq.embedX (selfSimilarField α a U s' t)) 0
          (1 - exp (-(s - s'))) := by
        simp only [ScaledMildFramework.IsMildOnIcc, hG, hK]
        exact hm
      refine h3 Freq.X (dilExponent α) F (fun s => Freq.embedX (rotatingSlice a U s))
        (fun t => Freq.embedX (selfSimilarField α a U s' t)) s' s hlt hm' ?_
      intro r hr
      have hr1 : 0 < (1 - r)⁻¹ := by
        apply inv_pos.mpr
        linarith [hr.2]
      simp only [selfSimilarField, hD]
      exact (hED _ _ hr1 (hdec _)).symm

theorem fracProfileOrbit_of_weak (h1 : SelfSimilarWeak)
    (h2 : ∀ α : ℝ, 1 < α → α < 5 / 4 → Freq.FracMildOfWeak α) : FracProfileOrbit :=
  fracProfileOrbit_of h1 h2 scaledFlowOfMild rotatingSliceContinuous_holds axialRotationSpec

end Breakdown
