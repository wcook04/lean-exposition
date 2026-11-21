import TorusEuler.TerminalBorelSeries
import TorusEuler.TerminalBoundaryLocalization
import TorusEuler.TerminalBoundaryJetGlue
import TorusEuler.TerminalExtensionPartition
import TorusEuler.TerminalPeriodicExtension

/-! Smooth extension through the right end of a closed time slab. -/

open Set Function
open scoped ContDiff

namespace TorusEuler

noncomputable section

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem exists_terminalSmoothExtensionAtZero {a : ℝ} (ha : a < 0)
    {O : Set E} (hO : IsOpen O) {f : ℝ × E → F} (hf : ContDiffOn ℝ ∞ f (Icc a 0 ×ˢ O)) :
    ∃ g : ℝ × E → F, ContDiffOn ℝ ∞ g (Ioi a ×ˢ O) ∧
      EqOn g f ((Icc a 0 ×ˢ O) ∩ (Ioi a ×ˢ O)) := by
  apply exists_contDiffOn_extension_of_local (isOpen_Ioi.prod hO)
  intro z hz
  by_cases hNeg : z.1 < 0
  · refine ⟨Ioo a 0 ×ˢ O, f, isOpen_Ioo.prod hO, ⟨⟨hz.1, hNeg⟩, hz.2⟩, ?_, ?_⟩
    · exact hf.mono (prod_mono (fun _ ht => ⟨ht.1.le, ht.2.le⟩) Subset.rfl)
    · intro w _
      rfl
  by_cases hPos : 0 < z.1
  · refine ⟨Ioi 0 ×ˢ O, fun _ => 0, isOpen_Ioi.prod hO, ⟨hPos, hz.2⟩,
      contDiff_const.contDiffOn, ?_⟩
    intro w hw
    exact (not_lt_of_ge hw.1.1.2 hw.2.1).elim
  have hz₀ : z.1 = 0 := le_antisymm (le_of_not_gt hPos) (le_of_not_gt hNeg)
  obtain ⟨V, hV, hzV, hVO, u, hu, hs, huEq⟩ := exists_terminalBoundaryLocalizedJets ha hO hf hz.2
  obtain ⟨G, hG, hGJet⟩ := exists_terminalBorelExtension u hu hs
  have hLeftSub : Icc a 0 ×ˢ V ⊆ Icc a 0 ×ˢ O := prod_mono Subset.rfl hVO
  have hLeft := hf.mono hLeftSub
  have hRight : ContDiffOn ℝ ∞ G (Ici 0 ×ˢ V) := hG.contDiffOn
  have hJets (n : ℕ) (x : E) (hx : x ∈ V) :
      iteratedFDerivWithin ℝ n f (Icc a 0 ×ˢ V) (0, x) (fun _ => (1, 0)) =
        iteratedFDerivWithin ℝ n G (Ici 0 ×ˢ V) (0, x) (fun _ => (1, 0)) := by
    have h0 : (0 : ℝ) ∈ Icc a 0 := ⟨ha.le, le_rfl⟩
    have hRestrict := iteratedFDerivWithin_subset hLeftSub
      ((uniqueDiffOn_Icc ha).prod hV.uniqueDiffOn) ((uniqueDiffOn_Icc ha).prod hO.uniqueDiffOn)
      (hf.of_le (by simp : (n : ℕ∞ω) ≤ ∞)) (show (0, x) ∈ Icc a 0 ×ˢ V from ⟨h0, hx⟩)
    have hSlice : ContDiff ℝ ∞ (fun t : ℝ => G (t, x)) :=
      hG.comp (contDiff_id.prodMk contDiff_const)
    have h0' : (0 : ℝ) ∈ Ici 0 := mem_Ici.mpr le_rfl
    have hScalar := iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici (0 : ℝ))
      (hSlice.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞)) h0'
    have hEval := iteratedDerivWithin_timeSlice hRight (uniqueDiffOn_Ici (0 : ℝ))
      hV.uniqueDiffOn n h0' hx
    rw [hRestrict, ← hEval, hScalar, hGJet n x]
    exact (huEq n x hx).symm
  refine ⟨Ioi a ×ˢ V, fun w => if w.1 ≤ 0 then f w else G w, isOpen_Ioi.prod hV,
    ⟨hz.1, hzV⟩, ?_, ?_⟩
  · exact contDiffOn_terminalPiecewise_of_timeJets ha hV hLeft hRight (fun x hx n => hJets n x hx)
  · intro w hw
    exact ite_eq_left hw.1.1.2

/-- A jointly smooth field on a closed time slab extends smoothly through
its right endpoint on the whole open spatial set of the slab. -/
theorem exists_terminalSmoothExtension {a T : ℝ} (ha : a < T)
    {O : Set E} (hO : IsOpen O) {f : ℝ × E → F} (hf : ContDiffOn ℝ ∞ f (Icc a T ×ˢ O)) :
    ∃ g : ℝ × E → F, ContDiffOn ℝ ∞ g (Ioi a ×ˢ O) ∧ EqOn g f (Icc a T ×ˢ O) := by
  let back (z : ℝ × E) : ℝ × E := (z.1 + T, z.2)
  let forward (z : ℝ × E) : ℝ × E := (z.1 - T, z.2)
  have hBack : ContDiff ℝ ∞ back := (contDiff_fst.add contDiff_const).prodMk contDiff_snd
  have hForward : ContDiff ℝ ∞ forward := (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
  have hf0 : ContDiffOn ℝ ∞ (f ∘ back) (Icc (a - T) 0 ×ˢ O) := by
    refine hf.comp hBack.contDiffOn ?_
    intro z hz
    exact ⟨⟨by linarith only [hz.1.1], by linarith only [hz.1.2]⟩, hz.2⟩
  obtain ⟨H, hH, hEq⟩ := exists_terminalSmoothExtensionAtZero (sub_neg.mpr ha) hO hf0
  have hMap : MapsTo forward (Ioi a ×ˢ O) (Ioi (a - T) ×ˢ O) := by
    intro z hz
    exact ⟨sub_lt_sub_right hz.1 T, hz.2⟩
  refine ⟨fun z => if a < z.1 then H (forward z) else f z, ?_, ?_⟩
  · exact (hH.comp hForward.contDiffOn hMap).congr (fun z hz => ite_eq_left hz.1)
  · intro z hz
    by_cases hza : a < z.1
    · simp only [ite_eq_left hza]
      have hMem : forward z ∈ (Icc (a - T) 0 ×ˢ O) ∩ (Ioi (a - T) ×ˢ O) :=
        ⟨⟨⟨sub_le_sub_right hz.1.1 T, sub_nonpos.mpr hz.1.2⟩, hz.2⟩, hMap ⟨hza, hz.2⟩⟩
      have hBackForward : back (forward z) = z := Prod.ext (sub_add_cancel _ _) rfl
      simpa only [Function.comp_apply, hBackForward] using hEq hMem
    · exact ite_eq_right hza

/-- Smooth extension in both time directions, retaining agreement at the
left endpoint of the original closed slab. -/
theorem exists_smoothExtensionOfClosedTimeSlab {a T : ℝ} (ha : a < T)
    {O : Set E} (hO : IsOpen O) {f : ℝ × E → F} (hf : ContDiffOn ℝ ∞ f (Icc a T ×ˢ O)) :
    ∃ g : ℝ × E → F, ContDiffOn ℝ ∞ g (univ ×ˢ O) ∧ EqOn g f (Icc a T ×ˢ O) := by
  obtain ⟨gR, hR, hREq⟩ := exists_terminalSmoothExtension ha hO hf
  let reflect (z : ℝ × E) : ℝ × E := (-z.1, z.2)
  have hReflect : ContDiff ℝ ∞ reflect := contDiff_fst.neg.prodMk contDiff_snd
  have hReflectSlab : MapsTo reflect (Icc (-T) (-a) ×ˢ O) (Icc a T ×ˢ O) := by
    intro z hz
    exact ⟨⟨le_neg_of_le_neg hz.1.2, neg_le_of_neg_le hz.1.1⟩, hz.2⟩
  obtain ⟨gL, hL, hLEq⟩ := exists_terminalSmoothExtension (neg_lt_neg ha) hO
    (hf.comp hReflect.contDiffOn hReflectSlab)
  have hReflectOpen : MapsTo reflect (Iio T ×ˢ O) (Ioi (-T) ×ˢ O) := by
    intro z hz
    exact ⟨mem_Ioi.mpr (neg_lt_neg (mem_Iio.mp hz.1)), hz.2⟩
  have hL' : ContDiffOn ℝ ∞ (gL ∘ reflect) (Iio T ×ˢ O) :=
    hL.comp hReflect.contDiffOn hReflectOpen
  have hLEq' : EqOn (gL ∘ reflect) f (Icc a T ×ˢ O) := by
    intro z hz
    have hz' : reflect z ∈ Icc (-T) (-a) ×ˢ O :=
      ⟨⟨neg_le_neg hz.1.2, neg_le_neg hz.1.1⟩, hz.2⟩
    have hRR : reflect (reflect z) = z := Prod.ext (neg_neg _) rfl
    simpa only [Function.comp_apply, hRR] using hLEq hz'
  have hLocal (z : ℝ × E) (hz : z ∈ univ ×ˢ O) :
      ∃ (W : Set (ℝ × E)) (g : ℝ × E → F),
        IsOpen W ∧ z ∈ W ∧ ContDiffOn ℝ ∞ g W ∧ EqOn g f ((Icc a T ×ˢ O) ∩ W) := by
    by_cases ht : z.1 < T
    · exact ⟨Iio T ×ˢ O, gL ∘ reflect, isOpen_Iio.prod hO, ⟨ht, hz.2⟩, hL',
        hLEq'.mono inter_subset_left⟩
    · exact ⟨Ioi a ×ˢ O, gR, isOpen_Ioi.prod hO, ⟨ha.trans_le (le_of_not_gt ht), hz.2⟩, hR,
        hREq.mono inter_subset_left⟩
  obtain ⟨g, hg, hgEq⟩ := exists_contDiffOn_extension_of_local (isOpen_univ.prod hO) hLocal
  exact ⟨g, hg, hgEq.mono (subset_inter Subset.rfl (prod_mono (subset_univ _) Subset.rfl))⟩

end

/-- A smooth lift of the torus velocity through the terminal slice on the
punctured torus, agreeing with the solution on its full physical slab. -/
def HasSmoothOffOriginExtension (T : ℝ) (u : Velocity) : Prop :=
  ∃ g : Velocity,
    ContDiffOn ℝ ∞ (Function.uncurry g) (univ ×ˢ offOrigin) ∧
    (∀ t, SpatiallyPeriodic (g t)) ∧
    EqOn (Function.uncurry g) (Function.uncurry u) (Ico 0 T ×ˢ offOrigin)

theorem IsEulerSolution.hasSmoothOffOriginExtension {T : ℝ} {u : Velocity} {p : Pressure}
    (hEuler : IsEulerSolution T u p)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ offOrigin)) :
    HasSmoothOffOriginExtension T u := by
  obtain ⟨g, hg, hAgree⟩ := exists_smoothExtensionOfClosedTimeSlab hEuler.time_pos isOpen_offOrigin hu
  obtain ⟨G, hG, hGEq, hPeriodic⟩ := exists_spatiallyPeriodic_contDiffOn_extension
    isOpen_univ hg (hAgree.mono (prod_mono Ico_subset_Icc_self Subset.rfl)) hEuler.periodic_velocity
  exact ⟨Function.curry G, hG, hPeriodic, hGEq⟩

end TorusEuler
