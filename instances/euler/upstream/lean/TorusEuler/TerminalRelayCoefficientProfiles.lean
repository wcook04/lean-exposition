import TorusEuler.TerminalCoefficientTimeNorms
import TorusEuler.TerminalWaveRelayTimeCoefficients
import TorusEuler.TerminalWaveRelayTimeGeometry
import TorusEuler.TerminalHierarchyRelayAssembly

/-! Exact periodic realizations of the normalized relay coefficients. -/

open Set
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)
local notation "slab" => Set.prod (Icc (0 : ℝ) T) (univ : Set Vec3)

section LabelSlices

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Phase independence and lattice twisting imply ordinary periodicity of
the phase-zero coefficient on each slab time. -/
private theorem spatiallyPeriodic_phaseZero_of_phaseIndependent
    (f : HierarchyTwistedProfile T k E) (hf : HierarchyPeriodicProfile.PhaseIndependent f.val.val)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    SpatiallyPeriodic (fun a => f.val.val.val (t,a,0)) := by
  intro n a
  have h₁ := hf (t, a + latticeVector n, (0 : ℝ)) ⟨ht, mem_univ _⟩
    ((0 : ℝ) + @inner ℝ Vec3 _ k (latticeVector n))
  exact h₁.symm.trans (twistedSlice f t a 0 n)

/-- A twisted label coefficient with no phase dependence is smooth on the
closed slab of times and labels. -/
private theorem contDiffOn_phaseZero (f : HierarchyTwistedProfile T k E) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => f.val.val.val (z.1,z.2,0))
      (Icc 0 T ×ˢ (univ : Set Vec3)) :=
  (HierarchySmoothProfile.smooth f.val.val).comp
    (contDiffOn_fst.prodMk (contDiffOn_snd.prodMk contDiffOn_const))
    (fun _ hz => ⟨hz.1, mem_univ _⟩)

end LabelSlices

namespace WaveRelayTimeCoefficients

/-- Evaluate a twisted coefficient at independent phase zero. -/
abbrev labelSlice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : HierarchyTwistedProfile T k E) : ℝ → Vec3 → E :=
  fun t a => f.val.val.val (t,a,0)

abbrev potentialLabel (κ : VP) (freq : ℝ) : ℝ → Vec3 → Vec3 →L[ℝ] Vec3 :=
  fun t a => hierarchyRelayPotentialCoefficient (freq⁻¹ • labelSlice κ t a)

abbrev potentialTimeLabel (M : MP) (κ : VP) (freq : ℝ) : ℝ → Vec3 → Vec3 →L[ℝ] Vec3 :=
  fun t a => hierarchyRelayTimeAmplitudeCoefficient (labelSlice M t a) (freq⁻¹ • labelSlice κ t a)

abbrev pressureAmplitudeLabel (M : MP) (κ : VP) (freq : ℝ) : ℝ → Vec3 → Vec3 →L[ℝ] ℝ :=
  fun t a => hierarchyRelayPressureAmplitudeCoefficient (labelSlice M t a) (freq⁻¹ • labelSlice κ t a)

abbrev pressureSourceLabel (κ : VP) (freq : ℝ) : ℝ → Vec3 → Vec3 →L[ℝ] ℝ :=
  fun t a => hierarchyRelayPressureSourceCoefficient (freq⁻¹ • labelSlice κ t a)

abbrev curlLabel (G : MP) (ell : ℝ) (i : Fin 3) : ℝ → Vec3 → Vec3 →L[ℝ] Vec3 :=
  fun t a => hierarchyRelayCurlRow ell (labelSlice G t a) i

abbrev materialLabel (G M : MP) (ell : ℝ) (i : Fin 3) : ℝ → Vec3 → Vec3 →L[ℝ] Vec3 :=
  fun t a => hierarchyRelayMaterialRow ell (labelSlice G t a) (labelSlice M t a) i

abbrev gradientLabel (G : MP) (ell : ℝ) (i : Fin 3) : ℝ → Vec3 → ℝ →L[ℝ] Vec3 :=
  fun t a => hierarchyRelayPressureRow ell (labelSlice G t a) i

/-- Joint time and label smoothness of the same coefficient formulas used
in the normalized primitive and relay. -/
structure LabelRegularity (G M : MP) (κ : VP) (ell freq : ℝ) : Prop where
  potential : ContDiffOn ℝ ∞ (Function.uncurry (potentialLabel κ freq)) slab
  potentialTime : ContDiffOn ℝ ∞ (Function.uncurry (potentialTimeLabel M κ freq)) slab
  pressureAmplitude : ContDiffOn ℝ ∞ (Function.uncurry (pressureAmplitudeLabel M κ freq)) slab
  pressureSource : ContDiffOn ℝ ∞ (Function.uncurry (pressureSourceLabel κ freq)) slab
  curl : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (curlLabel G ell i)) slab
  material : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (materialLabel G M ell i)) slab
  gradient : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (gradientLabel G ell i)) slab

/-- Separate amplitudes for coefficients inside and outside the phase
primitive. The outer amplitudes include the inverse label radius. -/
structure LabelMixedJetBounds (G M : MP) (κ : VP) (ell freq D Ainner Aouter : ℝ)
    (q p : ℕ) (Cinner Couter : ℕ → ℝ) : Prop where
  potential : TerminalMixedJetBound 0 T q p D Ainner Cinner (potentialLabel κ freq)
  potentialTime : TerminalMixedJetBound 0 T q p D Ainner Cinner (potentialTimeLabel M κ freq)
  pressureAmplitude : TerminalMixedJetBound 0 T q p D Ainner Cinner (pressureAmplitudeLabel M κ freq)
  pressureSource : TerminalMixedJetBound 0 T q p D Ainner Cinner (pressureSourceLabel κ freq)
  curl : ∀ i, TerminalMixedJetBound 0 T q p D Aouter Couter (curlLabel G ell i)
  material : ∀ i, TerminalMixedJetBound 0 T q p D Aouter Couter (materialLabel G M ell i)
  gradient : ∀ i, TerminalMixedJetBound 0 T q p D Aouter Couter (gradientLabel G ell i)

/-- Bundle the smooth periodic coefficient formulas into the twisted profile
space, retaining their exact values on the slab. -/
def ofLabelRegularity {G M : MP} {κ : VP} {ell freq : ℝ}
    (hG : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hM : HierarchyPeriodicProfile.PhaseIndependent M.val.val)
    (hκ : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hr : LabelRegularity G M κ ell freq) : WaveRelayTimeCoefficients G M κ ell freq := by
  have hGp (t : ℝ) (ht : t ∈ Icc 0 T) := spatiallyPeriodic_phaseZero_of_phaseIndependent G hG ht
  have hMp (t : ℝ) (ht : t ∈ Icc 0 T) := spatiallyPeriodic_phaseZero_of_phaseIndependent M hM ht
  have hκp (t : ℝ) (ht : t ∈ Icc 0 T) := spatiallyPeriodic_phaseZero_of_phaseIndependent κ hκ ht
  have hp (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (potentialLabel κ freq t) := by
    intro n a
    exact congrArg (fun v => hierarchyRelayPotentialCoefficient (freq⁻¹ • v)) (hκp t ht n a)
  have ht' (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (potentialTimeLabel M κ freq t) := by
    intro n a
    exact congrArg₂ (fun m v => hierarchyRelayTimeAmplitudeCoefficient m (freq⁻¹ • v))
      (hMp t ht n a) (hκp t ht n a)
  have hpa (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (pressureAmplitudeLabel M κ freq t) := by
    intro n a
    exact congrArg₂ (fun m v => hierarchyRelayPressureAmplitudeCoefficient m (freq⁻¹ • v))
      (hMp t ht n a) (hκp t ht n a)
  have hps (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (pressureSourceLabel κ freq t) := by
    intro n a
    exact congrArg (fun v => hierarchyRelayPressureSourceCoefficient (freq⁻¹ • v)) (hκp t ht n a)
  have hc (i : Fin 3) (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (curlLabel G ell i t) := by
    intro n a
    exact congrArg (fun g => hierarchyRelayCurlRow ell g i) (hGp t ht n a)
  have hm (i : Fin 3) (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (materialLabel G M ell i t) := by
    intro n a
    exact congrArg₂ (fun g m => hierarchyRelayMaterialRow ell g m i) (hGp t ht n a) (hMp t ht n a)
  have hg (i : Fin 3) (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (gradientLabel G ell i t) := by
    intro n a
    exact congrArg (fun g => hierarchyRelayPressureRow ell g i) (hGp t ht n a)
  exact
    { potential := ofLabelField k _ hr.potential hp
      potentialTime := ofLabelField k _ hr.potentialTime ht'
      pressureAmplitude := ofLabelField k _ hr.pressureAmplitude hpa
      pressureSource := ofLabelField k _ hr.pressureSource hps
      curl := fun i => ofLabelField k _ (hr.curl i) (hc i)
      material := fun i => ofLabelField k _ (hr.material i) (hm i)
      gradient := fun i => ofLabelField k _ (hr.gradient i) (hg i)
      potential_eq := fun _ ht _ _ => ofLabelField_eval k _ _ _ ⟨ht, mem_univ _⟩
      potentialTime_eq := fun _ ht _ _ => ofLabelField_eval k _ _ _ ⟨ht, mem_univ _⟩
      pressureAmplitude_eq := fun _ ht _ _ => ofLabelField_eval k _ _ _ ⟨ht, mem_univ _⟩
      pressureSource_eq := fun _ ht _ _ => ofLabelField_eval k _ _ _ ⟨ht, mem_univ _⟩
      curl_eq := fun _ _ ht _ _ => ofLabelField_eval k _ _ _ ⟨ht, mem_univ _⟩
      material_eq := fun _ _ ht _ _ => ofLabelField_eval k _ _ _ ⟨ht, mem_univ _⟩
      gradient_eq := fun _ _ ht _ _ => ofLabelField_eval k _ _ _ ⟨ht, mem_univ _⟩ }

/-- Turn the raw mixed jet bounds into the coefficient budget used by
the factorial completion and relay estimates. -/
theorem budget_of_labelMixedJetBounds {G M : MP} {κ : VP} {ell freq h D Ainner Aouter : ℝ}
    {q p : ℕ} {Cinner Couter : ℕ → ℝ}
    (R : WaveRelayTimeCoefficients G M κ ell freq)
    (hT : 0 < T) (hT₁ : T ≤ 1) (hEll : 0 ≤ ell) (hD : 0 ≤ D)
    (hInner : 0 ≤ Ainner) (hOuter : 0 ≤ Aouter) (hScale : ell * D ^ p ≤ 1)
    (hCinner : ∀ j, 0 ≤ Cinner j) (hCouter : ∀ j, 0 ≤ Couter j)
    (hb : LabelMixedJetBounds G M κ ell freq D Ainner Aouter q p Cinner Couter) (n : ℕ) :
    WaveRelayTimeCoefficientBudget R hT h q n
      (terminalLabelTimeSeminormCost Cinner q (n + 1) * Ainner +
        terminalLabelTimeSeminormCost Couter q n * Aouter) := by
  have hi : 0 ≤ terminalLabelTimeSeminormCost Cinner q (n + 1) * Ainner :=
    mul_nonneg (terminalLabelTimeSeminormCost_nonneg hCinner q _) hInner
  have ho : 0 ≤ terminalLabelTimeSeminormCost Couter q n * Aouter :=
    mul_nonneg (terminalLabelTimeSeminormCost_nonneg hCouter q _) hOuter
  have inner {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : HierarchyTwistedProfile T k E) (c : ℝ → Vec3 → E)
      (hv : ∀ t ∈ Icc 0 T, ∀ a s, f.val.val.val (t,a,s) = c t a)
      (hcb : TerminalMixedJetBound 0 T q p D Ainner Cinner c) :=
    (unweighted_timeJetSeminorm_le_of_labelMixedJetBound (h := h) hT hT₁ hEll hD hInner hScale
      f (fun x hx => hv x.1 hx.1 x.2.1 x.2.2) hcb hCinner (n + 1)).trans
      (le_add_of_nonneg_right ho)
  have outer {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : HierarchyTwistedProfile T k E) (c : ℝ → Vec3 → E)
      (hv : ∀ t ∈ Icc 0 T, ∀ a s, f.val.val.val (t,a,s) = c t a)
      (hcb : TerminalMixedJetBound 0 T q p D Aouter Couter c) :=
    (unweighted_timeJetSeminorm_le_of_labelMixedJetBound (h := h) hT hT₁ hEll hD hOuter hScale
      f (fun x hx => hv x.1 hx.1 x.2.1 x.2.2) hcb hCouter n).trans
      (le_add_of_nonneg_left hi)
  exact ⟨inner _ _ R.potential_eq hb.potential,
    inner _ _ R.potentialTime_eq hb.potentialTime,
    inner _ _ R.pressureAmplitude_eq hb.pressureAmplitude,
    inner _ _ R.pressureSource_eq hb.pressureSource,
    fun i => outer _ _ (R.curl_eq i) (hb.curl i),
    fun i => outer _ _ (R.material_eq i) (hb.material i),
    fun i => outer _ _ (R.gradient_eq i) (hb.gradient i)⟩

set_option maxHeartbeats 900000 in
/-- The parent strain, coframe, normalized covector and reciprocal determine
the seven normalized relay profiles and their factorial jet budgets. The
constant arrays are chosen before the parent data. -/
theorem exists_of_parentMixedJetBounds (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (q : ℕ) :
    ∃ Kinner Kouter : ℕ → ℝ, (∀ n, 0 ≤ Kinner n) ∧ (∀ n, 0 ≤ Kouter n) ∧
      ∀ {T : ℝ} {k : Vec3} {G M : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)}
        {κ : HierarchyTwistedProfile T k Vec3} {ell h freq D A : ℝ},
      ∀ hT : 0 < T, T ≤ 1 → 1 ≤ D → 1 ≤ A → 0 ≤ ell → ell * D ^ (16 : ℕ) ≤ 1 →
      HierarchyPeriodicProfile.PhaseIndependent G.val.val →
      HierarchyPeriodicProfile.PhaseIndependent M.val.val →
      HierarchyPeriodicProfile.PhaseIndependent κ.val.val →
      (∀ t ∈ Icc 0 T, ∀ a, freq⁻¹ • labelSlice κ t a ≠ 0) →
      TerminalMixedJetBound 0 T q 16 D A C (labelSlice G) →
      TerminalMixedJetBound 0 T q 16 D A C (labelSlice M) →
      TerminalMixedJetBound 0 T q 16 D A C (fun t a => freq⁻¹ • labelSlice κ t a) →
      TerminalMixedJetBound 0 T q 16 D A C (fun t a => (‖freq⁻¹ • labelSlice κ t a‖ ^ 2)⁻¹) →
      ∃ R : WaveRelayTimeCoefficients G M κ ell freq, ∀ n,
        WaveRelayTimeCoefficientBudget R hT h q n (Kinner n * A ^ 6 + Kouter n * (‖ell⁻¹‖ * A ^ 2)) := by
  obtain ⟨Ki, hKi, hInner⟩ := exists_terminalWaveRelayPotentialJetBounds C hC q
  obtain ⟨Ko, hKo, hOuter⟩ := exists_terminalWaveRelayGeometricJetBounds C hC q
  let Kinner (n : ℕ) := terminalLabelTimeSeminormCost Ki q (n + 1)
  let Kouter (n : ℕ) := terminalLabelTimeSeminormCost Ko q n
  refine ⟨Kinner, Kouter, fun n => terminalLabelTimeSeminormCost_nonneg hKi q (n + 1),
    fun n => terminalLabelTimeSeminormCost_nonneg hKo q n, ?_⟩
  intro T k G M κ ell h freq D A hT hT₁ hD hA hEll hScale hG hM hκ hκnz hGb hMb hκb hInv
  have hGreg : ContDiffOn ℝ ∞ (Function.uncurry (labelSlice G)) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    contDiffOn_phaseZero G
  have hMreg : ContDiffOn ℝ ∞ (Function.uncurry (labelSlice M)) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    contDiffOn_phaseZero M
  have hκreg : ContDiffOn ℝ ∞ (Function.uncurry (fun t a => freq⁻¹ • labelSlice κ t a))
      (Icc 0 T ×ˢ (univ : Set Vec3)) := by
    change ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => freq⁻¹ • κ.val.val.val (z.1,z.2,0)) _
    exact (contDiffOn_phaseZero κ).const_smul freq⁻¹
  obtain ⟨⟨hps, hpb⟩, ⟨hts, htb⟩, ⟨hpas, hpab⟩, ⟨hpss, hpsb⟩⟩ :=
    hInner hT hD hA hMreg hκreg hκnz hMb hκb hInv
  obtain ⟨hcs, hms, hgs⟩ := terminal_waveRelayGeometry_contDiffOn (ell := ell) hGreg hMreg
  obtain ⟨hcb, hmb, hgb⟩ := hOuter (ell := ell) hT hD hA hGreg hMreg hGb hMb
  let hr : LabelRegularity G M κ ell freq := ⟨hps, hts, hpas, hpss, hcs, hms, hgs⟩
  let hb : LabelMixedJetBounds G M κ ell freq D (A ^ 6) (‖ell⁻¹‖ * A ^ 2) q 16 Ki Ko :=
    ⟨hpb, htb, hpab, hpsb, hcb, hmb, hgb⟩
  let R := ofLabelRegularity hG hM hκ hr
  exact ⟨R, fun n => budget_of_labelMixedJetBounds R hT hT₁ hEll (zero_le_one.trans hD)
    (pow_nonneg (zero_le_one.trans hA) _) (mul_nonneg (norm_nonneg _) (sq_nonneg _))
    hScale hKi hKo hb n⟩

end WaveRelayTimeCoefficients

end

end TorusEuler.HierarchyTwistedProfile
