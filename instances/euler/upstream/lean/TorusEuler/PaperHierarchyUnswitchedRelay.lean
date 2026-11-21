import TorusEuler.PaperHierarchyRelay
import TorusEuler.PaperHierarchyActiveInverse
import TorusEuler.PaperHierarchyLeadingEquation
import TorusEuler.PaperGenericSwitchCompletion
import TorusEuler.LaterWaveHierarchyInput
import TorusEuler.TerminalSeeleyExtension

/-! The physical relay estimate for the unswitched leading wave on the active slab. -/

open Set Function
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T ℓ : ℝ} {k : Vec3}

private theorem envelopeWrapped_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ × Vec3 → E} {z : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hz : ContDiff ℝ ∞ z)
    (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) :
    ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint =>
      phaseTwistedPeriodizeCentered k (fun t a s => radialEnvelope ℓ a • (z s • u (t,a)))
        x.1 x.2.1 x.2.2) (hierarchyProfileSlab T) :=
  contDiffOn_phaseTwistedPeriodizeCentered_radialEnvelope hℓ hfit
    (((hz.comp contDiff_snd.snd).smul (hu.comp (contDiff_fst.prodMk contDiff_snd.fst))).contDiffOn)

private def envelopeWrapped {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ × Vec3 → E} {z : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hz : ContDiff ℝ ∞ z)
    (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) (hper : Periodic z 1) :
    HierarchyTwistedProfile T k E :=
  ofSmooth (fun x => phaseTwistedPeriodizeCentered k (fun t a s => radialEnvelope ℓ a • (z s • u (t,a)))
    x.1 x.2.1 x.2.2) (envelopeWrapped_smooth hu hz hℓ hfit)
    (fun x => by
      rcases x with ⟨t,a,s⟩
      simpa only [hierarchyPhasePeriod, Prod.mk_add_mk, add_zero] using
        (phaseTwistedPeriodizeCentered_phase_periodic (k := k)
          (f := fun t a s => radialEnvelope ℓ a • (z s • u (t,a)))
          (fun a q => by
            change radialEnvelope ℓ a • (z (q + 1) • u (t,a)) = _
            rw [hper q]) a s))
    (fun n x => by
      rw [add_hierarchyLatticeShift]
      exact phaseTwistedPeriodizeCentered_translate k _ x.1 x.2.1 x.2.2 n)

private theorem envelopeWrapped_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ × Vec3 → E} {z : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hz : ContDiff ℝ ∞ z)
    (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) (hper : Periodic z 1) {t : ℝ}
    (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (envelopeWrapped (T := T) (k := k) hu hz hℓ hfit hper).val.val.val (t,a,s) =
      phaseTwistedPeriodizeCentered k (fun t a s => radialEnvelope ℓ a • (z s • u (t,a))) t a s :=
  ofSmooth_eval _ _ _ ⟨ht, mem_univ _⟩

private theorem envelopeWrapped_phaseMean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {u : ℝ × Vec3 → E} {z : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hz : ContDiff ℝ ∞ z)
    (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) (hper : Periodic z 1) (hMean : phaseMean z = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) :
    phaseMean (fun s => (envelopeWrapped (T := T) (k := k) hu hz hℓ hfit hper).val.val.val (t,a,s)) = 0 := by
  simp_rw [envelopeWrapped_eval hu hz hℓ hfit hper ht]
  let b := centeredLabel a
  let c := -⟪k,a⟫_ℝ + ⟪k,b⟫_ℝ
  have he : (fun s => phaseTwistedPeriodizeCentered k
      (fun t a s => radialEnvelope ℓ a • (z s • u (t,a))) t a s) =
      fun s => radialEnvelope ℓ b • (z (s + c) • u (t,b)) := by
    funext s
    simp only [phaseTwistedPeriodizeCentered, b, c, sub_eq_add_neg, add_assoc]
  rw [he, phaseMean_const_smul, phaseMean, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_comp_add_right, zero_add]
  have hc := hper.intervalIntegral_add_eq c 0
  simp only [zero_add] at hc
  rw [add_comm (1 : ℝ) c, hc, ← phaseMean, hMean, zero_smul, smul_zero]

private theorem envelopeWrapped_average
    (hT : 0 < T) {u : ℝ × Vec3 → Vec3} {z : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hz : ContDiff ℝ ∞ z)
    (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) (hper : Periodic z 1) (hMean : phaseMean z = 0) :
    profilePhaseAverage hT (envelopeWrapped (T := T) (k := k) hu hz hℓ hfit hper) = 0 := by
  apply HierarchyTwistedProfile.ext
  rintro ⟨t,a,s⟩ hx
  change (HierarchySmoothProfile.profilePhaseAverage hT
    (envelopeWrapped (T := T) (k := k) hu hz hℓ hfit hper).val.val).val (t,a,s) = 0
  rw [HierarchySmoothProfile.profilePhaseAverage_apply hT _ hx]
  exact envelopeWrapped_phaseMean (k := k) hu hz hℓ hfit hper hMean hx.1 a

open LocalizedAmplitude

set_option maxHeartbeats 1500000 in
/-- The unswitched profiles admit smooth twisted representatives with their
exact active values. The phase mean is preserved by extending the
coefficients of the fixed wave and primitive. -/
theorem exists_unswitched_wrapped_representatives
    {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3}
    {center : ℝ → Vec3} {t₀ D C r h : ℝ} {w : SeedOn M κ center t₀ T ℓ D C}
    (reg : w.HierarchyRegularity r h) :
    ∃ (V : HierarchyTwistedProfile T k Vec3) (p : HierarchyTwistedProfile T k ℝ),
      profilePhaseAverage reg.end_pos V = 0 ∧
      (∀ t ∈ Icc 0 T, ∀ a, phaseMean (fun s => p.val.val.val (t,a,s)) = 0) ∧
      ∀ t ∈ Icc t₀ T, ∀ a s,
        V.val.val.val (t,a,s) = phaseTwistedPeriodizeCentered k (w.leading h) t a s ∧
        p.val.val.val (t,a,s) = phaseTwistedPeriodizeCentered k (w.leadingPressure h) t a s := by
  let b (z : ℝ × Vec3) := -wavePressureCoefficient 1 (κ z.1 z.2) (w.amplitude z.1 z.2) (M z.1 z.2)
  have hb : ContDiffOn ℝ ∞ b (Icc t₀ T ×ˢ (univ : Set Vec3)) := by
    have hb₀ := (contDiffOn_const (c := (2 : ℝ))).mul
      (reg.covector_smooth.inner ℝ (reg.strain_smooth.clm_apply reg.amplitude_smooth))
    have hn (z : ℝ × Vec3) (hz : z ∈ Icc t₀ T ×ˢ (univ : Set Vec3)) : ‖κ z.1 z.2‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr (reg.covector_nonzero z.1 hz.1 z.2))
    have hb₁ := (hb₀.div (ContDiffOn.norm_sq ℝ reg.covector_smooth) hn).neg
    simpa only [b, wavePressureCoefficient, mul_one, Function.uncurry, Pi.div_apply] using hb₁
  obtain ⟨U, hU, hUeq⟩ := exists_smoothExtensionOfClosedTimeSlab reg.start_lt_end isOpen_univ reg.amplitude_smooth
  obtain ⟨Q, hQ, hQeq⟩ := exists_smoothExtensionOfClosedTimeSlab reg.start_lt_end isOpen_univ hb
  have hUs : ContDiff ℝ ∞ U := contDiffOn_univ.mp (by simpa only [univ_prod_univ] using hU)
  have hQs : ContDiff ℝ ∞ Q := contDiffOn_univ.mp (by simpa only [univ_prod_univ] using hQ)
  have hv := contDiff_waveProfile reg.phase_pos reg.phase_le_one
  have hq := contDiff_wavePressurePrimitive reg.phase_pos reg.phase_le_one
  have hvper := periodic_waveProfile reg.phase_pos reg.phase_le_one
  have hqper := periodic_wavePressurePrimitive reg.phase_pos reg.phase_le_one
  let V : HierarchyTwistedProfile T k Vec3 := envelopeWrapped hUs hv reg.envelope_pos reg.envelope_fits hvper
  let p : HierarchyTwistedProfile T k ℝ := envelopeWrapped hQs hq reg.envelope_pos reg.envelope_fits hqper
  refine ⟨V, p, envelopeWrapped_average reg.end_pos hUs hv reg.envelope_pos reg.envelope_fits hvper
    (phaseMean_waveProfile reg.phase_pos reg.phase_le_one), ?_, ?_⟩
  · intro t ht a
    exact envelopeWrapped_phaseMean hQs hq reg.envelope_pos reg.envelope_fits hqper
      (phaseMean_wavePressurePrimitive reg.phase_pos reg.phase_le_one) ht a
  · intro t ht a s
    have hFull : t ∈ Icc 0 T := Icc_subset_Icc_left reg.nonneg_start ht
    constructor
    · rw [show V.val.val.val (t,a,s) = _ from
        envelopeWrapped_eval hUs hv reg.envelope_pos reg.envelope_fits hvper hFull a s]
      simp only [phaseTwistedPeriodizeCentered]
      rw [hUeq (show (t,centeredLabel a) ∈ Icc t₀ T ×ˢ (univ : Set Vec3) from ⟨ht,mem_univ _⟩)]
      simp only [SeedOn.leading, Function.uncurry_apply_pair, smul_smul]
    · rw [show p.val.val.val (t,a,s) = _ from
        envelopeWrapped_eval hQs hq reg.envelope_pos reg.envelope_fits hqper hFull a s]
      simp only [phaseTwistedPeriodizeCentered]
      rw [hQeq (show (t,centeredLabel a) ∈ Icc t₀ T ×ˢ (univ : Set Vec3) from ⟨ht,mem_univ _⟩)]
      simp only [b, SeedOn.leadingPressure, wavePressureCoefficient, mul_one, smul_eq_mul, div_eq_mul_inv]
      ring

private theorem wrapped_eq_on_centeredCell_of_radius {E : Type*} [Zero E]
    {f : ℝ → Vec3 → ℝ → E} {t : ℝ} {a : Vec3}
    (ha : a ∈ centeredCell) (s : ℝ) (hfit : 2 * ℓ < 1 / 2)
    (hf : ∀ b, 2 * ℓ ≤ ‖b‖ → ∀ q, f t b q = 0) :
    phaseTwistedPeriodizeCentered k f t a s = f t a s := by
  refine phaseTwistedPeriodizeCentered_eq_on_centeredCell (sub_pos.mpr hfit) ?_ ha s
  rintro b ⟨i, hi⟩ q
  have hb : |b i| ≤ ‖b‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le b i
  exact hf b (by linarith) q

variable {U : Velocity} {X : ℝ → Velocity} {hT : 0 < T}

local notation "J" => Icc 0 T
local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ

set_option maxHeartbeats 3500000 in
private theorem active_unswitched_conditions
    (d : ParentGeometry hT U X k) {center : ℝ → Vec3} {t₀ D C r h : ℝ}
    {w : SeedOn (fun t a => fderiv ℝ (U t) (X 0 t a))
      (fun t a => labelWaveVector X 0 a k t) center t₀ T ℓ D C} (reg : w.HierarchyRegularity r h)
    (V : VP) (p : SP)
    (hEval : ∀ t ∈ Icc t₀ T, ∀ a s,
      V.val.val.val (t,a,s) = phaseTwistedPeriodizeCentered k (w.leading h) t a s ∧
      p.val.val.val (t,a,s) = phaseTwistedPeriodizeCentered k (w.leadingPressure h) t a s) :
    let A := twistedHierarchyOperators hT d.inverse d.strain d.covector
    (∀ t ∈ Icc t₀ T, ∀ a s, ⟪d.covector.val.val.val (t,a,0), V.val.val.val (t,a,s)⟫_ℝ = 0) ∧
    ∀ t ∈ Icc t₀ T, ∀ a s, (A.material V + A.phaseGrad p).val.val.val (t,a,s) = 0 := by
  intro A
  let R := A.material V + A.phaseGrad p
  let I := Icc t₀ T
  have hI : I ⊆ J := Icc_subset_Icc_left reg.nonneg_start
  have hV (t : ℝ) (ht : t ∈ I) (a : Vec3) (ha : a ∈ centeredCell) (s : ℝ) :
      V.val.val.val (t,a,s) = w.leading h t a s := by
    rw [(hEval t ht a s).1]
    apply wrapped_eq_on_centeredCell_of_radius ha s reg.envelope_fits
    intro b hb q
    simp only [SeedOn.leading, radialEnvelope_eq_zero reg.envelope_pos hb, zero_mul, zero_smul]
  have hp (t : ℝ) (ht : t ∈ I) (a : Vec3) (ha : a ∈ centeredCell) (s : ℝ) :
      p.val.val.val (t,a,s) = w.leadingPressure h t a s := by
    rw [(hEval t ht a s).2]
    apply wrapped_eq_on_centeredCell_of_radius ha s reg.envelope_fits
    intro b hb q
    simp only [SeedOn.leadingPressure, wavePressureCoefficient, radialEnvelope_eq_zero reg.envelope_pos hb,
      mul_zero, zero_mul, zero_div, neg_zero]
  have hCell (t : ℝ) (ht : t ∈ I) (a : Vec3) (ha : a ∈ centeredCell) (s : ℝ) :
      ⟪d.covector.val.val.val (t,a,s), V.val.val.val (t,a,s)⟫_ℝ = 0 ∧ R.val.val.val (t,a,s) = 0 := by
    have hz : (t,a,s) ∈ hierarchyProfileSlab T := ⟨hI ht, mem_univ _⟩
    constructor
    · rw [d.covector_value _ hz, hV t ht a ha s]
      exact (w.paper_hierarchy_leading_homogeneous reg.start_lt_end reg.phase_pos reg.phase_le_one ht a s).2.1
    · have hQ : (fun q => p.val.val.val (t,a,q)) = w.leadingPressure h t a := funext (hp t ht a ha)
      have hv₀ := (HierarchySmoothProfile.hasDerivWithinAt_profileTime V.val.val (hI ht) a s).mono hI
      have hv := hv₀.derivWithin (uniqueDiffOn_Icc reg.start_lt_end t ht)
      have hVFun : EqOn (fun u => V.val.val.val (u,a,s)) (fun u => w.leading h u a s) I :=
        fun u hu => hV u hu a ha s
      rw [derivWithin_congr hVFun (hVFun ht)] at hv
      have hp' := (HierarchySmoothProfile.hasDerivAt_profilePhase p.val.val (hI ht) a s).deriv
      rw [hQ] at hp'
      let ops := HierarchySmoothProfile.hierarchyConcreteOperators hT d.inverse.val.val d.strain.val.val
        d.covector.val.val
      change (ops.material V.val.val).val (t,a,s) +
        (HierarchySmoothProfile.phaseGradient hT d.covector.val.val p.val.val).val (t,a,s) = 0
      rw [HierarchySmoothProfile.hierarchyConcreteOperators_material_apply hT _ _ _ _ hz,
        HierarchySmoothProfile.phaseGradient_apply hT _ _ hz, ← hv, ← hp',
        d.covector_value _ hz, d.strain_value _ hz, hV t ht a ha s]
      exact (w.paper_hierarchy_leading_homogeneous reg.start_lt_end reg.phase_pos reg.phase_le_one ht a s).1
  have hAll (t : ℝ) (ht : t ∈ I) (a : Vec3) (s : ℝ) :
      ⟪d.covector.val.val.val (t,a,s), V.val.val.val (t,a,s)⟫_ℝ = 0 ∧ R.val.val.val (t,a,s) = 0 := by
    obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell a
    have hShift (f : VP) : f.val.val.val (t,a,s) =
        f.val.val.val (t,a - latticeVector n,s - ⟪k,latticeVector n⟫_ℝ) := by
      simpa only [sub_add_cancel] using
        twistedSlice f t (a - latticeVector n) (s - ⟪k,latticeVector n⟫_ℝ) n
    rw [hShift d.covector, hShift V, hShift R]
    exact hCell t ht _ hn _
  refine ⟨fun t ht a s => ?_, fun t ht a s => (hAll t ht a s).2⟩
  have hc := d.oscillation.covector_independent (t,a,0) ⟨hI ht, mem_univ _⟩ s
  change d.covector.val.val.val (t,a,s) = d.covector.val.val.val (t,a,0) at hc
  rw [← hc]
  exact (hAll t ht a s).1

private theorem amplitudeSeminorm_eq_raw
    (V : VP) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T)
    {γ : ℝ → ℝ} (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (f : ℝ → Vec3 × ℝ → Vec3)
    (hEval : ∀ t ∈ Icc t₀ T, ∀ x, V.val.val.val (t,x) = f t x) (n : ℕ) :
    amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos V =
      paperHierarchyActiveVelocityNorm t₀ T ℓ h n γ f := by
  rw [amplitudeSeminorm_apply, paperHierarchyActiveVelocityNorm]
  congr 1
  funext t x
  change (γ t)⁻¹ • V.val.val.val (↑t,x) = (γ t)⁻¹ • f t x
  rw [hEval t t.property x]

set_option maxHeartbeats 3900000 in
/-- The homogeneous case of Lemma 5.5 for the actual unswitched leading
wave. Its representatives and curl have the displayed raw values throughout
the active slab, where the leading phase momentum vanishes. -/
theorem ParentGeometry.paper_hierarchy_unswitched_relay (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T t₀ D freq Cseed r h : ℝ}
        {k : Vec3} {hT : 0 < T} {center : ℝ → Vec3} (d : ParentGeometry hT U X k) (a : ℕ),
        16 ≤ a → T ≤ 1 → 1 ≤ D →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (X 0 t) x‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (X t 0) (X 0 t x)‖ ≤ D) →
        (∀ n j, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
          ‖iteratedFDeriv ℝ j (U t) x‖ ≤ R n * D ^ j) →
        (hf : 0 < freq) → ‖labelWaveVector X 0 0 k t₀‖ = freq →
        let ℓ := (D ^ a)⁻¹
        ∀ (w : SeedOn (fun t a => fderiv ℝ (U t) (X 0 t a))
          (fun t a => labelWaveVector X 0 a k t) center t₀ T ℓ D Cseed) (_reg : w.HierarchyRegularity r h)
          (γ : ℝ → ℝ) (_hγ : ContinuousOn γ (Icc t₀ T)) (_hpos : ∀ t ∈ Icc t₀ T, 0 < γ t),
        let A := twistedHierarchyOperators hT d.inverse d.strain d.covector
        let curl := complete hT d.inverse d.covector d.oscillation.covector_independent
          d.oscillation.covector_ne_zero
        ∃ (V : HierarchyTwistedProfile T k Vec3) (p : HierarchyTwistedProfile T k ℝ),
          (∀ t ∈ Icc t₀ T, ∀ x s,
            V.val.val.val (t,x,s) = phaseTwistedPeriodizeCentered k (w.leading h) t x s ∧
            p.val.val.val (t,x,s) = phaseTwistedPeriodizeCentered k (w.leadingPressure h) t x s ∧
            (curl V).val.val.val (t,x,s) = w.wrappedUnswitchedCompletion d.inverse (h := h) t x s ∧
            (A.material V + A.phaseGrad p).val.val.val (t,x,s) = 0) ∧
          let v (t : ℝ) (x : Vec3 × ℝ) := phaseTwistedPeriodizeCentered k (w.leading h) t x.1 x.2
          let q (t : ℝ) (x : Vec3 × ℝ) := phaseTwistedPeriodizeCentered k (w.leadingPressure h) t x.1 x.2
          let c (t : ℝ) (x : Vec3 × ℝ) := w.wrappedUnswitchedCompletion d.inverse (h := h) t x.1 x.2
          let relay (t : ℝ) (x : Vec3 × ℝ) :=
            derivWithin (fun u => c u x) (Icc t₀ T) t + fderiv ℝ (U t) (X 0 t x.1) (c t x) +
              (d.inverse.val.val.val (t,x)).adjoint (gradient (fun b => q t (b,x.2)) x.1)
          ∀ n : ℕ,
            let W := fun j => paperHierarchyActiveVelocityNorm t₀ T ℓ h j γ
            let K := C n * D ^ (2 * (15 + a)) * freq⁻¹
            W n c ≤ K * W (n + 1) v ∧ W n relay ≤ K * W (n + 1) v := by
  obtain ⟨C,hC,hRelay⟩ := paper_hierarchy_relay R hR
  refine ⟨C,hC,?_⟩
  intro U X T t₀ D freq Cseed r h k hT center d a ha hTime hD hX hU hper hF hG hJets hf hfreq
    ℓ w reg γ hγ hpos A curl
  obtain ⟨V,p,hVmean,hpMean,hEval⟩ := exists_unswitched_wrapped_representatives (k := k) reg
  obtain ⟨hTrans,hEq⟩ := active_unswitched_conditions (ℓ := ℓ) (t₀ := t₀) (D := D)
    (C := Cseed) (r := r) (h := h) (w := w) d reg V p hEval
  have hCeq (t : ℝ) (ht : t ∈ Icc t₀ T) (x : Vec3) (s : ℝ) :
      (curl V).val.val.val (t,x,s) = w.wrappedUnswitchedCompletion d.inverse (h := h) t x s := by
    have hc := complete_smul_wrapped_eval hT d.inverse d.covector V
      d.oscillation.covector_independent d.oscillation.covector_ne_zero
      (c := fun _ => 1) (κ := fun u b => labelWaveVector X 0 b k u) (raw := w.leading h)
      d.covector_value hVmean (Icc_subset_Icc_left reg.nonneg_start ht)
      (fun b q => ((hEval t ht b q).1).trans (one_smul ℝ _).symm) x s
    simpa only [one_smul, LocalizedAmplitude.SeedOn.wrappedUnswitchedCompletion] using hc
  refine ⟨V,p,fun t ht x s => ⟨(hEval t ht x s).1, (hEval t ht x s).2, hCeq t ht x s, hEq t ht x s⟩,?_⟩
  intro v q c relay n W K
  have hI : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc_left reg.nonneg_start
  have hVeq (t : ℝ) (ht : t ∈ Icc t₀ T) (x : Vec3 × ℝ) :
      V.val.val.val (t,x) = v t x := (hEval t ht x.1 x.2).1
  have hCurl (t : ℝ) (ht : t ∈ Icc t₀ T) (x : Vec3 × ℝ) :
      (curl V).val.val.val (t,x) = c t x := hCeq t ht x.1 x.2
  have hRe (t : ℝ) (ht : t ∈ Icc t₀ T) (x : Vec3 × ℝ) :
      (A.material (curl V) + A.labelGrad p).val.val.val (t,x) = relay t x := by
    have hx : (t,x) ∈ hierarchyProfileSlab T := ⟨hI ht,mem_univ _⟩
    have hTime := (HierarchySmoothProfile.hasDerivWithinAt_profileTime
      (curl V).val.val (hI ht) x.1 x.2).mono hI
    have hDerivative := hTime.derivWithin (uniqueDiffOn_Icc reg.start_lt_end t ht)
    have hc : EqOn (fun u => (curl V).val.val.val (u,x)) (fun u => c u x) (Icc t₀ T) :=
      fun u hu => hCurl u hu x
    rw [derivWithin_congr hc (hc ht)] at hDerivative
    have hPressure : (fun b => p.val.val.val (t,b,x.2)) = fun b => q t (b,x.2) :=
      funext fun b => (hEval t ht b x.2).2
    let ops := HierarchySmoothProfile.hierarchyConcreteOperators hT d.inverse.val.val d.strain.val.val
      d.covector.val.val
    change (ops.material (curl V).val.val).val (t,x) +
      (HierarchySmoothProfile.labelGradient hT d.inverse.val.val p.val.val).val (t,x) = _
    rw [HierarchySmoothProfile.hierarchyConcreteOperators_material_apply hT _ _ _ _ hx,
      HierarchySmoothProfile.labelGradient_eq_adjoint_gradient hT _ _ (hI ht) x.1 x.2,
      ← hDerivative, d.strain_value _ hx, hCurl t ht x, hPressure]
  obtain ⟨hc,hr⟩ := hRelay (h := h) d a ha hTime hD hX hU hper hF hG hJets hf
    reg.nonneg_start reg.start_lt_end hfreq γ hγ hpos n V hVmean hTrans
  have hb := hr 0 p (map_zero _) (fun t ht x => hpMean t (hI ht) x)
    (fun t ht x s => by simpa using hEq t ht x s)
  have hVnorm := amplitudeSeminorm_eq_raw (hT := hT) (ℓ := ℓ) (h := h) V reg.nonneg_start reg.start_lt_end.le
    hγ hpos v hVeq (n + 1)
  have hCnorm := amplitudeSeminorm_eq_raw (hT := hT) (ℓ := ℓ) (h := h) (curl V)
    reg.nonneg_start reg.start_lt_end.le hγ hpos c hCurl n
  have hRnorm := amplitudeSeminorm_eq_raw (hT := hT) (ℓ := ℓ) (h := h) (A.material (curl V) + A.labelGrad p)
    reg.nonneg_start reg.start_lt_end.le hγ hpos relay hRe n
  change paperHierarchyActiveVelocityNorm t₀ T ℓ h n γ c ≤
      _ * paperHierarchyActiveVelocityNorm t₀ T ℓ h (n + 1) γ v ∧
    paperHierarchyActiveVelocityNorm t₀ T ℓ h n γ relay ≤ _ * paperHierarchyActiveVelocityNorm t₀ T ℓ h (n + 1) γ v
  rw [← hVnorm, ← hCnorm, ← hRnorm]
  exact ⟨hc, by simpa only [map_zero, add_zero] using hb⟩


end
end TorusEuler.HierarchyTwistedProfile
