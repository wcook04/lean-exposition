import TorusEuler.EndpointMeanFubini
import TorusEuler.EndpointSpaceCompatibility
import TorusEuler.EndpointSpaceOperator
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-! The time-independent part of the projected weak endpoint equation, as in (A.9). -/

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace TorusEuler

local notation "timeMeasure" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "A" => UnitAddTorus (Fin 3)
local notation "H" => Lp Vec3 2 unitTorusMeasure
local notation "Y" => endpointSpatialSolenoidal

/-- Spatial Leray projection onto the closed weak divergence constraint. -/
noncomputable def endpointWeakSpatialProjection : H →L[ℝ] Y :=
  letI : CompleteSpace Y := isClosed_endpointSpatialSolenoidal.completeSpace_coe
  endpointSpatialSolenoidal.orthogonalProjectionOnto

private theorem inner_endpointWeakSpatialProjection (r : H) (y : Y) :
    ⟪endpointWeakSpatialProjection r, y⟫_ℝ = ⟪r, (y : H)⟫_ℝ := by
  let : CompleteSpace Y := isClosed_endpointSpatialSolenoidal.completeSpace_coe
  exact endpointSpatialSolenoidal.inner_orthogonalProjectionOnto_eq_of_mem_right y r

private theorem timeMeasure_real_univ_weak {T : ℝ} (hT : 0 ≤ T) :
    (timeMeasure T).real univ = T := by
  rw [measureReal_def, Measure.restrict_apply_univ, ← measureReal_def, Real.volume_real_Ioc_of_le hT,
    sub_zero]

private theorem memLp_endpointSeparatedTest {T : ℝ} {η : ℝ → ℝ}
    (hη : MemLp η ⊤ (timeMeasure T)) (y : H) :
    MemLp (fun q : ℝ × A => η q.1 • y q.2) 2 (endpointTorusMeasure T) :=
  ((Lp.memLp y).comp_snd (timeMeasure T)).smul (hη.comp_fst unitTorusMeasure)

private theorem mem_endpointCenteredSeparatedTest {T : ℝ} {η : ℝ → ℝ}
    (hη : MemLp η ⊤ (timeMeasure T)) (hzero : (∫ t, η t ∂timeMeasure T) = 0) (y : Y) :
    (memLp_endpointSeparatedTest hη (y : H)).toLp (fun q => η q.1 • (y : H) q.2)
      ∈ endpointTorusSpace T := by
  let hmem := memLp_endpointSeparatedTest hη (y : H)
  have hrep := hmem.coeFn_toLp
  apply (mem_endpointTorusSpace_iff_slices T _).mpr
  constructor
  · filter_upwards [ae_endpointTimeSlice_congr hrep] with a ha
    change (∫ t, hmem.toLp _ (t, a) ∂timeMeasure T) = 0
    rw [integral_congr_ae ha, integral_smul_const, hzero, zero_smul]
  · intro p
    filter_upwards [Measure.ae_ae_of_ae_prod hrep] with t ht
    change (∫ a, ⟪endpointPotentialGradient p a, hmem.toLp _ (t, a)⟫_ℝ
      ∂unitTorusMeasure) = 0
    have heq : (fun a => ⟪endpointPotentialGradient p a, hmem.toLp _ (t, a)⟫_ℝ)
        =ᵐ[unitTorusMeasure] fun a => ⟪endpointPotentialGradient p a, η t • (y : H) a⟫_ℝ :=
      ht.mono fun a ha => congrArg (fun z : Vec3 => ⟪endpointPotentialGradient p a, z⟫_ℝ) ha
    rw [integral_congr_ae heq]
    simp only [real_inner_smul_right, integral_const_mul,
      (mem_endpointSpatialSolenoidal (y : H)).mp y.property p, mul_zero]

private theorem integrable_endpointInner_snd {T : ℝ} (r : EndpointTorusL2 T) (y : H) :
    Integrable (fun q : ℝ × A => ⟪r q, y q.2⟫_ℝ) (endpointTorusMeasure T) := by
  have hy := (Lp.memLp y).comp_snd (timeMeasure T)
  exact (L2.integrable_inner r (hy.toLp _)).congr
    (hy.coeFn_toLp.mono fun q hq => congrArg (fun z : Vec3 => ⟪r q, z⟫_ℝ) hq)

private theorem integral_pair_endpointTimeIntegral {T : ℝ} (hT : 0 ≤ T)
    (r : EndpointTorusL2 T) (y : H) :
    (∫ t, (∫ a, ⟪r (t, a), y a⟫_ℝ ∂unitTorusMeasure) ∂timeMeasure T) =
      ⟪endpointTorusTimeIntegral hT r, y⟫_ℝ := by
  have hpair := integrable_endpointInner_snd r y
  rw [← integral_prod _ hpair, integral_prod_symm _ hpair, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(Lp.memLp r).integrable one_le_two |>.prod_left_ae,
    endpointTimeIntegral_apply_ae hT r] with a ha hmean
  change (∫ t, ⟪r (t, a), y a⟫_ℝ ∂timeMeasure T) = ⟪endpointTorusTimeIntegral hT r a, y a⟫_ℝ
  rw [show endpointTorusTimeIntegral hT r a = _ from hmean]
  calc
    (∫ t, ⟪r (t, a), y a⟫_ℝ ∂timeMeasure T) =
        ∫ t, ⟪y a, r (t, a)⟫_ℝ ∂timeMeasure T :=
      integral_congr_ae (ae_of_all _ fun _ => real_inner_comm _ _)
    _ = ⟪y a, ∫ t, r (t, a) ∂timeMeasure T⟫_ℝ := integral_inner (𝕜 := ℝ) ha (y a)
    _ = _ := real_inner_comm _ _

/-- Testing the weak time integral against a spatial field commutes with taking the
spatial slice. The formula uses the representative-independent product integral. -/
theorem integral_inner_endpointSpatialSlice {T : ℝ} (hT : 0 ≤ T)
    (v : EndpointTorusL2 T) (y : H) :
    (∫ t, ⟪endpointSpatialSlice v t, y⟫_ℝ ∂timeMeasure T) =
      ⟪endpointTorusTimeIntegral hT v, y⟫_ℝ := by
  calc
    _ = ∫ t, (∫ a, ⟪v (t, a), y a⟫_ℝ ∂unitTorusMeasure) ∂timeMeasure T := by
      apply integral_congr_ae
      filter_upwards [endpointSpatialSlice_apply_ae v] with t ht
      rw [L2.inner_def]
      exact integral_congr_ae (ht.mono fun a ha => congrArg (fun z : Vec3 => ⟪z, y a⟫_ℝ) ha)
    _ = _ := integral_pair_endpointTimeIntegral hT v y

private theorem ae_pair_endpointWeakResidual_eq_mean {T : ℝ} (hT : 0 < T)
    (r : EndpointTorusL2 T) (hres : ∀ z : endpointTorusSpace T, ⟪r, (z : EndpointTorusL2 T)⟫_ℝ = 0)
    (y : Y) :
    ∀ᵐ t ∂timeMeasure T, ⟪endpointSpatialSlice r t, (y : H)⟫_ℝ =
      ⟪T⁻¹ • endpointTorusTimeIntegral hT.le r, (y : H)⟫_ℝ := by
  let g (t : ℝ) : ℝ := ∫ a, ⟪r (t, a), (y : H) a⟫_ℝ ∂unitTorusMeasure
  have hpair := integrable_endpointInner_snd r (y : H)
  have hg : Integrable g (timeMeasure T) := hpair.integral_prod_left
  have hmean : (∫ t, g t ∂timeMeasure T) = ⟪endpointTorusTimeIntegral hT.le r, (y : H)⟫_ℝ :=
    integral_pair_endpointTimeIntegral hT.le r (y : H)
  have hconst : g =ᵐ[timeMeasure T] fun _ => T⁻¹ * ∫ t, g t ∂timeMeasure T := by
    refine Integrable.ae_eq_of_forall_setIntegral_eq g
      (fun _ => T⁻¹ * ∫ t, g t ∂timeMeasure T) hg (integrable_const _) ?_
    intro s hs _
    let χ : ℝ → ℝ := s.indicator fun _ => 1
    let c := T⁻¹ * (timeMeasure T).real s
    let η (t : ℝ) := χ t - c
    have hχ : MemLp χ ⊤ (timeMeasure T) :=
      memLp_top_of_bound (measurable_const.indicator hs).aestronglyMeasurable 1
        (ae_of_all _ fun t => by by_cases ht : t ∈ s <;> simp [χ, ht])
    have hη : MemLp η ⊤ (timeMeasure T) := hχ.sub (memLp_const c)
    have hχint : (∫ t, χ t ∂timeMeasure T) = (timeMeasure T).real s := by
      simp [χ, integral_indicator hs]
    have hηzero : (∫ t, η t ∂timeMeasure T) = 0 := by
      rw [integral_sub (hχ.integrable le_top) (integrable_const c), hχint, integral_const,
        timeMeasure_real_univ_weak hT.le, smul_eq_mul]
      simp [c, hT.ne']
    let f := (memLp_endpointSeparatedTest hη (y : H)).toLp
      (fun q : ℝ × A => η q.1 • (y : H) q.2)
    have hf := mem_endpointCenteredSeparatedTest hη hηzero y
    have hinner := hres ⟨f, hf⟩
    have hrep := (memLp_endpointSeparatedTest hη (y : H)).coeFn_toLp
    have heq : (fun q => ⟪r q, f q⟫_ℝ) =ᵐ[endpointTorusMeasure T]
        fun q => η q.1 * ⟪r q, (y : H) q.2⟫_ℝ :=
      hrep.mono fun q hq => by
        change ⟪r q, f q⟫_ℝ = _
        rw [show f q = _ from hq, real_inner_smul_right]
    have hInt := (L2.integrable_inner r f).congr heq
    have htest : (∫ t, η t * g t ∂timeMeasure T) = 0 := by
      change ⟪r, f⟫_ℝ = 0 at hinner
      rw [L2.inner_def, integral_congr_ae heq] at hinner
      change (∫ q, η q.1 * ⟪r q, (y : H) q.2⟫_ℝ ∂(timeMeasure T).prod unitTorusMeasure) = 0
        at hinner
      rw [integral_prod _ hInt] at hinner
      simpa only [g, integral_const_mul] using hinner
    have hχg : Integrable (fun t => χ t * g t) (timeMeasure T) := by
      simpa only [χ, ← indicator_mul_left, one_mul] using hg.indicator hs
    simp only [η, sub_mul] at htest
    rw [integral_sub hχg (hg.const_mul c), integral_const_mul] at htest
    simp only [χ, ← indicator_mul_left, one_mul, integral_indicator hs] at htest
    rw [setIntegral_const, smul_eq_mul]
    calc
      (∫ t in s, g t ∂timeMeasure T) = c * ∫ t, g t ∂timeMeasure T := sub_eq_zero.mp htest
      _ = _ := by unfold c; ring
  filter_upwards [endpointSpatialSlice_apply_ae r, hconst] with t ht havg
  rw [L2.inner_def, integral_congr_ae (ht.mono fun a ha => congrArg
    (fun z : Vec3 => ⟪z, (y : H) a⟫_ℝ) ha)]
  change g t = _
  rw [havg, hmean, real_inner_smul_left]

/-- The spatial projection of a space-time residual orthogonal to every solenoidal,
zero-time-mean test equals its projected time average at almost every time. -/
theorem endpointWeakResidualProjected_eq_mean {T : ℝ} (hT : 0 < T) (r : EndpointTorusL2 T)
    (hres : ∀ z : endpointTorusSpace T, ⟪r, (z : EndpointTorusL2 T)⟫_ℝ = 0) :
    ∀ᵐ t ∂timeMeasure T, endpointWeakSpatialProjection (endpointSpatialSlice r t) =
      endpointWeakSpatialProjection (T⁻¹ • endpointTorusTimeIntegral hT.le r) := by
  let m := endpointWeakSpatialProjection (T⁻¹ • endpointTorusTimeIntegral hT.le r)
  let bad (y : Y) : Set Y := {v | ⟪v, y⟫_ℝ ≠ ⟪m, y⟫_ℝ}
  have hopen (y : Y) : IsOpen (bad y) :=
    (isClosed_eq (continuous_id.inner continuous_const) continuous_const).isOpen_compl
  let : SecondCountableTopology H :=
    @Lp.SecondCountableTopology A Vec3 _ _ unitTorusMeasure 2 _ ⟨ENNReal.ofNat_ne_top⟩ _ _
  obtain ⟨tests, hcount, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable bad hopen
  have htests : ∀ᵐ t ∂timeMeasure T, ∀ y ∈ tests,
      ⟪endpointWeakSpatialProjection (endpointSpatialSlice r t), y⟫_ℝ = ⟪m, y⟫_ℝ := by
    apply (ae_ball_iff hcount).mpr
    intro y _
    simpa only [m, inner_endpointWeakSpatialProjection] using
      ae_pair_endpointWeakResidual_eq_mean hT r hres y
  filter_upwards [htests] with t ht
  apply ext_inner_right ℝ
  intro y
  by_contra hy
  have hu : endpointWeakSpatialProjection (endpointSpatialSlice r t) ∈ ⋃ z, bad z :=
    mem_iUnion.mpr ⟨y, hy⟩
  rw [← hcover] at hu
  obtain ⟨z, hz, hneq⟩ := mem_iUnion₂.mp hu
  exact hneq (ht z hz)

/-- For almost every time, taking the spatial slice of a product multiplier agrees
with applying the corresponding spatial multiplier to the slice. -/
theorem ae_endpointSpatialSlice_l2Multiplier {T : ℝ}
    (K : ℝ × A → Vec3 →L[ℝ] Vec3)
    (hK : AEStronglyMeasurable K (endpointTorusMeasure T))
    {CK : ℝ} (bK : ∀ᵐ q ∂endpointTorusMeasure T, ‖K q‖ ≤ CK)
    (v : EndpointTorusL2 T) :
    ∀ᵐ t ∂timeMeasure T, ∃ (hKt : AEStronglyMeasurable (fun a => K (t, a)) unitTorusMeasure)
      (bKt : ∀ᵐ a ∂unitTorusMeasure, ‖K (t, a)‖ ≤ CK),
      endpointSpatialSlice (endpointL2Multiplier K hK bK v) t =
        endpointL2Multiplier (fun a => K (t, a)) hKt bKt (endpointSpatialSlice v t) := by
  filter_upwards [hK.prodMk_left, Measure.ae_ae_of_ae_prod bK, endpointSpatialSlice_apply_ae v,
    endpointSpatialSlice_apply_ae (endpointL2Multiplier K hK bK v),
    Measure.ae_ae_of_ae_prod (endpointL2Multiplier_apply_ae K hK bK v)]
    with t hKt bKt hv hm hmul
  refine ⟨hKt, bKt, Lp.ext ?_⟩
  filter_upwards [hm, hv, hmul, endpointL2Multiplier_apply_ae (fun a => K (t, a)) hKt bKt
    (endpointSpatialSlice v t)] with a ham hav hamul htmul
  exact ham.trans (hamul.trans ((congrArg (K (t, a)) hav).symm.trans htmul.symm))

/-- Equation (A.9) for the product `L²` solution, before recovery in the spatial
Hölder norm. The constant is the spatial projection of the time-averaged residual. -/
theorem endpointWeakInstantaneous_of_product_solution {T : ℝ} (hT : 0 < T)
    (K Ω : ℝ × A → Vec3 →L[ℝ] Vec3)
    (hK : AEStronglyMeasurable K (endpointTorusMeasure T))
    (hΩ : AEStronglyMeasurable Ω (endpointTorusMeasure T))
    {CK CΩ : ℝ}
    (bK : ∀ᵐ q ∂endpointTorusMeasure T, ‖K q‖ ≤ CK)
    (bΩ : ∀ᵐ q ∂endpointTorusMeasure T, ‖Ω q‖ ≤ CΩ)
    (v : endpointTorusSpace T) (L : EndpointTorusL2 T)
    (hweak : ∀ z : endpointTorusSpace T,
      ⟪endpointProductOperator unitTorusMeasure hT.le K Ω hK hΩ bK bΩ (v : EndpointTorusL2 T),
        (z : EndpointTorusL2 T)⟫_ℝ = ⟪-L, (z : EndpointTorusL2 T)⟫_ℝ) :
    let JΩ : EndpointTorusL2 T := endpointProductPrimitive unitTorusMeasure hT.le
      (endpointL2Multiplier Ω hΩ bΩ (v : EndpointTorusL2 T))
    let r : EndpointTorusL2 T := (show EndpointTorusL2 T from
      endpointProductOperator unitTorusMeasure hT.le K Ω hK hΩ bK bΩ
        (v : EndpointTorusL2 T)) + L
    let c := endpointWeakSpatialProjection (T⁻¹ • endpointTorusTimeIntegral hT.le r)
    ∀ᵐ t ∂timeMeasure T, ∃ (hKt : AEStronglyMeasurable (fun a => K (t, a)) unitTorusMeasure)
      (bKt : ∀ᵐ a ∂unitTorusMeasure, ‖K (t, a)‖ ≤ CK),
      endpointWeakSpatialProjection (endpointL2Multiplier (fun a => K (t, a)) hKt bKt
        (endpointSpatialSlice (v : EndpointTorusL2 T) t)) =
      c + endpointWeakSpatialProjection (endpointSpatialSlice JΩ t) -
        endpointWeakSpatialProjection (endpointSpatialSlice L t) := by
  intro JΩ r c
  let Kv : EndpointTorusL2 T := endpointL2Multiplier K hK bK (v : EndpointTorusL2 T)
  have hres (z : endpointTorusSpace T) : ⟪r, (z : EndpointTorusL2 T)⟫_ℝ = 0 := by
    let Bv : EndpointTorusL2 T :=
      endpointProductOperator unitTorusMeasure hT.le K Ω hK hΩ bK bΩ (v : EndpointTorusL2 T)
    have hz : ⟪Bv, (z : EndpointTorusL2 T)⟫_ℝ = ⟪-L, (z : EndpointTorusL2 T)⟫_ℝ :=
      hweak z
    change ⟪Bv + L, (z : EndpointTorusL2 T)⟫_ℝ = 0
    rw [inner_add_left, hz, inner_neg_left, neg_add_cancel]
  have hsum : r = Kv - JΩ + L := rfl
  have hrep : ∀ᵐ q ∂endpointTorusMeasure T, r q = Kv q - JΩ q + L q := by
    filter_upwards [Lp.coeFn_add (Kv - JΩ) L, Lp.coeFn_sub Kv JΩ] with q ha hs
    rw [hsum, ha, Pi.add_apply, hs, Pi.sub_apply]
  filter_upwards [endpointWeakResidualProjected_eq_mean hT r hres,
    ae_endpointSpatialSlice_l2Multiplier K hK bK (v : EndpointTorusL2 T),
    endpointSpatialSlice_apply_ae r, endpointSpatialSlice_apply_ae Kv,
    endpointSpatialSlice_apply_ae JΩ, endpointSpatialSlice_apply_ae L,
    Measure.ae_ae_of_ae_prod hrep]
    with t hmean hk hr hkv hj hl hrt
  obtain ⟨hKt, bKt, hKtSlice⟩ := hk
  have hsl : endpointSpatialSlice r t =
      endpointSpatialSlice Kv t - endpointSpatialSlice JΩ t + endpointSpatialSlice L t := by
    apply Lp.ext
    filter_upwards [hr, hkv, hj, hl, hrt,
      Lp.coeFn_add (endpointSpatialSlice Kv t - endpointSpatialSlice JΩ t) (endpointSpatialSlice L t),
      Lp.coeFn_sub (endpointSpatialSlice Kv t) (endpointSpatialSlice JΩ t)]
      with a hra hkva hja hla hrta ha hs
    exact hra.trans (hrta.trans (by rw [ha, Pi.add_apply, hs, Pi.sub_apply, hkva, hja, hla]))
  refine ⟨hKt, bKt, ?_⟩
  change endpointWeakSpatialProjection (endpointSpatialSlice r t) = c at hmean
  change endpointSpatialSlice Kv t = _ at hKtSlice
  rw [hsl, map_add, map_sub, hKtSlice] at hmean
  rw [← hmean]
  abel

end TorusEuler
