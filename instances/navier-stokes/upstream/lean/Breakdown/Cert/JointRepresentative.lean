import Mathlib
import Breakdown.Cert.Statement

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace Breakdown.Cert

instance zero_lt_one_fact : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

namespace JointRepresentativeInternal

variable {α β F : Type*} [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup F]

theorem simpleSlice_stronglyMeasurable {p : ℝ≥0∞} {ν : Measure β} (g : SimpleFunc α (Lp F p ν)) :
    StronglyMeasurable (fun z : α × β => (g z.1 : β → F) z.2) := by
  classical
  have h : (fun z : α × β => (g z.1 : β → F) z.2) = fun z => ∑ e ∈ g.range,
      ((g ⁻¹' {e}) ×ˢ (univ : Set β)).indicator (fun z : α × β => (e : β → F) z.2) z := by
    funext z
    rw [Finset.sum_eq_single_of_mem (g z.1) (g.mem_range_self z.1)]
    · rw [indicator_of_mem]
      exact ⟨rfl, mem_univ _⟩
    · intro e _ he
      rw [indicator_of_notMem]
      rintro ⟨h1, -⟩
      exact he h1.symm
  rw [h]
  refine Finset.stronglyMeasurable_fun_sum _ fun e _ => ?_
  exact ((Lp.stronglyMeasurable e).comp_measurable measurable_snd).indicator
    ((g.measurableSet_fiber e).prod MeasurableSet.univ)

theorem two_mul_inv_four : (2 : ℝ≥0∞) * 4⁻¹ = 2⁻¹ := by
  rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
    ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

theorem tsum_inv_two_pow_ne_top : ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ k ≠ ⊤ := by
  rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.ofNat_ne_top

theorem le_mul_inv_two_pow {x S : ℝ≥0∞} (k : ℕ) (h : 2 ^ k * x ≤ S) : x ≤ S * 2⁻¹ ^ k := by
  calc x = 2⁻¹ ^ k * (2 ^ k * x) := by
        rw [← mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow,
          one_mul]
    _ ≤ 2⁻¹ ^ k * S := by gcongr
    _ = S * 2⁻¹ ^ k := mul_comm _ _

theorem joint_of_stronglyMeasurable [CompleteSpace F] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [SFinite ν] {c : α → Lp F p ν} (hcm : StronglyMeasurable c)
    (hc : MemLp c 1 μ) :
    ∃ h : α × β → F, StronglyMeasurable h ∧ ∀ᵐ a ∂μ, (c a : β → F) =ᵐ[ν] fun y => h (a, y) := by
  have hq : ∀ k : ℕ, ((4 : ℝ≥0∞)⁻¹) ^ k ≠ 0 := fun k =>
    pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)
  choose g hg _ using fun k : ℕ => hc.exists_simpleFunc_eLpNorm_sub_lt ENNReal.one_ne_top (hq k)
  let ε : ℕ → α → ℝ≥0∞ := fun k a => ‖c a - g k a‖ₑ
  have hεm : ∀ k, Measurable (ε k) := fun k => (hcm.sub (g k).stronglyMeasurable).enorm
  have hε : ∀ k, ∫⁻ a, ε k a ∂μ < 4⁻¹ ^ k := fun k => by
    have := hg k
    rwa [eLpNorm_one_eq_lintegral_enorm] at this
  have hT : ∫⁻ a, ∑' k, 2 ^ k * ε k a ∂μ ≠ ⊤ := by
    rw [lintegral_tsum fun k => ((hεm k).const_mul _).aemeasurable]
    refine ne_top_of_le_ne_top tsum_inv_two_pow_ne_top (ENNReal.tsum_le_tsum fun k => ?_)
    rw [lintegral_const_mul _ (hεm k)]
    calc 2 ^ k * ∫⁻ a, ε k a ∂μ ≤ 2 ^ k * 4⁻¹ ^ k := by gcongr; exact (hε k).le
      _ = 2⁻¹ ^ k := by rw [← mul_pow, two_mul_inv_four]
  have hTae : ∀ᵐ a ∂μ, ∑' k, 2 ^ k * ε k a < ⊤ :=
    ae_lt_top (Measurable.tsum fun k => (hεm k).const_mul _) hT
  let G : ℕ → α × β → F := fun k z => (g k z.1 : β → F) z.2
  have hG : ∀ k, StronglyMeasurable (G k) := fun k => simpleSlice_stronglyMeasurable (g k)
  have hbound : ∀ a, ∑' k, 2 ^ k * ε k a < ⊤ → ∀ k, ε k a ≤ (∑' k, 2 ^ k * ε k a) * 2⁻¹ ^ k :=
    fun a _ k => le_mul_inv_two_pow k (ENNReal.le_tsum k)
  have hslice : ∀ᵐ a ∂μ, ∀ᵐ y ∂ν, ∃ l : F, Tendsto (fun n => G n (a, y)) atTop (𝓝 l) := by
    filter_upwards [hTae] with a ha
    set S := ∑' k, 2 ^ k * ε k a
    refine Lp.ae_tendsto_of_cauchy_eLpNorm (f := fun n => (g n a : β → F))
      (fun n => Lp.aestronglyMeasurable _) (Fact.out : 1 ≤ p)
      (B := fun N => (2 * S + 1) * 2⁻¹ ^ N) ?_ ?_
    · rw [ENNReal.tsum_mul_left]
      exact ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) ha.ne,
        ENNReal.one_ne_top⟩) tsum_inv_two_pow_ne_top
    · intro N n m hn hm
      have hx0 : (2⁻¹ : ℝ≥0∞) ^ N ≠ 0 := pow_ne_zero _ (by simp)
      have hS : 2 * S * 2⁻¹ ^ N ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ha.ne) (by simp)
      calc eLpNorm ((g n a : β → F) - (g m a : β → F)) p ν = edist (g n a) (g m a) :=
            (Lp.edist_def _ _).symm
        _ ≤ edist (c a) (g n a) + edist (c a) (g m a) := edist_triangle_left _ _ _
        _ = ε n a + ε m a := by rw [edist_eq_enorm_sub, edist_eq_enorm_sub]
        _ ≤ S * 2⁻¹ ^ n + S * 2⁻¹ ^ m := add_le_add (hbound a ha n) (hbound a ha m)
        _ ≤ S * 2⁻¹ ^ N + S * 2⁻¹ ^ N :=
            add_le_add (mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.2 one_le_two) hn))
              (mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.2 one_le_two) hm))
        _ = 2 * S * 2⁻¹ ^ N := by ring
        _ < 2 * S * 2⁻¹ ^ N + 2⁻¹ ^ N := ENNReal.lt_add_right hS hx0
        _ = (2 * S + 1) * 2⁻¹ ^ N := by ring
  have hconv : MeasurableSet {z : α × β | ∃ l : F, Tendsto (fun n => G n z) atTop (𝓝 l)} :=
    StronglyMeasurable.measurableSet_exists_tendsto hG
  have hprod : ∀ᵐ z ∂μ.prod ν, ∃ l : F, Tendsto (fun n => G n z) atTop (𝓝 l) :=
    (Measure.ae_prod_iff_ae_ae hconv).2 hslice
  obtain ⟨h, hh, hlim⟩ := exists_stronglyMeasurable_limit_of_tendsto_ae
    (fun n => (hG n).aestronglyMeasurable) hprod
  refine ⟨h, hh, ?_⟩
  filter_upwards [hTae, Measure.ae_ae_of_ae_prod hlim] with a ha hay
  have h0 : Tendsto (fun n => ε n a) atTop (𝓝 0) := by
    have h1 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top ha.ne
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => bot_le)
      (fun n => ?_)
    exact le_mul_of_one_le_left' (one_le_pow₀ (by norm_num))
  have hle := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := p) (μ := ν)
    (f := fun n y => (g n a : β → F) y - (c a : β → F) y)
    (fun n => (Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))
    (fun y => h (a, y) - (c a : β → F) y) (hay.mono fun y hy => hy.sub_const _)
  have heq : ∀ n, eLpNorm (fun y => (g n a : β → F) y - (c a : β → F) y) p ν = ε n a := by
    intro n
    show _ = ‖c a - g n a‖ₑ
    rw [← edist_eq_enorm_sub, edist_comm, Lp.edist_def]
    rfl
  simp_rw [heq] at hle
  rw [h0.liminf_eq, nonpos_iff_eq_zero] at hle
  have hm : AEStronglyMeasurable (fun y => h (a, y) - (c a : β → F) y) ν :=
    (hh.comp_measurable measurable_prodMk_left).aestronglyMeasurable.sub (Lp.aestronglyMeasurable _)
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  filter_upwards [(eLpNorm_eq_zero_iff hm hp0).1 hle] with y hy
  exact (sub_eq_zero.1 hy).symm

theorem joint_of_memLp_one [CompleteSpace F] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [SFinite ν] {c : α → Lp F p ν} (hc : MemLp c 1 μ) :
    ∃ h : α × β → F, StronglyMeasurable h ∧ ∀ᵐ a ∂μ, (c a : β → F) =ᵐ[ν] fun y => h (a, y) := by
  obtain ⟨h, hh, hae⟩ := joint_of_stronglyMeasurable hc.1.stronglyMeasurable_mk
    (hc.ae_eq hc.1.ae_eq_mk)
  refine ⟨h, hh, ?_⟩
  filter_upwards [hae, hc.1.ae_eq_mk] with a h1 h2
  rw [h2]
  exact h1

theorem ae_coe_of_ae {P : AddCircle (1 : ℝ) → Prop} (h : ∀ᵐ a, P a) :
    ∀ᵐ σ : ℝ, P (σ : AddCircle (1 : ℝ)) := by
  have hn : ∀ n : ℤ, ∀ᵐ σ : ℝ ∂(volume.restrict (Ioc (n : ℝ) (n + 1))), P (σ : AddCircle (1 : ℝ)) :=
    fun n => (AddCircle.measurePreserving_mk (1 : ℝ) n).quasiMeasurePreserving.ae h
  have := (ae_restrict_iUnion_iff _ _).2 hn
  rwa [iUnion_Ioc_intCast, Measure.restrict_univ] at this

theorem measurable_of_dist_dense {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] {u : α → X} {D : ℕ → X} (hD : DenseRange D)
    (h : ∀ k, Measurable fun a => dist (u a) (D k)) : Measurable u := by
  refine measurable_of_isOpen fun U hU => ?_
  have hU' : u ⁻¹' U = ⋃ k : ℕ, ⋃ q : ℚ,
      {a | dist (u a) (D k) < q} ∩ {_a | Metric.ball (D k) q ⊆ U} := by
    ext a
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro ha
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU (u a) ha
      obtain ⟨q, hq0, hq⟩ := exists_rat_btwn (half_pos hε)
      obtain ⟨k, hk⟩ := Metric.denseRange_iff.1 hD (u a) q hq0
      refine ⟨k, q, hk, fun w hw => hball ?_⟩
      rw [Metric.mem_ball] at hw ⊢
      calc dist w (u a) ≤ dist w (D k) + dist (D k) (u a) := dist_triangle _ _ _
        _ < q + q := add_lt_add hw (by rw [dist_comm]; exact hk)
        _ < ε := by linarith
    · rintro ⟨k, q, hk, hsub⟩
      exact hsub (Metric.mem_ball.2 hk)
  rw [hU']
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun q =>
    (measurableSet_lt (h k) measurable_const).inter (MeasurableSet.const _)

theorem sq_eLpNorm_two {γ : Type*} [MeasurableSpace γ] (f : γ → F) (μ : Measure γ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

theorem measurable_eLpNorm_two_slice {ν : Measure β} [SFinite ν] {H : α × β → F}
    (hH : StronglyMeasurable H) : Measurable fun a => eLpNorm (fun y => H (a, y)) 2 ν := by
  have h : (fun a => eLpNorm (fun y => H (a, y)) 2 ν) =
      fun a => (∫⁻ y, ‖H (a, y)‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) := by
    funext a
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  rw [h]
  exact ((hH.enorm.pow_const _).lintegral_prod_right').pow_const _

theorem curve_of_joint [SecondCountableTopology F] {μ : Measure α} {ν : Measure β} [SFinite μ]
    [SFinite ν] [IsSeparable ν] {g : α × β → F} (hg : AEStronglyMeasurable g (μ.prod ν))
    (hfin : ∫⁻ a, ∫⁻ y, ‖g (a, y)‖ₑ ^ 2 ∂ν ∂μ ≠ ⊤) :
    ∃ c : Lp (Lp F 2 ν) 2 μ, (∀ᵐ a ∂μ, (c a : β → F) =ᵐ[ν] fun y => g (a, y)) ∧
      ‖c‖ ^ 2 = (∫⁻ a, ∫⁻ y, ‖g (a, y)‖ₑ ^ 2 ∂ν ∂μ).toReal := by
  classical
  set g' := hg.mk g
  have hg'm : StronglyMeasurable g' := hg.stronglyMeasurable_mk
  have hslice : ∀ a, StronglyMeasurable fun y => g' (a, y) := fun a =>
    hg'm.comp_measurable measurable_prodMk_left
  have hgg : ∀ᵐ a ∂μ, ∀ᵐ y ∂ν, g' (a, y) = g (a, y) :=
    Measure.ae_ae_of_ae_prod (hg.ae_eq_mk.mono fun z hz => hz.symm)
  let I : α → ℝ≥0∞ := fun a => ∫⁻ y, ‖g' (a, y)‖ₑ ^ 2 ∂ν
  have hIm : Measurable I := (hg'm.enorm.pow_const 2).lintegral_prod_right'
  have hII : ∫⁻ a, I a ∂μ = ∫⁻ a, ∫⁻ y, ‖g (a, y)‖ₑ ^ 2 ∂ν ∂μ :=
    lintegral_congr_ae (hgg.mono fun a ha => lintegral_congr_ae (ha.mono fun y hy => by
      simp only [hy]))
  have hIfin : ∀ᵐ a ∂μ, I a < ⊤ := ae_lt_top hIm (hII ▸ hfin)
  have hsq : ∀ a, eLpNorm (fun y => g' (a, y)) 2 ν ^ 2 = I a := fun a => sq_eLpNorm_two _ _
  have hmem : ∀ a, I a < ⊤ → MemLp (fun y => g' (a, y)) 2 ν := by
    intro a ha
    refine ⟨(hslice a).aestronglyMeasurable, lt_top_iff_ne_top.2 fun htop => ?_⟩
    rw [← hsq a, htop] at ha
    simp at ha
  let u : α → Lp F 2 ν := fun a => if h : I a < ⊤ then (hmem a h).toLp _ else 0
  borelize (↥(Lp F 2 ν))
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp F 2 ν) := Lp.SecondCountableTopology
  obtain ⟨D, hD⟩ := TopologicalSpace.exists_dense_seq (Lp F 2 ν)
  have hum : Measurable u := by
    refine measurable_of_dist_dense hD fun k => ?_
    have he : (fun a => dist (u a) (D k)) = fun a => if I a < ⊤ then
        (eLpNorm (fun y => g' (a, y) - (D k : β → F) y) 2 ν).toReal else dist 0 (D k) := by
      funext a
      by_cases ha : I a < ⊤
      · simp only [u, dif_pos ha, if_pos ha]
        rw [Lp.dist_def]
        congr 1
        exact eLpNorm_congr_ae ((hmem a ha).coeFn_toLp.sub EventuallyEq.rfl)
      · simp only [u, dif_neg ha, if_neg ha]
    rw [he]
    refine Measurable.ite (measurableSet_lt hIm measurable_const) ?_ measurable_const
    have hH : StronglyMeasurable fun z : α × β => g' z - (D k : β → F) z.2 :=
      hg'm.sub ((Lp.stronglyMeasurable (D k)).comp_measurable measurable_snd)
    exact (measurable_eLpNorm_two_slice (ν := ν) hH).ennreal_toReal
  have hnorm : ∀ᵐ a ∂μ, ‖u a‖ₑ ^ 2 = I a := by
    filter_upwards [hIfin] with a ha
    simp only [u, dif_pos ha]
    rw [Lp.enorm_def, eLpNorm_congr_ae (hmem a ha).coeFn_toLp, hsq]
  have hu2 : eLpNorm u 2 μ ^ 2 = ∫⁻ a, ∫⁻ y, ‖g (a, y)‖ₑ ^ 2 ∂ν ∂μ := by
    rw [sq_eLpNorm_two, lintegral_congr_ae hnorm, hII]
  have humem : MemLp u 2 μ := by
    refine ⟨hum.aestronglyMeasurable, lt_top_iff_ne_top.2 fun htop => hfin ?_⟩
    rw [← hu2, htop]
    simp
  refine ⟨humem.toLp u, ?_, ?_⟩
  · filter_upwards [humem.coeFn_toLp, hIfin, hgg] with a h1 h2 h3
    rw [h1]
    simp only [u, dif_pos h2]
    exact (hmem a h2).coeFn_toLp.trans h3
  · rw [Lp.norm_toLp, ← ENNReal.toReal_pow, hu2]

theorem periodic_of_coe_eq {F : Type*} {f : ℝ → Space → F} (hper : IsTimePeriodic f) {r σ : ℝ}
    (h : (r : AddCircle (1 : ℝ)) = σ) : f r = f σ := by
  have h0 : ((r - σ : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff 1).1 h0
  have hr : r = σ + n • (1 : ℝ) := by linarith
  funext y
  rw [hr]
  exact (Function.Periodic.zsmul (show Function.Periodic (fun s => f s y) 1 from
    fun s => hper s y) n) σ

end JointRepresentativeInternal

theorem exists_joint_representative {F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (c : Lp (α := AddCircle (1 : ℝ)) (Lp (α := Space) F p) 2) :
    ∃ f : ℝ → Space → F, AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume ∧
      IsTimePeriodic f ∧ ∀ᵐ σ : ℝ, ((c (σ : AddCircle (1 : ℝ)) : Space → F) =ᵐ[volume] f σ) := by
  obtain ⟨h, hh, hae⟩ := JointRepresentativeInternal.joint_of_memLp_one (μ := volume)
    (ν := volume) ((Lp.memLp c).mono_exponent (by norm_num))
  refine ⟨fun σ y => h ((σ : AddCircle (1 : ℝ)), y), ?_, fun σ y => ?_,
    JointRepresentativeInternal.ae_coe_of_ae hae⟩
  · rw [Measure.volume_eq_prod]
    exact (hh.comp_measurable ((AddCircle.measurable_mk'.comp measurable_fst).prodMk
      measurable_snd)).aestronglyMeasurable
  · simp only [AddCircle.coe_add_period]

theorem exists_curve_of_joint {F : Type*} [NormedAddCommGroup F] [SecondCountableTopology F]
    (f : ℝ → Space → F) (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume)
    (hper : IsTimePeriodic f)
    (hfin : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖f σ y‖ ^ 2) < ⊤) :
    ∃ c : Lp (α := AddCircle (1 : ℝ)) (Lp (α := Space) F 2) 2,
      (∀ᵐ σ : ℝ, ((c (σ : AddCircle (1 : ℝ)) : Space → F) =ᵐ[volume] f σ)) ∧
      ‖c‖ ^ 2 = (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖f σ y‖ ^ 2)).toReal := by
  have hI : Ioc (0 : ℝ) (0 + 1) = Ioc 0 1 := by rw [zero_add]
  have hg : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2)
      ((volume.restrict (Ioc (0 : ℝ) (0 + 1))).prod volume) := by
    have := hf.restrict (s := Ioc (0 : ℝ) (0 + 1) ×ˢ (univ : Set Space))
    rwa [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at this
  have hconv : ∀ σ, ∫⁻ y, ENNReal.ofReal (‖f σ y‖ ^ 2) = ∫⁻ y, ‖f σ y‖ₑ ^ 2 := fun σ => by
    congr 1
    funext y
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hIcc : (∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖f σ y‖ ^ 2)) =
      ∫⁻ σ in Ioc (0 : ℝ) (0 + 1), ∫⁻ y, ‖f σ y‖ₑ ^ 2 := by
    simp_rw [hconv, hI]
    exact setLIntegral_congr Ioc_ae_eq_Icc.symm
  obtain ⟨c0, hc0, hn⟩ := JointRepresentativeInternal.curve_of_joint hg (by rw [← hIcc]; exact hfin.ne)
  have hrep : MeasurePreserving (fun a : AddCircle (1 : ℝ) => (AddCircle.equivIoc 1 0 a : ℝ))
      volume (volume.restrict (Ioc (0 : ℝ) (0 + 1))) :=
    (measurePreserving_subtype_coe measurableSet_Ioc).comp (AddCircle.measurePreserving_equivIoc 1)
  refine ⟨Lp.compMeasurePreserving _ hrep c0, ?_, ?_⟩
  · have h1 := Lp.coeFn_compMeasurePreserving c0 hrep
    have h2 := hrep.quasiMeasurePreserving.ae hc0
    filter_upwards [JointRepresentativeInternal.ae_coe_of_ae (h1.and h2)] with σ hσ
    rw [hσ.1]
    refine hσ.2.trans (EventuallyEq.of_eq ?_)
    exact JointRepresentativeInternal.periodic_of_coe_eq hper AddCircle.coe_equivIoc
  · rw [Lp.norm_compMeasurePreserving, hn, hIcc]

end Breakdown.Cert
