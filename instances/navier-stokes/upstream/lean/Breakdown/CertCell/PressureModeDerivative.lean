import Breakdown.CertCell.BridgeTraceStatements
import Breakdown.FracCell.CylModeWeak
import Breakdown.FracCell.MeshDataAffineModes
import Breakdown.FracCell.ModeHeightAxis
import Breakdown.FracCell.LowEntry

open scoped ContDiff
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown

namespace CertCell

namespace SideTrace

namespace Internal.PressureMode

def dom (b : Bool) : Set ℝ := if b then Ioi 0 else univ

def ex (b : Bool) (N : ℕ) : Set ℝ :=
  if b then Icc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1) else Icc (-(N : ℝ)) N

def IsAdm (b : Bool) (ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ dom b

lemma isOpen_dom (b : Bool) : IsOpen (dom b) := by
  cases b <;> simp [dom, isOpen_Ioi]

lemma measurableSet_dom (b : Bool) : MeasurableSet (dom b) := (isOpen_dom b).measurableSet

lemma isCompact_ex (b : Bool) (N : ℕ) : IsCompact (ex b N) := by
  cases b <;> simp [ex, isCompact_Icc]

lemma measurableSet_ex (b : Bool) (N : ℕ) : MeasurableSet (ex b N) := by
  cases b <;> simp [ex, measurableSet_Icc]

lemma ex_sub_dom (b : Bool) (N : ℕ) : ex b N ⊆ dom b := by
  cases b
  · simp [dom]
  · intro x hx
    simp only [ex, if_true] at hx
    simp only [dom, if_true, mem_Ioi]
    have h1 : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    linarith [hx.1]

lemma ex_mono (b : Bool) {N M : ℕ} (h : N ≤ M) : ex b N ⊆ ex b M := by
  have hNM : (N : ℝ) ≤ M := by exact_mod_cast h
  cases b
  · simp only [ex, Bool.false_eq_true, if_false]
    exact Icc_subset_Icc (by linarith) hNM
  · simp only [ex, if_true]
    refine Icc_subset_Icc ?_ (by linarith)
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

lemma exists_ex_of_compact (b : Bool) {k : Set ℝ} (hk : IsCompact k) (hkd : k ⊆ dom b) :
    ∃ N : ℕ, k ⊆ ex b N := by
  obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall 0
  have habs : ∀ x ∈ k, |x| ≤ R := fun x hx => by
    have h := hR hx
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
  cases b
  · refine ⟨⌈R⌉₊, fun x hx => ?_⟩
    simp only [ex, Bool.false_eq_true, if_false, mem_Icc]
    have h1 := abs_le.1 ((habs x hx).trans (Nat.le_ceil R))
    exact h1
  · rcases k.eq_empty_or_nonempty with h0 | hne
    · exact ⟨0, by simp [h0]⟩
    obtain ⟨x0, hx0, hmin⟩ := hk.exists_isMinOn hne continuousOn_id
    have hpos : 0 < x0 := by
      have := hkd hx0
      simpa [dom] using this
    refine ⟨⌈R + 1 / x0⌉₊, fun x hx => ?_⟩
    simp only [ex, if_true, mem_Icc]
    have hc := Nat.le_ceil (R + 1 / x0)
    have hR0 : 0 ≤ R := (abs_nonneg x).trans (habs x hx)
    have hx0x : x0 ≤ x := hmin hx
    set M : ℝ := ((⌈R + 1 / x0⌉₊ : ℕ) : ℝ) with hM
    have hMp : 0 < M + 1 := by positivity
    refine ⟨?_, ?_⟩
    · have h2 : 1 / x0 < M + 1 := by
        have : 0 ≤ R := hR0
        linarith
      have h3 : 1 / (M + 1) < x0 := by
        rw [div_lt_iff₀ hMp]
        rw [div_lt_iff₀ hpos] at h2
        linarith
      linarith
    · have h4 := le_abs_self x
      have h5 : 0 < 1 / x0 := by positivity
      linarith [habs x hx]

lemma adm_of_sub (b : Bool) {ψ : ℝ → ℝ} {N : ℕ} (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ ex b N) :
    IsAdm b ψ :=
  ⟨hψ, IsCompact.of_isClosed_subset (isCompact_ex b N) (isClosed_tsupport _) hs, hs.trans (ex_sub_dom b N)⟩

lemma integral_eq_setIntegral_of_tsupport {F : ℝ → ℂ} {ψ : ℝ → ℝ} {S : Set ℝ} (hs : tsupport ψ ⊆ S) :
    ∫ x, F x * ((ψ x : ℝ) : ℂ) = ∫ x in S, F x * ((ψ x : ℝ) : ℂ) := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))]
  simp

lemma continuous_pairing {F : ℝ → ℂ} {S : Set ℝ} (hS : IsCompact S) (hF : IntegrableOn F S) :
    Continuous (fun u : C(ℝ, ℝ) => ∫ x in S, F x * ((u x : ℝ) : ℂ)) := by
  refine continuous_iff_continuousAt.2 fun u0 => ?_
  have hunif : TendstoUniformlyOn (fun (u : C(ℝ, ℝ)) (x : ℝ) => u x) u0 (𝓝 u0) S :=
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 tendsto_id) S hS
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn u0.continuous.continuousOn
  have hnear : ∀ᶠ u in 𝓝 u0, ∀ x ∈ S, dist (u0 x) (u x) < 1 :=
    Metric.tendstoUniformlyOn_iff.1 hunif 1 one_pos
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖F x‖ * (C + 1)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun u =>
      hF.1.mul (Complex.continuous_ofReal.comp u.continuous).aestronglyMeasurable
  · filter_upwards [hnear] with u hu
    refine (ae_restrict_iff' hS.measurableSet).2 (Eventually.of_forall fun x hx => ?_)
    rw [norm_mul, Complex.norm_real]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h1 := hC x hx
    have h2 := hu x hx
    rw [Real.dist_eq] at h2
    rw [Real.norm_eq_abs] at h1 ⊢
    have h3 : |u x| ≤ |u0 x| + |u0 x - u x| := by
      calc |u x| = |u0 x - (u0 x - u x)| := by ring_nf
        _ ≤ |u0 x| + |u0 x - u x| := abs_sub _ _
    linarith
  · exact hF.norm.mul_const _
  · exact Eventually.of_forall fun x => tendsto_const_nhds.mul
      ((Complex.continuous_ofReal.comp
        (continuous_eval_const x : Continuous fun u : C(ℝ, ℝ) => u x)).tendsto u0)

def pairSet (b : Bool) (N : ℕ) : Set (C(ℝ, ℝ) × C(ℝ, ℝ)) :=
  {p | ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ tsupport ψ ⊆ ex b N ∧ ⇑p.1 = ψ ∧ ⇑p.2 = deriv ψ}

lemma countable_dense_tests (b : Bool) : ∃ D : Set (ℝ → ℝ), D.Countable ∧ (∀ ψ ∈ D, IsAdm b ψ) ∧
    ∀ F Fd : ℝ → ℂ, (∀ N : ℕ, IntegrableOn F (ex b N) ∧ IntegrableOn Fd (ex b N)) →
      (∀ ψ ∈ D, ∫ x, F x * ((deriv ψ x : ℝ) : ℂ) = -∫ x, Fd x * ((ψ x : ℝ) : ℂ)) →
      ∀ ψ, IsAdm b ψ → ∫ x, F x * ((deriv ψ x : ℝ) : ℂ) = -∫ x, Fd x * ((ψ x : ℝ) : ℂ) := by
  choose T hTc hTd using fun N : ℕ => TopologicalSpace.exists_countable_dense (pairSet b N)
  refine ⟨⋃ N, (fun p : pairSet b N => ⇑p.1.1) '' T N, countable_iUnion fun N => (hTc N).image _, ?_, ?_⟩
  · intro ψ hψ
    obtain ⟨N, hN⟩ := mem_iUnion.1 hψ
    obtain ⟨p, -, rfl⟩ := hN
    obtain ⟨φ, hφ, hsupp, h1, -⟩ := p.2
    show IsAdm b (⇑p.1.1)
    rw [h1]
    exact adm_of_sub b hφ hsupp
  · intro F Fd hint hD ψ hψ
    obtain ⟨N, hN⟩ := exists_ex_of_compact b hψ.2.1 hψ.2.2
    set S := ex b N
    set Φ : C(ℝ, ℝ) × C(ℝ, ℝ) → ℂ := fun p => (∫ x in S, F x * ((p.2 x : ℝ) : ℂ)) +
      ∫ x in S, Fd x * ((p.1 x : ℝ) : ℂ) with hΦdef
    have hΦ : Continuous Φ :=
      ((continuous_pairing (isCompact_ex b N) (hint N).1).comp continuous_snd).add
        ((continuous_pairing (isCompact_ex b N) (hint N).2).comp continuous_fst)
    have hzero : (fun p : pairSet b N => Φ p.1) = fun _ => 0 := by
      refine Continuous.ext_on (hTd N) (hΦ.comp continuous_subtype_val) continuous_const fun p hp => ?_
      obtain ⟨φ, -, hφs, h1, h2⟩ := p.2
      have hmem : ⇑p.1.1 ∈ ⋃ N, (fun p : pairSet b N => ⇑p.1.1) '' T N := mem_iUnion.2 ⟨N, p, hp, rfl⟩
      have key := hD _ hmem
      rw [h1] at key
      simp only [hΦdef, h1, h2]
      rw [← integral_eq_setIntegral_of_tsupport (tsupport_deriv_subset.trans hφs),
        ← integral_eq_setIntegral_of_tsupport hφs, key, neg_add_cancel]
    have hp : ((⟨ψ, hψ.1.continuous⟩ : C(ℝ, ℝ)), (⟨deriv ψ, hψ.1.continuous_deriv (by simp)⟩ : C(ℝ, ℝ))) ∈
        pairSet b N := ⟨ψ, hψ.1, hN, rfl, rfl⟩
    have h0 := congrFun hzero ⟨_, hp⟩
    simp only [hΦdef, ContinuousMap.coe_mk] at h0
    rw [integral_eq_setIntegral_of_tsupport (tsupport_deriv_subset.trans hN),
      integral_eq_setIntegral_of_tsupport hN]
    linear_combination h0

lemma restrict_prod_eq' (S T : Set ℝ) :
    volume.restrict (S ×ˢ T) = (volume.restrict S).prod (volume.restrict T) := by
  rw [Measure.volume_eq_prod, Measure.prod_restrict]

lemma ae_slice_integrableOn {f : ℝ × ℝ → ℂ} {S T : Set ℝ} (hT : MeasurableSet T)
    (hf : IntegrableOn f (S ×ˢ T)) : ∀ᵐ s, s ∈ T → IntegrableOn (fun x => f (x, s)) S := by
  have h : Integrable f ((volume.restrict S).prod (volume.restrict T)) := by
    rw [← restrict_prod_eq']
    exact hf
  exact (ae_restrict_iff' hT).1 h.prod_left_ae

lemma ex_mem_of_dom (b : Bool) {s : ℝ} (hs : s ∈ dom b) : ∃ N, s ∈ ex b N := by
  obtain ⟨N, hN⟩ := exists_ex_of_compact b isCompact_singleton (singleton_subset_iff.2 hs)
  exact ⟨N, hN (mem_singleton s)⟩

lemma ae_slices (pa ps : Bool) {A : ℝ × ℝ → ℂ} (hA : ∀ N, IntegrableOn A (ex pa N ×ˢ ex ps N)) :
    ∀ᵐ s, s ∈ dom ps → ∀ N, IntegrableOn (fun x => A (x, s)) (ex pa N) := by
  have h := ae_all_iff.2 fun N => ae_slice_integrableOn (measurableSet_ex ps N) (hA N)
  filter_upwards [h] with s hs hsd N
  obtain ⟨M0, hM0⟩ := ex_mem_of_dom ps hsd
  have hM := hs (max N M0) (ex_mono ps (le_max_right N M0) hM0)
  exact hM.mono_set (ex_mono pa (le_max_left N M0))

lemma integrable_test_mul {pa ps : Bool} {A : ℝ × ℝ → ℂ} (hA : ∀ N, IntegrableOn A (ex pa N ×ˢ ex ps N))
    {a c : ℝ → ℝ} (ha : Continuous a) (hc : Continuous c) {N : ℕ} (has : tsupport a ⊆ ex pa N)
    (hcs : tsupport c ⊆ ex ps N) :
    Integrable (fun p : ℝ × ℝ => ((a p.1 * c p.2 : ℝ) : ℂ) * A p) := by
  have hK : IsCompact (ex pa N ×ˢ ex ps N) := (isCompact_ex pa N).prod (isCompact_ex ps N)
  have h1 : IntegrableOn (fun p : ℝ × ℝ => ((a p.1 * c p.2 : ℝ) : ℂ) * A p) (ex pa N ×ˢ ex ps N) :=
    IntegrableOn.continuousOn_mul
      (Complex.continuous_ofReal.comp ((ha.comp continuous_fst).mul (hc.comp continuous_snd))).continuousOn
      (hA N) hK
  refine h1.integrable_of_forall_notMem_eq_zero fun p hp => ?_
  rw [mem_prod, not_and_or] at hp
  rcases hp with h | h
  · rw [image_eq_zero_of_notMem_tsupport (fun h' => h (has h'))]
    simp
  · rw [image_eq_zero_of_notMem_tsupport (fun h' => h (hcs h'))]
    simp

lemma ae_slice_identity (pa ps : Bool) {A B : ℝ × ℝ → ℂ}
    (hA : ∀ N, IntegrableOn A (ex pa N ×ˢ ex ps N)) (hB : ∀ N, IntegrableOn B (ex pa N ×ˢ ex ps N))
    (hw : ∀ α β, IsAdm pa α → IsAdm ps β →
      ∫ p, ((deriv α p.1 * β p.2 : ℝ) : ℂ) * A p = -∫ p, ((α p.1 * β p.2 : ℝ) : ℂ) * B p)
    {α : ℝ → ℝ} (hα : IsAdm pa α) :
    ∀ᵐ s, s ∈ dom ps → (∀ N, IntegrableOn (fun x => A (x, s)) (ex pa N)) →
      (∀ N, IntegrableOn (fun x => B (x, s)) (ex pa N)) →
      ∫ x, A (x, s) * ((deriv α x : ℝ) : ℂ) = -∫ x, B (x, s) * ((α x : ℝ) : ℂ) := by
  obtain ⟨N0, hN0⟩ := exists_ex_of_compact pa hα.2.1 hα.2.2
  set S := ex pa N0 with hSdef
  have hαc : Continuous α := hα.1.continuous
  have hdc : Continuous (deriv α) := hα.1.continuous_deriv (by simp)
  set H : ℝ × ℝ → ℂ := fun p => A p * ((deriv α p.1 : ℝ) : ℂ) + B p * ((α p.1 : ℝ) : ℂ) with hHdef
  set g : ℝ → ℂ := fun s => ∫ x in S, H (x, s) with hgdef
  have hH : ∀ M, IntegrableOn H (S ×ˢ ex ps M) := by
    intro M
    have hsub : S ×ˢ ex ps M ⊆ ex pa (max N0 M) ×ˢ ex ps (max N0 M) :=
      prod_mono (ex_mono pa (le_max_left _ _)) (ex_mono ps (le_max_right _ _))
    have hK : IsCompact (S ×ˢ ex ps M) := (isCompact_ex pa N0).prod (isCompact_ex ps M)
    have h1 := ((hA _).mono_set hsub).mul_continuousOn
      (Complex.continuous_ofReal.comp (hdc.comp continuous_fst)).continuousOn hK
    have h2 := ((hB _).mono_set hsub).mul_continuousOn
      (Complex.continuous_ofReal.comp (hαc.comp continuous_fst)).continuousOn hK
    exact h1.add h2
  have hgint : ∀ M, IntegrableOn g (ex ps M) := by
    intro M
    have h := hH M
    unfold IntegrableOn at h
    rw [restrict_prod_eq'] at h
    exact h.integral_prod_right
  have hloc : LocallyIntegrableOn g (dom ps) := by
    rw [locallyIntegrableOn_iff (isOpen_dom ps).isLocallyClosed]
    intro k hk hkc
    obtain ⟨M, hM⟩ := exists_ex_of_compact ps hkc hk
    exact (hgint M).mono_set hM
  have hmom : ∀ β : ℝ → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ dom ps →
      ∫ s, β s • g s = 0 := by
    intro β hβ hβc hβs
    obtain ⟨N1, hN1⟩ := exists_ex_of_compact ps hβc hβs
    set T := ex ps N1 with hTdef
    have hβcont : Continuous β := hβ.continuous
    have hSN : S ⊆ ex pa (max N0 N1) := ex_mono pa (le_max_left _ _)
    have hTN : T ⊆ ex ps (max N0 N1) := ex_mono ps (le_max_right _ _)
    have hKT : IsCompact (S ×ˢ T) := (isCompact_ex pa N0).prod (isCompact_ex ps N1)
    have hint : IntegrableOn (fun p : ℝ × ℝ => ((β p.2 : ℝ) : ℂ) * H p) (S ×ˢ T) :=
      IntegrableOn.continuousOn_mul (Complex.continuous_ofReal.comp (hβcont.comp continuous_snd)).continuousOn
        (hH N1) hKT
    have step1 : ∫ s, β s • g s = ∫ s in T, ∫ x in S, ((β s : ℝ) : ℂ) * H (x, s) := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := T) (fun s hs => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hs (hN1 h)), zero_smul])]
      refine setIntegral_congr_fun (measurableSet_ex ps N1) fun s _ => ?_
      simp only [hgdef, Complex.real_smul]
      exact (integral_const_mul _ _).symm
    have step2 : ∫ s in T, ∫ x in S, ((β s : ℝ) : ℂ) * H (x, s) =
        ∫ p in S ×ˢ T, ((β p.2 : ℝ) : ℂ) * H p := by
      have h := hint
      unfold IntegrableOn at h
      rw [restrict_prod_eq'] at h ⊢
      exact (integral_prod_symm _ h).symm
    have step3 : ∫ p in S ×ˢ T, ((β p.2 : ℝ) : ℂ) * H p = ∫ p, ((β p.2 : ℝ) : ℂ) * H p := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_
      rw [mem_prod, not_and_or] at hp
      rcases hp with h | h
      · have h1 : α p.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h' => h (hN0 h'))
        have h2 : deriv α p.1 = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h' => h (hN0 (tsupport_deriv_subset h')))
        simp [hHdef, h1, h2]
      · rw [image_eq_zero_of_notMem_tsupport (fun h' => h (hN1 h'))]
        simp
    have step4 : ∫ p, ((β p.2 : ℝ) : ℂ) * H p =
        (∫ p, ((deriv α p.1 * β p.2 : ℝ) : ℂ) * A p) + ∫ p, ((α p.1 * β p.2 : ℝ) : ℂ) * B p := by
      rw [← integral_add
        (integrable_test_mul hA hdc hβcont (tsupport_deriv_subset.trans (hN0.trans hSN)) (hN1.trans hTN))
        (integrable_test_mul hB hαc hβcont (hN0.trans hSN) (hN1.trans hTN))]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      simp only [hHdef]
      push_cast
      ring
    rw [step1, step2, step3, step4, hw α β hα ⟨hβ, hβc, hβs⟩, neg_add_cancel]
  have hzero := (isOpen_dom ps).ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hmom
  filter_upwards [hzero] with s hs hsd hAs hBs
  have e := hs hsd
  have i1 : IntegrableOn (fun x => A (x, s) * ((deriv α x : ℝ) : ℂ)) S :=
    (hAs N0).mul_continuousOn (Complex.continuous_ofReal.comp hdc).continuousOn (isCompact_ex pa N0)
  have i2 : IntegrableOn (fun x => B (x, s) * ((α x : ℝ) : ℂ)) S :=
    (hBs N0).mul_continuousOn (Complex.continuous_ofReal.comp hαc).continuousOn (isCompact_ex pa N0)
  have e2 : g s = (∫ x in S, A (x, s) * ((deriv α x : ℝ) : ℂ)) + ∫ x in S, B (x, s) * ((α x : ℝ) : ℂ) :=
    integral_add i1 i2
  rw [integral_eq_setIntegral_of_tsupport (tsupport_deriv_subset.trans hN0),
    integral_eq_setIntegral_of_tsupport hN0]
  linear_combination e2.symm.trans e

lemma ae_slice_weak (pa ps : Bool) {A B : ℝ × ℝ → ℂ}
    (hA : ∀ N, IntegrableOn A (ex pa N ×ˢ ex ps N)) (hB : ∀ N, IntegrableOn B (ex pa N ×ˢ ex ps N))
    (hw : ∀ α β, IsAdm pa α → IsAdm ps β →
      ∫ p, ((deriv α p.1 * β p.2 : ℝ) : ℂ) * A p = -∫ p, ((α p.1 * β p.2 : ℝ) : ℂ) * B p) :
    ∀ᵐ s, s ∈ dom ps →
      (∀ N, IntegrableOn (fun x => A (x, s)) (ex pa N) ∧ IntegrableOn (fun x => B (x, s)) (ex pa N)) ∧
      ∀ α, IsAdm pa α → ∫ x, A (x, s) * ((deriv α x : ℝ) : ℂ) = -∫ x, B (x, s) * ((α x : ℝ) : ℂ) := by
  obtain ⟨D, hDc, hDa, hdense⟩ := countable_dense_tests pa
  have hall : ∀ᵐ s, ∀ α ∈ D, s ∈ dom ps → (∀ N, IntegrableOn (fun x => A (x, s)) (ex pa N)) →
      (∀ N, IntegrableOn (fun x => B (x, s)) (ex pa N)) →
      ∫ x, A (x, s) * ((deriv α x : ℝ) : ℂ) = -∫ x, B (x, s) * ((α x : ℝ) : ℂ) :=
    (ae_ball_iff hDc).2 fun α hα => ae_slice_identity pa ps hA hB hw (hDa α hα)
  filter_upwards [ae_slices pa ps hA, ae_slices pa ps hB, hall] with s hsA hsB hs hsd
  have hint : ∀ N, IntegrableOn (fun x => A (x, s)) (ex pa N) ∧ IntegrableOn (fun x => B (x, s)) (ex pa N) :=
    fun N => ⟨hsA hsd N, hsB hsd N⟩
  exact ⟨hint, hdense _ _ hint (fun α hα => hs α hα hsd (hsA hsd) (hsB hsd))⟩

lemma weak_of_slice (b : Bool) {F Fd : ℝ → ℂ}
    (hint : ∀ N, IntegrableOn F (ex b N) ∧ IntegrableOn Fd (ex b N))
    (hid : ∀ α, IsAdm b α → ∫ x, F x * ((deriv α x : ℝ) : ℂ) = -∫ x, Fd x * ((α x : ℝ) : ℂ))
    {lo hi : ℝ} (hsub : Icc lo hi ⊆ dom b) : Bridge.HasWeakDerivOn F Fd lo hi := by
  obtain ⟨N, hN⟩ := exists_ex_of_compact b isCompact_Icc hsub
  have hIoo : Ioo lo hi ⊆ ex b N := Ioo_subset_Icc_self.trans hN
  refine ⟨(hint N).1.mono_set hIoo, (hint N).2.mono_set hIoo, fun ψ hψ hψc hψs => ?_⟩
  have hadm : IsAdm b ψ := ⟨hψ, hψc, hψs.trans (Ioo_subset_Icc_self.trans hsub)⟩
  rw [← integral_eq_setIntegral_of_tsupport (tsupport_deriv_subset.trans hψs),
    ← integral_eq_setIntegral_of_tsupport hψs]
  exact hid ψ hadm

section Application

open CellCert.CellFormula CellCert.CellAnalysis SteadyCert

lemma integrableOn_of_weighted {f K : ℝ × ℝ → ℂ} (c : ℂ)
    (hK : ∀ R Z : ℝ, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * K p) (Icc 0 R ×ˢ Icc (-Z) Z))
    (heq : ∀ p : ℝ × ℝ, f p = c * K p) {a R Z : ℝ} (ha : 0 < a) :
    IntegrableOn f (Icc a R ×ˢ Icc (-Z) Z) := by
  have hsub : Icc a R ×ˢ Icc (-Z) Z ⊆ Icc 0 R ×ˢ Icc (-Z) Z :=
    prod_mono (Icc_subset_Icc ha.le le_rfl) subset_rfl
  have hcont : ContinuousOn (fun p : ℝ × ℝ => c * ((p.1 : ℂ))⁻¹) (Icc a R ×ˢ Icc (-Z) Z) := by
    refine continuousOn_const.mul
      (ContinuousOn.inv₀ (Complex.continuous_ofReal.comp continuous_fst).continuousOn fun p hp => ?_)
    exact_mod_cast (ha.trans_le hp.1.1).ne'
  have h := IntegrableOn.continuousOn_mul hcont ((hK R Z).mono_set hsub) (isCompact_Icc.prod isCompact_Icc)
  refine h.congr_fun (fun p hp => ?_) (measurableSet_Icc.prod measurableSet_Icc)
  have hp0 : (p.1 : ℂ) ≠ 0 := by exact_mod_cast (ha.trans_le hp.1.1).ne'
  rw [heq p]
  field_simp

lemma locInt_of_near {Q : Space → Space} (hQ : IsSquareIntegrableNear Q) : LocallyIntegrable Q volume := by
  refine FracInternal.MeshDataAffineModes.locInt_of_sq hQ.1 fun K hK => ?_
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine IntegrableOn.mono_set ?_ hR
  refine ⟨(hQ.1.norm.pow 2).restrict, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => by simp only [Pi.zero_apply]; positivity)]
  exact hQ.2 R

lemma pres_box {Q : Space → Space} {q : Space → ℝ} (hq : IsPotentialOf Q q) (m : ℕ) (n : ℤ) {a R Z : ℝ}
    (ha : 0 < a) : IntegrableOn (fun p : ℝ × ℝ => presMode m n q p.1 p.2) (Icc a R ×ˢ Icc (-Z) Z) :=
  integrableOn_of_weighted (1 / (2 * Real.pi) : ℂ)
    (fun R Z => FracInternal.ModeHeightAxis.weighted_int R Z (FracInternal.MeshDataAffineModes.pot_locInt hq)
      (FracInternal.MeshDataAffineModes.presKernel m n) (FracInternal.MeshDataAffineModes.presKernel_cont m n)
      (FracInternal.MeshDataAffineModes.presKernel_bound m n))
    (fun p => by
      rw [FracInternal.MeshDataAffineModes.presMode_k,
        FracInternal.MeshDataAffineModes.mode_ioo _ (FracInternal.MeshDataAffineModes.presKernel_per m n)]) ha

lemma vec_box {Q : Space → Space} (hQ : IsSquareIntegrableNear Q) (m : ℕ) (n : ℤ) (j : Fin 3) {a R Z : ℝ}
    (ha : 0 < a) : IntegrableOn (fun p : ℝ × ℝ => modeVec m n Q p.1 p.2 j) (Icc a R ×ˢ Icc (-Z) Z) :=
  integrableOn_of_weighted (1 / (2 * Real.pi) : ℂ)
    (fun R Z => FracInternal.ModeHeightAxis.weighted_int R Z (locInt_of_near hQ)
      (LowEntry.Internal.velKernel m n j) (LowEntry.Internal.velKernel_cont m n j)
      (LowEntry.Internal.velKernel_bound m n j))
    (fun p => LowEntry.Internal.modeVec_eq m n Q j p) ha

lemma plane_weak {Q : Space → Space} {q : Space → ℝ} (hq : IsPotentialOf Q q) (hQ : IsSquareIntegrableNear Q)
    (m : ℕ) (n : ℤ) (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    (∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * presMode m n q p.1 p.2 =
      -∫ p, ((ψ p : ℝ) : ℂ) * modeVec m n Q p.1 p.2 0) ∧
    (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * presMode m n q p.1 p.2 =
      -∫ p, ((ψ p : ℝ) : ℂ) * modeVec m n Q p.1 p.2 2) := by
  have hQloc := locInt_of_near hQ
  have hqloc := FracInternal.MeshDataAffineModes.pot_locInt hq
  have hg : ∀ j : Fin 3, LocallyIntegrable (fun y => (innerSL ℝ (Q y) : Space →L[ℝ] ℝ) (unitVector j)) volume := by
    intro j
    refine (locallyIntegrable_iff).2 fun K hK => ?_
    refine Integrable.mono' ((hQloc.integrableOn_isCompact hK).norm.mul_const ‖unitVector j‖) ?_
      (Eventually.of_forall fun y => ?_)
    · simp only [innerSL_apply_apply]
      exact (hQloc.aestronglyMeasurable.inner aestronglyMeasurable_const).restrict
    · simp only [innerSL_apply_apply]
      exact norm_inner_le_norm _ _
  obtain ⟨h1, h2⟩ := cylModeWeak ℝ q (fun y => innerSL ℝ (Q y)) hqloc hg
    (fun φ hφ j => by simpa only [smul_eq_mul, innerSL_apply_apply] using hq.2.2 φ hφ j)
    (fun _ => ContinuousLinearMap.id ℝ ℝ) contDiff_const m n ψ hψ hc hpos
  have eA : ∀ p : ℝ × ℝ, presMode m n q p.1 p.2 = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        ((ContinuousLinearMap.id ℝ ℝ) (q (cylPoint p.1 θ p.2)) : ℂ) := fun p => rfl
  have eR : ∀ p : ℝ × ℝ, modeVec m n Q p.1 p.2 0 = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        ((ContinuousLinearMap.id ℝ ℝ) ((innerSL ℝ (Q (cylPoint p.1 θ p.2))) (radialUnit θ)) : ℂ) :=
    fun p => rfl
  have eZ : ∀ p : ℝ × ℝ, modeVec m n Q p.1 p.2 2 = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        ((ContinuousLinearMap.id ℝ ℝ) ((innerSL ℝ (Q (cylPoint p.1 θ p.2))) axialUnit) : ℂ) :=
    fun p => rfl
  simp only [eA, eR, eZ, mul_left_comm _ ((1 / (2 * Real.pi) : ℂ)), integral_const_mul]
  exact ⟨by rw [h1]; ring, by rw [h2]; ring⟩

lemma fderiv_test_fst {α β : ℝ → ℝ} (hα : Differentiable ℝ α) (hβ : Differentiable ℝ β) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => α q.1 * β q.2) p (1, 0) = deriv α p.1 * β p.2 := by
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => α q.1 * β q.2) (p.1, p.2) :=
    ((hα _).comp _ differentiableAt_fst).mul ((hβ _).comp _ differentiableAt_snd)
  have hc : HasDerivAt (fun t : ℝ => (t, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have h2 : HasDerivAt ((fun q : ℝ × ℝ => α q.1 * β q.2) ∘ fun t : ℝ => (t, p.2))
      (fderiv ℝ (fun q : ℝ × ℝ => α q.1 * β q.2) (p.1, p.2) (1, 0)) p.1 :=
    hd.hasFDerivAt.comp_hasDerivAt p.1 hc
  exact h2.unique ((hα p.1).hasDerivAt.mul_const (β p.2))

lemma fderiv_test_snd {α β : ℝ → ℝ} (hα : Differentiable ℝ α) (hβ : Differentiable ℝ β) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => α q.1 * β q.2) p (0, 1) = α p.1 * deriv β p.2 := by
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => α q.1 * β q.2) (p.1, p.2) :=
    ((hα _).comp _ differentiableAt_fst).mul ((hβ _).comp _ differentiableAt_snd)
  have hc : HasDerivAt (fun t : ℝ => (p.1, t)) ((0 : ℝ), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have h2 : HasDerivAt ((fun q : ℝ × ℝ => α q.1 * β q.2) ∘ fun t : ℝ => (p.1, t))
      (fderiv ℝ (fun q : ℝ × ℝ => α q.1 * β q.2) (p.1, p.2) (0, 1)) p.2 :=
    hd.hasFDerivAt.comp_hasDerivAt p.2 hc
  exact h2.unique ((hβ p.2).hasDerivAt.const_mul (α p.1))

lemma prod_test_facts {α β : ℝ → ℝ} (hα : ContDiff ℝ ∞ α) (hαc : HasCompactSupport α) (hβ : ContDiff ℝ ∞ β)
    (hβc : HasCompactSupport β) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ => α q.1 * β q.2) ∧ HasCompactSupport (fun q : ℝ × ℝ => α q.1 * β q.2) ∧
      tsupport (fun q : ℝ × ℝ => α q.1 * β q.2) ⊆ tsupport α ×ˢ tsupport β := by
  have hsub : tsupport (fun q : ℝ × ℝ => α q.1 * β q.2) ⊆ tsupport α ×ˢ tsupport β := by
    intro p hp
    have h1 : p ∈ tsupport (α ∘ Prod.fst) := tsupport_mul_subset_left hp
    have h2 : p ∈ tsupport (β ∘ Prod.snd) := tsupport_mul_subset_right hp
    exact ⟨tsupport_comp_subset_preimage α continuous_fst h1, tsupport_comp_subset_preimage β continuous_snd h2⟩
  exact ⟨(hα.comp contDiff_fst).mul (hβ.comp contDiff_snd),
    IsCompact.of_isClosed_subset (IsCompact.prod hαc hβc) (isClosed_tsupport _) hsub, hsub⟩

end Application

end Internal.PressureMode

section Main

open Internal.PressureMode CellCert.CellFormula CellCert.CellAnalysis

theorem pressureModeDeriv : PressureModeDerivHolds := by
  intro m Q q _ hq hQ n
  have hA : ∀ N, IntegrableOn (fun p : ℝ × ℝ => presMode m n q p.1 p.2) (ex true N ×ˢ ex false N) :=
    fun N => by
      simp only [ex, ↓reduceIte, Bool.false_eq_true]
      exact pres_box hq m n (by positivity)
  have hB : ∀ (j : Fin 3) (N : ℕ),
      IntegrableOn (fun p : ℝ × ℝ => modeVec m n Q p.1 p.2 j) (ex true N ×ˢ ex false N) :=
    fun j N => by
      simp only [ex, ↓reduceIte, Bool.false_eq_true]
      exact vec_box hQ m n j (by positivity)
  refine ⟨?_, ?_⟩
  · have hw : ∀ α β, IsAdm true α → IsAdm false β →
        ∫ p : ℝ × ℝ, ((deriv α p.1 * β p.2 : ℝ) : ℂ) * presMode m n q p.1 p.2 =
          -∫ p : ℝ × ℝ, ((α p.1 * β p.2 : ℝ) : ℂ) * modeVec m n Q p.1 p.2 0 := by
      intro α β hα hβ
      obtain ⟨hs, hsc, hsub⟩ := prod_test_facts hα.1 hα.2.1 hβ.1 hβ.2.1
      have hpos : ∀ p ∈ tsupport (fun q : ℝ × ℝ => α q.1 * β q.2), 0 < p.1 := fun p hp => by
        have h0 := hα.2.2 (hsub hp).1
        simpa [dom] using h0
      have h := (plane_weak hq hQ m n _ hs hsc hpos).1
      simp only [fderiv_test_fst (hα.1.differentiable (by simp)) (hβ.1.differentiable (by simp))] at h
      exact h
    have h := ae_slice_weak true false hA (hB 0) hw
    filter_upwards [h] with z hz lo hi hlo hlohi
    obtain ⟨hint, hid⟩ := hz (by simp [dom])
    exact weak_of_slice true hint hid (fun x hx => by
      simp only [dom, ↓reduceIte, mem_Ioi]
      linarith [hx.1])
  · have hA' : ∀ N, IntegrableOn (fun p : ℝ × ℝ => presMode m n q p.2 p.1) (ex false N ×ˢ ex true N) :=
      fun N => by
        have h := hA N
        rw [Measure.volume_eq_prod] at h ⊢
        exact h.swap
    have hB' : ∀ N, IntegrableOn (fun p : ℝ × ℝ => modeVec m n Q p.2 p.1 2) (ex false N ×ˢ ex true N) :=
      fun N => by
        have h := hB 2 N
        rw [Measure.volume_eq_prod] at h ⊢
        exact h.swap
    have hw : ∀ α β, IsAdm false α → IsAdm true β →
        ∫ p : ℝ × ℝ, ((deriv α p.1 * β p.2 : ℝ) : ℂ) * presMode m n q p.2 p.1 =
          -∫ p : ℝ × ℝ, ((α p.1 * β p.2 : ℝ) : ℂ) * modeVec m n Q p.2 p.1 2 := by
      intro α β hα hβ
      obtain ⟨hs, hsc, hsub⟩ := prod_test_facts hβ.1 hβ.2.1 hα.1 hα.2.1
      have hpos : ∀ p ∈ tsupport (fun q : ℝ × ℝ => β q.1 * α q.2), 0 < p.1 := fun p hp => by
        have h0 := hβ.2.2 (hsub hp).1
        simpa [dom] using h0
      have h := (plane_weak hq hQ m n _ hs hsc hpos).2
      simp only [fderiv_test_snd (hβ.1.differentiable (by simp)) (hα.1.differentiable (by simp))] at h
      have s1 := integral_prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (fun p : ℝ × ℝ => ((β p.1 * deriv α p.2 : ℝ) : ℂ) * presMode m n q p.1 p.2)
      have s2 := integral_prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (fun p : ℝ × ℝ => ((β p.1 * α p.2 : ℝ) : ℂ) * modeVec m n Q p.1 p.2 2)
      simp only [Prod.fst_swap, Prod.snd_swap, ← Measure.volume_eq_prod] at s1 s2
      simp_rw [mul_comm (deriv α _) (β _), mul_comm (α _) (β _)]
      rw [s1, s2]
      exact h
    have h := ae_slice_weak false true hA' hB' hw
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    filter_upwards [h] with r hr hr0 zlo zhi _
    obtain ⟨hint, hid⟩ := hr (by simpa [dom] using hr0)
    exact weak_of_slice false hint hid (by simp [dom])

end Main

end SideTrace

end CertCell

end Breakdown
