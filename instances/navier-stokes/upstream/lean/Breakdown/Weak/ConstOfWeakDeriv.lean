import Breakdown.Weak.StatementsTime

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

namespace Internal

theorem exists_Ioo_cover {K : Set ℝ} {l r : ℝ} (hlr : l < r) (hK : IsCompact K)
    (hKs : K ⊆ Ioo l r) : ∃ p q, l < p ∧ q < r ∧ K ⊆ Ioo p q := by
  rcases K.eq_empty_or_nonempty with h | hne
  · exact ⟨(l + r) / 2, (l + r) / 2, by linarith, by linarith, by simp [h]⟩
  · have h1 := hKs (hK.sInf_mem hne)
    have h2 := hKs (hK.sSup_mem hne)
    refine ⟨(l + sInf K) / 2, (sSup K + r) / 2, by linarith [h1.1], by linarith [h2.2], ?_⟩
    intro x hx
    have a1 := csInf_le hK.bddBelow hx
    have a2 := le_csSup hK.bddAbove hx
    constructor <;> linarith [h1.1, h2.2]

theorem integral_Ici_deriv {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (τ : ℝ) : ∫ t in Ici τ, deriv θ t = -θ τ := by
  rw [integral_Ici_eq_integral_Ioi]
  have hd : ∀ x, HasDerivAt θ (deriv θ x) x := fun x =>
    ((hθ.differentiable (by simp)) x).hasDerivAt
  have hi : Integrable (deriv θ) :=
    (hθ.continuous_deriv (by simp)).integrable_of_hasCompactSupport hθc.deriv
  have ht : Tendsto θ atTop (𝓝 0) := hθc.is_zero_at_infty.mono_left atTop_le_cocompact
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hθ.continuous.continuousWithinAt
    (fun x _ => hd x) hi.integrableOn ht]
  ring

theorem integral_deriv_mul_primitive {θ bt : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθc : HasCompactSupport θ) (hb : Integrable bt) (l : ℝ) (hbl : ∀ τ, τ ≤ l → bt τ = 0) :
    ∫ t, deriv θ t * ∫ τ in l..t, bt τ = -∫ t, θ t * bt t := by
  have hprim : ∀ t, ∫ τ in l..t, bt τ = ∫ τ in Iic t, bt τ := by
    intro t
    rw [← intervalIntegral.integral_Iic_sub_Iic hb.integrableOn hb.integrableOn,
      setIntegral_eq_zero_of_forall_eq_zero (t := Iic l) (fun x hx => hbl x hx), sub_zero]
  have hi : Integrable (deriv θ) :=
    (hθ.continuous_deriv (by simp)).integrable_of_hasCompactSupport hθc.deriv
  set f : ℝ × ℝ → ℝ := Set.indicator {p : ℝ × ℝ | p.2 ≤ p.1}
    (fun p => deriv θ p.1 * bt p.2) with hf
  have hfi : Integrable f (volume.prod volume) :=
    (hi.mul_prod hb).indicator (measurableSet_le measurable_snd measurable_fst)
  have e1 : ∀ t, deriv θ t * ∫ τ in l..t, bt τ = ∫ τ, f (t, τ) := by
    intro t
    rw [hprim, ← integral_const_mul, ← integral_indicator measurableSet_Iic]
    congr 1
  have e2 : ∀ τ, ∫ t, f (t, τ) = -(θ τ * bt τ) := by
    intro τ
    have : (fun t => f (t, τ)) = Set.indicator (Ici τ) (fun t => deriv θ t * bt τ) := by
      funext t
      simp only [hf, Set.indicator_apply, mem_ofPred_eq, mem_Ici]
    rw [this, integral_indicator measurableSet_Ici, integral_mul_const, integral_Ici_deriv hθ hθc]
    ring
  simp_rw [e1]
  rw [integral_integral_swap (f := fun t τ => f (t, τ)) hfi]
  simp_rw [e2]
  rw [integral_neg]

theorem primitive_test {k : ℝ → ℝ} {l r p q : ℝ} (hk : ContDiff ℝ ∞ k) (hlp : l < p)
    (hqr : q < r) (hks : ∀ x, x ∉ Ioo p q → k x = 0) (hk0 : ∫ x, k x = 0) :
    ContDiff ℝ ∞ (fun t => ∫ s in l..t, k s) ∧ HasCompactSupport (fun t => ∫ s in l..t, k s) ∧
      tsupport (fun t => ∫ s in l..t, k s) ⊆ Ioo l r ∧
      deriv (fun t => ∫ s in l..t, k s) = k := by
  have hkc := hk.continuous
  have hd : ∀ t, HasDerivAt (fun t => ∫ s in l..t, k s) (k t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hkc.intervalIntegrable _ _)
      hkc.aestronglyMeasurable.stronglyMeasurableAtFilter hkc.continuousAt
  have hder : deriv (fun t => ∫ s in l..t, k s) = k := funext fun t => (hd t).deriv
  have hz : ∀ t, t ∉ Icc p q → ∫ s in l..t, k s = 0 := by
    intro t ht
    rcases le_or_gt t p with htp | htp
    · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
      intro x hx
      apply hks
      intro hx'
      rcases Set.mem_uIcc.1 hx with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith [hx'.1]
    · have hqt : q < t := by
        by_contra h
        exact ht ⟨htp.le, not_lt.1 h⟩
      rw [intervalIntegral.integral_of_le (by linarith),
        setIntegral_eq_integral_of_forall_compl_eq_zero, hk0]
      intro x hx
      apply hks
      intro hx'
      exact hx ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  refine ⟨contDiff_infty_iff_deriv.2 ⟨fun t => (hd t).differentiableAt, by rw [hder]; exact hk⟩,
    HasCompactSupport.intro isCompact_Icc hz, ?_, hder⟩
  exact (closure_minimal (Function.support_subset_iff'.2 hz) isClosed_Icc).trans
    (Icc_subset_Ioo hlp hqr)

end Internal

open Internal

theorem constOfWeakDeriv_holds : ConstOfWeakDeriv := by
  intro a b l r hlr ha hb hab
  set at' : ℝ → ℝ := Set.indicator (Ioo l r) a with hat
  set bt : ℝ → ℝ := Set.indicator (Ioo l r) b with hbt
  have hai : Integrable at' := ha.integrable_indicator measurableSet_Ioo
  have hbi : Integrable bt := hb.integrable_indicator measurableSet_Ioo
  have hbl : ∀ τ, τ ≤ l → bt τ = 0 := fun τ hτ =>
    Set.indicator_of_notMem (fun h => by linarith [h.1]) _
  set F : ℝ → ℝ := fun t => ∫ τ in l..t, bt τ with hF
  have hFc : Continuous F :=
    intervalIntegral.continuous_primitive (fun _ _ => hbi.intervalIntegrable) l
  have zero_out : ∀ θ : ℝ → ℝ, tsupport θ ⊆ Ioo l r → ∀ t, t ∉ Ioo l r → θ t = 0 :=
    fun θ h t ht => image_eq_zero_of_notMem_tsupport (fun h' => ht (h h'))
  have int_A : ∀ φ : ℝ → ℝ, Continuous φ → HasCompactSupport φ →
      Integrable (fun t => φ t * (at' t + F t)) := by
    intro φ hφ hφc
    obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
    have h1 : Integrable (fun t => φ t * at' t) :=
      hai.bdd_mul hφ.aestronglyMeasurable (Eventually.of_forall hC)
    have h2 : Integrable (fun t => φ t * F t) :=
      (hφ.mul hFc).integrable_of_hasCompactSupport hφc.mul_right
    refine (h1.add h2).congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, mul_add]
  have eq_ab : ∀ φ : ℝ → ℝ, tsupport φ ⊆ Ioo l r → ∀ t,
      φ t * at' t = φ t * a t ∧ φ t * bt t = φ t * b t := by
    intro φ hφ t
    by_cases ht : t ∈ Ioo l r
    · rw [hat, hbt, Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      exact ⟨rfl, rfl⟩
    · rw [zero_out φ hφ t ht]
      simp
  have key : ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ Ioo l r →
      ∫ t, deriv θ t * (at' t + F t) = 0 := by
    intro θ hθ hθc hθs
    have hdc : Continuous (deriv θ) := hθ.continuous_deriv (by simp)
    have hds : tsupport (deriv θ) ⊆ Ioo l r := tsupport_deriv_subset.trans hθs
    obtain ⟨C, hC⟩ := hdc.bounded_above_of_compact_support hθc.deriv
    have h1i : Integrable (fun t => deriv θ t * at' t) :=
      hai.bdd_mul hdc.aestronglyMeasurable (Eventually.of_forall hC)
    have h2i : Integrable (fun t => deriv θ t * F t) :=
      (hdc.mul hFc).integrable_of_hasCompactSupport hθc.deriv.mul_right
    simp_rw [mul_add]
    rw [integral_add h1i h2i]
    have h1 : ∫ t, deriv θ t * at' t = ∫ t, θ t * b t := by
      rw [← hab θ hθ hθc hθs]
      congr 1
      funext t
      exact (eq_ab _ hds t).1
    have h2 : ∫ t, deriv θ t * F t = -∫ t, θ t * b t := by
      refine (integral_deriv_mul_primitive hθ hθc hbi l hbl).trans ?_
      congr 2
      funext t
      exact (eq_ab θ hθs t).2
    rw [h1, h2]
    ring
  let B : ContDiffBump ((l + r) / 2 : ℝ) :=
    ContDiffBump.mk ((r - l) / 8) ((r - l) / 4) (by linarith) (by linarith)
  have hBr : B.rOut = (r - l) / 4 := rfl
  have h0c : ContDiff ℝ ∞ (B.normed volume) := B.contDiff_normed
  have h0k : HasCompactSupport (B.normed volume) := B.hasCompactSupport_normed
  have h0s : tsupport (B.normed volume) ⊆ Ioo l r := by
    rw [B.tsupport_normed_eq, Real.closedBall_eq_Icc, hBr]
    intro x hx
    constructor
    · linarith [hx.1]
    · linarith [hx.2]
  have h01 : ∫ t, B.normed volume t = 1 := B.integral_normed
  set θ₀ : ℝ → ℝ := B.normed volume with hθ₀
  set c : ℝ := ∫ t, θ₀ t * (at' t + F t) with hc
  refine ⟨c, ?_⟩
  have hloc : LocallyIntegrableOn (fun t => at' t + F t - c) (Ioo l r) volume := by
    have : LocallyIntegrable (fun t => at' t + F t - c) volume :=
      (hai.locallyIntegrable.add hFc.locallyIntegrable).sub
        (continuous_const (y := c)).locallyIntegrable
    exact this.locallyIntegrableOn _
  have hz := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
  · rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hz] with t ht hmem
    have h := ht hmem
    have ea : at' t = a t := Set.indicator_of_mem hmem _
    have eF : F t = ∫ τ in l..t, b τ := by
      simp only [hF]
      rw [intervalIntegral.integral_of_le hmem.1.le, intervalIntegral.integral_of_le hmem.1.le]
      exact setIntegral_congr_fun measurableSet_Ioc
        (fun x hx => Set.indicator_of_mem (show x ∈ Ioo l r from ⟨hx.1, hx.2.trans_lt hmem.2⟩) _)
    rw [← ea, ← eF]
    linarith
  intro ψ hψ hψc hψs
  obtain ⟨p, q, hlp, hqr, hpq⟩ := exists_Ioo_cover hlr (hψc.isCompact.union h0k.isCompact)
    (union_subset hψs h0s)
  set I : ℝ := ∫ t, ψ t with hI
  have hψi : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hψc
  have h0i : Integrable θ₀ := h0c.continuous.integrable_of_hasCompactSupport h0k
  have hks : ∀ x, x ∉ Ioo p q → ψ x - I * θ₀ x = 0 := by
    intro x hx
    have e1 : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hpq (Or.inl h)))
    have e2 : θ₀ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hpq (Or.inr h)))
    rw [e1, e2]
    ring
  have hk0 : ∫ x, (ψ x - I * θ₀ x) = 0 := by
    rw [integral_sub hψi (h0i.const_mul I), integral_const_mul, h01]
    ring
  obtain ⟨hθ, hθc, hθs, hder⟩ := primitive_test (hψ.sub (contDiff_const.mul h0c)) hlp hqr hks hk0
  have hkey := key _ hθ hθc hθs
  simp only [hder] at hkey
  have e3 : ∫ t, (ψ t - I * θ₀ t) * (at' t + F t) = (∫ t, ψ t * (at' t + F t)) - I * c := by
    simp_rw [sub_mul, mul_assoc]
    rw [integral_sub (int_A ψ hψ.continuous hψc)
      ((int_A θ₀ h0c.continuous h0k).const_mul I), integral_const_mul]
  simp_rw [smul_eq_mul, mul_sub]
  rw [integral_sub (int_A ψ hψ.continuous hψc) (hψi.mul_const c), integral_mul_const]
  rw [e3] at hkey
  rw [← hI]
  linarith

end Breakdown.WeakProfile
