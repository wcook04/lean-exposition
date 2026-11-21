import TorusEuler.FiniteHierarchyConstruction

/-! Quantitative induction for the finite expansion of Theorem 5.6.
The norm inequalities for the two analytic solves, completion, and source
terms are inputs. The recurrence tracks their actual derivative orders and
frequency costs before deriving any correction-level output exponent. -/

namespace TorusEuler

/-- Norms of the profiles and sources, indexed by derivative order and level.
`osc` measures the oscillation plus frequency times its pressure. `Z`
is a budget for centered slow terms, taking the weighted oscillation
plus the unweighted mean, so it can supply either factor in the product. -/
structure HierarchyMeasuredLevels where
  oscSource : ℕ → ℕ → ℝ
  meanSource : ℕ → ℕ → ℝ
  osc : ℕ → ℕ → ℝ
  mean : ℕ → ℕ → ℝ
  completion : ℕ → ℕ → ℝ
  Y : ℕ → ℕ → ℝ
  Z : ℕ → ℕ → ℝ
  nonneg : ∀ n p, 0 ≤ oscSource n p ∧ 0 ≤ meanSource n p ∧
    0 ≤ osc n p ∧ 0 ≤ mean n p ∧ 0 ≤ completion n p ∧ 0 ≤ Y n p ∧ 0 ≤ Z n p

/-- The quadratic pairs contributing to the retained source at level `p`. -/
def hierarchyLevelPairs (P shift p : ℕ) : Finset (ℕ × ℕ) :=
  (hierarchyAdvectionPairs P shift).filter fun ij => hierarchyAdvectionLevel shift ij = p

private theorem hierarchyLevelPairs_spec {P shift p : ℕ} {ij : ℕ × ℕ}
    (hij : ij ∈ hierarchyLevelPairs P shift p) :
    shift + 1 ≤ ij.1 ∧ 1 ≤ ij.2 ∧ ij.1 + ij.2 = p + shift := by
  obtain ⟨hbox, hlevel⟩ := Finset.mem_filter.mp hij
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hbox
  rw [Finset.mem_Icc] at hi hj
  unfold hierarchyAdvectionLevel at hlevel
  exact ⟨hi.1, hj.1, by omega⟩

/-- The level-two parent residual may carry its own parent-scale factor. -/
noncomputable def hierarchyParentResidualConstant (K : ℝ) : Option ℝ → ℝ
  | none => K
  | some loss => K * loss

/-- The norm recurrence supplied by the analytic estimates. `K` bounds the
order-dependent constants up to order `H`, and `L` bounds each primitive
parent loss. The factor `freq ^ (3 / 2)` occurs only in the transverse fast
terms. In the mean source, phase integration by parts has removed it. -/
structure HierarchyNormRecurrence (s : HierarchyMeasuredLevels) (freq L K : ℝ) (P H : ℕ)
    (meanResidualLoss : Option ℝ := none) : Prop where
  seed : ∀ n ≤ H, s.osc n 1 ≤ K * L * freq ^ hierarchyOscExponent 1
  seedZeros : ∀ n, s.oscSource n 1 = 0 ∧ s.meanSource n 1 = 0 ∧
    s.mean n 1 = 0 ∧ s.completion n 0 = 0
  meanForcing : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P,
    s.meanSource n p ≤ K * L *
      (∑ ij ∈ hierarchyLevelPairs P 0 p,
        (s.Y (n + 1) ij.1 * s.Y (n + 1) ij.2 +
          s.osc (n + 1) ij.1 * s.Y (n + 1) ij.2 +
          s.mean (n + 1) ij.1 * s.mean (n + 1) ij.2)) +
      (if p = 2 then hierarchyParentResidualConstant K meanResidualLoss * freq ^ hierarchyMeanExponent 2 else 0)
  meanSolve : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P,
    s.mean n p ≤ K * L * s.meanSource (n + 1) p
  oscForcing : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P,
    s.oscSource n p ≤ K * L *
      (freq ^ (-1 : ℝ) * (s.osc (n + 1) (p - 1) + s.oscSource (n + 1) (p - 1)) +
      (∑ ij ∈ hierarchyLevelPairs P 0 p, s.Z (n + 1) ij.1 * s.Z (n + 1) ij.2) +
      freq ^ (3 / 2 : ℝ) * (∑ ij ∈ hierarchyLevelPairs P 1 p,
        (s.completion n (ij.1 - 1) * s.Y (n + 1) ij.2 +
          s.mean n ij.1 * s.Y (n + 1) ij.2)))
  oscSolve : ∀ n ≤ H, ∀ p ∈ Finset.Icc 2 P, s.osc n p ≤ K * L * s.oscSource n p
  complete : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 1 P,
    s.completion n p ≤ K * L * freq ^ (-1 : ℝ) * s.osc (n + 1) p
  Ybound : ∀ n ≤ H, ∀ p ∈ Finset.Icc 1 P,
    s.Y n p ≤ s.osc n p + s.completion n (p - 1)
  Zbound : ∀ n ≤ H, ∀ p ∈ Finset.Icc 1 P, s.Z n p ≤ s.Y n p + s.mean n p

/-- The propagated and reconstructed bounds at one derivative order and
level. In particular, the source and the mean used as next-level inputs
carry no parent loss. -/
structure HierarchyLevelBound (s : HierarchyMeasuredLevels) (freq L A : ℝ) (n p : ℕ) : Prop where
  oscSource : s.oscSource n p ≤ A * freq ^ hierarchyOscExponent p
  meanSource : s.meanSource n p ≤ A * L ^ 5 * freq ^ hierarchyMeanExponent p
  osc : s.osc n p ≤ A * L * freq ^ hierarchyOscExponent p
  mean : s.mean n p ≤ A * freq ^ hierarchyInductiveMeanExponent p
  meanStrong : s.mean n p ≤ A * L ^ 6 * freq ^ hierarchyMeanExponent p
  completion : s.completion n p ≤ A * L ^ 2 * freq ^ hierarchyCompletionExponent p
  Y : s.Y n p ≤ A * L ^ 2 * freq ^ hierarchyOscExponent p
  Z : s.Z n p ≤ A * L ^ 2 * freq ^ hierarchyOscExponent p

private theorem bound_mul {freq L a b x y u v : ℝ} {i j : ℕ}
    (hf : 0 < freq) (ha : 0 ≤ a) (hL : 0 ≤ L) (hy : 0 ≤ y)
    (hx : x ≤ a * L ^ i * freq ^ u) (hy' : y ≤ b * L ^ j * freq ^ v) :
    x * y ≤ (a * b) * L ^ (i + j) * freq ^ (u + v) := by
  refine (mul_le_mul hx hy' hy (by positivity)).trans_eq ?_
  rw [pow_add, Real.rpow_add hf]
  ring

private theorem factor_absorb {freq L a e gap : ℝ} {i : ℕ}
    (hf : 1 ≤ freq) (hL : 1 ≤ L) (ha : 0 ≤ a)
    (hs : L ^ 6 * freq ^ (-1 / 12 : ℝ) ≤ 1)
    (hi : i ≤ 6) (hg : 1 / 12 ≤ gap) :
    a * L ^ i * freq ^ (e - gap) ≤ a * freq ^ e := by
  have hpow : L ^ i * freq ^ (-1 / 12 : ℝ) ≤ 1 := by
    refine (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL hi) ?_).trans hs
    exact Real.rpow_nonneg (zero_le_one.trans hf) _
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (hierarchy_absorb_parent_loss hf (pow_nonneg (zero_le_one.trans hL) _) hpow hg) ha

private theorem mean_factor_absorb {freq L a : ℝ} (p : ℕ)
    (hf : 1 ≤ freq) (hL : 1 ≤ L) (ha : 0 ≤ a)
    (hs : L ^ 6 * freq ^ (-1 / 12 : ℝ) ≤ 1) :
    a * L ^ 6 * freq ^ hierarchyMeanExponent p ≤ a * freq ^ hierarchyInductiveMeanExponent p := by
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (hierarchy_absorb_mean_parent_loss hf (pow_nonneg (zero_le_one.trans hL) _) hs p) ha

private theorem mono_factor {freq L a b e : ℝ} {i j : ℕ}
    (hf : 0 ≤ freq) (hL : 1 ≤ L) (hb : 0 ≤ b) (hab : a ≤ b) (hij : i ≤ j) :
    a * L ^ i * freq ^ e ≤ b * L ^ j * freq ^ e := by
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hab (pow_le_pow_right₀ hL hij) (pow_nonneg (zero_le_one.trans hL) _) hb)
    (Real.rpow_nonneg hf _)

private theorem mono_exponent {freq L a e e' : ℝ} {i : ℕ}
    (hf : 1 ≤ freq) (hL : 0 ≤ L) (ha : 0 ≤ a) (he : e ≤ e') :
    a * L ^ i * freq ^ e ≤ a * L ^ i * freq ^ e' :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hf he) (by positivity)

private theorem sum_mul_bound {ι : Type*} (S : Finset ι) {f : ι → ℝ} {M : ℝ}
    (h : ∀ i ∈ S, f i ≤ M) : ∑ i ∈ S, f i ≤ (S.card : ℝ) * M := by
  refine (Finset.sum_le_sum h).trans_eq ?_
  rw [Finset.sum_const, nsmul_eq_mul]

private theorem add_cost_mul {freq L K a x u v : ℝ} {i : ℕ}
    (hf : 0 < freq) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hx : x ≤ a * L ^ i * freq ^ u) :
    K * L * (freq ^ v * x) ≤ K * a * L ^ (i + 1) * freq ^ (v + u) := by
  refine (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hf.le v)) (mul_nonneg hK hL)).trans_eq ?_
  rw [pow_succ, Real.rpow_add hf]
  ring

/-- Increasing the order- and level-dependent constant preserves all bounds. -/
theorem HierarchyLevelBound.mono {s : HierarchyMeasuredLevels} {freq L A A' : ℝ} {n p : ℕ}
    (h : HierarchyLevelBound s freq L A n p) (hf : 1 ≤ freq) (hL : 1 ≤ L) (hA : A ≤ A') :
    HierarchyLevelBound s freq L A' n p := by
  have hf₀ : 0 ≤ freq := zero_le_one.trans hf
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  exact ⟨h.oscSource.trans (by gcongr), h.meanSource.trans (by gcongr), h.osc.trans (by gcongr),
    h.mean.trans (by gcongr), h.meanStrong.trans (by gcongr), h.completion.trans (by gcongr),
    h.Y.trans (by gcongr), h.Z.trans (by gcongr)⟩

private def hierarchyMeanCap (K A slow : ℝ) : ℝ := K * slow * (3 * (A * A)) + K

private def hierarchyOscSourceCap (K A slow fast B : ℝ) : ℝ :=
  2 * K * A + slow * (K * (A * A)) + fast * (K * (A * A) + K * (B * A))

/-- The order-dependent constants grow with depth through finitely many
terms, independently of the frequency and parent loss. -/
noncomputable def hierarchyStepCap (P p : ℕ) (K A : ℝ) : ℝ :=
  let slow : ℝ := (hierarchyLevelPairs P 0 p).card
  let fast : ℝ := (hierarchyLevelPairs P 1 p).card
  let M := hierarchyMeanCap K A slow
  let B := K * M
  let F := hierarchyOscSourceCap K A slow fast (A + B)
  let O := K * F
  A + M + B + F + O + K * O + (O + A + B)

/-- One correction step of Theorem 5.6. The three-order reserve accounts
for differentiating the source of the current mean, then the current
oscillation inside its completion. -/
theorem hierarchy_correction_level_bound_withResidualLoss
    {s : HierarchyMeasuredLevels} {freq L K A : ℝ} {meanResidualLoss : Option ℝ}
    {P H N p n : ℕ} (recurrence : HierarchyNormRecurrence s freq L K P H meanResidualLoss)
    (hf : 1 ≤ freq) (hL : 1 ≤ L) (hK : 1 ≤ K) (hA : 1 ≤ A)
    (hResidualLoss : hierarchyParentResidualConstant K meanResidualLoss ≤ K * L ^ 5)
    (hsmall : L ^ 6 * freq ^ (-1 / 12 : ℝ) ≤ 1)
    (hN : N ≤ H) (hp : p ∈ Finset.Icc 2 P) (hn : n + 3 ≤ N)
    (prev : ∀ i, 1 ≤ i → i < p → ∀ m ≤ N, HierarchyLevelBound s freq L A m i) :
    HierarchyLevelBound s freq L (hierarchyStepCap P p K A) n p := by
  obtain ⟨hp₂, hpP⟩ := Finset.mem_Icc.mp hp
  let slow := hierarchyLevelPairs P 0 p
  let fast := hierarchyLevelPairs P 1 p
  let M := hierarchyMeanCap K A (slow.card : ℝ)
  let B := K * M
  let F := hierarchyOscSourceCap K A (slow.card : ℝ) (fast.card : ℝ) (A + B)
  let O := K * F
  have hf₀ : 0 < freq := zero_lt_one.trans_le hf
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  have hA₀ : 0 ≤ A := zero_le_one.trans hA
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hM₀ : 0 ≤ M := by dsimp [M, hierarchyMeanCap]; positivity
  have hB₀ : 0 ≤ B := mul_nonneg hK₀ hM₀
  have hF₀ : 0 ≤ F := by dsimp [F, hierarchyOscSourceCap]; positivity
  have hO₀ : 0 ≤ O := mul_nonneg hK₀ hF₀
  have hOsc₂ (m i : ℕ) (hi : 1 ≤ i) (hip : i < p) (hm : m ≤ N) :
      s.osc m i ≤ A * L ^ 2 * freq ^ hierarchyOscExponent i := by
    apply (prev i hi hip m hm).osc.trans
    simpa only [pow_one] using
      (mono_factor (i := 1) (j := 2) (e := hierarchyOscExponent i) hf₀.le hL hA₀ le_rfl
        (by decide : 1 ≤ 2))
  have hMeanSrc (m : ℕ) (hm : m + 1 ≤ N) :
      s.meanSource m p ≤ M * L ^ 5 * freq ^ hierarchyMeanExponent p := by
    have hsum : (∑ ij ∈ slow,
        (s.Y (m + 1) ij.1 * s.Y (m + 1) ij.2 +
          s.osc (m + 1) ij.1 * s.Y (m + 1) ij.2 +
          s.mean (m + 1) ij.1 * s.mean (m + 1) ij.2)) ≤
        slow.card * (3 * ((A * A) * L ^ 4 * freq ^ hierarchyMeanExponent p)) := by
      refine sum_mul_bound slow fun ij hij => ?_
      obtain ⟨hi, hj, hgrade⟩ := hierarchyLevelPairs_spec hij
      simp only [Nat.zero_add, Nat.add_zero] at hi hgrade
      obtain ⟨hip, hjp⟩ := hierarchy_label_inputs_previous hi hj hgrade
      have li := prev ij.1 hi hip (m + 1) hm
      have lj := prev ij.2 hj hjp (m + 1) hm
      have hY₂ := (s.nonneg (m + 1) ij.2).2.2.2.2.2.1
      have hB₂ := (s.nonneg (m + 1) ij.2).2.2.2.1
      have hyy := bound_mul hf₀ hA₀ hL₀ hY₂ li.Y lj.Y
      have hoy := bound_mul hf₀ hA₀ hL₀ hY₂ (hOsc₂ _ _ hi hip hm) lj.Y
      rw [(hierarchy_label_product_exponent ij.1 ij.2).1, hgrade] at hyy hoy
      have hbi : s.mean (m + 1) ij.1 ≤ A * L ^ 0 * freq ^ hierarchyInductiveMeanExponent ij.1 := by
        simpa only [pow_zero, mul_one] using li.mean
      have hbj : s.mean (m + 1) ij.2 ≤ A * L ^ 0 * freq ^ hierarchyInductiveMeanExponent ij.2 := by
        simpa only [pow_zero, mul_one] using lj.mean
      have hbb := bound_mul hf₀ hA₀ hL₀ hB₂ hbi hbj
      rw [hierarchy_mean_product_exponent, hgrade] at hbb
      have hbb' := (hbb.trans (mono_exponent hf hL₀ (mul_nonneg hA₀ hA₀)
        (by linarith : hierarchyMeanExponent p - 1 ≤ hierarchyMeanExponent p))).trans
        (mono_factor hf₀.le hL (mul_nonneg hA₀ hA₀) le_rfl (by decide : 0 + 0 ≤ 4))
      exact (add_le_add (add_le_add hyy hoy) hbb').trans_eq (by norm_num; ring)
    have hparent : (if p = 2 then hierarchyParentResidualConstant K meanResidualLoss * freq ^ hierarchyMeanExponent 2 else 0) ≤
        K * L ^ 5 * freq ^ hierarchyMeanExponent p := by
      by_cases h2 : p = 2
      · subst p
        simp only [ite_true]
        exact mul_le_mul_of_nonneg_right hResidualLoss (Real.rpow_nonneg hf₀.le _)
      · simp only [ite_eq_right h2]
        positivity
    calc
      _ ≤ K * L * (slow.card * (3 * ((A * A) * L ^ 4 * freq ^ hierarchyMeanExponent p))) +
          K * L ^ 5 * freq ^ hierarchyMeanExponent p :=
        (recurrence.meanForcing m (hm.trans hN) p hp).trans
          (add_le_add (mul_le_mul_of_nonneg_left hsum (mul_nonneg hK₀ hL₀)) hparent)
      _ = _ := by dsimp [M, hierarchyMeanCap]; ring
  have hMeanStrong (m : ℕ) (hm : m + 2 ≤ N) :
      s.mean m p ≤ B * L ^ 6 * freq ^ hierarchyMeanExponent p := by
    calc
      _ ≤ K * L * (M * L ^ 5 * freq ^ hierarchyMeanExponent p) :=
        (recurrence.meanSolve m (by omega) p hp).trans
          (mul_le_mul_of_nonneg_left (hMeanSrc (m + 1) (by omega)) (mul_nonneg hK₀ hL₀))
      _ = _ := by dsimp [B]; ring
  have hMean (m : ℕ) (hm : m + 2 ≤ N) :
      s.mean m p ≤ B * freq ^ hierarchyInductiveMeanExponent p :=
    (hMeanStrong m hm).trans (mean_factor_absorb p hf hL hB₀ hsmall)
  have hOscSource (m : ℕ) (hm : m + 2 ≤ N) :
      s.oscSource m p ≤ F * freq ^ hierarchyOscExponent p := by
    have hprev := prev (p - 1) (by omega) (by omega) (m + 1) (by omega)
    have hForcingPrev : s.oscSource (m + 1) (p - 1) ≤
        A * L * freq ^ hierarchyOscExponent (p - 1) := by
      apply hprev.oscSource.trans
      simpa only [pow_zero, pow_one, mul_one] using
        (mono_factor (i := 0) (j := 1) (e := hierarchyOscExponent (p - 1))
          hf₀.le hL hA₀ le_rfl (by decide : 0 ≤ 1))
    have hrelay : K * L * (freq ^ (-1 : ℝ) *
        (s.osc (m + 1) (p - 1) + s.oscSource (m + 1) (p - 1))) ≤
        (2 * K * A) * freq ^ hierarchyOscExponent p := by
      have hsum : s.osc (m + 1) (p - 1) + s.oscSource (m + 1) (p - 1) ≤
          (2 * A) * L ^ 1 * freq ^ hierarchyOscExponent (p - 1) := by
        rw [pow_one]
        linarith [hprev.osc, hForcingPrev]
      have h := add_cost_mul (v := -1) hf₀ hL₀ hK₀ hsum
      rw [show -1 + hierarchyOscExponent (p - 1) = hierarchyCompletionExponent (p - 1) by
        unfold hierarchyCompletionExponent; ring, hierarchy_completion_previous (by omega : 1 ≤ p)] at h
      exact h.trans ((factor_absorb hf hL (by positivity) hsmall
        (by decide : 1 + 1 ≤ 6) (by norm_num : (1 / 12 : ℝ) ≤ 1 / 3)).trans_eq (by ring))
    have hslow : K * L * (∑ ij ∈ slow, s.Z (m + 1) ij.1 * s.Z (m + 1) ij.2) ≤
        slow.card * ((K * (A * A)) * freq ^ hierarchyOscExponent p) := by
      rw [Finset.mul_sum]
      refine sum_mul_bound slow fun ij hij => ?_
      obtain ⟨hi, hj, hgrade⟩ := hierarchyLevelPairs_spec hij
      simp only [Nat.zero_add, Nat.add_zero] at hi hgrade
      obtain ⟨hip, hjp⟩ := hierarchy_label_inputs_previous hi hj hgrade
      have hterm := bound_mul hf₀ hA₀ hL₀ (s.nonneg (m + 1) ij.2).2.2.2.2.2.2
        (prev ij.1 hi hip (m + 1) (by omega)).Z (prev ij.2 hj hjp (m + 1) (by omega)).Z
      rw [(hierarchy_label_product_exponent ij.1 ij.2).2, hgrade] at hterm
      have h := add_cost_mul (v := 0) hf₀ hL₀ hK₀ hterm
      simp only [Real.rpow_zero, one_mul, zero_add] at h
      exact h.trans (factor_absorb hf hL (by positivity) hsmall (by decide : 2 + 2 + 1 ≤ 6)
        (by norm_num : (1 / 12 : ℝ) ≤ 7 / 12))
    have hfast : K * L * (freq ^ (3 / 2 : ℝ) * (∑ ij ∈ fast,
        (s.completion m (ij.1 - 1) * s.Y (m + 1) ij.2 +
          s.mean m ij.1 * s.Y (m + 1) ij.2))) ≤
        fast.card * ((K * (A * A) + K * ((A + B) * A)) * freq ^ hierarchyOscExponent p) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine sum_mul_bound fast fun ij hij => ?_
      obtain ⟨hi, hj, hgrade⟩ := hierarchyLevelPairs_spec hij
      obtain ⟨hip, hjp, hip', _⟩ := hierarchy_phase_inputs_previous hi hj hgrade
      have hjbound := (prev ij.2 hj hjp (m + 1) (by omega)).Y
      have hy₀ := (s.nonneg (m + 1) ij.2).2.2.2.2.2.1
      have hC := bound_mul hf₀ hA₀ hL₀ hy₀
        (prev (ij.1 - 1) (by omega) hip m (by omega)).completion hjbound
      have hC' := add_cost_mul (v := 3 / 2) hf₀ hL₀ hK₀ hC
      rw [← add_assoc, hierarchy_fast_completion_exponent (by omega : 1 ≤ ij.1) hgrade] at hC'
      have hC'' := hC'.trans (factor_absorb hf hL (by positivity) hsmall
        (by decide : 2 + 2 + 1 ≤ 6) le_rfl)
      have hB : s.mean m ij.1 ≤ (A + B) * L ^ 0 * freq ^ hierarchyInductiveMeanExponent ij.1 := by
        simp only [pow_zero, mul_one]
        rcases lt_or_eq_of_le hip' with hlt | heq
        · exact (prev ij.1 (by omega) hlt m (by omega)).mean.trans
            (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hf₀.le _))
        · subst p
          exact (hMean m hm).trans
            (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hf₀.le _))
      have hb := bound_mul hf₀ (add_nonneg hA₀ hB₀) hL₀ hy₀ hB hjbound
      have hb' := add_cost_mul (v := 3 / 2) hf₀ hL₀ hK₀ hb
      rw [← add_assoc, hierarchy_fast_mean_exponent hgrade] at hb'
      have hb'' := hb'.trans (factor_absorb hf hL (by positivity) hsmall
        (by decide : 0 + 2 + 1 ≤ 6) (by norm_num : (1 / 12 : ℝ) ≤ 1 / 4))
      rw [mul_add, mul_add, add_mul]
      exact add_le_add hC'' hb''
    calc
      _ ≤ _ := recurrence.oscForcing m (by omega) p hp
      _ ≤ F * freq ^ hierarchyOscExponent p := by
        rw [mul_add, mul_add]
        dsimp [F, hierarchyOscSourceCap]
        rw [add_mul, add_mul]
        exact add_le_add (add_le_add hrelay (hslow.trans_eq (by ring))) (hfast.trans_eq (by ring))
  have hOsc (m : ℕ) (hm : m + 2 ≤ N) :
      s.osc m p ≤ O * L * freq ^ hierarchyOscExponent p := by
    exact (recurrence.oscSolve m (by omega) p hp).trans
      ((mul_le_mul_of_nonneg_left (hOscSource m hm) (mul_nonneg hK₀ hL₀)).trans_eq (by dsimp [O]; ring))
  have hC : s.completion n p ≤ (K * O) * L ^ 2 * freq ^ hierarchyCompletionExponent p := by
    refine (recurrence.complete n (by omega) p (Finset.mem_Icc.mpr ⟨by omega, hpP⟩)).trans ?_
    rw [mul_assoc (K * L)]
    have h := add_cost_mul (v := -1) hf₀ hL₀ hK₀
      (show s.osc (n + 1) p ≤ O * L ^ 1 * freq ^ hierarchyOscExponent p by
        simpa only [pow_one] using hOsc (n + 1) (by omega))
    simpa only [hierarchyCompletionExponent, sub_eq_add_neg, add_comm (-1 : ℝ)] using h
  have hY : s.Y n p ≤ (O + A) * L ^ 2 * freq ^ hierarchyOscExponent p := by
    have ho : s.osc n p ≤ O * L ^ 2 * freq ^ hierarchyOscExponent p := by
      apply (hOsc n (by omega)).trans
      simpa only [pow_one] using (mono_factor (i := 1) (j := 2) (e := hierarchyOscExponent p)
        hf₀.le hL hO₀ le_rfl (by decide : 1 ≤ 2))
    have hcp := (prev (p - 1) (by omega) (by omega) n (by omega)).completion
    rw [hierarchy_completion_previous (by omega : 1 ≤ p)] at hcp
    have hcp' := hcp.trans (mono_exponent hf hL₀ hA₀
      (by linarith : hierarchyOscExponent p - 1 / 3 ≤ hierarchyOscExponent p))
    exact (recurrence.Ybound n (by omega) p (Finset.mem_Icc.mpr ⟨by omega, hpP⟩)).trans
      ((add_le_add ho hcp').trans_eq (by ring))
  have hZ : s.Z n p ≤ (O + A + B) * L ^ 2 * freq ^ hierarchyOscExponent p := by
    have hb0 : s.mean n p ≤ B * freq ^ hierarchyOscExponent p := (hMean n (by omega)).trans (by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hf _) hB₀
      unfold hierarchyInductiveMeanExponent
      linarith)
    have hb := hb0.trans (by
      simpa only [pow_zero, mul_one] using (mono_factor (i := 0) (j := 2)
        (e := hierarchyOscExponent p) hf₀.le hL hB₀ le_rfl (by decide : 0 ≤ 2)))
    exact (recurrence.Zbound n (by omega) p (Finset.mem_Icc.mpr ⟨by omega, hpP⟩)).trans
      ((add_le_add hY hb).trans_eq (by ring))
  change HierarchyLevelBound s freq L (A + M + B + F + O + K * O + (O + A + B)) n p
  have hKO : 0 ≤ K * O := mul_nonneg hK₀ hO₀
  refine ⟨(hOscSource n (by omega)).trans ?_, (hMeanSrc n (by omega)).trans ?_,
    (hOsc n (by omega)).trans ?_, (hMean n (by omega)).trans ?_,
    (hMeanStrong n (by omega)).trans ?_, hC.trans ?_, hY.trans ?_, hZ.trans ?_⟩
  all_goals
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hf₀.le _)
    first
    | exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    | linarith

private theorem hierarchyStepCap_ge {P p : ℕ} {K A : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) :
    A ≤ hierarchyStepCap P p K A := by
  let M := hierarchyMeanCap K A ((hierarchyLevelPairs P 0 p).card : ℝ)
  let B := K * M
  let F := hierarchyOscSourceCap K A ((hierarchyLevelPairs P 0 p).card : ℝ)
    ((hierarchyLevelPairs P 1 p).card : ℝ) (A + B)
  let O := K * F
  have hM : 0 ≤ M := by dsimp [M, hierarchyMeanCap]; positivity
  have hB : 0 ≤ B := mul_nonneg hK hM
  have hF : 0 ≤ F := by dsimp [F, hierarchyOscSourceCap]; positivity
  have hO : 0 ≤ O := mul_nonneg hK hF
  have hKO : 0 ≤ K * O := mul_nonneg hK hO
  change A ≤ A + M + B + F + O + K * O + (O + A + B)
  linarith

/-- Constants for the full finite hierarchy. Their only quantitative inputs
are the derivative-order constant bound, the depth and the level. -/
noncomputable def hierarchyLevelConstant (P : ℕ) (K : ℝ) : ℕ → ℝ
  | 0 => 1 + K + K * K
  | p + 1 => hierarchyStepCap P (p + 1) K (hierarchyLevelConstant P K p)

theorem hierarchyLevelConstant_one_le {P : ℕ} {K : ℝ} (hK : 0 ≤ K) (p : ℕ) :
    1 ≤ hierarchyLevelConstant P K p := by
  induction p with
  | zero => change 1 ≤ 1 + K + K * K; nlinarith
  | succ p ih => exact ih.trans (hierarchyStepCap_ge hK (zero_le_one.trans ih))

theorem hierarchyLevelConstant_monotone {P : ℕ} {K : ℝ} (hK : 0 ≤ K) :
    Monotone (hierarchyLevelConstant P K) :=
  monotone_nat_of_le_succ fun p =>
    hierarchyStepCap_ge hK (zero_le_one.trans (hierarchyLevelConstant_one_le hK p))

/-- The spatial correction estimate with its unit parent-residual loss. -/
theorem hierarchy_correction_level_bound {s : HierarchyMeasuredLevels} {freq L K A : ℝ}
    {P H N p n : ℕ} (recurrence : HierarchyNormRecurrence s freq L K P H)
    (hf : 1 ≤ freq) (hL : 1 ≤ L) (hK : 1 ≤ K) (hA : 1 ≤ A)
    (hsmall : L ^ 6 * freq ^ (-1 / 12 : ℝ) ≤ 1)
    (hN : N ≤ H) (hp : p ∈ Finset.Icc 2 P) (hn : n + 3 ≤ N)
    (prev : ∀ i, 1 ≤ i → i < p → ∀ m ≤ N, HierarchyLevelBound s freq L A m i) :
    HierarchyLevelBound s freq L (hierarchyStepCap P p K A) n p :=
  hierarchy_correction_level_bound_withResidualLoss recurrence hf hL hK hA
    (le_mul_of_one_le_right (zero_le_one.trans hK) (one_le_pow₀ hL)) hsmall hN hp hn prev

private theorem hierarchy_seed_level_bound {s : HierarchyMeasuredLevels} {freq L K A : ℝ}
    {meanResidualLoss : Option ℝ} {P H n : ℕ}
    (recurrence : HierarchyNormRecurrence s freq L K P H meanResidualLoss)
    (hf : 1 ≤ freq) (hL : 1 ≤ L) (hK : 1 ≤ K) (hA : K ≤ A) (hA₂ : K * K ≤ A)
    (hP : 1 ≤ P) (hn : n + 1 ≤ H) :
    HierarchyLevelBound s freq L A n 1 := by
  have hf₀ := zero_lt_one.trans_le hf
  have hL₀ := zero_le_one.trans hL
  have hK₀ := zero_le_one.trans hK
  have hA₀ := hK₀.trans hA
  have hP₁ : 1 ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨le_rfl, hP⟩
  obtain ⟨hF, hM, hB, hC₀⟩ := recurrence.seedZeros n
  have hOsc : s.osc n 1 ≤ A * L * freq ^ hierarchyOscExponent 1 := by
    exact (recurrence.seed n (by omega)).trans (by gcongr)
  have hY : s.Y n 1 ≤ A * L ^ 2 * freq ^ hierarchyOscExponent 1 := by
    have h := recurrence.Ybound n (by omega) 1 hP₁
    rw [Nat.sub_self, hC₀, add_zero] at h
    exact (h.trans hOsc).trans (by
      simpa only [pow_one] using (mono_factor (i := 1) (j := 2)
        (e := hierarchyOscExponent 1) hf₀.le hL hA₀ le_rfl (by decide : 1 ≤ 2)))
  have hZ : s.Z n 1 ≤ A * L ^ 2 * freq ^ hierarchyOscExponent 1 := by
    have h := recurrence.Zbound n (by omega) 1 hP₁
    rw [hB, add_zero] at h
    exact h.trans hY
  have hC : s.completion n 1 ≤ A * L ^ 2 * freq ^ hierarchyCompletionExponent 1 := by
    refine (recurrence.complete n hn 1 hP₁).trans ?_
    rw [mul_assoc (K * L)]
    have h := add_cost_mul (v := -1) hf₀ hL₀ hK₀
      (show s.osc (n + 1) 1 ≤ K * L ^ 1 * freq ^ hierarchyOscExponent 1 by
        simpa only [pow_one] using recurrence.seed (n + 1) hn)
    apply h.trans
    change K * K * L ^ 2 * freq ^ (-1 + hierarchyOscExponent 1) ≤ _
    rw [hierarchyCompletionExponent, sub_eq_add_neg, add_comm (hierarchyOscExponent 1)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA₂ (pow_nonneg hL₀ _))
      (Real.rpow_nonneg hf₀.le _)
  refine ⟨?_, ?_, hOsc, ?_, ?_, hC, hY, hZ⟩
  · rw [hF]; positivity
  · rw [hM]; positivity
  · rw [hB]; positivity
  · rw [hB]; positivity

/-- Iterate the measured hierarchy through any retained level. Three
additional derivative orders per correction level, plus one for the seed
completion, suffice when the analytic constants are known through `H`. -/
theorem hierarchy_level_bounds_withResidualLoss {s : HierarchyMeasuredLevels} {freq L K : ℝ} {P H : ℕ}
    {meanResidualLoss : Option ℝ}
    (recurrence : HierarchyNormRecurrence s freq L K P H meanResidualLoss)
    (hf : 1 ≤ freq) (hL : 1 ≤ L) (hK : 1 ≤ K)
    (hResidualLoss : hierarchyParentResidualConstant K meanResidualLoss ≤ K * L ^ 5)
    (hsmall : L ^ 6 * freq ^ (-1 / 12 : ℝ) ≤ 1) :
    ∀ p, 1 ≤ p → p ≤ P → ∀ n, n + 3 * (p - 1) + 1 ≤ H →
      HierarchyLevelBound s freq L (hierarchyLevelConstant P K p) n p := by
  have hK₀ := zero_le_one.trans hK
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    intro hp hpP n hn
    by_cases hp₁ : p = 1
    · subst p
      have hcap : hierarchyLevelConstant P K 0 ≤ hierarchyLevelConstant P K 1 :=
        hierarchyLevelConstant_monotone hK₀ (by omega)
      have h0 : K ≤ hierarchyLevelConstant P K 0 := by
        change K ≤ 1 + K + K * K
        nlinarith
      have h0' : K * K ≤ hierarchyLevelConstant P K 0 := by
        change K * K ≤ 1 + K + K * K
        linarith
      exact hierarchy_seed_level_bound recurrence hf hL hK (h0.trans hcap) (h0'.trans hcap) hpP (by omega)
    · have hp₂ : 2 ≤ p := by omega
      let N := H - (3 * (p - 2) + 1)
      have hN : N ≤ H := Nat.sub_le _ _
      have hNn : n + 3 ≤ N := by omega
      let A := hierarchyLevelConstant P K (p - 1)
      have hA : 1 ≤ A := hierarchyLevelConstant_one_le hK₀ _
      have hprev (i : ℕ) (hi : 1 ≤ i) (hip : i < p) (m : ℕ) (hm : m ≤ N) :
          HierarchyLevelBound s freq L A m i :=
        (ih i hip hi (by omega) m (by omega)).mono hf hL
          (hierarchyLevelConstant_monotone hK₀ (by omega))
      have hstep := hierarchy_correction_level_bound_withResidualLoss recurrence hf hL hK hA
        hResidualLoss hsmall hN
        (Finset.mem_Icc.mpr ⟨hp₂, hpP⟩) hNn hprev
      have hindex : p - 1 + 1 = p := by omega
      have hcap : hierarchyLevelConstant P K p = hierarchyStepCap P p K A := by
        conv_lhs => rw [← hindex]
        rw [hierarchyLevelConstant, hindex]
      rw [hcap]
      exact hstep

/-- Retained level estimates for the spatial recurrence. -/
theorem hierarchy_level_bounds {s : HierarchyMeasuredLevels} {freq L K : ℝ} {P H : ℕ}
    (recurrence : HierarchyNormRecurrence s freq L K P H)
    (hf : 1 ≤ freq) (hL : 1 ≤ L) (hK : 1 ≤ K)
    (hsmall : L ^ 6 * freq ^ (-1 / 12 : ℝ) ≤ 1) :
    ∀ p, 1 ≤ p → p ≤ P → ∀ n, n + 3 * (p - 1) + 1 ≤ H →
      HierarchyLevelBound s freq L (hierarchyLevelConstant P K p) n p :=
  hierarchy_level_bounds_withResidualLoss recurrence hf hL hK
    (le_mul_of_one_le_right (zero_le_one.trans hK) (one_le_pow₀ hL)) hsmall

section ActualSources

variable {E Q : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup Q] [Module ℝ Q]

/-- Measure the exact profiles and right-hand sides of the finite solve.
The three supplied norm functions may use different time intervals for
the weighted oscillatory profiles and the unweighted means. -/
def HierarchyMeasuredLevels.ofProfiles (A : HierarchyOperators E Q)
    (u : HierarchyProfiles E Q) (P : ℕ) (completionSwitch parentResidual : E)
    (freq : ℝ) (hf : 0 ≤ freq) (unweighted weighted : ℕ → E → ℝ)
    (pressureWeighted : ℕ → Q → ℝ)
    (hu : ∀ n a, 0 ≤ unweighted n a) (hw : ∀ n a, 0 ≤ weighted n a)
    (hq : ∀ n a, 0 ≤ pressureWeighted n a) : HierarchyMeasuredLevels where
  oscSource n p :=
    let H := A.sourceBeforeMean u P completionSwitch p
    if p = 1 then 0 else weighted n (-(H - A.average H) -
      hierarchyAdvectionAtLevel P 1 p (A.meanPhaseProduct u))
  meanSource n p :=
    let H := A.sourceBeforeMean u P completionSwitch p
    if p = 1 then 0 else unweighted n (-A.average H - (if p = 2 then parentResidual else 0))
  osc n p := weighted n (u.V p) + freq * pressureWeighted n (u.p p)
  mean n p := unweighted n (u.B p)
  completion n p := weighted n (u.C p)
  Y n p := weighted n (u.Y p)
  Z n p := weighted n (u.Y p) + unweighted n (u.B p)
  nonneg n p := by
    refine ⟨?_, ?_, add_nonneg (hw _ _) (mul_nonneg hf (hq _ _)),
      hu _ _, hw _ _, hw _ _, add_nonneg (hw _ _) (hu _ _)⟩
    · split <;> first | exact le_rfl | exact hw _ _
    · split <;> first | exact le_rfl | exact hu _ _

/-- On the constructed profiles, the measured correction sources equal
the norms of the corresponding analytic left-hand sides. -/
theorem FiniteHierarchySolvers.construct_measured_sources_eq {A : HierarchyOperators E Q}
    (S : FiniteHierarchySolvers A) {P p : ℕ} (hp : p ∈ Finset.Icc 2 P)
    (completionSwitch parentResidual : E) (hR : A.average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput A) (freq : ℝ) (hf : 0 ≤ freq)
    (unweighted weighted : ℕ → E → ℝ) (pressureWeighted : ℕ → Q → ℝ)
    (hu : ∀ n a, 0 ≤ unweighted n a) (hw : ∀ n a, 0 ≤ weighted n a)
    (hq : ∀ n a, 0 ≤ pressureWeighted n a) (n : ℕ) :
    let u := S.construct P completionSwitch parentResidual hR leading
    let s := HierarchyMeasuredLevels.ofProfiles A u P completionSwitch parentResidual
      freq hf unweighted weighted pressureWeighted hu hw hq
    s.meanSource n p = unweighted n (A.material (u.B p) + A.labelGrad (u.q p)) ∧
      s.oscSource n p = weighted n (A.material (u.V p) + A.phaseGrad (u.p p)) := by
  have hp₁ : p ≠ 1 := by have h := (Finset.mem_Icc.mp hp).1; omega
  obtain ⟨hm, ho⟩ := S.construct_equations hp completionSwitch parentResidual hR leading
  simp only [HierarchyMeasuredLevels.ofProfiles, ite_eq_right hp₁]
  exact ⟨congrArg (unweighted n) hm.symm, congrArg (weighted n) ho.symm⟩

end ActualSources

end TorusEuler
