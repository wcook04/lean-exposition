import TorusEuler.Paper.Proofs.S5b.T56Master
import TorusEuler.Paper.Proofs.S5b.T56Conv

/-!
# Proof of Theorem 5.6

From the measured recurrence of `T56Master` (the induction of `sections/06c_finite_hierarchy.tex:521-637`)
the bounds (5.34)-(5.36) (TeX :514-636, level by level, with constants independent of the depth),
(5.37) (summing over the levels, TeX :638-640) and (5.38) (TeX :640-657, `master_recurrence`).
-/

open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper

open S5b AppendixD HierarchyTwistedProfile

noncomputable section

namespace S5b

/-- Exponent splitting for the oscillatory terms of (5.37), (5.38). -/
theorem osc_exp_split {lam : ℝ} (hlam0 : 0 < lam) (p : ℕ) :
    lam ^ hierarchyOscExponent p = lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * ((p : ℝ) - 1) / 3) := by
  unfold hierarchyOscExponent
  rw [← Real.rpow_add hlam0]
  congr 1
  ring

/-- Exponent splitting for the mean terms of (5.37), (5.38). -/
theorem mean_exp_split {lam : ℝ} (hlam0 : 0 < lam) (p : ℕ) :
    lam ^ hierarchyMeanExponent p = lam ^ (-5 / 2 : ℝ) * lam ^ (-2 * ((p : ℝ) - 2) / 3) := by
  unfold hierarchyMeanExponent
  rw [← Real.rpow_add hlam0]
  congr 1
  ring

/-- Exponent splitting for the completion terms of (5.37), (5.38). -/
theorem compl_exp_split {lam : ℝ} (hlam0 : 0 < lam) (p : ℕ) :
    lam ^ hierarchyCompletionExponent p = lam ^ (-9 / 4 : ℝ) * lam ^ (-2 * ((p : ℝ) - 1) / 3) := by
  unfold hierarchyCompletionExponent hierarchyOscExponent
  rw [← Real.rpow_add hlam0]
  congr 1
  ring

end S5b

set_option maxHeartbeats 8000000 in
/-- **Proof of Theorem 5.6** following `sections/06c_finite_hierarchy.tex:499-657` (statement
:469-498; equations (5.34)-(5.38), (5.39), (5.40)-(5.42)). The level induction is
`S5b.master_recurrence`: the transverse and mean solves use (5.21) of Lemma 5.3 (`h5_3`) and (5.12)
of Proposition 5.2 (`h5_2`); the seed `A₁`, `𝗉[A₁]` is bounded by (5.22) (`h5_3`); the completion by
(5.31) and the relay `(∂_t+M)C[V]+𝐝𝗉` by (5.32) and its leading clause (`h5_5`); the products of
the sources by the advection bounds (5.39), i.e. Lemma D.1 (`hD_1`), with the coefficient norms of
Proposition 5.1 (`h5_1`: (D.6), (5.8), and the composition clause (5.7) applied to the parent residual, whose band and size (5.6) come from `S5.Parent`) and Bernstein's inequality
(`hB_1`: (B.1) for the residual); Proposition 5.4 (`h5_4`) supplies the vanishing before `t₀`, the
supports, `Y_{P+1} = Z_{P+1} = C_{P+1}` (for (5.38)) and the decomposition `W_osc = ∑ (V_p + C_{p+1})`. Here (5.34)-(5.36) at level `p` follow
from the level bounds of the recurrence at depth `P ≥ p` (constants independent of `P`:
`S5b.levelConstant_indep`), (5.37) by summing over the levels, (5.38) by `master_recurrence`. -/
theorem Proof.theorem_5_6_of (h5_1 : Statement.proposition_5_1)
    (h5_2 : Statement.proposition_5_2) (h5_3 : Statement.lemma_5_3)
    (h5_4 : Statement.proposition_5_4) (h5_5 : Statement.lemma_5_5)
    (hD_1 : Statement.lemma_D_1) (hB_1 : Statement.lemma_B_1) : Statement.theorem_5_6 := by
  obtain ⟨a₀, hmaster⟩ := S5b.master_recurrence hD_1 h5_1 h5_2 h5_3 h5_4 h5_5 hB_1
  obtain ⟨a₄, h4⟩ := h5_4
  refine ⟨max a₀ a₄, fun a ha => ?_⟩
  have ha0 : a₀ ≤ a := le_trans (le_max_left _ _) ha
  have ha4 : a₄ ≤ a := le_trans (le_max_right _ _) ha
  obtain ⟨c, K, KP, hK1, hmain⟩ := hmaster a ha0
  refine ⟨6 * c, fun n p => 2 * hierarchyLevelConstant p (K (n + 3 * p + 1)) p,
    fun m P => max (KP m P) 0 + 2 * (P : ℝ) * hierarchyLevelConstant P (K (m + 1 + 3 * P)) P, ?_⟩
  intro T hT U X pU k D lam t₀ center d χ hP hL hO hsmall amp hamp P hP2 R S u hu ℓ h γ A cS W
  obtain ⟨osc₁, h₁, hle, hrec, hrem⟩ := hmain hT d χ hP hL hO hamp hP2 hu
  have hD : 1 ≤ D := Bridge.Parent.scale_ge_one hP
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hlam : 1 ≤ lam := hP.frequency_ge_one
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam
  have hf : 0 ≤ lam := hlam0.le
  set st := normSetting_of hP hL hO a with hst
  set L := D ^ c with hLdef
  have hL1 : 1 ≤ L := one_le_pow₀ hD
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hL6 : L ^ 6 * lam ^ (-1 / 12 : ℝ) ≤ 1 := by
    have : L ^ 6 = D ^ (6 * c) := by rw [hLdef, ← pow_mul, mul_comm]
    rw [this]; exact hsmall
  have hLe : ∀ e : ℕ, e ≤ 6 → L ^ e ≤ D ^ (6 * c) := fun e he =>
    (pow_le_pow_right₀ hL1 he).trans (le_of_eq (by rw [hLdef, ← pow_mul, mul_comm]))
  set s := measuredOf st (S5.ops d) u P (S5.curlCorrection d S) R lam
    (zero_le_one.trans hP.frequency_ge_one) with hsdef
  have hp1ne : ∀ p ∈ Finset.Icc 2 P, p ≠ 1 := fun p hp => by
    have := (Finset.mem_Icc.mp hp).1; omega
  have hsOscSrc : ∀ n, ∀ p ∈ Finset.Icc 2 P, s.oscSource n p =
      Wn (k := k) st n (S5.oscSource (S5.ops d) u (S5.curlCorrection d S) p +
        S5.suppSource (S5.ops d) u p) := fun n p hp => by
    have hpP := (Finset.mem_Icc.mp hp).2
    change (if p = 1 then 0 else Wn (k := k) st n (-((S5.ops d).sourceBeforeMean u P
      (S5.curlCorrection d S) p - (S5.ops d).average ((S5.ops d).sourceBeforeMean u P
        (S5.curlCorrection d S) p)) - hierarchyAdvectionAtLevel P 1 p
          ((S5.ops d).meanPhaseProduct u))) = _
    simp only [hp1ne p hp, ↓reduceIte]
    rw [Bridge.oscSource_add_suppSource_eq (S5.ops d) u _ hpP]
  have hsMeanSrc : ∀ n, ∀ p ∈ Finset.Icc 2 P, s.meanSource n p =
      Un (k := k) st n (S5.meanSource (S5.ops d) u (S5.curlCorrection d S) R p) := fun n p hp => by
    have hpP := (Finset.mem_Icc.mp hp).2
    change (if p = 1 then 0 else Un (k := k) st n (-(S5.ops d).average ((S5.ops d).sourceBeforeMean
      u P (S5.curlCorrection d S) p) - (if p = 2 then R else 0))) = _
    simp only [hp1ne p hp, ↓reduceIte]
    rw [Bridge.meanSource_eq (S5.ops d) u _ R hpP]
  have hs'1 : ∀ n, (measuredLevels' s osc₁ h₁).osc n 1 = osc₁ n := fun n => by
    simp [measuredLevels']
  have hs'ne : ∀ n, ∀ p ∈ Finset.Icc 2 P, (measuredLevels' s osc₁ h₁).osc n p = s.osc n p :=
    fun n p hp => measuredLevels'_osc_of_ne s osc₁ h₁ (hp1ne p hp) n
  -- the level bounds with constants independent of `P`
  have hlev1 : ∀ n, ∀ p ∈ Finset.Icc 1 P, HierarchyLevelBound (measuredLevels' s osc₁ h₁) lam L
      (hierarchyLevelConstant p (K (n + 3 * p + 1)) p) n p := fun n p hp => by
    obtain ⟨hp1, hpP⟩ := Finset.mem_Icc.mp hp
    have := hierarchy_level_bounds (hrec (n + 3 * p + 1)) hlam hL1 (hK1 _) hL6 p hp1 hpP n
      (by omega)
    rwa [levelConstant_indep (K (n + 3 * p + 1)) hpP p le_rfl] at this
  have hA0 : ∀ n p : ℕ, 0 ≤ hierarchyLevelConstant p (K (n + 3 * p + 1)) p := fun n p =>
    zero_le_one.trans (hierarchyLevelConstant_one_le (zero_le_one.trans (hK1 _)) p)
  have hRpow : ∀ x : ℝ, 0 ≤ lam ^ x := fun x => Real.rpow_nonneg hlam0.le x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (5.34), `p = 1`
    intro n
    have hb := hlev1 n 1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
    have h1 := hb.osc
    rw [hs'1] at h1
    have he : hierarchyOscExponent 1 = -5 / 4 := by norm_num [hierarchyOscExponent]
    rw [he] at h1
    refine (hle n).trans (h1.trans ?_)
    refine mul_le_mul_of_nonneg_right ?_ (hRpow _)
    have hLD := hLe 1 (by norm_num)
    rw [pow_one] at hLD
    have := hA0 n 1
    show _ ≤ 2 * hierarchyLevelConstant 1 (K (n + 3 * 1 + 1)) 1 * D ^ (6 * c)
    nlinarith
  · -- (5.34), `p ≥ 2`
    intro n p hp
    have hpI : p ∈ Finset.Icc 1 P :=
      Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hp).1; omega, (Finset.mem_Icc.mp hp).2⟩
    have hb := hlev1 n p hpI
    have ho := hb.osc
    rw [hs'ne _ p hp] at ho
    have hf' : s.oscSource n p ≤ _ := hb.oscSource
    rw [hsOscSrc _ p hp] at hf'
    rw [osc_exp_split hlam0] at ho hf'
    set E := lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * ((p : ℝ) - 1) / 3) with hE
    have hE0 : 0 ≤ E := mul_nonneg (hRpow _) (hRpow _)
    have ho' : S5.wNorm ℓ h t₀ γ n (u.V p) + lam * S5.wNorm ℓ h t₀ γ n (u.p p) ≤
        hierarchyLevelConstant p (K (n + 3 * p + 1)) p * L * E := ho
    have hf'' : S5.wNorm ℓ h t₀ γ n (S5.oscSource A u cS p + S5.suppSource A u p) ≤
        hierarchyLevelConstant p (K (n + 3 * p + 1)) p * E := hf'
    have hLD := hLe 1 (by norm_num)
    rw [pow_one] at hLD
    have := hA0 n p
    have h2 := mul_nonneg this hE0
    show _ ≤ 2 * hierarchyLevelConstant p (K (n + 3 * p + 1)) p * D ^ (6 * c) *
      lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * ((p : ℝ) - 1) / 3)
    have e1 : 2 * hierarchyLevelConstant p (K (n + 3 * p + 1)) p * D ^ (6 * c) *
        lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * ((p : ℝ) - 1) / 3) =
        2 * hierarchyLevelConstant p (K (n + 3 * p + 1)) p * D ^ (6 * c) * E := by rw [hE]; ring
    rw [e1]
    nlinarith [mul_le_mul_of_nonneg_left hLD h2, mul_le_mul_of_nonneg_left hL1 h2]
  · -- (5.35)
    intro n p hp
    have hpI : p ∈ Finset.Icc 1 P :=
      Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hp).1; omega, (Finset.mem_Icc.mp hp).2⟩
    have hb := hlev1 n p hpI
    have h1 := hb.meanStrong
    have h2 : s.meanSource n p ≤ _ := hb.meanSource
    rw [mean_exp_split hlam0] at h1 h2
    rw [hsMeanSrc _ p hp] at h2
    set E := lam ^ (-5 / 2 : ℝ) * lam ^ (-2 * ((p : ℝ) - 2) / 3) with hE
    have hE0 : 0 ≤ E := mul_nonneg (hRpow _) (hRpow _)
    have h1' : S5.uNorm ℓ h n (u.B p) ≤
        hierarchyLevelConstant p (K (n + 3 * p + 1)) p * L ^ 6 * E := h1
    have h2' : S5.uNorm ℓ h n (S5.meanSource A u cS R p) ≤
        hierarchyLevelConstant p (K (n + 3 * p + 1)) p * L ^ 5 * E := h2
    have hL5 := hLe 5 (by norm_num)
    have hL6' := hLe 6 le_rfl
    have := hA0 n p
    have h3 := mul_nonneg this hE0
    show _ ≤ 2 * hierarchyLevelConstant p (K (n + 3 * p + 1)) p * D ^ (6 * c) *
      lam ^ (-5 / 2 : ℝ) * lam ^ (-2 * ((p : ℝ) - 2) / 3)
    have e1 : 2 * hierarchyLevelConstant p (K (n + 3 * p + 1)) p * D ^ (6 * c) *
        lam ^ (-5 / 2 : ℝ) * lam ^ (-2 * ((p : ℝ) - 2) / 3) =
        2 * hierarchyLevelConstant p (K (n + 3 * p + 1)) p * D ^ (6 * c) * E := by rw [hE]; ring
    rw [e1]
    nlinarith [mul_le_mul_of_nonneg_left hL5 h3, mul_le_mul_of_nonneg_left hL6' h3]
  · -- (5.36)
    intro n p hp
    have hb := hlev1 n p hp
    have h1 := hb.completion
    rw [compl_exp_split hlam0] at h1
    set E := lam ^ (-9 / 4 : ℝ) * lam ^ (-2 * ((p : ℝ) - 1) / 3) with hE
    have hE0 : 0 ≤ E := mul_nonneg (hRpow _) (hRpow _)
    have h1' : S5.wNorm ℓ h t₀ γ n (S5.Cd u (p + 1)) ≤
        hierarchyLevelConstant p (K (n + 3 * p + 1)) p * L ^ 2 * E := h1
    have hL2 := hLe 2 (by norm_num)
    have := hA0 n p
    have h3 := mul_nonneg this hE0
    show _ ≤ 2 * hierarchyLevelConstant p (K (n + 3 * p + 1)) p * D ^ (6 * c) *
      lam ^ (-9 / 4 : ℝ) * lam ^ (-2 * ((p : ℝ) - 1) / 3)
    have e1 : 2 * hierarchyLevelConstant p (K (n + 3 * p + 1)) p * D ^ (6 * c) *
        lam ^ (-9 / 4 : ℝ) * lam ^ (-2 * ((p : ℝ) - 1) / 3) =
        2 * hierarchyLevelConstant p (K (n + 3 * p + 1)) p * D ^ (6 * c) * E := by rw [hE]; ring
    rw [e1]
    nlinarith [mul_le_mul_of_nonneg_left hL2 h3]
  · -- (5.37)
    intro m
    obtain ⟨-, h4r⟩ := h4 a ha4 hT d χ hP hL hO
    obtain ⟨-, -, h4id⟩ := h4r amp hamp P hP2
    obtain ⟨-, -, -, hosc, -⟩ := h4id R S u hu
    have hlevM : ∀ p ∈ Finset.Icc 1 P, HierarchyLevelBound (measuredLevels' s osc₁ h₁) lam L
        (hierarchyLevelConstant P (K (m + 1 + 3 * P)) P) m p := fun p hp =>
      hierarchy_level_bounds_through_depth (hrec (m + 1 + 3 * P)) hlam hL1 (hK1 _) hL6 m
        (Nat.le_succ m) p hp
    have hAm1 : 1 ≤ hierarchyLevelConstant P (K (m + 1 + 3 * P)) P :=
      hierarchyLevelConstant_one_le (zero_le_one.trans (hK1 _)) P
    have hAm0 := zero_le_one.trans hAm1
    have hVs' : ∀ p ∈ Finset.Icc 1 P, Wn (k := k) st m (u.V p) ≤
        (measuredLevels' s osc₁ h₁).osc m p := fun p hp => by
      by_cases h1 : p = 1
      · subst h1; rw [hs'1]
        exact (le_add_of_nonneg_right (mul_nonneg hlam0.le (apply_nonneg _ _))).trans (hle m)
      · rw [hs'ne _ p (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hp).1; omega,
          (Finset.mem_Icc.mp hp).2⟩)]
        exact le_add_of_nonneg_right (mul_nonneg hlam0.le (apply_nonneg _ _))
    constructor
    · rw [hosc]
      have hterm : ∀ p ∈ Finset.Icc 1 P, Wn (k := k) st m (u.V p + S5.Cd u (p + 1)) ≤
          2 * hierarchyLevelConstant P (K (m + 1 + 3 * P)) P * L ^ 2 * lam ^ (-5 / 4 : ℝ) :=
        fun p hp => by
        have hb := hlevM p hp
        refine (map_add_le_add (Wn (k := k) st m) _ _).trans ?_
        have h1 := (hVs' p hp).trans hb.osc
        have h2 : Wn (k := k) st m (S5.Cd u (p + 1)) ≤ _ := hb.completion
        have e1 : lam ^ hierarchyOscExponent p ≤ lam ^ (-5 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlam (by
            unfold hierarchyOscExponent
            have : (1 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp hp).1
            linarith)
        have e2 : lam ^ hierarchyCompletionExponent p ≤ lam ^ (-5 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlam (by
            unfold hierarchyCompletionExponent hierarchyOscExponent
            have : (1 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp hp).1
            linarith)
        have hLL : L ≤ L ^ 2 := by nlinarith
        have hAL := mul_nonneg hAm0 hL0
        calc _ ≤ _ + _ := add_le_add h1 h2
          _ ≤ hierarchyLevelConstant P (K (m + 1 + 3 * P)) P * L * lam ^ (-5 / 4 : ℝ) +
              hierarchyLevelConstant P (K (m + 1 + 3 * P)) P * L ^ 2 * lam ^ (-5 / 4 : ℝ) :=
            add_le_add (mul_le_mul_of_nonneg_left e1 hAL) (mul_le_mul_of_nonneg_left e2
              (mul_nonneg hAm0 (pow_nonneg hL0 _)))
          _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hLL hAm0,
              mul_nonneg (mul_nonneg hAm0 (pow_nonneg hL0 2)) (hRpow (-5 / 4 : ℝ)),
              mul_nonneg hAm0 (hRpow (-5 / 4 : ℝ))]
      refine (seminorm_finset_le (Wn (k := k) st m) (Finset.Icc 1 P)
        (fun p => u.V p + S5.Cd u (p + 1)) (fun _ => 2 * hierarchyLevelConstant P
          (K (m + 1 + 3 * P)) P * L ^ 2 * lam ^ (-5 / 4 : ℝ)) hterm).trans ?_
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
      have hX := hRpow (-5 / 4 : ℝ)
      have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
      have hLD2 := hLe 2 (by norm_num)
      have hm0 := le_max_right (KP m P) 0
      have h1 := mul_nonneg (mul_nonneg hP0 hAm0) hX
      nlinarith [mul_le_mul_of_nonneg_left hLD2 h1, mul_nonneg (le_max_right (KP m P) 0)
        (mul_nonneg (pow_nonneg hD0.le (6 * c)) hX)]
    · have hX := hRpow (-5 / 2 : ℝ)
      have hmem (p : ℕ) (hp : p ∈ Finset.Icc 2 P) : p ∈ Finset.Icc 1 P :=
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hp).1; omega, (Finset.mem_Icc.mp hp).2⟩
      have hterm1 : ∀ p ∈ Finset.Icc 2 P, Un (k := k) st m (u.B p) ≤
          hierarchyLevelConstant P (K (m + 1 + 3 * P)) P * L ^ 6 * lam ^ (-5 / 2 : ℝ) :=
        fun p hp => by
        have h1 := (hlevM p (hmem p hp)).meanStrong
        have e : lam ^ hierarchyMeanExponent p ≤ lam ^ (-5 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlam (by
            unfold hierarchyMeanExponent
            have : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp hp).1
            linarith)
        exact h1.trans (mul_le_mul_of_nonneg_left e (mul_nonneg hAm0 (pow_nonneg hL0 _)))
      have hterm2 : ∀ p ∈ Finset.Icc 2 P, Un (k := k) st m
          (S5.meanSource A u cS R p) ≤
          hierarchyLevelConstant P (K (m + 1 + 3 * P)) P * L ^ 6 * lam ^ (-5 / 2 : ℝ) :=
        fun p hp => by
        have h2 : s.meanSource m p ≤ hierarchyLevelConstant P (K (m + 1 + 3 * P)) P * L ^ 5 *
            lam ^ hierarchyMeanExponent p := (hlevM p (hmem p hp)).meanSource
        rw [hsMeanSrc m p hp] at h2
        have e : lam ^ hierarchyMeanExponent p ≤ lam ^ (-5 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlam (by
            unfold hierarchyMeanExponent
            have : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp hp).1
            linarith)
        have hL56 : L ^ 5 ≤ L ^ 6 := pow_le_pow_right₀ hL1 (by norm_num)
        refine h2.trans ?_
        calc hierarchyLevelConstant P (K (m + 1 + 3 * P)) P * L ^ 5 * lam ^ hierarchyMeanExponent p
            ≤ hierarchyLevelConstant P (K (m + 1 + 3 * P)) P * L ^ 5 * lam ^ (-5 / 2 : ℝ) :=
              mul_le_mul_of_nonneg_left e (mul_nonneg hAm0 (pow_nonneg hL0 _))
          _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL56 hAm0) hX
      have hs1 := seminorm_finset_le (Un (k := k) st m) (Finset.Icc 2 P) (fun p => u.B p)
        (fun _ => hierarchyLevelConstant P (K (m + 1 + 3 * P)) P * L ^ 6 * lam ^ (-5 / 2 : ℝ))
        hterm1
      have hs2 := seminorm_finset_le (Un (k := k) st m) (Finset.Icc 2 P)
        (fun p => S5.meanSource A u cS R p)
        (fun _ => hierarchyLevelConstant P (K (m + 1 + 3 * P)) P * L ^ 6 * lam ^ (-5 / 2 : ℝ))
        hterm2
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hs1 hs2
      have hcard : ((P + 1 - 2 : ℕ) : ℝ) ≤ P := Nat.cast_le.mpr (by omega)
      have hcard0 : (0 : ℝ) ≤ ((P + 1 - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
      have hL6' := hLe 6 le_rfl
      have h1 : 0 ≤ hierarchyLevelConstant P (K (m + 1 + 3 * P)) P * lam ^ (-5 / 2 : ℝ) :=
        mul_nonneg hAm0 hX
      have hb : hierarchyLevelConstant P (K (m + 1 + 3 * P)) P * L ^ 6 * lam ^ (-5 / 2 : ℝ) ≤
          hierarchyLevelConstant P (K (m + 1 + 3 * P)) P * D ^ (6 * c) * lam ^ (-5 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL6' hAm0) hX
      have hD6 : 0 ≤ D ^ (6 * c) := pow_nonneg hD0.le _
      have hm0 := le_max_right (KP m P) 0
      show _ ≤ (max (KP m P) 0 + 2 * (P : ℝ) * hierarchyLevelConstant P (K (m + 1 + 3 * P)) P) *
        D ^ (6 * c) * lam ^ (-5 / 2 : ℝ)
      have hb2 : ((P + 1 - 2 : ℕ) : ℝ) * (hierarchyLevelConstant P (K (m + 1 + 3 * P)) P * L ^ 6 *
          lam ^ (-5 / 2 : ℝ)) ≤ (P : ℝ) * (hierarchyLevelConstant P (K (m + 1 + 3 * P)) P *
          D ^ (6 * c) * lam ^ (-5 / 2 : ℝ)) :=
        mul_le_mul hcard hb (mul_nonneg (mul_nonneg hAm0 (pow_nonneg hL0 _)) hX) hP0
      have hq : 0 ≤ max (KP m P) 0 * (D ^ (6 * c) * lam ^ (-5 / 2 : ℝ)) :=
        mul_nonneg (le_max_right _ _) (mul_nonneg hD6 hX)
      have hs1' : S5.uNorm ℓ h m (∑ p ∈ Finset.Icc 2 P, u.B p) ≤ ((P + 1 - 2 : ℕ) : ℝ) *
          (hierarchyLevelConstant P (K (m + 1 + 3 * P)) P * L ^ 6 * lam ^ (-5 / 2 : ℝ)) := hs1
      have hs2' : S5.uNorm ℓ h m (∑ p ∈ Finset.Icc 2 P, S5.meanSource A u cS R p) ≤
          ((P + 1 - 2 : ℕ) : ℝ) * (hierarchyLevelConstant P (K (m + 1 + 3 * P)) P * L ^ 6 *
            lam ^ (-5 / 2 : ℝ)) := hs2
      nlinarith [hs1', hs2', hb2, hq]
  · -- (5.38)
    intro m
    have h := hrem hL6 m
    refine h.trans ?_
    have hAm : 0 ≤ hierarchyLevelConstant P (K (m + 1 + 3 * P)) P :=
      zero_le_one.trans (hierarchyLevelConstant_one_le (zero_le_one.trans (hK1 _)) P)
    have hTg0 : 0 ≤ lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * (P : ℝ) / 3) := mul_nonneg (hRpow _) (hRpow _)
    have : 0 ≤ 2 * (P : ℝ) * hierarchyLevelConstant P (K (m + 1 + 3 * P)) P := by positivity
    have hm0 := le_max_left (KP m P) 0
    show _ ≤ (max (KP m P) 0 + 2 * (P : ℝ) * hierarchyLevelConstant P (K (m + 1 + 3 * P)) P) *
      lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * (P : ℝ) / 3)
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) hTg0

end

end TorusEuler.Paper
