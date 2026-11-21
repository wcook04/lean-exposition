import TorusEuler.HierarchyTwistedFastSourceBounds
import TorusEuler.HierarchyTwistedSlowSourceBounds

/-! Slow source estimates on the full parent slab and the active wave interval. -/

open Set

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

set_option maxHeartbeats 1400000

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)
local notation "[" ℓ "," h "," n "," hT "]ᵁ" => unweightedSeminorm False ℓ h n hT
local notation "slowCost(" n "," L ")" => (3 * hierarchyQuadraticConstant (Fin 4) n ^ 2 * L)

private theorem slowCost_nonneg (holder : Prop) (ℓ h : ℝ) (n : ℕ) (hT : 0 < T)
    (G : MP) {L : ℝ} (hG : ∀ i : Fin 3,
      unweightedSeminorm holder ℓ h n hT (scaledCoframeRowProfile ℓ G i) ≤ L) :
    0 ≤ slowCost(n, L) := by
  have hL := (apply_nonneg _ _).trans (hG 0)
  positivity

/-- The unweighted slow advection bound applies across the full parent slab. -/
theorem unweightedSeminorm_labelAdv_le (hT : 0 < T) (G M : MP) (κ z g : VP)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) {L : ℝ}
    (hG : ∀ i : Fin 3, [ℓ,h,n,hT]ᵁ (scaledCoframeRowProfile ℓ G i) ≤ L) :
    [ℓ,h,n,hT]ᵁ ((twistedHierarchyOperators hT G M κ).labelAdv z g) ≤
      slowCost(n, L) * [ℓ,h,n,hT]ᵁ z * [ℓ,h,n+1,hT]ᵁ g := by
  have hraw := boundedWeightSeminorm_labelAdv_le hT G M κ z g ℓ h hℓ n hG
    (Subset.rfl : Icc 0 T ⊆ Icc 0 T) (fun _ => 1) (fun _ => 1)
    (R := 1) (Q := 1) (by simp) (by simp)
  dsimp only at hraw
  simp only [unweightedSeminorm, boundedWeightSeminorm_apply] at hraw ⊢
  simpa only [mul_one] using hraw

/-- The unweighted divergence product has one extra derivative on the
factor in the label divergence. -/
theorem unweightedSeminorm_slowLabelDivergenceProduct_le (holder : Prop) (hT : 0 < T)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) (G : MP) (V Y : VP) {L : ℝ}
    (hG : ∀ i : Fin 3, unweightedSeminorm holder ℓ h n hT (scaledCoframeRowProfile ℓ G i) ≤ L) :
    unweightedSeminorm holder ℓ h n hT (slowLabelDivergenceProduct hT G V Y) ≤
      slowCost(n, L) * unweightedSeminorm holder ℓ h (n + 1) hT V *
        unweightedSeminorm holder ℓ h n hT Y :=
  boundedWeightSeminorm_slowLabelDivergenceProduct_le (Subset.rfl : Icc 0 T ⊆ Icc 0 T)
    holder hT ℓ h hℓ n G V Y hG (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (CV := 1) (CY := 1) (CP := 1) (by simp) (by simp) (by simp) (by simp)

section Active

variable {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
  (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)

local notation "[" ℓ "," h "," n "," hT "]ᵂ" => amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos

private theorem restrictedUnweighted_le (holder : Prop) (ℓ h : ℝ) (n : ℕ) (hT : 0 < T)
    (f : VP) :
    boundedWeightSeminorm holder ℓ h n hT (Icc_subset_Icc_left ht₀) (fun _ => 1) (B := 1)
      (by simp) f ≤ unweightedSeminorm holder ℓ h n hT f :=
  boundedWeightSeminorm_mono_time holder ℓ h n hT (Icc_subset_Icc_left ht₀)
    (Subset.rfl : Icc 0 T ⊆ Icc 0 T) (fun _ => 1) (C := 1) (by simp) f

/-- Put the reciprocal amplitude on the advecting factor and measure the
unweighted differentiated factor on the full slab. -/
theorem amplitudeSeminorm_labelAdv_left_le (hT : 0 < T) (G M : MP) (κ z g : VP)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) {L : ℝ}
    (hG : ∀ i : Fin 3, [ℓ,h,n,hT]ᵁ (scaledCoframeRowProfile ℓ G i) ≤ L) :
    [ℓ,h,n,hT]ᵂ ((twistedHierarchyOperators hT G M κ).labelAdv z g) ≤
      slowCost(n, L) * [ℓ,h,n,hT]ᵂ z * [ℓ,h,n+1,hT]ᵁ g := by
  have hτ := (inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos).choose_spec
  have hraw := boundedWeightSeminorm_labelAdv_le hT G M κ z g ℓ h hℓ n hG
    (Icc_subset_Icc_left ht₀) (fun t => (γ t)⁻¹) (fun _ => 1) (Q := 1) hτ (by simp)
  have hbound : [ℓ,h,n,hT]ᵂ ((twistedHierarchyOperators hT G M κ).labelAdv z g) ≤
      slowCost(n, L) * [ℓ,h,n,hT]ᵂ z *
        boundedWeightSeminorm False ℓ h (n + 1) hT (Icc_subset_Icc_left ht₀)
          (fun _ => 1) (B := 1) (by simp) g := by
    dsimp only at hraw
    simp only [amplitudeSeminorm_apply, boundedWeightSeminorm_apply] at hraw ⊢
    simpa only [mul_one] using hraw
  exact hbound.trans (mul_le_mul_of_nonneg_left (restrictedUnweighted_le ht₀ False ℓ h (n + 1) hT g)
    (mul_nonneg (slowCost_nonneg False ℓ h n hT G hG) (apply_nonneg _ _)))

/-- Put the reciprocal amplitude on the differentiated factor and measure
its advector without the amplitude weight over the full slab. -/
theorem amplitudeSeminorm_labelAdv_right_le (hT : 0 < T) (G M : MP) (κ z g : VP)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) {L : ℝ}
    (hG : ∀ i : Fin 3, [ℓ,h,n,hT]ᵁ (scaledCoframeRowProfile ℓ G i) ≤ L) :
    [ℓ,h,n,hT]ᵂ ((twistedHierarchyOperators hT G M κ).labelAdv z g) ≤
      slowCost(n, L) * [ℓ,h,n,hT]ᵁ z * [ℓ,h,n+1,hT]ᵂ g := by
  have hτ := (inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos).choose_spec
  have hraw := boundedWeightSeminorm_labelAdv_le hT G M κ z g ℓ h hℓ n hG
    (Icc_subset_Icc_left ht₀) (fun _ => 1) (fun t => (γ t)⁻¹) (R := 1) (by simp) hτ
  have hbound : [ℓ,h,n,hT]ᵂ ((twistedHierarchyOperators hT G M κ).labelAdv z g) ≤
      slowCost(n, L) *
        boundedWeightSeminorm False ℓ h n hT (Icc_subset_Icc_left ht₀) (fun _ => 1) (B := 1)
          (by simp) z * [ℓ,h,n+1,hT]ᵂ g := by
    dsimp only at hraw
    simp only [amplitudeSeminorm_apply, boundedWeightSeminorm_apply] at hraw ⊢
    simpa only [one_mul] using hraw
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (restrictedUnweighted_le ht₀ False ℓ h n hT z)
      (slowCost_nonneg False ℓ h n hT G hG)) (apply_nonneg _ _))

/-- The differentiated factor of the slow divergence product carries the
reciprocal amplitude. -/
theorem amplitudeSeminorm_slowLabelDivergenceProduct_left_le (holder : Prop) (hT : 0 < T)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) (G : MP) (V Y : VP) {L : ℝ}
    (hG : ∀ i : Fin 3, unweightedSeminorm holder ℓ h n hT (scaledCoframeRowProfile ℓ G i) ≤ L) :
    amplitudeSeminorm holder ℓ h n hT ht₀ htT γ hγ hpos (slowLabelDivergenceProduct hT G V Y) ≤
      slowCost(n, L) * amplitudeSeminorm holder ℓ h (n + 1) hT ht₀ htT γ hγ hpos V *
        unweightedSeminorm holder ℓ h n hT Y := by
  have hτ := (inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos).choose_spec
  have hbound := boundedWeightSeminorm_slowLabelDivergenceProduct_le (Icc_subset_Icc_left ht₀)
    holder hT ℓ h hℓ n G V Y hG (fun t => (γ t)⁻¹) (fun _ => 1) (fun t => (γ t)⁻¹)
    (CY := 1) hτ (by simp) hτ (by simp)
  exact hbound.trans (mul_le_mul_of_nonneg_left (restrictedUnweighted_le ht₀ holder ℓ h n hT Y)
    (mul_nonneg (slowCost_nonneg holder ℓ h n hT G hG) (apply_nonneg _ _)))

/-- The undifferentiated factor may carry the reciprocal amplitude instead. -/
theorem amplitudeSeminorm_slowLabelDivergenceProduct_right_le (holder : Prop) (hT : 0 < T)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) (G : MP) (V Y : VP) {L : ℝ}
    (hG : ∀ i : Fin 3, unweightedSeminorm holder ℓ h n hT (scaledCoframeRowProfile ℓ G i) ≤ L) :
    amplitudeSeminorm holder ℓ h n hT ht₀ htT γ hγ hpos (slowLabelDivergenceProduct hT G V Y) ≤
      slowCost(n, L) * unweightedSeminorm holder ℓ h (n + 1) hT V *
        amplitudeSeminorm holder ℓ h n hT ht₀ htT γ hγ hpos Y := by
  have hτ := (inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos).choose_spec
  have hbound := boundedWeightSeminorm_slowLabelDivergenceProduct_le (Icc_subset_Icc_left ht₀)
    holder hT ℓ h hℓ n G V Y hG (fun _ => 1) (fun t => (γ t)⁻¹) (fun t => (γ t)⁻¹)
    (CV := 1) (by simp) hτ hτ (by simp)
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (restrictedUnweighted_le ht₀ holder ℓ h (n + 1) hT V)
      (slowCost_nonneg holder ℓ h n hT G hG)) (apply_nonneg _ _))

/-- Subtracting the phase average removes the mean–mean term. The resulting
weighted source has the two mixed terms and the oscillation–oscillation term. -/
theorem amplitudeSeminorm_centered_labelProduct_le (hT : 0 < T) (G M : MP) (κ : VP)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) {L : ℝ}
    (hG : ∀ i : Fin 3, [ℓ,h,n,hT]ᵁ (scaledCoframeRowProfile ℓ G i) ≤ L)
    (u : HierarchyProfiles VP SP) (i j : ℕ)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hzero : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, (u.Y j).val.val.val (t, x) = 0)
    (hmean : let A := twistedHierarchyOperators hT G M κ
      A.average (A.labelAdv (u.B i) (u.B j)) = A.labelAdv (u.B i) (u.B j)) :
    let A := twistedHierarchyOperators hT G M κ
    let F := A.labelProduct u (i, j)
    [ℓ,h,n,hT]ᵂ (F - A.average F) ≤
      (2 * slowCost(n, L)) * ([ℓ,h,n,hT]ᵂ (u.Y i) + [ℓ,h,n,hT]ᵁ (u.B i)) *
        ([ℓ,h,n+1,hT]ᵂ (u.Y j) + [ℓ,h,n+1,hT]ᵁ (u.B j)) := by
  let A := twistedHierarchyOperators hT G M κ
  let U (m : ℕ) : Seminorm ℝ VP := [ℓ,h,m,hT]ᵁ
  let W (m : ℕ) : Seminorm ℝ VP := [ℓ,h,m,hT]ᵂ
  let K := slowCost(n, L)
  let YY := A.labelAdv (u.Y i) (u.Y j)
  let YB := A.labelAdv (u.Y i) (u.B j)
  let BY := A.labelAdv (u.B i) (u.Y j)
  let F := YY + YB + BY
  have hK : 0 ≤ K := slowCost_nonneg False ℓ h n hT G hG
  have hy : U (n + 1) (u.Y j) ≤ W (n + 1) (u.Y j) :=
    unweightedSeminorm_le_amplitudeSeminorm_of_inactive False ℓ h (n + 1) hT ht₀ htT γ hγ hpos
      hγle (u.Y j) hzero
  have hYY : W n YY ≤ K * W n (u.Y i) * W (n + 1) (u.Y j) :=
    (amplitudeSeminorm_labelAdv_left_le ht₀ htT γ hγ hpos hT G M κ (u.Y i) (u.Y j)
      ℓ h hℓ n hG).trans (mul_le_mul_of_nonneg_left hy (mul_nonneg hK (apply_nonneg _ _)))
  have hYB : W n YB ≤ K * W n (u.Y i) * U (n + 1) (u.B j) :=
    amplitudeSeminorm_labelAdv_left_le ht₀ htT γ hγ hpos hT G M κ (u.Y i) (u.B j) ℓ h hℓ n hG
  have hBY : W n BY ≤ K * U n (u.B i) * W (n + 1) (u.Y j) :=
    amplitudeSeminorm_labelAdv_right_le ht₀ htT γ hγ hpos hT G M κ (u.B i) (u.Y j) ℓ h hℓ n hG
  have hcap : W n F ≤ K * (W n (u.Y i) + U n (u.B i)) * (W (n + 1) (u.Y j) + U (n + 1) (u.B j)) := by
    calc
      _ ≤ W n YY + W n YB + W n BY :=
        (map_add_le_add (W n) _ _).trans (add_le_add (map_add_le_add (W n) _ _) le_rfl)
      _ ≤ K * W n (u.Y i) * W (n + 1) (u.Y j) + K * W n (u.Y i) * U (n + 1) (u.B j) +
          K * U n (u.B i) * W (n + 1) (u.Y j) := add_le_add (add_le_add hYY hYB) hBY
      _ ≤ _ := by
        have hterm : 0 ≤ K * U n (u.B i) * U (n + 1) (u.B j) :=
          mul_nonneg (mul_nonneg hK (apply_nonneg _ _)) (apply_nonneg _ _)
        calc
          _ ≤ _ + K * U n (u.B i) * U (n + 1) (u.B j) := le_add_of_nonneg_right hterm
          _ = _ := by ring
  change W n (A.labelProduct u (i, j) - A.average (A.labelProduct u (i, j))) ≤ _
  rw [A.centered_labelProduct_eq u i j hmean]
  change W n (F - A.average F) ≤ _
  calc
    _ ≤ W n F + W n (A.average F) := map_sub_le_add (W n) _ _
    _ ≤ W n F + W n F := add_le_add le_rfl (amplitudeSeminorm_average_le ℓ h n hT G M κ F
      ht₀ htT γ hγ hpos)
    _ = 2 * W n F := (two_mul _).symm
    _ ≤ 2 * (K * (W n (u.Y i) + U n (u.B i)) *
        (W (n + 1) (u.Y j) + U (n + 1) (u.B j))) := mul_le_mul_of_nonneg_left hcap (by norm_num)
    _ = _ := by ring

/-- In the recurrence both factors of the centered slow term are
measured at the next order. -/
theorem amplitudeSeminorm_centered_labelProduct_le_succ (hT : 0 < T) (G M : MP) (κ : VP)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) {L : ℝ}
    (hG : ∀ i : Fin 3, [ℓ,h,n,hT]ᵁ (scaledCoframeRowProfile ℓ G i) ≤ L)
    (u : HierarchyProfiles VP SP) (i j : ℕ)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hzero : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, (u.Y j).val.val.val (t, x) = 0)
    (hmean : let A := twistedHierarchyOperators hT G M κ
      A.average (A.labelAdv (u.B i) (u.B j)) = A.labelAdv (u.B i) (u.B j)) :
    let A := twistedHierarchyOperators hT G M κ
    let F := A.labelProduct u (i, j)
    [ℓ,h,n,hT]ᵂ (F - A.average F) ≤
      (2 * slowCost(n, L)) * ([ℓ,h,n+1,hT]ᵂ (u.Y i) + [ℓ,h,n+1,hT]ᵁ (u.B i)) *
        ([ℓ,h,n+1,hT]ᵂ (u.Y j) + [ℓ,h,n+1,hT]ᵁ (u.B j)) := by
  refine (amplitudeSeminorm_centered_labelProduct_le ht₀ htT γ hγ hpos hT G M κ
    ℓ h hℓ n hG u i j hγle hzero hmean).trans ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) ?_)
    (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
  · exact amplitudeSeminorm_mono_order False ℓ h (Nat.le_succ n) hT ht₀ htT γ hγ hpos (u.Y i)
  · exact unweightedSeminorm_mono_order False ℓ h (Nat.le_succ n) hT (u.B i)
  · exact mul_nonneg zero_le_two (slowCost_nonneg False ℓ h n hT G hG)

/-- The three slow terms of the mean forcing consume one extra order.
The full-slab oscillation norms are bounded by the active norms since
these profiles vanish before activation. -/
theorem actualMeasuredLevels_meanForcing_slow_terms (hT : 0 < T) (G M : MP) (κ : VP)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) {L : ℝ}
    (hG : ∀ i : Fin 3, [ℓ,h,n,hT]ᵁ (scaledCoframeRowProfile ℓ G i) ≤ L)
    (u : HierarchyProfiles VP SP) (P : ℕ) (completionSwitch residual : VP) (freq : ℝ)
    (hf : 0 ≤ freq) (i j : ℕ)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hY : ∀ p, ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, (u.Y p).val.val.val (t, x) = 0)
    (hV : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, (u.V i).val.val.val (t, x) = 0) :
    let A := twistedHierarchyOperators hT G M κ
    let s := actualMeasuredLevels A u P completionSwitch residual freq hf ℓ h hT ht₀ htT γ hγ hpos
    [ℓ,h,n,hT]ᵁ (A.average (A.labelAdv (u.Y i) (u.Y j))) ≤
      slowCost(n, L) * (s.Y (n + 1) i * s.Y (n + 1) j) ∧
    [ℓ,h,n,hT]ᵁ (A.average (slowLabelDivergenceProduct hT G (u.V i) (u.Y j))) ≤
      slowCost(n, L) * (s.osc (n + 1) i * s.Y (n + 1) j) ∧
    [ℓ,h,n,hT]ᵁ (A.labelAdv (u.B i) (u.B j)) ≤
      slowCost(n, L) * (s.mean (n + 1) i * s.mean (n + 1) j) := by
  intro A s
  let U (m : ℕ) : Seminorm ℝ VP := [ℓ,h,m,hT]ᵁ
  let K := slowCost(n, L)
  have hK : 0 ≤ K := slowCost_nonneg False ℓ h n hT G hG
  have hYnext (p : ℕ) : U (n + 1) (u.Y p) ≤ s.Y (n + 1) p :=
    unweightedSeminorm_le_amplitudeSeminorm_of_inactive False ℓ h (n + 1) hT ht₀ htT γ hγ hpos
      hγle (u.Y p) (hY p)
  have hYhere (p : ℕ) : U n (u.Y p) ≤ s.Y (n + 1) p :=
    (unweightedSeminorm_mono_order False ℓ h (Nat.le_succ n) hT (u.Y p)).trans (hYnext p)
  have hVnext : U (n + 1) (u.V i) ≤ s.osc (n + 1) i := by
    refine (unweightedSeminorm_le_amplitudeSeminorm_of_inactive False ℓ h (n + 1) hT ht₀ htT
      γ hγ hpos hγle (u.V i) hV).trans ?_
    exact le_add_of_nonneg_right (mul_nonneg hf (apply_nonneg _ _))
  have hBhere : U n (u.B i) ≤ s.mean (n + 1) i :=
    unweightedSeminorm_mono_order False ℓ h (Nat.le_succ n) hT (u.B i)
  have habsorb {a b c d : ℝ} (ha : a ≤ c) (hb : b ≤ d) (hc : 0 ≤ c) (hb₀ : 0 ≤ b) :
      K * a * b ≤ K * (c * d) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul ha hb hb₀ hc) hK
  refine ⟨?_, ?_, ?_⟩
  · exact (unweightedSeminorm_average_le ℓ h n hT G M κ (A.labelAdv (u.Y i) (u.Y j))).trans
      ((unweightedSeminorm_labelAdv_le hT G M κ (u.Y i) (u.Y j) ℓ h hℓ n hG).trans
        (habsorb (hYhere i) (hYnext j) (s.nonneg _ _).2.2.2.2.2.1 (apply_nonneg _ _)))
  · exact (unweightedSeminorm_average_le ℓ h n hT G M κ
      (slowLabelDivergenceProduct hT G (u.V i) (u.Y j))).trans
      ((unweightedSeminorm_slowLabelDivergenceProduct_le False hT ℓ h hℓ n G (u.V i) (u.Y j)
        hG).trans (habsorb hVnext (hYhere j) (s.nonneg _ _).2.2.1 (apply_nonneg _ _)))
  · exact (unweightedSeminorm_labelAdv_le hT G M κ (u.B i) (u.B j) ℓ h hℓ n hG).trans
      (habsorb hBhere le_rfl (s.nonneg _ _).2.2.2.1 (apply_nonneg _ _))

end Active

end

end TorusEuler.HierarchyTwistedProfile
