import TorusEuler.Paper.Proofs.S5b.T56Rec

/-!
# Theorem 5.6, glue: the product terms of the sources

The individual product bounds of the proof of Theorem 5.6
(`sections/06c_finite_hierarchy.tex:563-634`), in the form required by the measured recurrence
(`normRecurrence'`): for the mean source `⟨(Y_i·𝐝)Y_j⟩`, `⟨(𝐝·V_i)Y_j⟩`, `(B_i·𝐝)B_j`
(unweighted), for the oscillatory source the centered label products
`(Z_i·𝐝)Z_j - ⟨(Z_i·𝐝)Z_j⟩` ("subtracting the phase mean removes `(B_i·𝐝)B_j`, and every other
product has a factor `Y_i` or `Y_j`, to which we apply the `γ` norm", TeX :565-567) and the
phase products `(C_i·κ)∂_sY_j - ⟨…⟩`, `(B_i·κ)∂_sY_j`. All follow from (5.39)
(`T56Bounds`, i.e. Lemma D.1 with coefficient bounds) and the comparisons of norms.
-/

open Set

namespace TorusEuler.Paper.S5b

open AppendixD HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3} {ℓ h t₀ : ℝ} {γ : ℝ → ℝ}

local notation "VP" => HierarchyTwistedProfile T k Vec3

/-- The weighted norm as a seminorm. -/
abbrev Wn {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (st : NormSetting T ℓ h t₀ γ)
    (n : ℕ) : Seminorm ℝ (HierarchyTwistedProfile T k E) :=
  amplitudeSeminorm False ℓ h n st.hT st.ht₀ st.htT γ st.hγc st.hγ

/-- The unweighted norm on `[0,T]` as a seminorm. -/
abbrev Un {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (st : NormSetting T ℓ h t₀ γ)
    (n : ℕ) : Seminorm ℝ (HierarchyTwistedProfile T k E) :=
  unweightedSeminorm False ℓ h n st.hT

/-- A profile vanishing for `t < t₀`. -/
def VanishBefore (t₀ : ℝ) (f : VP) : Prop :=
  ∀ t ∈ Icc 0 T, t < t₀ → ∀ x s, f.val.val.val (t, x, s) = 0

/-- The constant of the label products, `c_n² N_G 3ℓ⁻¹`. -/
def labelConst (ℓ : ℝ) (NG : ℕ → ℝ) (n : ℕ) : ℝ :=
  productConst n * productConst n * NG n * (3 * ℓ⁻¹)

/-- The constant of the phase products, `c_n² N_κ h⁻¹`. -/
def phaseConst (h : ℝ) (Nk : ℕ → ℝ) (n : ℕ) : ℝ :=
  productConst n * productConst n * Nk n * h⁻¹

section Terms

variable {hT' : 0 < T} {U : Velocity} {X : ℝ → Velocity} {NG Nk : ℕ → ℝ}

/-- The inverse bound of a norm setting. -/
theorem NormSetting.invBound (st : NormSetting T ℓ h t₀ γ) :
    ∃ B, ∀ t ∈ Icc t₀ T, ‖(γ t)⁻¹‖ ≤ B :=
  inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr st.htT) st.hγc st.hγ

/-- The `W` seminorms are monotone in the level. -/
theorem W_mono (st : NormSetting T ℓ h t₀ γ) {n m : ℕ} (hnm : n ≤ m) (f : VP) :
    Wn st n f ≤ Wn st m f := by
  obtain ⟨B, hB⟩ := st.invBound
  exact Bridge.wNorm_mono_order ℓ h hnm st.hT st.ht₀ γ hB f

/-- The `U` seminorms are monotone in the level. -/
theorem U_mono (st : NormSetting T ℓ h t₀ γ) {n m : ℕ} (hnm : n ≤ m) (f : VP) :
    Un st n f ≤ Un st m f :=
  Bridge.uNorm_mono_order ℓ h hnm st.hT f

/-- The `U` seminorm is at most the `W` seminorm for profiles vanishing before `t0`. -/
theorem U_le_W (st : NormSetting T ℓ h t₀ γ) (n : ℕ) {f : VP} (hf : VanishBefore t₀ f) :
    Un st n f ≤ Wn st n f :=
  uNorm_le_wNorm st.hT st.ht₀ st.htT st.hγc st.hγ st.hγ1 n hf

/-- The plain seminorm is at most the `W` seminorm. -/
theorem P_le_W (st : NormSetting T ℓ h t₀ γ) (n : ℕ) (f : VP) : plain ℓ h t₀ n f ≤ Wn st n f :=
  plain_le_wNorm st.hT st.ht₀ st.htT st.hγc st.hγ st.hγ1 n f

/-- The plain seminorm is at most the `U` seminorm. -/
theorem P_le_U (st : NormSetting T ℓ h t₀ γ) (n : ℕ) (f : VP) : plain ℓ h t₀ n f ≤ Un st n f :=
  plain_le_uNorm st.hT st.ht₀ n f

/-- Nonnegativity of the label constant from coefficient bounds. -/
theorem labelConst_nonneg {NG Nk : ℕ → ℝ} (hc : CoefBounds T ℓ h X k NG Nk) (hℓ : 0 < ℓ)
    (n : ℕ) : 0 ≤ labelConst ℓ NG n := by
  have hNG : 0 ≤ NG n := (fieldNorm_nonneg (hc ∅ (empty_subset _) n).1.1).trans
    (hc ∅ (empty_subset _) n).1.2
  have := productConst_nonneg n
  unfold labelConst
  positivity

/-- Nonnegativity of the phase constant from coefficient bounds. -/
theorem phaseConst_nonneg {NG Nk : ℕ → ℝ} (hc : CoefBounds T ℓ h X k NG Nk) (hh : 0 < h)
    (n : ℕ) : 0 ≤ phaseConst h Nk n := by
  have hNk : 0 ≤ Nk n := (fieldNorm_nonneg (hc ∅ (empty_subset _) n).2.1).trans
    (hc ∅ (empty_subset _) n).2.2
  have := productConst_nonneg n
  unfold phaseConst
  positivity

/-- `‖⟨(f·𝐝)g⟩‖_{[n]} ≤ Λ_n ‖f‖_{[n+1],γ} ‖g‖_{[n+1],γ}` for fields vanishing before `t₀`. -/
theorem term_YY (hD_1 : Statement.lemma_D_1) (st : NormSetting T ℓ h t₀ γ)
    (d : ParentGeometry hT' U X k) (hc : CoefBounds T ℓ h X k NG Nk) (n : ℕ) {f g : VP}
    (hf : VanishBefore t₀ f) (hg : VanishBefore t₀ g) :
    Un st n ((S5.ops d).average ((S5.ops d).labelAdv f g)) ≤
      labelConst ℓ NG n * (Wn st (n + 1) f * Wn st (n + 1) g) := by
  have h1 := uNorm_average hD_1 st d n ((S5.ops d).labelAdv f g)
  have h2 := uNorm_labelAdv hD_1 st d hc n f g
  have hf' : Un st n f ≤ Wn st (n + 1) f := (U_le_W st n hf).trans (W_mono st (Nat.le_succ n) f)
  have hg' : Un st (n + 1) g ≤ Wn st (n + 1) g := U_le_W st (n + 1) hg
  calc Un st n ((S5.ops d).average ((S5.ops d).labelAdv f g))
      ≤ productConst n * (productConst n * NG n * Un st n f) * (3 * ℓ⁻¹ * Un st (n + 1) g) :=
        h1.trans h2
    _ = labelConst ℓ NG n * (Un st n f * Un st (n + 1) g) := by unfold labelConst; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul hf' hg' (apply_nonneg _ _) (apply_nonneg _ _))
        (labelConst_nonneg hc st.hℓ n)

/-- `‖⟨(𝐝·V)Y⟩‖_{[n]} ≤ Λ_n ‖V‖_{[n+1],γ} ‖Y‖_{[n+1],γ}`. -/
theorem term_divY (hD_1 : Statement.lemma_D_1) (st : NormSetting T ℓ h t₀ γ)
    (d : ParentGeometry hT' U X k) (hc : CoefBounds T ℓ h X k NG Nk) (n : ℕ) {V Y : VP}
    (hV : VanishBefore t₀ V) (hY : VanishBefore t₀ Y) :
    Un st n ((S5.ops d).average (slowLabelDivergenceProduct hT' d.inverse V Y)) ≤
      labelConst ℓ NG n * (Wn st (n + 1) V * Wn st (n + 1) Y) := by
  have h1 := uNorm_average hD_1 st d n (slowLabelDivergenceProduct hT' d.inverse V Y)
  have h2 := uNorm_divProduct hD_1 st d hc n V Y
  have hV' : Un st (n + 1) V ≤ Wn st (n + 1) V := U_le_W st (n + 1) hV
  have hY' : Un st n Y ≤ Wn st (n + 1) Y := (U_le_W st n hY).trans (W_mono st (Nat.le_succ n) Y)
  calc Un st n ((S5.ops d).average (slowLabelDivergenceProduct hT' d.inverse V Y))
      ≤ productConst n * (productConst n * NG n * (3 * ℓ⁻¹ * Un st (n + 1) V)) * Un st n Y :=
        h1.trans h2
    _ = labelConst ℓ NG n * (Un st (n + 1) V * Un st n Y) := by unfold labelConst; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul hV' hY' (apply_nonneg _ _) (apply_nonneg _ _))
        (labelConst_nonneg hc st.hℓ n)

/-- `‖(B·𝐝)B'‖_{[n]} ≤ Λ_n ‖B‖_{[n+1]} ‖B'‖_{[n+1]}`. -/
theorem term_BB (hD_1 : Statement.lemma_D_1) (st : NormSetting T ℓ h t₀ γ)
    (d : ParentGeometry hT' U X k) (hc : CoefBounds T ℓ h X k NG Nk) (n : ℕ) (B B' : VP) :
    Un st n ((S5.ops d).labelAdv B B') ≤
      labelConst ℓ NG n * (Un st (n + 1) B * Un st (n + 1) B') := by
  have h2 := uNorm_labelAdv hD_1 st d hc n B B'
  calc Un st n ((S5.ops d).labelAdv B B')
      ≤ productConst n * (productConst n * NG n * Un st n B) * (3 * ℓ⁻¹ * Un st (n + 1) B') := h2
    _ = labelConst ℓ NG n * (Un st n B * Un st (n + 1) B') := by unfold labelConst; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (U_mono st (Nat.le_succ n) B)
        (apply_nonneg _ _)) (labelConst_nonneg hc st.hℓ n)

set_option maxHeartbeats 1600000 in
/-- **The centered label product** of `Z = Y + B`, `Z' = Y' + B'` (`Y`, `Y'` vanishing before
`t₀`, `B`, `B'` phase independent): `‖(Z·𝐝)Z' - ⟨…⟩‖_{[n],γ} ≤ 2Λ_n (‖Y‖_γ + ‖B‖)(‖Y'‖_γ + ‖B'‖)`
at order `n+1` (TeX :565-567). -/
theorem term_slow (hD_1 : Statement.lemma_D_1) (st : NormSetting T ℓ h t₀ γ)
    (d : ParentGeometry hT' U X k) (hc : CoefBounds T ℓ h X k NG Nk) (n : ℕ) {Y Y' B B' : VP}
    (hB : (S5.ops d).average B = B) (hB' : (S5.ops d).average B' = B') :
    Wn st n ((S5.ops d).labelAdv (Y + B) (Y' + B') -
        (S5.ops d).average ((S5.ops d).labelAdv (Y + B) (Y' + B'))) ≤
      2 * labelConst ℓ NG n * ((Wn st (n + 1) Y + Un st (n + 1) B) *
        (Wn st (n + 1) Y' + Un st (n + 1) B')) := by
  set A := S5.ops d
  have hBB : A.average (A.labelAdv B B') = A.labelAdv B B' :=
    average_labelAdv_independent_independent hT' d.inverse d.strain d.covector B B'
      d.mean.inverse_independent hB hB'
  set F := A.labelAdv Y Y' + A.labelAdv Y B' + A.labelAdv B Y'
  have hsplit : A.labelAdv (Y + B) (Y' + B') - A.average (A.labelAdv (Y + B) (Y' + B')) =
      F - A.average F := by
    have hexp : A.labelAdv (Y + B) (Y' + B') = F + A.labelAdv B B' := by
      simp only [F, map_add, LinearMap.add_apply]
      abel
    rw [hexp, map_add, hBB]
    abel
  rw [hsplit]
  have hc0 := labelConst_nonneg hc st.hℓ n
  have hYY : Wn st n (A.labelAdv Y Y') ≤ productConst n * (productConst n * NG n * plain ℓ h t₀ n Y) *
      (3 * ℓ⁻¹ * Wn st (n + 1) Y') := wNorm_labelAdv_right hD_1 st d hc n Y Y'
  have hYB : Wn st n (A.labelAdv Y B') ≤ productConst n * (3 * ℓ⁻¹ * plain ℓ h t₀ (n + 1) B') *
      (productConst n * NG n * Wn st n Y) := wNorm_labelAdv_left hD_1 st d hc n Y B'
  have hBY : Wn st n (A.labelAdv B Y') ≤ productConst n * (productConst n * NG n * plain ℓ h t₀ n B) *
      (3 * ℓ⁻¹ * Wn st (n + 1) Y') := wNorm_labelAdv_right hD_1 st d hc n B Y'
  have hY1 : plain ℓ h t₀ n Y ≤ Wn st (n + 1) Y := (P_le_W st n Y).trans (W_mono st (Nat.le_succ n) Y)
  have hY2 : Wn st n Y ≤ Wn st (n + 1) Y := W_mono st (Nat.le_succ n) Y
  have hB1 : plain ℓ h t₀ (n + 1) B' ≤ Un st (n + 1) B' := P_le_U st (n + 1) B'
  have hB2 : plain ℓ h t₀ n B ≤ Un st (n + 1) B := (P_le_U st n B).trans (U_mono st (Nat.le_succ n) B)
  have e1 : Wn st n (A.labelAdv Y Y') ≤ labelConst ℓ NG n * (Wn st (n + 1) Y * Wn st (n + 1) Y') := by
    refine hYY.trans (le_of_eq_of_le (by unfold labelConst; ring) (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hY1 (apply_nonneg _ _)) hc0))
  have e2 : Wn st n (A.labelAdv Y B') ≤ labelConst ℓ NG n * (Wn st (n + 1) Y * Un st (n + 1) B') := by
    refine hYB.trans (le_of_eq_of_le (by unfold labelConst; ring) (mul_le_mul_of_nonneg_left
      (mul_le_mul hY2 hB1 (fieldNorm_nonneg (NormSetting.finP st (n + 1) B')) (apply_nonneg _ _))
      hc0))
  have e3 : Wn st n (A.labelAdv B Y') ≤ labelConst ℓ NG n * (Un st (n + 1) B * Wn st (n + 1) Y') := by
    refine hBY.trans (le_of_eq_of_le (by unfold labelConst; ring) (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hB2 (apply_nonneg _ _)) hc0))
  have hcen := wNorm_center hD_1 st d n F
  have hF : Wn st n F ≤ labelConst ℓ NG n * (Wn st (n + 1) Y * Wn st (n + 1) Y' +
      Wn st (n + 1) Y * Un st (n + 1) B' + Un st (n + 1) B * Wn st (n + 1) Y') := by
    refine ((map_add_le_add _ _ _).trans (add_le_add (map_add_le_add _ _ _) le_rfl)).trans ?_
    rw [mul_add, mul_add]
    exact add_le_add (add_le_add e1 e2) e3
  have hprod : Wn st (n + 1) Y * Wn st (n + 1) Y' + Wn st (n + 1) Y * Un st (n + 1) B' +
      Un st (n + 1) B * Wn st (n + 1) Y' ≤
        (Wn st (n + 1) Y + Un st (n + 1) B) * (Wn st (n + 1) Y' + Un st (n + 1) B') := by
    have := mul_nonneg (apply_nonneg (Un (E := Vec3) (k := k) st (n + 1)) B)
      (apply_nonneg (Un (E := Vec3) (k := k) st (n + 1)) B')
    nlinarith
  calc Wn st n (F - A.average F) ≤ 2 * Wn st n F := hcen
    _ ≤ 2 * (labelConst ℓ NG n * (Wn st (n + 1) Y * Wn st (n + 1) Y' +
      Wn st (n + 1) Y * Un st (n + 1) B' + Un st (n + 1) B * Wn st (n + 1) Y')) :=
        mul_le_mul_of_nonneg_left hF (by norm_num)
    _ ≤ 2 * (labelConst ℓ NG n * ((Wn st (n + 1) Y + Un st (n + 1) B) *
        (Wn st (n + 1) Y' + Un st (n + 1) B'))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod hc0) (by norm_num)
    _ = _ := by ring

/-- **The centered completion phase product**: `‖(C·κ)∂_sY - ⟨…⟩‖_{[n],γ} ≤ 2Λ'_n ‖C‖_{[n],γ}
‖Y‖_{[n+1],γ}` (TeX :574-579, `Λ'_n = c_n² N_κ h⁻¹`, of size `𝖣^C λ^{3/2}`). -/
theorem term_fastC (hD_1 : Statement.lemma_D_1) (st : NormSetting T ℓ h t₀ γ)
    (d : ParentGeometry hT' U X k) (hc : CoefBounds T ℓ h X k NG Nk) (n : ℕ) (C Y : VP) :
    Wn st n ((S5.ops d).phaseAdv C Y - (S5.ops d).average ((S5.ops d).phaseAdv C Y)) ≤
      2 * phaseConst h Nk n * (Wn st n C * Wn st (n + 1) Y) := by
  have hcen := wNorm_center hD_1 st d n ((S5.ops d).phaseAdv C Y)
  have hb : Wn st n ((S5.ops d).phaseAdv C Y) ≤ productConst n * (h⁻¹ * plain ℓ h t₀ (n + 1) Y) *
      (productConst n * Nk n * Wn st n C) := wNorm_phaseAdv_left hD_1 st d hc n C Y
  have hc0 := phaseConst_nonneg hc st.hh n
  have hP : plain ℓ h t₀ (n + 1) Y ≤ Wn st (n + 1) Y := P_le_W st (n + 1) Y
  have e : Wn st n ((S5.ops d).phaseAdv C Y) ≤ phaseConst h Nk n * (Wn st n C * Wn st (n + 1) Y) := by
    refine hb.trans (le_of_eq_of_le (by unfold phaseConst; ring) (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hP (apply_nonneg _ _)) hc0))
  calc _ ≤ 2 * Wn st n ((S5.ops d).phaseAdv C Y) := hcen
    _ ≤ 2 * (phaseConst h Nk n * (Wn st n C * Wn st (n + 1) Y)) :=
        mul_le_mul_of_nonneg_left e (by norm_num)
    _ = _ := by ring

/-- **The mean phase product**: `‖(B·κ)∂_sY‖_{[n],γ} ≤ Λ'_n ‖B‖_{[n]} ‖Y‖_{[n+1],γ}`
(TeX :623-634). -/
theorem term_fastB (hD_1 : Statement.lemma_D_1) (st : NormSetting T ℓ h t₀ γ)
    (d : ParentGeometry hT' U X k) (hc : CoefBounds T ℓ h X k NG Nk) (n : ℕ) (B Y : VP) :
    Wn st n ((S5.ops d).phaseAdv B Y) ≤ phaseConst h Nk n * (Un st n B * Wn st (n + 1) Y) := by
  have hb : Wn st n ((S5.ops d).phaseAdv B Y) ≤ productConst n * (productConst n * Nk n * plain ℓ h t₀ n B) *
      (h⁻¹ * Wn st (n + 1) Y) := wNorm_phaseAdv_right hD_1 st d hc n B Y
  have hc0 := phaseConst_nonneg hc st.hh n
  refine hb.trans (le_of_eq_of_le (by unfold phaseConst; ring) (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (P_le_U st n B) (apply_nonneg _ _)) hc0))

end Terms

end

end TorusEuler.Paper.S5b
