import TorusEuler.Paper.Proofs.S5b.Lemma58D

/-!
# Lemma 5.8 from Lemmas 5.3, 5.5, 5.7, Proposition 5.4, Theorem 5.6 and the oddness of `W^♮`

`S5b.lemma_5_8_of_odd` proves `Statement.lemma_5_8` from the statements of the cited results
and the oddness of the Eulerian expansion `W^♮` (`S5b.OddExpansions`), which the text derives
from "the symmetry of the construction of Subsection 5.5 under `(a,s) ↦ (-a,-s)`"
(`sections/08_exact_wave.tex:121-123`). Each cited result is used where the TeX proof
(`08_exact_wave.tex:108-144`) uses it; see the docstring of the theorem.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.S5b

open HierarchyTwistedProfile

noncomputable section

/-- The Eulerian expansion `W^♮` of every expansion is odd (for `a` large). -/
def OddExpansions : Prop :=
  ∃ a₁ : ℕ, ∀ a : ℕ, a₁ ≤ a →
    ∀ {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
      {D lam t₀ : ℝ} {center : ℝ → Vec3} (d : ParentGeometry hT U X k) (χ : PaperWaveCutoff t₀ T),
      S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ → S5.Origin T U X k D lam t₀ center →
      ∀ amp : ℝ → Vec3 → Vec3, S5.IsSeed U X k t₀ T center amp →
      ∀ P : ℕ, 2 ≤ P →
      ∀ (R S : HierarchyTwistedProfile T k Vec3)
        (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)),
        S5.IsExpansion d pU χ (S5.radius D a) (S5.width lam) amp P R S u →
        ∀ t ∈ Icc 0 T, Function.Odd (graphRead (fun r => X r 0) (S5.expansion u P) t)

set_option maxHeartbeats 1600000 in
/-- **Lemma 5.8 from its cited results and the oddness of `W^♮`** (`08_exact_wave.tex:108-144`).

* `h5_4` (Proposition 5.4): `𝐝̃·W = 0` (divergence of `V`), the identity (5.29) (equation
  (5.46), via `approx_residual`), `W_osc = ∑(V_i + C_{i+1})` with its support in `supp g` and
  its vanishing before `t₀` (hypothesis of Lemma 5.7 for `W_osc`, and (5.47), (5.48) before
  `t₀`), and `R_P` independent of the phase outside `supp g` (hypothesis of Lemma 5.7 for `R_P`).
* `h5_6` (Theorem 5.6), whose hypothesis `𝖣^{C₆}λ^{-1/12} ≤ 1` follows from (5.43)
  (`08_exact_wave.tex:25-27`): (5.37) at order `0` for (5.47) and at order `m+1` for (5.48)
  (`W_osc`, `W̄`), and (5.38) at order `2` for `R_P`.
* `h5_7` (Lemma 5.7): (5.45) weighted for `W_osc`, phase-independent on `[0,T]` for `W̄`,
  unweighted at `m = 1` for `R_P`, and weighted at `m = 1` for `A₁ + C[A₁]` (the activation).
* `h5_3` (Lemma 5.3): (5.22) at order `3` for `‖A₁‖_{[3],γ}` (after `extLeading_wNorm_le`).
* `h5_5` (Lemma 5.5): (5.31) at order `2` for `‖C[A₁]‖_{[2],γ}`.

Constants: `b₀ = C₆ + 2C₇ + C₅ + C₃`, `Γ₀(P) = 1 + 4K₇(1)KP₆(2,P) + 4K₇(1)(1+K₅(2))K₃(3)`,
`C_{m,P} = K₇(m)KP₆(m+1,P) + KP₆(0,P)` (positive parts). -/
theorem lemma_5_8_of_odd (h5_3 : Statement.lemma_5_3) (h5_4 : Statement.proposition_5_4)
    (h5_5 : Statement.lemma_5_5) (h5_6 : Statement.theorem_5_6) (h5_7 : Statement.lemma_5_7)
    (hodd : OddExpansions) : Statement.lemma_5_8 := by
  obtain ⟨a₃, h3⟩ := h5_3
  obtain ⟨a₄, h4⟩ := h5_4
  obtain ⟨a₅, h5⟩ := h5_5
  obtain ⟨a₆, h6⟩ := h5_6
  obtain ⟨a₇, h7⟩ := h5_7
  obtain ⟨a₁, hod⟩ := hodd
  refine ⟨max (max (max a₃ a₄) (max a₅ a₆)) (max (max a₇ a₁) 3), fun a ha => ?_⟩
  simp only [max_le_iff] at ha
  obtain ⟨⟨⟨ha3, ha4⟩, ha5, ha6⟩, ⟨ha7, ha1⟩, haa⟩ := ha
  obtain ⟨C3, K3, h3'⟩ := h3 a ha3
  obtain ⟨C5, K5, h5'⟩ := h5 a ha5
  obtain ⟨C6, K6, KP6, h6'⟩ := h6 a ha6
  obtain ⟨C7, K7, h7'⟩ := h7 a ha7
  let cR : ℕ → ℝ := fun P => 4 * pos (K7 1) * pos (KP6 2 P)
  let cA : ℝ := 4 * pos (K7 1) * (1 + pos (K5 2)) * pos (K3 3)
  have hcR (P : ℕ) : 0 ≤ cR P := by
    have := pos_nonneg (K7 1); have := pos_nonneg (KP6 2 P); dsimp only [cR]; positivity
  have hcA : 0 ≤ cA := by
    have := pos_nonneg (K7 1); have := pos_nonneg (K5 2); have := pos_nonneg (K3 3)
    dsimp only [cA]; positivity
  refine ⟨C6 + 2 * C7 + C5 + C3, fun P => 1 + cR P + cA,
    fun m P => pos (K7 m) * pos (KP6 (m + 1) P) + pos (KP6 0 P), ?_⟩
  intro b hb Γ hΓ T hT U X pU k D lam t₀ center d χ hP hL hO amp hamp P hP2 R S u hu hsmall γ A Y W V
    Pres RV Wosc Wbar
  -- standing facts
  set ℓ := S5.radius D a with hℓdef
  set h := S5.width lam with hhdef
  have hD : 1 ≤ D := Bridge.Parent.scale_ge_one hP
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hlam : 1 ≤ lam := hP.frequency_ge_one
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam
  have hℓ : 0 < ℓ := Bridge.radius_pos hP a
  have hfit : 2 * ℓ < 1 / 2 := Bridge.radius_fits hP.scale_ge_two haa
  have hh : 0 < h := Bridge.width_pos hP
  have hh₁ : h ≤ 1 := Bridge.width_le_one hP
  have hγpos := Bridge.Origin.weight_pos hP hO
  have hγc := Bridge.Origin.weight_continuousOn hO
  have hγ1 := Bridge.Origin.weight_le_one hO
  obtain ⟨Bγ, hBγ⟩ := Bridge.Origin.exists_inverse_weight_bound hP hL hO
  have hΓ1 : 1 ≤ Γ P := by
    have := hΓ P
    linarith [hcR P, hcA]
  have hΓR : cR P ≤ Γ P := by have := hΓ P; linarith [hcA]
  have hΓA : cA ≤ Γ P := by have := hΓ P; linarith [hcR P]
  have hb6 : C6 ≤ b := by omega
  have hb7 : C7 ≤ b := by omega
  have hbA : 2 * C7 + C5 + C3 ≤ b := by omega
  have hb27 : 2 * C7 ≤ b := by omega
  -- the hypothesis of Theorem 5.6 from (5.43)
  have h56 : D ^ C6 * lam ^ (-1 / 12 : ℝ) ≤ 1 := by
    refine le_trans ?_ hsmall
    have hDb : D ^ C6 ≤ D ^ b := pow_le_pow_right₀ hD hb6
    have : D ^ C6 ≤ Γ P * D ^ b := hDb.trans (le_mul_of_one_le_left (by positivity) hΓ1)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  -- Proposition 5.4
  obtain ⟨-, h4r⟩ := h4 a ha4 hT d χ hP hL hO
  obtain ⟨-, -, h4id⟩ := h4r amp hamp P hP2
  obtain ⟨-, hdiv, hmom, hosc, hsupp, -, hvan, -, -, hRP⟩ := h4id R S u hu
  -- Theorem 5.6
  obtain ⟨-, -, -, -, h537, h538⟩ := h6' hT d χ hP hL hO h56 amp hamp P hP2 R S u hu
  -- `W_osc` vanishes before `t₀` and outside `supp g`
  have hoscVan : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x s, (W - A.average W).val.val.val (t, x, s) = 0 := by
    intro t ht hpre x s
    obtain ⟨hV, hC, -⟩ := hvan t ht hpre x s
    rw [hosc, profile_sum_eval]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := Finset.mem_Icc.mp hi
    change (u.V i).val.val.val (t, x, s) + (S5.Cd u (i + 1)).val.val.val (t, x, s) = 0
    rw [(hV i hi).1, hC (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), add_zero]
  have hoscSupp : ∀ t ∈ Icc 0 T, ∀ x ∉ S5.envelopeSupport ℓ, ∀ s,
      (W - A.average W).val.val.val (t, x, s) = (W - A.average W).val.val.val (t, x, 0) :=
    fun t ht x hx s => by rw [hsupp t ht x hx s, hsupp t ht x hx 0]
  -- `W̄` is phase independent
  have hBpi (p : ℕ) (hp : p ∈ Finset.Icc 2 P) (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) (s : ℝ) :
      (u.B p).val.val.val (t, x, s) = (u.B p).val.val.val (t, x, 0) := by
    have h := Bridge.phaseIndependent_of_average_eq d (hu.mean p hp).1.phase_independent
    rw [h (t, x, 0) ⟨ht, mem_univ _⟩ s]
  have hWbarPi : ∀ t ∈ Icc 0 T, ∀ x s,
      (∑ p ∈ Finset.Icc 2 P, u.B p).val.val.val (t, x, s) =
        (∑ p ∈ Finset.Icc 2 P, u.B p).val.val.val (t, x, 0) := by
    intro t ht x s
    rw [profile_sum_eval, profile_sum_eval]
    exact Finset.sum_congr rfl fun p hp => hBpi p hp t ht x s
  -- Lemma 5.7 applied to `W_osc`, `W̄`, `R_P`
  have h7osc := h7' hT hP hL hO (W - A.average W) hoscSupp
  have h7bar := h7' hT hP hL hO (∑ p ∈ Finset.Icc 2 P, u.B p)
    (fun t ht x _ s => hWbarPi t ht x s)
  have h7RP := h7' hT hP hL hO (S5.remainder A u P) hRP
  -- the activation: the extended leading profile and its bound
  obtain ⟨ampE, hE, hEq⟩ := exists_seed_extension hL hamp
  let V₀ := extLeading (T := T) k hℓ hfit hh hh₁ hE
  have hV₀supp : ∀ t ∈ Icc 0 T, ∀ x ∉ S5.envelopeSupport ℓ, ∀ s,
      (V₀ + S5.curlCorrection d V₀).val.val.val (t, x, s) =
        (V₀ + S5.curlCorrection d V₀).val.val.val (t, x, 0) := by
    intro t ht x hx s
    change V₀.val.val.val (t, x, s) + (S5.curlCorrection d V₀).val.val.val (t, x, s) =
      V₀.val.val.val (t, x, 0) + (S5.curlCorrection d V₀).val.val.val (t, x, 0)
    rw [extLeading_eq_zero_off_support k hℓ hfit hh hh₁ hE ht hx,
      extLeading_eq_zero_off_support k hℓ hfit hh hh₁ hE ht hx,
      curlCorrection_extLeading_eq_zero_off_support d hℓ hfit hh hh₁ hE ht hx,
      curlCorrection_extLeading_eq_zero_off_support d hℓ hfit hh hh₁ hE ht hx]
  have h7A := h7' hT hP hL hO (V₀ + S5.curlCorrection d V₀) hV₀supp
  -- `‖A₁ + C[A₁]‖_{[2],γ}` by (5.22) of Lemma 5.3 and (5.31) of Lemma 5.5
  have h3iii := (h3' hT d hP hL hO).2.2.2 3 amp hamp
  have h531 := ((h5' hT d hP hL hO).1 2 V₀ (extLeading_average hT d hℓ hfit hh hh₁ hE)
    (extLeading_transverse hT d hL hamp hℓ hfit hh hh₁ hE hEq)).1
  let NA : ℝ := (1 + pos (K5 2) * D ^ C5 * lam⁻¹) * (pos (K3 3) * D ^ C3 * lam ^ (-5 / 4 : ℝ))
  have hV₀3 : S5.wNorm ℓ h t₀ γ 3 V₀ ≤ pos (K3 3) * D ^ C3 * lam ^ (-5 / 4 : ℝ) := by
    have hP0 := fieldNorm_nonneg' ℓ h (Icc t₀ T) (fun t => (γ t)⁻¹) 3
      (fun t x => S5.leadingPressure U X k ℓ h amp t x.1 x.2)
    refine (extLeading_wNorm_le hT hL hℓ hfit hh hh₁ hE hEq hγc hγpos 3).trans ?_
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_pos _)
      (by positivity)) (by positivity))
    nlinarith [h3iii, mul_nonneg hlam0.le hP0]
  have hwN : ∀ n, 0 ≤ S5.wNorm ℓ h t₀ γ n V₀ := fun n =>
    Bridge.wNorm_nonneg ℓ h n hT hL.start_nonneg γ hBγ V₀
  have hNA : S5.wNorm ℓ h t₀ γ 2 (V₀ + S5.curlCorrection d V₀) ≤ NA := by
    refine (Bridge.wNorm_add_le ℓ h 2 hT hL.start_nonneg γ hBγ _ _).trans ?_
    have h23 := Bridge.wNorm_mono_order ℓ h (show 2 ≤ 3 by norm_num) hT hL.start_nonneg γ hBγ V₀
    have hC : S5.wNorm ℓ h t₀ γ 2 (S5.curlCorrection d V₀) ≤
        pos (K5 2) * D ^ C5 * lam⁻¹ * S5.wNorm ℓ h t₀ γ 3 V₀ :=
      h531.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_pos _) (by positivity)) (by positivity)) (hwN 3))
    have hK : 0 ≤ pos (K5 2) * D ^ C5 * lam⁻¹ := by have := pos_nonneg (K5 2); positivity
    calc S5.wNorm ℓ h t₀ γ 2 V₀ + S5.wNorm ℓ h t₀ γ 2 (S5.curlCorrection d V₀) ≤
          S5.wNorm ℓ h t₀ γ 3 V₀ + pos (K5 2) * D ^ C5 * lam⁻¹ * S5.wNorm ℓ h t₀ γ 3 V₀ :=
          add_le_add h23 hC
      _ = (1 + pos (K5 2) * D ^ C5 * lam⁻¹) * S5.wNorm ℓ h t₀ γ 3 V₀ := by ring
      _ ≤ NA := mul_le_mul_of_nonneg_left hV₀3 (by linarith)
  let BA : ℝ := pos (K7 1) * (D ^ C7 * lam ^ (3 / 2 : ℝ)) ^ 2 * NA
  have hAct := activation_holder d hL hℓ hfit hh hh₁ hE hEq hu hγc hγpos (B := BA)
    (fun t ht => by
      obtain ⟨-, hH, hN⟩ := h7A.1 1 t ht
      refine ⟨hH, hN.trans ?_⟩
      have hγt := (hγpos t ht).le
      have hw0 : 0 ≤ S5.wNorm ℓ h t₀ γ 2 (V₀ + S5.curlCorrection d V₀) :=
        Bridge.wNorm_nonneg ℓ h 2 hT hL.start_nonneg γ hBγ _
      calc K7 1 * (D ^ C7 * lam ^ (3 / 2 : ℝ)) ^ (1 + 1) * γ t *
            S5.wNorm ℓ h t₀ γ (1 + 1) (V₀ + S5.curlCorrection d V₀)
          ≤ pos (K7 1) * (D ^ C7 * lam ^ (3 / 2 : ℝ)) ^ 2 * γ t * NA := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_pos _)
              (by positivity)) hγt) hNA hw0 ?_
            have := pos_nonneg (K7 1); positivity
        _ = BA * γ t := by ring)
  -- assembly of the conclusions
  have hsm := approx_smooth (pU := pU) hT hP W (S5.expansionPressure u P)
  refine ⟨⟨hsm.1.1, fun t ht => ⟨hsm.1.2 t ht, fun x => ?_, fun x => approx_divergence hT d hP W hdiv ht x⟩⟩,
    hsm.2, fun t ht x => approx_residual hT d hP W R _ (S5.expansionPressure u P) hmom hu.residual ht x,
    fun t ht x => ?_, fun m t ht => ?_, fun m t ht => ?_, fun t ht => ?_⟩
  · -- oddness of `V = U + W^♮`
    change U t (-x) + graphRead Y W t (-x) = -(U t x + graphRead Y W t x)
    rw [hP.velocity_odd t ht x, hod a ha1 hT d χ hP hL hO amp hamp P hP2 R S u hu t ht x, neg_add]
  · -- (5.47)
    refine (graph_norm_le_wNorm hT hL.start_nonneg hL.start_lt.le hγc hγpos hγ1 ℓ h Y hoscVan ht x).trans ?_
    refine ((h537 0).1).trans ?_
    have hKP := le_pos (KP6 0 P)
    have hK : pos (KP6 0 P) ≤ pos (K7 0) * pos (KP6 (0 + 1) P) + pos (KP6 0 P) := by
      have := mul_nonneg (pos_nonneg (K7 0)) (pos_nonneg (KP6 (0 + 1) P)); linarith
    have hDb : D ^ C6 ≤ D ^ b := pow_le_pow_right₀ hD hb6
    have hl : 0 ≤ lam ^ (-5 / 4 : ℝ) := by positivity
    calc KP6 0 P * D ^ C6 * lam ^ (-5 / 4 : ℝ) ≤ pos (KP6 0 P) * D ^ C6 * lam ^ (-5 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKP (by positivity)) hl
      _ ≤ (pos (K7 0) * pos (KP6 (0 + 1) P) + pos (KP6 0 P)) * D ^ b * lam ^ (-5 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hK hDb (by positivity)
            (by have := pos_nonneg (K7 0); have := pos_nonneg (KP6 (0 + 1) P);
                have := pos_nonneg (KP6 0 P); positivity)) hl
  · -- (5.48), oscillation
    have hB0 : 0 ≤ (pos (K7 m) * pos (KP6 (m + 1) P) + pos (KP6 0 P)) * D ^ (b * (m + 2)) *
        lam ^ ((3 : ℝ) * ((m : ℝ) + 1) / 2 - 5 / 4) := by
      have := pos_nonneg (K7 m); have := pos_nonneg (KP6 (m + 1) P); have := pos_nonneg (KP6 0 P)
      positivity
    refine holder_of_active hoscVan hB0 (fun t ht' => ?_) t ht
    obtain ⟨-, hH, hN⟩ := h7osc.1 m t ht'
    refine ⟨hH, hN.trans ?_⟩
    have hw : 0 ≤ S5.wNorm ℓ h t₀ γ (m + 1) (W - A.average W) :=
      Bridge.wNorm_nonneg ℓ h (m + 1) hT hL.start_nonneg γ hBγ _
    refine (osc_constant_bound hD hlam hb6 hb7 hw (h537 (m + 1)).1 (hγpos t ht').le
      (hγ1 t ht')).trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) (by positivity)
    have := pos_nonneg (KP6 0 P)
    linarith
  · -- (5.48), mean
    obtain ⟨-, hH, hN⟩ := (h7bar.2.2 hWbarPi).2 m t ht
    refine ⟨hH, hN.trans ?_⟩
    have hu0 : 0 ≤ S5.uNorm ℓ h (m + 1) (∑ p ∈ Finset.Icc 2 P, u.B p) :=
      Bridge.uNorm_nonneg ℓ h (m + 1) hT _
    have hu1 : 0 ≤ S5.uNorm ℓ h (m + 1)
        (∑ p ∈ Finset.Icc 2 P, S5.meanSource A u (S5.curlCorrection d S) R p) :=
      Bridge.uNorm_nonneg ℓ h (m + 1) hT _
    have hbound : S5.uNorm ℓ h (m + 1) (∑ p ∈ Finset.Icc 2 P, u.B p) ≤
        KP6 (m + 1) P * D ^ C6 * lam ^ (-5 / 2 : ℝ) := by linarith [(h537 (m + 1)).2]
    refine (mean_constant_bound hD hb6 hb7 (by positivity) hu0 hbound).trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) (by positivity)
    have := pos_nonneg (KP6 0 P)
    linarith
  · -- (5.48), residual `R_V = R_P^♮ + R_χ̃^♮`
    clear h3 h4 h5 h6 h7 h3' h5' h6' h7' h4r h4id hod h7osc h7bar h7A h3iii h531 h537
    obtain ⟨-, hHP, hNP⟩ := h7RP.2.1 1 t ht
    obtain ⟨hHA, hNA'⟩ := hAct t ht
    have hsplit : RV t = graphRead Y (S5.remainder A u P) t +
        graphRead Y (S + S5.curlCorrection d S) t := rfl
    rw [hsplit]
    obtain ⟨hHsum, hNsum⟩ := spatialHolderHalf_add hHP hHA
    refine ⟨hHsum, hNsum.trans ?_⟩
    have hDS := (χ.derivativeSize_bounds hT hL.start_nonneg hL.start_lt.le hγc
      (fun t ht => (hγpos t ht).le)).1
    have hlam74 : lam ^ (7 / 4 : ℝ) ≤ lam ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hlam (by norm_num)
    have hΛ : (D ^ C7 * lam ^ (3 / 2 : ℝ)) ^ 2 = D ^ (2 * C7) * lam ^ (3 : ℝ) := by
      rw [frequency_pow hlam0]; norm_num [mul_comm]
    -- the parent remainder
    have hRPb : spatialHolderHalfNorm 1 (graphRead Y (S5.remainder A u P) t) ≤
        pos (K7 1) * pos (KP6 2 P) * D ^ b * lam ^ (2 : ℝ) * lam ^ (-2 * (P : ℝ) / 3) := by
      refine hNP.trans ?_
      have hu2 := Bridge.uNorm_nonneg ℓ h (1 + 1) hT (S5.remainder A u P)
      have hR2 := h538 2
      calc K7 1 * (D ^ C7 * lam ^ (3 / 2 : ℝ)) ^ (1 + 1) * 1 * S5.uNorm ℓ h (1 + 1) (S5.remainder A u P)
          ≤ pos (K7 1) * (D ^ (2 * C7) * lam ^ (3 : ℝ)) * 1 *
              (pos (KP6 2 P) * lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * (P : ℝ) / 3)) := by
            rw [show (1 + 1 : ℕ) = 2 from rfl, hΛ]
            refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_pos _)
              (by positivity)) zero_le_one) (hR2.trans (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (le_pos _) (by positivity)) (by positivity))) hu2 ?_
            have := pos_nonneg (K7 1); positivity
        _ = pos (K7 1) * pos (KP6 2 P) * D ^ (2 * C7) * (lam ^ (3 : ℝ) * lam ^ (-5 / 4 : ℝ)) *
              lam ^ (-2 * (P : ℝ) / 3) := by ring
        _ ≤ pos (K7 1) * pos (KP6 2 P) * D ^ b * lam ^ (2 : ℝ) * lam ^ (-2 * (P : ℝ) / 3) := by
            rw [← Real.rpow_add hlam0, show (3 : ℝ) + -5 / 4 = 7 / 4 by norm_num]
            have := pos_nonneg (K7 1); have := pos_nonneg (KP6 2 P)
            refine mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hD hb27) (by positivity)) hlam74 (by positivity) (by positivity))
              (by positivity)
    -- the activation
    have hBA : BA ≤ pos (K7 1) * (1 + pos (K5 2)) * pos (K3 3) * D ^ b * lam ^ (2 : ℝ) := by
      have h1 : 1 + pos (K5 2) * D ^ C5 * lam⁻¹ ≤ (1 + pos (K5 2)) * D ^ C5 := by
        have hDC : 1 ≤ D ^ C5 := one_le_pow₀ hD
        have hli : lam⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlam
        have := pos_nonneg (K5 2)
        nlinarith [mul_le_mul_of_nonneg_left hli (mul_nonneg this (zero_le_one.trans hDC))]
      dsimp only [BA, NA]
      rw [hΛ]
      have := pos_nonneg (K7 1); have := pos_nonneg (K5 2); have := pos_nonneg (K3 3)
      calc pos (K7 1) * (D ^ (2 * C7) * lam ^ (3 : ℝ)) *
            ((1 + pos (K5 2) * D ^ C5 * lam⁻¹) * (pos (K3 3) * D ^ C3 * lam ^ (-5 / 4 : ℝ)))
          ≤ pos (K7 1) * (D ^ (2 * C7) * lam ^ (3 : ℝ)) *
            (((1 + pos (K5 2)) * D ^ C5) * (pos (K3 3) * D ^ C3 * lam ^ (-5 / 4 : ℝ))) := by
            gcongr
        _ = pos (K7 1) * (1 + pos (K5 2)) * pos (K3 3) * D ^ (2 * C7 + C5 + C3) *
              (lam ^ (3 : ℝ) * lam ^ (-5 / 4 : ℝ)) := by rw [pow_add, pow_add]; ring
        _ ≤ _ := by
            rw [← Real.rpow_add hlam0, show (3 : ℝ) + -5 / 4 = 7 / 4 by norm_num]
            exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hbA) (by positivity))
              hlam74 (by positivity) (by positivity)
    have hAb : spatialHolderHalfNorm 1 (graphRead Y (S + S5.curlCorrection d S) t) ≤
        pos (K7 1) * (1 + pos (K5 2)) * pos (K3 3) * D ^ b * lam ^ (2 : ℝ) * χ.derivativeSize γ :=
      hNA'.trans (mul_le_mul_of_nonneg_right hBA hDS)
    have hl2 : 0 ≤ lam ^ (2 : ℝ) := by positivity
    have hlP : 0 ≤ lam ^ (-2 * (P : ℝ) / 3) := by positivity
    have hDb : 0 ≤ D ^ b := by positivity
    calc (2 * (((1 : ℕ) : ℝ) + 1)) * (spatialHolderHalfNorm 1 (graphRead Y (S5.remainder A u P) t) +
          spatialHolderHalfNorm 1 (graphRead Y (S + S5.curlCorrection d S) t))
        ≤ 4 * (pos (K7 1) * pos (KP6 2 P) * D ^ b * lam ^ (2 : ℝ) * lam ^ (-2 * (P : ℝ) / 3) +
            pos (K7 1) * (1 + pos (K5 2)) * pos (K3 3) * D ^ b * lam ^ (2 : ℝ) *
              χ.derivativeSize γ) := by
          have h4 : (2 * (((1 : ℕ) : ℝ) + 1)) = 4 := by norm_num
          rw [h4]
          exact mul_le_mul_of_nonneg_left (add_le_add hRPb hAb) (by norm_num)
      _ = cR P * D ^ b * lam ^ (2 : ℝ) * lam ^ (-2 * (P : ℝ) / 3) +
            cA * D ^ b * lam ^ (2 : ℝ) * χ.derivativeSize γ := by dsimp only [cR, cA]; ring
      _ ≤ Γ P * D ^ b * lam ^ (2 : ℝ) * lam ^ (-2 * (P : ℝ) / 3) +
            Γ P * D ^ b * lam ^ (2 : ℝ) * χ.derivativeSize γ :=
          add_le_add
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hΓR hDb) hl2) hlP)
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hΓA hDb) hl2) hDS)
      _ = Γ P * D ^ b * lam ^ (2 : ℝ) * (lam ^ (-2 * (P : ℝ) / 3) + χ.derivativeSize γ) := by ring

end

end TorusEuler.Paper.S5b
