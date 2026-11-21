import TorusEuler.Paper.Proofs.S5c.Library.CenterBound
import TorusEuler.HierarchyPhysicalPressureBounds

/-!
# Lemma 5.9 from its four parts

The proof of Lemma 5.9 (`sections/08_exact_wave.tex:171-279`) has four parts, stated here
with the quantifiers of `Statement.lemma_5_9` (each with its own exponent `C` and constants,
fixed after the envelope exponent `a`, and the smallness `𝖣^Cλ^{-1/12} ≤ 1` that (5.43)
implies once `b ≥ C`, `Γ_P ≥ 1`):

* `LeadingHessianClaim`: the signed bound of the Hessian of `𝗉_1^♮`, from (5.51)
  (`:172-204`), at most `K𝖣^Cλ^{-1/4}`;
* `HigherHessianClaim`: (5.52), `‖D_x²∑_{p≥2}𝗉_p^♮‖_∞ ≤ K_P𝖣^Cλ^{-5/12}` (`:206-232`);
* `MeanHessianClaim`: `‖D_x²∑_{p≥2}q̄_p^♮‖_∞ ≤ K_P𝖣^Cλ^{-5/2}` (`:233-255`);
* `CentralReturnClaim` (`CenterBound.lean`): (5.50) (`:257-278`).

`lemma59_of_claims` assembles them: `𝖯^♮ = 𝗉_1^♮ + ∑_{p≥2}𝗉_p^♮ + ∑_{p≥2}q̄_p^♮` (`q̄_1 = 0`),
the three Hessians add, and "Together with the bounds for the tensors of (5.51) and with
(5.52), this proves (5.49)" (`:252-255`) with `b ≥ C₁ + C₂ + C₃` and
`Γ_P ≥ 1 + |K₁| + |K₂,P| + |K₃,P|`.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5c

open HierarchyTwistedProfile LocalizedAmplitude InnerProductSpace

noncomputable section

/-- The signed Hessian bound of the leading pressure `𝗉_1^♮`, from (5.51)
(`sections/08_exact_wave.tex:172-204`). -/
def LeadingHessianClaim : Prop :=
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ C : ℕ, ∃ K : ℝ,
    ∀ {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
      {D lam t₀ : ℝ} {center : ℝ → Vec3} (d : ParentGeometry hT U X k) (χ : PaperWaveCutoff t₀ T),
      S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ → S5.Origin T U X k D lam t₀ center →
      D ^ C * lam ^ (-1 / 12 : ℝ) ≤ 1 →
      ∀ amp : ℝ → Vec3 → Vec3, S5.IsSeed U X k t₀ T center amp →
      ∀ P : ℕ, 2 ≤ P →
      ∀ (R S : HierarchyTwistedProfile T k Vec3)
        (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)),
        S5.IsExpansion d pU χ (S5.radius D a) (S5.width lam) amp P R S u →
        ∀ t ∈ Icc 0 T, ∀ x v : Vec3,
          ⟪v, fderiv ℝ (gradient (graphRead (fun t => X t 0) (u.p 1) t)) x v⟫_ℝ ≤
            K * D ^ C * lam ^ (-1 / 4 : ℝ) * ‖v‖ ^ 2

/-- (5.52): the Hessian of the higher oscillatory pressures `∑_{p=2}^P 𝗉_p^♮`
(`sections/08_exact_wave.tex:206-232`). -/
def HigherHessianClaim : Prop :=
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ C : ℕ, ∃ K : ℕ → ℝ,
    ∀ {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
      {D lam t₀ : ℝ} {center : ℝ → Vec3} (d : ParentGeometry hT U X k) (χ : PaperWaveCutoff t₀ T),
      S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ → S5.Origin T U X k D lam t₀ center →
      D ^ C * lam ^ (-1 / 12 : ℝ) ≤ 1 →
      ∀ amp : ℝ → Vec3 → Vec3, S5.IsSeed U X k t₀ T center amp →
      ∀ P : ℕ, 2 ≤ P →
      ∀ (R S : HierarchyTwistedProfile T k Vec3)
        (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)),
        S5.IsExpansion d pU χ (S5.radius D a) (S5.width lam) amp P R S u →
        ∀ t ∈ Icc 0 T, ∀ x : Vec3,
          ‖fderiv ℝ (gradient (graphRead (fun t => X t 0) (∑ p ∈ Finset.Icc 2 P, u.p p) t)) x‖ ≤
            K P * D ^ C * lam ^ (-5 / 12 : ℝ)

/-- The Hessian of the mean pressures `∑_{p=2}^P q̄_p^♮` (`sections/08_exact_wave.tex:233-255`). -/
def MeanHessianClaim : Prop :=
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ C : ℕ, ∃ K : ℕ → ℝ,
    ∀ {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
      {D lam t₀ : ℝ} {center : ℝ → Vec3} (d : ParentGeometry hT U X k) (χ : PaperWaveCutoff t₀ T),
      S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ → S5.Origin T U X k D lam t₀ center →
      D ^ C * lam ^ (-1 / 12 : ℝ) ≤ 1 →
      ∀ amp : ℝ → Vec3 → Vec3, S5.IsSeed U X k t₀ T center amp →
      ∀ P : ℕ, 2 ≤ P →
      ∀ (R S : HierarchyTwistedProfile T k Vec3)
        (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)),
        S5.IsExpansion d pU χ (S5.radius D a) (S5.width lam) amp P R S u →
        ∀ t ∈ Icc 0 T, ∀ x : Vec3,
          ‖fderiv ℝ (gradient (graphRead (fun t => X t 0) (∑ p ∈ Finset.Icc 2 P, u.q p) t)) x‖ ≤
            K P * D ^ C * lam ^ (-5 / 2 : ℝ)

/-- `𝖯 = 𝗉_1 + ∑_{p≥2}𝗉_p + ∑_{p≥2}q̄_p` for profiles with `q̄_1 = 0`. -/
theorem expansionPressure_eq_split {T : ℝ} {k : Vec3}
    (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ))
    {P : ℕ} (hP : 1 ≤ P) (hq1 : u.q 1 = 0) :
    S5.expansionPressure u P =
      u.p 1 + (∑ p ∈ Finset.Icc 2 P, u.p p) + ∑ p ∈ Finset.Icc 2 P, u.q p := by
  have hsplit (f : ℕ → HierarchyTwistedProfile T k ℝ) :
      ∑ p ∈ Finset.Icc 1 P, f p = f 1 + ∑ p ∈ Finset.Icc 2 P, f p := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_Icc.mpr ⟨le_rfl, hP⟩), add_comm]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [Finset.mem_erase, Finset.mem_Icc]
    omega
  unfold S5.expansionPressure
  rw [Finset.sum_add_distrib, hsplit u.p, hsplit u.q, hq1, zero_add]

set_option maxHeartbeats 1600000 in
/-- **Lemma 5.9 from its four parts** (`sections/08_exact_wave.tex:171-279`). (5.49) is the sum
of the three Hessian bounds (`:252-255`); (5.50) is `CentralReturnClaim`. The constants are
`a₀ = max` of the four, `b₀ = max (C₁ + C₂ + C₃) b₀(5.50)` and
`Γ₀ P = max (1 + |K₁| + |K₂ P| + |K₃ P|) (Γ₀(5.50) P)`. -/
theorem lemma59_of_claims (hL : LeadingHessianClaim) (hH : HigherHessianClaim)
    (hM : MeanHessianClaim) (hC : CentralReturnClaim) : Statement.lemma_5_9 := by
  obtain ⟨aL, hL⟩ := hL
  obtain ⟨aH, hH⟩ := hH
  obtain ⟨aM, hM⟩ := hM
  obtain ⟨aC, hC⟩ := hC
  refine ⟨max (max aL aH) (max aM aC), fun a ha => ?_⟩
  obtain ⟨C1, K1, hL'⟩ := hL a (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) ha))
  obtain ⟨C2, K2, hH'⟩ := hH a (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) ha))
  obtain ⟨C3, K3, hM'⟩ := hM a (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) ha))
  obtain ⟨bC, ΓC, hC'⟩ := hC a (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) ha))
  let ΓH : ℕ → ℝ := fun P => 1 + |K1| + |K2 P| + |K3 P|
  refine ⟨max (C1 + C2 + C3) bC, fun P => max (ΓH P) (ΓC P), fun b hb Γ hΓ => ?_⟩
  intro T hT U X pU k D lam t₀ center d χ hP hLa hO amp hamp P hP2 R S u hu h543 Y V Pnat
  refine ⟨?_, hC' b (le_trans (le_max_right _ _) hb) Γ
    (fun P => le_trans (le_max_right _ _) (hΓ P)) hT d χ hP hLa hO amp hamp P hP2 R S u hu h543⟩
  -- (5.49)
  have hD : 1 ≤ D := Bridge.Parent.scale_ge_one hP
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hlam : 1 ≤ lam := hP.frequency_ge_one
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam
  have hb3 : C1 + C2 + C3 ≤ b := le_trans (le_max_left _ _) hb
  have hΓH : ΓH P ≤ Γ P := le_trans (le_max_left _ _) (hΓ P)
  have hΓ1 : 1 ≤ Γ P := by
    refine le_trans ?_ hΓH
    simp only [ΓH]
    linarith [abs_nonneg K1, abs_nonneg (K2 P), abs_nonneg (K3 P)]
  have hl12 : 0 ≤ lam ^ (-1 / 12 : ℝ) := Real.rpow_nonneg hlam0.le _
  have hsmall (C : ℕ) (hCb : C ≤ b) : D ^ C * lam ^ (-1 / 12 : ℝ) ≤ 1 := by
    have h1 : D ^ C ≤ Γ P * D ^ b :=
      (pow_le_pow_right₀ hD hCb).trans (le_mul_of_one_le_left (pow_nonneg hD0 _) hΓ1)
    exact (mul_le_mul_of_nonneg_right h1 hl12).trans h543
  have h1 := hL' hT d χ hP hLa hO (hsmall C1 (by omega)) amp hamp P hP2 R S u hu
  have h2 := hH' hT d χ hP hLa hO (hsmall C2 (by omega)) amp hamp P hP2 R S u hu
  have h3 := hM' hT d χ hP hLa hO (hsmall C3 (by omega)) amp hamp P hP2 R S u hu
  intro t ht x v
  have hsplitP : Pnat t = graphRead Y (u.p 1) t + graphRead Y (∑ p ∈ Finset.Icc 2 P, u.p p) t +
      graphRead Y (∑ p ∈ Finset.Icc 2 P, u.q p) t := by
    funext y
    change (S5.expansionPressure u P).val.val.val (t, Y t y, ⟪k, Y t y⟫_ℝ) = _
    rw [expansionPressure_eq_split u (by omega) hu.first_mean.2]
    rfl
  have hs (f : HierarchyTwistedProfile T k ℝ) : ContDiff ℝ 2 (graphRead Y f t) :=
    (graphRead_slice_smooth hT hP f ht).of_le (by simp)
  rw [hsplitP, fderiv_gradient_add_three_pressures (hs _) (hs _) (hs _) x]
  simp only [add_apply, inner_add_right]
  have hv2 : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  have hHv : ⟪v, fderiv ℝ (gradient (graphRead Y (∑ p ∈ Finset.Icc 2 P, u.p p) t)) x v⟫_ℝ ≤
      K2 P * D ^ C2 * lam ^ (-5 / 12 : ℝ) * ‖v‖ ^ 2 := by
    refine (real_inner_le_norm _ _).trans ?_
    calc ‖v‖ * ‖fderiv ℝ (gradient (graphRead Y (∑ p ∈ Finset.Icc 2 P, u.p p) t)) x v‖
        ≤ ‖v‖ * (‖fderiv ℝ (gradient (graphRead Y (∑ p ∈ Finset.Icc 2 P, u.p p) t)) x‖ * ‖v‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ ‖v‖ * (K2 P * D ^ C2 * lam ^ (-5 / 12 : ℝ) * ‖v‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (h2 t ht x) (norm_nonneg _))
            (norm_nonneg _)
      _ = K2 P * D ^ C2 * lam ^ (-5 / 12 : ℝ) * ‖v‖ ^ 2 := by ring
  have hMv : ⟪v, fderiv ℝ (gradient (graphRead Y (∑ p ∈ Finset.Icc 2 P, u.q p) t)) x v⟫_ℝ ≤
      K3 P * D ^ C3 * lam ^ (-5 / 2 : ℝ) * ‖v‖ ^ 2 := by
    refine (real_inner_le_norm _ _).trans ?_
    calc ‖v‖ * ‖fderiv ℝ (gradient (graphRead Y (∑ p ∈ Finset.Icc 2 P, u.q p) t)) x v‖
        ≤ ‖v‖ * (‖fderiv ℝ (gradient (graphRead Y (∑ p ∈ Finset.Icc 2 P, u.q p) t)) x‖ * ‖v‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ ‖v‖ * (K3 P * D ^ C3 * lam ^ (-5 / 2 : ℝ) * ‖v‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (h3 t ht x) (norm_nonneg _))
            (norm_nonneg _)
      _ = K3 P * D ^ C3 * lam ^ (-5 / 2 : ℝ) * ‖v‖ ^ 2 := by ring
  have hLv := h1 t ht x v
  -- comparison of the three rates with `𝖣^b λ^{-1/4}`
  have hDC (C : ℕ) (hCb : C ≤ b) : D ^ C ≤ D ^ b := pow_le_pow_right₀ hD hCb
  have hl4 : 0 ≤ lam ^ (-1 / 4 : ℝ) := Real.rpow_nonneg hlam0.le _
  have hr2 : lam ^ (-5 / 12 : ℝ) ≤ lam ^ (-1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlam (by norm_num)
  have hr3 : lam ^ (-5 / 2 : ℝ) ≤ lam ^ (-1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlam (by norm_num)
  have hterm (K : ℝ) (C : ℕ) (r : ℝ) (hCb : C ≤ b) (hr : 0 ≤ r) (hrl : r ≤ lam ^ (-1 / 4 : ℝ)) :
      K * D ^ C * r * ‖v‖ ^ 2 ≤ |K| * D ^ b * lam ^ (-1 / 4 : ℝ) * ‖v‖ ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ hv2
    calc K * D ^ C * r ≤ |K| * D ^ C * r :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K)
            (pow_nonneg hD0 _)) hr
      _ ≤ |K| * D ^ b * lam ^ (-1 / 4 : ℝ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hDC C hCb) (abs_nonneg K)) hrl hr
            (mul_nonneg (abs_nonneg K) (pow_nonneg hD0 _))
  have e1 := hterm K1 C1 (lam ^ (-1 / 4 : ℝ)) (by omega) hl4 le_rfl
  have e2 := hterm (K2 P) C2 (lam ^ (-5 / 12 : ℝ)) (by omega) (Real.rpow_nonneg hlam0.le _) hr2
  have e3 := hterm (K3 P) C3 (lam ^ (-5 / 2 : ℝ)) (by omega) (Real.rpow_nonneg hlam0.le _) hr3
  have hsum : (|K1| + |K2 P| + |K3 P|) * D ^ b * lam ^ (-1 / 4 : ℝ) * ‖v‖ ^ 2 ≤
      Γ P * D ^ b * lam ^ (-1 / 4 : ℝ) * ‖v‖ ^ 2 := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hD0 _)) hl4) hv2
    refine le_trans ?_ hΓH
    simp only [ΓH]
    linarith
  linarith [e1, e2, e3, hsum, hLv, hHv, hMv]

end

end TorusEuler.Paper.Lib.S5c
