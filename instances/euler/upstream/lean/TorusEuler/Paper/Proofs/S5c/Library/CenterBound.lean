import TorusEuler.Paper.Proofs.S5c.Library.Center
import TorusEuler.Paper.Proofs.S5c.Library.Inactive
import TorusEuler.Paper.Proofs.S5c.Library.Support54
import TorusEuler.Paper.S34A.Statements
import TorusEuler.Paper.Proofs.S5Bridge.Norms

/-!
# Lemma 5.9, the central return (5.50)

`CentralReturnClaim` is the second conjunct (5.50) of `Statement.lemma_5_9`, with the same
quantifiers. `centralReturnClaim` proves it from Lemma 3.1, Proposition 5.4, Theorem 5.6 and Lemma 5.7,
following `sections/08_exact_wave.tex:257-278`:

* `g(0) = F_h'(0) = 1`, `F_h(0) = 0` (Lemma 3.1) and the chain rule (3.1) give
  `D_xV_1^♮(t,0) = χ̃(t)𝐚(t,0) ⊗ κ(t,0)`, so `E_c = D_x(W_osc - V_1)^♮(t,0) + D_xW̄^♮(t,0)`
  (`Lib.S5c.centralReturn_eq`);
* `W_osc - V_1 = ∑_{p≥2} V_p + ∑_{p≥2}^{P+1} C_p` is supported in `supp g`
  (`Lib.S5c.inactive_of_prop54`, from `h5_4`), and its norm `‖·‖_{[1],γ}` is at most
  `C_{2,P}𝖣^Cλ^{-23/12}` by (5.34) and (5.36) of Theorem 5.6; `‖W̄‖_{[1]} ≤ C_{2,P}𝖣^Cλ^{-5/2}`
  by (5.37);
* (5.44) of Lemma 5.7 at `m = 1` (on `[t₀,T]` for `W_osc - V_1`, for phase-independent fields
  on `[0,T]` for `W̄`) gives `|E_c| ≤ C_{2,P}𝖣^Cλ^{-5/12}`;
* `b` at least the exponent and `Γ_P ≥ C_{2,P}` turn this into `λ^{-1/3}` by (5.43).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5c

open HierarchyTwistedProfile LocalizedAmplitude InnerProductSpace

noncomputable section

/-- The claim (5.50) of Lemma 5.9, with the quantifiers of `Statement.lemma_5_9`
(`sections/08_exact_wave.tex:163-168`). -/
def CentralReturnClaim : Prop :=
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ b₀ : ℕ, ∃ Γ₀ : ℕ → ℝ,
    ∀ b : ℕ, b₀ ≤ b → ∀ Γ : ℕ → ℝ, (∀ P, Γ₀ P ≤ Γ P) →
    ∀ {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
      {D lam t₀ : ℝ} {center : ℝ → Vec3} (d : ParentGeometry hT U X k) (χ : PaperWaveCutoff t₀ T),
      S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ → S5.Origin T U X k D lam t₀ center →
      ∀ amp : ℝ → Vec3 → Vec3, S5.IsSeed U X k t₀ T center amp →
      ∀ P : ℕ, 2 ≤ P →
      ∀ (R S : HierarchyTwistedProfile T k Vec3)
        (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)),
        S5.IsExpansion d pU χ (S5.radius D a) (S5.width lam) amp P R S u →
        Γ P * D ^ b * lam ^ (-1 / 12 : ℝ) ≤ 1 →
        let Y : Velocity := fun t => X t 0
        let V : Velocity := U + graphRead Y (S5.expansion u P)
        ∀ t ∈ Icc t₀ T,
          ‖fderiv ℝ (V t) 0 - fderiv ℝ (U t) 0 -
              χ.value t • rankOne ℝ (center t) (S5.waveVector X k t 0)‖ ≤
            lam ^ (-1 / 3 : ℝ)

/-- `K 𝖣^C λ^{e₁} λ^{e₂} ≤ |K| 𝖣^C λ^e` for `λ ≥ 1` and `e₁ + e₂ ≤ e`. -/
theorem le_abs_rpow_of_exponent {K Dc lam e₁ e₂ e : ℝ} (hDc : 0 ≤ Dc) (hlam : 1 ≤ lam)
    (he : e₁ + e₂ ≤ e) : K * Dc * lam ^ e₁ * lam ^ e₂ ≤ |K| * Dc * lam ^ e := by
  have hl : 0 < lam := zero_lt_one.trans_le hlam
  rw [mul_assoc, ← Real.rpow_add hl]
  have h1 : lam ^ (e₁ + e₂) ≤ lam ^ e := Real.rpow_le_rpow_of_exponent_le hlam he
  have h2 : 0 ≤ lam ^ (e₁ + e₂) := Real.rpow_nonneg hl.le _
  calc K * Dc * lam ^ (e₁ + e₂) = K * (Dc * lam ^ (e₁ + e₂)) := by ring
    _ ≤ |K| * (Dc * lam ^ (e₁ + e₂)) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (mul_nonneg hDc h2)
    _ ≤ |K| * (Dc * lam ^ e) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hDc) (abs_nonneg K)
    _ = |K| * Dc * lam ^ e := by ring

set_option maxHeartbeats 1600000 in
/-- **(5.50) of Lemma 5.9** from Lemma 3.1 (`F_h(0) = 0`, `F_h'(0) = 1`, in the chain rule at
the origin), Theorem 5.6 ((5.34), (5.36) for `W_osc - V_1`, (5.37) for `W̄`) and Lemma 5.7
((5.44) at `m = 1`), as in `sections/08_exact_wave.tex:257-278`. The constants are
`a₀ = max (max a₀(5.6) a₀(5.7)) 3`, `b₀ = C₆ + C₇` (the exponents of 5.6 and 5.7) and
`Γ₀ P = 1 + |K₇,₁| (∑_{p=2}^P |K₆,₁,p| + ∑_{p=1}^P |K₆,₁,p| + |K^P₆,₁,P|)`. -/
theorem centralReturnClaim (h3_1 : Statement.lemma_3_1) (h5_4 : Statement.proposition_5_4)
    (h5_6 : Statement.theorem_5_6) (h5_7 : Statement.lemma_5_7) : CentralReturnClaim := by
  obtain ⟨C3, -, hprof, -⟩ := h3_1
  obtain ⟨a6, h6⟩ := h5_6
  obtain ⟨a7, h7⟩ := h5_7
  obtain ⟨a4, h4⟩ := inactive_of_prop54 h5_4
  refine ⟨max (max (max a6 a7) a4) 3, fun a ha => ?_⟩
  simp only [max_le_iff] at ha
  obtain ⟨⟨⟨ha6, ha7⟩, ha4⟩, ha3⟩ := ha
  obtain ⟨C6, K6, KP6, h6a⟩ := h6 a ha6
  obtain ⟨C7, K7, h7a⟩ := h7 a ha7
  let A6 : ℕ → ℝ := fun P => (∑ p ∈ Finset.Icc 2 P, |K6 1 p|) + ∑ p ∈ Finset.Icc 1 P, |K6 1 p|
  let cP : ℕ → ℝ := fun P => |K7 1| * (A6 P + |KP6 1 P|)
  have hA6 (P : ℕ) : 0 ≤ A6 P :=
    add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hcP (P : ℕ) : 0 ≤ cP P := mul_nonneg (abs_nonneg _) (add_nonneg (hA6 P) (abs_nonneg _))
  refine ⟨C6 + C7, fun P => 1 + cP P, fun b hb Γ hΓ => ?_⟩
  intro T hT U X pU k D lam t₀ center d χ hP hL hO amp hamp P hP2 R S u hu h543 Y V t ht
  -- standing facts
  have hD : 1 ≤ D := Bridge.Parent.scale_ge_one hP
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hlam : 1 ≤ lam := hP.frequency_ge_one
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam
  have hℓ : 0 < S5.radius D a := Bridge.radius_pos hP a
  have hfit : 2 * S5.radius D a < 1 / 2 := Bridge.radius_fits hP.scale_ge_two ha3
  have hh : 0 < S5.width lam := Bridge.width_pos hP
  have hh1 : S5.width lam ≤ 1 := Bridge.width_le_one hP
  have hst : Icc t₀ T ⊆ Icc 0 T := Bridge.Launch.active_subset hL
  have ht0 : 0 ≤ t₀ := hL.start_nonneg
  have htI : t ∈ Icc 0 T := hst ht
  obtain ⟨hFs, hFodd, -, -, -, -, -, hFd, -⟩ := hprof (S5.width lam) hh hh1
  have hF0 : waveProfile (S5.width lam) 0 = 0 := by
    have h0 := hFodd 0
    rw [neg_zero] at h0
    linarith
  have hF' : HasDerivAt (waveProfile (S5.width lam)) 1 0 :=
    hFd ▸ ((hFs.differentiable (by simp)) 0).hasDerivAt
  obtain ⟨Bγ, hBγ⟩ := Bridge.Origin.exists_inverse_weight_bound hP hL hO
  have hγ1 : S5.weight lam center t ≤ 1 := Bridge.Origin.weight_le_one hO t ht
  have hγ0 : 0 ≤ S5.weight lam center t := (Bridge.Origin.weight_pos hP hO t ht).le
  -- the hypothesis of Theorem 5.6 from (5.43)
  have hΓ1 : 1 ≤ Γ P := le_trans (le_add_of_nonneg_right (hcP P)) (hΓ P)
  have hDb : D ^ (C6 + C7) ≤ D ^ b := pow_le_pow_right₀ hD hb
  have hD6 : D ^ C6 ≤ D ^ (C6 + C7) := pow_le_pow_right₀ hD (by omega)
  have hl12 : 0 ≤ lam ^ (-1 / 12 : ℝ) := Real.rpow_nonneg hlam0.le _
  have h543' : D ^ C6 * lam ^ (-1 / 12 : ℝ) ≤ 1 := by
    have h1 : D ^ C6 ≤ Γ P * D ^ b :=
      (hD6.trans hDb).trans (le_mul_of_one_le_left (pow_nonneg hD0 _) hΓ1)
    exact (mul_le_mul_of_nonneg_right h1 hl12).trans h543
  have h6c := h6a hT d χ hP hL hO h543' amp hamp P hP2 R S u hu
  dsimp only at h6c
  obtain ⟨-, h534, -, h536, h537, -⟩ := h6c
  -- supports, and the two parts of `W - V₁`
  obtain ⟨hinV, hinC, -⟩ := h4 a ha4 ha3 hT d χ hP hL hO amp hamp P hP2 R S u hu
  let G : HierarchyTwistedProfile T k Vec3 :=
    (∑ p ∈ Finset.Icc 2 P, u.V p) + ∑ p ∈ Finset.Icc 1 P, S5.Cd u (p + 1)
  let Bs : HierarchyTwistedProfile T k Vec3 := ∑ p ∈ Finset.Icc 2 P, u.B p
  have hEq : fderiv ℝ (V t) 0 - fderiv ℝ (U t) 0 -
      χ.value t • rankOne ℝ (center t) (S5.waveVector X k t 0) =
        fderiv ℝ (graphRead Y G t) 0 + fderiv ℝ (graphRead Y Bs t) 0 :=
    centralReturn_eq d hP hamp hst hℓ hF0 hF' (by omega) hu ht
  have hGin : G ∈ inactiveVP T k Vec3 t₀ (S5.radius D a) := by
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun p hp => ?_)
      (Submodule.sum_mem _ fun p hp => ?_)
    · rw [Finset.mem_Icc] at hp
      exact (hinV p (Finset.mem_Icc.mpr ⟨by omega, hp.2⟩)).1
    · rw [Finset.mem_Icc] at hp
      exact hinC (p + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hGsupp : ∀ r ∈ Icc 0 T, ∀ x ∉ S5.envelopeSupport (S5.radius D a), ∀ s,
      G.val.val.val (r, x, s) = G.val.val.val (r, x, 0) := by
    intro r hr x hx s
    exact (hGin (x := (r, x, s)) ⟨⟨hr, mem_univ _⟩, Or.inr hx⟩).trans
      (hGin (x := (r, x, 0)) ⟨⟨hr, mem_univ _⟩, Or.inr hx⟩).symm
  have hBsavg : (S5.ops d).average Bs = Bs := by
    simp only [Bs, map_sum]
    exact Finset.sum_congr rfl fun p hp => (hu.mean p hp).1.phase_independent
  have hBsI := Bridge.phaseIndependent_of_average_eq d hBsavg
  have hBphase : ∀ r ∈ Icc 0 T, ∀ x s, Bs.val.val.val (r, x, s) = Bs.val.val.val (r, x, 0) :=
    fun r hr x s => hBsI (r, x, 0) ⟨hr, mem_univ _⟩ s
  -- (5.44) of Lemma 5.7 at `m = 1`
  have h7G := h7a hT hP hL hO G hGsupp
  have h7B := h7a hT hP hL hO Bs (fun r hr x _ s => hBphase r hr x s)
  dsimp only at h7G h7B
  have hGw := (h7G.1 1 t ht).1
  have hBw := ((h7B.2.2 hBphase).2 1 t htI).1
  simp only [pow_one, mul_one] at hGw hBw
  have hGd := norm_fderiv_graph_le_words hT hP G htI 0
  have hBd := norm_fderiv_graph_le_words hT hP Bs htI 0
  -- the norms from Theorem 5.6
  let wn := fun (f : HierarchyTwistedProfile T k Vec3) =>
    S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) 1 f
  have hwn (f : HierarchyTwistedProfile T k Vec3) : 0 ≤ wn f :=
    Bridge.wNorm_nonneg _ _ 1 hT ht0 _ hBγ f
  have hDC6 : 0 ≤ D ^ C6 := pow_nonneg hD0 _
  have hVp : ∀ p ∈ Finset.Icc 2 P, wn (u.V p) ≤ |K6 1 p| * D ^ C6 * lam ^ (-23 / 12 : ℝ) := by
    intro p hp
    have h := h534 1 p hp
    have hs := hwn (S5.oscSource (S5.ops d) u (S5.curlCorrection d S) p + S5.suppSource (S5.ops d) u p)
    have hq : 0 ≤ lam * S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) 1 (u.p p) :=
      mul_nonneg hlam0.le (Bridge.wNorm_nonneg _ _ 1 hT ht0 _ hBγ _)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp hp).1
    refine le_trans ?_ (le_abs_rpow_of_exponent hDC6 hlam (e₁ := -5 / 4)
      (e₂ := -2 * ((p : ℝ) - 1) / 3) (by linarith))
    change wn (u.V p) ≤ _
    linarith
  have hCp : ∀ p ∈ Finset.Icc 1 P,
      wn (S5.Cd u (p + 1)) ≤ |K6 1 p| * D ^ C6 * lam ^ (-23 / 12 : ℝ) := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp hp).1
    exact (h536 1 p hp).trans (le_abs_rpow_of_exponent hDC6 hlam (e₁ := -9 / 4)
      (e₂ := -2 * ((p : ℝ) - 1) / 3) (by linarith))
  have hWG : wn G ≤ A6 P * D ^ C6 * lam ^ (-23 / 12 : ℝ) := by
    have hadd := Bridge.wNorm_add_le (S5.radius D a) (S5.width lam) 1 hT ht0 _ hBγ
      (∑ p ∈ Finset.Icc 2 P, u.V p) (∑ p ∈ Finset.Icc 1 P, S5.Cd u (p + 1))
    have hs1 := Bridge.wNorm_sum_le (Finset.Icc 2 P) (S5.radius D a) (S5.width lam) 1 hT ht0 _ hBγ
      u.V
    have hs2 := Bridge.wNorm_sum_le (Finset.Icc 1 P) (S5.radius D a) (S5.width lam) 1 hT ht0 _ hBγ
      (fun p => S5.Cd u (p + 1))
    have hsum1 := Finset.sum_le_sum hVp
    have hsum2 := Finset.sum_le_sum hCp
    simp only [← Finset.sum_mul] at hsum1 hsum2
    change wn G ≤ _
    calc wn G ≤ (∑ p ∈ Finset.Icc 2 P, |K6 1 p|) * D ^ C6 * lam ^ (-23 / 12 : ℝ) +
          (∑ p ∈ Finset.Icc 1 P, |K6 1 p|) * D ^ C6 * lam ^ (-23 / 12 : ℝ) := by
          change wn G ≤ _ at hadd
          linarith
      _ = A6 P * D ^ C6 * lam ^ (-23 / 12 : ℝ) := by
          simp only [A6]
          ring
  have hUB : S5.uNorm (S5.radius D a) (S5.width lam) 1 Bs ≤ |KP6 1 P| * D ^ C6 * lam ^ (-5 / 2 : ℝ) := by
    have h := (h537 1).2
    have hm := Bridge.uNorm_nonneg (S5.radius D a) (S5.width lam) 1 hT
      (∑ p ∈ Finset.Icc 2 P, S5.meanSource (S5.ops d) u (S5.curlCorrection d S) R p)
    have hK : KP6 1 P * D ^ C6 * lam ^ (-5 / 2 : ℝ) ≤ |KP6 1 P| * D ^ C6 * lam ^ (-5 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hDC6)
        (Real.rpow_nonneg hlam0.le _)
    change S5.uNorm _ _ 1 Bs + _ ≤ _ at h
    linarith
  -- assembling the bound
  have hl512 : lam ^ (3 / 2 : ℝ) * lam ^ (-23 / 12 : ℝ) = lam ^ (-5 / 12 : ℝ) := by
    rw [← Real.rpow_add hlam0]
    norm_num
  have hl52 : lam ^ (-5 / 2 : ℝ) ≤ lam ^ (-5 / 12 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlam (by norm_num)
  have hl0 : 0 ≤ lam ^ (-5 / 12 : ℝ) := Real.rpow_nonneg hlam0.le _
  have hl32 : 0 ≤ lam ^ (3 / 2 : ℝ) := Real.rpow_nonneg hlam0.le _
  have hDC7 : 0 ≤ D ^ C7 := pow_nonneg hD0 _
  have hDsplit : D ^ (C6 + C7) = D ^ C6 * D ^ C7 := pow_add D C6 C7
  have hG' : ‖fderiv ℝ (graphRead Y G t) 0‖ ≤ |K7 1| * A6 P * D ^ (C6 + C7) * lam ^ (-5 / 12 : ℝ) := by
    have hw0 := hwn G
    have h1 : K7 1 * (D ^ C7 * lam ^ (3 / 2 : ℝ)) * S5.weight lam center t * wn G ≤
        |K7 1| * (D ^ C7 * lam ^ (3 / 2 : ℝ)) * wn G := by
      rw [mul_assoc (K7 1 * _)]
      refine mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hDC7 hl32)) ?_
        (mul_nonneg hγ0 hw0) (mul_nonneg (abs_nonneg _) (mul_nonneg hDC7 hl32))
      exact mul_le_of_le_one_left hw0 hγ1
    have h2 : |K7 1| * (D ^ C7 * lam ^ (3 / 2 : ℝ)) * wn G ≤
        |K7 1| * (D ^ C7 * lam ^ (3 / 2 : ℝ)) * (A6 P * D ^ C6 * lam ^ (-23 / 12 : ℝ)) :=
      mul_le_mul_of_nonneg_left hWG (mul_nonneg (abs_nonneg _) (mul_nonneg hDC7 hl32))
    have h3 : |K7 1| * (D ^ C7 * lam ^ (3 / 2 : ℝ)) * (A6 P * D ^ C6 * lam ^ (-23 / 12 : ℝ)) =
        |K7 1| * A6 P * D ^ (C6 + C7) * lam ^ (-5 / 12 : ℝ) := by
      rw [hDsplit, ← hl512]
      ring
    exact hGd.trans (hGw.trans (h1.trans (h2.trans h3.le)))
  have hB' : ‖fderiv ℝ (graphRead Y Bs t) 0‖ ≤ |K7 1| * |KP6 1 P| * D ^ (C6 + C7) * lam ^ (-5 / 12 : ℝ) := by
    have hu0 := Bridge.uNorm_nonneg (S5.radius D a) (S5.width lam) 1 hT Bs
    have h1 : K7 1 * D ^ C7 * S5.uNorm (S5.radius D a) (S5.width lam) 1 Bs ≤
        |K7 1| * D ^ C7 * (|KP6 1 P| * D ^ C6 * lam ^ (-5 / 2 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) hDC7) hUB hu0
        (mul_nonneg (abs_nonneg _) hDC7)
    have h2 : |K7 1| * D ^ C7 * (|KP6 1 P| * D ^ C6 * lam ^ (-5 / 2 : ℝ)) ≤
        |K7 1| * |KP6 1 P| * D ^ (C6 + C7) * lam ^ (-5 / 12 : ℝ) := by
      rw [hDsplit]
      have hc : 0 ≤ |K7 1| * |KP6 1 P| * (D ^ C6 * D ^ C7) := by positivity
      calc |K7 1| * D ^ C7 * (|KP6 1 P| * D ^ C6 * lam ^ (-5 / 2 : ℝ)) =
            |K7 1| * |KP6 1 P| * (D ^ C6 * D ^ C7) * lam ^ (-5 / 2 : ℝ) := by ring
        _ ≤ |K7 1| * |KP6 1 P| * (D ^ C6 * D ^ C7) * lam ^ (-5 / 12 : ℝ) :=
            mul_le_mul_of_nonneg_left hl52 hc
    exact hBd.trans (hBw.trans (h1.trans h2))
  have hsplit : lam ^ (-5 / 12 : ℝ) = lam ^ (-1 / 12 : ℝ) * lam ^ (-1 / 3 : ℝ) := by
    rw [← Real.rpow_add hlam0]
    norm_num
  have hl3 : 0 ≤ lam ^ (-1 / 3 : ℝ) := Real.rpow_nonneg hlam0.le _
  have hcΓ : cP P ≤ Γ P := le_trans (le_add_of_nonneg_left zero_le_one) (hΓ P)
  rw [hEq]
  calc ‖fderiv ℝ (graphRead Y G t) 0 + fderiv ℝ (graphRead Y Bs t) 0‖
      ≤ ‖fderiv ℝ (graphRead Y G t) 0‖ + ‖fderiv ℝ (graphRead Y Bs t) 0‖ := norm_add_le _ _
    _ ≤ cP P * D ^ (C6 + C7) * lam ^ (-5 / 12 : ℝ) := by
        have : cP P * D ^ (C6 + C7) * lam ^ (-5 / 12 : ℝ) =
            |K7 1| * A6 P * D ^ (C6 + C7) * lam ^ (-5 / 12 : ℝ) +
              |K7 1| * |KP6 1 P| * D ^ (C6 + C7) * lam ^ (-5 / 12 : ℝ) := by
          simp only [cP]
          ring
        rw [this]
        exact add_le_add hG' hB'
    _ ≤ Γ P * D ^ b * lam ^ (-1 / 12 : ℝ) * lam ^ (-1 / 3 : ℝ) := by
        rw [hsplit, ← mul_assoc]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul hcΓ hDb (pow_nonneg hD0 _) (zero_le_one.trans hΓ1)) hl12) hl3
    _ ≤ 1 * lam ^ (-1 / 3 : ℝ) := mul_le_mul_of_nonneg_right h543 hl3
    _ = lam ^ (-1 / 3 : ℝ) := one_mul _

end

end TorusEuler.Paper.Lib.S5c
