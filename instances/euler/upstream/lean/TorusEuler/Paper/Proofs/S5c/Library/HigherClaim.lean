import TorusEuler.Paper.Proofs.S5c.Library.HigherNorms
import TorusEuler.Paper.Proofs.S5c.Library.Support54
import TorusEuler.Paper.Proofs.S5c.Library.Assembly59

/-!
# (5.52) of Lemma 5.9: the Hessian of the higher oscillatory pressures

`higherHessianClaim` proves `HigherHessianClaim` (`sections/08_exact_wave.tex:206-232`,
(5.52)) from Proposition 5.1 (`h5_1`), Proposition 5.4 (`h5_4`), Theorem 5.6 (`h5_6`),
Lemma 5.7 (`h5_7`) and Lemma D.1 (`hD_1`); see the docstring of the theorem.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5c

open HierarchyTwistedProfile InnerProductSpace AppendixD

noncomputable section

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
  {D lam : ℝ}

/-- The phase gradient `κ∂_s q` of a profile vanishing on the inactive region vanishes there
(the inactive region does not depend on the phase). -/
theorem phaseGrad_mem_inactive (d : ParentGeometry hT U X k) {t₀ ℓ : ℝ}
    {q : HierarchyTwistedProfile T k ℝ} (hq : q ∈ inactiveVP T k ℝ t₀ ℓ) :
    (S5.ops d).phaseGrad q ∈ inactiveVP T k Vec3 t₀ ℓ := by
  intro x hx
  obtain ⟨t, a, s⟩ := x
  have hz : (fun z => q.val.val.val (t, a, z)) = fun _ => 0 := by
    funext z
    exact hq (x := (t, a, z)) ⟨⟨hx.1.1, mem_univ _⟩, hx.2⟩
  have h := Bridge.ops_phaseGrad_eval d q hx.1
  change ((S5.ops d).phaseGrad q).val.val.val (t, a, s) =
    deriv (fun z => q.val.val.val (t, a, z)) s • S5.waveVector X k t a at h
  rw [hz, deriv_const, zero_smul] at h
  exact h

/-- The label gradient `𝐝q` of a profile vanishing on the inactive region vanishes there. -/
theorem labelGrad_mem_inactive (d : ParentGeometry hT U X k) {t₀ ℓ : ℝ}
    {q : HierarchyTwistedProfile T k ℝ} (hq : q ∈ inactiveVP T k ℝ t₀ ℓ) :
    (S5.ops d).labelGrad q ∈ inactiveVP T k Vec3 t₀ ℓ :=
  (inactiveLaws (τ := t₀) hT (isClosed_envelopeSupport ℓ) d.inverse d.strain d.covector
    d.mean.inverse_independent).labelGrad hq

/-- **The norm of the gradient profile of a sum of levels.** For `q_p` with transverse
solutions `(V_p, 𝗉_p = q_p)` of (5.15) with sources `F_p`, `p ∈ s`, the profile
`𝐝̃ ∑ q_p = 𝐝 ∑ q_p + κ∂_s ∑ q_p` has `‖·‖_{[1],γ}` at most the sum over `p` of the label part
(`wNorm_labelGrad_le`) and the phase part (`wNorm_phaseGrad_le`) (`08_exact_wave.tex:219-221`). -/
theorem wNorm_gradProfile_le (hD1 : Statement.lemma_D_1) (d : ParentGeometry hT U X k)
    {t₀ ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) {γ : ℝ → ℝ}
    (hγc : ContinuousOn γ (Icc t₀ T)) (hγ : ∀ t ∈ Icc t₀ T, 0 < γ t)
    {B : ℝ} (hB : ∀ t ∈ Icc t₀ T, ‖(γ t)⁻¹‖ ≤ B) {BG BP BM : ℝ}
    (hGfin : FieldNormFinite ℓ h 1
      (fun (t : Icc t₀ T) (x : Vec3 × ℝ) => fderiv ℝ (X t.1 0) (X 0 t.1 x.1)))
    (hGn : fieldNorm ℓ h 1
      (fun (t : Icc t₀ T) (x : Vec3 × ℝ) => fderiv ℝ (X t.1 0) (X 0 t.1 x.1)) ≤ BG)
    (hPfin : FieldNormFinite ℓ h 1 (fun (t : Icc t₀ T) (x : Vec3 × ℝ) =>
      hierarchyLongitudinalProjection (S5.waveVector X k t.1 x.1)))
    (hPn : fieldNorm ℓ h 1 (fun (t : Icc t₀ T) (x : Vec3 × ℝ) =>
      hierarchyLongitudinalProjection (S5.waveVector X k t.1 x.1)) ≤ BP)
    (hMfin : FieldNormFinite ℓ h 1 (fun (t : Icc t₀ T) (x : Vec3 × ℝ) =>
      S5.strainField U X t.1 x.1))
    (hMn : fieldNorm ℓ h 1 (fun (t : Icc t₀ T) (x : Vec3 × ℝ) =>
      S5.strainField U X t.1 x.1) ≤ BM)
    (s : Finset ℕ) (q : ℕ → HierarchyTwistedProfile T k ℝ)
    (F V : ℕ → HierarchyTwistedProfile T k Vec3)
    (hq : ∀ p ∈ s, S5.TransverseSolution d (F p) (V p) (q p))
    (hF0 : ∀ p ∈ s, (S5.ops d).average (F p) = 0) :
    S5.wNorm ℓ h t₀ γ 1
        ((S5.ops d).labelGrad (∑ p ∈ s, q p) + (S5.ops d).phaseGrad (∑ p ∈ s, q p)) ≤
      ∑ p ∈ s, (((hierarchyAdmissibleWords (Fin 4) 1).card * (2 : ℝ) ^ 1 * 2) * BG *
          (3 * ℓ⁻¹ * S5.wNorm ℓ h t₀ γ 2 (q p)) +
        ((hierarchyAdmissibleWords (Fin 4) 1).card * (2 : ℝ) ^ 1 * 2) * BP *
          (S5.wNorm ℓ h t₀ γ 1 (F p) +
            ((hierarchyAdmissibleWords (Fin 4) 1).card * (2 : ℝ) ^ 1 * 4) * BM *
              S5.wNorm ℓ h t₀ γ 1 (V p))) := by
  rw [map_sum, map_sum, ← Finset.sum_add_distrib]
  refine (Bridge.wNorm_sum_le s ℓ h 1 hT ht₀ γ hB _).trans (Finset.sum_le_sum fun p hp => ?_)
  refine (Bridge.wNorm_add_le ℓ h 1 hT ht₀ γ hB _ _).trans (add_le_add ?_ ?_)
  · exact wNorm_labelGrad_le hD1 d hℓ hh ht₀ htT hγc hγ hGfin hGn (q p)
  · exact wNorm_phaseGrad_le hD1 d hℓ hh ht₀ htT hγc hγ hPfin hPn hMfin hMn (hq p hp) (hF0 p hp)

/-- Real arithmetic for one level: with `B_c ℓ_*⁻¹ ≤ κ₀ Z`, `B_c ≤ κ₀ Z`, `B_c² ≤ κ₀² Z`, the
level term of `wNorm_gradProfile_le` is at most `(3c_Lκ₀|K₂| + (c_Pκ₀ + c_Pc_Mκ₀²)|K₁|) Z X`. -/
theorem level_estimate {cL cP cM κ0 Bc Z il X w2 wF wV K2 K1' : ℝ}
    (hcL : 0 ≤ cL) (hcP : 0 ≤ cP) (hcM : 0 ≤ cM) (hκ0 : 0 ≤ κ0) (hZ : 0 ≤ Z)
    (hw2 : 0 ≤ w2) (hwF : 0 ≤ wF) (hwV : 0 ≤ wV)
    (ha : Bc * il ≤ κ0 * Z) (hb : Bc ≤ κ0 * Z) (hc : Bc * Bc ≤ κ0 ^ 2 * Z)
    (h2 : w2 ≤ K2 * X) (h1 : wF + wV ≤ K1' * X) :
    cL * Bc * (3 * il * w2) + cP * Bc * (wF + cM * Bc * wV) ≤
      (3 * cL * κ0 * K2 + (cP * κ0 + cP * cM * κ0 ^ 2) * K1') * Z * X := by
  have e1 : cL * Bc * (3 * il * w2) = 3 * cL * (Bc * il) * w2 := by ring
  have e2 : cP * Bc * (wF + cM * Bc * wV) = cP * Bc * wF + cP * cM * (Bc * Bc) * wV := by ring
  have s1 : 3 * cL * (Bc * il) * w2 ≤ 3 * cL * (κ0 * Z) * (K2 * X) :=
    mul_le_mul (mul_le_mul_of_nonneg_left ha (by positivity)) h2 hw2 (by positivity)
  have s2 : cP * Bc * wF ≤ cP * (κ0 * Z) * wF :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hcP) hwF
  have s3 : cP * cM * (Bc * Bc) * wV ≤ cP * cM * (κ0 ^ 2 * Z) * wV :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity)) hwV
  have s4 : cP * (κ0 * Z) * wF + cP * cM * (κ0 ^ 2 * Z) * wV ≤
      (cP * κ0 + cP * cM * κ0 ^ 2) * Z * (wF + wV) := by
    have : 0 ≤ cP * κ0 * Z * wV + cP * cM * κ0 ^ 2 * Z * wF := by positivity
    nlinarith [this]
  have s5 : (cP * κ0 + cP * cM * κ0 ^ 2) * Z * (wF + wV) ≤
      (cP * κ0 + cP * cM * κ0 ^ 2) * Z * (K1' * X) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have e3 : (3 * cL * κ0 * K2 + (cP * κ0 + cP * cM * κ0 ^ 2) * K1') * Z * X =
      3 * cL * (κ0 * Z) * (K2 * X) + (cP * κ0 + cP * cM * κ0 ^ 2) * Z * (K1' * X) := by ring
  rw [e1, e2, e3]
  linarith [s1, s2, s3, s4, s5]

/-- A jointly smooth field on the slab is smooth at each time. -/
theorem slice_smooth_c {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3))) {t : ℝ}
    (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (f t) :=
  contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

/-- The constant `#W_1 · 2 · 2` of (D.4) at order one for a bilinear map of norm at most one
(the factor `2‖B‖ ≤ 2`). -/
def prodC1 : ℝ := ((hierarchyAdmissibleWords (Fin 4) 1).card : ℝ) * (2 : ℝ) ^ 1 * 2

/-- The constant `#W_1 · 2 · 4` of (D.4) at order one for `‖B‖ ≤ 2`. -/
def prodC4 : ℝ := ((hierarchyAdmissibleWords (Fin 4) 1).card : ℝ) * (2 : ℝ) ^ 1 * 4

/-- The number of words of length at most one in the three label directions. -/
def coefC : ℝ := ((hierarchyAdmissibleWords (Fin 3) 1).card : ℝ)

/-- The constant `prodC1` of (D.4) at order one is nonnegative. -/
theorem prodC1_nonneg : 0 ≤ prodC1 := by unfold prodC1; positivity
/-- The constant `prodC4` of (D.4) at order one is nonnegative. -/
theorem prodC4_nonneg : 0 ≤ prodC4 := by unfold prodC4; positivity
/-- The constant `coefC` of (D.6) at order one is nonnegative. -/
theorem coefC_nonneg : 0 ≤ coefC := by unfold coefC; positivity

/-- The constant `κ₀ = #W_1 · max(K₁(1), 0)` bounding the order-one norms of the coefficients
`(D_aX)⁻¹`, `M`, `P_κ` by `κ₀ 𝖣^{C₁}` ((D.6), (5.8) of Proposition 5.1). -/
def coefK (K1 : ℕ → ℝ) : ℝ := coefC * max (K1 1) 0

/-- The level constant of (5.52): `3c₁κ₀|K₆(2,p)| + (c₁κ₀ + c₁c₄κ₀²)|K₆(1,p)|`. -/
def levelK (K1 : ℕ → ℝ) (K6 : ℕ → ℕ → ℝ) (p : ℕ) : ℝ :=
  3 * prodC1 * coefK K1 * |K6 2 p| + (prodC1 * coefK K1 + prodC1 * prodC4 * coefK K1 ^ 2) * |K6 1 p|

/-- The level constant `levelK K1 K6 p` of (5.52) is nonnegative. -/
theorem levelK_nonneg (K1 : ℕ → ℝ) (K6 : ℕ → ℕ → ℝ) (p : ℕ) : 0 ≤ levelK K1 K6 p := by
  have h1 := prodC1_nonneg
  have h4 := prodC4_nonneg
  have h0 : 0 ≤ coefK K1 := mul_nonneg coefC_nonneg (le_max_right _ _)
  unfold levelK
  positivity

set_option maxHeartbeats 3200000 in
/-- **(5.52) of Lemma 5.9** (`sections/08_exact_wave.tex:206-232`):
`‖D_x²∑_{p=2}^P 𝗉_p^♮‖_∞ ≤ K_P 𝖣^C λ^{-5/12}`. Following the text: `∇_x𝗉^♮ = (𝐝̃𝗉)^♮`
(chain rule (3.1), `gradient_graphRead_eq`); `𝐝̃ ∑𝗉_p = 𝐝∑𝗉_p + κ∂_s∑𝗉_p` is bounded in
`‖·‖_{[1],γ}` by Lemma D.1 (`hD_1`: (D.4) for the products `(∂_{a_j}𝗉) Gᵀe_j` and
`P_κ(f - 2MV)`, (D.3) for the label derivatives; `wNorm_gradProfile_le`), where
`κ∂_s𝗉_p = P_κ(f_p + f_p^S - 2MV_p)` is the transverse equation (5.15) (`slices_phaseGrad_eq`),
the coefficients `(D_aX)⁻¹`, `M`, `P_κ` have norms `‖·‖_{[1]} ≤ κ₀𝖣^{C₁}` by (D.6) and (5.8) of
`h5_1` (`coefNorm`), and `‖V_p‖_{[1],γ} + ‖f_p + f_p^S‖_{[1],γ} + λ‖𝗉_p‖_{[2],γ} ≤
K_{n,p}𝖣^{C₆}λ^{-5/4-2(p-1)/3} ≤ K𝖣^{C₆}λ^{-23/12}` is (5.34) of `h5_6` (the least decay is at
`p = 2`). The oscillatory pressures vanish for `t < t₀` and outside `supp g` (`h5_4`, through
`inactive_of_prop54`: the supports of the sources and the vanishing before `t₀`), which gives the
phase-independence hypothesis of (5.44) of `h5_7` for `𝐝̃ ∑𝗉_p` at `m = 1`:
`∑_i sup|∂_i(𝐝̃∑𝗉_p)^♮| ≤ K₇𝖣^{C₇}λ^{3/2}γ(t)‖𝐝̃∑𝗉_p‖_{[1],γ} ≤ K𝖣^Cλ^{-5/12}` with
`γ ≤ 1` and `3/2 - 23/12 = -5/12`. Constants: `a₀ = max (a₀(5.4), a₀(5.6), a₀(5.7), C₁, 3)`,
`C = C₆ + C₇ + a + 2C₁`, `K_P = |K₇(1)| ∑_{p=2}^P levelK p`. -/
theorem higherHessianClaim (h5_1 : Statement.proposition_5_1) (h5_4 : Statement.proposition_5_4)
    (h5_6 : Statement.theorem_5_6) (h5_7 : Statement.lemma_5_7) (hD_1 : Statement.lemma_D_1) :
    HigherHessianClaim := by
  obtain ⟨C1, K1, h1⟩ := h5_1
  obtain ⟨_Kf, h1⟩ := h1 (fun _ => 0)
  obtain ⟨a4, h4⟩ := inactive_of_prop54 h5_4
  obtain ⟨a6, h6⟩ := h5_6
  obtain ⟨a7, h7⟩ := h5_7
  refine ⟨max (max (max a4 a6) (max a7 C1)) 3, fun a ha => ?_⟩
  simp only [max_le_iff] at ha
  obtain ⟨⟨⟨ha4, ha6⟩, ha7, haC1⟩, ha3⟩ := ha
  obtain ⟨C6, K6, KP6, h6a⟩ := h6 a ha6
  obtain ⟨C7, K7, h7a⟩ := h7 a ha7
  refine ⟨C6 + C7 + (a + 2 * C1), fun P => |K7 1| * ∑ p ∈ Finset.Icc 2 P, levelK K1 K6 p, ?_⟩
  intro T hT U X pU k D lam t₀ center d χ hP hL hO hsm amp hamp P hP2 R S u hu t ht x
  -- standing facts
  have hD : 1 ≤ D := Bridge.Parent.scale_ge_one hP
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hDp : ∀ m : ℕ, 0 ≤ D ^ m := fun m => pow_nonneg hD0.le m
  have hlam : 1 ≤ lam := hP.frequency_ge_one
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam
  have hℓ : 0 < S5.radius D a := Bridge.radius_pos hP a
  have hfit : 2 * S5.radius D a < 1 / 2 := Bridge.radius_fits hP.scale_ge_two ha3
  have hh : 0 < S5.width lam := Bridge.width_pos hP
  have ht0 : 0 ≤ t₀ := hL.start_nonneg
  have htT : t₀ ≤ T := hL.start_lt.le
  have hst : Icc t₀ T ⊆ Icc 0 T := Bridge.Launch.active_subset hL
  have hKP : 0 ≤ |K7 1| * ∑ p ∈ Finset.Icc 2 P, levelK K1 K6 p :=
    mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun p _ => levelK_nonneg K1 K6 p)
  have hRHS : 0 ≤ (|K7 1| * ∑ p ∈ Finset.Icc 2 P, levelK K1 K6 p) * D ^ (C6 + C7 + (a + 2 * C1)) *
      lam ^ (-5 / 12 : ℝ) :=
    mul_nonneg (mul_nonneg hKP (hDp _)) (Real.rpow_nonneg hlam0.le _)
  -- the profile `g₀ = 𝐝̃ ∑ 𝗉_p` and the chain rule
  let Q : HierarchyTwistedProfile T k ℝ := ∑ p ∈ Finset.Icc 2 P, u.p p
  let g₀ : HierarchyTwistedProfile T k Vec3 := (S5.ops d).labelGrad Q + (S5.ops d).phaseGrad Q
  have hgrad : gradient (graphRead (fun t => X t 0) Q t) = graphRead (fun t => X t 0) g₀ t :=
    gradient_graphRead_eq d hP Q ht
  -- supports and vanishing before `t₀` (Proposition 5.4)
  obtain ⟨hinV, -, -⟩ := h4 a ha4 ha3 hT d χ hP hL hO amp hamp P hP2 R S u hu
  have hQin : Q ∈ inactiveVP T k ℝ t₀ (S5.radius D a) :=
    Submodule.sum_mem _ fun p hp => (hinV p (by rw [Finset.mem_Icc] at hp ⊢; omega)).2
  have hg0in : g₀ ∈ inactiveVP T k Vec3 t₀ (S5.radius D a) :=
    Submodule.add_mem _ (labelGrad_mem_inactive d hQin) (phaseGrad_mem_inactive d hQin)
  change ‖fderiv ℝ (gradient (graphRead (fun t => X t 0) Q t)) x‖ ≤ _
  rw [hgrad]
  by_cases hact : t₀ ≤ t
  swap
  · have hz : graphRead (fun t => X t 0) g₀ t = 0 := by
      funext y
      exact hg0in (x := (t, X t 0 y, ⟪k, X t 0 y⟫_ℝ)) ⟨⟨ht, mem_univ _⟩, Or.inl (lt_of_not_ge hact)⟩
    rw [hz, fderiv_zero, Pi.zero_apply, norm_zero]
    exact hRHS
  have htI : t ∈ Icc t₀ T := ⟨hact, ht.2⟩
  -- (5.44) of Lemma 5.7 at `m = 1` for `g₀`
  have hg0supp : ∀ r ∈ Icc 0 T, ∀ y ∉ S5.envelopeSupport (S5.radius D a), ∀ s,
      g₀.val.val.val (r, y, s) = g₀.val.val.val (r, y, 0) := by
    intro r hr y hy s
    exact (hg0in (x := (r, y, s)) ⟨⟨hr, mem_univ _⟩, Or.inr hy⟩).trans
      (hg0in (x := (r, y, 0)) ⟨⟨hr, mem_univ _⟩, Or.inr hy⟩).symm
  have h7c := h7a hT hP hL hO g₀ hg0supp
  dsimp only at h7c
  have hw := (h7c.1 1 t htI).1
  simp only [pow_one] at hw
  have hd := norm_fderiv_graph_le_words hT hP g₀ ht x
  -- (5.34) of Theorem 5.6
  have hsm6 : D ^ C6 * lam ^ (-1 / 12 : ℝ) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hD (by omega : C6 ≤ C6 + C7 + (a + 2 * C1)))
      (Real.rpow_nonneg hlam0.le _)) hsm
  have h6c := h6a hT d χ hP hL hO hsm6 amp hamp P hP2 R S u hu
  dsimp only at h6c
  obtain ⟨-, h534, -, -, -, -⟩ := h6c
  obtain ⟨Bγ, hBγ⟩ := Bridge.Origin.exists_inverse_weight_bound hP hL hO
  have hγ1 : S5.weight lam center t ≤ 1 := Bridge.Origin.weight_le_one hO t htI
  have hγ0 : 0 ≤ S5.weight lam center t := (Bridge.Origin.weight_pos hP hO t htI).le
  have hγpos : ∀ r ∈ Icc t₀ T, 0 < S5.weight lam center r := Bridge.Origin.weight_pos hP hO
  have hγc := Bridge.Origin.weight_continuousOn hO
  -- the coefficients (D.6), (5.8) of Proposition 5.1
  have hℓle : S5.radius D a ≤ (D ^ C1)⁻¹ :=
    inv_anti₀ (pow_pos hD0 _) (pow_le_pow_right₀ hD haC1)
  obtain ⟨hD6, -, h58⟩ := h1 hT hP hL
  have h58' := fun n s hs => h58 (S5.radius D a) hℓ hℓle n s hs
  have hιt : ∀ s : Icc t₀ T, s.1 ∈ Icc 0 T := fun s => hst s.2
  have hB1 : 0 ≤ max (K1 1) 0 * D ^ C1 := mul_nonneg (le_max_right _ _) (hDp _)
  have hGs : ∀ r ∈ Icc 0 T, ContDiff ℝ ∞ (fun b => fderiv ℝ (X r 0) (X 0 r b)) := fun r hr =>
    slice_smooth_c (f := fun r b => fderiv ℝ (X r 0) (X 0 r b))
      (hP.flow.contDiffOn_inverseLabelDerivative hT hP.velocity_smooth hP.velocity_periodic) hr
  have hMs : ∀ r ∈ Icc 0 T, ContDiff ℝ ∞ (S5.strainField U X r) := fun r hr =>
    slice_smooth_c (f := S5.strainField U X) (Bridge.Parent.strainField_smooth hT hP) hr
  have hPs : ∀ r ∈ Icc 0 T, ContDiff ℝ ∞
      (fun b => hierarchyLongitudinalProjection (S5.waveVector X k r b)) := fun r hr =>
    contDiff_hierarchyLongitudinalProjection
      (slice_smooth_c (f := S5.waveVector X k) (Bridge.Parent.waveVector_smooth hT hP) hr)
      (fun b => Bridge.Parent.waveVector_ne_zero hT hP hL.carrier_ne_zero hr b)
  have hGc := coefNorm (T := T) (Subtype.val : Icc t₀ T → ℝ) hιt
    (ContinuousLinearMap.id ℝ (Vec3 →L[ℝ] Vec3)) (c := fun r b => fderiv ℝ (X r 0) (X 0 r b))
    (ℓ := S5.radius D a) (h := S5.width lam) hℓ 1
    (b := fun m => K1 m * D ^ (C1 * (m + 1))) hB1 hGs
    (fun m r hr b => (hD6 m r hr b).2.1) (fun r hr => (h58' 1 r hr).2.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hDp _)))
  have hMc := coefNorm (T := T) (Subtype.val : Icc t₀ T → ℝ) hιt
    (ContinuousLinearMap.id ℝ (Vec3 →L[ℝ] Vec3)) (c := S5.strainField U X)
    (ℓ := S5.radius D a) (h := S5.width lam) hℓ 1
    (b := fun m => K1 m * D ^ (C1 * (m + 1))) hB1 hMs
    (fun m r hr b => (hD6 m r hr b).2.2.1) (fun r hr => (h58' 1 r hr).2.2.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hDp _)))
  have hPc := coefNorm (T := T) (Subtype.val : Icc t₀ T → ℝ) hιt
    (ContinuousLinearMap.id ℝ (Vec3 →L[ℝ] Vec3))
    (c := fun r b => hierarchyLongitudinalProjection (S5.waveVector X k r b))
    (ℓ := S5.radius D a) (h := S5.width lam) hℓ 1
    (b := fun m => K1 m * D ^ (C1 * (m + 1))) hB1 hPs
    (fun m r hr b => (hD6 m r hr b).2.2.2.2.2) (fun r hr => (h58' 1 r hr).2.2.2.2.2.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hDp _)))
  -- the order-one norms of the coefficients are at most `κ₀ 𝖣^{C₁}`
  let Bc : ℝ := coefC * (max (K1 1) 0 * D ^ C1)
  have hk0 : 0 ≤ coefK K1 := mul_nonneg coefC_nonneg (le_max_right _ _)
  have hBeq : Bc = coefK K1 * D ^ C1 := by
    simp only [Bc, coefK]
    ring
  have hid : ‖ContinuousLinearMap.id ℝ (Vec3 →L[ℝ] Vec3)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hbd : ∀ {z : ℝ}, z ≤ coefC * (‖ContinuousLinearMap.id ℝ (Vec3 →L[ℝ] Vec3)‖ *
      (max (K1 1) 0 * D ^ C1)) → z ≤ Bc := fun hz =>
    hz.trans (by
      calc _ ≤ coefC * (1 * (max (K1 1) 0 * D ^ C1)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hid hB1) coefC_nonneg
        _ = Bc := by simp only [Bc, one_mul])
  -- the sum over the levels
  let src : ℕ → HierarchyTwistedProfile T k Vec3 := fun p =>
    S5.oscSource (S5.ops d) u (S5.curlCorrection d S) p + S5.suppSource (S5.ops d) u p
  have hBavg : ∀ j, 2 ≤ j → j ≤ P → (S5.ops d).average (u.B j) = u.B j := fun j h1 h2 =>
    (hu.mean j (Finset.mem_Icc.mpr ⟨h1, h2⟩)).1.phase_independent
  have hF0 : ∀ p ∈ Finset.Icc 2 P, (S5.ops d).average (src p) = 0 := fun p hp =>
    average_transverseSource d u (S5.curlCorrection d S) (p := p) fun j hj =>
      hBavg j (by rw [Finset.mem_Icc] at hj hp; omega) (by rw [Finset.mem_Icc] at hj hp; omega)
  have hsum := wNorm_gradProfile_le hD_1 d hℓ hh ht0 htT hγc hγpos hBγ (BG := Bc) (BP := Bc)
    (BM := Bc) hGc.1 (hbd hGc.2) hPc.1 (hbd hPc.2) hMc.1 (hbd hMc.2) (Finset.Icc 2 P) u.p src u.V
    (fun p hp => hu.transverse p hp) hF0
  -- the level bounds from (5.34)
  have hil : (S5.radius D a)⁻¹ = D ^ a := by
    unfold S5.radius
    rw [inv_inv]
  have hZ0 : 0 ≤ D ^ (a + 2 * C1) := hDp _
  have hDC6 : 0 ≤ D ^ C6 := hDp _
  have hX0 : 0 ≤ D ^ C6 * lam ^ (-23 / 12 : ℝ) := mul_nonneg hDC6 (Real.rpow_nonneg hlam0.le _)
  have hwn0 (n : ℕ) (f : HierarchyTwistedProfile T k Vec3) :
      0 ≤ S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) n f :=
    Bridge.wNorm_nonneg _ _ n hT ht0 _ hBγ f
  have hwp0 (n : ℕ) (f : HierarchyTwistedProfile T k ℝ) :
      0 ≤ S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) n f :=
    Bridge.wNorm_nonneg _ _ n hT ht0 _ hBγ f
  have hlev : ∀ p ∈ Finset.Icc 2 P,
      prodC1 * Bc * (3 * (S5.radius D a)⁻¹ *
          S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) 2 (u.p p)) +
        prodC1 * Bc * (S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) 1 (src p) +
          prodC4 * Bc *
            S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) 1 (u.V p)) ≤
      levelK K1 K6 p * D ^ (a + 2 * C1) * (D ^ C6 * lam ^ (-23 / 12 : ℝ)) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp hp).1
    have hexp : (-5 / 4 : ℝ) + -2 * ((p : ℝ) - 1) / 3 ≤ -23 / 12 := by linarith
    have hb1 := le_abs_rpow_of_exponent (K := K6 1 p) hDC6 hlam hexp
    have hb2 := le_abs_rpow_of_exponent (K := K6 2 p) hDC6 hlam hexp
    have e1 := h534 1 p hp
    have e2 := h534 2 p hp
    have hF := hwn0 1 (src p)
    have hV := hwn0 1 (u.V p)
    have hF2 := hwn0 2 (src p)
    have hV2 := hwn0 2 (u.V p)
    have hq1 := hwp0 1 (u.p p)
    have hq2 := hwp0 2 (u.p p)
    have hlq1 : 0 ≤ lam * S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) 1 (u.p p) :=
      mul_nonneg hlam0.le hq1
    have hlq2 : S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) 2 (u.p p) ≤
        lam * S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) 2 (u.p p) :=
      le_mul_of_one_le_left hq2 hlam
    have h2 : S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) 2 (u.p p) ≤
        |K6 2 p| * (D ^ C6 * lam ^ (-23 / 12 : ℝ)) := by
      rw [← mul_assoc]
      change _ + _ + _ ≤ _ at e2
      linarith
    have h1' : S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) 1 (src p) +
        S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) 1 (u.V p) ≤
        |K6 1 p| * (D ^ C6 * lam ^ (-23 / 12 : ℝ)) := by
      rw [← mul_assoc]
      change _ + _ + _ ≤ _ at e1
      linarith
    have hDa : (S5.radius D a)⁻¹ = D ^ a := hil
    have hc1 : D ^ C1 * D ^ C1 = D ^ (2 * C1) := by
      rw [← pow_add]
      congr 1
      omega
    have ha : Bc * (S5.radius D a)⁻¹ ≤ coefK K1 * D ^ (a + 2 * C1) := by
      rw [hDa, hBeq]
      calc coefK K1 * D ^ C1 * D ^ a = coefK K1 * D ^ (C1 + a) := by rw [pow_add]; ring
        _ ≤ coefK K1 * D ^ (a + 2 * C1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) hk0
    have hb : Bc ≤ coefK K1 * D ^ (a + 2 * C1) := by
      rw [hBeq]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) hk0
    have hc : Bc * Bc ≤ coefK K1 ^ 2 * D ^ (a + 2 * C1) := by
      rw [hBeq]
      calc coefK K1 * D ^ C1 * (coefK K1 * D ^ C1) = coefK K1 ^ 2 * (D ^ C1 * D ^ C1) := by ring
        _ = coefK K1 ^ 2 * D ^ (2 * C1) := by rw [hc1]
        _ ≤ coefK K1 ^ 2 * D ^ (a + 2 * C1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) (sq_nonneg _)
    have := level_estimate (cL := prodC1) (cP := prodC1) (cM := prodC4) (κ0 := coefK K1) (Bc := Bc)
      (Z := D ^ (a + 2 * C1)) (il := (S5.radius D a)⁻¹) (X := D ^ C6 * lam ^ (-23 / 12 : ℝ))
      prodC1_nonneg prodC1_nonneg prodC4_nonneg hk0 hZ0 hq2 hF hV ha hb hc h2 h1'
    exact this
  have hwn : S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) 1 g₀ ≤
      (∑ p ∈ Finset.Icc 2 P, levelK K1 K6 p) * D ^ (a + 2 * C1) *
        (D ^ C6 * lam ^ (-23 / 12 : ℝ)) := by
    refine hsum.trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_le_sum hlev
  -- the final estimate
  have hl512 : lam ^ (3 / 2 : ℝ) * lam ^ (-23 / 12 : ℝ) = lam ^ (-5 / 12 : ℝ) := by
    rw [← Real.rpow_add hlam0]
    norm_num
  have hDs : D ^ (C6 + C7 + (a + 2 * C1)) = D ^ (a + 2 * C1) * D ^ C6 * D ^ C7 := by
    rw [pow_add, pow_add]
    ring
  have hl32 : 0 ≤ lam ^ (3 / 2 : ℝ) := Real.rpow_nonneg hlam0.le _
  have hDC7 : 0 ≤ D ^ C7 := hDp _
  have hwg0 := hwn0 1 g₀
  have h1' : K7 1 * (D ^ C7 * lam ^ (3 / 2 : ℝ)) * S5.weight lam center t *
      S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) 1 g₀ ≤
      |K7 1| * (D ^ C7 * lam ^ (3 / 2 : ℝ)) *
        S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) 1 g₀ := by
    rw [mul_assoc (K7 1 * _)]
    refine mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hDC7 hl32)) ?_
      (mul_nonneg hγ0 hwg0) (mul_nonneg (abs_nonneg _) (mul_nonneg hDC7 hl32))
    exact mul_le_of_le_one_left hwg0 hγ1
  have h2' : |K7 1| * (D ^ C7 * lam ^ (3 / 2 : ℝ)) *
        S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) 1 g₀ ≤
      |K7 1| * (D ^ C7 * lam ^ (3 / 2 : ℝ)) * ((∑ p ∈ Finset.Icc 2 P, levelK K1 K6 p) *
        D ^ (a + 2 * C1) * (D ^ C6 * lam ^ (-23 / 12 : ℝ))) :=
    mul_le_mul_of_nonneg_left hwn (mul_nonneg (abs_nonneg _) (mul_nonneg hDC7 hl32))
  have h3' : |K7 1| * (D ^ C7 * lam ^ (3 / 2 : ℝ)) * ((∑ p ∈ Finset.Icc 2 P, levelK K1 K6 p) *
        D ^ (a + 2 * C1) * (D ^ C6 * lam ^ (-23 / 12 : ℝ))) =
      (|K7 1| * ∑ p ∈ Finset.Icc 2 P, levelK K1 K6 p) * D ^ (C6 + C7 + (a + 2 * C1)) *
        lam ^ (-5 / 12 : ℝ) := by
    rw [hDs, ← hl512]
    ring
  exact hd.trans (hw.trans (h1'.trans (h2'.trans h3'.le)))

end

end TorusEuler.Paper.Lib.S5c
