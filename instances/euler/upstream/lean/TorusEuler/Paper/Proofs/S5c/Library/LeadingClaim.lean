import TorusEuler.Paper.Proofs.S5c.Library.LeadingHess
import TorusEuler.Paper.Proofs.S5c.Library.HigherClaim
import TorusEuler.Paper.Proofs.S5c.Library.Assembly59

/-!
# The leading pressure Hessian of Lemma 5.9

`leadingHessianClaim`: the signed bound `D_x²𝗉_1^♮ ≤ K𝖣^Cλ^{-1/4} Id` from the Hessian
identity (5.51) (`sections/08_exact_wave.tex:172-204`).

`quarter_pow`, `quarter_pow_neg`: `λ^{n/4} = r^n`, `λ^{-n/4} = r^{-n}` with `r = λ^{1/4}`, so the
exponent arithmetic of the proof is polynomial in `r`.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5c

open HierarchyTwistedProfile LocalizedAmplitude InnerProductSpace AppendixD

noncomputable section

/-- Power identity for the exponent `1/4`. -/
theorem quarter_pow {lam : ℝ} (hl : 0 ≤ lam) (n : ℕ) :
    lam ^ ((n : ℝ) / 4) = (lam ^ (1 / 4 : ℝ)) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hl]
  ring_nf

/-- Negative-exponent form of `quarter_pow`. -/
theorem quarter_pow_neg {lam : ℝ} (hl : 0 ≤ lam) (n : ℕ) :
    lam ^ (-(n : ℝ) / 4) = ((lam ^ (1 / 4 : ℝ)) ^ n)⁻¹ := by
  rw [neg_div, Real.rpow_neg hl, quarter_pow hl]

/-- Real arithmetic for the remaining tensors of (5.51): with `D, r ≥ 1`, `ℓ⁻¹ = D^a`, `h⁻¹ = r²`,
`λ = r⁴` and the coefficient norms `B_c = c_c k_B D^{C₁}`, `B_κ = c_c D r⁴ k_B D^{C₁}`, the sum of the
two terms is at most `28 c₁ c_c k_B D^N r⁶ W ‖v‖²` for `C₁ + 2a + 2 ≤ N`. -/
theorem remainder_bound {D r W v2 c1 cc kB : ℝ} (a C1 N : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hW : 0 ≤ W) (hv2 : 0 ≤ v2) (hc1 : 0 ≤ c1) (hcc : 0 ≤ cc) (hk : 0 ≤ kB)
    (hN : C1 + 2 * a + 2 ≤ N) :
    4 ^ 1 * (c1 * (cc * (kB * D ^ C1)) * (3 * D ^ a * W)) * v2 *
        (D * D ^ a + D * r ^ 4 * D * r ^ 2) +
      4 ^ 1 * (c1 * (cc * (D * r ^ 4 * (kB * D ^ C1))) * (r ^ 2 * W)) * v2 * (D * D ^ a) ≤
    28 * c1 * cc * kB * D ^ N * v2 * (r ^ 6 * W) := by
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hr6 : 1 ≤ r ^ 6 := one_le_pow₀ hr
  have e1 : D ^ (C1 + 2 * a + 1) ≤ D ^ N * r ^ 6 :=
    (pow_le_pow_right₀ hD (by omega)).trans (le_mul_of_one_le_right (pow_nonneg hD0 _) hr6)
  have e2 : D ^ (C1 + a + 2) * r ^ 6 ≤ D ^ N * r ^ 6 :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD (by omega)) (pow_nonneg hr0 _)
  have hP : 0 ≤ c1 * cc * kB * W * v2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc1 hcc) hk) hW) hv2
  calc _ = (c1 * cc * kB * W * v2) *
        (12 * D ^ (C1 + 2 * a + 1) + 16 * (D ^ (C1 + a + 2) * r ^ 6)) := by ring
    _ ≤ (c1 * cc * kB * W * v2) * (28 * (D ^ N * r ^ 6)) :=
        mul_le_mul_of_nonneg_left (by linarith) hP
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
/-- **The leading pressure Hessian of Lemma 5.9** (`sections/08_exact_wave.tex:172-204`).
For `t ≥ t₀` and every `x`, after a lattice translation putting `Y(x)` in the label cell (the
Hessian of the periodic readout is periodic), `D_x²𝗉_1^♮ = (𝐝̃𝐝̃𝗉_1)^♮` is split as in (5.51)
(`leading_hess_point`):

* the first tensor `-c_𝐚F_h'κ⊗κ` (with `𝗉_1 = -c_𝐚P_h`, `c_𝐚 = χ̃ p_w`) is bounded above by
  `C h c_𝐚|κ|²` using `F_h' ≥ -Ch` from `h3_1` (Lemma 3.1, also `P_h' = F_h`), and
  `0 ≤ c_𝐚|κ|² ≤ 2|κ||M||𝐚| ≤ 4𝖣³λ^{1/4}` from (5.19) of `h5_3` (`|𝐚| ≤ 2|𝐚(t,0)| ≤
  2λ^{-3/4}`, `κ·M𝐚 > 0` on `|a| ≤ 2ℓ_*`; `c_𝐚 = 0` elsewhere), `|κ| ≤ 𝖣²λ` and `|M| ≤ 𝖣`
  ((5.3), (5.1)); with `h = λ^{-1/2}` it is at most `4C𝖣³λ^{-1/4}`;
* the remaining tensors are bounded as in the text (`:197-204`) through Lemma D.1 (`hD_1`), in sup
  norm by the scaled jets of order one of the two gradient profiles `g₁ = 𝐝𝗉_1` and `g₂ = κ∂_s𝗉_1`
  (`leading_hess_point`; each label derivative costs `ℓ_*⁻¹ = 𝖣^a`, each phase derivative
  `h⁻¹ = λ^{1/2}`; `|D_xY| ≤ 𝖣`, `|k_*| ≤ 𝖣λ`, no second derivative of `Y` is needed): `‖g₁‖_{[1],γ} ≤
  C‖(D_aX)⁻¹‖_{[1]} ℓ_*⁻¹‖𝗉_1‖_{[2],γ}` (`wNorm_labelGrad_le`: (D.4) for the product, (D.3) for
  `∂_{a_j}`) and `‖g₂‖_{[1],γ} ≤ C‖κ‖_{[1]} h⁻¹‖𝗉_1‖_{[2],γ}` (`wNorm_phaseGradScalar_le`: (D.4) for
  `κ∂_s𝗉_1`, (D.3) for `∂_s`), the coefficient norms `‖(D_aX)⁻¹‖_{[1]} ≤ κ₀𝖣^{C₁}`,
  `‖κ‖_{[1]} ≤ κ₀|k_*|𝖣^{C₁}` coming from (D.6) and (5.8) of `h5_1` (`coefNorm`). Their sum is at
  most `C𝖣^Cλ^{3/2}‖𝗉_1‖_{[2],γ}` (`remainder_bound`), and `λ‖𝗉_1‖_{[2],γ} ≤ C𝖣^Cλ^{-5/4}` is the
  `p = 1` case of (5.34) of `h5_6` (Theorem 5.6; the text reads the same bound for
  `𝗉_1 = χ̃𝗉[A₁]` from (5.22) of Lemma 5.3, but the comparison of the twisted profile with the raw
  field of (5.22) is not available in the package). So they are at most `C𝖣^Cλ^{-3/4}`.

For `t < t₀` the profile `𝗉_1` vanishes (`IsExpansion.leadingPressure_mem_inactive`: the cutoff `χ̃` and the
envelope vanish there, `:185-186`; no use of Proposition 5.4). The hypothesis of Theorem 5.6
is `𝖣^{C₆}λ^{-1/12} ≤ 1`, implied by the smallness hypothesis of the claim since `C ≥ C₆`.
Constants: `a₀ = max (max a₀(5.3) a₀(5.6)) 3`, `C = C₆ + 2a + 2C₁ + 3`, `a₀` also at least `C₁` (so `ℓ_* ≤ 𝖣^{-C₁}` for (5.8)),
`K = 4C₃ + 28 c₁ c_c max(K₁,₁,0) |K₆,₂,₁|` (`c₁` = `prodC1`, `c_c` = `coefC`). -/
theorem leadingHessianClaim (h3_1 : Statement.lemma_3_1) (h5_1 : Statement.proposition_5_1)
    (h5_3 : Statement.lemma_5_3)
    (h5_6 : Statement.theorem_5_6) (hD_1 : Statement.lemma_D_1) : LeadingHessianClaim := by
  obtain ⟨C3, hC3, hprof, -⟩ := h3_1
  obtain ⟨C1, K1, h1⟩ := h5_1
  obtain ⟨_Kf, h1⟩ := h1 (fun _ => 0)
  obtain ⟨a3, h3⟩ := h5_3
  obtain ⟨a6, h6⟩ := h5_6
  refine ⟨max (max (max a3 a6) 3) C1, fun a ha => ?_⟩
  simp only [max_le_iff] at ha
  obtain ⟨⟨⟨ha3', ha6⟩, ha3⟩, haC1⟩ := ha
  obtain ⟨C5, K5, h3a⟩ := h3 a ha3'
  obtain ⟨C6, K6, KP6, h6a⟩ := h6 a ha6
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = 2 * a + 2 * C1 + 3 := ⟨_, rfl⟩
  obtain ⟨Kc, hKc_eq⟩ : ∃ Kc : ℝ, Kc = 4 * C3 + 28 * prodC1 * coefC * max (K1 1) 0 * |K6 2 1| := ⟨_, rfl⟩
  refine ⟨C6 + N, Kc, ?_⟩
  intro T hT U X pU k D lam t₀ center d χ hP hL hO hsm amp hamp P hP2 R S u hu t ht x v
  -- standing facts
  have hD : 1 ≤ D := Bridge.Parent.scale_ge_one hP
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hDp : ∀ m : ℕ, 0 ≤ D ^ m := fun m => pow_nonneg hD0 m
  have hlam : 1 ≤ lam := hP.frequency_ge_one
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam
  have hℓ : 0 < S5.radius D a := Bridge.radius_pos hP a
  have hfit : 2 * S5.radius D a < 1 / 2 := Bridge.radius_fits hP.scale_ge_two ha3
  have hh : 0 < S5.width lam := Bridge.width_pos hP
  have hh1 : S5.width lam ≤ 1 := Bridge.width_le_one hP
  have ht0 : 0 ≤ t₀ := hL.start_nonneg
  have htT : t₀ ≤ T := hL.start_lt.le
  have hK61 : 0 ≤ |K6 2 1| := abs_nonneg _
  have hkB : 0 ≤ max (K1 1) 0 := le_max_right _ _
  have hKc : 0 ≤ Kc := by
    rw [hKc_eq]
    exact add_nonneg (mul_nonneg (by norm_num) hC3.le)
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) prodC1_nonneg) coefC_nonneg)
        hkB) hK61)
  have hv2 : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  have hl4 : 0 ≤ lam ^ (-1 / 4 : ℝ) := Real.rpow_nonneg hlam0.le _
  have hRHS : 0 ≤ Kc * D ^ (C6 + N) * lam ^ (-1 / 4 : ℝ) * ‖v‖ ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hKc (hDp _)) hl4) hv2
  let Y : Velocity := fun t => X t 0
  let pnat : Vec3 → ℝ := graphRead Y (u.p 1) t
  change ⟪v, fderiv ℝ (gradient pnat) x v⟫_ℝ ≤ _
  by_cases hact : t₀ ≤ t
  swap
  · -- before `t₀` the leading pressure vanishes
    have hp1 := IsExpansion.leadingPressure_mem_inactive d hu hℓ hfit
    have hz : pnat = 0 := by
      funext y
      exact hp1 (x := (t, Y t y, ⟪k, Y t y⟫_ℝ)) ⟨⟨ht, mem_univ _⟩, Or.inl (lt_of_not_ge hact)⟩
    have hg : gradient (0 : Vec3 → ℝ) = (0 : Vec3 → Vec3) := by
      funext y
      simp [gradient]
    rw [hz, hg, fderiv_zero, Pi.zero_apply, zero_apply, inner_zero_right]
    exact hRHS
  have ht' : t ∈ Icc t₀ T := ⟨hact, ht.2⟩
  -- the profile slice, the readout and its periodicity
  let Q : Vec3 × ℝ → ℝ := fun z => (u.p 1).val.val.val (t, z.1, z.2)
  have hQ : ContDiff ℝ ∞ Q := HierarchySmoothProfile.contDiff_labelPhase_slice (u.p 1).val.val ht
  have hYs : ContDiff ℝ ∞ (Y t) := contDiff_slice (inverseFlow_smooth hT hP) ht
  have hps : ContDiff ℝ ∞ pnat := graphRead_slice_smooth hT hP (u.p 1) ht
  have hgs : ContDiff ℝ ∞ (gradient pnat) :=
    (InnerProductSpace.toDual ℝ Vec3).symm.toContinuousLinearEquiv.contDiff.comp
      (hps.fderiv_right (m := ∞) (by simp))
  have hper : SpatiallyPeriodic pnat :=
    HierarchyTwistedProfile.spatiallyPeriodic_graphRead Y (u.p 1) t
      (fun n y => inverseFlow_lattice hT hP ht n y)
  have hHper := (hper.gradient (hps.differentiable (by simp))).fderiv
    (hgs.differentiable (by simp))
  obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell (Y t x)
  obtain ⟨x', hx'⟩ : ∃ x', x' = x - latticeVector n := ⟨_, rfl⟩
  have hYx' : X t 0 x' = X t 0 x - latticeVector n := by
    have h := inverseFlow_lattice hT hP ht n x'
    rw [hx', sub_add_cancel] at h
    rw [hx', h, add_sub_cancel_right]
  have hcell : X t 0 x' ∈ centeredCell := by
    rw [hYx']
    exact hn
  have hxx : fderiv ℝ (gradient pnat) x = fderiv ℝ (gradient pnat) x' := by
    have h := hHper n x'
    rw [hx', sub_add_cancel] at h
    rw [hx']
    exact h
  rw [hxx]
  -- data at the label `a = Y(x')`
  set ℓ := S5.radius D a with hℓdef
  set h := S5.width lam with hhdef
  obtain ⟨hFs, -, -, -, -, -, hPd, -, hFb⟩ := hprof h hh hh1
  obtain ⟨cb, hcbdef⟩ : ∃ cb : ℝ, cb = wavePressureCoefficient (radialEnvelope ℓ (X t 0 x'))
      (S5.waveVector X k t (X t 0 x')) (amp t (X t 0 x')) (S5.strainField U X t (X t 0 x')) :=
    ⟨_, rfl⟩
  have hline : ∀ s, Q (X t 0 x', s) = (χ.value t * -cb) * wavePressurePrimitive h s := by
    intro s
    change (u.p 1).val.val.val (t, X t 0 x', s) = _
    rw [hu.leading_pressure t ht (X t 0 x') hcell s, hcbdef]
    simp only [S5.leadingPressure]
    ring
  -- the weighted norms through Lemma D.1 (`hD_1`)
  obtain ⟨Bγ, hBγ⟩ := Bridge.Origin.exists_inverse_weight_bound hP hL hO
  have hγc := Bridge.Origin.weight_continuousOn (lam := lam) hO
  have hγp := Bridge.Origin.weight_pos hP hO
  have hγ1 := Bridge.Origin.weight_le_one hO
  obtain ⟨W, hWdef⟩ : ∃ W, W = S5.wNorm ℓ h t₀ (S5.weight lam center) 2 (u.p 1) := ⟨_, rfl⟩
  have hDC6 : D ^ C6 ≤ D ^ (C6 + N) := pow_le_pow_right₀ hD (by omega)
  have hsm6 : D ^ C6 * lam ^ (-1 / 12 : ℝ) ≤ 1 :=
    (mul_le_mul_of_nonneg_right hDC6 (Real.rpow_nonneg hlam0.le _)).trans hsm
  have h6c := h6a hT d χ hP hL hO hsm6 amp hamp P hP2 R S u hu
  dsimp only at h6c
  have h534 := h6c.1 2
  -- the coefficients `(D_aX)⁻¹` and `κ = (D_aX)⁻ᵀ k_*` from (D.6), (5.8) of Proposition 5.1
  have hst : Icc t₀ T ⊆ Icc 0 T := Bridge.Launch.active_subset hL
  have hℓle : ℓ ≤ (D ^ C1)⁻¹ :=
    inv_anti₀ (pow_pos (zero_lt_one.trans_le hD) _) (pow_le_pow_right₀ hD haC1)
  obtain ⟨hD6, -, h58⟩ := h1 hT hP hL
  have h58' := fun n s hs => h58 ℓ hℓ hℓle n s hs
  have hιt : ∀ s : Icc t₀ T, s.1 ∈ Icc 0 T := fun s => hst s.2
  have hB1 : 0 ≤ max (K1 1) 0 * D ^ C1 := mul_nonneg (le_max_right _ _) (hDp _)
  have hGs : ∀ r ∈ Icc 0 T, ContDiff ℝ ∞ (fun b => fderiv ℝ (X r 0) (X 0 r b)) := fun r hr =>
    slice_smooth_c (f := fun r b => fderiv ℝ (X r 0) (X 0 r b))
      (hP.flow.contDiffOn_inverseLabelDerivative hT hP.velocity_smooth hP.velocity_periodic) hr
  have hG8 : ∀ r ∈ Icc 0 T, (∑ j ∈ Finset.range (1 + 1),
      ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (fun b => fderiv ℝ (X r 0) (X 0 r b)))) ≤
        max (K1 1) 0 * D ^ C1 := fun r hr =>
    (h58' 1 r hr).2.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hDp _))
  have hGc := coefNorm (T := T) (Subtype.val : Icc t₀ T → ℝ) hιt
    (ContinuousLinearMap.id ℝ (Vec3 →L[ℝ] Vec3)) (c := fun r b => fderiv ℝ (X r 0) (X 0 r b))
    (ℓ := ℓ) (h := h) hℓ 1 (b := fun m => K1 m * D ^ (C1 * (m + 1))) hB1 hGs
    (fun m r hr b => (hD6 m r hr b).2.1) hG8
  let Lκ : (Vec3 →L[ℝ] Vec3) →L[ℝ] Vec3 := (ContinuousLinearMap.apply ℝ Vec3 k).comp adjL
  have hLκ : ‖Lκ‖ ≤ ‖k‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg k) fun A => ?_
    change ‖A.adjoint k‖ ≤ ‖k‖ * ‖A‖
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [ContinuousLinearMap.adjoint.norm_map, mul_comm]
  have hKcn := coefNorm (T := T) (Subtype.val : Icc t₀ T → ℝ) hιt Lκ
    (c := fun r b => fderiv ℝ (X r 0) (X 0 r b))
    (ℓ := ℓ) (h := h) hℓ 1 (b := fun m => K1 m * D ^ (C1 * (m + 1))) hB1 hGs
    (fun m r hr b => (hD6 m r hr b).2.1) hG8
  have hkD : ‖k‖ ≤ D * lam := norm_carrier_le hP hL
  let Bc : ℝ := coefC * (max (K1 1) 0 * D ^ C1)
  let BK : ℝ := coefC * (D * lam * (max (K1 1) 0 * D ^ C1))
  have hid : ‖ContinuousLinearMap.id ℝ (Vec3 →L[ℝ] Vec3)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hGn : fieldNorm ℓ h 1 (fun (t : Icc t₀ T) (x : Vec3 × ℝ) => fderiv ℝ (X t.1 0) (X 0 t.1 x.1)) ≤
      Bc := hGc.2.trans (by
    calc _ ≤ coefC * (1 * (max (K1 1) 0 * D ^ C1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hid hB1) coefC_nonneg
      _ = Bc := by simp only [Bc, one_mul])
  have hKn : fieldNorm ℓ h 1 (fun (t : Icc t₀ T) (x : Vec3 × ℝ) => S5.waveVector X k t.1 x.1) ≤
      BK := hKcn.2.trans (by
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hLκ.trans hkD) hB1) coefC_nonneg)
  have hw1 := wNorm_labelGrad_le hD_1 d hℓ hh ht0 htT hγc hγp hGc.1 hGn (u.p 1)
  have hw2 := wNorm_phaseGradScalar_le hD_1 d hℓ hh ht0 htT hγc hγp hKcn.1 hKn (u.p 1)
  have hJ₁ := scaledJets_of_wNorm hT ht0 htT hγc hγp hγ1 hBγ ℓ h 1 ((S5.ops d).labelGrad (u.p 1)) ht'
  have hJ₂ := scaledJets_of_wNorm hT ht0 htT hγc hγp hγ1 hBγ ℓ h 1 ((S5.ops d).phaseGrad (u.p 1)) ht'
  -- the Hessian (5.51) at `x'`
  have hgr : gradient pnat = fun y =>
      ((S5.ops d).labelGrad (u.p 1)).val.val.val (t, X t 0 y, ⟪k, X t 0 y⟫_ℝ) +
        ((S5.ops d).phaseGrad (u.p 1)).val.val.val (t, X t 0 y, ⟪k, X t 0 y⟫_ℝ) :=
    gradient_graphRead_eq d hP (u.p 1) ht
  have hs₂ := phaseGrad_phase_deriv d ht (X t 0 x') ⟪k, X t 0 x'⟫_ℝ
    (q := u.p 1) (c := χ.value t * -cb) hline hPd (hFs.differentiable (by simp))
  have hpt := leading_hess_point
    (G₁ := fun z : Vec3 × ℝ => ((S5.ops d).labelGrad (u.p 1)).val.val.val (t, z.1, z.2))
    (G₂ := fun z : Vec3 × ℝ => ((S5.ops d).phaseGrad (u.p 1)).val.val.val (t, z.1, z.2))
    (HierarchySmoothProfile.contDiff_labelPhase_slice ((S5.ops d).labelGrad (u.p 1)).val.val ht)
    (HierarchySmoothProfile.contDiff_labelPhase_slice ((S5.ops d).phaseGrad (u.p 1)).val.val ht)
    hYs k x' v (S5.waveVector X k t (X t 0 x')) hℓ hh hJ₁ hJ₂
    (fun w => inner_carrier_fderiv_inverseFlow hT hP ht x' w) hs₂
    (norm_fderiv_inverseFlow_le hT hP ht x') hkD
  rw [hgr]
  have hpt' : ⟪v, fderiv ℝ (fun y => ((S5.ops d).labelGrad (u.p 1)).val.val.val
        (t, X t 0 y, ⟪k, X t 0 y⟫_ℝ) + ((S5.ops d).phaseGrad (u.p 1)).val.val.val
        (t, X t 0 y, ⟪k, X t 0 y⟫_ℝ)) x' v⟫_ℝ ≤
      χ.value t * -cb * deriv (waveProfile h) ⟪k, X t 0 x'⟫_ℝ *
          ⟪S5.waveVector X k t (X t 0 x'), v⟫_ℝ ^ 2 +
        4 ^ 1 * S5.wNorm ℓ h t₀ (S5.weight lam center) 1 ((S5.ops d).labelGrad (u.p 1)) * ‖v‖ ^ 2 *
          (D / ℓ + D * lam * D / h) +
        4 ^ 1 * S5.wNorm ℓ h t₀ (S5.weight lam center) 1 ((S5.ops d).phaseGrad (u.p 1)) * ‖v‖ ^ 2 *
          (D / ℓ) := hpt
  refine hpt'.trans ?_
  -- the powers of `λ` through `r = λ^{1/4}`
  obtain ⟨r, hr⟩ : ∃ r, r = lam ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := hr ▸ Real.one_le_rpow hlam (by norm_num)
  have hr0 : 0 < r := zero_lt_one.trans_le hr1
  have hrne : r ≠ 0 := hr0.ne'
  have hrp : ∀ m : ℕ, 0 < r ^ m := fun m => pow_pos hr0 m
  have hlr : lam = r ^ 4 := by
    have h4 := quarter_pow hlam0.le 4
    rw [← hr] at h4
    rw [← h4]
    norm_num
  have hhr : h = (r ^ 2)⁻¹ := by
    rw [hhdef, S5.width, show (-1 / 2 : ℝ) = -((2 : ℕ) : ℝ) / 4 by norm_num,
      quarter_pow_neg hlam0.le, ← hr]
  have hq4 : lam ^ (-1 / 4 : ℝ) = r⁻¹ := by
    rw [show (-1 / 4 : ℝ) = -((1 : ℕ) : ℝ) / 4 by norm_num, quarter_pow_neg hlam0.le, pow_one, ← hr]
  have hq54 : lam ^ (-5 / 4 : ℝ) = (r ^ 5)⁻¹ := by
    rw [show (-5 / 4 : ℝ) = -((5 : ℕ) : ℝ) / 4 by norm_num, quarter_pow_neg hlam0.le, ← hr]
  have hq34 : lam ^ (3 / 4 : ℝ) = r ^ 3 := by
    rw [show (3 / 4 : ℝ) = ((3 : ℕ) : ℝ) / 4 by norm_num, quarter_pow hlam0.le, ← hr]
  have hℓinv : ∀ y : ℝ, y / ℓ = y * D ^ a := fun y => by
    rw [hℓdef, S5.radius, div_inv_eq_mul]
  have hhinv : ∀ y : ℝ, y / h = y * r ^ 2 := fun y => by rw [hhr, div_inv_eq_mul]
  have hh0 : 0 ≤ h := hh.le
  -- the first tensor of (5.51)
  have hlead : χ.value t * -cb * deriv (waveProfile h) ⟪k, X t 0 x'⟫_ℝ *
      ⟪S5.waveVector X k t (X t 0 x'), v⟫_ℝ ^ 2 ≤ 4 * C3 * D ^ 3 * r⁻¹ * ‖v‖ ^ 2 := by
    have hχ := χ.range t ht
    have hC3r : 0 ≤ 4 * C3 * D ^ 3 * r⁻¹ * ‖v‖ ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC3.le) (hDp _))
        (inv_nonneg.mpr hr0.le)) hv2
    by_cases hnear : ‖X t 0 x'‖ ≤ 2 * ℓ
    · have h3c := h3a hT d hP hL hO
      dsimp only at h3c
      have h519 := h3c.1 amp hamp t ht' (X t 0 x') hnear
      have hκ0 : S5.waveVector X k t (X t 0 x') ≠ 0 :=
        Bridge.Parent.waveVector_ne_zero hT hP hL.carrier_ne_zero ht _
      obtain ⟨hcb0, hcbκ⟩ := wavePressureCoefficient_mul_norm_sq_le hκ0
        (radialEnvelope_mem_Icc ℓ (X t 0 x')) h519.2.le
      rw [← hcbdef] at hcb0 hcbκ
      have hneg : -deriv (waveProfile h) ⟪k, X t 0 x'⟫_ℝ ≤ C3 * h := by
        linarith [(hFb ⟪k, X t 0 x'⟫_ℝ).1]
      have hσ2 : ⟪S5.waveVector X k t (X t 0 x'), v⟫_ℝ ^ 2 ≤
          ‖S5.waveVector X k t (X t 0 x')‖ ^ 2 * ‖v‖ ^ 2 := by
        rw [← mul_pow, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
      have hcpos : 0 < ‖center t‖ := norm_pos_iff.mpr (hO.wave.nonzero t ht').2.1
      have hc' : ‖center t‖ ≤ (r ^ 3)⁻¹ := by
        have hc := hO.normalized t ht'
        rw [hq34] at hc
        calc ‖center t‖ = (r ^ 3)⁻¹ * (r ^ 3 * ‖center t‖) := by
              rw [← mul_assoc, inv_mul_cancel₀ (hrp 3).ne', one_mul]
          _ ≤ (r ^ 3)⁻¹ * 1 := mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr (hrp 3).le)
          _ = (r ^ 3)⁻¹ := mul_one _
      have hamp_le : ‖amp t (X t 0 x')‖ ≤ 2 * (r ^ 3)⁻¹ := by
        calc ‖amp t (X t 0 x')‖ ≤ 2 * ‖amp t 0‖ := h519.1
          _ = 2 * ‖center t‖ := by rw [hamp.at_origin t ht']
          _ ≤ 2 * (r ^ 3)⁻¹ := by linarith
      have hκa : ‖S5.waveVector X k t (X t 0 x')‖ ≤ D ^ 2 * lam := norm_waveVector_le hP hL ht _
      have hMa : ‖S5.strainField U X t (X t 0 x')‖ ≤ D := hP.gradient_le t ht (X 0 t (X t 0 x'))
      have hcbσ : 0 ≤ cb * ⟪S5.waveVector X k t (X t 0 x'), v⟫_ℝ ^ 2 :=
        mul_nonneg hcb0 (sq_nonneg _)
      have hCh : 0 ≤ C3 * h := mul_nonneg hC3.le hh0
      calc χ.value t * -cb * deriv (waveProfile h) ⟪k, X t 0 x'⟫_ℝ *
            ⟪S5.waveVector X k t (X t 0 x'), v⟫_ℝ ^ 2
          = (χ.value t * (cb * ⟪S5.waveVector X k t (X t 0 x'), v⟫_ℝ ^ 2)) *
              -deriv (waveProfile h) ⟪k, X t 0 x'⟫_ℝ := by ring
        _ ≤ (χ.value t * (cb * ⟪S5.waveVector X k t (X t 0 x'), v⟫_ℝ ^ 2)) * (C3 * h) :=
            mul_le_mul_of_nonneg_left hneg (mul_nonneg hχ.1 hcbσ)
        _ ≤ (1 * (cb * ⟪S5.waveVector X k t (X t 0 x'), v⟫_ℝ ^ 2)) * (C3 * h) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hχ.2 hcbσ) hCh
        _ ≤ (cb * (‖S5.waveVector X k t (X t 0 x')‖ ^ 2 * ‖v‖ ^ 2)) * (C3 * h) := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hσ2 hcb0) hCh
        _ = (cb * ‖S5.waveVector X k t (X t 0 x')‖ ^ 2) * ‖v‖ ^ 2 * (C3 * h) := by ring
        _ ≤ (2 * ‖S5.waveVector X k t (X t 0 x')‖ * ‖S5.strainField U X t (X t 0 x')‖ *
              ‖amp t (X t 0 x')‖) * ‖v‖ ^ 2 * (C3 * h) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcbκ hv2) hCh
        _ ≤ (2 * (D ^ 2 * lam) * D * (2 * (r ^ 3)⁻¹)) * ‖v‖ ^ 2 * (C3 * h) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hv2) hCh
            exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hκa (by norm_num)) hMa
              (norm_nonneg _) (mul_nonneg (by norm_num) (mul_nonneg (hDp 2) hlam0.le)))
              hamp_le (norm_nonneg _)
              (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (hDp 2) hlam0.le)) hD0)
        _ = 4 * C3 * D ^ 3 * r⁻¹ * ‖v‖ ^ 2 := by
            rw [hlr, hhr]
            field_simp
            ring
    · have hz : radialEnvelope ℓ (X t 0 x') = 0 :=
        radialEnvelope_eq_zero hℓ (le_of_not_ge hnear)
      have hcb : cb = 0 := by
        rw [hcbdef]
        simp only [wavePressureCoefficient, hz, mul_zero, zero_mul, zero_div]
      rw [hcb]
      simpa using hC3r
  -- the remaining tensors
  have hV0 : 0 ≤ S5.wNorm ℓ h t₀ (S5.weight lam center) 2 (u.V 1) :=
    Bridge.wNorm_nonneg _ _ 2 hT ht0 _ hBγ _
  have hW : W ≤ |K6 2 1| * D ^ C6 * (r ^ 9)⁻¹ := by
    have h1' : lam * W ≤ K6 2 1 * D ^ C6 * lam ^ (-5 / 4 : ℝ) := by
      have := h534
      rw [← hWdef] at this
      linarith
    rw [hq54, hlr] at h1'
    have h2 : r ^ 4 * W ≤ |K6 2 1| * D ^ C6 * (r ^ 5)⁻¹ :=
      h1'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
        (hDp _)) (inv_nonneg.mpr (hrp 5).le))
    have h3 : W = (r ^ 4)⁻¹ * (r ^ 4 * W) := by
      rw [← mul_assoc, inv_mul_cancel₀ (hrp 4).ne', one_mul]
    have h9 : (r ^ 9)⁻¹ = (r ^ 4)⁻¹ * (r ^ 5)⁻¹ := by
      rw [← mul_inv, ← pow_add]
    rw [h3]
    calc (r ^ 4)⁻¹ * (r ^ 4 * W) ≤ (r ^ 4)⁻¹ * (|K6 2 1| * D ^ C6 * (r ^ 5)⁻¹) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr (hrp 4).le)
      _ = |K6 2 1| * D ^ C6 * (r ^ 9)⁻¹ := by rw [h9]; ring
  have hW0 : 0 ≤ W := by rw [hWdef]; exact Bridge.wNorm_nonneg _ _ 2 hT ht0 _ hBγ _
  have hv2' : 0 ≤ ‖v‖ ^ 2 := hv2
  have hk0 : 0 ≤ max (K1 1) 0 := le_max_right _ _
  have hDl : 0 ≤ D / ℓ := div_nonneg hD0 hℓ.le
  have hDlh : 0 ≤ D * lam * D / h := div_nonneg (mul_nonneg (mul_nonneg hD0 hlam0.le) hD0) hh0
  have hw1' : S5.wNorm ℓ h t₀ (S5.weight lam center) 1 ((S5.ops d).labelGrad (u.p 1)) ≤
      prodC1 * Bc * (3 * ℓ⁻¹ * W) := by rw [hWdef]; exact hw1
  have hw2' : S5.wNorm ℓ h t₀ (S5.weight lam center) 1 ((S5.ops d).phaseGrad (u.p 1)) ≤
      prodC1 * BK * (h⁻¹ * W) := by rw [hWdef]; exact hw2
  have hrem0 : 4 ^ 1 * S5.wNorm ℓ h t₀ (S5.weight lam center) 1 ((S5.ops d).labelGrad (u.p 1)) *
        ‖v‖ ^ 2 * (D / ℓ + D * lam * D / h) +
      4 ^ 1 * S5.wNorm ℓ h t₀ (S5.weight lam center) 1 ((S5.ops d).phaseGrad (u.p 1)) *
        ‖v‖ ^ 2 * (D / ℓ) ≤
      4 ^ 1 * (prodC1 * Bc * (3 * ℓ⁻¹ * W)) * ‖v‖ ^ 2 * (D / ℓ + D * lam * D / h) +
      4 ^ 1 * (prodC1 * BK * (h⁻¹ * W)) * ‖v‖ ^ 2 * (D / ℓ) := by
    refine add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hw1' (by norm_num)) hv2') (add_nonneg hDl hDlh))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hw2' (by norm_num)) hv2') hDl)
  have hrem : 4 ^ 1 * S5.wNorm ℓ h t₀ (S5.weight lam center) 1 ((S5.ops d).labelGrad (u.p 1)) *
        ‖v‖ ^ 2 * (D / ℓ + D * lam * D / h) +
      4 ^ 1 * S5.wNorm ℓ h t₀ (S5.weight lam center) 1 ((S5.ops d).phaseGrad (u.p 1)) *
        ‖v‖ ^ 2 * (D / ℓ) ≤
      28 * prodC1 * coefC * max (K1 1) 0 * D ^ (C6 + N) * r⁻¹ * ‖v‖ ^ 2 * |K6 2 1| := by
    refine hrem0.trans ?_
    have hℓi : ℓ⁻¹ = D ^ a := by rw [hℓdef, S5.radius, inv_inv]
    have hhi : h⁻¹ = r ^ 2 := by rw [hhr, inv_inv]
    have hb := remainder_bound a C1 N hD hr1 hW0 hv2 prodC1_nonneg coefC_nonneg hk0 (by omega)
    have hW6 : r ^ 6 * W ≤ |K6 2 1| * D ^ C6 * r⁻¹ := by
      refine (mul_le_mul_of_nonneg_left hW (hrp 6).le).trans ?_
      have h96 : r ^ 6 * (r ^ 9)⁻¹ = (r ^ 3)⁻¹ := by
        rw [show r ^ 9 = r ^ 3 * r ^ 6 by ring, mul_inv, ← mul_assoc, mul_comm (r ^ 6) _,
          mul_assoc, mul_inv_cancel₀ (hrp 6).ne', mul_one]
      calc r ^ 6 * (|K6 2 1| * D ^ C6 * (r ^ 9)⁻¹) = |K6 2 1| * D ^ C6 * (r ^ 3)⁻¹ := by
            rw [← h96]; ring
        _ ≤ |K6 2 1| * D ^ C6 * r⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ hr0 (le_self_pow₀ hr1 (by norm_num)))
              (mul_nonneg hK61 (hDp _))
    rw [hℓi, hhi, hℓinv D, hhinv (D * lam * D), hlr]
    simp only [Bc, BK, hlr]
    refine (le_of_eq (by ring)).trans (hb.trans ?_)
    have hpre : 0 ≤ 28 * prodC1 * coefC * max (K1 1) 0 * D ^ N * ‖v‖ ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) prodC1_nonneg)
        coefC_nonneg) hk0) (hDp _)) hv2'
    calc _ ≤ (28 * prodC1 * coefC * max (K1 1) 0 * D ^ N * ‖v‖ ^ 2) *
          (|K6 2 1| * D ^ C6 * r⁻¹) := by
          have := mul_le_mul_of_nonneg_left hW6 hpre
          linarith
      _ = _ := by rw [pow_add]; ring
  rw [hq4]
  have hD3 : D ^ 3 ≤ D ^ (C6 + N) := pow_le_pow_right₀ hD (by omega)
  have hlead' : 4 * C3 * D ^ 3 * r⁻¹ * ‖v‖ ^ 2 ≤ 4 * C3 * D ^ (C6 + N) * r⁻¹ * ‖v‖ ^ 2 := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hr0.le)) hv2
    exact mul_le_mul_of_nonneg_left hD3 (mul_nonneg (by norm_num) hC3.le)
  have hsum : 4 * C3 * D ^ (C6 + N) * r⁻¹ * ‖v‖ ^ 2 +
      28 * prodC1 * coefC * max (K1 1) 0 * D ^ (C6 + N) * r⁻¹ * ‖v‖ ^ 2 * |K6 2 1| =
      Kc * D ^ (C6 + N) * r⁻¹ * ‖v‖ ^ 2 := by
    rw [hKc_eq]
    ring
  linarith [hlead, hrem, hlead', hsum]

end

end TorusEuler.Paper.Lib.S5c
