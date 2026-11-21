import TorusEuler.Paper.S5.Statements
import TorusEuler.Paper.Proofs.S5Bridge.Parent
import TorusEuler.Paper.Proofs.S5c.Library.FlowJets

/-!
# Proof of Lemma 5.10 (package S5c)

Conditional proof `Paper.Proof.lemma_5_10_of` of the flow bounds (5.53)
(`cc:uf:step:lem:flow-bounds`, `sections/08_exact_wave.tex:290-364`) from Proposition 5.1,
Proposition 5.4 and Theorem 5.6.

**Ledger.** The ledger (decision D9) lists 5.1, 5.6, 5.4 as cites of 5.10 (hypotheses in this
order). The proof uses from Proposition 5.4 the conclusions `𝐝̃·W = 0`, `W_osc = ∑_{p}(V_p + C_{p+1})` and the vanishing of `V_p`, `C_p` before
`t₀` of Proposition 5.4 (`08_exact_wave.tex:300-302`: "so `𝐝̃·(W + v∘X) = 0`"; the unweighted
bounds of `c_osc` on all of `[0,T]`, `:310-316`); they enter through the hypothesis `h5_4`.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

open HierarchyTwistedProfile ChildFlow

noncomputable section

namespace Lib.S5c

/-- The oscillatory part of the pulled-back field `c = (D_aX)^{-1}(W + v∘X)` is
`(D_aX)^{-1}(W - ⟨W⟩)`: the perturbation `v∘X` and the coefficient are independent of the
phase (`phaseOscillation_pullbackField_eq_uncut`), and the phase mean of the profile is the
average `⟨W⟩` of the operators of the parent. -/
theorem phaseOscillation_pullback_eq {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity}
    {k : Vec3} (d : ParentGeometry hT U X k) (W : HierarchyTwistedProfile T k Vec3)
    (v : Velocity) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) (s : ℝ) :
    phaseOscillation (fun r => pullbackField X (fun t a s => W.val.val.val (t, a, s)) v t (x, r)) s =
      fderiv ℝ (X t 0) (X 0 t x) ((W - (S5.ops d).average W).val.val.val (t, x, s)) := by
  have hc : Continuous (fun r => W.val.val.val (t, x, r)) := by
    have hsm := HierarchySmoothProfile.smooth W.val.val
    exact (contDiffOn_univ.mp (hsm.comp (contDiff_const.prodMk
      (contDiff_const.prodMk contDiff_id)).contDiffOn (fun r _ => ⟨ht, mem_univ _⟩))).continuous
  rw [phaseOscillation_pullbackField_eq_uncut hc]
  have hz : (t, x, s) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have havg := Bridge.ops_average_eval d W hz
  let G := fderiv ℝ (X t 0) (X 0 t x)
  show phaseOscillation (fun r => G (W.val.val.val (t, x, r) + (0 : Velocity) t (X 0 t x))) s =
    G (W.val.val.val (t, x, s) - ((S5.ops d).average W).val.val.val (t, x, s))
  simp only [Pi.zero_apply, add_zero]
  rw [havg, map_sub]
  simp only [phaseOscillation, phaseMean]
  rw [G.intervalIntegral_comp_comm (hc.intervalIntegrable 0 1)]

/-- The phase mean of a profile is its average `⟨W⟩`. -/
theorem phaseMean_eq_average {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity}
    {k : Vec3} (d : ParentGeometry hT U X k) (W : HierarchyTwistedProfile T k Vec3)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) (s : ℝ) :
    phaseMean (fun r => W.val.val.val (t, x, r)) = ((S5.ops d).average W).val.val.val (t, x, s) :=
  (Bridge.ops_average_eval d W (p := (t, x, s)) ⟨ht, mem_univ _⟩).symm

/-- Evaluation of a finite sum of twisted profiles. -/
theorem profile_sum_eval {T : ℝ} {k : Vec3} {ι : Type*} (s : Finset ι)
    (f : ι → HierarchyTwistedProfile T k Vec3) (z : ℝ × Vec3 × ℝ) :
    (∑ i ∈ s, f i).val.val.val z = ∑ i ∈ s, (f i).val.val.val z := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
    rfl

/-- A slice of a twisted profile is smooth in label and phase. -/
theorem profile_slice_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ}
    {k : Vec3} (f : HierarchyTwistedProfile T k E) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContDiff ℝ ∞ (Function.uncurry fun (a : Vec3) (s : ℝ) => f.val.val.val (t, a, s)) :=
  contDiffOn_univ.mp ((HierarchySmoothProfile.smooth f.val.val).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨ht, mem_univ _⟩))

end Lib.S5c

open Lib.S5c

set_option maxHeartbeats 1600000 in
/-- Proof of **Lemma 5.10** (`cc:uf:step:lem:flow-bounds`), following
`sections/08_exact_wave.tex:298-364`. The flow is produced by the library flow estimate
`ChildFlow.exists_childFlow_of_profile_jet_bounds` (the body of the TeX proof: the particle
system (5.54), the Piola identity, Gronwall, and `D𝒜_t^{±1}`; content of this row) for the
profile `W` of the expansion and the pulled-back field `c = (D_aX)^{-1}(W + v∘X)`. Its
inputs come from the cited results:

* `h5_4` (Proposition 5.4) for the expansion `u`: `𝐝̃·W = 0`, which with `div v = 0` gives the
  divergence identity of `W + v∘X` (`:300-302`), read along the flow by
  `Lib.S5c.profileDivergence_pointwise`; the identity `W - ⟨W⟩ = ∑_{p≤P}(V_p + C_{p+1})`, hence
  `⟨W⟩ = ∑_{p=2}^P B_p`; and the vanishing of `V_p`, `C_p` for `t < t₀`, so that `c_osc = 0`
  before activation.
* `h5_6` (Theorem 5.6), whose hypothesis `𝖣^C λ^{-1/12} ≤ 1` follows from (5.43) since
  `b ≥ C` and `Γ_P ≥ 1`: (5.37) at orders `≤ 2` bounds `‖W_osc‖_{[2],γ}` and
  `‖∑_{p≥2}B_p‖_{[1]}`; with `γ ≤ 1` they bound the scaled jets of `W_osc` on `[t₀,T]` and of
  `⟨W⟩` on `[0,T]` (`Lib.S5c.scaledJets_of_wNorm`, `scaledJets_of_uNorm`) — the bounds
  `‖c_osc‖_{[2]} ≤ C_{2,P}𝖣^Cλ^{-5/4}`, `‖c̄‖_{[2]} ≤ C_{2,P}𝖣^Cλ^{-5/2}` of `:310-316`.
* `h5_1` (Proposition 5.1, the coefficient bounds (D.6), of which (5.8) is the scaled sum) for
  the jets of `(D_aX)^{-1}` through order two, which multiply those of `W_osc` and `⟨W⟩`
  (Leibniz, `Lib.S5c.scaledJets_apply`), and for the first jet of `(D_aX)^{-1}` in the bound of
  the perturbation `(D_aX)^{-1} v∘X` (`ChildFlow.scaledPerturbation_phaseJetBound_one`, with
  `|D_aX| ≤ 𝖣` of (5.1)).

The standing bounds `|D_aX^{±1}| ≤ 𝖣` (5.1) and `|k_*| ≤ 𝖣λ` (from (5.3) and
`k_* = (D_aX)^T κ(t₀,0)`) enter the flow estimate; every label flow of `V + v` on `[0,T]` is the
flow it produces (`Lib.S5c.labelFlow_eq`, uniqueness for the Lipschitz field `V + v`).

Constants: `p = 3C₁ + C₆ + 2` (`C₁`, `C₆` the exponents of 5.1 and 5.6),
`B_P = 64 K (|K_{2,P}| + |K_{1,P}|) + 1 + K` with `K = |K₀| + |K₁| + |K₂|` the constants of (D.6),
`b₀ = max C₆ (max a 1 + (max a 1 + p) + 1)`, `Γ₀ P = 1 + 40 B_P`. -/
theorem Proof.lemma_5_10_of (h5_1 : Statement.proposition_5_1) (h5_6 : Statement.theorem_5_6)
    (h5_4 : Statement.proposition_5_4) : Statement.lemma_5_10 := by
  obtain ⟨C1, K1, h51⟩ := h5_1
  obtain ⟨_Kf, h51'⟩ := h51 (fun _ => 0)
  obtain ⟨a4, h54⟩ := h5_4
  obtain ⟨a6, h56⟩ := h5_6
  refine ⟨max a4 a6, fun a ha => ?_⟩
  obtain ⟨C6, _K6, KP6, h56a⟩ := h56 a (le_of_max_le_right ha)
  let KG : ℝ := |K1 0| + |K1 1| + |K1 2|
  have hKG : 0 ≤ KG := by positivity
  let p : ℕ := 3 * C1 + C6 + 2
  let Bc : ℕ → ℝ := fun P => 64 * KG * (|KP6 2 P| + |KP6 1 P|) + 1 + KG
  have hBc (P : ℕ) : 0 ≤ Bc P := by positivity
  refine ⟨max C6 (max a 1 + (max a 1 + p) + 1), fun P => 1 + 40 * Bc P, ?_⟩
  intro b hb Γ hΓ T hT U X pU k D lam t₀ center d χ hP hL hO amp hamp P hP2 R S u hu hsmall
    V Cflow v hv hvper hvdiv hvjet
  -- standing quantities
  have hD2 : 2 ≤ D := hP.scale_ge_two
  have hD1 : 1 ≤ D := one_le_two.trans hD2
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hlam1 : 1 ≤ lam := hP.frequency_ge_one
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam1
  have hΓ1 : 1 ≤ Γ P := (le_add_of_nonneg_right (by positivity)).trans (hΓ P)
  have hbC6 : C6 ≤ b := (le_max_left _ _).trans hb
  have hbp : max a 1 + (max a 1 + p) + 1 ≤ b := (le_max_right _ _).trans hb
  let ell := S5.radius D a
  let h := S5.width lam
  let γ := S5.weight lam center
  have hell0 : 0 < ell := inv_pos.mpr (pow_pos (zero_lt_one.trans_le hD1) a)
  have hell1 : |ell| ≤ 1 := by
    rw [abs_of_pos hell0]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hD1)
  have hellSize : ell⁻¹ ≤ D ^ a := by
    change ((D ^ a)⁻¹)⁻¹ ≤ D ^ a
    rw [inv_inv]
  -- Theorem 5.6 for the expansion
  have h56hyp : D ^ C6 * lam ^ (-1 / 12 : ℝ) ≤ 1 := by
    refine le_trans ?_ hsmall
    have hpow : D ^ C6 ≤ D ^ b := pow_le_pow_right₀ hD1 hbC6
    have hl : 0 ≤ lam ^ (-1 / 12 : ℝ) := Real.rpow_nonneg hlam0.le _
    calc D ^ C6 * lam ^ (-1 / 12 : ℝ) ≤ 1 * D ^ b * lam ^ (-1 / 12 : ℝ) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_right hpow hl
      _ ≤ Γ P * D ^ b * lam ^ (-1 / 12 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hl
          exact mul_le_mul_of_nonneg_right hΓ1 (pow_nonneg hD0 _)
  obtain ⟨-, -, -, -, h537, -⟩ := h56a hT d χ hP hL hO h56hyp amp hamp P hP2 R S u hu
  -- Proposition 5.4 for the expansion
  obtain ⟨-, hdivW, -, hoscW, -, -, hbefore, -⟩ :=
    (h54 a (le_of_max_le_left ha) hT d χ hP hL hO).2 amp hamp P hP2 |>.2.2 R S u hu
  -- the profile `W`, the coefficient `(D_aX)^{-1}` and the parent flow
  let Wf : ℝ → Vec3 → ℝ → Vec3 := fun t a s => (S5.expansion u P).val.val.val (t, a, s)
  let Gf : ℝ → Vec3 → Vec3 →L[ℝ] Vec3 := fun t a => fderiv ℝ (X t 0) (X 0 t a)
  let Bsum := ∑ q ∈ Finset.Icc 2 P, u.B q
  have hX := hP.flow
  have hU := hP.velocity_smooth
  have hUper := hP.velocity_periodic
  have hForward := hX.contDiffOn_forwardLabelFlow hT hU hUper
  have hInvFlow := hX.contDiffOn_inverseLabelFlow hT hU hUper
  have hInvDer := hX.contDiffOn_inverseLabelDerivative hT hU hUper
  obtain ⟨Klip, hKlip⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hUper
  have h0T : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hXinv (t : ℝ) (ht : t ∈ Icc 0 T) := hX.inverse hKlip h0T ht
  have hAs (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (X 0 t) :=
    contDiffOn_univ.mp ((hForward.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ => ⟨ht, mem_univ _⟩)))
  have hGs (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (Gf t) :=
    contDiffOn_univ.mp ((hInvDer.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ => ⟨ht, mem_univ _⟩)))
  have hvs (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (v t) :=
    contDiffOn_univ.mp ((hv.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ => ⟨ht, mem_univ _⟩)))
  -- (D.6) of Proposition 5.1 for `(D_aX)^{-1}` through order two
  obtain ⟨hD6, -, -⟩ := h51' hT hP hL
  have hGj (t : ℝ) (ht : t ∈ Icc 0 T) : ∀ j ≤ 2, ∀ x,
      ‖iteratedFDeriv ℝ j (Gf t) x‖ ≤ KG * D ^ (3 * C1) := by
    intro j hj x
    have h6 := (hD6 j t ht x).2.1
    have hK : K1 j ≤ KG := by
      have h0 := abs_nonneg (K1 0)
      have h1 := abs_nonneg (K1 1)
      have h2 := abs_nonneg (K1 2)
      interval_cases j
      · linarith [le_abs_self (K1 0)]
      · linarith [le_abs_self (K1 1)]
      · linarith [le_abs_self (K1 2)]
    have hpow : D ^ (C1 * (j + 1)) ≤ D ^ (3 * C1) := pow_le_pow_right₀ hD1 (by
      rw [mul_comm 3 C1]; exact Nat.mul_le_mul_left C1 (by omega))
    refine h6.trans ?_
    exact mul_le_mul hK hpow (pow_nonneg hD0 _) hKG
  -- Theorem 5.6 for the expansion: (5.37) at orders one and two
  obtain ⟨Bw, hBw⟩ := Bridge.Origin.exists_inverse_weight_bound hP hL hO
  have hw2 : S5.wNorm ell h t₀ γ 2 (S5.expansion u P - (S5.ops d).average (S5.expansion u P)) ≤
      |KP6 2 P| * D ^ C6 * lam ^ (-5 / 4 : ℝ) :=
    (h537 2).1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
      (pow_nonneg hD0 _)) (Real.rpow_nonneg hlam0.le _))
  have hu1 : S5.uNorm ell h 1 Bsum ≤ |KP6 1 P| * D ^ C6 * lam ^ (-5 / 2 : ℝ) := by
    have h1 := (h537 1).2
    have h2 := Bridge.uNorm_nonneg ell h 1 hT
      (∑ q ∈ Finset.Icc 2 P, S5.meanSource (S5.ops d) u (S5.curlCorrection d S) R q)
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
      (pow_nonneg hD0 _)) (Real.rpow_nonneg hlam0.le _))
    linarith
  -- Proposition 5.4: `⟨W⟩ = ∑_{p≥2} B_p`, and `W_osc = 0` before `t₀`
  have hAvgW : (S5.ops d).average (S5.expansion u P) = Bsum := by
    have h1 : (S5.ops d).average (S5.expansion u P) =
        S5.expansion u P - (S5.expansion u P - (S5.ops d).average (S5.expansion u P)) := by abel
    rw [h1, hoscW]
    change (∑ i ∈ Finset.Icc 1 P, (u.V i + S5.Cd u (i + 1) + u.B i)) -
      ∑ i ∈ Finset.Icc 1 P, (u.V i + S5.Cd u (i + 1)) = Bsum
    rw [← Finset.sum_sub_distrib]
    simp only [add_sub_cancel_left]
    have h1P : (1 : ℕ) ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    rw [← Finset.sum_erase_add _ _ h1P, hu.first_mean.1, add_zero]
    congr 1
    ext i
    simp only [Finset.mem_erase, Finset.mem_Icc]
    omega
  have hOscZero (t : ℝ) (ht : t ∈ Icc 0 T) (htt : t < t₀) (x : Vec3) (s : ℝ) :
      (S5.expansion u P - (S5.ops d).average (S5.expansion u P)).val.val.val (t, x, s) = 0 := by
    rw [hoscW, profile_sum_eval]
    obtain ⟨hV0, hC0, -⟩ := hbefore t ht htt x s
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := Finset.mem_Icc.mp hi
    change (u.V i).val.val.val (t, x, s) + (S5.Cd u (i + 1)).val.val.val (t, x, s) = 0
    rw [(hV0 i hi).1, hC0 (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), add_zero]
  -- the oscillatory part of `c` (5.10, `:310-316`)
  have hp3 : 3 * C1 + C6 ≤ p := by omega
  have hosc : ∀ t ∈ Icc 0 T, PhaseJetBound 2 (Bc P * D ^ p * lam ^ (-5 / 4 : ℝ))
      (scaledPhaseProfile ell h
        (fun x => phaseOscillation (fun s => pullbackField X Wf v t (x, s)))) := by
    intro t ht
    have heq : (fun x => phaseOscillation (fun s => pullbackField X Wf v t (x, s))) =
        fun x s => Gf t x
          ((S5.expansion u P - (S5.ops d).average (S5.expansion u P)).val.val.val (t, x, s)) := by
      funext x s
      exact phaseOscillation_pullback_eq d (S5.expansion u P) v ht x s
    rw [heq]
    have hL0 : 0 ≤ lam ^ (-5 / 4 : ℝ) := Real.rpow_nonneg hlam0.le _
    have hBnn : 0 ≤ Bc P * D ^ p * lam ^ (-5 / 4 : ℝ) := by
      have := hBc P; positivity
    by_cases htt : t < t₀
    · have hz : scaledPhaseProfile ell h (fun x s => Gf t x
          ((S5.expansion u P - (S5.ops d).average (S5.expansion u P)).val.val.val (t, x, s))) = 0 := by
        funext z
        change Gf t _ ((S5.expansion u P - (S5.ops d).average (S5.expansion u P)).val.val.val
          (t, _, _)) = 0
        rw [hOscZero t ht htt, map_zero]
      rw [hz]
      intro j _ z
      have h0 : iteratedFDeriv ℝ j (0 : Vec3 × ℝ → Vec3) z = 0 := by
        rw [show (0 : Vec3 × ℝ → Vec3) = fun _ => 0 from rfl, iteratedFDeriv_fun_zero]
        rfl
      rw [h0, norm_zero]
      exact hBnn
    · have ht' : t ∈ Icc t₀ T := ⟨not_lt.mp htt, ht.2⟩
      have hJ := scaledJets_of_wNorm hT hL.start_nonneg hL.start_lt.le
        (Bridge.Origin.weight_continuousOn hO) (Bridge.Origin.weight_pos hP hO)
        (Bridge.Origin.weight_le_one hO) hBw ell h 2
        (S5.expansion u P - (S5.ops d).average (S5.expansion u P)) ht'
      have hAF : 0 ≤ 4 ^ 2 * (|KP6 2 P| * D ^ C6 * lam ^ (-5 / 4 : ℝ)) := by positivity
      have hJ' : PhaseJetBound 2 (4 ^ 2 * (|KP6 2 P| * D ^ C6 * lam ^ (-5 / 4 : ℝ)))
          (scaledPhaseProfile ell h (fun a s =>
            (S5.expansion u P - (S5.ops d).average (S5.expansion u P)).val.val.val (t, a, s))) :=
        fun j hj z => (hJ j hj z).trans (mul_le_mul_of_nonneg_left hw2 (by norm_num))
      have hprod := scaledJets_apply hell1 (hGs t ht) (profile_slice_smooth _ ht)
        (mul_nonneg hKG (pow_nonneg hD0 _)) hAF (hGj t ht) hJ'
      intro j hj z
      refine (hprod j hj z).trans ?_
      have hpow : D ^ (3 * C1) * D ^ C6 ≤ D ^ p := by
        rw [← pow_add]; exact pow_le_pow_right₀ hD1 hp3
      have hK2 : 64 * KG * |KP6 2 P| ≤ Bc P := by
        have : 0 ≤ 64 * KG * |KP6 1 P| := by positivity
        change 64 * KG * |KP6 2 P| ≤ 64 * KG * (|KP6 2 P| + |KP6 1 P|) + 1 + KG
        have hr : 64 * KG * (|KP6 2 P| + |KP6 1 P|) = 64 * KG * |KP6 2 P| + 64 * KG * |KP6 1 P| := by
          ring
        linarith only [hr, this, hKG]
      have hA := abs_nonneg (KP6 2 P)
      calc (2 : ℝ) ^ 2 * (KG * D ^ (3 * C1)) * (4 ^ 2 * (|KP6 2 P| * D ^ C6 * lam ^ (-5 / 4 : ℝ)))
          = (64 * KG * |KP6 2 P|) * (D ^ (3 * C1) * D ^ C6) * lam ^ (-5 / 4 : ℝ) := by ring
        _ ≤ Bc P * D ^ p * lam ^ (-5 / 4 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hL0
          exact mul_le_mul hK2 hpow (by positivity) (hBc P)
  -- the mean part of `c`, with the perturbation `v∘X`
  have hmean : ∀ t ∈ Icc 0 T, PhaseJetBound 1 (Bc P * D ^ p * lam ^ (-5 / 2 : ℝ))
      (scaledPhaseProfile ell h
        (fun x _ => phaseMean (fun s => pullbackField X Wf v t (x, s)))) := by
    intro t ht
    have hWc (x : Vec3) : Continuous (Wf t x) :=
      ((profile_slice_smooth (S5.expansion u P) ht).comp
        (contDiff_const.prodMk contDiff_id)).continuous
    have hfun : (fun x (_ : ℝ) => phaseMean (fun s => pullbackField X Wf v t (x, s))) =
        (fun x s => Gf t x (Bsum.val.val.val (t, x, s))) +
          (fun x (_ : ℝ) => Gf t x (v t (X 0 t x))) := by
      funext x s
      rw [phaseMean_pullbackField_eq_add (hWc x)]
      change phaseMean (fun r => Gf t x (Wf t x r + (0 : Velocity) t (X 0 t x))) +
          Gf t x (v t (X 0 t x)) = Gf t x (Bsum.val.val.val (t, x, s)) + Gf t x (v t (X 0 t x))
      congr 1
      simp only [Pi.zero_apply, add_zero]
      unfold phaseMean
      rw [(Gf t x).intervalIntegral_comp_comm ((hWc x).intervalIntegrable 0 1)]
      change Gf t x (phaseMean (fun r => (S5.expansion u P).val.val.val (t, x, r))) = _
      rw [phaseMean_eq_average d (S5.expansion u P) ht x s, hAvgW]
    have hsplit : scaledPhaseProfile ell h
          (fun x (_ : ℝ) => phaseMean (fun s => pullbackField X Wf v t (x, s))) =
        scaledPhaseProfile ell h (fun x s => Gf t x (Bsum.val.val.val (t, x, s))) +
          scaledPhaseProfile ell h (fun x (_ : ℝ) => Gf t x (v t (X 0 t x))) := by
      rw [hfun]; rfl
    rw [hsplit]
    have hL0 : 0 ≤ lam ^ (-5 / 2 : ℝ) := Real.rpow_nonneg hlam0.le _
    have hJB := scaledJets_of_uNorm hT ell h 1 Bsum ht
    have hAF : 0 ≤ 4 ^ 1 * (|KP6 1 P| * D ^ C6 * lam ^ (-5 / 2 : ℝ)) := by positivity
    have hJB' : PhaseJetBound 1 (4 ^ 1 * (|KP6 1 P| * D ^ C6 * lam ^ (-5 / 2 : ℝ)))
        (scaledPhaseProfile ell h (fun a s => Bsum.val.val.val (t, a, s))) :=
      fun j hj z => (hJB j hj z).trans (mul_le_mul_of_nonneg_left hu1 (by norm_num))
    have hM := scaledJets_apply hell1 (hGs t ht) (profile_slice_smooth Bsum ht)
      (mul_nonneg hKG (pow_nonneg hD0 _)) hAF (fun j hj => hGj t ht j (hj.trans (by norm_num)))
      hJB'
    have hTl := scaledPerturbation_phaseJetBound_one (ell := ell) (h := h) hell1
      ((hAs t ht).differentiable (by simp)) ((hGs t ht).differentiable (by simp))
      (fun a => hP.deformation_le t ht a) (fun a => hP.inverse_deformation_le t ht a)
      (fun a => by simpa only [norm_iteratedFDeriv_one] using hGj t ht 1 (by norm_num) a)
      ((hvs t ht).differentiable (by simp))
      (fun a => by simpa only [norm_iteratedFDeriv_zero] using hvjet t ht 0 (by norm_num) a)
      (fun a => by simpa only [norm_iteratedFDeriv_one] using hvjet t ht 1 (by norm_num) a)
    have hd1 : Differentiable ℝ (scaledPhaseProfile ell h (fun x s => Gf t x (Bsum.val.val.val (t, x, s)))) :=
      ((((hGs t ht).comp (ell • ContinuousLinearMap.fst ℝ Vec3 ℝ).contDiff).clm_apply
        ((profile_slice_smooth Bsum ht).comp (labelPhaseScale ell h).contDiff))).differentiable
        (by simp)
    have hd2 : Differentiable ℝ (scaledPhaseProfile ell h (fun x (_ : ℝ) => Gf t x (v t (X 0 t x)))) :=
      (((hGs t ht).clm_apply ((hvs t ht).comp (hAs t ht))).comp
        (ell • ContinuousLinearMap.fst ℝ Vec3 ℝ).contDiff).differentiable (by simp)
    have hsum := TruncatedChildStage.phaseJetBound_one_add hd1 hd2 hM hTl
    intro j hj z
    refine (hsum j hj z).trans ?_
    have hpow1 : D ^ (3 * C1) * D ^ C6 ≤ D ^ p := by
      rw [← pow_add]; exact pow_le_pow_right₀ hD1 hp3
    have hpowD : D ≤ D ^ p := le_self_pow₀ hD1 (by omega)
    have hpowDD : D * D ≤ D ^ p := by
      rw [← pow_two]; exact pow_le_pow_right₀ hD1 (by omega)
    have hpowG : D ^ (3 * C1) ≤ D ^ p := pow_le_pow_right₀ hD1 (by omega)
    have hring : (1 + KG) * D ^ p = D ^ p + KG * D ^ p := by ring
    have hmax : max D (D * D + KG * D ^ (3 * C1)) ≤ (1 + KG) * D ^ p := by
      refine max_le ?_ ?_
      · linarith only [hpowD, hring, mul_nonneg hKG (pow_nonneg hD0 p)]
      · linarith only [hpowDD, hring, mul_le_mul_of_nonneg_left hpowG hKG]
    have hA := abs_nonneg (KP6 1 P)
    have hK1 : 8 * KG * |KP6 1 P| + (1 + KG) ≤ Bc P := by
      have : 0 ≤ 64 * KG * |KP6 2 P| := by positivity
      change 8 * KG * |KP6 1 P| + (1 + KG) ≤ 64 * KG * (|KP6 2 P| + |KP6 1 P|) + 1 + KG
      have hr : 64 * KG * (|KP6 2 P| + |KP6 1 P|) = 64 * KG * |KP6 2 P| + 64 * (KG * |KP6 1 P|) := by
        ring
      have hr' : 8 * KG * |KP6 1 P| = 8 * (KG * |KP6 1 P|) := by ring
      linarith only [hr, hr', this, mul_nonneg hKG hA]
    calc (2 : ℝ) ^ 1 * (KG * D ^ (3 * C1)) * (4 ^ 1 * (|KP6 1 P| * D ^ C6 * lam ^ (-5 / 2 : ℝ))) +
          max D (D * D + KG * D ^ (3 * C1)) * lam ^ (-5 / 2 : ℝ)
        ≤ (8 * KG * |KP6 1 P|) * D ^ p * lam ^ (-5 / 2 : ℝ) +
          ((1 + KG) * D ^ p) * lam ^ (-5 / 2 : ℝ) := by
          refine add_le_add ?_ (mul_le_mul_of_nonneg_right hmax hL0)
          have : (2 : ℝ) ^ 1 * (KG * D ^ (3 * C1)) * (4 ^ 1 * (|KP6 1 P| * D ^ C6 * lam ^ (-5 / 2 : ℝ)))
              = (8 * KG * |KP6 1 P|) * (D ^ (3 * C1) * D ^ C6) * lam ^ (-5 / 2 : ℝ) := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow1 (by positivity)) hL0
      _ = (8 * KG * |KP6 1 P| + (1 + KG)) * D ^ p * lam ^ (-5 / 2 : ℝ) := by ring
      _ ≤ Bc P * D ^ p * lam ^ (-5 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK1 (pow_nonneg hD0 _)) hL0
  -- the standing bounds `|D_aX^{±1}| ≤ 𝖣` and `|k_*| ≤ 𝖣λ`
  have hParentBd : ∀ t ∈ Icc 0 T, ∀ x : Vec3,
      ‖fderiv ℝ (X 0 t) x‖ ≤ D ∧ ‖fderiv ℝ (X t 0) x‖ ≤ D := by
    intro t ht x
    refine ⟨hP.deformation_le t ht x, ?_⟩
    have hx : X 0 t (X t 0 x) = x := (hXinv t ht).2 x
    have h1 := hP.inverse_deformation_le t ht (X t 0 x)
    rwa [hx] at h1
  have hk : ‖k‖ ≤ D * lam := by
    have hc := Bridge.Launch.carrier_eq hP hL
    have ht0 := Bridge.Launch.start_mem hL
    rw [← hc]
    calc ‖(fderiv ℝ (X 0 t₀) 0).adjoint (S5.waveVector X k t₀ 0)‖
        ≤ ‖(fderiv ℝ (X 0 t₀) 0).adjoint‖ * ‖S5.waveVector X k t₀ 0‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (X 0 t₀) 0‖ * lam := by
          rw [LinearIsometryEquiv.norm_map, hL.frequency]
      _ ≤ D * lam := mul_le_mul_of_nonneg_right (hP.deformation_le t₀ ht0 0) hlam0.le
  -- the flow estimate (the body of the proof of 5.10)
  have hWj : ContDiffOn ℝ ∞ (Function.uncurry fun t => Function.uncurry (Wf t))
      (Icc 0 T ×ˢ (univ : Set PhaseState)) := HierarchySmoothProfile.smooth (S5.expansion u P).val.val
  obtain ⟨Y, hY⟩ := exists_childFlow_of_profile_jet_bounds (v := v) (W := Wf) (B := Bc P)
    (Γ := Γ P) (a := a) (p := p) (b := b) hT hP.time_le_one hX (hU.of_le (by simp)) hUper
    hP.divergence_free (fun t ht x => ((hAs t ht).of_le (by simp)).contDiffAt) hParentBd hD1 hlam1
    hell0 (hBc P) hellSize rfl hk hbp (hΓ P) hsmall
    (contDiffOn_pullbackField_of_parent hT hX hU hUper hWj hv)
    (fun t ht => profile_slice_smooth (S5.expansion u P) ht)
    (fun t _ x => HierarchyPeriodicProfile.phasePeriodic (S5.expansion u P).val t x)
    (fun t _ n x s => twistedSlice (S5.expansion u P) t x s n)
    (profileDivergence_pointwise d hX hU hUper (S5.expansion u P) hdivW) hvper
    (fun t ht x => ⟨(hvs t ht).differentiable (by simp) x, hvdiv t ht x⟩) hosc hmean
  refine ⟨⟨Y, hY⟩, ?_⟩
  -- every label flow of `V + v` is this flow
  intro Yf hYf t ht x
  have hGr : ContDiffOn ℝ ∞ (Function.uncurry (graphRead (fun t => X t 0) (S5.expansion u P)))
      (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    HierarchySmoothProfile.contDiffOn_graphRead k (S5.expansion u P).val.val hInvFlow
  have hVv : ContDiffOn ℝ ∞ (Function.uncurry (V + v)) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    (hU.add hGr).add hv
  have hVvper : ∀ r ∈ Icc 0 T, SpatiallyPeriodic ((V + v) r) := by
    intro r hr n y
    have hg := spatiallyPeriodic_inverseParentGraphRead hT hX hU hUper (S5.expansion u P) hr
    change U r (y + latticeVector n) +
        graphRead (fun t => X t 0) (S5.expansion u P) r (y + latticeVector n) +
        v r (y + latticeVector n) =
      U r y + graphRead (fun t => X t 0) (S5.expansion u P) r y + v r y
    rw [hUper r hr n y, hg n y, hvper r hr n y]
  obtain ⟨K2, hK2⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hVv.of_le (by simp)) hVvper
  have e1 : Yf 0 t = Y 0 t := labelFlow_eq hK2 hY.flow hYf h0T ht
  have e2 : Yf t 0 = Y t 0 := labelFlow_eq hK2 hY.flow hYf ht h0T
  obtain ⟨-, hF, hG⟩ := hY.bounds t ht
  rw [e1, e2]
  exact ⟨(hF x).2, (hG x).2⟩

end

end TorusEuler.Paper
