import TorusEuler.Paper.S5.Statements
import TorusEuler.Paper.Proofs.S5Bridge.Norms
import TorusEuler.Paper.Proofs.S5Bridge.Parent
import TorusEuler.Paper.Proofs.S5a.Library.RelayBudget

/-!
# Lemma 5.5: the estimates (5.31) and (5.32)

`Lib.S5a.lemma55_main` proves the first conjunct of `Statement.lemma_5_5` (the estimates
(5.31) and (5.32) for every admissible `V`, `f`, `𝗉`) from Proposition 5.1 and Lemma D.1,
following `sections/06c_finite_hierarchy.tex:415-447`:

* (5.8) of Proposition 5.1 bounds the weighted label derivatives of the coefficients
  `(D_aX)⁻¹`, `M`, `κ/λ`, `λ²/|κ|²` by `C_n 𝖣^C` (`ℓ_* ≤ 𝖣^{-C}` since `a ≥ a₀`);
* the coefficients of `Q[V]`, `∂_tQ[V]` (5.33), `∂_s𝗉` and the curl and gradient rows are
  products of these with fixed maps and `ℓ_*⁻¹ = 𝖣^a` ("since `ℓ_*^{-1}` is a power of `𝖣`"),
  estimated with the product rule (D.4) of Lemma D.1 (`Lib.S5a.relayBudget`);
* the phase primitive is estimated with (D.5) of Lemma D.1 and the label derivative of the
  curl with (D.3)-type word bounds (`Lib.S5a.boundedWeightSeminorm_complete_le_of_D1`,
  `Lib.S5a.boundedWeightSeminorm_waveRelay_le_of_eval_of_D1`); the time derivative of `Q[V]`
  uses `κ_t = -Mᵀκ` and the transverse equation, without a time derivative of `M`, `f` or a
  mean (`material_complete_add_labelGrad_apply_relay_of_momentum_on`).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

noncomputable section

open HierarchyTwistedProfile

namespace Lib.S5a

/-- A slice of a field that is jointly smooth on the slab is smooth. -/
theorem contDiff_slice' {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {c : ℝ → Vec3 → Y} {T t : ℝ}
    (hc : ContDiffOn ℝ ∞ (Function.uncurry c) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (c t) :=
  contDiffOn_univ.mp (hc.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

set_option maxHeartbeats 8000000 in
/-- **(5.31) and (5.32) of Lemma 5.5** (`sections/06c_finite_hierarchy.tex:415-447`), from
Proposition 5.1 (`h5_1`, its bound (5.8) for the coefficients, with `a₀ = C`) and Lemma D.1
(`hD_1`, the product rule (D.4) in `Lib.S5a.relayBudget` and the primitive estimate (D.5) in
the relay estimates). The exponent is `C = 12(C_{5.1} + a)`. -/
theorem lemma55_main (h5_1 : Statement.proposition_5_1) (hD_1 : Statement.lemma_D_1) :
    ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ C : ℕ, ∃ K : ℕ → ℝ,
      ∀ {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
        {D lam t₀ : ℝ} {center : ℝ → Vec3} (d : ParentGeometry hT U X k),
        S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ → S5.Origin T U X k D lam t₀ center →
        ∀ n : ℕ, ∀ V : HierarchyTwistedProfile T k Vec3, (S5.ops d).average V = 0 →
          (∀ t ∈ Icc t₀ T, ∀ x s, ⟪S5.waveVector X k t x, V.val.val.val (t, x, s)⟫_ℝ = 0) →
          S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) n
              (S5.curlCorrection d V) ≤
            K n * D ^ C * lam⁻¹ *
              S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) (n + 1) V ∧
          ∀ (f : HierarchyTwistedProfile T k Vec3) (q : HierarchyTwistedProfile T k ℝ),
            (S5.ops d).average f = 0 →
            (∀ t ∈ Icc t₀ T, ∀ x, phaseMean (fun s => q.val.val.val (t, x, s)) = 0) →
            (∀ t ∈ Icc t₀ T, ∀ x s,
              ((S5.ops d).material V + (S5.ops d).phaseGrad q).val.val.val (t, x, s) =
                f.val.val.val (t, x, s)) →
            S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) n
                ((S5.ops d).material (S5.curlCorrection d V) + (S5.ops d).labelGrad q) ≤
              K n * D ^ C * lam⁻¹ *
                (S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) (n + 1) V +
                  S5.wNorm (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) (n + 1) f) := by
  obtain ⟨C5, K5, h51'⟩ := h5_1
  obtain ⟨_, h51⟩ := h51' (fun _ => 0)
  refine ⟨C5, fun a ha => ?_⟩
  let W4 (m : ℕ) : ℝ := ((hierarchyAdmissibleWords (Fin 4) m).card : ℝ)
  let L (m : ℕ) : ℝ := 1 + |K5 m|
  let c6 (n : ℕ) : ℝ := 6 * W4 n * W4 (n + 1) * (2 : ℝ) ^ n * (2 : ℝ) ^ (n + 1)
  let Kc (n : ℕ) : ℝ := max (c6 n) (waveRelayOrderConstant n) *
    (relayOmega (n + 1) ^ 10 * L (n + 1) ^ 6) ^ 2
  refine ⟨12 * (C5 + a), Kc, ?_⟩
  intro T hT U X pU k D lam t₀ center d hP hL hO n V hV htrans
  -- the standing quantities
  have hD : 1 ≤ D := one_le_two.trans hP.scale_ge_two
  have hD₀ : 0 < D := zero_lt_one.trans_le hD
  have hlam : 0 < lam := zero_lt_one.trans_le hP.frequency_ge_one
  set ℓ := S5.radius D a with hℓdef
  set h := S5.width lam with hhdef
  set γ := S5.weight lam center with hγdef
  have hℓ : 0 < ℓ := Bridge.radius_pos hP a
  have hh : 0 < h := Bridge.width_pos hP
  have hℓD : ℓ ≤ (D ^ C5)⁻¹ := inv_anti₀ (pow_pos hD₀ _) (pow_le_pow_right₀ hD ha)
  have ht₀ : 0 ≤ t₀ := hL.start_nonneg
  have htT : t₀ < T := hL.start_lt
  have hI : Icc t₀ T ⊆ Icc 0 T := Bridge.Launch.active_subset hL
  obtain ⟨Bγ, hBγ⟩ := Bridge.Origin.exists_inverse_weight_bound hP hL hO
  have hU₂ : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hP.velocity_smooth.of_le (by simp)
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  -- Proposition 5.1: (D.6) and (5.8) for the coefficients
  obtain ⟨hD6, -, h58⟩ := h51 hT hP hL
  -- the common bound `Θ` of the basic coefficients and of `ℓ_*⁻¹`
  set Θ := L (n + 1) * D ^ (C5 + a) with hΘdef
  have hL1 (m : ℕ) : 1 ≤ L m := le_add_of_nonneg_right (abs_nonneg _)
  have hΘ : 1 ≤ Θ := one_le_mul_of_one_le_of_one_le (hL1 _) (one_le_pow₀ hD)
  have hKΘ : K5 (n + 1) * D ^ C5 ≤ Θ := by
    calc K5 (n + 1) * D ^ C5 ≤ L (n + 1) * D ^ C5 :=
          mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_add_of_nonneg_left zero_le_one))
            (pow_nonneg hD₀.le _)
      _ ≤ Θ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega))
          (zero_le_one.trans (hL1 _))
  have hℓΘ : ‖ℓ⁻¹‖ ≤ Θ := by
    rw [hℓdef, S5.radius, inv_inv, Real.norm_of_nonneg (pow_nonneg hD₀.le _)]
    calc D ^ a = 1 * D ^ a := (one_mul _).symm
      _ ≤ L (n + 1) * D ^ (C5 + a) :=
        mul_le_mul (hL1 _) (pow_le_pow_right₀ hD (by omega)) (pow_nonneg hD₀.le _)
          (zero_le_one.trans (hL1 _))
  -- smoothness of the flow and of the coefficients
  have hXsmooth (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (X 0 t) :=
    contDiff_infty.mpr fun j =>
      (hP.flow.labelJets_evolve j hT hP.velocity_smooth hP.velocity_periodic).1 t ht
  have hGs (t : ℝ) (ht : t ∈ Icc 0 T) :
      ContDiff ℝ ∞ (fun b => fderiv ℝ (X t 0) (X 0 t b)) :=
    contDiff_infty.mpr fun j => hP.flow.contDiff_inverseLabelDerivative hT hU₂
      hP.velocity_periodic h₀ ht ((hXsmooth t ht).of_le (by simp))
  have hMs (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (S5.strainField U X t) :=
    contDiff_slice' (Bridge.Parent.strainField_smooth hT hP) ht
  have hκs (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (S5.waveVector X k t) :=
    contDiff_slice' (Bridge.Parent.waveVector_smooth hT hP) ht
  have hκnz (t : ℝ) (ht : t ∈ Icc 0 T) (b : Vec3) : S5.waveVector X k t b ≠ 0 :=
    Bridge.Parent.waveVector_ne_zero hT hP hL.carrier_ne_zero ht b
  -- a basic coefficient bounded by (5.8) has word bound `Θ` at order `n+1`
  have basic {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (c : ℝ → Vec3 → Y)
      (hcs : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (c t))
      (hbdd : ∀ j, ∀ t ∈ Icc 0 T, BddAbove (range fun b => ‖iteratedFDeriv ℝ j (c t) b‖))
      (hsum : ∀ t ∈ Icc 0 T, (∑ j ∈ Finset.range (n + 1 + 1),
        ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (c t))) ≤ K5 (n + 1) * D ^ C5) :
      MonoW ℓ h (n + 1) (relayOmega (n + 1)) Θ 0 1 (fun (t : Icc t₀ T) x => c t x.1) := by
    refine MonoW.of_wb (fun t => (hcs t (hI t.2)).comp contDiff_fst)
      (hierarchyRelayWordBound_of_phaseIndependent hℓ.le (zero_le_one.trans hΘ)
        (fun t => hcs t (hI t.2)) fun t j hj b => ?_)
    have ht := hI t.2
    have hnn (i : ℕ) : 0 ≤ ℓ ^ i * spatialSupNorm (iteratedFDeriv ℝ i (c t)) :=
      mul_nonneg (pow_nonneg hℓ.le _) ((norm_nonneg _).trans (le_ciSup (hbdd i t ht) 0))
    calc ℓ ^ j * ‖iteratedFDeriv ℝ j (c t) b‖
        ≤ ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (c t)) :=
          mul_le_mul_of_nonneg_left (le_ciSup (hbdd j t ht) b) (pow_nonneg hℓ.le _)
      _ ≤ ∑ i ∈ Finset.range (n + 1 + 1), ℓ ^ i * spatialSupNorm (iteratedFDeriv ℝ i (c t)) :=
          Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
      _ ≤ K5 (n + 1) * D ^ C5 := hsum t ht
      _ ≤ Θ := hKΘ
  have bddOf {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (c : ℝ → Vec3 → Y)
      (hjet : ∀ j, ∀ t ∈ Icc 0 T, ∀ b, ‖iteratedFDeriv ℝ j (c t) b‖ ≤ K5 j * D ^ (C5 * (j + 1)))
      (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) :
      BddAbove (range fun b => ‖iteratedFDeriv ℝ j (c t) b‖) :=
    ⟨_, by rintro _ ⟨b, rfl⟩; exact hjet j t ht b⟩
  -- the four basic coefficients, in the form of the parent geometry `d`
  have mG : MonoW ℓ h (n + 1) (relayOmega (n + 1)) Θ 0 1
      (fun (t : Icc t₀ T) x => d.inverse.val.val.val (t, x.1, 0)) :=
    (basic (fun t b => fderiv ℝ (X t 0) (X 0 t b)) hGs
      (bddOf _ fun j t ht b => (hD6 j t ht b).2.1)
      (fun t ht => (h58 ℓ hℓ hℓD (n + 1) t ht).2.1)).congr fun t x =>
        (d.inverse_value (t, x.1, 0) ⟨hI t.2, mem_univ _⟩).symm
  have mM : MonoW ℓ h (n + 1) (relayOmega (n + 1)) Θ 0 1
      (fun (t : Icc t₀ T) x => d.strain.val.val.val (t, x.1, 0)) :=
    (basic (S5.strainField U X) hMs (bddOf _ fun j t ht b => (hD6 j t ht b).2.2.1)
      (fun t ht => (h58 ℓ hℓ hℓD (n + 1) t ht).2.2.1)).congr fun t x =>
        (d.strain_value (t, x.1, 0) ⟨hI t.2, mem_univ _⟩).symm
  have mκ : MonoW ℓ h (n + 1) (relayOmega (n + 1)) Θ 0 1
      (fun (t : Icc t₀ T) x => lam⁻¹ • d.covector.val.val.val (t, x.1, 0)) :=
    (basic (fun t b => lam⁻¹ • S5.waveVector X k t b) (fun t ht => (hκs t ht).const_smul _)
      (bddOf _ fun j t ht b => (hD6 j t ht b).2.2.2.1)
      (fun t ht => (h58 ℓ hℓ hℓD (n + 1) t ht).2.2.2.1)).congr fun t x => by
        rw [d.covector_value (t, x.1, 0) ⟨hI t.2, mem_univ _⟩]
        rfl
  have mν : MonoW ℓ h (n + 1) (relayOmega (n + 1)) Θ 0 1
      (fun (t : Icc t₀ T) x => lam ^ 2 / ‖S5.waveVector X k t x.1‖ ^ 2) :=
    basic (fun t b => lam ^ 2 / ‖S5.waveVector X k t b‖ ^ 2)
      (fun t ht => contDiff_const.div ((hκs t ht).norm_sq ℝ)
        (fun b => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hκnz t ht b))))
      (bddOf _ fun j t ht b => (hD6 j t ht b).2.2.2.2.1)
      (fun t ht => (h58 ℓ hℓ hℓD (n + 1) t ht).2.2.2.2.1)
  have hνeq (t : Icc t₀ T) (b : Vec3) :
      lam ^ 2 / ‖S5.waveVector X k t b‖ ^ 2 = (‖lam⁻¹ • d.covector.val.val.val (t, b, 0)‖ ^ 2)⁻¹ := by
    rw [d.covector_value (t, b, 0) ⟨hI t.2, mem_univ _⟩, inv_sq_norm_inv_smul]
    rfl
  -- the coefficient budget, by (5.8) and (D.4)
  have hCoeff := relayBudget hD_1 hℓ hh hΘ n
    (G := fun (t : Icc t₀ T) b => d.inverse.val.val.val (t, b, 0))
    (M := fun (t : Icc t₀ T) b => d.strain.val.val.val (t, b, 0))
    (κn := fun (t : Icc t₀ T) b => lam⁻¹ • d.covector.val.val.val (t, b, 0))
    (ν := fun (t : Icc t₀ T) b => lam ^ 2 / ‖S5.waveVector X k t b‖ ^ 2) mG mM mκ mν hνeq hℓΘ
  -- the norms of the statement are the library seminorms on `[t₀,T]`
  have hW (m : ℕ) {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      (g : HierarchyTwistedProfile T k Y) :
      S5.wNorm ℓ h t₀ γ m g =
        boundedWeightSeminorm False ℓ h m hT hI (fun t => (γ t)⁻¹) hBγ g :=
    Bridge.wNorm_eq_boundedWeightSeminorm ℓ h m hT ht₀ γ hBγ g
  have hK2 : (relayOmega (n + 1) ^ 10 * Θ ^ 6) ^ 2 =
      (relayOmega (n + 1) ^ 10 * L (n + 1) ^ 6) ^ 2 * D ^ (12 * (C5 + a)) := by
    rw [hΘdef]
    ring
  have hc6 : 0 ≤ c6 n := by positivity
  have hcmax1 : c6 n ≤ max (c6 n) (waveRelayOrderConstant n) := le_max_left _ _
  have hcmax2 : waveRelayOrderConstant n ≤ max (c6 n) (waveRelayOrderConstant n) := le_max_right _ _
  have hD12 : 0 ≤ (relayOmega (n + 1) ^ 10 * L (n + 1) ^ 6) ^ 2 * D ^ (12 * (C5 + a)) := by
    positivity
  constructor
  · -- (5.31)
    have h531 := boundedWeightSeminorm_complete_le_of_D1 hD_1 hT d.inverse d.covector V
      d.mean.inverse_independent d.oscillation.covector_independent d.oscillation.covector_ne_zero
      hV hI (fun t => (γ t)⁻¹) hBγ ℓ h hℓ hh n hlam hCoeff.curl hCoeff.potential
    rw [hW, hW]
    refine h531.trans ?_
    rw [hK2]
    have hX := apply_nonneg (boundedWeightSeminorm (E := Vec3) False ℓ h (n + 1) hT hI (fun t => (γ t)⁻¹) hBγ) V
    have hli : 0 ≤ lam⁻¹ := inv_nonneg.mpr hlam.le
    calc c6 n * ((relayOmega (n + 1) ^ 10 * L (n + 1) ^ 6) ^ 2 * D ^ (12 * (C5 + a))) * lam⁻¹ *
          boundedWeightSeminorm False ℓ h (n + 1) hT hI (fun t => (γ t)⁻¹) hBγ V
        ≤ max (c6 n) (waveRelayOrderConstant n) *
            ((relayOmega (n + 1) ^ 10 * L (n + 1) ^ 6) ^ 2 * D ^ (12 * (C5 + a))) * lam⁻¹ *
          boundedWeightSeminorm False ℓ h (n + 1) hT hI (fun t => (γ t)⁻¹) hBγ V := by
          gcongr
      _ = Kc n * D ^ (12 * (C5 + a)) * lam⁻¹ *
          boundedWeightSeminorm False ℓ h (n + 1) hT hI (fun t => (γ t)⁻¹) hBγ V := by
          simp only [Kc]
          ring
  · -- (5.32)
    intro F q hFav hq hMom
    have hGeom := transportedWaveRelay_coefficient_timeEquations hT hP.flow hU₂
      hP.velocity_periodic d.inverse d.strain d.covector
      (fun t ht x => d.inverse_value (t, x, 0) ⟨ht, mem_univ _⟩)
      (fun t ht x => d.strain_value (t, x, 0) ⟨ht, mem_univ _⟩)
      (fun t ht x => d.covector_value (t, x, 0) ⟨ht, mem_univ _⟩)
    have htrans' (t : ℝ) (ht : t ∈ Icc t₀ T) (x : Vec3) (s : ℝ) :
        ⟪d.covector.val.val.val (t, x, 0), V.val.val.val (t, x, s)⟫_ℝ = 0 := by
      rw [d.covector_value (t, x, 0) ⟨hI ht, mem_univ _⟩]
      exact htrans t ht x s
    have hEval (t : ℝ) (ht : t ∈ Icc t₀ T) (x : Vec3 × ℝ) :
        ((S5.ops d).material (S5.curlCorrection d V) + (S5.ops d).labelGrad q).val.val.val (t, x) =
          waveRelayAt d.inverse d.strain d.covector V F t x :=
      material_complete_add_labelGrad_apply_relay_of_momentum_on hT d.inverse d.strain d.covector
        V F q ht₀ htT d.mean.inverse_independent
        (PhysicalApproximationData.parentStrain_phaseIndependent (d := d))
        d.oscillation.covector_independent d.oscillation.covector_ne_zero hV hGeom.1 hGeom.2
        htrans' hq hMom ht x
    have h532 := boundedWeightSeminorm_waveRelay_le_of_eval_of_D1 hD_1 hT d.inverse d.strain
      d.covector V F ((S5.ops d).material (S5.curlCorrection d V) + (S5.ops d).labelGrad q)
      ℓ h hℓ hh n hlam hI (fun t => (γ t)⁻¹) hBγ hV hFav hEval hCoeff
    rw [hW, hW, hW]
    refine h532.trans ?_
    rw [hK2]
    have hX := add_nonneg
      (apply_nonneg (boundedWeightSeminorm (E := Vec3) False ℓ h (n + 1) hT hI (fun t => (γ t)⁻¹) hBγ) V)
      (apply_nonneg (boundedWeightSeminorm (E := Vec3) False ℓ h (n + 1) hT hI (fun t => (γ t)⁻¹) hBγ) F)
    have hli : 0 ≤ lam⁻¹ := inv_nonneg.mpr hlam.le
    calc waveRelayOrderConstant n *
          ((relayOmega (n + 1) ^ 10 * L (n + 1) ^ 6) ^ 2 * D ^ (12 * (C5 + a))) * lam⁻¹ *
          (boundedWeightSeminorm False ℓ h (n + 1) hT hI (fun t => (γ t)⁻¹) hBγ V +
            boundedWeightSeminorm False ℓ h (n + 1) hT hI (fun t => (γ t)⁻¹) hBγ F)
        ≤ max (c6 n) (waveRelayOrderConstant n) *
            ((relayOmega (n + 1) ^ 10 * L (n + 1) ^ 6) ^ 2 * D ^ (12 * (C5 + a))) * lam⁻¹ *
          (boundedWeightSeminorm False ℓ h (n + 1) hT hI (fun t => (γ t)⁻¹) hBγ V +
            boundedWeightSeminorm False ℓ h (n + 1) hT hI (fun t => (γ t)⁻¹) hBγ F) := by
          gcongr
      _ = Kc n * D ^ (12 * (C5 + a)) * lam⁻¹ *
          (boundedWeightSeminorm False ℓ h (n + 1) hT hI (fun t => (γ t)⁻¹) hBγ V +
            boundedWeightSeminorm False ℓ h (n + 1) hT hI (fun t => (γ t)⁻¹) hBγ F) := by
          simp only [Kc]
          ring

end Lib.S5a

end

end TorusEuler.Paper
