import TorusEuler.TerminalCoefficientTimeProduct
import TorusEuler.HierarchyRelayPotentialCoefficientBounds

/-! Mixed jets of the four normalized potential and pressure relay coefficients. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "End" => (Vec3 →L[ℝ] Vec3)
local notation "Row" => (Vec3 →L[ℝ] ℝ)
local notation "Slab(" T ")" => Set.prod (Icc (0 : ℝ) T) (univ : Set Vec3)

private structure RelayTimeInput (q : ℕ) (C : ℕ → ℝ) where
  T : ℝ
  D : ℝ
  A : ℝ
  M : ℝ → Vec3 → End
  k : ℝ → Vec3 → Vec3
  time_pos : 0 < T
  D_ge_one : 1 ≤ D
  A_ge_one : 1 ≤ A
  M_smooth : ContDiffOn ℝ ∞ (Function.uncurry M) (Slab(T))
  k_smooth : ContDiffOn ℝ ∞ (Function.uncurry k) (Slab(T))
  k_ne_zero : ∀ t ∈ Icc 0 T, ∀ x, k t x ≠ 0
  M_bound : TerminalMixedJetBound 0 T q 16 D A C M
  k_bound : TerminalMixedJetBound 0 T q 16 D A C k
  inv_bound : TerminalMixedJetBound 0 T q 16 D A C (fun t x => (‖k t x‖ ^ 2)⁻¹)

private def RelayTimeInput.reciprocal {q : ℕ} {C : ℕ → ℝ} (s : RelayTimeInput q C) :
    ℝ → Vec3 → ℝ := fun t x => (‖s.k t x‖ ^ 2)⁻¹

private theorem RelayTimeInput.reciprocal_smooth {q : ℕ} {C : ℕ → ℝ} (s : RelayTimeInput q C) :
    ContDiffOn ℝ ∞ (Function.uncurry s.reciprocal) (Slab(s.T)) :=
  (s.k_smooth.norm_sq ℝ).inv (fun z hz => pow_ne_zero _ (norm_ne_zero_iff.mpr (s.k_ne_zero z.1 hz.1 z.2)))

/-- A coefficient formed from stage data has one mixed jet cost that is
uniform over all admissible instances of those data. -/
private def RelayTimeFamily {q : ℕ} {C : ℕ → ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ)
    (f : RelayTimeInput q C → ℝ → Vec3 → E) : Prop :=
  ∃ K : ℕ → ℝ, (∀ n, 0 ≤ K n) ∧
    ∀ s : RelayTimeInput q C, ContDiffOn ℝ ∞ (Function.uncurry (f s)) (Slab(s.T)) ∧
      TerminalMixedJetBound 0 s.T q 16 s.D (s.A ^ d) K (f s)

namespace RelayTimeFamily

variable {q : ℕ} {C : ℕ → ℝ} {d d' : ℕ}
  {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
  {f : RelayTimeInput q C → ℝ → Vec3 → E} {g : RelayTimeInput q C → ℝ → Vec3 → F}

private theorem map (hf : RelayTimeFamily d f) (L : E →L[ℝ] F) :
    RelayTimeFamily d (fun s t x => L (f s t x)) := by
  obtain ⟨K, hK, hF⟩ := hf
  refine ⟨fun n => ‖L‖ * K n, fun n => mul_nonneg (norm_nonneg L) (hK n), fun s => ?_⟩
  exact ⟨L.contDiff.comp_contDiffOn (hF s).1, (hF s).2.apply_clm s.time_pos (hF s).1 L⟩

private theorem bilinear (hf : RelayTimeFamily d f) (hg : RelayTimeFamily d' g)
    (L : E →L[ℝ] F →L[ℝ] H) :
    RelayTimeFamily (d + d') (fun s t x => L (f s t x) (g s t x)) := by
  obtain ⟨K, hK, hF⟩ := hf
  obtain ⟨K', hK', hG⟩ := hg
  refine ⟨terminalMixedProductCost q L K K', terminalMixedProductCost_nonneg q L hK hK', fun s => ?_⟩
  refine ⟨(L.contDiff.comp_contDiffOn (hF s).1).clm_apply (hG s).1, ?_⟩
  rw [pow_add]
  have hD := zero_le_one.trans s.D_ge_one
  have hA := zero_le_one.trans s.A_ge_one
  exact TerminalMixedJetBound.bilinear L s.time_pos hD (pow_nonneg hA _) (pow_nonneg hA _)
    hK hK' (hF s).2 (hG s).2 (hF s).1 (hG s).1

private theorem mono_power (hf : RelayTimeFamily d f) (hdd' : d ≤ d') :
    RelayTimeFamily d' f := by
  obtain ⟨K, hK, hF⟩ := hf
  exact ⟨K, hK, fun s => ⟨(hF s).1, (hF s).2.mono_amplitude
    (zero_le_one.trans s.D_ge_one) hK (pow_le_pow_right₀ s.A_ge_one hdd')⟩⟩

private theorem add (hf : RelayTimeFamily d f) {g' : RelayTimeInput q C → ℝ → Vec3 → E}
    (hg : RelayTimeFamily d g') :
    RelayTimeFamily d (fun s t x => f s t x + g' s t x) := by
  obtain ⟨K, hK, hF⟩ := hf
  obtain ⟨K', hK', hG⟩ := hg
  exact ⟨fun n => K n + K' n, fun n => add_nonneg (hK n) (hK' n), fun s =>
    ⟨(hF s).1.add (hG s).1, (hF s).2.add (hG s).2 s.time_pos (hF s).1 (hG s).1⟩⟩

private theorem smul (hf : RelayTimeFamily d f) (a : ℝ) :
    RelayTimeFamily d (fun s t x => a • f s t x) :=
  hf.map (a • ContinuousLinearMap.id ℝ E)

private theorem sub (hf : RelayTimeFamily d f) {g' : RelayTimeInput q C → ℝ → Vec3 → E}
    (hg : RelayTimeFamily d g') : RelayTimeFamily d (fun s t x => f s t x - g' s t x) := by
  simpa only [sub_eq_add_neg, neg_one_smul] using hf.add (hg.smul (-1))

private theorem congr (hf : RelayTimeFamily d f) {f' : RelayTimeInput q C → ℝ → Vec3 → E}
    (h : ∀ s t x, f s t x = f' s t x) : RelayTimeFamily d f' :=
  (funext fun s => funext fun t => funext fun x => h s t x) ▸ hf

end RelayTimeFamily

set_option maxHeartbeats 1800000 in
/-- The four normalized inner relay rows inherit one mixed bound from the
strain, normalized covector and its squared-norm reciprocal. The exponent
six reflects the degree of the time derivative of the potential. -/
theorem exists_terminalWaveRelayPotentialJetBounds (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n) (q : ℕ) :
    ∃ K : ℕ → ℝ, (∀ n, 0 ≤ K n) ∧
      ∀ {T D A : ℝ} {M : ℝ → Vec3 → End} {k : ℝ → Vec3 → Vec3},
        0 < T → 1 ≤ D → 1 ≤ A →
        ContDiffOn ℝ ∞ (Function.uncurry M) (Slab(T)) →
        ContDiffOn ℝ ∞ (Function.uncurry k) (Slab(T)) →
        (∀ t ∈ Icc 0 T, ∀ x, k t x ≠ 0) →
        TerminalMixedJetBound 0 T q 16 D A C M →
        TerminalMixedJetBound 0 T q 16 D A C k →
        TerminalMixedJetBound 0 T q 16 D A C (fun t x => (‖k t x‖ ^ 2)⁻¹) →
        let B := A ^ 6
        let V (t : ℝ) (x : Vec3) := hierarchyRelayPotentialCoefficient (k t x)
        let W (t : ℝ) (x : Vec3) := hierarchyRelayTimeAmplitudeCoefficient (M t x) (k t x)
        let P (t : ℝ) (x : Vec3) := hierarchyRelayPressureAmplitudeCoefficient (M t x) (k t x)
        let Q (t : ℝ) (x : Vec3) := hierarchyRelayPressureSourceCoefficient (k t x)
        (ContDiffOn ℝ ∞ (Function.uncurry V) (Slab(T)) ∧ TerminalMixedJetBound 0 T q 16 D B K V) ∧
        (ContDiffOn ℝ ∞ (Function.uncurry W) (Slab(T)) ∧ TerminalMixedJetBound 0 T q 16 D B K W) ∧
        (ContDiffOn ℝ ∞ (Function.uncurry P) (Slab(T)) ∧ TerminalMixedJetBound 0 T q 16 D B K P) ∧
        (ContDiffOn ℝ ∞ (Function.uncurry Q) (Slab(T)) ∧ TerminalMixedJetBound 0 T q 16 D B K Q) := by
  let Adj : End →L[ℝ] End :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)).toContinuousLinearEquiv.toContinuousLinearMap
  let Dot : Vec3 →L[ℝ] Row := innerSL ℝ
  let evV : End →L[ℝ] Vec3 →L[ℝ] Vec3 := (ContinuousLinearMap.apply ℝ Vec3).flip
  let evR : Row →L[ℝ] Vec3 →L[ℝ] ℝ := (ContinuousLinearMap.apply ℝ ℝ).flip
  have hM : RelayTimeFamily 1 (@RelayTimeInput.M q C) :=
    ⟨C, hC, fun d => ⟨d.M_smooth, by simpa only [pow_one] using d.M_bound⟩⟩
  have hκ : RelayTimeFamily 1 (@RelayTimeInput.k q C) :=
    ⟨C, hC, fun d => ⟨d.k_smooth, by simpa only [pow_one] using d.k_bound⟩⟩
  have hInv : RelayTimeFamily 1 (@RelayTimeInput.reciprocal q C) := by
    refine ⟨C, hC, fun d => ⟨d.reciprocal_smooth, ?_⟩⟩
    change TerminalMixedJetBound 0 d.T q 16 d.D (d.A ^ 1) C (fun t x => (‖d.k t x‖ ^ 2)⁻¹)
    rw [pow_one]
    exact d.inv_bound
  have hCross := hκ.map relayCrossMap
  have hDot := hκ.map Dot
  have hAdj := hM.map Adj
  have hMk := hM.bilinear hκ evV
  have hAdjk := hAdj.bilinear hκ evV
  have hFirst := hAdjk.map relayCrossMap
  have hSecond := hCross.bilinear hM (compL ℝ Vec3 Vec3 Vec3)
  have hTimeLinear := hInv.bilinear (hFirst.add hSecond) (lsmul ℝ ℝ)
  have hDotM := hDot.bilinear hMk evR
  have hInvTwice := hInv.bilinear hInv (lsmul ℝ ℝ)
  have hTimeScalar := hInvTwice.bilinear hDotM (lsmul ℝ ℝ)
  have hTimeCubic := (hTimeScalar.bilinear hCross (lsmul ℝ ℝ)).smul 2
  have hPressureLin := hDot.bilinear hM (compL ℝ Vec3 Vec3 ℝ)
  have hPot := (hInv.bilinear hCross (lsmul ℝ ℝ)).smul (-1)
  have hPressureAmp := (hInv.bilinear hPressureLin (lsmul ℝ ℝ)).smul (-2)
  have hPressureSrc := hInv.bilinear hDot (lsmul ℝ ℝ)
  have hTime := (hTimeLinear.mono_power (d' := 6) (by decide)).sub hTimeCubic
  have hV : RelayTimeFamily (q := q) (C := C) 6
      (fun s t x => hierarchyRelayPotentialCoefficient (s.k t x)) := by
    apply (hPot.mono_power (d' := 6) (by decide)).congr
    intro s t x
    simp [hierarchyRelayPotentialCoefficient, RelayTimeInput.reciprocal, relayCrossMap_apply, smul_smul]
  have hW : RelayTimeFamily (q := q) (C := C) 6
      (fun s t x => hierarchyRelayTimeAmplitudeCoefficient (s.M t x) (s.k t x)) := by
    apply hTime.congr
    intro s t x
    simp only [hierarchyRelayTimeAmplitudeCoefficient, RelayTimeInput.reciprocal, relayCrossMap_apply,
      lsmul_apply, compL_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply,
      Adj, Dot, evV, evR, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, smul_smul, smul_eq_mul]
    congr 2
    change 2 * ((‖s.k t x‖ ^ 2)⁻¹ * (‖s.k t x‖ ^ 2)⁻¹ *
      ⟪s.k t x, s.M t x (s.k t x)⟫_ℝ) =
      2 * ⟪s.k t x, s.M t x (s.k t x)⟫_ℝ / (‖s.k t x‖ ^ 2) ^ 2
    rw [div_eq_mul_inv, ← inv_pow, pow_two]
    ring
  have hP : RelayTimeFamily (q := q) (C := C) 6
      (fun s t x => hierarchyRelayPressureAmplitudeCoefficient (s.M t x) (s.k t x)) := by
    apply (hPressureAmp.mono_power (d' := 6) (by decide)).congr
    intro s t x
    simp [hierarchyRelayPressureAmplitudeCoefficient, RelayTimeInput.reciprocal, Dot, smul_smul]
  have hQ : RelayTimeFamily (q := q) (C := C) 6
      (fun s t x => hierarchyRelayPressureSourceCoefficient (s.k t x)) := by
    exact (hPressureSrc.mono_power (d' := 6) (by decide)).congr (fun _ _ _ => rfl)
  obtain ⟨KV, hKV, hV⟩ := hV
  obtain ⟨KW, hKW, hW⟩ := hW
  obtain ⟨KP, hKP, hP⟩ := hP
  obtain ⟨KQ, hKQ, hQ⟩ := hQ
  let K (n : ℕ) := KV n + KW n + KP n + KQ n
  refine ⟨K, fun n => add_nonneg (add_nonneg (add_nonneg (hKV n) (hKW n)) (hKP n)) (hKQ n), ?_⟩
  intro T D A M k hT hD hA hMreg hkreg hkne hMb hkb hInvb B V W P Q
  let d : RelayTimeInput q C := ⟨T, D, A, M, k, hT, hD, hA, hMreg, hkreg, hkne, hMb, hkb, hInvb⟩
  have hD₀ := zero_le_one.trans hD
  have hB : 0 ≤ B := pow_nonneg (zero_le_one.trans hA) _
  refine ⟨⟨(hV d).1, (hV d).2.mono_constant hD₀ hB ?_⟩,
    ⟨(hW d).1, (hW d).2.mono_constant hD₀ hB ?_⟩,
    ⟨(hP d).1, (hP d).2.mono_constant hD₀ hB ?_⟩,
    ⟨(hQ d).1, (hQ d).2.mono_constant hD₀ hB ?_⟩⟩ <;>
      intro n <;> dsimp only [K] <;> linarith [hKV n, hKW n, hKP n, hKQ n]

end

end TorusEuler
