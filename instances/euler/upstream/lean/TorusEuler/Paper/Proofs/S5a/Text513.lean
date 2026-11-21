import TorusEuler.Paper.S5.Statements
import TorusEuler.Paper.S5.TextStatements
import TorusEuler.Paper.S34A.Statements
import TorusEuler.Paper.SBD.Statements
import TorusEuler.Paper.Proofs.S5a.Proposition51
import TorusEuler.Paper.Proofs.S5a.Library.KOmegaPower

/-!
# Proof of the display (5.13) (thresholds for the mean coefficients)

`sections/06d_mean_estimates.tex:30-45` (latest numbering (5.13)). The coefficients
`K = (D_aX)ᵀ D_aX` and `Ω = (D_aX)ᵀ(Mᵀ - M)D_aX` of (4.1) are products of the coefficients of
Proposition 5.1, so they satisfy (D.6) (Lemma D.2(a), hypothesis `hD_2`, on the (D.6) jets of
`D_aX` and `M` from `h5_1`); the first bound of (D.2) (`hText_eq_D_2`) trades the half-Hölder
norm for sup norms at the cost `ℓ_*^{-1/2}`, Lemma D.2(c) bounds these by `ℓ_*`, and the choice
of the floor `a₀` for the exponent `a` of `ℓ_* = 𝖣^{-a}` gives the second inequality.
-/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

noncomputable section

open AppendixD HierarchyTwistedProfile Lib.S5a

namespace Lib.S5a

/-- (D.6) bounds every coefficient norm: all jet suprema of all orders are finite. -/
theorem coefficientNormFinite_of_power {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {C : ℕ → ℝ} {D : ℝ} {a : ℕ} {c : I → Vec3 → X} (hc : CoefficientPower C D a c) (n : ℕ) :
    CoefficientNormFinite n c := by
  refine ⟨hc.1, fun w hw => ?_⟩
  rw [mem_hierarchyAdmissibleWords] at hw
  refine hc.2.1 w.length w ?_
  unfold appendixCoefficientOrderWords
  exact Finset.mem_filter.mpr ⟨mem_hierarchyAdmissibleWords.mpr ⟨le_rfl, hw.2⟩, rfl⟩

/-- The finite norm (D.1) of a coefficient is bounded by the (5.8)-type sums of spatial suprema:
if `∑_{j ≤ n} ℓ^j ‖∂^j c(t)‖_∞ ≤ S` for every `t` (and `S ≥ 0`), then
`‖c‖_{[n]} ≤ (∑_{m ≤ n} #words(m)) · S`. -/
theorem coefficientNorm_le_of_spatialSup {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {c : I → Vec3 → X} {ℓ S : ℝ} (hℓ : 0 < ℓ) (hS0 : 0 ≤ S) (hc : ∀ t, ContDiff ℝ ∞ (c t))
    (hbdd : ∀ m t, BddAbove (Set.range fun b => ‖iteratedFDeriv ℝ m (c t) b‖)) (n : ℕ)
    (hS : ∀ t, (∑ j ∈ Finset.range (n + 1), ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (c t))) ≤ S) :
    AppendixD.coefficientNorm ℓ n c ≤
      (∑ m ∈ Finset.range (n + 1), ((appendixCoefficientOrderWords m).card : ℝ)) * S := by
  have hterm (m : ℕ) (hm : m ≤ n) (w : List (Fin 3)) (hw : w ∈ appendixCoefficientOrderWords m) :
      ℓ ^ m * sSup (hierarchyJetValues False (hierarchyLabelDirection 1) w c) ≤ S := by
    have hlen := (Finset.mem_filter.mp hw).2
    have hpos : 0 < ℓ ^ m := pow_pos hℓ m
    have hb : ∀ y ∈ hierarchyJetValues False (hierarchyLabelDirection 1) w c, y ≤ S / ℓ ^ m := by
      rintro y (rfl | ⟨t, x, rfl⟩ | ⟨hH, _⟩)
      · exact div_nonneg hS0 hpos.le
      · rw [labelWord_eq_iteratedFDeriv (hc t)]
        refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
        have hprod : ∏ i, ‖coordinateDirection (w.get i)‖ = 1 := by
          simp [coordinateDirection]
        rw [hprod, mul_one, le_div_iff₀ hpos, mul_comm]
        have hnn (i : ℕ) : 0 ≤ ℓ ^ i * spatialSupNorm (iteratedFDeriv ℝ i (c t)) :=
          mul_nonneg (pow_nonneg hℓ.le _)
            ((norm_nonneg _).trans (le_ciSup (hbdd i t) 0))
        calc ℓ ^ m * ‖iteratedFDeriv ℝ w.length (c t) x‖
            = ℓ ^ m * ‖iteratedFDeriv ℝ m (c t) x‖ := by rw [hlen]
          _ ≤ ℓ ^ m * spatialSupNorm (iteratedFDeriv ℝ m (c t)) :=
              mul_le_mul_of_nonneg_left (le_ciSup (hbdd m t) x) hpos.le
          _ ≤ ∑ j ∈ Finset.range (n + 1), ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (c t)) :=
              Finset.single_le_sum (f := fun j => ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (c t)))
                (fun i _ => hnn i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
          _ ≤ S := hS t
      · exact hH.elim
    have := csSup_le (⟨0, Or.inl rfl⟩ :
      (hierarchyJetValues False (hierarchyLabelDirection 1) w c).Nonempty) hb
    rw [le_div_iff₀ hpos, mul_comm] at this
    exact this
  unfold AppendixD.coefficientNorm
  calc ∑ m ∈ Finset.range (n + 1), ℓ ^ m * AppendixD.coefficientOrderNorm m c
      ≤ ∑ m ∈ Finset.range (n + 1), ((appendixCoefficientOrderWords m).card : ℝ) * S := by
        refine Finset.sum_le_sum fun m hm => ?_
        unfold AppendixD.coefficientOrderNorm
        rw [Finset.mul_sum]
        calc _ ≤ ∑ _w ∈ appendixCoefficientOrderWords m, S :=
              Finset.sum_le_sum fun w hw => hterm m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) w hw
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [Finset.sum_mul]

/-- Algebra: `ℓ^{-1/2} (x ℓ) = x ℓ^{1/2}`. -/
theorem inv_sqrt_mul_self {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) : (Real.sqrt ℓ)⁻¹ * (x * ℓ) = x * Real.sqrt ℓ := by
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ
  have h2 : Real.sqrt ℓ * Real.sqrt ℓ = ℓ := Real.mul_self_sqrt hℓ.le
  calc (Real.sqrt ℓ)⁻¹ * (x * ℓ) = (Real.sqrt ℓ)⁻¹ * (x * (Real.sqrt ℓ * Real.sqrt ℓ)) := by rw [h2]
    _ = x * Real.sqrt ℓ := by field_simp

end Lib.S5a

/-- Proof of the display **(5.13)** (`cc:uf:mean:thresholds`), following
`sections/06d_mean_estimates.tex:30-45`.

* `h5_1`, `hD_2`: (D.6) for `K` and `Ω` (`Lib.S5a.exists_KOmega_power`: Proposition 5.1 for `D_aX`
  and `M`, Lemma D.2(a) for the three products, TeX 30-33).
* `hD_2`: Lemma D.2(c) for the bound `ℓ_*^m |c|_m ≤ C_m 𝖣^{2C} ℓ_*` of `K` and `Ω` (TeX 38-41).
* `hText_eq_D_2`: the first bound of (D.2) for `K` and `Ω` (TeX 38-41).

Theorem 4.2 enters the text only through the constant `A` (4.10) and the comparison `A ≤ 𝖣^C`
(TeX 34-38); the display is stated for every `A ∈ (0, 𝖣^{C_A}]`, so that step is not part of this
node (it belongs to Text (5.14)); Theorem 4.2 is notation only for this node (D18). -/
theorem Proof.Text.eq_5_13_of (h5_1 : Statement.proposition_5_1)
    (hD_2 : Statement.lemma_D_2) (hText_eq_D_2 : Statement.Text.eq_D_2) :
    Statement.Text.eq_5_13 := by
  intro CA
  obtain ⟨CK, CO, A1, A2, hCK, hCO, hKO⟩ := Lib.S5a.exists_KOmega_power h5_1 hD_2
  obtain ⟨E1, hE1, hc1⟩ := hD_2.2.2 (Vec3 →L[ℝ] Vec3) CK A1
  obtain ⟨E2, hE2, hc2⟩ := hD_2.2.2 (Vec3 →L[ℝ] Vec3) CO A2
  let aT := max A1 A2
  refine ⟨2 * (CA + 2 * aT) + aT, fun a ha => ⟨2 * aT, fun m => 4 * (E1 m + E1 (m + 1) + E2 m +
    E2 (m + 1)), ?_⟩⟩
  intro T U X pU D lam hT hP A hA hAD ℓ Kin Om m hm
  have hD2 : 2 ≤ D := hP.scale_ge_two
  have hD1 : 1 ≤ D := by linarith
  have hD₀ : 0 < D := by linarith
  have hℓdef : ℓ = (D ^ a)⁻¹ := rfl
  have hℓ0 : 0 < ℓ := by rw [hℓdef]; positivity
  have hℓa (j : ℕ) (hj : j ≤ a) : ℓ ≤ (D ^ j)⁻¹ := by
    rw [hℓdef]; exact inv_anti₀ (pow_pos hD₀ _) (pow_le_pow_right₀ hD1 hj)
  have hℓ1 : ℓ ≤ 1 := by
    have := hℓa 0 (Nat.zero_le _)
    simpa using this
  let I := ↥(Icc (0 : ℝ) T)
  have hPK : CoefficientPower CK D A1 Kin := (hKO hT hP).1
  have hPO : CoefficientPower CO D A2 Om := (hKO hT hP).2
  have hℓ1' : ℓ ≤ (D ^ A1)⁻¹ := hℓa _ (by omega)
  have hℓ2' : ℓ ≤ (D ^ A2)⁻¹ := hℓa _ (by omega)
  have hbK := (hText_eq_D_2 I (Vec3 →L[ℝ] Vec3) ℓ hℓ0 hℓ1 _).1 m
    (coefficientNormFinite_of_power hPK (m + 1))
  have hbO := (hText_eq_D_2 I (Vec3 →L[ℝ] Vec3) ℓ hℓ0 hℓ1 _).1 m
    (coefficientNormFinite_of_power hPO (m + 1))
  have hm1 : 1 ≤ m + 1 := by omega
  have hK1 := ((hc1 I D ℓ hD1 hℓ0 hℓ1' _ hPK).2 m hm)
  have hK2 := ((hc1 I D ℓ hD1 hℓ0 hℓ1' _ hPK).2 (m + 1) hm1)
  have hO1 := ((hc2 I D ℓ hD1 hℓ0 hℓ2' _ hPO).2 m hm)
  have hO2 := ((hc2 I D ℓ hD1 hℓ0 hℓ2' _ hPO).2 (m + 1) hm1)
  have hs0 : 0 ≤ Real.sqrt ℓ := Real.sqrt_nonneg _
  have hsi : 0 ≤ (Real.sqrt ℓ)⁻¹ := inv_nonneg.mpr hs0
  have hpow1 : D ^ (2 * A1) ≤ D ^ (2 * aT) :=
    pow_le_pow_right₀ hD1 (by omega)
  have hpow2 : D ^ (2 * A2) ≤ D ^ (2 * aT) :=
    pow_le_pow_right₀ hD1 (by omega)
  have key (E : ℕ → ℝ) (hE : ∀ n, 0 ≤ E n) (c : I → Vec3 → (Vec3 →L[ℝ] Vec3)) (p : ℕ)
      (hb : ℓ ^ m * holderOrderNorm m c ≤ 4 * (Real.sqrt ℓ)⁻¹ *
        (ℓ ^ m * coefficientOrderNorm m c + ℓ ^ (m + 1) * coefficientOrderNorm (m + 1) c))
      (h1 : ℓ ^ m * coefficientOrderNorm m c ≤ E m * D ^ p * ℓ)
      (h2 : ℓ ^ (m + 1) * coefficientOrderNorm (m + 1) c ≤ E (m + 1) * D ^ p * ℓ) :
      ℓ ^ m * holderOrderNorm m c ≤ 4 * (E m + E (m + 1)) * D ^ p * Real.sqrt ℓ := by
    calc ℓ ^ m * holderOrderNorm m c
        ≤ 4 * (Real.sqrt ℓ)⁻¹ * (ℓ ^ m * coefficientOrderNorm m c +
          ℓ ^ (m + 1) * coefficientOrderNorm (m + 1) c) := hb
      _ ≤ 4 * (Real.sqrt ℓ)⁻¹ * (E m * D ^ p * ℓ + E (m + 1) * D ^ p * ℓ) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
      _ = 4 * ((Real.sqrt ℓ)⁻¹ * ((E m + E (m + 1)) * D ^ p * ℓ)) := by ring
      _ = _ := by rw [inv_sqrt_mul_self hℓ0]; ring
  have hKb := key E1 hE1 _ (2 * A1) hbK.2 hK1 hK2
  have hOb := key E2 hE2 _ (2 * A2) hbO.2 hO1 hO2
  have hpos1 : 0 ≤ 4 * (E1 m + E1 (m + 1)) := by have := hE1 m; have := hE1 (m + 1); positivity
  have hpos2 : 0 ≤ 4 * (E2 m + E2 (m + 1)) := by have := hE2 m; have := hE2 (m + 1); positivity
  have hKb' : 4 * (E1 m + E1 (m + 1)) * D ^ (2 * A1) * Real.sqrt ℓ ≤
      4 * (E1 m + E1 (m + 1)) * D ^ (2 * aT) * Real.sqrt ℓ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow1 hpos1) hs0
  have hOb' : 4 * (E2 m + E2 (m + 1)) * D ^ (2 * A2) * Real.sqrt ℓ ≤
      4 * (E2 m + E2 (m + 1)) * D ^ (2 * aT) * Real.sqrt ℓ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow2 hpos2) hs0
  have hCm : 0 ≤ 4 * (E1 m + E1 (m + 1) + E2 m + E2 (m + 1)) := by
    have := hE1 m; have := hE1 (m + 1); have := hE2 m; have := hE2 (m + 1); positivity
  refine ⟨fun w hw => ⟨hbK.1 w hw, hbO.1 w hw⟩, ?_, ?_⟩
  · rw [mul_add]
    calc _ ≤ 4 * (E1 m + E1 (m + 1)) * D ^ (2 * aT) * Real.sqrt ℓ +
          4 * (E2 m + E2 (m + 1)) * D ^ (2 * aT) * Real.sqrt ℓ :=
        add_le_add (hKb.trans hKb') (hOb.trans hOb')
      _ = _ := by ring
  · have hsq : Real.sqrt ℓ ≤ (D ^ (CA + 2 * aT))⁻¹ := by
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      have h := hℓa ((CA + 2 * aT) * 2) (by omega)
      rw [inv_pow, ← pow_mul]
      exact h
    have hAD' : A * D ^ (2 * aT) ≤ D ^ (CA + 2 * aT) := by
      rw [pow_add]
      exact mul_le_mul_of_nonneg_right hAD (by positivity)
    have hone : A * D ^ (2 * aT) * Real.sqrt ℓ ≤ 1 := by
      calc A * D ^ (2 * aT) * Real.sqrt ℓ ≤ D ^ (CA + 2 * aT) * (D ^ (CA + 2 * aT))⁻¹ :=
            mul_le_mul hAD' hsq hs0 (by positivity)
        _ = 1 := mul_inv_cancel₀ (by positivity)
    rw [le_div_iff₀ hA]
    calc 4 * (E1 m + E1 (m + 1) + E2 m + E2 (m + 1)) * D ^ (2 * aT) * Real.sqrt ℓ * A
        = 4 * (E1 m + E1 (m + 1) + E2 m + E2 (m + 1)) * (A * D ^ (2 * aT) * Real.sqrt ℓ) := by ring
      _ ≤ 4 * (E1 m + E1 (m + 1) + E2 m + E2 (m + 1)) * 1 := mul_le_mul_of_nonneg_left hone hCm
      _ = _ := mul_one _

end

end TorusEuler.Paper
