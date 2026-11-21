import TorusEuler.Paper.S5.Statements
import TorusEuler.Paper.S5.TextStatements
import TorusEuler.Paper.SBD.Statements
import TorusEuler.Paper.Proofs.S5a.Proposition51
import TorusEuler.Paper.Proofs.S5a.Text513
import TorusEuler.Paper.Proofs.S5a.Library.Launch
import TorusEuler.Paper.Proofs.S5a.Library.MeanUnique
import TorusEuler.Paper.Proofs.S5a.Library.Norm52

/-!
# Proof of Proposition 5.2 (columns of the mean equation)

`sections/06d_mean_estimates.tex:22-65` (latest numbering (5.12) with the displays (5.13), (5.14)).
After the display (5.14) (`hText_eq_5_14`, the Hölder bound for the velocity `v = z_t` of the
solution of (4.9)) the proof of the text uses only Proposition 5.1 (the coefficients `D_aX`
give the bounds (5.8)), (D.2) and (D.4): lines 59-65.
-/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

noncomputable section

open AppendixD HierarchyTwistedProfile Lib.S5a

/-- Proof of **Proposition 5.2** (`cc:uf:mean:columns`), following `sections/06d_mean_estimates.tex:59-65`.

* `hText_eq_5_14`: the Hölder estimate `‖v‖_{[n],1/2} ≤ C_n 𝖣^C ‖g‖_{[n],1/2}` of (5.14) for the
  velocity `v` of the solution (`MeanSolution.endpoint`), `g = (D_aX)ᵀ f̄` (TeX 56-58).
* `h5_1`: its bound (5.8) for `D_aX` (TeX 59-60: `‖D_aX‖_{[n],1/2} ≤ C_n ℓ_*^{-1/2} 𝖣^C`, at
  `ℓ = ℓ_* ≤ 𝖣^{-C}`); the transpose has the same norms (adjoint isometry). Its (D.6) clause only
  supplies the finiteness of the jet suprema used to pass to the word norms of (D.1).
* `hText_eq_D_2`: the comparisons (D.2) of the norms `‖·‖_{[n]}`, `‖·‖_{[n],1/2}` (second line of (D.2), the "hence" comparisons: `‖c‖_{[n],1/2} ≤ 4ℓ^{-1/2}‖c‖_{[n+1]}` for `g` and `D_aX`, TeX 59-60, and `‖B‖_{[n]} ≤ ‖B‖_{[n],1/2}`, TeX 64).
* `hD_1`: the product estimates (D.4), in `‖·‖_{[n],1/2}` for `B = D_aX v` (TeX 61-62) and in
  `‖·‖_{[n+1]}` for `g = (D_aX)ᵀ f̄`.
  The TeX (61-64) applies the Hölder product to `g` and then (D.2) to `f̄`; here the sup-norm product at order `n+1`
  (with (5.8) for `(D_aX)ᵀ`) comes first and (D.2) is applied to `g`, at the same cost.

Theorem 4.2, Lemmas D.2, D.3 and (5.13) enter only through the display (5.14) (TeX 30-58), which the
node Text eq_5_14 proves (D17). `Lib.S5a.exists_launch` only supplies the launch that the statement of
Proposition 5.1 requires; the coefficients do not depend on it. -/
theorem Proof.proposition_5_2_of (h5_1 : Statement.proposition_5_1) (hD_1 : Statement.lemma_D_1)
    (hText_eq_D_2 : Statement.Text.eq_D_2)
    (hText_eq_5_14 : Statement.Text.eq_5_14) : Statement.proposition_5_2 := by
  obtain ⟨a₀E, hE⟩ := hText_eq_5_14
  obtain ⟨C, Kc, hK⟩ := h5_1
  obtain ⟨Kf, hKf⟩ := hK (fun _ => 0)
  let W (m : ℕ) : ℝ := ((appendixCoefficientOrderWords m).card : ℝ)
  let CF (m : ℕ) : ℝ := W m * max (Kc m) 0
  let E1 (m : ℕ) : ℝ := (∑ i ∈ Finset.range (m + 1), W i) * max (Kc m) 0
  have hE1 (m : ℕ) : 0 ≤ E1 m :=
    mul_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (le_max_right _ _)
  let Bop : (Vec3 →L[ℝ] Vec3) →L[ℝ] Vec3 →L[ℝ] Vec3 :=
    (ContinuousLinearMap.apply ℝ Vec3 : Vec3 →L[ℝ] (Vec3 →L[ℝ] Vec3) →L[ℝ] Vec3).flip
  let P3 (n : ℕ) : ℝ := ((hierarchyAdmissibleWords (Fin 3) n).card * (2 : ℝ) ^ n * (2 * ‖Bop‖))
  let P4 (n : ℕ) : ℝ := ((hierarchyAdmissibleWords (Fin 4) n).card * (2 : ℝ) ^ n * (2 * ‖Bop‖))
  have hP3 (n : ℕ) : 0 ≤ P3 n := by positivity
  have hP4 (n : ℕ) : 0 ≤ P4 n := by positivity
  refine ⟨max a₀E C, fun a ha => ?_⟩
  obtain ⟨CE, CnE, hEa⟩ := hE a (le_trans (le_max_left _ _) ha)
  refine ⟨2 * a + 2 * C + CE, fun n => P3 n * (4 * E1 (n + 1)) *
    (max (CnE n) 0 * (4 * (P4 (n + 1) * E1 (n + 1)))), ?_⟩
  intro T hT U X pU k D lam d hP f B q hs n
  have hD2 : 2 ≤ D := hP.scale_ge_two
  have hD1 : 1 ≤ D := by linarith
  have hD₀ : 0 < D := by linarith
  obtain ⟨k', t₀, hL⟩ := Lib.S5a.exists_launch hT hP
  have hD6 := (hKf hT hP hL).1
  have h58 := (hKf hT hP hL).2.2
  set ℓ := S5.radius D a with hℓdef'
  have hℓdef : ℓ = (D ^ a)⁻¹ := rfl
  have hℓ0 : 0 < ℓ := by rw [hℓdef]; positivity
  have hℓa (j : ℕ) (hj : j ≤ a) : ℓ ≤ (D ^ j)⁻¹ := by
    rw [hℓdef]; exact inv_anti₀ (pow_pos hD₀ _) (pow_le_pow_right₀ hD1 hj)
  have hℓ1 : ℓ ≤ 1 := by
    have := hℓa 0 (Nat.zero_le _)
    simpa using this
  have hℓC : ℓ ≤ (D ^ C)⁻¹ := hℓa C (le_trans (le_max_right _ _) ha)
  have hsqrt : (Real.sqrt ℓ)⁻¹ ≤ D ^ a := by
    have hs0 : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ0
    have hsle : Real.sqrt ℓ ≤ 1 := Real.sqrt_le_iff.mpr ⟨zero_le_one, by simpa using hℓ1⟩
    have hmul : Real.sqrt ℓ * Real.sqrt ℓ = ℓ := Real.mul_self_sqrt hℓ0.le
    have hle : ℓ ≤ Real.sqrt ℓ := by nlinarith
    calc (Real.sqrt ℓ)⁻¹ ≤ ℓ⁻¹ := inv_anti₀ hℓ0 hle
      _ = D ^ a := by rw [hℓdef, inv_inv]
  have hXsmooth (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (X 0 t) :=
    contDiff_infty.mpr fun j =>
      (hP.flow.labelJets_evolve j hT hP.velocity_smooth hP.velocity_periodic).1 t ht
  let I := ↥(Icc (0 : ℝ) T)
  let cF : I → Vec3 → (Vec3 →L[ℝ] Vec3) := fun t a => fderiv ℝ (X 0 t) a
  let cFt : I → Vec3 → (Vec3 →L[ℝ] Vec3) := fun t a => (cF t a).adjoint
  let J := ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)
  have hFs (t : I) : ContDiff ℝ ∞ (cF t) := (contDiff_infty_iff_fderiv.mp (hXsmooth t t.2)).2
  have hFts (t : I) : ContDiff ℝ ∞ (cFt t) := J.toContinuousLinearEquiv.contDiff.comp (hFs t)
  have hjF (m : ℕ) (t : I) (x : Vec3) :
      ‖iteratedFDeriv ℝ m (cF t) x‖ ≤ Kc m * D ^ (C * (m + 1)) := (hD6 m t t.2 x).1
  have hPF : CoefficientPower CF D C cF :=
    coefficientPower_of_jets_max hD₀.le hFs hjF
  have hPFt : CoefficientPower CF D C cFt := by
    refine coefficientPower_of_jets_max hD₀.le hFts fun m t x => ?_
    change ‖iteratedFDeriv ℝ m (J ∘ cF t) x‖ ≤ _
    rw [J.norm_iteratedFDeriv_comp_left (cF t) x m]
    exact hjF m t x
  -- the solution
  obtain ⟨v, z, hv, -, hper, -, -, -, -, hvB⟩ := hs.endpoint
  have hperv : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (v t) := fun t ht => (hper t ht).1
  have hf0 : ∀ t ∈ Icc 0 T, ∀ a s, f.val.val.val (t, a, s) = f.val.val.val (t, a, 0) := by
    intro t ht a s
    rw [Lib.S5a.momentum_eval d hs ht a s, Lib.S5a.momentum_eval d hs ht a 0]
  have hB0 : ∀ t ∈ Icc 0 T, ∀ a s, B.val.val.val (t, a, s) = B.val.val.val (t, a, 0) := by
    intro t ht a s
    rw [hvB t ht a s, hvB t ht a 0]
  let f0 : I → Vec3 → Vec3 := fun t a => f.val.val.val ((t : ℝ), a, 0)
  let B0 : I → Vec3 → Vec3 := fun t a => B.val.val.val ((t : ℝ), a, 0)
  let vI : I → Vec3 → Vec3 := fun t => v t.val
  let g : I → Vec3 → Vec3 := fun t x =>
    (meanDeformation X t.val x).adjoint (f.val.val.val (t.val, x, 0))
  let gB : I → Vec3 → Vec3 := fun t x => Bop (cFt t x) (f0 t x)
  have hgB : g = gB := by
    funext t x
    simp [g, gB, Bop, cFt, cF, f0, meanDeformation]
  have hB0eq : B0 = fun t x => Bop (cF t x) (vI t x) := by
    funext t x
    simp only [B0, vI, Bop, cF]
    rw [hvB t t.2 x 0]
    rfl
  -- finiteness of the coefficient norms of `f0`, `B0`
  have hlift (F : HierarchyTwistedProfile T k Vec3)
      (hF : ∀ t ∈ Icc 0 T, ∀ a s, F.val.val.val (t, a, s) = F.val.val.val (t, a, 0)) :
      CoefficientNormFinite (n + 1) (fun (t : I) a => F.val.val.val ((t : ℝ), a, 0)) := by
    have hs' : Bridge.slices (Icc 0 T) F = fun (t : I) (x : Vec3 × ℝ) =>
        (fun (t : I) a => F.val.val.val ((t : ℝ), a, 0)) t x.1 := by
      funext t x
      exact hF t t.property x.1 x.2
    have h := Bridge.fieldNormFinite_slices hT 1 1 (n + 1) (subset_refl (Icc 0 T)) F
    rw [hs'] at h
    exact coefficientNormFinite_of_lift one_pos h
  have hf0fin : CoefficientNormFinite (n + 1) f0 := hlift f hf0
  have hB0fin : CoefficientNormFinite (n + 1) B0 := hlift B hB0
  have hU : S5.uNorm ℓ (S5.width lam) n B = coefficientNorm ℓ n B0 :=
    Bridge.uNorm_eq_coefficientNorm hℓ0.le _ n hB0
  have hUf : S5.uNorm ℓ (S5.width lam) (n + 1) f = coefficientNorm ℓ (n + 1) f0 :=
    Bridge.uNorm_eq_coefficientNorm hℓ0.le _ (n + 1) hf0
  -- the norms of `D_aX` and its transpose
  have hsF (t : I) : (∑ j ∈ Finset.range (n + 1 + 1),
      ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (cF t))) ≤ max (Kc (n + 1)) 0 * D ^ C :=
    (h58 ℓ hℓ0 hℓC (n + 1) t t.2).1.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hbF (m : ℕ) (t : I) : BddAbove (range fun b => ‖iteratedFDeriv ℝ m (cF t) b‖) :=
    ⟨_, by rintro _ ⟨b, rfl⟩; exact hjF m t b⟩
  have hnormFt (m : ℕ) (t : I) (b : Vec3) :
      ‖iteratedFDeriv ℝ m (cFt t) b‖ = ‖iteratedFDeriv ℝ m (cF t) b‖ := by
    change ‖iteratedFDeriv ℝ m (J ∘ cF t) b‖ = _
    exact J.norm_iteratedFDeriv_comp_left (cF t) b m
  have hsFt (t : I) : (∑ j ∈ Finset.range (n + 1 + 1),
      ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (cFt t))) ≤ max (Kc (n + 1)) 0 * D ^ C := by
    refine le_trans (le_of_eq ?_) (hsF t)
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold spatialSupNorm
    simp only [hnormFt]
  have hbFt (m : ℕ) (t : I) : BddAbove (range fun b => ‖iteratedFDeriv ℝ m (cFt t) b‖) := by
    simpa only [hnormFt] using hbF m t
  have hS0 : 0 ≤ max (Kc (n + 1)) 0 * D ^ C :=
    mul_nonneg (le_max_right _ _) (by positivity)
  have hcF : coefficientNorm ℓ (n + 1) cF ≤ E1 (n + 1) * D ^ C := by
    have := coefficientNorm_le_of_spatialSup hℓ0 hS0 hFs hbF (n + 1) hsF
    simpa only [E1, W, mul_assoc] using this
  have hcFt : coefficientNorm ℓ (n + 1) cFt ≤ E1 (n + 1) * D ^ C := by
    have := coefficientNorm_le_of_spatialSup hℓ0 hS0 hFts hbFt (n + 1) hsFt
    simpa only [E1, W, mul_assoc] using this
  -- the product `g = (D_aX)ᵀ f̄` in `‖·‖_{[n+1]}`
  have hw1 (h : I → Vec3 × ℝ → Vec3) : weighted (fun _ : I => (1 : ℝ)) h = h := by
    funext t x; simp [weighted]
  have hfin_f0 : FieldNormFinite ℓ 1 (n + 1)
      (weighted (fun _ : I => (1 : ℝ)) (fun t (x : Vec3 × ℝ) => f0 t x.1)) := by
    rw [hw1]; exact hf0fin.fieldNormFinite ℓ 1
  have hD4 := (hD_1 I ℓ 1 hℓ0 one_pos (fun _ => (1 : ℝ)) (fun _ => one_pos) (n + 1)).2.1
    (Vec3 →L[ℝ] Vec3) Vec3 Vec3 Bop (fun t (x : Vec3 × ℝ) => cFt t x.1)
    (fun t (x : Vec3 × ℝ) => f0 t x.1)
    ((hPFt.coefficientNormFinite (n + 1)).fieldNormFinite ℓ 1) hfin_f0
  have hgfin' : CoefficientNormFinite (n + 1) gB := by
    have h1 := hD4.1
    rw [hw1] at h1
    exact coefficientNormFinite_of_lift (c := gB) hℓ0 h1
  have hgfin : CoefficientNormFinite (n + 1) g := by rw [hgB]; exact hgfin'
  have e1 : weightedFieldNorm ℓ 1 (fun _ : I => (1 : ℝ)) (n + 1)
      (fun t (x : Vec3 × ℝ) => Bop (cFt t x.1) (f0 t x.1)) = coefficientNorm ℓ (n + 1) gB := by
    unfold weightedFieldNorm
    rw [hw1]
    exact fieldNorm_phaseIndependent (c := gB) hℓ0.le 1 (n + 1) hgfin'.1
  have e2 : fieldNorm ℓ 1 (n + 1) (fun t (x : Vec3 × ℝ) => cFt t x.1) =
      coefficientNorm ℓ (n + 1) cFt := fieldNorm_phaseIndependent hℓ0.le 1 (n + 1) hFts
  have e3 : weightedFieldNorm ℓ 1 (fun _ : I => (1 : ℝ)) (n + 1)
      (fun t (x : Vec3 × ℝ) => f0 t x.1) = coefficientNorm ℓ (n + 1) f0 := by
    unfold weightedFieldNorm
    rw [hw1]
    exact fieldNorm_phaseIndependent (c := f0) hℓ0.le 1 (n + 1) hf0fin.1
  have h2 : coefficientNorm ℓ (n + 1) gB ≤
      P4 (n + 1) * coefficientNorm ℓ (n + 1) cFt * coefficientNorm ℓ (n + 1) f0 := by
    have := hD4.2
    rw [← e1, ← e2, ← e3]
    exact this
  have hUnn : 0 ≤ coefficientNorm ℓ (n + 1) f0 := coefficientNorm_nonneg hℓ0.le _ _
  have hDpow (j : ℕ) : 0 ≤ D ^ j := by positivity
  have hcgb : coefficientNorm ℓ (n + 1) g ≤
      P4 (n + 1) * (E1 (n + 1) * D ^ C) * coefficientNorm ℓ (n + 1) f0 := by
    rw [hgB]
    refine h2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcFt (hP4 _)) hUnn)
  -- the Hölder norm of `g`
  have hDg := (hText_eq_D_2 I Vec3 ℓ hℓ0 hℓ1 g).2 n hgfin
  have hDF := (hText_eq_D_2 I (Vec3 →L[ℝ] Vec3) ℓ hℓ0 hℓ1 cF).2 n
    (hPF.coefficientNormFinite (n + 1))
  have hDB := (hText_eq_D_2 I Vec3 ℓ hℓ0 hℓ1 B0).2 n hB0fin
  -- (5.14)
  have hmain : ∀ n : ℕ, HolderFieldNormFinite ℓ n g →
      HolderFieldNormFinite ℓ n (fun t : Icc (0 : ℝ) T => v t.val) ∧
        holderFieldNorm ℓ n (fun t : Icc (0 : ℝ) T => v t.val) ≤
          CnE n * D ^ CE * holderFieldNorm ℓ n g :=
    hEa hT d hP f B q hs v hv hperv hvB
  obtain ⟨hvfin, hvle⟩ := hmain n hDg.1
  -- the Hölder norm of `D_aX`
  have hHC : holderFieldNorm ℓ n cF ≤ 4 * D ^ a * (E1 (n + 1) * D ^ C) := by
    calc holderFieldNorm ℓ n cF ≤ 4 * (Real.sqrt ℓ)⁻¹ * coefficientNorm ℓ (n + 1) cF := hDF.2.2
      _ ≤ 4 * D ^ a * (E1 (n + 1) * D ^ C) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) hcF
          (coefficientNorm_nonneg hℓ0.le _ _) (by positivity)
  have hCnE : 0 ≤ max (CnE n) 0 := le_max_right _ _
  have hHG : holderFieldNorm ℓ n g ≤ 4 * D ^ a * (P4 (n + 1) * (E1 (n + 1) * D ^ C) *
      coefficientNorm ℓ (n + 1) f0) := by
    calc holderFieldNorm ℓ n g ≤ 4 * (Real.sqrt ℓ)⁻¹ * coefficientNorm ℓ (n + 1) g := hDg.2.2
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) hcgb
        (coefficientNorm_nonneg hℓ0.le _ _) (by positivity)
  have hHV : holderFieldNorm ℓ n (fun t : Icc (0 : ℝ) T => v t.val) ≤
      max (CnE n) 0 * D ^ CE * (4 * D ^ a * (P4 (n + 1) * (E1 (n + 1) * D ^ C) *
        coefficientNorm ℓ (n + 1) f0)) := by
    refine hvle.trans ?_
    calc CnE n * D ^ CE * holderFieldNorm ℓ n g
        ≤ max (CnE n) 0 * D ^ CE * holderFieldNorm ℓ n g :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (hDpow _))
            (holderFieldNorm_nonneg _ _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hHG (mul_nonneg hCnE (hDpow _))
  -- the product `B = D_aX v` in `‖·‖_{[n],1/2}`
  have hD4h := (hD_1 I ℓ 1 hℓ0 one_pos (fun _ => (1 : ℝ)) (fun _ => one_pos) n).2.2.2
    (Vec3 →L[ℝ] Vec3) Vec3 Vec3 Bop cF vI hDF.1 hvfin
  have hBH : holderFieldNorm ℓ n B0 ≤ P3 n * holderFieldNorm ℓ n cF *
      holderFieldNorm ℓ n (fun t : Icc (0 : ℝ) T => v t.val) := by
    rw [hB0eq]; exact hD4h.2
  rw [hU]
  have hb1 : 0 ≤ 4 * D ^ a * (E1 (n + 1) * D ^ C) := mul_nonneg (by positivity) (mul_nonneg (hE1 (n + 1)) (by positivity))
  calc coefficientNorm ℓ n B0 ≤ holderFieldNorm ℓ n B0 := hDB.2.1
    _ ≤ P3 n * holderFieldNorm ℓ n cF *
      holderFieldNorm ℓ n (fun t : Icc (0 : ℝ) T => v t.val) := hBH
    _ ≤ P3 n * (4 * D ^ a * (E1 (n + 1) * D ^ C)) *
      (max (CnE n) 0 * D ^ CE * (4 * D ^ a * (P4 (n + 1) * (E1 (n + 1) * D ^ C) *
        coefficientNorm ℓ (n + 1) f0))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hHC (hP3 _)) hHV (holderFieldNorm_nonneg _ _ _)
        (mul_nonneg (hP3 _) hb1)
    _ = _ := by rw [hUf]; ring

end

end TorusEuler.Paper
