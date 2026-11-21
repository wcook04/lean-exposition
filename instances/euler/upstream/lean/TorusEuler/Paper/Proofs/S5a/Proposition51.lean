import TorusEuler.Paper.S5.Statements
import TorusEuler.Paper.SBD.Statements
import TorusEuler.Paper.Proofs.S5a.Library.Jets

/-!
# Proof of Proposition 5.1 from Lemma B.1 and Lemma D.2

`Paper.Proof.proposition_5_1_of` follows the proof of Proposition 5.1
(`sections/05b_parent_coefficients.tex:34-90`):

1. Bernstein's inequality (B.1) of Lemma B.1 for the gradient columns of the parent,
   with (5.1), gives `|U|_k ≤ C_k 𝖣^k` (`Lib.S5a.exists_velocityJets_of_lemmaB1`);
2. the recursion (5.9) gives `|D_aX|_m ≤ C_m 𝖣^{5m+1}` and the chain rule gives
   (5.7) and the bound for `M = ∇U ∘ X` (library `exists_forward_flowJetBounds`,
   `norm_iteratedFDeriv_parentComposition_le`, the row's own content);
3. the product and inverse rules (a), (b) of Lemma D.2 give (D.6) for `(D_aX)⁻¹`,
   `κ/λ = (D_aX)^{-T}k_*/λ`, `|κ/λ|^{-2} = λ²/|κ|²` and `P_κ`;
4. part (c) of Lemma D.2 gives the first bound of (5.8), and the second is
   `ℓ_*^m |f∘X|_m ≤ C_m A_f (𝖣^C ℓ_*)^m`.
-/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)

namespace Lib.S5a

/-- Step 1 of the proof of Proposition 5.1 (`sections/05b_parent_coefficients.tex:35-39`):
Bernstein's inequality (B.1) of Lemma B.1, applied to the gradient columns `∂_i U` of a
field with frequencies at most `4𝖣` (with the fixed symbol `dyadicMultiplierCutoff` and
`Λ = 𝖣`), together with `‖∇U‖_∞ ≤ 𝖣` ((5.1)), gives `‖∇^k U‖ ≤ C_k 𝖣^k` for `k ≥ 1`.
The coordinate sums of (B.1) are converted to operator norms by the symmetry of the
derivatives (`exists_sortedWord`) and `opNorm_le_coordinateSum`.
The constants `V n` depend only on `n` (through the constants of (B.1)). -/
theorem exists_velocityJets_of_lemmaB1 (hB : Statement.lemma_B_1) :
    ∃ V : ℕ → ℝ, (∀ n, 0 ≤ V n) ∧
      ∀ (g : C(Labels, Vec3)) {D : ℝ}, 1 ≤ D → RealTorusFourierBand (4 * D) g →
        ContDiff ℝ ∞ (fun y => g (toUnitTorus y)) →
        (∀ x, ‖fderiv ℝ (fun y => g (toUnitTorus y)) x‖ ≤ D) →
        ∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ x,
          ‖iteratedFDeriv ℝ k (fun y => g (toUnitTorus y)) x‖ ≤ V n * D ^ k := by
  obtain ⟨_, Cb, _, _, hCb, _, hBΛ⟩ := hB _ AppendixB.cutoffSymbol_dyadicMultiplierCutoff
  let K (m : ℕ) : ℝ := (3 : ℝ) ^ m * Cb m
  have hK (m : ℕ) : 0 ≤ K m := mul_nonneg (by positivity) (hCb m)
  let V (n : ℕ) : ℝ := 3 * ∑ j ∈ Finset.range n, K j
  have hV (n : ℕ) : 0 ≤ V n := mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => hK j)
  refine ⟨V, hV, ?_⟩
  intro g D hD hband hu hgradient n k hk hkn x
  have hD₀ : 0 < D := zero_lt_one.trans_le hD
  let u := fun y => g (toUnitTorus y)
  have hcol (i : Fin 3) : ∃ d : C(Labels, Vec3),
      ((fun y => d (toUnitTorus y)) = fun y => fderiv ℝ u y (coordinateDirection i)) ∧
      ∀ m : ℕ, ‖iteratedFDeriv ℝ m (fun y => d (toUnitTorus y)) x‖ ≤ K m * D * D ^ m := by
    obtain ⟨d, hd, hdband, _⟩ := gradientColumnFourierBand g (4 * D) (fun j hj =>
      hband j (lt_of_not_ge fun hj' => hj ((mem_frequencyBand _ _).mpr hj'))) i
    have hdNorm : ‖d‖ ≤ D := (ContinuousMap.norm_le d hD₀.le).mpr fun z => by
      obtain ⟨y, rfl⟩ := toUnitTorus_surjective z
      rw [hd]
      exact ((fderiv ℝ u y).le_opNorm (coordinateDirection i)).trans
        (by simpa [coordinateDirection] using hgradient y)
    have hdlift : (fun y => d (toUnitTorus y)) = fun y => fderiv ℝ u y (coordinateDirection i) :=
      funext hd
    have hdsmooth : ContDiff ℝ ∞ (fun y => d (toUnitTorus y)) := by
      rw [hdlift]
      exact (hu.fderiv_right (by simp)).clm_apply contDiff_const
    have hdR : RealNormedTorusFourierBand (4 * D) d :=
      realNormedTorusFourierBand_of_vector fun j hj =>
        hdband j (fun hj' => (not_lt_of_ge ((mem_frequencyBand _ _).mp hj')) hj)
    refine ⟨d, hdlift, fun m => ?_⟩
    -- (B.1) for the column `d`, at the frequency scale `Λ = 𝖣`
    obtain ⟨hbdd, hsum⟩ := (hBΛ D hD₀).2.2 m Vec3 d hdR
    have hcomp (β : Fin m → Fin 3) :
        ‖iteratedFDeriv ℝ m (fun y => d (toUnitTorus y)) x
          (fun j => coordinateDirection (β j))‖ ≤ Cb m * D ^ m * D := by
      obtain ⟨w, hw, hwx⟩ := exists_sortedWord hdsmooth β
      obtain ⟨β', hβ', hβw⟩ := exists_monotone_of_orderWord hw
      rw [hwx x, ← hβw, ofFnWord_eq_iteratedFDeriv hdsmooth β' x]
      have h1 : ‖iteratedFDeriv ℝ m (fun z => d (toUnitTorus z)) x
            (fun j => EuclideanSpace.single (β' j) 1)‖ ≤
          ⨆ y : Vec3, ‖iteratedFDeriv ℝ m (fun z => d (toUnitTorus z)) y
            (fun j => EuclideanSpace.single (β' j) 1)‖ :=
        le_ciSup (hbdd β') x
      have h2 : (⨆ y : Vec3, ‖iteratedFDeriv ℝ m (fun z => d (toUnitTorus z)) y
            (fun j => EuclideanSpace.single (β' j) 1)‖) ≤
          ∑ γ ∈ Finset.univ.filter (fun γ : Fin m → Fin 3 => Monotone γ), ⨆ y : Vec3,
            ‖iteratedFDeriv ℝ m (fun z => d (toUnitTorus z)) y
              (fun j => EuclideanSpace.single (γ j) 1)‖ :=
        Finset.single_le_sum (f := fun γ : Fin m → Fin 3 => ⨆ y : Vec3,
            ‖iteratedFDeriv ℝ m (fun z => d (toUnitTorus z)) y
              (fun j => EuclideanSpace.single (γ j) 1)‖)
          (fun γ _ => (norm_nonneg _).trans (le_ciSup (hbdd γ) 0))
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hβ'⟩)
      calc
        _ ≤ Cb m * D ^ m * ‖d‖ := h1.trans (h2.trans hsum)
        _ ≤ Cb m * D ^ m * D :=
          mul_le_mul_of_nonneg_left hdNorm (mul_nonneg (hCb m) (pow_nonneg hD₀.le _))
    calc
      _ ≤ ∑ β : Fin m → Fin 3, ‖iteratedFDeriv ℝ m (fun y => d (toUnitTorus y)) x
            (fun j => coordinateDirection (β j))‖ := opNorm_le_coordinateSum _
      _ ≤ ∑ _β : Fin m → Fin 3, Cb m * D ^ m * D := Finset.sum_le_sum fun β _ => hcomp β
      _ = K m * D * D ^ m := by simp [K, Finset.card_univ]; ring
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  change ‖iteratedFDeriv ℝ (m + 1) u x‖ ≤ _
  rw [← norm_iteratedFDeriv_fderiv]
  refine ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (hV n) (pow_nonneg hD₀.le _))
    fun v => ?_
  let J := iteratedFDeriv ℝ m (fderiv ℝ u) x
  have hdf : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hProd : 0 ≤ ∏ a, ‖v a‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hColJet (i : Fin 3) : ‖J v (coordinateDirection i)‖ ≤
      (K m * D * D ^ m) * ∏ a, ‖v a‖ := by
    obtain ⟨d, hd, hbound⟩ := hcol i
    let E := ContinuousLinearMap.apply ℝ Vec3 (coordinateDirection i)
    have heq : iteratedFDeriv ℝ m (fun y => d (toUnitTorus y)) x v =
        J v (coordinateDirection i) := by
      rw [show (fun y => d (toUnitTorus y)) = E ∘ fderiv ℝ u from hd]
      rw [E.iteratedFDeriv_comp_left hdf.contDiffAt (by simp)]
      rfl
    rw [← heq]
    exact ((iteratedFDeriv ℝ m (fun y => d (toUnitTorus y)) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hbound m) hProd)
  have hKsum : K m ≤ ∑ j ∈ Finset.range n, K j :=
    Finset.single_le_sum (f := K) (fun j _ => hK j) (Finset.mem_range.mpr (by omega))
  calc
    ‖J v‖ ≤ 3 * ((K m * D * D ^ m) * ∏ a, ‖v a‖) :=
      norm_linearMap_le_of_coordinateBounds
        (mul_nonneg (mul_nonneg (mul_nonneg (hK m) hD₀.le) (pow_nonneg hD₀.le _)) hProd)
        hColJet
    _ = (3 * K m * D ^ (m + 1)) * ∏ a, ‖v a‖ := by rw [pow_succ]; ring
    _ ≤ (V n * D ^ (m + 1)) * ∏ a, ‖v a‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hKsum (by norm_num)) (pow_nonneg hD₀.le _)) hProd

/-- The bilinear map `(u, v) ↦ u ⊗ v`, `w ↦ ⟪v, w⟫ u` (the rank-one map
`InnerProductSpace.rankOne ℝ u v`), of norm at most one: the product of Lemma D.2(a)
that builds `κ ⊗ κ` in `P_κ`. -/
def rankOneBilinear : Vec3 →L[ℝ] Vec3 →L[ℝ] (Vec3 →L[ℝ] Vec3) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun u v => InnerProductSpace.rankOne ℝ u v)
      (fun u₁ u₂ v => by ext w; simp)
      (fun c u v => by ext w; simp [smul_smul, mul_comm])
      (fun u v₁ v₂ => by ext w; simp)
      (fun c u v => by ext w; simp [smul_smul]))
    1 (fun u v => by simp)

/-- The rank-one bilinear form applied to `u`, `v`. -/
theorem rankOneBilinear_apply (u v : Vec3) :
    rankOneBilinear u v = InnerProductSpace.rankOne ℝ u v := rfl

/-- A velocity slice of a field smooth on the slab is smooth. -/
theorem contDiff_slice {U : Velocity} {T t : ℝ}
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (U t) :=
  contDiffOn_univ.mp (hU.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

end Lib.S5a

open Lib.S5a AppendixD

set_option maxHeartbeats 4000000 in
/-- Proof of **Proposition 5.1** (`cc:uf:trunc:prop:parent`), following
`sections/05b_parent_coefficients.tex:34-90`.

* `hB_1` (Lemma B.1, Bernstein's inequality (B.1)) enters in step 1 (TeX lines 35-39):
  `Lib.S5a.exists_velocityJets_of_lemmaB1 hB_1` bounds `|U|_k ≤ C_k 𝖣^k` from the
  frequency band `2𝖣 ≤ 4𝖣` of the parent and (5.1); these velocity jets feed the
  recursion (5.9) (`exists_forward_flowJetBounds`, TeX lines 40-72), the bound of
  `M = ∇U∘X` and (5.7) (`norm_iteratedFDeriv_parentComposition_le`, TeX lines 72-77).
* `hD_2` (Lemma D.2) enters in step 3 (TeX lines 79-84): part (b) gives (D.6) for
  `(D_aX)⁻¹ = Ring.inverse (D_aX)` (with `‖(D_aX)⁻¹‖ ≤ 𝖣` from (5.1)); part (a), with
  the bilinear products `A ↦ A v`, `⟪·,·⟫`, `u ⊗ v` and `c • A`, gives (D.6) for
  `κ/λ = (D_aX)^{-T}(k_*/λ)` (with `|k_*|/λ ≤ 𝖣` from (5.3)), `|κ/λ|²` and
  `|κ/λ|^{-2} ⊗ ...`; part (b) in `ℝ` gives (D.6) for `λ²/|κ|² = |κ/λ|^{-2}` (with
  `|κ|/λ ≥ 𝖣^{-2}` from (5.3)); and part (a) again gives `P_κ = |κ/λ|^{-2} (κ/λ ⊗ κ/λ)`.
  In step 4 (TeX lines 85-89) part (c) of `hD_2`, with `ℓ_* ≤ 𝖣^{-C}`, gives the first
  bound of (5.8) for the six coefficients.

The absolute exponent is `C = 360` (the largest exponent produced by the products and
inverses above: `5` for `D_aX`, `6` for `M`, `15` for `(D_aX)⁻¹`, `30` for `κ/λ`,
`180` for `λ²/|κ|²`, `360` for `P_κ`). The coefficient sizes of Appendix D and the
operator-norm jets of the statement are compared by `Lib.S5a.coefficientPower_of_jets`
and `Lib.S5a.norm_iteratedFDeriv_le_of_coefficientPower` (factors `#words` and `3^m`).
Equations: (B.1), (5.1), (5.3), (5.7), (5.8), (5.9), (D.6). -/
theorem Proof.proposition_5_1_of (hB_1 : Statement.lemma_B_1) (hD_2 : Statement.lemma_D_2) :
    Statement.proposition_5_1 := by
  -- Step 1: Bernstein's inequality (B.1) for the parent (TeX lines 35-39)
  obtain ⟨R, hR, hVel⟩ := exists_velocityJets_of_lemmaB1 hB_1
  -- Step 2: the recursion (5.9) for the flow (TeX lines 40-72)
  obtain ⟨Cf, hCf, hFlowJet⟩ := exists_forward_flowJetBounds R hR
  let W (m : ℕ) : ℝ := ((appendixCoefficientOrderWords m).card : ℝ)
  have hW (m : ℕ) : 0 ≤ W m := Nat.cast_nonneg _
  -- the constants of `D_aX` (exponent 5) and of `M` (exponent 6)
  let A (n : ℕ) := 1 + ∑ j ∈ Finset.range (n + 2), Cf j
  have hA (n : ℕ) : 1 ≤ A n := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hCf j)
  have hA₀ (n : ℕ) : 0 ≤ A n := zero_le_one.trans (hA n)
  have hCfA {j n : ℕ} (hj : j ≤ n + 1) : Cf j ≤ A n :=
    (Finset.single_le_sum (fun i _ => hCf i) (Finset.mem_range.mpr (by omega))).trans
      (le_add_of_nonneg_left zero_le_one)
  let Mb (n : ℕ) : ℝ := (n.factorial : ℝ) * R (n + 1) * (A n) ^ n
  have hMb (n : ℕ) : 0 ≤ Mb n :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hR _)) (pow_nonneg (hA₀ n) n)
  let CF (m : ℕ) : ℝ := W m * Cf (m + 1)
  let CM (m : ℕ) : ℝ := W m * Mb m
  let Ck (m : ℕ) : ℝ := W m * 1
  -- Step 3: the product and inverse rules of Lemma D.2 (TeX lines 79-84)
  obtain ⟨CG, hCG, hDG⟩ := hD_2.2.1 (Vec3 →L[ℝ] Vec3) CF 5 1
  let CGT (m : ℕ) : ℝ := W m * ((3 : ℝ) ^ m * CG m)
  obtain ⟨Cκ, hCκ, hDκ⟩ := hD_2.1 (Vec3 →L[ℝ] Vec3) Vec3 Vec3 CGT Ck (3 * max 5 1) 1
  obtain ⟨Cs, hCs, hDs⟩ := hD_2.1 Vec3 Vec3 ℝ Cκ Cκ (2 * max (3 * max 5 1) 1)
    (2 * max (3 * max 5 1) 1)
  obtain ⟨Cν, hCν, hDν⟩ := hD_2.2.1 ℝ Cs
    (2 * max (2 * max (3 * max 5 1) 1) (2 * max (3 * max 5 1) 1)) 4
  obtain ⟨Cr, hCr, hDr⟩ := hD_2.1 Vec3 Vec3 (Vec3 →L[ℝ] Vec3) Cκ Cκ (2 * max (3 * max 5 1) 1)
    (2 * max (3 * max 5 1) 1)
  obtain ⟨CP, hCP, hDP⟩ := hD_2.1 ℝ (Vec3 →L[ℝ] Vec3) (Vec3 →L[ℝ] Vec3) Cν Cr
    (3 * max (2 * max (2 * max (3 * max 5 1) 1) (2 * max (3 * max 5 1) 1)) 4)
    (2 * max (2 * max (3 * max 5 1) 1) (2 * max (3 * max 5 1) 1))
  -- Step 4: part (c) of Lemma D.2 for each coefficient, with the common exponent 360
  obtain ⟨EF, hEF, hcF⟩ := hD_2.2.2 (Vec3 →L[ℝ] Vec3) CF 360
  obtain ⟨EG, hEG, hcG⟩ := hD_2.2.2 (Vec3 →L[ℝ] Vec3) CG 360
  obtain ⟨EM, hEM, hcM⟩ := hD_2.2.2 (Vec3 →L[ℝ] Vec3) CM 360
  obtain ⟨Eκ, hEκ, hcκ⟩ := hD_2.2.2 Vec3 Cκ 360
  obtain ⟨Eν, hEν, hcν⟩ := hD_2.2.2 ℝ Cν 360
  obtain ⟨EP, hEP, hcP⟩ := hD_2.2.2 (Vec3 →L[ℝ] Vec3) CP 360
  have hCF (m : ℕ) : 0 ≤ CF m := mul_nonneg (hW m) (hCf _)
  have hCM (m : ℕ) : 0 ≤ CM m := mul_nonneg (hW m) (hMb m)
  have hCk (m : ℕ) : 0 ≤ Ck m := mul_nonneg (hW m) zero_le_one
  -- the constants of (D.6) and of the first bound of (5.8)
  let K (n : ℕ) : ℝ := (3 : ℝ) ^ n * (CF n + CG n + CM n + Cκ n + Cν n + CP n +
    (EF n + EG n + EM n + Eκ n + Eν n + EP n))
  have hK3 (n : ℕ) : (3 : ℝ) ^ n * CF n ≤ K n ∧ (3 : ℝ) ^ n * CG n ≤ K n ∧
      (3 : ℝ) ^ n * CM n ≤ K n ∧ (3 : ℝ) ^ n * Cκ n ≤ K n ∧ (3 : ℝ) ^ n * Cν n ≤ K n ∧
      (3 : ℝ) ^ n * CP n ≤ K n ∧ (3 : ℝ) ^ n * EF n ≤ K n ∧ (3 : ℝ) ^ n * EG n ≤ K n ∧
      (3 : ℝ) ^ n * EM n ≤ K n ∧ (3 : ℝ) ^ n * Eκ n ≤ K n ∧ (3 : ℝ) ^ n * Eν n ≤ K n ∧
      (3 : ℝ) ^ n * EP n ≤ K n := by
    have h3 : (0 : ℝ) ≤ 3 ^ n := by positivity
    have := hCF n; have := hCG n; have := hCM n; have := hCκ n; have := hCν n
    have := hCP n; have := hEF n; have := hEG n; have := hEM n; have := hEκ n
    have := hEν n; have := hEP n
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      exact mul_le_mul_of_nonneg_left (by linarith) h3
  refine ⟨360, K, fun C' => ?_⟩
  -- the constants of (5.7) and of the second bound of (5.8) (TeX lines 72-75, 88-89)
  let C'' : ℕ → ℝ := fun n => max (C' n) 0
  let B (m : ℕ) := 1 + ∑ j ∈ Finset.range (m + 1), Cf j
  let Kc (m : ℕ) := ∑ j ∈ Finset.range (m + 1), C'' j
  have hB (m : ℕ) : 1 ≤ B m := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hCf j)
  have hKc (m : ℕ) : 0 ≤ Kc m := Finset.sum_nonneg fun j _ => le_max_right _ _
  let Cc (m : ℕ) := (m.factorial : ℝ) * Kc m * B m ^ m
  have hCc (m : ℕ) : 0 ≤ Cc m := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hKc m))
    (pow_nonneg (zero_le_one.trans (hB m)) _)
  let Kf : ℕ → ℝ := fun n => ∑ j ∈ Finset.range (n + 1), Cc j
  have hKf (n : ℕ) : Cc n ≤ Kf n :=
    Finset.single_le_sum (fun j _ => hCc j) (Finset.mem_range.mpr (Nat.lt_succ_self n))
  refine ⟨Kf, ?_⟩
  intro T U X pU k D lam t₀ hT hP hL
  have hD : 1 ≤ D := one_le_two.trans hP.scale_ge_two
  have hD₀ : 0 < D := zero_lt_one.trans_le hD
  have hlam : 0 < lam := zero_lt_one.trans_le hP.frequency_ge_one
  have ht₀ : t₀ ∈ Icc 0 T := ⟨hL.start_nonneg, hL.start_lt.le⟩
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hU₂ : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hP.velocity_smooth.of_le (by simp)
  -- the velocity jets of step 1
  obtain ⟨v, hv⟩ := hP.velocity_band
  have hJets : ∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ j (U t) x‖ ≤ R n * D ^ j := by
    intro n j hj hjn t ht x
    have hlift : (fun y => v t (toUnitTorus y)) = U t := funext fun y => (hv t ht).1 y
    rw [← hlift]
    refine hVel (v t) hD ?_ ?_ ?_ n j hj hjn x
    · intro q hq
      exact (hv t ht).2 q
        ((mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 4) hD₀.le).trans_lt hq)
    · rw [hlift]
      exact contDiff_slice hP.velocity_smooth ht
    · intro y
      rw [hlift]
      exact hP.gradient_le t ht y
  -- the flow jets of step 2
  have hFlowAt (j : ℕ) (hj : 1 ≤ j) (t : ℝ) (ht : t ∈ Icc 0 T) (b : Vec3) :
      ‖iteratedFDeriv ℝ j (X 0 t) b‖ ≤ Cf j * D ^ (5 * j - 4) :=
    hFlowJet hT hP.time_le_one hD hP.flow hP.velocity_smooth hP.velocity_periodic
      hP.deformation_le hP.inverse_deformation_le
      (fun n _ i hi hin => hJets n i (by omega) hin) j hj t ht b
  have hXsmooth (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (X 0 t) :=
    contDiff_infty.mpr fun j =>
      (hP.flow.labelJets_evolve j hT hP.velocity_smooth hP.velocity_periodic).1 t ht
  -- the six coefficients, on the time domain `I = [0,T]`
  let I := ↥(Icc (0 : ℝ) T)
  let cF : I → Vec3 → (Vec3 →L[ℝ] Vec3) := fun t a => fderiv ℝ (X 0 t) a
  let cG : I → Vec3 → (Vec3 →L[ℝ] Vec3) := fun t a => fderiv ℝ (X t 0) (X 0 t a)
  let cGT : I → Vec3 → (Vec3 →L[ℝ] Vec3) := fun t a => (cG t a).adjoint
  let cM : I → Vec3 → (Vec3 →L[ℝ] Vec3) := fun t a => S5.strainField U X t a
  let ck : I → Vec3 → Vec3 := fun _ _ => lam⁻¹ • k
  let cκ : I → Vec3 → Vec3 := fun t a => lam⁻¹ • S5.waveVector X k t a
  let cs : I → Vec3 → ℝ := fun t a => ⟪cκ t a, cκ t a⟫_ℝ
  let cν : I → Vec3 → ℝ := fun t a => lam ^ 2 / ‖S5.waveVector X k t a‖ ^ 2
  let cr : I → Vec3 → (Vec3 →L[ℝ] Vec3) := fun t a =>
    InnerProductSpace.rankOne ℝ (cκ t a) (cκ t a)
  let cP : I → Vec3 → (Vec3 →L[ℝ] Vec3) := fun t a =>
    (‖S5.waveVector X k t a‖ ^ 2)⁻¹ •
      InnerProductSpace.rankOne ℝ (S5.waveVector X k t a) (S5.waveVector X k t a)
  -- (D.6) for `D_aX` (exponent 5), from (5.9)
  have hPF : CoefficientPower CF D 5 cF := by
    refine coefficientPower_of_jets hD₀.le (fun m => hCf (m + 1)) (fun t => ?_) fun m t a => ?_
    · exact (contDiff_infty_iff_fderiv.mp (hXsmooth t t.2)).2
    · have h := norm_iteratedFDeriv_labelJacobian_le_of_flowJets m
        (hFlowAt (m + 1) (by omega) t t.2 a)
      exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) (hCf _))
  -- (D.6) for `M = ∇U∘X` (exponent 6), from the chain rule (TeX lines 76-77)
  have hPM : CoefficientPower CM D 6 cM := by
    refine coefficientPower_of_jets hD₀.le hMb (fun t => ?_) fun n t a => ?_
    · exact ((contDiff_infty_iff_fderiv.mp (contDiff_slice hP.velocity_smooth t.2)).2).comp
        (hXsmooth t t.2)
    · have hgradSmooth : ContDiff ℝ n (fderiv ℝ (U t)) :=
        ((contDiff_infty_iff_fderiv.mp (contDiff_slice hP.velocity_smooth t.2)).2).of_le
          (by simp)
      have hGrad (i : ℕ) (hi : i ≤ n) :
          ‖iteratedFDeriv ℝ i (fderiv ℝ (U t)) (X 0 t a)‖ ≤ R (n + 1) * D * D ^ i := by
        rw [norm_iteratedFDeriv_fderiv]
        have h := hJets (n + 1) (i + 1) (by omega) (by omega) t t.2 (X 0 t a)
        exact h.trans_eq (by rw [pow_succ]; ring)
      have h := norm_iteratedFDeriv_parentComposition_le hgradSmooth
        ((hXsmooth t t.2).of_le (by simp)) a hD (hA n) (hR (n + 1)) hD₀.le
        (fun i hi hin => (hFlowAt i hi t t.2 a).trans
          (mul_le_mul (hCfA (by omega)) (pow_le_pow_right₀ hD (by omega))
            (by positivity) (hA₀ n))) hGrad
      change ‖iteratedFDeriv ℝ n (fderiv ℝ (U t) ∘ X 0 t) a‖ ≤ _
      refine h.trans ?_
      calc
        _ = Mb n * D ^ (6 * n + 1) := by rw [pow_succ]; dsimp only [Mb]; ring
        _ ≤ Mb n * D ^ (6 * (n + 1)) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) (hMb n)
  -- `D_aX` is invertible with inverse `(D_aX)⁻¹`, and `‖(D_aX)⁻¹‖ ≤ 𝖣` ((5.1))
  have hinv (t : I) (a : Vec3) : IsUnit (cF t a) ∧ Ring.inverse (cF t a) = cG t a := by
    obtain ⟨hGF, hFG⟩ := hP.flow.labelDerivative_inverse hT hU₂ hP.velocity_periodic h₀ t.2 a
    let w : (Vec3 →L[ℝ] Vec3)ˣ := ⟨cF t a, cG t a, hFG, hGF⟩
    exact ⟨w.isUnit, Ring.inverse_unit w⟩
  have hGfun : (fun t a => Ring.inverse (cF t a)) = cG :=
    funext fun t => funext fun a => (hinv t a).2
  -- Lemma D.2(b): (D.6) for `(D_aX)⁻¹`
  have hPG : CoefficientPower CG D (3 * max 5 1) cG := by
    have h := hDG I D hD cF hPF (fun t a => (hinv t a).1) (fun t a => by
      rw [(hinv t a).2, pow_one]
      exact hP.inverse_deformation_le t t.2 a)
    rwa [hGfun] at h
  -- the transpose has the same jets
  have hPGT : CoefficientPower CGT D (3 * max 5 1) cGT := by
    refine coefficientPower_of_jets hD₀.le
      (fun m => mul_nonneg (by positivity) (hCG m)) (fun t => ?_) fun m t a => ?_
    · let J := ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)
      exact J.toContinuousLinearEquiv.contDiff.comp (hPG.1 t)
    · let J := ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)
      change ‖iteratedFDeriv ℝ m (J ∘ cG t) a‖ ≤ _
      rw [J.norm_iteratedFDeriv_comp_left (cG t) a m]
      have h := norm_iteratedFDeriv_le_of_coefficientPower hPG m t a
      calc
        _ ≤ 3 ^ m * CG m * D ^ (3 * max 5 1 * (m + 1)) := h
        _ = _ := by ring
  -- the normalized carrier `k_*/λ` is a constant field with `|k_*|/λ ≤ 𝖣` ((5.3))
  have hNorm (t : I) (b : Vec3) :=
    hP.flow.norm_normalizedLabelWaveVector_bounds hT hU₂ hP.velocity_periodic ht₀ t.2 b k hD
      hlam hL.frequency (hP.deformation_le t₀ ht₀ 0) (hP.inverse_deformation_le t₀ ht₀ 0)
      (hP.deformation_le t t.2 b) (hP.inverse_deformation_le t t.2 b)
  have hPk : CoefficientPower Ck D 1 ck := by
    refine coefficientPower_of_jets hD₀.le (fun _ => zero_le_one) (fun _ => contDiff_const)
      fun m t a => ?_
    rcases m with _ | m
    · simp only [norm_iteratedFDeriv_zero, one_mul, zero_add, mul_one, pow_one, ck]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam), ← div_eq_inv_mul]
      exact (hNorm t 0).1
    · rw [iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, norm_zero]
      positivity
  -- Lemma D.2(a): (D.6) for `κ/λ = (D_aX)^{-T}(k_*/λ)`
  have hκfun : (fun t a => ContinuousLinearMap.id ℝ (Vec3 →L[ℝ] Vec3) (cGT t a) (ck t a)) = cκ := by
    funext t a
    simp only [ContinuousLinearMap.id_apply, cGT, cG, ck, cκ, S5.waveVector, labelWaveVector,
      map_smul]
  have hPκ : CoefficientPower Cκ D (2 * max (3 * max 5 1) 1) cκ := by
    have h := hDκ (ContinuousLinearMap.id ℝ (Vec3 →L[ℝ] Vec3)) ContinuousLinearMap.norm_id_le
      I D hD cGT ck hPGT hPk
    rwa [hκfun] at h
  -- Lemma D.2(a): (D.6) for `|κ/λ|²`
  have hPs : CoefficientPower Cs D (2 * max (2 * max (3 * max 5 1) 1) (2 * max (3 * max 5 1) 1))
      cs := hDs (innerSL ℝ) (norm_innerSL_le ℝ) I D hD cκ cκ hPκ hPκ
  -- `|κ/λ|² ≥ 𝖣^{-4}` ((5.3)), so Lemma D.2(b) in `ℝ` gives (D.6) for `λ²/|κ|²`
  have hcs (t : I) (a : Vec3) : cs t a = ‖cκ t a‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hνfun : (fun t a => Ring.inverse (cs t a)) = cν := by
    funext t a
    rw [Ring.inverse_eq_inv', hcs]
    exact inv_sq_norm_inv_smul lam (S5.waveVector X k t a)
  have hPν : CoefficientPower Cν D
      (3 * max (2 * max (2 * max (3 * max 5 1) 1) (2 * max (3 * max 5 1) 1)) 4) cν := by
    have hlow (t : I) (a : Vec3) := normalizedWaveNorm_ne_zero_and_inv_sq_le hD₀ (hNorm t a).2.1
    have h := hDν I D hD cs hPs (fun t a => by
        rw [hcs]
        exact (pow_pos (norm_pos_iff.mpr (hlow t a).1) 2).ne'.isUnit)
      (fun t a => by
        rw [Ring.inverse_eq_inv', hcs, norm_inv, norm_pow, norm_norm]
        exact (hlow t a).2)
    rwa [hνfun] at h
  -- Lemma D.2(a): (D.6) for `κ/λ ⊗ κ/λ` and for `P_κ = |κ/λ|^{-2} (κ/λ ⊗ κ/λ)`
  have hPr : CoefficientPower Cr D (2 * max (2 * max (3 * max 5 1) 1) (2 * max (3 * max 5 1) 1))
      cr := hDr rankOneBilinear (LinearMap.mkContinuous₂_norm_le _ zero_le_one _) I D hD cκ cκ hPκ hPκ
  have hPfun : (fun t a => ContinuousLinearMap.lsmul ℝ ℝ (cν t a) (cr t a)) = cP := by
    funext t a
    simp only [ContinuousLinearMap.lsmul_apply, cP, cν, cr, cκ]
    rw [← inv_sq_norm_inv_smul lam (S5.waveVector X k t a),
      rankOne_directionProjection_smul (S5.waveVector X k t a) (inv_ne_zero hlam.ne')]
  have hPP : CoefficientPower CP D
      (2 * max (3 * max (2 * max (2 * max (3 * max 5 1) 1) (2 * max (3 * max 5 1) 1)) 4)
        (2 * max (2 * max (3 * max 5 1) 1) (2 * max (3 * max 5 1) 1))) cP := by
    have h := hDP (ContinuousLinearMap.lsmul ℝ ℝ) ContinuousLinearMap.opNorm_lsmul_le I D hD
      cν cr hPν hPr
    rwa [hPfun] at h
  -- all six coefficients with the common absolute exponent `C = 360`
  have hF360 := CoefficientPower.mono_exponent (b := 360) hPF hD (by norm_num)
  have hG360 := CoefficientPower.mono_exponent (b := 360) hPG hD (by norm_num)
  have hM360 := CoefficientPower.mono_exponent (b := 360) hPM hD (by norm_num)
  have hκ360 := CoefficientPower.mono_exponent (b := 360) hPκ hD (by norm_num)
  have hν360 := CoefficientPower.mono_exponent (b := 360) hPν hD (by norm_num)
  have hP360 := CoefficientPower.mono_exponent (b := 360) hPP hD (by norm_num)
  -- operator-norm jets with the constants `K`
  have jet {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {Cc : ℕ → ℝ} {c : I → Vec3 → Y}
      (hc : CoefficientPower Cc D 360 c) (hK : ∀ m, (3 : ℝ) ^ m * Cc m ≤ K m)
      (m : ℕ) (t : I) (a : Vec3) :
      ‖iteratedFDeriv ℝ m (c t) a‖ ≤ K m * D ^ (360 * (m + 1)) :=
    (norm_iteratedFDeriv_le_of_coefficientPower hc m t a).trans
      (mul_le_mul_of_nonneg_right (hK m) (by positivity))
  -- the composition estimate (5.7), uniform in the target space (TeX lines 72-75)
  have hComp : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → Vec3 → E) (Af : ℝ),
      0 ≤ Af → (∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (f t)) →
      (∀ m : ℕ, ∀ t ∈ Icc 0 T, ∀ x, ‖iteratedFDeriv ℝ m (f t) x‖ ≤ C' m * Af * D ^ m) →
      ∀ m : ℕ, ∀ t ∈ Icc 0 T, ∀ a,
        ‖iteratedFDeriv ℝ m (fun b => f t (X 0 t b)) a‖ ≤ Cc m * Af * D ^ (6 * m) := by
    intro E _ _ f Af hAf hf hfJ m t ht x
    have hCcomp := norm_iteratedFDeriv_parentComposition_le (n := m) ((hf t ht).of_le (by simp))
      ((hXsmooth t ht).of_le (by simp)) x hD (hB m) (hKc m) hAf (fun i hi him => ?_)
      (fun i him => ?_)
    · exact hCcomp
    · have hCi : Cf i ≤ B m :=
        (Finset.single_le_sum (fun j _ => hCf j)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le him))).trans
          (le_add_of_nonneg_left zero_le_one)
      exact (hFlowAt i hi t ht x).trans (mul_le_mul hCi (pow_le_pow_right₀ hD (Nat.sub_le _ _))
        (by positivity) (zero_le_one.trans (hB m)))
    · have hCi : C'' i ≤ Kc m :=
        Finset.single_le_sum (fun j _ => le_max_right (C' j) 0)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le him))
      refine (hfJ i t ht (X 0 t x)).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans hCi) hAf) (by positivity)
  -- the first bound of (5.8) from Lemma D.2(c), at each time (TeX lines 85-88)
  have weighted {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {Cc Ec : ℕ → ℝ}
      {c : I → Vec3 → Y} (hc : CoefficientPower Cc D 360 c)
      (hEc : ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ (D ^ 360)⁻¹ → ∀ n, coefficientNorm ℓ n c ≤ Ec n * D ^ 360)
      (hK : ∀ n, (3 : ℝ) ^ n * Ec n ≤ K n)
      (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓD : ℓ ≤ (D ^ 360)⁻¹) (n : ℕ) (t : I) :
      (∑ j ∈ Finset.range (n + 1), ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (c t))) ≤
        K n * D ^ 360 := by
    have hterm (j : ℕ) (hj : j ≤ n) :
        ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (c t)) ≤
          (3 : ℝ) ^ n * (ℓ ^ j * coefficientOrderNorm j c) := by
      have hsup : spatialSupNorm (iteratedFDeriv ℝ j (c t)) ≤
          (3 : ℝ) ^ j * coefficientOrderNorm j c :=
        ciSup_le fun a => norm_iteratedFDeriv_le_coefficientOrderNorm hc.1 (hc.2.1 j) t a
      have hnorm : 0 ≤ coefficientOrderNorm j c :=
        Finset.sum_nonneg fun w hw => le_csSup (hc.2.1 j w hw) (Or.inl rfl)
      calc
        _ ≤ ℓ ^ j * ((3 : ℝ) ^ j * coefficientOrderNorm j c) :=
          mul_le_mul_of_nonneg_left hsup (pow_nonneg hℓ.le _)
        _ = (3 : ℝ) ^ j * (ℓ ^ j * coefficientOrderNorm j c) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj)
          (mul_nonneg (pow_nonneg hℓ.le _) hnorm)
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1), (3 : ℝ) ^ n * (ℓ ^ j * coefficientOrderNorm j c) :=
        Finset.sum_le_sum fun j hj => hterm j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      _ = (3 : ℝ) ^ n * coefficientNorm ℓ n c := by rw [← Finset.mul_sum]; rfl
      _ ≤ (3 : ℝ) ^ n * (Ec n * D ^ 360) :=
        mul_le_mul_of_nonneg_left (hEc ℓ hℓ hℓD n) (by positivity)
      _ ≤ K n * D ^ 360 := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hK n) (by positivity)
  have hEF' := fun ℓ (hℓ : 0 < ℓ) hℓD => (hcF I D ℓ hD hℓ hℓD cF hF360).1
  have hEG' := fun ℓ (hℓ : 0 < ℓ) hℓD => (hcG I D ℓ hD hℓ hℓD cG hG360).1
  have hEM' := fun ℓ (hℓ : 0 < ℓ) hℓD => (hcM I D ℓ hD hℓ hℓD cM hM360).1
  have hEκ' := fun ℓ (hℓ : 0 < ℓ) hℓD => (hcκ I D ℓ hD hℓ hℓD cκ hκ360).1
  have hEν' := fun ℓ (hℓ : 0 < ℓ) hℓD => (hcν I D ℓ hD hℓ hℓD cν hν360).1
  have hEP' := fun ℓ (hℓ : 0 < ℓ) hℓD => (hcP I D ℓ hD hℓ hℓD cP hP360).1
  refine ⟨fun m t ht a => ?_, ?_, ?_⟩
  · -- (D.6) for the six coefficients
    exact ⟨jet hF360 (fun n => (hK3 n).1) m ⟨t, ht⟩ a,
      jet hG360 (fun n => (hK3 n).2.1) m ⟨t, ht⟩ a,
      jet hM360 (fun n => (hK3 n).2.2.1) m ⟨t, ht⟩ a,
      jet hκ360 (fun n => (hK3 n).2.2.2.1) m ⟨t, ht⟩ a,
      jet hν360 (fun n => (hK3 n).2.2.2.2.1) m ⟨t, ht⟩ a,
      jet hP360 (fun n => (hK3 n).2.2.2.2.2.1) m ⟨t, ht⟩ a⟩
  · -- (5.7)
    intro E _ _ f Af hAf hf hfJ m t ht a
    refine (hComp f Af hAf hf hfJ m t ht a).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_right (hKf m) hAf)
      (pow_le_pow_right₀ hD (by omega)) (by positivity) (mul_nonneg ((hCc m).trans (hKf m)) hAf)
  · -- (5.8)
    intro ℓ hℓ hℓD n t ht
    refine ⟨weighted hF360 hEF' (fun n => (hK3 n).2.2.2.2.2.2.1) ℓ hℓ hℓD n ⟨t, ht⟩,
      weighted hG360 hEG' (fun n => (hK3 n).2.2.2.2.2.2.2.1) ℓ hℓ hℓD n ⟨t, ht⟩,
      weighted hM360 hEM' (fun n => (hK3 n).2.2.2.2.2.2.2.2.1) ℓ hℓ hℓD n ⟨t, ht⟩,
      weighted hκ360 hEκ' (fun n => (hK3 n).2.2.2.2.2.2.2.2.2.1) ℓ hℓ hℓD n ⟨t, ht⟩,
      weighted hν360 hEν' (fun n => (hK3 n).2.2.2.2.2.2.2.2.2.2.1) ℓ hℓ hℓD n ⟨t, ht⟩,
      weighted hP360 hEP' (fun n => (hK3 n).2.2.2.2.2.2.2.2.2.2.2) ℓ hℓ hℓD n ⟨t, ht⟩, ?_⟩
    intro E _ _ f Af hAf hf hfJ
    have hscale : ℓ * D ^ (360 : ℕ) ≤ 1 := by
      calc ℓ * D ^ (360 : ℕ) ≤ (D ^ 360)⁻¹ * D ^ 360 :=
            mul_le_mul_of_nonneg_right hℓD (by positivity)
        _ = 1 := inv_mul_cancel₀ (by positivity)
    have hscale6 : ℓ * D ^ (6 : ℕ) ≤ 1 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by norm_num : 6 ≤ 360)) hℓ.le).trans
        hscale
    have hb : ParentLabelJetBound T D (fun r => f r ∘ X 0 r) (fun j => Cc j * Af) 6 0 := by
      intro m r hr a
      exact hComp f Af hAf hf hfJ m r hr a
    exact paperProposition51_weightedComposition hD hℓ.le hAf hscale6 hCc hb ht n

end

end TorusEuler.Paper
