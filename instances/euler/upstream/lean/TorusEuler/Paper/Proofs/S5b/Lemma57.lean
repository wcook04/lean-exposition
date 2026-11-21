import TorusEuler.Paper.Proofs.S5b.Library.Words57
import TorusEuler.Paper.S5.Statements
import TorusEuler.Paper.Proofs.S5Bridge.Parent

/-!
# Proof of Lemma 5.7 (`cc:uf:hier:lem:physical`)

The conditional proof `Paper.Proof.lemma_5_7_of` of Lemma 5.7 from Proposition 5.1 and
Lemma D.1, following `sections/08_exact_wave.tex:51-74`:

1. `d̃ = (D_aX)^{-T}(∇_a + k_*∂_s)` and the chain rule (3.1) turn every Eulerian derivative
   word of `g₀^♮(t)` into the graph of the `d̃`-word of `g₀` (`spatialDerivativeWord_graph`).
2. The one-step bound `∑_i ‖d̃_i g‖_{[n],γ} ≤ C_n 𝖣^C λ^{3/2} ‖g‖_{[n+1],γ}` from Lemma D.1
   ((D.3), (D.4); `tilde_step_general`) and (5.8) of Proposition 5.1 for the coefficient
   `(D_aX)⁻¹` (`coef_bounds`, `domain_bounds`), with `ℓ_*^{-1} = 𝖣^a` and
   `|k_*| h^{-1} ≤ 𝖣 λ^{3/2}` by (5.3).
3. Iterating the bound (`words_general`) and `sup |g(t)| ≤ γ(t)‖g‖_{[0],γ}` give (5.44); the
   Hölder bound with one more derivative gives (5.45) (`graph_from_words`).
4. For a phase-independent field `∂_s g = 0`, so the factor `λ^{3/2}` disappears
   (`words_phaseIndep`).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.S5b

open AppendixD

noncomputable section

/-- The one-step constant `κ₀_n = 12 c_n #W_n max(K_n, 0)` of the proof of Lemma 5.7, for
the constants `K_n` of (5.8) in Proposition 5.1. -/
def wordConst (K₁ : ℕ → ℝ) (n : ℕ) : ℝ :=
  12 * productConst n * (hierarchyAdmissibleWords (Fin 3) n).card * max (K₁ n) 0

/-- The word constant of Lemma 5.7 is nonnegative. -/
theorem wordConst_nonneg (K₁ : ℕ → ℝ) (n : ℕ) : 0 ≤ wordConst K₁ n := by
  unfold wordConst
  have := productConst_nonneg n
  have := le_max_right (K₁ n) 0
  positivity

/-- The constants `C_m` of Lemma 5.7: `∏_{l<m} κ₀_l + 3(m+1) ∑_{j≤m+1} ∏_{l<j} κ₀_l`. -/
def lemma57Const (K₁ : ℕ → ℝ) (m : ℕ) : ℝ :=
  (∏ l ∈ Finset.range m, wordConst K₁ l) +
    3 * (m + 1) * ∑ j ∈ Finset.range (m + 2), ∏ l ∈ Finset.range j, wordConst K₁ l

/-- Conversion of the bounds of `graph_from_words` into the form of the statement,
`C_m Λ^m γ(t) N_m` and `C_m Λ^{m+1} γ(t) N_{m+1}`, when the word constants are at most
`(∏_{l<j} κ₀_l) Λ^j` with `Λ ≥ 1`. -/
theorem final_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Vec3 → E} {γt N0 N1 Λ : ℝ} {P : ℕ → ℝ} {K₁ : ℕ → ℝ} {m : ℕ}
    (hΛ : 1 ≤ Λ) (hγt : 0 ≤ γt) (hN0 : 0 ≤ N0) (hN1 : 0 ≤ N1)
    (hP : ∀ j, P j ≤ (∏ l ∈ Finset.range j, wordConst K₁ l) * Λ ^ j)
    (h1 : (∑ w : Fin m → Fin 3, spatialSupNorm (spatialDerivativeWord (List.ofFn w) F)) ≤
      γt * P m * N0)
    (h2 : SpatialHolderHalf m F ∧ spatialHolderHalfNorm m F ≤
      (3 * (m + 1) : ℝ) * (γt * (∑ j ∈ Finset.range (m + 2), P j) * N1)) :
    (∑ w : Fin m → Fin 3, spatialSupNorm (spatialDerivativeWord (List.ofFn w) F)) ≤
        lemma57Const K₁ m * Λ ^ m * γt * N0 ∧
      SpatialHolderHalf m F ∧ spatialHolderHalfNorm m F ≤ lemma57Const K₁ m * Λ ^ (m + 1) * γt * N1 := by
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  have hprod (j : ℕ) : 0 ≤ ∏ l ∈ Finset.range j, wordConst K₁ l :=
    Finset.prod_nonneg fun l _ => wordConst_nonneg K₁ l
  have hS : 0 ≤ ∑ j ∈ Finset.range (m + 2), ∏ l ∈ Finset.range j, wordConst K₁ l :=
    Finset.sum_nonneg fun j _ => hprod j
  have hC1 : (∏ l ∈ Finset.range m, wordConst K₁ l) ≤ lemma57Const K₁ m :=
    le_add_of_nonneg_right (by positivity)
  have hC2 : (3 * (m + 1) : ℝ) * ∑ j ∈ Finset.range (m + 2), ∏ l ∈ Finset.range j, wordConst K₁ l ≤
      lemma57Const K₁ m := le_add_of_nonneg_left (hprod m)
  refine ⟨h1.trans ?_, h2.1, h2.2.trans ?_⟩
  · calc γt * P m * N0 ≤ γt * ((∏ l ∈ Finset.range m, wordConst K₁ l) * Λ ^ m) * N0 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hP m) hγt) hN0
      _ ≤ γt * (lemma57Const K₁ m * Λ ^ m) * N0 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hC1 (pow_nonneg hΛ0 _)) hγt) hN0
      _ = _ := by ring
  · have hsum : (∑ j ∈ Finset.range (m + 2), P j) ≤
        (∑ j ∈ Finset.range (m + 2), ∏ l ∈ Finset.range j, wordConst K₁ l) * Λ ^ (m + 1) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj => (hP j).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hΛ (by have := Finset.mem_range.mp hj; omega)) (hprod j))
    calc (3 * (m + 1) : ℝ) * (γt * (∑ j ∈ Finset.range (m + 2), P j) * N1) ≤
          (3 * (m + 1) : ℝ) * (γt * ((∑ j ∈ Finset.range (m + 2), ∏ l ∈ Finset.range j,
            wordConst K₁ l) * Λ ^ (m + 1)) * N1) := by gcongr
      _ = ((3 * (m + 1) : ℝ) * ∑ j ∈ Finset.range (m + 2), ∏ l ∈ Finset.range j,
            wordConst K₁ l) * Λ ^ (m + 1) * γt * N1 := by ring
      _ ≤ _ := by gcongr

/-- A function jointly smooth on `[0,T] × ℝ³` is smooth in space at each time of `[0,T]`. -/
theorem slice_contDiff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : ℝ × Vec3 → F}
    {T : ℝ} (hg : ContDiffOn ℝ ∞ g (Icc 0 T ×ˢ (univ : Set Vec3))) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContDiff ℝ ∞ (fun a => g (t, a)) :=
  contDiffOn_univ.mp (hg.comp (contDiffOn_const.prodMk contDiffOn_id)
    (fun a _ => ⟨ht, mem_univ a⟩))

/-- `λ^{3/2} = λ · λ^{1/2}`. -/
theorem rpow_three_halves {lam : ℝ} (hlam : 0 < lam) :
    lam ^ (3 / 2 : ℝ) = lam * lam ^ (1 / 2 : ℝ) := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hlam, Real.rpow_one]

/-- `h⁻¹ = λ^{1/2}` for `h = λ^{-1/2}`. -/
theorem width_inv {lam : ℝ} (hlam : 0 < lam) : (S5.width lam)⁻¹ = lam ^ (1 / 2 : ℝ) := by
  unfold S5.width
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hlam.le, inv_inv]

/-- **Lemma 5.7 on one time domain.** For a time domain `I` mapped into `[0,T]`, a positive
weight `γ` and a field `f` with all norms `‖f‖_{[n],γ}` finite, the graph
`F = f(t) ∘ (X(t,·)⁻¹, k·X(t,·)⁻¹)` satisfies (5.44), (5.45) with `Λ = 𝖣^{C₁+a+1} λ^{3/2}`,
and with `Λ = 𝖣^{C₁+a+1}` when `f` is phase independent. The hypotheses `hD6`, `h58` are
(D.6) and (5.8) of Proposition 5.1 for `(D_aX)⁻¹`; `hk` is `|k_*| ≤ 𝖣λ` ((5.3));
`hD_1` (Lemma D.1) enters the one-step bound. -/
theorem domain_bounds (hD_1 : Statement.lemma_D_1) {I : Type} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} (ι : I → ℝ) (hι : ∀ t, ι t ∈ Icc 0 T)
    {X : ℝ → Velocity} {k : Vec3} {D lam : ℝ} {a C₁ : ℕ} {K₁ : ℕ → ℝ}
    (hD : 1 ≤ D) (hlam : 1 ≤ lam) (hk : ‖k‖ ≤ D * lam)
    (hAs : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (X t 0))
    (hGs : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (fun b => fderiv ℝ (X t 0) (X 0 t b)))
    (hGA : ∀ t ∈ Icc 0 T, ∀ x, fderiv ℝ (X t 0) (X 0 t (X t 0 x)) = fderiv ℝ (X t 0) x)
    (hD6 : ∀ m, ∀ t ∈ Icc 0 T, ∀ b,
      ‖iteratedFDeriv ℝ m (fun b => fderiv ℝ (X t 0) (X 0 t b)) b‖ ≤ K₁ m * D ^ (C₁ * (m + 1)))
    (h58 : ∀ n, ∀ t ∈ Icc 0 T,
      (∑ j ∈ Finset.range (n + 1), S5.radius D a ^ j *
        spatialSupNorm (iteratedFDeriv ℝ j (fun b => fderiv ℝ (X t 0) (X 0 t b)))) ≤ K₁ n * D ^ C₁)
    {γ : I → ℝ} (hγ : ∀ t, 0 < γ t) {f : I → Vec3 × ℝ → E}
    (hfin : ∀ n, FieldNormFinite (S5.radius D a) (S5.width lam) n (weighted γ f))
    (t : I) (m : ℕ) :
    let F := f t ∘ graphPoint (X (ι t) 0) k
    let N := fun n => weightedFieldNorm (S5.radius D a) (S5.width lam) γ n f
    let bnd := fun (Λ : ℝ) =>
      (∑ w : Fin m → Fin 3, spatialSupNorm (spatialDerivativeWord (List.ofFn w) F)) ≤
          lemma57Const K₁ m * Λ ^ m * γ t * N m ∧
        SpatialHolderHalf m F ∧ spatialHolderHalfNorm m F ≤ lemma57Const K₁ m * Λ ^ (m + 1) * γ t * N (m + 1)
    bnd (D ^ (C₁ + a + 1) * lam ^ (3 / 2 : ℝ)) ∧ (PhaseIndep f → bnd (D ^ (C₁ + a + 1))) := by
  intro F N bnd
  set ℓ := S5.radius D a with hℓdef
  set h := S5.width lam with hhdef
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam
  have hℓ : 0 < ℓ := inv_pos.mpr (pow_pos hD0 a)
  have hh : 0 < h := Real.rpow_pos_of_pos hlam0 _
  have hℓinv : ℓ⁻¹ = D ^ a := by rw [hℓdef, S5.radius, inv_inv]
  have hhinv : h⁻¹ = lam ^ (1 / 2 : ℝ) := width_inv hlam0
  let G : I → Vec3 → Vec3 →L[ℝ] Vec3 := fun t b => fderiv ℝ (X (ι t) 0) (X 0 (ι t) b)
  let M : ℕ → ℝ := fun n => max (K₁ n) 0
  have hM (n : ℕ) : 0 ≤ M n := le_max_right _ _
  let B : ℕ → ℝ := fun n => M n * D ^ C₁
  have hB (n : ℕ) : 0 ≤ B n := mul_nonneg (hM n) (pow_nonneg hD0.le _)
  have hGsm (t : I) : ContDiff ℝ ∞ (G t) := hGs _ (hι t)
  -- the jets of `(D_aX)⁻¹` from (D.6) and (5.8) of Proposition 5.1
  have hunif (m : ℕ) : ∃ b, ∀ t a, ‖iteratedFDeriv ℝ m (G t) a‖ ≤ b :=
    ⟨K₁ m * D ^ (C₁ * (m + 1)), fun t a => hD6 m _ (hι t) a⟩
  have hjet (n : ℕ) : ∀ m ≤ n, ∀ t a, ℓ ^ m * ‖iteratedFDeriv ℝ m (G t) a‖ ≤ B n := by
    intro m hm t b
    have hbdd : BddAbove (range fun x => ‖iteratedFDeriv ℝ m (G t) x‖) :=
      ⟨K₁ m * D ^ (C₁ * (m + 1)), forall_mem_range.mpr fun x => hD6 m _ (hι t) x⟩
    have hsup := norm_le_spatialSupNorm hbdd b
    have hterm : ℓ ^ m * spatialSupNorm (iteratedFDeriv ℝ m (G t)) ≤
        ∑ j ∈ Finset.range (n + 1), ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (G t)) :=
      Finset.single_le_sum (f := fun j => ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (G t)))
        (fun j _ => mul_nonneg (pow_nonneg hℓ.le _) (Real.iSup_nonneg fun _ => norm_nonneg _))
        (Finset.mem_range.mpr (by omega))
    calc ℓ ^ m * ‖iteratedFDeriv ℝ m (G t) b‖ ≤ ℓ ^ m * spatialSupNorm (iteratedFDeriv ℝ m (G t)) :=
          mul_le_mul_of_nonneg_left hsup (pow_nonneg hℓ.le _)
      _ ≤ K₁ n * D ^ C₁ := hterm.trans (h58 n _ (hι t))
      _ ≤ B n := mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hD0.le _)
  -- the coefficients of `d̃`
  let card3 : ℕ → ℝ := fun n => ((hierarchyAdmissibleWords (Fin 3) n).card : ℝ)
  have hcard3 (n : ℕ) : 0 ≤ card3 n := Nat.cast_nonneg _
  let Nc : ℕ → ℝ := fun n => card3 n * B n
  let Nk : ℕ → ℝ := fun n => card3 n * (‖k‖ * B n)
  have hcL : ∀ n i j, FieldNormFinite ℓ h n (fun t (x : Vec3 × ℝ) => labelCoef G i j t x.1) ∧
      fieldNorm ℓ h n (fun t (x : Vec3 × ℝ) => labelCoef G i j t x.1) ≤ Nc n := by
    intro n i j
    obtain ⟨h1, h2⟩ := coef_bounds (labelFunctional i j) hℓ.le h n (hB n) hGsm hunif (hjet n)
    have hLB : ‖labelFunctional i j‖ * B n ≤ B n := by
      simpa using mul_le_mul_of_nonneg_right (norm_labelFunctional_le i j) (hB n)
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left hLB (hcard3 n))⟩
  have hcP : ∀ n i, FieldNormFinite ℓ h n (fun t (x : Vec3 × ℝ) => phaseCoef G k i t x.1) ∧
      fieldNorm ℓ h n (fun t (x : Vec3 × ℝ) => phaseCoef G k i t x.1) ≤ Nk n := by
    intro n i
    obtain ⟨h1, h2⟩ := coef_bounds (phaseFunctional k i) hℓ.le h n (hB n) hGsm hunif (hjet n)
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (norm_phaseFunctional_le k i) (hB n)) (hcard3 n))⟩
  -- the graph at time `t`
  have hA : ContDiff ℝ ∞ (X (ι t) 0) := hAs _ (hι t)
  have hGA' : ∀ x, G t (X (ι t) 0 x) = fderiv ℝ (X (ι t) 0) x := hGA _ (hι t)
  have hγt : 0 ≤ γ t := (hγ t).le
  have hN (n : ℕ) : 0 ≤ N n := fieldNorm_nonneg (hfin n)
  have hDpow (n : ℕ) : 1 ≤ D ^ n := one_le_pow₀ hD
  have hlam32 : 1 ≤ lam ^ (3 / 2 : ℝ) := Real.one_le_rpow hlam (by norm_num)
  have hprodle {κ : ℕ → ℝ} {Λ : ℝ} (hκ0 : ∀ l, 0 ≤ κ l) (hκ : ∀ l, κ l ≤ wordConst K₁ l * Λ)
      (j : ℕ) : (∏ l ∈ Finset.range j, κ l) ≤ (∏ l ∈ Finset.range j, wordConst K₁ l) * Λ ^ j := by
    calc (∏ l ∈ Finset.range j, κ l) ≤ ∏ l ∈ Finset.range j, (wordConst K₁ l * Λ) :=
          Finset.prod_le_prod (fun l _ => hκ0 l) (fun l _ => hκ l)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  refine ⟨?_, fun hpi => ?_⟩
  · -- general fields
    let κ : ℕ → ℝ := fun l => productConst l * (9 * Nc l * ℓ⁻¹ + 3 * Nk l * h⁻¹)
    have hκ0 (l : ℕ) : 0 ≤ κ l := by
      have := hcard3 l; have := hB l; have := productConst_nonneg l
      have : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr hℓ.le
      have : 0 ≤ h⁻¹ := inv_nonneg.mpr hh.le
      dsimp only [κ, Nc, Nk]; positivity
    have hκ (l : ℕ) : κ l ≤ wordConst K₁ l * (D ^ (C₁ + a + 1) * lam ^ (3 / 2 : ℝ)) := by
      have hkh : ‖k‖ * h⁻¹ ≤ D * lam ^ (3 / 2 : ℝ) := by
        rw [hhinv, rpow_three_halves hlam0, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hlam0.le _)
      have hinner : 9 * ℓ⁻¹ + 3 * (‖k‖ * h⁻¹) ≤ 12 * (D ^ (a + 1) * lam ^ (3 / 2 : ℝ)) := by
        have h1 : D ^ a ≤ D ^ (a + 1) * lam ^ (3 / 2 : ℝ) :=
          (pow_le_pow_right₀ hD (Nat.le_succ a)).trans (le_mul_of_one_le_right (by positivity) hlam32)
        have h2 : D * lam ^ (3 / 2 : ℝ) ≤ D ^ (a + 1) * lam ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (by simpa using pow_le_pow_right₀ hD (Nat.le_add_left 1 a))
            (by positivity)
        rw [hℓinv]
        linarith
      have hpos : 0 ≤ productConst l * card3 l * B l :=
        mul_nonneg (mul_nonneg (productConst_nonneg l) (hcard3 l)) (hB l)
      calc κ l = productConst l * card3 l * B l * (9 * ℓ⁻¹ + 3 * (‖k‖ * h⁻¹)) := by
            dsimp only [κ, Nc, Nk]; ring
        _ ≤ productConst l * card3 l * B l * (12 * (D ^ (a + 1) * lam ^ (3 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hinner hpos
        _ = _ := by
            dsimp only [wordConst, B, M, card3]
            rw [show C₁ + a + 1 = C₁ + (a + 1) by ring, pow_add]
            ring
    have hW := words_general hD_1 hℓ hh hγ hcL hcP hfin
    obtain ⟨h1, h2⟩ := graph_from_words hγ hfin (P := fun j => ∏ l ∈ Finset.range j, κ l)
      (fun j => Finset.prod_nonneg fun l _ => hκ0 l) hW t hA (hGsm t) hGA' m
    exact final_bounds (one_le_mul_of_one_le_of_one_le (hDpow _) hlam32) hγt (hN m) (hN (m + 1))
      (hprodle hκ0 hκ) h1 h2
  · -- phase-independent fields
    let κ : ℕ → ℝ := fun l => productConst l * (9 * Nc l * ℓ⁻¹)
    have hκ0 (l : ℕ) : 0 ≤ κ l := by
      have := hcard3 l; have := hB l; have := productConst_nonneg l
      have : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr hℓ.le
      dsimp only [κ, Nc]; positivity
    have hκ (l : ℕ) : κ l ≤ wordConst K₁ l * D ^ (C₁ + a + 1) := by
      have hpos : 0 ≤ productConst l * card3 l * M l := by
        have := hM l; have := hcard3 l; have := productConst_nonneg l; positivity
      calc κ l = 9 * (productConst l * card3 l * M l) * D ^ (C₁ + a) := by
            dsimp only [κ, Nc, B]; rw [hℓinv, pow_add]; ring
        _ ≤ 9 * (productConst l * card3 l * M l) * D ^ (C₁ + a + 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (Nat.le_succ (C₁ + a)))
              (by positivity)
        _ ≤ 12 * (productConst l * card3 l * M l) * D ^ (C₁ + a + 1) := by
            have : 0 ≤ (productConst l * card3 l * M l) * D ^ (C₁ + a + 1) :=
              mul_nonneg hpos (by positivity)
            linarith
        _ = _ := by dsimp only [wordConst, M, card3]; ring
    have hW := words_phaseIndep hD_1 hℓ hh hγ hcL hcP hpi hfin
    obtain ⟨h1, h2⟩ := graph_from_words hγ hfin (P := fun j => ∏ l ∈ Finset.range j, κ l)
      (fun j => Finset.prod_nonneg fun l _ => hκ0 l) hW t hA (hGsm t) hGA' m
    exact final_bounds (hDpow _) hγt (hN m) (hN (m + 1)) (hprodle hκ0 hκ) h1 h2

end

end TorusEuler.Paper.S5b

namespace TorusEuler.Paper

open Set
open scoped ContDiff InnerProductSpace

/-- Proof of **Lemma 5.7** (`cc:uf:hier:lem:physical`), following
`sections/08_exact_wave.tex:51-74`, for (5.44), (5.45) (`main.aux`).

* `h5_1` (Proposition 5.1) supplies the bounds of the coefficient `(D_aX)⁻¹` of
  `d̃ = (D_aX)^{-T}(∇_a + k_*∂_s)`: (D.6) (uniform jets, for the finiteness of the coefficient
  norms) and (5.8) `∑_{j≤n} ℓ_*^j |∇^j (D_aX)⁻¹| ≤ C_n 𝖣^{C₁}` (`08_exact_wave.tex:61-62`,
  "by Lemma D.1 and (5.8)"), the latter with `ℓ_* = 𝖣^{-a} ≤ 𝖣^{-C₁}` since `a ≥ a₀ = C₁+1`.
* `hD_1` (Lemma D.1) gives the one-step bound
  `∑_i ‖d̃_i g‖_{[n],γ} ≤ C_n 𝖣^C λ^{3/2} ‖g‖_{[n+1],γ}` (`08_exact_wave.tex:57-63`): (D.4)
  for the products of the coefficients `G_{ji}`, `k_*·G e_i` with the derivatives, (D.3) for
  the label and phase derivatives (`S5b.tilde_step`), used at every step of the iteration
  (`S5b.words_general`, `S5b.words_phaseIndep`) on `[t₀,T]` with the weight `γ` and on
  `[0,T]` with weight one.
* Glue: the chain rule (3.1) (`S5b.spatialDerivativeWord_graph`), `|k_*| ≤ 𝖣λ` from (5.3)
  (`|κ(t₀,0)| = λ`, `|D_aX| ≤ 𝖣`), `h⁻¹ = λ^{1/2}`, `sup |g(t)| ≤ γ(t)‖g‖_{[0],γ}` and the
  Hölder bound with one more derivative (`S5b.graph_from_words`).

The exponent is `C = C₁ + a + 1` with the exponent `C₁` of Proposition 5.1; the constants
`C_m` are `S5b.lemma57Const` of the constants of (5.8). The hypothesis that `g₀` is phase
independent outside `supp g` is not needed: lattice-twisted profiles are smooth and
periodic on all of `ℝ³ × ℝ`, which is the use the text makes of it
(`08_exact_wave.tex:52-54`). -/
theorem Proof.lemma_5_7_of (h5_1 : Statement.proposition_5_1) (hD_1 : Statement.lemma_D_1) :
    Statement.lemma_5_7 := by
  obtain ⟨C₁, K₁, h51⟩ := h5_1
  obtain ⟨_, h51'⟩ := h51 (fun _ => 0)
  refine ⟨C₁ + 1, fun a ha => ⟨C₁ + a + 1, S5b.lemma57Const K₁, ?_⟩⟩
  intro T hT U X pU k D lam t₀ center hP hL hO E _ _ g₀ ℓ h γ _ F bound
  obtain ⟨hD6, -, h58⟩ := h51' hT hP hL
  have hD : 1 ≤ D := Bridge.Parent.scale_ge_one hP
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hlam : 1 ≤ lam := hP.frequency_ge_one
  have hℓpos : 0 < ℓ := Bridge.radius_pos hP a
  have hℓle : ℓ ≤ (D ^ C₁)⁻¹ :=
    inv_anti₀ (pow_pos hD0 _) (pow_le_pow_right₀ hD (by omega))
  -- `|k_*| ≤ 𝖣λ`, from (5.3): `k_* = (D_aX(t₀,0))^T κ(t₀,0)` and `|κ(t₀,0)| = λ`
  have hk : ‖k‖ ≤ D * lam := by
    rw [← Bridge.Launch.carrier_eq hP hL]
    refine ((ContinuousLinearMap.adjoint (fderiv ℝ (X 0 t₀) (0 : Vec3))).le_opNorm _).trans ?_
    rw [LinearIsometryEquiv.norm_map, hL.frequency]
    exact mul_le_mul_of_nonneg_right (hP.deformation_le t₀ (Bridge.Launch.start_mem hL) 0)
      (zero_le_one.trans hlam)
  -- the flow, its inverse and the coframe `(D_aX)⁻¹`
  obtain ⟨Kl, hKl⟩ := Bridge.Parent.exists_lipschitz hT hP
  have hAs : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (X t 0) := fun t ht =>
    S5b.slice_contDiff (hP.flow.contDiffOn_inverseLabelFlow hT hP.velocity_smooth
      hP.velocity_periodic) ht
  have hGs : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (fun b => fderiv ℝ (X t 0) (X 0 t b)) := fun t ht =>
    S5b.slice_contDiff (hP.flow.contDiffOn_inverseLabelDerivative hT hP.velocity_smooth
      hP.velocity_periodic) ht
  have hGA : ∀ t ∈ Icc 0 T, ∀ x, fderiv ℝ (X t 0) (X 0 t (X t 0 x)) = fderiv ℝ (X t 0) x :=
    fun t ht x => by rw [(hP.flow.inverse hKl (left_mem_Icc.mpr hT.le) ht).2 x]
  have hD6' : ∀ m, ∀ t ∈ Icc 0 T, ∀ b,
      ‖iteratedFDeriv ℝ m (fun b => fderiv ℝ (X t 0) (X 0 t b)) b‖ ≤ K₁ m * D ^ (C₁ * (m + 1)) :=
    fun m t ht b => (hD6 m t ht b).2.1
  have h58' : ∀ n, ∀ t ∈ Icc 0 T,
      (∑ j ∈ Finset.range (n + 1), S5.radius D a ^ j *
        spatialSupNorm (iteratedFDeriv ℝ j (fun b => fderiv ℝ (X t 0) (X 0 t b)))) ≤
        K₁ n * D ^ C₁ := fun n t ht => (h58 ℓ hℓpos hℓle n t ht).2.1
  -- the two time domains
  have hfinW (n : ℕ) := Bridge.fieldNormFinite_weighted hT ℓ h n hL.start_nonneg hL.start_lt.le
    (Bridge.Origin.weight_continuousOn hO) (Bridge.Origin.weight_pos hP hO) g₀
  have hfinU (n : ℕ) := Bridge.fieldNormFinite_weighted_one hT ℓ h n (subset_refl _) g₀
  have hW (t : ℝ) (ht : t ∈ Icc t₀ T) (m : ℕ) :=
    S5b.domain_bounds hD_1 (I := Icc t₀ T) Subtype.val
      (fun s => Bridge.Launch.active_subset hL s.2) hD hlam hk hAs hGs hGA hD6' h58'
      (γ := Bridge.restrictWeight (Icc t₀ T) γ) (fun s => Bridge.Origin.weight_pos hP hO s s.2)
      (f := Bridge.slices (Icc t₀ T) g₀) hfinW ⟨t, ht⟩ m
  have hU (t : ℝ) (ht : t ∈ Icc 0 T) (m : ℕ) :=
    S5b.domain_bounds hD_1 (I := Icc 0 T) Subtype.val (fun s => s.2) hD hlam hk hAs hGs hGA
      hD6' h58' (γ := fun _ => (1 : ℝ)) (fun _ => zero_lt_one)
      (f := Bridge.slices (Icc 0 T) g₀) hfinU ⟨t, ht⟩ m
  have huNorm (n : ℕ) : S5.uNorm ℓ h n g₀ =
      AppendixD.weightedFieldNorm ℓ h (fun _ : Icc 0 T => (1 : ℝ)) n (Bridge.slices (Icc 0 T) g₀) :=
    Bridge.uNorm_eq_weightedFieldNorm_one ℓ h n g₀
  have hpiI {A : Set ℝ} (hA : A ⊆ Icc 0 T)
      (hpi : ∀ t ∈ Icc 0 T, ∀ x s, g₀.val.val.val (t, x, s) = g₀.val.val.val (t, x, 0)) :
      S5b.PhaseIndep (Bridge.slices A g₀) := fun t x s => hpi t (hA t.2) x s
  refine ⟨fun m t ht => (hW t ht m).1, fun m t ht => ?_, fun hpi => ⟨fun m t ht =>
    (hW t ht m).2 (hpiI (Bridge.Launch.active_subset hL) hpi), fun m t ht => ?_⟩⟩
  · rw [show (fun n => S5.uNorm ℓ h n g₀) = fun n => AppendixD.weightedFieldNorm ℓ h
        (fun _ : Icc 0 T => (1 : ℝ)) n (Bridge.slices (Icc 0 T) g₀) from funext huNorm]
    exact (hU t ht m).1
  · rw [show (fun n => S5.uNorm ℓ h n g₀) = fun n => AppendixD.weightedFieldNorm ℓ h
        (fun _ : Icc 0 T => (1 : ℝ)) n (Bridge.slices (Icc 0 T) g₀) from funext huNorm]
    exact (hU t ht m).2 (hpiI (subset_refl _) hpi)

end TorusEuler.Paper
