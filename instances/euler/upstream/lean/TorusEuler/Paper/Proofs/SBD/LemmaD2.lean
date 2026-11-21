import TorusEuler.Paper.SBD.Statements
import TorusEuler.Paper.Proofs.SBD.Library.Coordinate

/-! # Proof of Lemma D.2 (products, inverses and weighted norms of coefficients)

Conditional proof `Paper.Proof.lemma_D_2` of `Paper.Statement.lemma_D_2`
(`cc:uf:trunc:lem:coefficients`, sections/appD_finite_norms.tex:93-122 of the
latest manuscript). Lemma D.2 is a leaf of the proof spine: its TeX proof cites
no other numbered result, so the Lean proof has no hypotheses. -/

open MeasureTheory Set
open scoped ContDiff

namespace TorusEuler.Paper

open AppendixD Lib.SBD

/-- Proof of **Lemma D.2** (`cc:uf:trunc:lem:coefficients`), following
sections/appD_finite_norms.tex:107-122. The TeX proof cites no numbered
result, so this leaf has no hypotheses. Throughout, (D.6)
`cc:uf:trunc:eq:power` is converted to pointwise bounds on the operator norms
of the iterated label derivatives (`Lib.SBD.coefficientPower_pointwise`,
`‖D^m c‖ ≤ 3^m C_m 𝖣^{a(m+1)}`) and back
(`Lib.SBD.coefficientPower_of_pointwise`).

* appD:108-110, (a): "take `C` large enough": both coefficients obey
  `‖D^i‖ ≤ B_n 𝖣^{e(i+1)}` for `i ≤ n`, with `e = max(a, b)` and
  `B_n = 1 + ∑_{i≤n} 3^i max(0, C_i)`; Leibniz' rule for the bilinear product
  (`norm_iteratedFDeriv_bilinear_scaled_le`, own content of D.2) gives
  `|cd|_n ≤ C_n 𝖣^{e(n+2)}`, hence (D.6) with exponent `2e`, and
  `C''_n = #W_n 2^n B_n B'_n`.
* appD:111-117, (b): differentiating `c e = I` and inducting from
  `|e|_0 ≤ 𝖣^C` is the jet bound of the inverse
  (`norm_iteratedFDeriv_ringInverse_comp_le`, own content of D.2), applied with
  `E = max(a, e)`; it gives `|c^{-1}|_n ≤ C_n 𝖣^{E(3n+1)}`, hence (D.6) with
  exponent `3E`, and `C''_n = #W_n (n!)² max(1, ‖1‖) B_n^n`.
* appD:118-121, (c): `ℓ_*^m |c|_m ≤ C_m 𝖣^a (ℓ_* 𝖣^a)^m` with `ℓ_* 𝖣^a ≤ 1`;
  summing over `m ≤ n` gives the first bound, and retaining one factor
  `ℓ_* 𝖣^a` for `m ≥ 1` (`hierarchy_weighted_coefficient_le`, own content of
  D.2) gives the second; `C'_n = ∑_{m≤n} max(0, C_m)`. -/
theorem Proof.lemma_D_2 : Statement.lemma_D_2 := by
  refine ⟨?_, ?_, ?_⟩
  · -- (a) products
    intro X Y Z _ _ _ _ _ _ C C' a b
    let Bc (n : ℕ) : ℝ := 1 + ∑ i ∈ Finset.range (n + 1), 3 ^ i * max 0 (C i)
    let Bd (n : ℕ) : ℝ := 1 + ∑ i ∈ Finset.range (n + 1), 3 ^ i * max 0 (C' i)
    have hBc (n : ℕ) : 1 ≤ Bc n :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
    have hBd (n : ℕ) : 1 ≤ Bd n :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
    refine ⟨fun n => (appendixCoefficientOrderWords n).card * ((2 : ℝ) ^ n * (Bc n * Bd n)),
      fun n => by have := hBc n; have := hBd n; positivity, ?_⟩
    intro B hB I D hD c d hc hd
    let e := max a b
    have hD0 : 0 ≤ D := zero_le_one.trans hD
    have hpc (n : ℕ) (t : I) (x : Vec3) (i : ℕ) (hi : i ≤ n) :
        ‖iteratedFDeriv ℝ i (c t) x‖ ≤ Bc n * D ^ (e * i + e) := by
      refine (coefficientPower_pointwise hc i t x).trans ?_
      have h1 : 3 ^ i * C i ≤ Bc n := by
        refine (mul_le_mul_of_nonneg_left (le_max_right 0 (C i)) (by positivity)).trans ?_
        exact (Finset.single_le_sum (f := fun i => (3 : ℝ) ^ i * max 0 (C i))
          (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))).trans
          (le_add_of_nonneg_left zero_le_one)
      have h2 : D ^ (a * (i + 1)) ≤ D ^ (e * i + e) :=
        pow_le_pow_right₀ hD ((Nat.mul_le_mul_right (i + 1) (le_max_left a b)).trans_eq
          (by ring))
      calc
        _ = (3 ^ i * C i) * D ^ (a * (i + 1)) := by ring
        _ ≤ Bc n * D ^ (a * (i + 1)) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (zero_le_one.trans (hBc n))
    have hpd (n : ℕ) (t : I) (x : Vec3) (i : ℕ) (hi : i ≤ n) :
        ‖iteratedFDeriv ℝ i (d t) x‖ ≤ Bd n * D ^ (e * i + e) := by
      refine (coefficientPower_pointwise hd i t x).trans ?_
      have h1 : 3 ^ i * C' i ≤ Bd n := by
        refine (mul_le_mul_of_nonneg_left (le_max_right 0 (C' i)) (by positivity)).trans ?_
        exact (Finset.single_le_sum (f := fun i => (3 : ℝ) ^ i * max 0 (C' i))
          (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))).trans
          (le_add_of_nonneg_left zero_le_one)
      have h2 : D ^ (b * (i + 1)) ≤ D ^ (e * i + e) :=
        pow_le_pow_right₀ hD ((Nat.mul_le_mul_right (i + 1) (le_max_right a b)).trans_eq
          (by ring))
      calc
        _ = (3 ^ i * C' i) * D ^ (b * (i + 1)) := by ring
        _ ≤ Bd n * D ^ (b * (i + 1)) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (zero_le_one.trans (hBd n))
    have hsm (t : I) : ContDiff ℝ ∞ (fun y => B (c t y) (d t y)) :=
      B.isBoundedBilinearMap.contDiff.comp ((hc.1 t).prodMk (hd.1 t))
    refine coefficientPower_of_pointwise hsm (fun n => by
      have := hBc n; have := hBd n; positivity) hD0 fun n t x => ?_
    have h := norm_iteratedFDeriv_bilinear_scaled_le B hB (n := n) (p := e) (q := e) (r := e)
      ((hc.1 t).of_le (by simp)) ((hd.1 t).of_le (by simp)) x (hpc n t x) (hpd n t x)
    refine h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD
      (show e * n + e + e ≤ 2 * e * (n + 1) by nlinarith [Nat.zero_le (e * n)])) ?_)
    have := hBc n; have := hBd n; positivity
  · -- (b) inverses
    intro A _ _ _ C a e
    let Bc (n : ℕ) : ℝ := 1 + ∑ i ∈ Finset.range (n + 1), 3 ^ i * max 0 (C i)
    have hBc (n : ℕ) : 1 ≤ Bc n :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
    refine ⟨fun n => (appendixCoefficientOrderWords n).card *
      ((n.factorial : ℝ) ^ 2 * max 1 ‖(1 : A)‖ * (Bc n) ^ n), fun n => by
        have := hBc n; have : (0 : ℝ) ≤ max 1 ‖(1 : A)‖ := zero_le_one.trans (le_max_left _ _)
        positivity, ?_⟩
    intro I D hD c hc hUnit hInv
    let E := max a e
    have hD0 : 0 ≤ D := zero_le_one.trans hD
    have hpc (n : ℕ) (t : I) (x : Vec3) (i : ℕ) (hi : i ≤ n) :
        ‖iteratedFDeriv ℝ i (c t) x‖ ≤ Bc n * D ^ (E * (i + 1)) := by
      refine (coefficientPower_pointwise hc i t x).trans ?_
      have h1 : 3 ^ i * C i ≤ Bc n := by
        refine (mul_le_mul_of_nonneg_left (le_max_right 0 (C i)) (by positivity)).trans ?_
        exact (Finset.single_le_sum (f := fun i => (3 : ℝ) ^ i * max 0 (C i))
          (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))).trans
          (le_add_of_nonneg_left zero_le_one)
      have h2 : D ^ (a * (i + 1)) ≤ D ^ (E * (i + 1)) :=
        pow_le_pow_right₀ hD (Nat.mul_le_mul_right (i + 1) (le_max_left a e))
      calc
        _ = (3 ^ i * C i) * D ^ (a * (i + 1)) := by ring
        _ ≤ Bc n * D ^ (a * (i + 1)) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (zero_le_one.trans (hBc n))
    have hsm (t : I) : ContDiff ℝ ∞ (fun x => Ring.inverse (c t x)) := by
      apply contDiff_iff_contDiffAt.mpr
      intro x
      obtain ⟨u, hu⟩ := hUnit t x
      exact ((hu ▸ contDiffAt_ringInverse ℝ u).comp x (hc.1 t).contDiffAt)
    refine coefficientPower_of_pointwise hsm (fun n => by have := hBc n; positivity) hD0
      fun n t x => ?_
    have hOne : 1 ≤ D ^ E := one_le_pow₀ hD
    have hJet (i : ℕ) (hi₁ : 1 ≤ i) (hi₂ : i ≤ n) :
        ‖iteratedFDeriv ℝ i (c t) x‖ ≤ (Bc n * D ^ (2 * E)) ^ i := by
      refine (hpc n t x i hi₂).trans ?_
      rw [mul_pow, ← pow_mul]
      exact mul_le_mul (le_self_pow₀ (hBc n) (by omega))
        (pow_le_pow_right₀ hD (by nlinarith)) (by positivity)
        (zero_le_one.trans (one_le_pow₀ (hBc n)))
    have hInvE : ‖Ring.inverse (c t x)‖ ≤ D ^ E :=
      (hInv t x).trans (pow_le_pow_right₀ hD (le_max_right a e))
    have h := norm_iteratedFDeriv_ringInverse_comp_le (s := (univ : Set Vec3)) isOpen_univ
      (mem_univ x) ((hc.1 t).of_le (by simp)).contDiffOn
      (fun y _ => hUnit t y) hOne hInvE hJet
    simp only [Function.comp_def, mul_pow, ← pow_mul] at h
    refine h.trans ?_
    calc
      _ = ((n.factorial : ℝ) ^ 2 * max 1 ‖(1 : A)‖ * (Bc n) ^ n) *
            D ^ (E * (n + 1) + 2 * E * n) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by
            show E * (n + 1) + 2 * E * n ≤ 3 * E * (n + 1)
            nlinarith [Nat.zero_le (E * n)]))
          (mul_nonneg (mul_nonneg (sq_nonneg _) (zero_le_one.trans (le_max_left _ _)))
            (pow_nonneg (zero_le_one.trans (hBc n)) _))
  · -- (c) weighted norms under `ℓ_* ≤ 𝖣^{-a}`
    intro X _ _ C a
    refine ⟨fun n => ∑ m ∈ Finset.range (n + 1), max 0 (C m),
      fun n => Finset.sum_nonneg fun _ _ => le_max_left _ _, ?_⟩
    intro I D ℓ hD hℓ hℓD c hc
    have hD0 : 0 < D := zero_lt_one.trans_le hD
    have hscale : ℓ * D ^ a ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hℓD (pow_nonneg hD0.le a)
      rwa [inv_mul_cancel₀ (pow_ne_zero _ hD0.ne')] at this
    have hCm (m : ℕ) : coefficientOrderNorm m c ≤ max 0 (C m) * D ^ (a * (m + 1)) :=
      (hc.2.2 m).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    have hmain (m : ℕ) : ℓ ^ m * coefficientOrderNorm m c ≤ max 0 (C m) * D ^ a := by
      calc
        _ ≤ ℓ ^ m * (max 0 (C m) * D ^ (a * (m + 1))) :=
          mul_le_mul_of_nonneg_left (hCm m) (pow_nonneg hℓ.le _)
        _ = (ℓ * D ^ a) ^ m * (max 0 (C m) * D ^ a) := by
          rw [mul_pow, ← pow_mul, Nat.mul_succ, pow_add]
          ring
        _ ≤ _ := mul_le_of_le_one_left (mul_nonneg (le_max_left _ _) (by positivity))
          (pow_le_one₀ (mul_nonneg hℓ.le (by positivity)) hscale)
    refine ⟨fun n => ?_, fun m hm => ?_⟩
    · unfold coefficientNorm
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun m _ => hmain m
    · refine (hierarchy_weighted_coefficient_le hD hℓ.le (le_max_left 0 (C m)) hscale hm
        (hCm m)).trans ?_
      have hle : max 0 (C m) ≤ ∑ i ∈ Finset.range (m + 1), max 0 (C i) :=
        Finset.single_le_sum (f := fun i => max 0 (C i)) (fun _ _ => le_max_left _ _)
          (Finset.mem_range.mpr (Nat.lt_succ_self m))
      have := mul_le_mul_of_nonneg_right hle (by positivity : (0 : ℝ) ≤ D ^ (2 * a) * ℓ)
      simpa [mul_assoc] using this

end TorusEuler.Paper
