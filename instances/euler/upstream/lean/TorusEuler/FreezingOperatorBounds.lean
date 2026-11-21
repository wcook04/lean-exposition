import TorusEuler.FreezingSymbol
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum

open ContinuousLinearMap Set
open scoped InnerProductSpace Nat

namespace TorusEuler

section Inversion

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The derivatives of Banach-algebra inversion at a unit have a factorial bound
with one factor of the inverse for each derivative and one for the value. -/
theorem norm_iteratedFDeriv_ringInverse_le (z : Aˣ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (Ring.inverse : A → A) (z : A)‖ ≤
      n.factorial * max 1 ‖(1 : A)‖ * ‖(↑z⁻¹ : A)‖ ^ (n + 1) := by
  let L : A →L[ℝ] A := -mul ℝ A (↑z⁻¹ : A)
  let R : A →L[ℝ] A := (mul ℝ A).flip (↑z⁻¹ : A)
  let g (y : A) := Ring.inverse (1 - y)
  have hL : ‖L‖ ≤ ‖(↑z⁻¹ : A)‖ := by
    refine opNorm_le_bound _ (norm_nonneg _) fun y => ?_
    change ‖-((↑z⁻¹ : A) * y)‖ ≤ _
    rw [norm_neg]
    exact norm_mul_le _ _
  have hR : ‖R‖ ≤ ‖(↑z⁻¹ : A)‖ := by
    refine opNorm_le_bound _ (norm_nonneg _) fun y => ?_
    change ‖y * (↑z⁻¹ : A)‖ ≤ _
    rw [mul_comm ‖(↑z⁻¹ : A)‖]
    exact norm_mul_le _ _
  have hinv : (fun y : A => Ring.inverse ((z : A) + y)) = R ∘ (g ∘ L) := by
    funext y
    have hz : (z : A) * (1 - L y) = (z : A) + y := by
      change (z : A) * (1 - -((↑z⁻¹ : A) * y)) = (z : A) + y
      rw [sub_neg_eq_add, mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
    rw [← hz, Ring.inverse_mul (Or.inl z.isUnit), Ring.inverse_unit]
    rfl
  have hseries : HasFPowerSeriesOnBall g (formalMultilinearSeries_geometric ℝ A) (L 0) 1 := by
    simpa only [map_zero] using hasFPowerSeriesOnBall_inverse_one_sub ℝ A
  have htranslated := R.comp_hasFPowerSeriesOnBall (hseries.compContinuousLinearMap (u := L))
  have hshift := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := (Ring.inverse : A → A)) n (z : A) 0
  rw [add_zero, hinv] at hshift
  rw [← hshift]
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  rw [htranslated.iteratedFDeriv_eq_sum_of_completeSpace]
  have hterm (σ : Equiv.Perm (Fin n)) :
      ‖R (formalMultilinearSeries_geometric ℝ A n (fun i => L (v (σ i))))‖ ≤
        (max 1 ‖(1 : A)‖ * ‖(↑z⁻¹ : A)‖ ^ (n + 1)) * ∏ i, ‖v i‖ := by
    calc
      _ ≤ ‖R‖ * (‖formalMultilinearSeries_geometric ℝ A n‖ * ∏ i, ‖L (v (σ i))‖) :=
        R.le_opNorm_of_le ((formalMultilinearSeries_geometric ℝ A n).le_opNorm _)
      _ ≤ ‖(↑z⁻¹ : A)‖ * (max 1 ‖(1 : A)‖ * ∏ i, (‖(↑z⁻¹ : A)‖ * ‖v (σ i)‖)) := by
        gcongr with i
        · exact formalMultilinearSeries_geometric_apply_norm_le ℝ A n
        · exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Equiv.prod_comp σ (fun i => ‖v i‖), pow_succ]
        ring
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin n),
        ‖R (formalMultilinearSeries_geometric ℝ A n (fun i => L (v (σ i))))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n),
        (max 1 ‖(1 : A)‖ * ‖(↑z⁻¹ : A)‖ ^ (n + 1)) * ∏ i, ‖v i‖ :=
      Finset.sum_le_sum fun σ _ => hterm σ
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
      ring

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A bound for the derivatives of a smooth operator family transfers to its inverse.
The open set allows the use of ambient Fréchet derivatives at each point. -/
theorem norm_iteratedFDeriv_ringInverse_comp_le {s : Set X} (hs : IsOpen s)
    {F : X → A} {x : X} (hx : x ∈ s) {n : ℕ}
    (hF : ContDiffOn ℝ n F s) (hunit : ∀ y ∈ s, IsUnit (F y))
    {K D : ℝ} (hK : 1 ≤ K) (hKx : ‖Ring.inverse (F x)‖ ≤ K)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i F x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (Ring.inverse ∘ F) x‖ ≤
      (n.factorial : ℝ) ^ 2 * max 1 ‖(1 : A)‖ * K ^ (n + 1) * D ^ n := by
  let U : Set A := {z | IsUnit z}
  have hU : IsOpen U := Units.isOpen
  have hmaps : MapsTo F s U := hunit
  have hg : ContDiffOn ℝ n (Ring.inverse : A → A) U := by
    intro z hz
    obtain ⟨u, rfl⟩ := hz
    exact (contDiffAt_ringInverse ℝ u).contDiffWithinAt
  let C : ℝ := (n.factorial : ℝ) * max 1 ‖(1 : A)‖ * K ^ (n + 1)
  have hbound (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i (Ring.inverse : A → A) U (F x)‖ ≤ C := by
    have hgi : ContDiffAt ℝ i (Ring.inverse : A → A) (F x) :=
      (hg.contDiffAt (hU.mem_nhds (hmaps hx))).of_le (by exact_mod_cast hi)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn hgi (hmaps hx)]
    obtain ⟨u, hu⟩ := hunit x hx
    rw [← hu] at hKx ⊢
    rw [Ring.inverse_unit] at hKx
    refine (norm_iteratedFDeriv_ringInverse_le u i).trans ?_
    calc
      _ ≤ (i.factorial : ℝ) * max 1 ‖(1 : A)‖ * K ^ (i + 1) := by
        gcongr
      _ ≤ C := by
        dsimp only [C]
        gcongr
  have hinput (i : ℕ) (hi₁ : 1 ≤ i) (hi₂ : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i F s x‖ ≤ D ^ i := by
    have hFi : ContDiffAt ℝ i F x :=
      (hF.contDiffAt (hs.mem_nhds hx)).of_le (by exact_mod_cast hi₂)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn hFi hx]
    exact hD i hi₁ hi₂
  have h := norm_iteratedFDerivWithin_comp_le hg hF (n := n) le_rfl hU.uniqueDiffOn
    hs.uniqueDiffOn hmaps hx hbound hinput
  have hcomp := (hg.comp hF hmaps).contDiffAt (hs.mem_nhds hx)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn hcomp hx] at h
  calc
    _ ≤ (n.factorial : ℝ) * C * D ^ n := h
    _ = _ := by dsimp only [C]; ring

end Inversion

section DirectSymbol

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The derivative of the direct frozen symbol is bounded by the Leibniz estimate
for `r * B * r` and the derivative bound for `r`. -/
theorem norm_iteratedFDeriv_frozenSymbol_comp_le {s : Set X} (hs : IsOpen s)
    {r : X → E →L[ℝ] E} (B : E →L[ℝ] E) {x : X} (hx : x ∈ s) {i : ℕ}
    (hi : 0 < i) (hr : ContDiffOn ℝ i r s) {D : ℝ}
    (hD : 0 ≤ D) (hderiv : ∀ j, j ≤ i → ‖iteratedFDeriv ℝ j r x‖ ≤ D ^ j) :
    ‖iteratedFDeriv ℝ i (fun y => frozenSymbol (r y) B) x‖ ≤ (‖B‖ + 1) * (2 * D) ^ i := by
  let A := E →L[ℝ] E
  let mulB : A →L[ℝ] A := (mul ℝ A).flip B
  have hmulB : ‖mulB‖ ≤ ‖B‖ := by
    refine opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    change ‖v * B‖ ≤ ‖B‖ * ‖v‖
    rw [mul_comm]
    exact norm_mul_le _ _
  let f (y : X) := r y * B
  let g (y : X) := f y * r y
  let c (_ : X) : A := 1
  have hf : ContDiffOn ℝ i f s := hr.mul contDiffOn_const
  have hg : ContDiffOn ℝ i g s := hf.mul hr
  have hc : ContDiffOn ℝ i c s := contDiffOn_const
  have hwithin (j : ℕ) (hj : j ≤ i) : ‖iteratedFDerivWithin ℝ j r s x‖ ≤ D ^ j := by
    have hj' : ContDiffAt ℝ j r x := (hr.contDiffAt (hs.mem_nhds hx)).of_le (by exact_mod_cast hj)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn hj' hx]
    exact hderiv j hj
  have hfbound (j : ℕ) (hj : j ≤ i) :
      ‖iteratedFDerivWithin ℝ j f s x‖ ≤ ‖B‖ * D ^ j := by
    change ‖iteratedFDerivWithin ℝ j (mulB ∘ r) s x‖ ≤ _
    exact (mulB.norm_iteratedFDerivWithin_comp_left (hr x hx) hs.uniqueDiffOn hx
      (by exact_mod_cast hj)).trans (mul_le_mul hmulB (hwithin j hj) (norm_nonneg _) (norm_nonneg _))
  have hgbound : ‖iteratedFDerivWithin ℝ i g s x‖ ≤ ‖B‖ * (2 * D) ^ i := by
    refine (norm_iteratedFDerivWithin_mul_le hf hr hs.uniqueDiffOn hx le_rfl).trans ?_
    calc
      _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * ‖B‖ * D ^ i := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        calc
          _ ≤ (i.choose j : ℝ) * (‖B‖ * D ^ j) * D ^ (i - j) := by
            gcongr
            · exact hfbound j hj'
            · exact hwithin (i - j) (Nat.sub_le _ _)
          _ = (i.choose j : ℝ) * ‖B‖ * (D ^ j * D ^ (i - j)) := by ring
          _ = _ := by rw [← pow_add, Nat.add_sub_of_le hj']
      _ = _ := by
        have hchoose : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) = (2 : ℝ) ^ i := by
          exact_mod_cast Nat.sum_range_choose i
        rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose, mul_pow]
        ring
  have hFg : ContDiffOn ℝ i (fun y => frozenSymbol (r y) B) s := hg.add (hc.sub hr)
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn (hFg.contDiffAt (hs.mem_nhds hx)) hx]
  change ‖iteratedFDerivWithin ℝ i (g + (c - r)) s x‖ ≤ _
  rw [iteratedFDerivWithin_add_apply (f := g) (g := c - r) (hg x hx)
      ((hc.sub hr) x hx) hs.uniqueDiffOn hx,
    iteratedFDerivWithin_sub_apply (f := c) (g := r) (hc x hx) (hr x hx) hs.uniqueDiffOn hx]
  change ‖iteratedFDerivWithin ℝ i g s x +
      (iteratedFDerivWithin ℝ i (fun _ : X => (1 : A)) s x - _)‖ ≤ _
  simp only [iteratedFDerivWithin_const_of_ne hi.ne' (1 : A) s, Pi.zero_apply, zero_sub]
  have hmono : D ^ i ≤ (2 * D) ^ i := by gcongr; linarith
  calc
    _ ≤ ‖iteratedFDerivWithin ℝ i g s x‖ + ‖iteratedFDerivWithin ℝ i r s x‖ := by
      rw [← norm_neg (iteratedFDerivWithin ℝ i r s x)]
      exact norm_add_le _ _
    _ ≤ ‖B‖ * (2 * D) ^ i + (2 * D) ^ i :=
      add_le_add hgbound ((hwithin i le_rfl).trans hmono)
    _ = _ := by ring

end DirectSymbol

section FrozenProjection

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Given the derivative bounds of the direct symbol, the inverse-symbol derivative bound
in the proof of Lemma A.2 depends only on those bounds and the coercivity constant. -/
theorem norm_iteratedFDeriv_frozenSymbol_inverse_comp_le {s : Set X} (hs : IsOpen s)
    {r : X → E →L[ℝ] E} {B : E →L[ℝ] E} {μ : ℝ} (hμ : 0 < μ)
    (hr : ∀ y ∈ s, (r y : E →ₗ[ℝ] E).IsSymmetricProjection)
    (hB : ∀ y ∈ s, ∀ v, r y v = v → μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ)
    {x : X} (hx : x ∈ s) {n : ℕ} {D : ℝ}
    (hF : ContDiffOn ℝ n (fun y => frozenSymbol (r y) B) s)
    (hD : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i (fun y => frozenSymbol (r y) B) x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (fun y => Ring.inverse (frozenSymbol (r y) B)) x‖ ≤
      (n.factorial : ℝ) ^ 2 * ((min 1 μ)⁻¹) ^ (n + 1) * D ^ n := by
  have hK : 1 ≤ (min 1 μ)⁻¹ := (one_le_inv₀ (lt_min zero_lt_one hμ)).mpr (min_le_left _ _)
  have hopen (y : X) (hy : y ∈ s) : IsUnit (frozenSymbol (r y) B) :=
    frozenSymbol_isUnit (hr y hy) hμ (hB y hy)
  have hKx := norm_frozenSymbol_inverse_le (hr x hx) hμ (hB x hx)
  have hone : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  simpa only [Function.comp_def, max_eq_left hone, mul_one] using
    norm_iteratedFDeriv_ringInverse_comp_le hs hx hF hopen hK hKx hD

/-- The inverse frozen symbol has polynomial bounds at every fixed order in
the projection derivative bound, the norm of `B` and the reciprocal coercivity. -/
theorem norm_iteratedFDeriv_frozenSymbol_inverse_of_projection_bounds
    {s : Set X} (hs : IsOpen s) {r : X → E →L[ℝ] E} {B : E →L[ℝ] E} {μ : ℝ} (hμ : 0 < μ)
    (hr : ∀ y ∈ s, (r y : E →ₗ[ℝ] E).IsSymmetricProjection)
    (hB : ∀ y ∈ s, ∀ v, r y v = v → μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ)
    {x : X} (hx : x ∈ s) {n : ℕ} {D : ℝ} (hrDiff : ContDiffOn ℝ n r s)
    (hD : 0 ≤ D) (hderiv : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i r x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (fun y => Ring.inverse (frozenSymbol (r y) B)) x‖ ≤
      (n.factorial : ℝ) ^ 2 * ((min 1 μ)⁻¹) ^ (n + 1) * (2 * D * (‖B‖ + 1)) ^ n := by
  have hconst : ContDiffOn ℝ n (fun _ : X => B) s := contDiffOn_const
  have hone : ContDiffOn ℝ n (fun _ : X => (1 : E →L[ℝ] E)) s := contDiffOn_const
  have hF : ContDiffOn ℝ n (fun y => frozenSymbol (r y) B) s :=
    ((hrDiff.mul hconst).mul hrDiff).add (hone.sub hrDiff)
  refine norm_iteratedFDeriv_frozenSymbol_inverse_comp_le hs hμ hr hB hx hF ?_
  intro i hi₁ hi₂
  have hiDiff : ContDiffOn ℝ i r s := hrDiff.of_le (by exact_mod_cast hi₂)
  have hnorm : 1 ≤ ‖B‖ + 1 := by linarith [norm_nonneg B]
  have hpow : ‖B‖ + 1 ≤ (‖B‖ + 1) ^ i := by
    simpa only [pow_one] using pow_le_pow_right₀ hnorm hi₁
  calc
    _ ≤ (‖B‖ + 1) * (2 * D) ^ i :=
      norm_iteratedFDeriv_frozenSymbol_comp_le hs B hx hi₁ hiDiff hD
        (fun j hj => hderiv j (hj.trans hi₂))
    _ ≤ (‖B‖ + 1) ^ i * (2 * D) ^ i := mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = _ := by rw [← mul_pow, mul_comm (‖B‖ + 1)]

end FrozenProjection

end TorusEuler
