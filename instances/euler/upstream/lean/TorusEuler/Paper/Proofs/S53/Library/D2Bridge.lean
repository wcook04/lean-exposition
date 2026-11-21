import TorusEuler.Paper.Proofs.S53.Library.Leaves
import TorusEuler.Paper.Proofs.S5a.Library.Mono53
import TorusEuler.PaperAppendixDMultiIndex
import TorusEuler.SeedDerivativeBudgets

/-!
# S53 library: Lemma D.2 for pointwise jets

Lemma D.2 is stated for `CoefficientPower` (suprema of coordinate word derivatives). The chain behind
Lemma 5.3 works with pointwise jets `‖∂^m f x‖`. This file contains

* the conversions between the two forms (glue: coordinates of a multilinear map, permutation of
  coordinate words; adapted from the proofs of `finiteCoefficientPower_iff_multiIndex` and
  `appendixOpNorm_le_coordinateSum`, which are not reached),
* the wrappers `mul_of_D2` (Lemma D.2(a)) and `rescale_of_D2` (Lemma D.2(c)) from the hypothesis
  `Leaves.d2`, in the pointwise form used by the chain,
* the two-scale hypothesis `Leaf2` that makes the scale separation of D.2(c) explicit: the data are
  controlled at a base scale `D₀` with `D₀ ^ d2Scale ≤ D`, where `D` is the scale of the chain.
-/
open Set ContinuousLinearMap
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S53

open TorusEuler TorusEuler.Paper.AppendixD

noncomputable section

/-- Pointwise power bound `‖∂^m f x‖ ≤ C_m D^{a(m+1)}` (the pointwise form of (D.6)). -/
def JetPower {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : ℕ → ℝ) (D : ℝ) (a : ℕ) (f : Vec3 → X) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ m x, ‖iteratedFDeriv ℝ m f x‖ ≤ C m * D ^ (a * (m + 1))

/-- The power of the base scale: the chain scale `D` dominates `D₀ ^ d2Scale`. -/
def d2Scale : ℕ := 64

/-- The leaf jets at a base scale `D₀` with `D₀ ^ d2Scale ≤ D`; `D` is the scale of the chain. -/
def Leaf2 (B : ℕ → ℝ) (U : Velocity) (X : ℝ → Velocity) (T D : ℝ) (k : Vec3) (Λ : ℝ) : Prop :=
  ∃ D₀ : ℝ, 1 ≤ D₀ ∧ D₀ ^ d2Scale ≤ D ∧ Lib.S5a.LeafBounds B U X T D₀ k Λ

/-- The leaf jets at the scale `D` hold at every larger scale. -/
theorem leafBounds_mono {B : ℕ → ℝ} (hB : ∀ n, 0 ≤ B n) {U : Velocity} {X : ℝ → Velocity} {T D D' : ℝ}
    {k : Vec3} {Λ : ℝ} (hD : 1 ≤ D) (hDD' : D ≤ D') (h : Lib.S5a.LeafBounds B U X T D k Λ) :
    Lib.S5a.LeafBounds B U X T D' k Λ := by
  intro n t ht a
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h n t ht a
  have key (e : ℕ) : B n * D ^ e ≤ B n * D' ^ e :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hDD' e) (hB n)
  exact ⟨h1.trans (key _), h2.trans (key _), h3.trans (key _), h4.trans (key _), h5.trans (key _),
    h6.trans (key _), h7.trans (key _)⟩

/-- The two-scale leaf jets give the leaf jets at the chain scale. -/
theorem Leaf2.toLeaf {B : ℕ → ℝ} (hB : ∀ n, 0 ≤ B n) {U : Velocity} {X : ℝ → Velocity} {T D : ℝ}
    {k : Vec3} {Λ : ℝ} (h : Leaf2 B U X T D k Λ) : Lib.S5a.LeafBounds B U X T D k Λ := by
  obtain ⟨D₀, hD₀, hpow, hleaf⟩ := h
  exact leafBounds_mono hB hD₀ ((le_self_pow₀ hD₀ (by norm_num [d2Scale])).trans hpow) hleaf

section Bridge

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Glue: `∑_i v_i e_i = v` for the coordinate vectors of `ℝ³`. -/
private theorem labelDirection_one' : hierarchyLabelDirection 1 = fun j _ => coordinateDirection j := by
  funext j x
  exact one_smul ℝ (coordinateDirection j)

/-- The word `List.ofFn β` of coordinate derivatives is the multilinear map on the coordinate vectors. -/
theorem word_eq_coordinate (m : ℕ) (β : Fin m → Fin 3) {f : Vec3 → X} (hf : ContDiff ℝ ∞ f)
    (x : Vec3) :
    phaseOperatorWord (hierarchyLabelDirection 1) (List.ofFn β) f x =
      iteratedFDeriv ℝ m f x (fun j => coordinateDirection (β j)) := by
  rw [labelDirection_one', phaseOperatorWord_constant_eq_iteratedFDeriv _ hf]
  simp only [List.get_ofFn]
  have h (k : ℕ) (hk : k = m) :
      iteratedFDeriv ℝ k f x (fun j => coordinateDirection (β (Fin.cast hk j))) =
        iteratedFDeriv ℝ m f x (fun j => coordinateDirection (β j)) := by subst k; rfl
  exact h _ List.length_ofFn

/-- Glue: `∑_i v_i e_i = v` for the coordinate vectors of `ℝ³`. -/
private theorem sum_coordinate' (v : Vec3) : (∑ i, v i • coordinateDirection i) = v := by
  apply PiLp.ext
  intro j
  let ev := (EuclideanSpace.proj j : Vec3 →L[ℝ] ℝ)
  change ev (∑ i, v i • coordinateDirection i) = v j
  rw [map_sum]
  simp [ev, coordinateDirection, EuclideanSpace.single, PiLp.single_apply]

/-- The operator norm of a multilinear map on `ℝ³` is at most the sum of its values on coordinate vectors. -/
theorem opNorm_le_coordinateSum {m : ℕ} (D : ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec3) X) :
    ‖D‖ ≤ ∑ β : Fin m → Fin 3, ‖D (fun i => coordinateDirection (β i))‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro p
  have h := D.toMultilinearMap.map_sum (fun j i => p j i • coordinateDirection i)
  have hsum : (fun j => ∑ i, p j i • coordinateDirection i) = p :=
    funext fun j => sum_coordinate' (p j)
  rw [hsum] at h
  change D p = ∑ β : Fin m → Fin 3, D (fun j => p j (β j) • coordinateDirection (β j)) at h
  rw [h, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
  rw [show D (fun j => p j (β j) • coordinateDirection (β j)) =
    (∏ j, p j (β j)) • D (fun j => coordinateDirection (β j)) from
      D.toMultilinearMap.map_smul_univ _ _, norm_smul, Real.norm_eq_abs, Finset.abs_prod, mul_comm]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => abs_nonneg _)
    (fun j _ => PiLp.norm_apply_le (p j) (β j))) (norm_nonneg _)

/-- Every word supremum in a `CoefficientPower` is nonnegative. -/
theorem sSup_word_nonneg {I : Type} {c : I → Vec3 → X} {w : List (Fin 3)}
    (hb : BddAbove (hierarchyJetValues False (hierarchyLabelDirection 1) w c)) :
    0 ≤ sSup (hierarchyJetValues False (hierarchyLabelDirection 1) w c) :=
  le_csSup hb (Or.inl rfl)

/-- The pointwise jet of a coefficient is at most `3 ^ m` times the order-`m` size `|c|_m`. -/
theorem norm_iteratedFDeriv_le_coefficientOrderNorm {I : Type} {c : I → Vec3 → X} {C : ℕ → ℝ} {D : ℝ}
    {a : ℕ} (hc : CoefficientPower C D a c) (t : I) (m : ℕ) (x : Vec3) :
    ‖iteratedFDeriv ℝ m (c t) x‖ ≤ 3 ^ m * coefficientOrderNorm m c := by
  obtain ⟨hs, hb, -⟩ := hc
  have hterm (β : Fin m → Fin 3) :
      ‖iteratedFDeriv ℝ m (c t) x (fun j => coordinateDirection (β j))‖ ≤
        coefficientOrderNorm m c := by
    let w := (List.ofFn β).mergeSort (· ≤ ·)
    have hperm : w.Perm (List.ofFn β) := List.mergeSort_perm _ _
    have hlen : w.length = m := hperm.length_eq.trans List.length_ofFn
    have hw : w ∈ appendixCoefficientOrderWords m :=
      Finset.mem_filter.mpr ⟨mem_hierarchyAdmissibleWords.mpr
        ⟨hlen.le, List.pairwise_mergeSort' (· ≤ ·) _⟩, hlen⟩
    have hword := congrFun (phaseOperatorWord_constantDirections_perm coordinateDirection (hs t) hperm) x
    rw [← word_eq_coordinate m β (hs t), labelDirection_one', ← hword, ← labelDirection_one']
    exact (le_csSup (hb m w hw) (Or.inr (Or.inl ⟨t, x, rfl⟩))).trans
      (Finset.single_le_sum (fun v hv => sSup_word_nonneg (hb m v hv)) hw)
  calc ‖iteratedFDeriv ℝ m (c t) x‖
      ≤ ∑ β : Fin m → Fin 3, ‖iteratedFDeriv ℝ m (c t) x (fun i => coordinateDirection (β i))‖ :=
        opNorm_le_coordinateSum _
    _ ≤ ∑ _β : Fin m → Fin 3, coefficientOrderNorm m c := Finset.sum_le_sum fun β _ => hterm β
    _ = 3 ^ m * coefficientOrderNorm m c := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Pointwise jets with a power bound give a `CoefficientPower` (the size `|c|_m` is a sum over the
nondecreasing coordinate words, each of whose terms is a pointwise jet). -/
theorem coefficientPower_of_jets {I : Type} {c : I → Vec3 → X} {C : ℕ → ℝ} {D : ℝ} {a : ℕ}
    (hD : 1 ≤ D) (hC : ∀ m, 0 ≤ C m) (hs : ∀ t, ContDiff ℝ ∞ (c t))
    (h : ∀ m t x, ‖iteratedFDeriv ℝ m (c t) x‖ ≤ C m * D ^ (a * (m + 1))) :
    CoefficientPower (fun m => ((appendixCoefficientOrderWords m).card : ℝ) * C m) D a c := by
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hb (m : ℕ) (w : List (Fin 3)) (hw : w ∈ appendixCoefficientOrderWords m) :
      C m * D ^ (a * (m + 1)) ∈ upperBounds (hierarchyJetValues False (hierarchyLabelDirection 1) w c) := by
    have hlen := (Finset.mem_filter.mp hw).2
    rintro y (rfl | ⟨t, x, rfl⟩ | ⟨hf, _⟩)
    · exact mul_nonneg (hC m) (by positivity)
    · rw [labelDirection_one', phaseOperatorWord_constant_eq_iteratedFDeriv _ (hs t)]
      refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
      calc
        _ ≤ C w.length * D ^ (a * (w.length + 1)) := by
          simpa [coordinateDirection] using h w.length t x
        _ = _ := by rw [hlen]
    · exact hf.elim
  refine ⟨hs, fun m w hw => ⟨_, hb m w hw⟩, fun m => ?_⟩
  unfold coefficientOrderNorm
  calc
    _ ≤ ∑ _w ∈ appendixCoefficientOrderWords m, C m * D ^ (a * (m + 1)) :=
      Finset.sum_le_sum fun w hw => csSup_le ⟨0, Or.inl rfl⟩ (hb m w hw)
    _ = ((appendixCoefficientOrderWords m).card : ℝ) * (C m * D ^ (a * (m + 1))) := by simp
    _ = _ := by rw [mul_assoc]

/-- A `CoefficientPower` gives a `JetPower`. -/
theorem jetPower_of_coefficientPower {I : Type} {c : I → Vec3 → X} {C : ℕ → ℝ} {D : ℝ} {a : ℕ}
    (hc : CoefficientPower C D a c) (t : I) :
    JetPower (fun m => 3 ^ m * C m) D a (c t) := by
  refine ⟨hc.1 t, fun m x => ?_⟩
  calc ‖iteratedFDeriv ℝ m (c t) x‖ ≤ 3 ^ m * coefficientOrderNorm m c :=
        norm_iteratedFDeriv_le_coefficientOrderNorm hc t m x
    _ ≤ 3 ^ m * (C m * D ^ (a * (m + 1))) :=
        mul_le_mul_of_nonneg_left (hc.2.2 m) (by positivity)
    _ = _ := by ring

end Bridge

section D2

variable [L : Leaves]

/-- **Lemma D.2(a)** in the pointwise form: products of jets with a power bound keep a power bound,
with the exponent `2 max(a, b)`; the constants depend only on the value spaces, the input constants and
the exponents. -/
theorem mul_of_D2 {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (C C' : ℕ → ℝ) (hC : ∀ m, 0 ≤ C m) (hC' : ∀ m, 0 ≤ C' m) (a b : ℕ) :
    ∃ C'' : ℕ → ℝ, (∀ m, 0 ≤ C'' m) ∧ ∀ (B : X →L[ℝ] Y →L[ℝ] Z), ‖B‖ ≤ 1 →
      ∀ {D : ℝ} {c : Vec3 → X} {d : Vec3 → Y}, 1 ≤ D → JetPower C D a c → JetPower C' D b d →
        JetPower C'' D (2 * max a b) (fun x => B (c x) (d x)) := by
  obtain ⟨C₂, hC₂, h⟩ := L.d2.1 X Y Z (fun m => ((appendixCoefficientOrderWords m).card : ℝ) * C m)
    (fun m => ((appendixCoefficientOrderWords m).card : ℝ) * C' m) a b
  refine ⟨fun m => 3 ^ m * C₂ m, fun m => by have := hC₂ m; positivity, ?_⟩
  intro B hB D c d hD hc hd
  have hcp := coefficientPower_of_jets (I := Unit) (c := fun _ => c) hD hC (fun _ => hc.1)
    (fun m _ x => hc.2 m x)
  have hdp := coefficientPower_of_jets (I := Unit) (c := fun _ => d) hD hC' (fun _ => hd.1)
    (fun m _ x => hd.2 m x)
  exact jetPower_of_coefficientPower (h B hB Unit D hD (fun _ => c) (fun _ => d) hcp hdp) ()

/-- **Lemma D.2(c)** in the pointwise form: under `ℓ ≤ D^{-a}`, the rescaled jets `y ↦ f (ℓ y)` of a
coefficient with the power bound are at most `C' D^a` at every order, and at most `C' ℓ D^{2a}` at
every positive order. -/
theorem rescale_of_D2 {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : ℕ → ℝ) (hC : ∀ m, 0 ≤ C m) (a : ℕ) :
    ∃ C' : ℕ → ℝ, (∀ m, 0 ≤ C' m) ∧ ∀ {D ℓ : ℝ} {f : Vec3 → X}, 1 ≤ D → 0 < ℓ → ℓ * D ^ a ≤ 1 →
      JetPower C D a f → ∀ n x,
        ‖iteratedFDeriv ℝ n (fun y => f (ℓ • y)) x‖ ≤ C' n * D ^ a ∧
          (0 < n → ‖iteratedFDeriv ℝ n (fun y => f (ℓ • y)) x‖ ≤ C' n * ℓ * D ^ (2 * a)) := by
  obtain ⟨C₂, hC₂, h⟩ := L.d2.2.2 X (fun m => ((appendixCoefficientOrderWords m).card : ℝ) * C m) a
  refine ⟨fun m => 3 ^ m * C₂ m, fun m => by have := hC₂ m; positivity, ?_⟩
  intro D ℓ f hD hℓ hs hf n x
  have hD₀ : 0 < D := zero_lt_one.trans_le hD
  have hcp := coefficientPower_of_jets (I := Unit) (c := fun _ => f) hD hC (fun _ => hf.1)
    (fun m _ y => hf.2 m y)
  have hℓa : ℓ ≤ (D ^ a)⁻¹ := by
    rw [← one_div, le_div_iff₀ (pow_pos hD₀ a)]
    exact hs
  obtain ⟨h1, h2⟩ := h Unit D ℓ hD hℓ hℓa (fun _ => f) hcp
  have hbdd (m : ℕ) : 0 ≤ coefficientOrderNorm m (fun _ : Unit => f) := by
    unfold coefficientOrderNorm
    exact Finset.sum_nonneg fun w hw => sSup_word_nonneg (hcp.2.1 m w hw)
  have hjet : ‖iteratedFDeriv ℝ n (fun y => f (ℓ • y)) x‖ ≤
      3 ^ n * (ℓ ^ n * coefficientOrderNorm n (fun _ : Unit => f)) := by
    calc _ = ℓ ^ n * ‖iteratedFDeriv ℝ n f (ℓ • x)‖ := by
          rw [iteratedFDeriv_comp_const_smul ℓ (hf.1.of_le (by simp)), norm_smul,
            Real.norm_of_nonneg (pow_nonneg hℓ.le _)]
      _ ≤ ℓ ^ n * (3 ^ n * coefficientOrderNorm n (fun _ : Unit => f)) :=
          mul_le_mul_of_nonneg_left
            (norm_iteratedFDeriv_le_coefficientOrderNorm hcp () n (ℓ • x)) (pow_nonneg hℓ.le _)
      _ = _ := by ring
  refine ⟨hjet.trans ?_, fun hn => hjet.trans ?_⟩
  · have hle : ℓ ^ n * coefficientOrderNorm n (fun _ : Unit => f) ≤
        coefficientNorm ℓ n (fun _ : Unit => f) := by
      unfold coefficientNorm
      exact Finset.single_le_sum (f := fun m => ℓ ^ m * coefficientOrderNorm m (fun _ : Unit => f))
        (fun m _ => mul_nonneg (pow_nonneg hℓ.le _) (hbdd m)) (Finset.mem_range.mpr (Nat.lt_succ_self n))
    calc _ ≤ 3 ^ n * (C₂ n * D ^ a) :=
          mul_le_mul_of_nonneg_left (hle.trans (h1 n)) (by positivity)
      _ = _ := by ring
  · calc _ ≤ 3 ^ n * (C₂ n * D ^ (2 * a) * ℓ) :=
          mul_le_mul_of_nonneg_left (h2 n hn) (by positivity)
      _ = _ := by ring

end D2

end

end TorusEuler.Paper.Lib.S53
