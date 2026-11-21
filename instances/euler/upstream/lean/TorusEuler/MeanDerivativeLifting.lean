import TorusEuler.EndpointSpatialDerivativeHierarchy

/-! The finite-order inverse lifting estimate with a single zeroth-order inverse cost. -/

namespace TorusEuler

private theorem length_endpointMixedCorrectionPairs_add_one {I : Type*} (w : List I) :
    (endpointMixedCorrectionPairs w).length + 1 = 2 ^ w.length := by
  induction w with
  | nil => simp [endpointMixedCorrectionPairs]
  | cons i w ih =>
    have h := endpointMixedCorrectionPairs_sum_cons i w (fun _ => (1 : ℕ))
    have hf (l : List (List I × List I)) : (l.map (fun _ => (1 : ℕ))).sum = l.length := by
      induction l <;> simp_all
      omega
    have h₂ (l : List (List I × List I)) : (l.map (fun _ => (2 : ℕ))).sum = 2 * l.length := by
      induction l <;> simp_all
      omega
    simp only [show (1 : ℕ) + 1 = 2 by decide, hf, h₂] at h
    rw [List.length_cons, pow_succ, ← ih]
    omega

/-- Including the zeroth coefficient derivative gives all binary choices
of factors for an ordered derivative word. -/
theorem endpointMixedCorrectionPairs_length_add_one {I : Type*} (w : List I) :
    (endpointMixedCorrectionPairs w).length + 1 = 2 ^ w.length :=
  length_endpointMixedCorrectionPairs_add_one w

private theorem mul_sum_list_map {I : Type*} (c : ℝ) (l : List I) (f : I → ℝ) :
    c * (l.map f).sum = (l.map fun i => c * f i).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

private theorem sum_list_map_const {I : Type*} (l : List I) (c : ℝ) :
    (l.map fun _ => c).sum = (l.length : ℝ) * c := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.cast_succ, add_mul, one_mul]
    rw [add_comm]

/-- In the differentiated mean solve, the coefficient derivatives carry the
scaled factor that pays for the inverse. The estimate retains one factor of
the zeroth-order inverse norm on the forcing. The word list is the actual
ordered Leibniz list with its multiplicities. -/
theorem meanDerivativeLifting {I : Type*} (N : ℕ) (V F B : List I → ℝ)
    {ℓ A M C : ℝ} (hℓ : 0 ≤ ℓ) (hA : 0 ≤ A) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hV : ∀ s : List I, 0 ≤ V s)
    (hf : ∀ s : List I, s.length ≤ N → ℓ ^ s.length * F s ≤ M)
    (hb : ∀ s : List I, 1 ≤ s.length → s.length ≤ N → A * (ℓ ^ s.length * B s) ≤ C)
    (hRec : ∀ s : List I, s.length ≤ N → V s ≤ A * (F s +
      ((endpointMixedCorrectionPairs s).map fun p => B p.1 * V p.2).sum)) :
    ∀ s : List I, s.length ≤ N →
      ℓ ^ s.length * V s ≤ A * M * (1 + (2 : ℝ) ^ N * C) ^ s.length := by
  let G := 1 + (2 : ℝ) ^ N * C
  let L := A * M
  let W (s : List I) := ℓ ^ s.length * V s
  have hG : 1 ≤ G := le_add_of_nonneg_right (by positivity)
  have hL : 0 ≤ L := mul_nonneg hA hM
  have hW (s : List I) : 0 ≤ W s := mul_nonneg (pow_nonneg hℓ _) (hV s)
  have hStep (s : List I) (hs : s.length ≤ N) :
      W s ≤ L + ((endpointMixedCorrectionPairs s).map
        fun p => (A * (ℓ ^ p.1.length * B p.1)) * W p.2).sum := by
    have hsum :
        (A * ℓ ^ s.length) * ((endpointMixedCorrectionPairs s).map fun p => B p.1 * V p.2).sum =
          ((endpointMixedCorrectionPairs s).map
            fun p => (A * (ℓ ^ p.1.length * B p.1)) * W p.2).sum := by
      rw [mul_sum_list_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      rw [← (endpointMixedCorrectionPairs_mem hp).2.1, pow_add]
      dsimp only [W]
      ring
    calc
      W s ≤ ℓ ^ s.length *
          (A * (F s + ((endpointMixedCorrectionPairs s).map fun p => B p.1 * V p.2).sum)) :=
        mul_le_mul_of_nonneg_left (hRec s hs) (pow_nonneg hℓ _)
      _ = A * (ℓ ^ s.length * F s) +
          (A * ℓ ^ s.length) * ((endpointMixedCorrectionPairs s).map fun p => B p.1 * V p.2).sum := by
        ring
      _ ≤ _ := by rw [hsum]; exact add_le_add (mul_le_mul_of_nonneg_left (hf s hs) hA) le_rfl
  have hAll (n : ℕ) : ∀ s : List I, s.length = n → n ≤ N → W s ≤ L * G ^ n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs hN
      have hStep' := hStep s (hs ▸ hN)
      cases n with
      | zero =>
        have hs' := List.length_eq_zero_iff.mp hs
        subst s
        simpa only [endpointMixedCorrectionPairs, List.map_nil, List.sum_nil, add_zero, pow_zero,
          mul_one] using hStep'
      | succ n =>
        have hEach :
            ∀ p ∈ endpointMixedCorrectionPairs s,
              (A * (ℓ ^ p.1.length * B p.1)) * W p.2 ≤ C * (L * G ^ n) := by
          intro p hp
          obtain ⟨hpos, hlength, hlt⟩ := endpointMixedCorrectionPairs_mem hp
          have htop : p.1.length ≤ N := by omega
          have hbelow : p.2.length ≤ n := by omega
          have ih' := ih p.2.length (hs ▸ hlt) p.2 rfl (by omega)
          have hv := ih'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hG hbelow) hL)
          exact mul_le_mul (hb p.1 hpos htop) hv (hW _) hC
        have hsum := List.sum_le_sum
          (f := fun p : List I × List I => (A * (ℓ ^ p.1.length * B p.1)) * W p.2)
          (g := fun _ : List I × List I => C * (L * G ^ n)) hEach
        have hcard : ((endpointMixedCorrectionPairs s).length : ℝ) ≤ (2 : ℝ) ^ N := by
          exact_mod_cast ((Nat.le_add_right _ 1).trans
            ((length_endpointMixedCorrectionPairs_add_one s).le.trans
              (Nat.pow_le_pow_right (by decide) (hs ▸ hN))))
        rw [sum_list_map_const] at hsum
        calc
          W s ≤ L + ((endpointMixedCorrectionPairs s).map
              fun p => (A * (ℓ ^ p.1.length * B p.1)) * W p.2).sum := hStep'
          _ ≤ L + (2 : ℝ) ^ N * (C * (L * G ^ n)) :=
            add_le_add_right (hsum.trans (mul_le_mul_of_nonneg_right hcard (by positivity))) _
          _ ≤ (L * G ^ n) + (2 : ℝ) ^ N * (C * (L * G ^ n)) :=
            add_le_add (le_mul_of_one_le_right hL (one_le_pow₀ hG)) le_rfl
          _ = L * G ^ (n + 1) := by rw [pow_succ]; dsimp only [G]; ring
  exact fun s hs => hAll s.length s rfl hs

end TorusEuler
