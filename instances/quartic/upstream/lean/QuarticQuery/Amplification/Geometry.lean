module

public import QuarticQuery.Statement

/-!
# The two-dimensional rotation of amplitude amplification

Lemma 3.1 of the preprint, geometric half; Brassard, Hoyer, Mosca and Tapp,
Section 2, Lemma 1 and equation (8). A `Preparation` is a unitary `A`, a unit
vector `|0⟩` and an orthogonal projection onto the successful subspace. Circuits
are syntax over the five gates `A`, `A⁻¹`, `S₀`, `S_χ`, `-1`, so a circuit
mentions no particular `A`, and the number of calls is a syntactic count.

The successful and unsuccessful parts of `A|0⟩` stay unnormalised through the
recurrence, as in Troy Lee's `Quantum/Amplitude/Geometry.lean` (adapted here, not
imported), so `p = 0` and `p = 1` need no case split.
-/

@[expose] public section

namespace QuarticQuery.Amplification

/-- `v / ‖v‖`, with `0` going to `0`. -/
noncomputable def normalised {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : H) : H :=
  ((‖v‖⁻¹ : ℝ) : ℂ) • v

/-- Equality up to a global phase. -/
def PhaseEq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (v w : H) : Prop :=
  ∃ c : ℂ, ‖c‖ = 1 ∧ v = c • w

/-- Ledger: lem-3.1. A state preparation with a designated successful subspace. -/
structure Preparation (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  unitary : H ≃ₗᵢ[ℂ] H
  zero : H
  norm_zero : ‖zero‖ = 1
  good : H →ₗ[ℂ] H
  good_idem : ∀ v, good (good v) = good v
  good_symm : ∀ v w, inner ℂ (good v) w = inner ℂ v (good w)

/-- Ledger: def-grover-trial. The gates of a Grover circuit. Only `prepare` and
`unprepare` touch `A`. -/
inductive Gate where
  | prepare
  | unprepare
  | flipZero
  | flipGood
  | negate

/-- Ledger: def-grover-trial. Gate sequences, leftmost first. -/
abbrev Circuit := List Gate

/-- A call to `A` or `A⁻¹`. -/
def Gate.isCall : Gate → Bool
  | .prepare => true
  | .unprepare => true
  | _ => false

/-- Ledger: def-grover-trial. Calls to `A` and `A⁻¹`. -/
def Circuit.calls (c : Circuit) : ℕ := c.countP Gate.isCall

/-- Ledger: def-grover-trial. `G = -A S₀ A⁻¹ S_χ`, the operator `Q` of BHMT. -/
def groverStep : Circuit := [.flipGood, .unprepare, .flipZero, .prepare, .negate]

/-- Ledger: def-grover-trial. `G^ℓ A`. -/
def groverCircuit : ℕ → Circuit
  | 0 => [.prepare]
  | ℓ + 1 => groverCircuit ℓ ++ groverStep

/-- Ledger: lem-3.1. `ℓ` iterations and the preparation use `2ℓ + 1` calls. -/
theorem calls_groverCircuit (ℓ : ℕ) : (groverCircuit ℓ).calls = 2 * ℓ + 1 := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    simp only [Circuit.calls, groverCircuit, List.countP_append] at ih ⊢
    rw [ih]
    rfl

/-! ## Reading a preparation -/

/-- The coefficients of the unnormalised good and bad parts after `j` iterations. -/
noncomputable def ampPair (p : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 1)
  | j + 1 => ((1 - 2 * p) * (ampPair p j).1 + 2 * (1 - p) * (ampPair p j).2,
      -(2 * p) * (ampPair p j).1 + (1 - 2 * p) * (ampPair p j).2)

noncomputable def ampA (p : ℝ) (j : ℕ) : ℝ := (ampPair p j).1
noncomputable def ampB (p : ℝ) (j : ℕ) : ℝ := (ampPair p j).2

theorem ampA_succ (p : ℝ) (j : ℕ) :
    ampA p (j + 1) = (1 - 2 * p) * ampA p j + 2 * (1 - p) * ampB p j := rfl
theorem ampB_succ (p : ℝ) (j : ℕ) :
    ampB p (j + 1) = -(2 * p) * ampA p j + (1 - 2 * p) * ampB p j := rfl

/-- Ledger: claim-grover-state. The rotation without division, with `p = sin² θ`. -/
theorem sin_mul_ampA_and_cos_mul_ampB (θ : ℝ) (j : ℕ) :
    Real.sin θ * ampA (Real.sin θ ^ 2) j = Real.sin ((2 * j + 1) * θ) ∧
    Real.cos θ * ampB (Real.sin θ ^ 2) j = Real.cos ((2 * j + 1) * θ) := by
  induction j with
  | zero => simp [ampA, ampB, ampPair]
  | succ j ih =>
    obtain ⟨hs, hc⟩ := ih
    have hangle : (2 * ((j + 1 : ℕ) : ℝ) + 1) * θ = (2 * (j : ℝ) + 1) * θ + 2 * θ := by
      push_cast; ring
    have h1 := Real.sin_sq_add_cos_sq θ
    rw [ampA_succ, ampB_succ, hangle, Real.sin_add, Real.cos_add, Real.sin_two_mul,
      Real.cos_two_mul, ← hs, ← hc]
    constructor
    · linear_combination (-(2 * Real.sin θ * ampA (Real.sin θ ^ 2) j
        + 2 * Real.sin θ * ampB (Real.sin θ ^ 2) j)) * h1
    · linear_combination (-(2 * Real.cos θ * ampB (Real.sin θ ^ 2) j)) * h1

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem smul_normalised (v : H) : ((‖v‖ : ℝ) : ℂ) • normalised v = v := by
  by_cases hv : v = 0
  · simp [normalised, hv]
  · have h : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have h' : ((‖v‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
    rw [normalised, smul_smul]
    push_cast
    rw [mul_inv_cancel₀ h', one_smul]

theorem norm_normalised {v : H} (hv : v ≠ 0) : ‖normalised v‖ = 1 := by
  have h : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [normalised, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ h]

/-- A nonzero multiple of a unit vector normalises to that vector up to phase. -/
theorem phaseEq_normalised_smul {s : ℝ} (hs : s ≠ 0) {g : H} (hg : ‖g‖ = 1) :
    PhaseEq (normalised ((s : ℂ) • g)) g := by
  have hn : ‖(s : ℂ) • g‖ = |s| := by
    rw [norm_smul, hg, mul_one, Complex.norm_real, Real.norm_eq_abs]
  refine ⟨((|s|⁻¹ * s : ℝ) : ℂ), ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_inv, abs_abs,
      inv_mul_cancel₀ (abs_ne_zero.mpr hs)]
  · rw [normalised, hn, smul_smul]
    push_cast
    rfl

namespace Preparation

variable (A : Preparation H)

/-- `A|0⟩`. -/
noncomputable def state : H := A.unitary A.zero

/-- Ledger: lem-3.1. `p = ‖Π A|0⟩‖²`. -/
noncomputable def prob : ℝ := ‖A.good A.state‖ ^ 2

/-- The unnormalised successful part. -/
noncomputable def goodPart : H := A.good A.state

/-- The unnormalised unsuccessful part. -/
noncomputable def badPart : H := A.state - A.good A.state

/-- `|g⟩`, which is `0` when `p = 0`. -/
noncomputable def goodState : H := normalised A.goodPart

/-- `|b⟩`, which is `0` when `p = 1`. -/
noncomputable def badState : H := normalised A.badPart

/-- `S₀`, sign flip of `|0⟩`. Query free. -/
noncomputable def flipZero (v : H) : H := v - ((2 : ℂ) * inner ℂ A.zero v) • A.zero

/-- `S_χ`, sign flip of the successful subspace. -/
noncomputable def flipGood (v : H) : H := v - (2 : ℂ) • A.good v

end Preparation

/-- The action of one gate. -/
noncomputable def Gate.eval (A : Preparation H) : Gate → H → H
  | .prepare, v => A.unitary v
  | .unprepare, v => A.unitary.symm v
  | .flipZero, v => A.flipZero v
  | .flipGood, v => A.flipGood v
  | .negate, v => -v

/-- The action of a circuit. -/
noncomputable def Circuit.run (A : Preparation H) (c : Circuit) (v : H) : H :=
  c.foldl (fun u g => g.eval A u) v

theorem Circuit.run_append (A : Preparation H) (c d : Circuit) (v : H) :
    Circuit.run A (c ++ d) v = Circuit.run A d (Circuit.run A c v) := by
  simp [Circuit.run, List.foldl_append]

namespace Preparation

variable (A : Preparation H)

/-- Ledger: def-grover-trial. `G`. -/
noncomputable def grover (v : H) : H := Circuit.run A groverStep v

/-- Ledger: claim-grover-state. `G^ℓ A|0⟩`, as the circuit computes it. -/
noncomputable def iterate (ℓ : ℕ) : H := Circuit.run A (groverCircuit ℓ) A.zero

theorem iterate_zero : A.iterate 0 = A.state := rfl

theorem iterate_succ (ℓ : ℕ) : A.iterate (ℓ + 1) = A.grover (A.iterate ℓ) := by
  simp only [iterate, groverCircuit, Circuit.run_append]
  rfl

/-- Ledger: claim-grover-state. `G = (2|ψ⟩⟨ψ| - 1) S_χ`. -/
theorem grover_apply (v : H) :
    A.grover v =
      ((2 : ℂ) * inner ℂ A.state (A.flipGood v)) • A.state - A.flipGood v := by
  have hin : ∀ w : H, inner ℂ A.zero (A.unitary.symm w) = inner ℂ A.state w := by
    intro w
    have := A.unitary.inner_map_map A.zero (A.unitary.symm w)
    rw [LinearIsometryEquiv.apply_symm_apply] at this
    exact this.symm
  simp only [grover, groverStep, Circuit.run, List.foldl, Gate.eval, flipZero]
  rw [hin, map_sub, LinearIsometryEquiv.apply_symm_apply, map_smul]
  simp only [state]
  module

theorem good_goodPart : A.good A.goodPart = A.goodPart := A.good_idem _

theorem good_badPart : A.good A.badPart = 0 := by
  simp [badPart, A.good_idem]

theorem goodPart_add_badPart : A.goodPart + A.badPart = A.state := by
  simp [goodPart, badPart]

theorem norm_state : ‖A.state‖ = 1 := by
  rw [state, A.unitary.norm_map, A.norm_zero]

/-- Ledger: lem-3.1. Measuring the success bit splits the squared norm. -/
theorem norm_sq_split (v : H) : ‖v‖ ^ 2 = ‖A.good v‖ ^ 2 + ‖v - A.good v‖ ^ 2 := by
  have hin : inner ℂ (A.good v) (v - A.good v) = 0 := by
    rw [A.good_symm, map_sub, A.good_idem, sub_self, inner_zero_right]
  have h := norm_add_sq (𝕜 := ℂ) (A.good v) (v - A.good v)
  rw [hin] at h
  simpa using h

theorem norm_badPart_sq : ‖A.badPart‖ ^ 2 = 1 - A.prob := by
  have h := A.norm_sq_split A.state
  rw [A.norm_state] at h
  simp only [badPart, prob]
  linarith

theorem prob_nonneg : 0 ≤ A.prob := by
  rw [prob]; positivity

theorem prob_le_one : A.prob ≤ 1 := by
  have h := A.norm_badPart_sq
  have := sq_nonneg ‖A.badPart‖
  linarith

theorem inner_state_goodPart : inner ℂ A.state A.goodPart = (A.prob : ℂ) := by
  have h : A.goodPart = A.good A.goodPart := A.good_goodPart.symm
  rw [h, goodPart, ← A.good_symm, inner_self_eq_norm_sq_to_K, prob]
  push_cast
  rfl

theorem inner_state_badPart : inner ℂ A.state A.badPart = ((1 - A.prob : ℝ) : ℂ) := by
  have h1 : inner ℂ A.state A.state = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, A.norm_state]; simp
  have h2 := A.inner_state_goodPart
  rw [goodPart] at h2
  rw [badPart, inner_sub_right, h1, h2]
  push_cast
  rfl

/-- Ledger: claim-grover-state. `G` on the plane of the two unnormalised parts. -/
theorem grover_parts (a b : ℝ) :
    A.grover ((a : ℂ) • A.goodPart + (b : ℂ) • A.badPart) =
      (((1 - 2 * A.prob) * a + 2 * (1 - A.prob) * b : ℝ) : ℂ) • A.goodPart +
      ((-(2 * A.prob) * a + (1 - 2 * A.prob) * b : ℝ) : ℂ) • A.badPart := by
  have hflip : A.flipGood ((a : ℂ) • A.goodPart + (b : ℂ) • A.badPart) =
      (-(a : ℂ)) • A.goodPart + (b : ℂ) • A.badPart := by
    simp only [flipGood, map_add, map_smul, good_goodPart, good_badPart, smul_zero, add_zero]
    module
  rw [grover_apply, hflip, inner_add_right, inner_smul_right, inner_smul_right,
    A.inner_state_goodPart, A.inner_state_badPart, ← A.goodPart_add_badPart]
  push_cast
  module

/-- Ledger: claim-grover-state. BHMT equation (8) in unnormalised form. -/
theorem iterate_eq_amp (ℓ : ℕ) :
    A.iterate ℓ =
      ((ampA A.prob ℓ : ℝ) : ℂ) • A.goodPart + ((ampB A.prob ℓ : ℝ) : ℂ) • A.badPart := by
  induction ℓ with
  | zero =>
    simp only [ampA, ampB, ampPair, iterate_zero]
    simp [A.goodPart_add_badPart]
  | succ ℓ ih =>
    rw [iterate_succ, ih, grover_parts, ampA_succ, ampB_succ]

/-- Ledger: claim-grover-state. `sin θ = √p`, with `0 ≤ θ ≤ π/2`. -/
noncomputable def angle : ℝ := Real.arcsin (Real.sqrt A.prob)

theorem sqrt_prob_le_one : Real.sqrt A.prob ≤ 1 :=
  Real.sqrt_le_one.mpr A.prob_le_one

theorem sin_angle : Real.sin A.angle = ‖A.goodPart‖ := by
  rw [angle, Real.sin_arcsin (by linarith [Real.sqrt_nonneg A.prob]) A.sqrt_prob_le_one,
    prob, Real.sqrt_sq (norm_nonneg _)]
  rfl

theorem sin_angle_sq : Real.sin A.angle ^ 2 = A.prob := by
  rw [sin_angle]; rfl

theorem cos_angle : Real.cos A.angle = ‖A.badPart‖ := by
  rw [angle, Real.cos_arcsin, Real.sq_sqrt A.prob_nonneg, ← A.norm_badPart_sq,
    Real.sqrt_sq (norm_nonneg _)]

theorem cos_angle_sq : Real.cos A.angle ^ 2 = 1 - A.prob := by
  rw [cos_angle, A.norm_badPart_sq]

/-- Ledger: claim-grover-state. For `0 < p < 1`, `0 < θ < π/2`. -/
theorem angle_mem {h0 : 0 < A.prob} {h1 : A.prob < 1} :
    0 < A.angle ∧ A.angle < Real.pi / 2 := by
  constructor
  · exact Real.arcsin_pos.mpr (Real.sqrt_pos.mpr h0)
  · exact Real.arcsin_lt_pi_div_two.mpr ((Real.sqrt_lt' one_pos).mpr (by simpa using h1))

theorem goodPart_eq : A.goodPart = ((Real.sin A.angle : ℝ) : ℂ) • A.goodState := by
  rw [sin_angle, goodState, smul_normalised]

theorem badPart_eq : A.badPart = ((Real.cos A.angle : ℝ) : ℂ) • A.badState := by
  rw [cos_angle, badState, smul_normalised]

/-- Ledger: claim-grover-state. `A|0⟩ = sin θ |g⟩ + cos θ |b⟩`. -/
theorem state_eq :
    A.state = ((Real.sin A.angle : ℝ) : ℂ) • A.goodState +
      ((Real.cos A.angle : ℝ) : ℂ) • A.badState := by
  rw [← goodPart_eq, ← badPart_eq, goodPart_add_badPart]

theorem amp_mul_sin (ℓ : ℕ) :
    ampA A.prob ℓ * Real.sin A.angle = Real.sin ((2 * ℓ + 1) * A.angle) := by
  have h := (sin_mul_ampA_and_cos_mul_ampB A.angle ℓ).1
  rw [sin_angle_sq] at h
  rw [← h]; ring

theorem amp_mul_cos (ℓ : ℕ) :
    ampB A.prob ℓ * Real.cos A.angle = Real.cos ((2 * ℓ + 1) * A.angle) := by
  have h := (sin_mul_ampA_and_cos_mul_ampB A.angle ℓ).2
  rw [sin_angle_sq] at h
  rw [← h]; ring

/-- Ledger: claim-grover-state. `G^ℓ A|0⟩ = sin((2ℓ+1)θ)|g⟩ + cos((2ℓ+1)θ)|b⟩`.
No hypothesis on `p`: at `p = 0` or `p = 1` the absent vector is `0`. -/
theorem iterate_eq (ℓ : ℕ) :
    A.iterate ℓ =
      ((Real.sin ((2 * ℓ + 1) * A.angle) : ℝ) : ℂ) • A.goodState +
      ((Real.cos ((2 * ℓ + 1) * A.angle) : ℝ) : ℂ) • A.badState := by
  rw [iterate_eq_amp, ← amp_mul_sin, ← amp_mul_cos]
  conv_lhs => rw [goodPart_eq, badPart_eq]
  simp only [smul_smul]
  push_cast
  rfl

/-- Ledger: claim-grover-state. For `0 < p < 1`, `G` rotates the plane of `|g⟩, |b⟩`
by `2θ`. -/
theorem grover_rotation (h0 : 0 < A.prob) (h1 : A.prob < 1) (x y : ℝ) :
    A.grover ((x : ℂ) • A.goodState + (y : ℂ) • A.badState) =
      ((x * Real.cos (2 * A.angle) + y * Real.sin (2 * A.angle) : ℝ) : ℂ) • A.goodState +
      ((y * Real.cos (2 * A.angle) - x * Real.sin (2 * A.angle) : ℝ) : ℂ) • A.badState := by
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sin A.angle := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = Real.cos A.angle := ⟨_, rfl⟩
  have hs2 : s ^ 2 = A.prob := by rw [hs, sin_angle_sq]
  have hc2 : c ^ 2 = 1 - A.prob := by rw [hc, cos_angle_sq]
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs2; simp at hs2; linarith
  have hc0 : c ≠ 0 := fun h => by rw [h] at hc2; simp at hc2; linarith
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
  have hg : A.goodState = ((s⁻¹ : ℝ) : ℂ) • A.goodPart := by
    rw [goodPart_eq, ← hs, smul_smul]; push_cast; rw [inv_mul_cancel₀ hsc, one_smul]
  have hb : A.badState = ((c⁻¹ : ℝ) : ℂ) • A.badPart := by
    rw [badPart_eq, ← hc, smul_smul]; push_cast; rw [inv_mul_cancel₀ hcc, one_smul]
  have hstart : (x : ℂ) • A.goodState + (y : ℂ) • A.badState =
      ((x * s⁻¹ : ℝ) : ℂ) • A.goodPart + ((y * c⁻¹ : ℝ) : ℂ) • A.badPart := by
    rw [hg, hb, smul_smul, smul_smul]; push_cast; rfl
  have hp : (1 : ℝ) - s ^ 2 = c ^ 2 := by rw [hs2, hc2]
  have hu : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0
  have hv : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0
  have hsin2 : Real.sin (2 * A.angle) = 2 * s * c := by rw [Real.sin_two_mul, ← hs, ← hc]
  have hcos2 : Real.cos (2 * A.angle) = 1 - 2 * s ^ 2 := by
    rw [Real.cos_two_mul, ← hc]; linarith
  have hgp : A.goodPart = (s : ℂ) • A.goodState := by rw [hs]; exact A.goodPart_eq
  have hbp : A.badPart = (c : ℂ) • A.badState := by rw [hc]; exact A.badPart_eq
  have e1 : ((1 - 2 * A.prob) * (x * s⁻¹) + 2 * (1 - A.prob) * (y * c⁻¹)) * s =
      x * Real.cos (2 * A.angle) + y * Real.sin (2 * A.angle) := by
    rw [hcos2, hsin2, ← hs2]
    linear_combination (1 - 2 * s ^ 2) * x * hu + 2 * y * s * c * hv + 2 * y * c⁻¹ * s * hp
  have e2 : (-(2 * A.prob) * (x * s⁻¹) + (1 - 2 * A.prob) * (y * c⁻¹)) * c =
      y * Real.cos (2 * A.angle) - x * Real.sin (2 * A.angle) := by
    rw [hcos2, hsin2, ← hs2]
    linear_combination (-2 * s * c * x) * hu + (1 - 2 * s ^ 2) * y * hv
  rw [hstart, grover_parts, hgp, hbp, smul_smul, smul_smul, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, e1, e2]

theorem good_goodState : A.good A.goodState = A.goodState := by
  simp only [goodState, normalised, map_smul, good_goodPart]

theorem good_badState : A.good A.badState = 0 := by
  simp only [badState, normalised, map_smul, good_badPart, smul_zero]

/-- Ledger: claim-grover-state. The successful component after `ℓ` iterations is
`sin((2ℓ+1)θ) |g⟩`. -/
theorem good_iterate (ℓ : ℕ) :
    A.good (A.iterate ℓ) = ((Real.sin ((2 * ℓ + 1) * A.angle) : ℝ) : ℂ) • A.goodState := by
  rw [iterate_eq, map_add, map_smul, map_smul, good_goodState, good_badState, smul_zero,
    add_zero]

/-- Ledger: claim-grover-state. The success mass after `ℓ` iterations, every `p`. -/
theorem norm_good_iterate_sq (ℓ : ℕ) :
    ‖A.good (A.iterate ℓ)‖ ^ 2 = Real.sin ((2 * ℓ + 1) * A.angle) ^ 2 := by
  have h : A.good (A.iterate ℓ) = ((ampA A.prob ℓ : ℝ) : ℂ) • A.goodPart := by
    rw [iterate_eq_amp, map_add, map_smul, map_smul, good_goodPart, good_badPart,
      smul_zero, add_zero]
  rw [h, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, ← amp_mul_sin,
    mul_pow, sin_angle]

/-- Ledger: claim-grover-state. The failure mass after `ℓ` iterations, every `p`. -/
theorem norm_bad_iterate_sq (ℓ : ℕ) :
    ‖A.iterate ℓ - A.good (A.iterate ℓ)‖ ^ 2 = 1 - Real.sin ((2 * ℓ + 1) * A.angle) ^ 2 := by
  have h : A.iterate ℓ - A.good (A.iterate ℓ) = ((ampB A.prob ℓ : ℝ) : ℂ) • A.badPart := by
    conv_lhs => rw [iterate_eq_amp]
    rw [map_add, map_smul, map_smul, good_goodPart, good_badPart, smul_zero, add_zero]
    abel
  rw [h, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hcos : Real.cos ((2 * ℓ + 1) * A.angle) ^ 2 = ampB A.prob ℓ ^ 2 * ‖A.badPart‖ ^ 2 := by
    rw [← amp_mul_cos, mul_pow, cos_angle]
  have := Real.sin_sq_add_cos_sq ((2 * ℓ + 1) * A.angle)
  linarith

theorem norm_goodState (h : 0 < A.prob) : ‖A.goodState‖ = 1 := by
  refine norm_normalised fun h0 => ?_
  have : A.prob = 0 := by
    rw [prob]; change ‖A.goodPart‖ ^ 2 = 0; simp [h0]
  linarith

/-- Ledger: claim-grover-state. After any number of iterations, the normalised
successful component is `|g⟩` up to phase, the phase being the sign of
`sin((2ℓ+1)θ)`. When that sine vanishes the successful outcome has mass zero. -/
theorem phaseEq_normalised_good_iterate {ℓ : ℕ}
    (hs : Real.sin ((2 * ℓ + 1) * A.angle) ≠ 0) :
    PhaseEq (normalised (A.good (A.iterate ℓ))) A.goodState := by
  have hp : 0 < A.prob := by
    by_contra hp
    have h0 : A.prob = 0 := le_antisymm (not_lt.mp hp) A.prob_nonneg
    have h := A.amp_mul_sin ℓ
    have hsa : Real.sin A.angle = 0 := by
      have := A.sin_angle_sq
      rw [h0] at this
      simpa using this
    rw [hsa, mul_zero] at h
    exact hs h.symm
  rw [good_iterate]
  exact phaseEq_normalised_smul hs (A.norm_goodState hp)

/-- Ledger: claim-grover-state. `p = 0`: the successful component stays zero. -/
theorem good_iterate_of_prob_zero (h : A.prob = 0) (ℓ : ℕ) : A.good (A.iterate ℓ) = 0 := by
  have hg : A.goodPart = 0 := by
    have : ‖A.goodPart‖ ^ 2 = 0 := h
    simpa using this
  rw [iterate_eq_amp, map_add, map_smul, map_smul, good_goodPart, good_badPart, hg]
  simp

/-- Ledger: claim-sin2theta. `sin 2θ = 2 √(p (1 - p))`. -/
theorem sin_two_angle :
    Real.sin (2 * A.angle) = 2 * Real.sqrt (A.prob * (1 - A.prob)) := by
  rw [Real.sin_two_mul, Real.sqrt_mul A.prob_nonneg, ← A.cos_angle_sq, ← A.sin_angle_sq]
  have hs : 0 ≤ Real.sin A.angle := by rw [sin_angle]; positivity
  have hc : 0 ≤ Real.cos A.angle := by rw [cos_angle]; positivity
  rw [Real.sqrt_sq hs, Real.sqrt_sq hc]
  ring

end Preparation

end QuarticQuery.Amplification
