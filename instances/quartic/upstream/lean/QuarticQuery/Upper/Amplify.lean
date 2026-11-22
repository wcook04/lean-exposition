module

public import QuarticQuery.Upper.Compile
public import QuarticQuery.Amplification.Bounded

/-!
# Bounded amplification of a sampler

The abstract `Preparation` is instantiated on a register, with the successful labels
as a coordinate projection. `Samples.amplify` is Lemma 3.1 as a measured program: its
result is `none` with probability `f x`, and otherwise `some b` with probability
proportional to the sampler's own law on `some b`, exactly. The reduction to
`Amplification` is direct: a trial measures every label, so the program never
needs `Proc`, only the values `trialFail` and `mass` of the geometry.

The parameters `iterationBound` and `trialCount` are computed from `γ` and `η` alone,
so the program does not depend on the input.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace QuarticQuery.Upper

open QuarticQuery.Amplification

section Prep

variable {Z : Type} [Fintype Z]

open Classical in
/-- The coordinate projection onto the labels satisfying `S`. -/
noncomputable def coordProj (S : Z → Prop) : Reg Z →ₗ[ℂ] Reg Z where
  toFun ψ := WithLp.toLp 2 fun z => if S z then ψ.ofLp z else 0
  map_add' ψ φ := by
    ext z
    by_cases h : S z <;> simp [h]
  map_smul' a ψ := by
    ext z
    by_cases h : S z <;> simp [h]

open Classical in
theorem coordProj_apply (S : Z → Prop) (ψ : Reg Z) (z : Z) :
    (coordProj S ψ).ofLp z = if S z then ψ.ofLp z else 0 := rfl

/-- Ledger: lem-3.1. A unitary on a register, a basis start and a set of labels make a
`Preparation`. -/
noncomputable def prepOf (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Prop) :
    Preparation (Reg Z) where
  unitary := U
  zero := rket o
  norm_zero := norm_rket o
  good := coordProj S
  good_idem v := by
    classical
    ext z
    by_cases h : S z <;> simp [coordProj_apply, h]
  good_symm v w := by
    classical
    simp only [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases h : S z <;> simp [coordProj_apply, h]

open Classical in
/-- The sign on the labels satisfying `S`. -/
noncomputable def signU (S : Z → Prop) : Reg Z ≃ₗᵢ[ℂ] Reg Z :=
  signedOp id (fun z => if S z then -1 else 1) (fun _ => rfl) (fun _ => rfl)
    (fun z => by by_cases h : S z <;> simp [h])

theorem signU_apply (S : Z → Prop) (ψ : Reg Z) :
    signU S ψ = ψ - (2 : ℂ) • coordProj S ψ := by
  classical
  ext z
  change (if S z then (-1 : ℂ) else 1) * ψ.ofLp z = _
  by_cases h : S z <;> simp [coordProj_apply, h]
  ring

theorem inner_rket (o : Z) (v : Reg Z) : inner ℂ (rket o) v = v.ofLp o := by
  classical
  simp [rket, EuclideanSpace.inner_single_left]

/-- The gates of a Grover circuit as unitaries. -/
noncomputable def gateU (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Prop) :
    Amplification.Gate → Reg Z ≃ₗᵢ[ℂ] Reg Z
  | .prepare => U
  | .unprepare => U.symm
  | .flipZero => signU (· = o)
  | .flipGood => signU S
  | .negate => signU fun _ => True

theorem gateU_apply (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Prop) (g : Amplification.Gate) (v : Reg Z) :
    gateU U o S g v = g.eval (prepOf U o S) v := by
  classical
  cases g with
  | prepare => rfl
  | unprepare => rfl
  | flipZero =>
    simp only [gateU, Amplification.Gate.eval, Preparation.flipZero, signU_apply]
    change _ = v - ((2 : ℂ) * inner ℂ (rket o) v) • rket o
    rw [inner_rket]
    ext z
    by_cases h : z = o
    · subst h
      simp [coordProj_apply, rket_apply]
    · simp [coordProj_apply, rket_apply, h]
  | flipGood => exact signU_apply S v
  | negate =>
    simp only [gateU, Amplification.Gate.eval, signU_apply]
    ext z
    simp [coordProj_apply]
    ring

/-- A Grover circuit as a unitary. -/
noncomputable def circU (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Prop) :
    Amplification.Circuit → Reg Z ≃ₗᵢ[ℂ] Reg Z
  | [] => LinearIsometryEquiv.refl ℂ _
  | g :: c => (gateU U o S g).trans (circU U o S c)

theorem circU_apply (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Prop) (c : Amplification.Circuit) (v : Reg Z) :
    circU U o S c v = Amplification.Circuit.run (prepOf U o S) c v := by
  induction c generalizing v with
  | nil => rfl
  | cons g c ih =>
    change circU U o S c (gateU U o S g v) = _
    rw [ih, gateU_apply]
    rfl

theorem isCirc_gateU {ι : Type} {n : ℕ} {F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z} (hF : IsCirc n F)
    (o : Z) (S : Z → Prop) (g : Amplification.Gate) :
    IsCirc (if g.isCall then n else 0) fun x => gateU (F x) o S g := by
  cases g with
  | prepare => exact hF
  | unprepare => exact hF.symm
  | flipZero => exact IsCirc.gate _
  | flipGood => exact IsCirc.gate _
  | negate => exact IsCirc.gate _

theorem isCirc_circU {ι : Type} {n : ℕ} {F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z} (hF : IsCirc n F)
    (o : Z) (S : Z → Prop) (c : Amplification.Circuit) :
    IsCirc (c.calls * n) fun x => circU (F x) o S c := by
  induction c with
  | nil => exact (IsCirc.gate _).cast (by simp [Amplification.Circuit.calls])
  | cons g c ih =>
    refine ((isCirc_gateU hF o S g).comp ih).cast ?_
    simp only [Amplification.Circuit.calls, List.countP_cons]
    cases g <;> simp [Amplification.Gate.isCall] <;> ring

end Prep

/-- The law of the amplified program: failure `f`, and otherwise the law `q`, normalised. -/
noncomputable def ampLaw {β : Type} [Fintype β] (f : ℝ) (q : β → ℝ) : Option β → ℝ
  | none => f
  | some b => (1 - f) * (q b / ∑ c, q c)

section Trial

variable {Z β : Type} [Fintype Z] [Fintype β]

/-- The label of a successful outcome. -/
def isGood (out : Z → Option β) (z : Z) : Prop := (out z).isSome = true

theorem lawOf_good_some (out : Z → Option β) (v : Reg Z) (b : β) :
    lawOf (coordProj (isGood out) v) out (some b) = lawOf v out (some b) := by
  classical
  simp only [lawOf]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases h : out z = some b
  · simp [h, coordProj_apply, isGood]
  · simp [h]

theorem lawOf_good_none (out : Z → Option β) (v : Reg Z) :
    lawOf (coordProj (isGood out) v) out none = 0 := by
  classical
  simp only [lawOf]
  refine Finset.sum_eq_zero fun z _ => ?_
  by_cases h : out z = none
  · simp [h, coordProj_apply, isGood]
  · simp [h]

/-- The successful labels carry the squared norm of the successful part. -/
theorem sum_lawOf_some (out : Z → Option β) (v : Reg Z) :
    ∑ b, lawOf v out (some b) = ‖coordProj (isGood out) v‖ ^ 2 := by
  have h := sum_lawOf (coordProj (isGood out) v) out
  rw [Fintype.sum_option, lawOf_good_none, zero_add] at h
  simpa only [lawOf_good_some] using h

theorem lawOf_none (out : Z → Option β) (v : Reg Z) :
    lawOf v out none = ‖v‖ ^ 2 - ‖coordProj (isGood out) v‖ ^ 2 := by
  have h := sum_lawOf v out
  rw [Fintype.sum_option, sum_lawOf_some] at h
  linarith

variable (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (out : Z → Option β)

local notation "A" => prepOf U o (isGood out)

theorem prob_eq_sum : (A).prob = ∑ b, lawOf (U (rket o)) out (some b) :=
  (sum_lawOf_some out _).symm

/-- Ledger: lem-3.1. After `ℓ` iterations a successful label has the sampler's own law,
scaled by the success mass. -/
theorem lawOf_iterate_some (ℓ : ℕ) (b : β) :
    lawOf ((A).iterate ℓ) out (some b) =
      (A).mass ℓ * (lawOf (U (rket o)) out (some b) /
        ∑ c, lawOf (U (rket o)) out (some c)) := by
  have hg : lawOf ((A).iterate ℓ) out (some b) =
      lawOf ((A).good ((A).iterate ℓ)) out (some b) := (lawOf_good_some out _ b).symm
  rw [hg]
  by_cases hs : Real.sin ((2 * ℓ + 1) * (A).angle) = 0
  · have h0 : (A).mass ℓ = 0 := by simp [Preparation.mass, hs]
    have h1 : ‖(A).good ((A).iterate ℓ)‖ ^ 2 = 0 := by rw [← (A).mass_eq, h0]
    have h2 : (A).good ((A).iterate ℓ) = 0 := by simpa using h1
    rw [h2, h0, zero_mul]
    simp [lawOf]
  · obtain ⟨c, hc, e⟩ := (A).phaseEq_normalised_good_iterate hs
    have hsm : (A).good ((A).iterate ℓ) =
        ((‖(A).good ((A).iterate ℓ)‖ : ℝ) : ℂ) • c • (A).goodState := by
      rw [← e, smul_normalised]
    have hstate : (A).goodState =
        (((‖(A).goodPart‖⁻¹ : ℝ) : ℂ)) • (A).good (U (rket o)) := rfl
    have hgp : ‖(A).goodPart‖ ^ 2 = ∑ c, lawOf (U (rket o)) out (some c) :=
      (sum_lawOf_some out _).symm
    have hgood : lawOf ((A).good (U (rket o))) out (some b) = lawOf (U (rket o)) out (some b) :=
      lawOf_good_some out _ b
    rw [hsm, lawOf_smul, lawOf_smul, hstate, lawOf_smul, hc, hgood]
    simp only [Complex.norm_real, norm_norm, norm_inv, one_pow, one_mul, inv_pow]
    rw [← (A).mass_eq, ← hgp]
    ring

theorem lawOf_iterate_none (ℓ : ℕ) :
    lawOf ((A).iterate ℓ) out none = 1 - (A).mass ℓ := by
  have hn : ‖(A).iterate ℓ‖ = 1 := by
    have : (A).iterate ℓ = circU U o (isGood out) (groverCircuit ℓ) (rket o) :=
      (circU_apply _ _ _ _ _).symm
    rw [this, LinearIsometryEquiv.norm_map, norm_rket]
  rw [lawOf_none, hn, (A).mass_eq]
  norm_num
  rfl

end Trial

variable {ι β : Type} [Fintype ι] [Inhabited ι] [Fintype β]

/-- Ledger: lem-3.1. Lemma 3.1 on a sampler: at most `n_tr` trials, each of at most
`2 M + 1` calls of a circuit of `n` reads. The law on success is exact. -/
theorem Samples.attempts {n : ℕ} {L : BitInput ι → Option β → ℝ} (h : Samples n L) {M : ℕ}
    (hM : M ≠ 0) : ∃ f₀ : BitInput ι → ℝ,
      (∀ x, 0 ≤ f₀ x ∧ f₀ x ≤ 1) ∧
      (∀ x γ, 0 < γ → M = iterationBound γ → γ ≤ ∑ b, L x (some b) → f₀ x ≤ 31 / 40) ∧
      (∀ x, ∑ b, L x (some b) = 0 → f₀ x = 1) ∧
      ∀ t, Runs (t * (2 * ((2 * M + 1) * n))) fun x => ampLaw (f₀ x ^ t) fun b => L x (some b) := by
  classical
  obtain ⟨Z, _, o, out, F, hF, hL⟩ := h
  let A : BitInput ι → Preparation (Reg Z) := fun x => prepOf (F x) o (isGood out)
  have hprob : ∀ x, (A x).prob = ∑ b, L x (some b) := fun x => by
    simp only [hL]
    exact prob_eq_sum (F x) o out
  have hfail1 : ∀ x, (A x).trialFail M ≤ 1 := fun x => by
    rw [(A x).trialFail_eq hM]
    have : 0 ≤ ∑ ℓ : Fin M, trialWeight M ℓ * (A x).mass ℓ :=
      Finset.sum_nonneg fun ℓ _ => mul_nonneg (trialWeight_nonneg _ _) ((A x).mass_nonneg _)
    linarith
  refine ⟨fun x => (A x).trialFail M, fun x => ⟨(A x).trialFail_nonneg M, hfail1 x⟩,
    fun x γ hγ hM' hp => ?_, fun x h0 => ?_, fun t => ?_⟩
  · subst hM'
    exact (A x).trialFail_le hγ (by rw [hprob]; exact hp)
  · exact (A x).trialFail_of_prob_zero (by rw [hprob, h0]) hM
  · -- one trial of length `ℓ`
    have htrial : ∀ ℓ : Fin M, Runs (2 * ((2 * M + 1) * n)) fun x o' =>
        lawOf ((A x).iterate ℓ) out o' := fun ℓ => by
      have hc := isCirc_circU hF o (isGood out) (groverCircuit ℓ)
      rw [calls_groverCircuit] at hc
      have hs : Samples ((2 * (ℓ : ℕ) + 1) * n) fun x o' => lawOf ((A x).iterate ℓ) out o' :=
        ⟨Z, inferInstance, o, out, _, hc, fun x b => by rw [circU_apply]; rfl⟩
      refine hs.runs.mono (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right n ?_))
      have := ℓ.isLt
      omega
    have hweights : Samples (ι := ι) 0 fun _ (ℓ : Fin M) => trialWeight M ℓ :=
      Samples.gate (fun ℓ => trialWeight_nonneg _ _) (sum_trialWeight hM)
    induction t with
    | zero =>
      refine (Runs.pure (ι := ι) (none : Option β)).mono (by omega) |>.congr fun x o' => ?_
      cases o' with
      | none => simp [ampLaw, pt_self]
      | some b => simp [ampLaw, pt_of_ne]
    | succ t ih =>
      let K : Option β → BitInput ι → Option β → ℝ := fun o₁ x o' =>
        match o₁ with
        | none => ampLaw ((A x).trialFail M ^ t) (fun b => L x (some b)) o'
        | some b => pt (some b) o'
      have hK : ∀ o₁, Runs (t * (2 * ((2 * M + 1) * n))) (K o₁) := fun o₁ => by
        cases o₁ with
        | none => exact ih
        | some b => exact (Runs.pure (ι := ι) (some b)).mono (by omega)
      have hstep := fun ℓ : Fin M => (htrial ℓ).bind hK
      have hall := hweights.runs.bind hstep
      refine (hall.mono (by
        generalize 2 * ((2 * M + 1) * n) = Y
        have e : (t + 1) * Y = t * Y + Y := by ring
        omega)).congr fun x o' => ?_
      -- the value of one trial
      obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ampLaw 0 (fun b => L x (some b)) o' := ⟨_, rfl⟩
      obtain ⟨V, hV⟩ : ∃ V : ℝ, V = ampLaw ((A x).trialFail M ^ t) (fun b => L x (some b)) o' :=
        ⟨_, rfl⟩
      have hterm : ∀ ℓ : Fin M, ∑ o₁, lawOf ((A x).iterate ℓ) out o₁ * K o₁ x o' =
          (1 - (A x).mass ℓ) * V + (A x).mass ℓ * Q := by
        intro ℓ
        rw [Fintype.sum_option]
        simp only [K]
        rw [← hV]
        congr 1
        · rw [show lawOf ((A x).iterate ℓ) out none = 1 - (A x).mass ℓ from
            lawOf_iterate_none (F x) o out ℓ]
        · simp only [show ∀ b, lawOf ((A x).iterate ℓ) out (some b) = _ from
            lawOf_iterate_some (F x) o out ℓ, ← hL, hQ]
          cases o' with
          | none => simp [ampLaw, pt_of_ne]
          | some b =>
            have : ∀ c : β, pt (some c) (some b) = pt c b := fun c => by
              by_cases h : c = b
              · subst h; simp [pt_self]
              · rw [pt_of_ne h, pt_of_ne (by simpa using h)]
            simp only [this, ampLaw, sub_zero, one_mul]
            rw [Finset.sum_congr rfl fun c _ => mul_assoc _ _ _, ← Finset.mul_sum]
            rw [sum_mul_pt]
      simp only [hterm]
      have hsum : ∑ ℓ : Fin M, trialWeight M ℓ * ((1 - (A x).mass ℓ) * V + (A x).mass ℓ * Q) =
          (A x).trialFail M * V + (1 - (A x).trialFail M) * Q := by
        have h1 : 1 - (A x).trialFail M = ∑ ℓ : Fin M, trialWeight M ℓ * (A x).mass ℓ := by
          rw [(A x).trialFail_eq hM]; ring
        rw [h1, Preparation.trialFail, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun ℓ _ => by ring
      rw [hsum, hV, hQ]
      cases o' with
      | none =>
        simp only [ampLaw]
        rw [pow_succ']
        ring
      | some b =>
        simp only [ampLaw]
        rw [pow_succ']
        ring

/-- Ledger: lem-3.1. `Samples.attempts` at the parameters of Lemma 3.1. -/
theorem Samples.amplify {n : ℕ} {L : BitInput ι → Option β → ℝ} (h : Samples n L) {γ η : ℝ}
    (hγ : 0 < γ) (hη : 0 < η) : ∃ f : BitInput ι → ℝ,
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∀ x, γ ≤ ∑ b, L x (some b) → f x ≤ η) ∧
      (∀ x, ∑ b, L x (some b) = 0 → f x = 1) ∧
      Runs (trialCount η * (2 * ((2 * iterationBound γ + 1) * n)))
        fun x => ampLaw (f x) fun b => L x (some b) := by
  obtain ⟨f₀, h01, hfail, hzero, hrun⟩ := h.attempts (iterationBound_ne_zero hγ)
  refine ⟨fun x => f₀ x ^ trialCount η, fun x => ⟨pow_nonneg (h01 x).1 _,
    pow_le_one₀ (h01 x).1 (h01 x).2⟩, fun x hp => ?_, fun x h0 => ?_, hrun _⟩
  · calc f₀ x ^ trialCount η ≤ (31 / 40 : ℝ) ^ trialCount η :=
        pow_le_pow_left₀ (h01 x).1 (hfail x γ hγ rfl hp) _
      _ ≤ η := pow_trialCount_le hη
  · simp [hzero x h0]

end QuarticQuery.Upper
