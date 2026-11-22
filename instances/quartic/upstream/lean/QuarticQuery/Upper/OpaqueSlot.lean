module

public import QuarticQuery.Upper.Amplify

/-!
Black-box slot source.
The order is left-to-right circuit time order, matching `circU`/`trans`.
The two A calls are unconditional on the iteration label.  Only the fixed,
oracle-independent reflections are controlled by that label.
-/

@[expose] public section

namespace QuarticQuery.Upper

variable {ι Λ Z : Type} [Fintype Λ] [Fintype Z]

noncomputable def condSign (P : Λ → Prop) (S : Z → Prop) :
    Reg (Σ _ : Λ, Z) ≃ₗᵢ[ℂ] Reg (Σ _ : Λ, Z) :=
  by
    classical
    exact sigmaOp fun a => if P a then signU S else LinearIsometryEquiv.refl ℂ _

/-- One padded Grover slot. The inactive branch is identity by A⁻¹A;
the active branch is `- A S₀ A⁻¹ Sχ`. -/
noncomputable def opaqueSlot (U : Reg Z ≃ₗᵢ[ℂ] Reg Z)
    (o : Z) (S : Z → Prop) (P : Λ → Prop) :
    Reg (Σ _ : Λ, Z) ≃ₗᵢ[ℂ] Reg (Σ _ : Λ, Z) :=
  ((((condSign P S).trans (sigmaOp fun _ : Λ => U.symm)).trans
    (condSign P (· = o))).trans (sigmaOp fun _ : Λ => U)).trans
      (condSign P fun _ => True)

/-- On each iteration-label slice the fixed slot is exactly one Grover step
or the identity. Inactive slices cancel the unconditional `U†,U` pair. -/
theorem slice_opaqueSlot (U : Reg Z ≃ₗᵢ[ℂ] Reg Z)
    (o : Z) (S : Z → Prop) (P : Λ → Prop) [DecidablePred P]
    (a : Λ) (ψ : Reg (Σ _ : Λ, Z)) :
    slice a (opaqueSlot U o S P ψ) =
      if P a then circU U o S Amplification.groverStep (slice a ψ)
      else slice a ψ := by
  classical
  simp only [opaqueSlot, LinearIsometryEquiv.trans_apply, slice_sigmaOp]
  by_cases h : P a
  · simp [condSign, h, slice_sigmaOp, circU, Amplification.groverStep, gateU]
  · simp [condSign, h, slice_sigmaOp]

/-- The two unconditional calls cost `2*n` logical reads, regardless of P.
The fixed reflections consume zero oracle reads. -/
theorem opaqueSlot_isCirc {n : ℕ}
    (F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z) (hF : IsCirc n F)
    (o : Z) (S : Z → Prop) (P : Λ → Prop) :
    IsCirc (2 * n) (fun x => opaqueSlot (F x) o S P) := by
  have hfixed (Q : Z → Prop) :
      IsCirc 0 (fun _ : BitInput ι => condSign P Q) := IsCirc.gate _
  have hinv : IsCirc n (fun x => sigmaOp fun _ : Λ => (F x).symm) :=
    IsCirc.sigma (fun _ : Λ => hF.symm)
  have hfwd : IsCirc n (fun x => sigmaOp fun _ : Λ => F x) :=
    IsCirc.sigma (fun _ : Λ => hF)
  have h := (((hfixed S).comp hinv).comp (hfixed (· = o))).comp hfwd
  have h := h.comp (hfixed fun _ => True)
  have heq : (0 + n + 0 + n + 0) = 2 * n := by omega
  exact (h.cast heq).of_eq (fun _ _ => rfl)

/-- `r` fixed slots after one unconditional preparation. The label controls
only the fixed reflections, while every slot calls U† and U in that order. -/
noncomputable def opaquePrefix (U : Reg Z ≃ₗᵢ[ℂ] Reg Z)
    (o : Z) (S : Z → Prop) (active : ℕ → Λ → Prop) :
    (r : ℕ) → Reg (Σ _ : Λ, Z) ≃ₗᵢ[ℂ] Reg (Σ _ : Λ, Z)
  | 0 => sigmaOp fun _ : Λ => U
  | r + 1 => (opaquePrefix U o S active r).trans
      (opaqueSlot U o S (active r))

/-- The fixed opaque-preparation schedule has exactly `2*r+1` uses of the
input-dependent preparation circuit, regardless of label or success. -/
theorem opaquePrefix_isCirc {n : ℕ}
    (F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z) (hF : IsCirc n F)
    (o : Z) (S : Z → Prop) (active : ℕ → Λ → Prop) (r : ℕ) :
    IsCirc ((2 * r + 1) * n)
      (fun x => opaquePrefix (F x) o S active r) := by
  induction r with
  | zero =>
    simpa [opaquePrefix]
      using (IsCirc.sigma (fun _ : Λ => hF))
  | succ r ih =>
    have h := ih.comp (opaqueSlot_isCirc F hF o S (active r))
    have heq : (2 * r + 1) * n + 2 * n = (2 * (r + 1) + 1) * n := by ring
    exact (h.cast heq).of_eq (fun _ _ => rfl)

/-- Branch word for the fixed slot schedule: disabled slots contribute no gate.
The order is the same left-to-right order as `Amplification.Circuit.run`. -/
def prefixWord (ℓ : ℕ) : ℕ → Amplification.Circuit
  | 0 => [.prepare]
  | r + 1 =>
      if r < ℓ then prefixWord ℓ r ++ Amplification.groverStep
      else prefixWord ℓ r

theorem prefixWord_eq_grover (ℓ r : ℕ) :
    prefixWord ℓ r = Amplification.groverCircuit (min r ℓ) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    by_cases h : r < ℓ
    · have hmin : min r ℓ = r := Nat.min_eq_left (by omega)
      have hmin' : min (r + 1) ℓ = r + 1 := Nat.min_eq_left (by omega)
      simp [prefixWord, h, ih, hmin, hmin', Amplification.groverCircuit]
    · have hmin : min r ℓ = ℓ := Nat.min_eq_right (by omega)
      have hmin' : min (r + 1) ℓ = ℓ := Nat.min_eq_right (by omega)
      simp [prefixWord, h, ih, hmin, hmin']

theorem circU_append (U : Reg Z ≃ₗᵢ[ℂ] Reg Z)
    (o : Z) (S : Z → Prop) (c d : Amplification.Circuit) :
    circU U o S (c ++ d) = (circU U o S c).trans (circU U o S d) := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    simp only [List.cons_append, circU, ih]
    rfl

/-- Uniform fixed schedule has the branch's Grover word on every label,
including inactive labels. The statement holds on an arbitrary input vector. -/
theorem slice_opaquePrefix (U : Reg Z ≃ₗᵢ[ℂ] Reg Z)
    (o : Z) (S : Z → Prop) {M : ℕ} (r : ℕ)
    (ψ : Reg (Σ _ : Fin M, Z)) (ℓ : Fin M) :
    slice ℓ (opaquePrefix U o S (fun s a => s < a.val) r ψ) =
      circU U o S (prefixWord ℓ.val r) (slice ℓ ψ) := by
  induction r with
  | zero => simp [opaquePrefix, prefixWord, circU, gateU, slice_sigmaOp]
  | succ r ih =>
    rw [opaquePrefix, LinearIsometryEquiv.trans_apply, slice_opaqueSlot]
    by_cases h : r < ℓ.val
    · simp only [h, ↓reduceIte, ih, prefixWord, circU_append,
        LinearIsometryEquiv.trans_apply]
    · simp only [h, ↓reduceIte, ih, prefixWord]

/-- At `M-1` slots every branch `ℓ<M` receives exactly `G^ℓ A`. -/
theorem slice_opaquePrefix_full (U : Reg Z ≃ₗᵢ[ℂ] Reg Z)
    (o : Z) (S : Z → Prop) {M : ℕ} (hM : 0 < M)
    (ψ : Reg (Σ _ : Fin M, Z)) (ℓ : Fin M) :
    slice ℓ (opaquePrefix U o S (fun s a => s < a.val) (M - 1) ψ) =
      circU U o S (Amplification.groverCircuit ℓ.val) (slice ℓ ψ) := by
  rw [slice_opaquePrefix, prefixWord_eq_grover]
  have hmin : min (M - 1) ℓ.val = ℓ.val := Nat.min_eq_right (by omega)
  rw [hmin]

/-- The oracle-independent square-root amplitudes of the maintained trial
mixture, on the single Fin M selector register. -/
noncomputable def choiceState (M : ℕ) : Reg (Fin M) :=
  WithLp.toLp 2 fun ℓ => ((Real.sqrt (Amplification.trialWeight M ℓ.val) : ℝ) : ℂ)

theorem choiceState_norm {M : ℕ} (hM : 0 < M) :
    ‖choiceState M‖ = 1 := by
  have hs : ‖choiceState M‖ ^ 2 = 1 := by
    rw [reg_norm_sq]
    simp only [choiceState, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (Amplification.trialWeight_nonneg M _)]
    exact Amplification.sum_trialWeight (Nat.ne_of_gt hM)
  nlinarith [norm_nonneg (choiceState M)]

/-- Any fixed initial selector basis state can be mapped to `choiceState` by
an input-independent gate, using the finite-dimensional unitary extension. -/
theorem exists_choiceGate {M : ℕ} (hM : 0 < M) (o : Fin M) :
    ∃ V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M), V (rket o) = choiceState M := by
  exact exists_unit_gate (norm_rket o) (choiceState_norm hM)

end QuarticQuery.Upper
