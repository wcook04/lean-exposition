module

public import QuarticQuery.Bridge.Oracle

/-!
# Deferring measurement: adaptive programs as fixed sequences

Every `AdaptiveProgram` with `queryCap ≤ T` becomes a fixed sequence of exactly `T`
controlled phase queries with the same acceptance probability on every input and
every starting vector. There is no query overhead, so the paper's factor from
controlled queries does not appear.

The workspace is grown by structural recursion on the program. A measurement takes
the direct sum `W₁ ⊕ W₂` of the workspaces of its branches, with the summand acting
as the coherent record of the outcome: the phase oracle acts block by block, so both
branches query in lockstep and no controlled query is needed. A branch that has
finished keeps being queried on its own block. That is harmless, since `output`
reads only the norm and every query preserves it. Unitary steps and measurement
splits go into the isometry entering the simulation, and the one place a gate has
to be chosen is after a query, by extending an isometry from a subspace to the
whole finite-dimensional space (`exists_gate`).
-/

public section

namespace QuarticQuery

open Cslib.Quantum (phaseOracle phaseOracle_apply run measureProb norm_run)

variable {N w : ℕ} {W W₁ W₂ : Type}

/-! ## Direct sums of workspaces -/

/-- The block of `W₁`. -/
@[expose] noncomputable def resL : QState N (W₁ ⊕ W₂) →ₗ[ℂ] QState N W₁ where
  toFun Ψ := WithLp.toLp 2 fun p => Ψ.ofLp (p.1, p.2.1, Sum.inl p.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The block of `W₂`. -/
@[expose] noncomputable def resR : QState N (W₁ ⊕ W₂) →ₗ[ℂ] QState N W₂ where
  toFun Ψ := WithLp.toLp 2 fun p => Ψ.ofLp (p.1, p.2.1, Sum.inr p.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Two blocks side by side. -/
@[expose] noncomputable def join (a : QState N W₁) (b : QState N W₂) : QState N (W₁ ⊕ W₂) :=
  WithLp.toLp 2 fun p =>
    Sum.elim (fun z => a.ofLp (p.1, p.2.1, z)) (fun z => b.ofLp (p.1, p.2.1, z)) p.2.2

theorem join_inl (a : QState N W₁) (b : QState N W₂) (i : Fin N) (c : Bool) (z : W₁) :
    (join a b).ofLp (i, c, Sum.inl z) = a.ofLp (i, c, z) := rfl

theorem join_inr (a : QState N W₁) (b : QState N W₂) (i : Fin N) (c : Bool) (z : W₂) :
    (join a b).ofLp (i, c, Sum.inr z) = b.ofLp (i, c, z) := rfl

theorem resL_join (a : QState N W₁) (b : QState N W₂) : resL (join a b) = a := rfl

theorem resR_join (a : QState N W₁) (b : QState N W₂) : resR (join a b) = b := rfl

theorem join_add (a a' : QState N W₁) (b b' : QState N W₂) :
    join (a + a') (b + b') = join a b + join a' b' := by
  ext ⟨i, c, z | z⟩ <;> rfl

theorem join_smul (k : ℂ) (a : QState N W₁) (b : QState N W₂) :
    join (k • a) (k • b) = k • join a b := by
  ext ⟨i, c, z | z⟩ <;> rfl

theorem phaseOracle_join (x : Fin N → Bool) (a : QState N W₁) (b : QState N W₂) :
    phaseOracle x (join a b) = join (phaseOracle x a) (phaseOracle x b) := by
  ext ⟨i, c, z | z⟩ <;> rfl

variable [Fintype W₁] [Fintype W₂]

theorem norm_sq_res (Ψ : QState N (W₁ ⊕ W₂)) : ‖Ψ‖ ^ 2 = ‖resL Ψ‖ ^ 2 + ‖resR Ψ‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fintype.sum_sum_type,
    Finset.sum_add_distrib]
  rfl

theorem norm_sq_join (a : QState N W₁) (b : QState N W₂) :
    ‖join a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [norm_sq_res, resL_join, resR_join]

/-- Two gates acting block by block. -/
@[expose] noncomputable def dsum (U₁ : QState N W₁ →ₗᵢ[ℂ] QState N W₁)
    (U₂ : QState N W₂ →ₗᵢ[ℂ] QState N W₂) :
    QState N (W₁ ⊕ W₂) →ₗᵢ[ℂ] QState N (W₁ ⊕ W₂) where
  toFun Ψ := join (U₁ (resL Ψ)) (U₂ (resR Ψ))
  map_add' Ψ Φ := by simp only [map_add, join_add]
  map_smul' k Ψ := by simp only [map_smul, join_smul, RingHom.id_apply]
  norm_map' Ψ := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    change ‖join (U₁ (resL Ψ)) (U₂ (resR Ψ))‖ ^ 2 = _
    rw [norm_sq_join, U₁.norm_map, U₂.norm_map, ← norm_sq_res]

theorem dsum_join (U₁ : QState N W₁ →ₗᵢ[ℂ] QState N W₁) (U₂ : QState N W₂ →ₗᵢ[ℂ] QState N W₂)
    (a : QState N W₁) (b : QState N W₂) : dsum U₁ U₂ (join a b) = join (U₁ a) (U₂ b) := rfl

/-- Block sequences run independently. -/
theorem run_dsum (U₁ : ℕ → QState N W₁ →ₗᵢ[ℂ] QState N W₁)
    (U₂ : ℕ → QState N W₂ →ₗᵢ[ℂ] QState N W₂) (a : QState N W₁) (b : QState N W₂)
    (x : Fin N → Bool) (t : ℕ) :
    run (fun s => dsum (U₁ s) (U₂ s)) (join a b) x t = join (run U₁ a x t) (run U₂ b x t) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [run, ih, phaseOracle_join, dsum_join]

/-- The acceptance set of a direct sum. -/
@[expose] def acceptSum (S₁ : Finset (Fin N × Bool × W₁)) (S₂ : Finset (Fin N × Bool × W₂)) :
    Finset (Fin N × Bool × (W₁ ⊕ W₂)) :=
  (S₁.map ⟨fun p => (p.1, p.2.1, Sum.inl p.2.2), fun p q h => by
      obtain ⟨i, c, z⟩ := p
      obtain ⟨i', c', z'⟩ := q
      simpa using h⟩).disjUnion
    (S₂.map ⟨fun p => (p.1, p.2.1, Sum.inr p.2.2), fun p q h => by
      obtain ⟨i, c, z⟩ := p
      obtain ⟨i', c', z'⟩ := q
      simpa using h⟩)
    (by
      simp only [Finset.disjoint_left, Finset.mem_map]
      rintro _ ⟨p, _, rfl⟩ ⟨q, _, h⟩
      change (q.1, q.2.1, Sum.inr q.2.2) = (p.1, p.2.1, Sum.inl p.2.2) at h
      simp at h)

omit [Fintype W₁] [Fintype W₂] in
theorem measureProb_join (a : QState N W₁) (b : QState N W₂) (S₁ : Finset (Fin N × Bool × W₁))
    (S₂ : Finset (Fin N × Bool × W₂)) :
    measureProb (join a b) (acceptSum S₁ S₂) = measureProb a S₁ + measureProb b S₂ := by
  simp only [measureProb, acceptSum, Finset.sum_disjUnion, Finset.sum_map]
  rfl

/-! ## Choosing a gate -/

/-- Two isometries into a finite-dimensional space differ by a gate. -/
theorem exists_gate [Fintype W] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c L : H →ₗᵢ[ℂ] QState N W) :
    ∃ Z : QState N W →ₗᵢ[ℂ] QState N W, ∀ φ, Z (c φ) = L φ := by
  let M : LinearMap.range c.toLinearMap →ₗᵢ[ℂ] QState N W :=
    L.comp c.equivRange.symm.toLinearIsometry
  refine ⟨M.extend, fun φ => ?_⟩
  have h := LinearIsometry.extend_apply M (c.equivRange φ)
  simpa [M] using h

/-! ## The simulation -/

/-- A fixed sequence of `T` phase queries simulating `A`, on every starting vector.
`embed` commutes with the oracle and is what the next query enters through. -/
structure FixedSim (A : AdaptiveProgram (Fin N) w) (T : ℕ) where
  W : Type
  fintype : Fintype W
  embed : State (Fin N) w →ₗᵢ[ℂ] QState N W
  embed_phase : ∀ (x : Fin N → Bool) φ, embed (phaseOracle x φ) = phaseOracle x (embed φ)
  entry : State (Fin N) w →ₗᵢ[ℂ] QState N W
  gate : ℕ → QState N W →ₗᵢ[ℂ] QState N W
  accept : Finset (Fin N × Bool × W)
  spec : ∀ (x : Fin N → Bool) ψ,
    measureProb (run gate (entry ψ) x T) accept = AdaptiveProgram.outputMass A x ψ true

attribute [instance] FixedSim.fintype

/-- A finished program idles on its own block. -/
noncomputable def FixedSim.output (a : Bool) (T : ℕ) :
    FixedSim (.output a : AdaptiveProgram (Fin N) w) T where
  W := Fin (w + 1)
  fintype := inferInstance
  embed := LinearIsometry.id
  embed_phase _ _ := rfl
  entry := LinearIsometry.id
  gate _ := LinearIsometry.id
  accept := if a then Finset.univ else ∅
  spec x ψ := by
    cases a
    · simp [AdaptiveProgram.outputMass, measureProb]
    · simp only [if_true, AdaptiveProgram.outputMass]
      rw [Cslib.Quantum.measureProb_univ, norm_run]
      rfl

/-- A unitary step goes into the entry. -/
noncomputable def FixedSim.unitary {V : State (Fin N) w →ₗᵢ[ℂ] State (Fin N) w}
    {A : AdaptiveProgram (Fin N) w} {T : ℕ} (s : FixedSim A T) :
    FixedSim (.unitary V A) T where
  W := s.W
  fintype := s.fintype
  embed := s.embed
  embed_phase := s.embed_phase
  entry := s.entry.comp V
  gate := s.gate
  accept := s.accept
  spec x ψ := s.spec x (V ψ)

/-- A query: enter in the Hadamard basis, query, then hand over to the simulation of
what follows through a gate. -/
noncomputable def FixedSim.query {A : AdaptiveProgram (Fin N) w} {T : ℕ} (s : FixedSim A T) :
    FixedSim (.query A) (T + 1) :=
  let Z := Classical.choose (exists_gate s.embed (s.entry.comp hadamard))
  have hZ : ∀ φ, Z (s.embed φ) = s.entry (hadamard φ) :=
    Classical.choose_spec (exists_gate s.embed (s.entry.comp hadamard))
  let gate' : ℕ → QState N s.W →ₗᵢ[ℂ] QState N s.W := fun t =>
    match t with
    | 0 => LinearIsometry.id
    | 1 => (s.gate 0).comp Z
    | t + 2 => s.gate (t + 1)
  have key : ∀ (x : Fin N → Bool) (ψ : State (Fin N) w) (t : ℕ),
      run gate' (s.embed (hadamard ψ)) x (t + 1) = run s.gate (s.entry (bitOracle x ψ)) x t := by
    intro x ψ t
    induction t with
    | zero =>
      change s.gate 0 (Z (phaseOracle x (s.embed (hadamard ψ)))) = s.gate 0 _
      rw [← s.embed_phase, hZ, hadamard_phaseOracle_hadamard]
    | succ t ih =>
      change s.gate (t + 1) (phaseOracle x (run gate' _ x (t + 1))) = _
      rw [ih]
      rfl
  { W := s.W
    fintype := s.fintype
    embed := s.embed
    embed_phase := s.embed_phase
    entry := s.embed.comp hadamard
    gate := gate'
    accept := s.accept
    spec := fun x ψ => by
      change measureProb (run gate' (s.embed (hadamard ψ)) x (T + 1)) s.accept = _
      rw [key, s.spec]
      rfl }

/-- A measurement: the two outcomes enter their own blocks. -/
noncomputable def FixedSim.measure (S : Finset (Basis (Fin N) w))
    {A B : AdaptiveProgram (Fin N) w} {T : ℕ} (s : FixedSim A T) (t : FixedSim B T) :
    FixedSim (.measure S A B) T :=
  letI := s.fintype
  letI := t.fintype
  { W := s.W ⊕ t.W
    fintype := inferInstance
    embed :=
      { toFun := fun φ => join (s.embed φ) 0
        map_add' := fun φ φ' => by
          conv_lhs => rw [map_add, ← add_zero (0 : QState N t.W), join_add]
        map_smul' := fun k φ => by
          conv_lhs => rw [map_smul, ← smul_zero k, join_smul]
          rfl
        norm_map' := fun φ => by
          refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
          change ‖join (s.embed φ) 0‖ ^ 2 = _
          rw [norm_sq_join, s.embed.norm_map]
          simp }
    embed_phase := fun x φ => by
      change join (s.embed (phaseOracle x φ)) 0 = phaseOracle x (join (s.embed φ) 0)
      rw [phaseOracle_join, s.embed_phase, map_zero]
    entry :=
      { toFun := fun ψ => join (s.entry (project S ψ)) (t.entry (ψ - project S ψ))
        map_add' := fun ψ φ => by
          rw [project_add, map_add, add_sub_add_comm, map_add, join_add]
        map_smul' := fun k ψ => by
          rw [project_smul, map_smul, ← smul_sub, map_smul, join_smul]
          rfl
        norm_map' := fun ψ => by
          refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
          change ‖join (s.entry (project S ψ)) (t.entry (ψ - project S ψ))‖ ^ 2 = _
          rw [norm_sq_join, s.entry.norm_map, t.entry.norm_map, ← norm_sq_eq_project_add] }
    gate := fun r => dsum (s.gate r) (t.gate r)
    accept := acceptSum s.accept t.accept
    spec := fun x ψ => by
      change measureProb (run _ (join (s.entry (project S ψ)) (t.entry (ψ - project S ψ))) x T) _ = _
      rw [run_dsum, measureProb_join, s.spec, t.spec]
      rfl }

/-- Ledger: lem-A.2. Every program with `queryCap ≤ T` has a fixed simulation. -/
noncomputable def FixedSim.build :
    (A : AdaptiveProgram (Fin N) w) → (T : ℕ) → A.queryCap ≤ T → FixedSim A T
  | .output a, T, _ => .output a T
  | .unitary _ next, T, h => (FixedSim.build next T h).unitary
  | .query next, 0, h => absurd h (by simp [AdaptiveProgram.queryCap])
  | .query next, T + 1, h =>
    (FixedSim.build next T (by
      simp only [AdaptiveProgram.queryCap] at h
      omega)).query
  | .measure S yes no, T, h =>
    .measure S
      (FixedSim.build yes T (le_trans (le_max_left _ _) h))
      (FixedSim.build no T (le_trans (le_max_right _ _) h))

/-- Ledger: lem-A.2. Deferred measurement with no query overhead: an adaptive program
with `queryCap ≤ T` is `T` phase queries interleaved with input-independent gates on a
larger finite workspace, with the same acceptance probability on every input and from
every starting vector, and the starting vector enters through an isometry. -/
theorem exists_fixedSequence (A : AdaptiveProgram (Fin N) w) {T : ℕ} (hT : A.queryCap ≤ T) :
    ∃ (W' : Type) (_ : Fintype W') (entry : State (Fin N) w →ₗᵢ[ℂ] QState N W')
      (U : ℕ → QState N W' →ₗᵢ[ℂ] QState N W') (S : Finset (Fin N × Bool × W')),
      ∀ (x : BitInput (Fin N)) (ψ : State (Fin N) w),
        measureProb (run U (entry ψ) x T) S = A.outputMass x ψ true := by
  let s := FixedSim.build A T hT
  exact ⟨s.W, s.fintype, s.entry, s.gate, s.accept, s.spec⟩

end QuarticQuery
