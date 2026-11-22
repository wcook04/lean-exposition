module

public import QuarticQuery.Model.Classical

/-!
# Basic facts about the quantum query model

The bit oracle is a linear isometry and an involution, measurement projectors are
orthogonal, and the branch masses of an adaptive program add up to the squared
norm. Programs relabel along a renaming of coordinates, so `Q` is invariant.

A decision tree compiles to an adaptive program on the workspace of the caller's
choice: swap the current basis vector for the next query, query, measure the
answer bit, and keep the classical record in the program's own branches. That
gives `QLe f t` from `DLe f t`, hence the read-all witness that makes the infimum
in `Q` attained.
-/

@[expose] public section

namespace QuarticQuery

variable {ι κ : Type} {w : ℕ}

/-! ## Permuting amplitudes -/

/-- The action of `O_x` on basis labels. -/
def flipPoint (x : BitInput ι) (p : Basis ι w) : Basis ι w :=
  (p.1, (if x p.1 then !p.2.1 else p.2.1), p.2.2)

theorem flipPoint_flipPoint (x : BitInput ι) (p : Basis ι w) :
    flipPoint x (flipPoint x p) = p := by
  obtain ⟨i, c, z⟩ := p
  cases hx : x i <;> simp [flipPoint, hx]

/-- `flipPoint` as a permutation of the basis labels. -/
def flipPerm (x : BitInput ι) : Equiv.Perm (Basis ι w) :=
  Function.Involutive.toPerm (flipPoint x) (flipPoint_flipPoint x)

section

variable [Fintype ι] [Fintype κ]

/-- A bijection of basis labels moves amplitudes isometrically. -/
noncomputable def permIsometry (e : Basis ι w ≃ Basis κ w) : State ι w ≃ₗᵢ[ℂ] State κ w :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

theorem permIsometry_apply (e : Basis ι w ≃ Basis κ w) (ψ : State ι w) (p : Basis κ w) :
    (permIsometry e ψ).ofLp p = ψ.ofLp (e.symm p) := by
  simp [permIsometry, LinearIsometryEquiv.piLpCongrLeft_apply]

/-! ## The bit oracle -/

theorem bitOracle_apply (x : BitInput ι) (ψ : State ι w) (p : Basis ι w) :
    (bitOracle x ψ).ofLp p = ψ.ofLp (flipPoint x p) := rfl

/-- Ledger: def-query-oracle. `O_x` as a linear isometry equivalence. -/
noncomputable def bitOracleL (x : BitInput ι) : State ι w ≃ₗᵢ[ℂ] State ι w :=
  permIsometry (flipPerm x)

theorem bitOracleL_apply (x : BitInput ι) (ψ : State ι w) :
    bitOracleL x ψ = bitOracle x ψ := by
  ext p
  simp only [bitOracleL, permIsometry_apply, bitOracle_apply]
  rfl

/-- Ledger: def-query-oracle. The oracle is additive. -/
theorem bitOracle_add (x : BitInput ι) (ψ φ : State ι w) :
    bitOracle x (ψ + φ) = bitOracle x ψ + bitOracle x φ := by
  simp only [← bitOracleL_apply, map_add]

/-- Ledger: def-query-oracle. The oracle is homogeneous. -/
theorem bitOracle_smul (x : BitInput ι) (c : ℂ) (ψ : State ι w) :
    bitOracle x (c • ψ) = c • bitOracle x ψ := by
  simp only [← bitOracleL_apply, map_smul]

/-- Ledger: def-query-oracle. The oracle preserves the norm. -/
theorem norm_bitOracle (x : BitInput ι) (ψ : State ι w) : ‖bitOracle x ψ‖ = ‖ψ‖ := by
  rw [← bitOracleL_apply]
  exact (bitOracleL x).norm_map ψ

/-- Ledger: def-query-oracle. The oracle is an involution. -/
theorem bitOracle_bitOracle (x : BitInput ι) (ψ : State ι w) :
    bitOracle x (bitOracle x ψ) = ψ := by
  ext p
  simp only [bitOracle_apply, flipPoint_flipPoint]

/-! ## Projective measurement -/

theorem project_apply_of_mem {S : Finset (Basis ι w)} (ψ : State ι w) {p : Basis ι w}
    (hp : p ∈ S) : (project S ψ).ofLp p = ψ.ofLp p := by
  simp [project, hp]

theorem project_apply_of_notMem {S : Finset (Basis ι w)} (ψ : State ι w) {p : Basis ι w}
    (hp : p ∉ S) : (project S ψ).ofLp p = 0 := by
  simp [project, hp]

/-- The coordinate projector is additive. -/
theorem project_add (S : Finset (Basis ι w)) (ψ φ : State ι w) :
    project S (ψ + φ) = project S ψ + project S φ := by
  ext p
  by_cases hp : p ∈ S <;> simp [project_apply_of_mem, project_apply_of_notMem, hp]

/-- The coordinate projector is homogeneous. -/
theorem project_smul (S : Finset (Basis ι w)) (c : ℂ) (ψ : State ι w) :
    project S (c • ψ) = c • project S ψ := by
  ext p
  by_cases hp : p ∈ S <;> simp [project_apply_of_mem, project_apply_of_notMem, hp]

/-- `project S` as a linear map. -/
noncomputable def projectL (S : Finset (Basis ι w)) : State ι w →ₗ[ℂ] State ι w where
  toFun := project S
  map_add' := project_add S
  map_smul' := project_smul S

/-- The coordinate projector is idempotent. -/
theorem project_project (S : Finset (Basis ι w)) (ψ : State ι w) :
    project S (project S ψ) = project S ψ := by
  ext p
  by_cases hp : p ∈ S <;> simp [project_apply_of_mem, project_apply_of_notMem, hp]

/-- Measurement splits the squared norm between its two outcomes. -/
theorem norm_sq_eq_project_add (S : Finset (Basis ι w)) (ψ : State ι w) :
    ‖ψ‖ ^ 2 = ‖project S ψ‖ ^ 2 + ‖ψ - project S ψ‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p ∈ S <;> simp [project_apply_of_mem, project_apply_of_notMem, hp]

/-! ## Branch mass -/

namespace AdaptiveProgram

/-- Ledger: def-Q. A branch mass is nonnegative. -/
theorem outputMass_nonneg (A : AdaptiveProgram ι w) (x : BitInput ι) (ψ : State ι w) (b : Bool) :
    0 ≤ A.outputMass x ψ b := by
  induction A generalizing ψ with
  | output a =>
    simp only [outputMass]
    split <;> positivity
  | unitary U next ih => exact ih _
  | query next ih => exact ih _
  | measure S yes no ihy ihn => exact add_nonneg (ihy _) (ihn _)

/-- Ledger: def-Q. The two output masses exhaust the squared norm. -/
theorem outputMass_true_add_false (A : AdaptiveProgram ι w) (x : BitInput ι) (ψ : State ι w) :
    A.outputMass x ψ true + A.outputMass x ψ false = ‖ψ‖ ^ 2 := by
  induction A generalizing ψ with
  | output a => cases a <;> simp [outputMass]
  | unitary U next ih =>
    simp only [outputMass]
    rw [ih, U.norm_map]
  | query next ih =>
    simp only [outputMass]
    rw [ih, norm_bitOracle]
  | measure S yes no ihy ihn =>
    have h := norm_sq_eq_project_add S ψ
    have hy := ihy (project S ψ)
    have hn := ihn (ψ - project S ψ)
    simp only [outputMass]
    linarith

/-- Each output mass is at most the squared norm. -/
theorem outputMass_le (A : AdaptiveProgram ι w) (x : BitInput ι) (ψ : State ι w) (b : Bool) :
    A.outputMass x ψ b ≤ ‖ψ‖ ^ 2 := by
  have h := A.outputMass_true_add_false x ψ
  have ht := A.outputMass_nonneg x ψ true
  have hf := A.outputMass_nonneg x ψ false
  cases b <;> linarith

/-- The zero branch contributes nothing. -/
theorem outputMass_zero (A : AdaptiveProgram ι w) (x : BitInput ι) (b : Bool) :
    A.outputMass x 0 b = 0 := by
  have h := A.outputMass_le x 0 b
  have h' := A.outputMass_nonneg x 0 b
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  linarith

end AdaptiveProgram

/-! ## Budgets -/

/-- `QLe` is monotone in the budget. -/
theorem QLe.mono {f : PartialBool ι} {s t : ℕ} (h : QLe f s) (hst : s ≤ t) : QLe f t := by
  rcases h with h | ⟨w, ψ, A, hψ, hA, hc⟩
  · exact .inl h
  · exact .inr ⟨w, ψ, A, hψ, hA.trans hst, hc⟩

/-- Ledger: def-Q. A witness bounds `Q`. -/
theorem Q_le_of_QLe {f : PartialBool ι} {t : ℕ} (h : QLe f t) : Q f ≤ t :=
  Nat.sInf_le h

/-! ## Relabelling a program -/

/-- A renaming of coordinates acts on basis labels, fixing the other two registers. -/
def basisEquiv (e : ι ≃ κ) : Basis ι w ≃ Basis κ w :=
  Equiv.prodCongr e (Equiv.refl _)

/-- A renaming of coordinates carries states isometrically. -/
noncomputable def stateEquiv (e : ι ≃ κ) : State ι w ≃ₗᵢ[ℂ] State κ w :=
  permIsometry (basisEquiv e)

theorem bitOracle_stateEquiv (e : ι ≃ κ) (x : BitInput κ) (ψ : State ι w) :
    bitOracle x (stateEquiv e ψ) = stateEquiv e (bitOracle (fun i => x (e i)) ψ) := by
  ext p
  simp [stateEquiv, permIsometry_apply, bitOracle_apply, flipPoint, basisEquiv]

theorem project_stateEquiv (e : ι ≃ κ) (S : Finset (Basis ι w)) (ψ : State ι w) :
    project (S.map (basisEquiv e).toEmbedding) (stateEquiv e ψ) = stateEquiv e (project S ψ) := by
  ext p
  have hmem : p ∈ S.map (basisEquiv (w := w) e).toEmbedding ↔ (basisEquiv e).symm p ∈ S := by
    simp [Finset.mem_map_equiv]
  by_cases hp : (basisEquiv e).symm p ∈ S
  · rw [project_apply_of_mem _ (hmem.mpr hp)]
    simp only [stateEquiv, permIsometry_apply, project_apply_of_mem _ hp]
  · rw [project_apply_of_notMem _ (fun h => hp (hmem.mp h))]
    simp only [stateEquiv, permIsometry_apply, project_apply_of_notMem _ hp]

/-- Conjugate every gate, relabel every measurement, keep the query count. -/
noncomputable def AdaptiveProgram.relabel (e : ι ≃ κ) :
    AdaptiveProgram ι w → AdaptiveProgram κ w
  | .output a => .output a
  | .unitary U next =>
    .unitary ((stateEquiv e).toLinearIsometry.comp
      (U.comp (stateEquiv e).symm.toLinearIsometry)) (next.relabel e)
  | .query next => .query (next.relabel e)
  | .measure S yes no =>
    .measure (S.map (basisEquiv e).toEmbedding) (yes.relabel e) (no.relabel e)

@[simp] theorem AdaptiveProgram.queryCap_relabel (e : ι ≃ κ) (A : AdaptiveProgram ι w) :
    (A.relabel e).queryCap = A.queryCap := by
  induction A with
  | output a => rfl
  | unitary U next ih => simpa [relabel, queryCap] using ih
  | query next ih => simp [relabel, queryCap, ih]
  | measure S yes no ihy ihn => simp [relabel, queryCap, ihy, ihn]

/-- A relabelled program on `x` behaves as the original does on the pulled-back input. -/
theorem AdaptiveProgram.outputMass_relabel (e : ι ≃ κ) (A : AdaptiveProgram ι w)
    (x : BitInput κ) (ψ : State ι w) (b : Bool) :
    (A.relabel e).outputMass x (stateEquiv e ψ) b =
      A.outputMass (fun i => x (e i)) ψ b := by
  induction A generalizing ψ with
  | output a => simp [relabel, outputMass]
  | unitary U next ih =>
    simp only [relabel, outputMass]
    rw [← ih]
    simp
  | query next ih =>
    simp only [relabel, outputMass]
    rw [bitOracle_stateEquiv, ih]
  | measure S yes no ihy ihn =>
    simp only [relabel, outputMass]
    rw [project_stateEquiv, ihy, ← map_sub, ihn]

/-- Ledger: def-Q. Renaming coordinates makes no queries. -/
theorem QLe.reindex (e : ι ≃ κ) {f : PartialBool ι} {t : ℕ} (h : QLe f t) :
    QLe (QuarticQuery.reindex e f) t := by
  rcases h with ⟨b, hb⟩ | ⟨w, ψ, A, hψ, hA, hc⟩
  · exact .inl ⟨b, fun x c hx => hb _ c hx⟩
  · refine .inr ⟨w, stateEquiv e ψ, A.relabel e, ?_, by simpa using hA, fun x b hx => ?_⟩
    · rw [(stateEquiv e).norm_map, hψ]
    · rw [AdaptiveProgram.outputMass_relabel]
      exact hc _ b hx

/-- Ledger: def-Q. Renaming coordinates makes no queries. -/
theorem QLe_reindex_iff (e : ι ≃ κ) {f : PartialBool ι} {t : ℕ} :
    QLe (QuarticQuery.reindex e f) t ↔ QLe f t := by
  constructor
  · intro h
    have := h.reindex e.symm
    rwa [reindex_symm_reindex] at this
  · exact QLe.reindex e

/-- Ledger: def-Q. `Q` does not see the names of the coordinates. -/
theorem Q_reindex (e : ι ≃ κ) (f : PartialBool ι) : Q (QuarticQuery.reindex e f) = Q f := by
  simp only [Q, QLe_reindex_iff]

/-! ## Compiling a decision tree -/

open Classical in
/-- The basis vector `|p⟩`. -/
noncomputable def ket (p : Basis ι w) : State ι w := EuclideanSpace.single p 1

theorem norm_ket (p : Basis ι w) : ‖(ket p : State ι w)‖ = 1 := by
  simp [ket]

open Classical in
theorem ket_apply (p q : Basis ι w) : (ket p : State ι w).ofLp q = if q = p then 1 else 0 := by
  simp [ket]

theorem permIsometry_ket (e : Basis ι w ≃ Basis κ w) (p : Basis ι w) :
    permIsometry e (ket p) = ket (e p) := by
  classical
  ext q
  simp only [permIsometry_apply, ket_apply, Equiv.symm_apply_eq]

theorem bitOracle_ket (x : BitInput ι) (p : Basis ι w) :
    bitOracle x (ket p) = ket (flipPoint x p) := by
  rw [← bitOracleL_apply, bitOracleL, permIsometry_ket]
  rfl

theorem project_ket_of_mem {S : Finset (Basis ι w)} {p : Basis ι w} (hp : p ∈ S) :
    project S (ket p) = ket p := by
  classical
  ext q
  by_cases hq : q ∈ S
  · rw [project_apply_of_mem _ hq]
  · have hne : q ≠ p := by
      rintro rfl
      exact hq hp
    rw [project_apply_of_notMem _ hq, ket_apply]
    simp [hne]

theorem project_ket_of_notMem {S : Finset (Basis ι w)} {p : Basis ι w} (hp : p ∉ S) :
    project S (ket p) = 0 := by
  classical
  ext q
  by_cases hq : q ∈ S
  · have hne : q ≠ p := by
      rintro rfl
      exact hp hq
    rw [project_apply_of_mem _ hq, ket_apply]
    simp [hne]
  · rw [project_apply_of_notMem _ hq]
    rfl

open Classical in
/-- The gate exchanging two basis vectors. -/
noncomputable def swapGate (p q : Basis ι w) : State ι w →ₗᵢ[ℂ] State ι w :=
  (permIsometry (Equiv.swap p q)).toLinearIsometry

theorem swapGate_ket (p q : Basis ι w) : swapGate p q (ket p) = ket q := by
  classical
  simp [swapGate, permIsometry_ket]

/-- The address and answer registers holding `i` with a clear answer bit. -/
def readyPoint (i : ι) : Basis ι w := (i, false, 0)

/-- The address and answer registers holding `i` with answer `true`. -/
def setPoint (i : ι) : Basis ι w := (i, true, 0)

/-- Run a decision tree: from the known basis vector `p`, swap to `|i, 0, 0⟩`,
query, and measure the answer bit. The branches of the program are the tree's. -/
noncomputable def AdaptiveProgram.ofTree : Basis ι w → QueryTree ι → AdaptiveProgram ι w
  | _, .leaf b => .output b
  | p, .query i l r =>
    .unitary (swapGate p (readyPoint i)) <| .query <|
      .measure {setPoint i} (ofTree (setPoint i) r) (ofTree (readyPoint i) l)

@[simp] theorem AdaptiveProgram.queryCap_ofTree (p : Basis ι w) (t : QueryTree ι) :
    (ofTree p t).queryCap = t.depth := by
  induction t generalizing p with
  | leaf b => rfl
  | query i l r ihl ihr =>
    simp only [ofTree, queryCap, QueryTree.depth_query, ihl, ihr]
    rw [max_comm]

/-- The compiled program outputs the tree's answer with certainty. -/
theorem AdaptiveProgram.outputMass_ofTree (p : Basis ι w) (t : QueryTree ι) (x : BitInput ι)
    (b : Bool) : (ofTree p t).outputMass x (ket p) b = if t.eval x = b then 1 else 0 := by
  induction t generalizing p with
  | leaf a => cases a <;> cases b <;> simp [ofTree, outputMass, norm_ket]
  | query i l r ihl ihr =>
    have hflip : flipPoint x (readyPoint i : Basis ι w) =
        if x i then setPoint i else readyPoint i := by
      cases hx : x i <;> simp [flipPoint, readyPoint, setPoint, hx]
    simp only [ofTree, outputMass]
    rw [swapGate_ket, bitOracle_ket, hflip, QueryTree.eval_query]
    cases hx : x i
    · have hne : (readyPoint i : Basis ι w) ∉ ({setPoint i} : Finset (Basis ι w)) := by
        simp [readyPoint, setPoint]
      simp only [Bool.false_eq_true, ite_false]
      rw [project_ket_of_notMem hne, outputMass_zero, sub_zero, ihl, zero_add]
    · simp only [ite_true]
      rw [project_ket_of_mem (Finset.mem_singleton_self _), sub_self, outputMass_zero, ihr,
        add_zero]

omit [Fintype ι] in
/-- With no coordinates there is one input, so every function is constant on its
promise. -/
theorem constantOnPromise_of_isEmpty [IsEmpty ι] (f : PartialBool ι) : ConstantOnPromise f := by
  refine ⟨(f fun _ => false).getD false, fun x c hx => ?_⟩
  have hxe : x = fun _ => false := funext fun i => isEmptyElim i
  rw [← hxe, hx]
  rfl

/-- Ledger: def-Q. A decision tree is a quantum program of the same cost: measuring
the answer bit keeps the run classical. -/
theorem DLe.toQLe {f : PartialBool ι} {t : ℕ} (h : DLe f t) : QLe f t := by
  cases isEmpty_or_nonempty ι with
  | inl _ => exact .inl (constantOnPromise_of_isEmpty f)
  | inr hι =>
    obtain ⟨i₀⟩ := hι
    obtain ⟨T, hT, hc⟩ := h
    refine .inr ⟨0, ket (readyPoint i₀), .ofTree (readyPoint i₀) T, norm_ket _,
      by simpa using hT, fun x b hx => ?_⟩
    rw [AdaptiveProgram.outputMass_ofTree]
    norm_num [hc x b hx]

/-- Ledger: def-Q. The read-all witness: `QLe f n` for every finite `f`. -/
theorem QLe_card (f : PartialBool ι) : QLe f (Fintype.card ι) :=
  (DLe_card f).toQLe

/-- The set defining `Q` is nonempty, so `sInf` in `Q` is a true minimum. -/
theorem QLe_set_nonempty (f : PartialBool ι) : {t : ℕ | QLe f t}.Nonempty :=
  ⟨_, QLe_card f⟩

/-- Ledger: def-Q. The infimum is attained. -/
theorem QLe_Q (f : PartialBool ι) : QLe f (Q f) :=
  Nat.sInf_mem (QLe_set_nonempty f)

/-- Ledger: def-Q. `Q` is the least budget. -/
theorem Q_le_iff {f : PartialBool ι} {t : ℕ} : Q f ≤ t ↔ QLe f t :=
  ⟨(QLe_Q f).mono, Q_le_of_QLe⟩

/-- Quantum cost is at most deterministic cost. -/
theorem Q_le_D (f : PartialBool ι) : Q f ≤ D f :=
  Q_le_of_QLe (DLe_D f).toQLe

/-- Quantum cost is at most the number of coordinates. -/
theorem Q_le_card (f : PartialBool ι) : Q f ≤ Fintype.card ι :=
  Q_le_of_QLe (QLe_card f)

end

end QuarticQuery
