module

public import QuarticQuery.Upper.Sampler

/-!
# From samplers to adaptive programs

`Runs c L` says an adaptive program with at most `c` bit queries on every branch
has classical result law `L x`, in continuation-passing form, so programs compose.
`Samples.runs` compiles a sampler: run the circuit, measure every basis vector,
branch classically on the outcome, and return to the fixed start state by a
swap. That reset is why no fresh registers are needed for classical
composition: after a full measurement the state is known to the program.

A read costs two bit queries on the program's own oracle: load the bit, act under it,
unload. The address register of `AdaptiveProgram` is parked at a fixed coordinate
between reads. The physical gates are extensions of isometries given on the
orthonormal vectors they will meet.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace QuarticQuery.Upper

open QuarticQuery.AdaptiveProgram

section Orth

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The isometry sending `|y⟩` to the orthonormal `v y`. -/
noncomputable def embOrth {Y : Type} [Fintype Y] (v : Y → E) (hv : Orthonormal ℂ v) :
    Reg Y →ₗᵢ[ℂ] E where
  toFun ψ := ∑ y, ψ.ofLp y • v y
  map_add' ψ φ := by
    simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a ψ := by
    simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]
  norm_map' ψ := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    have h := hv.inner_sum (fun y => ψ.ofLp y) (fun y => ψ.ofLp y) Finset.univ
    have hc : ∀ y, (starRingEnd ℂ) (ψ.ofLp y) * ψ.ofLp y = ((‖ψ.ofLp y‖ ^ 2 : ℝ) : ℂ) := fun y => by
      rw [Complex.conj_mul']
      push_cast
      rfl
    change ‖∑ y, ψ.ofLp y • v y‖ ^ 2 = ‖ψ‖ ^ 2
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), h, reg_norm_sq]
    simp only [hc]
    rw [← Complex.ofReal_sum]
    exact Complex.ofReal_re _

theorem embOrth_rket {Y : Type} [Fintype Y] (v : Y → E) (hv : Orthonormal ℂ v) (y : Y) :
    embOrth v hv (rket y) = v y := by
  classical
  change ∑ y', (rket y : Reg Y).ofLp y' • v y' = v y
  simp [rket_apply]

/-- Ledger: claim-coherent-access. A gate can take any orthonormal family to any other. -/
theorem exists_gate_orth {Y : Type} [Fintype Y] [FiniteDimensional ℂ E] (v v' : Y → E)
    (hv : Orthonormal ℂ v) (hv' : Orthonormal ℂ v') :
    ∃ G : E →ₗᵢ[ℂ] E, ∀ y, G (v y) = v' y := by
  obtain ⟨G, hG⟩ := exists_extend (embOrth v hv) (embOrth v' hv')
  refine ⟨G, fun y => ?_⟩
  have := hG (rket y)
  rwa [embOrth_rket, embOrth_rket] at this

end Orth

section

variable {ι : Type} [Fintype ι] {w : ℕ}

open Classical in
theorem inner_ket (p q : Basis ι w) :
    inner ℂ (ket p : State ι w) (ket q) = if p = q then 1 else 0 := by
  rw [ket, EuclideanSpace.inner_single_left, ket_apply]
  simp

theorem orthonormal_kets {Y : Type} (f : Y → Basis ι w) (hf : Function.Injective f)
    (s : Y → ℂ) (hs : ∀ y, ‖s y‖ = 1) :
    Orthonormal ℂ fun y => s y • (ket (f y) : State ι w) := by
  classical
  rw [orthonormal_iff_ite]
  intro y y'
  rw [inner_smul_left, inner_smul_right, inner_ket]
  by_cases h : y = y'
  · subst h
    simp [Complex.conj_mul', hs]
  · simp [h, hf.ne h]

theorem outputMass_smul (A : AdaptiveProgram ι w) (x : BitInput ι) (a : ℂ) (ψ : State ι w)
    (b : Bool) : A.outputMass x (a • ψ) b = ‖a‖ ^ 2 * A.outputMass x ψ b := by
  induction A generalizing ψ with
  | output c =>
    simp only [outputMass, norm_smul, mul_pow]
    split_ifs <;> simp
  | unitary U next ih =>
    simp only [outputMass, map_smul, ih]
  | query next ih =>
    simp only [outputMass, bitOracle_smul, ih]
  | measure S yes no ihy ihn =>
    simp only [outputMass]
    rw [project_smul, ← smul_sub, ihy, ihn]
    ring

/-! ## Physical layout -/

variable [Inhabited ι]

/-- The state every program stage starts from. -/
noncomputable def startState : State ι w := ket (default, false, 0)

theorem norm_startState : ‖(startState : State ι w)‖ = 1 := norm_ket _

variable {Z : Type} [Fintype Z] (e : Z ↪ Fin (w + 1))

/-- Where a logical label sits between reads. -/
def clPoint (z : Z) : Basis ι w := (default, false, e z)

theorem clPoint_injective : Function.Injective (clPoint (ι := ι) e) := fun a b h => by
  have := congrArg (fun p : Basis ι w => p.2.2) h
  exact e.injective this

theorem orthonormal_cl : Orthonormal ℂ fun z => (ket (clPoint e z) : State ι w) := by
  simpa using orthonormal_kets (clPoint e) (clPoint_injective e) (fun _ => 1) (by simp)

/-- The logical register inside the program state. -/
noncomputable def clEmb : Reg Z →ₗᵢ[ℂ] State ι w := embOrth _ (orthonormal_cl e)

theorem clEmb_rket (z : Z) : clEmb (ι := ι) e (rket z) = ket (clPoint e z) :=
  embOrth_rket _ _ z

theorem clEmb_apply_cl (ψ : Reg Z) (z : Z) :
    (clEmb (ι := ι) e ψ).ofLp (clPoint e z) = ψ.ofLp z := by
  classical
  change (∑ y, ψ.ofLp y • (ket (clPoint e y) : State ι w)).ofLp (clPoint e z) = _
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, ket_apply, smul_eq_mul,
    (clPoint_injective (ι := ι) e).eq_iff]
  simp

theorem clEmb_apply_of_ne (ψ : Reg Z) (p : Basis ι w) (hp : ∀ z, p ≠ clPoint e z) :
    (clEmb (ι := ι) e ψ).ofLp p = 0 := by
  classical
  change (∑ y, ψ.ofLp y • (ket (clPoint e y) : State ι w)).ofLp p = _
  simp [WithLp.ofLp_sum, Finset.sum_apply, ket_apply, hp]

/-- Ledger: claim-coherent-access. A read costs two bit queries: load the addressed bit
into the answer register, act under it, and unload it. -/
theorem compile_read (R : ReadSpec ι Z) :
    ∃ P : AdaptiveProgram ι w → AdaptiveProgram ι w, ∀ next,
      (P next).queryCap = 2 + next.queryCap ∧
      ∀ x ψ b, (P next).outputMass x (clEmb e ψ) b =
        next.outputMass x (clEmb e (R.op x ψ)) b := by
  classical
  let p₁ : Z → Basis ι w := fun z => (R.addr z, false, e z)
  let p₂ : Bool × Z → Basis ι w := fun q => (R.addr q.2, q.1, e q.2)
  have hp₁ : Function.Injective p₁ := fun a b h => by
    exact e.injective (congrArg (fun p : Basis ι w => p.2.2) h)
  have hp₂ : Function.Injective p₂ := fun a b h => by
    have h1 := congrArg (fun p : Basis ι w => p.2.1) h
    have h2 := e.injective (congrArg (fun p : Basis ι w => p.2.2) h)
    exact Prod.ext h1 h2
  let τ : Bool × Z → Bool × Z := fun q => (q.1, if q.1 then R.perm q.2 else q.2)
  have hτ : Function.Injective τ := by
    rintro ⟨c, a⟩ ⟨c', b⟩ h
    obtain ⟨rfl, h'⟩ := Prod.ext_iff.1 h
    cases c
    · simpa [τ] using h'
    · have := congrArg R.perm h'
      simpa [τ, R.perm_perm] using this
  let s : Bool × Z → ℂ := fun q => if q.1 && R.sign q.2 then -1 else 1
  have hs : ∀ q, ‖s q‖ = 1 := fun q => by
    simp only [s]
    split_ifs <;> simp
  obtain ⟨G₁, hG₁⟩ := exists_gate_orth (fun z => (ket (clPoint e z) : State ι w))
    (fun z => ket (p₁ z)) (orthonormal_cl e)
    (by simpa using orthonormal_kets p₁ hp₁ (fun _ => 1) (by simp))
  obtain ⟨G₂, hG₂⟩ := exists_gate_orth (fun q => (ket (p₂ q) : State ι w))
    (fun q => s q • ket (p₂ (τ q)))
    (by simpa using orthonormal_kets p₂ hp₂ (fun _ => 1) (by simp))
    (orthonormal_kets (p₂ ∘ τ) (hp₂.comp hτ) s hs)
  obtain ⟨G₃, hG₃⟩ := exists_gate_orth (fun z => (ket (p₁ z) : State ι w))
    (fun z => ket (clPoint e z))
    (by simpa using orthonormal_kets p₁ hp₁ (fun _ => 1) (by simp)) (orthonormal_cl e)
  refine ⟨fun next => .unitary G₁ (.query (.unitary G₂ (.query (.unitary G₃ next)))),
    fun next => ⟨?_, fun x ψ b => ?_⟩⟩
  · simp only [queryCap]
    omega
  · simp only [outputMass]
    congr 1
    let f : Reg Z →ₗ[ℂ] State ι w :=
      G₃.toLinearMap ∘ₗ (bitOracleL x).toLinearEquiv.toLinearMap ∘ₗ G₂.toLinearMap ∘ₗ
        (bitOracleL x).toLinearEquiv.toLinearMap ∘ₗ G₁.toLinearMap ∘ₗ
        (clEmb (ι := ι) e).toLinearMap
    let g : Reg Z →ₗ[ℂ] State ι w :=
      (clEmb (ι := ι) e).toLinearMap ∘ₗ (R.op x).toLinearEquiv.toLinearMap
    have hfg := reg_map_ext f g (fun z => ?_) ψ
    · simpa [f, g, bitOracleL_apply] using hfg
    · have hflip1 : flipPoint x (p₁ z) = p₂ (x (R.addr z), z) := by
        cases hx : x (R.addr z) <;> simp [flipPoint, p₁, p₂, hx]
      have hτd : τ (x (R.addr z), z) = (x (R.addr z), R.dest x z) := by
        cases hx : x (R.addr z) <;> simp [τ, ReadSpec.dest, hx]
      have hsc : s (x (R.addr z), z) = R.coef x z := rfl
      have hflip2 : flipPoint x (p₂ (x (R.addr z), R.dest x z)) = p₁ (R.dest x z) := by
        cases hx : x (R.addr z) <;>
          simp [flipPoint, p₁, p₂, R.addr_dest, hx]
      simp only [f, g, LinearMap.comp_apply, LinearIsometry.coe_toLinearMap,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe, bitOracleL_apply]
      change G₃ (bitOracle x (G₂ (bitOracle x (G₁ (clEmb e (rket z)))))) =
        clEmb e (R.op x (rket z))
      rw [clEmb_rket, hG₁, bitOracle_ket, hflip1, hG₂, hτd, hsc, bitOracle_smul, bitOracle_ket,
        hflip2, map_smul, hG₃, ReadSpec.op_rket, map_smul, clEmb_rket]

/-- Ledger: claim-coherent-access. A circuit of `n` reads costs `2 n` bit queries. -/
theorem compile_circ {n : ℕ} {F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z} (hF : IsCirc n F) :
    ∃ P : AdaptiveProgram ι w → AdaptiveProgram ι w, ∀ next,
      (P next).queryCap ≤ 2 * n + next.queryCap ∧
      ∀ x ψ b, (P next).outputMass x (clEmb e ψ) b =
        next.outputMass x (clEmb e (F x ψ)) b := by
  induction hF with
  | gate U =>
    obtain ⟨G, hG⟩ := exists_extend (clEmb (ι := ι) e)
      ((clEmb (ι := ι) e).comp U.toLinearIsometry)
    refine ⟨fun next => .unitary G next, fun next => ⟨by simp [queryCap], fun x ψ b => ?_⟩⟩
    simp only [outputMass, hG]
    rfl
  | @step n F h R U ih =>
    obtain ⟨P, hP⟩ := ih
    obtain ⟨Q, hQ⟩ := compile_read e R
    obtain ⟨G, hG⟩ := exists_extend (clEmb (ι := ι) e)
      ((clEmb (ι := ι) e).comp U.toLinearIsometry)
    refine ⟨fun next => P (Q (.unitary G next)), fun next => ⟨?_, fun x ψ b => ?_⟩⟩
    · have h1 := (hP (Q (.unitary G next))).1
      have h2 := (hQ (.unitary G next)).1
      simp only [queryCap] at h2
      change (P (Q (.unitary G next))).queryCap ≤ 2 * (n + 1) + next.queryCap
      omega
    · rw [(hP _).2, (hQ _).2]
      simp only [outputMass, hG]
      rfl

/-! ## Measuring everything -/

/-- Measure the labels of `l` one at a time, and on outcome `z` go back to the start
state and continue with `k z`. The fall-through branch has no mass. -/
noncomputable def measureAll (k : Z → AdaptiveProgram ι w) : List Z → AdaptiveProgram ι w
  | [] => .output false
  | z :: l => .measure {clPoint e z} (.unitary (swapGate (clPoint e z) (default, false, 0)) (k z))
      (measureAll k l)

theorem queryCap_measureAll (k : Z → AdaptiveProgram ι w) {d : ℕ}
    (hd : ∀ z, (k z).queryCap ≤ d) (l : List Z) : (measureAll e k l).queryCap ≤ d := by
  induction l with
  | nil => simp [measureAll, queryCap]
  | cons z l ih =>
    simp only [measureAll, queryCap]
    exact max_le (hd z) ih

theorem project_singleton (p : Basis ι w) (ψ : State ι w) :
    project {p} ψ = ψ.ofLp p • (ket p : State ι w) := by
  classical
  ext q
  by_cases h : q = p
  · subst h
    rw [project_apply_of_mem _ (Finset.mem_singleton_self _)]
    simp [ket_apply]
  · rw [project_apply_of_notMem _ (by simpa using h)]
    simp [ket_apply, h]

theorem outputMass_measureAll (k : Z → AdaptiveProgram ι w) (x : BitInput ι) (b : Bool)
    (l : List Z) (hl : l.Nodup) (Ψ : State ι w) (hΨ : ∀ p, (∀ z ∈ l, p ≠ clPoint e z) → Ψ.ofLp p = 0) :
    (measureAll e k l).outputMass x Ψ b =
      (l.map fun z => ‖Ψ.ofLp (clPoint e z)‖ ^ 2 * (k z).outputMass x startState b).sum := by
  classical
  induction l generalizing Ψ with
  | nil =>
    have : Ψ = 0 := by
      ext p
      exact hΨ p (by simp)
    subst this
    simp [measureAll, outputMass]
  | cons z l ih =>
    obtain ⟨hz, hnd⟩ := List.nodup_cons.1 hl
    simp only [measureAll, outputMass, List.map_cons, List.sum_cons]
    congr 1
    · rw [project_singleton, map_smul, swapGate_ket, outputMass_smul]
      rfl
    · have hval : ∀ z' ∈ l, (Ψ - project {clPoint e z} Ψ).ofLp (clPoint e z') =
          Ψ.ofLp (clPoint e z') := by
        intro z' hz'
        have hne : clPoint (ι := ι) e z' ≠ clPoint e z := fun h =>
          hz ((clPoint_injective e h) ▸ hz')
        rw [project_singleton]
        simp [ket_apply, hne]
      rw [ih hnd]
      · congr 1
        exact List.map_congr_left fun z' hz' => by rw [hval z' hz']
      · intro p hp
        by_cases hpz : p = clPoint e z
        · subst hpz
          rw [project_singleton]
          simp [ket_apply]
        · have : p ∉ ({clPoint e z} : Finset (Basis ι w)) := by simpa using hpz
          rw [project_singleton]
          simp only [PiLp.sub_apply, PiLp.smul_apply, ket_apply, hpz, ite_false, smul_eq_mul,
            mul_zero, sub_zero]
          exact hΨ p fun z' hz' => by
            rcases List.mem_cons.1 hz' with rfl | h
            · exact hpz
            · exact hp z' h

end

/-! ## Runs -/

variable {ι α β : Type} [Fintype ι] [Inhabited ι]

/-- A program with continuation: it stops in the start state with classical result `a`
having probability `L x a`. -/
def RunsW (w c : ℕ) [Fintype α] (L : BitInput ι → α → ℝ) : Prop :=
  ∃ P : (α → AdaptiveProgram ι w) → AdaptiveProgram ι w,
    ∀ (k : α → AdaptiveProgram ι w) (d : ℕ), (∀ a, (k a).queryCap ≤ d) →
      (P k).queryCap ≤ c + d ∧
      ∀ x b, (P k).outputMass x startState b =
        ∑ a, L x a * (k a).outputMass x startState b

/-- Ledger: def-Q. An adaptive program with at most `c` queries on every branch, with
classical result law `L x`, on any sufficiently large workspace. -/
def Runs (c : ℕ) [Fintype α] (L : BitInput ι → α → ℝ) : Prop :=
  ∃ w₀ : ℕ, ∀ w, w₀ ≤ w → RunsW w c L

namespace Runs

variable [Fintype α] [Fintype β] {c d : ℕ} {L L' : BitInput ι → α → ℝ}

theorem congr (h : Runs c L) (e : ∀ x a, L' x a = L x a) : Runs c L' := by
  have : L' = L := funext fun x => funext (e x)
  exact this ▸ h

theorem mono (h : Runs c L) (hc : c ≤ d) : Runs d L := by
  obtain ⟨w₀, h⟩ := h
  refine ⟨w₀, fun w hw => ?_⟩
  obtain ⟨P, hP⟩ := h w hw
  exact ⟨P, fun k e hk => ⟨(hP k e hk).1.trans (by omega), (hP k e hk).2⟩⟩

theorem pure (a : α) : Runs (ι := ι) 0 fun _ b => pt a b :=
  ⟨0, fun w _ => ⟨fun k => k a, fun k d hk =>
    ⟨by simpa using hk a, fun x b =>
      (sum_pt_mul (fun a' => (k a').outputMass x startState b) a).symm⟩⟩⟩

/-- Ledger: def-Q. Classical sequential composition. -/
theorem bind {c₁ c₂ : ℕ} {L₁ : BitInput ι → α → ℝ} {K : α → BitInput ι → β → ℝ}
    (h₁ : Runs c₁ L₁) (h₂ : ∀ a, Runs c₂ (K a)) :
    Runs (c₁ + c₂) fun x b => ∑ a, L₁ x a * K a x b := by
  obtain ⟨w₁, h₁⟩ := h₁
  choose w₂ h₂ using h₂
  refine ⟨max w₁ (Finset.univ.sup w₂), fun w hw => ?_⟩
  obtain ⟨P₁, hP₁⟩ := h₁ w (le_trans (le_max_left _ _) hw)
  choose P₂ hP₂ using fun a =>
    h₂ a w (le_trans (Finset.le_sup (Finset.mem_univ a)) (le_trans (le_max_right _ _) hw))
  refine ⟨fun k => P₁ fun a => P₂ a k, fun k d hk => ?_⟩
  have hcap : ∀ a, (P₂ a k).queryCap ≤ c₂ + d := fun a => (hP₂ a k d hk).1
  refine ⟨((hP₁ _ _ hcap).1).trans (by omega), fun x b => ?_⟩
  rw [(hP₁ _ _ hcap).2]
  simp only [(hP₂ _ k d hk).2, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- Ledger: def-Q. Bounded error on a promise, from a law favouring the right answer.
The query cap holds on every input. -/
theorem toQLePartial {c : ℕ} {L : BitInput ι → Bool → ℝ} (h : Runs c L) (f : PartialBool ι)
    (hL : ∀ x b, f x = some b → (2 / 3 : ℝ) ≤ L x b) : QLe f c := by
  obtain ⟨w₀, h⟩ := h
  obtain ⟨P, hP⟩ := h w₀ le_rfl
  obtain ⟨hcap, hmass⟩ := hP (fun a => .output a) 0 (by simp [AdaptiveProgram.queryCap])
  refine .inr ⟨w₀, startState, P fun a => .output a, norm_startState, by simpa using hcap,
    fun x b hb => ?_⟩
  rw [hmass]
  have hn : ‖(startState : State ι w₀)‖ ^ 2 = 1 := by rw [norm_startState]; norm_num
  have h2 := hL x b hb
  cases b <;> simpa [AdaptiveProgram.outputMass, hn] using h2

/-- Ledger: def-Q. Bounded error for a total function. -/
theorem toQLe {c : ℕ} {L : BitInput ι → Bool → ℝ} (h : Runs c L) (f : TotalBool ι)
    (hL : ∀ x, (2 / 3 : ℝ) ≤ L x (f x)) : QLe (totalise f) c :=
  h.toQLePartial _ fun x b hb => by
    obtain rfl : f x = b := Option.some.inj hb
    exact hL x

end Runs

/-- Ledger: claim-coherent-access. A sampler compiles to a program measuring its label,
at two bit queries per read. -/
theorem Samples.runs [Fintype α] {n : ℕ} {L : BitInput ι → α → ℝ} (h : Samples n L) :
    Runs (2 * n) L := by
  classical
  obtain ⟨Z, _, o, out, F, hF, hL⟩ := h
  refine ⟨Fintype.card Z, fun w hw => ?_⟩
  have hcard : Fintype.card Z ≤ Fintype.card (Fin (w + 1)) := by simp; omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  obtain ⟨P, hP⟩ := compile_circ e hF
  let g : AdaptiveProgram ι w → AdaptiveProgram ι w :=
    fun n => .unitary (swapGate (default, false, 0) (clPoint e o)) n
  refine ⟨fun k => g (P (measureAll e (fun z => k (out z)) Finset.univ.toList)),
    fun k d hk => ⟨?_, fun x b => ?_⟩⟩
  · have h1 := (hP (measureAll e (fun z => k (out z)) Finset.univ.toList)).1
    have h2 := queryCap_measureAll e (fun z => k (out z)) (fun z => hk (out z)) Finset.univ.toList
    simp only [g, AdaptiveProgram.queryCap]
    omega
  · simp only [g, AdaptiveProgram.outputMass]
    have hs : swapGate (ι := ι) (w := w) (default, false, 0) (clPoint e o) startState =
        clEmb e (rket o) := by
      rw [clEmb_rket]
      exact swapGate_ket _ _
    rw [hs, (hP _).2, outputMass_measureAll e _ x b _ (Finset.nodup_toList _) _ ?_]
    · simp only [clEmb_apply_cl, hL, lawOf, Finset.sum_mul]
      rw [Finset.sum_map_toList, Finset.sum_comm]
      · refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_eq_single (out z)]
        · simp
        · intro a _ ha
          simp [Ne.symm ha]
        · simp
    · intro p hp
      exact clEmb_apply_of_ne e _ p fun z => hp z (Finset.mem_toList.2 (Finset.mem_univ z))

end QuarticQuery.Upper
