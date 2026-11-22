module

public import QuarticQuery.Upper.Circuit

/-!
# Coherent samplers

`Samples n L` says a circuit of `n` reads prepares, from a fixed basis state, a
state whose computational-basis outcome, read through a fixed labelling, has law
`L x` on input `x`. All workspace is retained: nothing is ever measured, so a
sampler can be run backwards. Failures stay inside the state, as labels.

`Samples.bind` is the central fact. Sampling `b` from `L`, then running the family
`K b` on a fresh register under the control of the computational-basis label `b`,
is a sampler for the mixture. Different labels do not interfere, because the
second stage is block diagonal in the first register, so the classical law
composes as for a randomized algorithm. The families need a common read count only.
This is the sentence in Section 3.3 of the preprint: "different address outcomes are
orthogonal and do not interfere". It replaces all reversible bookkeeping, because
thresholds and comparisons are functions of the retained labels.
-/

@[expose] public section

namespace QuarticQuery.Upper

open Finset

section Law

variable {Z β : Type} [Fintype Z]

open Classical in
/-- The law of the label `out z` when `ψ` is measured. -/
noncomputable def lawOf (ψ : Reg Z) (out : Z → β) (b : β) : ℝ :=
  ∑ z, if out z = b then ‖ψ.ofLp z‖ ^ 2 else 0

theorem lawOf_nonneg (ψ : Reg Z) (out : Z → β) (b : β) : 0 ≤ lawOf ψ out b := by
  classical
  exact Finset.sum_nonneg fun z _ => by split_ifs <;> positivity

theorem sum_lawOf [Fintype β] (ψ : Reg Z) (out : Z → β) : ∑ b, lawOf ψ out b = ‖ψ‖ ^ 2 := by
  classical
  simp only [lawOf]
  rw [Finset.sum_comm, reg_norm_sq]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp

theorem lawOf_smul (a : ℂ) (ψ : Reg Z) (out : Z → β) (b : β) :
    lawOf (a • ψ) out b = ‖a‖ ^ 2 * lawOf ψ out b := by
  classical
  simp only [lawOf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs
  · simp [mul_pow]
  · simp

theorem lawOf_sigma {Γ : Type} [Fintype Γ] {Zf : Γ → Type} [∀ c, Fintype (Zf c)]
    (ψ : Reg (Σ c, Zf c)) (out : (Σ c, Zf c) → β) (b : β) :
    lawOf ψ out b = ∑ c, lawOf (slice c ψ) (fun z => out ⟨c, z⟩) b := by
  classical
  simp only [lawOf]
  rw [Fintype.sum_sigma]
  rfl

end Law

/-- The point mass at `a`, as a function. -/
noncomputable def pt {β : Type} (a b : β) : ℝ := by
  classical exact if a = b then 1 else 0

theorem pt_self {β : Type} (a : β) : pt a a = 1 := by
  simp [pt]

theorem pt_of_ne {β : Type} {a b : β} (h : a ≠ b) : pt a b = 0 := by
  simp [pt, h]

theorem pt_nonneg {β : Type} (a b : β) : 0 ≤ pt a b := by
  classical
  by_cases h : a = b
  · simp [pt, h]
  · simp [pt, h]

theorem pt_le_one {β : Type} (a b : β) : pt a b ≤ 1 := by
  classical
  by_cases h : a = b
  · simp [pt, h]
  · simp [pt, h]

theorem sum_mul_pt {β : Type} [Fintype β] (f : β → ℝ) (a : β) : ∑ b, f b * pt b a = f a := by
  classical
  rw [Finset.sum_eq_single a]
  · rw [pt_self, mul_one]
  · intro b _ hb
    rw [pt_of_ne hb, mul_zero]
  · simp

theorem sum_pt_mul {β : Type} [Fintype β] (f : β → ℝ) (a : β) : ∑ b, pt a b * f b = f a := by
  classical
  rw [Finset.sum_eq_single a]
  · rw [pt_self, one_mul]
  · intro b _ hb
    rw [pt_of_ne (Ne.symm hb), zero_mul]
  · simp

theorem sum_pt {β : Type} [Fintype β] (a : β) : ∑ b, pt a b = 1 := by
  have := sum_pt_mul (fun _ => (1 : ℝ)) a
  simpa using this

/-- A Bernoulli law on `Bool`. -/
def bern (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- Ledger: claim-coherent-access. A circuit of `n` reads whose measured label has law
`L x` on input `x`. -/
def Samples {ι β : Type} (n : ℕ) (L : BitInput ι → β → ℝ) : Prop :=
  ∃ (Z : Type) (_ : Fintype Z) (o : Z) (out : Z → β) (F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z),
    IsCirc n F ∧ ∀ x b, L x b = lawOf (F x (rket o)) out b

namespace Samples

variable {ι β γ : Type} {n m : ℕ} {L L' : BitInput ι → β → ℝ}

theorem congr (h : Samples n L) (e : ∀ x b, L' x b = L x b) : Samples n L' := by
  obtain ⟨Z, _, o, out, F, hF, hL⟩ := h
  exact ⟨Z, _, o, out, F, hF, fun x b => (e x b).trans (hL x b)⟩

theorem cast (h : Samples n L) (e : n = m) : Samples m L := e ▸ h

theorem mono [Nonempty ι] (h : Samples n L) (hn : n ≤ m) : Samples m L := by
  obtain ⟨Z, _, o, out, F, hF, hL⟩ := h
  exact ⟨Z, _, o, out, F, hF.mono hn, hL⟩

theorem nonneg (h : Samples n L) (x : BitInput ι) (b : β) : 0 ≤ L x b := by
  obtain ⟨Z, _, o, out, F, -, hL⟩ := h
  rw [hL]
  exact lawOf_nonneg _ _ _

/-- A sampler's law has total mass one. -/
theorem sum_eq_one [Fintype β] (h : Samples n L) (x : BitInput ι) : ∑ b, L x b = 1 := by
  obtain ⟨Z, _, o, out, F, -, hL⟩ := h
  simp only [hL]
  rw [sum_lawOf, LinearIsometryEquiv.norm_map, norm_rket]
  norm_num

theorem le_one [Fintype β] (h : Samples n L) (x : BitInput ι) (b : β) : L x b ≤ 1 := by
  rw [← h.sum_eq_one x]
  exact Finset.single_le_sum (f := L x) (fun c _ => h.nonneg x c) (Finset.mem_univ b)

/-- The constant label. -/
theorem pure (a : β) : Samples (ι := ι) 0 fun _ b => pt a b := by
  classical
  refine ⟨Unit, inferInstance, (), fun _ => a, fun _ => LinearIsometryEquiv.refl ℂ _,
    IsCirc.gate _, fun x b => ?_⟩
  by_cases h : a = b <;> simp [lawOf, pt, h, rket_apply]

/-- Any fixed law, prepared by a gate. -/
theorem gate [Fintype β] {p : β → ℝ} (h0 : ∀ b, 0 ≤ p b) (h1 : ∑ b, p b = 1) :
    Samples (ι := ι) 0 fun _ b => p b := by
  classical
  have hne : Nonempty β := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    simp at h1
  obtain ⟨o⟩ := hne
  let v : Reg β := WithLp.toLp 2 fun b => ((Real.sqrt (p b) : ℝ) : ℂ)
  have hv : ‖v‖ = 1 := by
    have : ‖v‖ ^ 2 = 1 := by
      rw [reg_norm_sq, ← h1]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [v, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact Real.sq_sqrt (h0 b)
    nlinarith [norm_nonneg v]
  obtain ⟨U, hU⟩ := exists_unit_gate (norm_rket o) hv
  refine ⟨β, inferInstance, o, id, fun _ => U, IsCirc.gate U, fun x b => ?_⟩
  simp only [hU, lawOf, id, v]
  rw [Finset.sum_ite_eq' ]
  simp only [Finset.mem_univ, ite_true, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact (Real.sq_sqrt (h0 b)).symm

/-- One input bit, read into a fresh qubit. -/
theorem query (i : ι) : Samples 1 fun (x : BitInput ι) b => pt (x i) b := by
  classical
  let R : ReadSpec ι Bool :=
    { addr := fun _ => i, perm := not, sign := fun _ => false, perm_perm := by simp,
      addr_perm := fun _ => rfl, sign_perm := fun _ => rfl }
  refine ⟨Bool, inferInstance, false, id, R.op, IsCirc.read R, fun x b => ?_⟩
  rw [ReadSpec.op_rket]
  have hc : R.coef x false = 1 := by simp [ReadSpec.coef, R]
  have hd : R.dest x false = x i := by
    cases h : x i <;> simp [ReadSpec.dest, R, h]
  rw [hc, hd, one_smul]
  by_cases h : x i = b
  · subst h
    simp [lawOf, pt, rket_apply]
  · simp [lawOf, pt, rket_apply, h, Ne.symm h]

end Samples

/-! ## Bind -/

section Left

variable {Z W : Type} [Fintype Z] [Fintype W]

/-- Swap the two tags of a non-dependent pair. -/
def sigmaSwap (Z W : Type) : (Σ _ : W, Z) ≃ (Σ _ : Z, W) :=
  (Equiv.sigmaEquivProd W Z).trans ((Equiv.prodComm W Z).trans (Equiv.sigmaEquivProd Z W).symm)

/-- `U` acting on the first component. -/
noncomputable def leftOp (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) : Reg (Σ _ : Z, W) ≃ₗᵢ[ℂ] Reg (Σ _ : Z, W) :=
  (regCongr (sigmaSwap Z W)).symm.trans
    ((sigmaOp fun _ : W => U).trans (regCongr (sigmaSwap Z W)))

theorem slice_leftOp_rket (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o z : Z) (w₀ : W) :
    slice z (leftOp U (rket (⟨o, w₀⟩ : Σ _ : Z, W))) = (U (rket o)).ofLp z • rket w₀ := by
  classical
  ext w
  have hs : (sigmaSwap Z W).symm ⟨z, w⟩ = ⟨w, z⟩ := rfl
  have hk : (regCongr (sigmaSwap Z W)).symm (rket (⟨o, w₀⟩ : Σ _ : Z, W)) =
      rket (⟨w₀, o⟩ : Σ _ : W, Z) := by
    rw [LinearIsometryEquiv.symm_apply_eq, regCongr_rket]
    rfl
  simp only [leftOp, LinearIsometryEquiv.trans_apply, hk]
  rw [slice_apply, regCongr_apply, hs, sigmaOp_apply]
  by_cases h : w = w₀
  · subst h
    rw [slice_rket_same]
    simp [rket_apply]
  · rw [slice_rket_ne h]
    simp [rket_apply, h]

theorem IsCirc.left {ι : Type} {n : ℕ} {F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z} (h : IsCirc n F) :
    IsCirc n fun x => (leftOp (F x) : Reg (Σ _ : Z, W) ≃ₗᵢ[ℂ] _) :=
  (IsCirc.sigma fun _ : W => h).congr (sigmaSwap Z W)

end Left

/-- Ledger: claim-coherent-access. Running a family under the control of a sampled
label composes the classical laws. The family's circuits may differ arbitrarily, on
different registers, provided they have a common read count. -/
theorem Samples.bind {ι β γ : Type} [Fintype β] {n₁ n₂ : ℕ} {L : BitInput ι → β → ℝ}
    {K : β → BitInput ι → γ → ℝ} (h₁ : Samples n₁ L) (h₂ : ∀ b, Samples n₂ (K b)) :
    Samples (n₁ + n₂) fun x c => ∑ b, L x b * K b x c := by
  classical
  obtain ⟨Z₁, _, o₁, out₁, F₁, hF₁, hL⟩ := h₁
  choose Zb instZ ob outb Fb hFb hK using h₂
  let _ := instZ
  let W := Σ b, Zb b
  let O : W := ⟨out₁ o₁, ob _⟩
  let T : BitInput ι → Reg W ≃ₗᵢ[ℂ] Reg W := fun x => sigmaOp fun b => Fb b x
  have hT : IsCirc n₂ T := IsCirc.sigma hFb
  let P : Z₁ → Reg W ≃ₗᵢ[ℂ] Reg W := fun z => regCongr (Equiv.swap O ⟨out₁ z, ob (out₁ z)⟩)
  let C : BitInput ι → Reg (Σ _ : Z₁, W) ≃ₗᵢ[ℂ] Reg (Σ _ : Z₁, W) :=
    fun x => sigmaOp fun z => (P z).trans (T x)
  have hC : IsCirc n₂ C :=
    IsCirc.sigma fun z => ((IsCirc.gate (P z)).comp hT).cast (by omega)
  let out : (Σ _ : Z₁, W) → γ := fun p => outb p.2.1 p.2.2
  refine ⟨Σ _ : Z₁, W, inferInstance, ⟨o₁, O⟩, out,
    fun x => (leftOp (F₁ x)).trans (C x), IsCirc.left hF₁ |>.comp hC, fun x c => ?_⟩
  -- the state after the second stage, block by block
  have hslice : ∀ z, slice z (C x (leftOp (F₁ x) (rket (⟨o₁, O⟩ : Σ _ : Z₁, W)))) =
      (F₁ x (rket o₁)).ofLp z • T x (rket (⟨out₁ z, ob (out₁ z)⟩ : W)) := by
    intro z
    simp only [C]
    rw [slice_sigmaOp, slice_leftOp_rket, map_smul]
    simp only [LinearIsometryEquiv.trans_apply, P, regCongr_rket, Equiv.swap_apply_left]
  have hblock : ∀ b, lawOf (T x (rket (⟨b, ob b⟩ : W))) (fun p => outb p.1 p.2) c = K b x c := by
    intro b
    rw [lawOf_sigma, hK, Finset.sum_eq_single b]
    · simp only [T]
      rw [slice_sigmaOp, slice_rket_same]
    · intro b' _ hb'
      simp only [T]
      rw [slice_sigmaOp, slice_rket_ne hb', map_zero]
      simp [lawOf]
    · simp
  change _ = lawOf (C x (leftOp (F₁ x) (rket (⟨o₁, O⟩ : Σ _ : Z₁, W)))) out c
  rw [lawOf_sigma]
  simp only [hslice, lawOf_smul, out, hblock, hL]
  simp only [lawOf, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_eq_single (out₁ z)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

namespace Samples

variable {ι β γ : Type} {n m : ℕ} {L : BitInput ι → β → ℝ}

/-- Relabel the outcome. -/
theorem map [Fintype β] (h : Samples n L) (f : β → γ) :
    Samples n fun x c => ∑ b, L x b * pt (f b) c :=
  (h.bind fun b => Samples.pure (f b)).cast (by omega)

/-- A decision tree, run coherently with its query answers retained. Ledger:
claim-coherent-access. -/
theorem tree [Nonempty ι] (T : QueryTree ι) :
    Samples T.depth fun (x : BitInput ι) b => pt (T.eval x) b := by
  induction T with
  | leaf a => exact Samples.pure a
  | query i l r ihl ihr =>
    have hl : Samples (max l.depth r.depth) _ := ihl.mono (le_max_left _ _)
    have hr : Samples (max l.depth r.depth) _ := ihr.mono (le_max_right _ _)
    have hb := (Samples.query i).bind
      (K := fun b x c => pt ((if b then r else l).eval x) c)
      (n₂ := max l.depth r.depth) fun b => by
        cases b
        · simpa using hl
        · simpa using hr
    refine hb.congr fun x b => ?_
    rw [sum_pt_mul (fun c : Bool => pt ((if c then r else l).eval x) b) (x i)]
    cases h : x i <;> simp [QueryTree.eval, h]

end Samples

end QuarticQuery.Upper
