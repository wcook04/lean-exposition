module

public import QuarticQuery.Upper.Compile
public import QuarticQuery.Forrelation.Repetition

/-!
# Lemma 2.1(ii) as a sampler

The Forrelation test on any `k` locations of the input: prepare `u`, run the product of
equation (3), and label the outcome by whether the state returned to `u`. The label is
true with probability `Φ²`. Its repetition is a product of independent copies in
coherent superposition, and the threshold is a function of the retained labels.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace QuarticQuery.Upper

open QuarticQuery.Forrelation Matrix

/-! ## Repetition -/

section Count

variable {ι : Type}

theorem binomWeight_succ_zero (n : ℕ) (p : ℝ) :
    binomWeight (n + 1) p 0 = (1 - p) * binomWeight n p 0 := by
  simp [binomWeight, pow_succ]
  ring

theorem binomWeight_succ_succ (n j : ℕ) (p : ℝ) :
    binomWeight (n + 1) p (j + 1) =
      p * binomWeight n p j + (1 - p) * binomWeight n p (j + 1) := by
  rcases Nat.lt_or_ge n (j + 1) with h | h
  · have h0 : n.choose (j + 1) = 0 := Nat.choose_eq_zero_of_lt h
    by_cases hj : n = j
    · subst hj
      simp [binomWeight]
      ring
    · have h1 : (n + 1).choose (j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have h2 : n.choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [binomWeight, h0, h1, h2]
  · obtain ⟨d, rfl⟩ : ∃ d, n = j + 1 + d := ⟨n - (j + 1), by omega⟩
    have e1 : j + 1 + d + 1 - (j + 1) = d + 1 := by omega
    have e2 : j + 1 + d - j = d + 1 := by omega
    have e3 : j + 1 + d - (j + 1) = d := by omega
    simp only [binomWeight, e1, e2, e3, Nat.choose_succ_succ' (j + 1 + d) j]
    push_cast
    ring

/-- Ledger: lem-2.1.ii. `n` independent coherent copies of a Bernoulli sampler: the
number of successes is binomial. -/
theorem Samples.count {c : ℕ} {p : BitInput ι → ℝ} (h : Samples c fun x b => bern (p x) b)
    (n : ℕ) : Samples (n * c) fun x (j : Fin (n + 1)) => binomWeight n (p x) j := by
  induction n with
  | zero =>
    refine (Samples.pure (0 : Fin 1)).cast (by omega) |>.congr fun x j => ?_
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [binomWeight, pt_self]
  | succ n ih =>
    have hb := ih.bind (K := fun (j : Fin (n + 1)) x g =>
      ∑ b, bern (p x) b * pt (if b then j.succ else j.castSucc) g)
      fun j => h.map fun b => if b then j.succ else j.castSucc
    refine (hb.cast (by ring)).congr fun x g => ?_
    simp only [Fintype.sum_bool, bern, ite_true, ite_false, Bool.false_eq_true]
    simp only [mul_add, Finset.sum_add_distrib]
    have hA : ∑ j : Fin (n + 1), binomWeight n (p x) j * ((1 - p x) * pt j.castSucc g) =
        (1 - p x) * binomWeight n (p x) g := by
      induction g using Fin.lastCases with
      | last =>
        have : binomWeight n (p x) (Fin.last (n + 1) : Fin (n + 2)) = 0 := by
          simp [binomWeight, Nat.choose_succ_self]
        rw [this, mul_zero]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [pt_of_ne (Fin.castSucc_lt_last j).ne, mul_zero, mul_zero]
      | cast g =>
        have : ∀ j : Fin (n + 1), pt j.castSucc g.castSucc = pt j g := fun j => by
          by_cases hj : j = g
          · subst hj; simp [pt_self]
          · rw [pt_of_ne hj, pt_of_ne (by simpa using hj)]
        simp only [this, Fin.val_castSucc]
        rw [Finset.sum_congr rfl fun (j : Fin (n + 1)) _ => (by ring :
          binomWeight n (p x) j * ((1 - p x) * pt j g) =
            (1 - p x) * binomWeight n (p x) j * pt j g),
          sum_mul_pt (fun j : Fin (n + 1) => (1 - p x) * binomWeight n (p x) j) g]
    have hB : ∑ j : Fin (n + 1), binomWeight n (p x) j * (p x * pt j.succ g) =
        if (g : ℕ) = 0 then 0 else p x * binomWeight n (p x) ((g : ℕ) - 1) := by
      induction g using Fin.cases with
      | zero =>
        simp only [Fin.val_zero, ite_true]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [pt_of_ne (Fin.succ_ne_zero j), mul_zero, mul_zero]
      | succ g =>
        have : ∀ j : Fin (n + 1), pt j.succ g.succ = pt j g := fun j => by
          by_cases hj : j = g
          · subst hj; simp [pt_self]
          · rw [pt_of_ne hj, pt_of_ne (by simpa using hj)]
        simp only [this, Fin.val_succ, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
        rw [Finset.sum_congr rfl fun (j : Fin (n + 1)) _ => (by ring :
          binomWeight n (p x) j * (p x * pt j g) = p x * binomWeight n (p x) j * pt j g),
          sum_mul_pt (fun j : Fin (n + 1) => p x * binomWeight n (p x) j) g]
    rw [hA, hB]
    obtain ⟨v, hv⟩ : ∃ v, v = (g : ℕ) := ⟨_, rfl⟩
    rw [← hv]
    cases v with
    | zero => rw [binomWeight_succ_zero]; simp
    | succ v =>
      rw [binomWeight_succ_succ]
      simp

/-- Ledger: lem-2.1.ii. Thresholding the retained count: at least `s` successes. -/
theorem Samples.threshold {c : ℕ} {p : BitInput ι → ℝ} (h : Samples c fun x b => bern (p x) b)
    (n : ℕ) (s : ℝ) : Samples (n * c) fun x b => bern (binomTail n (p x) s) b := by
  classical
  refine ((h.count n).map fun j : Fin (n + 1) => decide (s ≤ ((j : ℕ) : ℝ))).congr fun x b => ?_
  have hT : binomTail n (p x) s =
      ∑ j : Fin (n + 1), if s ≤ ((j : ℕ) : ℝ) then binomWeight n (p x) j else 0 := by
    rw [binomTail, Finset.sum_filter]
    exact (Fin.sum_univ_eq_sum_range
      (fun j : ℕ => if s ≤ (j : ℝ) then binomWeight n (p x) j else 0) (n + 1)).symm
  have hS : ∑ j : Fin (n + 1), binomWeight n (p x) j = 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => binomWeight n (p x) j) (n + 1)]
    exact sum_binomWeight n (p x)
  have hpt : ∀ (j : Fin (n + 1)) (b : Bool), pt (decide (s ≤ ((j : ℕ) : ℝ))) b =
      if (b = true) ↔ s ≤ ((j : ℕ) : ℝ) then 1 else 0 := by
    intro j b
    by_cases hj : s ≤ ((j : ℕ) : ℝ) <;> cases b <;> simp [hj, pt_self, pt_of_ne]
  simp only [hpt]
  cases b with
  | true =>
    simp only [bern, ite_true, hT, true_iff]
    exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
  | false =>
    simp only [bern, Bool.false_eq_true, ite_false, hT, false_iff]
    have e : ∀ j : Fin (n + 1), binomWeight n (p x) j * (if ¬ s ≤ ((j : ℕ) : ℝ) then 1 else 0) =
        binomWeight n (p x) j - (if s ≤ ((j : ℕ) : ℝ) then binomWeight n (p x) j else 0) := by
      intro j
      split_ifs <;> simp_all
    rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_sub_distrib, hS]

end Count

/-! ## Products -/

/-- Ledger: lem-2.1.ii. Independent samplers, one per coordinate: the product law on
functions. -/
theorem Samples.pi {ι β : Type} [Fintype β] {n : ℕ} :
    ∀ {r : ℕ} {L : Fin r → BitInput ι → β → ℝ}, (∀ h, Samples n (L h)) →
      Samples (r * n) fun x (s : Fin r → β) => ∏ h, L h x (s h) := by
  intro r
  induction r with
  | zero =>
    intro L _
    refine (Samples.pure (Fin.elim0 : Fin 0 → β)).cast (by omega) |>.congr fun x s => ?_
    obtain rfl : s = Fin.elim0 := Subsingleton.elim _ _
    simp [pt_self]
  | succ r ih =>
    intro L hL
    have htail := ih (L := fun h => L h.succ) fun h => hL h.succ
    have hb := htail.bind (K := fun (tl : Fin r → β) x s =>
      ∑ b, L 0 x b * pt (Fin.cons b tl : Fin (r + 1) → β) s)
      fun tl => (hL 0).map fun b => (Fin.cons b tl : Fin (r + 1) → β)
    refine (hb.cast (by ring)).congr fun x s => ?_
    have hsplit : ∀ (b : β) (tl : Fin r → β), pt (Fin.cons b tl : Fin (r + 1) → β) s =
        pt b (s 0) * pt tl (fun h => s h.succ) := by
      intro b tl
      by_cases hb : b = s 0
      · by_cases htl : tl = fun h => s h.succ
        · have : (Fin.cons b tl : Fin (r + 1) → β) = s := by
            subst htl hb
            exact Fin.cons_self_tail s
          rw [this, hb, htl, pt_self, pt_self, pt_self, one_mul]
        · have : (Fin.cons b tl : Fin (r + 1) → β) ≠ s := fun e =>
            htl (funext fun h => by rw [← e]; simp)
          rw [pt_of_ne this, pt_of_ne htl, mul_zero]
      · have : (Fin.cons b tl : Fin (r + 1) → β) ≠ s := fun e =>
          hb (by rw [← e]; simp)
        rw [pt_of_ne this, pt_of_ne hb, zero_mul]
    simp only [hsplit]
    rw [Fin.prod_univ_succ]
    have hin : ∀ tl : Fin r → β, ∑ b, L 0 x b * (pt b (s 0) * pt tl fun h => s h.succ) =
        L 0 x (s 0) * pt tl fun h => s h.succ := by
      intro tl
      rw [Finset.sum_congr rfl fun b _ => (by ring :
        L 0 x b * (pt b (s 0) * pt tl fun h => s h.succ) =
          (L 0 x b * pt tl fun h => s h.succ) * pt b (s 0)),
        sum_mul_pt (fun b => L 0 x b * pt tl fun h => s h.succ) (s 0)]
    simp only [hin]
    rw [Finset.sum_congr rfl fun tl _ => (by ring :
      (∏ h, L h.succ x (tl h)) * (L 0 x (s 0) * pt tl fun h => s h.succ) =
        (L 0 x (s 0) * ∏ h, L h.succ x (tl h)) * pt tl fun h => s h.succ),
      sum_mul_pt (fun tl : Fin r → β => L 0 x (s 0) * ∏ h, L h.succ x (tl h))]

/-- A product of `r` factors at least `1 - η` is at least `1 - r η`. -/
theorem one_sub_le_prod {r : ℕ} {f : Fin r → ℝ} {η : ℝ} (h1 : η ≤ 1)
    (hf : ∀ h, 1 - η ≤ f h) : 1 - (r : ℝ) * η ≤ ∏ h, f h := by
  have hp : ∏ _h : Fin r, (1 - η) ≤ ∏ h, f h :=
    Finset.prod_le_prod₀ (fun _ _ => by linarith) fun h _ => hf h
  have hb := one_add_mul_le_pow (a := -η) (by linarith) r
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hp
  have e : (1 : ℝ) + -η = 1 - η := by ring
  rw [e] at hb
  nlinarith

/-! ## The gates -/

section Gates

variable (t : ℕ)

/-- A real vector as amplitudes. -/
noncomputable def cplx {n : Type} [Fintype n] (v : n → ℝ) : Reg n :=
  WithLp.toLp 2 fun i => ((v i : ℝ) : ℂ)

/-- The columns of `H` are orthonormal. -/
theorem orthonormal_columns :
    Orthonormal ℂ fun j : Fin (mValue t) => cplx fun i => H t i j := by
  rw [orthonormal_iff_ite]
  intro j j'
  have h := congrFun (congrFun (H_mul_H t) j) j'
  rw [Matrix.mul_apply] at h
  have hsym : ∀ i, H t j i = H t i j := fun i => by
    have := congrFun (congrFun (H_transpose t) i) j
    simpa [Matrix.transpose_apply] using this
  simp only [hsym] at h
  simp only [PiLp.inner_apply, cplx, RCLike.inner_apply, Complex.conj_ofReal]
  rw [show (if j = j' then (1 : ℂ) else 0) = (((1 : Matrix _ _ ℝ) j j' : ℝ) : ℂ) by
    by_cases hj : j = j' <;> simp [hj, Matrix.one_apply]]
  rw [← h]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Ledger: lem-2.1.ii. `H` as a gate. -/
noncomputable def hGate : Reg (Fin (mValue t)) ≃ₗᵢ[ℂ] Reg (Fin (mValue t)) :=
  (embOrth _ (orthonormal_columns t)).toLinearIsometryEquiv rfl

theorem hGate_cplx (v : Fin (mValue t) → ℝ) : hGate t (cplx v) = cplx (H t *ᵥ v) := by
  change ∑ j, (cplx v).ofLp j • (cplx fun i => H t i j) = _
  ext i
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, cplx, mulVec,
    dotProduct]
  push_cast
  exact Finset.sum_congr rfl fun j _ => by ring

theorem rket_zero_eq (h0 : 0 < mValue t) :
    (rket (⟨0, h0⟩ : Fin (mValue t))) = cplx (Pi.single ⟨0, h0⟩ 1) := by
  classical
  ext i
  by_cases h : i = ⟨0, h0⟩
  · subst h
    simp [rket_apply, cplx]
  · simp [rket_apply, cplx, h]

end Gates

section Forr

variable {ι : Type} {k t : ℕ}

/-- `D_{z_h}` by one read: the phase of the bit at `loc (h, i)`. -/
def phaseRead (loc : ForrelationCoord k t → ι) (h : Fin k) : ReadSpec ι (Fin (mValue t)) where
  addr i := loc (h, i)
  perm i := i
  sign _ := true
  perm_perm _ := rfl
  addr_perm _ := rfl
  sign_perm _ := rfl

theorem phaseRead_cplx (loc : ForrelationCoord k t → ι) (h : Fin k) (x : BitInput ι)
    (v : Fin (mValue t) → ℝ) :
    (phaseRead loc h).op x (cplx v) =
      cplx (signDiag (fun c => x (loc c)) h *ᵥ v) := by
  ext i
  rw [ReadSpec.op_apply]
  simp only [cplx, signDiag, mulVec_diagonal, phaseRead, ReadSpec.coef, ReadSpec.dest, bitSign]
  by_cases hx : x (loc (h, i)) = true <;> simp [hx]

/-- The circuit of `alternate` on a list of layers. -/
theorem exists_alternate (loc : ForrelationCoord k t → ι) (l : List (Fin k)) :
    ∃ G : BitInput ι → Reg (Fin (mValue t)) ≃ₗᵢ[ℂ] Reg (Fin (mValue t)),
      IsCirc l.length G ∧ ∀ x v, G x (cplx v) =
        cplx (alternate (H t) (l.map fun h => signDiag (fun c => x (loc c)) h) *ᵥ v) := by
  induction l with
  | nil =>
    refine ⟨fun _ => LinearIsometryEquiv.refl ℂ _, IsCirc.gate _, fun x v => ?_⟩
    simp [alternate]
  | cons h l ih =>
    cases l with
    | nil =>
      refine ⟨fun x => (phaseRead loc h).op x, IsCirc.read _, fun x v => ?_⟩
      rw [phaseRead_cplx]
      simp [alternate, tailProd]
    | cons h' l =>
      obtain ⟨G, hG, hv⟩ := ih
      refine ⟨fun x => (G x).trans ((hGate t).trans ((phaseRead loc h).op x)),
        ((hG.post (hGate t)).comp (IsCirc.read _)).cast (by simp), fun x v => ?_⟩
      simp only [LinearIsometryEquiv.trans_apply, hv, hGate_cplx, phaseRead_cplx, List.map_cons,
        mulVec_mulVec]
      congr 2
      simp [alternate, tailProd, mul_assoc]

variable [Nonempty ι]

/-- Ledger: lem-2.1.ii, claim-proj-prob. One Forrelation test on the input bits at `loc`:
`k` reads, and the label is true with probability `Φ²`. -/
theorem forr_samples (hk : 1 ≤ k) (loc : ForrelationCoord k t → ι) :
    Samples k fun (x : BitInput ι) b => bern (Phi k t (fun c => x (loc c)) ^ 2) b := by
  classical
  have h0 : 0 < mValue t := by simp [mValue]
  let o : Fin (mValue t) := ⟨0, h0⟩
  obtain ⟨G, hG, hv⟩ := exists_alternate loc (List.ofFn fun h : Fin k => h)
  have hHe : H t *ᵥ Pi.single o 1 = u t := by
    funext i
    simp only [mulVec_single_one, Matrix.col_apply, u, H, Matrix.smul_apply, smul_eq_mul, W,
      Matrix.map_apply, walshZ, Matrix.of_apply]
    have : walshSign t i o = 1 := by
      simp [walshSign, o]
    simp [this]
  let F : BitInput ι → Reg (Fin (mValue t)) ≃ₗᵢ[ℂ] Reg (Fin (mValue t)) :=
    fun x => (hGate t).trans ((G x).trans (hGate t))
  have hF : IsCirc k F :=
    (((IsCirc.gate (hGate t)).comp hG).post (hGate t)).cast (by simp)
  have hstate : ∀ x : BitInput ι, F x (rket o) = cplx (H t *ᵥ psi fun c => x (loc c)) := fun x => by
    simp only [F, LinearIsometryEquiv.trans_apply]
    rw [rket_zero_eq t h0, hGate_cplx, hHe, hv, hGate_cplx]
    congr 3
    simp [List.map_ofFn, Function.comp_def]
  have hamp : ∀ x : BitInput ι, (H t *ᵥ psi fun c => x (loc c)) o = Phi k t fun c => x (loc c) :=
      fun x => by
    rw [Phi_eq_matrix_product k t hk]
    change _ = u t ⬝ᵥ psi fun c => x (loc c)
    simp only [mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    have hs : walshSign t o j = 1 := by simp [walshSign, o]
    simp [H, W, walshZ, hs, u]
  let out : Fin (mValue t) → Bool := fun j => decide (j = o)
  have hlaw : ∀ x : BitInput ι, lawOf (F x (rket o)) out true = Phi k t (fun c => x (loc c)) ^ 2 := fun x => by
    simp only [lawOf, out, decide_eq_true_eq]
    rw [Finset.sum_ite_eq' ]
    simp only [Finset.mem_univ, ite_true, hstate, cplx, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      hamp]
  refine ⟨Fin (mValue t), inferInstance, o, out, F, hF, fun x b => ?_⟩
  cases b with
  | true => exact (by simpa [bern] using (hlaw x).symm)
  | false =>
    have hs := sum_lawOf (F x (rket o)) out
    rw [LinearIsometryEquiv.norm_map, norm_rket, Fintype.sum_bool, hlaw] at hs
    simp only [bern, Bool.false_eq_true, ite_false]
    linarith

/-- The probability that the threshold test reports `true`. -/
noncomputable def decodeProb (k t n : ℕ) (z : BitInput (ForrelationCoord k t)) : ℝ :=
  binomTail n (successProb z) (n * (delta k ^ 2 / 2))

/-- Ledger: lem-2.1.ii. Lemma 2.1(ii): the `n`-fold threshold test, coherently, on any
locations, with `n k` reads and every workspace retained. -/
theorem decode_samples (hk : 1 ≤ k) (loc : ForrelationCoord k t → ι) (n : ℕ) :
    Samples (n * k) fun (x : BitInput ι) b =>
      bern (decodeProb k t n fun c => x (loc c)) b := by
  have hs := forr_samples (t := t) hk loc
  have hs' : Samples k fun (x : BitInput ι) b =>
      bern (successProb fun c => x (loc c)) b :=
    hs.congr fun x b => by rw [successProb_eq k t hk]
  exact hs'.threshold n _

/-- Ledger: lem-2.1.ii. The error bound of Lemma 2.1(ii) on the promise. -/
theorem decodeProb_correct {k t n : ℕ} (hk : 1 ≤ k) {η : ℝ} (h0 : 0 < η)
    (hn : repetitions k η ≤ n) (z : BitInput (ForrelationCoord k t)) {b : Bool}
    (hz : P k t z = some b) : 1 - η ≤ bern (decodeProb k t n z) b := by
  obtain ⟨h1, h2⟩ := threshold_correct k t hk h0 hn z
  cases b with
  | true => simpa [bern, decodeProb] using h1 hz
  | false =>
    have := h2 hz
    simp only [bern, Bool.false_eq_true, ite_false, decodeProb]
    linarith

end Forr

/-- Ledger: lem-2.1.ii. Lemma 2.1(ii) for error `η`: at most `2 n k` bit queries on every
input, in or out of the promise, for any `n ≥ repetitions k η`. -/
theorem P_runs {k t : ℕ} (hk : 1 ≤ k) [Inhabited (ForrelationCoord k t)] {η : ℝ} (h0 : 0 < η)
    {n : ℕ} (hn : repetitions k η ≤ n) :
    ∃ L : BitInput (ForrelationCoord k t) → Bool → ℝ, Runs (2 * (n * k)) L ∧
      ∀ z b, P k t z = some b → 1 - η ≤ L z b :=
  ⟨fun z b => bern (decodeProb k t n z) b, (decode_samples hk id n).runs,
    fun z b hz => decodeProb_correct hk h0 hn z hz⟩

/-- Ledger: lem-2.1.ii. Lemma 2.1(ii) at error `1/3`: a budget independent of `t`. -/
theorem P_QLe {k : ℕ} (t : ℕ) (hk : 1 ≤ k) :
    QLe (P k t) (2 * (2 ^ (10 * k + 5) * k)) := by
  have hm : 0 < mValue t := by simp [mValue]
  letI : Inhabited (ForrelationCoord k t) := ⟨(⟨0, hk⟩, ⟨0, hm⟩)⟩
  refine (decode_samples hk (id : ForrelationCoord k t → _) (2 ^ (10 * k + 5))).runs.toQLePartial
    _ fun z b hz => ?_
  obtain ⟨h1, h2⟩ := threshold_correct_third k t hk z
  cases b with
  | true => simpa [bern, decodeProb] using h1 hz
  | false =>
    have := h2 hz
    simp only [bern, Bool.false_eq_true, ite_false, decodeProb]
    simp only [id] at this ⊢
    linarith

end QuarticQuery.Upper
