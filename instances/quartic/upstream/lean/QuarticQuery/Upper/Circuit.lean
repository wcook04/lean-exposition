module

public import QuarticQuery.Model.Quantum

/-!
# Coherent query circuits on a register of any finite type

`IsCirc n F` says the input-indexed unitary `F` on the amplitudes of a finite type
`Z` is a fixed sequence of input-independent gates around `n` reads. A read
(`ReadSpec`) maps `|z⟩` to `±|π z⟩` when the bit at `addr z` is one and fixes `|z⟩`
otherwise, where `π` is an involution preserving `addr` and the sign. Every read
is its own inverse, and it is block diagonal in any label it does not touch.

The closure laws are composition, inverse, relabelling, and `sigma`, the direct
sum over a classical label. `sigma` is the whole of coherent control: the oracle
acts the same way in every block, so a family of circuits with a common read
count is one circuit. `Compile.lean` charges two bit queries per read, by the
load, act, unload pattern of Section 2.2 of the preprint.
-/

@[expose] public section

namespace QuarticQuery.Upper

/-- Amplitudes on a finite register. -/
abbrev Reg (Z : Type) [Fintype Z] := EuclideanSpace ℂ Z

section Basic

variable {Z Y : Type} [Fintype Z] [Fintype Y]

open Classical in
/-- `|z⟩`. -/
noncomputable def rket (z : Z) : Reg Z := EuclideanSpace.single z 1

open Classical in
theorem rket_apply (z z' : Z) : (rket z : Reg Z).ofLp z' = if z' = z then 1 else 0 := by
  simp [rket]

theorem norm_rket (z : Z) : ‖(rket z : Reg Z)‖ = 1 := by
  classical
  simp [rket]

/-- The squared norm is the sum of squared moduli of amplitudes. -/
theorem reg_norm_sq (ψ : Reg Z) : ‖ψ‖ ^ 2 = ∑ z, ‖ψ.ofLp z‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq ψ

/-- A vector is the combination of kets with its amplitudes. -/
theorem reg_eq_sum (ψ : Reg Z) : ψ = ∑ z, ψ.ofLp z • rket z := by
  classical
  ext z'
  simp [rket_apply, Finset.sum_apply]

/-- Linear maps agreeing on kets agree. -/
theorem reg_map_ext {E : Type*} [AddCommGroup E] [Module ℂ E] (f g : Reg Z →ₗ[ℂ] E)
    (h : ∀ z, f (rket z) = g (rket z)) (ψ : Reg Z) : f ψ = g ψ := by
  rw [reg_eq_sum ψ]
  simp only [map_sum, map_smul, h]

/-- Relabelling a register along a bijection. -/
noncomputable def regCongr (e : Z ≃ Y) : Reg Z ≃ₗᵢ[ℂ] Reg Y :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

theorem regCongr_apply (e : Z ≃ Y) (ψ : Reg Z) (y : Y) :
    (regCongr e ψ).ofLp y = ψ.ofLp (e.symm y) := by
  simp [regCongr, LinearIsometryEquiv.piLpCongrLeft_apply]

theorem regCongr_symm_apply (e : Z ≃ Y) (ψ : Reg Y) (z : Z) :
    ((regCongr e).symm ψ).ofLp z = ψ.ofLp (e z) := by
  have : ψ = regCongr e ((regCongr e).symm ψ) := by simp
  conv_rhs => rw [this]
  rw [regCongr_apply]
  simp

theorem regCongr_rket (e : Z ≃ Y) (z : Z) : regCongr e (rket z) = rket (e z) := by
  classical
  ext y
  simp only [regCongr_apply, rket_apply, Equiv.symm_apply_eq]

end Basic

/-! ## Signed involutions -/

section Signed

variable {Z : Type} [Fintype Z]

/-- `ψ ↦ (z ↦ c z * ψ (p z))`, for `p` an involution with `c` constant on its orbits
and `c z * c z = 1`. -/
noncomputable def signedLin (p : Z → Z) (c : Z → ℂ) : Reg Z →ₗ[ℂ] Reg Z where
  toFun ψ := WithLp.toLp 2 fun z => c z * ψ.ofLp (p z)
  map_add' ψ φ := by
    ext z
    simp only [PiLp.add_apply]
    ring
  map_smul' a ψ := by
    ext z
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem signedLin_apply (p : Z → Z) (c : Z → ℂ) (ψ : Reg Z) (z : Z) :
    (signedLin p c ψ).ofLp z = c z * ψ.ofLp (p z) := rfl

/-- `signedLin` as a unitary. -/
noncomputable def signedOp (p : Z → Z) (c : Z → ℂ) (hp : ∀ z, p (p z) = z)
    (hc : ∀ z, c (p z) = c z) (hcc : ∀ z, c z * c z = 1) : Reg Z ≃ₗᵢ[ℂ] Reg Z where
  toLinearEquiv := LinearEquiv.ofInvolutive (signedLin p c) (by
    intro ψ
    ext z
    simp only [signedLin_apply, hp, hc]
    rw [← mul_assoc, hcc, one_mul])
  norm_map' ψ := by
    have hn : ∀ z, ‖c z‖ = 1 := fun z => by
      have h := congrArg norm (hcc z)
      rw [norm_mul, norm_one] at h
      have h0 := norm_nonneg (c z)
      nlinarith
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    change ‖signedLin p c ψ‖ ^ 2 = ‖ψ‖ ^ 2
    rw [reg_norm_sq, reg_norm_sq]
    simp only [signedLin_apply, norm_mul, hn, one_mul]
    exact Equiv.sum_comp (Function.Involutive.toPerm p hp) fun z => ‖ψ.ofLp z‖ ^ 2

theorem signedOp_apply (p : Z → Z) (c : Z → ℂ) (hp : ∀ z, p (p z) = z)
    (hc : ∀ z, c (p z) = c z) (hcc : ∀ z, c z * c z = 1) (ψ : Reg Z) (z : Z) :
    (signedOp p c hp hc hcc ψ).ofLp z = c z * ψ.ofLp (p z) := rfl

theorem signedOp_signedOp (p : Z → Z) (c : Z → ℂ) (hp : ∀ z, p (p z) = z)
    (hc : ∀ z, c (p z) = c z) (hcc : ∀ z, c z * c z = 1) (ψ : Reg Z) :
    signedOp p c hp hc hcc (signedOp p c hp hc hcc ψ) = ψ := by
  ext z
  simp only [signedOp_apply, hp, hc]
  rw [← mul_assoc, hcc, one_mul]

end Signed

/-! ## Reads -/

/-- Ledger: claim-coherent-access. One read: `|z⟩ ↦ ±|perm z⟩` if the input bit at
`addr z` is one, and `|z⟩ ↦ |z⟩` if it is zero. -/
structure ReadSpec (ι Z : Type) where
  addr : Z → ι
  perm : Z → Z
  sign : Z → Bool
  perm_perm : ∀ z, perm (perm z) = z
  addr_perm : ∀ z, addr (perm z) = addr z
  sign_perm : ∀ z, sign (perm z) = sign z

namespace ReadSpec

variable {ι Z Y : Type}

/-- Where a basis label goes on input `x`. -/
def dest (R : ReadSpec ι Z) (x : BitInput ι) (z : Z) : Z := if x (R.addr z) then R.perm z else z

/-- The sign picked up on input `x`. -/
def coef (R : ReadSpec ι Z) (x : BitInput ι) (z : Z) : ℂ :=
  if x (R.addr z) && R.sign z then -1 else 1

theorem addr_dest (R : ReadSpec ι Z) (x : BitInput ι) (z : Z) : R.addr (R.dest x z) = R.addr z := by
  unfold dest
  split_ifs
  · exact R.addr_perm z
  · rfl

theorem dest_dest (R : ReadSpec ι Z) (x : BitInput ι) (z : Z) : R.dest x (R.dest x z) = z := by
  cases h : x (R.addr z)
  · simp [dest, h]
  · simp [dest, h, R.addr_perm, R.perm_perm]

theorem coef_dest (R : ReadSpec ι Z) (x : BitInput ι) (z : Z) : R.coef x (R.dest x z) = R.coef x z := by
  cases h : x (R.addr z)
  · simp [dest, coef, h]
  · simp [dest, coef, h, R.addr_perm, R.sign_perm]

theorem coef_mul_self (R : ReadSpec ι Z) (x : BitInput ι) (z : Z) : R.coef x z * R.coef x z = 1 := by
  unfold coef
  split_ifs <;> norm_num

variable [Fintype Z] [Fintype Y]

/-- Ledger: claim-coherent-access. The unitary of one read. -/
noncomputable def op (R : ReadSpec ι Z) (x : BitInput ι) : Reg Z ≃ₗᵢ[ℂ] Reg Z :=
  signedOp (R.dest x) (R.coef x) (R.dest_dest x) (R.coef_dest x) (R.coef_mul_self x)

theorem op_apply (R : ReadSpec ι Z) (x : BitInput ι) (ψ : Reg Z) (z : Z) :
    (R.op x ψ).ofLp z = R.coef x z * ψ.ofLp (R.dest x z) := rfl

theorem op_op (R : ReadSpec ι Z) (x : BitInput ι) (ψ : Reg Z) : R.op x (R.op x ψ) = ψ :=
  signedOp_signedOp _ _ _ _ _ ψ

theorem op_symm (R : ReadSpec ι Z) (x : BitInput ι) : (R.op x).symm = R.op x := by
  ext1 ψ
  rw [LinearIsometryEquiv.symm_apply_eq, op_op]

theorem op_rket (R : ReadSpec ι Z) (x : BitInput ι) (z : Z) :
    R.op x (rket z) = R.coef x z • rket (R.dest x z) := by
  classical
  ext z'
  simp only [op_apply, rket_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases h : z' = R.dest x z
  · subst h
    simp [dest_dest, coef_dest]
  · have h' : R.dest x z' ≠ z := fun e => h (by rw [← e, dest_dest])
    simp [h, h']

/-- The read that does nothing. -/
def idle (i : ι) : ReadSpec ι Z where
  addr _ := i
  perm z := z
  sign _ := false
  perm_perm _ := rfl
  addr_perm _ := rfl
  sign_perm _ := rfl

theorem idle_op (i : ι) (x : BitInput ι) : (idle i : ReadSpec ι Z).op x = LinearIsometryEquiv.refl ℂ _ := by
  ext ψ z
  simp [op_apply, idle, coef, dest]

/-- Move a read along a bijection of labels. -/
def congr (e : Z ≃ Y) (R : ReadSpec ι Z) : ReadSpec ι Y where
  addr y := R.addr (e.symm y)
  perm y := e (R.perm (e.symm y))
  sign y := R.sign (e.symm y)
  perm_perm y := by simp [R.perm_perm]
  addr_perm y := by simp [R.addr_perm]
  sign_perm y := by simp [R.sign_perm]

theorem congr_op (e : Z ≃ Y) (R : ReadSpec ι Z) (x : BitInput ι) (ψ : Reg Y) :
    (R.congr e).op x ψ = regCongr e (R.op x ((regCongr e).symm ψ)) := by
  ext y
  rw [regCongr_apply, op_apply, op_apply, regCongr_symm_apply]
  by_cases h : x (R.addr (e.symm y))
  · simp [dest, coef, congr, h]
  · simp [dest, coef, congr, h]

end ReadSpec

/-! ## Direct sums -/

section Sigma

variable {Γ : Type} [Fintype Γ] {Zf : Γ → Type} [∀ c, Fintype (Zf c)]

/-- The block of `ψ` at the label `c`. -/
noncomputable def slice (c : Γ) : Reg (Σ c, Zf c) →ₗ[ℂ] Reg (Zf c) where
  toFun ψ := WithLp.toLp 2 fun z => ψ.ofLp ⟨c, z⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem slice_apply (c : Γ) (ψ : Reg (Σ c, Zf c)) (z : Zf c) :
    (slice c ψ).ofLp z = ψ.ofLp ⟨c, z⟩ := rfl

theorem norm_sq_eq_slice (ψ : Reg (Σ c, Zf c)) : ‖ψ‖ ^ 2 = ∑ c, ‖slice c ψ‖ ^ 2 := by
  rw [reg_norm_sq, Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun c _ => (reg_norm_sq (slice c ψ)).symm

/-- Assemble blocks. -/
noncomputable def sigmaLin (F : ∀ c, Reg (Zf c) →ₗ[ℂ] Reg (Zf c)) :
    Reg (Σ c, Zf c) →ₗ[ℂ] Reg (Σ c, Zf c) where
  toFun ψ := WithLp.toLp 2 fun p => (F p.1 (slice p.1 ψ)).ofLp p.2
  map_add' ψ φ := by
    ext p
    simp [map_add]
  map_smul' a ψ := by
    ext p
    simp [map_smul]

theorem slice_sigmaLin (F : ∀ c, Reg (Zf c) →ₗ[ℂ] Reg (Zf c)) (c : Γ) (ψ : Reg (Σ c, Zf c)) :
    slice c (sigmaLin F ψ) = F c (slice c ψ) := rfl

theorem sigma_ext {ψ φ : Reg (Σ c, Zf c)} (h : ∀ c, slice c ψ = slice c φ) : ψ = φ := by
  ext ⟨c, z⟩
  exact congrArg (fun v => v.ofLp z) (h c)

/-- Ledger: claim-coherent-access. The direct sum of unitaries over a label. -/
noncomputable def sigmaOp (F : ∀ c, Reg (Zf c) ≃ₗᵢ[ℂ] Reg (Zf c)) :
    Reg (Σ c, Zf c) ≃ₗᵢ[ℂ] Reg (Σ c, Zf c) where
  toLinearEquiv := LinearEquiv.ofLinearMap
    (sigmaLin fun c => (F c).toLinearEquiv.toLinearMap)
    (sigmaLin fun c => (F c).symm.toLinearEquiv.toLinearMap)
    (by
      ext1 ψ
      refine sigma_ext fun c => ?_
      simp [slice_sigmaLin])
    (by
      ext1 ψ
      refine sigma_ext fun c => ?_
      simp [slice_sigmaLin])
  norm_map' ψ := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    change ‖sigmaLin (fun c => (F c).toLinearEquiv.toLinearMap) ψ‖ ^ 2 = ‖ψ‖ ^ 2
    rw [norm_sq_eq_slice, norm_sq_eq_slice]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [slice_sigmaLin]
    exact congrArg (· ^ 2) ((F c).norm_map _)

theorem slice_sigmaOp (F : ∀ c, Reg (Zf c) ≃ₗᵢ[ℂ] Reg (Zf c)) (c : Γ) (ψ : Reg (Σ c, Zf c)) :
    slice c (sigmaOp F ψ) = F c (slice c ψ) := rfl

theorem sigmaOp_apply (F : ∀ c, Reg (Zf c) ≃ₗᵢ[ℂ] Reg (Zf c)) (ψ : Reg (Σ c, Zf c)) (c : Γ)
    (z : Zf c) : (sigmaOp F ψ).ofLp ⟨c, z⟩ = (F c (slice c ψ)).ofLp z := rfl

open Classical in
theorem slice_rket_same (c : Γ) (z : Zf c) :
    slice c (rket (⟨c, z⟩ : Σ c, Zf c)) = rket z := by
  ext z'
  simp [slice_apply, rket_apply]

open Classical in
theorem slice_rket_ne {c c' : Γ} (h : c ≠ c') (z : Zf c') :
    slice c (rket (⟨c', z⟩ : Σ c, Zf c)) = 0 := by
  ext z'
  simp [slice_apply, rket_apply, h]

/-- Blocks of reads on the blocks: one read. -/
def ReadSpec.sigma {ι : Type} (R : ∀ c, ReadSpec ι (Zf c)) : ReadSpec ι (Σ c, Zf c) where
  addr p := (R p.1).addr p.2
  perm p := ⟨p.1, (R p.1).perm p.2⟩
  sign p := (R p.1).sign p.2
  perm_perm p := by simp [ReadSpec.perm_perm]
  addr_perm p := by simp [ReadSpec.addr_perm]
  sign_perm p := by simp [ReadSpec.sign_perm]

theorem ReadSpec.sigma_op {ι : Type} (R : ∀ c, ReadSpec ι (Zf c)) (x : BitInput ι) :
    (ReadSpec.sigma R).op x = sigmaOp fun c => (R c).op x := by
  ext1 ψ
  refine sigma_ext fun c => ?_
  rw [slice_sigmaOp]
  ext z
  rw [slice_apply, ReadSpec.op_apply, ReadSpec.op_apply, slice_apply]
  by_cases h : x ((R c).addr z)
  · simp [ReadSpec.dest, ReadSpec.coef, ReadSpec.sigma, h]
  · simp [ReadSpec.dest, ReadSpec.coef, ReadSpec.sigma, h]

end Sigma

/-! ## Circuits -/

/-- Ledger: claim-coherent-access. `F` is a fixed alternation of gates and `n` reads.
The gates do not depend on the input. -/
inductive IsCirc {ι Z : Type} [Fintype Z] :
    ℕ → (BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z) → Prop
  | gate (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) : IsCirc 0 fun _ => U
  | step {n : ℕ} {F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z} (h : IsCirc n F) (R : ReadSpec ι Z)
      (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) : IsCirc (n + 1) fun x => (F x).trans ((R.op x).trans U)

namespace IsCirc

variable {ι Z Y : Type} [Fintype Z] [Fintype Y]

theorem of_eq {n : ℕ} {F G : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z} (h : IsCirc n F)
    (e : ∀ x ψ, F x ψ = G x ψ) : IsCirc n G := by
  have : F = G := funext fun x => LinearIsometryEquiv.ext (e x)
  exact this ▸ h

theorem cast {n m : ℕ} {F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z} (h : IsCirc n F) (e : n = m) :
    IsCirc m F := e ▸ h

theorem read (R : ReadSpec ι Z) : IsCirc 1 fun x => R.op x :=
  of_eq (step (gate (LinearIsometryEquiv.refl ℂ (Reg Z))) R (LinearIsometryEquiv.refl ℂ _))
    fun _ _ => rfl

/-- A final gate costs nothing. -/
theorem post {n : ℕ} {F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z} (hF : IsCirc n F)
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) : IsCirc n fun x => (F x).trans U := by
  induction hF with
  | gate V => exact gate _
  | step h R V _ => exact of_eq (step h R (V.trans U)) fun _ _ => rfl

/-- Ledger: claim-coherent-access. Composition adds reads. -/
theorem comp {n m : ℕ} {F G : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z} (hF : IsCirc n F)
    (hG : IsCirc m G) : IsCirc (n + m) fun x => (F x).trans (G x) := by
  induction hG with
  | gate U => exact post hF U
  | step h R U ih => exact of_eq (step ih R U) fun _ _ => rfl

/-- Ledger: claim-coherent-access. The inverse makes the same reads in reverse. -/
theorem symm {n : ℕ} {F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z} (hF : IsCirc n F) :
    IsCirc n fun x => (F x).symm := by
  induction hF with
  | gate U => exact gate _
  | @step n F h R U ih =>
    refine cast (of_eq (comp (comp (gate U.symm) (read R)) ih) fun x ψ => ?_) (by omega)
    change (F x).symm (R.op x (U.symm ψ)) = (F x).symm ((R.op x).symm (U.symm ψ))
    rw [ReadSpec.op_symm]

/-- Idling is a read too, so read counts may be padded. -/
theorem succ [Nonempty ι] {n : ℕ} {F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z} (hF : IsCirc n F) :
    IsCirc (n + 1) F :=
  of_eq (step hF (ReadSpec.idle (Classical.arbitrary ι)) (LinearIsometryEquiv.refl ℂ _))
    fun x ψ => by simp [ReadSpec.idle_op]

theorem mono [Nonempty ι] {n m : ℕ} {F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z} (hF : IsCirc n F)
    (h : n ≤ m) : IsCirc m F := by
  induction m, h using Nat.le_induction with
  | base => exact hF
  | succ m _ ih => exact succ ih

theorem zero_inv {F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z} (h : IsCirc 0 F) :
    ∃ U, F = fun _ => U := by
  cases h with
  | gate U => exact ⟨U, rfl⟩

theorem succ_inv {n : ℕ} {F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z} (h : IsCirc (n + 1) F) :
    ∃ (G : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z) (R : ReadSpec ι Z) (U : Reg Z ≃ₗᵢ[ℂ] Reg Z),
      IsCirc n G ∧ F = fun x => (G x).trans ((R.op x).trans U) := by
  cases h with
  | step h R U => exact ⟨_, R, U, h, rfl⟩

/-- Ledger: claim-coherent-access. A circuit relabels along a bijection. -/
theorem congr (e : Z ≃ Y) {n : ℕ} {F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z} (h : IsCirc n F) :
    IsCirc n fun x => (regCongr e).symm.trans ((F x).trans (regCongr e)) := by
  induction h with
  | gate U => exact gate _
  | step h R U ih =>
    refine of_eq (step ih (R.congr e) ((regCongr e).symm.trans (U.trans (regCongr e))))
      fun x ψ => ?_
    simp [ReadSpec.congr_op, LinearIsometryEquiv.trans_apply]

/-- Ledger: claim-coherent-access. Coherent control: circuits with a common read count
on the blocks of a label are one circuit. Reads of all blocks happen simultaneously. -/
theorem sigma {Γ : Type} [Fintype Γ] {Zf : Γ → Type} [∀ c, Fintype (Zf c)] :
    ∀ {n : ℕ} {F : ∀ c, BitInput ι → Reg (Zf c) ≃ₗᵢ[ℂ] Reg (Zf c)},
      (∀ c, IsCirc n (F c)) → IsCirc n fun x => sigmaOp fun c => F c x := by
  intro n
  induction n with
  | zero =>
    intro F h
    choose U hU using fun c => zero_inv (h c)
    obtain rfl : F = fun c _ => U c := funext hU
    exact gate (sigmaOp U)
  | succ n ih =>
    intro F h
    choose G R U hG hF using fun c => succ_inv (h c)
    obtain rfl : F = fun c x => (G c x).trans (((R c).op x).trans (U c)) := funext hF
    refine of_eq (step (ih hG) (ReadSpec.sigma R) (sigmaOp U)) fun x ψ => ?_
    refine sigma_ext fun c => ?_
    simp only [LinearIsometryEquiv.trans_apply, ReadSpec.sigma_op, slice_sigmaOp]

end IsCirc

/-! ## Gates exist -/

section Extend

variable {E D : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup D] [InnerProductSpace ℂ D]

/-- Any isometry from a subspace extends to a gate: in finite dimension, a gate is
free to do anything that preserves inner products on the states it will meet. -/
theorem exists_extend (A B : D →ₗᵢ[ℂ] E) : ∃ G : E →ₗᵢ[ℂ] E, ∀ y, G (A y) = B y := by
  let L : LinearMap.range A.toLinearMap →ₗᵢ[ℂ] E :=
    B.comp (A.equivRange (R := ℂ) (S := ℂ)).symm.toLinearIsometry
  refine ⟨L.extend, fun y => ?_⟩
  have hy : A y ∈ LinearMap.range A.toLinearMap := ⟨y, rfl⟩
  have h := LinearIsometry.extend_apply L ⟨A y, hy⟩
  refine h.trans ?_
  change B ((A.equivRange (R := ℂ) (S := ℂ)).symm ⟨A y, hy⟩) = B y
  congr 1
  rw [LinearIsometryEquiv.symm_apply_eq]
  rfl

/-- A unit vector can be carried to any unit vector. -/
theorem exists_unit_gate {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ U : E ≃ₗᵢ[ℂ] E, U u = v := by
  obtain ⟨G, hG⟩ := exists_extend (LinearIsometry.toSpanSingleton ℂ E hu)
    (LinearIsometry.toSpanSingleton ℂ E hv)
  refine ⟨G.toLinearIsometryEquiv rfl, ?_⟩
  simpa using hG 1

end Extend

end QuarticQuery.Upper
