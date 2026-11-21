import Mathlib
import Breakdown.FracCell.FiniteDefs
import Breakdown.CertCell.StatementDefs

open Matrix Breakdown.CellCert.Finite

noncomputable section

namespace Breakdown.CertCell.Certificate

def IsState {V A B : Type*} [Fintype A] [Fintype B] (Q : V → ℝ) (v₀ : V) (z₀ : V → A → ℝ)
    (L : Matrix A B ℝ) (Ψ : Matrix (A ⊕ B) (A ⊕ B) ℝ) : Prop :=
  z₀ v₀ = 0 ∧ ∀ (x : V) (u : B → ℝ), quadValue Ψ (Sum.elim (z₀ x + L *ᵥ u) u) ≤ Q x

def IsIndependentOf {A B : Type*} [Fintype A] [Fintype B] (Ψ : Matrix (A ⊕ B) (A ⊕ B) ℝ)
    (E : Finset A) : Prop :=
  ∀ x y : A ⊕ B → ℝ, (∀ i, i ∉ E → x (Sum.inl i) = y (Sum.inl i)) →
    (∀ j, x (Sum.inr j) = y (Sum.inr j)) → quadValue Ψ x = quadValue Ψ y

def StateTerminalTest : Prop :=
  ∀ (V A B : Type) [Fintype A] [Fintype B] (Q : V → ℝ) (v₀ : V) (z₀ : V → A → ℝ)
    (L : Matrix A B ℝ) (Ψ : Matrix (A ⊕ B) (A ⊕ B) ℝ) (E : Finset A)
    (P : Submodule ℝ (A ⊕ B → ℝ)),
    Q v₀ ≤ 0 → IsState Q v₀ z₀ L Ψ → IsIndependentOf Ψ E →
    Fintype.card A ≤ Module.finrank ℝ P + E.card → IsPositiveOn Ψ P → ∀ x, 0 ≤ Q x

namespace SignedTree

variable {A B : Type} [Fintype A] [Fintype B] (T : SignedTree A B)

def totalForm : Matrix (A ⊕ B) (A ⊕ B) ℝ :=
  haveI := T.leafFintype; ∑ l, T.leafForm l

def pivotGain (ν : T.Node) (x : A ⊕ B → ℝ) : ℝ :=
  ∑ j ∈ T.pivots ν, T.slack ν j * x j ^ 2

open Classical in
def columnLoss (ν : T.Node) (x : A ⊕ B → ℝ) : ℝ :=
  haveI := T.columnFintype
  ∑ c ∈ Finset.univ.filter (fun c => T.columnNode c = ν), (T.column c ⬝ᵥ x) ^ 2

open Classical in
def rootForm : Matrix (A ⊕ B) (A ⊕ B) ℝ :=
  haveI := T.nodeFintype; haveI := T.columnFintype
  T.front T.root + (∑ ν, diagonal (fun j => if j ∈ T.pivots ν then T.slack ν j else 0))
    - ∑ c, vecMulVec (T.column c) (T.column c)

end SignedTree

structure IsSignedTree {A B : Type} [Fintype A] [Fintype B] (T : SignedTree A B) : Prop where
  root_parent : T.parent T.root = none
  only_root : ∀ ν, T.parent ν = none → ν = T.root
  node_bound : ∀ ν (x : A ⊕ B → ℝ),
    quadValue (T.front ν) x + T.pivotGain ν x - T.columnLoss ν x ≤ quadValue (T.nodeInput ν) x

def SignedTreeLowerBound : Prop :=
  ∀ (A B : Type) [Fintype A] [Fintype B] (T : SignedTree A B), IsSignedTree T →
    ∀ x, quadValue T.rootForm x ≤ quadValue T.totalForm x

def PivotCountPositive : Prop :=
  ∀ (A B : Type) [Fintype A] [Fintype B] (T : SignedTree A B), PassesPivotCount T →
    ∃ P : Submodule ℝ (A ⊕ B → ℝ), Fintype.card A ≤ Module.finrank ℝ P ∧ IsPositiveOn T.rootForm P

def SignedCertificateTerminal : Prop :=
  ∀ (V A B : Type) [Fintype A] [Fintype B] (Q : V → ℝ) (v₀ : V) (z₀ : V → A → ℝ)
    (L : Matrix A B ℝ) (T : SignedTree A B), IsSignedTree T → PassesPivotCount T → Q v₀ ≤ 0 →
    IsState Q v₀ z₀ L T.totalForm → ∀ x, 0 ≤ Q x

def TreeCertificateIsSigned : Prop :=
  ∀ (a b : ℕ) (T : TreeCertificate a b), IsTreeCertificate T →
    ∃ S : SignedTree (Fin a) (Fin b), IsSignedTree S ∧
      S.totalForm = (haveI := T.cellFintype; ∑ c, T.cellForm c) + T.globalForm ∧
      ∃ (E : Finset (Fin a)) (P : Submodule ℝ (Fin a ⊕ Fin b → ℝ)), IsIndependentOf S.rootForm E ∧
        a ≤ Module.finrank ℝ P + E.card ∧ IsPositiveOn S.rootForm P

def SignedSlackBound : Prop :=
  ∀ (n p q : Type) [Fintype n] [DecidableEq n] [Fintype p] [Fintype q] (M S : Matrix n n ℝ)
    (pivot : Finset n) (δ w r : n → ℝ) (Fp : Matrix n p ℝ) (Fm : Matrix n q ℝ),
    Mᵀ = M → Sᵀ = S → (∀ j, 0 < w j) →
    (∀ i, w i * ∑ j, |slackRemainder M S pivot δ Fp Fm i j| / w j ≤ r i) →
    ∀ x : n → ℝ, quadValue (S - pivotDiagonal (Finset.univ \ pivot) r) x
        + ∑ j ∈ pivot, (δ j - r j) * x j ^ 2 - ∑ c, (∑ i, Fm i c * x i) ^ 2 ≤ quadValue M x

def complexFormValue {n : Type*} [Fintype n] (M : Matrix n n ℂ) (z : n → ℂ) : ℝ :=
  (star z ⬝ᵥ (M *ᵥ z)).re

def ComplexSignedSlackBound : Prop :=
  ∀ (n p q : Type) [Fintype n] [DecidableEq n] [Fintype p] [Fintype q] (M S : Matrix n n ℂ)
    (pivot : Finset n) (δ w r : n → ℝ) (Fp : Matrix n p ℂ) (Fm : Matrix n q ℂ),
    Mᴴ = M → Sᴴ = S → (∀ j, 0 < w j) →
    (∀ i, w i * ∑ j, ‖complexSlackRemainder M S pivot δ Fp Fm i j‖ / w j ≤ r i) →
    ∀ z : n → ℂ, complexFormValue (S - complexDiagonal (Finset.univ \ pivot) r) z
        + ∑ j ∈ pivot, (δ j - r j) * ‖z j‖ ^ 2 - ∑ c, ‖∑ i, star (Fm i c) * z i‖ ^ 2
        ≤ complexFormValue M z

def RealRestrictionValue : Prop :=
  ∀ (n m : Type) [Fintype n] [Fintype m] (E : Matrix n m ℂ) (M : Matrix n n ℂ) (y : m → ℝ),
    quadValue (realRestriction E M) y = complexFormValue M (E *ᵥ ofRealVec y)

def RealRestrictionAdd : Prop :=
  ∀ (n m : Type) [Fintype n] (E : Matrix n m ℂ) (M M' : Matrix n n ℂ),
    realRestriction E (M + M') = realRestriction E M + realRestriction E M'

def ComplexColumnSplit : Prop :=
  ∀ (n m q : Type) [Fintype n] [Fintype m] (E : Matrix n m ℂ) (F : Matrix n q ℂ) (t : ℝ) (y : m → ℝ)
    (c : q), 0 ≤ t →
    t * ‖∑ i, star (F i c) * (E *ᵥ ofRealVec y) i‖ ^ 2
      = (realColumns E t F (Sum.inl c) ⬝ᵥ y) ^ 2 + (realColumns E t F (Sum.inr c) ⬝ᵥ y) ^ 2

namespace CoordinateRealification

variable {n m : Type} (R : CoordinateRealification n m)

end CoordinateRealification

def CoordinateSlack : Prop :=
  ∀ (n m : Type) [Fintype n] [Fintype m] [DecidableEq m] (R : CoordinateRealification n m)
    (pivot : Finset n) (s : n → ℝ) (y : m → ℝ), IsCoordinateOn R pivot →
    ∑ j ∈ pivot, s j * ‖(R.matrix *ᵥ ofRealVec y) j‖ ^ 2
      = ∑ k ∈ R.pivotImage pivot, R.slackOn pivot s k * y k ^ 2

def ComplexNodeRealBound : Prop :=
  ∀ (n m p q : Type) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype p] [Fintype q]
    (R : CoordinateRealification n m) (t : ℝ) (M S : Matrix n n ℂ) (pivot : Finset n)
    (δ w r : n → ℝ) (Fp : Matrix n p ℂ) (Fm : Matrix n q ℂ),
    IsCoordinateOn R pivot → 0 ≤ t → Mᴴ = M → Sᴴ = S → (∀ j, 0 < w j) →
    (∀ i, w i * ∑ j, ‖complexSlackRemainder M S pivot δ Fp Fm i j‖ / w j ≤ r i) →
    ∀ y : m → ℝ,
      quadValue (t • realRestriction R.matrix (S - complexDiagonal (Finset.univ \ pivot) r)) y
        + ∑ k ∈ R.pivotImage pivot, t * R.slackOn pivot (fun j => δ j - r j) k * y k ^ 2
        - ∑ c : q ⊕ q, (realColumns R.matrix t Fm c ⬝ᵥ y) ^ 2
        ≤ quadValue (t • realRestriction R.matrix M) y

structure SignedInvolution (n : Type) where
  perm : Equiv.Perm n
  sign : n → ℝ

structure IsSignedInvolution {n : Type} (σ : SignedInvolution n) : Prop where
  perm_involutive : ∀ i, σ.perm (σ.perm i) = i
  sign_sq : ∀ i, σ.sign i ^ 2 = 1
  sign_perm : ∀ i, σ.sign (σ.perm i) = σ.sign i

namespace SignedInvolution

variable {n : Type} (σ : SignedInvolution n)

def conjVec (u : n → ℂ) : n → ℂ := fun i => (σ.sign i : ℂ) * star (u (σ.perm i))

def conjMatrix (M : Matrix n n ℂ) : Matrix n n ℂ := fun a b =>
  ((σ.sign (σ.perm a) * σ.sign (σ.perm b) : ℝ) : ℂ) * star (M (σ.perm a) (σ.perm b))

end SignedInvolution

def ConjugateFormValue : Prop :=
  ∀ (n : Type) [Fintype n] (σ : SignedInvolution n) (M : Matrix n n ℂ) (u : n → ℂ),
    IsSignedInvolution σ → complexFormValue M (σ.conjVec u) = complexFormValue (σ.conjMatrix M) u

def ConjugateHalfLowerBound : Prop :=
  ∀ (n : Type) [Fintype n] (σ : SignedInvolution n) (M : Matrix n n ℂ)
    (Φ Φ' : (n → ℂ) → ℝ), IsSignedInvolution σ → (∀ u, Φ' (σ.conjVec u) = Φ u) →
    (∀ u, complexFormValue M u ≤ Φ u) → ∀ u, complexFormValue (σ.conjMatrix M) u ≤ Φ' u

def ConjugateOnRealSubspace : Prop :=
  ∀ (n m : Type) [Fintype n] [Fintype m] (σ : SignedInvolution n) (E : Matrix n m ℂ)
    (M : Matrix n n ℂ), IsSignedInvolution σ →
    (∀ y : m → ℝ, σ.conjVec (E *ᵥ ofRealVec y) = E *ᵥ ofRealVec y) →
    ∀ y, quadValue (realRestriction E (σ.conjMatrix M)) y = quadValue (realRestriction E M) y

def StateLowerStep : Prop :=
  ∀ (V A B B' : Type) [Fintype A] [Fintype B] [Fintype B'] (Q : V → ℝ) (v₀ : V) (z₀ : V → A → ℝ)
    (L : Matrix A B ℝ) (Ψ : Matrix (A ⊕ B) (A ⊕ B) ℝ) (Ψ' : Matrix (A ⊕ (B ⊕ B')) (A ⊕ (B ⊕ B')) ℝ),
    IsState Q v₀ z₀ L Ψ →
    (∀ z u u', quadValue Ψ' (Sum.elim z (Sum.elim u u')) ≤ quadValue Ψ (Sum.elim z u)) →
    IsState Q v₀ z₀ (fromCols L 0) Ψ'

def StateChangeStep : Prop :=
  ∀ (V A A' B : Type) [Fintype A] [DecidableEq A] [Fintype A'] [Fintype B] (Q : V → ℝ) (v₀ : V)
    (z₀ : V → A → ℝ) (L : Matrix A B ℝ) (T : Matrix A A' ℝ) (T' : Matrix A B ℝ) (Ti : Matrix A' A ℝ)
    (Ψ : Matrix (A ⊕ B) (A ⊕ B) ℝ) (Ψ' : Matrix (A' ⊕ B) (A' ⊕ B) ℝ),
    IsState Q v₀ z₀ L Ψ → T * Ti = 1 →
    (∀ z u, quadValue Ψ' (Sum.elim z u) ≤ quadValue Ψ (Sum.elim (T *ᵥ z + T' *ᵥ u) u)) →
    IsState Q v₀ (fun x => Ti *ᵥ z₀ x) (Ti * (L - T')) Ψ'

def StateRestrictStep : Prop :=
  ∀ (V A B B' : Type) [Fintype A] [Fintype B] [Fintype B'] (Q : V → ℝ) (v₀ : V) (z₀ : V → A → ℝ)
    (L : Matrix A B ℝ) (E : Matrix B B' ℝ) (Ψ : Matrix (A ⊕ B) (A ⊕ B) ℝ)
    (Ψ' : Matrix (A ⊕ B') (A ⊕ B') ℝ),
    IsState Q v₀ z₀ L Ψ →
    (∀ z u, quadValue Ψ' (Sum.elim z u) ≤ quadValue Ψ (Sum.elim z (E *ᵥ u))) →
    IsState Q v₀ z₀ (L * E) Ψ'

def StateEliminateStep : Prop :=
  ∀ (V A₁ A₂ B : Type) [Fintype A₁] [Fintype A₂] [Fintype B] (Q : V → ℝ) (v₀ : V)
    (z₀ : V → A₁ ⊕ A₂ → ℝ) (L : Matrix (A₁ ⊕ A₂) B ℝ)
    (Ψ : Matrix ((A₁ ⊕ A₂) ⊕ B) ((A₁ ⊕ A₂) ⊕ B) ℝ) (Ψ' : Matrix (A₂ ⊕ B) (A₂ ⊕ B) ℝ),
    IsState Q v₀ z₀ L Ψ →
    (∀ z₁ z₂ u, quadValue Ψ' (Sum.elim z₂ u) ≤ quadValue Ψ (Sum.elim (Sum.elim z₁ z₂) u)) →
    IsState Q v₀ (fun x i => z₀ x (Sum.inr i)) (L.submatrix Sum.inr id) Ψ'

def StateNullFormStep : Prop :=
  ∀ (V A B R : Type) [Fintype A] [Fintype B] [Fintype R] (Q : V → ℝ) (v₀ : V) (z₀ : V → A → ℝ)
    (L : Matrix A B ℝ) (N : Matrix A A ℝ) (Z : Matrix R A ℝ) (Ψ : Matrix (A ⊕ B) (A ⊕ B) ℝ)
    (Ψ' : Matrix (A ⊕ (B ⊕ R)) (A ⊕ (B ⊕ R)) ℝ),
    IsState Q v₀ z₀ L Ψ → (∀ x u, quadValue N (z₀ x + L *ᵥ u) ≤ 0) →
    (∀ x u, Z *ᵥ (z₀ x + L *ᵥ u) = 0) →
    (∀ z u u', quadValue Ψ' (Sum.elim z (Sum.elim u u'))
      ≤ quadValue Ψ (Sum.elim z u) + quadValue N z + 2 * (u' ⬝ᵥ (Z *ᵥ z))) →
    IsState Q v₀ z₀ (fromCols L 0) Ψ'

def StateIdentityStep : Prop :=
  ∀ (V A A' B R : Type) [Fintype A] [Fintype A'] [Fintype B] [Fintype R] (Q : V → ℝ) (v₀ : V)
    (z₀ : V → A → ℝ) (L : Matrix A B ℝ) (C : Matrix A' A ℝ) (Z : Matrix R A ℝ)
    (Ψ : Matrix (A ⊕ B) (A ⊕ B) ℝ) (Ψ' : Matrix (A' ⊕ B) (A' ⊕ B) ℝ),
    IsState Q v₀ z₀ L Ψ → (∀ x u, Z *ᵥ (z₀ x + L *ᵥ u) = 0) →
    (∀ z u, Z *ᵥ z = 0 → quadValue Ψ' (Sum.elim (C *ᵥ z) u) ≤ quadValue Ψ (Sum.elim z u)) →
    IsState Q v₀ (fun x => C *ᵥ z₀ x) (C * L) Ψ'

def copyIndex {A G K : Type*} : A ⊕ (K × G) → A ⊕ G :=
  Sum.elim Sum.inl (fun p => Sum.inr p.2)

def StateUnshareStep : Prop :=
  ∀ (V A G K B X : Type) [Fintype A] [Fintype G] [Fintype K] [Fintype B] [Fintype X] (Q : V → ℝ)
    (v₀ : V) (z₀ : V → A ⊕ G → ℝ) (L : Matrix (A ⊕ G) B ℝ) (Ψ : Matrix ((A ⊕ G) ⊕ B) ((A ⊕ G) ⊕ B) ℝ)
    (Ψ' : Matrix ((A ⊕ (K × G)) ⊕ (B ⊕ X)) ((A ⊕ (K × G)) ⊕ (B ⊕ X)) ℝ),
    IsState Q v₀ z₀ L Ψ →
    (∀ z u χ, quadValue Ψ' (Sum.elim (z ∘ copyIndex) (Sum.elim u χ)) ≤ quadValue Ψ (Sum.elim z u)) →
    IsState Q v₀ (fun x => z₀ x ∘ copyIndex) (fromCols (L.submatrix copyIndex id) 0) Ψ'

def StateGaugeStep : Prop :=
  ∀ (V A₀ J B : Type) [Fintype A₀] [Fintype J] [Fintype B] [DecidableEq J] (Q : V → ℝ) (v₀ : V)
    (z₀ : V → A₀ ⊕ J → ℝ) (L : Matrix (A₀ ⊕ J) B ℝ) (Nm : Matrix (A₀ ⊕ J) J ℝ)
    (Ψ : Matrix ((A₀ ⊕ J) ⊕ B) ((A₀ ⊕ J) ⊕ B) ℝ) (Ψ' : Matrix (A₀ ⊕ B) (A₀ ⊕ B) ℝ),
    IsState Q v₀ z₀ L Ψ → Nm.submatrix Sum.inr id = 1 →
    (∀ z u w, quadValue Ψ (Sum.elim (z + Nm *ᵥ w) u) = quadValue Ψ (Sum.elim z u)) →
    (∀ z u, quadValue Ψ' (Sum.elim z u) ≤ quadValue Ψ (Sum.elim (Sum.elim z 0) u)) →
    IsState Q v₀ (fun x i => (z₀ x - Nm *ᵥ (fun j => z₀ x (Sum.inr j))) (Sum.inl i))
      ((L - Nm * L.submatrix Sum.inr id).submatrix Sum.inl id) Ψ'

def GaugeFromNullVectors : Prop :=
  ∀ (A₀ J C B : Type) [Fintype A₀] [Fintype J] [Fintype C] [Fintype B] [DecidableEq J]
    (Ψ : Matrix ((A₀ ⊕ J) ⊕ B) ((A₀ ⊕ J) ⊕ B) ℝ) (N : Matrix (A₀ ⊕ J) C ℝ) (Ki : Matrix C J ℝ),
    N.submatrix Sum.inr id * Ki = 1 →
    (∀ z u w, quadValue Ψ (Sum.elim (z + N *ᵥ w) u) = quadValue Ψ (Sum.elim z u)) →
    (N * Ki).submatrix Sum.inr id = 1 ∧
      ∀ z u w, quadValue Ψ (Sum.elim (z + (N * Ki) *ᵥ w) u) = quadValue Ψ (Sum.elim z u)

def RowDominantRightInverse : Prop :=
  ∀ (J : Type) [Fintype J] [DecidableEq J] (K : Matrix J J ℝ),
    (∀ k, ∑ j ∈ Finset.univ.erase k, |K k j| < |K k k|) → ∃ Ki : Matrix J J ℝ, K * Ki = 1

def TriangularRightInverse : Prop :=
  ∀ (J : Type) [Fintype J] [DecidableEq J] (K : Matrix J J ℝ) (rank : J → ℕ),
    (∀ k j, j ≠ k → rank k ≤ rank j → K k j = 0) → (∀ k, K k k ≠ 0) →
    ∃ Ki : Matrix J J ℝ, K * Ki = 1

def StateFreeCopyStep : Prop :=
  ∀ (V A B₁ B₂ : Type) [Fintype A] [Fintype B₁] [Fintype B₂] (Q : V → ℝ) (v₀ : V)
    (z₀ : V → A → ℝ) (L : Matrix A (B₁ ⊕ B₂) ℝ) (Ψ : Matrix (A ⊕ (B₁ ⊕ B₂)) (A ⊕ (B₁ ⊕ B₂)) ℝ)
    (Ψt : Matrix (A ⊕ ((B₁ ⊕ B₁) ⊕ B₂)) (A ⊕ ((B₁ ⊕ B₁) ⊕ B₂)) ℝ)
    (Ψ' : Matrix ((A ⊕ B₁) ⊕ ((B₁ ⊕ B₁) ⊕ B₂)) ((A ⊕ B₁) ⊕ ((B₁ ⊕ B₁) ⊕ B₂)) ℝ),
    IsState Q v₀ z₀ L Ψ →
    (∀ z a u, quadValue Ψ (Sum.elim z (Sum.elim a u))
      = quadValue Ψt (Sum.elim z (Sum.elim (Sum.elim a a) u))) →
    (∀ z χ a a' u, quadValue Ψ' (Sum.elim (Sum.elim z χ) (Sum.elim (Sum.elim a a') u))
      = quadValue Ψt (Sum.elim z (Sum.elim (Sum.elim a a') u)) + 2 * (χ ⬝ᵥ (a - a'))) →
    ∃ (z₀' : V → A ⊕ B₁ → ℝ) (L' : Matrix (A ⊕ B₁) ((B₁ ⊕ B₁) ⊕ B₂) ℝ),
      (∀ x i, z₀' x (Sum.inl i) = z₀ x i) ∧
      (∀ (a a' : B₁ → ℝ) (u : B₂ → ℝ) (i : A),
        (L' *ᵥ Sum.elim (Sum.elim a a') u) (Sum.inl i) = (L *ᵥ Sum.elim a u) i) ∧
      IsState Q v₀ z₀' L' Ψ'

namespace SignedTree

variable {A B : Type} [Fintype A] [Fintype B] (T : SignedTree A B)

end SignedTree

open Classical in
structure PassesRealNodeCondition {A B : Type} [Fintype A] [Fintype B] (T : SignedTree A B)
    (ν : T.Node) (D : RealNodeData A B) : Prop where
  input_eq : T.nodeInput ν = D.input
  input_symm : D.inputᵀ = D.input
  base_symm : D.baseᵀ = D.base
  weight_pos : ∀ j, 0 < D.weight j
  row_bound : ∀ i, D.weight i * ∑ j, |(haveI := D.posFintype; haveI := T.columnFintype;
    slackRemainder D.input D.base (T.pivots ν) D.pivotValue D.posColumns (T.nodeColumns ν)) i j|
      / D.weight j ≤ D.radius i
  front_eq : T.front ν = D.base - pivotDiagonal (Finset.univ \ T.pivots ν) D.radius
  slack_le : ∀ j ∈ T.pivots ν, T.slack ν j ≤ D.pivotValue j - D.radius j

open Classical in
structure PassesComplexNodeCondition {A B : Type} [Fintype A] [Fintype B] (T : SignedTree A B)
    (ν : T.Node) (D : ComplexNodeData A B) : Prop where
  coordinates : IsCoordinateOn D.coords D.pivot
  factor_nonneg : 0 ≤ D.factor
  input_self_adjoint : D.inputᴴ = D.input
  base_self_adjoint : D.baseᴴ = D.base
  weight_pos : ∀ j, 0 < D.weight j
  row_bound : ∀ i, D.weight i * (haveI := D.indexFintype; ∑ j,
    ‖(haveI := D.posFintype; haveI := D.negFintype;
      complexSlackRemainder D.input D.base D.pivot D.pivotValue D.posColumns D.negColumns) i j‖
      / D.weight j) ≤ D.radius i
  input_eq : T.nodeInput ν = (haveI := D.indexFintype; D.factor • realRestriction D.coords.matrix D.input)
  front_eq : T.front ν = (haveI := D.indexFintype;
    D.factor • realRestriction D.coords.matrix (D.base - complexDiagonal (Finset.univ \ D.pivot) D.radius))
  pivots_eq : T.pivots ν = D.coords.pivotImage D.pivot
  slack_le : ∀ k ∈ T.pivots ν,
    T.slack ν k ≤ D.factor * D.coords.slackOn D.pivot (fun j => D.pivotValue j - D.radius j) k
  columns : ∃ e : D.Neg ⊕ D.Neg → T.Column, Function.Injective e ∧ ∀ c,
    T.columnNode (e c) = ν ∧
      T.column (e c) = (haveI := D.indexFintype; realColumns D.coords.matrix D.factor D.negColumns c)

def PassesNodeCondition {A B : Type} [Fintype A] [Fintype B] (T : SignedTree A B) (ν : T.Node) : Prop :=
  (∃ D : RealNodeData A B, PassesRealNodeCondition T ν D) ∨
    ∃ D : ComplexNodeData A B, PassesComplexNodeCondition T ν D

structure SignedStateCertificate (V : Type) where
  Slaved : Type
  slavedFintype : Fintype Slaved
  Free : Type
  freeFintype : Fintype Free
  basePoint : V
  data : V → Slaved → ℝ
  freeMap : Matrix Slaved Free ℝ
  tree : SignedTree Slaved Free

structure IsSignedStateCertificate {V : Type} (Q : V → ℝ) (C : SignedStateCertificate V) :
    Prop where
  base_value : Q C.basePoint ≤ 0
  state : (haveI := C.slavedFintype; haveI := C.freeFintype;
    IsState Q C.basePoint C.data C.freeMap C.tree.totalForm)
  root_parent : C.tree.parent C.tree.root = none
  only_root : ∀ ν, C.tree.parent ν = none → ν = C.tree.root
  node_conditions : ∀ ν, (haveI := C.slavedFintype; haveI := C.freeFintype; PassesNodeCondition C.tree ν)
  pivot_count : (haveI := C.slavedFintype; haveI := C.freeFintype; PassesPivotCount C.tree)

def StateCertificateNonneg : Prop :=
  ∀ (V : Type) (Q : V → ℝ) (C : SignedStateCertificate V), IsSignedStateCertificate Q C →
    ∀ x, 0 ≤ Q x

structure CertificateLayerHolds : Prop where
  terminal_test : StateTerminalTest
  tree_lower : SignedTreeLowerBound
  pivot_count : PivotCountPositive
  certificate_terminal : SignedCertificateTerminal
  tree_is_signed : TreeCertificateIsSigned
  slack_real : SignedSlackBound
  slack_complex : ComplexSignedSlackBound
  real_restriction : RealRestrictionValue
  real_restriction_add : RealRestrictionAdd
  column_split : ComplexColumnSplit
  coordinate_slack : CoordinateSlack
  complex_node : ComplexNodeRealBound
  conjugate_value : ConjugateFormValue
  conjugate_lower : ConjugateHalfLowerBound
  conjugate_real : ConjugateOnRealSubspace
  step_lower : StateLowerStep
  step_change : StateChangeStep
  step_restrict : StateRestrictStep
  step_eliminate : StateEliminateStep
  step_null : StateNullFormStep
  step_identity : StateIdentityStep
  step_unshare : StateUnshareStep
  step_gauge : StateGaugeStep
  gauge_null_vectors : GaugeFromNullVectors
  row_dominant : RowDominantRightInverse
  triangular_inverse : TriangularRightInverse
  step_free_copy : StateFreeCopyStep
  state_certificate : StateCertificateNonneg

theorem signedCertificateTerminal_of_parts (h₁ : StateTerminalTest) (h₂ : SignedTreeLowerBound)
    (h₃ : PivotCountPositive) : SignedCertificateTerminal := by
  intro V A B _ _ Q v₀ z₀ L T hT hP hQ hS
  obtain ⟨P, hcard, hpos⟩ := h₃ A B T hP
  refine h₁ V A B Q v₀ z₀ L T.rootForm ∅ P hQ
    ⟨hS.1, fun x u => (h₂ A B T hT _).trans (hS.2 x u)⟩ ?_ (by simpa using hcard) hpos
  intro x y hx hy
  have hxy : x = y := by
    funext i
    cases i with
    | inl i => exact hx i (by simp)
    | inr j => exact hy j
  rw [hxy]

theorem complexNodeRealBound_of_parts (h₁ : ComplexSignedSlackBound) (h₂ : RealRestrictionValue)
    (h₃ : ComplexColumnSplit) (h₄ : CoordinateSlack) : ComplexNodeRealBound := by
  intro n m p q _ _ _ _ _ _ R t M S pivot δ w r Fp Fm hR ht hM hS hw hr y
  have key := h₁ n p q M S pivot δ w r Fp Fm hM hS hw hr (R.matrix *ᵥ ofRealVec y)
  have hsmul : ∀ N : Matrix m m ℝ, quadValue (t • N) y = t * quadValue N y := by
    intro N
    simp only [quadValue, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hslack : ∑ k ∈ R.pivotImage pivot, t * R.slackOn pivot (fun j => δ j - r j) k * y k ^ 2
      = t * ∑ j ∈ pivot, (δ j - r j) * ‖(R.matrix *ᵥ ofRealVec y) j‖ ^ 2 := by
    have hc := h₄ n m R pivot (fun j => δ j - r j) y hR
    rw [hc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hcol : ∑ c : q ⊕ q, (realColumns R.matrix t Fm c ⬝ᵥ y) ^ 2
      = t * ∑ c, ‖∑ i, star (Fm i c) * (R.matrix *ᵥ ofRealVec y) i‖ ^ 2 := by
    rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => (h₃ n m q R.matrix Fm t y c ht).symm
  rw [hsmul, hsmul, h₂, h₂, hslack, hcol]
  have hk := mul_le_mul_of_nonneg_left key ht
  linarith

theorem tree_terminal_of_signed (h₁ : StateTerminalTest) (h₂ : SignedTreeLowerBound)
    (h₃ : TreeCertificateIsSigned) (V : Type) [AddCommGroup V] [Module ℝ V] {a b : ℕ} (Q : V → ℝ)
    (z₀ : V →ₗ[ℝ] Fin a → ℝ) (L : Matrix (Fin a) (Fin b) ℝ) (T : TreeCertificate a b) :
    IsTreeCertificate T → Q 0 ≤ 0 →
    IsStateBound Q z₀ L ((haveI := T.cellFintype; ∑ c, T.cellForm c) + T.globalForm) →
    ∀ x, 0 ≤ Q x := by
  intro hT hQ hS
  obtain ⟨S, hSig, htot, E, P, hind, hcard, hpos⟩ := h₃ a b T hT
  refine h₁ V (Fin a) (Fin b) Q 0 (⇑z₀) L S.rootForm E P hQ ⟨map_zero z₀, fun x u => ?_⟩ hind
    (by simpa using hcard) hpos
  refine (h₂ _ _ S hSig _).trans ?_
  rw [htot]
  exact hS x u

theorem isSignedTree_of_nodeConditions (h₁ : SignedSlackBound) (h₂ : ComplexNodeRealBound)
    {A B : Type} [Fintype A] [Fintype B] (T : SignedTree A B) (hroot : T.parent T.root = none)
    (honly : ∀ ν, T.parent ν = none → ν = T.root) (hnode : ∀ ν, PassesNodeCondition T ν) :
    IsSignedTree T := by
  refine ⟨hroot, honly, fun ν x => ?_⟩
  letI := T.columnFintype
  rcases hnode ν with ⟨D, hD⟩ | ⟨D, hD⟩
  · letI := D.posFintype
    open Classical in
    have key := h₁ (A ⊕ B) D.Pos T.Column D.input D.base (T.pivots ν) D.pivotValue D.weight
      D.radius D.posColumns (T.nodeColumns ν) hD.input_symm hD.base_symm hD.weight_pos
      hD.row_bound x
    have hgain : T.pivotGain ν x ≤ ∑ j ∈ T.pivots ν, (D.pivotValue j - D.radius j) * x j ^ 2 :=
      Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hD.slack_le j hj) (sq_nonneg _)
    have hloss : ∑ c, (∑ i, T.nodeColumns ν i c * x i) ^ 2 = T.columnLoss ν x := by
      classical
      unfold SignedTree.columnLoss SignedTree.nodeColumns
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs with hc
      · simp only [dotProduct]
      · simp
    rw [hD.front_eq, hD.input_eq]
    linarith
  · letI := D.indexFintype
    letI := D.posFintype
    letI := D.negFintype
    open Classical in
    have key := h₂ D.Index (A ⊕ B) D.Pos D.Neg D.coords D.factor D.input D.base D.pivot
      D.pivotValue D.weight D.radius D.posColumns D.negColumns hD.coordinates hD.factor_nonneg
      hD.input_self_adjoint hD.base_self_adjoint hD.weight_pos hD.row_bound x
    have hgain : T.pivotGain ν x ≤ ∑ k ∈ T.pivots ν,
        D.factor * D.coords.slackOn D.pivot (fun j => D.pivotValue j - D.radius j) k * x k ^ 2 :=
      Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hD.slack_le k hk) (sq_nonneg _)
    obtain ⟨e, he, hec⟩ := hD.columns
    have hloss : ∑ c : D.Neg ⊕ D.Neg,
        (realColumns D.coords.matrix D.factor D.negColumns c ⬝ᵥ x) ^ 2 ≤ T.columnLoss ν x := by
      classical
      calc ∑ c : D.Neg ⊕ D.Neg, (realColumns D.coords.matrix D.factor D.negColumns c ⬝ᵥ x) ^ 2
          = ∑ c ∈ Finset.univ.map ⟨e, he⟩, (T.column c ⬝ᵥ x) ^ 2 := by
            rw [Finset.sum_map]
            exact Finset.sum_congr rfl fun c _ => by simp only [Function.Embedding.coeFn_mk, (hec c).2]
        _ ≤ T.columnLoss ν x := by
            unfold SignedTree.columnLoss
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
            intro c hc
            obtain ⟨d, -, rfl⟩ := Finset.mem_map.1 hc
            simpa using (hec d).1
    rw [hD.pivots_eq] at hgain
    rw [hD.front_eq, hD.input_eq]
    linarith

theorem stateCertificateNonneg_of_parts (h₁ : SignedCertificateTerminal) (h₂ : SignedSlackBound)
    (h₃ : ComplexNodeRealBound) : StateCertificateNonneg := by
  intro V Q C hC
  letI := C.slavedFintype
  letI := C.freeFintype
  exact h₁ V C.Slaved C.Free Q C.basePoint C.data C.freeMap C.tree
    (isSignedTree_of_nodeConditions h₂ h₃ C.tree hC.root_parent hC.only_root hC.node_conditions)
    hC.pivot_count hC.base_value hC.state

end Breakdown.CertCell.Certificate
