import Breakdown.CertCell.ShapeSplineAgree
import Breakdown.CertCell.ShapeSplineConj
import Breakdown.CertCell.ShapeSplineReflect

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline cellCount atFirst)

namespace Internal

namespace Closure

theorem negKey_negKey (κ : FieldKey) : κ.negKey.negKey = κ := by
  obtain ⟨⟨a, b⟩, p⟩ := κ
  simp [FieldKey.negKey]

theorem flipKey_flipKey (κ : FieldKey) : κ.flipKey.flipKey = κ := by
  obtain ⟨⟨a, b⟩, p⟩ := κ
  simp only [FieldKey.flipKey, labelFlip, FieldKey.mk.injEq, Prod.mk.injEq, and_true]
  constructor <;> ring

theorem flipKey_negKey (κ : FieldKey) : κ.flipKey.negKey = κ.negKey.flipKey := by
  obtain ⟨⟨a, b⟩, p⟩ := κ
  show FieldKey.mk (-(-a, b - a)) (-p) = FieldKey.mk (-(-(a, b)).1, (-(a, b)).2 - (-(a, b)).1) (-p)
  congr 1
  ext
  · rfl
  · show -(b - a) = -b - -a
    ring

theorem flipKey_of_fst_eq_zero {κ : FieldKey} (h : κ.label.1 = 0) : κ.flipKey = κ := by
  obtain ⟨⟨a, b⟩, p⟩ := κ
  simp only at h
  subst h
  simp [FieldKey.flipKey, labelFlip]

def orbitMove : Bool → Bool → FieldKey → FieldKey
  | false, false, κ => κ
  | true, false, κ => κ.negKey
  | false, true, κ => κ.flipKey
  | true, true, κ => κ.flipKey.negKey

def ampMove : Bool → Bool → KeyAmp → KeyAmp
  | false, false, A => A
  | true, false, A => A.conj
  | false, true, A => A.reflect
  | true, true, A => A.conj.reflect

theorem xor_xor_cancel (a c : Bool) : xor (xor a c) c = a := by
  cases a <;> cases c <;> rfl

theorem xor_xor_cancel_left (a c : Bool) : xor a (xor a c) = c := by
  cases a <;> cases c <;> rfl

theorem orbitMove_orbitMove (a b c d : Bool) (κ : FieldKey) :
    orbitMove a b (orbitMove c d κ) = orbitMove (xor a c) (xor b d) κ := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [orbitMove, negKey_negKey, flipKey_flipKey, flipKey_negKey]

theorem orbitMove_self (a b : Bool) (κ : FieldKey) : orbitMove a b (orbitMove a b κ) = κ := by
  cases a <;> cases b <;> simp [orbitMove, negKey_negKey, flipKey_flipKey, flipKey_negKey]

theorem orbitMove_shift (a b c d : Bool) (κ : FieldKey) :
    orbitMove (xor a c) (xor b d) (orbitMove c d κ) = orbitMove a b κ := by
  rw [orbitMove_orbitMove, xor_xor_cancel, xor_xor_cancel]

theorem fst_orbitMove_eq_zero (a b : Bool) (κ : FieldKey) :
    (orbitMove a b κ).label.1 = 0 ↔ κ.label.1 = 0 := by
  cases a <;> cases b <;> simp [orbitMove, FieldKey.negKey, FieldKey.flipKey, labelFlip]

theorem orbitMove_of_fst_eq_zero (a b : Bool) {κ : FieldKey} (h : κ.label.1 = 0) :
    orbitMove a b κ = orbitMove a false κ := by
  cases a <;> cases b <;> simp [orbitMove, flipKey_of_fst_eq_zero h]

theorem mem_orbitClosure {S : Finset FieldKey} {κ : FieldKey} :
    κ ∈ orbitClosure S ↔ ∃ a b, orbitMove a b κ ∈ S := by
  have key : ∀ a b, (∃ ν ∈ S, orbitMove a b ν = κ) ↔ orbitMove a b κ ∈ S := by
    intro a b
    constructor
    · rintro ⟨ν, hν, rfl⟩
      rwa [orbitMove_self]
    · intro h
      exact ⟨_, h, orbitMove_self a b κ⟩
  unfold orbitClosure
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (((h | h) | h) | h)
    · exact ⟨false, false, h⟩
    · exact ⟨true, false, (key true false).1 h⟩
    · exact ⟨false, true, (key false true).1 h⟩
    · exact ⟨true, true, (key true true).1 h⟩
  · rintro ⟨a, b, h⟩
    cases a <;> cases b
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inr ((key false true).2 h))
    · exact Or.inl (Or.inl (Or.inr ((key true false).2 h)))
    · exact Or.inr ((key true true).2 h)

theorem orbitMove_mem {S : Finset FieldKey} {κ : FieldKey} (c d : Bool) (h : κ ∈ orbitClosure S) :
    orbitMove c d κ ∈ orbitClosure S := by
  obtain ⟨a, b, hab⟩ := mem_orbitClosure.1 h
  exact mem_orbitClosure.2 ⟨xor a c, xor b d, by rw [orbitMove_shift]; exact hab⟩

theorem closureAmp_eq {S : Finset FieldKey} (given : FieldKey → KeyAmp) {κ : FieldKey}
    (hκ : κ ∈ orbitClosure S) :
    ∃ a b, orbitMove a b κ ∈ S ∧ closureAmp S given κ = ampMove a b (given (orbitMove a b κ)) := by
  unfold closureAmp
  split_ifs with h1 h2 h3
  · exact ⟨false, false, h1, rfl⟩
  · exact ⟨true, false, h2, rfl⟩
  · exact ⟨false, true, h3, rfl⟩
  · obtain ⟨a, b, h⟩ := mem_orbitClosure.1 hκ
    cases a <;> cases b
    · exact (h1 h).elim
    · exact (h3 h).elim
    · exact (h2 h).elim
    · exact ⟨true, true, h, rfl⟩

theorem orbitMove_eq_of_mem {S : Finset FieldKey} {given : FieldKey → KeyAmp} (hS : IsGivenKeyData S given)
    {ν : FieldKey} (hν : ν ∈ S) (a b : Bool) (h : orbitMove a b ν ∈ S) : orbitMove a b ν = ν := by
  cases a <;> cases b
  · rfl
  · exact hS.one_per_orbit ν hν _ h (Or.inr (Or.inl rfl))
  · exact hS.one_per_orbit ν hν _ h (Or.inl rfl)
  · exact hS.one_per_orbit ν hν _ h (Or.inr (Or.inr rfl))

structure IsAmpRel (R : KeyAmp → KeyAmp → Prop) : Prop where
  refl : ∀ A : KeyAmp, R A A
  symm : ∀ {A B : KeyAmp}, R A B → R B A
  trans : ∀ {A B C : KeyAmp}, R A B → R B C → R A C
  conj : ∀ {A B : KeyAmp}, R A B → R A.conj B.conj
  reflect : ∀ {A B : KeyAmp}, R A B → R A.reflect B.reflect
  conj_conj : ∀ A : KeyAmp, R A.conj.conj A
  reflect_reflect : ∀ A : KeyAmp, R A.reflect.reflect A
  conj_reflect : ∀ A : KeyAmp, R A.reflect.conj A.conj.reflect

theorem ampMove_congr {R : KeyAmp → KeyAmp → Prop} (hR : IsAmpRel R) (a b : Bool) {A B : KeyAmp}
    (h : R A B) : R (ampMove a b A) (ampMove a b B) := by
  cases a <;> cases b
  · exact h
  · exact hR.reflect h
  · exact hR.conj h
  · exact hR.reflect (hR.conj h)

theorem ampMove_ampMove {R : KeyAmp → KeyAmp → Prop} (hR : IsAmpRel R) (a b c d : Bool) (A : KeyAmp) :
    R (ampMove a b (ampMove c d A)) (ampMove (xor a c) (xor b d) A) := by
  cases a <;> cases b <;> cases c <;> cases d
  · exact hR.refl A
  · exact hR.refl A.reflect
  · exact hR.refl A.conj
  · exact hR.refl A.conj.reflect
  · exact hR.refl A.reflect
  · exact hR.reflect_reflect A
  · exact hR.refl A.conj.reflect
  · exact hR.reflect_reflect A.conj
  · exact hR.refl A.conj
  · exact hR.conj_reflect A
  · exact hR.conj_conj A
  · exact hR.trans (hR.conj_reflect A.conj) (hR.reflect (hR.conj_conj A))
  · exact hR.refl A.conj.reflect
  · exact hR.trans (hR.reflect (hR.conj_reflect A)) (hR.reflect_reflect A.conj)
  · exact hR.reflect (hR.conj_conj A)
  · exact hR.trans (hR.reflect (hR.conj_reflect A.conj)) (hR.trans (hR.reflect_reflect _) (hR.conj_conj A))

section Orbit

variable {R : KeyAmp → KeyAmp → Prop} {S : Finset FieldKey} {given : FieldKey → KeyAmp}
  (hR : IsAmpRel R) (hS : IsGivenKeyData S given) (T : FieldKey → Prop)
  (hT : ∀ a b κ, T (orbitMove a b κ) ↔ T κ)
  (hstab : ∀ ν ∈ S, T ν → ∀ a b, orbitMove a b ν = ν → R (given ν) (ampMove a b (given ν)))

include hR hS hT hstab

theorem closureAmp_rel {κ : FieldKey} (hκ : κ ∈ orbitClosure S) (hTκ : T κ) (a b : Bool)
    (hab : orbitMove a b κ ∈ S) : R (closureAmp S given κ) (ampMove a b (given (orbitMove a b κ))) := by
  obtain ⟨c, d, hcd, heq⟩ := closureAmp_eq given hκ
  rw [heq]
  have hmove : orbitMove a b κ = orbitMove (xor a c) (xor b d) (orbitMove c d κ) :=
    (orbitMove_shift a b c d κ).symm
  have hfix : orbitMove (xor a c) (xor b d) (orbitMove c d κ) = orbitMove c d κ :=
    orbitMove_eq_of_mem hS hcd _ _ (by rw [← hmove]; exact hab)
  have hst := hstab _ hcd ((hT c d κ).2 hTκ) _ _ hfix
  rw [hmove, hfix]
  have h2 := ampMove_ampMove hR a b (xor a c) (xor b d) (given (orbitMove c d κ))
  rw [xor_xor_cancel_left, xor_xor_cancel_left] at h2
  exact hR.symm (hR.trans (ampMove_congr hR a b hst) h2)

theorem closureAmp_move_rel {κ : FieldKey} (hκ : κ ∈ orbitClosure S) (hTκ : T κ) (c d : Bool) :
    R (closureAmp S given (orbitMove c d κ)) (ampMove c d (closureAmp S given κ)) := by
  obtain ⟨a, b, hab⟩ := mem_orbitClosure.1 hκ
  have h1 := closureAmp_rel hR hS T hT hstab (orbitMove_mem c d hκ) ((hT c d κ).2 hTκ) (xor a c) (xor b d)
    (by rw [orbitMove_shift]; exact hab)
  rw [orbitMove_shift] at h1
  have h0 := closureAmp_rel hR hS T hT hstab hκ hTκ a b hab
  have h3 := ampMove_ampMove hR c d a b (given (orbitMove a b κ))
  rw [Bool.xor_comm c a, Bool.xor_comm d b] at h3
  exact hR.trans h1 (hR.symm (hR.trans (ampMove_congr hR c d h0) h3))

end Orbit

theorem ampMove_lowOrder (a b : Bool) (A : KeyAmp) : (ampMove a b A).lowOrder = A.lowOrder := by
  cases a <;> cases b <;> rfl

theorem ampMove_highOrder (a b : Bool) (A : KeyAmp) : (ampMove a b A).highOrder = A.highOrder := by
  cases a <;> cases b <;> rfl

section Rules

variable (hA : SplineAgreementRules)
include hA

theorem agrees_refl' (S : Spline) : SplineAgrees S S := (hA 0 0 false S S S).1

theorem agrees_symm' {S T : Spline} (h : SplineAgrees S T) : SplineAgrees T S := (hA 0 0 false S T S).2.1 h

theorem agrees_trans' {S T U : Spline} (h1 : SplineAgrees S T) (h2 : SplineAgrees T U) : SplineAgrees S U :=
  (hA 0 0 false S T U).2.2.1 h1 h2

theorem agrees_conj' {S T : Spline} (h : SplineAgrees S T) : SplineAgrees S.conj T.conj :=
  ((hA 0 0 false S T S).2.2.2.1 h).1

theorem agrees_reflect' (odd : Bool) {S T : Spline} (h : SplineAgrees S T) :
    SplineAgrees (reflectSpline odd S) (reflectSpline odd T) :=
  ((hA 0 0 odd S T S).2.2.2.1 h).2

theorem agrees_conj_conj' (S : Spline) : SplineAgrees S.conj.conj S := (hA 0 0 false S S S).2.2.2.2.1

theorem agrees_reflect_reflect' (odd : Bool) (S : Spline) :
    SplineAgrees (reflectSpline odd (reflectSpline odd S)) S := (hA 0 0 odd S S S).2.2.2.2.2.1

theorem agrees_reflect_conj' (odd : Bool) (S : Spline) :
    SplineAgrees (reflectSpline odd S).conj (reflectSpline odd S.conj) := (hA 0 0 odd S S S).2.2.2.2.2.2.1

theorem joined_of_agrees' {a b : ℕ} {S T : Spline} (h : SplineAgrees S T) (hS : IsJoinedSpline a b S) :
    IsJoinedSpline a b T := (hA a b false S T S).2.2.2.2.2.2.2.1 h hS

end Rules

abbrev TypeOneRel (A B : KeyAmp) : Prop :=
  SplineAgrees A.radial B.radial ∧ SplineAgrees A.polar B.polar ∧ A.lowOrder = B.lowOrder ∧
    A.highOrder = B.highOrder

abbrev TypeTwoRel (A B : KeyAmp) : Prop :=
  SplineAgrees A.stream B.stream ∧ SplineAgrees A.swirl B.swirl ∧ A.axisCoef = B.axisCoef ∧
    A.lowOrder = B.lowOrder ∧ A.highOrder = B.highOrder

theorem isAmpRel_typeOne (hA : SplineAgreementRules) : IsAmpRel TypeOneRel where
  refl _ := ⟨agrees_refl' hA _, agrees_refl' hA _, rfl, rfl⟩
  symm h := ⟨agrees_symm' hA h.1, agrees_symm' hA h.2.1, h.2.2.1.symm, h.2.2.2.symm⟩
  trans h1 h2 := ⟨agrees_trans' hA h1.1 h2.1, agrees_trans' hA h1.2.1 h2.2.1, h1.2.2.1.trans h2.2.2.1,
    h1.2.2.2.trans h2.2.2.2⟩
  conj h := ⟨agrees_conj' hA h.1, agrees_conj' hA h.2.1, h.2.2.1, h.2.2.2⟩
  reflect h := ⟨agrees_reflect' hA false h.1, agrees_reflect' hA true h.2.1, h.2.2.1, h.2.2.2⟩
  conj_conj _ := ⟨agrees_conj_conj' hA _, agrees_conj_conj' hA _, rfl, rfl⟩
  reflect_reflect _ := ⟨agrees_reflect_reflect' hA false _, agrees_reflect_reflect' hA true _, rfl, rfl⟩
  conj_reflect _ := ⟨agrees_reflect_conj' hA false _, agrees_reflect_conj' hA true _, rfl, rfl⟩

theorem isAmpRel_typeTwo (hA : SplineAgreementRules) : IsAmpRel TypeTwoRel where
  refl _ := ⟨agrees_refl' hA _, agrees_refl' hA _, rfl, rfl, rfl⟩
  symm h := ⟨agrees_symm' hA h.1, agrees_symm' hA h.2.1, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩
  trans h1 h2 := ⟨agrees_trans' hA h1.1 h2.1, agrees_trans' hA h1.2.1 h2.2.1, h1.2.2.1.trans h2.2.2.1,
    h1.2.2.2.1.trans h2.2.2.2.1, h1.2.2.2.2.trans h2.2.2.2.2⟩
  conj h := ⟨agrees_conj' hA h.1, agrees_conj' hA h.2.1, congrArg (starRingEnd ℂ) h.2.2.1, h.2.2.2.1,
    h.2.2.2.2⟩
  reflect h := ⟨agrees_reflect' hA true h.1, agrees_reflect' hA true h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  conj_conj _ := ⟨agrees_conj_conj' hA _, agrees_conj_conj' hA _, Complex.conj_conj _, rfl, rfl⟩
  reflect_reflect _ := ⟨agrees_reflect_reflect' hA true _, agrees_reflect_reflect' hA true _, rfl, rfl, rfl⟩
  conj_reflect _ := ⟨agrees_reflect_conj' hA true _, agrees_reflect_conj' hA true _, rfl, rfl, rfl⟩

theorem stab_typeOne (hA : SplineAgreementRules) {S : Finset FieldKey} {given : FieldKey → KeyAmp}
    (hS : IsGivenKeyData S given) :
    ∀ ν ∈ S, ν.label.1 ≠ 0 → ∀ a b, orbitMove a b ν = ν → TypeOneRel (given ν) (ampMove a b (given ν)) := by
  intro ν hν h1 a b hfix
  cases a <;> cases b
  · exact (isAmpRel_typeOne hA).refl _
  · have h := congrArg (fun κ : FieldKey => κ.label.1) hfix
    change -ν.label.1 = ν.label.1 at h
    exact absurd (by omega) h1
  · have h := congrArg (fun κ : FieldKey => κ.label.1) hfix
    change -ν.label.1 = ν.label.1 at h
    exact absurd (by omega) h1
  · obtain ⟨hr, hp⟩ := hS.self_conj_flip ν hν h1 hfix
    exact ⟨hr, hp, rfl, rfl⟩

theorem stab_typeTwo (hA : SplineAgreementRules) {S : Finset FieldKey} {given : FieldKey → KeyAmp}
    (hS : IsGivenKeyData S given) :
    ∀ ν ∈ S, ν.label.1 = 0 → ∀ a b, orbitMove a b ν = ν → TypeTwoRel (given ν) (ampMove a b (given ν)) := by
  intro ν hν h0 a b hfix
  have hodd : TypeTwoRel (given ν) (given ν).reflect :=
    ⟨hS.stream_odd ν hν h0, hS.swirl_odd ν hν h0, rfl, rfl, rfl⟩
  have hconj : ν.negKey = ν → TypeTwoRel (given ν) (given ν).conj := by
    intro hn
    obtain ⟨hs, hw, ha⟩ := hS.self_conj ν hν hn
    exact ⟨hs, hw, ha.symm, rfl, rfl⟩
  cases a <;> cases b
  · exact (isAmpRel_typeTwo hA).refl _
  · exact hodd
  · exact hconj hfix
  · have hn : ν.negKey = ν := by
      change ν.flipKey.negKey = ν at hfix
      rwa [flipKey_of_fst_eq_zero h0] at hfix
    exact (isAmpRel_typeTwo hA).trans hodd ((isAmpRel_typeTwo hA).reflect (hconj hn))

theorem fullMesh_cellCount_pos {M : CellCert.GivenFields.TensorMesh} (h : IsFullMesh M) :
    0 < cellCount M.tBreaks := by
  have h1 := h.t_first
  have h2 := h.t_last
  generalize M.tBreaks = l at h1 h2 ⊢
  rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩
  · simp at h1
  · simp at h1 h2
    rw [h1] at h2
    norm_num at h2
  · simp only [cellCount, List.length_cons]
    omega

theorem atFirst_zero_map_conj (P : MvPolynomial (Fin 2) ℂ) :
    atFirst 0 (MvPolynomial.map (starRingEnd ℂ) P) = MvPolynomial.map (starRingEnd ℂ) (atFirst 0 P) := by
  unfold atFirst
  rw [MvPolynomial.map_bind₁]
  congr 2
  funext k
  split_ifs <;> simp

theorem origin_of_agrees {U V : Spline} (h : SplineAgrees U V) (hV : IsFullMesh V.mesh)
    (h0 : ∀ j < cellCount V.mesh.xBreaks, atFirst 0 (V.piece 0 j) = 0) :
    ∀ j < cellCount U.mesh.xBreaks, atFirst 0 (U.piece 0 j) = 0 := by
  intro j hj
  have hm := h.mesh_eq
  have ht : 0 < cellCount U.mesh.tBreaks := by
    rw [hm]
    exact fullMesh_cellCount_pos hV
  rw [h.piece_eq 0 ht j hj]
  exact h0 j (by rw [← hm]; exact hj)

theorem origin_conj {V : Spline} (h0 : ∀ j < cellCount V.mesh.xBreaks, atFirst 0 (V.piece 0 j) = 0) :
    ∀ j < cellCount V.conj.mesh.xBreaks, atFirst 0 (V.conj.piece 0 j) = 0 := by
  intro j hj
  change atFirst 0 (MvPolynomial.map (starRingEnd ℂ) (V.piece 0 j)) = 0
  rw [atFirst_zero_map_conj, h0 j hj, map_zero]

section Classes

variable (hR : SplineReflection) (hC : SplineConjugation)
include hR hC

theorem joined_reflect_conj {p q : ℕ} (odd : Bool) {U : Spline} (h : IsJoinedSpline p q U) :
    IsJoinedSpline p q U.conj ∧ IsJoinedSpline p q (reflectSpline odd U) ∧
      IsJoinedSpline p q (reflectSpline odd U.conj) :=
  ⟨(hC p q U h).1, (hR p q odd U h).1, (hR p q odd U.conj (hC p q U h).1).1⟩

theorem ampMove_radial {p q : ℕ} (a b : Bool) {A : KeyAmp} (h : IsJoinedSpline p q A.radial) :
    IsJoinedSpline p q (ampMove a b A).radial := by
  have := joined_reflect_conj hR hC false h
  cases a <;> cases b
  · exact h
  · exact this.2.1
  · exact this.1
  · exact this.2.2

theorem ampMove_polar {p q : ℕ} (a b : Bool) {A : KeyAmp} (h : IsJoinedSpline p q A.polar) :
    IsJoinedSpline p q (ampMove a b A).polar := by
  have := joined_reflect_conj hR hC true h
  cases a <;> cases b
  · exact h
  · exact this.2.1
  · exact this.1
  · exact this.2.2

theorem ampMove_stream {p q : ℕ} (a b : Bool) {A : KeyAmp} (h : IsJoinedSpline p q A.stream) :
    IsJoinedSpline p q (ampMove a b A).stream := by
  have := joined_reflect_conj hR hC true h
  cases a <;> cases b
  · exact h
  · exact this.2.1
  · exact this.1
  · exact this.2.2

theorem ampMove_swirl {p q : ℕ} (a b : Bool) {A : KeyAmp} (h : IsJoinedSpline p q A.swirl) :
    IsJoinedSpline p q (ampMove a b A).swirl := by
  have := joined_reflect_conj hR hC true h
  cases a <;> cases b
  · exact h
  · exact this.2.1
  · exact this.1
  · exact this.2.2

end Classes

end Closure

end Internal

open Internal.Closure in
theorem closureDataValid_of_rules (hA : SplineAgreementRules) (hR : SplineReflection)
    (hC : SplineConjugation) : ClosureDataValid := by
  intro S given hS
  have R1 := isAmpRel_typeOne hA
  have R2 := isAmpRel_typeTwo hA
  have T1 : ∀ a b κ, (fun κ : FieldKey => κ.label.1 ≠ 0) (orbitMove a b κ) ↔ κ.label.1 ≠ 0 :=
    fun a b κ => not_congr (fst_orbitMove_eq_zero a b κ)
  have T2 : ∀ a b κ, (fun κ : FieldKey => κ.label.1 = 0) (orbitMove a b κ) ↔ κ.label.1 = 0 :=
    fun a b κ => fst_orbitMove_eq_zero a b κ
  have st1 := stab_typeOne hA hS
  have st2 := stab_typeTwo hA hS
  have move1 : ∀ κ ∈ orbitClosure S, κ.label.1 ≠ 0 → ∀ c d,
      TypeOneRel (closureAmp S given (orbitMove c d κ)) (ampMove c d (closureAmp S given κ)) :=
    fun κ hκ h c d => closureAmp_move_rel R1 hS _ T1 st1 hκ h c d
  have move2 : ∀ κ ∈ orbitClosure S, κ.label.1 = 0 → ∀ c d,
      TypeTwoRel (closureAmp S given (orbitMove c d κ)) (ampMove c d (closureAmp S given κ)) :=
    fun κ hκ h c d => closureAmp_move_rel R2 hS _ T2 st2 hκ h c d
  have rep1 : ∀ κ ∈ orbitClosure S, κ.label.1 ≠ 0 → ∃ a b, orbitMove a b κ ∈ S ∧
      (orbitMove a b κ).label.1 ≠ 0 ∧
      TypeOneRel (closureAmp S given κ) (ampMove a b (given (orbitMove a b κ))) := by
    intro κ hκ h
    obtain ⟨a, b, hab⟩ := mem_orbitClosure.1 hκ
    exact ⟨a, b, hab, (T1 a b κ).2 h, closureAmp_rel R1 hS _ T1 st1 hκ h a b hab⟩
  have rep2 : ∀ κ ∈ orbitClosure S, κ.label.1 = 0 → ∃ a, orbitMove a false κ ∈ S ∧
      (orbitMove a false κ).label.1 = 0 ∧
      TypeTwoRel (closureAmp S given κ) (ampMove a false (given (orbitMove a false κ))) := by
    intro κ hκ h
    obtain ⟨a, b, hab⟩ := mem_orbitClosure.1 hκ
    rw [orbitMove_of_fst_eq_zero a b h] at hab
    exact ⟨a, hab, (T2 a false κ).2 h, closureAmp_rel R2 hS _ T2 st2 hκ h a false hab⟩
  refine
    { keys_neg := fun κ => ⟨fun h => orbitMove_mem true false h, fun h => ?_⟩
      keys_flip := fun κ => ⟨fun h => orbitMove_mem false true h, fun h => ?_⟩
      neg_radial := fun κ hκ h => (move1 κ hκ h true false).1
      neg_polar := fun κ hκ h => (move1 κ hκ h true false).2.1
      neg_stream := fun κ hκ h => (move2 κ hκ h true false).1
      neg_swirl := fun κ hκ h => (move2 κ hκ h true false).2.1
      neg_axisCoef := fun κ hκ h => (move2 κ hκ h true false).2.2.1
      neg_orders := fun κ hκ => ?_
      flip_radial := fun κ hκ h => (move1 κ hκ h false true).1
      flip_polar := fun κ hκ h => (move1 κ hκ h false true).2.1
      flip_orders := fun κ hκ => ?_
      stream_odd := fun κ hκ h => ?_
      swirl_odd := fun κ hκ h => ?_
      radial_class := fun κ hκ h => ?_
      polar_class := fun κ hκ h => ?_
      lowOrder_ge := fun κ hκ h => ?_
      stream_class := fun κ hκ h => ?_
      swirl_class := fun κ hκ h => ?_
      stream_origin := fun κ hκ h => ?_
      swirl_origin := fun κ hκ h => ?_
      highOrder_pos := fun κ hκ => ?_ }
  · have := orbitMove_mem (S := S) true false h
    rwa [show orbitMove true false κ.negKey = κ from negKey_negKey κ] at this
  · have := orbitMove_mem (S := S) false true h
    rwa [show orbitMove false true κ.flipKey = κ from flipKey_flipKey κ] at this
  · by_cases h : κ.label.1 = 0
    · exact ⟨(move2 κ hκ h true false).2.2.2.1, (move2 κ hκ h true false).2.2.2.2⟩
    · exact ⟨(move1 κ hκ h true false).2.2.1, (move1 κ hκ h true false).2.2.2⟩
  · by_cases h : κ.label.1 = 0
    · exact ⟨(move2 κ hκ h false true).2.2.2.1, (move2 κ hκ h false true).2.2.2.2⟩
    · exact ⟨(move1 κ hκ h false true).2.2.1, (move1 κ hκ h false true).2.2.2⟩
  · have e := move2 κ hκ h false true
    rw [show orbitMove false true κ = κ from flipKey_of_fst_eq_zero h] at e
    exact e.1
  · have e := move2 κ hκ h false true
    rw [show orbitMove false true κ = κ from flipKey_of_fst_eq_zero h] at e
    exact e.2.1
  · obtain ⟨a, b, hab, hν, r⟩ := rep1 κ hκ h
    exact joined_of_agrees' hA (agrees_symm' hA r.1) (ampMove_radial hR hC a b (hS.radial_class _ hab hν))
  · obtain ⟨a, b, hab, hν, r⟩ := rep1 κ hκ h
    exact joined_of_agrees' hA (agrees_symm' hA r.2.1) (ampMove_polar hR hC a b (hS.polar_class _ hab hν))
  · obtain ⟨a, b, hab, hν, r⟩ := rep1 κ hκ h
    change 2 ≤ (closureAmp S given κ).lowOrder
    rw [r.2.2.1, ampMove_lowOrder]
    exact hS.lowOrder_ge _ hab hν
  · obtain ⟨a, hab, hν, r⟩ := rep2 κ hκ h
    exact joined_of_agrees' hA (agrees_symm' hA r.1) (ampMove_stream hR hC a false (hS.stream_class _ hab hν))
  · obtain ⟨a, hab, hν, r⟩ := rep2 κ hκ h
    exact joined_of_agrees' hA (agrees_symm' hA r.2.1) (ampMove_swirl hR hC a false (hS.swirl_class _ hab hν))
  · obtain ⟨a, hab, hν, r⟩ := rep2 κ hκ h
    refine origin_of_agrees r.1 ?_ ?_
    · cases a
      · exact (hS.stream_class _ hab hν).mesh
      · exact (hS.stream_class _ hab hν).mesh
    · cases a
      · exact hS.stream_origin _ hab hν
      · exact origin_conj (hS.stream_origin _ hab hν)
  · obtain ⟨a, hab, hν, r⟩ := rep2 κ hκ h
    refine origin_of_agrees r.2.1 ?_ ?_
    · cases a
      · exact (hS.swirl_class _ hab hν).mesh
      · exact (hS.swirl_class _ hab hν).mesh
    · cases a
      · exact hS.swirl_origin _ hab hν
      · exact origin_conj (hS.swirl_origin _ hab hν)
  · change 1 ≤ (closureAmp S given κ).highOrder
    by_cases h : κ.label.1 = 0
    · obtain ⟨a, hab, hν, r⟩ := rep2 κ hκ h
      rw [r.2.2.2.2, ampMove_highOrder]
      exact hS.highOrder_pos _ hab
    · obtain ⟨a, b, hab, hν, r⟩ := rep1 κ hκ h
      rw [r.2.2.2, ampMove_highOrder]
      exact hS.highOrder_pos _ hab

theorem closureDataValid : ClosureDataValid :=
  closureDataValid_of_rules splineAgreementRules splineReflection splineConjugation

end GivenShape

end CertCell

end Breakdown
