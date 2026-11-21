import Breakdown.CertCell.CertificateStatements
import Breakdown.CertCell.StatementDefs

open Matrix Breakdown.CellCert.Finite

noncomputable section

namespace Breakdown.CertCell.Certificate

def RealNodeEnclosureBound : Prop :=
  ∀ (A B : Type) [Fintype A] [Fintype B] (T : SignedTree A B) (ν : T.Node) (D : RealNodeData A B)
    (E F : Matrix (A ⊕ B) (A ⊕ B) ℝ), PassesRealNodeEnclosure T ν D E F → ∀ x : A ⊕ B → ℝ,
    quadValue (T.front ν) x + T.pivotGain ν x - T.columnLoss ν x ≤ quadValue (T.nodeInput ν) x

def ComplexNodeEnclosureBound : Prop :=
  ∀ (A B : Type) [Fintype A] [Fintype B] (T : SignedTree A B) (ν : T.Node) (D : ComplexNodeData A B)
    (E F : Matrix D.Index D.Index ℝ), PassesComplexNodeEnclosure T ν D E F → ∀ x : A ⊕ B → ℝ,
    quadValue (T.front ν) x + T.pivotGain ν x - T.columnLoss ν x ≤ quadValue (T.nodeInput ν) x

structure IsSignedStateEnclosureCertificate {V : Type} (Q : V → ℝ) (C : SignedStateCertificate V) :
    Prop where
  base_value : Q C.basePoint ≤ 0
  state : (haveI := C.slavedFintype; haveI := C.freeFintype;
    IsState Q C.basePoint C.data C.freeMap C.tree.totalForm)
  root_parent : C.tree.parent C.tree.root = none
  only_root : ∀ ν, C.tree.parent ν = none → ν = C.tree.root
  node_conditions : ∀ ν, (haveI := C.slavedFintype; haveI := C.freeFintype; PassesNodeEnclosure C.tree ν)
  pivot_count : (haveI := C.slavedFintype; haveI := C.freeFintype; PassesPivotCount C.tree)

def StateEnclosureCertificateNonneg : Prop :=
  ∀ (V : Type) (Q : V → ℝ) (C : SignedStateCertificate V), IsSignedStateEnclosureCertificate Q C →
    ∀ x, 0 ≤ Q x

theorem realNodeEnclosure_of_condition {A B : Type} [Fintype A] [Fintype B] (T : SignedTree A B)
    (ν : T.Node) (D : RealNodeData A B) (h : PassesRealNodeCondition T ν D) :
    PassesRealNodeEnclosure T ν D 0 0 where
  input_lower x := by rw [h.input_eq]; simp [quadValue]
  input_symm := h.input_symm
  base_symm := h.base_symm
  weight_pos := h.weight_pos
  input_error_nonneg _ _ := le_rfl
  input_error_symm := by simp
  front_error_nonneg _ _ := le_rfl
  front_error_symm := by simp
  row_bound i := by simpa using h.row_bound i
  front_upper x := by rw [h.front_eq]; simp [quadValue]
  slack_le := h.slack_le

theorem complexNodeEnclosure_of_condition {A B : Type} [Fintype A] [Fintype B] (T : SignedTree A B)
    (ν : T.Node) (D : ComplexNodeData A B) (h : PassesComplexNodeCondition T ν D) :
    PassesComplexNodeEnclosure T ν D 0 0 where
  coordinates := h.coordinates
  factor_nonneg := h.factor_nonneg
  input_self_adjoint := h.input_self_adjoint
  base_self_adjoint := h.base_self_adjoint
  weight_pos := h.weight_pos
  input_error_nonneg _ _ := le_rfl
  input_error_symm := by simp
  front_error_nonneg _ _ := le_rfl
  front_error_symm := by simp
  row_bound i := by simpa using h.row_bound i
  input_lower x := by rw [h.input_eq]; simp [quadValue]
  front_upper x := by rw [h.front_eq]; simp [quadValue]
  pivots_eq := h.pivots_eq
  slack_le := h.slack_le
  columns := h.columns

theorem nodeEnclosure_of_condition {A B : Type} [Fintype A] [Fintype B] (T : SignedTree A B)
    (ν : T.Node) (h : PassesNodeCondition T ν) : PassesNodeEnclosure T ν := by
  rcases h with ⟨D, hD⟩ | ⟨D, hD⟩
  · exact Or.inl ⟨D, 0, 0, realNodeEnclosure_of_condition T ν D hD⟩
  · exact Or.inr ⟨D, 0, 0, complexNodeEnclosure_of_condition T ν D hD⟩

theorem isSignedStateEnclosureCertificate_of_certificate {V : Type} (Q : V → ℝ)
    (C : SignedStateCertificate V) (h : IsSignedStateCertificate Q C) :
    IsSignedStateEnclosureCertificate Q C where
  base_value := h.base_value
  state := h.state
  root_parent := h.root_parent
  only_root := h.only_root
  node_conditions ν := by
    letI := C.slavedFintype
    letI := C.freeFintype
    exact nodeEnclosure_of_condition C.tree ν (h.node_conditions ν)
  pivot_count := h.pivot_count

theorem isSignedTree_of_nodeEnclosures (h₁ : RealNodeEnclosureBound)
    (h₂ : ComplexNodeEnclosureBound) {A B : Type} [Fintype A] [Fintype B] (T : SignedTree A B)
    (hroot : T.parent T.root = none) (honly : ∀ ν, T.parent ν = none → ν = T.root)
    (hnode : ∀ ν, PassesNodeEnclosure T ν) : IsSignedTree T := by
  refine ⟨hroot, honly, fun ν x => ?_⟩
  rcases hnode ν with ⟨D, E, F, hD⟩ | ⟨D, E, F, hD⟩
  · exact h₁ A B T ν D E F hD x
  · exact h₂ A B T ν D E F hD x

theorem stateEnclosureCertificateNonneg_of_parts (h₁ : SignedCertificateTerminal)
    (h₂ : RealNodeEnclosureBound) (h₃ : ComplexNodeEnclosureBound) :
    StateEnclosureCertificateNonneg := by
  intro V Q C hC
  letI := C.slavedFintype
  letI := C.freeFintype
  exact h₁ V C.Slaved C.Free Q C.basePoint C.data C.freeMap C.tree
    (isSignedTree_of_nodeEnclosures h₂ h₃ C.tree hC.root_parent hC.only_root hC.node_conditions)
    hC.pivot_count hC.base_value hC.state

private theorem mul_le_weighted_half (a b u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    a * b ≤ (a ^ 2 * u / v + b ^ 2 * v / u) / 2 := by
  have h : a ^ 2 * u / v + b ^ 2 * v / u - 2 * (a * b) = (a * u - b * v) ^ 2 / (u * v) := by
    field_simp
    ring
  have : 0 ≤ (a * u - b * v) ^ 2 / (u * v) := div_nonneg (sq_nonneg _) (mul_pos hu hv).le
  linarith

private theorem quadValue_le_weightedRows {n : Type*} [Fintype n] (E : Matrix n n ℝ)
    (w a : n → ℝ) (hw : ∀ j, 0 < w j) (hE : ∀ i j, 0 ≤ E i j) (hs : Eᵀ = E) :
    quadValue E a ≤ ∑ i, (w i * ∑ j, E i j / w j) * a i ^ 2 := by
  have hexp : quadValue E a = ∑ i, ∑ j, E i j * (a i * a j) := by
    simp only [quadValue, dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsym : ∀ i j, E j i = E i j := fun i j => by
    have := congrFun (congrFun hs i) j
    simpa [transpose_apply] using this
  rw [hexp]
  calc ∑ i, ∑ j, E i j * (a i * a j)
      ≤ ∑ i, ∑ j, E i j * ((a i ^ 2 * w i / w j + a j ^ 2 * w j / w i) / 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (mul_le_weighted_half _ _ _ _ (hw i) (hw j)) (hE i j)
    _ = (∑ i, ∑ j, E i j * (a i ^ 2 * w i / w j)
          + ∑ i, ∑ j, E i j * (a j ^ 2 * w j / w i)) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i, ∑ j, E i j * (a i ^ 2 * w i / w j) := by
        have : ∑ i, ∑ j, E i j * (a j ^ 2 * w j / w i)
            = ∑ i, ∑ j, E i j * (a i ^ 2 * w i / w j) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hsym]
        rw [this]
        ring
    _ = ∑ i, (w i * ∑ j, E i j / w j) * a i ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring

private theorem quadValue_pivotDiagonal {n : Type*} [Fintype n] [DecidableEq n] (P : Finset n)
    (g x : n → ℝ) : quadValue (pivotDiagonal P g) x = ∑ j ∈ P, g j * x j ^ 2 := by
  simp only [quadValue, pivotDiagonal, mulVec_diagonal, dotProduct]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ P)]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h0 : ∑ x_1 ∈ Finset.univ.filter (fun j => j ∉ P), x x_1 * ((if x_1 ∈ P then g x_1 else 0) * x x_1) = 0 :=
    Finset.sum_eq_zero fun j hj => by simp [(Finset.mem_filter.1 hj).2]
  rw [h0, add_zero]
  exact Finset.sum_congr rfl fun j hj => by simp [hj]; ring


private theorem quadValue_sub' {n : Type*} [Fintype n] (M N : Matrix n n ℝ) (x : n → ℝ) :
    quadValue (M - N) x = quadValue M x - quadValue N x := by
  simp [quadValue, sub_mulVec, dotProduct_sub]

private theorem quadValue_add' {n : Type*} [Fintype n] (M N : Matrix n n ℝ) (x : n → ℝ) :
    quadValue (M + N) x = quadValue M x + quadValue N x := by
  simp [quadValue, add_mulVec, dotProduct_add]

open Classical in
theorem realNodeEnclosureBound_of_slackBound (h : SignedSlackBound) : RealNodeEnclosureBound := by
  intro A B _ _ T ν D E F hD x
  letI := T.columnFintype
  letI := D.posFintype
  set ρ : A ⊕ B → ℝ := fun i => D.weight i * ∑ j, (E + F) i j / D.weight j with hρ
  have hr : ∀ i, D.weight i * ∑ j, |slackRemainder D.input D.base (T.pivots ν) D.pivotValue
      D.posColumns (T.nodeColumns ν) i j| / D.weight j ≤ D.radius i - ρ i := by
    intro i
    have hb := hD.row_bound i
    have hsplit : D.weight i * ∑ j, (|slackRemainder D.input D.base (T.pivots ν) D.pivotValue
        D.posColumns (T.nodeColumns ν) i j| + E i j + F i j) / D.weight j
        = D.weight i * ∑ j, |slackRemainder D.input D.base (T.pivots ν) D.pivotValue
        D.posColumns (T.nodeColumns ν) i j| / D.weight j + ρ i := by
      simp only [hρ, ← mul_add, ← Finset.sum_add_distrib, Matrix.add_apply]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    linarith
  have key := h (A ⊕ B) D.Pos T.Column D.input D.base (T.pivots ν) D.pivotValue D.weight
    (fun i => D.radius i - ρ i) D.posColumns (T.nodeColumns ν) hD.input_symm hD.base_symm
    hD.weight_pos hr x
  have e1 : ∀ g : A ⊕ B → ℝ,
      quadValue (D.base - pivotDiagonal (Finset.univ \ T.pivots ν) g) x
        = quadValue D.base x - ∑ j ∈ Finset.univ \ T.pivots ν, g j * x j ^ 2 := fun g => by
    rw [quadValue_sub', quadValue_pivotDiagonal]
  have hf := hD.front_upper x
  rw [e1] at key hf
  have hin := hD.input_lower x
  have hB : quadValue E (fun i => |x i|) + quadValue F (fun i => |x i|) ≤ ∑ i, ρ i * x i ^ 2 := by
    rw [← quadValue_add']
    have hs : (E + F)ᵀ = E + F := by
      rw [transpose_add, hD.input_error_symm, hD.front_error_symm]
    have := quadValue_le_weightedRows (E + F) D.weight (fun i => |x i|) hD.weight_pos
      (fun i j => add_nonneg (hD.input_error_nonneg i j) (hD.front_error_nonneg i j)) hs
    simpa only [sq_abs] using this
  have hsd : ∑ j ∈ Finset.univ \ T.pivots ν, ρ j * x j ^ 2 + ∑ j ∈ T.pivots ν, ρ j * x j ^ 2
      = ∑ j, ρ j * x j ^ 2 := Finset.sum_sdiff (Finset.subset_univ _)
  have h1 : ∑ j ∈ Finset.univ \ T.pivots ν, (D.radius j - ρ j) * x j ^ 2
      = ∑ j ∈ Finset.univ \ T.pivots ν, D.radius j * x j ^ 2
        - ∑ j ∈ Finset.univ \ T.pivots ν, ρ j * x j ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ j ∈ T.pivots ν, (D.pivotValue j - (D.radius j - ρ j)) * x j ^ 2
      = ∑ j ∈ T.pivots ν, (D.pivotValue j - D.radius j) * x j ^ 2
        + ∑ j ∈ T.pivots ν, ρ j * x j ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2] at key
  have hgain : T.pivotGain ν x ≤ ∑ j ∈ T.pivots ν, (D.pivotValue j - D.radius j) * x j ^ 2 :=
    Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hD.slack_le j hj) (sq_nonneg _)
  have hloss : ∑ c, (∑ i, T.nodeColumns ν i c * x i) ^ 2 = T.columnLoss ν x := by
    unfold SignedTree.columnLoss SignedTree.nodeColumns
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hc
    · simp only [dotProduct]
    · simp
  rw [hloss] at key
  linarith


private theorem complexFormValue_sub' {n : Type*} [Fintype n] (M N : Matrix n n ℂ) (z : n → ℂ) :
    complexFormValue (M - N) z = complexFormValue M z - complexFormValue N z := by
  simp [complexFormValue, sub_mulVec, dotProduct_sub]

private theorem complexFormValue_complexDiagonal {n : Type*} [Fintype n] [DecidableEq n]
    (P : Finset n) (g : n → ℝ) (z : n → ℂ) :
    complexFormValue (complexDiagonal P g) z = ∑ j ∈ P, g j * ‖z j‖ ^ 2 := by
  have hd : complexDiagonal P g = diagonal (fun j => (((if j ∈ P then g j else 0 : ℝ)) : ℂ)) := by
    unfold complexDiagonal pivotDiagonal
    rw [Matrix.diagonal_map (by simp)]
  have hterm : ∀ j, (star (z j) * ((((if j ∈ P then g j else 0 : ℝ)) : ℂ) * z j)).re
      = (if j ∈ P then g j else 0) * ‖z j‖ ^ 2 := fun j => by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hd]
  simp only [complexFormValue, mulVec_diagonal, dotProduct, Complex.re_sum, Pi.star_apply, hterm]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ P)]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h0 : ∑ j ∈ Finset.univ.filter (fun j => j ∉ P), (if j ∈ P then g j else 0) * ‖z j‖ ^ 2 = 0 :=
    Finset.sum_eq_zero fun j hj => by simp [(Finset.mem_filter.1 hj).2]
  rw [h0, add_zero]
  exact Finset.sum_congr rfl fun j hj => by simp [hj]

open Classical in
theorem complexNodeEnclosureBound_of_parts (h₁ : ComplexNodeRealBound)
    (h₂ : RealRestrictionValue) (h₃ : CoordinateSlack) : ComplexNodeEnclosureBound := by
  intro A B _ _ T ν D E F hD x
  letI := T.columnFintype
  letI := D.indexFintype
  letI := D.posFintype
  letI := D.negFintype
  have hf := hD.front_upper x
  have hin := hD.input_lower x
  set z : D.Index → ℂ := D.coords.matrix *ᵥ ofRealVec x with hz
  set ρ : D.Index → ℝ := fun i => D.weight i * ∑ j, (E + F) i j / D.weight j with hρ
  have hr : ∀ i, D.weight i * ∑ j, ‖complexSlackRemainder D.input D.base D.pivot D.pivotValue
      D.posColumns D.negColumns i j‖ / D.weight j ≤ D.radius i - ρ i := by
    intro i
    have hb := hD.row_bound i
    have hsplit : D.weight i * ∑ j, (‖complexSlackRemainder D.input D.base D.pivot D.pivotValue
        D.posColumns D.negColumns i j‖ + E i j + F i j) / D.weight j
        = D.weight i * ∑ j, ‖complexSlackRemainder D.input D.base D.pivot D.pivotValue
        D.posColumns D.negColumns i j‖ / D.weight j + ρ i := by
      simp only [hρ, ← mul_add, ← Finset.sum_add_distrib, Matrix.add_apply]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    linarith
  have key := h₁ D.Index (A ⊕ B) D.Pos D.Neg D.coords D.factor D.input D.base D.pivot D.pivotValue
    D.weight (fun i => D.radius i - ρ i) D.posColumns D.negColumns hD.coordinates
    hD.factor_nonneg hD.input_self_adjoint hD.base_self_adjoint hD.weight_pos hr x
  have hsmul : ∀ N : Matrix (A ⊕ B) (A ⊕ B) ℝ, quadValue (D.factor • N) x = D.factor * quadValue N x := by
    intro N
    simp only [quadValue, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have e1 : ∀ g : D.Index → ℝ,
      quadValue (D.factor • realRestriction D.coords.matrix
        (D.base - complexDiagonal (Finset.univ \ D.pivot) g)) x
        = D.factor * complexFormValue D.base z - D.factor * ∑ j ∈ Finset.univ \ D.pivot, g j * ‖z j‖ ^ 2 := by
    intro g
    rw [hsmul, h₂, complexFormValue_sub', complexFormValue_complexDiagonal, mul_sub]
  have e2 : ∀ s : D.Index → ℝ,
      ∑ k ∈ D.coords.pivotImage D.pivot, D.factor * D.coords.slackOn D.pivot s k * x k ^ 2
        = D.factor * ∑ j ∈ D.pivot, s j * ‖z j‖ ^ 2 := by
    intro s
    rw [h₃ D.Index (A ⊕ B) D.coords D.pivot s x hD.coordinates, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1] at key hf
  rw [e2] at key
  have hB : D.factor * quadValue E (fun i => ‖z i‖) + D.factor * quadValue F (fun i => ‖z i‖)
      ≤ D.factor * ∑ i, ρ i * ‖z i‖ ^ 2 := by
    rw [← mul_add, ← quadValue_add']
    have hs : (E + F)ᵀ = E + F := by
      rw [transpose_add, hD.input_error_symm, hD.front_error_symm]
    exact mul_le_mul_of_nonneg_left (quadValue_le_weightedRows (E + F) D.weight (fun i => ‖z i‖)
      hD.weight_pos (fun i j => add_nonneg (hD.input_error_nonneg i j) (hD.front_error_nonneg i j))
      hs) hD.factor_nonneg
  have hsd : D.factor * ∑ j ∈ Finset.univ \ D.pivot, ρ j * ‖z j‖ ^ 2 + D.factor * ∑ j ∈ D.pivot, ρ j * ‖z j‖ ^ 2
      = D.factor * ∑ j, ρ j * ‖z j‖ ^ 2 := by
    rw [← mul_add, Finset.sum_sdiff (Finset.subset_univ _)]
  have h1 : D.factor * ∑ j ∈ Finset.univ \ D.pivot, (D.radius j - ρ j) * ‖z j‖ ^ 2
      = D.factor * ∑ j ∈ Finset.univ \ D.pivot, D.radius j * ‖z j‖ ^ 2
        - D.factor * ∑ j ∈ Finset.univ \ D.pivot, ρ j * ‖z j‖ ^ 2 := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : D.factor * ∑ j ∈ D.pivot, (D.pivotValue j - (D.radius j - ρ j)) * ‖z j‖ ^ 2
      = D.factor * ∑ j ∈ D.pivot, (D.pivotValue j - D.radius j) * ‖z j‖ ^ 2
        + D.factor * ∑ j ∈ D.pivot, ρ j * ‖z j‖ ^ 2 := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2] at key
  have hgain : T.pivotGain ν x ≤ ∑ k ∈ T.pivots ν,
      D.factor * D.coords.slackOn D.pivot (fun j => D.pivotValue j - D.radius j) k * x k ^ 2 :=
    Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hD.slack_le k hk) (sq_nonneg _)
  rw [hD.pivots_eq, e2] at hgain
  obtain ⟨e, he, hec⟩ := hD.columns
  have hloss : ∑ c : D.Neg ⊕ D.Neg,
      (realColumns D.coords.matrix D.factor D.negColumns c ⬝ᵥ x) ^ 2 ≤ T.columnLoss ν x := by
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
  linarith

theorem stateEnclosureCertificateNonneg_of_holds (h₁ : SignedCertificateTerminal)
    (h₂ : SignedSlackBound) (h₃ : ComplexNodeRealBound) (h₄ : RealRestrictionValue)
    (h₅ : CoordinateSlack) : StateEnclosureCertificateNonneg :=
  stateEnclosureCertificateNonneg_of_parts h₁ (realNodeEnclosureBound_of_slackBound h₂)
    (complexNodeEnclosureBound_of_parts h₃ h₄ h₅)

end Breakdown.CertCell.Certificate
