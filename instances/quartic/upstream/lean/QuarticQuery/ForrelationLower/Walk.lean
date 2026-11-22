module

public import QuarticQuery.ForrelationLower.Stein
public import QuarticQuery.ForrelationLower.TreeGrowth

/-!
# The hard distribution and the Stein walk

Blueprint lemmas W1–W3. `wv s u` is the bias vector: block `0` is `s · X_0`, block `r` is
`Y_{r-1} ⊙ X_r`, block `l` is `Y_{l-1}`, with `X_r = φ(U_r)`, `Y_r = φ(H U_r)`. Stein in
`U_j(a)` moves one index one block to the right. Nothing branches, so only level `l+1`
occurs.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open MeasureTheory Finset

namespace QuarticQuery.ForrelationLower

variable {n : Type} [Fintype n] [DecidableEq n] {l : ℕ} (H : Matrix n n ℝ)

/-- The hidden Gaussian coordinates. -/
abbrev PC (l : ℕ) (n : Type) := Fin l × n
/-- The coordinates of the Forrelation input. -/
abbrev BC (l : ℕ) (n : Type) := Fin (l + 1) × n

/-- `U_r(a)`. -/
noncomputable def Uc (u : PC l n → ℝ) (r : ℕ) (a : n) : ℝ :=
  if h : r < l then u (⟨r, h⟩, a) else 0

/-- `V_r(b) = (H U_r)(b)`. -/
noncomputable def Vc (u : PC l n → ℝ) (r : ℕ) (b : n) : ℝ := ∑ i, H b i * Uc u r i

/-- `X_r(a)`, and `1` past the last pair. -/
noncomputable def Xf (u : PC l n → ℝ) (r : ℕ) (a : n) : ℝ :=
  if r < l then phiS (Uc u r a) else 1

/-- `Y_{r-1}(a)`, and `1` at block `0`. -/
noncomputable def Yf (u : PC l n → ℝ) (r : ℕ) (a : n) : ℝ :=
  if r = 0 then 1 else phiS (Vc H u (r - 1) a)

/-- The scale on block `0`. -/
noncomputable def Sf (s : ℝ) (c : BC l n) : ℝ := if c.1.val = 0 then s else 1

/-- The bias vector. -/
noncomputable def wv (s : ℝ) (u : PC l n → ℝ) (c : BC l n) : ℝ :=
  Sf s c * (Yf H u c.1 c.2 * Xf u c.1 c.2)

/-- The coordinate in block `r`. -/
def cn (r : ℕ) (b : n) : BC l n := (⟨min r l, by omega⟩, b)

/-- Support for blueprint W1–W3. -/
theorem cn_val_of_le {r : ℕ} (h : r ≤ l) (b : n) : (cn r b : BC l n).1.val = r := by
  simp [cn, h]

/-! ## Regularity -/

/-- Continuous and bounded. -/
def BCf (f : (PC l n → ℝ) → ℝ) : Prop := Continuous f ∧ ∃ C, ∀ u, |f u| ≤ C

/-- Support for blueprint W1–W3. -/
theorem BCf.const (c : ℝ) : BCf (l := l) (n := n) fun _ => c := ⟨continuous_const, |c|, fun _ => le_rfl⟩

/-- Support for blueprint W1–W3. -/
theorem BCf.mul {f g : (PC l n → ℝ) → ℝ} (hf : BCf f) (hg : BCf g) : BCf fun u => f u * g u := by
  obtain ⟨cf, Cf, hCf⟩ := hf
  obtain ⟨cg, Cg, hCg⟩ := hg
  refine ⟨cf.mul cg, Cf * Cg, fun u => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hCf u) (hCg u) (abs_nonneg _) ((abs_nonneg _).trans (hCf u))

/-- Support for blueprint W1–W3. -/
theorem BCf.sum {J : Type} (s : Finset J) {f : J → (PC l n → ℝ) → ℝ} (hf : ∀ j ∈ s, BCf (f j)) :
    BCf fun u => ∑ j ∈ s, f j u := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BCf.const (l := l) (n := n) 0
  | insert a s ha ih =>
    simp only [sum_insert ha]
    obtain ⟨c1, C1, h1⟩ := hf a (mem_insert_self a s)
    obtain ⟨c2, C2, h2⟩ := ih fun j hj => hf j (mem_insert_of_mem hj)
    exact ⟨c1.add c2, C1 + C2, fun u => (abs_add_le _ _).trans (add_le_add (h1 u) (h2 u))⟩

/-- Support for blueprint W1–W3. -/
theorem BCf.integrable {f : (PC l n → ℝ) → ℝ} (hf : BCf f) : Integrable f (gP (PC l n)) := by
  obtain ⟨c, C, h⟩ := hf
  exact Integrable.of_bound c.aestronglyMeasurable C (.of_forall fun u => by simpa using h u)

/-- Support for blueprint W1–W3. -/
theorem continuous_Uc (r : ℕ) (a : n) : Continuous fun u : PC l n → ℝ => Uc u r a := by
  unfold Uc
  by_cases h : r < l
  · simpa [h] using continuous_apply _
  · simpa [h] using continuous_const

/-- Support for blueprint W1–W3. -/
theorem continuous_Vc (r : ℕ) (b : n) : Continuous fun u : PC l n → ℝ => Vc H u r b := by
  unfold Vc
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_Uc r i)

/-- Support for blueprint W1–W3. -/
theorem continuous_phiS : Continuous phiS :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_phiS x).continuousAt

/-- Support for blueprint W1–W3. -/
theorem abs_phiS_le_one (x : ℝ) : |phiS x| ≤ 1 := (abs_phiS_le x).trans (by norm_num)

/-- Support for blueprint W1–W3. -/
theorem bcf_Xf (r : ℕ) (a : n) : BCf fun u : PC l n → ℝ => Xf u r a := by
  unfold Xf
  by_cases h : r < l
  · simp only [h, if_true]
    exact ⟨continuous_phiS.comp (continuous_Uc r a), 1, fun u => abs_phiS_le_one _⟩
  · simpa [h] using BCf.const (l := l) (n := n) 1

/-- Support for blueprint W1–W3. -/
theorem bcf_Yf (r : ℕ) (a : n) : BCf fun u : PC l n → ℝ => Yf H u r a := by
  unfold Yf
  by_cases h : r = 0
  · simpa [h] using BCf.const (l := l) (n := n) 1
  · simp only [h, if_false]
    exact ⟨continuous_phiS.comp (continuous_Vc H _ a), 1, fun u => abs_phiS_le_one _⟩

/-- Support for blueprint W1–W3. -/
theorem abs_Xf_le (u : PC l n → ℝ) (r : ℕ) (a : n) : |Xf u r a| ≤ 1 := by
  unfold Xf; split_ifs
  · exact abs_phiS_le_one _
  · simp

/-- Support for blueprint W1–W3. -/
theorem abs_Yf_le (u : PC l n → ℝ) (r : ℕ) (a : n) : |Yf H u r a| ≤ 1 := by
  unfold Yf; split_ifs
  · simp
  · exact abs_phiS_le_one _

/-- Support for blueprint W1–W3. -/
theorem abs_wv_le {s : ℝ} (hs : |s| ≤ 1) (u : PC l n → ℝ) (c : BC l n) : |wv H s u c| ≤ 1 := by
  unfold wv
  have h1 : |Sf s c| ≤ 1 := by unfold Sf; split_ifs <;> simp [hs]
  rw [abs_mul, abs_mul]
  have h2 := abs_Xf_le u c.1 c.2
  have h3 := abs_Yf_le H u c.1 c.2
  calc _ ≤ (1 : ℝ) * (1 * 1) := by gcongr
    _ = 1 := by norm_num

/-- The bias stays in `[-1/2, 1/2]`. -/
theorem abs_wv_le_half (hl : 1 ≤ l) {s : ℝ} (hs : |s| ≤ 1) (u : PC l n → ℝ) (c : BC l n) :
    |wv H s u c| ≤ 1 / 2 := by
  unfold wv
  have h1 : |Sf s c| ≤ 1 := by unfold Sf; split_ifs <;> simp [hs]
  have key : |Yf H u c.1 c.2| * |Xf u c.1 c.2| ≤ 1 / 2 := by
    by_cases h : c.1.val < l
    · have hx : |Xf u c.1 c.2| ≤ 1 / 2 := by
        unfold Xf; rw [if_pos h]; exact abs_phiS_le _
      have := abs_Yf_le H u c.1 c.2
      nlinarith [abs_nonneg (Yf H u c.1 c.2), abs_nonneg (Xf u c.1 c.2)]
    · have h0 : c.1.val ≠ 0 := by omega
      have hy : |Yf H u c.1 c.2| ≤ 1 / 2 := by
        unfold Yf; rw [if_neg h0]; exact abs_phiS_le _
      have := abs_Xf_le u c.1 c.2
      nlinarith [abs_nonneg (Yf H u c.1 c.2), abs_nonneg (Xf u c.1 c.2)]
  rw [abs_mul, abs_mul]
  nlinarith [abs_nonneg (Sf s c), abs_nonneg (Yf H u c.1 c.2), abs_nonneg (Xf u c.1 c.2),
    mul_nonneg (abs_nonneg (Yf H u c.1 c.2)) (abs_nonneg (Xf u c.1 c.2))]

/-- Support for blueprint W1–W3. -/
theorem continuous_wv (s : ℝ) (c : BC l n) : Continuous fun u : PC l n → ℝ => wv H s u c :=
  continuous_const.mul ((bcf_Yf H _ _).1.mul (bcf_Xf _ _).1)

/-- Support for blueprint W1–W3. -/
theorem continuous_ext {ι : Type} [Fintype ι] [DecidableEq ι] (g : (ι → Bool) → ℝ) :
    Continuous (ext g) := by
  unfold ext bw piB
  fun_prop

/-- Support for blueprint W1–W3. -/
theorem bcf_ext (g : (BC l n → Bool) → ℝ) {s : ℝ} (hs : |s| ≤ 1) :
    BCf fun u : PC l n → ℝ => ext g (wv H s u) := by
  obtain ⟨B, hB⟩ : ∃ B, ∀ z, |g z| ≤ B :=
    ⟨∑ z, |g z|, fun z => single_le_sum (f := fun z => |g z|) (fun _ _ => abs_nonneg _) (mem_univ z)⟩
  exact ⟨(continuous_ext g).comp (continuous_pi fun c => continuous_wv H s c), B,
    fun u => abs_ext_le hB fun c => abs_wv_le H hs u c⟩

/-! ## W1. The derivative in one hidden coordinate -/

variable {j : ℕ} (hj : j < l) (a : n)

/-- Support for blueprint W1–W3. -/
theorem Uc_update (u : PC l n → ℝ) (t : ℝ) (r : ℕ) (i : n) :
    Uc (Function.update u (⟨j, hj⟩, a) t) r i = if r = j ∧ i = a then t else Uc u r i := by
  unfold Uc
  by_cases hr : r < l
  · simp only [hr, dif_pos]
    by_cases h : r = j ∧ i = a
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [if_neg h, Function.update_of_ne]
      intro h'
      apply h
      have h1 := congrArg (fun p => p.1.val) h'
      have h2 := congrArg (fun p => p.2) h'
      exact ⟨h1, h2⟩
  · have : ¬ (r = j ∧ i = a) := fun h => hr (h.1 ▸ hj)
    simp [hr, this]

/-- Support for blueprint W1–W3. -/
theorem hasDerivAt_Uc (u : PC l n → ℝ) (t : ℝ) (r : ℕ) (i : n) :
    HasDerivAt (fun t => Uc (Function.update u (⟨j, hj⟩, a) t) r i)
      (if r = j ∧ i = a then 1 else 0) t := by
  simp only [Uc_update]
  by_cases h : r = j ∧ i = a
  · simpa [h] using hasDerivAt_id' t
  · simpa [h] using hasDerivAt_const t (Uc u r i)

/-- Support for blueprint W1–W3. -/
theorem hasDerivAt_Vc (u : PC l n → ℝ) (t : ℝ) (r : ℕ) (b : n) :
    HasDerivAt (fun t => Vc H (Function.update u (⟨j, hj⟩, a) t) r b)
      (if r = j then H b a else 0) t := by
  unfold Vc
  have := HasDerivAt.fun_sum (u := univ) fun i (_ : i ∈ univ) =>
    (hasDerivAt_Uc hj a u t r i).const_mul (H b i)
  convert this using 1
  by_cases h : r = j
  · simp [h]
  · simp [h]

/-- The derivative of `X` along the coordinate. -/
noncomputable def dX (j : ℕ) (a : n) (u : PC l n → ℝ) (r : ℕ) (i : n) : ℝ :=
  dphi (Uc u r i) * if r = j ∧ i = a then 1 else 0

/-- The derivative of `Y` along the coordinate. -/
noncomputable def dY (j : ℕ) (a : n) (u : PC l n → ℝ) (r : ℕ) (i : n) : ℝ :=
  if r = 0 then 0 else dphi (Vc H u (r - 1) i) * if r - 1 = j then H i a else 0

/-- Support for blueprint W1–W3. -/
theorem hasDerivAt_Xf (u : PC l n → ℝ) (t : ℝ) (r : ℕ) (i : n) :
    HasDerivAt (fun t => Xf (Function.update u (⟨j, hj⟩, a) t) r i)
      (dX j a (Function.update u (⟨j, hj⟩, a) t) r i) t := by
  unfold Xf dX
  by_cases hr : r < l
  · simp only [hr, if_true]
    exact (hasDerivAt_phiS _).comp t (hasDerivAt_Uc hj a u t r i)
  · have : ¬ (r = j ∧ i = a) := fun h => hr (h.1 ▸ hj)
    simpa [hr, this] using hasDerivAt_const t (1 : ℝ)

/-- Support for blueprint W1–W3. -/
theorem hasDerivAt_Yf (u : PC l n → ℝ) (t : ℝ) (r : ℕ) (i : n) :
    HasDerivAt (fun t => Yf H (Function.update u (⟨j, hj⟩, a) t) r i)
      (dY H j a (Function.update u (⟨j, hj⟩, a) t) r i) t := by
  unfold Yf dY
  by_cases hr : r = 0
  · simpa [hr] using hasDerivAt_const t (1 : ℝ)
  · simp only [hr, if_false]
    exact (hasDerivAt_phiS _).comp t (hasDerivAt_Vc H hj a u t (r - 1) i)

/-- Support for blueprint W1–W3. -/
theorem hasDerivAt_wv (s : ℝ) (u : PC l n → ℝ) (t : ℝ) (c : BC l n) :
    HasDerivAt (fun t => wv H s (Function.update u (⟨j, hj⟩, a) t) c)
      (Sf s c * (dY H j a (Function.update u (⟨j, hj⟩, a) t) c.1 c.2 *
          Xf (Function.update u (⟨j, hj⟩, a) t) c.1 c.2 +
        Yf H (Function.update u (⟨j, hj⟩, a) t) c.1 c.2 *
          dX j a (Function.update u (⟨j, hj⟩, a) t) c.1 c.2)) t :=
  ((hasDerivAt_Yf H hj a u t _ _).fun_mul (hasDerivAt_Xf hj a u t _ _)).const_mul _

include hj in
/-- The chain rule collapses to one block. -/
theorem sum_dw_eq (s : ℝ) (u : PC l n → ℝ) (E : BC l n → ℝ) (hE : E (cn j a) = 0) :
    ∑ c : BC l n, (Sf s c * (dY H j a u c.1 c.2 * Xf u c.1 c.2 +
        Yf H u c.1 c.2 * dX j a u c.1 c.2)) * E c =
      ∑ b, H b a * dphi (Vc H u j b) * Xf u (j + 1) b * E (cn (j + 1) b) := by
  have hj' : j + 1 < l + 1 := by omega
  have hcn : ∀ b : n, (cn (j + 1) b : BC l n) = (⟨j + 1, hj'⟩, b) := fun b => by
    simp only [cn]
    congr 2
    omega
  have hcj : (cn j a : BC l n) = (⟨j, by omega⟩, a) := by
    simp only [cn]
    congr 2
    omega
  simp only [add_mul, mul_add, sum_add_distrib]
  have h2 : ∑ c : BC l n, (Sf s c * (Yf H u c.1 c.2 * dX j a u c.1 c.2)) * E c = 0 := by
    refine sum_eq_zero fun c _ => ?_
    by_cases h : c.1.val = j ∧ c.2 = a
    · have : c = cn j a := by
        rw [hcj]
        exact Prod.ext (Fin.ext h.1) h.2
      rw [this, hE, mul_zero]
    · simp [dX, h]
  rw [h2, add_zero, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (⟨j + 1, hj'⟩ : Fin (l + 1))]
  · refine sum_congr rfl fun b _ => ?_
    have hS : Sf s ((⟨j + 1, hj'⟩ : Fin (l + 1)), b) = 1 := by simp [Sf]
    have hD : dY H j a u (j + 1) b = dphi (Vc H u j b) * H b a := by simp [dY]
    show (Sf s (⟨j + 1, hj'⟩, b) * (dY H j a u (j + 1) b * Xf u (j + 1) b)) *
      E (⟨j + 1, hj'⟩, b) = _
    rw [hS, hD, hcn b]
    ring
  · intro r _ hr
    refine sum_eq_zero fun b _ => ?_
    have : dY H j a u r.val b = 0 := by
      unfold dY
      by_cases h0 : r.val = 0
      · simp [h0]
      · have : r.val - 1 ≠ j := fun h => hr (Fin.ext (by simp; omega))
        simp [h0, this]
    simp [this]
  · simp

/-! ## W2. The recursive integrand -/

/-- Dependence on the pairs before `j` only. -/
def EarlyOnly (j : ℕ) (θ : (PC l n → ℝ) → ℝ) : Prop :=
  ∀ (u : PC l n → ℝ) (p : PC l n) (t : ℝ), j ≤ p.1.val → θ (Function.update u p t) = θ u

/-- The resolved integrand: one `H`, one `Ψ` and one `φ'` per remaining pair. -/
noncomputable def Int (s : ℝ) : ℕ → ℕ → n → ((BC l n → Bool) → ℝ) → (PC l n → ℝ) → ℝ
  | 0, _, _, g, u => ext g (wv H s u)
  | e + 1, j, a, g, u => ∑ b, H b a * psiS (Uc u j a) * dphi (Vc H u j b) *
      Int s e (j + 1) b (D (cn (j + 1) b) g) u

/-- Support for blueprint W1–W3. -/
theorem Uc_update_of_ne (u : PC l n → ℝ) (p : PC l n) (t : ℝ) {r : ℕ} (hr : r ≠ p.1.val) (i : n) :
    Uc (Function.update u p t) r i = Uc u r i := by
  unfold Uc
  by_cases h : r < l
  · simp only [h, dif_pos]
    rw [Function.update_of_ne]
    intro h'
    exact hr (congrArg (fun q : PC l n => q.1.val) h')
  · simp [h]

/-- Support for blueprint W1–W3. -/
theorem Vc_update_of_ne (u : PC l n → ℝ) (p : PC l n) (t : ℝ) {r : ℕ} (hr : r ≠ p.1.val) (i : n) :
    Vc H (Function.update u p t) r i = Vc H u r i := by
  unfold Vc
  simp only [Uc_update_of_ne u p t hr]

/-- Support for blueprint W1–W3. -/
theorem bcf_psiU (j : ℕ) (a : n) : BCf fun u : PC l n → ℝ => psiS (Uc u j a) :=
  ⟨continuous_psiS.comp (continuous_Uc j a), 1, fun u => by
    rw [abs_of_pos (psiS_pos _)]; exact psiS_le _⟩

/-- Support for blueprint W1–W3. -/
theorem bcf_dphiV (j : ℕ) (b : n) : BCf fun u : PC l n → ℝ => dphi (Vc H u j b) :=
  ⟨continuous_dphi.comp (continuous_Vc H j b), 3, fun u => by
    rw [abs_of_pos (dphi_pos _)]; exact dphi_le _⟩

/-- Support for blueprint W1–W3. -/
theorem bcf_Int {s : ℝ} (hs : |s| ≤ 1) (e : ℕ) : ∀ (j : ℕ) (a : n) (g : (BC l n → Bool) → ℝ),
    BCf (Int H s e j a g) := by
  induction e with
  | zero => exact fun j a g => bcf_ext H g hs
  | succ e ih =>
    intro j a g
    exact BCf.sum _ fun b _ =>
      (((BCf.const _).mul (bcf_psiU j a)).mul (bcf_dphiV H j b)).mul (ih _ _ _)

/-- W2. One walk: `E[θ X_j(a) ext g] = E[θ Int]` for `g` a derivative at `(j, a)`. -/
theorem integral_walk {s : ℝ} (hs : |s| ≤ 1) (e : ℕ) : ∀ (j : ℕ), j + e = l → ∀ (a : n)
    (g₀ : (BC l n → Bool) → ℝ) (θ : (PC l n → ℝ) → ℝ), BCf θ → EarlyOnly j θ →
    ∫ u, θ u * (Xf u j a * ext (D (cn j a) g₀) (wv H s u)) ∂(gP (PC l n)) =
      ∫ u, θ u * Int H s e j a (D (cn j a) g₀) u ∂(gP (PC l n)) := by
  induction e with
  | zero =>
    intro j hj a g₀ θ _ _
    have : ¬ j < l := by omega
    simp [Int, Xf, this]
  | succ e ih =>
    intro j hje a g₀ θ hθ hearly
    have hj : j < l := by omega
    set g := D (cn j a) g₀ with hg
    set p : PC l n := (⟨j, hj⟩, a) with hp
    have hup : ∀ u : PC l n → ℝ, Uc u j a = u p := fun u => by simp [Uc, hj, hp]
    have hXp : ∀ u : PC l n → ℝ, Xf u j a = phiS (u p) := fun u => by simp [Xf, hj, hup]
    let E : (PC l n → ℝ) → BC l n → ℝ := fun u c => ext (D c g) (wv H s u)
    have hE0 : ∀ u, E u (cn j a) = 0 := fun u => by
      simp only [E, hg, D_D]
      exact ext_const 0 _
    let G : (PC l n → ℝ) → ℝ := fun u => θ u * ext g (wv H s u)
    let G' : (PC l n → ℝ) → ℝ := fun u => θ u *
      ∑ b, H b a * dphi (Vc H u j b) * Xf u (j + 1) b * E u (cn (j + 1) b)
    have hBCG : BCf G := hθ.mul (bcf_ext H g hs)
    have hBCG' : BCf G' := hθ.mul (BCf.sum _ fun b _ =>
      ((((BCf.const _).mul (bcf_dphiV H j b)).mul (bcf_Xf _ b))).mul (bcf_ext H _ hs))
    obtain ⟨hc, C, hC⟩ := hBCG
    obtain ⟨hc', C', hC'⟩ := hBCG'
    have hd : ∀ u t, HasDerivAt (fun r => G (Function.update u p r)) (G' (Function.update u p t)) t := by
      intro u t
      have hθu : ∀ r, θ (Function.update u p r) = θ u := fun r => hearly u p r le_rfl
      simp only [G, G', hθu]
      refine HasDerivAt.const_mul _ ?_
      have h1 := hasDerivAt_ext g (fun c => hasDerivAt_wv H hj a s u t c)
      convert h1 using 1
      exact (sum_dw_eq H hj a s (Function.update u p t) (E (Function.update u p t))
        (hE0 _)).symm
    have hS := stein_pi p hc hc' hC hC' hd
    have e1 : ∫ u, θ u * (Xf u j a * ext g (wv H s u)) ∂(gP (PC l n)) =
        ∫ u, phiS (u p) * G u ∂(gP (PC l n)) :=
      integral_congr_ae (.of_forall fun u => by simp only [G, hXp]; ring)
    let θb : n → (PC l n → ℝ) → ℝ := fun b u =>
      θ u * (H b a * psiS (Uc u j a) * dphi (Vc H u j b))
    have hθb : ∀ b, BCf (θb b) := fun b =>
      hθ.mul (((BCf.const _).mul (bcf_psiU j a)).mul (bcf_dphiV H j b))
    have hearlyb : ∀ b, EarlyOnly (j + 1) (θb b) := by
      intro b u q t hq
      have hne : j ≠ q.1.val := by omega
      simp only [θb, Uc_update_of_ne u q t hne, Vc_update_of_ne H u q t hne,
        hearly u q t (by omega)]
    have hit : ∀ b, BCf fun u => θb b u * Int H s e (j + 1) b (D (cn (j + 1) b) g) u :=
      fun b => (hθb b).mul (bcf_Int H hs e _ _ _)
    calc _ = ∫ u, phiS (u p) * G u ∂(gP (PC l n)) := e1
      _ = ∫ u, psiS (u p) * G' u ∂(gP (PC l n)) := hS
      _ = ∑ b, ∫ u, θb b u * (Xf u (j + 1) b * ext (D (cn (j + 1) b) g) (wv H s u))
            ∂(gP (PC l n)) := by
          rw [← integral_finsetSum _ fun b _ =>
            ((hθb b).mul ((bcf_Xf _ b).mul (bcf_ext H _ hs))).integrable]
          refine integral_congr_ae (.of_forall fun u => ?_)
          simp only [G', E, θb, hup, mul_sum]
          exact sum_congr rfl fun b _ => by ring
      _ = ∑ b, ∫ u, θb b u * Int H s e (j + 1) b (D (cn (j + 1) b) g) u ∂(gP (PC l n)) :=
          sum_congr rfl fun b _ => ih (j + 1) (by omega) b g (θb b) (hθb b) (hearlyb b)
      _ = _ := by
          rw [← integral_finsetSum _ fun b _ => (hit b).integrable]
          refine integral_congr_ae (.of_forall fun u => ?_)
          simp only [Int, θb, mul_sum]
          exact sum_congr rfl fun b _ => by ring

/-! ## W3. The identity -/

/-- Support for blueprint W1–W3. -/
theorem hasDerivAt_ext_s (g : (BC l n → Bool) → ℝ) (u : PC l n → ℝ) (s : ℝ) (hl : 0 < l) :
    HasDerivAt (fun s => ext g (wv H s u))
      (∑ a, Xf u 0 a * ext (D (cn 0 a) g) (wv H s u)) s := by
  have h : ∀ c : BC l n, HasDerivAt (fun s => wv H s u c)
      ((if c.1.val = 0 then 1 else 0) * (Yf H u c.1 c.2 * Xf u c.1 c.2)) s := by
    intro c
    unfold wv Sf
    by_cases h0 : c.1.val = 0
    · simpa [h0] using (hasDerivAt_id' s).mul_const (Yf H u c.1 c.2 * Xf u c.1 c.2)
    · simpa [h0] using hasDerivAt_const s (Yf H u c.1 c.2 * Xf u c.1 c.2)
  have h1 := hasDerivAt_ext g h
  convert h1 using 1
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (0 : Fin (l + 1))]
  · refine sum_congr rfl fun a _ => ?_
    have e : (cn 0 a : BC l n) = (0, a) := by
      simp only [cn]
      congr 1
    simp [Yf, e]
  · intro r _ hr
    refine sum_eq_zero fun a _ => ?_
    have : r.val ≠ 0 := fun h => hr (Fin.ext h)
    simp [this]
  · simp

/-- W3. The bias-scaling path and the Stein walk: a mean-value form of (★). -/
theorem exists_identity (hl : 0 < l) (g : (BC l n → Bool) → ℝ) :
    ∃ s ∈ Set.Ioo (0 : ℝ) 1,
      ∫ u, ext g (wv H 1 u) ∂(gP (PC l n)) - ∫ u, ext g (wv H 0 u) ∂(gP (PC l n)) =
        ∑ a, ∫ u, Int H s l 0 a (D (cn 0 a) g) u ∂(gP (PC l n)) := by
  obtain ⟨B, hB⟩ : ∃ B, ∀ z, |g z| ≤ B :=
    ⟨∑ z, |g z|, fun z => single_le_sum (f := fun z => |g z|) (fun _ _ => abs_nonneg _) (mem_univ z)⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB fun _ => false)
  set h : ℝ → ℝ := fun s => ∫ u, ext g (wv H s u) ∂(gP (PC l n)) with hh
  have hbd : ∀ s u, |s| ≤ 1 → ‖ext g (wv H s u)‖ ≤ B := fun s u hs =>
    abs_ext_le hB fun c => abs_wv_le H hs u c
  have hcont : ContinuousOn h (Set.Icc 0 1) := by
    refine continuousOn_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const _) ?_
    · intro s hs
      exact ((continuous_ext g).comp (continuous_pi fun c => continuous_wv H s c)).aestronglyMeasurable
    · intro s hs
      exact .of_forall fun u => hbd s u (abs_le.mpr ⟨by linarith [hs.1], hs.2⟩)
    · refine .of_forall fun u => ?_
      refine Continuous.continuousOn ?_
      exact continuous_iff_continuousAt.mpr fun s =>
        (hasDerivAt_ext_s H g u s hl).continuousAt
  have hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt h
      (∑ a, ∫ u, Int H s l 0 a (D (cn 0 a) g) u ∂(gP (PC l n))) s := by
    intro s hs
    have hs1 : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2.le⟩
    have hBd : ∀ s' ∈ Set.Ioo (0 : ℝ) 1, ∀ u : PC l n → ℝ,
        ‖∑ a, Xf u 0 a * ext (D (cn 0 a) g) (wv H s' u)‖ ≤ Fintype.card n * B := by
      intro s' hs' u
      have hs1' : |s'| ≤ 1 := abs_le.mpr ⟨by linarith [hs'.1], hs'.2.le⟩
      calc _ ≤ ∑ _a : n, B := by
            refine (norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_)
            rw [Real.norm_eq_abs, abs_mul]
            have h1 := abs_Xf_le u 0 a
            have h2 : |ext (D (cn 0 a) g) (wv H s' u)| ≤ B :=
              abs_ext_le (abs_D_le hB _) fun c => abs_wv_le H hs1' u c
            nlinarith [abs_nonneg (Xf u 0 a), abs_nonneg (ext (D (cn 0 a) g) (wv H s' u))]
        _ = _ := by simp
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gP (PC l n))
      (F := fun s u => ext g (wv H s u))
      (F' := fun s u => ∑ a, Xf u 0 a * ext (D (cn 0 a) g) (wv H s u))
      (bound := fun _ => Fintype.card n * B) (x₀ := s) (s := Set.Ioo 0 1)
      (Ioo_mem_nhds hs.1 hs.2)
      (.of_forall fun s' => ((continuous_ext g).comp
        (continuous_pi fun c => continuous_wv H s' c)).aestronglyMeasurable)
      (bcf_ext H g hs1).integrable
      (BCf.sum _ fun a _ => (bcf_Xf 0 a).mul (bcf_ext H _ hs1)).1.aestronglyMeasurable
      (.of_forall fun u s' hs' => hBd s' hs' u) (integrable_const _)
      (.of_forall fun u s' _ => hasDerivAt_ext_s H g u s' hl)
    have e : ∫ u, (∑ a, Xf u 0 a * ext (D (cn 0 a) g) (wv H s u)) ∂(gP (PC l n)) =
        ∑ a, ∫ u, Int H s l 0 a (D (cn 0 a) g) u ∂(gP (PC l n)) := by
      rw [integral_finsetSum _ fun a _ => ((bcf_Xf 0 a).mul (bcf_ext H _ hs1)).integrable]
      refine sum_congr rfl fun a _ => ?_
      have := integral_walk H hs1 l 0 (by omega) a g (fun _ => 1) (BCf.const 1) (fun _ _ _ _ => rfl)
      simpa using this
    rw [← e]
    exact this.2
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope h _ (by norm_num : (0 : ℝ) < 1) hcont hderiv
  refine ⟨c, hc, ?_⟩
  rw [hc']
  simp [hh]

/-! ## Paths -/

/-- The list of coordinates visited after block `j`. -/
def plist : (e : ℕ) → ℕ → (Fin e → n) → List (BC l n)
  | 0, _, _ => []
  | e + 1, j, q => cn (j + 1) (q 0) :: plist e (j + 1) (Fin.tail q)

/-- The weight of a path. -/
noncomputable def cf (s : ℝ) : (e : ℕ) → ℕ → n → (Fin e → n) → (PC l n → ℝ) → ℝ
  | 0, _, _, _, _ => 1
  | e + 1, j, a, q, u => H (q 0) a * psiS (Uc u j a) * dphi (Vc H u j (q 0)) *
      cf s e (j + 1) (q 0) (Fin.tail q) u

/-- Support for blueprint W1–W3. -/
theorem sum_fin_succ {α : Type} [Fintype α] (e : ℕ) (f : (Fin (e + 1) → α) → ℝ) :
    ∑ q, f q = ∑ b, ∑ q' : Fin e → α, f (Fin.cons b q') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => α) _ _ fun p => rfl).symm

/-- The integrand as a sum over paths. -/
theorem Int_eq_paths (s : ℝ) (e : ℕ) : ∀ (j : ℕ) (a : n) (g : (BC l n → Bool) → ℝ)
    (u : PC l n → ℝ), Int H s e j a g u =
      ∑ q : Fin e → n, cf H s e j a q u * ext (Dl (plist e j q) g) (wv H s u) := by
  induction e with
  | zero => intro j a g u; simp [Int, cf, plist, Dl]
  | succ e ih =>
    intro j a g u
    rw [sum_fin_succ]
    simp only [Int, ih]
    refine sum_congr rfl fun b _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun q _ => ?_
    simp [cf, plist, Dl, mul_assoc]

/-- Support for blueprint W1–W3. -/
theorem abs_cf_le (s : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (hH : ∀ a b, |H a b| ≤ ε) (e : ℕ) :
    ∀ (j : ℕ) (a : n) (q : Fin e → n) (u : PC l n → ℝ), |cf H s e j a q u| ≤ (3 * ε) ^ e := by
  induction e with
  | zero => intro j a q u; simp [cf]
  | succ e ih =>
    intro j a q u
    simp only [cf]
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (psiS_pos _), abs_of_pos (dphi_pos _), pow_succ']
    have h1 := hH (q 0) a
    have h2 := psiS_le (Uc u j a)
    have h3 := dphi_le (Vc H u j (q 0))
    have h4 := ih (j + 1) (q 0) (Fin.tail q) u
    have h5 := psiS_pos (Uc u j a)
    have h6 := dphi_pos (Vc H u j (q 0))
    calc _ ≤ ε * 1 * 3 * (3 * ε) ^ e := by gcongr
      _ = _ := by ring

/-- Each edge contributes at most `3ε/16`, with the scalar factors grouped together. -/
theorem abs_cf_le_sharp (s : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hH : ∀ a b, |H a b| ≤ ε) (e : ℕ) :
    ∀ (j : ℕ) (a : n) (q : Fin e → n) (u : PC l n → ℝ),
      |cf H s e j a q u| ≤ ((3 / 16 : ℝ) * ε) ^ e := by
  induction e with
  | zero => intro j a q u; simp [cf]
  | succ e ih =>
    intro j a q u
    simp only [cf]
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (psiS_pos _),
      abs_of_pos (dphi_pos _), pow_succ']
    calc _ = |H (q 0) a| * (psiS (Uc u j a) * dphi (Vc H u j (q 0))) *
          |cf H s e (j + 1) (q 0) (Fin.tail q) u| := by ring
      _ ≤ ε * (3 / 16) * (((3 / 16 : ℝ) * ε) ^ e) := by
          have hstep : |H (q 0) a| *
              (psiS (Uc u j a) * dphi (Vc H u j (q 0))) ≤ ε * (3 / 16) :=
            mul_le_mul (hH (q 0) a) (psi_dphi_le_sharp _ _)
              (mul_pos (psiS_pos _) (dphi_pos _)).le hε
          exact mul_le_mul hstep (ih (j + 1) (q 0) (Fin.tail q) u)
            (abs_nonneg _) (by positivity)
      _ = _ := by ring

end QuarticQuery.ForrelationLower
