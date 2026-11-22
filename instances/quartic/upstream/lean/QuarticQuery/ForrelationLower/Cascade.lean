module

public import QuarticQuery.ForrelationLower.Walk

/-!
# Starting point of the path, and the advantage bound

Blueprint lemma W4 and M1. With block `0` zeroed, the coordinates of the later blocks are
zeroed one at a time by the reflection that flips a single `V_{r-1}(a)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open MeasureTheory Finset

namespace QuarticQuery.ForrelationLower

variable {n : Type} [Fintype n] [DecidableEq n] {l : ℕ} (H : Matrix n n ℝ)

/-- Rows of `H` are orthonormal. -/
def RowsOrth (H : Matrix n n ℝ) : Prop := ∀ a b, ∑ i, H a i * H b i = if a = b then 1 else 0

/-- The coordinates already zeroed. -/
def Zm (r : ℕ) (T : Finset n) (c : BC l n) : Prop := c.1.val < r ∨ (c.1.val = r ∧ c.2 ∈ T)

open Classical in
/-- The masked bias. -/
noncomputable def mw (r : ℕ) (T : Finset n) (u : PC l n → ℝ) (c : BC l n) : ℝ :=
  if Zm r T c then 0 else wv H 1 u c

/-- The unit vector of `V_j(a)`. -/
noncomputable def eV (j : ℕ) (a : n) (p : PC l n) : ℝ := if p.1.val = j then H a p.2 else 0

/-- The reflection flipping `V_j(a)`. -/
noncomputable def Rf (j : ℕ) (a : n) (u : PC l n → ℝ) : PC l n → ℝ :=
  fun p => u p - 2 * (∑ q, eV H j a q * u q) * eV H j a p

/-- Support for blueprint W4 and M1. -/
theorem sum_eV_mul {j : ℕ} (hj : j < l) (a : n) (u : PC l n → ℝ) :
    ∑ q, eV H j a q * u q = Vc H u j a := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (⟨j, hj⟩ : Fin l)]
  · simp [eV, Vc, Uc, hj]
  · intro r _ hr
    refine sum_eq_zero fun i _ => ?_
    have : r.val ≠ j := fun h => hr (Fin.ext h)
    simp [eV, this]
  · simp

/-- Support for blueprint W4 and M1. -/
theorem sum_eV_sq {j : ℕ} (hj : j < l) (hH : RowsOrth H) (a : n) :
    ∑ q : PC l n, eV H j a q ^ 2 = 1 := by
  have h := sum_eV_mul H hj a (eV H j a)
  have e : Vc H (eV H j a : PC l n → ℝ) j a = 1 := by
    have h1 : ∀ i, Uc (eV H j a : PC l n → ℝ) j i = H a i := fun i => by simp [Uc, hj, eV]
    show ∑ i, H a i * Uc (eV H j a : PC l n → ℝ) j i = 1
    simp only [h1]
    simpa using hH a a
  rw [← e, ← h]
  exact sum_congr rfl fun q _ => by ring

/-- Support for blueprint W4 and M1. -/
theorem Uc_Rf_of_ne {j : ℕ} (a : n) (u : PC l n → ℝ) {r : ℕ} (hr : r ≠ j) (i : n) :
    Uc (Rf H j a u) r i = Uc u r i := by
  unfold Uc Rf
  by_cases h : r < l
  · simp [h, eV, hr]
  · simp [h]

/-- Support for blueprint W4 and M1. -/
theorem Uc_Rf {j : ℕ} (hj : j < l) (a : n) (u : PC l n → ℝ) (i : n) :
    Uc (Rf H j a u) j i = Uc u j i - 2 * Vc H u j a * H a i := by
  have h1 : ∀ v : PC l n → ℝ, Uc v j i = v (⟨j, hj⟩, i) := fun v => by simp [Uc, hj]
  rw [h1, h1]
  show u (⟨j, hj⟩, i) - 2 * (∑ q, eV H j a q * u q) * eV H j a (⟨j, hj⟩, i) = _
  rw [sum_eV_mul H hj]
  simp [eV]

/-- Support for blueprint W4 and M1. -/
theorem Vc_Rf_of_ne {j : ℕ} (a : n) (u : PC l n → ℝ) {r : ℕ} (hr : r ≠ j) (b : n) :
    Vc H (Rf H j a u) r b = Vc H u r b := by
  unfold Vc
  simp only [Uc_Rf_of_ne H a u hr]

/-- Support for blueprint W4 and M1. -/
theorem Vc_Rf {j : ℕ} (hj : j < l) (hH : RowsOrth H) (a b : n) (u : PC l n → ℝ) :
    Vc H (Rf H j a u) j b = if b = a then - Vc H u j a else Vc H u j b := by
  have h : Vc H (Rf H j a u) j b = Vc H u j b - 2 * Vc H u j a * ∑ i, H b i * H a i := by
    generalize hκ : Vc H u j a = κ
    show ∑ i, H b i * Uc (Rf H j a u) j i = (∑ i, H b i * Uc u j i) - _
    simp only [Uc_Rf H hj, hκ, mul_sub, sum_sub_distrib]
    congr 1
    rw [mul_sum]
    exact sum_congr rfl fun i _ => by ring
  rw [h, hH]
  by_cases hab : b = a
  · subst hab; simp; ring
  · simp [hab]

/-- Support for blueprint W4 and M1. -/
theorem Xf_Rf_of_ne {j : ℕ} (a : n) (u : PC l n → ℝ) {r : ℕ} (hr : r ≠ j) (i : n) :
    Xf (Rf H j a u) r i = Xf u r i := by
  simp only [Xf, Uc_Rf_of_ne H a u hr]

/-- The effect of the reflection on the masked bias. -/
theorem mw_Rf {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ l) (hH : RowsOrth H) {T : Finset n} {a : n}
    (ha : a ∉ T) (u : PC l n → ℝ) (c : BC l n) :
    mw H r T (Rf H (r - 1) a u) c = if c = cn r a then - mw H r T u c else mw H r T u c := by
  classical
  have hcv : (cn r a : BC l n).1.val = r := cn_val_of_le hr a
  by_cases hZ : Zm r T c
  · have hne : c ≠ cn r a := by
      rintro rfl
      rcases hZ with h | ⟨_, h⟩
      · omega
      · exact ha h
    simp [mw, hZ, hne]
  · have hnc : ¬ c.1.val < r := fun h => hZ (Or.inl h)
    have hjl : r - 1 < l := by omega
    have hXe : Xf (Rf H (r - 1) a u) c.1 c.2 = Xf u c.1 c.2 :=
      Xf_Rf_of_ne H a u (by omega) _
    have hS : ∀ s, Sf (l := l) (n := n) s c = 1 := fun s => by
      simp only [Sf]; rw [if_neg (by omega)]
    simp only [mw, hZ, if_false, wv, hS, one_mul, hXe]
    by_cases hc : c.1.val = r
    · have hy : Yf H (Rf H (r - 1) a u) c.1 c.2 =
          if c.2 = a then - Yf H u c.1 c.2 else Yf H u c.1 c.2 := by
        simp only [Yf, hc, show r ≠ 0 by omega, if_false, Vc_Rf H hjl hH]
        split_ifs with h
        · rw [h, phiS_neg]
        · rfl
      by_cases h2 : c.2 = a
      · have : c = cn r a := Prod.ext (Fin.ext (by rw [hc, hcv])) h2
        rw [if_pos this, hy, if_pos h2]
        ring
      · have : c ≠ cn r a := fun h => h2 (by rw [h]; rfl)
        rw [if_neg this, hy, if_neg h2]
    · have hne : c ≠ cn r a := fun h => hc (by rw [h, hcv])
      have hy : Yf H (Rf H (r - 1) a u) c.1 c.2 = Yf H u c.1 c.2 := by
        unfold Yf
        by_cases h0 : c.1.val = 0
        · simp [h0]
        · simp only [h0, if_false]
          rw [Vc_Rf_of_ne H a u (by omega)]
      rw [if_neg hne, hy]

/-- Support for blueprint W4 and M1. -/
theorem mw_insert {r : ℕ} (hr : r ≤ l) {T : Finset n} (a : n) (u : PC l n → ℝ) :
    mw H r (insert a T) u = Function.update (mw H r T u) (cn r a) 0 := by
  classical
  funext c
  by_cases hc : c = cn r a
  · subst hc
    have : Zm r (insert a T) (cn r a : BC l n) :=
      Or.inr ⟨cn_val_of_le hr a, by simp [cn]⟩
    simp [mw, this]
  · rw [Function.update_of_ne hc]
    have : Zm r (insert a T) c ↔ Zm r T c := by
      unfold Zm
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · rcases mem_insert.mp h2 with h3 | h3
          · exact absurd (Prod.ext (Fin.ext (by rw [h1, cn_val_of_le hr])) h3) hc
          · exact Or.inr ⟨h1, h3⟩
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h1, mem_insert_of_mem h2⟩
    simp [mw, this]

/-- Support for blueprint W4 and M1. -/
theorem measurable_mw (r : ℕ) (T : Finset n) (c : BC l n) :
    Measurable fun u : PC l n → ℝ => mw H r T u c := by
  classical
  unfold mw
  by_cases h : Zm r T c
  · simp [h]
  · simpa [h] using (continuous_wv H 1 c).measurable

/-- Support for blueprint W4 and M1. -/
theorem abs_mw_le (r : ℕ) (T : Finset n) (u : PC l n → ℝ) (c : BC l n) : |mw H r T u c| ≤ 1 := by
  classical
  unfold mw
  split_ifs
  · simp
  · exact abs_wv_le H (by simp) u c

/-- One coordinate is zeroed by a reflection. -/
theorem integral_mw_insert {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ l) (hH : RowsOrth H)
    (g : (BC l n → Bool) → ℝ) {T : Finset n} {a : n} (ha : a ∉ T) :
    ∫ u, ext g (mw H r (insert a T) u) ∂(gP (PC l n)) =
      ∫ u, ext g (mw H r T u) ∂(gP (PC l n)) := by
  classical
  set c0 : BC l n := cn r a with hc0
  obtain ⟨B, hB⟩ : ∃ B, ∀ z, |g z| ≤ B :=
    ⟨∑ z, |g z|, fun z => single_le_sum (f := fun z => |g z|) (fun _ _ => abs_nonneg _) (mem_univ z)⟩
  have hmw : Measurable fun u : PC l n → ℝ => mw H r T u :=
    measurable_pi_iff.mpr fun c => measurable_mw H r T c
  let f : (PC l n → ℝ) → ℝ := fun u => mw H r T u c0 * ext (D c0 g) (mw H r T u)
  have hfm : Measurable f :=
    (measurable_mw H r T c0).mul ((continuous_ext _).measurable.comp hmw)
  have hflip : ∀ u, f (Rf H (r - 1) a u) = - f u := by
    intro u
    have h1 : ext (D c0 g) (mw H r T (Rf H (r - 1) a u)) = ext (D c0 g) (mw H r T u) :=
      ext_congr_off c0 _ (D_flip c0 g) fun b hb => by
        rw [mw_Rf H hr1 hr hH ha, if_neg hb]
    simp only [f, h1]
    rw [mw_Rf H hr1 hr hH ha, if_pos rfl]
    ring
  have hj : r - 1 < l := by omega
  have hrefl := integral_reflect (eV H (r - 1) a) (sum_eV_sq H hj hH a) hfm
  have hRf : ∀ u : PC l n → ℝ, (fun p => u p - 2 * (∑ q, eV H (r - 1) a q * u q) * eV H (r - 1) a p) =
      Rf H (r - 1) a u := fun u => rfl
  simp only [hRf, hflip, integral_neg] at hrefl
  have hf0 : ∫ u, f u ∂(gP (PC l n)) = 0 := by linarith
  have hbd : ∀ u, |ext (D c0 g) (mw H r T u)| ≤ B := fun u =>
    abs_ext_le (abs_D_le hB c0) fun c => abs_mw_le H r T u c
  have hif : Integrable f (gP (PC l n)) := by
    refine Integrable.of_bound hfm.aestronglyMeasurable B (.of_forall fun u => ?_)
    simp only [f, Real.norm_eq_abs, abs_mul]
    have := abs_mw_le H r T u c0
    have := hbd u
    nlinarith [abs_nonneg (mw H r T u c0), abs_nonneg (ext (D c0 g) (mw H r T u))]
  have hie : Integrable (fun u => ext g (mw H r (insert a T) u)) (gP (PC l n)) := by
    refine Integrable.of_bound ((continuous_ext g).measurable.comp ?_).aestronglyMeasurable B
      (.of_forall fun u => abs_ext_le hB fun c => abs_mw_le H r _ u c)
    exact measurable_pi_iff.mpr fun c => measurable_mw H r _ c
  have key : ∀ u, ext g (mw H r T u) = ext g (mw H r (insert a T) u) + f u := fun u => by
    rw [mw_insert H hr a u]
    exact ext_affine c0 g _
  simp only [key]
  rw [integral_add hie hif, hf0, add_zero]

/-- Support for blueprint W4 and M1. -/
theorem integral_mw_all {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ l) (hH : RowsOrth H)
    (g : (BC l n → Bool) → ℝ) (T : Finset n) :
    ∫ u, ext g (mw H r T u) ∂(gP (PC l n)) = ∫ u, ext g (mw H r ∅ u) ∂(gP (PC l n)) := by
  induction T using Finset.induction_on with
  | empty => rfl
  | insert a T ha ih => rw [integral_mw_insert H hr1 hr hH g ha, ih]

/-- Support for blueprint W4 and M1. -/
theorem mw_succ (r : ℕ) (u : PC l n → ℝ) :
    mw H (r + 1) ∅ u = mw H r (univ : Finset n) u := by
  classical
  funext c
  have : Zm (r + 1) ∅ c ↔ Zm r univ c := by
    simp only [Zm, mem_univ, and_true, notMem_empty, and_false, or_false]
    omega
  simp [mw, this]

/-- W4. The start of the path is the uniform average. -/
theorem integral_ext_wv_zero (hH : RowsOrth H) (g : (BC l n → Bool) → ℝ) :
    ∫ u, ext g (wv H 0 u) ∂(gP (PC l n)) = ext g 0 := by
  classical
  have h0 : ∀ u : PC l n → ℝ, wv H 0 u = mw H 1 ∅ u := by
    intro u
    funext c
    by_cases hc : c.1.val = 0
    · have : Zm 1 ∅ c := Or.inl (by omega)
      simp [mw, this, wv, Sf, hc]
    · have : ¬ Zm 1 ∅ c := by
        simp only [Zm, notMem_empty, and_false, or_false]
        omega
      simp [mw, this, wv, Sf, hc]
  have hstep : ∀ r, r ≤ l → ∫ u, ext g (mw H 1 ∅ u) ∂(gP (PC l n)) =
      ∫ u, ext g (mw H (r + 1) ∅ u) ∂(gP (PC l n)) := by
    intro r
    induction r with
    | zero => intro _; rfl
    | succ r ih =>
      intro hr
      rw [ih (by omega)]
      simp only [mw_succ H (r + 1)]
      exact (integral_mw_all H (by omega) hr hH g univ).symm
  simp only [h0]
  rw [hstep l le_rfl]
  have hz : ∀ u : PC l n → ℝ, mw H (l + 1) ∅ u = 0 := by
    intro u
    funext c
    have : Zm (l + 1) ∅ c := Or.inl c.1.isLt
    simp [mw, this]
  simp [hz]

/-! ## M1. The advantage bound -/

/-- Support for blueprint W4 and M1. -/
theorem plist_length (e j : ℕ) (q : Fin e → n) : (plist (l := l) e j q).length = e := by
  induction e generalizing j with
  | zero => rfl
  | succ e ih => simp [plist, ih]

/-- Support for blueprint W4 and M1. -/
theorem mem_plist_lt {e j : ℕ} (hle : j + e ≤ l) {q : Fin e → n} {c : BC l n}
    (hc : c ∈ plist e j q) : j < c.1.val := by
  induction e generalizing j with
  | zero => simp [plist] at hc
  | succ e ih =>
    simp only [plist, List.mem_cons] at hc
    rcases hc with rfl | hc
    · rw [cn_val_of_le (by omega)]; omega
    · have := ih (j := j + 1) (by omega) hc
      omega

/-- Support for blueprint W4 and M1. -/
theorem plist_nodup {e j : ℕ} (hle : j + e ≤ l) (q : Fin e → n) :
    (plist (l := l) e j q).Nodup := by
  induction e generalizing j with
  | zero => simp [plist]
  | succ e ih =>
    simp only [plist, List.nodup_cons]
    refine ⟨fun h => ?_, ih (j := j + 1) (by omega) _⟩
    have := mem_plist_lt (j := j + 1) (by omega) h
    rw [cn_val_of_le (by omega)] at this
    omega

/-- Support for blueprint W4 and M1. -/
theorem plist_inj {e j : ℕ} (hle : j + e ≤ l) {q q' : Fin e → n}
    (h : (plist (l := l) e j q).toFinset = (plist (l := l) e j q').toFinset) : q = q' := by
  induction e generalizing j with
  | zero => exact Subsingleton.elim _ _
  | succ e ih =>
    have hv : ((cn (j + 1) (q 0) : BC l n)).1.val = j + 1 := cn_val_of_le (by omega) _
    have hmem : (cn (j + 1) (q 0) : BC l n) ∈ (plist (l := l) (e + 1) j q').toFinset := by
      rw [← h]; simp [plist]
    have h0 : q 0 = q' 0 := by
      simp only [plist, List.mem_toFinset, List.mem_cons] at hmem
      rcases hmem with h1 | h1
      · exact congrArg Prod.snd h1
      · have := mem_plist_lt (j := j + 1) (by omega) h1
        omega
    have hne : ∀ (p : Fin (e + 1) → n), (cn (j + 1) (q 0) : BC l n) ∉
        (plist (l := l) e (j + 1) (Fin.tail p)).toFinset := by
      intro p hp
      have := mem_plist_lt (j := j + 1) (by omega) (List.mem_toFinset.mp hp)
      omega
    have ht : (plist (l := l) e (j + 1) (Fin.tail q)).toFinset =
        (plist (l := l) e (j + 1) (Fin.tail q')).toFinset := by
      have := congrArg (fun s => s.erase (cn (j + 1) (q 0) : BC l n)) h
      simp only [plist, List.toFinset_cons, ← h0] at this
      rwa [erase_insert (hne q), erase_insert (hne q')] at this
    have hq := ih (j := j + 1) (by omega) ht
    funext i
    refine Fin.cases h0 (fun i => ?_) i
    exact congrFun hq i

/-- The index lists of full paths. -/
def Lpath (l : ℕ) (p : n × (Fin l → n)) : List (BC l n) := cn 0 p.1 :: plist l 0 p.2

/-- Support for blueprint W4 and M1. -/
theorem Lpath_nodup (p : n × (Fin l → n)) : (Lpath l p).Nodup := by
  simp only [Lpath, List.nodup_cons]
  refine ⟨fun h => ?_, plist_nodup (by omega) _⟩
  have := mem_plist_lt (j := 0) (by omega) h
  rw [cn_val_of_le (by omega)] at this
  omega

/-- Support for blueprint W4 and M1. -/
theorem Lpath_inj : Function.Injective fun p : n × (Fin l → n) => (Lpath l p).toFinset := by
  rintro ⟨a, q⟩ ⟨a', q'⟩ h
  simp only [Lpath, List.toFinset_cons] at h
  have hmem : (cn 0 a : BC l n) ∈ insert (cn 0 a' : BC l n) (plist (l := l) l 0 q').toFinset := by
    rw [← h]; simp
  have ha : a = a' := by
    rcases mem_insert.mp hmem with h1 | h1
    · exact congrArg Prod.snd h1
    · have := mem_plist_lt (j := 0) (by omega) (List.mem_toFinset.mp h1)
      rw [cn_val_of_le (by omega)] at this
      omega
  subst ha
  have hne : ∀ q'' : Fin l → n, (cn 0 a : BC l n) ∉ (plist (l := l) l 0 q'').toFinset := by
    intro q'' hp
    have := mem_plist_lt (j := 0) (by omega) (List.mem_toFinset.mp hp)
    rw [cn_val_of_le (by omega)] at this
    omega
  have := congrArg (fun s => s.erase (cn 0 a : BC l n)) h
  simp only [erase_insert (hne _)] at this
  rw [plist_inj (by omega) this]

/-- M1. The advantage of a depth-`d` tree over the uniform measure. -/
theorem advantage_le_sharp (hl : 0 < l) (hH : RowsOrth H) {ε : ℝ} (hε : 0 ≤ ε) (hHb : ∀ a b, |H a b| ≤ ε)
    {Λ K : ℝ} {d : ℕ} (hd : 0 < d) (hK : 0 < K) (hKsq : K ^ 2 = 2 * d * 2 ^ 2 * Λ)
    (hn : 1 ≤ Fintype.card (BC l n)) (T : QueryTree (BC l n)) (hT : T.depth ≤ d) (v : Bool → ℝ)
    (hv : ∀ b, |v b| ≤ 1) :
    |∫ u, ext (fun z => v (T.eval z)) (wv H 1 u) ∂(gP (PC l n)) -
        ext (fun z => v (T.eval z)) 0| ≤
      ((3 / 16 : ℝ) * ε) ^ l * (K ^ (l + 1) + (Fintype.card (BC l n) * 2) ^ (l + 1) *
        ((4 * Fintype.card (BC l n) : ℝ) ^ (l + 1) * Real.exp (-Λ))) := by
  set g : (BC l n → Bool) → ℝ := fun z => v (T.eval z) with hg
  obtain ⟨s, hs, hid⟩ := exists_identity H hl g
  rw [integral_ext_wv_zero H hH g] at hid
  rw [hid]
  have hs1 : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2.le⟩
  rw [← integral_finsetSum _ fun a _ => (bcf_Int H hs1 l 0 a _).integrable]
  set W := K ^ (l + 1) + (Fintype.card (BC l n) * 2 : ℝ) ^ (l + 1) *
        ((4 * Fintype.card (BC l n) : ℝ) ^ (l + 1) * Real.exp (-Λ)) with hW
  have hpt : ∀ u : PC l n → ℝ, ‖∑ a, Int H s l 0 a (D (cn 0 a) g) u‖ ≤ ((3 / 16 : ℝ) * ε) ^ l * W := by
    intro u
    have hμ : ∀ c, |wv H s u c| ≤ 1 / 2 := abs_wv_le_half H hl hs1 u
    have hgrow := sum_abs_ext_Dl_le (Lpath l) Lpath_nodup (k := l + 1)
      (fun p => by simp [Lpath, plist_length]) Lpath_inj hμ hd hK hKsq hn T hT v hv
    rw [Fintype.sum_prod_type] at hgrow
    calc ‖∑ a, Int H s l 0 a (D (cn 0 a) g) u‖
        ≤ ∑ a, ∑ q : Fin l → n, ((3 / 16 : ℝ) * ε) ^ l *
            |ext (Dl (plist l 0 q) (D (cn 0 a) g)) (wv H s u)| := by
          refine (norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_)
          rw [Int_eq_paths]
          refine (norm_sum_le _ _).trans (sum_le_sum fun q _ => ?_)
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (abs_cf_le_sharp H s hε hHb l 0 a q u) (abs_nonneg _)
      _ = ((3 / 16 : ℝ) * ε) ^ l * ∑ a, ∑ q : Fin l → n,
            |ext (Dl (plist l 0 q) (D (cn 0 a) g)) (wv H s u)| := by
          simp only [mul_sum]
      _ ≤ ((3 / 16 : ℝ) * ε) ^ l * W := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact hgrow
  have := norm_integral_le_of_norm_le_const (μ := gP (PC l n))
    (.of_forall hpt)
  simpa using this


/-- The earlier coarse advantage bound, retained for its existing consumers. -/
theorem advantage_le (hl : 0 < l) (hH : RowsOrth H) {ε : ℝ} (hε : 0 ≤ ε) (hHb : ∀ a b, |H a b| ≤ ε)
    {Λ K : ℝ} {d : ℕ} (hd : 0 < d) (hK : 0 < K) (hKsq : K ^ 2 = 2 * d * 2 ^ 2 * Λ)
    (hn : 1 ≤ Fintype.card (BC l n)) (T : QueryTree (BC l n)) (hT : T.depth ≤ d) (v : Bool → ℝ)
    (hv : ∀ b, |v b| ≤ 1) :
    |∫ u, ext (fun z => v (T.eval z)) (wv H 1 u) ∂(gP (PC l n)) -
        ext (fun z => v (T.eval z)) 0| ≤
      (3 * ε) ^ l * (K ^ (l + 1) + (Fintype.card (BC l n) * 2) ^ (l + 1) *
        ((4 * Fintype.card (BC l n) : ℝ) ^ (l + 1) * Real.exp (-Λ))) := by
  refine (advantage_le_sharp H hl hH hε hHb hd hK hKsq hn T hT v hv).trans ?_
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) (by nlinarith : (3 / 16 : ℝ) * ε ≤ 3 * ε) l)
    (by positivity)

end QuarticQuery.ForrelationLower
