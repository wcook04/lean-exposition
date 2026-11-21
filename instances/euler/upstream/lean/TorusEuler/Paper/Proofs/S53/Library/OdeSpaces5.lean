import TorusEuler.Paper.Proofs.S53.Library.OdeSpaces4

/-!
# S53 library: the zero-order seminorms of the jet spaces
-/

open Set


namespace TorusEuler.Paper.Lib.S53

noncomputable section

/-- The seminorm `u ↦ c ‖f u‖`. -/
def scaledNormSem {M W : Type} [AddCommGroup M] [Module ℝ M] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (f : M →ₗ[ℝ] W) (c : ℝ) (hc : 0 ≤ c) : Seminorm ℝ M where
  toFun u := c * ‖f u‖
  map_zero' := by simp
  add_le' u v := by
    simp only [map_add]
    calc c * ‖f u + f v‖ ≤ c * (‖f u‖ + ‖f v‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hc
      _ = _ := by ring
  neg' u := by simp
  smul' a u := by simp only [map_smul, norm_smul]; ring

/-- Evaluation formula `scaledNormSem_apply` for the jet-space maps of the ODE instance of Lemma D.3. -/
theorem scaledNormSem_apply {M W : Type} [AddCommGroup M] [Module ℝ M] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (f : M →ₗ[ℝ] W) (c : ℝ) (hc : 0 ≤ c) (u : M) :
    scaledNormSem f c hc u = c * ‖f u‖ := rfl

/-- The supremum of a pointwise bounded family of seminorms. -/
def supSem {M I : Type} [AddCommGroup M] [Module ℝ M] (q : I → Seminorm ℝ M)
    (_hq : ∀ x, BddAbove (range fun i => q i x)) : Seminorm ℝ M := ⨆ i, q i

/-- Evaluation formula `supSem_apply` for the jet-space maps of the ODE instance of Lemma D.3. -/
theorem supSem_apply {M I : Type} [AddCommGroup M] [Module ℝ M] (q : I → Seminorm ℝ M)
    (hq : ∀ x, BddAbove (range fun i => q i x)) (x : M) :
    supSem q hq x = ⨆ i, q i x :=
  Seminorm.iSup_apply (Seminorm.bddAbove_range_iff.mpr hq)

/-- Auxiliary fact `le_supSem` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem le_supSem {M I : Type} [AddCommGroup M] [Module ℝ M] (q : I → Seminorm ℝ M)
    (hq : ∀ x, BddAbove (range fun i => q i x)) (x : M) (i : I) : q i x ≤ supSem q hq x := by
  rw [supSem_apply]; exact le_ciSup (hq x) i

/-- Upper bound for a supremum seminorm from a pointwise bound (`supSem_le`). -/
theorem supSem_le {M I : Type} [Nonempty I] [AddCommGroup M] [Module ℝ M] (q : I → Seminorm ℝ M)
    (hq : ∀ x, BddAbove (range fun i => q i x)) (x : M) {c : ℝ} (h : ∀ i, q i x ≤ c) :
    supSem q hq x ≤ c := by
  rw [supSem_apply]; exact ciSup_le h

variable {Idx : Type} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable (s : Slab)

/-- The slab `Icc s.l s.r` is nonempty (needed for the supremum seminorms). -/
instance : Nonempty (Icc s.l s.r) := ⟨⟨s.l, le_rfl, s.hlr.le⟩⟩

/-- Nonnegativity of the weight factor (`inv_g_nonneg`). -/
theorem inv_g_nonneg (t : Icc s.l s.r) : 0 ≤ (s.g t)⁻¹ := (inv_pos.mpr (s.hg0 t t.2)).le

/-- Nonnegativity of the weight factor (`rg_nonneg`). -/
theorem rg_nonneg (t : Icc s.l s.r) : 0 ≤ (s.r - s.l) / s.g t :=
  div_nonneg (sub_nonneg.mpr s.hlr.le) (s.hg0 t t.2).le

/-- Evaluation of a solution jet at the empty word and the time `t`. -/
def evE (t : ℝ) : Esub Idx V s →ₗ[ℝ] V :=
  LinearMap.proj t ∘ₗ LinearMap.proj ([] : List Idx) ∘ₗ (Esub Idx V s).subtype

/-- Evaluation of the forcing at the empty word and the time `t`. -/
def evF (t : ℝ) : Fsub Idx V s →ₗ[ℝ] V :=
  LinearMap.proj t ∘ₗ LinearMap.proj ([] : List Idx) ∘ₗ LinearMap.fst ℝ _ _ ∘ₗ
    (Fsub Idx V s).subtype

/-- The initial datum at the empty word. -/
def evI : Fsub Idx V s →ₗ[ℝ] V :=
  LinearMap.proj ([] : List Idx) ∘ₗ LinearMap.snd ℝ _ _ ∘ₗ (Fsub Idx V s).subtype

/-- Evaluation of a coefficient at the empty word and the time `t`. -/
def evA (t : ℝ) : Asub Idx V s →ₗ[ℝ] (V →L[ℝ] V) :=
  LinearMap.proj t ∘ₗ LinearMap.proj ([] : List Idx) ∘ₗ (Asub Idx V s).subtype

/-- Evaluation formula `evE_apply` for the jet-space maps of the ODE instance of Lemma D.3. -/
theorem evE_apply (t : ℝ) (u : Esub Idx V s) : evE s t u = u.1 [] t := rfl
/-- Evaluation formula `evF_apply` for the jet-space maps of the ODE instance of Lemma D.3. -/
theorem evF_apply (t : ℝ) (x : Fsub Idx V s) : evF s t x = x.1.1 [] t := rfl
/-- Evaluation formula `evI_apply` for the jet-space maps of the ODE instance of Lemma D.3. -/
theorem evI_apply (x : Fsub Idx V s) : evI s x = x.1.2 [] := rfl
/-- Evaluation formula `evA_apply` for the jet-space maps of the ODE instance of Lemma D.3. -/
theorem evA_apply (t : ℝ) (a : Asub Idx V s) : evA s t a = a.1 [] t := rfl

/-- The seminorm `u ↦ ‖u(t)‖ / g(t)`. -/
def qE (Idx V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (t : Icc s.l s.r) :
    Seminorm ℝ (Esub Idx V s) := scaledNormSem (evE s t) (s.g t)⁻¹ (inv_g_nonneg s t)

/-- The seminorm `x ↦ (r - l) ‖x(t)‖ / g(t)`. -/
def qF (Idx V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (t : Icc s.l s.r) :
    Seminorm ℝ (Fsub Idx V s) := scaledNormSem (evF s t) ((s.r - s.l) / s.g t) (rg_nonneg s t)

/-- The seminorm `a ↦ ‖a(t)‖`. -/
def qA (Idx V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (t : Icc s.l s.r) :
    Seminorm ℝ (Asub Idx V s) := scaledNormSem (evA s t) 1 zero_le_one

/-- Evaluation formula `qE_apply` for the jet-space maps of the ODE instance of Lemma D.3. -/
theorem qE_apply (t : Icc s.l s.r) (u : Esub Idx V s) :
    qE s Idx V t u = (s.g t)⁻¹ * ‖u.1 [] t‖ := rfl

/-- Evaluation formula `qF_apply` for the jet-space maps of the ODE instance of Lemma D.3. -/
theorem qF_apply (t : Icc s.l s.r) (x : Fsub Idx V s) :
    qF s Idx V t x = (s.r - s.l) / s.g t * ‖x.1.1 [] t‖ := rfl

/-- Evaluation formula `qA_apply` for the jet-space maps of the ODE instance of Lemma D.3. -/
theorem qA_apply (t : Icc s.l s.r) (a : Asub Idx V s) :
    qA s Idx V t a = 1 * ‖a.1 [] t‖ := rfl

/-- The supremum defining the seminorm in `pE_bdd` is finite. -/
theorem pE_bdd (u : Esub Idx V s) : BddAbove (range fun t : Icc s.l s.r => qE s Idx V t u) := by
  obtain ⟨M, hM⟩ := wbdd_of_continuousOn s (u.2.2 []).1.continuousOn
  refine ⟨M, ?_⟩
  rintro _ ⟨t, rfl⟩
  have hg := s.hg0 t t.2
  beta_reduce
  rw [qE_apply, inv_mul_le_iff₀ hg, mul_comm]
  exact hM t t.2

/-- The zero-order solution seminorm `sup_t ‖u(t)‖ / g(t)`. -/
def pE (Idx V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] : Seminorm ℝ (Esub Idx V s) :=
  supSem (qE s Idx V) (pE_bdd s)

/-- Pointwise lower bound for the supremum seminorm (`pE_ge`). -/
theorem pE_ge (u : Esub Idx V s) (t : ℝ) (ht : t ∈ Icc s.l s.r) :
    ‖u.1 [] t‖ / s.g t ≤ pE s Idx V u := by
  have : qE s Idx V ⟨t, ht⟩ u ≤ pE s Idx V u := le_supSem (qE s Idx V) (pE_bdd s) u ⟨t, ht⟩
  rw [qE_apply] at this
  rw [div_eq_inv_mul]
  exact this

/-- Upper bound for a supremum seminorm from a pointwise bound (`pE_le`). -/
theorem pE_le (u : Esub Idx V s) {c : ℝ} (h : ∀ t ∈ Icc s.l s.r, ‖u.1 [] t‖ / s.g t ≤ c) :
    pE s Idx V u ≤ c := by
  refine supSem_le (qE s Idx V) (pE_bdd s) u fun t => ?_
  rw [qE_apply, ← div_eq_inv_mul]
  exact h t t.2

/-- The supremum defining the seminorm in `pF_bdd` is finite. -/
theorem pF_bdd (x : Fsub Idx V s) : BddAbove (range fun t : Icc s.l s.r => qF s Idx V t x) := by
  obtain ⟨M, hM⟩ := x.2.2.2 []
  refine ⟨(s.r - s.l) * M, ?_⟩
  rintro _ ⟨t, rfl⟩
  have hg := s.hg0 t t.2
  beta_reduce
  rw [qF_apply, div_mul_eq_mul_div, div_le_iff₀ hg]
  calc (s.r - s.l) * ‖x.1.1 [] t‖ ≤ (s.r - s.l) * (M * s.g t) :=
        mul_le_mul_of_nonneg_left (hM t t.2) (sub_nonneg.mpr s.hlr.le)
    _ = _ := by ring

/-- The sup part of the forcing seminorm. -/
def pFsup (Idx V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] : Seminorm ℝ (Fsub Idx V s) :=
  supSem (qF s Idx V) (pF_bdd s)

/-- Auxiliary fact `g_l_pos` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem g_l_pos : 0 < s.g s.l := s.hg0 s.l ⟨le_rfl, s.hlr.le⟩

/-- The forcing seminorm `(r - l) sup ‖f‖/g + ‖x_l‖/g(l)`. -/
def pF (Idx V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] : Seminorm ℝ (Fsub Idx V s) :=
  pFsup s Idx V + scaledNormSem (evI s) (s.g s.l)⁻¹ (inv_pos.mpr (g_l_pos s)).le

/-- Evaluation formula `pF_apply` for the jet-space maps of the ODE instance of Lemma D.3. -/
theorem pF_apply (x : Fsub Idx V s) :
    pF s Idx V x = pFsup s Idx V x + (s.g s.l)⁻¹ * ‖x.1.2 []‖ := rfl

/-- Pointwise lower bound for the supremum seminorm (`pFsup_ge`). -/
theorem pFsup_ge (x : Fsub Idx V s) (t : ℝ) (ht : t ∈ Icc s.l s.r) :
    (s.r - s.l) * (‖x.1.1 [] t‖ / s.g t) ≤ pFsup s Idx V x := by
  have : qF s Idx V ⟨t, ht⟩ x ≤ pFsup s Idx V x := le_supSem (qF s Idx V) (pF_bdd s) x ⟨t, ht⟩
  rw [qF_apply] at this
  have e : (s.r - s.l) * (‖x.1.1 [] t‖ / s.g t) = (s.r - s.l) / s.g t * ‖x.1.1 [] t‖ := by ring
  rw [e]; exact this

/-- Upper bound for a supremum seminorm from a pointwise bound (`pFsup_le`). -/
theorem pFsup_le (x : Fsub Idx V s) {c : ℝ}
    (h : ∀ t ∈ Icc s.l s.r, (s.r - s.l) * (‖x.1.1 [] t‖ / s.g t) ≤ c) : pFsup s Idx V x ≤ c := by
  refine supSem_le (qF s Idx V) (pF_bdd s) x fun t => ?_
  rw [qF_apply]
  have e : (s.r - s.l) * (‖x.1.1 [] t‖ / s.g t) = (s.r - s.l) / s.g t * ‖x.1.1 [] t‖ := by ring
  rw [← e]; exact h t t.2

/-- Upper bound for a supremum seminorm from a pointwise bound (`pF_le`). -/
theorem pF_le (x : Fsub Idx V s) {H B : ℝ}
    (hf : ∀ t ∈ Icc s.l s.r, ‖x.1.1 [] t‖ / s.g t ≤ H) (hi : ‖x.1.2 []‖ / s.g s.l ≤ B) :
    pF s Idx V x ≤ (s.r - s.l) * H + B := by
  rw [pF_apply]
  refine add_le_add (pFsup_le s x fun t ht => ?_) ?_
  · exact mul_le_mul_of_nonneg_left (hf t ht) (sub_nonneg.mpr s.hlr.le)
  · rw [← div_eq_inv_mul]; exact hi

/-- The supremum defining the seminorm in `pA_bdd` is finite. -/
theorem pA_bdd (a : Asub Idx V s) : BddAbove (range fun t : Icc s.l s.r => qA s Idx V t a) := by
  obtain ⟨M, hM⟩ := a.2.2 []
  refine ⟨M, ?_⟩
  rintro _ ⟨t, rfl⟩
  beta_reduce
  rw [qA_apply, one_mul]; exact hM t t.2

/-- The zero-order coefficient seminorm `sup_t ‖a(t)‖`. -/
def pA (Idx V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] : Seminorm ℝ (Asub Idx V s) :=
  supSem (qA s Idx V) (pA_bdd s)

/-- Pointwise lower bound for the supremum seminorm (`pA_ge`). -/
theorem pA_ge (a : Asub Idx V s) (t : ℝ) (ht : t ∈ Icc s.l s.r) :
    ‖a.1 [] t‖ ≤ pA s Idx V a := by
  have : qA s Idx V ⟨t, ht⟩ a ≤ pA s Idx V a := le_supSem (qA s Idx V) (pA_bdd s) a ⟨t, ht⟩
  rw [qA_apply, one_mul] at this
  exact this

/-- Upper bound for a supremum seminorm from a pointwise bound (`pA_le`). -/
theorem pA_le (a : Asub Idx V s) {c : ℝ} (h : ∀ t ∈ Icc s.l s.r, ‖a.1 [] t‖ ≤ c) :
    pA s Idx V a ≤ c := by
  refine supSem_le (qA s Idx V) (pA_bdd s) a fun t => ?_
  rw [qA_apply, one_mul]
  exact h t t.2

/-- The product bound `p_F(T(a) u) ≤ (r - l) p_A(a) p_E(u)`. -/
theorem pF_Tmap_le (a : Asub Idx V s) (u : Esub Idx V s) :
    pF s Idx V (Tmap s a u) ≤ (s.r - s.l) * pA s Idx V a * pE s Idx V u := by
  rw [pF_apply]
  have h0 : (s.g s.l)⁻¹ * ‖(Tmap s a u).1.2 []‖ = 0 := by simp [Tmap_snd]
  rw [h0, add_zero]
  refine pFsup_le s _ fun t ht => ?_
  have hg := s.hg0 t ht
  have h1 := pA_ge s a t ht
  have h2 := pE_ge s u t ht
  have h3 : ‖(Tmap s a u).1.1 [] t‖ ≤ ‖a.1 [] t‖ * ‖u.1 [] t‖ := by
    rw [Tmap_fst]
    simp only [lsum, norm_neg]
    exact (a.1 [] t).le_opNorm _
  have hA0 : 0 ≤ pA s Idx V a := (norm_nonneg _).trans h1
  calc (s.r - s.l) * (‖(Tmap s a u).1.1 [] t‖ / s.g t)
      ≤ (s.r - s.l) * (‖a.1 [] t‖ * (‖u.1 [] t‖ / s.g t)) := by
        refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.mpr s.hlr.le)
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right h3 hg.le
    _ ≤ (s.r - s.l) * (pA s Idx V a * pE s Idx V u) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (div_nonneg (norm_nonneg _) hg.le) hA0)
          (sub_nonneg.mpr s.hlr.le)
    _ = _ := by ring

end

end TorusEuler.Paper.Lib.S53
