import TorusEuler.Paper.Proofs.S53.Library.OdeSpaces2

/-!
# S53 library: forcing and coefficient spaces, derivative maps, `L₀` and `T`
-/

open Set


namespace TorusEuler.Paper.Lib.S53

noncomputable section

variable {Idx : Type} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ V] in
/-- Auxiliary fact `congr` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem WBdd.congr {s : Slab} {f g : ℝ → V} (hf : WBdd s f) (h : ∀ t ∈ Icc s.l s.r, g t = f t) :
    WBdd s g := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨M, fun t ht => by rw [h t ht]; exact hM t ht⟩

/-- The space of forcings with initial data. -/
def Fsub (Idx V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (s : Slab) :
    Submodule ℝ ((List Idx → ℝ → V) × (List Idx → V)) where
  carrier := {x | IsSymm x.1 ∧ IsSymm x.2 ∧ ∀ w, WBdd s (x.1 w)}
  add_mem' := by
    rintro x y ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    refine ⟨fun {w w'} h => ?_, fun {w w'} h => ?_, fun w => (h3 w).add (k3 w)⟩
    · simp only [Prod.fst_add, Pi.add_apply]; rw [h1 h, k1 h]
    · simp only [Prod.snd_add, Pi.add_apply]; rw [h2 h, k2 h]
  zero_mem' := ⟨fun _ => rfl, fun _ => rfl, fun w => ⟨0, fun t _ => by simp⟩⟩
  smul_mem' := by
    rintro c x ⟨h1, h2, h3⟩
    refine ⟨fun {w w'} h => ?_, fun {w w'} h => ?_, fun w => (h3 w).smul c⟩
    · simp only [Prod.smul_fst, Pi.smul_apply]; rw [h1 h]
    · simp only [Prod.smul_snd, Pi.smul_apply]; rw [h2 h]

/-- The space of coefficient jets (operator valued). -/
def Asub (Idx V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (s : Slab) :
    Submodule ℝ (List Idx → ℝ → V →L[ℝ] V) where
  carrier := {a | IsSymm a ∧ ∀ w, ∃ M : ℝ, ∀ t ∈ Icc s.l s.r, ‖a w t‖ ≤ M}
  add_mem' := by
    rintro a b ⟨h1, h2⟩ ⟨k1, k2⟩
    refine ⟨fun {w w'} h => ?_, fun w => ?_⟩
    · simp only [Pi.add_apply]; rw [h1 h, k1 h]
    · obtain ⟨M, hM⟩ := h2 w
      obtain ⟨N, hN⟩ := k2 w
      exact ⟨M + N, fun t ht => (norm_add_le _ _).trans (add_le_add (hM t ht) (hN t ht))⟩
  zero_mem' := ⟨fun _ => rfl, fun w => ⟨0, fun t _ => by simp⟩⟩
  smul_mem' := by
    rintro c a ⟨h1, h2⟩
    refine ⟨fun {w w'} h => ?_, fun w => ?_⟩
    · simp only [Pi.smul_apply]; rw [h1 h]
    · obtain ⟨M, hM⟩ := h2 w
      refine ⟨|c| * M, fun t ht => ?_⟩
      calc ‖(c • a w) t‖ = |c| * ‖a w t‖ := by simp [norm_smul]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hM t ht) (abs_nonneg _)

/-- Shift of a family by a letter, as a linear map. -/
def shiftLM (Idx : Type) {X : Type} [AddCommGroup X] [Module ℝ X] (i : Idx) :
    (List Idx → X) →ₗ[ℝ] (List Idx → X) :=
  LinearMap.funLeft ℝ X (fun w : List Idx => i :: w)

/-- Evaluation formula `shiftLM_apply` for the jet-space maps of the ODE instance of Lemma D.3. -/
@[simp] theorem shiftLM_apply {X : Type} [AddCommGroup X] [Module ℝ X] (i : Idx)
    (u : List Idx → X) (w : List Idx) : shiftLM Idx i u w = u (i :: w) := rfl

variable (s : Slab)

/-- The weighted derivative in the direction `i` on solution jets. -/
def DE (i : Idx) : Esub Idx V s →ₗ[ℝ] Esub Idx V s :=
  (shiftLM Idx i).restrict (fun _ hu => ⟨isSymm_cons hu.1 i, fun w => hu.2 (i :: w)⟩)

/-- The derivative in the direction `i` on forcings. -/
def DF (i : Idx) : Fsub Idx V s →ₗ[ℝ] Fsub Idx V s :=
  ((shiftLM Idx i).prodMap (shiftLM Idx i)).restrict (fun _ hx =>
    ⟨isSymm_cons hx.1 i, isSymm_cons hx.2.1 i, fun w => hx.2.2 (i :: w)⟩)

/-- The derivative in the direction `i` on coefficients. -/
def DA (i : Idx) : Asub Idx V s →ₗ[ℝ] Asub Idx V s :=
  (shiftLM Idx i).restrict (fun _ ha => ⟨isSymm_cons ha.1 i, fun w => ha.2 (i :: w)⟩)

/-- Evaluation formula `DE_apply` for the jet-space maps of the ODE instance of Lemma D.3. -/
@[simp] theorem DE_apply (i : Idx) (u : Esub Idx V s) (w : List Idx) :
    (DE s i u).1 w = u.1 (i :: w) := rfl

/-- Auxiliary fact `DF_apply_fst` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
@[simp] theorem DF_apply_fst (i : Idx) (x : Fsub Idx V s) (w : List Idx) :
    (DF s i x).1.1 w = x.1.1 (i :: w) := rfl

/-- Auxiliary fact `DF_apply_snd` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
@[simp] theorem DF_apply_snd (i : Idx) (x : Fsub Idx V s) (w : List Idx) :
    (DF s i x).1.2 w = x.1.2 (i :: w) := rfl

/-- Evaluation formula `DA_apply` for the jet-space maps of the ODE instance of Lemma D.3. -/
@[simp] theorem DA_apply (i : Idx) (a : Asub Idx V s) (w : List Idx) :
    (DA s i a).1 w = a.1 (i :: w) := rfl

/-- The weighted derivative maps commute (`DE_comm`), as required by Lemma D.3. -/
theorem DE_comm (i j : Idx) (u : Esub Idx V s) : DE s i (DE s j u) = DE s j (DE s i u) := by
  apply Subtype.ext; funext w
  simp only [DE_apply]
  exact u.2.1 (List.Perm.swap i j w)

/-- The weighted derivative maps commute (`DF_comm`), as required by Lemma D.3. -/
theorem DF_comm (i j : Idx) (x : Fsub Idx V s) : DF s i (DF s j x) = DF s j (DF s i x) := by
  apply Subtype.ext; apply Prod.ext
  · funext w
    simp only [DF_apply_fst]
    exact x.2.1 (List.Perm.swap i j w)
  · funext w
    simp only [DF_apply_snd]
    exact x.2.2.1 (List.Perm.swap i j w)

/-- The weighted derivative maps commute (`DA_comm`), as required by Lemma D.3. -/
theorem DA_comm (i j : Idx) (a : Asub Idx V s) : DA s i (DA s j a) = DA s j (DA s i a) := by
  apply Subtype.ext; funext w
  simp only [DA_apply]
  exact a.2.1 (List.Perm.swap i j w)

end

end TorusEuler.Paper.Lib.S53
