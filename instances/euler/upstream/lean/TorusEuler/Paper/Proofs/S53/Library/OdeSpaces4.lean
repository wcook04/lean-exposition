import TorusEuler.Paper.Proofs.S53.Library.OdeSpaces3

/-!
# S53 library: the operators `L₀` and `T` on the jet spaces
-/

open Set


namespace TorusEuler.Paper.Lib.S53

noncomputable section

variable {Idx : Type} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable (s : Slab)

/-- `L₀ u = (∂_t u, u(l))` on every word. -/
def L0 : Esub Idx V s →ₗ[ℝ] Fsub Idx V s where
  toFun u := ⟨(fun w => (Icc s.l s.r).indicator (derivWithin (u.1 w) (Icc s.l s.r)),
      fun w => u.1 w s.l),
    ⟨fun {w w'} h => by simp only [u.2.1 h],
     fun {w w'} h => by simp only [u.2.1 h],
     fun w => (wbdd_of_continuousOn s (u.2.2 w).2).congr
       (fun t ht => by simp [indicator_of_mem ht])⟩⟩
  map_add' u v := by
    apply Subtype.ext; apply Prod.ext
    · funext w t
      by_cases ht : t ∈ Icc s.l s.r
      · simp only [Submodule.coe_add, Prod.fst_add, Pi.add_apply, indicator_of_mem ht]
        exact derivWithin_add_on s (u.2.2 w).1 (v.2.2 w).1 ht
      · simp [indicator_of_notMem ht]
    · rfl
  map_smul' c u := by
    apply Subtype.ext; apply Prod.ext
    · funext w t
      by_cases ht : t ∈ Icc s.l s.r
      · simp only [Submodule.coe_smul, Prod.smul_fst, Pi.smul_apply, indicator_of_mem ht,
          RingHom.id_apply]
        exact derivWithin_smul_on s c (u.2.2 w).1 ht
      · simp [indicator_of_notMem ht]
    · rfl

/-- Auxiliary fact `L0_fst` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem L0_fst (u : Esub Idx V s) (w : List Idx) {t : ℝ} (ht : t ∈ Icc s.l s.r) :
    (L0 s u).1.1 w t = derivWithin (u.1 w) (Icc s.l s.r) t := by
  simp [L0, indicator_of_mem ht]

/-- Auxiliary fact `L0_snd` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem L0_snd (u : Esub Idx V s) (w : List Idx) : (L0 s u).1.2 w = u.1 w s.l := rfl

/-- The weighted derivative maps commute (`L0_comm`), as required by Lemma D.3. -/
theorem L0_comm (i : Idx) (u : Esub Idx V s) : DF s i (L0 s u) = L0 s (DE s i u) := rfl

/-- The weighted bound of a Leibniz sum. -/
theorem lsum_wbdd (w : List Idx) :
    ∀ (a : List Idx → ℝ → V →L[ℝ] V) (u : List Idx → ℝ → V),
      (∀ v, ∃ M : ℝ, ∀ t ∈ Icc s.l s.r, ‖a v t‖ ≤ M) → (∀ v, WBdd s (u v)) →
      WBdd s (fun t => lsum w (fun v₁ v₂ => a v₁ t (u v₂ t))) := by
  induction w with
  | nil =>
    intro a u ha hu
    obtain ⟨M, hM⟩ := ha []
    obtain ⟨N, hN⟩ := hu []
    refine ⟨M * N, fun t ht => ?_⟩
    have hg := (s.hg0 t ht).le
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM t ht)
    calc ‖lsum [] (fun v₁ v₂ => a v₁ t (u v₂ t))‖ = ‖a [] t (u [] t)‖ := rfl
      _ ≤ ‖a [] t‖ * ‖u [] t‖ := (a [] t).le_opNorm _
      _ ≤ M * (N * s.g t) :=
        mul_le_mul (hM t ht) (hN t ht) (norm_nonneg _) hM0
      _ = _ := by ring
  | cons i w ih =>
    intro a u ha hu
    have h1 := ih (fun v => a (i :: v)) u (fun v => ha _) hu
    have h2 := ih a (fun v => u (i :: v)) ha (fun v => hu _)
    exact (h1.add h2).congr fun t _ => rfl

/-- `T(a)u = -(a u)` with the Leibniz rule for words, and zero initial data. -/
def Tmap : Asub Idx V s →ₗ[ℝ] Esub Idx V s →ₗ[ℝ] Fsub Idx V s :=
  LinearMap.mk₂ ℝ
    (fun a u => ⟨(fun w t => - lsum w (fun v₁ v₂ => a.1 v₁ t (u.1 v₂ t)), fun _ => 0),
      ⟨fun {w w'} h => by
        funext t
        simp only
        rw [lsum_perm (fun (A : V →L[ℝ] V) (y : V) => A y) h (fun v => a.1 v t) (fun v => u.1 v t)
          (fun {x y} hxy => congrFun (a.2.1 hxy) t) (fun {x y} hxy => congrFun (u.2.1 hxy) t)],
       fun _ => rfl,
       fun w => by
         have := lsum_wbdd s w a.1 u.1 a.2.2 (fun v => wbdd_of_continuousOn s (u.2.2 v).1.continuousOn)
         have h2 := this.smul (-1 : ℝ)
         exact h2.congr fun t _ => by simp⟩⟩)
    (fun a b u => by
      apply Subtype.ext; apply Prod.ext
      · funext w t
        simp only [Submodule.coe_add, Prod.fst_add, Pi.add_apply]
        rw [← neg_add, ← lsum_add]
        congr 1
      · funext w; simp)
    (fun c a u => by
      apply Subtype.ext; apply Prod.ext
      · funext w t
        simp only [Submodule.coe_smul, Prod.smul_fst, Pi.smul_apply]
        rw [smul_neg, ← lsum_smul]
        congr 1
      · funext w; simp)
    (fun a u v => by
      apply Subtype.ext; apply Prod.ext
      · funext w t
        simp only [Submodule.coe_add, Prod.fst_add, Pi.add_apply]
        rw [← neg_add, ← lsum_add]
        congr 1
        refine lsum_congr w fun v₁ v₂ => ?_
        simp
      · funext w; simp)
    (fun c a u => by
      apply Subtype.ext; apply Prod.ext
      · funext w t
        simp only [Submodule.coe_smul, Prod.smul_fst, Pi.smul_apply]
        rw [smul_neg, ← lsum_smul]
        congr 1
        refine lsum_congr w fun v₁ v₂ => ?_
        simp
      · funext w; simp)

/-- Auxiliary fact `Tmap_fst` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem Tmap_fst (a : Asub Idx V s) (u : Esub Idx V s) (w : List Idx) (t : ℝ) :
    (Tmap s a u).1.1 w t = - lsum w (fun v₁ v₂ => a.1 v₁ t (u.1 v₂ t)) := rfl

/-- Auxiliary fact `Tmap_snd` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem Tmap_snd (a : Asub Idx V s) (u : Esub Idx V s) (w : List Idx) :
    (Tmap s a u).1.2 w = 0 := rfl

/-- Auxiliary fact `Tmap_leibniz` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem Tmap_leibniz (i : Idx) (a : Asub Idx V s) (u : Esub Idx V s) :
    DF s i (Tmap s a u) = Tmap s (DA s i a) u + Tmap s a (DE s i u) := by
  apply Subtype.ext; apply Prod.ext
  · funext w t
    simp only [DF_apply_fst, Tmap_fst, Submodule.coe_add, Prod.fst_add, Pi.add_apply, DA_apply,
      DE_apply]
    rw [← neg_add]
    rfl
  · funext w; simp [Tmap_snd]

end

end TorusEuler.Paper.Lib.S53
