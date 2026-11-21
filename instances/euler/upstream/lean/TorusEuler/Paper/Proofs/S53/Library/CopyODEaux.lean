import TorusEuler.OscillatoryDerivativeEstimates
import TorusEuler.Paper.Proofs.S53.Library.Leaves

/-!
# S53 library: Lemma 5.3 chain: private helpers of the oscillatory word estimates

Generated copy (script `s53tools/mkcopy.py`) of the declarations phaseOperatorWord_add, phaseOperatorWord_zero, contDiff_slabSlice, norm_listMapSum_div_le, hasDerivWithinAt_translate, phaseOperatorWord_eventuallyEq, norm_word_inv_smul, phasePrimitive_const_smul of
`TorusEuler/OscillatoryDerivativeEstimates.lean`, placed in `TorusEuler.Paper.Lib.S53` so that the calls of the leaf results of
Lemmas 3.1, D.1 and D.3 resolve to the hypotheses carried by `Leaves`; the bounds of Lemma D.2 come from
`Leaves.d2` (`mul_of_D2`, `rescale_of_D2`) and the jets of Proposition 5.1 enter through the hypothesis
`Leaf2` / `Lib.S5a.LeafBounds`.
-/
noncomputable section


open ContinuousLinearMap Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace Interval Topology

namespace TorusEuler.Paper.Lib.S53

open TorusEuler
section WordDerivative

variable {ι P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Copy of the private library lemma `phaseOperatorWord_add`, made public in `Paper.Lib.S53` (glue). -/
theorem phaseOperatorWord_add (d : ι → P)
    {f g : P → E} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (w : List ι) (p : P) :
    phaseOperatorWord (fun i _ => d i) w (fun q => f q + g q) p =
      phaseOperatorWord (fun i _ => d i) w f p +
        phaseOperatorWord (fun i _ => d i) w g p := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih =>
    change fderiv ℝ (phaseOperatorWord (fun j _ => d j) w (fun q => f q + g q)) p (d i) = _
    rw [funext ih, fderiv_fun_add
      ((contDiff_phaseOperatorWord (fun _ => contDiff_const) hf w).differentiable (by simp) p)
      ((contDiff_phaseOperatorWord (fun _ => contDiff_const) hg w).differentiable (by simp) p)]
    rfl

/-- Copy of the private library lemma `phaseOperatorWord_zero`, made public in `Paper.Lib.S53` (glue). -/
theorem phaseOperatorWord_zero (d : ι → P) (w : List ι) :
    phaseOperatorWord (fun i _ => d i) w (0 : P → E) = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change phaseDirectionalDerivative (fun _ => d i) (phaseOperatorWord (fun j _ => d j) w 0) = 0
    rw [ih]
    funext x
    simp [phaseDirectionalDerivative, Pi.zero_def]

/-- Copy of the private library lemma `contDiff_slabSlice`, made public in `Paper.Lib.S53` (glue). -/
theorem contDiff_slabSlice {G : ℝ → P → E} {l r t : ℝ}
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (Icc l r ×ˢ (univ : Set P)))
    (ht : t ∈ Icc l r) : ContDiff ℝ ∞ (G t) :=
  contDiffOn_univ.mp (hG.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun p _ => ⟨ht, mem_univ p⟩))

end WordDerivative

section LinearODE

variable {ι P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Copy of the private library lemma `norm_listMapSum_div_le`, made public in `Paper.Lib.S53` (glue). -/
theorem norm_listMapSum_div_le {α : Type} (l : List α) (z : α → E)
    {g C : ℝ} (hg : 0 < g) (hC : ∀ i ∈ l, ‖z i‖ / g ≤ C) :
    ‖(l.map z).sum‖ / g ≤ (l.length : ℝ) * C := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    calc
      ‖z i + (l.map z).sum‖ / g ≤ (‖z i‖ + ‖(l.map z).sum‖) / g :=
        div_le_div_of_nonneg_right (norm_add_le _ _) hg.le
      _ ≤ (l.length : ℝ) * C + C := by
        rw [add_div, add_comm ((l.length : ℝ) * C) C]
        exact add_le_add (hC i (by simp)) (ih fun j hj => hC j (by simp [hj]))

omit [FiniteDimensional ℝ E] in
/-- Copy of the private library lemma `hasDerivWithinAt_translate`, made public in `Paper.Lib.S53` (glue). -/
theorem hasDerivWithinAt_translate {y : ℝ → E} {dy : E}
    {I J : Set ℝ} {c t : ℝ} (hd : HasDerivWithinAt y dy J (t + c))
    (hI : MapsTo (fun u => u + c) I J) :
    HasDerivWithinAt (fun u => y (u + c)) dy I t := by
  have h := hd.scomp t ((hasDerivAt_id t).add_const c).hasDerivWithinAt hI
  simpa only [Function.comp_def, id_eq, one_smul] using h

end LinearODE

section FiniteNorm

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Copy of the private library lemma `phaseOperatorWord_eventuallyEq`, made public in `Paper.Lib.S53` (glue). -/
theorem phaseOperatorWord_eventuallyEq {ι P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {D : ι → P → P}
    {f g : P → F} {p : P} (h : f =ᶠ[𝓝 p] g) (w : List ι) :
    phaseOperatorWord D w f =ᶠ[𝓝 p] phaseOperatorWord D w g := by
  induction w with
  | nil => exact h
  | cons i w ih =>
    exact (ih.fderiv (𝕜 := ℝ)).mono fun q hq => congrFun (congrArg DFunLike.coe hq) (D i q)

/-- Copy of the private library lemma `norm_word_inv_smul`, made public in `Paper.Lib.S53` (glue). -/
theorem norm_word_inv_smul {ι P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {d : ι → P} {f : P → F}
    (hf : ContDiff ℝ ∞ f) {g : ℝ} (hg : 0 < g) (w : List ι) (p : P) :
    ‖phaseOperatorWord (fun i _ => d i) w (fun q => g⁻¹ • f q) p‖ =
      ‖phaseOperatorWord (fun i _ => d i) w f p‖ / g := by
  rw [phaseOperatorWord_const_smul (fun _ => contDiff_const) hf, norm_smul_of_nonneg (inv_nonneg.mpr hg.le),
    div_eq_mul_inv, mul_comm]

end FiniteNorm

section FixedCoordinates

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end FixedCoordinates

section Pressure

variable {T : Type}

/-- Copy of the private library lemma `phasePrimitive_const_smul`, made public in `Paper.Lib.S53` (glue). -/
theorem phasePrimitive_const_smul (c : ℝ) (f : ℝ → ℝ) (s : ℝ) :
    phasePrimitive (fun σ => c • f σ) s = c • phasePrimitive f s := by
  simp only [phasePrimitive, phaseOscillation, intervalIntegral.integral_smul,
    phaseMean_const_smul, smul_sub]

end Pressure

end TorusEuler.Paper.Lib.S53

