import TorusEuler.FlowHigherVariations
import TorusEuler.HierarchyLinearRelayBounds
import TorusEuler.OscillatoryLabelRegularity

/-! Weighted derivative estimates for the transverse equation in §5.
The directions in a word may include the envelope and phase scales. -/

open ContinuousLinearMap Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace Interval Topology

namespace TorusEuler

section WordDerivative

variable {ι P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem phaseOperatorWord_eq_jet
    (d : ι → P) {f : P → E} (hf : ContDiff ℝ ∞ f) (w : List ι) (x : P) :
    phaseOperatorWord (fun i _ => d i) w f x =
      iteratedFDeriv ℝ w.length f x (fun i => d (w.get i)) := by
  induction w generalizing x with
  | nil => simp [phaseOperatorWord]
  | cons i w ih =>
    change fderiv ℝ (phaseOperatorWord (fun j _ => d j) w f) x (d i) =
      iteratedFDeriv ℝ (w.length + 1) f x (fun j => d ((i :: w).get j))
    rw [funext ih]
    have hd := hf.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top w.length) x
    rw [hd.iteratedFDeriv_succ_apply_left']
    rfl

private theorem phaseOperatorWord_add (d : ι → P)
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

private theorem phaseOperatorWord_zero (d : ι → P) (w : List ι) :
    phaseOperatorWord (fun i _ => d i) w (0 : P → E) = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change phaseDirectionalDerivative (fun _ => d i) (phaseOperatorWord (fun j _ => d j) w 0) = 0
    rw [ih]
    funext x
    simp [phaseDirectionalDerivative, Pi.zero_def]

private theorem contDiff_slabSlice {G : ℝ → P → E} {l r t : ℝ}
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (Icc l r ×ˢ (univ : Set P)))
    (ht : t ∈ Icc l r) : ContDiff ℝ ∞ (G t) :=
  contDiffOn_univ.mp (hG.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun p _ => ⟨ht, mem_univ p⟩))

end WordDerivative

section LinearODE

variable {ι P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 500000 in
/-- Parameter word derivatives of a linear solve satisfy the time derivative
of the differentiated right-hand side, including at both slab endpoints. -/
theorem phaseOperatorWord_linearODE_time
    (d : ι → P) (w : List ι) {A : ℝ → P → E →L[ℝ] E} {f x : ℝ → P → E}
    {T : ℝ} (hT : 0 < T)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (Icc 0 T ×ˢ (univ : Set P)))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set P)))
    (hx : ContDiffOn ℝ ∞ (Function.uncurry x) (Icc 0 T ×ˢ (univ : Set P)))
    (hxt : ∀ p t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun s => x s p) (A t p (x t p) + f t p) (Icc 0 T) t) :
    let R (t : ℝ) (p : P) := A t p (x t p) + f t p
    ContinuousOn (fun q : ℝ × P => phaseOperatorWord (fun i _ => d i) w (R q.1) q.2)
      (Icc 0 T ×ˢ (univ : Set P)) ∧
    ∀ p t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun s => phaseOperatorWord (fun i _ => d i) w (x s) p)
        (phaseOperatorWord (fun i _ => d i) w (R t) p) (Icc 0 T) t := by
  let I := Icc (0 : ℝ) T
  let S := I ×ˢ (univ : Set P)
  let R (t : ℝ) (p : P) := A t p (x t p) + f t p
  let Y (t : ℝ) (p : P) := (x t p, p)
  let F (t : ℝ) (z : E × P) : E × P := (A t z.2 z.1 + f t z.2, 0)
  let J := ContinuousLinearMap.fst ℝ E P
  have hR : ContDiffOn ℝ ∞ (Function.uncurry R) S :=
    (hA.clm_apply hx).add hf
  have hY : ContDiffOn ℝ ∞ (Function.uncurry Y) S := hx.prodMk contDiffOn_snd
  have hF : ContDiffOn ℝ ∞ (Function.uncurry F) (I ×ˢ (univ : Set (E × P))) := by
    have hProj : ContDiffOn ℝ ∞ (fun z : ℝ × (E × P) => (z.1, z.2.2))
        (I ×ˢ (univ : Set (E × P))) := contDiffOn_fst.prodMk contDiffOn_snd.snd
    have hMaps : MapsTo (fun z : ℝ × (E × P) => (z.1, z.2.2))
        (I ×ˢ (univ : Set (E × P))) S := fun z hz => ⟨hz.1, mem_univ z.2.2⟩
    exact (((hA.comp hProj hMaps).clm_apply contDiffOn_snd.fst).add
      (hf.comp hProj hMaps)).prodMk contDiffOn_const
  have hD (p : P) (t : ℝ) (ht : t ∈ I) :
      HasDerivWithinAt (fun s => Y s p) (F t (Y t p)) I t :=
    (hxt p t ht).prodMk (hasDerivWithinAt_const t I p)
  obtain ⟨hYt, _, hRc, hJets⟩ := trajectoryFamily_spatialJets w.length hT hF
    hY.continuousOn hD (contDiff_slabSlice hY ⟨le_rfl, hT.le⟩)
  let v (j : Fin w.length) := d (w.get j)
  let L : (P [×w.length]→L[ℝ] (E × P)) →L[ℝ] E :=
    J.comp (ContinuousMultilinearMap.apply ℝ (fun _ : Fin w.length => P) (E × P) v)
  have hProject (G : P → E × P) (hG : ContDiff ℝ w.length G) (p : P) :
      L (iteratedFDeriv ℝ w.length G p) =
        iteratedFDeriv ℝ w.length (J ∘ G) p v := by
    rw [J.iteratedFDeriv_comp_left hG.contDiffAt le_rfl]
    rfl
  have hRjet (t : ℝ) (ht : t ∈ I) (p : P) :
      L (iteratedFDeriv ℝ w.length (F t ∘ Y t) p) =
        phaseOperatorWord (fun i _ => d i) w (R t) p := by
    rw [hProject _ (((contDiff_slabSlice hF ht).of_le (by simp)).comp (hYt t ht)),
      phaseOperatorWord_eq_jet d (contDiff_slabSlice hR ht)]
    rfl
  have hxjet (t : ℝ) (ht : t ∈ I) (p : P) :
      L (iteratedFDeriv ℝ w.length (Y t) p) =
        phaseOperatorWord (fun i _ => d i) w (x t) p := by
    rw [hProject _ (hYt t ht), phaseOperatorWord_eq_jet d (contDiff_slabSlice hx ht)]
    rfl
  refine ⟨(L.continuous.comp_continuousOn hRc).congr
    (fun q hq => (hRjet q.1 hq.1 q.2).symm), fun p t ht => ?_⟩
  have h := L.hasFDerivAt.comp_hasDerivWithinAt t (hJets p t ht)
  change HasDerivWithinAt (fun s => L (iteratedFDeriv ℝ w.length (Y s) p))
    (L (iteratedFDeriv ℝ w.length (F t ∘ Y t) p)) I t at h
  rw [hRjet t ht p] at h
  exact h.congr_of_mem (fun s hs => (hxjet s hs p).symm) ht

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem norm_listMapSum_div_le {α : Type} (l : List α) (z : α → E)
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

set_option maxHeartbeats 700000 in
/-- A word derivative has the same weighted forward bound as the original
solve. Its additional source uses only positive-order coefficient words and
strictly lower-order solution words. -/
theorem norm_phaseOperatorWord_linearODE_le
    (d : ι → P) (w : List ι) {A : ℝ → P → E →L[ℝ] E} {f x : ℝ → P → E}
    {g dg : ℝ → ℝ} {T K C M B H : ℝ} {p : P} {t : ℝ}
    (hT : 0 < T) (hK : 0 ≤ K) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (Icc 0 T ×ˢ (univ : Set P)))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set P)))
    (hx : ContDiffOn ℝ ∞ (Function.uncurry x) (Icc 0 T ×ˢ (univ : Set P)))
    (hxt : ∀ q u, u ∈ Icc 0 T →
      HasDerivWithinAt (fun s => x s q) (A u q (x u q) + f u q) (Icc 0 T) u)
    (hg₀ : ∀ u ∈ Icc 0 T, 0 < g u)
    (hg : ∀ u ∈ Icc 0 T, HasDerivWithinAt g (dg u) (Icc 0 T) u)
    (hdg : ContinuousOn dg (Icc 0 T))
    (hStable : ∀ y : ℝ → E,
      (∀ u ∈ Icc 0 T, HasDerivWithinAt y (A u p (y u)) (Icc 0 T) u) →
      ∀ u ∈ Icc 0 T, ∀ v ∈ Icc u T, ‖y v‖ / g v ≤ K * (‖y u‖ / g u))
    (hinit : ‖phaseOperatorWord (fun i _ => d i) w (x 0) p‖ / g 0 ≤ B)
    (hsource : ∀ u ∈ Icc 0 T, ‖phaseOperatorWord (fun i _ => d i) w (f u) p‖ / g u ≤ H)
    (hcoeff : ∀ v, List.Sublist v w → v ≠ [] → ∀ u ∈ Icc 0 T,
      ‖phaseOperatorWord (fun i _ => d i) v (A u) p‖ ≤ C)
    (hprev : ∀ v, List.Sublist v w → v.length < w.length → ∀ u ∈ Icc 0 T,
      ‖phaseOperatorWord (fun i _ => d i) v (x u) p‖ / g u ≤ M)
    (ht : t ∈ Icc 0 T) :
    ‖phaseOperatorWord (fun i _ => d i) w (x t) p‖ / g t ≤
      K * (B + t * (H + (2 : ℝ) ^ w.length * C * M)) := by
  let I := Icc (0 : ℝ) T
  let D (i : ι) (_ : P) := d i
  let y (u : ℝ) := phaseOperatorWord D w (x u) p
  let R (u : ℝ) (q : P) := A u q (x u q) + f u q
  let Z (u : ℝ) := phaseOperatorWord D w (R u) p
  let W (u : ℝ) := Z u - A u p (y u)
  have hA' : ContinuousOn (fun u => A u p) I :=
    hA.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hu => ⟨hu, mem_univ p⟩)
  obtain ⟨hZ, hy⟩ := phaseOperatorWord_linearODE_time d w hT hA hf hx hxt
  have hyt (u : ℝ) (hu : u ∈ I) : HasDerivWithinAt y (Z u) I u := hy p u hu
  have hZc : ContinuousOn Z I :=
    hZ.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ hu => ⟨hu, mem_univ p⟩)
  have hW : ContinuousOn W I := hZc.sub (hA'.clm_apply (HasDerivWithinAt.continuousOn hyt))
  have hyODE (u : ℝ) (hu : u ∈ I) : HasDerivWithinAt y (A u p (y u) + W u) I u := by
    refine (hyt u hu).congr_deriv ?_
    dsimp only [W]
    abel
  have hb (u : ℝ) (hu : u ∈ I) : ‖W u‖ / g u ≤ H + (2 : ℝ) ^ w.length * C * M := by
    let L := (hierarchyLeibnizSplits w).filter (fun v => !v.1.isEmpty)
    let z (v : List ι × List ι) :=
      phaseOperatorWord D v.1 (A u) p (phaseOperatorWord D v.2 (x u) p)
    let eval : (E →L[ℝ] E) →L[ℝ] E →L[ℝ] E := (ContinuousLinearMap.apply ℝ E).flip
    have hAu := contDiff_slabSlice hA hu
    have hxu := contDiff_slabSlice hx hu
    have hfu := contDiff_slabSlice hf hu
    have hprod : ContDiff ℝ ∞ (fun q : P => A u q (x u q)) := hAu.clm_apply hxu
    have hcomm := phaseOperatorWord_bilinear_commutator eval
      (D := D) (fun _ => contDiff_const) hAu hxu w p
    change phaseOperatorWord D w (fun q => A u q (x u q)) p - A u p (y u) =
      (L.map z).sum at hcomm
    have hW_eq : W u = phaseOperatorWord D w (f u) p + (L.map z).sum := by
      change phaseOperatorWord D w (fun q => A u q (x u q) + f u q) p - A u p (y u) = _
      rw [phaseOperatorWord_add d hprod hfu]
      change phaseOperatorWord D w (fun q => A u q (x u q)) p +
        phaseOperatorWord D w (f u) p - A u p (y u) = _
      rw [add_comm, add_sub_assoc, hcomm]
    have hz (v : List ι × List ι) (hv : v ∈ L) : ‖z v‖ / g u ≤ C * M := by
      have hm := List.mem_filter.mp hv
      have hn : v.1 ≠ [] := by simpa using hm.2
      obtain ⟨h₁, h₂, _⟩ := hierarchyLeibnizSplits_spec hm.1
      have hw := hierarchyLeibnizSplits_order_lt hm.1 hn
      calc
        _ ≤ ‖phaseOperatorWord D v.1 (A u) p‖ * ‖phaseOperatorWord D v.2 (x u) p‖ / g u :=
          div_le_div_of_nonneg_right ((phaseOperatorWord D v.1 (A u) p).le_opNorm _) (hg₀ u hu).le
        _ = ‖phaseOperatorWord D v.1 (A u) p‖ * (‖phaseOperatorWord D v.2 (x u) p‖ / g u) :=
          mul_div_assoc _ _ _
        _ ≤ _ := mul_le_mul (hcoeff v.1 h₁ hn u hu) (hprev v.2 h₂ hw u hu)
          (div_nonneg (norm_nonneg _) (hg₀ u hu).le) hC
    have hc : (L.length : ℝ) ≤ (2 : ℝ) ^ w.length := by
      exact_mod_cast (List.length_filter_le _ _).trans_eq (length_hierarchyLeibnizSplits w)
    rw [hW_eq]
    calc
      _ ≤ ‖phaseOperatorWord D w (f u) p‖ / g u + ‖(L.map z).sum‖ / g u := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (norm_add_le _ _) (hg₀ u hu).le
      _ ≤ H + (L.length : ℝ) * (C * M) :=
        add_le_add (hsource u hu) (norm_listMapSum_div_le L z (hg₀ u hu) hz)
      _ ≤ _ := by
        rw [mul_assoc]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hc (mul_nonneg hC hM))
  have hd := weighted_linearODE_forced_norm_le hA' hW hg₀ hg hdg hStable hyODE ht
  have hgc := HasDerivWithinAt.continuousOn hg
  have hInt : IntervalIntegrable (fun u => ‖W u‖ / g u) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact (hW.norm.div hgc (fun u hu => (hg₀ u hu).ne')).mono (Icc_subset_Icc_right ht.2)
  have hInt_le : (∫ u in (0 : ℝ)..t, ‖W u‖ / g u) ≤
      t * (H + (2 : ℝ) ^ w.length * C * M) := by
    rw [← show (∫ _u in (0 : ℝ)..t, H + (2 : ℝ) ^ w.length * C * M) =
      t * (H + (2 : ℝ) ^ w.length * C * M) by simp; ring]
    exact intervalIntegral.integral_mono_on ht.1 hInt intervalIntegrable_const
      (fun u hu => hb u ⟨hu.1, hu.2.trans ht.2⟩)
  exact hd.trans (mul_le_mul_of_nonneg_left (add_le_add hinit hInt_le) hK)


/-- The order-dependent amplification from the coefficient commutator. Its
argument is the product of the forward bound, slab length, and the bound on
positive-order scaled coefficient derivatives. -/
def linearODEWordFactor (q : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => 1 + (2 : ℝ) ^ (n + 1) * q * linearODEWordFactor q n

theorem linearODEWordFactor_nonneg {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    0 ≤ linearODEWordFactor q n := by
  induction n with
  | zero => simp [linearODEWordFactor]
  | succ n ih =>
    rw [linearODEWordFactor]
    positivity

theorem linearODEWordFactor_mono {q r : ℝ} (hq : 0 ≤ q) (hqr : q ≤ r) (n : ℕ) :
    linearODEWordFactor q n ≤ linearODEWordFactor r n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [linearODEWordFactor]
    have hr := hq.trans hqr
    have hh := linearODEWordFactor_nonneg hq n
    exact add_le_add le_rfl (mul_le_mul
      (mul_le_mul_of_nonneg_left hqr (by positivity)) ih hh (by positivity))

set_option maxHeartbeats 700000 in
/-- The all-order weighted estimate on a set of labels and phases. The bound
involves derivatives of the actual solution of the ODE. If the positive-order
scaled coefficient bound satisfies `K * T * C ≤ 1`, the same constant
`linearODEWordFactor 1 N` applies to any carrier frequency. -/
theorem linearODE_wordBounds
    (d : ι → P) (N : ℕ) {A : ℝ → P → E →L[ℝ] E} {f x : ℝ → P → E}
    {g dg : ℝ → ℝ} {S : Set P} {T K C B H : ℝ}
    (hT : 0 < T) (hK : 0 ≤ K) (hC : 0 ≤ C) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (Icc 0 T ×ˢ (univ : Set P)))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set P)))
    (hx : ContDiffOn ℝ ∞ (Function.uncurry x) (Icc 0 T ×ˢ (univ : Set P)))
    (hxt : ∀ p t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun s => x s p) (A t p (x t p) + f t p) (Icc 0 T) t)
    (hg₀ : ∀ u ∈ Icc 0 T, 0 < g u)
    (hg : ∀ u ∈ Icc 0 T, HasDerivWithinAt g (dg u) (Icc 0 T) u)
    (hdg : ContinuousOn dg (Icc 0 T))
    (hStable : ∀ p ∈ S, ∀ y : ℝ → E,
      (∀ u ∈ Icc 0 T, HasDerivWithinAt y (A u p (y u)) (Icc 0 T) u) →
      ∀ u ∈ Icc 0 T, ∀ v ∈ Icc u T, ‖y v‖ / g v ≤ K * (‖y u‖ / g u))
    (hinit : ∀ w : List ι, w.length ≤ N → ∀ p ∈ S,
      ‖phaseOperatorWord (fun i _ => d i) w (x 0) p‖ / g 0 ≤ B)
    (hsource : ∀ w : List ι, w.length ≤ N → ∀ p ∈ S, ∀ u ∈ Icc 0 T,
      ‖phaseOperatorWord (fun i _ => d i) w (f u) p‖ / g u ≤ H)
    (hcoeff : ∀ w : List ι, w.length ≤ N → w ≠ [] → ∀ p ∈ S, ∀ u ∈ Icc 0 T,
      ‖phaseOperatorWord (fun i _ => d i) w (A u) p‖ ≤ C) :
    ∀ w : List ι, w.length ≤ N → ∀ p ∈ S, ∀ u ∈ Icc 0 T,
      ‖phaseOperatorWord (fun i _ => d i) w (x u) p‖ / g u ≤
        linearODEWordFactor (K * T * C) N * (K * (B + T * H)) := by
  let α := K * T * C
  let V := K * (B + T * H)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  let step (w : List ι) (p : P) (u : ℝ) :=
    ‖phaseOperatorWord (fun i _ => d i) w (x u) p‖ / g u
  suffices h : ∀ n ≤ N, ∀ w : List ι, w.length ≤ n → ∀ p ∈ S, ∀ u ∈ Icc 0 T,
      step w p u ≤ linearODEWordFactor α n * V from h N le_rfl
  intro n
  induction n with
  | zero =>
    intro hn w hw p hp u hu
    have hw0 : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hw)
    subst w
    have h := norm_phaseOperatorWord_linearODE_le d [] (p := p) (t := u) (M := 0)
      hT hK hC le_rfl hA hf hx hxt hg₀ hg hdg (hStable p hp)
      (hinit [] (hw.trans hn) p hp) (hsource [] (hw.trans hn) p hp)
      (fun v hv hvn => (hvn (List.sublist_nil.mp hv)).elim)
      (fun v _ hv => (Nat.not_lt_zero v.length hv).elim) hu
    change step [] p u ≤ _
    refine h.trans ?_
    simp only [mul_zero, add_zero, linearODEWordFactor, one_mul]
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_right hu.2 hH)) hK
  | succ n ih =>
    intro hn w hw p hp u hu
    have hnN : n ≤ N := (Nat.le_succ n).trans hn
    let M := linearODEWordFactor α n * V
    have hM : 0 ≤ M := mul_nonneg (linearODEWordFactor_nonneg hα n) hV
    have h := norm_phaseOperatorWord_linearODE_le d w (p := p) (t := u) (M := M)
      hT hK hC hM hA hf hx hxt hg₀ hg hdg (hStable p hp)
      (hinit w (hw.trans hn) p hp) (hsource w (hw.trans hn) p hp)
      (fun v hv hvn => hcoeff v (hv.length_le.trans (hw.trans hn)) hvn p hp)
      (fun v _ hv r hr => ih hnN v (Nat.lt_succ_iff.mp (hv.trans_le hw)) p hp r hr) hu
    refine h.trans ?_
    have hpw : (2 : ℝ) ^ w.length ≤ (2 : ℝ) ^ (n + 1) :=
      pow_le_pow_right₀ (by norm_num) hw
    have hq : H + (2 : ℝ) ^ w.length * C * M ≤ H + (2 : ℝ) ^ (n + 1) * C * M := by
      gcongr
    calc
      _ ≤ K * (B + T * (H + (2 : ℝ) ^ (n + 1) * C * M)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl
          (mul_le_mul hu.2 hq (by positivity) hT.le)) hK
      _ = _ := by rw [linearODEWordFactor]; dsimp [M, V, α]; ring


omit [FiniteDimensional ℝ E] in
private theorem hasDerivWithinAt_translate {y : ℝ → E} {dy : E}
    {I J : Set ℝ} {c t : ℝ} (hd : HasDerivWithinAt y dy J (t + c))
    (hI : MapsTo (fun u => u + c) I J) :
    HasDerivWithinAt (fun u => y (u + c)) dy I t := by
  have h := hd.scomp t ((hasDerivAt_id t).add_const c).hasDerivWithinAt hI
  simpa only [Function.comp_def, id_eq, one_smul] using h

set_option maxHeartbeats 800000 in
/-- The weighted derivative recurrence on a slab with arbitrary starting
time, including the launch interval of the oscillatory hierarchy. -/
theorem linearODE_wordBounds_Icc
    (d : ι → P) (N : ℕ) {A : ℝ → P → E →L[ℝ] E} {f x : ℝ → P → E}
    {g dg : ℝ → ℝ} {S : Set P} {l r K C B H : ℝ}
    (hlr : l < r) (hK : 0 ≤ K) (hC : 0 ≤ C) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (Icc l r ×ˢ (univ : Set P)))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc l r ×ˢ (univ : Set P)))
    (hx : ContDiffOn ℝ ∞ (Function.uncurry x) (Icc l r ×ˢ (univ : Set P)))
    (hxt : ∀ p t, t ∈ Icc l r →
      HasDerivWithinAt (fun s => x s p) (A t p (x t p) + f t p) (Icc l r) t)
    (hg₀ : ∀ u ∈ Icc l r, 0 < g u)
    (hg : ∀ u ∈ Icc l r, HasDerivWithinAt g (dg u) (Icc l r) u)
    (hdg : ContinuousOn dg (Icc l r))
    (hStable : ∀ p ∈ S, ∀ y : ℝ → E,
      (∀ u ∈ Icc l r, HasDerivWithinAt y (A u p (y u)) (Icc l r) u) →
      ∀ u ∈ Icc l r, ∀ v ∈ Icc u r, ‖y v‖ / g v ≤ K * (‖y u‖ / g u))
    (hinit : ∀ w : List ι, w.length ≤ N → ∀ p ∈ S,
      ‖phaseOperatorWord (fun i _ => d i) w (x l) p‖ / g l ≤ B)
    (hsource : ∀ w : List ι, w.length ≤ N → ∀ p ∈ S, ∀ u ∈ Icc l r,
      ‖phaseOperatorWord (fun i _ => d i) w (f u) p‖ / g u ≤ H)
    (hcoeff : ∀ w : List ι, w.length ≤ N → w ≠ [] → ∀ p ∈ S, ∀ u ∈ Icc l r,
      ‖phaseOperatorWord (fun i _ => d i) w (A u) p‖ ≤ C) :
    ∀ w : List ι, w.length ≤ N → ∀ p ∈ S, ∀ u ∈ Icc l r,
      ‖phaseOperatorWord (fun i _ => d i) w (x u) p‖ / g u ≤
        linearODEWordFactor (K * (r - l) * C) N * (K * (B + (r - l) * H)) := by
  let T := r - l
  let A' (t : ℝ) := A (t + l)
  let f' (t : ℝ) := f (t + l)
  let x' (t : ℝ) := x (t + l)
  let g' (t : ℝ) := g (t + l)
  let dg' (t : ℝ) := dg (t + l)
  have hT : 0 < T := sub_pos.mpr hlr
  have hmap : MapsTo (fun u => u + l) (Icc 0 T) (Icc l r) := by
    intro u hu
    exact ⟨by linarith [hu.1], by have := hu.2; dsimp [T] at this; linarith⟩
  have hback : MapsTo (fun u => u + (-l)) (Icc l r) (Icc 0 T) := by
    intro u hu
    exact ⟨by linarith [hu.1], by dsimp [T]; linarith [hu.2]⟩
  have hproj : ContDiffOn ℝ ∞ (fun z : ℝ × P => (z.1 + l, z.2)) (Icc 0 T ×ˢ univ) :=
    (contDiffOn_fst.add contDiffOn_const).prodMk contDiffOn_snd
  have hmaps : MapsTo (fun z : ℝ × P => (z.1 + l, z.2))
      (Icc 0 T ×ˢ univ) (Icc l r ×ˢ univ) := fun z hz => ⟨hmap hz.1, mem_univ _⟩
  have hA' : ContDiffOn ℝ ∞ (Function.uncurry A') (Icc 0 T ×ˢ univ) := hA.comp hproj hmaps
  have hf' : ContDiffOn ℝ ∞ (Function.uncurry f') (Icc 0 T ×ˢ univ) := hf.comp hproj hmaps
  have hx' : ContDiffOn ℝ ∞ (Function.uncurry x') (Icc 0 T ×ˢ univ) := hx.comp hproj hmaps
  have hxt' (p : P) (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun s => x' s p) (A' t p (x' t p) + f' t p) (Icc 0 T) t :=
    hasDerivWithinAt_translate (hxt p (t + l) (hmap ht)) hmap
  have hg'₀ (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < g' t := hg₀ (t + l) (hmap ht)
  have hgt' (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivWithinAt g' (dg' t) (Icc 0 T) t :=
    hasDerivWithinAt_translate (hg (t + l) (hmap ht)) hmap
  have hdg' : ContinuousOn dg' (Icc 0 T) :=
    hdg.comp (continuous_id.add continuous_const).continuousOn hmap
  have hStable' (p : P) (hp : p ∈ S) (y : ℝ → E)
      (hy : ∀ u ∈ Icc 0 T, HasDerivWithinAt y (A' u p (y u)) (Icc 0 T) u)
      (u : ℝ) (hu : u ∈ Icc 0 T) (v : ℝ) (hv : v ∈ Icc u T) :
      ‖y v‖ / g' v ≤ K * (‖y u‖ / g' u) := by
    have hY (s : ℝ) (hs : s ∈ Icc l r) :
        HasDerivWithinAt (fun t => y (t + (-l))) (A s p (y (s + (-l)))) (Icc l r) s := by
      have h := hasDerivWithinAt_translate (hy (s + (-l)) (hback hs)) hback
      simpa only [A', neg_add_cancel_right] using h
    have hv' : v + l ∈ Icc (u + l) r :=
      ⟨add_le_add_left hv.1 l, (hmap (show v ∈ Icc 0 T from ⟨hu.1.trans hv.1, hv.2⟩)).2⟩
    have h := hStable p hp (fun s => y (s + (-l))) hY (u + l) (hmap hu) (v + l) hv'
    simpa only [g', add_neg_cancel_right] using h
  have hinit' (w : List ι) (hw : w.length ≤ N) (p : P) (hp : p ∈ S) :
      ‖phaseOperatorWord (fun i _ => d i) w (x' 0) p‖ / g' 0 ≤ B := by
    simpa only [x', g', zero_add] using hinit w hw p hp
  have h := linearODE_wordBounds d N (A := A') (f := f') (x := x') (g := g') (dg := dg')
    (S := S) hT hK hC hB hH hA' hf' hx' hxt' hg'₀ hgt' hdg' hStable' hinit'
    (fun w hw p hp t ht => hsource w hw p hp (t + l) (hmap ht))
    (fun w hw hn p hp t ht => hcoeff w hw hn p hp (t + l) (hmap ht))
  intro w hw p hp u hu
  simpa only [x', g', neg_add_cancel_right, T] using h w hw p hp (u + (-l)) (hback hu)


end LinearODE

section FiniteNorm

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem phaseOperatorWord_eventuallyEq {ι P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {D : ι → P → P}
    {f g : P → F} {p : P} (h : f =ᶠ[𝓝 p] g) (w : List ι) :
    phaseOperatorWord D w f =ᶠ[𝓝 p] phaseOperatorWord D w g := by
  induction w with
  | nil => exact h
  | cons i w ih =>
    exact (ih.fderiv (𝕜 := ℝ)).mono fun q hq => congrFun (congrArg DFunLike.coe hq) (D i q)

private theorem norm_word_inv_smul {ι P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {d : ι → P} {f : P → F}
    (hf : ContDiff ℝ ∞ f) {g : ℝ} (hg : 0 < g) (w : List ι) (p : P) :
    ‖phaseOperatorWord (fun i _ => d i) w (fun q => g⁻¹ • f q) p‖ =
      ‖phaseOperatorWord (fun i _ => d i) w f p‖ / g := by
  rw [phaseOperatorWord_const_smul (fun _ => contDiff_const) hf, norm_smul_of_nonneg (inv_nonneg.mpr hg.le),
    div_eq_mul_inv, mul_comm]

set_option maxHeartbeats 900000 in
/-- The weighted derivative estimate applies to localized initial data
and forcing on the active interval. Stability and positive-order
coefficient estimates are used on their common closed support. -/
theorem linearODE_weightedHierarchyWordBound_of_initial
    {A : ℝ → (Vec3 × ℝ) → E →L[ℝ] E} {f x : ℝ → (Vec3 × ℝ) → E}
    {g dg : ℝ → ℝ} {S : Set (Vec3 × ℝ)} {l r K C Ccomm B H ℓ h : ℝ} (N : ℕ)
    (hlr : l < r) (hK : 0 ≤ K) (hC : 0 ≤ C) (hcomm : K * (r - l) * C ≤ Ccomm)
    (hS : IsClosed S)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (Icc l r ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc l r ×ˢ univ))
    (hx : ContDiffOn ℝ ∞ (Function.uncurry x) (Icc l r ×ˢ univ))
    (hx₀ : ∀ p ∉ S, x l p = 0)
    (hxt : ∀ p t, t ∈ Icc l r →
      HasDerivWithinAt (fun s => x s p) (A t p (x t p) + f t p) (Icc l r) t)
    (hfs : ∀ p ∉ S, ∀ u ∈ Icc l r, f u p = 0)
    (hg₀ : ∀ u ∈ Icc l r, 0 < g u)
    (hg : ∀ u ∈ Icc l r, HasDerivWithinAt g (dg u) (Icc l r) u)
    (hdg : ContinuousOn dg (Icc l r))
    (hStable : ∀ p ∈ S, ∀ y : ℝ → E,
      (∀ u ∈ Icc l r, HasDerivWithinAt y (A u p (y u)) (Icc l r) u) →
      ∀ u ∈ Icc l r, ∀ v ∈ Icc u r, ‖y v‖ / g v ≤ K * (‖y u‖ / g u))
    (hinit : HierarchyRelayWordBound ℓ h N B
      (fun (_ : Icc l r) p => (g l)⁻¹ • x l p))
    (hsource : HierarchyRelayWordBound ℓ h N H
      (fun (u : Icc l r) p => (g u)⁻¹ • f u p))
    (hcoeff : ∀ w ∈ hierarchyAdmissibleWords (Fin 4) N, w ≠ [] → ∀ p ∈ S, ∀ u ∈ Icc l r,
      ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (A u) p‖ ≤ C) :
    HierarchyRelayWordBound ℓ h N (linearODEWordFactor Ccomm N * (K * (B + (r - l) * H)))
      (fun (u : Icc l r) p => (g u)⁻¹ • x u p) := by
  let d (i : Fin 4) : Vec3 × ℝ := hierarchyMixedDirection ℓ h i 0
  have hd : (fun i (_ : Vec3 × ℝ) => d i) = hierarchyMixedDirection ℓ h := rfl
  have hl : l ∈ Icc l r := ⟨le_rfl, hlr.le⟩
  have hT : 0 ≤ r - l := sub_nonneg.mpr hlr.le
  have hα : 0 ≤ K * (r - l) * C := by positivity
  have hB : 0 ≤ linearODEWordFactor Ccomm N * (K * (B + (r - l) * H)) := by
    exact mul_nonneg (linearODEWordFactor_nonneg (hα.trans hcomm) N)
      (mul_nonneg hK (add_nonneg hinit.1 (mul_nonneg hT hsource.1)))
  have hs (w : List (Fin 4)) (hw : w.length ≤ N) :
      w.mergeSort ∈ hierarchyAdmissibleWords (Fin 4) N :=
    mem_hierarchyAdmissibleWords.mpr
      ⟨(List.mergeSort_perm _ _).length_eq.le.trans hw, List.pairwise_mergeSort' _ _⟩
  have hsource' (w : List (Fin 4)) (hw : w.length ≤ N) (p : Vec3 × ℝ) (u : ℝ) (hu : u ∈ Icc l r) :
      ‖phaseOperatorWord (fun i _ => d i) w (f u) p‖ / g u ≤ H := by
    have hfu := contDiff_slabSlice hf hu
    rw [← phaseOperatorWord_constantDirections_perm d hfu (List.mergeSort_perm w _),
      ← norm_word_inv_smul hfu (hg₀ u hu), hd]
    exact hsource.2 (w.mergeSort) (hs w hw) ⟨u, hu⟩ p
  have hcoeff' (w : List (Fin 4)) (hw : w.length ≤ N) (hn : w ≠ [])
      (p : Vec3 × ℝ) (hp : p ∈ S) (u : ℝ) (hu : u ∈ Icc l r) :
      ‖phaseOperatorWord (fun i _ => d i) w (A u) p‖ ≤ C := by
    have hperm : w.mergeSort.Perm w := List.mergeSort_perm _ _
    have hnil : w.mergeSort ≠ [] := fun h => hn (List.Perm.nil_eq (h ▸ hperm)).symm
    rw [← phaseOperatorWord_constantDirections_perm d (contDiff_slabSlice hA hu) hperm, hd]
    exact hcoeff (w.mergeSort) (hs w hw) hnil p hp u hu
  have hinitial (w : List (Fin 4)) (hw : w.length ≤ N) (p : Vec3 × ℝ) :
      ‖phaseOperatorWord (fun i _ => d i) w (x l) p‖ / g l ≤ B := by
    have hxl := contDiff_slabSlice hx hl
    rw [← phaseOperatorWord_constantDirections_perm d hxl (List.mergeSort_perm w _),
      ← norm_word_inv_smul hxl (hg₀ l hl), hd]
    exact hinit.2 (w.mergeSort) (hs w hw) ⟨l, hl⟩ p
  have hwords := linearODE_wordBounds_Icc d N (S := S) hlr hK hC hinit.1 hsource.1
    hA hf hx hxt hg₀ hg hdg hStable (fun w hw p _ => hinitial w hw p)
    (fun w hw p _ => hsource' w hw p) hcoeff'
  have hxOutside (p : Vec3 × ℝ) (hp : p ∉ S) (u : ℝ) (hu : u ∈ Icc l r) : x u p = 0 := by
    have hAp : ContinuousOn (fun t => A t p) (Icc l r) :=
      hA.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun _ ht => ⟨ht, mem_univ p⟩)
    have hXp (t : ℝ) (ht : t ∈ Icc l r) :
        HasDerivWithinAt (fun s => x s p) (A t p (x t p)) (Icc l r) t := by
      simpa only [hfs p hp t ht, add_zero] using hxt p t ht
    exact linearODE_unique_of_mem (y := fun _ => (0 : E)) ordConnected_Icc hl hAp hXp
      (fun t _ => by simpa only [map_zero] using hasDerivWithinAt_const t (Icc l r) (0 : E))
      (hx₀ p hp) hu
  refine ⟨hB, fun w hw u p => ?_⟩
  rw [← hd, norm_word_inv_smul (contDiff_slabSlice hx u.property) (hg₀ u u.property)]
  by_cases hp : p ∈ S
  · refine (hwords w (mem_hierarchyAdmissibleWords.mp hw).1 p hp u u.property).trans ?_
    exact mul_le_mul_of_nonneg_right (linearODEWordFactor_mono hα hcomm N)
      (mul_nonneg hK (add_nonneg hinit.1 (mul_nonneg hT hsource.1)))
  · have hN : ∀ᶠ q in 𝓝 p, q ∈ Sᶜ := hS.isOpen_compl.mem_nhds hp
    have heq : x u =ᶠ[𝓝 p] (0 : Vec3 × ℝ → E) :=
      hN.mono fun q hq => hxOutside q hq u u.property
    rw [(phaseOperatorWord_eventuallyEq (D := fun i _ => d i) heq w).eq_of_nhds,
      phaseOperatorWord_zero, Pi.zero_apply, norm_zero, zero_div]
    exact hB

/-- Zero-start instance of the localized weighted derivative estimate. -/
theorem linearODE_weightedHierarchyWordBound
    {A : ℝ → (Vec3 × ℝ) → E →L[ℝ] E} {f x : ℝ → (Vec3 × ℝ) → E}
    {g dg : ℝ → ℝ} {S : Set (Vec3 × ℝ)} {l r K C Ccomm H ℓ h : ℝ} (N : ℕ)
    (hlr : l < r) (hK : 0 ≤ K) (hC : 0 ≤ C) (hcomm : K * (r - l) * C ≤ Ccomm)
    (hS : IsClosed S)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (Icc l r ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc l r ×ˢ univ))
    (hx : ContDiffOn ℝ ∞ (Function.uncurry x) (Icc l r ×ˢ univ))
    (hx₀ : x l = 0)
    (hxt : ∀ p t, t ∈ Icc l r →
      HasDerivWithinAt (fun s => x s p) (A t p (x t p) + f t p) (Icc l r) t)
    (hfs : ∀ p ∉ S, ∀ u ∈ Icc l r, f u p = 0)
    (hg₀ : ∀ u ∈ Icc l r, 0 < g u)
    (hg : ∀ u ∈ Icc l r, HasDerivWithinAt g (dg u) (Icc l r) u)
    (hdg : ContinuousOn dg (Icc l r))
    (hStable : ∀ p ∈ S, ∀ y : ℝ → E,
      (∀ u ∈ Icc l r, HasDerivWithinAt y (A u p (y u)) (Icc l r) u) →
      ∀ u ∈ Icc l r, ∀ v ∈ Icc u r, ‖y v‖ / g v ≤ K * (‖y u‖ / g u))
    (hsource : HierarchyRelayWordBound ℓ h N H
      (fun (u : Icc l r) p => (g u)⁻¹ • f u p))
    (hcoeff : ∀ w ∈ hierarchyAdmissibleWords (Fin 4) N, w ≠ [] → ∀ p ∈ S, ∀ u ∈ Icc l r,
      ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (A u) p‖ ≤ C) :
    HierarchyRelayWordBound ℓ h N (linearODEWordFactor Ccomm N * (K * ((r - l) * H)))
      (fun (u : Icc l r) p => (g u)⁻¹ • x u p) := by
  have hInit : HierarchyRelayWordBound ℓ h N 0
      (fun (_ : Icc l r) p => (g l)⁻¹ • x l p) := by
    refine ⟨le_rfl, fun w _ _ p => ?_⟩
    simp only [hx₀, Pi.zero_apply, smul_zero]
    change ‖phaseOperatorWord (fun i (_ : Vec3 × ℝ) => hierarchyMixedDirection ℓ h i 0)
      w (0 : Vec3 × ℝ → E) p‖ ≤ 0
    rw [phaseOperatorWord_zero, Pi.zero_apply, norm_zero]
  simpa only [zero_add] using linearODE_weightedHierarchyWordBound_of_initial
    N hlr hK hC hcomm hS hA hf hx (fun p _ => by simp [hx₀]) hxt hfs
    hg₀ hg hdg hStable hInit hsource hcoeff

end FiniteNorm

section FixedCoordinates

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Reading the transverse components of the physical solution yields the
same forced equation in the fixed plane used by the weighted estimates. -/
theorem hasDerivWithinAt_oscillatory_fixedCoordinates
    {I : Set ℝ} {t : ℝ} {J : ℝ → F →L[ℝ] E} {R : ℝ → E →L[ℝ] F}
    {V : ℝ → E} {dR : E →L[ℝ] F} {M : E →L[ℝ] E} {κ f : E} {q : ℝ}
    (ht : t ∈ I) (hI : UniqueDiffWithinAt ℝ I t)
    (hRJ : ∀ u ∈ I, (R u).comp (J u) = ContinuousLinearMap.id ℝ F)
    (hJR : (J t).comp (R t) = oscillatoryTransverseProjection κ)
    (hJ : HasDerivWithinAt J (M.comp (J t)) I t)
    (hR : HasDerivWithinAt R dR I t)
    (hV : HasDerivWithinAt V (f - M (V t) - q • κ) I t)
    (hVκ : ⟪κ, V t⟫_ℝ = 0) :
    HasDerivWithinAt (fun u => R u (V u))
      (((-2 : ℝ) • (R t).comp (M.comp (J t))) (R t (V t)) + R t f) I t := by
  let v := R t (V t)
  have hVlift : J t v = V t := by
    change ((J t).comp (R t)) (V t) = V t
    rw [hJR, oscillatoryTransverseProjection_apply, hVκ, zero_div, zero_smul, sub_zero]
  have hproj : oscillatoryTransverseProjection κ κ = 0 := by
    by_cases hk : κ = 0
    · rw [hk, map_zero]
    rw [oscillatoryTransverseProjection_apply, real_inner_self_eq_norm_sq,
      div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr hk)), one_smul, sub_self]
  have hLiftκ : J t (R t κ) = 0 := by
    change ((J t).comp (R t)) κ = _
    rw [hJR, hproj]
  have hread (u : ℝ) (hu : u ∈ I) (a : F) : R u (J u a) = a :=
    DFunLike.congr_fun (hRJ u hu) a
  have hRκ : R t κ = 0 := by
    rw [← hread t ht (R t κ), hLiftκ, map_zero]
  have hJv : HasDerivWithinAt (fun u => J u v) (M (J t v)) I t := by
    let ev : (F →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E v
    exact ev.hasFDerivAt.comp_hasDerivWithinAt t hJ
  have hConst : HasDerivWithinAt (fun _ : ℝ => v)
      (dR (J t v) + R t (M (J t v))) I t :=
    (hR.clm_apply hJv).congr_of_mem (fun u hu => (hread u hu v).symm) ht
  have hr : dR (V t) + R t (M (V t)) = 0 := by
    rw [← hVlift, ← hConst.derivWithin hI]
    exact (hasDerivWithinAt_const t I v).derivWithin hI
  refine (hR.clm_apply hV).congr_deriv ?_
  change dR (V t) + R t (f - M (V t) - q • κ) =
    (-2 : ℝ) • R t (M (J t v)) + R t f
  rw [map_sub, map_sub, map_smul, hRκ, smul_zero, sub_zero, hVlift,
    show dR (V t) = -R t (M (V t)) from eq_neg_of_add_eq_zero_left hr]
  rw [show (-2 : ℝ) = -(1 + 1) by norm_num, neg_smul, add_smul, one_smul]
  abel

end FixedCoordinates

set_option maxHeartbeats 1300000 in
/-- The finite weighted norm of the physical transverse velocity follows
from the fixed-plane forward estimate and the word bounds of the two
coframes. The force is measured in physical coordinates. -/
theorem oscillatoryVelocity_weightedWordBound_of_initial
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {J : ℝ → Vec3 → F →L[ℝ] Vec3} {R : ℝ → Vec3 → Vec3 →L[ℝ] F}
    {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3}
    {V f : ℝ → (Vec3 × ℝ) → Vec3} {q : ℝ → (Vec3 × ℝ) → ℝ}
    {g dg : ℝ → ℝ} {S : Set (Vec3 × ℝ)} {l r K C Ccomm CJ CR B H ℓ h : ℝ}
    (N : ℕ) (hlr : l < r) (hK : 0 ≤ K) (hC : 0 ≤ C) (hcomm : K * (r - l) * C ≤ Ccomm)
    (hS : IsClosed S)
    (hJ : ContDiffOn ℝ ∞ (Function.uncurry J) (Icc l r ×ˢ univ))
    (hR : ContDiffOn ℝ ∞ (Function.uncurry R) (Icc l r ×ˢ univ))
    (hM : ContDiffOn ℝ ∞ (Function.uncurry M) (Icc l r ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc l r ×ˢ univ))
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc l r ×ˢ univ))
    (hV₀ : ∀ p ∉ S, V l p = 0)
    (hJt : ∀ a t, t ∈ Icc l r → HasDerivWithinAt (fun u => J u a) ((M t a).comp (J t a)) (Icc l r) t)
    (hRJ : ∀ a t, t ∈ Icc l r → (R t a).comp (J t a) = .id ℝ F)
    (hJR : ∀ a t, t ∈ Icc l r → (J t a).comp (R t a) = oscillatoryTransverseProjection (κ t a))
    (hVt : ∀ p t, t ∈ Icc l r → HasDerivWithinAt (fun u => V u p)
      (f t p - M t p.1 (V t p) - q t p • κ t p.1) (Icc l r) t)
    (hVκ : ∀ p t, t ∈ Icc l r → ⟪κ t p.1, V t p⟫_ℝ = 0)
    (hfs : ∀ p ∉ S, ∀ u ∈ Icc l r, f u p = 0)
    (hg₀ : ∀ u ∈ Icc l r, 0 < g u)
    (hg : ∀ u ∈ Icc l r, HasDerivWithinAt g (dg u) (Icc l r) u)
    (hdg : ContinuousOn dg (Icc l r))
    (hJN : HierarchyRelayWordBound ℓ h N CJ (fun (u : Icc l r) p => J u p.1))
    (hRN : HierarchyRelayWordBound ℓ h N CR (fun (u : Icc l r) p => R u p.1))
    (hInit : HierarchyRelayWordBound ℓ h N B (fun (_ : Icc l r) p => (g l)⁻¹ • V l p))
    (hfN : HierarchyRelayWordBound ℓ h N H (fun (u : Icc l r) p => (g u)⁻¹ • f u p)) :
    let A (t : ℝ) (p : Vec3 × ℝ) := (-2 : ℝ) • (R t p.1).comp ((M t p.1).comp (J t p.1))
    (∀ p ∈ S, ∀ y : ℝ → F,
      (∀ u ∈ Icc l r, HasDerivWithinAt y (A u p (y u)) (Icc l r) u) →
      ∀ u ∈ Icc l r, ∀ v ∈ Icc u r, ‖y v‖ / g v ≤ K * (‖y u‖ / g u)) →
    (∀ w ∈ hierarchyAdmissibleWords (Fin 4) N, w ≠ [] → ∀ p ∈ S, ∀ u ∈ Icc l r,
      ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (A u) p‖ ≤ C) →
    HierarchyRelayWordBound ℓ h N
      ((2 : ℝ) ^ N * CJ * (linearODEWordFactor Ccomm N *
        (K * ((2 : ℝ) ^ N * CR * B + (r - l) * ((2 : ℝ) ^ N * CR * H)))))
      (fun (u : Icc l r) p => (g u)⁻¹ • V u p) := by
  let A (t : ℝ) (p : Vec3 × ℝ) := (-2 : ℝ) • (R t p.1).comp ((M t p.1).comp (J t p.1))
  let X (t : ℝ) (p : Vec3 × ℝ) := R t p.1 (V t p)
  let fR (t : ℝ) (p : Vec3 × ℝ) := R t p.1 (f t p)
  let D := Icc l r ×ˢ (univ : Set (Vec3 × ℝ))
  dsimp only
  intro hStable hcoeff
  have hproj : ContDiffOn ℝ ∞ (fun z : ℝ × (Vec3 × ℝ) => (z.1, z.2.1)) D :=
    contDiffOn_fst.prodMk contDiffOn_snd.fst
  have hm : MapsTo (fun z : ℝ × (Vec3 × ℝ) => (z.1, z.2.1)) D
      (Icc l r ×ˢ (univ : Set Vec3)) := fun z hz => ⟨hz.1, mem_univ z.2.1⟩
  have hJ' : ContDiffOn ℝ ∞ (Function.uncurry (fun t (p : Vec3 × ℝ) => J t p.1)) D :=
    hJ.comp hproj hm
  have hR' : ContDiffOn ℝ ∞ (Function.uncurry (fun t (p : Vec3 × ℝ) => R t p.1)) D :=
    hR.comp hproj hm
  have hM' : ContDiffOn ℝ ∞ (Function.uncurry (fun t (p : Vec3 × ℝ) => M t p.1)) D :=
    hM.comp hproj hm
  have hA : ContDiffOn ℝ ∞ (Function.uncurry A) D :=
    (contDiffOn_const (c := (-2 : ℝ))).smul (hR'.clm_comp (hM'.clm_comp hJ'))
  have hX : ContDiffOn ℝ ∞ (Function.uncurry X) D := hR'.clm_apply hV
  have hfR : ContDiffOn ℝ ∞ (Function.uncurry fR) D := hR'.clm_apply hf
  have hX₀ (p : Vec3 × ℝ) (hp : p ∉ S) : X l p = 0 := by simp [X, hV₀ p hp]
  have hXode (p : Vec3 × ℝ) (t : ℝ) (ht : t ∈ Icc l r) :
      HasDerivWithinAt (fun u => X u p) (A t p (X t p) + fR t p) (Icc l r) t := by
    have hRc : ContDiffOn ℝ ∞ (fun u => R u p.1) (Icc l r) :=
      hR.comp (contDiff_id.prodMk contDiff_const).contDiffOn
        (fun _ hu => ⟨hu, mem_univ p.1⟩)
    have hRd : HasDerivWithinAt (fun u => R u p.1)
        (derivWithin (fun u => R u p.1) (Icc l r) t) (Icc l r) t :=
      (hRc.differentiableOn (by simp) t ht).hasDerivWithinAt
    have hd := hasDerivWithinAt_oscillatory_fixedCoordinates
      (J := fun u => J u p.1) (R := fun u => R u p.1) (V := fun u => V u p)
      (M := M t p.1) (κ := κ t p.1) (f := f t p) (q := q t p) ht (uniqueDiffOn_Icc hlr t ht)
      (hRJ p.1) (hJR p.1 t ht) (hJt p.1 t ht) hRd (hVt p t ht) (hVκ p t ht)
    exact hd
  let ForceBound := (2 : ℝ) ^ N * CR * H
  have hfRN : HierarchyRelayWordBound ℓ h N ForceBound
      (fun (u : Icc l r) p => (g u)⁻¹ • fR u p) := by
    have hfRW := HierarchyRelayWordBound.clm_apply
      (f := fun (u : Icc l r) p => R u p.1) (g := fun u p => (g u)⁻¹ • f u p)
      (fun u => contDiff_slabSlice hR' u.property)
      (fun u => (contDiff_slabSlice hf u.property).const_smul _) hRN hfN
    simpa only [fR, map_smul] using hfRW
  have hl : l ∈ Icc l r := ⟨le_rfl, hlr.le⟩
  have hInitial : HierarchyRelayWordBound ℓ h N ((2 : ℝ) ^ N * CR * B)
      (fun (_ : Icc l r) p => (g l)⁻¹ • X l p) := by
    have hRead : HierarchyRelayWordBound ℓ h N CR (fun (_ : Icc l r) p => R l p.1) :=
      ⟨hRN.1, fun w hw _ p => hRN.2 w hw ⟨l, hl⟩ p⟩
    have hProd := HierarchyRelayWordBound.clm_apply
      (f := fun (_ : Icc l r) p => R l p.1) (g := fun _ p => (g l)⁻¹ • V l p)
      (fun _ => contDiff_slabSlice hR' hl)
      (fun _ => (contDiff_slabSlice hV hl).const_smul _) hRead hInit
    simpa only [X, map_smul] using hProd
  have hXN := linearODE_weightedHierarchyWordBound_of_initial N
    (A := A) (f := fR) (x := X) (S := S) hlr hK hC hcomm hS
    hA hfR hX hX₀ hXode (fun p hp u hu => by simp [fR, hfs p hp u hu])
    hg₀ hg hdg hStable hInitial hfRN hcoeff
  have hLift := HierarchyRelayWordBound.clm_apply
    (f := fun (u : Icc l r) p => J u p.1) (g := fun u p => (g u)⁻¹ • X u p)
    (fun u => contDiff_slabSlice hJ' u.property)
    (fun u => (contDiff_slabSlice hX u.property).const_smul _) hJN hXN
  have heq (u : Icc l r) (p : Vec3 × ℝ) : J u p.1 ((g u)⁻¹ • X u p) = (g u)⁻¹ • V u p := by
    rw [map_smul]
    congr 1
    change ((J u p.1).comp (R u p.1)) (V u p) = _
    rw [hJR p.1 u u.property, oscillatoryTransverseProjection_apply, hVκ p u u.property,
      zero_div, zero_smul, sub_zero]
  simpa only [heq, ForceBound] using hLift

/-- Zero-start version of the weighted estimate for the transverse velocity. -/
theorem oscillatoryVelocity_weightedWordBound
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {J : ℝ → Vec3 → F →L[ℝ] Vec3} {R : ℝ → Vec3 → Vec3 →L[ℝ] F}
    {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3}
    {V f : ℝ → (Vec3 × ℝ) → Vec3} {q : ℝ → (Vec3 × ℝ) → ℝ}
    {g dg : ℝ → ℝ} {S : Set (Vec3 × ℝ)} {l r K C Ccomm CJ CR H ℓ h : ℝ}
    (N : ℕ) (hlr : l < r) (hK : 0 ≤ K) (hC : 0 ≤ C) (hcomm : K * (r - l) * C ≤ Ccomm)
    (hS : IsClosed S)
    (hJ : ContDiffOn ℝ ∞ (Function.uncurry J) (Icc l r ×ˢ univ))
    (hR : ContDiffOn ℝ ∞ (Function.uncurry R) (Icc l r ×ˢ univ))
    (hM : ContDiffOn ℝ ∞ (Function.uncurry M) (Icc l r ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc l r ×ˢ univ))
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc l r ×ˢ univ))
    (hV₀ : V l = 0)
    (hJt : ∀ a t, t ∈ Icc l r → HasDerivWithinAt (fun u => J u a) ((M t a).comp (J t a)) (Icc l r) t)
    (hRJ : ∀ a t, t ∈ Icc l r → (R t a).comp (J t a) = .id ℝ F)
    (hJR : ∀ a t, t ∈ Icc l r → (J t a).comp (R t a) = oscillatoryTransverseProjection (κ t a))
    (hVt : ∀ p t, t ∈ Icc l r → HasDerivWithinAt (fun u => V u p)
      (f t p - M t p.1 (V t p) - q t p • κ t p.1) (Icc l r) t)
    (hVκ : ∀ p t, t ∈ Icc l r → ⟪κ t p.1, V t p⟫_ℝ = 0)
    (hfs : ∀ p ∉ S, ∀ u ∈ Icc l r, f u p = 0)
    (hg₀ : ∀ u ∈ Icc l r, 0 < g u)
    (hg : ∀ u ∈ Icc l r, HasDerivWithinAt g (dg u) (Icc l r) u)
    (hdg : ContinuousOn dg (Icc l r))
    (hJN : HierarchyRelayWordBound ℓ h N CJ (fun (u : Icc l r) p => J u p.1))
    (hRN : HierarchyRelayWordBound ℓ h N CR (fun (u : Icc l r) p => R u p.1))
    (hfN : HierarchyRelayWordBound ℓ h N H (fun (u : Icc l r) p => (g u)⁻¹ • f u p)) :
    let A (t : ℝ) (p : Vec3 × ℝ) := (-2 : ℝ) • (R t p.1).comp ((M t p.1).comp (J t p.1))
    (∀ p ∈ S, ∀ y : ℝ → F,
      (∀ u ∈ Icc l r, HasDerivWithinAt y (A u p (y u)) (Icc l r) u) →
      ∀ u ∈ Icc l r, ∀ v ∈ Icc u r, ‖y v‖ / g v ≤ K * (‖y u‖ / g u)) →
    (∀ w ∈ hierarchyAdmissibleWords (Fin 4) N, w ≠ [] → ∀ p ∈ S, ∀ u ∈ Icc l r,
      ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (A u) p‖ ≤ C) →
    HierarchyRelayWordBound ℓ h N
      ((2 : ℝ) ^ N * CJ * (linearODEWordFactor Ccomm N * (K * ((r - l) * ((2 : ℝ) ^ N * CR * H)))))
      (fun (u : Icc l r) p => (g u)⁻¹ • V u p) := by
  dsimp only
  intro hStable hcoeff
  have hInit : HierarchyRelayWordBound ℓ h N 0
      (fun (_ : Icc l r) p => (g l)⁻¹ • V l p) := by
    refine ⟨le_rfl, fun w _ _ p => ?_⟩
    simp only [hV₀, Pi.zero_apply, smul_zero]
    change ‖phaseOperatorWord (fun i (_ : Vec3 × ℝ) => hierarchyMixedDirection ℓ h i 0)
      w (0 : Vec3 × ℝ → Vec3) p‖ ≤ 0
    rw [phaseOperatorWord_zero, Pi.zero_apply, norm_zero]
  simpa only [mul_zero, zero_add] using
    oscillatoryVelocity_weightedWordBound_of_initial (S := S) N hlr hK hC hcomm hS hJ hR hM hf hV
      (fun p _ => by simp [hV₀]) hJt hRJ hJR hVt hVκ hfs hg₀ hg hdg hJN hRN hInit hfN hStable hcoeff

section Pressure

variable {T : Type}

private theorem phasePrimitive_const_smul (c : ℝ) (f : ℝ → ℝ) (s : ℝ) :
    phasePrimitive (fun σ => c • f σ) s = c • phasePrimitive f s := by
  simp only [phasePrimitive, phaseOscillation, intervalIntegral.integral_smul,
    phaseMean_const_smul, smul_sub]

/-- The actual normalized pressure has one inverse factor of the carrier at
every order, with the remaining constants given by the normalized covector
and strain coefficient bounds. -/
theorem oscillatoryPhasePressure_weightedWordBound
    {M : T → Vec3 → Vec3 →L[ℝ] Vec3} {κ : T → Vec3 → Vec3}
    {V f : T → (Vec3 × ℝ) → Vec3} {g : T → ℝ}
    {freq ℓ h A B V₀ F₀ : ℝ} {n : ℕ} (hfreq : 0 < freq)
    (hV : ∀ t, ContDiff ℝ ∞ (V t)) (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hVp : ∀ t a, Function.Periodic (fun s => V t (a,s)) 1)
    (hfp : ∀ t a, Function.Periodic (fun s => f t (a,s)) 1)
    (hVz : ∀ t a, phaseMean (fun s => V t (a,s)) = 0)
    (hfz : ∀ t a, phaseMean (fun s => f t (a,s)) = 0)
    (ha : ∀ t, ContDiff ℝ ∞ (fun p : Vec3 × ℝ =>
      hierarchyRelayPressureAmplitudeCoefficient (M t p.1) (κ t p.1)))
    (hb : ∀ t, ContDiff ℝ ∞ (fun p : Vec3 × ℝ => hierarchyRelayPressureSourceCoefficient (κ t p.1)))
    (haN : HierarchyRelayWordBound ℓ h n A
      (fun t p => hierarchyRelayPressureAmplitudeCoefficient (M t p.1) (κ t p.1)))
    (hbN : HierarchyRelayWordBound ℓ h n B (fun t p => hierarchyRelayPressureSourceCoefficient (κ t p.1)))
    (hVN : HierarchyRelayWordBound ℓ h n V₀ (fun t p => (g t)⁻¹ • V t p))
    (hfN : HierarchyRelayWordBound ℓ h n F₀ (fun t p => (g t)⁻¹ • f t p)) :
    HierarchyRelayWordBound ℓ h n
      (2 * ((hierarchyAdmissibleWords (Fin 4) n).card *
        ((2 : ℝ) ^ n * A * V₀ + (2 : ℝ) ^ n * B * F₀)))
      (fun t p => (g t)⁻¹ • freq • oscillatoryPhasePressure (M t p.1) (freq • κ t p.1)
        (fun s => f t (p.1, s)) (fun s => V t (p.1, s)) p.2) := by
  let a (t : T) (x : Vec3) := hierarchyRelayPressureAmplitudeCoefficient (M t x) (κ t x)
  let b (t : T) (x : Vec3) := hierarchyRelayPressureSourceCoefficient (κ t x)
  let V' (t : T) (p : Vec3 × ℝ) := (g t)⁻¹ • V t p
  let f' (t : T) (p : Vec3 × ℝ) := (g t)⁻¹ • f t p
  have hV' (t : T) : ContDiff ℝ ∞ (V' t) := (hV t).const_smul _
  have hf' (t : T) : ContDiff ℝ ∞ (f' t) := (hf t).const_smul _
  have hVp' (t : T) (x : Vec3) : Function.Periodic (fun s => V' t (x,s)) 1 :=
    fun s => congrArg ((g t)⁻¹ • ·) (hVp t x s)
  have hfp' (t : T) (x : Vec3) : Function.Periodic (fun s => f' t (x,s)) 1 :=
    fun s => congrArg ((g t)⁻¹ • ·) (hfp t x s)
  have hVz' (t : T) (x : Vec3) : phaseMean (fun s => V' t (x,s)) = 0 := by
    change phaseMean (fun s => (g t)⁻¹ • V t (x,s)) = _
    rw [phaseMean_const_smul, hVz, smul_zero]
  have hfz' (t : T) (x : Vec3) : phaseMean (fun s => f' t (x,s)) = 0 := by
    change phaseMean (fun s => (g t)⁻¹ • f t (x,s)) = _
    rw [phaseMean_const_smul, hfz, smul_zero]
  let Q (t : T) (p : Vec3 × ℝ) :=
    phasePrimitive (fun s => a t p.1 (V' t (p.1,s)) + b t p.1 (f' t (p.1,s))) p.2
  have hP : HierarchyRelayWordBound ℓ h n
      (2 * ((hierarchyAdmissibleWords (Fin 4) n).card *
        ((2 : ℝ) ^ n * A * V₀ + (2 : ℝ) ^ n * B * F₀))) Q :=
    (hierarchyRelayWordBound_linearPrimitive (a := a) (b := b) (V := V') (f := f')
      ha hb hV' hf' hVp' hfp' hVz' hfz' haN hbN hVN hfN).2
  have heq (t : T) (p : Vec3 × ℝ) :
      (g t)⁻¹ • freq • oscillatoryPhasePressure (M t p.1) (freq • κ t p.1)
        (fun s => f t (p.1, s)) (fun s => V t (p.1, s)) p.2 = Q t p := by
    rw [oscillatoryPhasePressure_frequency_scale hfreq, smul_smul freq freq⁻¹,
      mul_inv_cancel₀ hfreq.ne', one_smul]
    unfold Q oscillatoryPhasePressure
    rw [← phasePrimitive_const_smul]
    congr 1
    funext s
    simp only [V', f', map_smul, ← smul_add, a, b, oscillatoryPressureSlope_eq_coefficients]
  simpa only [heq] using hP

end Pressure

end TorusEuler
