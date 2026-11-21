import Breakdown.CellReduction.PotScalarDecayCells

open scoped ContDiff Topology
open MeasureTheory Polynomial

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape AdjointDefect
open CellCert.GivenFields (heightRatio cellCount cellIndex weightPoly Spline)
open CertCell.GivenShape.Internal.KeyDecay

namespace Internal.ScalarDecay

theorem lastCell_factor (H : JetSpline) (ht : IsJetAxis H.tAxis 0 1) {z : ℕ} (hz : z ≤ H.tAxis.depth)
    (hv : EndVanishOrder H z) :
    ∃ tb < 1, ∃ D : ℕ, ∀ x : ℝ, ∃ r : ℂ[X], r.natDegree ≤ D ∧
      ∀ t : ℝ, tb ≤ t → H.toSpline.evalHalf t x = ((t : ℂ) - 1) ^ z * r.eval (t : ℂ) := by
  set N := cellCount H.tAxis.breaks with hN
  have hN1 : 1 ≤ N := length_two_le one_pos ht.first ht.last
  have hbd := inner_bounds ht.sorted ht.first ht.last
  obtain ⟨m, hm1, hmI⟩ := exists_inner_upper (lo := 0) (hi := 1) one_pos
    (I := (H.tAxis.breaks.drop 1).dropLast) fun b hb => (hbd b hb).2
  set i := N - 1 with hi
  set bb : ℝ := H.tAxis.breaks.getD (i + 1) 0 with hbb
  have hbb1 : bb = 1 := by
    rw [hbb, show i + 1 = N by omega]
    exact getD_last ht.last
  have hlen : N < H.tAxis.breaks.length := by
    have : N = H.tAxis.breaks.length - 1 := rfl
    omega
  have hab : H.tAxis.breaks.getD i 0 ≠ bb :=
    (CertCell.GivenShape.Internal.getD_lt_getD_of_sorted ht.sorted (Nat.lt_succ_self i) (by omega)).ne
  have hdiv : ∀ d, (∀ e, H.coef d e = 0) ∨ (X - C (bb : ℂ)) ^ z ∣ H.tAxis.dofPoly i d := by
    intro d
    cases d with
    | node k p =>
      by_cases hp : p < H.tAxis.depth
      · by_cases hk : k = i
        · right
          refine dvd_of_iterate_derivative fun o ho => ?_
          rw [JetAxis.dofPoly, if_pos hp, if_pos hk]
          exact iterate_derivative_nodalLeft_eval_right _ p o hab (lt_of_lt_of_le ho hz)
        · by_cases hk1 : k = i + 1
          · by_cases hpz : p < z
            · left
              intro e
              rw [hk1, show i + 1 = N by omega]
              exact hv p hpz e
            · right
              refine dvd_of_iterate_derivative fun o ho => ?_
              rw [JetAxis.dofPoly, if_pos hp, if_neg hk, if_pos hk1]
              rw [iterate_derivative_nodalRight_eval_right _ p o hab (lt_of_lt_of_le ho hz), if_neg (by omega)]
          · right
            rw [JetAxis.dofPoly, if_pos hp, if_neg hk, if_neg hk1]
            exact dvd_zero _
      · right
        rw [JetAxis.dofPoly, if_neg hp]
        exact dvd_zero _
    | bubble i' s =>
      right
      rw [JetAxis.dofPoly]
      split_ifs
      · exact dvd_of_iterate_derivative fun o ho =>
          iterate_derivative_bubblePoly_eval_right _ s o _ _ (lt_of_lt_of_le ho hz)
      · exact dvd_zero _
  have hmon : ((X - C (bb : ℂ)) ^ z).Monic := (monic_X_sub_C _).pow z
  set Q : JetDof → ℂ[X] := fun d => H.tAxis.dofPoly i d /ₘ (X - C (bb : ℂ)) ^ z with hQdef
  have hQ : ∀ d e (u : ℂ), H.coef d e * (H.tAxis.dofPoly i d).eval u =
      H.coef d e * ((u - bb) ^ z * (Q d).eval u) := by
    intro d e u
    rcases hdiv d with h | h
    · rw [h e, zero_mul, zero_mul]
    · have e1 := modByMonic_add_div (H.tAxis.dofPoly i d) ((X - C (bb : ℂ)) ^ z)
      rw [(modByMonic_eq_zero_iff_dvd hmon).2 h, zero_add] at e1
      conv_lhs => rw [← e1]
      simp [hQdef]
  have hci : ∀ t : ℝ, m ≤ t → cellIndex H.tAxis.breaks t = i := fun t ht' =>
    cellIndex_eq_last fun b hb => (hmI b hb).trans ht'
  refine ⟨m, hm1, ∑ d ∈ H.tAxis.dofs, (Q d).natDegree, fun x => ?_⟩
  set j := cellIndex H.xAxis.breaks x
  refine ⟨∑ d ∈ H.tAxis.dofs, ∑ e ∈ H.xAxis.dofs, C (H.coef d e * (H.xAxis.dofPoly j e).eval (x : ℂ)) * Q d,
    ?_, fun t ht' => ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun d hd => natDegree_sum_le_of_forall_le _ _ fun e _ => ?_
    exact natDegree_C_mul_le _ _ |>.trans (Finset.single_le_sum (f := fun d => (Q d).natDegree)
      (fun _ _ => Nat.zero_le _) hd)
  · rw [evalHalf_eq, hci t ht', eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [eval_mul, eval_C]
    have h1 := hQ d e (t : ℂ)
    rw [hbb1] at h1
    push_cast at h1
    linear_combination (H.xAxis.dofPoly j e).eval (x : ℂ) * h1

theorem slopeRegular_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ × ℝ → ℂ) (h : ∀ k ∈ s, SlopeRegular (f k)) :
    SlopeRegular (fun p => ∑ k ∈ s, f k p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const_reg 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem slopeRegular_slice {G : ℝ × ℝ → ℂ} (hG : SlopeRegular G) (c : ℝ) :
    SlopeRegular (fun p : ℝ × ℝ => G (c, p.2)) := by
  have hφ : ContDiff ℝ 1 (fun p : ℝ × ℝ => (c, p.2)) := contDiff_const.prodMk contDiff_snd
  set L0 : ℝ × ℝ →L[ℝ] ℝ × ℝ := (0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hd : ∀ p : ℝ × ℝ, HasFDerivAt (fun p : ℝ × ℝ => (c, p.2)) L0 p := fun p =>
    (hasFDerivAt_const c p).prodMk (hasFDerivAt_snd)
  have he : fderiv ℝ (fun p : ℝ × ℝ => G (c, p.2)) =
      fun p => (ContinuousLinearMap.compL ℝ (ℝ × ℝ) (ℝ × ℝ) ℂ).flip L0 (fderiv ℝ G (c, p.2)) := by
    funext p
    have h2 : HasFDerivAt (fun p : ℝ × ℝ => G (c, p.2)) ((fderiv ℝ G (c, p.2)).comp L0) p :=
      ((hG.1.differentiable one_ne_zero) (c, p.2)).hasFDerivAt.comp p (hd p)
    rw [h2.fderiv]
    rfl
  refine ⟨hG.1.comp hφ, ?_⟩
  rw [he]
  exact ((ContinuousLinearMap.lipschitz _).locallyLipschitz.comp (hG.2.comp hφ.locallyLipschitz))

theorem slopeRegular_poly (q : ℂ[X]) : SlopeRegular (fun p : ℝ × ℝ => q.eval (p.1 : ℂ)) := by
  have h := Polynomial.contDiff_aeval (𝕜 := ℂ) q 2
  simp only [Polynomial.coe_aeval_eq_eval] at h
  refine SlopeRegular.of_contDiff ?_
  exact (h.restrict_scalars ℝ).comp (Complex.ofRealCLM.contDiff.comp contDiff_fst)

theorem interp_parts (tb : ℝ) (htb : tb < 1) (D : ℕ) :
    ∃ v : Fin (D + 1) → ℝ, Function.Injective v ∧ ∀ k, tb ≤ v k ∧ v k < 1 := by
  have hD : (0 : ℝ) < (D : ℝ) + 2 := by positivity
  have hc : (0 : ℝ) < 1 - tb := by linarith
  refine ⟨fun k => tb + (1 - tb) * (((k : ℕ) : ℝ) + 1) / ((D : ℝ) + 2), ?_, fun k => ⟨?_, ?_⟩⟩
  · intro a b hab
    have e1 := add_left_cancel hab
    rw [div_left_inj' hD.ne'] at e1
    have e2 := mul_left_cancel₀ hc.ne' e1
    exact Fin.ext (by exact_mod_cast add_right_cancel e2)
  · exact le_add_of_nonneg_right (by positivity)
  · have hk : (((k : ℕ) : ℝ) + 1) < (D : ℝ) + 2 := by
      have := k.isLt
      have : ((k : ℕ) : ℝ) ≤ D := by exact_mod_cast Nat.lt_succ_iff.1 this
      linarith
    have : (1 - tb) * (((k : ℕ) : ℝ) + 1) / ((D : ℝ) + 2) < 1 - tb := by
      rw [div_lt_iff₀ hD]
      nlinarith
    linarith

theorem interp_eq {g : ℝ → ℝ → ℂ} {tb : ℝ} {z D : ℕ} {v : Fin (D + 1) → ℝ} (hinj : Function.Injective v)
    (hv : ∀ k, tb ≤ v k ∧ v k < 1)
    (hg : ∀ x, ∃ r : ℂ[X], r.natDegree ≤ D ∧ ∀ t, tb ≤ t → g t x = ((t : ℂ) - 1) ^ z * r.eval (t : ℂ))
    (t x : ℝ) (ht : tb ≤ t) :
    g t x = ((t : ℂ) - 1) ^ z * ∑ k, (Lagrange.basis Finset.univ (fun k => (v k : ℂ)) k).eval (t : ℂ) *
      (g (v k) x / (((v k : ℝ) : ℂ) - 1) ^ z) := by
  obtain ⟨r, hr, hre⟩ := hg x
  have hinjC : Set.InjOn (fun k => (v k : ℂ)) (Finset.univ : Finset (Fin (D + 1))) :=
    fun a _ b _ h => hinj (Complex.ofReal_injective h)
  have hdeg : r.degree < (Finset.univ : Finset (Fin (D + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hr)
  have e := congrArg (Polynomial.eval (t : ℂ)) (Lagrange.eq_interpolate hinjC hdeg)
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum] at e
  rw [hre t ht, e]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk1 : ((v k : ℝ) : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (hv k).2.ne
  rw [hre (v k) (hv k).1, mul_div_cancel_left₀ _ (pow_ne_zero _ hk1), Polynomial.eval_mul, Polynomial.eval_C,
    mul_comm]

end Internal.ScalarDecay

end PotentialShape

end Breakdown
