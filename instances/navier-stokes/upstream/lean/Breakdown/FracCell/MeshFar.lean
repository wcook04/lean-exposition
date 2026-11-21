import Breakdown.FracCell.MeshFarCoefEnergy
import Breakdown.FracCell.MeshFarRegular

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace MeshFarInternal

theorem symSq_add_antiSq (s : Fin 3 → Fin 3 → ℂ) : symSq s + antiSq s = sumSq s := by
  have par : ∀ x y : ℂ, ‖(x + y) / 2‖ ^ 2 + ‖(x - y) / 2‖ ^ 2 = (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
    intro x y
    have h := parallelogram_law_with_norm ℝ x y
    rw [norm_div, norm_div, show ‖(2 : ℂ)‖ = 2 by simp, div_pow, div_pow, sq, sq, sq, sq]
    linarith
  unfold symSq antiSq sumSq
  simp only [← Finset.sum_add_distrib, par]
  simp only [Fin.sum_univ_three]
  ring

theorem sq_add_le (η : ℝ) (hη : 0 < η) (y e : ℂ) :
    ‖y + e‖ ^ 2 ≤ (1 + η) * ‖y‖ ^ 2 + (1 + η⁻¹) * ‖e‖ ^ 2 := by
  rw [← one_div]
  have h1 := norm_add_le y e
  have h0 : 0 ≤ ‖y + e‖ := norm_nonneg _
  have h3 : (1 + η) * ‖y‖ ^ 2 + (1 + 1 / η) * ‖e‖ ^ 2 - (‖y‖ + ‖e‖) ^ 2 = (η * ‖y‖ - ‖e‖) ^ 2 / η := by
    field_simp
    ring
  have h4 : 0 ≤ (η * ‖y‖ - ‖e‖) ^ 2 / η := div_nonneg (sq_nonneg _) hη.le
  have h5 : ‖y + e‖ ^ 2 ≤ (‖y‖ + ‖e‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
  linarith

theorem sumSq_fold (Y : Fin 3 → Fin 3 → ℂ) (T : Fin 3 → ℂ) (η : ℝ) (hη : 0 < η) :
    sumSq (fun a b => Y a b + if b = 1 then T a else 0) ≤ (1 + η) * sumSq Y + (1 + 1 / η) * vecSq T := by
  have z : ∀ y : ℂ, ‖y‖ ^ 2 ≤ (1 + η) * ‖y‖ ^ 2 := fun y => by nlinarith [sq_nonneg ‖y‖]
  rw [one_div]
  unfold sumSq vecSq
  simp only [Fin.sum_univ_three]
  simp
  linarith [sq_add_le η hη (Y 0 1) (T 0), sq_add_le η hη (Y 1 1) (T 1), sq_add_le η hη (Y 2 1) (T 2),
    z (Y 0 0), z (Y 0 2), z (Y 1 0), z (Y 1 2), z (Y 2 0), z (Y 2 2)]

theorem strain_term (Y : Fin 3 → Fin 3 → ℂ) (T : Fin 3 → ℂ) (P : Prop) [Decidable P] (hs ha fl η : ℝ)
    (hfl : 0 < fl) (hhs : fl ≤ hs) (hha : fl ≤ ha) (hη : 0 < η) :
    symSq (fun a b => Y a b + (if P ∧ b = 1 then T a else 0)) / hs
      + antiSq (fun a b => Y a b + (if P ∧ b = 1 then T a else 0)) / ha
      ≤ (if P then 1 + η else 1) / fl * sumSq Y + (if P then (1 + 1 / η) / fl * vecSq T else 0) := by
  set X : Fin 3 → Fin 3 → ℂ := fun a b => Y a b + (if P ∧ b = 1 then T a else 0) with hX
  have hsym : 0 ≤ symSq X := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hanti : 0 ≤ antiSq X := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have e1 : symSq X / hs ≤ symSq X / fl := div_le_div_of_nonneg_left hsym hfl hhs
  have e2 : antiSq X / ha ≤ antiSq X / fl := div_le_div_of_nonneg_left hanti hfl hha
  have e3 : symSq X / fl + antiSq X / fl = sumSq X / fl := by rw [← add_div, symSq_add_antiSq]
  by_cases hP : P
  · have hX' : X = fun a b => Y a b + if b = 1 then T a else 0 := by
      funext a b; simp [hX, hP]
    have := sumSq_fold Y T η hη
    rw [← hX'] at this
    rw [if_pos hP, if_pos hP]
    have e4 : sumSq X / fl ≤ ((1 + η) * sumSq Y + (1 + 1 / η) * vecSq T) / fl :=
      div_le_div_of_nonneg_right this hfl.le
    have e5 : ((1 + η) * sumSq Y + (1 + 1 / η) * vecSq T) / fl
        = (1 + η) / fl * sumSq Y + (1 + 1 / η) / fl * vecSq T := by ring
    linarith
  · have hX' : X = Y := by funext a b; simp [hX, hP]
    rw [if_neg hP, if_neg hP, ← hX']
    have e5 : sumSq X / fl = 1 / fl * sumSq X := by ring
    linarith

theorem tsum_le_of_le {f g : ℕ × ℕ → ℝ} (hg : Summable g) (hg0 : ∀ x, 0 ≤ g x) (h : ∀ x, f x ≤ g x) :
    ∑' x, f x ≤ ∑' x, g x := by
  by_cases hf : Summable f
  · exact hf.tsum_le_tsum h hg
  · rw [tsum_eq_zero_of_not_summable hf]
    exact tsum_nonneg hg0

theorem family_tsum {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O) (g : O → ℤ → ℕ × ℕ → ℝ)
    (hg : ∀ o n, Summable (g o n)) :
    Summable (fun jl => ∑ o, T.outWeight o * ∑ n ∈ T.outModes o, g o n jl) ∧
      ∑' jl, ∑ o, T.outWeight o * ∑ n ∈ T.outModes o, g o n jl
        = ∑ o, T.outWeight o * ∑ n ∈ T.outModes o, ∑' jl, g o n jl := by
  constructor
  · exact summable_sum (fun o _ => (summable_sum (fun n _ => hg o n)).mul_left _)
  · rw [Summable.tsum_finsetSum (fun o _ => (summable_sum (fun n _ => hg o n)).mul_left _)]
    refine Finset.sum_congr rfl (fun o _ => ?_)
    rw [tsum_mul_left, Summable.tsum_finsetSum (fun n _ => hg o n)]

theorem sum_groupWeight {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O) (i : I) (d : ℕ)
    (hd : T.inputDeg i ≤ d) (q : ℕ → ℕ → ℝ) :
    ∑ j ∈ Finset.range (d + 1), ∑ l ∈ Finset.range (d + 1), CellScalars.groupWeight T i j l * q j l =
      ∑ j ∈ Finset.range (T.inputDeg i + 1), ∑ l ∈ Finset.range (T.inputDeg i + 1),
        (T.radialTotal * T.radialBound i j + T.heightTotal * T.heightBound i l) * q j l := by
  refine Eq.trans (Finset.sum_subset (s₁ := Finset.range (T.inputDeg i + 1))
    (Finset.range_subset_range.mpr (by omega)) ?_).symm ?_
  · intro j _ hj
    simp only [Finset.mem_range, not_lt] at hj
    refine Finset.sum_eq_zero (fun l _ => ?_)
    unfold CellScalars.groupWeight
    rw [if_neg (by omega), zero_mul]
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    refine Eq.trans (Finset.sum_subset (s₁ := Finset.range (T.inputDeg i + 1))
      (Finset.range_subset_range.mpr (by omega)) ?_).symm ?_
    · intro l _ hl
      simp only [Finset.mem_range, not_lt] at hl
      unfold CellScalars.groupWeight
      rw [if_neg (by omega), zero_mul]
    · refine Finset.sum_congr rfl (fun l hl => ?_)
      simp only [Finset.mem_range] at hj hl
      unfold CellScalars.groupWeight
      rw [if_pos ⟨by omega, by omega⟩]

theorem sum_nine (f : Fin 3 → Fin 3 → ℝ) :
    ∑ e : Fin 9, f ⟨e.val / 3, by omega⟩ ⟨e.val % 3, Nat.mod_lt _ (by norm_num)⟩ = ∑ a : Fin 3, ∑ b : Fin 3, f a b := by
  rw [← (finProdFinEquiv (m := 3) (n := 3)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  have h1 : (⟨(finProdFinEquiv (a, b)).val / 3, by omega⟩ : Fin 3) = a := by
    ext; simp [finProdFinEquiv]; omega
  have h2 : (⟨(finProdFinEquiv (a, b)).val % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = b := by
    ext; simp [finProdFinEquiv]
  rw [h1, h2]

theorem sum_nine_sq (s : Fin 3 → Fin 3 → ℂ) :
    ∑ e : Fin 9, ‖s ⟨e.val / 3, by omega⟩ ⟨e.val % 3, Nat.mod_lt _ (by norm_num)⟩‖ ^ 2 = sumSq s :=
  sum_nine (fun a b => ‖s a b‖ ^ 2)

theorem add4 {a b c d a' b' c' d' : ℝ} (h1 : a = a') (h2 : b = b') (h3 : c = c') (h4 : d = d') :
    a + b + c + d = c' + d' + a' + b' := by
  subst h1 h2 h3 h4
  ring

open CellScalars in
theorem majorant_sum {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (F : FarMajorantData)
    (u : (ℤ × Fin 3 × Fin 4 × ℕ × ℕ) ⊕ (Fin k ⊕ Fin k) → ℂ)
    (hgw0 : S.band = ∅ → ∀ j l, groupWeight (bandGroupFamily c K S F) () j l = 0) :
    (strainGroupFamily c K S F).majorant (strainInput u) + (velocityGroupFamily c K S F).majorant (velocityInput u)
      + (bandGroupFamily c K S F).majorant (velocityInput u) = farMajorantForm c K S F u := by
  have hif : ∀ j l, (if S.band = ∅ then (0 : ℝ) else groupWeight (bandGroupFamily c K S F) () j l)
      = groupWeight (bandGroupFamily c K S F) () j l := fun j l => by
    split_ifs with hb
    · exact (hgw0 hb j l).symm
    · rfl
  have h0 := fun n => sum_groupWeight (strainGroupFamily c K S F) 0 S.degHigh (by simp [strainGroupFamily])
    (fun j l => curlSq (lowStrainCoef u n j l))
  have h1 := fun n => sum_groupWeight (strainGroupFamily c K S F) 1 S.degHigh (by simp [strainGroupFamily])
    (fun j l => vecSq (lowVelocityCoef u n j l))
  have hv := fun n => sum_groupWeight (velocityGroupFamily c K S F) () S.degHigh (by simp [velocityGroupFamily])
    (fun j l => sumSq (lowStrainCoef u n j l))
  have hb := fun n => sum_groupWeight (bandGroupFamily c K S F) () S.degHigh (by simp [bandGroupFamily])
    (fun j l => sumSq (lowStrainCoef u n j l))
  unfold farMajorantForm
  simp only [hif]
  simp only [add_mul, Finset.sum_add_distrib]
  simp only [h0, h1, hv, hb]
  unfold TailFamily.majorant
  simp only [Fin.sum_univ_two, Fintype.sum_unique]
  refine add4 ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_)))
    congr 1
    exact sum_nine_sq _
  · refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_)))
    congr 1
    exact sum_nine_sq _

def bandless (F : FarMajorantData) : FarMajorantData :=
  { F with bandGroup := ⟨fun _ _ => 0, fun _ _ => 0⟩, bandVelocityWeight := 0 }

end MeshFarInternal

open CellScalars MeshFarInternal in
private theorem farMajorant_core (h : TailMajorantStatement) (hcoef : FarCoefStatement) (hreg : FarRegularStatement)
    (hsum : FarSummableStatement) (α : ℝ) (hα1 : 1 < α) (hα2 : α < 5 / 4) {k N : ℕ} (c : FracCellData k N)
    (hc : IsFormData α c) (K : CellBox) (S : CellScalars) (B : CellBases) {slots : ℕ} (R : CellRows N slots k)
    (F : FarMajorantData) (hK : IsCellBox K) (hsol : K.solid ⊆ c.cellRegion) (hS : IsCellScalars α c K S)
    (hB : IsCellBases K B) (hsub : S.resolved ∪ S.band ⊆ R.yModes) (hF : IsFarMajorant c K S B R F)
    (hbb : IsTailBounds K B S.degNear (bandGroupFamily c K S F))
    (hgw0 : S.band = ∅ → ∀ j l, groupWeight (bandGroupFamily c K S F) () j l = 0)
    (x : FieldTuple k) (hx : IsAdmissible c x) (ζ : Fin k → ℝ) :
    farWeighted c K S B x.2.2.2.1 ζ x.1 x.2.1 R ≤ farFormValue c K S R B x ζ := by
  obtain ⟨hrs, hrv, hrb⟩ := hreg α hα1 hα2 c hc K S F hK hsol hS
  have hcf := hcoef α hα1 hα2 c hc K S B R F hK hsol hS hB hsub hF x hx ζ
  have hm : 1 ≤ c.order := by have := hc.base.order_ge; omega
  have hdeg := hS.degrees
  set u := farVector c K S B x ζ with hu
  set Ts := strainGroupFamily c K S F with hTs
  set Tv := velocityGroupFamily c K S F with hTv
  set Tb := bandGroupFamily c K S F with hTb
  set gs : Fin 3 × Fin 3 → ℤ → ℕ × ℕ → ℝ := fun o n jl =>
    if S.degNear < max jl.1 jl.2 then ‖B.coef K (Ts.outputMode c.order B (strainInput u) o n) jl.1 jl.2‖ ^ 2 else 0
    with hgs
  set gv : Fin 3 → ℤ → ℕ × ℕ → ℝ := fun o n jl =>
    if S.degNear < max jl.1 jl.2 then ‖B.coef K (Tv.outputMode c.order B (velocityInput u) o n) jl.1 jl.2‖ ^ 2 else 0
    with hgv
  set gb : Fin 3 → ℤ → ℕ × ℕ → ℝ := fun o n jl =>
    if S.degNear < max jl.1 jl.2 then ‖B.coef K (Tb.outputMode c.order B (velocityInput u) o n) jl.1 jl.2‖ ^ 2 else 0
    with hgb
  have sS : ∀ o n, Summable (gs o n) := fun o n => hsum K B hK hB c.order S.degNear Ts hrs (strainInput u) o n
  have sV : ∀ o n, Summable (gv o n) := fun o n => hsum K B hK hB c.order S.degNear Tv hrv (velocityInput u) o n
  have sB : ∀ o n, Summable (gb o n) := fun o n => hsum K B hK hB c.order S.degNear Tb hrb (velocityInput u) o n
  obtain ⟨gS, eS⟩ := family_tsum Ts gs sS
  obtain ⟨gV, eV⟩ := family_tsum Tv gv sV
  obtain ⟨gB, eB⟩ := family_tsum Tb gb sB
  have tS := h K B hK hB c.order hm S.degNear Ts hrs hF.strain_bounds (strainInput u)
  have tV := h K B hK hB c.order hm S.degNear Tv hrv hF.velocity_bounds (velocityInput u)
  have tB := h K B hK hB c.order hm S.degNear Tb hrb hbb (velocityInput u)
  have hmaj := majorant_sum c K S F u hgw0
  have hker := hF.kernel_dominates u
  have hG0 : ∀ jl, 0 ≤ (∑ o, Ts.outWeight o * ∑ n ∈ Ts.outModes o, gs o n jl)
      + (∑ o, Tv.outWeight o * ∑ n ∈ Tv.outModes o, gv o n jl)
      + (∑ o, Tb.outWeight o * ∑ n ∈ Tb.outModes o, gb o n jl) := by
    intro jl
    have p1 : ∀ (g : ℝ), 0 ≤ (if S.degNear < max jl.1 jl.2 then g ^ 2 else 0) := fun g => by
      split_ifs
      · exact sq_nonneg _
      · exact le_rfl
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · exact Finset.sum_nonneg (fun o _ => mul_nonneg (hF.strain_bounds.outWeight_nonneg o)
        (Finset.sum_nonneg (fun n _ => p1 _)))
    · exact Finset.sum_nonneg (fun o _ => mul_nonneg (hF.velocity_bounds.outWeight_nonneg o)
        (Finset.sum_nonneg (fun n _ => p1 _)))
    · exact Finset.sum_nonneg (fun o _ => mul_nonneg (hbb.outWeight_nonneg o)
        (Finset.sum_nonneg (fun n _ => p1 _)))
  have key : farWeighted c K S B x.2.2.2.1 ζ x.1 x.2.1 R ≤ ∑' jl,
      ((∑ o, Ts.outWeight o * ∑ n ∈ Ts.outModes o, gs o n jl)
      + (∑ o, Tv.outWeight o * ∑ n ∈ Tv.outModes o, gv o n jl)
      + (∑ o, Tb.outWeight o * ∑ n ∈ Tb.outModes o, gb o n jl)) := by
    unfold farWeighted
    refine tsum_le_of_le ((gS.add gV).add gB) hG0 (fun jl => ?_)
    obtain ⟨j, l⟩ := jl
    dsimp only
    split_ifs with hfar
    · have hdl : S.degHigh < max j l := by omega
      set Y : ℤ → Fin 3 → Fin 3 → ℂ := fun n a b => B.coef K (Ts.outputMode c.order B (strainInput u) (a, b) n) j l
        with hY
      set V : ℤ → Fin 3 → ℂ := fun n a => B.coef K (Tb.outputMode c.order B (velocityInput u) a n) j l with hV
      set W : ℤ → Fin 3 → ℂ := fun n a => B.coef K (Tv.outputMode c.order B (velocityInput u) a n) j l with hW
      have egs : ∀ o n, gs o n (j, l) = ‖Y n o.1 o.2‖ ^ 2 := fun o n => if_pos hfar
      have egv : ∀ o n, gv o n (j, l) = ‖W n o‖ ^ 2 := fun o n => if_pos hfar
      have egb : ∀ o n, gb o n (j, l) = ‖V n o‖ ^ 2 := fun o n => if_pos hfar
      have hGS : ∑ o, Ts.outWeight o * ∑ n ∈ Ts.outModes o, gs o n (j, l)
          = F.strainWeight * ∑ n ∈ S.resolved ∪ S.band, sumSq (Y n) := by
        simp only [egs]
        show ∑ o : Fin 3 × Fin 3, F.strainWeight * ∑ n ∈ S.resolved ∪ S.band, ‖Y n o.1 o.2‖ ^ 2 = _
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Fintype.sum_prod_type]
        rfl
      have hGV : ∑ o, Tv.outWeight o * ∑ n ∈ Tv.outModes o, gv o n (j, l)
          = F.resolvedVelocityWeight * ∑ n ∈ S.resolved, vecSq (W n) := by
        simp only [egv]
        show ∑ o : Fin 3, F.resolvedVelocityWeight * ∑ n ∈ S.resolved, ‖W n o‖ ^ 2 = _
        rw [← Finset.mul_sum, Finset.sum_comm]
        rfl
      have hGB : ∑ o, Tb.outWeight o * ∑ n ∈ Tb.outModes o, gb o n (j, l)
          = F.bandVelocityWeight * ∑ n ∈ S.band, vecSq (V n) := by
        simp only [egb]
        show ∑ o : Fin 3, F.bandVelocityWeight * ∑ n ∈ S.band, ‖V n o‖ ^ 2 = _
        rw [← Finset.mul_sum, Finset.sum_comm]
        rfl
      rw [hGS, hGV, hGB]
      have hstrain : (∑ n ∈ R.yModes,
          if n ∉ S.resolved ∨ S.degHigh < max j l then
            (symSq fun a b => B.coef K (fun p => yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b) j l) / S.symWeight n j l +
              (antiSq fun a b => B.coef K (fun p => yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b) j l) / S.antiWeight n j l
          else 0)
          ≤ F.strainWeight * ∑ n ∈ S.resolved ∪ S.band, sumSq (Y n) + F.bandVelocityWeight * ∑ n ∈ S.band, vecSq (V n) := by
        calc _ ≤ ∑ n ∈ R.yModes, (if n ∈ S.resolved ∪ S.band then
                F.strainWeight * sumSq (Y n) + (if n ∈ S.band then F.bandVelocityWeight * vecSq (V n) else 0) else 0) := by
              refine Finset.sum_le_sum (fun n hn => ?_)
              rw [if_pos (Or.inr hdl)]
              have hX := (hcf n hn j l hfar).1
              have hfun : (fun a b => B.coef K (fun p => yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b) j l) =
                  fun a b => (if n ∈ S.resolved ∪ S.band then Y n a b else 0)
                    + (if n ∈ S.band ∧ b = 1 then turnAdjInv (azimuth c.order n) (V n) a else 0) := by
                funext a b
                exact hX a b
              rw [hfun]
              by_cases hrb : n ∈ S.resolved ∪ S.band
              · simp only [hrb, if_true]
                have hfl := (hF.far_floor n j l hfar).1 hrb
                have ht := strain_term (Y n) (turnAdjInv (azimuth c.order n) (V n)) (n ∈ S.band) (S.symWeight n j l)
                  (S.antiWeight n j l) F.strainFloor F.share hF.floors_pos.1 hfl.1 hfl.2 hF.share_pos
                refine ht.trans ?_
                have hY0 : 0 ≤ sumSq (Y n) := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
                have hsw := hF.strainWeight_ge
                have hbw := hF.bandVelocityWeight_ge
                have fl0 := hF.floors_pos.1
                by_cases hnb : n ∈ S.band
                · rw [if_pos hnb, if_pos hnb, if_pos hnb]
                  have hne : S.band ≠ ∅ := Finset.ne_empty_of_mem hnb
                  rw [if_neg hne] at hsw
                  have hT := hF.turn_bound n hnb (V n)
                  have hVpos : 0 ≤ vecSq (V n) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
                  have h1 : (1 + F.share) / F.strainFloor * sumSq (Y n) ≤ F.strainWeight * sumSq (Y n) :=
                    mul_le_mul_of_nonneg_right hsw hY0
                  have h2 : (1 + 1 / F.share) / F.strainFloor * vecSq (turnAdjInv (azimuth c.order n) (V n))
                      ≤ (1 + 1 / F.share) / F.strainFloor * (F.turnBound ^ 2 * vecSq (V n)) :=
                    mul_le_mul_of_nonneg_left hT
                      (div_nonneg (add_nonneg zero_le_one (one_div_nonneg.mpr hF.share_pos.le)) fl0.le)
                  have h3 : (1 + 1 / F.share) / F.strainFloor * (F.turnBound ^ 2 * vecSq (V n))
                      = (1 + 1 / F.share) * F.turnBound ^ 2 / F.strainFloor * vecSq (V n) := by ring
                  have h4 : (1 + 1 / F.share) * F.turnBound ^ 2 / F.strainFloor * vecSq (V n)
                      ≤ F.bandVelocityWeight * vecSq (V n) := mul_le_mul_of_nonneg_right (hbw hne) hVpos
                  linarith
                · rw [if_neg hnb, if_neg hnb, if_neg hnb]
                  have h0 : 1 / F.strainFloor ≤ F.strainWeight := by
                    refine le_trans ?_ hsw
                    split_ifs
                    · exact le_rfl
                    · exact div_le_div_of_nonneg_right (by linarith [hF.share_pos]) fl0.le
                  have := mul_le_mul_of_nonneg_right h0 hY0
                  linarith
              · have hnb : n ∉ S.band := fun h => hrb (Finset.mem_union_right _ h)
                simp [hrb, hnb, symSq, antiSq]
          _ = F.strainWeight * ∑ n ∈ S.resolved ∪ S.band, sumSq (Y n)
              + F.bandVelocityWeight * ∑ n ∈ S.band, vecSq (V n) := by
              rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub, Finset.sum_add_distrib, Finset.mul_sum,
                Finset.sum_ite_mem, Finset.inter_eq_right.mpr Finset.subset_union_right, Finset.mul_sum]
      have hvel : ∑ n ∈ S.resolved, (vecSq fun a => B.coef K (fun p => yVelocity c K S x.1 x.2.1 n p a) j l)
          / S.velWeight n j l ≤ F.resolvedVelocityWeight * ∑ n ∈ S.resolved, vecSq (W n) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun n hn => ?_)
        have hWn := (hcf n (hsub (Finset.mem_union_left _ hn)) j l hfar).2 hn
        have hfun : (fun a => B.coef K (fun p => yVelocity c K S x.1 x.2.1 n p a) j l) = W n := funext hWn
        rw [hfun]
        have hv := (hF.far_floor n j l hfar).2 hn
        have fl0 := hF.floors_pos.2
        have hW0 : 0 ≤ vecSq (W n) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        have e1 : vecSq (W n) / S.velWeight n j l ≤ vecSq (W n) / F.velocityFloor := div_le_div_of_nonneg_left hW0 fl0 hv
        have e2 : vecSq (W n) / F.velocityFloor = 1 / F.velocityFloor * vecSq (W n) := by ring
        have e3 := mul_le_mul_of_nonneg_right hF.resolvedVelocityWeight_ge hW0
        linarith
      linarith
    · exact hG0 (j, l)
  rw [Summable.tsum_add (gS.add gV) gB, Summable.tsum_add gS gV, eS, eV, eB] at key
  unfold farCoefSum at tS tV tB
  have hk2 : farMajorantForm c K S F u ≤ farFormValue c K S R B x ζ := hker
  linarith

open CellScalars MeshFarInternal in
theorem farMajorant_of_parts (h : TailMajorantStatement) (hcoef : FarCoefStatement) (hreg : FarRegularStatement)
    (hsum : FarSummableStatement) : FarMajorantStatement := by
  intro α hα1 hα2 k N c hc K S B slots R F hK hsol hS hB hsub hF x hx ζ
  by_cases hb0 : S.band = ∅
  · have hF' : IsFarMajorant c K S B R (bandless F) :=
      { hF with
        band_bounds := fun h' => absurd hb0 h'
        bandVelocityWeight_ge := fun h' => absurd hb0 h'
        kernel_dominates := fun u => by
          have e := hF.kernel_dominates u
          unfold farMajorantForm at e ⊢
          simp only [if_pos hb0, add_zero] at e ⊢
          exact e }
    refine farMajorant_core h hcoef hreg hsum α hα1 hα2 c hc K S B R (bandless F) hK hsol hS hB hsub hF' ?_ ?_ x hx ζ
    · exact ⟨fun _ => le_rfl, fun _ _ => le_rfl, fun _ _ => le_rfl,
        fun _ _ _ _ _ _ _ => by simp [bandGroupFamily, bandless],
        fun _ _ _ _ _ _ _ => by simp [bandGroupFamily, bandless]⟩
    · intro _ j l
      unfold groupWeight
      split_ifs <;> simp [bandGroupFamily, bandless]
  · exact farMajorant_core h hcoef hreg hsum α hα1 hα2 c hc K S B R F hK hsol hS hB hsub hF (hF.band_bounds hb0)
      (fun h' => absurd h' hb0) x hx ζ

theorem farMajorant_of (h : TailMajorantStatement) (hcoef : FarCoefStatement) (hcyl : CylinderCompStatement) :
    FarMajorantStatement :=
  farMajorant_of_parts h hcoef (farRegular_of hcyl) farSummable_holds

end CellAnalysis

end CellCert

end Breakdown
