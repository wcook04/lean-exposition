import TorusEuler.Paper.Proofs.S5a.Library.TowerVel

/-!
# S5a library: the lifting estimate for the velocity of the integrated mean system

`main_tower_bound` carries out the lifting step of `sections/06d_mean_estimates.tex:44-58` on the towers of a
smooth mean solution: Lemma D.3 (`hD3`, via `tower_lifting`) with the zero-order inverse bound of Theorem 4.2
(`H1`, via `zero_order`) gives `‖v‖_{[n]} ≤ C_n C_low ‖P ∫g‖_{[n]}`; the word norms are the sums of closed-time
norms of the words (`Vt.Y w`, `gt.Y w`). The base identity `hmom` is the projected equation (4.9).
-/

open Set
open scoped ContDiff

namespace TorusEuler.Paper.Lib.S5a.Tower

noncomputable section

local notation "C½" => HalfHolder (UnitAddTorus (Fin 3)) Vec3
local notation "K½" => HalfHolder (UnitAddTorus (Fin 3)) (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal

local instance towerMainSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance towerMainSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `hasSD_neg`. -/
theorem hasSD_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : Vec3}
    {f df : HalfHolder (UnitAddTorus (Fin 3)) E} (h : endpointTorusHasSpatialDerivative u f df) :
    endpointTorusHasSpatialDerivative u (-f) (-df) := by
  intro a s
  have hn := (h a s).neg
  change HasDerivAt (fun r : ℝ => -(HalfHolder.eval (a + toUnitTorus (r • u)) f)) _ s at hn
  simpa only [map_neg] using hn

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `norm_S_eq`. -/
theorem norm_S_eq (x : S) : ‖(x : C½)‖ = ‖x‖ := rfl

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `N_coe_eq`. -/
theorem N_coe_eq {T : ℝ} {u : ℝ → S} {y : ℝ → C½} (h : ∀ t ∈ Icc 0 T, (u t : C½) = y t) :
    endpointClosedTimeNorm T u = endpointClosedTimeNorm T y := by
  unfold endpointClosedTimeNorm
  congr 1
  apply Set.image_congr
  intro t ht
  rw [← h t ht]
  rfl

set_option maxHeartbeats 2000000 in
/-- The lifting estimate (Lemma D.3 on the towers of the integrated mean system (4.9), `sections/06d_mean_estimates.tex:44-58`): `‖v‖_{[n],1/2} ≤ C_n C_low ‖P ∫ g‖_{[n],1/2}` as sums of closed-time norms of the words; `H1` is the first item of Theorem 4.2, `hmom` the projected equation (4.9) at the base level. -/
theorem main_tower_bound (hD3 : Statement.lemma_D_3) {T : ℝ} (hT : 0 < T)
    {Kf Ωf : ℝ × Vec3 → (Vec3 →L[ℝ] Vec3)} (Kt : SymTower T Kf) (Ωt : SymTower T Ωf)
    {A : ℝ}
    (H1 : ∀ src : ℝ → C½, ContinuousOn src (Icc 0 T) →
      ∃ (z v : ℝ → S) (c : S) (φ : Pressure) (G : ℝ → C½),
        EndpointSystemSolution T (Kt.Y []) (Ωt.Y []) src z v c φ G ∧
        endpointClosedTimeNorm T v ≤ A * endpointClosedTimeNorm T src ∧
        ∀ (z' v' : ℝ → S) (c' : S) (φ' : Pressure) (G' : ℝ → C½),
          EndpointSystemSolution T (Kt.Y []) (Ωt.Y []) src z' v' c' φ' G' →
          EqOn z' z (Icc 0 T) ∧ EqOn v' v (Icc 0 T) ∧ c' = c ∧ EqOn G' G (Icc 0 T))
    {v z : ℝ → Vec3 → Vec3}
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hz : ContDiffOn ℝ ∞ (Function.uncurry z) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hzper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (z t))
    (hz0 : z 0 = 0) (hzT : z T = 0)
    (hzd : ∀ t ∈ Icc 0 T, ∀ x, HasDerivWithinAt (fun r => z r x) (v t x) (Icc 0 T) t)
    (hdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (v t) x = 0)
    (Vt : SymTower T (Function.uncurry v))
    {gf : ℝ → Vec3 → Vec3} (gt : SymTower T (Function.uncurry gf))
    (srcT : SymTower T (fun p : ℝ × Vec3 => -endpointPrimitive (fun r => gf r p.2) p.1))
    (Θt : SymTower T (fun p : ℝ × Vec3 =>
      -endpointPrimitive (fun r => Ωf (r, p.2) (v r p.2)) p.1))
    (hgc : ContinuousOn (gt.Y []) (Icc 0 T))
    (hmom : ∀ t ∈ Icc 0 T,
      pjL ((Kt.Y [] t).coefficientMul (Vt.Y [] t)) - pjL ((Kt.Y [] 0).coefficientMul (Vt.Y [] 0)) -
        pjL (endpointPrimitive (fun r => (Ωt.Y [] r).coefficientMul (Vt.Y [] r)) t) =
          pjL (endpointPrimitive (gt.Y []) t))
    (n : ℕ) (Cm : ℕ → ℝ) :
    0 ≤ Cn_of hD3 n Cm ∧ ∀ (ℓ Clow : ℝ), 0 ≤ ℓ → 0 ≤ Clow → A ≤ Clow →
      (∀ m, 1 ≤ m → m ≤ n →
        Clow * (4 * ‖pjL‖ * ∑ w ∈ (hierarchyAdmissibleWords (Fin 3) m).filter
              (fun w => w.length = m), ℓ ^ m * endpointClosedTimeNorm T (Kt.Y w) +
            2 * ‖pjL‖ * T * ∑ w ∈ (hierarchyAdmissibleWords (Fin 3) m).filter
              (fun w => w.length = m), ℓ ^ m * endpointClosedTimeNorm T (Ωt.Y w)) ≤ Cm m) →
      ∑ w ∈ hierarchyAdmissibleWords (Fin 3) n, ℓ ^ w.length * endpointClosedTimeNorm T (Vt.Y w) ≤
        Cn_of hD3 n Cm * Clow * (‖pjL‖ * T) * ∑ w ∈ hierarchyAdmissibleWords (Fin 3) n,
          ℓ ^ w.length * endpointClosedTimeNorm T (gt.Y w) := by
  classical
  obtain ⟨hCn, HL⟩ := tower_lifting hD3 hT n Cm
  refine ⟨hCn, fun ℓ Clow hℓ hClow hAC hD7 => ?_⟩
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  obtain ⟨u, hE, hu⟩ := exists_velocityTower hT hv hz hzper hz0 hzT hzd hdiv Vt
  have haK : Kt.Y ∈ tower T K½ := ⟨Kt.sym, fun w => (Kt.smooth w).continuousOn⟩
  have haΩ : Ωt.Y ∈ tower T K½ := ⟨Ωt.sym, fun w => (Ωt.smooth w).continuousOn⟩
  -- zero-order estimate
  have hZero : ∀ u' ∈ Esp T hT.le, endpointClosedTimeNorm T (u' []) ≤
      Clow * endpointClosedTimeNorm T (Tk Kt.Y u' [] + Tom T Ωt.Y u' []) := by
    intro u' hu'
    refine (zero_order hT (haK.2 []) (haΩ.2 []) H1 haK haΩ (fun _ _ => rfl) (fun _ _ => rfl)
      u' hu').trans ?_
    exact mul_le_mul_of_nonneg_right hAC (endpointClosedTimeNorm_nonneg hT.le _)
  have key := HL ℓ Clow hℓ hClow Kt.Y Ωt.Y haK haΩ hZero hD7 u hE
  -- derivative towers
  have hdu : ∀ (i : Fin 3) (w : Wd), ∀ t ∈ Icc 0 T,
      endpointTorusHasSpatialDerivative (coordinateDirection i) (u w t : C½) (u (i :: w) t : C½) := by
    intro i w t ht
    rw [hu w t ht, hu (i :: w) t ht]
    exact Vt.der i w t ht
  have huS : Sym u := hE.1.1
  -- the tower of the `Ω`-term
  have hΘforce : ∀ q, ContinuousOn (Tw q Ωt.Y u) (Icc 0 T) := fun q => Tw_continuousOn haΩ hE.1 q
  have hΘbase : EqOn (Θt.Y []) (fun t => -endpointPrimitive (Tw [] Ωt.Y u) t) (Icc 0 T) :=
    endpointSourceCurve_eq_negPrimitive_of_lift (Θt.Y []) (Tw [] Ωt.Y u)
      (fun r x => Ωf (r, x) (v r x)) (hΘforce [])
      (fun t ht x => by
        have e1 : HalfHolder.eval (toUnitTorus x) (Tw [] Ωt.Y u t) =
            Ωf (t, x) (v t x) := by
          simp only [Tw, HalfHolder.eval_coefficientMul]
          rw [hu [] t ht, Ωt.lift [] t ht x, Vt.lift [] t ht x]
          rfl
        exact e1)
      (fun t ht x => by
        have h := Θt.lift [] t ht x
        exact h)
  have hΘkey (q : Wd) : EqOn (Θt.Y q) (fun t => -endpointPrimitive (Tw q Ωt.Y u) t) (Icc 0 T) :=
    endpointSourceWords_eq_negPrimitive hT Θt.Y (fun q => Tw q Ωt.Y u) coordinateDirection q.length
      (fun r _ => (Θt.smooth r).differentiableOn (by simp))
      (fun r _ => hΘforce r)
      (fun i r _ t ht => Θt.der i r t ht)
      (fun i r _ t ht => Tw_der Ωt.sym huS Ωt.der hdu r i t ht) hΘbase q le_rfl
  have hTom (w : Wd) (t : ℝ) (ht : t ∈ Icc 0 T) : Tom T Ωt.Y u w t = pjL (Θt.Y w t) := by
    simp only [Tom, primC_eq ht, hΘkey w ht, map_neg]
  -- the tower of the forcing
  have hFder : IsDer T (Tk Kt.Y u + Tom T Ωt.Y u) := by
    intro i w t ht
    have h1 := Tk_der Kt.sym huS Kt.der hdu w i ht
    have h2 : endpointTorusHasSpatialDerivative (coordinateDirection i)
        (Tom T Ωt.Y u w t) (Tom T Ωt.Y u (i :: w) t) := by
      rw [hTom w t ht, hTom (i :: w) t ht]
      exact hasSD_pjL (Θt.der i w t ht)
    exact h1.add h2
  have hsrcBase : EqOn (srcT.Y []) (fun t => -endpointPrimitive (gt.Y []) t) (Icc 0 T) :=
    endpointSourceCurve_eq_negPrimitive_of_lift (srcT.Y []) (gt.Y []) (fun r x => gf r x) hgc
      (fun t ht x => gt.lift [] t ht x) (fun t ht x => srcT.lift [] t ht x)
  have hsrcKey (q : Wd) : EqOn (srcT.Y q) (fun t => -endpointPrimitive (gt.Y q) t) (Icc 0 T) :=
    endpointSourceWords_eq_negPrimitive hT srcT.Y gt.Y coordinateDirection q.length
      (fun r _ => (srcT.smooth r).differentiableOn (by simp))
      (fun r _ => (gt.smooth r).continuousOn)
      (fun i r _ t ht => srcT.der i r t ht) (fun i r _ t ht => gt.der i r t ht) hsrcBase q le_rfl
  let Yg : Wd → ℝ → C½ := fun w t => -pjL (srcT.Y w t)
  have hYder : IsDer T Yg := by
    intro i w t ht
    exact hasSD_neg (hasSD_pjL (srcT.der i w t ht))
  have hbase : ∀ t ∈ Icc 0 T, (Tk Kt.Y u + Tom T Ωt.Y u) [] t = Yg [] t := by
    intro t ht
    have e1 : Tk Kt.Y u [] t = pjL ((Kt.Y [] t).coefficientMul (Vt.Y [] t)) -
        pjL ((Kt.Y [] 0).coefficientMul (Vt.Y [] 0)) := by
      simp only [Tk, Tw, hu [] t ht, hu [] 0 h0]
    have e2 : Tom T Ωt.Y u [] t =
        -pjL (endpointPrimitive (fun r => (Ωt.Y [] r).coefficientMul (Vt.Y [] r)) t) := by
      have hp : endpointPrimitive (Tw [] Ωt.Y u) t =
          endpointPrimitive (fun r => (Ωt.Y [] r).coefficientMul (Vt.Y [] r)) t := by
        unfold endpointPrimitive
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le ht.1]
        intro r hr
        simp only [Tw, hu [] r ⟨hr.1, hr.2.trans ht.2⟩]
      simp only [Tom, primC_eq ht, hp]
    have e3 : Yg [] t = pjL (endpointPrimitive (gt.Y []) t) := by
      simp only [Yg, hsrcKey [] ht, map_neg, neg_neg]
    simp only [Pi.add_apply, e1, e2, e3]
    rw [← hmom t ht]
    abel
  have hF : ∀ w, ∀ t ∈ Icc 0 T, (Tk Kt.Y u + Tom T Ωt.Y u) w t = Yg w t :=
    eq_of_der hFder hYder hbase
  -- the norms
  have hNu (w : Wd) : endpointClosedTimeNorm T (u w) = endpointClosedTimeNorm T (Vt.Y w) :=
    N_coe_eq (hu w)
  have hNF (w : Wd) : endpointClosedTimeNorm T (Tk Kt.Y u w + Tom T Ωt.Y u w) ≤
      ‖pjL‖ * T * endpointClosedTimeNorm T (gt.Y w) := by
    have e : endpointClosedTimeNorm T (Tk Kt.Y u w + Tom T Ωt.Y u w) =
        endpointClosedTimeNorm T (Yg w) := endpointClosedTimeNorm_congr (hF w)
    rw [e]
    apply endpointClosedTimeNorm_le hT.le
    intro t ht
    have h1 : ‖srcT.Y w t‖ ≤ endpointClosedTimeNorm T (srcT.Y w) :=
      norm_le_endpointClosedTimeNorm (srcT.smooth w).continuousOn ht
    have h2 := endpointClosedTimeNorm_le_of_negPrimitive hT (gt.smooth w).continuousOn (hsrcKey w)
    calc ‖Yg w t‖ = ‖pjL (srcT.Y w t)‖ := norm_neg _
      _ ≤ ‖pjL‖ * ‖srcT.Y w t‖ := pjL.le_opNorm _
      _ ≤ ‖pjL‖ * (T * endpointClosedTimeNorm T (gt.Y w)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg pjL)
      _ = _ := by ring
  have hCC : 0 ≤ Cn_of hD3 n Cm * Clow := mul_nonneg hCn hClow
  calc ∑ w ∈ hierarchyAdmissibleWords (Fin 3) n, ℓ ^ w.length * endpointClosedTimeNorm T (Vt.Y w)
      = ∑ w ∈ hierarchyAdmissibleWords (Fin 3) n, ℓ ^ w.length * endpointClosedTimeNorm T (u w) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hNu]
    _ ≤ Cn_of hD3 n Cm * Clow * ∑ w ∈ hierarchyAdmissibleWords (Fin 3) n,
          ℓ ^ w.length * endpointClosedTimeNorm T (Tk Kt.Y u w + Tom T Ωt.Y u w) := key
    _ ≤ Cn_of hD3 n Cm * Clow * ∑ w ∈ hierarchyAdmissibleWords (Fin 3) n,
          ℓ ^ w.length * (‖pjL‖ * T * endpointClosedTimeNorm T (gt.Y w)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ => ?_) hCC
        exact mul_le_mul_of_nonneg_left (hNF w) (pow_nonneg hℓ _)
    _ = _ := by
        rw [mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        ring

end

end TorusEuler.Paper.Lib.S5a.Tower
