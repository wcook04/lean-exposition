import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-! Smooth gluing from matching time derivatives on a boundary hyperplane. -/

open Set Filter
open scoped ContDiff Topology

noncomputable section

namespace TorusEuler

universe u v

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

private def along (s : Set X) (f : X → F) (d : X) (x : X) : F :=
  fderivWithin ℝ f s x d

private def repeatedJet (s : Set X) (f : X → F) (d : X) (n : ℕ) (x : X) : F :=
  iteratedFDerivWithin ℝ n f s x (fun _ => d)

private theorem repeatedJet_zero (s : Set X) (f : X → F) (d x : X) :
    repeatedJet s f d 0 x = f x := by
  simp [repeatedJet]

private theorem along_smooth {s : Set X} {f : X → F} (h : ContDiffOn ℝ ∞ f s)
    (hs : UniqueDiffOn ℝ s) (d : X) : ContDiffOn ℝ ∞ (along s f d) s :=
  (h.fderivWithin hs (by simp)).clm_apply contDiffOn_const

private theorem repeatedJet_succ {s : Set X} {f : X → F}
    (h : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s) (d : X) (n : ℕ) {x : X} (hx : x ∈ s) :
    repeatedJet s f d (n + 1) x = along s (repeatedJet s f d n) d x := by
  unfold repeatedJet along
  rw [iteratedFDerivWithin_succ_apply_left,
    fderivWithin_continuousMultilinear_apply_const_apply (hs x hx)
      (h.differentiableOn_iteratedFDerivWithin (m := n) (by exact_mod_cast ENat.natCast_lt_top n) hs x hx)]
  rfl

private theorem repeatedJet_smooth {s : Set X} {f : X → F} (h : ContDiffOn ℝ ∞ f s)
    (hs : UniqueDiffOn ℝ s) (d : X) (n : ℕ) : ContDiffOn ℝ ∞ (repeatedJet s f d n) s := by
  induction n with
  | zero => exact h.congr fun x _ => repeatedJet_zero s f d x
  | succ n ih => exact (along_smooth ih hs d).congr fun _ hx => repeatedJet_succ h hs d n hx

private theorem along_comp_eval {s : Set X} {f : X → F}
    (h : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s) (d w : X) {x : X} (hx : x ∈ s) :
    along s (along s f d) w x = (fderivWithin ℝ (fderivWithin ℝ f s) s x w) d := by
  let eval : (X →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F d
  have hD := (h.fderivWithin hs (m := ∞) (by simp)).differentiableOn (by simp) x hx
  have hc := eval.hasFDerivAt.comp_hasFDerivWithinAt x hD.hasFDerivWithinAt
  exact congrArg (fun L : X →L[ℝ] F => L w) (hc.fderivWithin (hs x hx))

private theorem along_comm {s : Set X} {f : X → F}
    (h : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s) (hcl : s ⊆ closure (interior s))
    (d w : X) {x : X} (hx : x ∈ s) :
    along s (along s f d) w x = along s (along s f w) d x := by
  rw [along_comp_eval h hs d w hx, along_comp_eval h hs w d hx]
  exact (h x hx).isSymmSndFDerivWithinAt (by simp) hs (hcl hx) hx w d

private theorem repeatedJet_along {s : Set X} {f : X → F}
    (h : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s) (hcl : s ⊆ closure (interior s))
    (d w : X) (n : ℕ) :
    EqOn (repeatedJet s (along s f w) d n) (along s (repeatedJet s f d n) w) s := by
  induction n with
  | zero =>
    intro x hx
    rw [repeatedJet_zero]
    exact congrArg (fun L : X →L[ℝ] F => L w)
      (fderivWithin_congr' (fun z _ => (repeatedJet_zero s f d z).symm) hx)
  | succ n ih =>
    intro x hx
    rw [repeatedJet_succ (along_smooth h hs w) hs d n hx]
    have hnext : EqOn (repeatedJet s f d (n + 1)) (along s (repeatedJet s f d n) d) s :=
      fun z hz => repeatedJet_succ h hs d n hz
    change fderivWithin ℝ (repeatedJet s (along s f w) d n) s x d =
      fderivWithin ℝ (repeatedJet s f d (n + 1)) s x w
    rw [fderivWithin_congr' ih hx, fderivWithin_congr' hnext hx]
    exact along_comm (repeatedJet_smooth h hs d n) hs hcl w d hx

section Slices

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem hasFDerivWithinAt_timeSlice {f : ℝ × E → F} {I : Set ℝ} {O : Set E}
    {t : ℝ} {x : E} (hx : x ∈ O) {L : (ℝ × E) →L[ℝ] F}
    (h : HasFDerivWithinAt f L (I ×ˢ O) (t, x)) :
    HasFDerivWithinAt (fun r : ℝ => f (r, x)) (L.comp (ContinuousLinearMap.inl ℝ ℝ E)) I t := by
  let A : ℝ →L[ℝ] ℝ × E := ContinuousLinearMap.inl ℝ ℝ E
  have hin : HasFDerivAt (fun r : ℝ => A r + (0, x)) (A + 0) t :=
    A.hasFDerivAt.add (hasFDerivAt_const (c := ((0 : ℝ), x)) (x := t))
  have hi : HasFDerivAt (fun r : ℝ => (r, x)) A t := by
    simpa [A] using hin
  exact h.comp t hi.hasFDerivWithinAt (fun r hr => show (r, x) ∈ I ×ˢ O from ⟨hr, hx⟩)

private theorem hasFDerivWithinAt_spaceSlice {f : ℝ × E → F} {I : Set ℝ} {O : Set E}
    {t : ℝ} {x : E} (ht : t ∈ I) {L : (ℝ × E) →L[ℝ] F}
    (h : HasFDerivWithinAt f L (I ×ˢ O) (t, x)) :
    HasFDerivWithinAt (fun y : E => f (t, y)) (L.comp (ContinuousLinearMap.inr ℝ ℝ E)) O x := by
  let A : E →L[ℝ] ℝ × E := ContinuousLinearMap.inr ℝ ℝ E
  have hin : HasFDerivAt (fun y : E => A y + (t, 0)) (A + 0) x :=
    A.hasFDerivAt.add (hasFDerivAt_const (c := (t, (0 : E))) (x := x))
  have hi : HasFDerivAt (fun y : E => (t, y)) A x := by
    simpa [A] using hin
  exact h.comp x hi.hasFDerivWithinAt (fun y hy => show (t, y) ∈ I ×ˢ O from ⟨ht, hy⟩)

/-- The time derivative of a slice is the joint derivative applied to time directions. -/
theorem iteratedDerivWithin_timeSlice {f : ℝ × E → F} {I : Set ℝ} {O : Set E}
    (h : ContDiffOn ℝ ∞ f (I ×ˢ O)) (hI : UniqueDiffOn ℝ I) (hO : UniqueDiffOn ℝ O)
    (n : ℕ) {t : ℝ} (ht : t ∈ I) {x : E} (hx : x ∈ O) :
    iteratedDerivWithin n (fun r => f (r, x)) I t =
      iteratedFDerivWithin ℝ n f (I ×ˢ O) (t, x) (fun _ => ((1 : ℝ), (0 : E))) := by
  let d : ℝ × E := (1, 0)
  change iteratedDerivWithin n (fun r => f (r, x)) I t =
    repeatedJet (I ×ˢ O) f d n (t, x)
  induction n generalizing t with
  | zero => rw [iteratedDerivWithin_zero, repeatedJet_zero]
  | succ n ih =>
    rw [iteratedDerivWithin_succ, repeatedJet_succ h (hI.prod hO) d n ⟨ht, hx⟩]
    have hs : UniqueDiffOn ℝ (I ×ˢ O) := hI.prod hO
    have hd := ((repeatedJet_smooth h hs d n).differentiableOn (by simp) (t, x)
      (show (t, x) ∈ I ×ˢ O from ⟨ht, hx⟩)).hasFDerivWithinAt
    have ht' := hasFDerivWithinAt_timeSlice hx hd
    have ht'' := ht'.congr (fun r hr => ih hr) (ih ht)
    rw [← fderivWithin_derivWithin, ht''.fderivWithin (hI t ht)]
    rfl

end Slices

section Gluing

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

private abbrev leftSlab (a : ℝ) (O : Set E) : Set (ℝ × E) := Icc a 0 ×ˢ O

private abbrev rightSlab (O : Set E) : Set (ℝ × E) := Ici 0 ×ˢ O

private abbrev fullSlab (a : ℝ) (O : Set E) : Set (ℝ × E) := Ici a ×ˢ O

private def terminalPiecewise (f g : ℝ × E → F) (z : ℝ × E) : F :=
  if z.1 ≤ 0 then f z else g z

omit [NormedSpace ℝ E] in
private theorem leftSlab_denseInterior {a : ℝ} (ha : a < 0) {O : Set E} (hO : IsOpen O) :
    leftSlab a O ⊆ closure (interior (leftSlab a O)) := by
  unfold leftSlab
  rw [interior_prod_eq, interior_Icc, hO.interior_eq, closure_prod_eq, closure_Ioo ha.ne]
  exact fun _ hz => ⟨hz.1, subset_closure hz.2⟩

omit [NormedSpace ℝ E] in
private theorem rightSlab_denseInterior {O : Set E} (hO : IsOpen O) :
    rightSlab O ⊆ closure (interior (rightSlab O)) := by
  unfold rightSlab
  rw [interior_prod_eq, interior_Ici, hO.interior_eq, closure_prod_eq, closure_Ioi]
  exact fun _ hz => ⟨hz.1, subset_closure hz.2⟩

private theorem fderivWithin_same_timeJets {a : ℝ} (ha : a < 0) {O : Set E} (hO : IsOpen O)
    {f g : ℝ × E → F} (hf : ContDiffOn ℝ ∞ f (leftSlab a O))
    (hg : ContDiffOn ℝ ∞ g (rightSlab O))
    (hjets : ∀ x ∈ O, ∀ n, repeatedJet (leftSlab a O) f (1, 0) n (0, x) =
      repeatedJet (rightSlab O) g (1, 0) n (0, x)) :
    ∀ x ∈ O, ∀ n, repeatedJet (leftSlab a O) (fderivWithin ℝ f (leftSlab a O)) (1, 0) n (0, x) =
      repeatedJet (rightSlab O) (fderivWithin ℝ g (rightSlab O)) (1, 0) n (0, x) := by
  intro x hx n
  let L := leftSlab a O
  let R := rightSlab O
  let e : ℝ × E := (1, 0)
  have hL : UniqueDiffOn ℝ L := (uniqueDiffOn_Icc ha).prod hO.uniqueDiffOn
  have hR : UniqueDiffOn ℝ R := (uniqueDiffOn_Ici 0).prod hO.uniqueDiffOn
  have hxL : (0, x) ∈ L := ⟨⟨ha.le, le_rfl⟩, hx⟩
  have hxR : (0, x) ∈ R := ⟨mem_Ici.mpr le_rfl, hx⟩
  have hn : ((n : ℕ) : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  let p := repeatedJet L f e n
  let q := repeatedJet R g e n
  have hp := repeatedJet_smooth hf hL e n
  have hq := repeatedJet_smooth hg hR e n
  have htime : along L p e (0, x) = along R q e (0, x) := by
    rw [← repeatedJet_succ hf hL e n hxL, ← repeatedJet_succ hg hR e n hxR]
    exact hjets x hx (n + 1)
  have hspace (w : E) : along L p (0, w) (0, x) = along R q (0, w) (0, x) := by
    have hleft := hasFDerivWithinAt_spaceSlice (I := Icc a 0) (t := 0) ⟨ha.le, le_rfl⟩
      ((hp.differentiableOn (by simp) (0, x) hxL).hasFDerivWithinAt)
    have hright := hasFDerivWithinAt_spaceSlice (I := Ici 0) (t := 0) (mem_Ici.mpr le_rfl)
      ((hq.differentiableOn (by simp) (0, x) hxR).hasFDerivWithinAt)
    have hs := hright.congr (fun y hy => hjets y hy n) (hjets x hx n)
    have he := (hleft.fderivWithin (hO.uniqueDiffOn x hx)).symm.trans
      (hs.fderivWithin (hO.uniqueDiffOn x hx))
    exact congrArg (fun A : E →L[ℝ] F => A w) he
  have hdiff (w : ℝ × E) : along L p w (0, x) = along R q w (0, x) := by
    have hw : w = w.1 • e + (0, w.2) := by
      ext <;> simp [e, smul_eq_mul]
    conv_lhs => rw [hw]
    conv_rhs => rw [hw]
    unfold along at *
    rw [map_add, map_add, map_smul, map_smul, htime, hspace]
  apply ContinuousLinearMap.ext
  intro w
  change (iteratedFDerivWithin ℝ n (fderivWithin ℝ f L) L (0, x) (fun _ => e)) w =
    (iteratedFDerivWithin ℝ n (fderivWithin ℝ g R) R (0, x) (fun _ => e)) w
  rw [← iteratedFDerivWithin_clm_apply_const_apply hL (hf.fderivWithin hL (m := ∞) (by simp)) hn hxL,
    ← iteratedFDerivWithin_clm_apply_const_apply hR (hg.fderivWithin hR (m := ∞) (by simp)) hn hxR]
  change repeatedJet L (along L f w) e n (0, x) = repeatedJet R (along R g w) e n (0, x)
  rw [repeatedJet_along hf hL (leftSlab_denseInterior ha hO) e w n hxL,
    repeatedJet_along hg hR (rightSlab_denseInterior hO) e w n hxR]
  exact hdiff w

private theorem terminalPiecewise_hasFDerivWithinAt {a : ℝ} {O : Set E} {f g : ℝ × E → F}
    (hf : ContDiffOn ℝ ∞ f (leftSlab a O)) (hg : ContDiffOn ℝ ∞ g (rightSlab O))
    (hval : ∀ x ∈ O, f (0, x) = g (0, x))
    (hd : ∀ x ∈ O, fderivWithin ℝ f (leftSlab a O) (0, x) =
      fderivWithin ℝ g (rightSlab O) (0, x)) :
    ∀ z ∈ fullSlab a O, HasFDerivWithinAt (terminalPiecewise f g)
      (terminalPiecewise (fderivWithin ℝ f (leftSlab a O)) (fderivWithin ℝ g (rightSlab O)) z)
      (fullSlab a O) z := by
  let L := leftSlab a O
  let R := rightSlab O
  let W := fullSlab a O
  let glue := terminalPiecewise f g
  let glueD := terminalPiecewise (fderivWithin ℝ f L) (fderivWithin ℝ g R)
  have hL (z : ℝ × E) (hz : z ∈ L) : HasFDerivWithinAt glue (glueD z) L z := by
    have hpiece : EqOn glue f L := by
      intro y hy
      simp [glue, terminalPiecewise, hy.1.2]
    have hJet : glueD z = fderivWithin ℝ f L z := by simp [glueD, terminalPiecewise, hz.1.2]
    rw [hJet]
    exact ((hf.differentiableOn (by simp) z hz).hasFDerivWithinAt).congr hpiece (hpiece hz)
  have hR (z : ℝ × E) (hz : z ∈ R) : HasFDerivWithinAt glue (glueD z) R z := by
    have hpiece : EqOn glue g R := by
      intro y hy
      change (if y.1 ≤ 0 then f y else g y) = g y
      split
      · next h =>
        have hy0 : y.1 = 0 := le_antisymm h hy.1
        have heq : y = (0, y.2) := Prod.ext hy0 rfl
        rw [heq]
        exact hval y.2 hy.2
      · rfl
    have hJet : glueD z = fderivWithin ℝ g R z := by
      change (if z.1 ≤ 0 then fderivWithin ℝ f L z else fderivWithin ℝ g R z) = _
      split
      · next h =>
        have hz0 : z.1 = 0 := le_antisymm h hz.1
        have heq : z = (0, z.2) := Prod.ext hz0 rfl
        rw [heq]
        exact hd z.2 hz.2
      · rfl
    rw [hJet]
    exact ((hg.differentiableOn (by simp) z hz).hasFDerivWithinAt).congr hpiece (hpiece hz)
  intro z hz
  change HasFDerivWithinAt glue (glueD z) W z
  rcases lt_trichotomy z.1 0 with hlt | heq | hgt
  · have hzL : z ∈ L := ⟨⟨hz.1, hlt.le⟩, hz.2⟩
    have hnear : L ∈ 𝓝[W] z := by
      apply eventually_nhdsWithin_iff.mpr
      have H : ∀ᶠ y : ℝ × E in 𝓝 z, y.1 < 0 :=
        (isOpen_lt continuous_fst continuous_const).mem_nhds hlt
      exact H.mono fun y hy hyW => ⟨⟨hyW.1, hy.le⟩, hyW.2⟩
    exact (hL z hzL).mono_of_mem_nhdsWithin hnear
  · have hzL : z ∈ L := ⟨⟨hz.1, heq.le⟩, hz.2⟩
    have hzR : z ∈ R := ⟨heq.ge, hz.2⟩
    exact ((hL z hzL).union (hR z hzR)).mono (fun y hy =>
      (le_total y.1 0).imp (fun h => ⟨⟨hy.1, h⟩, hy.2⟩) (fun h => ⟨h, hy.2⟩))
  · have hzR : z ∈ R := ⟨hgt.le, hz.2⟩
    have hnear : R ∈ 𝓝[W] z := by
      apply eventually_nhdsWithin_iff.mpr
      have H : ∀ᶠ y : ℝ × E in 𝓝 z, 0 < y.1 :=
        (isOpen_lt continuous_const continuous_fst).mem_nhds hgt
      exact H.mono fun y hy hyW => ⟨hy.le, hyW.2⟩
    exact (hR z hzR).mono_of_mem_nhdsWithin hnear

private theorem terminalPiecewise_contDiffOn_nat {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a : ℝ} (ha : a < 0) {O : Set E}
    (hO : IsOpen O) (k : ℕ) {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f g : ℝ × E → G} (hf : ContDiffOn ℝ ∞ f (leftSlab a O))
    (hg : ContDiffOn ℝ ∞ g (rightSlab O))
    (hjets : ∀ x ∈ O, ∀ n, repeatedJet (leftSlab a O) f (1, 0) n (0, x) =
      repeatedJet (rightSlab O) g (1, 0) n (0, x)) :
    ContDiffOn ℝ (k : ℕ∞ω) (terminalPiecewise f g) (fullSlab a O) := by
  induction k generalizing G with
  | zero =>
    have hgrad := fderivWithin_same_timeJets ha hO hf hg hjets
    have hval (x : E) (hx : x ∈ O) := hjets x hx 0
    have hd (x : E) (hx : x ∈ O) := hgrad x hx 0
    simp only [repeatedJet_zero] at hval hd
    have H := terminalPiecewise_hasFDerivWithinAt hf hg hval hd
    exact contDiffOn_zero.mpr fun z hz => (H z hz).continuousWithinAt
  | succ k ih =>
    have hgrad := fderivWithin_same_timeJets ha hO hf hg hjets
    have hval (x : E) (hx : x ∈ O) := hjets x hx 0
    have hd (x : E) (hx : x ∈ O) := hgrad x hx 0
    simp only [repeatedJet_zero] at hval hd
    have H := terminalPiecewise_hasFDerivWithinAt hf hg hval hd
    rw [Nat.cast_succ, contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      ((uniqueDiffOn_Ici a).prod hO.uniqueDiffOn)]
    exact ⟨by simp, _, ih
      (hf.fderivWithin ((uniqueDiffOn_Icc ha).prod hO.uniqueDiffOn) (m := ∞) (by simp))
      (hg.fderivWithin ((uniqueDiffOn_Ici 0).prod hO.uniqueDiffOn) (m := ∞) (by simp)) hgrad, H⟩

/-- Smooth fields on either side of the time-zero hyperplane glue when all time jets agree. -/
theorem contDiffOn_terminalPiecewise_of_timeJets {E G : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {a : ℝ} (ha : a < 0) {O : Set E} (hO : IsOpen O) {f g : ℝ × E → G}
    (hf : ContDiffOn ℝ ∞ f (Icc a 0 ×ˢ O)) (hg : ContDiffOn ℝ ∞ g (Ici 0 ×ˢ O))
    (hjets : ∀ x ∈ O, ∀ n : ℕ,
      iteratedFDerivWithin ℝ n f (Icc a 0 ×ˢ O) (0, x) (fun _ => ((1 : ℝ), (0 : E))) =
        iteratedFDerivWithin ℝ n g (Ici 0 ×ˢ O) (0, x) (fun _ => ((1 : ℝ), (0 : E)))) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => if z.1 ≤ 0 then f z else g z) (Ioi a ×ˢ O) :=
  (contDiffOn_infty.mpr (fun k => terminalPiecewise_contDiffOn_nat ha hO k hf hg hjets)).mono
    (fun _ hz => ⟨mem_Ici.mpr (mem_Ioi.mp hz.1).le, hz.2⟩)

end Gluing

end TorusEuler
