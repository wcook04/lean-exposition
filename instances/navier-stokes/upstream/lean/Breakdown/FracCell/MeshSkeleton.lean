import Breakdown.FracCell.MeshSkeletonSplit

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

namespace MeshSkeletonInternal

variable {α : ℝ} {k N : ℕ} {c : FracCellData k N} {Sp : CellSplit k N} {M : MeshData k N Sp} {x : FieldTuple k}

theorem segSplitRow (hS : StreamIndependenceStatement) (h1 : 1 < α) (h2 : α < 5 / 4) (hc : IsFormData α c)
    (hM : IsMeshData α c Sp M) (hx : IsAdmissible c x) (K : Fin Sp.cellCount)
    (j : Fin (systemSkeletonCoords (M.coords K).layout (M.coords K).param).card) (parts : List (Fin Sp.slots × ℝ))
    (extra : List ((K' : Fin Sp.cellCount) × (M.coords K').layout.Datum × ℝ))
    (hkap : ∀ p ∈ parts, ∀ a, Sp.kappaSlot a ≠ p.1)
    (hdel : ∀ p ∈ parts, ¬ M.IsDelaySlot p.1)
    (hpart : ∀ p ∈ parts, (M.rowDatum (M.ownerCell p.1) (M.ownerRow p.1)).2 = (M.rowDatum K j).2)
    (hext : ∀ e ∈ extra, (M.coords e.1).layout.IsGaugeDeleted e.2.1)
    (hsplit : SegmentSplit (M.rowKey K j) (parts.map (fun p => (M.ownerKey p.1, p.2)) ++ M.extraKeys extra))
    (hnodes : ∀ u ∈ M.participantNodes K j parts ++ M.extraNodes extra,
      ∀ v ∈ M.participantNodes K j parts ++ M.extraNodes extra, u.1 = v.1 → u.2 = v.2) :
    (parts.map (fun p => p.2 * M.canonicalMoment c x p.1)).sum = M.localValue c K x j := by
  classical
  obtain ⟨hrp, hrc, hq, hzero⟩ := split_kinds _ _ hsplit
  set Ls := M.participantNodes K j parts ++ M.extraNodes extra with hLs
  set ν : ℝ → ℝ := fun r => if h : ∃ u ∈ Ls, u.1 = r then M.classValue x (Classical.choose h).2 else 0
    with hνdef
  have hν : ∀ u ∈ Ls, M.classValue x u.2 = ν u.1 := by
    intro u hu
    have h : ∃ u' ∈ Ls, u'.1 = u.1 := ⟨u, hu, rfl⟩
    rw [hνdef]
    dsimp only
    rw [dif_pos h]
    obtain ⟨h1', h2'⟩ := Classical.choose_spec h
    exact congrArg _ (hnodes u hu _ h1' h2'.symm)
  have glue : ∀ (K' : Fin Sp.cellCount) (d : (M.coords K').layout.Datum), keyOf _ d ≠ SkeletonKey.private_ →
      (∀ n p a, keyOf _ d ≠ SkeletonKey.corner n p a) →
      (∀ u ∈ (pressurePositions (M.coords K').layout d).map (fun q => (q.1, M.nodeClass K' q.2)), u ∈ Ls) →
      (M.coords K').layout.shiftedData
          ((M.coords K').layout.gaugeShiftOf (M.canonicalLeft K') (M.canonicalRight K')) x d
        = keyData (M.coords K).layout x ν (keyOf _ d) := by
    intro K' d hp hcn hin
    refine shifted_key hS hx (hM.same_order K) (layoutValid hM K') (hM.same_gauge K K') _ _ ν d hp hcn ?_
    intro u hu
    rw [side_value]
    exact hν _ (hin _ (List.mem_map.2 ⟨u, hu, rfl⟩))
  set b := (M.rowDatum K j).2 with hb
  set V := keyData (M.coords K).layout x ν with hV
  let pt : ℂ → ℝ := fun z => if b = 0 then z.re else z.im
  have hrow : M.localValue c K x j = pt (V (M.rowKey K j)) / keyScale c.splitVisc (M.rowKey K j) := by
    unfold MeshData.localValue
    simp only [CellLayout.realPart]
    rw [glue K _ hrp hrc (fun u hu => List.mem_append_left _ (List.mem_append_left _ hu)), scale_key]
    rfl
  have hown : ∀ p ∈ parts, M.canonicalMoment c x p.1 =
      pt (V (M.ownerKey p.1)) / keyScale c.splitVisc (M.rowKey K j) := by
    intro p hp
    have hnk : ¬ ∃ a, Sp.kappaSlot a = p.1 := fun ⟨a, ha⟩ => hkap p hp a ha
    have hmem : (M.ownerKey p.1, p.2) ∈ parts.map (fun p => (M.ownerKey p.1, p.2)) ++ M.extraKeys extra :=
      List.mem_append_left _ (List.mem_map.2 ⟨p, hp, rfl⟩)
    obtain ⟨hp1, hp2, hp3⟩ := hq _ hmem
    unfold MeshData.canonicalMoment
    rw [if_neg (hdel p hp)]
    unfold MeshData.baseMoment
    rw [dif_neg hnk]
    unfold MeshData.localValue
    simp only [CellLayout.realPart]
    rw [glue _ _ hp1 hp2 (fun u hu => List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨p, hp, rfl⟩, hu⟩))), scale_key, hpart p hp]
    have := hp3 c.splitVisc
    simp only at this
    rw [← this]
    rfl
  have hextra : ∀ e ∈ extra, pt (V (keyOf (M.coords e.1).layout e.2.1)) = 0 := by
    intro e he
    have hmem : (keyOf (M.coords e.1).layout e.2.1, e.2.2) ∈
        parts.map (fun p => (M.ownerKey p.1, p.2)) ++ M.extraKeys extra :=
      List.mem_append_right _ (List.mem_map.2 ⟨e, he, rfl⟩)
    obtain ⟨hp1, hp2, _⟩ := hq _ hmem
    obtain ⟨rad, lev, lo, hi, t, dd, hkey⟩ := deleted_key _ (hext e he)
    obtain ⟨rad', lev', lo', hi', t', dd', hrk⟩ := hzero _ hmem rad lev lo hi t dd hkey
    have hb0 : b = 0 := system_part K j (mode_of_pressure _ hrk)
    have hz := deleted_zero h1 h2 hc hM hx e.1 e.2.1 (hext e he)
    rw [glue _ _ hp1 hp2 (fun u hu => List.mem_append_right _
      (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨e, he, rfl⟩, hu⟩))] at hz
    simp only [pt, hb0, if_true]
    exact hz
  have hsum := congrArg pt (segmentSplit_keyData hx (M.coords K).layout (hM.same_order K) ν _ _ hsplit
    (level_pos (layoutValid hM K) _))
  rw [show pt ((List.map (fun p => (p.2 : ℂ) * keyData (M.coords K).layout x ν p.1)
      (parts.map (fun p => (M.ownerKey p.1, p.2)) ++ M.extraKeys extra)).sum) =
      ((parts.map (fun p => (M.ownerKey p.1, p.2)) ++ M.extraKeys extra).map
        (fun p => p.2 * pt (V p.1))).sum from part_lin b _ V] at hsum
  rw [List.map_append, List.sum_append] at hsum
  have hz2 : ((M.extraKeys extra).map (fun p => p.2 * pt (V p.1))).sum = 0 := by
    unfold MeshData.extraKeys
    rw [List.map_map]
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
    simp only [Function.comp]
    rw [hextra e he, mul_zero]
  rw [hz2, add_zero, List.map_map] at hsum
  rw [hrow, List.map_congr_left (fun p hp => by rw [hown p hp]), list_div]
  congr 1
  exact hsum.symm


end MeshSkeletonInternal

open MeshSkeletonInternal

theorem meshSkeletonSlot_of (hS : StreamIndependenceStatement) (hF : FluxStreamStatement) :
    MeshSkeletonSlotStatement := by
  intro α hα1 hα2 k N c hc Sp M hM x hx K j
  obtain ⟨parts, extra, hT, hkap, hnd0, hpart, hext, hcase, hnodes⟩ := hM.rows K j
  have hsum : ∑ i, (M.coords K).Tmap j i * M.canonicalMoment c x i =
      (parts.map (fun p => p.2 * M.canonicalMoment c x p.1)).sum := by
    rw [← sum_rowEntries]
    exact Finset.sum_congr rfl (fun i _ => by rw [hT i])
  rw [hsum]
  rcases hcase with ⟨hex, i, hpi, hk, hpriv⟩ | hs | hf | ⟨hp0, hex, hdel⟩
  · subst hpi hex
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
    have hnk : ¬ ∃ a, Sp.kappaSlot a = i := fun ⟨a, ha⟩ => hkap (i, 1) (List.mem_singleton_self _) a ha
    unfold MeshData.canonicalMoment
    rw [if_neg (hnd0 (i, 1) (List.mem_singleton_self _))]
    unfold MeshData.baseMoment
    rw [dif_neg hnk]
    by_cases hpv : M.rowKey K j = SkeletonKey.private_
    · obtain ⟨hK, hj⟩ := hpriv hpv
      subst hK
      rw [eq_of_heq hj]
    · have hn := hnodes
      simp only [MeshData.participantNodes, MeshData.extraNodes, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil, List.append_nil] at hn
      exact (localValue_eq hS hM hx K (M.ownerCell i) j (M.ownerRow i) hk hpv
        (hpart (i, 1) (List.mem_singleton_self _)).symm hn).symm
  · exact segSplitRow hS hα1 hα2 hc hM hx K j parts extra hkap hnd0 hpart hext hs hnodes
  · exact fluxSplitRow hS hF hM hx K j parts extra hkap hnd0 hpart hext hf hnodes
  · subst hp0 hex
    obtain ⟨K', d, hdl, hkd, hnd⟩ := hdel
    obtain ⟨rad, lev, lo, hi, t, dd, hkey⟩ := deleted_key d hdl
    have hrow : M.rowKey K j = SkeletonKey.pressure 0 rad lev lo hi t dd := hkd.symm.trans hkey
    have h2 := system_part K j (mode_of_pressure _ hrow)
    have e := value_eq hS hM hx K K' (M.rowDatum K j).1 d (hkd.symm : M.rowKey K j = keyOf _ d)
      (by
        intro h
        have h' : M.rowKey K j = SkeletonKey.private_ := h
        rw [h'] at hrow
        cases hrow) (fun u hu v hv huv => hnd u hu v hv huv)
    unfold MeshData.localValue
    simp only [CellLayout.realPart, h2, if_true, List.map_nil, List.sum_nil]
    rw [e, deleted_zero hα1 hα2 hc hM hx K' d hdl, zero_div]

end Breakdown.CellCert.CellCoordinates
