import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_1629_891
    (hlin : ∀ (n : ℕ) (C : Circuit), Monotone2 C →
      (∀ k : Fin n, ∃ x y : Fin n → Bool, (∀ j : Fin n, j ≠ k → x j = y j) ∧
        circuitFun n C x ≠ circuitFun n C y) → n ≤ C.size + 1)
    (hzero : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      Monotone2 C → NestedCover.ReadsBack (N + N) C →
      (∀ p l : Fin N, I p l → circuitFun (N + N) C
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) C z = false) →
      PEqualNP.CrossAnd.crossCount (N + N)
        (Finset.univ.filter (fun v : Fin (N + N) => N ≤ v.val)) C = 0 → N * q ≤ 6 * C.size + 2 * N)
    (hstep : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      Monotone2 C → NestedCover.ReadsBack (N + N) C →
      (∀ p l : Fin N, I p l → circuitFun (N + N) C
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) C z = false) →
      0 < PEqualNP.CrossAnd.crossCount (N + N)
        (Finset.univ.filter (fun v : Fin (N + N) => N ≤ v.val)) C →
      ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack (N + N) D ∧
        D.size ≤ C.size + 15 ∧ PEqualNP.CrossAnd.crossCount (N + N)
        (Finset.univ.filter (fun v : Fin (N + N) => N ≤ v.val)) D < PEqualNP.CrossAnd.crossCount (N + N)
        (Finset.univ.filter (fun v : Fin (N + N) => N ≤ v.val)) C ∧
        ∀ z : Fin (N + N) → Bool,
          Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
          circuitFun (N + N) D z = circuitFun (N + N) C z) : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → N * q ≤ 100 * C.size := by
  have h4 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧ D.size ≤ C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C := by
      intro n C0 hC
      classical
      have hevA : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.and l = l.all id := fun _ => rfl
      have hevO : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.or l = l.any id := fun _ => rfl
      let fx : ℕ → PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun j g =>
        if g.op = PEqualNP.CircuitLowerBounds.GateOp.and then (if ∀ i ∈ g.inputs, i < n + j then g else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
        else ⟨g.op, g.inputs.filter (fun i => decide (i < n + j))⟩
      have hfx_eval : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (w : List Bool), w.length = n + j → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
          (fx j g).op.eval ((fx j g).inputs.map fun i => w.getD i false) = g.op.eval (g.inputs.map fun i => w.getD i false) := by
        intro j g w hw hop
        have hfw : ∀ i, n + j ≤ i → w.getD i false = false := by
          intro i hi
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
          rfl
        rcases hop with hop | hop
        · by_cases hall : ∀ i ∈ g.inputs, i < n + j
          · simp only [fx, hop, if_pos hall, ite_true]
          · simp only [fx, hop, if_neg hall, ite_true]
            push_neg at hall
            obtain ⟨i, hi, hge⟩ := hall
            simp only [hevA, hevO, List.map_nil, List.any_nil]
            symm
            rw [List.all_eq_false]
            exact ⟨false, List.mem_map.mpr ⟨i, hi, hfw i hge⟩, by simp⟩
        · have hne : g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and := by rw [hop]; intro h; cases h
          simp only [fx, if_neg hne, hop, hevO]
          rw [Bool.eq_iff_iff]
          simp only [List.any_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq, id]
          constructor
          · rintro ⟨b, ⟨i, ⟨hi, _⟩, rfl⟩, hb⟩
            exact ⟨_, ⟨i, hi, rfl⟩, hb⟩
          · rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
            by_cases hlt : i < n + j
            · exact ⟨_, ⟨i, ⟨hi, hlt⟩, rfl⟩, hb⟩
            · rw [hfw i (by omega)] at hb
              exact absurd hb (by simp)
      have hop : ∀ g ∈ C0.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
        intro g hg
        have := (hC g hg).1
        simpa using this
      have key : ∀ G : List PEqualNP.CircuitLowerBounds.Gate, (∀ g ∈ G, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ x : List Bool, x.length = n →
          (G.mapIdx fx).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
            = G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x ∧
          (G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length = n + G.length := by
        intro G
        induction G using List.reverseRecOn with
        | nil => intro _ x hx; simp [hx]
        | append_singleton G g ih =>
          intro hG x hx
          obtain ⟨ih1, ih2⟩ := ih (fun g' hg' => hG g' (List.mem_append_left _ hg')) x hx
          have hg := hG g (by simp)
          rw [List.mapIdx_append, List.foldl_append, List.foldl_append, ih1]
          simp only [List.mapIdx_cons, List.mapIdx_nil, List.foldl_cons, List.foldl_nil, zero_add]
          refine ⟨?_, by rw [List.length_append, ih2]; simp; omega⟩
          rw [hfx_eval G.length g _ ih2 hg]
      refine ⟨⟨C0.gates.mapIdx fx, C0.output⟩, ?_, ?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨j, hj, rfl⟩ := List.mem_mapIdx.mp hg
        have hm := hC _ (List.getElem_mem hj)
        have ho := hop _ (List.getElem_mem hj)
        by_cases ha : (C0.gates[j]).op = PEqualNP.CircuitLowerBounds.GateOp.and
        · by_cases hall : ∀ i ∈ (C0.gates[j]).inputs, i < n + j
          · simp only [fx, ha, if_pos hall, ite_true]
            exact ⟨by simp, hm.2⟩
          · simp only [fx, ha, if_neg hall, ite_true]
            exact ⟨by simp, by simp⟩
        · simp only [fx, if_neg ha]
          exact ⟨hm.1, le_trans (List.length_filter_le _ _) hm.2⟩
      · intro j hj i hi
        simp only [List.length_mapIdx] at hj
        have hgd : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨C0.gates.mapIdx fx, C0.output⟩ j = fx j (C0.gates[j]) := by
          show (C0.gates.mapIdx fx).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = fx j (C0.gates[j])
          simp [List.getD_eq_getElem?_getD, hj]
        rw [hgd] at hi
        by_cases ha : (C0.gates[j]).op = PEqualNP.CircuitLowerBounds.GateOp.and
        · by_cases hall : ∀ i ∈ (C0.gates[j]).inputs, i < n + j
          · simp only [fx, ha, if_pos hall, ite_true] at hi
            exact hall i hi
          · simp only [fx, ha, if_neg hall, ite_true] at hi
            simp at hi
        · simp only [fx, if_neg ha, List.mem_filter, decide_eq_true_eq] at hi
          exact hi.2
      · show (C0.gates.mapIdx fx).length ≤ C0.gates.length
        simp
      · funext x
        show ((C0.gates.mapIdx fx).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD C0.output false = (C0.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD C0.output false
        rw [(key C0.gates hop (List.ofFn x) (by simp)).1]
  intro q N I _ C hq hN hcard hline hmon hacc hsound
  have hNpos : 2 ≤ N := by nlinarith
  have hcast_ne_nat : ∀ (p l : Fin N), Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro p l h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have hsens : ∀ k : Fin (N + N), ∃ x y : Fin (N + N) → Bool,
      (∀ j : Fin (N + N), j ≠ k → x j = y j) ∧
      circuitFun (N + N) C x ≠ circuitFun (N + N) C y := by
    intro k
    by_cases hk : k.val < N
    · let p : Fin N := ⟨k.val, hk⟩
      have hkp : k = Fin.castAdd N p := Fin.ext rfl
      let p' : Fin N := if p.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
      have hne : p ≠ p' := by
        intro h
        have hv := congrArg Fin.val h
        by_cases hp0 : p.val = 0 <;> simp [p', hp0] at hv
      obtain ⟨l, ⟨hIpl, _⟩, _⟩ := hline p p' hne
      let x : Fin (N + N) → Bool := fun j => decide (j = Fin.natAdd N l)
      let y : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l)
      refine ⟨x, y, ?_, ?_⟩
      · intro j hj
        rw [hkp] at hj
        simp only [x, y, hj, false_or]
      · have hy : circuitFun (N + N) C y = true := hacc p l hIpl
        have hx : circuitFun (N + N) C x = false := by
          apply hsound x
          · have hsub : Finset.univ.filter (fun l' : Fin N => x (Fin.natAdd N l') = true) ⊆ {l} := by
              intro l' hl'
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, x, decide_eq_true_eq] at hl'
              have hval := congrArg Fin.val hl'
              simp only [Fin.val_natAdd] at hval
              exact Finset.mem_singleton.mpr (Fin.ext (by omega))
            exact (Finset.card_le_card hsub).trans (by simp; omega)
          · rintro ⟨p0, l0, _, hp0, _⟩
            simp only [x, decide_eq_true_eq] at hp0
            exact hcast_ne_nat p0 l hp0
        rw [hx, hy]
        decide
    · let l : Fin N := ⟨k.val - N, by omega⟩
      have hkl : k = Fin.natAdd N l := Fin.ext (by simp [l]; omega)
      have hpos : 0 < (Finset.univ.filter (fun p : Fin N => I p l)).card := by
        rw [hcard l]; omega
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
      have hIpl : I p l := (Finset.mem_filter.mp hp).2
      let x : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p)
      let y : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l)
      refine ⟨x, y, ?_, ?_⟩
      · intro j hj
        rw [hkl] at hj
        simp only [x, y, hj, or_false]
      · have hy : circuitFun (N + N) C y = true := hacc p l hIpl
        have hx : circuitFun (N + N) C x = false := by
          apply hsound x
          · have hemp : Finset.univ.filter (fun l' : Fin N => x (Fin.natAdd N l') = true) = ∅ := by
              ext l'
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
                iff_false, x, decide_eq_true_eq]
              intro h
              exact hcast_ne_nat p l' h.symm
            rw [hemp]
            simp
          · rintro ⟨p0, l0, _, _, hl0⟩
            simp only [x, decide_eq_true_eq] at hl0
            exact hcast_ne_nat p l0 hl0.symm
        rw [hx, hy]
        decide
  have hNsize : N ≤ C.size := by
    have h2N := hlin (N + N) C hmon hsens
    omega
  classical
  have hcard' : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1 := by
    intro l
    simpa only [Fintype.card_subtype] using hcard l
  have hsound' : ∀ z : Fin (N + N) → Bool,
      Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N + N) C z = false := by
    intro z hz hn
    rw [Fintype.card_subtype] at hz
    exact hsound z hz hn
  have pairWeight (p l : Fin N) :
      Fintype.card {t : Fin N // decide (Fin.natAdd N t = Fin.castAdd N p ∨
        Fin.natAdd N t = Fin.natAdd N l) = true} ≤ q := by
    rw [Fintype.card_subtype]
    have ht : (Finset.univ.filter fun t : Fin N => decide (Fin.natAdd N t = Fin.castAdd N p ∨
        Fin.natAdd N t = Fin.natAdd N l) = true) ⊆ {l} := by
      intro t ht
      obtain ht | ht := of_decide_eq_true (Finset.mem_filter.mp ht).2
      · exact (hcast_ne_nat p t ht.symm).elim
      · apply Finset.mem_singleton.mpr
        have hv := congrArg Fin.val ht
        simp only [Fin.val_natAdd] at hv
        exact Fin.ext (by omega)
    exact (Finset.card_le_card ht).trans (by simp; omega)
  let K : Circuit → ℕ := PEqualNP.CrossAnd.crossCount (N + N)
    (Finset.univ.filter (fun v : Fin (N + N) => N ≤ v.val))
  let Good : Circuit → Prop := fun D => Monotone2 D ∧ NestedCover.ReadsBack (N + N) D ∧
    (∀ p l : Fin N, I p l → circuitFun (N + N) D
      (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) ∧
    (∀ z : Fin (N + N) → Bool,
      Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N + N) D z = false)
  have eliminate : ∀ k (D : Circuit), Good D → K D = k →
      ∃ E : Circuit, Good E ∧ K E = 0 ∧ E.size ≤ D.size + 15 * k := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro D hd hk
      by_cases hz : k = 0
      · exact ⟨D, hd, hk.trans hz, by omega⟩
      · obtain ⟨hm, hr, hp, hs⟩ := hd
        obtain ⟨E, hem, her, hes, hek, heval⟩ := hstep q N I D hq hN hcard' hline
          hm hr hp hs (by change 0 < K D; omega)
        have heg : Good E := by
          refine ⟨hem, her, ?_, ?_⟩
          · intro p l hi
            rw [heval _ (pairWeight p l)]
            exact hp p l hi
          · intro z hz hn
            rw [heval z hz]
            exact hs z hz hn
        have hek' : K E < k := by change K E < K D at hek; omega
        obtain ⟨F, hfg, hfk, hfs⟩ := ih (K E) hek' E heg rfl
        refine ⟨F, hfg, hfk, ?_⟩
        omega
  obtain ⟨D, hdm, hdr, hds, hdf⟩ := h4 (N + N) C hmon
  have hdg : Good D := by
    refine ⟨hdm, hdr, ?_, ?_⟩
    · rw [hdf]
      exact hacc
    · rw [hdf]
      exact hsound'
  obtain ⟨E, heg, hek, hes⟩ := eliminate (K D) D hdg rfl
  have hkbound : K D ≤ D.size := by
    change (Finset.filter _ (Finset.range D.gates.length)).card ≤ D.gates.length
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
  have hEsize : E.size ≤ 16 * C.size := by omega
  obtain ⟨hem, her, hep, hesound⟩ := heg
  have hb := hzero q N I E hq hN hcard' hline hem her hep hesound hek
  nlinarith
