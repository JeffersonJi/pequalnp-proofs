import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1578_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]; simp [step]

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix gs w
  rw [ht]; simp [hl]

theorem fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem fold_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ)
    (h : w.length + gs.length ≤ i) : (gs.foldl step w).getD i false = false := by
  rw [List.getD_eq_default]; rw [fold_length]; exact h


def rd (C : Circuit) (x : List Bool) (g i : ℕ) : Bool :=
  if i < g then (C.wires x).getD i false else false

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := fold_length _ _

theorem wires_input (C : Circuit) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (C.wires x).getD i false = x.getD i false := fold_getD_lt _ _ _ h

theorem wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false
      = C.gates[j].op.eval (C.gates[j].inputs.map fun i => rd C x (x.length + j) i) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    simp
  set A := (C.gates.take j).foldl step x with hA
  have hAl : A.length = x.length + j := by
    rw [hA, fold_length]; simp; omega
  have hw : C.wires x = (C.gates.drop (j + 1)).foldl step (step A C.gates[j]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hreadA : ∀ i, A.getD i false = rd C x (x.length + j) i := by
    intro i
    unfold rd
    by_cases hi : i < x.length + j
    · rw [if_pos hi, hw, fold_getD_lt _ (step A C.gates[j]) i (by simp [step]; omega), step,
        List.getD_append _ _ _ _ (by omega)]
    · rw [if_neg hi, List.getD_eq_default]; omega
  rw [hw, fold_getD_lt _ _ _ (by simp [step]; omega), step,
    List.getD_append_right _ _ _ _ (by omega)]
  simp only [hAl, Nat.sub_self]
  simp only [List.getD_cons_zero]
  congr 1
  exact List.map_congr_left (fun i _ => hreadA i)

def value {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  Circuit.eval ⟨gs,w⟩ (List.ofFn x)

lemma input_value {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (p : Fin n) :
    value gs x p.val = x p := by
  unfold value Circuit.eval
  rw [wires_input _ _ p.val (by simp)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, p.isLt]

lemma gate_value {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin gs.length)
    (hvalid : ∀ a ∈ (gs.get i).inputs, a < n+i.val) :
    value gs x (n+i.val) = (gs.get i).op.eval ((gs.get i).inputs.map (value gs x)) := by
  have hv := wires_gate (⟨gs,0⟩ : Circuit) (List.ofFn x) i.val i.isLt
  simp only [List.length_ofFn] at hv
  change ((⟨gs,0⟩ : Circuit).wires (List.ofFn x)).getD (n+i.val) false = _
  rw [hv]
  congr 1
  apply List.map_congr_left
  intro a ha
  simp only [rd, if_pos (hvalid a ha)]
  rfl

lemma earlier_wire {n : ℕ} (gs : List Gate) (zs : Fin gs.length)
    (X Y Z : Fin n → Bool)
    (hb : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hv : ∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs, a < n+i.val)
    (ha : ∀ i : Fin gs.length, i < zs → (gs.get i).op = GateOp.and →
      value gs X (n+i.val) = false → value gs Y (n+i.val) = false →
      value gs Z (n+i.val) = false)
    (hinput : ∀ p, X p = false → Z p = true → Y p = true) :
    ∀ w, w < n+zs.val → value gs X w = false → value gs Z w = true → value gs Y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx hz
    by_cases hn : w < n
    · let p : Fin n := ⟨w,hn⟩
      have eX := input_value gs X p
      have eY := input_value gs Y p
      have eZ := input_value gs Z p
      exact eY.trans (hinput p (eX.symm.trans hx) (eZ.symm.trans hz))
    · let i : Fin gs.length := ⟨w-n, by omega⟩
      have hi : i < zs := by change w-n < zs.val; omega
      have he : w = n+i.val := by change w = n+(w-n); omega
      rw [he] at hx hz ⊢
      rcases hb (gs.get i) (List.get_mem gs i) with hop | hop
      · by_cases hy : value gs Y (n+i.val) = true
        · exact hy
        · have hyf : value gs Y (n+i.val) = false := by cases hh : value gs Y (n+i.val) <;> simp_all
          have hzF := ha i hi hop hx hyf
          rw [hzF] at hz
          contradiction
      · have hxAll : ∀ a ∈ (gs.get i).inputs, value gs X a = false := by
          rw [gate_value gs X i (hv i), hop] at hx
          simpa [GateOp.eval] using hx
        obtain ⟨a, hai, hza⟩ : ∃ a ∈ (gs.get i).inputs, value gs Z a = true := by
          rw [gate_value gs Z i (hv i), hop] at hz
          simpa [GateOp.eval] using hz
        have hay : value gs Y a = true := ih a (by have := hv i a hai; omega) (by have := hv i a hai; omega) (hxAll a hai) hza
        rw [gate_value gs Y i (hv i), hop]
        simpa [GateOp.eval] using (show ∃ a ∈ (gs.get i).inputs, value gs Y a = true from ⟨a,hai,hay⟩)

end PEqualNP.Outside.L_meta_1578_aux

open PEqualNP.Outside.L_meta_1578_aux in
theorem PEqualNP.Outside.L_meta_1578 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (zs : Fin gates.length) (u v : ℕ) (l m : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) →
    (gates.get zs).op = PEqualNP.CircuitLowerBounds.GateOp.and → (gates.get zs).inputs = [u, v] →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 3 ∨ ((3 = 3 ∨ 3 = 9) ∧ v ∉ L 0)))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 9 ∨ ((9 = 3 ∨ 9 = 9) ∧ v ∉ L 0)))) = true) →
    (∀ i : Fin gates.length, i < zs → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false →
      ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 3 ∨ ((3 = 3 ∨ 3 = 9) ∧ v ∉ L 0)))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 9 ∨ ((9 = 3 ∨ 9 = 9) ∧ v ∉ L 0)))) = false) →
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = true) ∨
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = true) := by
  classical
  intro L hL gs zs u v l m hb hv hl hm hop hins h0 hll hmm hpos hear
  let co := fun r p : Fin 13 => decide (p ∉ L r)
  let test := fun c p : Fin 13 => decide (p = c ∨ p ∉ L 0)
  have hpos' : value gs (test 3) (13+zs.val) = true ∨ value gs (test 9) (13+zs.val) = true := by
    simpa [value, test] using hpos
  obtain ⟨c, hc, hz⟩ : ∃ c : Fin 13, (c=3 ∨ c=9) ∧ value gs (test c) (13+zs.val) = true := by
    rcases hpos' with h | h
    · exact ⟨3, Or.inl rfl, h⟩
    · exact ⟨9, Or.inr rfl, h⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl hm
  have hl0 : l ≠ 0 := by rcases hl with rfl | rfl | rfl <;> decide
  have hm0 : m ≠ 0 := by rcases hm with rfl | rfl | rfl <;> decide
  have hcl : c ∉ L l := by rcases hc with rfl | rfl <;> rcases hl with rfl | rfl | rfl <;> norm_num [hL]
  have hcm : c ∉ L m := by rcases hc with rfl | rfl <;> rcases hm with rfl | rfl | rfl <;> norm_num [hL]
  have hinp : ∀ r : Fin 13, c ∉ L r → ∀ p, co 0 p = false → test c p = true → co r p = true := by
    intro r hcr p hp ht
    have hp0 : p ∈ L 0 := by simpa [co] using hp
    have ht' : p=c ∨ p ∉ L 0 := by simpa [test] using ht
    have he := ht'.resolve_right (fun hn => hn hp0)
    subst p
    simp [co, hcr]
  have earlier : ∀ r : Fin 13, r ≠ 0 → c ∉ L r →
      ∀ w, w < 13+zs.val → value gs (co 0) w = false →
        value gs (test c) w = true → value gs (co r) w = true := by
    intro r hr0 hcr
    apply earlier_wire gs zs (co 0) (co r) (test c)
      (fun g hg => (hb g hg).1) (fun i a ha => (hv i).2 a ha)
    · intro i hi hand hi0 hir
      have hh := hear i hi hand (by simpa [value, co] using hi0) r hr0 (by simpa [value, co] using hir)
      rcases hc with rfl | rfl
      · simpa [value, test] using hh.1
      · simpa [value, test] using hh.2
    · exact hinp r hcr
  have hug : u < 13+zs.val := (hv zs).2 u (by rw [hins]; simp)
  have hvg : v < 13+zs.val := (hv zs).2 v (by rw [hins]; simp)
  have hand : ∀ x : Fin 13 → Bool, value gs x (13+zs.val) = (value gs x u && value gs x v) := by
    intro x
    rw [gate_value gs x zs (hv zs).2, hop, hins]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  have h0' : (value gs (co 0) u && value gs (co 0) v) = false := by
    rw [← hand]; exact h0
  have hl' : (value gs (co l) u && value gs (co l) v) = false := by
    rw [← hand]; exact hll
  have hm' : (value gs (co m) u && value gs (co m) v) = false := by
    rw [← hand]; exact hmm
  rw [hand] at hz
  have hzpair : value gs (test c) u = true ∧ value gs (test c) v = true := by simpa using hz
  have hzu := hzpair.1
  have hzv := hzpair.2
  by_cases hu0 : value gs (co 0) u = false
  · have hul := earlier l hl0 hcl u hug hu0 hzu
    have hum := earlier m hm0 hcm u hug hu0 hzu
    have hvl : value gs (co l) v = false := by simpa [hul] using hl'
    have hvm : value gs (co m) v = false := by simpa [hum] using hm'
    have hv0 : value gs (co 0) v = true := by
      cases he : value gs (co 0) v with
      | false =>
        have hh := earlier l hl0 hcl v hvg he hzv
        rw [hh] at hvl
        contradiction
      | true => rfl
    exact Or.inr ⟨hvl,hvm,hv0,hu0,hul,hum⟩
  · have hu0T : value gs (co 0) u = true := by
      cases he : value gs (co 0) u with
      | false => exact False.elim (hu0 he)
      | true => rfl
    have hv0 : value gs (co 0) v = false := by simpa [hu0T] using h0'
    have hvl := earlier l hl0 hcl v hvg hv0 hzv
    have hvm := earlier m hm0 hcm v hvg hv0 hzv
    have hul : value gs (co l) u = false := by simpa [hvl] using hl'
    have hum : value gs (co m) u = false := by simpa [hvm] using hm'
    exact Or.inl ⟨hul,hum,hu0T,hv0,hvl,hvm⟩
