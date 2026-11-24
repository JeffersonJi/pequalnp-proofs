import Mathlib
import PEqualNP.Defs

-- Reduction adapted from public PR3067 (L-meta-1515).
-- Counting adapted from public PR3062 (L-meta-1516).
-- The assembly and protected-set transfer specialize them to this step.

namespace PEqualNP.Outside.L_meta_1517_aux.Reduction
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

def Rep {n : ℕ} {P : (Fin n → Bool) → Prop} (new : List Gate) (f : (Subtype P) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Subtype P, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Subtype P, (W new x.val).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h

lemma rep_congr {n : ℕ} {P : (Fin n → Bool) → Prop} {new : List Gate} {f g : (Subtype P) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {P : (Fin n → Bool) → Prop} {new new' : List Gate} (he : Ext new new')
    (f : (Subtype P) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, if_neg hne]
      exact hv x

lemma rep_and {n : ℕ} {P : (Fin n → Bool) → Prop} (new : List Gate) (f g : (Subtype P) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x.val).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, Or.inl rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x.val).getD (n + new.length) false = (f x && g x)
      rw [W_val, if_pos rfl]
      show GateOp.and.eval [(W new x.val).getD j false, (W new x.val).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_or {n : ℕ} {P : (Fin n → Bool) → Prop} (new : List Gate) (f g : (Subtype P) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x.val).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, Or.inr rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x.val).getD (n + new.length) false = (f x || g x)
      rw [W_val, if_pos rfl]
      show GateOp.or.eval [(W new x.val).getD j false, (W new x.val).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma gate_rep {n : ℕ} {P : (Fin n → Bool) → Prop} (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, Rep (P := P) new (fun x => (W old x.val).getD t false)) :
    ∃ new', Ext new new' ∧
      Rep (P := P) new' (fun x => op.eval (l.map fun i => (W old x.val).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

variable {n : ℕ} {P : (Fin n → Bool) → Prop}

abbrev wire (old : List Gate) (t : ℕ) (x : Subtype P) := (W old x.val).getD t false
abbrev value (old : List Gate) (g : Gate) (x : Subtype P) :=
  g.op.eval (g.inputs.map fun i => wire old i x)
abbrev Good (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma reader_free (old new : List Gate) (g : Gate) (z : ℕ) (hg : Good g)
    (hm : z ∈ g.inputs) (hz : ∀ x : Subtype P, wire old z x = false)
    (hr : ∀ t, Rep (P := P) new (wire old t)) : Rep (P := P) new (value old g) := by
  obtain ⟨op,l⟩ := g
  obtain ⟨hop,hl⟩ := hg
  change z ∈ l at hm
  change l.length ≤ 2 at hl
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp at hm
  · simp at hm; subst a
    rcases hop with e | e <;> change op = _ at e <;> subst op <;>
      exact Or.inl ⟨false, fun x => by simpa [value, GateOp.eval, wire] using hz x⟩
  · simp at hm
    rcases hm with e | e <;> subst_vars <;> rcases hop with e | e <;>
      change op = _ at e <;> subst op
    · exact Or.inl ⟨false, fun x => by have h0 := hz x; simp [wire] at h0; simp [value, wire, GateOp.eval, h0]⟩
    · apply rep_congr _ (hr b); intro x; have h0 := hz x; simp [wire] at h0; simp [value, wire, GateOp.eval, h0]
    · exact Or.inl ⟨false, fun x => by have h0 := hz x; simp [wire] at h0; simp [value, wire, GateOp.eval, h0]⟩
    · apply rep_congr _ (hr a); intro x; have h0 := hz x; simp [wire] at h0; simp [value, wire, GateOp.eval, h0]
  · simp at hl

lemma stable (a b : List Gate) (x : Fin n → Bool) {t : ℕ} (ht : t < n + a.length) :
    (W (a ++ b) x).getD t false = (W a x).getD t false := by
  induction b using List.reverseRecOn with
  | nil => simp
  | append_singleton b g ih =>
    rw [← List.append_assoc, W_val, if_neg (by simp only [List.length_append]; omega), ih]

lemma take_stable (gs : List Gate) (k t : ℕ) (x : Fin n → Bool) (ht : t < n + (gs.take k).length) :
    (W (gs.take k) x).getD t false = (W gs x).getD t false := by
  simpa using (stable (gs.take k) (gs.drop k) x ht).symm

lemma compress (gs : List Gate) (start : ℕ) (hs : start ≤ gs.length)
    (S : Finset (Fin gs.length)) (hp : ∀ g ∈ gs.take start, Good g)
    (hbase : ∀ i ∈ S, start ≤ i.val)
    (action : ∀ (i : Fin gs.length), start ≤ i.val → ∀ new : List Gate,
      (∀ t, Rep (P := P) new (wire (gs.take i.val) t)) →
      ∃ new', Ext new new' ∧ (i ∈ S → new' = new) ∧ Rep (P := P) new' (value (gs.take i.val) (gs.get i))) :
    ∃ new, (∀ g ∈ new, Good g) ∧ gs.take start <+: new ∧ new.length + S.card ≤ gs.length ∧
      ∀ t, Rep (P := P) new (wire gs t) := by
  classical
  let C (k : ℕ) := (S.filter fun i => i.val < k).card
  have aux (k : ℕ) (hk : start ≤ k) (hk' : k ≤ gs.length) :
      ∃ new, (∀ g ∈ new, Good g) ∧ gs.take start <+: new ∧ new.length + C k ≤ k ∧
        ∀ t, Rep (P := P) new (wire (gs.take k) t) := by
    induction k, hk using Nat.le_induction with
    | base =>
      have hem : S.filter (fun i => i.val < start) = ∅ := by
        ext i; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]; rintro ⟨hi, hh⟩; exact (hh.not_ge (hbase i hi))
      refine ⟨gs.take start, hp, by simp, by simp [C, hem, hs], fun t => ?_⟩
      by_cases ht : t < n + (gs.take start).length
      · exact Or.inr ⟨t, ht, fun _ => rfl⟩
      · exact Or.inl ⟨false, fun x => List.getD_eq_default _ _ (by rw [W_len]; omega)⟩
    | succ k hk ih =>
      let i : Fin gs.length := ⟨k, by omega⟩
      obtain ⟨new, hgood, hpre, hlen, hr⟩ := ih (by omega)
      obtain ⟨new', he, hfree, hv⟩ := action i hk new hr
      have heq : gs.take (k+1) = gs.take k ++ [gs.get i] := by
        exact List.take_succ_eq_append_getElem (by omega)
      refine ⟨new', ?_, ?_, ?_, fun t => ?_⟩
      · rcases he with rfl | ⟨g, rfl, hop, h2⟩
        · exact hgood
        · intro q hq; rcases List.mem_append.mp hq with h | h
          · exact hgood q h
          · simp only [List.mem_singleton] at h; subst q; exact ⟨hop, h2.le⟩
      · rcases he with rfl | ⟨g,rfl,_⟩
        · exact hpre
        · exact hpre.trans ⟨[g], rfl⟩
      · by_cases hi : i ∈ S
        · have eq : S.filter (fun q => q.val < k+1) = insert i (S.filter fun q => q.val < k) := by
            ext q; simp only [Finset.mem_filter, Finset.mem_insert]; constructor
            · rintro ⟨h, hl⟩; by_cases e : q.val = k
              · exact Or.inl (Fin.ext e)
              · exact Or.inr ⟨h, by omega⟩
            · rintro (rfl | ⟨h, hl⟩)
              · exact ⟨hi, Nat.lt_succ_self k⟩
              · exact ⟨h, by omega⟩
          have hc : C (k+1) = C k + 1 := by unfold C; rw [eq, Finset.card_insert_of_notMem (by simp [i])]
          rw [hfree hi, hc]; omega
        · have eq : S.filter (fun q => q.val < k+1) = S.filter (fun q => q.val < k) := by
            ext q; simp only [Finset.mem_filter]; constructor
            · rintro ⟨h, hl⟩; refine ⟨h, ?_⟩; by_contra! hn; exact hi ((show q = i from Fin.ext (by dsimp [i]; omega)) ▸ h)
            · rintro ⟨h, hl⟩; exact ⟨h, by omega⟩
          have hc : C (k+1) = C k := congrArg Finset.card eq
          rw [hc]; rcases he with rfl | ⟨g,rfl,_⟩ <;> simp_all only [List.length_append,List.length_singleton] <;> omega
      · rw [heq]; by_cases ht : t = n + (gs.take k).length
        · exact rep_congr (fun x => by unfold wire; rw [W_val, if_pos ht]) hv
        · exact rep_congr (fun x => by unfold wire; rw [W_val, if_neg ht]) (rep_mono he _ (hr t))
  simpa [C] using aux gs.length hs (le_refl _)

lemma value_eq (gs : List Gate) (i : Fin gs.length) (x : Subtype P) :
    value (gs.take i.val) (gs.get i) x = wire gs (n+i.val) x := by
  have heq : gs.take (i.val+1) = gs.take i.val ++ [gs.get i] := List.take_succ_eq_append_getElem i.isLt
  have hlt : n+i.val < n + (gs.take (i.val+1)).length := by simp [List.length_take, Nat.min_eq_left (Nat.succ_le_of_lt i.isLt)]
  unfold wire
  rw [← take_stable gs (i.val+1) _ x.val hlt, heq, W_val, if_pos (by simp [Nat.min_eq_left i.isLt.le])]



lemma main : ∀ (n m : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (n + (h : ℕ)) :: r) →
    (∀ w : Fin m, ∃ x y : Fin n → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn y) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn y) = false) →
    ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ),
      (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates.take (h : ℕ) <+: gates' ∧
      gates'.length + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2
        ≤ gates.length ∧
      ∀ (w : Fin m) (x : Fin n → Bool),
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)
 := by
  classical
  intro n m gs out j h hb hj hu hh hin hw
  let P (x : Fin n → Bool) := (W gs x).getD (n+h.val) false = true
  let R := Finset.univ.filter (fun i : Fin gs.length => j < i ∧ n+j.val ∈ (gs.get i).inputs)
  let S := insert h (insert j R)
  have hval (x : Subtype P) : wire gs (n+h.val) x = true := x.property
  have earlier (i : Fin gs.length) {a : Fin gs.length} (ha : a < i) (x : Subtype P) :
      wire (gs.take i.val) (n+a.val) x = wire gs (n+a.val) x := by
    apply take_stable; simp [List.length_take, Nat.min_eq_left i.isLt.le]; exact ha
  have jval (x : Subtype P) : wire gs (n+j.val) x = false := by
    obtain ⟨r,hr⟩ := hin
    rw [← value_eq gs j x]; unfold value; rw [hj,hr]; change (!(wire (gs.take j.val) (n+h.val) x)) = false
    rw [earlier j hh, hval]; rfl
  have good (i : Fin gs.length) (hi : i ≠ j) : Good (gs.get i) := by
    obtain ⟨ho,hl⟩ := hb _ (List.get_mem gs i)
    exact ⟨ho.elim Or.inl (fun z => z.elim Or.inr (fun hn => False.elim (hi (hu i hn)))), hl⟩
  have hp : ∀ g ∈ gs.take h.val, Good g := by
    intro g hg
    obtain ⟨i,he⟩ := List.get_of_mem hg
    have il : i.val < h.val := lt_of_lt_of_le i.isLt (by simp)
    let a : Fin gs.length := ⟨i.val, by omega⟩
    have eq : gs.get a = g := by simpa [a, List.get_eq_getElem] using he
    rw [← eq]; apply good; intro e; have := congrArg Fin.val e; dsimp [a] at this; omega
  have base : ∀ i ∈ S, h.val ≤ i.val := by
    intro i hi; simp only [S, Finset.mem_insert, R, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases hi with rfl | rfl | ⟨lt,_⟩ <;> omega
  obtain ⟨new,hg,pre,budget,rep⟩ := compress (P := P) gs h.val h.isLt.le S hp base (by
    intro i _ new hr
    by_cases ih : i = h
    · subst i; exact ⟨new, Or.inl rfl, fun _ => rfl, Or.inl ⟨true, fun x => (value_eq gs h x).trans (hval x)⟩⟩
    by_cases ij : i = j
    · subst i; exact ⟨new, Or.inl rfl, fun _ => rfl, Or.inl ⟨false, fun x => (value_eq gs j x).trans (jval x)⟩⟩
    by_cases ir : i ∈ R
    · obtain ⟨lt,hm⟩ := (Finset.mem_filter.mp ir).2
      exact ⟨new, Or.inl rfl, fun _ => rfl, reader_free _ _ _ _ (good i ij) hm (fun x => (earlier i lt x).trans (jval x)) hr⟩
    · obtain ⟨new',he,hv⟩ := gate_rep _ new _ _ (good i ij).1 (good i ij).2 hr
      exact ⟨new',he,by simp [S, ih, ij, ir],hv⟩)
  have card : S.card = R.card + 2 := by
    have hR : h ∉ R := by simp [R, not_lt_of_ge hh.le]
    have jR : j ∉ R := by simp [R]
    simp [S, hR, jR, hh.ne, Nat.add_assoc]
  rw [card] at budget
  have idx (w : Fin m) : ∃ t, ∀ x : Subtype P, wire new t x = wire gs (out w) x := by
    rcases rep (out w) with ⟨c,hc⟩ | ⟨t,_,hv⟩
    · obtain ⟨x,y,hx,hy,ox,oy⟩ := hw w
      have eq := (hc ⟨x,hx⟩).trans (hc ⟨y,hy⟩).symm
      change Circuit.eval ⟨gs,out w⟩ (List.ofFn x) = Circuit.eval ⟨gs,out w⟩ (List.ofFn y) at eq
      simp [ox,oy] at eq
    · exact ⟨t,hv⟩
  choose f hf using idx
  exact ⟨new,f,hg,pre,by simpa [R, Nat.add_assoc] using budget,fun w x hx => hf w ⟨x,hx⟩⟩

end PEqualNP.Outside.L_meta_1517_aux.Reduction

namespace PEqualNP.Outside.L_meta_1517_aux.Counting
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

-- The value of wire `w` on input `x`.
def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

-- Collapsing one colour loses at most one colour.
theorem merge_card {n : ℕ} (A : Finset (Fin n)) (c : Fin n → Fin n) (x y : Fin n) :
    (A.image c).card ≤ (A.image fun p => if c p = y then x else c p).card + 1 := by
  classical
  have h1 : ((A.image c).erase y) ⊆ A.image fun p => if c p = y then x else c p := by
    intro v hv
    rw [Finset.mem_erase] at hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hv.2
    exact Finset.mem_image.2 ⟨p, hp, by simp [hv.1]⟩
  have h2 := Finset.card_le_card h1
  have h3 := Finset.pred_card_le_card_erase (s := A.image c) (a := y)
  omega

theorem two_list (l : List ℕ) (hl : l.length ≤ 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : l = [a, b] ∨ l = [b, a] := by
  match l, hl with
  | [], _ => simp at ha
  | [u], _ =>
    simp only [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | [u, v], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hab

theorem main (n : ℕ) (M A : Finset (Fin n)) (tau : Fin n → Fin n → Bool)
    (gates : List Gate)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hAM : A ⊆ M) (htau : ∀ p ∈ A, ∀ v ∈ M, tau p v = true ↔ v = p)
    (I : Finset (Fin gates.length))
    (hI : ∀ g : Fin gates.length, ((gates.get g).op = GateOp.or ∧
        val gates (n + (g : ℕ)) (fun v : Fin n => decide (v ∉ M)) = false ∧
        ∃ p ∈ A, ∃ p' ∈ A, p ≠ p' ∧
          val gates (n + (g : ℕ)) (tau p) = true ∧ val gates (n + (g : ℕ)) (tau p') = true) → g ∈ I) :
    ∀ k, k ≤ gates.length → ∃ c : Fin n → Fin n,
      A.card ≤ (A.image c).card + (I.filter fun g => g.val < k).card ∧
      ∀ w < n + k, val gates w (fun v : Fin n => decide (v ∉ M)) = false →
        ∀ p ∈ A, ∀ p' ∈ A, val gates w (tau p) = true → val gates w (tau p') = true →
          c p = c p' := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨id, by simp, ?_⟩
    intro w hw hz p hp p' hp' h1 h2
    have hw' : w < n := by omega
    rw [val_input gates _ w hw'] at hz h1 h2
    have hM : (⟨w, hw'⟩ : Fin n) ∈ M := by simpa using hz
    have e1 := (htau p hp _ hM).1 h1
    have e2 := (htau p' hp' _ hM).1 h2
    exact e1.symm.trans e2
  | succ k ih =>
    intro hk
    have hk' : k < gates.length := hk
    obtain ⟨c, hcard, hc⟩ := ih (Nat.le_of_lt hk')
    have hmono : (I.filter fun g => g.val < k).card ≤ (I.filter fun g => g.val < k + 1).card :=
      Finset.card_le_card (fun g hg => by
        rw [Finset.mem_filter] at hg ⊢; exact ⟨hg.1, by omega⟩)
    -- the old colouring works whenever the new wire needs nothing new
    have keep : (val gates (n + k) (fun v : Fin n => decide (v ∉ M)) = false →
        ∀ p ∈ A, ∀ p' ∈ A, val gates (n + k) (tau p) = true → val gates (n + k) (tau p') = true →
          c p = c p') →
        ∃ c : Fin n → Fin n,
          A.card ≤ (A.image c).card + (I.filter fun g => g.val < k + 1).card ∧
          ∀ w < n + (k + 1), val gates w (fun v : Fin n => decide (v ∉ M)) = false →
            ∀ p ∈ A, ∀ p' ∈ A, val gates w (tau p) = true → val gates w (tau p') = true →
              c p = c p' := by
      intro hnew
      refine ⟨c, by omega, ?_⟩
      intro w hw hz p hp p' hp' h1 h2
      by_cases hwk : w = n + k
      · subst hwk; exact hnew hz p hp p' hp' h1 h2
      · exact hc w (by omega) hz p hp p' hp' h1 h2
    have hlegk := hleg gates[k] (List.getElem_mem hk')
    rcases hlegk.1 with hop | hop
    · -- an AND gate false off M has an input false off M
      apply keep
      intro hz p hp p' hp' h1 h2
      have hz' : ¬ ∀ i ∈ gates[k].inputs, i < n + k ∧
          val gates i (fun v : Fin n => decide (v ∉ M)) = true := by
        intro h; rw [(val_and gates _ k hk' hop).2 h] at hz; exact absurd hz (by simp)
      push_neg at hz'
      obtain ⟨i, hi, hiz⟩ := hz'
      have a1 := (val_and gates (tau p) k hk' hop).1 h1 i hi
      have a2 := (val_and gates (tau p') k hk' hop).1 h2 i hi
      have hzi : val gates i (fun v : Fin n => decide (v ∉ M)) = false := by
        simpa using hiz a1.1
      exact hc i a1.1 hzi p hp p' hp' a1.2 a2.2
    · -- an OR gate
      by_cases hkI : (⟨k, hk'⟩ : Fin gates.length) ∈ I
      · -- a gate of `I`: merge two colours if needed
        by_cases hsame : val gates (n + k) (fun v : Fin n => decide (v ∉ M)) = false →
            ∀ p ∈ A, ∀ p' ∈ A, val gates (n + k) (tau p) = true →
              val gates (n + k) (tau p') = true → c p = c p'
        · exact keep hsame
        · push_neg at hsame
          obtain ⟨hz, a, ha, b, hb, hva, hvb, hne⟩ := hsame
          obtain ⟨ia, hia, hia1, hia2⟩ := (val_or gates (tau a) k hk' hop).1 hva
          obtain ⟨ib, hib, hib1, hib2⟩ := (val_or gates (tau b) k hk' hop).1 hvb
          have hzall : ∀ i ∈ gates[k].inputs, i < n + k →
              val gates i (fun v : Fin n => decide (v ∉ M)) = false := by
            intro i hi hlt
            by_contra hcon
            have : val gates i (fun v : Fin n => decide (v ∉ M)) = true := by simpa using hcon
            rw [(val_or gates _ k hk' hop).2 ⟨i, hi, hlt, this⟩] at hz
            exact absurd hz (by simp)
          have hiab : ia ≠ ib := by
            intro h; subst h
            exact hne (hc ia hia1 (hzall ia hia hia1) a ha b hb hia2 hib2)
          have hcount : (I.filter fun g => g.val < k).card + 1 ≤
              (I.filter fun g => g.val < k + 1).card := by
            have hsub : insert (⟨k, hk'⟩ : Fin gates.length) (I.filter fun g => g.val < k) ⊆
                I.filter fun g => g.val < k + 1 := by
              intro g hg
              rw [Finset.mem_insert] at hg
              rcases hg with rfl | hg
              · exact Finset.mem_filter.2 ⟨hkI, by simp⟩
              · rw [Finset.mem_filter] at hg ⊢; exact ⟨hg.1, by omega⟩
            have := Finset.card_le_card hsub
            rw [Finset.card_insert_of_notMem (by simp)] at this
            exact this
          refine ⟨fun p => if c p = c b then c a else c p, ?_, ?_⟩
          · have := merge_card A c (c a) (c b)
            omega
          · intro w hw hzw p hp p' hp' h1 h2
            by_cases hwk : w = n + k
            · subst hwk
              have col : ∀ q ∈ A, val gates (n + k) (tau q) = true → c q = c a ∨ c q = c b := by
                intro q hq hvq
                obtain ⟨iq, hiq, hiq1, hiq2⟩ := (val_or gates (tau q) k hk' hop).1 hvq
                rcases two_list _ hlegk.2 ia ib hia hib hiab with hl | hl
                · rw [hl] at hiq
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hiq
                  rcases hiq with rfl | rfl
                  · exact Or.inl (hc _ hiq1 (hzall _ hia hiq1) q hq a ha hiq2 hia2)
                  · exact Or.inr (hc _ hiq1 (hzall _ hib hiq1) q hq b hb hiq2 hib2)
                · rw [hl] at hiq
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hiq
                  rcases hiq with rfl | rfl
                  · exact Or.inr (hc _ hiq1 (hzall _ hib hiq1) q hq b hb hiq2 hib2)
                  · exact Or.inl (hc _ hiq1 (hzall _ hia hiq1) q hq a ha hiq2 hia2)
              have fin : ∀ q ∈ A, val gates (n + k) (tau q) = true →
                  (if c q = c b then c a else c q) = c a := by
                intro q hq hvq
                rcases col q hq hvq with h | h
                · rw [h]; split_ifs <;> rfl
                · rw [if_pos h]
              show (if c p = c b then c a else c p) = (if c p' = c b then c a else c p')
              rw [fin p hp h1, fin p' hp' h2]
            · have := hc w (by omega) hzw p hp p' hp' h1 h2
              show (if c p = c b then c a else c p) = (if c p' = c b then c a else c p')
              rw [this]
      · -- not in `I`: the gate does not join two different points
        apply keep
        intro hz p hp p' hp' h1 h2
        obtain ⟨ia, hia, hia1, hia2⟩ := (val_or gates (tau p) k hk' hop).1 h1
        obtain ⟨ib, hib, hib1, hib2⟩ := (val_or gates (tau p') k hk' hop).1 h2
        have hzall : ∀ i ∈ gates[k].inputs, i < n + k →
            val gates i (fun v : Fin n => decide (v ∉ M)) = false := by
          intro i hi hlt
          by_contra hcon
          have : val gates i (fun v : Fin n => decide (v ∉ M)) = true := by simpa using hcon
          rw [(val_or gates _ k hk' hop).2 ⟨i, hi, hlt, this⟩] at hz
          exact absurd hz (by simp)
        by_cases hiab : ia = ib
        · subst hiab
          exact hc ia hia1 (hzall ia hia hia1) p hp p' hp' hia2 hib2
        · by_contra hcne
          have hpp : p ≠ p' := fun h => hcne (by rw [h])
          apply hkI
          apply hI ⟨k, hk'⟩
          exact ⟨hop, hz, p, hp, p', hp', hpp, h1, h2⟩




lemma row_bound : ∀ (n : ℕ) (M A : Finset (Fin n)) (tau : Fin n → Fin n → Bool)
    (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    A ⊆ M →
    (∀ p ∈ A, ∀ v ∈ M, tau p v = true ↔ v = p) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false →
    (∀ p ∈ A, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (tau p)) = true) →
    ∀ I : Finset (Fin gates.length),
      (∀ g : Fin gates.length, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false ∧
        ∃ p ∈ A, ∃ p' ∈ A, p ≠ p' ∧
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (tau p)) = true ∧
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (tau p')) = true) → g ∈ I) →
      A.card ≤ 1 + I.card := by
  classical
  intro n M A tau gates o hleg hAM htau hout htrue I hI
  obtain ⟨c, hcard, hc⟩ := main n M A tau gates hleg hAM htau I hI gates.length le_rfl
  have hJ : (I.filter fun g => g.val < gates.length).card ≤ I.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rcases A.eq_empty_or_nonempty with hA | ⟨p0, hp0⟩
  · subst hA; simp
  · have ho : o < n + gates.length := by
      by_contra hcon
      have := htrue p0 hp0
      rw [eval_eq] at this
      have h2 := val_big gates (tau p0) o (by omega)
      rw [val] at h2
      rw [h2] at this
      exact absurd this (by simp)
    have hconst : ∀ p ∈ A, c p = c p0 := fun p hp =>
      hc o ho hout p hp p0 hp0 (htrue p hp) (htrue p0 hp0)
    have himg : (A.image c).card ≤ 1 := by
      apply Finset.card_le_one.2
      intro x hx y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
      rw [hconst p hp, hconst q hq]
    omega



lemma val_mono {n : ℕ} (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) (w : ℕ) :
    val gs w x = true → val gs w y = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · simpa only [val_input gs _ w hw] using hxy ⟨w,hw⟩
    by_cases hg : w < n + gs.length
    · have hi : w - n < gs.length := by omega
      have he : n + (w-n) = w := by omega
      rcases (legal gs[w-n] (List.getElem_mem hi)).1 with ha | ho
      · intro h
        have hs := (val_and gs x (w-n) hi ha).mp (by simpa only [he] using h)
        rw [← he]
        apply (val_and gs y (w-n) hi ha).mpr
        intro r hr
        obtain ⟨hlt,hit⟩ := hs r hr
        exact ⟨hlt, ih r (by omega) hit⟩
      · intro h
        obtain ⟨r,hr,hlt,hit⟩ := (val_or gs x (w-n) hi ho).mp (by simpa only [he] using h)
        rw [← he]
        exact (val_or gs y (w-n) hi ho).mpr ⟨r,hr,hlt,ih r (by omega) hit⟩
    · simp [val_big gs x w (by omega)]

def lines (t : Fin 13) : Finset (Fin 13) := {t,t+1,t+3,t+9}

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma geometry : (∀ t, (lines t).card = 4) ∧
    (∀ t u, t ≠ u → (lines t ∩ lines u).card ≤ 1) ∧
    (∀ t u, t ≠ u → (lines t \ lines u).Nonempty) ∧
    (∀ t v, ∃ s, v ∈ lines s ∧ (lines t \ lines s).Nonempty) := by
  decide +kernel

lemma final_bound :
∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ D : (Fin 13 → Bool) → Prop,
    (∀ x y : Fin 13 → Bool, D x → (∀ v : Fin 13, x v = true → y v = true) → D y) →
    (∀ t : Fin 13, D (fun v => decide (v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), D x →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ (Lam : Finset (Fin 13)) (B : Fin 13 → Fin 13 → Finset (Fin 13)),
    (∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ D (fun v => decide (v = p ∨ v ∈ B t p))) →
    (∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
      (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty))) →
    ∀ I : Finset (Fin gates.length), (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      3 * Lam.card + max (13 - Lam.card) I.card ≤ gates.length := by
  classical
  intro L hL D hup hd gates o legal computes Lam B hB hsep I hI
  have hLeq : L = lines := funext hL
  subst L
  obtain ⟨hcard,hthin,hdiff,hpoint⟩ := geometry
  let neg (t : Fin 13) (v : Fin 13) : Bool := decide (v ∉ lines t)
  let tau (t p v : Fin 13) : Bool := decide (v = p ∨ v ∈ B t p)
  have low (t : Fin 13) : val gates (o t) (neg t) = false := by
    change Circuit.eval ⟨gates,o t⟩ (List.ofFn (neg t)) = false
    rw [computes t _ (hd t)]
    simp [neg]
  have high (t : Fin 13) (ht : t ∈ Lam) (p : Fin 13) (hp : p ∈ lines t) :
      val gates (o t) (tau t p) = true := by
    change Circuit.eval ⟨gates,o t⟩ (List.ofFn (tau t p)) = true
    rw [computes t _ (hB t ht p hp).2]
    exact decide_eq_true ⟨p,hp,by simp [tau]⟩
  have spec (t : Fin 13) (ht : t ∈ Lam) (p : Fin 13) (hp : p ∈ lines t)
      (v : Fin 13) (hv : v ∈ lines t) : tau t p v = true ↔ v = p := by
    simp only [tau,decide_eq_true_eq]
    constructor
    · rintro (h|h)
      · exact h
      · have hi := Finset.mem_inter.mpr ⟨h,hv⟩
        rw [(hB t ht p hp).1] at hi
        exact False.elim (Finset.notMem_empty v hi)
    · exact Or.inl
  let pay (t : Fin 13) := Finset.univ.filter (fun g : Fin gates.length =>
    (gates.get g).op = GateOp.or ∧ val gates (13+g.val) (neg t) = false ∧
      ∃ p ∈ lines t, ∃ p' ∈ lines t, p ≠ p' ∧
        val gates (13+g.val) (tau t p) = true ∧ val gates (13+g.val) (tau t p') = true)
  have props (t : Fin 13) (g : Fin gates.length) (hg : g ∈ pay t) :
    (gates.get g).op = GateOp.or ∧ val gates (13+g.val) (neg t) = false ∧
      ∃ p ∈ lines t, ∃ p' ∈ lines t, p ≠ p' ∧
        val gates (13+g.val) (tau t p) = true ∧ val gates (13+g.val) (tau t p') = true :=
    (Finset.mem_filter.mp hg).2
  have many (t : Fin 13) (ht : t ∈ Lam) : 3 ≤ (pay t).card := by
    have hb := row_bound 13 (lines t) (lines t) (tau t) gates (o t) legal
      (Finset.Subset.refl _) (spec t ht) (low t) (high t ht) (pay t)
      (fun g hg => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hg⟩)
    rw [hcard t] at hb
    omega
  have pointing (t u : Fin 13) (hne : t ≠ u) (g : Fin gates.length)
      (ht : g ∈ pay t) (hu : g ∈ pay u) :
      ∃ p ∈ lines t \ lines u, (B t p ∩ lines u).Nonempty := by
    obtain ⟨p,hp,p',hp',hpp,hit,hit'⟩ := (props t g ht).2.2
    have out : ∃ p ∈ lines t, p ∉ lines u ∧ val gates (13+g.val) (tau t p) = true := by
      by_cases hpu : p ∈ lines u
      · have hp'u : p' ∉ lines u := by
          intro hp'u
          exact hpp (Finset.card_le_one.mp (hthin t u hne) p
            (Finset.mem_inter.mpr ⟨hp,hpu⟩) p' (Finset.mem_inter.mpr ⟨hp',hp'u⟩))
        exact ⟨p',hp',hp'u,hit'⟩
      · exact ⟨p,hp,hpu,hit⟩
    obtain ⟨r,hr,hru,hit⟩ := out
    refine ⟨r,Finset.mem_sdiff.mpr ⟨hr,hru⟩,?_⟩
    by_contra none
    have le (v : Fin 13) (hv : tau t r v = true) : neg u v = true := by
      apply decide_eq_true
      intro hvu
      rcases of_decide_eq_true hv with e | hb
      · subst v; exact hru hvu
      · exact none ⟨v,Finset.mem_inter.mpr ⟨hb,hvu⟩⟩
    have h := val_mono gates legal (tau t r) (neg u) le (13+g.val) hit
    rw [(props u g hu).2.1] at h
    contradiction
  have dis (t : Fin 13) (ht : t ∈ Lam) (u : Fin 13) (hu : u ∈ Lam) (hne : t ≠ u) :
      Disjoint (pay t) (pay u) := by
    apply Finset.disjoint_left.mpr
    intro g hgt hgu
    exact hsep t ht u hu hne ⟨pointing t u hne g hgt hgu,pointing u t hne.symm g hgu hgt⟩
  let paid := Lam.biUnion pay
  have paidmany : 3 * Lam.card ≤ paid.card := by
    dsimp [paid]
    rw [Finset.card_biUnion dis]
    calc
      3 * Lam.card = ∑ t ∈ Lam, 3 := by simp [Nat.mul_comm]
      _ ≤ ∑ t ∈ Lam, (pay t).card := Finset.sum_le_sum many
  have disI : Disjoint paid I := by
    apply Finset.disjoint_left.mpr
    intro g hg hi
    obtain ⟨t,ht,hgt⟩ := Finset.mem_biUnion.mp hg
    have op := (props t g hgt).1
    rw [hI g hi] at op
    contradiction
  have boundI : paid.card + I.card ≤ gates.length := by
    have h := Finset.card_le_univ (paid ∪ I)
    rw [Finset.card_union_of_disjoint disI,Fintype.card_fin] at h
    exact h
  have output_high (t s : Fin 13) (hne : t ≠ s) : val gates (o t) (neg s) = true := by
    obtain ⟨p,hp⟩ := hdiff t s hne
    obtain ⟨hpt,hps⟩ := Finset.mem_sdiff.mp hp
    change Circuit.eval ⟨gates,o t⟩ (List.ofFn (neg s)) = true
    rw [computes t _ (hd s)]
    exact decide_eq_true ⟨p,hpt,decide_eq_true hps⟩
  have bounds (t : Fin 13) : 13 ≤ o t ∧ o t < 13 + gates.length := by
    constructor
    · by_contra! small
      let v : Fin 13 := ⟨o t,small⟩
      obtain ⟨s,hvs,p,hp⟩ := hpoint t v
      have hit : val gates (o t) (neg s) = true := by
        change Circuit.eval ⟨gates,o t⟩ (List.ofFn (neg s)) = true
        rw [computes t _ (hd s)]
        exact decide_eq_true ⟨p,(Finset.mem_sdiff.mp hp).1,decide_eq_true (Finset.mem_sdiff.mp hp).2⟩
      rw [val_input gates _ _ small] at hit
      exact (of_decide_eq_true hit) hvs
    · have hall : D (fun _ => true) := hup (neg 0) (fun _ => true) (hd 0) (by simp)
      have hit : val gates (o t) (fun _ : Fin 13 => true) = true := by
        change Circuit.eval ⟨gates,o t⟩ (List.ofFn (fun _ : Fin 13 => true)) = true
        rw [computes t _ hall]
        exact decide_eq_true ⟨t,by simp [lines],rfl⟩
      by_contra! big
      rw [val_big gates _ _ big] at hit
      contradiction
  let idx (t : Fin 13) : Fin gates.length := ⟨o t-13,by have := bounds t;omega⟩
  have idxeq (t : Fin 13) : 13+(idx t).val = o t := by have := bounds t;dsimp [idx];omega
  have idxinj : Function.Injective idx := by
    intro t u heq
    by_contra hne
    have eqo : o t = o u := by rw [← idxeq t,← idxeq u,heq]
    have hit := output_high u t (Ne.symm hne)
    rw [← eqo,low t] at hit
    contradiction
  let free := (Finset.univ \ Lam).image idx
  have freecard : free.card = 13 - Lam.card := by
    dsimp [free]
    rw [Finset.card_image_of_injective _ idxinj,
      Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin]
  have disfree : Disjoint paid free := by
    apply Finset.disjoint_left.mpr
    intro g hg hf
    obtain ⟨t,ht,hgt⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hf
    have hut : u ≠ t := by intro h;subst u;exact (Finset.mem_sdiff.mp hu).2 ht
    have hit := output_high u t hut
    have zero := (props t (idx u) hgt).2.1
    rw [idxeq u] at zero
    rw [zero] at hit
    contradiction
  have boundfree : paid.card + free.card ≤ gates.length := by
    have h := Finset.card_le_univ (paid ∪ free)
    rw [Finset.card_union_of_disjoint disfree,Fintype.card_fin] at h
    exact h
  rw [freecard] at boundfree
  omega

end PEqualNP.Outside.L_meta_1517_aux.Counting


namespace PEqualNP.Outside.L_meta_1517_aux

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x


theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : t - l.length ≠ 0 := by omega
      simp [List.getElem?_cons, this]

theorem getD_false_lt {l : List Bool} {t : ℕ} (h : l.getD t false = true) : t < l.length := by
  by_contra h'
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
  simp at h


def Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩

theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y) : Le (W gs x) (W gs y) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : (W gs x).length = (W gs y).length := by simp [W_length, hl]
    rw [W_snoc, getD_snoc] at ht ⊢
    rw [← hlen]
    by_cases h1 : t < (W gs x).length
    · rw [if_pos h1] at ht ⊢; exact ih t ht
    · rw [if_neg h1] at ht ⊢
      by_cases h2 : t = (W gs x).length
      · rw [if_pos h2] at ht ⊢
        exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [if_neg h2] at ht; simp at ht

lemma W_prefix (pre tail : List Gate) (x : List Bool) :
    ∃ ys, W (pre ++ tail) x = W pre x ++ ys := by
  induction tail using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton tail g ih =>
    obtain ⟨ys, hys⟩ := ih
    refine ⟨ys ++ [g.op.eval (g.inputs.map fun i => (W (pre ++ tail) x).getD i false)], ?_⟩
    rw [← List.append_assoc, W_snoc, hys]
    simp [List.append_assoc]

lemma eval_prefix (gs : List Gate) (x : List Bool) (k w : ℕ)
    (hk : k ≤ gs.length) (hw : w < x.length + k) :
    Circuit.eval ⟨gs, w⟩ x = Circuit.eval ⟨gs.take k, w⟩ x := by
  change (W gs x).getD w false = (W (gs.take k) x).getD w false
  have hs : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
  obtain ⟨ys, hys⟩ := W_prefix (gs.take k) (gs.drop k) x
  rw [← hs] at hys
  rw [hys]
  apply List.getD_append
  simpa [W_length, List.length_take, Nat.min_eq_left hk] using hw

lemma prefix_no_not (gs : List Gate) (j : Fin gs.length)
    (basis : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (unique : ∀ i : Fin gs.length, (gs.get i).op = GateOp.not → i = j) :
    ∀ g ∈ gs.take j.val, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hg
  have hij : i < j.val := lt_of_lt_of_le hi (List.length_take_le _ _)
  have hig : i < gs.length := lt_trans hij j.isLt
  have heq : gs[i] = g := by simpa using hgi
  rcases basis g (List.mem_of_mem_take hg) with ha | ho | hn
  · exact Or.inl ha
  · exact Or.inr ho
  · have e := unique ⟨i, hig⟩ (by simpa [heq] using hn)
    have ev : i = j.val := congrArg Fin.val e
    omega

lemma protected_before_h (gs : List Gate) (h : Fin gs.length)
    (I : Finset (Fin gs.length))
    (hprotected : ∀ g ∈ I, ∀ T : Finset (Fin gs.length),
      (∀ i g' : Fin gs.length, (i = h ∨ i ∈ T) →
        13 + (g' : ℕ) ∈ (gs.get i).inputs → g' < i → g' ∈ T) → g ∈ T) :
    ∀ g ∈ I, g < h := by
  intro g hg
  let T := Finset.univ.filter (fun i : Fin gs.length => i < h)
  have hc : ∀ i g' : Fin gs.length, (i = h ∨ i ∈ T) →
      13 + (g' : ℕ) ∈ (gs.get i).inputs → g' < i → g' ∈ T := by
    intro i g' hi _ hgi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hi with rfl | hi
    · exact hgi
    · exact lt_trans hgi (Finset.mem_filter.mp hi).2
  exact (Finset.mem_filter.mp (hprotected g hg T hc)).2

lemma input_Le {n : ℕ} (x y : Fin n → Bool)
    (hxy : ∀ v, x v = true → y v = true) : Le (List.ofFn x) (List.ofFn y) := by
  intro i hi
  by_cases hin : i < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hin,
      Option.getD_some] at hi ⊢
    exact hxy ⟨i, hin⟩ hi
  · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hin] at hi

lemma earlier_wire_mono (gs : List Gate) (j h : Fin gs.length)
    (basis : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (unique : ∀ i : Fin gs.length, (gs.get i).op = GateOp.not → i = j)
    (hhj : h < j) (n : ℕ) (x y : Fin n → Bool)
    (hxy : ∀ v, x v = true → y v = true) :
    Circuit.eval ⟨gs, n + h.val⟩ (List.ofFn x) = true →
    Circuit.eval ⟨gs, n + h.val⟩ (List.ofFn y) = true := by
  rw [eval_prefix gs (List.ofFn x) j.val _ j.isLt.le (by simp; omega),
      eval_prefix gs (List.ofFn y) j.val _ j.isLt.le (by simp; omega)]
  exact W_mono (gs.take j.val) (prefix_no_not gs j basis unique)
    (List.ofFn x) (List.ofFn y) (by simp) (input_Le x y hxy) _

lemma protected_transfer (gs gs' : List Gate) (h : Fin gs.length)
    (hpref : gs.take h.val <+: gs') (I : Finset (Fin gs.length))
    (hbefore : ∀ g ∈ I, g < h)
    (hand : ∀ g ∈ I, (gs.get g).op = GateOp.and) :
    ∃ I' : Finset (Fin gs'.length), I'.card = I.card ∧
      ∀ g ∈ I', (gs'.get g).op = GateOp.and := by
  classical
  have hlen : h.val ≤ gs'.length := by
    have := hpref.length_le
    simpa [List.length_take, Nat.min_eq_left h.isLt.le] using this
  let emb : {g // g ∈ I} ↪ Fin gs'.length :=
    { toFun := fun g => ⟨g.val.val, lt_of_lt_of_le (hbefore g.val g.property) hlen⟩
      inj' := by intro a b hab; apply Subtype.ext; apply Fin.ext; exact congrArg (fun v : Fin gs'.length => v.val) hab }
  refine ⟨I.attach.map emb, by simp, ?_⟩
  intro g hg
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hg
  have hlt : a.val.val < (gs.take h.val).length := by
    simpa [List.length_take, Nat.min_eq_left h.isLt.le] using hbefore a.val a.property
  have heq := hpref.getElem hlt
  have ha := hand a.val a.property
  have hag : a.val.val < gs'.length := lt_of_lt_of_le (hbefore a.val a.property) hlen
  change (gs'[a.val.val]'hag).op = GateOp.and
  rw [← heq]
  simpa using ha

lemma line_nonempty (L : Fin 13 → Finset (Fin 13))
    (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) (t : Fin 13) :
    (L t).Nonempty := by
  exact ⟨t, by simp [hL]⟩

lemma count_transfer (gates gates' : List Gate) (k a : ℕ)
    (hcount : a ≤ gates'.length) (hremove : gates'.length + k + 2 ≤ gates.length) :
    k + 2 + a ≤ gates.length := by omega

lemma replace_not_true (pre post : List Gate) (ins : List ℕ) (x : List Bool)
    (hv : (ins.map (fun i => (W pre x).getD i false)).headD false = true) :
    W (pre ++ ⟨GateOp.not, ins⟩ :: post) x =
      W (pre ++ ⟨GateOp.or, []⟩ :: post) x := by
  simp only [W, List.foldl_append, List.foldl_cons]
  change post.foldl _ (W pre x ++ [!((ins.map (fun i => (W pre x).getD i false)).headD false)]) =
    post.foldl _ (W pre x ++ [false])
  rw [hv]
  rfl

lemma replace_not_true_wire (pre post : List Gate) (ins : List ℕ) (x : List Bool) (w : ℕ)
    (hv : (ins.map (fun i => (W pre x).getD i false)).headD false = true) :
    Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, w⟩ x =
      Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: post, w⟩ x := by
  change (W _ x).getD w false = (W _ x).getD w false
  rw [replace_not_true pre post ins x hv]

def ReductionStep : Prop :=
  ∀ (n m : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (n + (h : ℕ)) :: r) →
    (∀ w : Fin m, ∃ x y : Fin n → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn y) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn y) = false) →
    ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ),
      (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates.take (h : ℕ) <+: gates' ∧
      gates'.length + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2
        ≤ gates.length ∧
      ∀ (w : Fin m) (x : Fin n → Bool),
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)

def CountingStep : Prop :=
  ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ D : (Fin 13 → Bool) → Prop,
    (∀ x y : Fin 13 → Bool, D x → (∀ v : Fin 13, x v = true → y v = true) → D y) →
    (∀ t : Fin 13, D (fun v => decide (v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), D x →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ (Lam : Finset (Fin 13)) (B : Fin 13 → Fin 13 → Finset (Fin 13)),
    (∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ D (fun v => decide (v = p ∨ v ∈ B t p))) →
    (∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
      (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty))) →
    ∀ I : Finset (Fin gates.length), (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      3 * Lam.card + max (13 - Lam.card) I.card ≤ gates.length

lemma counting_proved : CountingStep := Counting.final_bound

lemma assemble (reduction : ReductionStep) (counting : CountingStep) :
  ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ t : Fin 13, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true) →
    ∀ (Lam : Finset (Fin 13)) (B : Fin 13 → Fin 13 → Finset (Fin 13)),
    (∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ v ∈ B t p))) = true) →
    (∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
      (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty))) →
    ∀ I : Finset (Fin gates.length),
      (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∀ T : Finset (Fin gates.length), (∀ i g' : Fin gates.length, (i = h ∨ i ∈ T) →
          13 + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → g ∈ T) →
      (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 + 3 * Lam.card + max (13 - Lam.card) I.card ≤ gates.length := by
  classical
  intro L hL gs o j h hb hnot huniq hhj hread hout hco Lam B hB hcross I hI
  have hb0 : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
    fun g hg => (hb g hg).1
  let D := fun x : Fin 13 → Bool => Circuit.eval ⟨gs, 13 + h.val⟩ (List.ofFn x) = true
  have hD : ∀ x y : Fin 13 → Bool, D x → (∀ v, x v = true → y v = true) → D y := by
    intro x y hx hxy
    exact earlier_wire_mono gs j h hb0 huniq hhj 13 x y hxy hx
  have hall : D (fun _ => true) :=
    hD _ _ (hco 0) (by simp)
  have hvar : ∀ w : Fin 13, ∃ x y : Fin 13 → Bool,
      Circuit.eval ⟨gs, 13 + h.val⟩ (List.ofFn x) = true ∧
      Circuit.eval ⟨gs, 13 + h.val⟩ (List.ofFn y) = true ∧
      Circuit.eval ⟨gs, o w⟩ (List.ofFn x) = true ∧
      Circuit.eval ⟨gs, o w⟩ (List.ofFn y) = false := by
    intro w
    refine ⟨(fun _ => true), (fun v => decide (v ∉ L w)), hall, hco w, ?_, ?_⟩
    · rw [hout]
      simp [hL]
    · rw [hout]
      simp
  obtain ⟨gs', o', hb', hpref, hsize, heval⟩ :=
    reduction 13 13 gs o j h hb hnot huniq hhj hread hvar
  obtain ⟨I', hcard, hand⟩ := protected_transfer gs gs' h hpref I
    (protected_before_h gs h I (fun g hg => (hI g hg).2))
    (fun g hg => (hI g hg).1)
  have hout' : ∀ (t : Fin 13) (x : Fin 13 → Bool), D x →
      Circuit.eval ⟨gs', o' t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true) := by
    intro t x hx
    rw [heval t x hx, hout t x]
  have hc := counting L hL D hD hco gs' o' hb' hout' Lam B hB hcross I' hand
  rw [hcard] at hc
  omega

end PEqualNP.Outside.L_meta_1517_aux

theorem PEqualNP.Outside.L_meta_1517 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ t : Fin 13, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true) →
    ∀ (Lam : Finset (Fin 13)) (B : Fin 13 → Fin 13 → Finset (Fin 13)),
    (∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ v ∈ B t p))) = true) →
    (∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
      (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty))) →
    ∀ I : Finset (Fin gates.length),
      (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∀ T : Finset (Fin gates.length), (∀ i g' : Fin gates.length, (i = h ∨ i ∈ T) →
          13 + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → g ∈ T) →
      (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 + 3 * Lam.card + max (13 - Lam.card) I.card ≤ gates.length :=
  PEqualNP.Outside.L_meta_1517_aux.assemble
    PEqualNP.Outside.L_meta_1517_aux.Reduction.main
    PEqualNP.Outside.L_meta_1517_aux.counting_proved
