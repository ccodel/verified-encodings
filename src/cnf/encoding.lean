/-
This file sets out definitions of what it means for a CNF formula to encode
a Boolean function. Encodings of non-Boolean functions may require different
definitions.

Authors: Cayden Codel, Marijn Heule, Jeremy Avigad
Carnegie Mellon University
-/

import logic.function.basic

import cnf.literal
import cnf.assignment
import cnf.clause
import cnf.cnf
import cnf.gensym
import basic

open clause cnf assignment gensym
open list function

variables {V : Type*} [decidable_eq V] --[fintype V] --[inhabited V]

-- Alternate definition is (fin n → bool) → bool [which is isomorphic to lists]
def constraint := list bool → bool

-- An encoding is a process that takes a list of vars and a gensym and produces a formula
-- A (possibly updated) gensym is also output
def enc_fn (V : Type*) := list (literal V) → gensym V → cnf V × gensym V

-- Disjointness condition between gensym and lists of literals
def disj (l : list (literal V)) (g : gensym V) := disjoint g.stock (clause.vars l)

theorem disj_left {l : list (literal V)} {g : gensym V} : 
  disj l g ↔ ∀ ⦃v⦄, v ∈ clause.vars l → v ∉ g.stock :=
set.disjoint_right

theorem disj_right {l : list (literal V)} {g : gensym V} : 
  disj l g ↔ ∀ ⦃v⦄, v ∈ g.stock → v ∉ clause.vars l :=
set.disjoint_left

theorem disj_perm {l : list (literal V)} {g : gensym V} {p : list (literal V) → list (literal V)}
  (hp : ∀ l, perm l (p l)) : disj l g ↔ disj (p l) g :=
begin
  unfold disj,
  rw clause.vars_perm (hp l)
end

namespace constraint

variables (c : constraint) (τ : assignment V) (l : list (literal V))

protected def eval := c (l.map (literal.eval τ))

theorem eval_eq_of_agree_on {τ₁ τ₂} :
  (agree_on τ₁ τ₂ (clause.vars l)) → c.eval τ₁ l = c.eval τ₂ l :=
begin
  -- TODO: feels like a more streamlined proof exists, rather than induction
  intro hagree_on,
  unfold constraint.eval,
  apply congr_arg,
  induction l with l₁ ls ih,
  { simp only [list.map_nil] },
  { simp [clause.vars] at hagree_on,
    simp [ih (agree_on_union_right hagree_on)],
    have := finset.mem_union_left (clause.vars ls) (finset.mem_singleton_self l₁.var),
    exact eval_eq_of_agree_on_of_var_mem hagree_on this }
end

/-! # append -/

-- TODO: why not unfolding with simp?
protected def append (c₁ c₂ : constraint) : constraint := λ l, c₁ l && c₂ l
instance : has_append constraint := ⟨constraint.append⟩

-- TODO better name?
def append_id : constraint := λ l, tt

@[simp] theorem append_id_left_id : append_id ++ c = c :=
begin
  apply funext_iff.mpr,
  intro l,
  simp [append, constraint.append, append_id]
end

@[simp] theorem append_id_right_id : c ++ append_id = c :=
begin
  apply funext_iff.mpr,
  intro l,
  simp [append, constraint.append, append_id]
end

instance : is_left_id constraint has_append.append append_id := ⟨ append_id_left_id ⟩
instance : is_right_id constraint has_append.append append_id := ⟨ append_id_right_id ⟩

theorem append_comm (c₁ c₂ : constraint) : c₁ ++ c₂ = c₂ ++ c₁ :=
begin
  apply funext_iff.mpr,
  intro l,
  simp [append, constraint.append, bool.band_comm]
end

theorem append_tt_iff {c₁ c₂ : constraint} {l : list bool} :
  (c₁ ++ c₂) l = tt ↔ c₁ l = tt ∧ c₂ l = tt :=
by simp [append, constraint.append]

theorem append_eval_tt_iff {c₁ c₂ : constraint} {l : list (literal V)} {τ : assignment V} :
  (c₁ ++ c₂).eval τ l = tt ↔ c₁.eval τ l = tt ∧ c₂.eval τ l = tt :=
by simp [constraint.eval, append_tt_iff]

/-! # fold -/

def fold (l : list constraint) := l.foldr append append_id 

@[simp] theorem fold_nil : fold [] = append_id := rfl
@[simp] theorem fold_singleton : fold [c] = c := by simp [fold]

@[simp] theorem fold_cons (l : list constraint) : fold (c :: l) = c ++ fold l :=
by simp [fold]

theorem fold_tt_iff_forall_tt {l : list constraint} {bs : list bool} :
  (fold l) bs = tt ↔ ∀ (c : constraint), c ∈ l → c bs = tt :=
begin
  induction l with c₁ cs ih,
  { simp [append_id] },
  { simp [ih, append, constraint.append] }
end

theorem fold_ff_iff_exists_ff {l : list constraint} {bs : list bool} :
  (fold l) bs = ff ↔ ∃ (c : constraint), c ∈ l ∧ c bs = ff :=
begin
  induction l with c₁ cs ih,
  { simp [append_id] },
  { simp [append, constraint.append],
    split,
    { rintros (h | h),
      { exact ⟨c₁, or.inl rfl, h⟩ },
      { rcases ih.mp h with ⟨c, hmem, hc⟩,
        exact ⟨c, or.inr hmem, hc⟩ } },
    { rintros ⟨c, (rfl | h), hc⟩,
      { exact or.inl hc },
      { exact or.inr (ih.mpr ⟨c, h, hc⟩) } } }
end

/-! # check -/

-- TODO: A better name exists, but basically a check on the input (can be a length check)
-- In the case where the function returns false, returns the all false constraint
def len_check (c : constraint) (f : nat → bool) : constraint := λ l, if f (length l) then c l else ff

theorem check_append (c₁ c₂ : constraint) (f : nat → bool) :
  len_check (c₁ ++ c₂) f = len_check c₁ f ++ len_check c₂ f :=
begin
  apply funext_iff.mpr,
  intro l,
  cases hf : f (length l);
  simp [len_check, append, constraint.append, hf]
end

end constraint

namespace encoding

theorem disj_of_disj_cons {lit : literal V} {l : list (literal V)} {g} :
  disj (lit :: l) g → disj l g :=
begin
  intro h,
  unfold disj at h,
  simp [clause.vars] at h,
  rw set.insert_eq at h,
  exact (set.disjoint_union_right.mp h).2
end

theorem disj_fresh_of_disj {l : list (literal V)} {g} : disj l g → disj l g.fresh.2 :=
set.disjoint_of_subset_left (fresh_stock_subset g)

theorem disj_fresh_cons {lit : literal V} {l : list (literal V)} {g} : disj (lit :: l) g →
  disj l g.fresh.2 :=
assume h, disj_fresh_of_disj (disj_of_disj_cons h)

variables (c : constraint) (enc : enc_fn V) (τ : assignment V) (F : cnf V) (l : list (literal V))

protected def append (enc₁ enc₂ : enc_fn V) : enc_fn V := λ l g,
  let (F₁, g₁) := enc₁ l g in
  let (F₂, g₂) := enc₂ l g₁ in
  (F₁ ++ F₂, g₂)

instance : has_append (enc_fn V) := ⟨encoding.append⟩

@[ext] theorem append_ext (enc₁ enc₂ : enc_fn V) : ∀ l g,
  (enc₁ ++ enc₂) l g = ((enc₁ l g).1 ++ (enc₂ l (enc₁ l g).2).1, (enc₂ l (enc₁ l g).2).2) :=
begin
  intros l g,
  simp [append, encoding.append],
  rw [prod.ext_self (enc₁ l g), append._match_2, 
    prod.ext_self (enc₂ l (enc₁ l g).2), append._match_1],
  refl
end

def append_id : enc_fn V := λ l g, ⟨[], g⟩

@[simp] theorem append_id_left_id : append_id ++ enc = enc :=
begin
  apply funext_iff.mpr, intro l,
  apply funext_iff.mpr, intro g,
  simp [append_ext, append_id]
end

@[simp] theorem append_id_right_id : enc ++ append_id = enc :=
begin
  apply funext_iff.mpr, intro l,
  apply funext_iff.mpr, intro g,
  simp [append_ext, append_id]
end

instance : is_left_id (enc_fn V) has_append.append append_id := ⟨ append_id_left_id ⟩
instance : is_right_id (enc_fn V) has_append.append append_id := ⟨ append_id_right_id ⟩

/-! # fold -/

def fold (l : list (enc_fn V)) := l.foldr append append_id

@[simp] theorem fold_nil : fold ([] : list (enc_fn V)) = append_id := rfl
@[simp] theorem fold_singleton : fold [enc] = enc := by simp [fold]

@[simp] theorem fold_cons (l : list (enc_fn V)) : fold (enc :: l) = enc ++ fold l :=
by simp [fold]

-- TODO translate later?
--theorem fold_tt_iff_forall_tt {l : list constraint} {bs : list bool} :
--  (fold l) bs = tt ↔ ∀ (c : constraint), c ∈ l → c bs = tt :=

/-! # encodes -/

/- A CNF formula encodes a Boolean function on a base list of input literals
   if an extending assignment on those literals can be found to satisfy the formula. -/
def formula_encodes := ∀ (τ : assignment V), (c.eval τ l = tt) ↔ ∃ σ, F.eval σ = tt ∧ agree_on τ σ (clause.vars l)

/- An encoding function encodes a Boolean constraint if, when given a disjoint
   gensym, the encodes judgment is satisfied -/
def encodes_base := ∀ ⦃l : list (literal V)⦄ ⦃g⦄, disj l g → formula_encodes c (enc l g).1 l

/-! # Well-behavedness -/
-- TODO: name?

/- Encoding functions are well-behaved if the only variables they generate are from the
   input literals and from the gensym, and no more. The gensym is also updated accordingly. -/
def is_wb := ∀ ⦃l : list (literal V)⦄ ⦃g⦄, disj l g →
    (enc l g).2.stock ⊆ g.stock ∧ 
    ↑(enc l g).1.vars ⊆ ↑(clause.vars l) ∪ (g.stock \ (enc l g).2.stock)

theorem not_mem_form_of_is_wb {enc : enc_fn V} (henc : is_wb enc) :
  ∀ ⦃l : list (literal V)⦄ ⦃g⦄, disj l g →
  ∀ ⦃v : V⦄, v ∉ ↑(clause.vars l) ∪ g.stock → v ∉ (enc l g).1.vars :=
begin
  intros l g hdis v hnmem hv,
  rcases (set.mem_union _ _ _).mp (((henc hdis).2) hv) with (h | h),
  { exact hnmem (set.mem_union_left _ h) },
  { exact hnmem (set.mem_union_right _ h.1 ) }
end

-- TODO: not as strong as it could be?
theorem mem_vars_or_stock_of_is_wb_of_mem {enc : enc_fn V} (henc : is_wb enc) :
  ∀ ⦃l : list (literal V)⦄ ⦃g⦄, disj l g →
  ∀ ⦃v : V⦄, v ∈ (enc l g).1.vars → v ∈ clause.vars l ∨ v ∈ g.stock :=
begin
  intros l g hdis v hmem,
  rcases (set.mem_union _ _ _).mp (((henc hdis).2) hmem) with (h | h),
  { exact or.inl h },
  { exact or.inr h.1 }
end

theorem disj_of_is_wb {enc : enc_fn V} (henc : is_wb enc) :
  ∀ ⦃l : list (literal V)⦄  ⦃g⦄, disj l g →
  disjoint ↑(enc l g).1.vars (enc l g).2.stock :=
begin
  intros l g hdis,
  apply set.disjoint_left.mpr,
  intros v hv,
  rcases (set.mem_union _ _ _).mp ((henc hdis).2 hv) with (hv | hv),
  { exact not_mem_subset (disj_left.mp hdis hv) (henc hdis).1 },
  { exact hv.2 }
end

theorem disj_left_of_is_wb {enc : enc_fn V} (henc : is_wb enc) :
  ∀ ⦃l : list (literal V)⦄ ⦃g⦄, disj l g →
  ∀ ⦃v⦄, v ∈ (enc l g).1.vars → v ∉ (enc l g).2.stock :=
assume l g hdis, set.disjoint_left.mp (disj_of_is_wb henc hdis)

theorem disj_right_of_is_wb {enc : enc_fn V} (henc : is_wb enc) :
  ∀ ⦃l : list (literal V)⦄ ⦃g⦄, disj l g →
  ∀ ⦃v⦄, v ∈ (enc l g).2.stock → v ∉ (enc l g).1.vars :=
assume l g hdis, set.disjoint_right.mp (disj_of_is_wb henc hdis)

theorem append_is_wb {e₁ e₂ : enc_fn V} :
  is_wb e₁ → is_wb e₂ → is_wb (e₁ ++ e₂) :=
begin
  intros h₁ h₂ l g hdis,
  have h₃ := (h₁ hdis).1,
  have h₄ : disj l (e₁ l g).2, from set.disjoint_of_subset_left h₃ hdis,
  split,
  { simp [append_ext],
    exact subset_trans (h₂ h₄).1 h₃ },
  { simp [append_ext],
    have hl : ↑(e₁ l g).1.vars ⊆ ↑(clause.vars l) ∪ (g.stock \ (e₂ l (e₁ l g).2).2.stock),
    { exact subset_trans (h₁ hdis).2 (set.union_subset_union_right ↑(clause.vars l) 
        (set.diff_subset_diff_right (h₂ h₄).1)) },
    have hr : ↑(e₂ l (e₁ l g).2).1.vars ⊆ ↑(clause.vars l) ∪ (g.stock \ (e₂ l (e₁ l g).2).2.stock),
    { exact subset_trans (h₂ h₄).2 (set.union_subset_union_right ↑(clause.vars l) (set.diff_subset_diff_left h₃)) },
    exact ⟨hl, hr⟩ }
end

theorem subset_union_of_wb {enc : enc_fn V} :
  is_wb enc → ∀ ⦃l : list (literal V)⦄ ⦃g⦄, disj l g → 
  ↑((enc l g).1.vars) ⊆ ↑(clause.vars l) ∪ g.stock :=
begin
  intros h l g hdis v hv,
  have := (h hdis).2,
  rcases (set.mem_union _ _ _).mp (this hv) with (hv | hv),
  { exact set.mem_union_left _ hv },
  { exact set.mem_union_right _ ((set.mem_diff _).mp hv).1 }
end

def encodes := encodes_base c enc ∧ is_wb enc

theorem encodes_base_of_encodes : encodes c enc → encodes_base c enc :=
assume h l g hdis, h.1 hdis

theorem is_wb_of_encodes : encodes c enc → is_wb enc :=
assume h l g hdis, h.2 hdis

theorem append_id_is_wb : is_wb (append_id : enc_fn V) :=
assume l g hdis, by simp [append_id]

@[simp] theorem encodes_id : encodes constraint.append_id (append_id : enc_fn V) :=
begin
  split,
  { intros l g hdis τ,
    simp [constraint.append_id, constraint.eval, append_id],
    use τ },
  { exact append_id_is_wb }
end

theorem encodes_append {c₁ c₂ : constraint} {enc₁ enc₂ : enc_fn V} :
  encodes c₁ enc₁ → encodes c₂ enc₂ → encodes (c₁ ++ c₂) (enc₁ ++ enc₂) :=
begin
  rintros h₁ h₂, split,
  { intros l g hdis τ, split,
    { intro he,
      rcases (h₁.1 hdis τ).mp (constraint.append_tt_iff.mp he).1 with ⟨σ₁, he₁, hs₁⟩,
      have := set.disjoint_of_subset_left (h₁.2 hdis).1 hdis,
      rcases (h₂.1 this τ).mp (constraint.append_tt_iff.mp he).2 with ⟨σ₂, he₂, hs₂⟩,
      use aite (enc₁ l g).1.vars σ₁ σ₂,
      split,
      { rw eval_tt_iff_forall_clause_eval_tt,
        intros c hc,
        simp [append_ext] at hc,
        rcases hc with (hc | hc),
        { revert hc c,
          rw ← eval_tt_iff_forall_clause_eval_tt,
          rw cnf.eval_eq_of_agree_on (aite_agree_on (enc₁ l g).1.vars σ₁ σ₂),
          exact he₁ },
        { have := eval_tt_iff_forall_clause_eval_tt.mp he₂ _ hc,
          rcases eval_tt_iff_exists_literal_eval_tt.mp this with ⟨lit, hmem, hlit⟩,
          rw eval_tt_iff_exists_literal_eval_tt,
          use [lit, hmem],
          by_cases hm : lit.var ∈ (enc₁ l g).1.vars,
          { rcases h₁.2 hdis with ⟨hf₁, hf₂⟩,
            rcases set.mem_or_mem_of_mem_union (hf₂ hm) with (h | h),
            { -- Say eval under σ₁ = τ = σ₂
              rw aite_pos_lit hm,
              rw ← eval_eq_of_agree_on_of_var_mem hs₁ h,
              rw eval_eq_of_agree_on_of_var_mem hs₂ h,
              exact hlit },
            { -- Derive contradiction that lit is not a member of e₁'s fresh vars
              rcases (h₂.2 (set.disjoint_of_subset_left (h₁.2 hdis).1 hdis)) with ⟨_, hf₄⟩,
              have := mem_vars_iff_exists_mem_clause_and_mem.mpr ⟨c, hc, mem_vars_of_mem hmem⟩,
              rcases set.mem_or_mem_of_mem_union (hf₄ this) with (hl | hl),
              { rw aite_pos_lit hm,
                rw ← eval_eq_of_agree_on_of_var_mem hs₁ hl,
                rw eval_eq_of_agree_on_of_var_mem hs₂ hl,
                exact hlit },
              { rw set.mem_diff at hl h,
                exact absurd hl.1 h.2 } } },
          { rw aite_neg_lit hm, exact hlit } } },
      { exact aite_agree_on_of_agree_on_of_agree_on hs₁ hs₂ _ } },
    { rintros ⟨σ, he, hs⟩,
      rw constraint.append_eval_tt_iff,
      simp [append_ext, cnf.eval_append] at he,
      split,
      { apply (h₁.1 hdis τ).mpr,
        use [σ, he.1, hs] },
      { apply (h₂.1 (set.disjoint_of_subset_left (h₁.2 hdis).1 hdis) τ).mpr,
        use [σ, he.2, hs], } } },
  { exact append_is_wb h₁.2 h₂.2 }
end

/-! # check -/

def len_check (f : nat → bool) : enc_fn V := 
  λ l g, if f (length l) then enc l g else ⟨[[]], g⟩

theorem check_encodes_of_encodes (f : nat → bool) : 
  encodes c enc → encodes (constraint.len_check c f) (len_check enc f) :=
begin
  intro henc,
  split,
  { intros l g hdis τ,
    cases hf : f (length l);
    simp [len_check, hf, constraint.eval, constraint.len_check],
    { exact ((henc.1 hdis) τ) } },
  { intros l g hdis,
    cases hf : f (length l);
    simp [len_check, constraint.len_check, hf],
    exact (henc.2 hdis) }
end

/-! # misc -/

theorem encodes_fold_fold {α : Type*} {f : α → constraint} {g : α → enc_fn V} {l : list α} :
  (∀ ⦃a : α⦄, a ∈ l → encodes (f a) (g a)) → encodes (constraint.fold (l.map f)) (fold (l.map g)) :=
begin
  induction l with a as ih,
  { simp },
  { intro h,
    simp,
    apply encodes_append,
    { exact h (mem_cons_self a as) },
    { apply ih,
      intros b hb,
      exact h (mem_cons_of_mem _ hb) } }
end

theorem filter_by_idx_is_wb (p : nat → Prop) [decidable_pred p] {enc : enc_fn V} :
  is_wb enc → is_wb (enc ∘ filter_by_idx p) :=
begin
  intros h₁ l g hdis,
  have h₂ := set.disjoint_of_subset_right (clause.vars_subset_of_subset (filter_by_idx_subset p l)) hdis,
  simp,
  split,
  { exact (h₁ h₂).1 },
  { have h₃ := (h₁ h₂).2,
    intros v hv,
    rw set.mem_union,
    rcases (set.mem_union _ _ _).mp (h₃ hv) with (hv | hv),
    { exact or.inl ((clause.vars_subset_of_subset (filter_by_idx_subset p l)) hv) },
    { exact set.mem_union_right _ hv } }
end

theorem filter_by_idx_encodes_of_encodes (p : nat → Prop) [decidable_pred p] 
  {c : constraint} {enc : enc_fn V} :
  encodes c enc → encodes (c ∘ (filter_by_idx p)) (enc ∘ (filter_by_idx p)) :=
begin
  intro h,
  split,
  { intros l g hdis τ,
    simp [constraint.eval],
    rw map_filter_by_idx,
    have hw := filter_by_idx_subset p l,
    have hdis' := set.disjoint_of_subset_right (clause.vars_subset_of_subset hw) hdis,
    split,
    { intro hc,
      rcases (h.1 hdis' τ).mp hc with ⟨σ, heval, hs⟩,
      use aite (cnf.vars (enc (filter_by_idx p l) g).1) σ τ,
      split,
      { rw cnf.eval_eq_of_agree_on (aite_agree_on _ _ _), exact heval },
      { intros v hv,
        by_cases hvmem : v ∈ (enc (filter_by_idx p l) g).1.vars,
        { rw aite_pos hvmem,
          rcases (set.mem_union _ _ _).mp ((h.2 hdis').2 hvmem) with (hv₂ | hv₂),
          { exact hs _ hv₂ },
          { have h₉ := set.disjoint_left.mp hdis hv₂.1,
            exact absurd hv h₉ } },
        { rw aite_neg hvmem } } },
    { rintros ⟨σ, heval, hs⟩,
      apply (h.1 hdis' τ).mpr,
      use [σ, heval],
      exact agree_on_subset (clause.vars_subset_of_subset hw) hs } },
  { exact filter_by_idx_is_wb p h.2 }
end

/-! # direct encoding -/

/- Definition of a direct encoding -/
def dir_enc (f : list (literal V) → cnf V) : enc_fn V := λ l g, (f l, g)

end encoding