/-
This file contains the definition of a Boolean (disjunctive) clause (as in CNF).
This particular implementation has clauses as lists.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon Univeristy
-/

import cnf.literal
import basic
import data.list.basic
import data.list.perm

/- (Disjunctive) clauses are lists of literals, joined by logical ORs. -/
def clause := list literal

namespace clause

open literal
open list

instance : inhabited clause := ⟨[default literal]⟩

instance has_decidable_eq [s : decidable_eq literal] : decidable_eq clause
| []        []        := is_true rfl
| (a :: as) []        := is_false (λ h, list.no_confusion h)
| []        (b :: bs) := is_false (λ h, list.no_confusion h)
| (a :: as) (b :: bs) :=
  match s a b with
  | is_true hab  :=
    match has_decidable_eq as bs with
    | is_true habs  := is_true (eq.subst hab (eq.subst habs rfl))
    | is_false nabs := is_false (λ h, list.no_confusion h (λ _ habs, absurd habs nabs))
    end
  | is_false nab := is_false (λ h, list.no_confusion h (λ hab _, absurd hab nab))
  end

instance : has_mem literal clause := ⟨list.mem⟩
instance : has_emptyc clause := ⟨list.nil⟩
instance : has_union clause := ⟨list.union⟩
instance : has_inter clause := ⟨list.inter⟩
instance : has_singleton literal clause := ⟨λ l, [l]⟩ 
instance : has_insert literal clause := ⟨list.insert⟩
instance : has_append clause := ⟨list.append⟩
instance : has_subset clause := ⟨list.subset⟩

/- The clause represents a disjunction, so we evaluate literals until tt is found -/
def eval (α : assignment) (c : clause) : bool :=
  c.foldr (λ l b, b || (l.eval α)) ff

@[simp] theorem eval_nil (α : assignment) : eval α [] = ff := rfl

@[simp] theorem eval_singleton (α : assignment) (l : literal) : eval α [l] = literal.eval α l :=
by simp [eval]

theorem eval_cons (α : assignment) (l : literal) (c : clause) : eval α (l :: c) = (literal.eval α l) || (eval α c) :=
by simp [eval, bool.bor_comm]

-- Can be cleaned up
theorem eval_tt_iff_exists_literal_tt {α : assignment} {c : clause} : eval α c = tt ↔ ∃ l ∈ c, literal.eval α l = tt :=
begin
  induction c with l ls ih,
  { simp }, split,
  { simp [eval_cons],
    rintros (hl | hls),
    { use l, simp [hl] },
    { rcases ih.mp hls with ⟨l, hl, hlt⟩,
      use l,
      simp [hl, hlt] } },
  { rintros ⟨l2, hl2, hlt⟩,
    rcases eq_or_ne_mem_of_mem hl2 with rfl | ⟨hne, hls⟩,
    { simp [eval_cons, hlt] },
    { simp [eval_cons], 
      have : ∃ (l3 : literal) (H : l3 ∈ ls), literal.eval α l3 = tt,  -- Shorten this?
        { use l2, simp [hls, hlt] },
      simp [ih.mpr this] } }
end

-- Can be cleaned up
theorem eval_ff_iff_literals_ff {α : assignment} {c : clause} : eval α c = ff ↔ ∀ l ∈ c, literal.eval α l = ff :=
begin
  induction c with l ls ih,
  { simp }, split,
  { simp [eval_cons],
    intros hl hls,
    exact and.intro hl (ih.mp hls) },
  { intro hl,
    simp [eval_cons],
    simp [hl l (mem_cons_self l ls)],
    have : ∀ (l2 : literal), l2 ∈ ls → literal.eval α l2 = ff,
      { intros l2 hl2,
        have : l2 ∈ l :: ls, from mem_cons_of_mem l hl2,
        exact hl l2 this },
    exact ih.mpr this }
end

-- For any list of natural numbers and assignment, a false clause can be computed
def falsify : assignment → list nat → clause
| α []        := []
| α (n :: ns) := if α n then Neg n :: falsify α ns else Pos n :: falsify α ns

-- And here's a companion function that might have fewer uses
-- NOTE: The empty case doesn't work, but the empty case is trivial anyways...
def truthify : assignment → list nat → clause
| α []        := []
| α (n :: ns) := if α n then Pos n :: truthify α ns else Neg n :: truthify α ns

@[simp] lemma falsify_nil (α : assignment) : falsify α [] = [] := rfl
@[simp] lemma truthify_nil (α : assignment) : truthify α [] = [] := rfl

theorem eval_ff_of_falsify (α : assignment) (ns : list nat) : eval α (falsify α ns) = ff :=
begin
  induction ns with m ms ih,
  { simp [falsify] },
  { unfold falsify,
    by_cases α m = tt,
    { simp [h, eval_cons, literal.eval, ih] },
    { simp at h,
      simp [h, eval_cons, literal.eval, ih] } }
end

theorem eval_tt_of_truthify (α : assignment) {ns : list nat} (hns : ns ≠ []) : eval α (truthify α ns) = tt :=
begin
  induction ns with m ms ih,
  { contradiction },
  { by_cases α m = tt,
    { simp [truthify, h, literal.eval, eval_cons] },
    { simp at h, simp [truthify, h, literal.eval, eval_cons] } }
end

theorem map_var_falsify_eq_list (α : assignment) (ns : list nat) : map var (falsify α ns) = ns :=
begin
  induction ns with m ms ih,
  { simp },
  { rcases bool_by_cases (α m) with h | h;
    { simp [falsify, h, ih, var] } }
end

theorem map_var_truthify_eq_list (α : assignment) (ns : list nat) : map var (truthify α ns) = ns :=
begin
  induction ns with m ms ih,
  { simp },
  { rcases bool_by_cases (α m) with h | h;
    { simp [truthify, h, ih, var] } }
end

theorem flip_truthify_eq_falsify (α : assignment) (ns : list nat) :
  map flip (truthify α ns) = falsify α ns :=
begin
  induction ns with m ms ih,
  { simp [truthify, falsify] },
  { simp [truthify, falsify],
    by_cases α m = tt,
    { simp [h, literal.eval, ih, literal.flip] },
    { simp at h, simp [h, literal.eval, ih, literal.flip] } }
end

theorem eval_erase_of_mem (α : assignment) {l : literal} {c : clause} (h : l ∈ c) : eval α c = (literal.eval α l) || (eval α (c.erase l)) :=
begin
  induction c with d ds ih,
  { exact absurd h (not_mem_nil _) },
  rcases classical.em (l = d) with rfl | hne,
  { simp [erase_cons_head, eval_cons] },
  { simp only [eval_cons, erase_cons_tail ds (ne.symm hne), ih (mem_of_ne_of_mem hne h), ← bool.bor_assoc, bool.bor_comm] }
end

theorem eval_erase_of_not_mem {α : assignment} {l : literal} {c : clause} (h : l ∉ c) : eval α c = eval α (c.erase l) :=
by simp [erase_of_not_mem h]

/-! ### Similarity of clauses -/
-- Because clauses are literals joined by ORs, and OR is commutative, similar clauses evaluate identically

theorem eval_sim (α : assignment) {c₁ : clause} : ∀ (c₂ : clause), c₁ ~ c₂ → eval α c₁ = eval α c₂ :=
begin
  induction c₁ with l c ih; intros c₂ h,
  { simp [perm.nil_eq h] },
  { simp only [ih (c₂.erase l) (cons_perm_iff_perm_erase.mp h).2, 
      eval_cons, (eval_erase_of_mem α ((perm.mem_iff h).mp (mem_cons_self l c))).symm] }
end

-- A potentially helpful lemma stating that if a clause mapped to vars is similar to a list,
-- then for any nat, there is a literal whose variable is that nat
-- NOTE: Another version of this can be proven with no duplicates in either the clause or the list, via ↔
lemma all_mem_of_sim_var {ns : list nat} : ∀ (c : clause), c.map var ~ ns → ∀ n ∈ ns, ∃ l ∈ c, literal.var l = n :=
begin
  intros c hsim n hn,
  rcases exists_of_mem_map ((perm.mem_iff hsim).mpr hn) with ⟨a, ⟨ha1, ha2⟩⟩,
  use a, exact and.intro ha1 ha2
end

-- TODO cleanup with split and cases
lemma erase_map_var_eq_map_var_erase {c : clause} : 
  ∀ (n : nat), n ∈ c.map var → ∃ (l : literal), l ∈ c ∧ l.var = n ∧ (c.map var).erase n ~ (c.erase l).map var :=
begin
  induction c with l ls ih; intros n hn,
  { rw map_nil at hn, exact absurd hn (not_mem_nil _) },
  by_cases l.var = n,
  { use l, split, { exact mem_cons_self l ls },
    split, { exact h },
    simp only [mem_cons_self, erase_cons_head, map_cons, h, perm.refl] },
  rcases mem_map.mp hn with ⟨a, ⟨hal, han⟩⟩,
  have hcase := h,
  rw ← han at h,
  have laneq : l ≠ a, from ne_of_apply_ne (λ (l : literal), l.var) h,
  have hals : a ∈ ls, from mem_of_ne_of_mem laneq.symm hal,
  have hamap : a.var ∈ map var ls, from mem_map_of_mem var hals,
  rw han at hamap,
  have ihred := ih n hamap,
  rcases ihred with ⟨l2, ⟨hl2ls, ⟨hl2n, hl2sim⟩⟩⟩,
  use l2,
  have hl2lls : l2 ∈ l :: ls, from mem_cons_of_mem l hl2ls,
  by_cases l2 = l,
  { rw h at hl2n, exact absurd hl2n hcase },
  rw erase_cons_tail ls (ne.symm h),
  rw map_cons,
  rw map_cons,
  rw erase_cons_tail (map var ls) hcase,
  exact and.intro hl2lls (and.intro (hl2n) (perm.cons l.var hl2sim))
end

theorem map_var_sim_of_var_of_mem {n : nat} {l : literal} {c : clause} : 
  l ∈ c → l.var = n → (map var c).erase n ~ map var (c.erase l) :=
begin
  induction c with d ds ih,
  { intro h, exact absurd h (not_mem_nil _) },
  { intros hds hn,
    by_cases l = d,
    { rw h at hn, simp [erase_cons, h, hn] },
    { have : l ∈ ds, from mem_of_ne_of_mem h hds,
      have ihred := ih (mem_of_ne_of_mem h hds) hn,
      simp [ihred, erase_cons, (ne.symm h)],
      by_cases (d.var = l.var),
      { simp [h, hn],
        have : var l ∈ map var ds, from mem_map_of_mem var this,
        rw hn at this,
        exact perm.trans (perm_cons_erase this) (perm.cons n ihred) },
      { simp [ne_of_ne_of_eq h hn, ihred] } } }
end

/-! ### Counting -/
/- Counts the number of literals that evaluate to true in the clause, under some assignment -/
def count_tt (α : assignment) (c : clause) : nat :=
  c.countp (λ l, l.eval α = tt)

/- Counts the number of literals that evaluate to false in the clause, under some assignment -/
def count_ff (α : assignment) (c : clause) : nat :=
  c.countp (λ l, l.eval α = ff)

/- Counts the number of positive literals in the clause -/
def count_pos (c : clause) : nat :=
  c.countp (λ l, literal.is_pos l = tt)

/- Counts the number of negative literals in the clause -/
def count_neg (c : clause) : nat :=
  c.countp (λ l, literal.is_neg l = tt)

@[simp] lemma count_tt_nil (α : assignment) : count_tt α [] = 0 := by dec_trivial
@[simp] lemma count_ff_nil (α : assignment) : count_ff α [] = 0 := by dec_trivial
@[simp] lemma count_pos_nil : count_pos [] = 0 := by dec_trivial
@[simp] lemma count_neg_nil : count_neg [] = 0 := by dec_trivial

lemma count_tt_cons (α : assignment) (l : literal) (c : clause) : count_tt α (l :: c) = bool.to_nat (l.eval α) + count_tt α c :=
begin
  unfold count_tt, cases classical.em (l.eval α = tt),
  { simp [countp_cons_of_pos (λ l, literal.eval α l = tt) c h, h, bool.to_nat, add_comm] },
  { simp [countp_cons_of_neg (λ l, literal.eval α l = tt) c h, h, bool.to_nat, bool_eq_false h] }
end

lemma count_ff_cons (α : assignment) (l : literal) (c : clause) : count_ff α (l :: c) = bool.to_nat (!l.eval α) + count_ff α c :=
begin
  unfold count_ff, cases classical.em (l.eval α = ff),
  { simp [countp_cons_of_pos (λ l, literal.eval α l = ff) c h, h, bool.to_nat, add_comm] },
  { simp [countp_cons_of_neg (λ l, literal.eval α l = ff) c h, bool.to_nat, eq_tt_of_not_eq_ff h] }
end

lemma count_pos_cons (l : literal) (c : clause) : count_pos (l :: c) = bool.to_nat (l.is_pos) + count_pos c :=
begin
  unfold count_pos, cases classical.em (l.is_pos = tt),
  { simp [countp_cons_of_pos (λ l, literal.is_pos l = tt) c h, h, bool.to_nat, add_comm] },
  { simp [countp_cons_of_neg (λ l, literal.is_pos l = tt) c h, bool.to_nat, bool_eq_false h] }
end

lemma count_neg_cons (l : literal) (c : clause) : count_neg (l :: c) = bool.to_nat (l.is_neg) + count_neg c :=
begin
  unfold count_neg, cases classical.em (l.is_neg = tt),
  { simp [countp_cons_of_pos (λ l, literal.is_neg l = tt) c h, h, bool.to_nat, add_comm] },
  { simp [countp_cons_of_neg (λ l, literal.is_neg l = tt) c h, bool.to_nat, bool_eq_false h] }
end

lemma count_tt_singleton (α : assignment) (l : literal) : count_tt α [l] = bool.to_nat (l.eval α) := by simp [count_tt_cons α l []]
lemma count_ff_singleton (α : assignment) (l : literal) : count_ff α [l] = bool.to_nat (!l.eval α) := by simp [count_ff_cons α l []]
lemma count_pos_singleton (l : literal) : count_pos [l] = bool.to_nat l.is_pos := by simp [count_pos_cons l []]
lemma count_neg_singleton (l : literal) : count_neg [l] = bool.to_nat l.is_neg := by simp [count_neg_cons l []]

lemma count_pos_subset {c₁ c₂ : clause} : c₁ <+ c₂ → count_pos c₁ ≤ count_pos c₂ := 
  assume h, by simp [count_pos, countp_le_of_sublist (λ l, literal.is_pos l = tt) h]

lemma count_neg_subset {c₁ c₂ : clause} : c₁ <+ c₂ → count_neg c₁ ≤ count_neg c₂ :=
  assume h, by simp [count_neg, countp_le_of_sublist (λ l, literal.is_neg l = tt) h]

lemma exists_pos_of_odd_count_pos {c : clause} : c.count_pos.bodd → ∃ (n : nat), Pos n ∈ c :=
begin
  induction c with cl cls ih, --; intro h,
  { simp [nat.bodd_zero] },
  { intro h,
    rcases exists_nat_of_lit cl with ⟨n, (rfl | rfl)⟩,
    { use n, exact mem_cons_self (Pos n) cls },
    { simp [count_pos_cons, is_pos, bool.to_nat] at h,
      rcases ih h with ⟨n2, h2⟩, use n2, simp [h2] } }
end

lemma count_tt_le_length (α : assignment) (c : clause) : count_tt α c ≤ length c :=
by simp [count_tt, countp_eq_length_filter, length_filter]

-- Handling the erase case
lemma count_pos_erase_of_mem {c : clause} {l : literal} (h : l ∈ c) : count_pos c = count_pos (c.erase l) + count_pos [l] :=
begin
  induction c with d ds ih,
  { exact absurd h ( not_mem_nil _) },
  rcases eq_or_ne_mem_of_mem h with rfl | ⟨hne, h2⟩,
  { simp [erase_cons_head, count_pos_cons, add_comm] },
  { rw erase_cons_tail ds (ne.symm hne),
    have : count_pos [l] ≤ count_pos ds, from count_pos_subset (singleton_sublist.mpr h2),
    simp [count_pos_singleton] at this,
    simp [count_pos_cons, ih h2, add_assoc] }
end

lemma count_neg_erase_of_mem {c : clause} {l : literal} (h : l ∈ c) : count_neg c = count_neg (c.erase l) + count_neg [l] :=
begin
  induction c with d ds ih,
  { exact absurd h ( not_mem_nil _) },
  rcases eq_or_ne_mem_of_mem h with rfl | ⟨hne, h2⟩,
  { simp [erase_cons_head, count_neg_cons, add_comm] },
  { rw erase_cons_tail ds (ne.symm hne),
    have : count_neg [l] ≤ count_neg ds, from count_neg_subset (singleton_sublist.mpr h2),
    simp [count_neg_singleton] at this,
    simp [count_neg_cons, ih h2, add_assoc] }
end

/-! ## Parity reasoning for evaluation -/

-- This can probably be vastly shortened with a restatement or the introduction with a few supporting lemmas
theorem eval_tt_of_neq_counts {α : assignment} {ns : list nat} (hnil : ns ≠ nil) (hns : ns.nodup) :
  ∀ (c : clause), map var c = ns → count_tt α (map Pos ns) ≠ count_neg c → eval α c = tt :=
begin
  induction ns with m ms ih,
  { contradiction },
  by_cases ms = nil,
  { rw h,
    intros c hc hcount,
    rcases exists_of_map_singleton hc with ⟨l, rfl, hl⟩,
    rcases pos_or_neg_of_var_eq_nat hl with rfl | rfl,
    { simp [literal.eval],
      by_cases α m = tt,
      { exact h },
      { simp at h,
        simp [count_tt_singleton, count_neg_singleton, is_neg, bool.to_nat, h, literal.eval] at hcount,
        exfalso, exact hcount } },
    { simp [literal.eval],
      by_cases α m = tt,
      { simp [count_tt_singleton, count_neg_singleton, is_neg, bool.to_nat, h, literal.eval] at hcount, 
        exfalso, exact hcount },
      { simp at h, exact h } } },
  { intros c hc hcount,
    rcases exists_cons_of_map_cons hc with ⟨l, ls, rfl, hl, hls⟩,
    have ihred := ih h (nodup_of_nodup_cons hns) ls hls,
    rw eval_cons,
    by_cases literal.eval α l = tt,
    { simp [h] },
    { simp at h,
      rcases pos_or_neg_of_var_eq_nat hl with rfl | rfl,
      { simp [h],
        simp [count_tt_cons, count_neg_cons, h, bool.to_nat, is_neg] at hcount,
        exact ihred hcount },
      { simp [count_tt_cons, count_neg_cons, h, bool.to_nat, is_neg] at hcount,
        have : literal.eval α (Pos m) = tt, 
        { have h3 := literal.eval_flip α (Pos m),
          simp [literal.flip] at h3,
          rw h at h3,
          simp at h3,
          exact h3 },
        simp [this] at hcount,
        simp [ihred hcount] } } }
end

-- Corollary of the above wrt parity reasoning
theorem eval_tt_of_opposite_parity {α : assignment} {ns : list nat} {c : clause} (hnil : ns ≠ nil) (hns : ns.nodup) : 
  map var c = ns → nat.bodd (count_tt α (map Pos ns)) ≠ nat.bodd (count_neg c) → eval α c = tt :=
begin
  intros hc hcount,
  exact eval_tt_of_neq_counts hnil hns c hc (ne_of_apply_ne nat.bodd hcount)
end

-- Falsify negates those literals that, if positive, are true
theorem count_tt_pos_eq_count_neg_falsify (α : assignment) (ns : list nat) : 
  count_tt α (map Pos ns) = count_neg (falsify α ns) :=
begin
  induction ns with m ms ih,
  { simp },
  { rcases bool_by_cases (α m) with h | h;
    { simp [count_tt_cons, h, falsify, count_neg_cons, literal.eval, is_neg, bool.to_nat, ih] } }
end

end clause