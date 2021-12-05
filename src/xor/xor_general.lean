/-

  This file concerns the definition and translation of XOR gates into CNF, and
  proves that this translation is correct.

  Variables are general.

  Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
  Carnegie Mellon University

-/

import data.bool
import data.list.basic

import cnf.literal_general
import cnf.clause_general
import cnf.cnf_general
import cnf.explode_general
import basic

universe u

-- Represents the parametric type of the variable stored in the literal
variables {V : Type u} [decidable_eq V] [inhabited V]

/- An n-literal XOR gate is a list of those literals -/
def xor_gate (V : Type u) := list (literal V)

namespace xor_gate

open list
open literal
open clause
open cnf
open explode

instance : has_append (xor_gate V) := ⟨list.append⟩

-- The conversion of the XOR gate to a clause is a nice way of sweeping
-- uner the rug that the two definitions are actually identical
-- TODO canonical way of saying we want the nil/empty clause?
def to_clause (g : xor_gate V) : clause V :=
  g.foldr (λ l c, l :: c) []

-- Kinda cheesy
lemma gate_eq_clause (g : xor_gate V) : g = g.to_clause :=
by simp [to_clause]

/- Evaluates the XOR gate under an assignment -/
def eval (α : assignment V) (g : xor_gate V) : bool :=
  g.foldr (λ l b, b ⊕ l.eval α) ff

@[simp] theorem eval_nil (α : assignment V) : eval α [] = ff := rfl

protected theorem eval_cons (α : assignment V) (l : literal V) (g : xor_gate V) : 
  eval α (l :: g) = bxor (literal.eval α l) (eval α g) :=
by simp [eval, foldr_cons, bool.bxor_comm]

theorem eval_concat (α : assignment V) (g₁ g₂ : xor_gate V) : eval α (g₁ ++ g₂) = bxor (eval α g₁) (eval α g₂) :=
begin
  induction g₁ with l ls ih,
  { simp },
  { simp [xor_gate.eval_cons, ih] }
end

theorem eval_cons_conjunctive (α : assignment V) (l : literal V) (g : xor_gate V) : 
  eval α (l :: g) = (literal.eval α l || eval α g) && (!(literal.eval α l) || !(eval α g)) :=
by simp only [← bxor_conjunctive, xor_gate.eval_cons α l g]

theorem eval_cons_disjunctive (α : assignment V) (l : literal V) (g : xor_gate V) :
  eval α (l :: g) = (!(literal.eval α l) && eval α g) || (literal.eval α l && !(eval α g)) :=
by simp only [← bxor_disjunctive, xor_gate.eval_cons α l g]

/- Using a recursive evaluation function is sometimes more convenient -/
def eval_rec (α : assignment V) : xor_gate V → bool
| []        := ff
| (l :: ls) := l.eval α ⊕ eval_rec ls

/- To use the recursive definition, we need to prove that the two functions are equivalent -/
theorem eval_and_eval_rec_equiv (α : assignment V) (g : xor_gate V) : 
  eval α g = eval_rec α g :=
begin
  induction g with l ls ih,
  { simp [eval_rec, eval] },
  { simp [eval_rec, ih, xor_gate.eval_cons] },
end

/- The XOR gate evaluates to true if an odd number of literals evaluates to true -/
theorem xor_odd_eval_tt (α : assignment V) (g : xor_gate V) : 
  g.eval α = nat.bodd (g.countp (λ l, l.eval α = tt)) :=
begin
  induction g with l ls ih,
  { simp },
  { cases h : (l.eval α);
    { simp [xor_gate.eval_cons, h, ih] } }
end

-- This is a shortcut of the above that uses gate.to_clause instead
-- NOTE that the to_clause is essentially an identity operation, but if sets/permuations are
-- used instead, the proof may grow more complex
theorem xor_odd_eval_tt2 (α : assignment V) (g : xor_gate V) :
  g.eval α = nat.bodd (g.to_clause.count_tt α) :=
begin
  induction g with l ls ih,
  { simp [to_clause] },
  { cases h : (l.eval α);
    { rw ← gate_eq_clause ls at ih,
      simp [to_clause, xor_gate.eval_cons, count_tt_cons, bool.to_nat, h, ih] } }
end

/-! ## Naive encoding, simple version -/

-- The naive encoding returns a formula with all possible clauses with an even number of negated literals
-- Because we are using natural numbers, i.e. positive literals, we want an even number of negative literals
def to_xor_cnf : list V → cnf V
| []        := [[]]
| (v :: vs) := (explode vs).map (λ c, cond (nat.bodd c.count_neg = ff) ((Pos v) :: c) ((Neg v) :: c))

@[simp] theorem to_xor_cnf_nil : to_xor_cnf ([] : list V) = [[]] := rfl

theorem mem_explode_of_mem_to_xor :
  ∀ {l : list V}, ∀ {c : clause V}, c ∈ to_xor_cnf l → c ∈ explode l
| []        := by simp [to_xor_cnf]
| (v :: vs) := begin
  simp [to_xor_cnf, mem_map, mem_append],
  intros c hc,
  have : (Pos v).var = v ∧ (Neg v).var = v, simp [var], -- Make into literal lemma?
  cases h : (c.count_neg.bodd);
  { simp [h, this],
    apply mem_explode_cons_of_mem_explode_of_lit,
    exact hc }
end

theorem length_to_xor_cnf : 
  ∀ {l : list V}, l ≠ [] → length (to_xor_cnf l) = 2^(length l - 1)
| []        := by { contradiction }
| (n :: ns) := by simp [to_xor_cnf, length_explode]

theorem length_to_xor_cnf_pos : ∀ {l : list V}, length (to_xor_cnf l) > 0
| []        := by { simp [to_xor_cnf] }
| (n :: ns) := by simp [length_to_xor_cnf]

theorem exists_mem_to_xor_cnf : ∀ (l : list V),
  ∃ (c : clause V), c ∈ to_xor_cnf l
| [] := by simp [to_xor_cnf]
| (v :: vs) := exists_mem_of_length_pos length_to_xor_cnf_pos

theorem map_var_eq_of_mem_to_xor : 
  ∀ {l : list V}, ∀ {c : clause V}, c ∈ to_xor_cnf l → c.map var = l
| []        := by simp [to_xor_cnf]
| (n :: ns) := begin
  simp [to_xor_cnf],
  intros c hc,
  cases h : c.count_neg.bodd;
  { simp [h, var, map_var_eq_of_mem_explode hc] }
end

theorem mem_to_xor_of_even_negation_of_map_var_eq : 
  ∀ {l : list V}, ∀ {c : clause V}, c.map var = l → (nat.bodd c.count_neg = ff) → c ∈ to_xor_cnf l
| []        := by simp [to_xor_cnf]
| (n :: ns) := begin
  intros c hc,
  rcases exists_cons_of_map_cons hc with ⟨l, ls, rfl, hl, hls⟩,
  rcases pos_or_neg_of_var_eq_nat hl with rfl | rfl;
  { simp [count_neg_cons, is_neg, bool.to_nat, to_xor_cnf],
    intro hcount, use ls,
    simp [hcount, mem_explode_of_map_var_eq hls] }
end

theorem even_negation_of_mem_to_xor_of_map_var_eq : 
  ∀ {l : list V}, ∀ {c : clause V}, c.map var = l → c ∈ to_xor_cnf l → nat.bodd c.count_neg = ff
| []        := by simp
| (n :: ns) := begin
  intros c hc hxor,
  simp [to_xor_cnf] at hxor,
  rcases hxor with ⟨a, ha, hacons⟩,
  rcases exists_cons_of_map_cons hc with ⟨l, ls, rfl, hl, hls⟩,
  cases h : a.count_neg.bodd;
  { simp [h] at hacons,
    simp [← hacons, count_neg_cons, is_neg, bool.to_nat, h] },
end

theorem even_negation_iff_mem_to_xor 
  {l : list V} {c : clause V} (hc : c.map var = l) : c ∈ to_xor_cnf l ↔ nat.bodd c.count_neg = ff :=
⟨even_negation_of_mem_to_xor_of_map_var_eq hc,
  mem_to_xor_of_even_negation_of_map_var_eq hc⟩

theorem not_mem_to_xor_cnf_of_odd_negation_of_map_var_eq 
  {l : list V} {c : clause V} : c.map var = l → (nat.bodd c.count_neg = tt) → c ∉ to_xor_cnf l :=
begin
  intros hc hcount,
  by_contradiction,
  exact absurd_bool hcount (even_negation_of_mem_to_xor_of_map_var_eq hc h)
end

-- TODO move the c.map var assumption into the ns list nat portion since the above need it too
theorem odd_negation_of_not_mem_nat_to_xor_of_map_var_eq 
  {l : list V} {c : clause V} (hc : c.map var = l) : c ∉ to_xor_cnf l → nat.bodd c.count_neg = tt :=
begin
  contrapose,
  simp,
  exact (even_negation_iff_mem_to_xor hc).mpr
end

theorem odd_negation_iff_not_mem_to_xor 
  {l : list V} {c : clause V} (hc : c.map var = l) : c ∉ to_xor_cnf l ↔ nat.bodd c.count_neg = tt :=
⟨odd_negation_of_not_mem_nat_to_xor_of_map_var_eq hc, 
  not_mem_to_xor_cnf_of_odd_negation_of_map_var_eq hc⟩

-- We prove that the naive encoding is equivalent to an XOR gate of all positive literals
lemma exists_to_xor_cnf_of_xor {l : list V} 
  : (∃ (α : assignment V), eval α (map Pos l) = tt) → 
     ∃ (α₂ : assignment V), cnf.eval α₂ (to_xor_cnf l) = tt :=
begin
  rintros ⟨α, ha⟩,
  rw xor_odd_eval_tt2 α (map Pos l) at ha,
  rw ← gate_eq_clause (map Pos l) at ha,
  use α,
  apply eval_tt_iff_forall_clause_eval_tt.mpr,
  intros c hc,
  have mve := map_var_eq_of_mem_to_xor hc,
  have neq := neq_of_ff_of_tt ha ((even_negation_iff_mem_to_xor mve).mp hc),
  exact eval_tt_of_opposite_parity mve neq
end

lemma exists_xor_of_to_xor_cnf {l : list V}
  : (∃ (α : assignment V), cnf.eval α (to_xor_cnf l) = tt) → 
    ∃ (α₂ : assignment V), eval α₂ (map Pos l) = tt :=
begin
  rintros ⟨α, ha⟩,
  use α,
  rw xor_odd_eval_tt2 α (map Pos l),
  rw ← gate_eq_clause (map Pos l),
  rcases exists_mem_to_xor_cnf l with ⟨c, hc⟩,
  have := eval_tt_iff_forall_clause_eval_tt.mp ha,
  by_contradiction,
  simp at h,
  rw count_tt_pos_eq_count_neg_falsify at h,
  have falsify_mem := mem_to_xor_of_even_negation_of_map_var_eq 
    (map_var_falsify_eq_list α l) h,
  have falsify_eval := falsify_eval_ff α l,
  have := this (falsify α l) falsify_mem,
  exact absurd_bool this falsify_eval
end

theorem equisatisfiable_to_xor_cnf (l : list V) :
  assignment.equisatisfiable (λ α, cnf.eval α (to_xor_cnf l)) (λ α, xor_gate.eval α (map Pos l)) :=
begin
  split,
  { rintros ⟨a, ha⟩,
    simp at ha,
    have : ∃ α, cnf.eval α (to_xor_cnf l) = tt,
    { use [a, ha] },
    exact exists_xor_of_to_xor_cnf this },
  { rintros ⟨a, ha⟩,
    simp at ha,
    have : ∃ α, xor_gate.eval α (map Pos l) = tt,
    {use [a, ha] },
    exact exists_to_xor_cnf_of_xor this }
end

/-! # More complex encoding -/

/-
The above encoding assumed that the list of interest were only positive literals.
Here, we generalize and prove the encoding valid with general lists of literals.
The encoding is generated by counting "flips" between clauses rather than negations of literals.
-/
def xor_cnf : list (literal V) → cnf V
| []        := [[]]
| (l :: ls) := (explode (map var ls)).map (λ c, cond (nat.bodd (c.count_flips (ls)) = ff) (l :: c) (l.flip :: c))

@[simp] theorem xor_cnf_nil : xor_cnf ([] : list (literal V)) = [[]] := rfl

@[simp] theorem xor_cnf_singleton (l : literal V) : xor_cnf [l] = [[l]] :=
by simp [xor_cnf]

theorem mem_explode_of_mem_xor_cnf : ∀ {l : list (literal V)} {c : clause V}, 
  c ∈ xor_cnf l → c ∈ explode (map var l)
| []        := by simp [xor_cnf]
| (l :: ls) := begin
  simp [xor_cnf, explode],
  intros c hc,
  cases l,
  { cases h : (nat.bodd (c.count_flips ls)),
    { use c, simp [h, hc, var, literal.flip] },
    { right, use c, simp [h, hc, var, literal.flip] } },
  { cases h : (nat.bodd (c.count_flips ls)), 
    { right, use c, simp [h, hc, var, literal.flip] },
    { use c, simp [h, hc, var, literal.flip] } }
end

theorem length_xor_cnf : ∀ {l : list (literal V)}, 
  l ≠ [] → length (xor_cnf l) = 2^(length l - 1)
| []        := by { contradiction }
| (l :: ls) := by simp [xor_cnf, length_explode]

theorem length_xor_cnf_pos : ∀ {l : list (literal V)}, length (xor_cnf l) > 0
| []        := by { simp [xor_cnf] }
| (l :: ls) := by simp [length_xor_cnf]

theorem exists_mem_xor_cnf : ∀ (l : list (literal V)),
  ∃ (c : clause V), c ∈ xor_cnf l
| []        := by simp [xor_cnf]
| (v :: vs) := exists_mem_of_length_pos length_xor_cnf_pos

theorem map_var_eq_of_mem_xor_cnf {l : list (literal V)} : ∀ {c : clause V}, 
  c ∈ xor_cnf l → map var c = map var l :=
begin
  induction l with v vs ih,
  { simp [xor_cnf] },
  { simp [xor_cnf],
    intros c hc,
    cases h : (nat.bodd (c.count_flips vs));
    { simp [h, map_var_eq_of_mem_explode hc, flip_var_eq v] } }
end

-- TODO choose to add back in lemmas on flips for literal
theorem mem_xor_cnf_of_even_flips_of_map_var_eq : ∀ {l : list (literal V)}, 
  ∀ {c : clause V}, map var c = map var l → 
  (nat.bodd (c.count_flips l) = ff) → c ∈ xor_cnf l
| []        := by simp [xor_cnf]
| (l :: ls) := begin
  simp [xor_cnf, map_cons],
  intros c hc hcount,
  rcases exists_cons_of_map_cons hc with ⟨d, ds, rfl, hd, hds⟩,
  use ds,
  cases htf : (nat.bodd (count_flips ds ls)),
  { by_cases l.flip = d,
    { have : d.flip = l, from congr_arg literal.flip h ▸ flip_flip l,
      simp [count_flips, this] at hcount,
      exact absurd_bool hcount htf },
    { simp [htf, mem_explode_of_map_var_eq hds, hd],
      rcases eq_or_flip_eq_of_var_eq hd with rfl | h₂,
      { refl },
      { have : d = l.flip, from congr_arg literal.flip h₂ ▸ (flip_flip d).symm, 
        exact absurd this (ne.symm h) } } },
  { by_cases l.flip = d,
    { simp [htf, mem_explode_of_map_var_eq hds, hd, h], },
    { have := function.injective.ne flip_injective h,
      rw flip_flip at this,
      simp [count_flips, ne.symm this] at hcount,
      exact absurd_bool htf hcount } }
end

theorem even_flips_of_mem_xor_cnf_of_map_var_eq : ∀ {l : list (literal V)}, 
  ∀ {c : clause V}, c.map var = map var l → 
  c ∈ xor_cnf l → nat.bodd (count_flips c l) = ff
| []        := by simp [xor_cnf]
| (l :: ls) := begin
  intros c hc hxor,
  simp [xor_cnf] at hxor,
  rcases hxor with ⟨a, ha, hacons⟩,
  rcases exists_cons_of_map_cons hc with ⟨c, cs, rfl, hc2, hcs⟩,
  cases h : (nat.bodd (count_flips a ls));
  { simp [h] at hacons,
    simp [← hacons, count_flips, is_neg, bool.to_nat, h, flip_flip _, flip_ne] }
end

theorem even_flips_iff_mem_xor_cnf {l : list (literal V)} {c : clause V} 
  (hc : c.map var = map var l) :
  nat.bodd (count_flips c l) = ff ↔ c ∈ xor_cnf l :=
⟨mem_xor_cnf_of_even_flips_of_map_var_eq hc, even_flips_of_mem_xor_cnf_of_map_var_eq hc⟩

theorem not_mem_xor_cnf_of_odd_flips_of_map_var_eq {l : list (literal V)} 
  {c : clause V} : map var c = map var l → 
  (nat.bodd (count_flips c l)) = tt → c ∉ xor_cnf l :=
begin
  intros hc hcount,
  by_contradiction,
  exact absurd_bool hcount ((even_flips_iff_mem_xor_cnf hc).mpr h)
end

theorem odd_flips_of_not_mem_xor_cnf_of_map_var_eq {l : list (literal V)} 
  {c : clause V} : map var c = map var l → 
  c ∉ xor_cnf l → (nat.bodd (count_flips c l)) = tt :=
begin
  intro hc,
  contrapose,
  simp,
  exact (even_flips_iff_mem_xor_cnf hc).mp
end

theorem odd_flips_iff_not_mem_xor_cnf {l : list (literal V)} 
  {c : clause V} (hc : map var c = map var l) :
  nat.bodd (count_flips c l) = tt ↔ c ∉ xor_cnf l :=
⟨not_mem_xor_cnf_of_odd_flips_of_map_var_eq hc, odd_flips_of_not_mem_xor_cnf_of_map_var_eq hc⟩

lemma exists_xor_cnf_of_xor {l : list (literal V)} :
  (∃ (α : assignment V), eval α l = tt) → 
  ∃ (α₂ : assignment V), cnf.eval α₂ (xor_cnf l) = tt :=
begin
  rintros ⟨α, ha⟩,
  rw xor_odd_eval_tt2 α l at ha,
  rw ← gate_eq_clause l at ha,
  use α,
  apply eval_tt_iff_forall_clause_eval_tt.mpr,
  intros c hc,
  have mve := map_var_eq_of_mem_xor_cnf hc,
  have neqodd := neq_of_ff_of_tt ha ((even_flips_iff_mem_xor_cnf mve).mpr hc),
  have neq := ne_of_apply_ne nat.bodd neqodd,
  rw count_flips_comm at neq,
  exact eval_tt_of_neq_flips c mve.symm neq
end

lemma exists_xor_of_xor_cnf {l : list (literal V)} :
  (∃ (α : assignment V), cnf.eval α (xor_cnf l) = tt) →
  ∃ (α₂ : assignment V), eval α₂ l = tt :=
begin
  rintros ⟨α, ha⟩,
  use α,
  rw xor_odd_eval_tt2 α l,
  rw ← gate_eq_clause l,
  rcases exists_mem_xor_cnf l with ⟨c, hc⟩,
  have := eval_tt_iff_forall_clause_eval_tt.mp ha,
  by_contradiction,
  simp at h,
  rw [← count_flips_falsify_eq_count_tt, count_flips_comm] at h,
  have falsify_mem := mem_xor_cnf_of_even_flips_of_map_var_eq
    (map_var_falsify_eq_list α (map var l)) h,
  have falsify_eval := falsify_eval_ff α (map var l),
  have := this (falsify α (map var l)) falsify_mem,
  exact absurd_bool this falsify_eval
end

theorem equisatisfiable_xor_cnf (l : list (literal V)) :
  assignment.equisatisfiable (λ α, cnf.eval α (xor_cnf l)) (λ α, xor_gate.eval α l) :=
begin
  split,
  { rintros ⟨α, ha⟩,
    simp at ha,
    have : ∃ α, cnf.eval α (xor_cnf l) = tt,
    { use [α, ha] },
    exact exists_xor_of_xor_cnf this },
  { rintros ⟨α, ha⟩,
    simp at ha,
    have : ∃ α, xor_gate.eval α l = tt,
    { use [α, ha] },
    exact exists_xor_cnf_of_xor this }
end

theorem vars_cnf_subset_xor {ls : list (literal V)} :
  ls ≠ [] → cnf.vars (xor_cnf ls) ⊆ (map var ls) :=
begin
  intro h,
  cases ls,
  { contradiction },
  { intros n hn,
    rcases cnf.exists_mem_clause_of_mem_vars hn with ⟨c, hcnf, hc⟩,
    simp [← map_var_eq_of_mem_xor_cnf hcnf, mem_vars_iff_mem_map_vars, hc] }
end

end xor_gate

/-! # Equivalence on domain for this encoding -/

namespace assignment

open list
open literal
open clause
open xor_gate

theorem equiv_on_domain_for_xor {α₁ α₂ : assignment V} {ls : list (literal V)} :
  (α₁ ≡[map var ls]≡ α₂) → eval α₁ ls = eval α₂ ls :=
begin
  induction ls with v vs ih,
  { simp },
  { intro h,
    simp [h, xor_gate.eval_cons],
    cases heval : literal.eval α₁ v;
    { cases v;
      { simp [literal.eval] at heval,
        simp [var] at h,
        rw h v (mem_cons_self v _) at heval,
        simp [heval, ih (eqod_of_eqod_cons h), literal.eval] } } }
end

end assignment