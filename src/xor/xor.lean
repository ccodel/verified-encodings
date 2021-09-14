/-

  This file concerns the definition and translation of XOR gates into CNF, and
  proves that this translation is correct.

  Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
  Carnegie Mellon University

-/

import data.bool
import data.list.basic

import cnf.literal
import cnf.clause
import cnf.cnf
import cnf.explode
import basic

/- An n-literal XOR gate is a list of those literals -/
def xor_gate := list literal

namespace xor_gate

open list
open literal
open clause
open cnf
open explode

instance : has_append xor_gate := ⟨list.append⟩

-- The conversion of the XOR gate to a clause is a nice way of sweeping
-- uner the rug that the two definitions are actually identical
-- TODO canonical way of saying we want the nil/empty clause?
def to_clause (g : xor_gate) : clause :=
  g.foldr (λ l c, l :: c) []

-- Kinda cheesy
lemma gate_eq_clause (g : xor_gate) : g = g.to_clause :=
by simp [to_clause]

/- Evaluates the XOR gate under an assignment -/
def eval (α : assignment) (g : xor_gate) : bool :=
  g.foldr (λ l b, b ⊕ l.eval α) ff

@[simp] lemma eval_nil (α : assignment) : eval α [] = ff := rfl

lemma eval_cons (α : assignment) (l : literal) (g : xor_gate) : eval α (l :: g) = bxor (literal.eval α l) (eval α g) :=
by simp [eval, foldr_cons, bool.bxor_comm]

lemma eval_concat (α : assignment) (g₁ g₂ : xor_gate) : eval α (g₁ ++ g₂) = bxor (eval α g₁) (eval α g₂) :=
begin
  induction g₁ with l ls ih,
  { simp },
  { simp [eval_cons, ih] }
end

theorem eval_cons_conjunctive (α : assignment) (l : literal) (g : xor_gate) : 
  eval α (l :: g) = (literal.eval α l || eval α g) && (!(literal.eval α l) || !(eval α g)) :=
by simp only [← bxor_conjunctive, eval_cons α l g]

theorem eval_cons_disjunctive (α : assignment) (l : literal) (g : xor_gate) :
  eval α (l :: g) = (!(literal.eval α l) && eval α g) || (literal.eval α l && !(eval α g)) :=
by simp only [← bxor_disjunctive, eval_cons α l g]

/- Using a recursive evaluation function is sometimes more convenient -/
def eval_rec (α : assignment) : xor_gate → bool
| []        := ff
| (l :: ls) := l.eval α ⊕ eval_rec ls

/- To use the recursive definition, we need to prove that the two functions are equivalent -/
theorem eval_and_eval_rec_equiv (α : assignment) (g : xor_gate) : eval α g = eval_rec α g :=
begin
  induction g with l ls ih,
  { simp [eval_rec, eval] },
  { simp [eval_rec, ih, eval_cons] },
end

/- The XOR gate evaluates to true if an odd number of literals evaluates to true -/
theorem xor_odd_eval_tt (α : assignment) (g : xor_gate) : g.eval α = nat.bodd (g.countp (λ l, l.eval α = tt)) :=
begin
  induction g with l ls ih,
  { simp },
  { rcases bool_by_cases (l.eval α) with h | h;
    { simp [eval_cons, h, ih] } }
end

-- This is a shortcut of the above that uses gate.to_clause instead
-- NOTE that the to_clause is essentially an identity operation, but if sets/permuations are
-- used instead, the proof may grow more complex
theorem xor_odd_eval_tt2 (α : assignment) (g : xor_gate) : g.eval α = nat.bodd (g.to_clause.count_tt α) :=
begin
  induction g with l ls ih,
  { simp [to_clause] },
  { rcases bool_by_cases (l.eval α);
    { rw ← gate_eq_clause ls at ih,
      simp [to_clause, eval_cons, count_tt_cons, bool.to_nat, h, ih] } }
end

/-! ## Naive encoding, simple version -/

-- Let's start easier: turning a list of natural numbers into a cnf form
-- The naive encoding returns a formula with all possible clauses with an even number of negated literals
-- Because we are using natural numbers, i.e. positive literals, we want an even number of negative literals
def nat_to_xor_cnf : list nat → cnf
| []        := [[]]
| (n :: ns) := (explode ns).map (λ c, cond (nat.bodd c.count_neg = ff) ((Pos n) :: c) ((Neg n) :: c))

theorem mem_explode_of_mem_nat_to_xor :
  ∀ {ns : list nat}, ∀ {c : clause}, c ∈ nat_to_xor_cnf ns → c ∈ explode ns
| []        := by simp [nat_to_xor_cnf]
| (n :: ns) := begin
  simp [nat_to_xor_cnf, mem_map, mem_append],
  intros c hc,
  have : (Pos n).var = n ∧ (Neg n).var = n, simp [var], -- Make into literal lemma?
  rcases bool_by_cases (c.count_neg.bodd) with h | h;
  { simp [h, mem_explode_cons_of_lit c hc, this] }
end

theorem length_nat_to_xor_cnf : ∀ {ns : list nat}, ns ≠ [] → length (nat_to_xor_cnf ns) = 2^(length ns - 1)
| []        := by { contradiction }
| (n :: ns) := by simp [nat_to_xor_cnf, length_explode]

theorem length_nat_to_xor_cnf_pos : ∀ {ns : list nat}, ns ≠ [] → length (nat_to_xor_cnf ns) > 0
| []        := by { contradiction }
| (n :: ns) := by simp [length_nat_to_xor_cnf]

theorem exists_mem_nat_to_xor_of_ne_nil {ns : list nat} : ns ≠ [] → ∃ (c : clause), c ∈ nat_to_xor_cnf ns :=
assume h, exists_mem_of_length_pos (length_nat_to_xor_cnf_pos h)

theorem map_var_eq_of_mem_nat_to_xor : ∀ {ns : list nat}, ∀ {c : clause}, c ∈ nat_to_xor_cnf ns → c.map var = ns
| []        := by simp [nat_to_xor_cnf]
| (n :: ns) := begin
  simp [nat_to_xor_cnf],
  intros c hc,
  rcases bool_by_cases c.count_neg.bodd;
  { simp [h, var, map_var_eq_of_mem_explode hc] }
end

theorem mem_nat_to_xor_of_even_negation_of_map_var_eq : ∀ {ns : list nat}, ∀ {c : clause}, 
  c.map var = ns → (nat.bodd c.count_neg = ff) → c ∈ nat_to_xor_cnf ns
| []        := by simp [nat_to_xor_cnf]
| (n :: ns) := begin
  intros c hc,
  rcases exists_cons_of_map_cons hc with ⟨l, ls, rfl, hl, hls⟩,
  rcases pos_or_neg_of_var_eq_nat hl with rfl | rfl;
  { simp [count_neg_cons, is_neg, bool.to_nat, nat_to_xor_cnf],
    intro hcount, use ls,
    simp [hcount, mem_explode_of_map_var_eq hls] }
end

theorem even_negation_of_mem_nat_to_xor_of_map_var_eq : ∀ {ns : list nat}, ∀ {c : clause}, 
  c.map var = ns → c ∈ nat_to_xor_cnf ns → nat.bodd c.count_neg = ff
| []        := by simp
| (n :: ns) := begin
  intros c hc hxor,
  simp [nat_to_xor_cnf] at hxor,
  rcases hxor with ⟨a, ha, hacons⟩,
  rcases exists_cons_of_map_cons hc with ⟨l, ls, rfl, hl, hls⟩,
  rcases bool_by_cases a.count_neg.bodd with h | h;
  { simp [h] at hacons,
    simp [← hacons, count_neg_cons, is_neg, bool.to_nat, h] },
end

theorem even_negation_iff_mem_nat_to_xor {ns : list nat} {c : clause} (hc : c.map var = ns) :
  c ∈ nat_to_xor_cnf ns ↔ nat.bodd c.count_neg = ff :=
⟨even_negation_of_mem_nat_to_xor_of_map_var_eq hc,
  mem_nat_to_xor_of_even_negation_of_map_var_eq hc⟩

theorem not_mem_nat_to_xor_cnf_of_odd_negation_of_map_var_eq {ns : list nat} {c : clause} :
  c.map var = ns → (nat.bodd c.count_neg = tt) → c ∉ nat_to_xor_cnf ns :=
begin
  intros hc hcount,
  by_contradiction,
  exact absurd_bool hcount (even_negation_of_mem_nat_to_xor_of_map_var_eq hc h)
end

-- TODO move the c.map var assumption into the ns list nat portion since the above need it too
theorem odd_negation_of_not_mem_nat_to_xor_of_map_var_eq {ns : list nat} {c : clause} (hc : c.map var = ns) :
  c ∉ nat_to_xor_cnf ns → nat.bodd c.count_neg = tt :=
begin
  contrapose,
  simp,
  exact (even_negation_iff_mem_nat_to_xor hc).mpr
end

theorem odd_negation_iff_not_mem_nat_to_xor {ns : list nat} {c : clause} (hc : c.map var = ns) :
  c ∉ nat_to_xor_cnf ns ↔ nat.bodd c.count_neg = tt :=
⟨odd_negation_of_not_mem_nat_to_xor_of_map_var_eq hc, 
  not_mem_nat_to_xor_cnf_of_odd_negation_of_map_var_eq hc⟩

-- We prove that the naive encoding is equivalent to an XOR gate of all positive literals
theorem nat_to_xor_cnf_correct (α : assignment) : ∀ {ns : list nat}, 
  ns.nodup → cnf.eval α (nat_to_xor_cnf ns) = eval α (ns.map Pos)
| []        := by simp [nat_to_xor_cnf]
| (n :: ns) := begin
  intro hnodup,
  have red := xor_odd_eval_tt2 α (map Pos (n :: ns)),
  rcases bool_by_cases (eval α (map Pos (n :: ns))) with h | h;
  rw [h, ← gate_eq_clause (map Pos (n :: ns))] at red; rw h,
  -- tt case: Parities of α and clause tt evals means all clauses are true
  { apply eval_tt_iff_clauses_tt.mpr,
    intros c hc,
    have mve := map_var_eq_of_mem_nat_to_xor hc,
    have neq := neq_of_ff_of_tt (eq.symm red) ((even_negation_iff_mem_nat_to_xor mve).mp hc),
    exact eval_tt_of_opposite_parity (cons_ne_nil n ns) hnodup mve neq },
  -- ff case: We generate a false clause and show it is in the encoded formula
  { apply eval_ff_iff_exists_clause_ff.mpr,
    use (falsify α (n :: ns)),
    split,
    { apply (even_negation_iff_mem_nat_to_xor (map_var_falsify_eq_list α (n :: ns))).mpr,
      have oddeq := congr_arg nat.bodd (count_tt_pos_eq_count_neg_falsify α (n :: ns)),
      rw ← red at oddeq,
      exact oddeq.symm },
    { exact eval_ff_of_falsify α (n :: ns) } }
end

/-! # More complex encoding -/

/-
The above encoding assumed that the list of interest were only positive literals.
Here, we generalize and prove the encoding valid with general lists of literals.
The encoding is generated by counting "flips" between clauses rather than negations of literals.
-/
def xor_cnf : list literal → cnf
| []        := [[]]
| (l :: ls) := (explode (map var ls)).map (λ c, cond (nat.bodd (c.count_flips (ls)) = ff) (l :: c) (l.flip :: c))

theorem mem_explode_of_mem_xor_cnf :
  ∀ {ls : list literal} {c : clause}, c ∈ xor_cnf ls → c ∈ explode (map var ls)
| []        := by simp [xor_cnf]
| (l :: ls) := begin
  simp [xor_cnf, explode],
  intros c hc,
  rcases exists_nat_of_lit l with ⟨n, (rfl | rfl)⟩;
  rcases bool_by_cases (nat.bodd (c.count_flips ls)) with h | h,
  { right, use c, simp [h, hc, var, literal.flip] },
  { left, use c, simp [h, hc, var, literal.flip] },
  { left, use c, simp [h, hc, var, literal.flip] },
  { right, use c, simp [h, hc, var, literal.flip] }
end

theorem length_xor_cnf : ∀ {ls : list literal}, ls ≠ [] → length (xor_cnf ls) = 2^(length ls - 1)
| []        := by { contradiction }
| (l :: ls) := by simp [xor_cnf, length_explode]

theorem length_xor_cnf_pos : ∀ {ls : list literal}, ls ≠ [] → length (xor_cnf ls) > 0
| []        := by { contradiction }
| (l :: ls) := by simp [length_xor_cnf]

theorem exists_mem_xor_cnf_of_ne_nil {ls : list literal} : ls ≠ [] → ∃ (c : clause), c ∈ xor_cnf ls :=
assume h, exists_mem_of_length_pos (length_xor_cnf_pos h)

theorem map_var_eq_of_mem_xor_cnf {ls : list literal} : ∀ {c : clause}, c ∈ xor_cnf ls → map var c = map var ls :=
begin
  induction ls with l ls ih,
  { simp [xor_cnf] },
  { simp [xor_cnf],
    intros c hc,
    rcases bool_by_cases (nat.bodd (c.count_flips ls)) with h | h;
    { simp [h, map_var_eq_of_mem_explode hc, var_flip_eq_var l] } }
end

theorem mem_xor_cnf_of_even_flips_of_map_var_eq : ∀ {ls : list literal}, ∀ {c : clause},
  map var c = map var ls → (nat.bodd (c.count_flips ls) = ff) → c ∈ xor_cnf ls
| []        := by simp [xor_cnf]
| (l :: ls) := begin
  simp [xor_cnf, map_cons],
  intros c hc hcount,
  rcases exists_cons_of_map_cons hc with ⟨d, ds, rfl, hd, hds⟩,
  use ds,
  rcases bool_by_cases (nat.bodd (count_flips ds ls)) with htt | hff,
  { by_cases l.flip = d,
    { simp [htt, mem_explode_of_map_var_eq hds, hd, h] },
    { simp [count_flips, ne.symm (ne_flip_of_flip_ne h)] at hcount,
      exact absurd_bool htt hcount } },
  { by_cases l.flip = d,
    { simp [count_flips, eq_flip_of_flip_eq h] at hcount,
      exact absurd_bool hcount hff },
    { simp [hff, mem_explode_of_map_var_eq hds, hd, eq_of_flip_ne_of_var_eq hd.symm h] } }
end

theorem even_flips_of_mem_xor_cnf_of_map_var_eq : ∀ {ls : list literal}, ∀ {c : clause},
  c.map var = map var ls → c ∈ xor_cnf ls → nat.bodd (count_flips c ls) = ff
| []        := by simp [xor_cnf]
| (l :: ls) := begin
  intros c hc hxor,
  simp [xor_cnf] at hxor,
  rcases hxor with ⟨a, ha, hacons⟩,
  rcases exists_cons_of_map_cons hc with ⟨c, cs, rfl, hc2, hcs⟩,
  rcases bool_by_cases (nat.bodd (count_flips a ls)) with h | h;
  { simp [h] at hacons,
    simp [← hacons, count_flips, is_neg, bool.to_nat, h, eq_flip_flip _, ne_flip_self] }
end

theorem even_flips_iff_mem_xor_cnf {ls : list literal} {c : clause} (hc : c.map var = map var ls) :
  nat.bodd (count_flips c ls) = ff ↔ c ∈ xor_cnf ls :=
⟨mem_xor_cnf_of_even_flips_of_map_var_eq hc, even_flips_of_mem_xor_cnf_of_map_var_eq hc⟩

theorem not_mem_xor_cnf_of_odd_flips_of_map_var_eq {ls : list literal} {c : clause} :
  map var c = map var ls → (nat.bodd (count_flips c ls)) = tt → c ∉ xor_cnf ls :=
begin
  intros hc hcount,
  by_contradiction,
  exact absurd_bool hcount ((even_flips_iff_mem_xor_cnf hc).mpr h)
end

theorem odd_flips_of_not_mem_xor_cnf_of_map_var_eq {ls : list literal} {c : clause} :
  map var c = map var ls → c ∉ xor_cnf ls → (nat.bodd (count_flips c ls)) = tt :=
begin
  intro hc,
  contrapose,
  simp,
  exact (even_flips_iff_mem_xor_cnf hc).mp
end

theorem odd_flips_iff_not_mem_xor_cnf {ls : list literal} {c : clause} (hc : map var c = map var ls) :
  nat.bodd (count_flips c ls) = tt ↔ c ∉ xor_cnf ls :=
⟨not_mem_xor_cnf_of_odd_flips_of_map_var_eq hc, odd_flips_of_not_mem_xor_cnf_of_map_var_eq hc⟩

-- A restatement of the above theorem in a more general way
-- Alternatively, the assignment can be manipulated by flipping the correct literals
theorem xor_cnf_correct (α : assignment) : ∀ {ls : list literal},
  (map var ls).nodup → cnf.eval α (xor_cnf ls) = eval α ls
| []        := by simp [xor_cnf]
| (l :: ls) := begin
  intro hnodup,
  have red := xor_odd_eval_tt2 α (l :: ls),
  rcases bool_by_cases (eval α (l :: ls)) with h | h;
  rw [h, ← gate_eq_clause (l :: ls)] at red; rw h,
  { apply eval_tt_iff_clauses_tt.mpr,
    intros c hc,
    have mve := map_var_eq_of_mem_xor_cnf hc,
    have neqodd := neq_of_ff_of_tt (eq.symm red) ((even_flips_iff_mem_xor_cnf mve).mpr hc),
    have neq := ne_of_apply_ne nat.bodd neqodd,
    rw count_flips_comm at neq,
    exact eval_tt_of_neq_flips (cons_ne_nil l ls) hnodup c mve.symm neq },
  { apply eval_ff_iff_exists_clause_ff.mpr,
    use (falsify α (map var (l :: ls))),
    split,
    { rw ← count_flips_falsify_eq_count_tt α (l :: ls) at red,
      rw count_flips_comm at red,
      apply (even_flips_iff_mem_xor_cnf (map_var_falsify_eq_list α (map var (l :: ls)))).mp,
      exact red.symm },
    { exact eval_ff_of_falsify α (map var (l :: ls)) } }
end

end xor_gate