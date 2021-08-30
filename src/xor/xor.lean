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
  split; { simp [eval] },
  by_cases (l.eval α = tt),
  { simp [h, ih, eval_cons] },
  { simp at h, simp [h, ih, eval_cons] }
end

theorem xor_odd_eval_tt2 (α : assignment) (g : xor_gate) : g.eval α = nat.bodd (g.to_clause.count_tt α) :=
begin
  induction g with l ls ih,
  { simp [to_clause] },
  {
    by_cases (l.eval α = tt),
    { rw ← gate_eq_clause ls at ih,
      simp [to_clause, eval_cons, count_tt_cons, bool.to_nat, h, ih] },
    { simp at h,
      rw ← gate_eq_clause ls at ih,
      simp [to_clause, eval_cons, count_tt_cons, bool.to_nat, h, ih] } }
end

-- Let's start easier: turning a list of natural numbers into a cnf form
-- We use explode.explode, which takes in a list of nats. Alternatively, we take a list of ints and get tricky with negatives meaning flipped
-- Note the return value of explode is list clause, which is cnf
def nat_to_xor_cnf : list nat → cnf
| []        := [[]]
| (n :: ns) := (explode ns).map (λ c, cond (nat.bodd c.count_neg = ff) ((Pos n) :: c) ((Neg n) :: c))

-- Riskier, but what else can you do?
theorem mem_explode_of_mem_nat_to_xor :
  ∀ {ns : list nat}, ∀ {c : clause}, c ∈ nat_to_xor_cnf ns → c ∈ explode ns
| []        := by simp [nat_to_xor_cnf]
| (n :: ns) := begin
  simp [nat_to_xor_cnf, mem_map, mem_append],
  intros c hc,
  by_cases c.count_neg.bodd = tt,
  { simp [h], have : (Pos n).var = n, simp [var],
    exact mem_explode_cons_of_lit c hc this },
  { simp [bool_eq_false h], have : (Neg n).var = n, simp [var],
    exact mem_explode_cons_of_lit c hc this }
end

theorem nat_to_xor_cnf_length {ns : list nat} : ns ≠ [] → length (nat_to_xor_cnf ns) = 2^(length ns - 1) :=
begin
  cases classical.em (ns = nil); intro hns,
  { exact absurd h hns },
  { rcases exists_cons_of_ne_nil hns with ⟨w, ⟨l, rfl⟩⟩, 
    simp only [nat_to_xor_cnf, length_map, length_cons, length_explode, nat.succ_sub_one] }
end

theorem exists_mem_nat_to_xor_of_ne_nil {ns : list nat} : ns ≠ [] → ∃ (c : clause), c ∈ nat_to_xor_cnf ns :=
begin
  induction ns with m ms ih,
  { contradiction },
  { intro _,
    by_cases hms : ms = [],
    { use (Pos m) :: [],
      simp [hms, nat_to_xor_cnf] },
    { 
      rcases ih hms with ⟨c, hc⟩,
      by_cases nat.bodd c.count_neg = ff,
      { use (Pos m :: c),
        simp [nat_to_xor_cnf],
        use c,
        simp [mem_explode_of_mem_nat_to_xor hc, h] },
      { use (Neg m :: c),
        simp [nat_to_xor_cnf],
        use c,
        simp [mem_explode_of_mem_nat_to_xor hc, h] } } }
end

theorem map_var_eq_of_mem_nat_to_xor : ∀ {ns : list nat}, ∀ {c : clause}, c ∈ nat_to_xor_cnf ns → c.map var = ns
| []        := by { simp [nat_to_xor_cnf] }
| (n :: ns) := begin
  simp [nat_to_xor_cnf],
  intros c hc,
  by_cases c.count_neg.bodd = ff;
  { simp [h, var, map_var_eq_of_mem_explode hc] }
end

-- Can be shortened to one or two lines given aboce theorem, as sim. is weaker
theorem map_var_sim_of_mem_nat_to_xor : ∀ (ns : list nat), ∀ (c : clause), c ∈ nat_to_xor_cnf ns → c.map var ~ ns
| []        := by { simp [nat_to_xor_cnf] }
| (n :: ns) := begin
  simp only [nat_to_xor_cnf, mem_map, mem_append],
  rintros c ⟨a, ⟨ha1, ha2⟩⟩,
  by_cases a.count_neg.bodd = tt,
  { simp [h] at ha2, simp [← ha2, var, map_var_sim_of_mem_explode a ha1] },
  { simp [bool_eq_false h] at ha2, simp [← ha2, var, map_var_sim_of_mem_explode a ha1] }
end

theorem exists_mem_explode_sim_of_mem_nat_to_xor {ns : list nat} : 
  ∀ (c : clause), c ∈ nat_to_xor_cnf ns → ∃ cl ∈ explode ns, c ~ cl :=
assume c h, mem_explode_sim_of_map_var_sim c (map_var_sim_of_mem_nat_to_xor ns c h)



-- Technically not a proof by induction, fix later?
theorem nat_to_xor_cnf_contains_all_even_negated_clauses {ns : list nat} :
  ∀ {c : clause}, c.map var = ns → (nat.bodd c.count_neg = ff) → c ∈ nat_to_xor_cnf ns :=
begin
  induction ns with m ms ih,
  { simp [nat_to_xor_cnf] },
  { intros c hc,
  rcases exists_cons_of_map_cons hc with ⟨l, ls, rfl, hl, hls⟩,
  rcases pos_or_neg_of_var_eq_nat hl with rfl | rfl;
  { simp [count_neg_cons, is_neg, bool.to_nat, nat_to_xor_cnf],
    intro hcount, use ls,
    simp [hcount, mem_explode_of_map_var_eq hls] } }
end

-- Not really induction, switch later
theorem even_negation_of_mem_nat_to_xor {ns : list nat} :
  ∀ {c : clause}, c.map var = ns → c ∈ nat_to_xor_cnf ns → nat.bodd c.count_neg = ff :=
begin
  induction ns with m ms ih,
  { simp },
  intros c hc hxor,
  simp [nat_to_xor_cnf] at hxor,
  rcases hxor with ⟨a, ha, hacons⟩,
  rcases exists_cons_of_map_cons hc with ⟨l, ls, rfl, hl, hls⟩,
  by_cases a.count_neg.bodd = ff,
  { simp [h] at hacons,
    simp [← hacons, count_neg_cons, is_neg, bool.to_nat, h] },
  { simp [h] at hacons,
    simp at h,
    simp [← hacons, count_neg_cons, is_neg, bool.to_nat, h] }
end

theorem even_negation_iff_mem_nat_to_xor {ns : list nat} {c : clause} (hc : c.map var = ns) :
  c ∈ nat_to_xor_cnf ns ↔ nat.bodd c.count_neg = ff :=
⟨even_negation_of_mem_nat_to_xor hc, nat_to_xor_cnf_contains_all_even_negated_clauses hc⟩

theorem nat_to_xor_cnf_contains_no_odd_negated_clauses {ns : list nat} :
  ∀ {c : clause}, c.map var = ns → (nat.bodd c.count_neg = tt) → c ∉ nat_to_xor_cnf ns :=
begin
  intros c hc hcount,
  by_cases c ∈ nat_to_xor_cnf ns, -- This is a little cheesy, but I want to show contradiction
  { have red := even_negation_of_mem_nat_to_xor hc h,
    rw hcount at red,
    exact absurd red (ne.symm ff_eq_tt_eq_false) },
  { exact h }
end

-- TODO move the c.map var assumption into the ns list nat portion since the above need it too
theorem odd_negation_of_not_mem_nat_to_xor {ns : list nat} :
  ∀ {c : clause}, c.map var = ns → c ∉ nat_to_xor_cnf ns → nat.bodd c.count_neg = tt :=
begin
  intros c hc,
  contrapose,
  simp,
  intro hcount,
  exact nat_to_xor_cnf_contains_all_even_negated_clauses hc hcount
end

theorem odd_negation_iff_not_mem_nat_to_xor {ns : list nat} {c : clause} (hc : c.map var = ns) :
  c ∉ nat_to_xor_cnf ns ↔ nat.bodd c.count_neg = tt :=
⟨odd_negation_of_not_mem_nat_to_xor hc, nat_to_xor_cnf_contains_no_odd_negated_clauses hc⟩

-- TODO clean up, e.g. by apply
theorem true_forward {α : assignment} : ∀ {ns : list nat} (hnodup: ns.nodup), eval α (ns.map Pos) = tt → cnf.eval α (nat_to_xor_cnf ns) = tt
| []        := by simp
| (n :: ns) := begin
  intros hnsnodup h,
  have red := xor_odd_eval_tt2 α (map Pos (n :: ns)),
  rw h at red,
  rw ← gate_eq_clause (map Pos (n :: ns)) at red,
  have : ∀ (c : clause), c ∈ nat_to_xor_cnf (n :: ns) → clause.eval α c = tt,
  { intros c hc,
    have mapvareq : map var c = (n :: ns), from map_var_eq_of_mem_nat_to_xor hc,
    have : nat.bodd c.count_neg = ff, from even_negation_of_mem_nat_to_xor mapvareq hc,
    have neq : nat.bodd (count_tt α (map Pos (n :: ns))) ≠ nat.bodd c.count_neg,
      from neq_of_ff_of_tt (eq.symm red) this,
    exact eval_tt_of_opposite_parity (cons_ne_nil n ns) hnsnodup mapvareq neq },
  exact eval_tt_iff_clauses_tt.mpr this
end

-- TODO clean up
theorem false_forward {α : assignment} : ∀ {ns : list nat} (hnodup : ns.nodup), eval α (ns.map Pos) = ff → cnf.eval α (nat_to_xor_cnf ns) = ff
| []        := by simp [nat_to_xor_cnf]
| (n :: ns) := begin
  intros hnsnodup h,
  have red := xor_odd_eval_tt2 α (map Pos (n :: ns)),
  rw h at red,
  rw ← gate_eq_clause (map Pos (n :: ns)) at red,
  apply eval_ff_iff_exists_clause_ff.mpr,
  have : count_tt α (map Pos (n :: ns)) = count_neg (falsify α (n :: ns)), 
    from count_tt_pos_eq_count_neg_falsify α (n :: ns),
  have : nat.bodd (count_tt α (map Pos (n :: ns))) = nat.bodd (count_neg (falsify α (n :: ns))), 
    from congr_arg nat.bodd this,
  rw ← red at this,
  have mapvareq := nat_to_xor_cnf_contains_all_even_negated_clauses (map_var_falsify_eq_list α (n :: ns)) this.symm,
  use (falsify α (n :: ns)),
  simp [mapvareq, eval_ff_of_falsify α (n :: ns)]
end

-- We prove that the naive encoding is equivalent to an XOR gate of all positive literals
theorem nat_to_xor_cnf_correct (α : assignment) {ns : list nat} (hns : ns.nodup) : 
  cnf.eval α (nat_to_xor_cnf ns) = eval α (ns.map Pos) :=
begin
  rcases bool_by_cases (eval α (map Pos ns)) with h | h,
  { simp [h, true_forward hns] },
  { simp [h, false_forward hns] }
end

end xor_gate