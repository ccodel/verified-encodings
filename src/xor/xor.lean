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
theorem eval_and_eval_rec_equiv {α : assignment} {g : xor_gate} : eval α g = eval_rec α g :=
begin
  induction g with l ls ih,
  { simp [eval_rec, eval] },
  { simp [eval_rec, ih, eval_cons] },
end

/- The XOR gate evaluates to true if an odd number of literals evaluates to true -/
theorem xor_odd_eval_tt {α : assignment} {g : xor_gate} : g.eval α = nat.bodd (g.countp (λ l, l.eval α = tt)) :=
begin
  induction g with l ls ih,
  split; { simp [eval] },
  by_cases (l.eval α = tt),
  { simp [h, ih, eval_cons] },
  { simp at h, simp [h, ih, eval_cons] }
end

-- Let's start easier: turning a list of natural numbers into a cnf form
-- We use explode.explode, which takes in a list of nats. Alternatively, we take a list of ints and get tricky with negatives meaning flipped
-- Note the return value of explode is list clause, which is cnf
def nat_to_xor_cnf : list nat → cnf
| []        := [[]]
| (n :: ns) := (explode ns).map (λ c, cond (nat.bodd c.count_neg = ff) ((Pos n) :: c) ((Neg n) :: c))

theorem nat_to_xor_cnf_length {ns : list nat} : ns ≠ [] → length (nat_to_xor_cnf ns) = 2^(length ns - 1) :=
begin
  cases classical.em (ns = nil); intro hns,
  { exact absurd h hns },
  { rcases exists_cons_of_ne_nil hns with ⟨w, ⟨l, rfl⟩⟩, 
    simp only [nat_to_xor_cnf, length_map, length_cons, length_explode, nat.succ_sub_one] }
end

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

-- Riskier, but what else can you do?
theorem exists_mem_explode_of_mem_nat_to_xor :
  ∀ (ns : list nat), ∀ (c : clause), c ∈ nat_to_xor_cnf ns → c ∈ explode ns
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

-- TODO cleanup
theorem nat_to_xor_cnf_contains_no_even_negated_clauses {ns : list nat} (hns: ns ≠ []) :
  ∀ {c : clause}, c.map var = ns → (nat.bodd c.count_neg = tt) → c ∉ nat_to_xor_cnf ns :=
begin
  induction ns with m ms ih,
  { contradiction },
  {
    intros c hc,
    rcases exists_cons_of_map_cons hc with ⟨l, ls, rfl, hl, hls⟩,
    rcases pos_or_neg_of_var_eq_nat hl with rfl | rfl,
    { simp [count_neg_cons, is_neg, bool.to_nat, nat_to_xor_cnf],
      intros hcount x hx,
      by_cases (count_neg x).bodd = tt,
      { simp [h], intro h2,
        exact absurd (head_eq_of_cons_eq h2) ne_pos_neg_of_nat.symm },
      { simp [bool_eq_false h], -- Lots of fooling around with ¬ and ff, clean up
        intro h2, have h2 := tail_eq_of_cons_eq h2,
        rw h2 at h,
        rw hcount at h,
        exact absurd (refl tt) h } },
    { simp [count_neg_cons, is_neg, bool.to_nat, nat_to_xor_cnf],
      intros hcount x hx,
      by_cases (count_neg x).bodd = tt,
      { simp [h], intro h2,
        have h2 := tail_eq_of_cons_eq h2,
        rw h2 at h,
        exact bool_iff_false.mpr hcount h },
      { simp [bool_eq_false h], intro h2,
        exact absurd (head_eq_of_cons_eq h2) ne_pos_neg_of_nat } } }
end

-- We prove that the naive encoding is equivalent to an XOR gate of all positive literals
theorem nat_to_xor_cnf_correct {α : assignment} : ∀ (ns : list nat), cnf.eval α (nat_to_xor_cnf ns) = eval α (ns.map Pos)
| []        := by simp [nat_to_xor_cnf]
| (n :: ns) := begin
  --simp [nat_to_xor_cnf, map_cons, eval_cons],
  by_cases ((map Pos (n :: ns)).countp (λ l, literal.eval α l = tt)).bodd = tt,
  { --  We are in the odd case, meaning that we should satisfy
    have : eval α (map Pos (n :: ns)) = ((map Pos (n :: ns)).countp (λ l, literal.eval α l = tt)).bodd, from xor_odd_eval_tt,
    rw this.symm at h,
    rw h,
    simp [nat_to_xor_cnf],
    sorry,


  }
  sorry,
  sorry,
end

end xor_gate