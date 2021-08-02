/-

  This file contains the definitions of and basic operations on variables, literals,
  clauses, and conjunctive normal form.

  Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
  Carnegie Mellon University

-/

import data.list.basic
import init.data.nat

/- 
  All propositional formulas are comprised of Boolean variables.
  Here, we represent variables as natural numbers, which may then be evaluated
  with an appropriate assignment of boolean values to those variables.

  Literals are positive and negative instances of those variables.
-/

inductive literal : Type
  | Pos : nat → literal
  | Neg : nat → literal

/- Assignments give boolean values to the variables -/
def assignment := nat → bool

namespace literal

/- Negated literals receive the opposite boolean value as the variable -/
def eval (α : assignment) : literal → bool
  | (Pos n) := α n
  | (Neg n) := bnot (α n)

/- Extracts the natural number boolean variable of the literal -/
def var : literal → nat
  | (Pos n) := n
  | (Neg n) := n

def flip : literal → literal
  | (Pos n) := Neg n
  | (Neg n) := Pos n

def set_pos : literal → literal
  | (Pos n) := Pos n
  | (Neg n) := Pos n

def set_neg : literal → literal
  | (Pos n) := Neg n
  | (Neg n) := Neg n

def is_pos : literal → bool
  | (Pos _) := tt
  | (Neg _) := ff

def is_neg : literal → bool
  | (Pos _) := ff
  | (Neg _) := tt

end literal

/- (Disjunctive) clauses are lists of literals joined by logical ORs -/
def clause := list literal

namespace clause

--def length (c : clause) : nat := c.length

/- The clause represents a disjunction, so we evaluate literals until tt is found -/
def eval (α : assignment) (c : clause) : bool :=
  c.foldr (λ l, λ b, b ∨ l.eval α) ff

/- Counts the number of literals that evaluate to true in the clause, under some assignment -/
def count_tt (α : assignment) (c : clause) : nat :=
  list.length $ c.filter (λ l, l.eval α = tt)

/- Counts the number of literals that evaluate to false in the clause, under some assignment -/
def count_ff (α : assignment) (c : clause) : nat :=
  list.length $ c.filter (λ l, l.eval α = ff)

/- Counts the number of positive literals in the clause -/
/- TODO why can't I use a match statement? Requires decidable_pred... -/
def count_pos (c : clause) : nat :=
  --list.length $ c.filter (λ l, match l with | (literal.Pos _) := true | _ := false end)
  list.length $ c.filter (λ l, literal.is_pos l = tt)

/- Counts the number of negative literals in the clause -/
def count_neg (c : clause) : nat :=
  list.length $ c.filter (λ l, literal.is_neg l = tt)

/- Some useful statements for proofs of clauses -/
lemma empty_eval_ff (α : assignment) (c : clause) : c.length = 0 → eval α c = ff :=
begin
  intro h,
  rw list.length_eq_zero at h,
  rw h,
  unfold eval,
  simp,
end

lemma single_eval_lit [inhabited literal] (α : assignment) (c : clause) : c.length = 1 → eval α c = c.head.eval α :=
begin
  intro h,
  rw list.length_eq_one at h,
  cases h with a ha,
  unfold eval,
  simp [ha],
end

end clause

/- Conjunctive normal form is a list of clauses joined by logical ANDs -/
def cnf := list clause

namespace cnf

/- The clauses of the CNF are joined by conjunctions, so all must evaluate to true -/
def eval (α : assignment) (f : cnf) : bool :=
  f.foldr (λ c, λ b, b ∧ c.eval α) tt

/- Counts the number of clauses which evaluate to true under some assignment -/
def count_tt (α : assignment) (f : cnf) : nat :=
  list.length $ f.filter (λ c, c.eval α = tt)

/- Counts the number of clauses which evaluate to false under some assignment -/
def count_ff (α : assignment) (f : cnf) : nat :=
  list.length $ f.filter (λ c, c.eval α = ff)

/- Some useful simplifying statements -/
lemma empty_eval_ff (α : assignment) (f : cnf) : f.length = 0 → f.eval α = tt :=
begin
  intro h,
  rw list.length_eq_zero at h,
  rw h,
  unfold eval,
  simp,
end

-- Note: These proofs are identical to the ones above: simpler proof?
lemma single_eval_clause [inhabited clause] (α : assignment) (f : cnf) : f.length = 1 → eval α f = f.head.eval α :=
begin
  intro h,
  rw list.length_eq_one at h,
  cases h with a ha,
  unfold eval,
  simp [ha],
end

end cnf

/- Sometimes, it is necessary to get all possible disjunctive clauses from a set of variables -/
/- For lack of a better name, we call that operation "exploding" -/
namespace explode

open literal

/- This should ideally take in a nodup list or a finset, but lists are easier to manipulate -/
/- Also, should ideally return a nodup list or a finset, see above comment -/
def expl (l : list nat) : list clause :=
  l.foldr (λ n, λ ls, (ls.map (λ e, (Pos n) :: e)) ++ (ls.map (λ e, (Neg n) :: e))) [[]]

/- Note: The nil case differs between the two. See if can fix above... -/
def expl_rec : list nat → list clause 
  | []        := []
  | (n :: ns) :=
  let
    res := expl_rec ns
  in
    res.map (λ e, (Pos n) :: e) ++ res.map (λ e, (Neg n) :: e)

/- True if clause has even number of negated clauses, false otherwise -/
def expl_parity (l : list nat) : list (clause × bool) :=
  l.foldr (λ n, λ r,
    (r.map (λ e, let (cl, par) := e in ⟨(Pos n) :: cl, par⟩) ++ 
    (r.map (λ e, let (cl, par) := e in ⟨(Neg n) :: cl, bnot par⟩)))) [([], tt)]

/- Counts the number of negated literals in each clause -/
def expl_count (l : list nat) : list (clause × nat) :=
  l.foldr (λ n, λ r,
    (r.map (λ e, let (cl, c) := e in ⟨(Pos n) :: cl, c⟩) ++ 
    (r.map (λ e, let (cl, c) := e in ⟨(Neg n) :: cl, c + 1⟩)))) [([], 0)]

-- Again, this proof is exactly the same as the eval single above
lemma explode_single (l : list nat) : l.length = 1 → expl l = [[Pos l.head], [Neg l.head]] :=
begin
  intro h,
  rw list.length_eq_one at h,
  cases h with a ha,
  unfold expl,
  simp [ha],
end

lemma explode_all_same_length (l : list nat) (len : l.length > 0) : ∀ c ∈ expl l, list.length c = list.length l :=
begin
  intros c h,
  induction l,

  -- This can probably be cleaned up
  exfalso,
  have : ([] : list nat) = [], from rfl,
  have z : list.length [] = 0, from list.length_eq_zero.2 this,
  rw z at len,
  simp at len,
  exact len,

  -- Inudction hypothesis
  cases l_tl,
  have hd_len : [l_hd].length = 1, from list.length_singleton l_hd,
  unfold expl at h,
  simp at h,
  cases h with hl hr,
  rw hd_len,
  simp [hl],

  rw hd_len,
  simp [hr],

  have not_nil : (l_tl_hd :: l_tl_tl) ≠ list.nil, from list.cons_ne_nil l_tl_hd l_tl_tl,
  have pos_len : (l_tl_hd :: l_tl_tl).length > 0, from list.length_pos_of_ne_nil not_nil,
  have k := l_ih pos_len,
  


end

lemma explode_count_accurate (l : list nat) (cl : clause) (c : nat) : ∀ e ∈ expl_count l, e = (cl, c) → clause.count_neg cl = c :=
begin
  intros e h eq,
  induction l,
  unfold expl_count at h,
  simp at h,
  rw eq at h,
  have k := prod.mk.inj h,
  cases k with k1 k2,
  rw k1,
  unfold clause.count_neg,
  simp,
  symmetry,
  exact k2,

  -- Induction step
  unfold expl_count at h,
  simp at h,
  cases h with hl hr,
  
end

--lemma exists_sat (l : list nat) (α : assignment) : l.length > 0 → ∃c ∈ expl l, clause.eval α c = tt :=
--begin
--  intro h,
--  induction l with n hn,
--  exfalso,
--  simp at h,
--  exact h,

  -- Induction case
--  cases α n with hf ht,
--  sorry,
--  sorry,
--end

-- Cannot write clause for list literal here, for some reason
/- States that for exploded var lists, any clause is a member -/
/- This seems an overly complex definition... sets would be so much easier -/
--lemma all_mem_explode {ns : list nat} {c : list literal} (nsl : ns.length > 0) (cs_eq_c : c.length = ns.length) 
--  : (∀i, (0 ≤ i ∧ i < c.length) ∧ ∃ (cl : literal), list.nth c i = some cl ∧ ∃ (nn : nat), list.nth ns i = some nn ∧ cl.var = nn) → c ∈ expl ns :=
--∀ l ∈ c, literal.var l ∈ ns) → c ∈ expl ns :=
--begin
--  intro i,
--  intro h,

--end

end explode