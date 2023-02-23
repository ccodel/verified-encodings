/-
This file defines the boolean XOR constraint on n variables.

Authors: Cayden Codel, Marijn Heule, Jeremy Avigad
Carnegie Mellon University
-/

import basic
import cnf.literal cnf.assignment cnf.clause cnf.cnf cnf.encoding
import parity.explode
import data.list.basic data.finset.basic

universe u

open clause
open nat list
open encoding

-- Represents the type of the variable stored in the literal
variables {V : Type*} [decidable_eq V]

/- An n-variable XOR constraint is a map from a list of bools to an output bool -/
def parity : constraint := λ l, (l.foldr bxor ff)
def parityF : constraint := λ l, (l.foldr bxor tt)

namespace parity

/-! # eval -/
section eval

variables (τ : assignment V) (l l₁ l₂ : list (literal V)) (lit : literal V)

@[simp] theorem eval_nil : parity.eval τ [] = ff := rfl

@[simp] theorem eval_singleton : parity.eval τ [lit] = lit.eval τ :=
by simp only [constraint.eval, parity, map, bool.bxor_ff_right, foldr]

theorem eval_cons : parity.eval τ (lit :: l) = bxor (lit.eval τ) (parity.eval τ l) :=
by simp only [constraint.eval, parity, foldr, foldr_map]

theorem eval_append : 
  parity.eval τ (l₁ ++ l₂) = bxor (parity.eval τ l₁) (parity.eval τ l₂) :=
begin
  induction l₁ with l ls ih,
  { simp only [bool.bxor_ff_left, eval_nil, nil_append] },
  { simp only [eval_cons, ih, cons_append, bool.bxor_assoc] }
end

/- Evaluates to true if an odd number of literals evaluates to true -/
theorem eval_eq_bodd_count_tt : parity.eval τ l = bodd (clause.count_tt τ l) :=
begin
  induction l with l ls ih,
  { simp only [bodd_zero, eval_nil, count_tt_nil] },
  { cases h : (l.eval τ); { simp [parity.eval_cons, count_tt_cons, h, ih] } }
end

theorem eval_eq_of_perm {l₁ l₂ : list (literal V)} : l₁ ~ l₂ → 
  ∀ (τ : assignment V), parity.eval τ l₁ = parity.eval τ l₂ :=
begin
  intros hp τ,
  induction hp with x l₂ l₂' p IH  x y l₂  l₂ m₂ r₂ p₁ p₂ IH₁ IH₂,
  { refl },
  { simp [eval_cons, IH] },
  { simp [eval_cons, ← bool.bxor_assoc],
    rw bool.bxor_comm (literal.eval τ y) (literal.eval τ x) },
  { exact eq.trans IH₁ IH₂ }
end

open assignment

theorem eval_eq_of_agree_on [decidable_eq V] {τ₁ τ₂ : assignment V} {l : list (literal V)} :
  (agree_on τ₁ τ₂ (clause.vars l)) → parity.eval τ₁ l = parity.eval τ₂ l :=
begin
  induction l with l ls ih,
  { simp only [agree_on_nil, parity.eval_nil, forall_true_left, clause.vars_nil] },
  { intro h,
    simp only [parity.eval_cons],
    rw eval_eq_of_agree_on_of_var_mem h (mem_vars_of_mem (mem_cons_self l ls)),
    rw ih (agree_on_subset (vars_subset_of_vars_cons l ls) h) }
end

end eval

end parity