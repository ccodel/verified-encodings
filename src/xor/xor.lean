/-
This file defines the boolean XOR constraint on n variables.

Authors: Cayden Codel, Marijn Heule, Jeremy Avigad
Carnegie Mellon University
-/

import basic
import cnf.literal cnf.assignment cnf.clause cnf.cnf cnf.explode
import data.list.basic data.finset.basic

universe u

-- Represents the type of the variable stored in the literal
variables {V : Type u}

/- An n-variable XOR constraint is a map from a list of bools to an output bool -/
def Xor (l : list bool) : bool := l.foldr bxor ff

namespace Xor

open clause
open nat list

/-! # eval -/
section eval

variables (τ : assignment V) (l l₁ l₂ : list (literal V)) (lit : literal V)

/- Evaluate the variables under the assignment according to typical XOR -/
protected def eval : bool := Xor (l.map (literal.eval τ))

@[simp] theorem eval_nil : Xor.eval τ [] = ff := rfl

@[simp] theorem eval_singleton : Xor.eval τ [lit] = lit.eval τ :=
by simp only [Xor.eval, Xor, map, bool.bxor_ff_right, foldr]

theorem eval_cons : Xor.eval τ (lit :: l) = bxor (lit.eval τ) (Xor.eval τ l) :=
by simp only [Xor.eval, Xor, foldr, foldr_map]

theorem eval_append : 
  Xor.eval τ (l₁ ++ l₂) = bxor (Xor.eval τ l₁) (Xor.eval τ l₂) :=
begin
  induction l₁ with l ls ih,
  { simp only [bool.bxor_ff_left, eval_nil, nil_append] },
  { simp only [eval_cons, ih, cons_append, bool.bxor_assoc] }
end

/- Evaluates to true if an odd number of literals evaluates to true -/
theorem eval_eq_bodd_count_tt : Xor.eval τ l = bodd (clause.count_tt τ l) :=
begin
  induction l with l ls ih,
  { simp only [bodd_zero, eval_nil, count_tt_nil] },
  { cases h : (l.eval τ); { simp [Xor.eval_cons, count_tt_cons, h, ih] } }
end

theorem eval_eq_of_perm {l₁ l₂ : list (literal V)} : l₁ ~ l₂ → 
  ∀ (τ : assignment V), Xor.eval τ l₁ = Xor.eval τ l₂ :=
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

theorem eval_eq_of_eqod [decidable_eq V] {τ₁ τ₂ : assignment V} {l : list (literal V)} :
  (eqod τ₁ τ₂ (clause.vars l)) → Xor.eval τ₁ l = Xor.eval τ₂ l :=
begin
  induction l with l ls ih,
  { simp only [eqod_nil, Xor.eval_nil, forall_true_left, clause.vars_nil] },
  { intro h,
    simp only [Xor.eval_cons],
    rw eval_eq_of_eqod_of_var_mem h (mem_vars_of_mem (mem_cons_self l ls)),
    rw ih (eqod_subset (vars_subset_of_vars_cons l ls) h) }
end

end eval

end Xor