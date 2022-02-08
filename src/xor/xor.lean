/-
This file defines the XOR gate on n variables, as well as
general properties of evaluation of XORs.

Authors: Cayden Codel, Marijn Heule, Jeremy Avigad
Carnegie Mellon University
-/

import basic
import cnf.literal
import cnf.assignment
import cnf.clause
import cnf.cnf
import cnf.explode

import data.list.basic
import data.finset.basic

universe u

-- Represents the parametric type of the variable stored in the literal
variables {V : Type u} [decidable_eq V] [inhabited V]

/- An n-literal XOR function is a list of those literals. -/
-- Unfortunately, "xor" was already defined, so "n"xor to mean n literals
def Xor (V : Type u) := list (literal V)

-- Not to be confused with the XNOR gate
-- See the note in cnf/clause.lean for discussion of list vs. set typing

namespace Xor

open nat
open list
open clause

/-! # Properties -/

instance : inhabited (clause V) := ⟨[arbitrary (literal V)]⟩
instance : has_append (Xor V) := ⟨list.append⟩
instance : has_mem (literal V) (Xor V) := ⟨list.mem⟩

/-! # eval -/
section eval

variables (τ : assignment V) (g : Xor V) (l : literal V)

/- Evaluate the variables under the assignment according to typical XOR -/
protected def eval : bool :=
  g.foldr (λ l b, b ⊕ l.eval τ) ff

@[simp] theorem eval_nil : Xor.eval τ [] = ff := rfl

@[simp] theorem eval_singleton : Xor.eval τ [l] = l.eval τ :=
by simp only [Xor.eval, bool.bxor_ff_left, foldr]

theorem eval_cons : Xor.eval τ (l :: g) = bxor (l.eval τ) (g.eval τ) :=
by simp only [Xor.eval, foldr, bool.bxor_comm]

theorem eval_append (g₁ g₂ : Xor V) : 
  Xor.eval τ (g₁ ++ g₂) = bxor (g₁.eval τ) (g₂.eval τ) :=
begin
  induction g₁ with l ls ih,
  { simp only [bool.bxor_ff_left, eval_nil, nil_append] },
  { simp only [eval_cons, ih, cons_append, bool.bxor_assoc] }
end

/- Evaluates to true if an odd number of literals evaluates to true -/
theorem eval_eq_bodd_count_tt : g.eval τ = bodd (clause.count_tt τ g) :=
begin
  induction g with l ls ih,
  { simp only [bodd_zero, eval_nil, count_tt_nil] },
  { cases h : (l.eval τ);
    { simp [Xor.eval_cons, count_tt_cons, h, ih] } }
end

end eval

/-! # vars -/
section vars

variables {g : Xor V} {l : literal V} {v : V}

/- For now, since the implementation of clause and Xor are the same,
   using clause.lean's version of vars saves on space for redundant theorems.
   If the implementation of clause or Xor changes, this definition will
   need to be updated accordingly. -/
def vars (g : Xor V) : finset V := clause.vars g

@[simp] theorem vars_nil : Xor.vars ([] : Xor V) = ∅ := rfl

@[simp] theorem vars_singleton (l : literal V) : Xor.vars [l] = {l.var} :=
clause.vars_singleton l

theorem mem_vars_cons_of_mem_vars : v ∈ g.vars → v ∈ Xor.vars (l :: g) :=
clause.mem_vars_cons_of_mem_vars l

theorem mem_vars_of_mem : l ∈ g → l.var ∈ g.vars :=
clause.mem_vars_of_mem

theorem vars_subset_of_vars_cons (l : literal V) (g : Xor V) :
  g.vars ⊆ Xor.vars (l :: g) :=
finset.subset_union_right _ _

-- Other theorems from clause.vars possible, if needed

end vars

end Xor

/-! # eqod for Xor -/

namespace assignment

open list
open Xor

theorem eval_eq_Xor_of_eqod {τ₁ τ₂ : assignment V} {g : Xor V} :
  (τ₁ ≡g.vars≡ τ₂) → g.eval τ₁ = g.eval τ₂ :=
begin
  induction g with l ls ih,
  { simp only [eqod_nil, eval_nil, vars_nil, forall_true_left] },
  { intro h,
    simp only [eval_cons],
    rw eval_eq_of_eqod_of_var_mem h (mem_vars_of_mem (mem_cons_self l ls)),
    rw ih (eqod_subset (vars_subset_of_vars_cons l ls) h) }
end

end assignment