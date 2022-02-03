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
def nxor (V : Type u) := list (literal V)

-- Not to be confused with the XNOR gate
-- See the note in cnf/clause.lean for discussion of list vs. set typing

namespace nxor

open nat
open list
open clause

/-! # Properties -/

instance : inhabited (clause V) := ⟨[arbitrary (literal V)]⟩
instance : has_append (nxor V) := ⟨list.append⟩
instance : has_mem (literal V) (nxor V) := ⟨list.mem⟩

/-! # eval -/
section eval

variables (α : assignment V) (g : nxor V) (l : literal V)

/- Evaluate the variables under the assignment according to typical XOR -/
protected def eval : bool :=
  g.foldr (λ l b, b ⊕ l.eval α) ff

@[simp] theorem eval_nil : nxor.eval α [] = ff := rfl

@[simp] theorem eval_singleton : nxor.eval α [l] = l.eval α :=
by simp only [nxor.eval, bool.bxor_ff_left, foldr]

theorem eval_cons : nxor.eval α (l :: g) = bxor (l.eval α) (g.eval α) :=
by simp only [nxor.eval, foldr, bool.bxor_comm]

theorem eval_append (g₁ g₂ : nxor V) : 
  nxor.eval α (g₁ ++ g₂) = bxor (g₁.eval α) (g₂.eval α) :=
begin
  induction g₁ with l ls ih,
  { simp only [bool.bxor_ff_left, eval_nil, nil_append] },
  { simp only [eval_cons, ih, cons_append, bool.bxor_assoc] }
end

/- Evaluates to true if an odd number of literals evaluates to true -/
theorem eval_eq_bodd_count_tt : g.eval α = bodd (clause.count_tt α g) :=
begin
  induction g with l ls ih,
  { simp only [bodd_zero, eval_nil, count_tt_nil] },
  { cases h : (l.eval α);
    { simp [nxor.eval_cons, count_tt_cons, h, ih] } }
end

end eval

/-! # vars -/
section vars

variables {g : nxor V} {l : literal V} {v : V}

/- For now, since the implementation of clause and nxor are the same,
   using clause.lean's version of vars saves on space for redundant theorems.
   If the implementation of clause or nxor changes, this definition will
   need to be updated accordingly. -/
def vars (g : nxor V) : finset V := clause.vars g

@[simp] theorem vars_nil : nxor.vars ([] : nxor V) = ∅ := rfl

@[simp] theorem vars_singleton (l : literal V) : nxor.vars [l] = {l.var} :=
clause.vars_singleton l

theorem mem_vars_cons_of_mem_vars : v ∈ g.vars → v ∈ nxor.vars (l :: g) :=
clause.mem_vars_cons_of_mem_vars l

theorem mem_vars_of_mem : l ∈ g → l.var ∈ g.vars :=
clause.mem_vars_of_mem

theorem vars_subset_of_vars_cons (l : literal V) (g : nxor V) :
  g.vars ⊆ nxor.vars (l :: g) :=
finset.subset_union_right _ _

-- Other theorems from clause.vars possible, if needed

end vars

end nxor

/-! # eqod for nxor -/

namespace assignment

open list
open nxor

theorem eval_eq_nxor_of_eqod {α₁ α₂ : assignment V} {g : nxor V} :
  (α₁ ≡g.vars≡ α₂) → g.eval α₁ = g.eval α₂ :=
begin
  induction g with l ls ih,
  { simp only [eqod_nil, eval_nil, vars_nil, forall_true_left] },
  { intro h,
    simp only [eval_cons],
    rw eval_eq_of_eqod_of_var_mem h (mem_vars_of_mem (mem_cons_self l ls)),
    rw ih (eqod_subset (vars_subset_of_vars_cons l ls) h) }
end

end assignment