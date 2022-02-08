/-
This file defines and proves the equisatisfiability of the direct (or naive)
encoding for the n-variable XOR gate.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import cnf.literal
import cnf.assignment
import cnf.clause
import cnf.cnf
import xor.xor
import basic

import data.list.basic
import data.nat.basic

universe u

-- Represents the parametric type of the variable stored in the literal
variables {V : Type u} [decidable_eq V] [inhabited V]

namespace nxor

open literal
open clause -- TODO opening clause doesn't seem to open library...
open cnf
open list
open nxor
open explode
open nat

/-! # Direct encoding -/
section direct_encoding

variables {g : nxor V} {c : clause V}

/- The direct encoding is the set of all possible clauses with an even number 
   of negations on the provided literals in a single CNF formula. -/
def direct_xor : nxor V → cnf V
| []        := [[]]
| (l :: ls) := (explode (map var ls)).map 
      (λ c, ite (!bodd (c.count_flips ls)) (l :: c) (l.flip :: c))

@[simp] theorem direct_xor_nil : direct_xor ([] : nxor V) = [[]] := rfl

@[simp] theorem direct_xor_singleton (l : literal V) : direct_xor [l] = [[l]] :=
by simp [direct_xor]

theorem mem_explode_of_mem_direct_xor : 
  c ∈ direct_xor g → c ∈ explode (map var g) :=
begin
  cases g with l ls,
  { simp only [explode_nil, imp_self, direct_xor_nil, map_nil] },
  { simp [direct_xor, explode],
    intros cl hcl,
    cases l,
    { cases (bodd (cl.count_flips ls)),
      { simp, intro h, use [cl, hcl, h] },
      { simp, intro h, unfold literal.flip at h, 
        right, use [cl, hcl, h] } },
    { cases (bodd (cl.count_flips ls)),
      { simp, intro h, right, use [cl, hcl, h] },
      { simp, intro h, unfold literal.flip at h,
        use [cl, hcl, h] } } }
end

theorem length_direct_xor : g ≠ [] → length (direct_xor g) = 2^(length g - 1) :=
begin
  cases g,
  { contradiction },
  { simp only [direct_xor, length_explode, add_zero, length, add_succ_sub_one, 
      ne.def, forall_true_left, not_false_iff, length_map] }
end

theorem length_direct_xor_pos : g ≠ [] → length (direct_xor g) > 0 :=
assume h, by simp only [length_direct_xor h, succ_pos', gt_iff_lt, pow_pos]

theorem exists_mem_direct_xor (g : nxor V) : 
  ∃ (c : clause V), c ∈ direct_xor g :=
begin
  cases g with l ls,
  { use [nil, mem_singleton_self nil] },
  { exact exists_mem_of_length_pos (length_direct_xor_pos (cons_ne_nil l ls)) }
end

-- These theorems begin to be dependent on order of encoding
-- If the underlying type of nxor changes to (fin)set, must update
theorem map_var_eq_of_mem_direct_xor :
  c ∈ direct_xor g → map var c = map var g :=
begin
  cases g with l ls,
  { simp only [direct_xor, imp_self, map_eq_nil, map_nil, mem_singleton] },
  { simp [direct_xor],
    intros c hc,
    cases (bodd (c.count_flips ls)),
    { simp only [if_true, eq_self_iff_true],
      rintro rfl,
      simp [map_var_eq_iff_mem_explode.mpr hc] },
    { simp only [if_false],
      rintro rfl,
      simp [map_var_eq_iff_mem_explode.mpr hc, flip_var_eq] } }
end

theorem even_flips_iff_mem_direct_xor_of_map_var_eq : map var c = map var g → 
  (bodd (c.count_flips g) = ff ↔ c ∈ direct_xor g) :=
begin
  intro hc, split,
  { cases g with l ls,
    { revert hc, simp },
    { simp only [direct_xor, map_cons, bool.cond_to_bool, mem_map],
      intro hf,
      rcases exists_cons_of_map_cons hc with ⟨x, xs, rfl, hx, hxs⟩,
      use xs, split,
      { exact map_var_eq_iff_mem_explode.mp hxs },
      { cases h : (bodd (clause.count_flips xs ls)),
        { rcases var_eq_iff_eq_or_flip_eq.mp hx with rfl | hx,
          { simp only [if_true, coe_sort_tt, bool.bnot_false] },
          { simp [clause.count_flips, hx] at hf,
            rw h at hf, contradiction } },
        { rcases var_eq_iff_eq_or_flip_eq.mp hx with hx | rfl,
          { simp [clause.count_flips, hx] at hf,
            rw h at hf, contradiction },
          { simp only [flip_flip, if_false, bool.bnot_true, coe_sort_ff]} } } } },
  { cases g with l ls,
    { simp },
    { simp only [direct_xor, bool.cond_to_bool, mem_map],
      rintro ⟨a, ha, hf⟩,
      rcases exists_cons_of_map_cons hc with ⟨x, xs, rfl, hx, hxs⟩,
      cases h : (nat.bodd (a.count_flips ls));
      { simp only [h, if_true, eq_self_iff_true, if_false] at hf,
        simp [← hf, clause.count_flips, literal.is_neg, 
          bool.to_nat, h, flip_flip _, flip_ne] } } }      
end

theorem odd_flips_iff_not_mem_direct_xor_of_map_var_eq : map var c = map var g → 
  (bodd (c.count_flips g) = tt ↔ c ∉ direct_xor g) :=
begin
  intro hc, split,
  { intro hcount, by_contradiction,
    rw (even_flips_iff_mem_direct_xor_of_map_var_eq hc).mpr h at hcount,
    contradiction },
  { contrapose, simp only [eq_ff_eq_not_eq_tt, not_not],
    exact (even_flips_iff_mem_direct_xor_of_map_var_eq hc).mp }
end

theorem mem_direct_xor_self (g : nxor V) : g ∈ (direct_xor g) :=
begin
  have hcount := clause.count_flips_self g,
  have := nat.bodd_zero,
  rw ← hcount at this,
  exact (even_flips_iff_mem_direct_xor_of_map_var_eq (refl _)).mp this
end

-- Some proofs require the stronger statement that direct is exactly xor
theorem eval_direct_xor_eq_eval_nxor (g : nxor V) (τ : assignment V) :
  (direct_xor g).eval τ = g.eval τ :=
begin
  cases g with l ls,
  { simp only [cnf.eval_singleton, eval_nil, direct_xor_nil, clause.eval_nil] },
  { have he := eval_eq_bodd_count_tt τ (l :: ls),
    cases h : (nxor.eval τ (l :: ls)),
    { apply eval_ff_iff_exists_clause_eval_ff.mpr,
      use (clause.falsify τ (map var (l :: ls))),
      split,
      { rw [← clause.count_flips_falsify_eq_count_tt τ (l :: ls),
            clause.count_flips_comm] at he,
        apply (even_flips_iff_mem_direct_xor_of_map_var_eq 
          (clause.falsify_map_var_eq τ (map var (l :: ls)))).mp,
        rw ← h,
        exact he.symm },
      { exact clause.falsify_eval_ff τ (map var (l :: ls)) } },
    { rw h at he,
      apply eval_tt_iff_forall_clause_eval_tt.mpr,
      intros c hc,
      have mve := map_var_eq_of_mem_direct_xor hc,
      have neqodd := ne_of_eq_ff_of_eq_tt
        ((even_flips_iff_mem_direct_xor_of_map_var_eq mve).mpr hc) he.symm,
      have neq := ne_of_apply_ne nat.bodd neqodd,
      rw clause.count_flips_comm at neq,
      exact clause.eval_tt_of_ne_flips mve.symm (ne.symm neq) } }
end

theorem vars_direct_xor (g : nxor V) : (direct_xor g).vars = g.vars :=
begin
  cases g with l ls,
  { simp only [cnf.vars_singleton, direct_xor_nil, vars_nil, clause.vars_nil] },
  { rw finset.ext_iff,
    intro v,
    split,
    { intro hv,
      rcases mem_vars_iff_exists_mem_clause_and_mem.mp hv with ⟨c, hc⟩,
      rw [vars, clause.mem_vars_iff_mem_map_vars],
      rw ← (map_var_eq_of_mem_direct_xor hc.1),
      exact clause.mem_vars_iff_mem_map_vars.mp hc.2 },
    { intro hv,
      apply mem_vars_iff_exists_mem_clause_and_mem.mpr,
      use (l :: ls),
      exact ⟨mem_direct_xor_self _, hv⟩ } }
end

end direct_encoding

end nxor