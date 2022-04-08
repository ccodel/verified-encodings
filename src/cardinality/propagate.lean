/-

Experiments with propagation structures.

Author: Cayden Codel
-/

import data.list.basic
import cnf.cnf
import cnf.gensym
import cnf.encoding
import cardinality.distinct
import cardinality.cardinality

variables {V : Type*} [inhabited V] [decidable_eq V]

namespace propagate

open list
open literal
open cnf
open clause
open assignment
open distinct
open prod
open gensym
open encoding
open amk

def propagate : list (literal V) → cnf V
| []               := []
| [l₁]             := []
| (l₁ :: l₂ :: ls) := [l₁.flip, l₂] :: propagate (l₂ :: ls)

@[simp] theorem propagate_nil : propagate ([] : list (literal V)) = [] := rfl

@[simp] theorem propagate_singleton : ∀ (l : literal V), propagate [l] = [] :=
assume l, rfl

theorem propagate_truth {τ : assignment V} {l : list (literal V)} {l₁ l₂ : literal V} : 
  (propagate l).eval τ = tt → distinct l₁ l₂ l → l₁.eval τ = tt → l₂.eval τ = tt :=
begin
  intros hp hdis h₁,
  induction l with x₁ ls ih generalizing l₁,
  { exact absurd hdis (not_distinct_nil _ _) },
  { cases ls with x₂ ls,
    { exact absurd hdis (not_distinct_singleton _ _ _) },
    { cases ls with x₃ ls,
      { rcases eq_of_distinct_double hdis with ⟨rfl, rfl⟩,
        simp [propagate, clause.eval_cons, eval_flip, h₁] at hp,
        exact hp },
      { rw propagate at hp,
        simp [cnf.eval_cons] at hp,
        rcases hp with ⟨hp₁, hp₂⟩,
        rcases eq_or_distinct_of_distinct_cons hdis with (rfl | h),
        { simp [clause.eval_cons, eval_flip, h₁] at hp₁,
          rcases eq_or_mem_of_mem_cons (mem_tail_of_distinct_cons hdis)
            with (rfl | h₂),
          { exact hp₁ },
          { exact ih hp₂ (distinct_cons_of_mem x₂ h₂) hp₁ } },
        { exact ih hp₂ h h₁ } } } }
end

def zipped_propagate (l : list (list (literal V) × literal V)) : cnf V :=
l.map (λ p, ((fst p).map (literal.flip)) ++ [snd p])

theorem zipped_propagate_truth {τ : assignment V} 
  {l : list (list (literal V) × literal V)} :
  (zipped_propagate l).eval τ = tt ↔ 
  (∀ p ∈ l, ((∀ (lit : literal V), lit ∈ (fst p) → lit.eval τ = tt) → (snd p).eval τ = tt)) :=
begin
  induction l with l ls ih,
  { simp [zipped_propagate] },
  { sorry }
end

def sinz_amkv2 (k : nat) {g : gensym V} {l : list (literal V)} 
  (hdis : disjoint g.stock (clause.vars l)) (hnil : l ≠ []) : cnf V :=

-- A (k + 1) x n matrix where the (i, j) is s_{i, j} corresponding to x_i and counter (j + 1)
--
let S : (nat → nat → V) := λ r c, g.nth ((r * length l) + c) in

-- A single unit clause for the (k + 1)th counter variable for x_n
[Neg (S k (length l))] ::

-- For each of the (k + 1) rows, take the row and encode propagation forward
-- Flatten the propagate results for each row
(foldl (λ l₁ l₂, l₁ ++ l₂) ([] : cnf V) 
  -- Take each row (k + 1 rows, each with length n)
  ((range (k + 1)).map (λ i, 
    -- Generate clauses that propagate truth of same counter signal variables
    propagate ((range (length l)).map (λ j, Pos (S i j)))))) ++

-- Take each x_i and make x_i => s_{i, 1}
l.map_with_index (λ i x, [x.flip, Pos (S 0 i)]) ++

-- For each signal variable not on the first row or column, 
-- make (x_{i} ^ s_{i - 1, j - 1} => s_{i, j})
(foldl (λ l₁ l₂, l₁ ++ l₂) ([] : cnf V) 
  (l.tail.map_with_index (λ i x, 
    (range k).map (λ j, 
      [x.flip, Neg (S j i), Pos (S (j + 1) (i + 1))]))))

theorem enc (k : nat) {g : gensym V} {l : list (literal V)}
  (hdis : disjoint g.stock (clause.vars l)) (hnil : l ≠ []) : 
  encodes (amk k) (sinz_amkv2 k hdis hnil) l :=
begin
  intro τ,
  induction k with k ih,
  split,
  { intro hamk,
    use assignment.ite (clause.vars l) τ all_ff,
    split,
    { 
      rw sinz_amkv2,
      rw eval_tt_iff_forall_clause_eval_tt,
      simp,
      split,
      { have := set.disjoint_left.mp hdis (nth_mem_stock g l.length),
        rw [literal.eval, ite_neg this, all_ff_eval_ff],
        refl },
      {
        intros c hc,
        rcases hc with (hc | hc | hc),
        { simp [range, range_core] at hc,
          sorry -- by facts of propogate, can always find one!
        },
        {
          
        }
      }
    },
    { exact (ite_eqod (clause.vars l) τ all_ff).symm } }
end

end propagate