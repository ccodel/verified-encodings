/-
The Sinz at-most-one encoding.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import cnf.literal
import cnf.clause
import cnf.cnf
import cnf.encoding
import cnf.gensym

import cardinality.distinct
import cardinality.cardinality

import data.list.basic
import data.nat.basic

variables {V : Type*} [inhabited V] [decidable_eq V]

namespace sinz_amk

open list
open literal
open clause
open cnf
open assignment
open encoding
--open distinct
open gensym
--open amo

variables {l : list (literal V)} {lit l₁ l₂ : literal V} {g : gensym V}
          {τ : assignment V} (hdis : disjoint g.stock (clause.vars l))
          {c : clause V}
          {k : nat} (hk : k ≥ 2)

-- Not true, refine later
lemma a1 {k : nat} : k ≥ 2 → ∀ m, m < k :=
begin
  sorry
end

lemma a2 {k : nat} {l : list V} : k ≥ 2 → length l = k → length l ≥ 2 :=
begin
  sorry
end

lemma disjoint_fresh_of_disjoint : disjoint g.stock (clause.vars (lit :: l)) → 
  disjoint (g.nfresh k).2.stock (clause.vars l) :=
begin
  sorry
end

def sinz_k {k : nat} (hk : k ≥ 2) : Π (l : list (literal V)), Π (g : gensym V),
  (disjoint g.stock (clause.vars l)) → cnf V
| [] _ _ := []
| [l₁] _ _ := [] -- [l₁.flip, Neg (g.prev)]
| (l₁ :: l₂ :: ls) g hdis :=
  --let ⟨ss, g'⟩ := g.nfresh k in
  have hlen₁ : length (g.nfresh k).1 ≥ 2, from a2 hk (length_list_nfresh g k),
  have hlen₂ : length ((g.nfresh k).2.nfresh k).1 ≥ 2, 
    from a2 hk (length_list_nfresh (g.nfresh k).2 k),
  -- x_i → s_(i, 1)
  [l₁.flip, Pos (nth_le (g.nfresh k).1 0 (a1 hlen₁ _))] ::

  -- x_(i + 1) → ¬s_(i, k)
  [l₂.flip, Neg (nth_le (g.nfresh k).1 (k - 1) (a1 hlen₁ _))] ::

  -- s_(i, j) → s_(i + 1, j)
  (map (λ p : (nat × V), let ⟨i, s⟩ := p in 
      [Neg s,
       Pos (nth_le ((g.nfresh k).2.nfresh k).1 i (a1 hlen₂ _))])
    (enum (g.nfresh k).1))
  ++
  (map (λ p : (nat × V), let ⟨i, s⟩ := p in
      [l₂.flip, Neg s, Pos (nth_le ((g.nfresh k).2.nfresh k).1 (i + 1) (a1 hlen₂ _))])
      (enum (take (k - 1) (g.nfresh k).1)))
  ++
  sinz_k (l₂ :: ls) (g.nfresh k).2 (disjoint_fresh_of_disjoint hdis)

def sinz {k : nat} (hk : k ≥ 2) : Π (l : list (literal V)), Π (g : gensym V),
  (disjoint g.stock (clause.vars l)) → cnf V
| l g hdis := (sinz_k hk l g hdis) ++ 
              -- ¬s_(1, j) for j > 1
              map (λ s, [Neg s]) (g.nfresh k).1.tail

/-
    [l₁.flip, Pos (g.fresh.1)] :: 
    [Neg g.fresh.1, Pos g.fresh.2.fresh.1] ::
    [Neg g.fresh.1, l₂.flip] ::
    (sinz (l₂ :: ls) g.fresh.2 (disjoint_fresh_of_disjoint hdis))
-/

end sinz_amk