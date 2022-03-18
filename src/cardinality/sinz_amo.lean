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

namespace sinz_amo

open list
open literal
open clause
open cnf
open assignment
open encoding
open distinct
open gensym

variables {l : list (literal V)} {lit lit₁ lit₂ : literal V} {g : gensym V}
          {τ : assignment V} (hdis : disjoint g.stock (clause.vars l))

lemma disjoint_fresh_of_disjoint : disjoint g.stock (clause.vars (lit :: l)) → 
  disjoint (g.fresh.2.stock) (clause.vars l) :=
begin
  sorry
end

def sinz_helper : Π (l : list (literal V)), Π (g : gensym V),
  (disjoint g.stock (clause.vars l)) → cnf V
| []               _ _            := []
| [l₁]             g hdis         := [[l₁.flip, Pos (g.fresh.1)]]
| (l₁ :: l₂ :: ls) g hdis         := 
    [l₁.flip, Pos (g.fresh.1)] :: 
    [Neg g.fresh.1, Pos g.fresh.2.fresh.1] ::
    [Neg g.fresh.1, l₂.flip] ::
    (sinz_helper (l₂ :: ls) g.fresh.2 (disjoint_fresh_of_disjoint hdis))

def sinz : Π (l : list (literal V)), Π (g : gensym V),
  (disjoint g.stock (clause.vars l)) → cnf V
| []   _ _    := []
| [l₁] _ _    := []
| l    g hdis := sinz_helper l g hdis

-- TODO: helper and sinz or one function and just prove theorems for lists of
-- at least 2 elements?

/-
def sinz_alt2 : Π (l : list (literal V)), Π (g : gensym V),
  (disjoint g.stock (clause.vars l)) → cnf V
| []   _ _    := []
| [l₁] _ _    := []
| l    g hdis := (foldr (++) [] (map (λ (p : (nat × literal V)), 
                  if p.1 = length l - 1 then [[p.2]] else [[p.2]]) (enum l)))
-/

/-
lemma eval_tt_cons_of_eval_tt_of_neg (hdis : disjoint g.stock (clause.vars (lit :: l))) : 
  (sinz_helper l g.fresh.2 (disjoint_fresh_of_disjoint hdis) [g.fresh.1])
  -/

-- Really an iff relation, but one way is fine for now?
theorem exists_signal_mem_of_mem_of_length_ge_two : length l ≥ 2 → lit ∈ l → 
  ∃ {s : V}, s ∈ g.stock ∧ [lit.flip, Pos s] ∈ sinz l g hdis :=
begin
  intros hl hmem,
  induction l with l₁ ls ih generalizing g,
  { exact absurd hmem (not_mem_nil _) },
  { cases ls with l₂ ls,
    { simp [length] at hl, linarith },
    { rcases eq_or_mem_of_mem_cons hmem with (rfl | h),
      { use g.fresh.1,
        rw [sinz, sinz_helper],
        exact ⟨fresh_mem_stock g, mem_cons_self _ _⟩ },
      { cases ls with l₃ ls,
        { simp at h,
          use g.fresh.2.fresh.1,
          split, { exact fresh_fresh_mem_stock g },
          rw [sinz, sinz_helper, sinz_helper],
          simp [h] },
        { have : length (l₂ :: l₃ :: ls) ≥ 2,
          { simp, linarith },
          rcases ih this h (disjoint_fresh_of_disjoint hdis) with ⟨s, hs, hc⟩,
          rw sinz at hc |-,
          rw sinz_helper,
          use s, split,
          { exact fresh_stock_subset g hs },
          { simp [hc] } } } } }
end

theorem all_ff_eval_tt : length l ≥ 2 → (sinz_helper l g hdis).eval all_ff = tt :=
begin
  induction l with l₁ ls ih,
  { intro hlen, rw length at hlen, linarith },
  { intro hlen,
    cases ls with l₂ ls,
    { simp [length] at hlen, linarith},
    { cases ls with l₃ ls,
      {
        simp [eval_tt_iff_forall_clause_eval_tt, sinz_helper],
      } 
    }
  }
end

theorem ne_of_distinct_of_length_ge_two {s₁ s₂ : V} : length l ≥ 2 → distinct lit₁ lit₂ l →
  s₁ ∈ g.stock → s₂ ∈ g.stock → [lit₁.flip, Pos s₁] ∈ sinz l g hdis →
  [lit₂.flip, Pos s₂] ∈ sinz l g hdis → s₁ ≠ s₂ :=
begin
  intros hl hd hs₁ hs₂ hmem₁ hmem₂,
  induction l with l₁ ls ih,
  { exact absurd hd (not_distinct_nil _ _) },
  { cases ls with l₂ ls,
    { exact absurd hd (not_distinct_singleton _ _ _) },
    { cases ls with l₃ ls,
      { 

      }

    }
  }
end

lemma eval_tt_iff_distinct_eval_ff_of_eval_tt :
  (sinz l g hdis).eval τ = tt ↔ (∀ {lit₁ lit₂ : literal V},
  distinct lit₁ lit₂ l → lit₁.eval τ = tt → lit₂.eval τ = ff) :=
begin
  induction l with l₁ ls ih generalizing g,
  { split,
    { intros _ lit₁ lit₂ hd, exact absurd hd (not_distinct_nil _ _) },
    { rw [sinz, cnf.eval_nil], tautology } },
  { cases ls with l₂ ls,
    { split,
      { intros _ lit₁ lit₂ hd, exact absurd hd (not_distinct_singleton _ _ _) },
      { rw [sinz, cnf.eval_nil], tautology } },
    { split,
      {
        intros heval lit₁ lit₂ hd h₁,
        sorry,
      },
      {
        sorry
      } } }
end

theorem sinz_encodes_amo {l : list (literal V)} {g : gensym V} (hdis : disjoint g.stock (clause.vars l)) :
  encodes amo (sinz l g hdis) l :=
begin
  induction l using strong_induction_on_lists with l ih generalizing g,
  intro τ,
  cases l with l₁ ls,
  { simp [sinz] },
  { cases ls with l₂ ls,
    { simp [sinz], use τ },
    { cases ls with l₃ ls,
      { split,
        { simp [← amo.eval, sinz, sinz_helper, eval_tt_iff_forall_clause_eval_tt],
          intro heval,
          cases h₁ : (literal.eval τ l₁),
          { use [assignment.ite (clause.vars [l₁, l₂]) τ all_ff],
            split,
            {
              have hmem₁ : l₁.flip.var ∈ clause.vars [l₁, l₂],
              { simp [flip_var_eq, clause.vars] },
              have hmem₂ : l₂.flip.var ∈ clause.vars [l₁, l₂],
              { simp [flip_var_eq, clause.vars] },
              have hnmem₁ : g.fresh.1 ∉ clause.vars [l₁, l₂],
              { have := set.disjoint_left.mp hdis (fresh_mem_stock g),
                assumption }, -- TODO coercion is silly
              have hnmem₂ : g.fresh.2.fresh.1 ∉ clause.vars [l₁, l₂],
              { have := fresh_mem_stock g.fresh.2,
                have := set.disjoint_left.mp hdis (fresh_stock_subset g this),
                assumption }, -- TODO this too
              simp [eval_tt_iff_exists_literal_eval_tt, literal.eval],
              split,
              { use [l₁.flip],
                rw ite_pos_lit τ all_ff hmem₁,
                simp [eval_flip, h₁] },
              { split,
                { use [Neg g.fresh.1],
                  simp [literal.eval],
                  rw ite_neg τ all_ff hnmem₁,
                  refl },
                { split,
                  { use [Neg g.fresh.1],
                    simp [literal.eval],
                    rw ite_neg τ all_ff hnmem₁,
                    refl },
                  {

                  }

                }

              }
            },
            { exact (ite_eqod τ all_ff (clause.vars [l₁, l₂])).symm }
          }
        }
      },
      
      have hlen : length (l₂ :: ls) < length (l₁ :: l₂ :: ls), simp,
      have ihred := ih (l₂ :: ls) hlen (disjoint_fresh_of_disjoint hdis) τ,
      split,
      { intro hamo,
        rw ← amo.eval at hamo,
        have := amo.eval_tt_of_eval_tt_cons hamo,
        rcases ihred.mp this with ⟨σ, heval', heqod'⟩,
        use assignment.ite (clause.vars (l₁ :: l₂ :: ls)) τ σ,
        split,
        {
          sorry,
        },
        { exact (ite_eqod τ σ (clause.vars (l₁ :: l₂ :: ls))).symm } },
      {
        rintros ⟨σ, heval, heqod⟩,
        rw ← amo.eval,
        rw amo.amo_eval_tt_iff_distinct_eval_ff_of_eval_tt,
        intros lit₁ lit₂ hd h₁,

        rw eval_tt_iff_forall_clause_eval_tt at heval,
        rw [sinz, sinz_helper] at heval,
        simp at heval,
        rcases heval with ⟨c₁, c₂, c₃, hp⟩,
        rw [← eval_tt_iff_forall_clause_eval_tt] at hp,


        rcases hd with ⟨i, j, hi, hj, hij, hil, hjl⟩,
        cases i,
        {

        }
       -- have := (eval_tt_iff_distinct_eval_ff_of_eval_tt hdis).mp heval,

        --rw [eval_tt_iff_forall_clause_eval_tt, sinz, sinz_helper] at heval,
        --have : ∃ (σ : assignment V), cnf.eval σ (sinz (l₂ :: ls) g.fresh.2 
        --  (disjoint_fresh_of_disjoint hdis)) = tt ∧ (τ ≡clause.vars (l₂ :: ls)≡ σ),
      } } }
end

end sinz_amo