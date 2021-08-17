/-
This file contains the definitions of and basic operations on variables, literals,
clauses, and conjunctive normal form.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

-- TODO: by_cases can often replace classical.em (a = b), etc.
-- TODO: Use variables to clean up theorem definitions, etc.

import basic
import cnf.literal
import cnf.clause

import data.list.basic
import data.list.nodup
import data.list.perm
import init.data.nat
import data.nat.basic

/- Conjunctive normal form is a list of clauses joined by logical ANDs -/
def cnf := list clause

namespace cnf

open literal
open clause
open list

/- Instance properties -/
instance : inhabited cnf := ⟨[default clause]⟩

instance : has_mem clause cnf := ⟨list.mem⟩

instance : has_emptyc cnf := ⟨list.nil⟩

instance : has_union cnf := ⟨list.union⟩

instance : has_inter cnf := ⟨list.inter⟩

instance : has_singleton clause cnf := ⟨λ c, [c]⟩ 

instance : has_insert clause cnf := ⟨list.insert⟩

instance : has_append cnf := ⟨list.append⟩

/-! # sim_erase -/
-- If we only care about evaluations, we can weaken the erase operation to removing similar clauses only
-- See clause.eval_sim for motivation

def sim_erase : cnf → clause → cnf
| []          c := []
| (cl :: cls) c := if cl ~ c then cls else cl :: sim_erase cls c

-- Technically, sim_erase "inherits" a lot of functionality from erase, as it is weaker
-- We reproduce only a few results here
@[simp] theorem sim_erase_nil {c : clause} : sim_erase [] c = [] := rfl

@[simp] theorem sim_erase_cons_head {c₁ c₂ : clause} {f : cnf} (h : c₁ ~ c₂) : sim_erase (c₁ :: f) c₂ = f :=
by simp [sim_erase, h]

theorem sim_erase_cons_tail {c₁ c₂ : clause} {f : cnf} (h : ¬(c₁ ~ c₂)) : sim_erase (c₁ :: f) c₂ = c₁ :: (sim_erase f c₂) :=
by simp [sim_erase, h]

theorem sim_erase_of_not_sim {c : clause} {f : cnf} (h : ∀ cl ∈ f, ¬(cl ~ c)) : sim_erase f c = f :=
begin
  induction f with cl cls ih,
  { simp [sim_erase_nil] },
  { simp [h cl (mem_cons_self cl cls), sim_erase], simp at h, simp [ih h.2] } -- TODO tighten up?
end

/-
by { induction f with cl cls ih, { exact sim_erase_nil },
  unfold sim_erase, have : ¬ cl ~ c, from h cl (mem_cons_self cl cls), simp [this], }
  -/

/-! ### Eval -/

/- The clauses of the CNF are joined by conjunctions, so all must evaluate to true -/
def eval (α : assignment) (f : cnf) : bool :=
  f.foldr (λ c, λ b, b && (c.eval α)) tt

@[simp] theorem eval_nil {α : assignment} : eval α [] = tt := rfl

@[simp] theorem eval_singleton {α : assignment} {c : clause} : eval α [c] = clause.eval α c := by simp [eval]

theorem eval_cons {α : assignment} {c : clause} {f : cnf} : eval α (c :: f) = (clause.eval α c && eval α f) :=
  by simp [eval, bool.band_comm]

/-
theorem eval_double {α : assignment} {c : clause} {f : cnf} (hin : c ∈ f) : c ∈ (f.erase c) → eval α f = eval α (f.erase c) :=
begin
  induction f with cl cls ih,
  { exact absurd hin (not_mem_nil _) },
  intro he,

end
-/

/-
theorem eval_erase_equiv_eval_sim_erase {α : assignment} {c : clause} {f : cnf} (hin : c ∈ f) : ∀ (cl : clause), cl ~ c → eval α (f.erase c) = eval α (f.sim_erase c) :=
begin
  induction f with cl cls ih,
  { exact absurd hin (not_mem_nil _) },
  intros clsim hclsim,
  by_cases (cl = c),
  { simp [erase_cons_head, sim_erase, h, perm.refl] },
  { by_cases (cl ~ c),
    { }
    --have ihred := ih (mem_of_ne_of_mem h hin) clsim hclsim,
    --rw erase_cons_tail cls (ne.symm h),
    --by_cases (c ~ cl),
    --{ simp [ihred, eval_cons, sim_erase, h.symm], }
    --simp [ihred, eval_cons, sim_erase],
   }
end
-/

/-
theorem eval_erase_of_mem {α : assignment} {c : clause} {f : cnf} (h : c ∈ f) : eval α f = (clause.eval α c) && (eval α (f.erase c)) :=
begin
  /-
    induction c with d ds ih,
  { exact absurd h (not_mem_nil _) },
  rcases classical.em (l = d) with rfl | hne,
  { simp [erase_cons_head, eval_cons] },
  { simp only [eval_cons, erase_cons_tail ds (ne.symm hne), ih (mem_of_ne_of_mem hne h), ← bool.bor_assoc, bool.bor_comm] }
  -/

  induction f with cl cls ih,
  { exact absurd h (not_mem_nil _) },
  cases classical.em (c ~ cl),
  
end 
-/

/-! ### Counting -/

/- Counts the number of clauses which evaluate to true under some assignment -/
def count_tt (α : assignment) (f : cnf) : nat :=
  length $ f.filter (λ c, c.eval α = tt)

/- Counts the number of clauses which evaluate to false under some assignment -/
def count_ff (α : assignment) (f : cnf) : nat :=
  length $ f.filter (λ c, c.eval α = ff)

end cnf

/- Sometimes, it is necessary to get all possible disjunctive clauses from a set of variables -/
/- For lack of a better name, we call that operation "exploding" -/
namespace explode

open literal
open clause
open list

/- This should ideally take in a nodup list or a finset, but lists are easier to manipulate -/
/- Also, should ideally return a nodup list or a finset, see above comment -/
-- Here is a non-recursive definition of expl. Recursive is easier though...
def explode_non_rec (l : list nat) : list clause :=
  l.foldr (λ n, λ ls, (ls.map (λ e, (Pos n) :: e)) ++ (ls.map (λ e, (Neg n) :: e))) [[]]

@[simp] lemma explode_non_rec_nil : explode_non_rec [] = [[]] := rfl

@[simp] lemma explode_non_rec_cons {n : nat} {ns : list nat} : 
  explode_non_rec (n :: ns) = (explode_non_rec ns).map (λ e, (Pos n) :: e) ++ (explode_non_rec ns).map (λ e, (Neg n) :: e) :=
    by simp [explode_non_rec]

/- Note: The nil case differs between the two. See if can fix above... -/
def explode : list nat → list clause 
  | []        := [[]]
  | (n :: ns) := (explode ns).map (cons (Pos n)) ++ (explode ns).map (cons (Neg n))

-- Saying they're equal is a little dangerous - maybe saying they're similar is good enough?
theorem explode_and_explode_rec_equiv {ns : list nat} : explode_non_rec ns = explode ns :=
begin
  induction ns with m ms ih,
  { simp [explode] },
  { simp [explode, ih] }
end

theorem length_explode : ∀ (ns : list nat), length (explode ns) = 2^(length ns)
| []        := rfl
| (n :: ns) := by {
  unfold explode,
  unfold length,
  rw pow_succ,
  rw two_mul,
  rw length_append,
  repeat {rw length_map},
  rw length_explode ns,
}
-- by simp [explode, length_explode ns, pow_succ, two_mul]
-- was getting replace and stack space errors, so wrote out long-hand

-- Corollary of the above theorem
-- Can probably be reduced in length
theorem length_explode_pos {ns : list nat} : length (explode ns) > 0 :=
begin
  rw length_explode ns,
  induction ns with d hd,
  { unfold length, simp },
  { unfold length,
    rw pow_succ,
    rw two_mul,
    exact add_pos (ns_ih) (ns_ih)}
end

-- Another corollary - is this needed?
theorem exists_mem_of_explode : ∀ (ns : list nat), ∃ (c : clause), c ∈ explode ns :=
  λ _, exists_mem_of_length_pos length_explode_pos

theorem length_clause_explode {ns : list nat} : ∀ (c : clause), c ∈ explode ns → length c = length ns :=
begin
  induction ns with m ms ih,
  { intros c h, unfold explode at h, rw (mem_singleton.mp h), refl},
  simp only [explode, mem_cons_iff, mem_append, map_cons, mem_map],
  rintros c (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩);
  { unfold length, rw ih c hc}
end

theorem mem_explode_of_mem {ns : list nat} : ∀ n ∈ ns, ∀ c ∈ explode ns, Pos n ∈ c ∨ Neg n ∈ c :=
begin
  induction ns with m ms ih,
  { intros m hm, exact absurd hm (not_mem_nil _) },
  simp only [explode, mem_cons_iff, mem_append, map_cons, mem_map],
  rintros n (rfl | hn) c (⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩),
  { left, apply mem_cons_self },
  { right, apply mem_cons_self },
  { cases ih n hn d hd with h h,
    { left, apply mem_cons_of_mem _ h},
    right, apply mem_cons_of_mem _ h},
  { cases ih n hn d hd with h h,
    { left, apply mem_cons_of_mem _ h},
    right, apply mem_cons_of_mem _ h},
end

theorem not_mem_explode_of_not_mem {ns : list nat} : ∀ n ∉ ns, ∀ c ∈ explode ns, Pos n ∉ c ∧ Neg n ∉ c :=
begin
  induction ns with m ms ih,
  { rintros m hm c hc,
    simp [explode, hc] at hc,
    simp [hc]},
  simp only [explode, mem_append, map_cons, mem_map],
  rintros p hp d hd,
  rcases hd with ⟨c, ⟨hce, rfl⟩⟩ | ⟨c, ⟨hce, rfl⟩⟩,
  rcases ih p (not_mem_of_not_mem_cons hp) c hce with ⟨hpos, hneg⟩,
  { split,
    { exact not_mem_cons_of_ne_of_not_mem (ne_pos_of_ne_nat (ne_of_not_mem_cons hp)) hpos},
    exact not_mem_cons_of_ne_of_not_mem ne_lit_of_nat.symm hneg},
  rcases ih p (not_mem_of_not_mem_cons hp) c hce with ⟨hpos, hneg⟩,
  split,
  exact not_mem_cons_of_ne_of_not_mem ne_lit_of_nat hpos,
  exact not_mem_cons_of_ne_of_not_mem (ne_neg_of_ne_nat (ne_of_not_mem_cons hp)) hneg,
end

theorem mem_of_mem_explode {ns : list nat} : ∀ c ∈ explode ns, ∀ l ∈ c, literal.var l ∈ ns :=
begin
  induction ns with m ms ih,
  { rintros c hc l hl,
    simp [explode] at hc,
    rw hc at hl,
    exact absurd hl (not_mem_nil _)},
  simp only [explode, mem_cons_iff, mem_append, map_cons, mem_map],
  rintros c haor l hl,
  rcases haor with ⟨a, ⟨hams, rfl⟩⟩ | ⟨a, ⟨hams, rfl⟩⟩,
  { rcases hl with ⟨rfl, hla⟩,
    { left, unfold var },
    right, exact ih a hams l hl},
  rcases hl with ⟨rfl | hlcons⟩,
  { left, unfold var},
  right, exact ih a hams l hl,
end

-- Another way to express this is to say for all literals where it and its opposite are not in c
theorem not_mem_of_not_mem_explode {ns : list nat} : 
  ∀ c ∈ explode ns, ∀ (n : nat), ((Pos n ∉ c) ∧ (Neg n ∉ c)) → n ∉ ns :=
begin
  induction ns with m ms ih,
  { rintros _ _ _ _, exact not_mem_nil _},
  simp only [explode, mem_append, map_cons, mem_map],
  rintros c (⟨a, ⟨hams, rfl⟩⟩ | ⟨a, ⟨hams, rfl⟩⟩) n ⟨hpos, hneg⟩,

  apply not_mem_cons_of_ne_of_not_mem,
  { exact ne_nat_of_ne_pos (ne_of_not_mem_cons hpos) },
  exact ih a hams n (and.intro (not_mem_of_not_mem_cons hpos) (not_mem_of_not_mem_cons hneg)),

  apply not_mem_cons_of_ne_of_not_mem,
  { exact ne_nat_of_ne_neg (ne_of_not_mem_cons hneg) },
  exact ih a hams n (and.intro (not_mem_of_not_mem_cons hpos) (not_mem_of_not_mem_cons hneg)),
end

theorem xor_lit_of_explode_of_nodup_list {ns : list nat} (hnodup : list.nodup ns) : ∀ n ∈ ns, ∀ c ∈ explode ns, Pos n ∉ c ∨ Neg n ∉ c :=
begin
  induction ns with m ms ih,
  { rintros _ hnil _ _, exact absurd hnil (not_mem_nil n)},
  simp only [explode, mem_append, map_cons, mem_map],
  rintros n hn c (⟨a, ⟨hams, rfl⟩⟩ | ⟨a, ⟨hams, rfl⟩⟩),
  { rcases eq_or_ne_mem_of_mem hn with ⟨rfl | ⟨hn1, hn2⟩⟩, -- Why do hn1 and hn2 not appear?
    { right, apply not_mem_cons_of_ne_of_not_mem, 
      { exact ne_lit_of_nat.symm },
      exact (not_mem_explode_of_not_mem m (nodup_cons.mp hnodup).left a hams).right },
    cases h with h1 h2,
    have ihred := ih ((nodup_cons.mp hnodup).right) n h2 a hams,
    cases ihred,
    { left, exact not_mem_cons_of_ne_of_not_mem (ne_pos_of_ne_nat h1) ihred},
    right, exact not_mem_cons_of_ne_of_not_mem (ne_lit_of_nat.symm) ihred},
  { rcases eq_or_ne_mem_of_mem hn with ⟨rfl | ⟨hn1, hn2⟩⟩,
    { left, apply not_mem_cons_of_ne_of_not_mem,
      { exact ne_lit_of_nat },
      exact (not_mem_explode_of_not_mem m(nodup_cons.mp hnodup).left a hams).left },
    cases h with h1 h2,
    have ihred := ih ((nodup_cons.mp hnodup).right) n h2 a hams,
    cases ihred,
    { left, exact not_mem_cons_of_ne_of_not_mem ne_lit_of_nat ihred},
    right, exact not_mem_cons_of_ne_of_not_mem (ne_neg_of_ne_nat h1) ihred}
end

/-
theorem aaa {ns : list nat} (hnodup : list.nodup ns) : ∀ (c : clause), ∀ n ∈ ns, xor (Pos n ∈ c) (Neg n ∈ c) → ∃ e ∈ explode ns, c.equiv e :=
begin
  induction ns with m ms ih,
  { rintros _ _ hnil _, exact absurd hnil (not_mem_nil n)},
  rintros c n hn (⟨hpos, hnneg⟩ | ⟨hneg, hnnpos⟩),
  { cases classical.em (n = m),
    { have : m ∉ ms, from not_mem_of_nodup_cons hnodup, 
      rw ← h at this,
      have exi : ∃ (cl : clause), cl ∈ explode ms, from exists_mem_of_explode ms,
      cases exi with cl clh,
      use (Pos n) :: cl,
      rw h,
      unfold explode,
      simp,
      split,
      {left, use cl, exact and.intro clh rfl},
      sorry,
    } sorry, sorry,}
end

theorem bbb {ns : list nat} (hnodup : list.nodup ns) : ∀ (c : clause), c.length = ns.length → (∀ n ∈ ns, xor (Pos n ∈ c) (Neg n ∈ c)) → ∃ e ∈ explode ns, c.equiv e :=
begin
  induction ns with m ms ih,
  { intros c h _, 
    use ([] : clause),
    simp [explode, length_eq_zero.mp h]},
  { rintros c hcl hn,
    unfold length at hcl,
    have msnodup : ms.nodup, from nodup_of_nodup_cons hnodup,
    have sss := hn m (mem_cons_self m ms),
    rcases sss with ⟨hpos, hnneg⟩ | ⟨hneg, hnpos⟩,
    have len_erase : length (c.erase (Pos m)) = length c - 1, from length_erase_of_mem hpos,
    have : length c - 1 = (length ms + nat.succ(0)) - 1, from congr_arg nat.pred hcl,
    rw nat.add_succ_sub_one at this,
    rw nat.add_zero at this,
    rw ← len_erase at this,
    have ihred := ih msnodup (c.erase (Pos m)) this,
    have : ∀ (n : ℕ), n ∈ ms → xor (Pos n ∈ c.erase (Pos m)) (Neg n ∈ c.erase (Pos m)),
      { intros n hnms, have : n ∈ (m :: ms), from mem_cons_of_mem m hnms,
        have abcd := hn n this,
        have erasems : (m :: ms).erase m = ms, from erase_cons_head m ms,
        rw ← erasems at hnms,
        have nm : n ≠ m, from ((mem_erase_iff_of_nodup hnodup).mp hnms).left,
        sorry,
      },
    have := ihred this,
    cases this with e he,
    cases he with hhe hequiv,
    use (Pos m :: e),
    split,
    { unfold explode,
      simp,
      use e,
      exact and.intro hhe rfl },
    { }
  }
end
-/

theorem perm_explode_of_perm {ns : list nat} : ∀ (l : list nat), l ~ ns → ∀ cn ∈ explode ns, ∃ cl ∈ explode l, cn ~ cl :=
begin
  induction ns with m ms ih,
  { intro l, intro sim, intro cn, intro cn_sim, have : l = [], from perm.eq_nil sim, rw this,
    unfold explode at cn_sim, have : cn = nil, from mem_singleton.mp cn_sim,
    use ([] : clause),
    unfold explode,
    rw this,
    exact and.intro (mem_singleton_self _) (perm.refl _)
  },
  {
    intros l hlsim cn hcnexpl,
    unfold explode at hcnexpl,
    simp at hcnexpl,
    cases hcnexpl,
    have hlerase : l.erase m ~ (m :: ms).erase m, from perm.erase m hlsim,
    have : (m :: ms).erase m = ms, from erase_cons_head m ms,
    rw this at hlerase,
    { cases hcnexpl with a ha, cases ha with ha1 ha2,
      have ihred := ih (l.erase m) hlerase a ha1,
      cases ihred with b hb,
      cases hb with hb absim,
      use (Pos m :: b),
      sorry,
     }, sorry,
  }
end

-- The symbol '~' means a permutation between two lists, of which clauses are, under the hood
theorem ccc {ns : list nat} (hnodup : list.nodup ns) : ∀ (c : clause), c.length = ns.length → (∀ n ∈ ns, xor (Pos n ∈ c) (Neg n ∈ c)) → ∃ e ∈ explode ns, c ~ e :=
begin
  sorry,
end

theorem ddd {ns : list nat} {n : nat} : ∀ c ∈ explode (n :: ns), ∃ cn ∈ explode ns, (Pos n :: cn) ~ c ∨ (Neg n :: cn) ~ c :=
begin
  induction ns with m ms ih,
  { intros c hc, use nil, unfold explode at hc, simp at hc, split, simp [explode],
    cases hc with hcp hcn, simp [hcp], simp [hcn]},
  simp only [explode, mem_cons_iff, mem_append, map_cons, mem_map],
  intro c,
  intro h,
  cases h with h1 h2, -- h is an or
  cases h1 with a ha, -- h1 is and exists hyp
  cases ha with ha1 ha2,
  cases ha1 with ha1 ha1,
  cases ha1 with a1 ha1,
  cases ha1 with haa1 haa2,
  sorry,
  sorry,
  sorry,
end

theorem sim_erase_cons_of_explode {ns : list nat} {n : nat} (h : n ∈ ns) : ∀ c ∈ explode ns, ∃ cn ∈ explode (ns.erase n), (Pos n :: cn) ~ c ∨ (Neg n :: cn) ~ c :=
begin
  induction ns with m ms ih,
  { exact absurd h (not_mem_nil _) },
  simp only [explode, mem_cons_iff, mem_append, map_cons, mem_map],
  intros c hc,
  cases hc with hcp hcn,
  { cases hcp with a ha,
    cases ha with ha1 ha2,
    cases classical.em (n = m),
    { use a, simp [h_1, erase_cons_head, ha2, ha1, perm.refl] },
    { have ihred := ih (mem_of_ne_of_mem h_1 h) a ha1,
      cases ihred with cn hcn,
      cases hcn with hhcn hhhcn,
      rw erase_cons_tail ms (ne.symm h_1),
      rw ← ha2,
      cases hhhcn,
      { use (Pos m :: cn), unfold explode, split,
        { simp only [mem_cons_iff, mem_append, map_cons, mem_map],
          left, use cn, exact and.intro hhcn (and.intro (refl _) (refl _)) },
        left, exact perm.trans (perm.swap (Pos m) (Pos n) cn) ((perm_cons (Pos m)).mpr hhhcn) },
      { use (Pos m :: cn), unfold explode, split,
        { simp only [mem_cons_iff, mem_append, map_cons, mem_map],
          left, use cn, exact and.intro hhcn (and.intro (refl _) (refl _)) },
        right, exact perm.trans (perm.swap (Pos m) (Neg n) cn) ((perm_cons (Pos m)).mpr hhhcn) }
    }},
  { cases hcn with a ha,
    cases ha with ha1 ha2,
    cases classical.em (n = m),
    { use a, simp [h_1, erase_cons_head, ha2, ha1, perm.refl] },
    { have ihred := ih (mem_of_ne_of_mem h_1 h) a ha1,
      cases ihred with cn hcn,
      cases hcn with hhcn hhhcn,
      rw erase_cons_tail ms (ne.symm h_1),
      rw ← ha2,
      cases hhhcn,
      { use (Neg m :: cn), unfold explode, split,
        { simp only [mem_cons_iff, mem_append, map_cons, mem_map],
          right, use cn, exact and.intro hhcn (and.intro (refl _) (refl _)) },
        left, exact perm.trans (perm.swap (Neg m) (Pos n) cn) ((perm_cons (Neg m)).mpr hhhcn) },
      { use (Neg m :: cn), unfold explode, split,
        { simp only [mem_cons_iff, mem_append, map_cons, mem_map],
          right, use cn, exact and.intro hhcn (and.intro (refl _) (refl _)) },
        right, exact perm.trans (perm.swap (Neg m) (Neg n) cn) ((perm_cons (Neg m)).mpr hhhcn) } } }
end

theorem explode_clause_perm_of_list {ns : list nat} : ∀ (c : clause), c ∈ explode ns → c.map var ~ ns :=
begin 
  induction ns with m ms ih,
  { intros c hc, unfold explode at hc, rw (mem_singleton.mp hc), simp },
  simp only [explode, mem_cons_iff, mem_append, map_cons, mem_map],
  rintros c (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩) ;
  { simp [map, var, perm.cons m, ih c hc] }
end

-- TODO cleanup with simp, etc.
theorem explode_exhaustive {ns : list nat} : ∀ (c : clause), c.map var ~ ns → ∃ cl ∈ explode ns, c ~ cl :=
begin
  induction ns with m ms ih,
  { simp [explode, perm_nil] },
  rintros c h,
  have : (map var c).erase m ~ (m :: ms).erase m, from perm.erase m h,
  rw erase_cons_head m at this,
  have hm : m ∈ map var c, from h.mem_iff.mpr (mem_cons_self m ms),
  have : ∃ l, l ∈ c ∧ var l = m, from mem_map.mp hm,
  cases this with l hl,
  cases hl with hl1 hl2,
  have testthm := erase_map_var_eq_map_var_erase m hm,
  rcases testthm with ⟨l2, ⟨hl1, ⟨hl2, hl3⟩⟩⟩,
  have : map var (c.erase l2) ~ ms, from (perm.symm hl3).trans this,
  rcases ih (c.erase l2) this with ⟨cl, ⟨hclms, hclsim⟩⟩,
  use l2 :: cl,
  split,
  { unfold explode, simp only [mem_cons_iff, mem_append, map_cons, mem_map], 
    rcases pos_or_neg_of_var_eq_nat hl2 with rfl | rfl,
    { left, use cl, exact and.intro hclms (and.intro (refl _) (refl _)) },
    right, use cl, exact and.intro hclms (and.intro (refl _) (refl _)) },
  have : c ~ l2 :: (c.erase l2), from perm_cons_erase hl1,
  have onemore : l2 :: list.erase c l2 ~ l2 :: cl, from (perm_cons l2).mpr hclsim,
  exact perm.trans this onemore
end

end explode