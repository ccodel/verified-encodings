/-
This file contains the definition of the "explode" operation, which
creates a "powerset" of literals from a list of variables. Associated
theorems dealing with the contents of explode are also included.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import cnf.literal
import cnf.clause
import cnf.cnf

import data.nat.basic
import data.nat.pow

/- Sometimes, it is necessary to get all possible disjunctive clauses from a set of variables -/
/- For lack of a better name, we call that operation "exploding" -/
namespace explode

open literal
open clause
open list

/-! ## Non-recursive definition of explode -/

/- This should ideally take in a nodup list or a finset, but lists are easier to manipulate -/
/- Also, should ideally return a nodup list or a finset, see above comment -/
-- Here is a non-recursive definition of expl. Recursive is easier though...
def explode_non_rec (l : list nat) : list clause :=
  l.foldr (λ n ls, (ls.map (cons (Pos n))) ++ (ls.map (cons (Neg n)))) [[]]

@[simp] lemma explode_non_rec_nil : explode_non_rec [] = [[]] := rfl

@[simp] lemma explode_non_rec_singleton {n : nat} : explode_non_rec [n] = [[Pos n], [Neg n]] :=
by simp [explode_non_rec]

lemma explode_non_rec_cons {n : nat} {ns : list nat} : 
  explode_non_rec (n :: ns) = (explode_non_rec ns).map (cons (Pos n)) ++ (explode_non_rec ns).map (cons (Neg n)) :=
by simp [explode_non_rec]

/-! ## Recursive definition of explode (preferred) -/

def explode : list nat → list clause 
| []        := [[]]
| (n :: ns) := (explode ns).map (cons (Pos n)) ++ (explode ns).map (cons (Neg n))

-- Saying they're equal is a little dangerous - maybe saying they're similar is good enough?
-- By straight implementation, though, they are equal
theorem explode_and_explode_rec_equiv {ns : list nat} : explode_non_rec ns = explode ns :=
begin
  induction ns with m ms ih,
  { simp [explode, explode_non_rec] },
  { simp only [explode, ih, explode_non_rec_cons] }
end

@[simp] lemma explode_nil : explode [] = [[]] := rfl

@[simp] lemma explode_singleton {n : nat} : explode [n] = [[Pos n], [Neg n]] :=
by simp [explode]

-- Technically, a cons lemma could go here, but the definition could just be unfolded, so...

/-! ## Length of explode and clauses in explode -/

theorem length_explode : ∀ (ns : list nat), length (explode ns) = 2^(length ns)
| []        := rfl
| (n :: ns) := by simp [explode, length_explode ns, pow_succ, two_mul]

theorem length_explode_pos {ns : list nat} : length (explode ns) > 0 :=
by simp [length_explode]

theorem exists_mem_explode : ∀ (ns : list nat), ∃ (c : clause), c ∈ explode ns :=
λ _, exists_mem_of_length_pos length_explode_pos

theorem length_eq_of_mem_explode {ns : list nat} : ∀ {c : clause}, c ∈ explode ns → length c = length ns :=
begin
  induction ns with m ms ih, { simp },
  { simp only [explode, mem_append, mem_map],
    rintros c (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩); simp [length, ih hc] }
end

theorem mem_explode_cons_of_lit {ns : list nat} {n : nat} {l : literal} : 
  ∀ (c : clause), c ∈ explode ns → l.var = n → (l :: c) ∈ explode (n :: ns) :=
begin
  intros c hc heq, simp [explode],
  rcases pos_or_neg_of_var_eq_nat heq with rfl | rfl; { simp [hc] }
end

/-! ## Similarity of clauses in explode -/

-- Depends on the implementation of explode, but I think that's okay
theorem map_var_eq_of_mem_explode {ns : list nat} : ∀ {c : clause}, c ∈ explode ns → c.map var = ns :=
begin
  induction ns with m ms ih,
  { simp [explode] },
  { simp only [explode, mem_append, mem_map], 
    rintros c (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩);
    { simp [var, map_cons, ih ha] }
  }
end

theorem map_var_sim_of_mem_explode {ns : list nat} : ∀ (c : clause), c ∈ explode ns → c.map var ~ ns :=
begin
  induction ns with m ms ih,
  { simp [explode] },
  { simp only [explode, mem_append, mem_map],
    rintros c (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩); simp [var, perm.cons m, ih c hc] }
end

theorem mem_explode_of_map_var_eq {ns : list nat} : ∀ {c : clause}, c.map var = ns → c ∈ explode ns :=
begin
  induction ns with m ms ih,
  { simp [explode] },
  { intros c h,
    rcases exists_cons_of_map_cons h with ⟨l, ls, rfl, hl, hls⟩,
    rcases pos_or_neg_of_var_eq_nat hl with rfl | rfl,
    { simp [explode], left, use ls, simp [ih hls] },
    { simp [explode], right, use ls, simp [ih hls] } }
end

theorem mem_explode_iff_map_var_eq {ns : list nat} : ∀ {c : clause}, c.map var = ns ↔ c ∈ explode ns :=
λ _, ⟨assume h, mem_explode_of_map_var_eq h, assume h, map_var_eq_of_mem_explode h⟩

theorem mem_explode_sim_of_map_var_sim {ns : list nat} : ∀ (c : clause), c.map var ~ ns → ∃ cl ∈ explode ns, c ~ cl :=
begin
  induction ns with m ms ih,
  { simp [explode, perm_nil] },
  { intros c h,
    have : (map var c).erase m ~ (m :: ms).erase m, from perm.erase m h,
    rw erase_cons_head m at this,
    rcases erase_map_var_eq_map_var_erase m (h.mem_iff.mpr (mem_cons_self m ms)) with ⟨l2, ⟨hl1, ⟨hl2, hl3⟩⟩⟩,
    rcases ih (c.erase l2) ((perm.symm hl3).trans this) with ⟨cl, ⟨hclms, hclsim⟩⟩,
    use l2 :: cl, split,
    { simp [explode, mem_append, mem_map, hclms],
      rcases pos_or_neg_of_var_eq_nat hl2 with rfl | rfl; simp },
    { exact perm.trans (perm_cons_erase hl1) ((perm_cons l2).mpr hclsim) } }
end

theorem mem_explode_sim_iff_map_var_sim {ns : list nat} : ∀ (c : clause), c.map var ~ ns ↔ ∃ cl ∈ explode ns, c ~ cl :=
begin
  intro c, split,
  { exact mem_explode_sim_of_map_var_sim c },
  { intro h, rcases h with ⟨cl, ⟨hcl1, hcl2⟩⟩,
    exact perm.trans (perm.map var hcl2) (map_var_sim_of_mem_explode cl hcl1) }
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

end explode