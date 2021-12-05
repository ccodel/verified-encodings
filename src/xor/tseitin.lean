/-
This file contains the development of the Tseitin encoding for XOR

Authors: Cayden Codel, Jeremy Avidgad, Marijn Heule
Carnegie Mellon University
-/

import cnf.literal_general
import cnf.clause_general
import cnf.cnf_general
import xor.xor_general
import cnf.gensym

import data.list.basic
import data.nat.basic
import init.function

universe u

variables {V : Type u} [inhabited V] [decidable_eq V]

open literal
open clause
open cnf
open xor_gate

open list
open assignment
open function

namespace tseitin_xor

lemma dropn_len {α : Type u} {n : nat} (a : α) {l : list α} :
  n > 1 → length l > n → length (l.drop n ++ [a]) < length l :=
begin
  intros hn hl,
  induction l with x xs ih,
  { simp [lt_trans hn hl] at hl, contradiction },
  { by_cases length xs = n,
    { simp [h, gt.lt hn] },
    { simp at hl,
      have red := ih (gt.lt (array.push_back_idx hl (ne.symm h))), -- strange theorem
      simp at red,
      simp [tsub_add_eq_add_tsub (nat.lt_succ_iff.mp hl)] at red,
      simp [red] } }
end

lemma three_gt_one : 3 > 1 :=
nat.one_lt_succ_succ 1

def thelper : list (literal V) → gensym V → cnf V
| [] g₁ := [[]]
| l  g₁ := if h : length l ≤ 3 then xor_cnf l else
                  let ⟨v, g₂⟩ := gensym.fresh g₁ in
                  have length (l.drop 3 ++ [Pos v]) < length l,
                    from (dropn_len _ three_gt_one (not_le.mp h)),
                  xor_cnf (l.take 3 ++ [Neg v]) ++ thelper (l.drop 3 ++ [Pos v]) g₂
using_well_founded {
  rel_tac := λ a b, `[exact ⟨_, measure_wf (λ σ, list.length σ.1)⟩],
  dec_tac := tactic.assumption
}

def tseitin_xor3 {f : nat → V} (hf : injective f) {g : V → nat} (hg : injective g)
  (hfg : right_inverse f g) (l : list (literal V)) : cnf V :=
thelper l (gensym.seed hf hg hfg (clause.vars l))

lemma exists_tseitin_of_xor_cnf {f : nat → V} (hf : injective f)
  {g : V → nat} (hg : injective g) (hfg : right_inverse f g) 
  {l : list (literal V)} :
  (∃ (α : assignment V), cnf.eval α (tseitin_xor3 hf hg hfg l) = tt) → 
   ∃ (α₂ : assignment V), cnf.eval α₂ (xor_cnf l) = tt :=
begin
  rintros ⟨α, ha⟩,
  
end


lemma exists_xor_cnf_of_tseitin {f : nat → V} (hf : injective f)
  {g : V → nat} (hg : injective g) (hfg : right_inverse f g) 
  {l : list (literal V)} :
  (∃ (α : assignment V), cnf.eval α (xor_cnf l) = tt) → 
   ∃ (α₂ : assignment V), cnf.eval α₂ (tseitin_xor3 hf hg hfg l) = tt :=
begin

end


noncomputable def tseitin_xor3 {f : V → nat} (hf : bijective f) : list (literal V) → list V → cnf V
| [] _ := [[]]
| l vs := if h : length l ≤ 3 then xor_cnf l else
    have exi : ∃ (v : V), v ∉ vs, from exists_not_mem_of_bijection hf vs,
    have length (l.drop 3 ++ [Pos (classical.some exi)]) < length l,
      from (dropn_len _ three_gt_one (not_le.mp h)),
    xor_cnf (l.take 3 ++ [Neg (classical.some exi)]) ++ 
      (tseitin_xor3 (l.drop 3 ++ [Pos (classical.some exi)]) ((classical.some exi) :: vs))
using_well_founded {
  rel_tac := λ a b, `[exact ⟨_, measure_wf (λ σ, list.length σ.1)⟩],
  dec_tac := tactic.assumption
}
/-
(∃ (α : assignment V), cnf.eval α (xor_cnf l) = tt) →
  ∃ (α₂ : assignment V), eval α₂ l = tt :=
-/

/-
/-
It is noncomputable because pulling a variable from the witness in an exists hypothesis
is not non-classical. In the future, attempt to use gensym in place of the ∃hyp.
-/


lemma empty_intersect_of_empty_intersect {l : list (literal V)} {g : gensym V} :
  ∀ (l₂ : list (literal V)), l₂ ⊆ l → (∀ (n : nat), clause.vars l ∩ (g.nfresh n).1 = []) →
  ∀ (m : nat), clause.vars l₂ ++ [g.fresh.1] ∩ (g.fresh.2.nfresh m).1 = [] :=
begin
  induction l with l ls ih,
  { intros l₂ hl₂ hn m,
    have := eq_nil_of_subset_nil hl₂,
    rw this,
    simp,
    cases m,
    { simp [gensym.nfresh] },
    {
      
    }
  }
end

def tx3 : Π (l : list (literal V)), Π (g : gensym V),
          (∀ n : nat, clause.vars l ∩ (g.nfresh n).1 = []) → cnf V
| l g p := if h : length l ≤ 3 then xor_cnf l else
          let ⟨v, g₂⟩ := gensym.fresh g in
          xor_cnf (l.take 3 ++ [Neg v]) ++ (tx3 (l.drop 3 ++ [Pos v]) g₂ p)

/-
def tx3_helper : list (literal V) × gensym (literal V) → cnf V 
| ⟨[], _⟩ := [[]]
| ⟨l, g⟩  := if h : length l ≤ 3 then xor_cnf l else
    let ⟨v, g2⟩ := gensym.fresh g in
    have length (l.drop 3 ++ [set_pos v]) < length l,
      from (dropn_len _ three_gt_one (not_le.mp h)),
    xor_cnf (l.take 3 ++ [set_neg v]) ++ (tx3_helper ⟨(l.drop 3 ++ [set_pos v]), g2⟩)
using_well_founded {
  rel_tac := λ a b, `[exact ⟨_, measure_wf (λ σ, list.length σ.1)⟩],
  dec_tac := tactic.assumption
}

def tx3 {f : nat → (literal V)} (hf : injective f) (n : nat) : cnf V :=
  tx3_helper (gensym.nfresh (gensym.init hf) n)

lemma tx3_base_case {f : nat → (literal V)} (hf : injective f) {n : nat} :
  n ≤ 3 → cnf.equisatisfiable (tx3 hf n) (xor_cnf (gensym.nfresh (gensym.init hf) n).1) :=
begin
  intro h,
  cases n,
  { simp [gensym.nfresh, tx3, tx3_helper] },
  { simp [tx3],
    rw gensym.nfresh_succ_eq_nfresh_fresh (gensym.init hf),
    unfold tx3_helper,
    simp [h, gensym.length_list_nfresh] }
end

theorem tx3_correct {f : nat → (literal V)} (hf : injective f) (n : nat) :
  cnf.equisatisfiable (tx3 hf n) (xor_cnf (gensym.nfresh (gensym.init hf) n).1) :=
begin
  unfold tx3,
  induction n using nat.case_strong_induction_on with n ih,
  { simp [tx3, tx3_helper, gensym.nfresh] },
  { simp at ih,
    by_cases h : n.succ ≤ 3,
    { exact tx3_base_case hf h },
    { 

      rw gensym.nfresh_succ_eq_nfresh_fresh (gensym.init hf),
      unfold tx3_helper,
      simp [h, gensym.length_list_nfresh],

    }
  }
  /-
  by_cases h : n ≤ 3,
  { exact tx3_base_case hf h },
  { cases n,
    { simp at h, contradiction },
    {
      simp [tx3],
      rw gensym.nfresh_succ_eq_nfresh_fresh (gensym.init hf),
      unfold tx3_helper,
      simp [h, gensym.length_list_nfresh],
      split,
      { sorry, },
      {
        rintros ⟨α, ha⟩,

      }
    }
    -/
  }
end
/-
lemma tseitin_base_case {f : V → nat} (hf : bijective f) {l : list (literal V)} : 
  length l ≤ 3 → cnf.equisatisfiable (tseitin_xor3 hf l (clause.vars l)) (xor_cnf l) :=
begin
  intro h,
  cases l,
  { simp [tseitin_xor3, xor_cnf] },
  { unfold tseitin_xor3, simp [h] }
end

theorem equisatisfiable_tseitin_xor3 {f : V → nat} (hf : bijective f) (l : list (literal V)) :
  assignment.equisatisfiable (λ α, cnf.eval α (tseitin_xor3 hf l (clause.vars l)))
                             (λ α, cnf.eval α (xor_cnf l)) :=
begin
  cases l,
  { simp [tseitin_xor3, xor_cnf], 
    split;
    { rintros ⟨α, ha⟩,
      simp at ha,
      contradiction } },
  { by_cases h : (length (l_hd :: l_tl) ≤ 3),
    { split,
      { rintros ⟨α, ha⟩,
        unfold tseitin_xor3 at ha,
        simp [h] at ha,
        use [α, ha] },
      { rintros ⟨α, ha⟩,
        simp at ha,
        unfold tseitin_xor3,
        use [α],
        simp [h, ha] } },
    { split,
      { rintros ⟨α, ha⟩,
        unfold tseitin_xor3 at ha,
        simp [h] at ha,

      }

    }
  }
end

-- We start with the instance of pooling number n = 3
-- The n provided is the greatest element in l, so that new variables can be created
-- The well_founded had to be used because of the growing n variable
-- Unfold didn't work until I provided a nil case - intentional?
/-
def tseitin_xor3 : list literal → nat → cnf
| [] _ := [[]]
| l n := 
    if h : length l ≤ 3 then xor_cnf l
    else
      have length (l.drop 3 ++ [Pos (n + 1)]) < length l, 
        from (dropn_len (nat.succ 0).one_lt_succ_succ (not_le.mp h)),
      xor_cnf (l.take 3 ++ [Neg (n + 1)]) ++ (tseitin_xor3 (l.drop 3 ++ [Pos (n + 1)]) (n + 1))
using_well_founded {
  rel_tac := λ a b, `[exact ⟨_, measure_wf (λ σ, list.length σ.fst)⟩],
  dec_tac := tactic.assumption
}

lemma tseitin_xor3_base_case {ls : list literal} (n : nat) (h : length ls ≤ 3) :
  tseitin_xor3 ls n = xor_cnf ls :=
begin
  cases ls,
  { simp [tseitin_xor3, xor_cnf] },
  { unfold tseitin_xor3, simp [h] }
end

α : assignment, ls, ∃ a₂ cnf.eval α (tseitn ls)

∀ α, ∃ a₂ s.t. cnf α (xor_cnf ls) = tt → cnf α₂ (tseitn ls) = tt
            (cnf α (xor_cnf ls) = cnf α₂ (xor_cnf ls) by equiv on domain?)
               cnf α (xor_cnf ls) = cnf α₂ (tseitin ls)

∀ α, ∃ a₂ st. cnf α (tseitin ls) = tt → cnf α₂ (xor_cnf ls) = tt
                cnf α₂ (xor_cnf ls) = ff → cnf α (tseitn ls) = ff

theorem tseitin_xor3_correct : ∀ (α : assignment), ∀ (ls : list literal), ∀ (n : nat),
  n = max_var ls → ∃ (α₂ : assignment) 
  (H : α ≡[vars ls]≡ α₂),
  cnf.eval α₂ (xor_cnf ls) = cnf.eval α₂ (tseitin_xor3 ls n)
| α [] n hmax := begin
  use α, simp [xor_cnf, tseitin_xor3]
end
| α [l] n hmax := begin
  use α, split, { exact eqod.refl α (vars [l]) },
  { have hlen : length [l] = 1, simp [length],
    rw tseitin_xor3_base_case n (eq.trans_le hlen (nat.one_le_bit1 1)) }
end
| α (l₁ :: [l₂]) n hmax := begin
  use α, split, { exact eqod.refl α _ },
  { have hlen : length (l₁ :: [l₂]) = 2, simp [length],
    rw tseitin_xor3_base_case n (eq.trans_le hlen (nat.le_succ 2)) }
end
| α (l₁ :: l₂ :: [l₃]) n hmax := begin
  use α, split, { exact eqod.refl α _ },
  { have hlen : length (l₁ :: l₂ :: [l₃]) = 3, simp [length],
    rw tseitin_xor3_base_case n (eq.symm hlen).ge }
end
| α (l₁ :: l₂ :: l₃ :: l₄ :: l) n hmax := begin

  have pos_not_mem : Pos (n + 1) ∉ (l₁ :: l₂ :: l₃ :: l₄ :: l),
    { have hg : n + 1 > n, from lt_add_one n,
      have : (Pos (n + 1)).var = n + 1, simp [var],
      rw ← this at hg,
      rw hmax at hg,
      have := not_mem_of_gt_max_var hg,
      rw ← hmax at this,
      exact this },
  have neg_not_mem : Neg (n + 1) ∉ (l₁ :: l₂ :: l₃ :: l₄ :: l),
    { have hg : n + 1 > n, from lt_add_one n,
      have : (Neg (n + 1)).var = n + 1, simp [var],
      rw ← this at hg,
      rw hmax at hg,
      have := not_mem_of_gt_max_var hg,
      rw ← hmax at this,
      exact this },
  have nsucc_not_mem_map_var : n + 1 ∉ map var (l₁ :: l₂ :: l₃ :: l₄ :: l),
  { apply not_mem_map_var_of_gt_max_var2,
    rw hmax, exact lt_add_one _ },
  have nsucc_not_mem : n + 1 ∉ vars (l₁ :: l₂ :: l₃ :: l₄ :: l),
    from not_mem_vars_iff_not_mem_map_vars.mp nsucc_not_mem_map_var,
  
  -- We want to call the IH on the smaller list - say it's a sublist to get nodup
  have hsublist : map var (l₄ :: l) <+ map var (l₁ :: l₂ :: l₃ :: l₄ :: l),
    simp [sublist.cons],
  have nsucc_not_mem_sublist_map_var : n + 1 ∉ map var (l₄ :: l),
    from not_mem_of_sublist_of_not_mem nsucc_not_mem_map_var hsublist,

  have dis : disjoint (map var (l₁ :: l₂ :: l₃ :: l₄ :: l)) [n + 1],
    { apply disjoint_right.mpr,
      intros a ha,
      rw eq_of_mem_singleton ha,
      exact nsucc_not_mem_map_var },
  have dis2 : disjoint (map var (l₄ :: l)) [n + 1],
    { apply disjoint_right.mpr,
      intros a ha,
      rw eq_of_mem_singleton ha,
      exact nsucc_not_mem_sublist_map_var },
  have hnewmax : n + 1 = max_var ((l₁ :: l₂ :: l₃ :: l₄ :: l) ++ [Pos (n + 1)]),
    { rw max_var_append,
      rw ← hmax,
      simp [max_var_singleton, var] },
  have hnewmax2 : n + 1 = max_var (l₄ :: l ++ [Pos (n + 1)]),
  { have hsl : l₄ :: l <+ l₁ :: l₂ :: l₃ :: l₄ :: l, simp [sublist.cons],
    have hgt : max_var [Pos (n + 1)] > max_var (l₁ :: l₂ :: l₃ :: l₄ :: l),
      { simp [max_var_singleton, ← hmax, var] },
    have := max_var_sublist_append hsl hgt,
    simp [max_var_singleton, var] at this,
    exact this.symm },
  have hlen : (l₁ :: l₂ :: l₃ :: l₄ :: l).length > 3,
    simp [length, nat.lt_add_left 3 4 (length l) (nat.lt.base 3)],

  cases h123 : (xor_gate.eval α (l₁ :: l₂ :: [l₃])),
  { have hextend := exists_extended_assignment_of_assignment α nsucc_not_mem ff,
    rcases hextend with ⟨α₂, hequiv, hff⟩,
    --unfold tseitin_xor3,
    --simp [not_le.mpr hlen],
    rcases tseitin_xor3_correct α₂ ((l₄ :: l) ++ [Pos (n + 1)]) (n + 1) hnewmax2 with ⟨a3, ha3, h3eq⟩,
    have hnewa : α ≡[vars (l₁ :: l₂ :: l₃ :: l₄ :: l)]≡ (λ v, if v ∈ vars (l₁ :: l₂ :: l₃ :: l₄ :: l) then α v else a3 v),
      { intros v hv, simp [hv] },
    use [(λ v, if v ∈ vars (l₁ :: l₂ :: l₃ :: l₄ :: l) then α v else a3 v), hnewa],
    
    have : cnf.vars (xor_cnf (l₁ :: l₂ :: l₃ :: l₄ :: l)) ⊆ vars (l₁ :: l₂ :: l₃ :: l₄ :: l),
    { have : l₁ :: l₂ :: l₃ :: l₄ :: l ≠ [], simp,
      exact subset.trans (vars_cnf_subset_xor this) (map_var_subset_of_vars (l₁ :: l₂ :: l₃ :: l₄ :: l)) },

    have : α ≡[cnf.vars (xor_cnf (l₁ :: l₂ :: l₃ :: l₄ :: l))]≡ (λ v, if v ∈ vars (l₁ :: l₂ :: l₃ :: l₄ :: l) then α v else a3 v),
      from eqod_subset_of_eqod this hnewa,

    rw ← eval_eq_of_equiv_on_domain_vars this,
    unfold tseitin_xor3,
    simp [not_le.mpr hlen],
    rw eval_append,

    --have : cnf.eval (λ v, ite (v ∈ vars (l₁ :: l₂ :: l₃ :: l₄ :: l) (α v) (a3 v))) (xor_cnf (l₁ :: l₂ :: l₃ :: l₄ ))
    --rw eval_append,
      
    --rw xor_cnf_correct α₂ (l₁ :: l₂ :: l₃ :: l₄ :: l),
   -- rw xor_cnf_correct α₂ [l₁, l₂, l₃, Neg (n + 1)],

    have : cnf.vars (xor_cnf (l₄ :: l ++ [Pos (n + 1)])) ⊆ clause.vars (l₄ :: l ++ [Pos (n + 1)]),
    { have : (l₄ :: l ++ [Pos (n + 1)]) ≠ [], simp,
      have h : map var (l₄ :: l ++ [Pos (n + 1)]) ⊆ clause.vars (l₄ :: l ++ [Pos (n + 1)]),
        from map_var_subset_of_vars (l₄ :: l ++ [Pos (n + 1)]),
      exact subset.trans (vars_cnf_subset_xor this) h },
    
    have h3equivnew : α₂ ≡[cnf.vars (xor_cnf (l₄ :: l ++ [Pos (n + 1)]))]≡ a₃,
      from eqod_subset_of_eqod this h3equiv,

    have evala3 : cnf.eval α₂ (xor_cnf (l₄ :: l ++ [Pos (n + 1)])) = cnf.eval a₃ (xor_cnf (l₄ :: l ++ [Pos (n + 1)])),
      from eval_eq_of_equiv_on_domain_vars h3equivnew,
    }
  }
end
-/
-/
-/
-/

end tseitin_xor