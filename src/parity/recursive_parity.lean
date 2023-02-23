/-
This file contains the recursive encoding for parity.
Both the pooled and linear encodings are included here.

Authors: Cayden Codel, Jeremy Avidgad, Marijn Heule
Carnegie Mellon University
-/

import cnf.literal
import cnf.clause
import cnf.cnf
import cnf.encoding
import cnf.gensym
import parity.parity
import parity.direct_parity

import data.list.basic
import data.nat.basic

variables {V : Type*} [inhabited V] [decidable_eq V]

open literal clause cnf parity encoding gensym assignment
open nat list list.perm function

namespace recursive_parity

variables {l : list (literal V)} {g : gensym V} {k : nat} (hk : k ≥ 3) {v : V} {τ : assignment V}

lemma disjoint_fresh_of_disjoint (k : nat) : disj l g → 
  disj ((Pos g.fresh.1) :: (l.drop (k - 1))) g.fresh.2 :=
begin
  intro hdis,
  apply disj_left.mpr,
  intros v hv,
  simp only [clause.vars_cons, finset.mem_union, finset.mem_singleton, var] at hv,
  rcases hv with (rfl | hv),
  { exact fresh_not_mem_fresh_stock _ },
  { exact disj_left.mp (disj_fresh_of_disj hdis) 
      (((vars_subset_of_subset (drop_subset (k - 1) l)) hv)) }
end

lemma drop_len_lt (lit : literal V) (hk : k ≥ 3) :
  length l > k → length (lit :: (l.drop (k - 1))) < length l :=
begin
  intro hl,
  rcases exists_append_of_gt_length hl with ⟨x₁, x₂, rfl, hl₁⟩,
  simp only [length_cons, hl₁, length_drop, length_append],
  rw [add_comm k x₂.length, nat.add_sub_assoc (nat.sub_le k 1),
      nat.sub_sub_self (le_of_add_le_right hk), add_assoc],
  apply add_lt_add_left,
  exact succ_le_iff.mp hk,
end

variables {p : list (literal V) → list (literal V)} (hp : ∀ l, perm l (p l))

def recursive_parity : enc_fn V 
| l g :=  if h : length l ≤ k then direct_parity l g else
    have length (p (Pos g.fresh.1 :: (l.drop (k - 1)))) < length l,
      from (perm.length_eq (hp (Pos g.fresh.1 :: (l.drop (k - 1))))) ▸ 
             (drop_len_lt _ hk (not_le.mp h)),
    ⟨(direct_parity (l.take (k - 1) ++ [(Neg g.fresh.1)]) g.fresh.2).1 ++
     (recursive_parity (p (Pos g.fresh.1 :: (l.drop (k - 1)))) g.fresh.2).1,
     (recursive_parity (p (Pos g.fresh.1 :: (l.drop (k - 1)))) g.fresh.2).2⟩ 
using_well_founded {
  rel_tac := λ a b, `[exact ⟨_, measure_wf (λ σ, list.length σ.1)⟩],
  dec_tac := tactic.assumption
}

def recursive_parity' : enc_fn V 
| l g :=  if h : length l ≤ k then direct_parity l g else
    let ⟨y, g₁⟩ := g.fresh in
    have length (p (Pos y :: (l.drop (k - 1)))) < length l,
      from (perm.length_eq (hp (Pos y :: (l.drop (k - 1))))) ▸ 
           (drop_len_lt _ hk (not_le.mp h)),
    let ⟨Frec, g₂⟩ := recursive_parity' (p (Pos y :: (l.drop (k - 1)))) g₁ in
      ⟨(direct_parity (l.take (k - 1) ++ [Neg y]) g₁).1 ++ Frec, g₂⟩
using_well_founded {
  rel_tac := λ a b, `[exact ⟨_, measure_wf (λ σ, list.length σ.1)⟩],
  dec_tac := tactic.assumption
}

theorem recursive_parity_eq_recursive_parity' : ∀ (l : list (literal V)) (g : gensym V),
  recursive_parity hk hp l g = recursive_parity' hk hp l g :=
begin
  intros l g,
  induction l using strong_induction_on_lists with l ih generalizing g,
  rw [recursive_parity, recursive_parity'],
  by_cases hl : length l ≤ k,
  { simp [hl] },
  { simp [hl, fresh],
    rw [recursive_parity'._match_2, prod.ext_self (recursive_parity' hk hp _ _), ← ih, recursive_parity'._match_1],
    exact (perm.length_eq (hp (Pos g.fresh.1 :: (l.drop (k - 1))))) ▸ 
             (drop_len_lt _ hk (not_le.mp hl)) }
end

lemma tseitin_base_case : length l ≤ k → (recursive_parity hk hp l g).1 = (direct_parity l g).1 :=
assume h, by { rw recursive_parity, simp only [h, if_true] }

theorem mem_recursive_parity_vars_of_mem_vars (hdis : disj l g) :
  clause.vars l ⊆ (recursive_parity hk hp l g).1.vars :=
begin
  induction l using strong_induction_on_lists with l ih generalizing g,
  by_cases hl : length l ≤ k,
  { rw [tseitin_base_case hk hp hl, ← direct_parity_eq_direct_parity, vars_direct_parity], refl },
  { intros v hv,
    rw recursive_parity,
    simp [hl],
    rw [← take_append_drop (k - 1) l, clause.vars_append] at hv,
    rcases finset.mem_union.mp hv with (h | h),
    { left,
      rw [← direct_parity_eq_direct_parity, vars_direct_parity, clause.vars_append],
      exact finset.mem_union_left _ h },
    { rw not_le at hl,
      have h₁ := drop_len_lt (Pos g.fresh.1) hk hl,
      have h₂ := disjoint_fresh_of_disjoint k hdis,
      rw perm.length_eq (hp (Pos g.fresh.1 :: drop (k - 1) l)) at h₁,
      rw (disj_perm hp) at h₂,
      have := ih _ h₁ h₂,
      rw ← clause.vars_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at this,
      exact or.inr (this (mem_vars_cons_of_mem_vars _ h)) } }
end

theorem recursive_parity_is_wb : is_wb (recursive_parity hk hp) :=
begin
  intros l g hdis,
  induction l using strong_induction_on_lists with l ih generalizing g,
  rw recursive_parity,
  by_cases hl : length l ≤ k,
  { simp [hl], exact (direct_parity_encodes_parity.2 hdis) },
  { simp [hl],
    have h₁ := drop_len_lt (Pos g.fresh.1) hk (not_le.mp hl),
    rw perm.length_eq (hp (Pos g.fresh.1 :: drop (k - 1) l)) at h₁,
    have h₂ := disjoint_fresh_of_disjoint k hdis,
    rw (disj_perm hp) at h₂,
    have ihred := ih _ h₁ h₂,
    split,
    { exact subset_trans ihred.1 (fresh_stock_subset g) },
    { split,
      { rw ← direct_parity_eq_direct_parity, -- TODO: shortcut vars_direct_parity
        rw vars_direct_parity,
        rw clause.vars_append,
        intros v hv,
        rcases finset.mem_union.mp hv with (h | h),
        { exact set.mem_union_left _ (clause.vars_subset_of_subset (take_subset _ l) h) },
        { simp [literal.var] at h, subst h,
          apply set.mem_union_right,
          apply (set.mem_diff _).mpr,
          exact ⟨fresh_mem_stock _, λ hcon, (fresh_not_mem_fresh_stock g) (ihred.1 hcon)⟩ } },
      { intros v hv,
        rcases (set.mem_union v _ _).mp (ihred.2 hv) with (h | h),
        { simp [← clause.vars_perm (hp _), clause.vars, literal.var] at h,
          rcases h with (rfl | h),
          { apply set.mem_union_right _,
            apply (set.mem_diff _).mpr,
            exact ⟨fresh_mem_stock _, λ hcon, (fresh_not_mem_fresh_stock g) (ihred.1 hcon)⟩ },
          { exact set.mem_union_left _ (clause.vars_subset_of_subset (drop_subset _ l) h) } },
        { apply set.mem_union_right,
          apply (set.mem_diff _).mpr,
          exact ⟨(fresh_stock_subset g) ((set.mem_diff _).mp h).1, 
                 λ hcon, (((set.mem_diff _).mp h).2) hcon⟩ } } } }
end

-- TODO: make into a shorter lemma
theorem not_mem_recursive_parity_vars_of_not_mem_vars_of_not_mem_stock (hdis : disj l g) :
  v ∉ (clause.vars l) → v ∉ g.stock → v ∉ (recursive_parity hk hp l g).1.vars :=
begin
  induction l using strong_induction_on_lists with l ih generalizing g,
  by_cases hl : length l ≤ k,
  { rw [tseitin_base_case hk hp hl, ← direct_parity_eq_direct_parity, vars_direct_parity l], tautology },
  { intros hvars hg,
    rw recursive_parity,
    simp [hl, not_or_distrib],
    split,
    { rw [← direct_parity_eq_direct_parity, vars_direct_parity, clause.vars_append],
      apply finset.not_mem_union.mpr,
      split,
      { exact (λ hcon, absurd (((vars_subset_of_subset (take_subset (k - 1) l))) hcon) hvars) },
      { simp [var],
        intro hcon,
        rw hcon at hg,
        exact absurd (fresh_mem_stock g) hg } },
    { have h₁ := drop_len_lt (Pos g.fresh.1) hk (not_le.mp hl),
      have h₂ := disjoint_fresh_of_disjoint k hdis,
      have h₃ : v ∉ clause.vars (Pos g.fresh.1 :: drop (k - 1) l),
      { simp [clause.vars, var],
        rintros (rfl | h),
        { exact hg (fresh_mem_stock g) },
        { exact hvars (vars_subset_of_subset (drop_subset (k - 1) l) h) } },
      have h₄ : v ∉ g.fresh.2.stock,
      { exact (λ hcon, hg ((fresh_stock_subset g) hcon)) },
      rw perm.length_eq (hp (Pos g.fresh.1 :: drop (k - 1) l)) at h₁,
      rw (disj_perm hp) at h₂,
      rw vars_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at h₃,
      exact ih _ h₁ h₂ h₃ h₄ } }
end

lemma tseitin_reverse (hdis : disj l g) :
  (recursive_parity hk hp l g).1.eval τ = tt → parity.eval τ l = tt :=
begin
  intro he,
  induction l using strong_induction_on_lists with l ih generalizing g,
  by_cases hl : length l ≤ k,
  { rw [tseitin_base_case hk hp hl, ← direct_parity_eq_direct_parity, eval_direct_parity_eq_eval_parity] at he,
    exact he },
  { rw recursive_parity at he,
    simp [hl, cnf.eval_append] at he,
    rcases he with ⟨hdir, hrec⟩,
    have h₁ := drop_len_lt (Pos g.fresh.1) hk (not_le.mp hl),
    have h₂ := disjoint_fresh_of_disjoint k hdis,
    rw perm.length_eq (hp (Pos g.fresh.1 :: drop (k - 1) l)) at h₁,
    rw (disj_perm hp) at h₂,
    have ihred := ih _ h₁ h₂ hrec,
    rw [← direct_parity_eq_direct_parity, eval_direct_parity_eq_eval_parity] at hdir,
    rw eval_eq_bodd_count_tt at ihred hdir |-,
    rw ← clause.count_tt_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at ihred,
    have := congr_arg ((clause.count_tt τ)) (take_append_drop (k - 1) l).symm,
    have := congr_arg bodd this,
    cases hnew : (τ g.fresh.1),
    { simp [clause.count_tt_cons, clause.count_tt_append, hnew, literal.eval] at ihred hdir,
      rw [clause.count_tt_append, bodd_add, hdir, ihred, ff_bxor] at this,
      exact this },
    { simp [clause.count_tt_cons, clause.count_tt_append, hnew, literal.eval] at ihred hdir,
      rw [clause.count_tt_append, bodd_add, hdir, ihred, bxor_ff] at this,
      exact this } }
end

theorem recursive_parity_encodes_parity : encodes parity (recursive_parity hk hp) :=
begin
  split,
  { intros l g hdis τ,
    induction l using strong_induction_on_lists with l ih generalizing g τ,
    by_cases hl : length l ≤ k,
    { rw tseitin_base_case hk hp hl,
      exact direct_parity_formula_encodes_parity l τ },
    { have h₁ := drop_len_lt (Pos g.fresh.1) hk (not_le.mp hl),
      rw perm.length_eq (hp (Pos g.fresh.1 :: drop (k - 1) l)) at h₁,
      have h₂ := disjoint_fresh_of_disjoint k hdis,
      rw (disj_perm hp) at h₂,
      split,
      { rw recursive_parity,
        simp [hl],
        have hnotmem := set.disjoint_left.mp hdis (g.fresh_mem_stock),
        have htakevars := vars_subset_of_subset (take_subset (k - 1) l),
        have hdropvars := vars_subset_of_subset (drop_subset (k - 1) l),
        intro heval,
        rw [eval_eq_bodd_count_tt, ← (take_append_drop (k - 1) l), clause.count_tt_append, bodd_add] at heval,
        cases hevalsub : bodd (clause.count_tt τ (take (k - 1) l)),
        { rw [hevalsub, bool.bxor_ff_left] at heval,
          rcases exists_agree_on_and_eq_of_not_mem τ ff hnotmem with ⟨γ, hagree_on, hg⟩,
          have : bodd (clause.count_tt γ (Pos g.fresh.1 :: drop (k - 1) l)) = tt,
          { simp only [clause.count_tt_cons, literal.eval, hg, cond,
              ← count_tt_eq_of_agree_on (agree_on_subset hdropvars hagree_on), heval] },
          rw [← eval_eq_bodd_count_tt, eval_eq_of_perm (hp (Pos g.fresh.1 :: drop (k - 1) l))] at this,

          -- Apply the induction hypothesis
          rcases (ih _ h₁ _ h₂).mp this with ⟨γ₂, he₂, hg₂⟩,

          have hagree_on₂ : agree_on (aite ((recursive_parity hk hp (p (Pos g.fresh.1 :: (l.drop (k - 1)))) g.fresh.2).1.vars) γ₂ γ) γ (clause.vars l),
          { intros v hv,
            by_cases hmem : v ∈ clause.vars (l.drop (k - 1)),
            { have h₃ := mem_vars_cons_of_mem_vars (Pos g.fresh.1) hmem,
              rw vars_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at h₃,
              rw [aite_pos (mem_recursive_parity_vars_of_mem_vars hk hp h₂ h₃), hg₂ v h₃] },
            { have hdis₂ := set.disjoint_right.mp hdis hv,
              have hne : v ≠ g.fresh.1,
              { exact (λ hcon, (hcon ▸ hdis₂) (fresh_mem_stock g)) },
              have : v ∉ clause.vars (Pos g.fresh.1 :: drop (k - 1) l),
              { simp [clause.vars, var],
                rintros (hcon | hcon),
                { exact hne hcon },
                { exact hmem hcon } },
              rw vars_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at this,
              have hstock : v ∉ g.fresh.2.stock,
              { exact (λ hcon, hdis₂ ((fresh_stock_subset g) hcon)) },
              rw aite_neg (not_mem_recursive_parity_vars_of_not_mem_vars_of_not_mem_stock hk hp h₂ this hstock) } },

          use aite (recursive_parity hk hp (p (Pos g.fresh.1 :: (l.drop (k - 1)))) g.fresh.2).1.vars γ₂ γ,
          split,
          { split,
            { rw ← direct_parity_eq_direct_parity,
              simp [eval_direct_parity_eq_eval_parity, eval_eq_bodd_count_tt, 
              clause.count_tt_append, bodd_add, literal.eval, hg],
              have : g.fresh.1 ∈ clause.vars (Pos g.fresh.1 :: (l.drop (k - 1))),
              { exact mem_vars_cons_self _ _ },
              rw vars_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at this,
              simp [aite_pos (mem_recursive_parity_vars_of_mem_vars hk hp h₂ this), 
                ← (hg₂ g.fresh.1 this), hg,
                count_tt_eq_of_agree_on (agree_on_subset htakevars hagree_on₂),
                ← count_tt_eq_of_agree_on (agree_on_subset htakevars hagree_on), hevalsub] },
            { exact he₂ ▸ eval_eq_of_agree_on (aite_agree_on _ _ _) } },
          { exact agree_on.trans hagree_on (hagree_on₂.symm) } },
        { simp only [hevalsub, bnot_eq_true_eq_eq_ff, tt_bxor] at heval,
          rcases exists_agree_on_and_eq_of_not_mem τ tt hnotmem with ⟨γ, hagree_on, hg⟩,
          have : bodd (clause.count_tt γ (Pos g.fresh.1 :: drop (k - 1) l)) = tt,
          { simp only [clause.count_tt_cons, literal.eval, hg, cond, 
              ← count_tt_eq_of_agree_on (agree_on_subset hdropvars hagree_on), heval, bodd_succ,
              bodd_add, bodd_zero, bool.bnot_ff, bxor_tt_left], },
          rw [← eval_eq_bodd_count_tt, eval_eq_of_perm (hp (Pos g.fresh.1 :: drop (k - 1) l))] at this,

          -- Apply the induction hypothesis
          rcases (ih _ h₁ _ h₂).mp this with ⟨γ₂, he₂, hg₂⟩,

          have hagree_on₂ : agree_on (aite (recursive_parity hk hp (p (Pos g.fresh.1 :: (l.drop (k - 1)))) g.fresh.2).1.vars γ₂ γ) γ (clause.vars l),
          { intros v hv,
            by_cases hmem : v ∈ clause.vars (l.drop (k - 1)),
            { have h₃ := mem_vars_cons_of_mem_vars (Pos g.fresh.1) hmem,
              rw vars_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at h₃,
              rw [aite_pos (mem_recursive_parity_vars_of_mem_vars hk hp h₂ h₃), hg₂ v h₃] },
            { have hdis₂ := set.disjoint_right.mp hdis hv,
              have hne : v ≠ g.fresh.1,
              { exact (λ hcon, (hcon ▸ hdis₂) (fresh_mem_stock g)) },
              have : v ∉ clause.vars (Pos g.fresh.1 :: drop (k - 1) l),
              { simp [clause.vars, var],
                rintros (hcon | hcon),
                { exact hne hcon },
                { exact hmem hcon } },
              rw vars_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at this,
              have hstock : v ∉ g.fresh.2.stock,
              { exact (λ hcon, hdis₂ ((fresh_stock_subset g) hcon)) },
              rw aite_neg (not_mem_recursive_parity_vars_of_not_mem_vars_of_not_mem_stock hk hp h₂ this hstock) } },
          
          use aite (recursive_parity hk hp (p (Pos g.fresh.1 :: (l.drop (k - 1)))) g.fresh.2).1.vars γ₂ γ,
          split,
          { split,
            { rw ← direct_parity_eq_direct_parity,
              simp [eval_direct_parity_eq_eval_parity, eval_eq_bodd_count_tt, 
                clause.count_tt_append, bodd_add, literal.eval, hg],
              have : g.fresh.1 ∈ clause.vars (Pos g.fresh.1 :: (l.drop (k - 1))),
              { exact mem_vars_cons_self _ _ },
              rw vars_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at this,
              simp [aite_pos (mem_recursive_parity_vars_of_mem_vars hk hp h₂ this), 
                ← (hg₂ g.fresh.1 this), hg,
                count_tt_eq_of_agree_on (agree_on_subset htakevars hagree_on₂),
                ← count_tt_eq_of_agree_on (agree_on_subset htakevars hagree_on), hevalsub] },
            { exact he₂ ▸ eval_eq_of_agree_on (aite_agree_on _ _ _) } },
        { exact agree_on.trans hagree_on hagree_on₂.symm } } },
      { rintros ⟨σ, heval, hagree_on⟩,
        rw parity.eval_eq_of_agree_on hagree_on,
        exact tseitin_reverse hk hp hdis heval } } },
  { exact recursive_parity_is_wb hk hp }
end

def linear_perm (l : list (literal V)) : list (literal V) := l

lemma linear_perm_is_perm : ∀ (l : list (literal V)), l ~ linear_perm l :=
begin
  intro l, rw linear_perm
end

def linear_parity : enc_fn V := recursive_parity hk linear_perm_is_perm

theorem linear_parity_encodes_parity : encodes parity (linear_parity hk : enc_fn V) :=
recursive_parity_encodes_parity hk linear_perm_is_perm

def pooled_perm : list (literal V) → list (literal V)
| []        := []
| (x :: xs) := xs ++ [x]

lemma pooled_perm_is_perm : ∀ (l : list (literal V)), l ~ pooled_perm l :=
begin
  intro l,
  cases l,
  { refl },
  { rw [pooled_perm, ← singleton_append],
    exact perm_append_comm }
end

def pooled_parity : enc_fn V := recursive_parity hk pooled_perm_is_perm

theorem pooled_parity_encodes_parity : encodes parity (pooled_parity hk : enc_fn V) :=
recursive_parity_encodes_parity hk pooled_perm_is_perm

end recursive_parity