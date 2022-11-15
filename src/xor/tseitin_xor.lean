/-
This file contains the Tseitin encoding for XOR.
Both the pooled and linear encodigns are included here.

Authors: Cayden Codel, Jeremy Avidgad, Marijn Heule
Carnegie Mellon University
-/

import cnf.literal
import cnf.clause
import cnf.cnf
import cnf.encoding
import cnf.gensym
import xor.xor
import xor.direct_xor

import data.list.basic
import data.nat.basic

universe u

variables {V : Type u} [inhabited V] [decidable_eq V]

open literal
open clause
open cnf
open Xor
open encoding
open gensym

open nat
open list
open list.perm
open assignment
open function

namespace tseitin_xor

variables {l : list (literal V)} {g : gensym V} {k : nat} (hk : k ≥ 3) {v : V} {τ : assignment V}

lemma disjoint_fresh_of_disjoint : disjoint g.stock (clause.vars l) → 
  disjoint g.fresh.2.stock (clause.vars ((Pos g.fresh.1) :: (l.drop (k - 1)))) :=
begin
  intro h,
  apply set.disjoint_right.mpr,
  intros v hv,
  simp [clause.vars] at hv,
  rcases hv with rfl | hv,
  { rw var,
    exact fresh_not_mem_fresh_stock g },
  { intro hcon,
    rw set.disjoint_right at h,
    have := vars_subset_of_subset (drop_subset (k - 1) l),
    exact absurd ((fresh_stock_subset g) hcon) (h (this hv)) }
end

lemma drop_len_lt (lit : literal V) (hk : k ≥ 3) :
  length l > k → length (lit :: (l.drop (k - 1))) < length l :=
begin
  intro hl,
  rw length_cons,
  rcases exists_append_of_gt_length hl with ⟨x₁, x₂, rfl, hl₁⟩,
  simp only [hl₁, length_drop, length_append],
  rw [add_comm k x₂.length, nat.add_sub_assoc (nat.sub_le k 1),
      nat.sub_sub_self (le_of_add_le_right hk), add_assoc],
  apply add_lt_add_left,
  exact succ_le_iff.mp hk,
end

variables {p : list (literal V) → list (literal V)} (hp : ∀ l, perm l (p l))

def tseitin_xor : list (literal V) → gensym V → cnf V
| l g :=  if h : length l ≤ k then direct_xor l else
          have length (p (Pos g.fresh.1 :: (l.drop (k - 1)))) < length l,
            from (perm.length_eq (hp (Pos g.fresh.1 :: (l.drop (k - 1))))) ▸ 
              (drop_len_lt _ hk (not_le.mp h)),
          (direct_xor (l.take (k - 1) ++ [(Neg g.fresh.1)])) ++
          (tseitin_xor (p (Pos g.fresh.1 :: (l.drop (k - 1)))) g.fresh.2)
using_well_founded {
  rel_tac := λ a b, `[exact ⟨_, measure_wf (λ σ, list.length σ.1)⟩],
  dec_tac := tactic.assumption
}

lemma tseitin_base_case : length l ≤ k → tseitin_xor hk hp l g = direct_xor l :=
assume h, by { rw tseitin_xor, simp only [h, if_true] }

theorem mem_tseitin_xor_vars_of_mem_vars
  (hdis : disjoint g.stock (clause.vars l)) :
  v ∈ (clause.vars l) → v ∈ (tseitin_xor hk hp l g).vars :=
begin
  induction l using strong_induction_on_lists with l ih generalizing g,
  by_cases hl : length l ≤ k,
  { rw [tseitin_base_case hk hp hl, vars_direct_xor], exact id },
  { intro h,
    rw tseitin_xor,
    simp [hl],
    rw [← take_append_drop (k - 1) l, clause.vars_append] at h,
    rw cnf.vars_append,
    rcases finset.mem_union.mp h with (h | h),
    { apply finset.mem_union_left,
      rw [vars_direct_xor, clause.vars_append],
      exact finset.mem_union_left _ h },
    { rw not_le at hl,
      have h₁ := drop_len_lt (Pos g.fresh.1) hk hl,
      have h₂ := disjoint_fresh_of_disjoint hdis,
      rw perm.length_eq (hp (Pos g.fresh.1 :: drop (k - 1) l)) at h₁,
      rw vars_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at h₂,
      have := ih _ h₁ h₂,
      rw ← clause.vars_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at this,
      exact finset.mem_union_right _ (this (mem_vars_cons_of_mem_vars _ h)) } }
end

theorem not_mem_tseitin_xor_vars_of_not_mem_vars_of_not_mem_stock
  (hdis : disjoint g.stock (clause.vars l)) :
  v ∉ (clause.vars l) → v ∉ g.stock → v ∉ (tseitin_xor hk hp l g).vars :=
begin
  induction l using strong_induction_on_lists with l ih generalizing g,
  by_cases hl : length l ≤ k,
  { rw [tseitin_base_case hk hp hl, vars_direct_xor l], tautology },
  { intros hvars hg,
    rw tseitin_xor,
    simp [hl],
    rw cnf.vars_append,
    apply finset.not_mem_union.mpr,
    split,
    { rw [vars_direct_xor, clause.vars_append],
      apply finset.not_mem_union.mpr,
      split,
      { intro hcon,
        have := (vars_subset_of_subset (take_subset (k - 1) l)),
        exact absurd (this hcon) hvars },
      { simp [var],
        intro hcon,
        rw hcon at hg,
        exact absurd (fresh_mem_stock g) hg } },
    { have h₁ := drop_len_lt (Pos g.fresh.1) hk (not_le.mp hl),
      have h₂ := disjoint_fresh_of_disjoint hdis,
      have h₃ : v ∉ clause.vars (Pos g.fresh.1 :: drop (k - 1) l),
      { simp [clause.vars, var],
        rintros (rfl | h),
        { exact hg (fresh_mem_stock g) },
        { exact hvars (vars_subset_of_subset (drop_subset (k - 1) l) h) } },
      have h₄ : v ∉ g.fresh.2.stock,
      { intro hcon,
        exact hg ((fresh_stock_subset g) hcon) },
      rw perm.length_eq (hp (Pos g.fresh.1 :: drop (k - 1) l)) at h₁,
      rw vars_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at h₂ h₃,
      exact ih _ h₁ h₂ h₃ h₄ } }
end

lemma tseitin_forward (hdis : disjoint g.stock (clause.vars l)) : 
  Xor.eval τ l = tt → ∃ (σ : assignment V),
  (tseitin_xor hk hp l g).eval σ = tt ∧ (eqod τ σ (clause.vars l)) :=
begin
  intro he,
  induction l using strong_induction_on_lists with l ih generalizing g τ,
  by_cases hl : length l ≤ k,
  { use τ, rw [tseitin_base_case hk hp hl, eval_direct_xor_eq_eval_Xor], simp [he] },
  {
    rw [eval_eq_bodd_count_tt,
      ← (take_append_drop (k - 1) l), clause.count_tt_append, bodd_add] at he,

    have hnotmem := set.disjoint_left.mp hdis (g.fresh_mem_stock),
    have h₁ := drop_len_lt (Pos g.fresh.1) hk (not_le.mp hl),
    have h₂ := disjoint_fresh_of_disjoint hdis,
    rw perm.length_eq (hp (Pos g.fresh.1 :: drop (k - 1) l)) at h₁,
    rw vars_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at h₂,
    have htakevars := vars_subset_of_subset (take_subset (k - 1) l),
    have hdropvars := vars_subset_of_subset (drop_subset (k - 1) l),

    rw tseitin_xor,
    simp [hl, cnf.eval_append],

    -- Case on the truth value of the last n - k + 1 variables
    -- Note: the proof is symmetric, so any tightening-up can be done in both
    cases hc : bodd (clause.count_tt τ (take (k - 1) l)),
    { rw [hc, bool.bxor_ff_left] at he,
      rcases exists_eqod_and_eq_of_not_mem τ ff hnotmem with ⟨γ, heqod, hg⟩,
      have : bodd (clause.count_tt γ (Pos g.fresh.1 :: drop (k - 1) l)) = tt,
      { simp only [clause.count_tt_cons, literal.eval, hg, cond,
          ← count_tt_eq_of_eqod (eqod_subset hdropvars heqod), he] },
      rw [← eval_eq_bodd_count_tt, eval_eq_of_perm (hp (Pos g.fresh.1 :: drop (k - 1) l))] at this,

      -- Apply the induction hypothesis
      rcases (ih _ h₁ h₂ this) with ⟨γ₂, he₂, hg₂⟩,

      have heqod₂ : eqod (assignment.ite (cnf.vars (tseitin_xor hk hp (p (Pos g.fresh.1 :: (l.drop (k - 1)))) g.fresh.2)) γ₂ γ) γ (clause.vars l),
      { intros v hv,
        by_cases hmem : v ∈ clause.vars (l.drop (k - 1)),
        { have h₃ := mem_vars_cons_of_mem_vars (Pos g.fresh.1) hmem,
          rw vars_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at h₃,
          rw [ite_pos (mem_tseitin_xor_vars_of_mem_vars hk hp h₂ h₃), hg₂ v h₃] },
        { have hdis₂ := set.disjoint_right.mp hdis hv,
          have hne : v ≠ g.fresh.1,
          { intro hcon,
            exact (hcon ▸ hdis₂) (fresh_mem_stock g) },
          have : v ∉ clause.vars (Pos g.fresh.1 :: drop (k - 1) l),
          { simp [clause.vars, var],
            rintros (hcon | hcon),
            { exact hne hcon },
            { exact hmem hcon } },
          rw vars_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at this,
          have hstock : v ∉ g.fresh.2.stock,
          { intro hcon,
            exact hdis₂ ((fresh_stock_subset g) hcon) },
          rw ite_neg (not_mem_tseitin_xor_vars_of_not_mem_vars_of_not_mem_stock hk hp h₂ this hstock) } },
        
      use assignment.ite (cnf.vars (tseitin_xor hk hp (p (Pos g.fresh.1 :: (l.drop (k - 1)))) g.fresh.2)) γ₂ γ,
      split,
      { split,
        { simp [eval_direct_xor_eq_eval_Xor, eval_eq_bodd_count_tt, 
            clause.count_tt_append, bodd_add, literal.eval, hg],
          have : g.fresh.1 ∈ clause.vars (Pos g.fresh.1 :: (l.drop (k - 1))),
          { exact mem_vars_cons_self _ _ },
          rw vars_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at this,
          simp [ite_pos (mem_tseitin_xor_vars_of_mem_vars hk hp h₂ this), 
            ← (hg₂ g.fresh.1 this), hg,
            count_tt_eq_of_eqod (eqod_subset htakevars heqod₂),
            ← count_tt_eq_of_eqod (eqod_subset htakevars heqod), hc] },
        { exact he₂ ▸ eval_eq_of_eqod (ite_eqod _ _ _) } },
      { exact eqod.trans heqod (heqod₂.symm) } },
    { simp only [hc, bnot_eq_true_eq_eq_ff, tt_bxor] at he,
        rcases exists_eqod_and_eq_of_not_mem τ tt hnotmem with ⟨γ, heqod, hg⟩,
        have : bodd (clause.count_tt γ (Pos g.fresh.1 :: drop (k - 1) l)) = tt,
        { simp only [clause.count_tt_cons, literal.eval, hg, cond, 
            ← count_tt_eq_of_eqod (eqod_subset hdropvars heqod), he, bodd_succ,
            bodd_add, bodd_zero, bool.bnot_ff, bxor_tt_left], },
        rw [← eval_eq_bodd_count_tt, eval_eq_of_perm (hp (Pos g.fresh.1 :: drop (k - 1) l))] at this,

        -- Apply the induction hypothesis
        rcases (ih _ h₁ h₂ this) with ⟨γ₂, he₂, hg₂⟩,

        have heqod₂ : eqod (assignment.ite (cnf.vars (tseitin_xor hk hp (p (Pos g.fresh.1 :: (l.drop (k - 1)))) g.fresh.2)) γ₂ γ) γ (clause.vars l),
        { intros v hv,
          by_cases hmem : v ∈ clause.vars (l.drop (k - 1)),
          { have h₃ := mem_vars_cons_of_mem_vars (Pos g.fresh.1) hmem,
            rw vars_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at h₃,
            rw [ite_pos (mem_tseitin_xor_vars_of_mem_vars hk hp h₂ h₃), hg₂ v h₃] },
          { have hdis₂ := set.disjoint_right.mp hdis hv,
            have hne : v ≠ g.fresh.1,
            { intro hcon,
              exact (hcon ▸ hdis₂) (fresh_mem_stock g) },
            have : v ∉ clause.vars (Pos g.fresh.1 :: drop (k - 1) l),
            { simp [clause.vars, var],
              rintros (hcon | hcon),
              { exact hne hcon },
              { exact hmem hcon } },
            rw vars_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at this,
            have hstock : v ∉ g.fresh.2.stock,
            { intro hcon,
              exact hdis₂ ((fresh_stock_subset g) hcon) },
            rw ite_neg (not_mem_tseitin_xor_vars_of_not_mem_vars_of_not_mem_stock hk hp h₂ this hstock) } },
        
        use assignment.ite (cnf.vars (tseitin_xor hk hp (p (Pos g.fresh.1 :: (l.drop (k - 1)))) g.fresh.2)) γ₂ γ,
        split,
        { split,
          { simp [eval_direct_xor_eq_eval_Xor, eval_eq_bodd_count_tt, 
              clause.count_tt_append, bodd_add, literal.eval, hg],
            have : g.fresh.1 ∈ clause.vars (Pos g.fresh.1 :: (l.drop (k - 1))),
            { exact mem_vars_cons_self _ _ },
            rw vars_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at this,
            simp [ite_pos (mem_tseitin_xor_vars_of_mem_vars hk hp h₂ this), 
              ← (hg₂ g.fresh.1 this), hg,
              count_tt_eq_of_eqod (eqod_subset htakevars heqod₂),
              ← count_tt_eq_of_eqod (eqod_subset htakevars heqod), hc] },
          { exact he₂ ▸ eval_eq_of_eqod (ite_eqod _ _ _) } },
        { exact eqod.trans heqod heqod₂.symm } } } 
end

lemma tseitin_reverse (hdis : disjoint g.stock (clause.vars l)) :
  cnf.eval τ (tseitin_xor hk hp l g) = tt → Xor.eval τ l = tt :=
begin
  intro he,
  induction l using strong_induction_on_lists with l ih generalizing g,
  by_cases hl : length l ≤ k,
  { rw [tseitin_base_case hk hp hl, eval_direct_xor_eq_eval_Xor] at he, exact he },
  { rw tseitin_xor at he,
    simp [hl, cnf.eval_append] at he,
    rcases he with ⟨hdir, hrec⟩,
    have h₁ := drop_len_lt (Pos g.fresh.1) hk (not_le.mp hl),
    have h₂ := disjoint_fresh_of_disjoint hdis,
    rw perm.length_eq (hp (Pos g.fresh.1 :: drop (k - 1) l)) at h₁,
    rw vars_perm (hp (Pos g.fresh.1 :: drop (k - 1) l)) at h₂,
    have ihred := ih _ h₁ h₂ hrec,
    rw eval_direct_xor_eq_eval_Xor at hdir,
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

theorem tseitin_xor_encodes_Xor (hdis : disjoint g.stock (clause.vars l)) :
  encodes Xor (tseitin_xor hk hp l g) l :=
begin
  intro τ,
  split,
  { exact tseitin_forward hk hp hdis },
  { rintros ⟨σ, he, heqod⟩,
    rw [← Xor.eval, Xor.eval_eq_of_eqod heqod],
    exact tseitin_reverse hk hp hdis he }
end

def linear_perm (l : list (literal V)) : list (literal V) := l

lemma linear_perm_is_perm : ∀ (l : list (literal V)), l ~ linear_perm l :=
begin
  intro l,
  rw linear_perm
end

def linear_xor (l : list (literal V)) (g : gensym V) : cnf V :=
  tseitin_xor hk linear_perm_is_perm l g

theorem linear_xor_encodes_Xor (hdis : disjoint g.stock (clause.vars l)) :
  encodes Xor (linear_xor hk l g) l :=
tseitin_xor_encodes_Xor hk linear_perm_is_perm hdis

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

def pooled_xor (l : list (literal V)) (g : gensym V) : cnf V :=
  tseitin_xor hk pooled_perm_is_perm l g

theorem pooled_xor_encodes_Xor (hdis : disjoint g.stock (clause.vars l)) :
  encodes Xor (pooled_xor hk l g) l :=
tseitin_xor_encodes_Xor hk pooled_perm_is_perm hdis

end tseitin_xor