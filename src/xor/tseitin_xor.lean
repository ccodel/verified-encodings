/-
This file contains the development of the Tseitin encoding for XOR.
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
open nxor
open encoding

open list
open assignment
open function

namespace tseitin_xor

lemma disjoint_fresh_of_disjoint {x : nxor V} {g : gensym V} {k : nat} (hk : k ≥ 3) :
  disjoint g.stock x.vars → 
  disjoint g.fresh.2.stock (nxor.vars ((Pos g.fresh.1) :: (x.drop (k - 1)))) :=
begin
  intro h,
  apply set.disjoint_right.mpr,
  intros v hv,
  simp [vars, clause.vars] at hv,
  rcases hv with rfl | hv,
  { rw var,
    exact gensym.fresh_not_mem_fresh_stock g },
  { intro hcon,
    have := clause.vars_subset_of_subset (drop_subset (k - 1) x),
    rw set.disjoint_right at h,
    exact absurd ((gensym.fresh_stock_subset g) hcon) (h (this hv)) }
end

lemma drop_len_lt {k : nat} {x : nxor V} (l : literal V) :
  k ≥ 3 → length x > k → length (l :: (x.drop (k - 1))) < length x :=
begin
  intros hk hx,
  rw length_cons,
  rcases exists_append_of_gt_length hx with ⟨x₁, x₂, rfl, hx₁⟩,
  simp only [hx₁, length_drop, length_append],
  rw [add_comm k x₂.length, nat.add_sub_assoc (nat.sub_le k 1),
      nat.sub_sub_self (nat.le_of_add_le_right hk), add_assoc],
  apply add_lt_add_left,
  exact nat.succ_le_iff.mp hk,
end

-- Note: x and g can be made implicit args
def linear_xor {k : nat} (hk : k ≥ 3) : Π (x : nxor V), Π (g : gensym V),
  (disjoint g.stock x.vars) → cnf V
| x g hdis := if h : length x ≤ k then direct_xor x else
                have length ((Pos g.fresh.1) :: (x.drop (k - 1))) < length x,
                  from (drop_len_lt _ hk (not_le.mp h)),
                (direct_xor (x.take (k - 1) ++ [(Neg g.fresh.1)])) ++
                (linear_xor ((Pos g.fresh.1) :: (x.drop (k - 1))) (g.fresh.2)
                (disjoint_fresh_of_disjoint hk hdis))
using_well_founded {
  rel_tac := λ a b, `[exact ⟨_, measure_wf (λ σ, list.length σ.1)⟩],
  dec_tac := tactic.assumption
}

lemma linear_base_case {k : nat} (hk : k ≥ 3) {x : nxor V} {g : gensym V}
  (hdis : disjoint g.stock x.vars) : 
  length x ≤ k → linear_xor hk x g hdis = direct_xor x :=
assume h, by { rw linear_xor, simp only [h, if_true] }

theorem mem_linear_xor_vars_of_mem_vars {k : nat} (hk : k ≥ 3) {x : nxor V} {g : gensym V}
  (hdis : disjoint g.stock x.vars) {v : V} :
  v ∈ x.vars → v ∈ (linear_xor hk x g hdis).vars :=
begin
  induction x using strong_induction_on_lists with x ih generalizing g,
  by_cases hx : length x ≤ k,
  { rw linear_base_case hk hdis hx, rw vars_direct_xor, exact id },
  { intro h,
    rw linear_xor,
    simp [hx],
    rw [← take_append_drop (k - 1) x, vars, clause.vars_append] at h,
    rw cnf.vars_append,
    rcases finset.mem_union.mp h with (h | h),
    { apply finset.mem_union_left,
      rw [vars_direct_xor, vars, clause.vars_append],
      exact finset.mem_union_left _ h },
    { rw not_le at hx,
      have h₁ := drop_len_lt (Pos g.fresh.1) hk hx,
      have h₂ := disjoint_fresh_of_disjoint hk hdis,
      have := ih _ h₁ h₂ (clause.mem_vars_cons_of_mem_vars _ h),
      exact finset.mem_union_right _ this } }
end

theorem not_mem_linear_xor_vars_of_not_mem_vars_of_not_mem_stock {k : nat} (hk : k ≥ 3) {x : nxor V} {g : gensym V}
  (hdis : disjoint g.stock x.vars) {v : V} :
  v ∉ x.vars → v ∉ g.stock → v ∉ (linear_xor hk x g hdis).vars :=
begin
  induction x using strong_induction_on_lists with x ih generalizing g,
  by_cases hx : length x ≤ k,
  { rw [linear_base_case hk hdis hx, vars_direct_xor x], tautology },
  { intros hvars hg,
    rw linear_xor,
    simp [hx],
    rw cnf.vars_append,
    apply finset.not_mem_union.mpr,
    rw vars at hvars,
    split,
    { rw [vars_direct_xor, vars, clause.vars_append],
      apply finset.not_mem_union.mpr,
      split,
      { intro hcon,
        have := (clause.vars_subset_of_subset (take_subset (k - 1) x)),
        exact absurd (this hcon) hvars },
      { simp [var],
        intro hcon,
        rw hcon at hg,
        exact absurd (gensym.fresh_mem_stock g) hg } },
    { have h₁ := drop_len_lt (Pos g.fresh.1) hk (not_le.mp hx),
      have h₂ := disjoint_fresh_of_disjoint hk hdis,
      have h₃ : v ∉ vars (Pos g.fresh.1 :: drop (k - 1) x),
      { simp [vars, clause.vars, var],
        rintros (rfl | h),
        { exact hg (gensym.fresh_mem_stock g) },
        { exact hvars (vars_subset_of_subset (drop_subset (k - 1) x) h) } },
      have h₄ : v ∉ g.fresh.2.stock,
      { intro hcon,
        exact hg ((gensym.fresh_stock_subset g) hcon) },
      exact ih _ h₁ h₂ h₃ h₄ } }
end

-- A slightly stronger statement
lemma linear_forward {k : nat} (hk : k ≥ 3) {x : nxor V} {g : gensym V}
  (hdis : disjoint g.stock x.vars) {α : assignment V} :
  cnf.eval α (linear_xor hk x g hdis) = tt → cnf.eval α (direct_xor x) = tt :=
begin
  induction x using strong_induction_on_lists with x ih generalizing g,
  by_cases hx : length x ≤ k,
  { rw linear_base_case hk hdis hx, exact id },
  { intro h,
    rw linear_xor at h,
    simp [hx, cnf.eval_append] at h,
    rcases h with ⟨hdir, hrec⟩,
    rw not_le at hx,
    have h₁ := drop_len_lt (Pos g.fresh.1) hk hx,
    have h₂ := disjoint_fresh_of_disjoint hk hdis,
    have ihred := ih _ h₁ h₂ hrec,
    rw [eval_direct_xor_eq_eval_nxor, eval_eq_bodd_count_tt] at ihred,
    rw [eval_direct_xor_eq_eval_nxor, eval_eq_bodd_count_tt] at hdir,
    rw [eval_direct_xor_eq_eval_nxor, eval_eq_bodd_count_tt],
    have := take_append_drop (k - 1) x,
    have := congr_arg ((clause.count_tt α)) this,
    have := congr_arg (nat.bodd) this,
    cases hnew : (α g.fresh.1),
    { simp [count_tt_cons, hnew, literal.eval] at ihred,
      simp [count_tt_append, hnew, literal.eval] at hdir,
      rw [count_tt_append, nat.bodd_add, hdir, ihred, ff_bxor] at this,
      exact this.symm },
    { simp [count_tt_cons, hnew, literal.eval] at ihred,
      simp [count_tt_append, hnew, literal.eval] at hdir,
      rw [count_tt_append, nat.bodd_add, hdir, ihred, bxor_ff] at this,
      exact this.symm } }
end

theorem linear_sequiv {k : nat} (hk : k ≥ 3) {x : nxor V} {g : gensym V}
  (hdis : disjoint g.stock x.vars) :
  sequiv (linear_xor hk x g hdis) (direct_xor x) x.vars :=
begin
  induction x using strong_induction_on_lists with x ih generalizing g,
  by_cases hx : length x ≤ k,
  { rw linear_base_case hk hdis hx },
  { intro τ,
    split,
    -- forward direction: linear -> direct
    { rintros ⟨σ, hl, hs⟩,
      use [σ, linear_forward hk hdis hl, hs] },
    -- reverse direction: direct -> linear
    { rintros ⟨σ, he, hs⟩,

      rw [eval_direct_xor_eq_eval_nxor, eval_eq_bodd_count_tt] at he,
      have htakedrop := take_append_drop (k - 1) x,
      have hnotmem := set.disjoint_left.mp hdis (g.fresh_mem_stock),
      rw [← htakedrop, count_tt_append, nat.bodd_add] at he, 

      have h₁ := drop_len_lt (Pos g.fresh.1) hk (not_le.mp hx),
      have h₂ := disjoint_fresh_of_disjoint hk hdis, 

      rw linear_xor,
      simp [hx, cnf.eval_append],

      cases hc : nat.bodd (clause.count_tt σ (take (k - 1) x)),
      { simp [hc] at he,
        rcases exists_eqod_and_eq_of_not_mem σ ff hnotmem with ⟨γ, heqod, hg⟩,
        have : nat.bodd (clause.count_tt γ (Pos g.fresh.1 :: drop (k - 1) x)) = tt,
        { simp only [count_tt_cons, literal.eval, hg, cond],
          rw ← count_tt_eq_of_eqod (eqod_subset (vars_subset_of_subset (drop_subset (k - 1) x)) heqod),
          exact he },
        rw [← eval_eq_bodd_count_tt, ← eval_direct_xor_eq_eval_nxor] at this,

        -- Apply the induction hypothesis
        rcases (ih _ h₁ h₂ γ).mpr ⟨γ, this, eqod.refl _ _⟩ with ⟨γ₂, he₂, hg₂⟩,
        have hg₂copy := hg₂,
        rw [vars, clause.vars, var] at hg₂copy,
        have := eqod_subset (finset.subset_union_right {g.fresh.1} (clause.vars (x.drop (k - 1)))) hg₂copy,

        have bigeqod : eqod (assignment.ite (cnf.vars (linear_xor hk (Pos g.fresh.1 :: (x.drop (k - 1))) g.fresh.2 h₂)) γ₂ γ) γ (clause.vars x),
        {
          intros v hv,
          by_cases hmem : v ∈ vars (x.drop (k - 1)),
          { rw vars at hmem,
            have h₃ := clause.mem_vars_cons_of_mem_vars (Pos g.fresh.1) hmem,
            have := mem_linear_xor_vars_of_mem_vars hk h₂ h₃,
            rw ite_pos _ _ this,
            rw hg₂ v h₃ },
          {
            have hdis₂ := set.disjoint_right.mp hdis hv,
            have hne : v ≠ g.fresh.1,
            { intro hcon,
              rw hcon at hdis₂,
              exact hdis₂ (gensym.fresh_mem_stock g) },
            have : v ∉ vars (Pos g.fresh.1 :: drop (k - 1) x),
            { simp [vars, clause.vars, var],
              rintros (hcon | hcon),
              { exact hne hcon },
              { rw vars at hmem, exact hmem hcon } },
            have hdis₃ := gensym.fresh_stock_subset g,
            have hstock : v ∉ g.fresh.2.stock,
            { intro hcon,
              exact hdis₂ (hdis₃ hcon) },
            have := not_mem_linear_xor_vars_of_not_mem_vars_of_not_mem_stock hk h₂ this hstock,
            rw ite_neg _ _ this } },
        
        use assignment.ite (cnf.vars (linear_xor hk (Pos g.fresh.1 :: (x.drop (k - 1))) g.fresh.2 h₂)) γ₂ γ,
        
        split,
        { split,
          { simp [eval_direct_xor_eq_eval_nxor, eval_eq_bodd_count_tt, 
              count_tt_append, nat.bodd_add, literal.eval, hg],
            have : g.fresh.1 ∈ vars (Pos g.fresh.1 :: (x.drop (k - 1))),
            { exact mem_vars_cons_self _ _ },
            have := mem_linear_xor_vars_of_mem_vars hk h₂ this,
            rw ite_pos _ _ this,
            have := clause.mem_vars_cons_self (Pos g.fresh.1) (x.drop (k - 1)),
            rw var at this,
            rw ← (hg₂ g.fresh.1 this),
            simp [hg],
            have := eqod_subset (vars_subset_of_subset (take_subset (k - 1) x)) bigeqod,
            rw count_tt_eq_of_eqod this,
            rw ← count_tt_eq_of_eqod (eqod_subset (vars_subset_of_subset (take_subset (k - 1) x)) heqod),
            exact hc },
          { rw eval_eq_cnf_of_eqod (ite_eqod _ _ _),
            exact he₂ } },
        { exact eqod.trans (eqod.trans hs heqod) bigeqod.symm } },
      { sorry, } } }
end

-- Note: The proofs here are symmetric with the linear encoding ones
-- If an improvement is made to the above proofs, simplify here

lemma drop_len_lt' {k : nat} {x : nxor V} (l : literal V) :
  k ≥ 3 → length x > k → length (x.drop (k - 1) ++ [l]) < length x :=
begin
  have : (drop (k - 1) x ++ [l]).length = (l :: drop (k - 1) x).length,
  { simp only [length, length_append] },
  rw this,
  exact drop_len_lt l
end

lemma disjoint_fresh_of_disjoint' {x : nxor V} {g : gensym V} {k : nat} (hk : k ≥ 3) :
  disjoint g.stock x.vars → 
  disjoint g.fresh.2.stock (nxor.vars (x.drop (k - 1) ++ [Pos g.fresh.1])) :=
begin
  intro h,
  apply set.disjoint_right.mpr,
  intros v hv,
  simp [vars, clause.vars, clause.vars_append] at hv,
  rcases hv with rfl | hv,
  { rw var,
    exact gensym.fresh_not_mem_fresh_stock g },
  { intro hcon,
    have := clause.vars_subset_of_subset (drop_subset (k - 1) x),
    rw set.disjoint_right at h,
    exact absurd ((gensym.fresh_stock_subset g) hcon) (h (this hv)) }
end

-- Note: x and g can be made implicit args
def pooled_xor {k : nat} (hk : k ≥ 3) : Π (x : nxor V), Π (g : gensym V),
  (disjoint g.stock x.vars) → cnf V
| x g hdis := if h : length x ≤ k then direct_xor x else
                have length (x.drop (k - 1) ++ [Pos g.fresh.1]) < length x,
                  from (drop_len_lt' _ hk (not_le.mp h)),
                (direct_xor (x.take (k - 1) ++ [(Neg g.fresh.1)])) ++
                (pooled_xor (x.drop (k - 1) ++ [Pos g.fresh.1]) (g.fresh.2)
                (disjoint_fresh_of_disjoint' hk hdis))
using_well_founded {
  rel_tac := λ a b, `[exact ⟨_, measure_wf (λ σ, list.length σ.1)⟩],
  dec_tac := tactic.assumption
}

lemma pooled_base_case {k : nat} (hk : k ≥ 3) {x : nxor V} {g : gensym V}
  (hdis : disjoint g.stock x.vars) : 
  length x ≤ k → pooled_xor hk x g hdis = direct_xor x :=
assume h, by { rw pooled_xor, simp only [h, if_true] }

theorem mem_pooled_xor_vars_of_mem_vars {k : nat} (hk : k ≥ 3) {x : nxor V} {g : gensym V}
  (hdis : disjoint g.stock x.vars) {v : V} :
  v ∈ x.vars → v ∈ (pooled_xor hk x g hdis).vars :=
begin
  induction x using strong_induction_on_lists with x ih generalizing g,
  by_cases hx : length x ≤ k,
  { rw pooled_base_case hk hdis hx, rw vars_direct_xor, exact id },
  { intro h,
    rw pooled_xor,
    simp [hx],
    rw [← take_append_drop (k - 1) x, vars, clause.vars_append] at h,
    rw cnf.vars_append,
    rcases finset.mem_union.mp h with (h | h),
    { apply finset.mem_union_left,
      rw [vars_direct_xor, vars, clause.vars_append],
      exact finset.mem_union_left _ h },
    { rw not_le at hx,
      have h₁ := drop_len_lt' (Pos g.fresh.1) hk hx,
      have h₂ := disjoint_fresh_of_disjoint' hk hdis,
      have h₃ : v ∈ vars (drop (k - 1) x ++ [Pos g.fresh.1]),
      { rw [vars, clause.vars_append],
        exact finset.mem_union_left _ h },
      have := ih _ h₁ h₂ h₃,
      exact finset.mem_union_right _ this } }
end

theorem not_mem_pooled_xor_vars_of_not_mem_vars_of_not_mem_stock {k : nat} (hk : k ≥ 3) {x : nxor V} {g : gensym V}
  (hdis : disjoint g.stock x.vars) {v : V} :
  v ∉ x.vars → v ∉ g.stock → v ∉ (pooled_xor hk x g hdis).vars :=
begin
  induction x using strong_induction_on_lists with x ih generalizing g,
  by_cases hx : length x ≤ k,
  { rw [pooled_base_case hk hdis hx, vars_direct_xor x], tautology },
  { intros hvars hg,
    rw pooled_xor,
    simp [hx],
    rw cnf.vars_append,
    apply finset.not_mem_union.mpr,
    rw vars at hvars,
    split,
    { rw [vars_direct_xor, vars, clause.vars_append],
      apply finset.not_mem_union.mpr,
      split,
      { intro hcon,
        have := (clause.vars_subset_of_subset (take_subset (k - 1) x)),
        exact absurd (this hcon) hvars },
      { simp [var],
        intro hcon,
        rw hcon at hg,
        exact absurd (gensym.fresh_mem_stock g) hg } },
    { have h₁ := drop_len_lt' (Pos g.fresh.1) hk (not_le.mp hx),
      have h₂ := disjoint_fresh_of_disjoint' hk hdis,
      have h₃ : v ∉ vars (drop (k - 1) x ++ [Pos g.fresh.1]),
      { simp [vars, clause.vars, var, clause.vars_append],
        rintros (h | rfl),
        { exact hvars (vars_subset_of_subset (drop_subset (k - 1) x) h) },
        { exact hg (gensym.fresh_mem_stock g) } },
      have h₄ : v ∉ g.fresh.2.stock,
      { intro hcon,
        exact hg ((gensym.fresh_stock_subset g) hcon) },
      exact ih _ h₁ h₂ h₃ h₄ } }
end

end tseitin_xor