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
open Xor
open encoding
open gensym

open nat
open list
open assignment
open function

namespace tseitin_xor

variables {l : list (literal V)} {g : gensym V} {k : nat} {v : V} {τ : assignment V}

lemma disjoint_fresh_of_disjoint (hk : k ≥ 3) : disjoint g.stock (clause.vars l) → 
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
      nat.sub_sub_self (nat.le_of_add_le_right hk), add_assoc],
  apply add_lt_add_left,
  exact succ_le_iff.mp hk,
end

-- Note: l and g can be made implicit args
def linear_xor (hk : k ≥ 3) : list (literal V) → gensym V → cnf V
| l g := if h : length l ≤ k then direct_xor l else
           have length ((Pos g.fresh.1) :: (l.drop (k - 1))) < length l,
             from (drop_len_lt _ hk (not_le.mp h)),
           (direct_xor (l.take (k - 1) ++ [(Neg g.fresh.1)])) ++
           (linear_xor ((Pos g.fresh.1) :: (l.drop (k - 1))) (g.fresh.2))
using_well_founded {
  rel_tac := λ a b, `[exact ⟨_, measure_wf (λ σ, list.length σ.1)⟩],
  dec_tac := tactic.assumption
}

lemma linear_base_case (hk : k ≥ 3) :
  length l ≤ k → linear_xor hk l g = direct_xor l :=
assume h, by { rw linear_xor, simp only [h, if_true] }

theorem mem_linear_xor_vars_of_mem_vars (hk : k ≥ 3)
  (hdis : disjoint g.stock (clause.vars l)) :
  v ∈ (clause.vars l) → v ∈ (linear_xor hk l g).vars :=
begin
  induction l using strong_induction_on_lists with l ih generalizing g,
  by_cases hl : length l ≤ k,
  { rw linear_base_case hk hl, rw vars_direct_xor, exact id },
  { intro h,
    rw linear_xor,
    simp [hl],
    rw [← take_append_drop (k - 1) l, clause.vars_append] at h,
    rw cnf.vars_append,
    rcases finset.mem_union.mp h with (h | h),
    { apply finset.mem_union_left,
      rw [vars_direct_xor, clause.vars_append],
      exact finset.mem_union_left _ h },
    { rw not_le at hl,
      have h₁ := drop_len_lt (Pos g.fresh.1) hk hl,
      have h₂ := disjoint_fresh_of_disjoint hk hdis,
      have := ih _ h₁ h₂ (mem_vars_cons_of_mem_vars _ h),
      exact finset.mem_union_right _ this } }
end

theorem not_mem_linear_xor_vars_of_not_mem_vars_of_not_mem_stock 
  (hk : k ≥ 3) (hdis : disjoint g.stock (clause.vars l)) :
  v ∉ (clause.vars l) → v ∉ g.stock → v ∉ (linear_xor hk l g).vars :=
begin
  induction l using strong_induction_on_lists with l ih generalizing g,
  by_cases hl : length l ≤ k,
  { rw [linear_base_case hk hl, vars_direct_xor l], tautology },
  { intros hvars hg,
    rw linear_xor,
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
      have h₂ := disjoint_fresh_of_disjoint hk hdis,
      have h₃ : v ∉ clause.vars (Pos g.fresh.1 :: drop (k - 1) l),
      { simp [clause.vars, var],
        rintros (rfl | h),
        { exact hg (fresh_mem_stock g) },
        { exact hvars (vars_subset_of_subset (drop_subset (k - 1) l) h) } },
      have h₄ : v ∉ g.fresh.2.stock,
      { intro hcon,
        exact hg ((fresh_stock_subset g) hcon) },
      exact ih _ h₁ h₂ h₃ h₄ } }
end

lemma linear_forward (hk : k ≥ 3) (hdis : disjoint g.stock (clause.vars l)) :
  Xor.eval τ l = tt → ∃ (σ : assignment V), 
  (linear_xor hk l g).eval σ = tt ∧ (τ≡(clause.vars l)≡σ) :=
begin
  intro he,
  induction l using strong_induction_on_lists with l ih generalizing g τ,
  by_cases hl : length l ≤ k,
  { use τ, rw [linear_base_case hk hl, eval_direct_xor_eq_eval_Xor], simp [he] },
  { rw [eval_eq_bodd_count_tt,
      ← (take_append_drop (k - 1) l), count_tt_append, bodd_add] at he,

    have hnotmem := set.disjoint_left.mp hdis (g.fresh_mem_stock),
    have h₁ := drop_len_lt (Pos g.fresh.1) hk (not_le.mp hl),
    have h₂ := disjoint_fresh_of_disjoint hk hdis,
    have htakevars := vars_subset_of_subset (take_subset (k - 1) l),
    have hdropvars := vars_subset_of_subset (drop_subset (k - 1) l),

    rw linear_xor,
    simp [hl, cnf.eval_append],

    -- Case on the truth value of the last n - k + 1 variables
    -- Note: the proof is symmetric, so any tightening-up can be done in both
    cases hc : bodd (clause.count_tt τ (take (k - 1) l)),
    { rw [hc, bool.bxor_ff_left] at he,
      rcases exists_eqod_and_eq_of_not_mem τ ff hnotmem with ⟨γ, heqod, hg⟩,
      have : bodd (clause.count_tt γ (Pos g.fresh.1 :: drop (k - 1) l)) = tt,
      { simp only [count_tt_cons, literal.eval, hg, cond,
          ← count_tt_eq_of_eqod (eqod_subset hdropvars heqod), he] },
      rw [← eval_eq_bodd_count_tt] at this,

      -- Apply the induction hypothesis
      rcases (ih _ h₁ h₂ this) with ⟨γ₂, he₂, hg₂⟩,

      have heqod₂ : eqod (assignment.ite (cnf.vars (linear_xor hk (Pos g.fresh.1 :: (l.drop (k - 1))) g.fresh.2)) γ₂ γ) γ (clause.vars l),
      { intros v hv,
        by_cases hmem : v ∈ clause.vars (l.drop (k - 1)),
        { have h₃ := mem_vars_cons_of_mem_vars (Pos g.fresh.1) hmem,
          rw [ite_pos (mem_linear_xor_vars_of_mem_vars hk h₂ h₃), hg₂ v h₃] },
        { have hdis₂ := set.disjoint_right.mp hdis hv,
          have hne : v ≠ g.fresh.1,
          { intro hcon,
            exact (hcon ▸ hdis₂) (fresh_mem_stock g) },
          have : v ∉ clause.vars (Pos g.fresh.1 :: drop (k - 1) l),
          { simp [clause.vars, var],
            rintros (hcon | hcon),
            { exact hne hcon },
            { exact hmem hcon } },
          have hstock : v ∉ g.fresh.2.stock,
          { intro hcon,
            exact hdis₂ ((fresh_stock_subset g) hcon) },
          rw ite_neg (not_mem_linear_xor_vars_of_not_mem_vars_of_not_mem_stock hk h₂ this hstock) } },
        
      use assignment.ite (cnf.vars (linear_xor hk (Pos g.fresh.1 :: (l.drop (k - 1))) g.fresh.2)) γ₂ γ,
      split,
      { split,
        { simp [eval_direct_xor_eq_eval_Xor, eval_eq_bodd_count_tt, 
            count_tt_append, bodd_add, literal.eval, hg],
          have : g.fresh.1 ∈ clause.vars (Pos g.fresh.1 :: (l.drop (k - 1))),
          { exact mem_vars_cons_self _ _ },
          simp [ite_pos (mem_linear_xor_vars_of_mem_vars hk h₂ this), 
            ← (hg₂ g.fresh.1 this), hg,
            count_tt_eq_of_eqod (eqod_subset htakevars heqod₂),
            ← count_tt_eq_of_eqod (eqod_subset htakevars heqod), hc] },
        { exact he₂ ▸ eval_eq_cnf_of_eqod (ite_eqod _ _ _) } },
      { exact eqod.trans heqod (heqod₂.symm) } },
    {
      simp only [hc, bnot_eq_true_eq_eq_ff, tt_bxor] at he,
        rcases exists_eqod_and_eq_of_not_mem τ tt hnotmem with ⟨γ, heqod, hg⟩,
        have : bodd (clause.count_tt γ (Pos g.fresh.1 :: drop (k - 1) l)) = tt,
        { simp only [count_tt_cons, literal.eval, hg, cond, 
            ← count_tt_eq_of_eqod (eqod_subset hdropvars heqod), he, bodd_succ, 
            bodd_add, bodd_zero, bool.bnot_false, bool.bxor_ff_right], },
        rw [← eval_eq_bodd_count_tt] at this,

        -- Apply the induction hypothesis
        rcases (ih _ h₁ h₂ this) with ⟨γ₂, he₂, hg₂⟩,

        have heqod₂ : eqod (assignment.ite (cnf.vars (linear_xor hk (Pos g.fresh.1 :: (l.drop (k - 1))) g.fresh.2)) γ₂ γ) γ (clause.vars l),
        { intros v hv,
          by_cases hmem : v ∈ clause.vars (l.drop (k - 1)),
          { have h₃ := mem_vars_cons_of_mem_vars (Pos g.fresh.1) hmem,
            rw [ite_pos (mem_linear_xor_vars_of_mem_vars hk h₂ h₃), hg₂ v h₃] },
          { have hdis₂ := set.disjoint_right.mp hdis hv,
            have hne : v ≠ g.fresh.1,
            { intro hcon,
              exact (hcon ▸ hdis₂) (fresh_mem_stock g) },
            have : v ∉ clause.vars (Pos g.fresh.1 :: drop (k - 1) l),
            { simp [clause.vars, var],
              rintros (hcon | hcon),
              { exact hne hcon },
              { exact hmem hcon } },
            have hstock : v ∉ g.fresh.2.stock,
            { intro hcon,
              exact hdis₂ ((fresh_stock_subset g) hcon) },
            rw ite_neg (not_mem_linear_xor_vars_of_not_mem_vars_of_not_mem_stock hk h₂ this hstock) } },
        
        use assignment.ite (cnf.vars (linear_xor hk (Pos g.fresh.1 :: (l.drop (k - 1))) g.fresh.2)) γ₂ γ,
        split,
        { split,
          { simp [eval_direct_xor_eq_eval_Xor, eval_eq_bodd_count_tt, 
              count_tt_append, bodd_add, literal.eval, hg],
            have : g.fresh.1 ∈ clause.vars (Pos g.fresh.1 :: (l.drop (k - 1))),
            { exact mem_vars_cons_self _ _ },
            simp [ite_pos (mem_linear_xor_vars_of_mem_vars hk h₂ this), 
              ← (hg₂ g.fresh.1 this), hg,
              count_tt_eq_of_eqod (eqod_subset htakevars heqod₂),
              ← count_tt_eq_of_eqod (eqod_subset htakevars heqod), hc] },
          { exact he₂ ▸ eval_eq_cnf_of_eqod (ite_eqod _ _ _) } },
        { exact eqod.trans heqod heqod₂.symm } } } 
end

lemma linear_reverse (hk : k ≥ 3) (hdis : disjoint g.stock (clause.vars l)) :
  cnf.eval τ (linear_xor hk l g) = tt → Xor.eval τ l = tt :=
begin
  intro he,
  induction l using strong_induction_on_lists with l ih generalizing g,
  by_cases hl : length l ≤ k,
  { rw [linear_base_case hk hl, eval_direct_xor_eq_eval_Xor] at he, exact he },
  { rw linear_xor at he,
    simp [hl, cnf.eval_append] at he,
    rcases he with ⟨hdir, hrec⟩,
    have h₁ := drop_len_lt (Pos g.fresh.1) hk (not_le.mp hl),
    have h₂ := disjoint_fresh_of_disjoint hk hdis,
    have ihred := ih _ h₁ h₂ hrec,
    rw eval_direct_xor_eq_eval_Xor at hdir,
    rw eval_eq_bodd_count_tt at ihred hdir |-,
    have := congr_arg ((clause.count_tt τ)) (take_append_drop (k - 1) l).symm,
    have := congr_arg bodd this,
    cases hnew : (τ g.fresh.1),
    { simp [count_tt_cons, count_tt_append, hnew, literal.eval] at ihred hdir,
      rw [count_tt_append, bodd_add, hdir, ihred, ff_bxor] at this,
      exact this },
    { simp [count_tt_cons, count_tt_append, hnew, literal.eval] at ihred hdir,
      rw [count_tt_append, bodd_add, hdir, ihred, bxor_ff] at this,
      exact this } }
end

theorem linear_xor_encodes_Xor (hk : k ≥ 3) (hdis : disjoint g.stock (clause.vars l)) :
  encodes Xor (linear_xor hk l g) l :=
begin
  intro τ,
  split,
  { exact linear_forward hk hdis },
  { rintros ⟨σ, he, heqod⟩,
    rw [← Xor.eval, eval_eq_Xor_of_eqod heqod],
    exact linear_reverse hk hdis he }
end

-- Note: The proofs here are symmetric with the linear encoding ones
-- If an improvement is made to the above proofs, simplify here

lemma drop_len_lt' (lit : literal V) (hk : k ≥ 3) :
  length l > k → length (l.drop (k - 1) ++ [lit]) < length l :=
begin
  have : (drop (k - 1) l ++ [lit]).length = (lit :: drop (k - 1) l).length,
  { simp only [length, length_append] },
  rw this,
  exact drop_len_lt lit hk
end

lemma disjoint_fresh_of_disjoint' (hk : k ≥ 3) :
  disjoint g.stock (clause.vars l) → 
  disjoint g.fresh.2.stock (clause.vars (l.drop (k - 1) ++ [Pos g.fresh.1])) :=
begin
  intro h,
  apply set.disjoint_right.mpr,
  intros v hv,
  simp [clause.vars, clause.vars_append] at hv,
  rcases hv with rfl | hv,
  { rw var,
    exact fresh_not_mem_fresh_stock g },
  { intro hcon,
    rw set.disjoint_right at h,
    have := vars_subset_of_subset (drop_subset (k - 1) l),
    exact absurd ((fresh_stock_subset g) hcon) (h (this hv)) }
end

-- Note: x and g can be made implicit args
def pooled_xor (hk : k ≥ 3) : Π (l : list (literal V)), Π (g : gensym V),
  (disjoint g.stock (clause.vars l)) → cnf V
| l g hdis := if h : length l ≤ k then direct_xor l else
                have length (l.drop (k - 1) ++ [Pos g.fresh.1]) < length l,
                  from (drop_len_lt' _ hk (not_le.mp h)),
                (direct_xor (l.take (k - 1) ++ [(Neg g.fresh.1)])) ++
                (pooled_xor (l.drop (k - 1) ++ [Pos g.fresh.1]) (g.fresh.2)
                (disjoint_fresh_of_disjoint' hk hdis))
using_well_founded {
  rel_tac := λ a b, `[exact ⟨_, measure_wf (λ σ, list.length σ.1)⟩],
  dec_tac := tactic.assumption
}

lemma pooled_base_case (hk : k ≥ 3) (hdis : disjoint g.stock (clause.vars l)) : 
  length l ≤ k → pooled_xor hk l g hdis = direct_xor l :=
assume h, by { rw pooled_xor, simp only [h, if_true] }

theorem mem_pooled_xor_vars_of_mem_vars (hk : k ≥ 3)
  (hdis : disjoint g.stock (clause.vars l)) :
  v ∈ (clause.vars l) → v ∈ (pooled_xor hk l g hdis).vars :=
begin
  induction l using strong_induction_on_lists with l ih generalizing g,
  by_cases hl : length l ≤ k,
  { rw pooled_base_case hk hdis hl, rw vars_direct_xor, exact id },
  { intro h,
    rw pooled_xor,
    simp [hl],
    rw [← take_append_drop (k - 1) l, clause.vars_append] at h,
    rw cnf.vars_append,
    rcases finset.mem_union.mp h with (h | h),
    { apply finset.mem_union_left,
      rw [vars_direct_xor, clause.vars_append],
      exact finset.mem_union_left _ h },
    { rw not_le at hl,
      have h₁ := drop_len_lt' (Pos g.fresh.1) hk hl,
      have h₂ := disjoint_fresh_of_disjoint' hk hdis,
      have h₃ : v ∈ clause.vars (drop (k - 1) l ++ [Pos g.fresh.1]),
      { rw [clause.vars_append],
        exact finset.mem_union_left _ h },
      have := ih _ h₁ h₂ h₃,
      exact finset.mem_union_right _ this } }
end

theorem not_mem_pooled_xor_vars_of_not_mem_vars_of_not_mem_stock
  (hk : k ≥ 3) (hdis : disjoint g.stock (clause.vars l)) :
  v ∉ (clause.vars l) → v ∉ g.stock → v ∉ (pooled_xor hk l g hdis).vars :=
begin
  induction l using strong_induction_on_lists with l ih generalizing g,
  by_cases hl : length l ≤ k,
  { rw [pooled_base_case hk hdis hl, vars_direct_xor l], tautology },
  { intros hvars hg,
    rw pooled_xor,
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
    { have h₁ := drop_len_lt' (Pos g.fresh.1) hk (not_le.mp hl),
      have h₂ := disjoint_fresh_of_disjoint' hk hdis,
      have h₃ : v ∉ clause.vars (drop (k - 1) l ++ [Pos g.fresh.1]),
      { simp [clause.vars, var, clause.vars_append],
        rintros (h | rfl),
        { exact hvars (vars_subset_of_subset (drop_subset (k - 1) l) h) },
        { exact hg (fresh_mem_stock g) } },
      have h₄ : v ∉ g.fresh.2.stock,
      { intro hcon,
        exact hg ((fresh_stock_subset g) hcon) },
      exact ih _ h₁ h₂ h₃ h₄ } }
end

lemma pooled_forward (hk : k ≥ 3) (hdis : disjoint g.stock (clause.vars l)) :
  cnf.eval τ (pooled_xor hk l g hdis) = tt → cnf.eval τ (direct_xor l) = tt :=
begin
  induction l using strong_induction_on_lists with l ih generalizing g,
  by_cases hl : length l ≤ k,
  { rw pooled_base_case hk hdis hl, exact id },
  { intro h,
    rw pooled_xor at h,
    simp [hl, cnf.eval_append] at h,
    rcases h with ⟨hdir, hrec⟩,
    have h₁ := drop_len_lt' (Pos g.fresh.1) hk (not_le.mp hl),
    have h₂ := disjoint_fresh_of_disjoint' hk hdis,
    have ihred := ih _ h₁ h₂ hrec,
    rw [eval_direct_xor_eq_eval_Xor, eval_eq_bodd_count_tt] at ihred hdir |-,
    have := congr_arg ((clause.count_tt τ)) (take_append_drop (k - 1) l).symm,
    have := congr_arg bodd this,
    cases hnew : (τ g.fresh.1),
    { simp [count_tt_cons, count_tt_append, hnew, literal.eval] at ihred hdir,
      rw [count_tt_append, bodd_add, hdir, ihred, ff_bxor] at this,
      exact this },
    { simp [count_tt_cons, count_tt_append, hnew, literal.eval] at ihred hdir,
      rw [count_tt_append, bodd_add, hdir, ihred, bxor_ff] at this,
      exact this } }
end

theorem pooled_sequiv (hk : k ≥ 3) (hdis : disjoint g.stock (clause.vars l)) :
  sequiv (pooled_xor hk l g hdis) (direct_xor l) (clause.vars l) :=
begin
  induction l using strong_induction_on_lists with l ih generalizing g,
  by_cases hl : length l ≤ k,
  { rw pooled_base_case hk hdis hl },
  { intro τ, split,
    -- forward direction: pooled -> direct
    { rintros ⟨σ, hl, hs⟩,
      use [σ, pooled_forward hk hdis hl, hs] },
    -- reverse direction: direct -> pooled 
    { rintros ⟨σ, he, hs⟩,

      rw [eval_direct_xor_eq_eval_Xor, eval_eq_bodd_count_tt,
        ← (take_append_drop (k - 1) l), count_tt_append, bodd_add] at he,

      have hnotmem := set.disjoint_left.mp hdis (g.fresh_mem_stock),
      have h₁ := drop_len_lt' (Pos g.fresh.1) hk (not_le.mp hl),
      have h₂ := disjoint_fresh_of_disjoint' hk hdis,

      have htakevars := vars_subset_of_subset (take_subset (k - 1) l),
      have hdropvars := vars_subset_of_subset (drop_subset (k - 1) l),

      rw pooled_xor,
      simp [hl, cnf.eval_append],

      -- Case on the truth value of the last n - k + 1 variables
      -- Note: the proof is symmetric, so any tightening-up can be done in both
      cases hc : bodd (clause.count_tt σ (take (k - 1) l)),
      { rw [hc, bool.bxor_ff_left] at he,
        rcases exists_eqod_and_eq_of_not_mem σ ff hnotmem with ⟨γ, heqod, hg⟩,
        have : bodd (clause.count_tt γ (drop (k - 1) l ++ [Pos g.fresh.1])) = tt,
        { simp [count_tt_append, literal.eval, hg, cond,
            ← count_tt_eq_of_eqod (eqod_subset hdropvars heqod), he] },
        rw [← eval_eq_bodd_count_tt, ← eval_direct_xor_eq_eval_Xor] at this,

        -- Apply the induction hypothesis
        rcases (ih _ h₁ h₂ γ).mpr ⟨γ, this, eqod.refl _ _⟩ with ⟨γ₂, he₂, hg₂⟩,

        have heqod₂ : eqod (assignment.ite (cnf.vars (pooled_xor hk (l.drop (k - 1) ++ [Pos g.fresh.1]) g.fresh.2 h₂)) γ₂ γ) γ (clause.vars l),
        { intros v hv,
          by_cases hmem : v ∈ clause.vars (l.drop (k - 1)),
          { have h₃ : v ∈ clause.vars (drop (k - 1) l ++ [Pos g.fresh.1]),
            { rw [clause.vars_append],
              exact finset.mem_union_left _ hmem },
            rw [ite_pos (mem_pooled_xor_vars_of_mem_vars hk h₂ h₃), hg₂ v h₃] },
          { have hdis₂ := set.disjoint_right.mp hdis hv,
            have hne : v ≠ g.fresh.1,
            { intro hcon,
              exact (hcon ▸ hdis₂) (fresh_mem_stock g) },
            have : v ∉ clause.vars (drop (k - 1) l ++ [Pos g.fresh.1]),
            { simp [clause.vars, var, clause.vars_append],
              rintros (hcon | hcon),
              { exact hmem hcon },
              { exact hne hcon } },
            have hstock : v ∉ g.fresh.2.stock,
            { intro hcon,
              exact hdis₂ ((fresh_stock_subset g) hcon) },
            rw ite_neg (not_mem_pooled_xor_vars_of_not_mem_vars_of_not_mem_stock hk h₂ this hstock) } },
        
        use assignment.ite (cnf.vars (pooled_xor hk (drop (k - 1) l ++ [Pos g.fresh.1]) g.fresh.2 h₂)) γ₂ γ,
        split,
        { split,
          { simp [eval_direct_xor_eq_eval_Xor, eval_eq_bodd_count_tt, 
              count_tt_append, bodd_add, literal.eval, hg],
            have : g.fresh.1 ∈ clause.vars (drop (k - 1) l ++ [Pos g.fresh.1]),
            { simp [clause.vars_append, var] },
            simp [ite_pos (mem_pooled_xor_vars_of_mem_vars hk h₂ this), 
              ← (hg₂ g.fresh.1 this), hg,
              count_tt_eq_of_eqod (eqod_subset htakevars heqod₂),
              ← count_tt_eq_of_eqod (eqod_subset htakevars heqod), hc] },
          { exact he₂ ▸ eval_eq_cnf_of_eqod (ite_eqod _ _ _) } },
        { exact eqod.trans (eqod.trans hs heqod) heqod₂.symm } },
      { simp only [hc, bnot_eq_true_eq_eq_ff, tt_bxor] at he,
        rcases exists_eqod_and_eq_of_not_mem σ tt hnotmem with ⟨γ, heqod, hg⟩,
        have : bodd (clause.count_tt γ (drop (k - 1) l ++ [Pos g.fresh.1])) = tt,
        { simp only [count_tt_append, literal.eval, hg, cond, 
            ← count_tt_eq_of_eqod (eqod_subset hdropvars heqod), he, bodd_succ,
            bool.bnot_false, count_tt_singleton, bodd_succ] },
        rw [← eval_eq_bodd_count_tt, ← eval_direct_xor_eq_eval_Xor] at this,

        -- Apply the induction hypothesis
        rcases (ih _ h₁ h₂ γ).mpr ⟨γ, this, eqod.refl _ _⟩ with ⟨γ₂, he₂, hg₂⟩,

        have heqod₂ : eqod (assignment.ite (cnf.vars (pooled_xor hk (drop (k - 1) l ++ [Pos g.fresh.1]) g.fresh.2 h₂)) γ₂ γ) γ (clause.vars l),
        { intros v hv,
          by_cases hmem : v ∈ clause.vars (l.drop (k - 1)),
          { have h₃ : v ∈ clause.vars (drop (k - 1) l ++ [Pos g.fresh.1]),
            { rw [clause.vars_append],
              exact finset.mem_union_left _ hmem },
            rw [ite_pos (mem_pooled_xor_vars_of_mem_vars hk h₂ h₃), hg₂ v h₃] },
          { have hdis₂ := set.disjoint_right.mp hdis hv,
            have hne : v ≠ g.fresh.1,
            { intro hcon,
              exact (hcon ▸ hdis₂) (fresh_mem_stock g) },
            have : v ∉ clause.vars (drop (k - 1) l ++ [Pos g.fresh.1]),
            { simp [clause.vars, var, clause.vars_append],
              rintros (hcon | hcon),
              { exact hmem hcon },
              { exact hne hcon } },
            have hstock : v ∉ g.fresh.2.stock,
            { intro hcon,
              exact hdis₂ ((fresh_stock_subset g) hcon) },
            rw ite_neg (not_mem_pooled_xor_vars_of_not_mem_vars_of_not_mem_stock hk h₂ this hstock) } },
        
        use assignment.ite (cnf.vars (pooled_xor hk (drop (k - 1) l ++ [Pos g.fresh.1]) g.fresh.2 h₂)) γ₂ γ,
        split,
        { split,
          { simp [eval_direct_xor_eq_eval_Xor, eval_eq_bodd_count_tt, 
              count_tt_append, bodd_add, literal.eval, hg],
            have : g.fresh.1 ∈ clause.vars (drop (k - 1) l ++ [Pos g.fresh.1]),
            { simp [clause.vars_append, var] },
            simp [ite_pos (mem_pooled_xor_vars_of_mem_vars hk h₂ this), 
              ← (hg₂ g.fresh.1 this), hg,
              count_tt_eq_of_eqod (eqod_subset htakevars heqod₂),
              ← count_tt_eq_of_eqod (eqod_subset htakevars heqod), hc] },
          { exact he₂ ▸ eval_eq_cnf_of_eqod (ite_eqod _ _ _) } },
        { exact eqod.trans (eqod.trans hs heqod) heqod₂.symm } } } }
end

theorem pooled_xor_encodes_Xor (hk : k ≥ 3) (hdis : disjoint g.stock (clause.vars l)) :
  encodes Xor (pooled_xor hk l g hdis) l :=
encodes_of_encodes_of_sequiv (direct_xor_encodes_Xor l) (pooled_sequiv hk hdis).symm

end tseitin_xor