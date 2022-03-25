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
open amo

-- NOTES: Proofs need to be cleaned up
--        Lemmas? The theorem length_lt_length_cons may be useful

variables {l : list (literal V)} {lit l₁ l₂ : literal V} {g : gensym V}
          {τ : assignment V} (hdis : disjoint g.stock (clause.vars l))
          {c : clause V}

lemma disjoint_fresh_of_disjoint : disjoint g.stock (clause.vars (lit :: l)) → 
  disjoint g.fresh.2.stock (clause.vars l) :=
begin
  intro hdis,
  apply set.disjoint_right.mpr,
  intros v hv,
  have := (vars_subset_of_vars_cons lit l) hv,
  have := set.disjoint_right.mp hdis this,
  exact set.not_mem_subset (fresh_stock_subset g) this
end

lemma disjoint_fresh_of_disjoint_of_subset {l₂ : list (literal V)} : 
  disjoint g.stock (clause.vars l) → l₂ ⊆ l → disjoint g.fresh.2.stock (clause.vars l₂) :=
begin
  intros hdis hss,
  apply set.disjoint_right.mpr,
  intros v hv,
  have := (clause.vars_subset_of_subset hss) hv,
  have := set.disjoint_right.mp hdis this,
  exact set.not_mem_subset (fresh_stock_subset g) this
end

-- NOTE: Only well-defined for lists with lengths ≥ 2
def sinz : Π (l : list (literal V)), Π (g : gensym V),
  (disjoint g.stock (clause.vars l)) → cnf V
| []               _ _            := []
| [l₁]             g hdis         := [] --[[l₁.flip, Pos (g.fresh.1)]] -- may be unneeded
| (l₁ :: l₂ :: ls) g hdis         := 
    [l₁.flip, Pos (g.fresh.1)] :: 
    [Neg g.fresh.1, Pos g.fresh.2.fresh.1] ::
    [Neg g.fresh.1, l₂.flip] ::
    (sinz (l₂ :: ls) g.fresh.2 (disjoint_fresh_of_disjoint hdis))

theorem mem_sinz_vars_of_mem : length l ≥ 2 → clause.vars l ⊆ cnf.vars (sinz l g hdis) :=
begin
  intro hlen,
  induction l using strong_induction_on_lists with l ih generalizing g,
  rcases exists_cons_cons_of_length_ge_two hlen with ⟨l₁, l₂, ls, rfl⟩,
  intros v hv,
  rw sinz,
  simp [clause.vars] at hv,
  rcases hv with (rfl | rfl | hv),
  { simp [cnf.vars, clause.vars, flip_var_eq] },
  { simp [cnf.vars, clause.vars, flip_var_eq] },
  { cases ls with l₃ ls,
    { rw clause.vars_nil at hv,
      exact absurd hv (finset.not_mem_empty _) },
    { have hlen' : length (l₂ :: l₃ :: ls) ≥ 2, dec_trivial,
      have hless : length (l₂ :: l₃ :: ls) < length (l₁ :: l₂ :: l₃ :: ls), simp,
      have hdis' := disjoint_fresh_of_disjoint hdis,
      simp [cnf.vars],
      right, right, right,
      exact (ih _ hless hlen' hdis') (vars_subset_of_vars_cons l₂ (l₃ :: ls) hv) } }
end

theorem mem_or_mem_of_mem_vars {v : V} : v ∈ cnf.vars (sinz l g hdis) → 
  v ∈ clause.vars l ∨ v ∈ g.stock :=
begin
  induction l using strong_induction_on_lists with l ih generalizing g,
  cases l with l₁ ls,
  { rw [sinz, cnf.vars_nil], intro h, exact absurd h (finset.not_mem_empty _) },
  cases ls with l₂ ls,
  { rw [sinz, cnf.vars_nil], intro h, exact absurd h (finset.not_mem_empty _) },
  rw sinz,
  intro h,
  simp [cnf.vars, clause.vars, flip_var_eq, var] at h,
  rcases h with (rfl | rfl | rfl | rfl | rfl | h),
  { left, simp [clause.vars] },
  { exact or.inr (fresh_mem_stock g) },
  { exact or.inr (fresh_fresh_mem_stock g) },
  { exact or.inr (fresh_mem_stock g) },
  { left, simp [clause.vars] },
  { cases ls with l₃ ls,
    { rw [sinz, cnf.vars_nil] at h,
      exact absurd h (finset.not_mem_empty _) },
    { have hlen := length_lt_length_cons l₁ (l₂ :: l₃ :: ls),
      have hdis' := disjoint_fresh_of_disjoint hdis,
      rcases ih _ hlen hdis' h with (hv | hv),
      { exact or.inl ((vars_subset_of_vars_cons l₁ _) hv) },
      { exact or.inr (fresh_stock_subset g hv) } } }
end

theorem not_mem_sinz_vars_of_not_mems {v : V} : v ∉ clause.vars l → 
  v ∉ g.stock → v ∉ cnf.vars (sinz l g hdis) :=
begin
  intros hvar hstock,
  induction l using strong_induction_on_lists with l ih generalizing g,
  cases l with l₁ ls,
  { simp [sinz] },
  cases ls with l₂ ls,
  { simp [sinz] },
  have hg₁ : v ≠ g.fresh.1,
  { exact (ne_of_mem_of_not_mem (fresh_mem_stock g) hstock).symm },
  have hg₂ : v ≠ g.fresh.2.fresh.1,
  { exact (ne_of_mem_of_not_mem (fresh_fresh_mem_stock g) hstock).symm },
  cases ls with l₃ ls,
  { simp [clause.vars, not_or_distrib] at hvar,
    rcases hvar with ⟨hvar₁, hvar₂⟩,
    simp [sinz, cnf.vars, clause.vars, not_or_distrib, flip_var_eq, var,
      hvar₁, hvar₂, hg₁, hg₂] },
  { rw sinz,
    have hvar' : v ∉ clause.vars (l₂ :: l₃ :: ls),
    { rw clause.vars at hvar,
      simp only [not_or_distrib, finset.mem_union, finset.mem_singleton] at hvar,
      exact hvar.2 },
    have hless : length (l₂ :: l₃ :: ls) < length (l₁ :: l₂ :: l₃ :: ls), simp,
    have hdis' := disjoint_fresh_of_disjoint hdis,
    have : v ∉ g.fresh.2.stock,
    { intro hcon,
      exact hstock ((fresh_stock_subset g) hcon) },
    have ihred := ih _ hless hvar' hdis' this,
    simp [clause.vars, not_or_distrib] at hvar,
    rcases hvar with ⟨hvar₁, hvar₂, hvar₃, hvar⟩,
    simp [cnf.vars, clause.vars, not_or_distrib, flip_var_eq, var,
      hvar₁, hvar₂, hvar₃, hg₁, hg₂, ihred] }
end

/-
theorem sinz_amz : amz.eval τ l = tt → 
  (sinz l g hdis).eval (assignment.ite (clause.vars l) τ all_ff) = tt :=
begin
  induction l using strong_induction_on_lists with l ih generalizing g,
  cases l with l₁ ls,
  { simp [sinz] },
  { cases ls with l₂ ls,
    { simp [sinz] },
    { intro hamz,
      have hdis' := disjoint_fresh_of_disjoint hdis,
      rw [eval_tt_iff_forall_clause_eval_tt, sinz],
      intros c hc,
      simp at hc,
      rw eval_tt_iff_exists_literal_eval_tt,
      rcases hc with (rfl | rfl | rfl | hc),
      { use l₁.flip,
        rw [eval_flip,ite_pos_lit (mem_vars_of_mem (mem_cons_self l₁ _))],
        rw amz.eval_tt_iff_forall_eval_ff at hamz,
        simp [hamz l₁ (mem_cons_self l₁ _)] },
      { use Neg g.fresh.1,
        have := set.disjoint_left.mp hdis (fresh_mem_stock g), -- TODO why not ellide?
        simp [literal.eval, ite_neg this, all_ff] },
      { use Neg g.fresh.1,
        have := set.disjoint_left.mp hdis (fresh_mem_stock g), -- TODO why not ellide?
        simp [literal.eval, ite_neg this, all_ff] },
      { have hlen : length (l₂ :: ls) < length (l₁ :: l₂ :: ls), simp,
        have := ih (l₂ :: ls) hlen hdis' (amz.eval_tt_of_eval_tt_cons hamz),
        rw eval_tt_iff_forall_clause_eval_tt at this,
        rcases eval_tt_iff_exists_literal_eval_tt.mp (this c hc) with ⟨l, hlc, hl⟩,
        use [l, hlc],
        by_cases hlmem : (l.var ∈ clause.vars (l₂ :: ls)),
        { rw ite_pos_lit (vars_subset_of_vars_cons l₁ (l₂ :: ls) hlmem),
          rw ite_pos_lit hlmem at hl,
          exact hl },
        { rw ite_neg_lit hlmem at hl,
          by_cases h₁ : l₁.var ∈ clause.vars (l₂ :: ls),
          { have : l.var ∉ clause.vars (l₁ :: l₂ :: ls),
            { rw clause.vars,
              intro hcon,
              rcases finset.mem_union.mp hcon with (hcon | hcon),
              { simp at hcon,
                rw ← hcon at h₁,
                exact hlmem h₁ },
              { exact hlmem hcon } },
            rw ite_neg_lit this,
            exact hl },
          { have := mem_vars_of_mem (mem_cons_self l₁ (l₂ :: ls)),
            have := set.disjoint_right.mp hdis this,
            have := set.not_mem_subset (fresh_stock_subset g) this,
            have h₁' := not_mem_sinz_vars_of_not_mems hdis' h₁ this,
            have := clause_vars_subset_of_vars_of_mem hc
              (mem_vars_of_mem hlc),
            --have : l.var ≠ l₁.var, library_search,
            have := ne_of_mem_of_not_mem this h₁',
            have : l.var ∉ clause.vars (l₁ :: l₂ :: ls),
            { rw clause.vars,
              simp [not_or_distrib],
              exact ⟨this, hlmem⟩ },
            rw ite_neg_lit this,
            exact hl } } } } }
end
-/

-- NOTE: This theorem and the above are very similar, fixes to one go to other
theorem sinz_amz' : amz.eval τ l = tt →
  (sinz l g hdis).eval (assignment.ite (clause.vars l) τ all_tt) = tt :=
begin
  induction l using strong_induction_on_lists with l ih generalizing g,
  cases l with l₁ ls,
  { simp [sinz] },
  { cases ls with l₂ ls,
    { simp [sinz] },
    { intro hamz,
      have hdis' := disjoint_fresh_of_disjoint hdis,
      rw [eval_tt_iff_forall_clause_eval_tt, sinz],
      intros c hc,
      simp at hc,
      rw eval_tt_iff_exists_literal_eval_tt,
      rcases hc with (rfl | rfl | rfl | hc),
      { use l₁.flip,
        rw [eval_flip, ite_pos_lit (mem_vars_of_mem (mem_cons_self l₁ _))],
        rw amz.eval_tt_iff_forall_eval_ff at hamz,
        simp [hamz l₁ (mem_cons_self l₁ _)] },
      { use Pos g.fresh.2.fresh.1,
        have := set.disjoint_left.mp hdis (fresh_fresh_mem_stock g),
        simp [literal.eval, ite_neg this, all_tt] },
      { use l₂.flip,
        have : l₂.var ∈ clause.vars (l₁ :: l₂ :: ls), simp [clause.vars],
        rw [eval_flip, ite_pos_lit this],
        rw amz.eval_tt_iff_forall_eval_ff at hamz,
        simp [hamz l₂ (mem_cons_of_mem _ (mem_cons_self l₂ _))] },
      { have hlen : length (l₂ :: ls) < length (l₁ :: l₂ :: ls), simp,
        have := ih (l₂ :: ls) hlen hdis' (amz.eval_tt_of_eval_tt_cons hamz),
        rw eval_tt_iff_forall_clause_eval_tt at this,
        rcases eval_tt_iff_exists_literal_eval_tt.mp (this c hc) with ⟨l, hlc, hl⟩,
        use [l, hlc],
        by_cases hlmem : (l.var ∈ clause.vars (l₂ :: ls)),
        { rw ite_pos_lit (vars_subset_of_vars_cons l₁ (l₂ :: ls) hlmem),
          rw ite_pos_lit hlmem at hl,
          exact hl },
        { rw ite_neg_lit hlmem at hl,
          by_cases h₁ : l₁.var ∈ clause.vars (l₂ :: ls),
          { have : l.var ∉ clause.vars (l₁ :: l₂ :: ls),
            { rw clause.vars,
              intro hcon,
              rcases finset.mem_union.mp hcon with (hcon | hcon),
              { simp at hcon,
                rw ← hcon at h₁,
                exact hlmem h₁ },
              { exact hlmem hcon } },
            rw ite_neg_lit this,
            exact hl },
          { have := mem_vars_of_mem (mem_cons_self l₁ (l₂ :: ls)),
            have := set.disjoint_right.mp hdis this,
            have := set.not_mem_subset (fresh_stock_subset g) this,
            have h₁' := not_mem_sinz_vars_of_not_mems hdis' h₁ this,
            have := clause_vars_subset_of_vars_of_mem hc
              (mem_vars_of_mem hlc),
            --have : l.var ≠ l₁.var, library_search,
            have := ne_of_mem_of_not_mem this h₁',
            have : l.var ∉ clause.vars (l₁ :: l₂ :: ls),
            { rw clause.vars,
              simp [not_or_distrib],
              exact ⟨this, hlmem⟩ },
            rw ite_neg_lit this,
            exact hl } } } } }
end

theorem sinz_amo (hdis : disjoint g.stock (clause.vars (l₁ :: l))) : 
  amz.eval τ l = tt → l₁.eval τ = tt → 
  (sinz (l₁ :: l) g hdis).eval (assignment.ite (clause.vars (l₁ :: l)) τ all_tt) = tt :=
begin
  intros hamz h₁,
  cases l with l₂ ls,
  { simp [sinz] },
  { rw [eval_tt_iff_forall_clause_eval_tt, sinz],
    intros c hc,
    simp at hc,
    rw eval_tt_iff_exists_literal_eval_tt,
    rcases hc with (rfl | rfl | rfl | hc),
    { use Pos g.fresh.1,
      have := set.disjoint_left.mp hdis (fresh_mem_stock g),
      simp [literal.eval, ite_neg this, all_tt] },
    { use Pos g.fresh.2.fresh.1,
      have := set.disjoint_left.mp hdis (fresh_fresh_mem_stock g),
      simp [literal.eval, ite_neg this, all_tt] },
    { use l₂.flip,
      have : l₂.var ∈ clause.vars (l₁ :: l₂ :: ls), simp [clause.vars],
      rw [eval_flip, ite_pos_lit this],
      rw amz.eval_tt_iff_forall_eval_ff at hamz,
      simp [hamz l₂ (mem_cons_self l₂ _)] },
    {
      have hdis' := disjoint_fresh_of_disjoint hdis,
      have := sinz_amz' hdis' hamz,
      rw eval_tt_iff_forall_clause_eval_tt at this,
      rcases eval_tt_iff_exists_literal_eval_tt.mp (this c hc) with ⟨l, hlc, hl⟩,
      use [l, hlc],
      have := cnf.clause_vars_subset_of_vars_of_mem hc,
      rcases mem_or_mem_of_mem_vars hdis' (this (mem_vars_of_mem hlc)) with (hv | hv),
      { rw ite_pos_lit (mem_vars_cons_of_mem_vars l₁ hv),
        rw ite_pos_lit hv at hl,
        exact hl },
      { have := set.disjoint_left.mp hdis (fresh_stock_subset g hv),
        rw ite_neg_lit this,
        rw clause.vars at this,
        simp [not_or_distrib] at this,
        rw ite_neg_lit this.2 at hl,
        exact hl } } }
end

theorem sinz_signal (hdis : disjoint g.stock (clause.vars (l₁ :: l))) :
  τ g.fresh.1 = tt → (sinz (l₁ :: l) g hdis).eval τ = tt → 
  ∀ (lit : literal V), lit ∈ l → lit.eval τ = ff :=
begin
  sorry,
  /-
  intro ht,
  induction l using strong_induction_on_lists with l ih generalizing g,
  cases l with l₂ ls,
  { simp [sinz] },
  intros heval lit hlit,
  rw [sinz, eval_tt_iff_forall_clause_eval_tt] at heval,
  simp at heval,
  rcases heval with ⟨h₁, h₂, h₃, h₄⟩,
  have hlen : length ls < length (l₂ :: ls), simp,
  have hdis' : disjoint g.fresh.2.stock (clause.vars (l₁ :: ls)),
  {
    apply set.disjoint_right.mpr,
    intros v hv,
    have : clause.vars (l₁ :: ls) ⊆ clause.vars (l₁ :: l₂ :: ls),
    { apply clause.vars_subset_of_subset,
      simp [subset_cons_of_subset l₁ (subset_cons l₂ ls)] },
    have := this hv,
    have := set.disjoint_right.mp hdis this,
    intro hcon,
    exact this (fresh_stock_subset g hcon) },
    have ihred := ih _ hlen hdis',
    sorry

   simp [sinz, eval_tt_iff_forall_clause_eval_tt],
    rintros ht hc₁ hc₂ hc₃ rfl,
    simp [eval_tt_iff_exists_literal_eval_tt] at hc₃,
    rcases hc₃ with ⟨l, (rfl | rfl), hl⟩,
    { rw [literal.eval, ht] at hl, contradiction },
    { simp [eval_flip] at hl, exact hl } },
  {
    intros ht heval,
    rw [sinz, eval_tt_iff_forall_clause_eval_tt] at heval,
    simp at heval,
    have hlen : length (l₃ :: ls) < length (l₂ :: l₃ :: ls), simp,
    have hdis' := disjoint_fresh_of_disjoint hdis,
    have ihred := (ih _ hlen hdis'),

  }
  -/
end

#exit

theorem sinz_base_case (hdis : disjoint g.stock (clause.vars [l₁, l₂])) : 
  encodes amo (sinz [l₁, l₂] g hdis) [l₁, l₂] :=
begin
  intro τ,
  split,
  { intro hamo,
    cases h₁ : (literal.eval τ l₁),
    { use assignment.ite (clause.vars [l₁, l₂]) τ all_ff,
      split,
      { have hnmem₁ : g.fresh.1 ∉ clause.vars [l₁, l₂],
        { have := set.disjoint_left.mp hdis (fresh_mem_stock g), assumption },
        rw eval_tt_iff_forall_clause_eval_tt,
        intros c hc,
        simp [sinz] at hc,
        rw eval_tt_iff_exists_literal_eval_tt,
        rcases hc with (rfl | rfl | rfl),
        { use l₁.flip,
          have hmem₁ : l₁.flip.var ∈ clause.vars [l₁, l₂],
          { simp [flip_var_eq, clause.vars] },
          rw [ite_pos_lit hmem₁, eval_flip],
          simp [h₁] },
        { use Neg g.fresh.1,
          simp [literal.eval, ite_neg hnmem₁, all_ff] },
        { use Neg g.fresh.1,
          simp [literal.eval, ite_neg hnmem₁, all_ff]
        } },
      { exact (ite_eqod _ _ _).symm } },
    { rw [← amo.eval, eval_cons_pos h₁] at hamo,
      use [(assignment.ite (clause.vars [l₁, l₂]) τ all_tt),
        sinz_amo hdis hamo h₁, (ite_eqod _ _ _).symm] } },
  { rintros ⟨σ, heval, heqod⟩,
    have heq : literal.eval τ l₂ = literal.eval σ l₂,
    { have : l₂.var ∈ clause.vars [l₁, l₂],
      { simp [clause.vars] },
        exact eval_eq_of_eqod_of_var_mem heqod this },
      rw [← amo.eval, eval_eq_amo_of_eqod heqod],
      rw eval_tt_iff_forall_clause_eval_tt at heval,
      cases h₁ : (literal.eval σ l₁),
      { rw [eval_cons_neg h₁, amo.eval_singleton] },
      { have : ∀ (lit₁ lit₂ : literal V), (distinct lit₁ lit₂ [l₁, l₂]) → 
          lit₁.eval τ = tt → lit₂.eval τ = ff,
        { intros lit₁ lit₂ hd _,
          rcases eq_of_distinct_double hd with ⟨rfl, rfl⟩,
          simp [sinz, clause.eval, eval_flip, literal.eval, h₁] at heval,
          rcases heval with ⟨hs₁, hs₂, hs₃⟩,
          simp [hs₁] at hs₃,
          rw heq,
          exact hs₃ },
        rw ← eval_eq_amo_of_eqod heqod,
        exact amo_eval_tt_iff_distinct_eval_ff_of_eval_tt.mpr this } }
end

theorem sinz_encodes_amo : encodes amo (sinz l g hdis) l :=
begin
  induction l using strong_induction_on_lists with l ih generalizing g,
  cases l with l₁ ls,
  { intro τ, simp [sinz] },
  cases ls with l₂ ls,
  { intro τ, simp [sinz], use τ },

  have hdis' := disjoint_fresh_of_disjoint hdis,

  cases ls with l₃ ls,
  { exact sinz_base_case hdis },
  { intro τ, 
    have hlen : length (l₂ :: l₃ :: ls) < length (l₁ :: l₂ :: l₃ :: ls), simp,
    have ihred := (ih _ hlen hdis') τ,
    split,
    { intro hamo,
      cases h₁ : (literal.eval τ l₁),
      { rcases ihred.mp (eval_tt_of_eval_tt_cons hamo) with ⟨σ, heval', hs⟩,
        use assignment.ite (cnf.vars (sinz (l₂ :: l₃ :: ls) g.fresh.2 hdis')) σ 
            (assignment.ite {l₁.var} τ all_ff),
        have heval₁ : literal.eval (assignment.ite (cnf.vars (sinz (l₂ :: l₃ :: ls) g.fresh.2 hdis')) σ 
            (assignment.ite {l₁.var} τ all_ff)) l₁ = ff,
        { by_cases h : (l₁.var ∈ cnf.vars (sinz (l₂ :: l₃ :: ls) g.fresh.2 hdis')),
          { rw ite_pos_lit h,
            rcases mem_or_mem_of_mem_vars hdis' h with (hv | hv),
            { rw ← eval_eq_of_eqod_of_var_mem hs hv,
              exact h₁ },
            { have : l₁.var ∈ clause.vars (l₁ :: l₂ :: l₃ :: ls),
              { rw clause.vars,
                exact finset.mem_union.mpr (or.inl (finset.mem_singleton_self l₁.var)) },
              have := set.disjoint_right.mp hdis this,
              have := (fresh_stock_subset g) hv,
              contradiction } },
          { rw ite_neg_lit h,
            rw ite_pos_lit (finset.mem_singleton_self l₁.var),
            exact h₁ } },
        have heval₂ : (assignment.ite (cnf.vars (sinz (l₂ :: l₃ :: ls) g.fresh.2 hdis')) σ 
            (assignment.ite {l₁.var} τ all_ff)) g.fresh.1 = ff,
        { 
          have h₀ := set.disjoint_left.mp hdis (fresh_mem_stock g),
          have h₁ : g.fresh.1 ∉ clause.vars (l₂ :: l₃ :: ls),
          { rw clause.vars at h₀,
            simp [not_or_distrib] at h₀,
            exact h₀.2 },
          have h₂ : g.fresh.1 ∉ g.fresh.2.stock,
          { exact fresh_not_mem_fresh_stock g },
          rw ite_neg (not_mem_sinz_vars_of_not_mems hdis' h₁ h₂),
          rw clause.vars at h₀,
          simp [not_or_distrib] at h₀,
          have : g.fresh.1 ∉ {l₁.var},
          { rw finset.mem_singleton,
            exact h₀.1 },
          rw [ite_neg this, all_ff] },
        split,
        { rw [eval_tt_iff_forall_clause_eval_tt, sinz],
          intros c hc,
          rw eval_tt_iff_exists_literal_eval_tt,
          simp at hc,
          rcases hc with (rfl | rfl | rfl | hc),
          { use l₁.flip,
            simp [eval_flip, heval₁] },
          { use Neg g.fresh.1,
            simp [literal.eval, heval₂] },
          { use Neg g.fresh.1,
            simp [literal.eval, heval₂] },
          { rw ← eval_tt_iff_exists_literal_eval_tt,
            rw eval_tt_iff_forall_clause_eval_tt at heval',
            rw ← heval' c hc,
            apply eval_eq_clause_of_eqod,
            apply eqod_subset (clause_vars_subset_of_vars_of_mem hc),
            intros v hv,
            rw ite_pos hv } },
        { intros v hv,
          rcases finset.mem_union.mp hv with (hvmem | hvmem),
          { cases l₁;
            { simp [literal.flip, literal.eval, var] at h₁ hvmem heval₁ |-,
              simp [heval₁, hvmem, h₁] } },
          { have : length (l₂ :: l₃ :: ls) ≥ 2, dec_trivial,
            rw ite_pos (mem_sinz_vars_of_mem hdis' this hvmem),
            exact hs v hvmem } } },
      { rw [← amo.eval, eval_cons_pos h₁] at hamo,
        use [(assignment.ite (clause.vars (l₁ :: l₂ :: l₃ :: ls)) τ all_tt),
        sinz_amo hdis hamo h₁, 
        (ite_eqod (clause.vars (l₁ :: l₂ :: l₃ :: ls)) τ _).symm] } },
    { rintros ⟨σ, heval, heqod⟩,
      cases h₁ : (literal.eval τ l₁),
      { rw [eval_tt_iff_forall_clause_eval_tt, sinz] at heval,
        simp at heval,
        rcases heval with ⟨hc₁, hc₂, hc₃, hc₄⟩,
        rw ← eval_tt_iff_forall_clause_eval_tt at hc₄,
        rw [← amo.eval, eval_cons_neg h₁],
        exact ihred.mpr ⟨σ, hc₄, eqod_subset (vars_subset_of_vars_cons _ _) heqod⟩ },
      { rw [← amo.eval, eval_cons_pos h₁],
        cases hf : (σ g.fresh.1),
        { rw [eval_tt_iff_forall_clause_eval_tt] at heval,
          have : [l₁.flip, Pos (g.fresh.1)] ∈ sinz (l₁ :: l₂ :: l₃ :: ls) g hdis,
          { exact mem_cons_self _ _ },
          have := heval _ this,
          simp [eval_tt_iff_exists_literal_eval_tt] at this,
          rcases this with ⟨w, (rfl | rfl), hw⟩,
          { rw [eval_flip, ← h₁] at hw, -- This can be cleaned up
            have := eval_eq_of_eqod_of_var_mem heqod (mem_vars_of_mem (mem_cons_self l₁ _)),
            rw h₁ at this,
            simp [← this] at hw,
            rw ← hw at h₁,
            contradiction },
          { rw [literal.eval, hf] at hw,
            contradiction } },
        { rw amz.eval_eq_amz_of_eqod (eqod_subset (vars_subset_of_vars_cons l₁ (l₂ :: l₃ :: ls)) heqod),
          exact amz.eval_tt_iff_forall_eval_ff.mpr (sinz_signal hdis hf heval) } } } }
end

/-
theorem sinz_encodes_amo : length l ≥ 2 → encodes amo (sinz l g hdis) l :=
begin
  intros hl τ,
  induction l using strong_induction_on_lists with l ih generalizing g,
  rcases exists_cons_cons_of_length_ge_two hl with ⟨l₁, l₂, ls, rfl⟩,
  have hdis' := disjoint_fresh_of_disjoint hdis,
  have hmem₁ : l₁.flip.var ∈ clause.vars (l₁ :: l₂ :: ls),
  { simp [flip_var_eq, clause.vars] },
  have hmemnot₁ : l₁.flip.var ∉ g.stock,
  { exact set.disjoint_right.mp hdis hmem₁ },
  have hmem₂ : l₂.flip.var ∈ clause.vars (l₁ :: l₂ :: ls),
  { simp [flip_var_eq, clause.vars] },
  have hnmem₁ : g.fresh.1 ∉ clause.vars (l₁ :: l₂ :: ls),
  { have := set.disjoint_left.mp hdis (fresh_mem_stock g),
    assumption }, -- TODO coercion is silly
  have hnmem₂ : g.fresh.2.fresh.1 ∉ clause.vars (l₁ :: l₂ :: ls),
  { have := fresh_mem_stock g.fresh.2,
    have := set.disjoint_left.mp hdis (fresh_stock_subset g this),
    assumption }, -- TODO this too
  cases ls with l₃ ls,
  { sorry }, /-split,
    { intro heval,
      rw ← amo.eval at heval,
      cases h₁ : (literal.eval τ l₁),
      { use assignment.ite (clause.vars [l₁, l₂]) τ all_ff,
        split,
        { rw eval_tt_iff_forall_clause_eval_tt,
          intros c hc,
          simp [sinz] at hc,
          rw eval_tt_iff_exists_literal_eval_tt,
          rcases hc with (rfl | rfl | rfl),
          { use l₁.flip,
            rw [ite_pos_lit hmem₁, eval_flip],
            simp [h₁] },
          { use Neg g.fresh.1,
            simp [literal.eval, ite_neg hnmem₁, all_ff] },
          { use Neg g.fresh.1,
            simp [literal.eval, ite_neg hnmem₁, all_ff] } },
        { exact (ite_eqod (clause.vars [l₁, l₂]) τ _).symm } },
      { use assignment.ite (clause.vars [l₁, l₂]) τ all_tt,
        split,
        { rw eval_tt_iff_forall_clause_eval_tt,
          intros c hc,
          simp [sinz] at hc,
          rw eval_tt_iff_exists_literal_eval_tt,
          rcases hc with (rfl | rfl | rfl),
          { use Pos g.fresh.1,
            simp [literal.eval, ite_neg hnmem₁, all_tt] },
          { use Pos g.fresh.2.fresh.1,
            simp [literal.eval, ite_neg hnmem₂, all_tt] },
          { use l₂.flip,
            have := amo.amo_eval_tt_iff_distinct_eval_ff_of_eval_tt.mp heval,
            have := this (distinct_double l₁ l₂) h₁,
            simp [ite_pos_lit hmem₂],
            rw eval_flip,
            simp [this] } },
        { exact (ite_eqod (clause.vars [l₁, l₂]) τ _).symm } } },
    { rintros ⟨σ, heval, hs⟩,
    have heq : literal.eval τ l₂ = literal.eval σ l₂,
    { have : l₂.var ∈ clause.vars [l₁, l₂],
      { simp [clause.vars] },
        exact eval_eq_of_eqod_of_var_mem hs this },
      rw [← amo.eval, eval_eq_amo_of_eqod hs],
      rw eval_tt_iff_forall_clause_eval_tt at heval,
      cases h₁ : (literal.eval σ l₁),
      { rw [eval_cons_neg h₁, amo.eval_singleton] },
      { have : ∀ (lit₁ lit₂ : literal V), (distinct lit₁ lit₂ [l₁, l₂]) → 
          lit₁.eval τ = tt → lit₂.eval τ = ff,
        { intros lit₁ lit₂ hd _,
          rcases eq_of_distinct_double hd with ⟨rfl, rfl⟩,
          simp [sinz, clause.eval, eval_flip, literal.eval, h₁] at heval,
          rcases heval with ⟨hs₁, hs₂, hs₃⟩,
          simp [hs₁] at hs₃,
          rw heq,
          exact hs₃ },
        rw ← eval_eq_amo_of_eqod hs,
        exact amo_eval_tt_iff_distinct_eval_ff_of_eval_tt.mpr this } } }, -/
  { split,
    { intro heval,
      rw ← amo.eval at heval,
      have hless : length (l₂ :: l₃ :: ls) < length (l₁ :: l₂ :: l₃ :: ls), simp,
      have hlen : length (l₂ :: l₃ :: ls) ≥ 2, dec_trivial,
      have ihred := ih _ hless hlen hdis',
      cases h₁ : (literal.eval τ l₁),
      { sorry }, /- rw eval_cons_neg h₁ at heval,
        rcases ihred.mp heval with ⟨σ, heval', hs⟩,
        use assignment.ite (cnf.vars (sinz (l₂ :: l₃ :: ls) g.fresh.2 hdis')) σ 
            (assignment.ite {l₁.var} τ all_ff),
        have heval₁ : literal.eval (assignment.ite (cnf.vars (sinz (l₂ :: l₃ :: ls) g.fresh.2 hdis')) σ 
            (assignment.ite {l₁.var} τ all_ff)) l₁ = ff,
        { sorry },
        have heval₂ : (assignment.ite (cnf.vars (sinz (l₂ :: l₃ :: ls) g.fresh.2 hdis')) σ 
            (assignment.ite {l₁.var} τ all_ff)) g.fresh.1 = ff,
        { sorry },
        split,
        { rw [eval_tt_iff_forall_clause_eval_tt, sinz],
          intros c hc,
          rw eval_tt_iff_exists_literal_eval_tt,
          simp at hc,
          rcases hc with (rfl | rfl | rfl | hc),
          { use l₁.flip,
            simp [eval_flip, heval₁] },
          { use Neg g.fresh.1,
            simp [literal.eval, heval₂] },
          { use Neg g.fresh.1,
            simp [literal.eval, heval₂] },
          { rw ← eval_tt_iff_exists_literal_eval_tt,
            rw eval_tt_iff_forall_clause_eval_tt at heval',
            rw ← heval' c hc,
            apply eval_eq_clause_of_eqod,
            apply eqod_subset (clause_vars_subset_of_vars_of_mem hc),
            intros v hv,
            rw ite_pos hv } },
        { intros v hv,
          rcases finset.mem_union.mp hv with (hvmem | hvmem),
          { cases l₁;
            { simp [literal.flip, literal.eval, var] at h₁ hvmem heval₁ |-,
              simp [heval₁, hvmem, h₁] } },
          { rw ite_pos (mem_sinz_vars_of_mem hdis' hlen hvmem),
            exact hs v hvmem }
        } }, -/
      { sorry } },
      /-
      { rw eval_cons_pos h₁ at heval,
        rw amz.eval_tt_iff_forall_eval_ff at heval,
        use assignment.ite (clause.vars (l₁ :: l₂ :: l₃ :: ls)) τ all_tt,
        have heval₁ : literal.eval (assignment.ite (clause.vars (l₁ :: l₂ :: l₃ :: ls)) τ all_tt) l₁ = tt,
        { sorry },
        have heval₂ : (assignment.ite (clause.vars (l₁ :: l₂ :: l₃ :: ls)) τ all_tt) g.fresh.1 = tt,
        { sorry },
        have heval₃ : (assignment.ite (clause.vars (l₁ :: l₂ :: l₃ :: ls)) τ all_tt) g.fresh.2.fresh.1 = tt,
        { sorry },
        split,
        { rw [eval_tt_iff_forall_clause_eval_tt, sinz],
          intros c hc,
          simp at hc,
          rw eval_tt_iff_exists_literal_eval_tt,
          rcases hc with (rfl | rfl | rfl | hc),
          { use Pos g.fresh.1,
            simp [literal.eval, heval₂] },
          { use Pos g.fresh.2.fresh.1,
            simp [literal.eval, heval₃] },
          { use l₂.flip,
            rw [ite_pos_lit hmem₂, eval_flip],
            simp [ite_pos_lit hmem₂, eval_flip, heval l₂ (mem_cons_self l₂ _)] },
          { rw ← amz.eval_tt_iff_forall_eval_ff at heval,
            have := all_tt_eval_tt_of_amz_eval_tt hdis' hlen heval,
            rw eval_tt_iff_forall_clause_eval_tt at this,
            have := this c hc,
            rcases eval_tt_iff_exists_literal_eval_tt.mp this with ⟨l, hlmem, hle⟩,
            use [l, hlmem],
            by_cases hlin : l.var ∈ clause.vars (l₂ :: l₃ :: ls),
            { rw ite_pos_lit hlin at hle,
              rw ite_pos_lit (vars_subset_of_vars_cons l₁ (l₂ :: l₃ :: ls) hlin),
              exact hle },
            { rw ite_neg_lit hlin at hle,
              -- show l.var is not equal to l₁.var
              sorry } } },
        { intros v hv, rw ite_pos hv } } }, -/
    {
      rintros ⟨σ, heval, heqod⟩,
      rw [sinz, eval_tt_iff_forall_clause_eval_tt] at heval,
      simp at heval,
    }
  }
end
-/

end sinz_amo