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
import cardinality.amk
import cardinality.alk

import data.list.basic
import data.nat.basic

variables {V : Type*} [inhabited V] [decidable_eq V]

namespace sinz_amo

open nat
open list
open literal
open clause
open cnf
open assignment
open encoding
open distinct
open gensym
open amk
open alk

variables {l : list (literal V)} {g : gensym V}
          {τ : assignment V} (hdis : disjoint g.stock (clause.vars l))

@[inline] def xi_to_si (g : gensym V) (n i : nat) (lit : literal V) : cnf V :=
  if (i < n - 1) then [[lit.flip, Pos (g.nth i)]] else []

@[inline] def si_to_next_si (g : gensym V) (n i : nat) : cnf V :=
  if (i < n - 2) then [[Neg (g.nth i), Pos (g.nth (i + 1))]] else []

@[inline] def si_to_next_xi (g : gensym V) (i : nat) (lit : literal V) : cnf V :=
  if (0 < i) then [[Neg (g.nth (i - 1)), lit.flip]] else []

-- TODO: no need to case on length 0 and 1, because the length checks handle things?
def sinz_amo : enc_fn V
| []     g := ⟨[], g⟩
| [lit₁] g := ⟨[], g⟩
| l      g :=
  ⟨join (map_with_index (λ (idx : nat) (lit : literal V),
    xi_to_si g (length l) idx lit ++
    si_to_next_si g (length l) idx ++
    si_to_next_xi g idx lit) l),
  (g.nfresh (length l - 1)).2⟩

def nth_from_var (g : gensym V) (v : V) : nat → nat
| 0       := 0
| (i + 1) := if v = g.nth (i + 1) then i + 1 else nth_from_var i

theorem nth_from_var_eq_nth_of_le (g : gensym V) {i n : nat} (Hi : i ≤ n) :
  nth_from_var g (g.nth i) n = i :=
begin
  induction n with n ih generalizing i,
  { cases i,
    { refl },
    { rw nonpos_iff_eq_zero at Hi,
      exact absurd Hi (succ_ne_zero _) } },
  { by_cases hn : i = n.succ,
    { subst hn,
      simp [nth_from_var] },
    { simp [nth_from_var, nth_ne_of_ne hn],
      exact ih (le_of_lt_succ (lt_of_le_of_ne Hi hn)) } }
end

theorem xi_to_si_mem_sinz_amo (g : gensym V) {i : nat} (Hi : i < length l - 1) (Hi' : i < length l) :
  [(l.nth_le i Hi').flip, Pos (g.nth i)] ∈ (sinz_amo l g).1 :=
begin
  cases l with lit₁ ls, { simp at Hi, contradiction },
  cases ls with lit₂ ls, { simp at Hi, contradiction },
  rw sinz_amo,
  simp at Hi Hi',
  simp [-map_with_index_cons],
  use [((xi_to_si g (ls.length + 2) i ((lit₁ :: lit₂ :: ls).nth_le i Hi')) ++ 
      (si_to_next_si g (ls.length + 2) i) ++ 
      si_to_next_xi g i ((lit₁ :: lit₂ :: ls).nth_le i Hi')),
      ((lit₁ :: lit₂ :: ls).nth_le i Hi'), i, Hi'],
  { refl },
  { rw append_assoc },
  { simp [xi_to_si, Hi], left, refl }
end

theorem si_to_next_si_mem (g : gensym V) {i : nat} (Hi : i < length l - 2) :
  [Neg (g.nth i), Pos (g.nth (i + 1))] ∈ (sinz_amo l g).1 :=
begin
  cases l with lit₁ ls, { simp at Hi, contradiction },
  cases ls with lit₂ ls, { simp at Hi, contradiction },
  rw sinz_amo,
  simp at Hi,
  have Hi' : i < length (lit₁ :: lit₂ :: ls),
  { simp, exact lt_succ_of_lt (lt_succ_of_lt Hi) },
  simp [-map_with_index_cons],
  use [(xi_to_si g (ls.length + 2) i ((lit₁ :: lit₂ :: ls).nth_le i Hi') ++ 
       si_to_next_si g (ls.length + 2) i ++ 
      si_to_next_xi g i ((lit₁ :: lit₂ :: ls).nth_le i Hi')),
      ((lit₁ :: lit₂ :: ls).nth_le i Hi'), i, Hi'],
  { rw append_assoc },
  { simp [si_to_next_si, Hi] }
end

theorem si_to_next_xi_mem (g : gensym V) {i : nat} (Hi : i + 1 < length l) :
  [Neg (g.nth i), (l.nth_le (i + 1) Hi).flip] ∈ (sinz_amo l g).1 :=
begin
  cases l with lit₁ ls, { simp at Hi, contradiction },
  cases ls with lit₂ ls, { simp at Hi, contradiction },
  rw sinz_amo,
  have Hi' : i < length (lit₁ :: lit₂ :: ls),
  { simp at Hi, simp only [length], exact lt_succ_of_lt Hi },
  simp [-map_with_index_cons],
  use [(xi_to_si g (ls.length + 2) (i + 1) ((lit₁ :: lit₂ :: ls).nth_le (i + 1) Hi) ++ 
       si_to_next_si g (ls.length + 2) (i + 1) ++ 
      si_to_next_xi g (i + 1) ((lit₁ :: lit₂ :: ls).nth_le (i + 1) Hi)),
      ((lit₁ :: lit₂ :: ls).nth_le (i + 1) Hi), i + 1, Hi],
  { rw append_assoc },
  { simp [si_to_next_xi] }
end

-- If the var is in l, then use τ.
-- Otherwise, the signal variable is true if at least 1 variable before is true
def sinz_amo_tau (l : list (literal V)) (g : gensym V) (τ : assignment V) : assignment V :=
  aite (clause.vars l) τ (λ v, (alk 1).eval τ (l.take ((nth_from_var g v (length l - 1)) + 1)))

theorem sinz_amo_eval_tt_under_sinz_amo_tau (hdis : disj l g) : ∀ (τ : assignment V), 
  (amk 1).eval τ l = tt → (sinz_amo l g).1.eval (sinz_amo_tau l g τ) = tt :=
begin
  intros τ heval,
  cases l with lit₁ ls,
  { simp [sinz_amo] },
  cases ls with lit₂ ls,
  { simp [sinz_amo] },
  { rw eval_tt_iff_forall_clause_eval_tt,
    intros c hc,
    rw sinz_amo at hc,
    unfold prod.fst at hc,
    simp [-map_with_index_cons] at hc,
    rcases hc with ⟨f, ⟨lit, i, ⟨hi, rfl⟩, rfl⟩, hmemc⟩,
    simp only [mem_append] at hmemc,
    rcases hmemc with (hc | hc | hc),
    { unfold xi_to_si at hc,
      rcases eq_or_lt_of_le (le_of_lt_succ hi) with (rfl | hlt),
      { simp at hc, contradiction },
      { simp [hlt] at hc, subst hc,
        rw eval_tt_iff_exists_literal_eval_tt,
        cases halk : (alk 1).eval τ ((lit₁ :: lit₂ :: ls).take (i + 1)),
        { use [((lit₁ :: lit₂ :: ls).nth_le i hi).flip, mem_cons_self _ _],
          simp [eval_flip],
          rw [sinz_amo_tau, aite_pos_lit (mem_vars_of_mem (nth_le_mem (lit₁ :: lit₂ :: ls) i hi))],
          have hamk : !((alk 1).eval τ ((lit₁ :: lit₂ :: ls).take (i + 1))) = !ff, exact congr_arg bnot halk,
          rw [← amk_eval_eq_alk_succ_eval, bool.bnot_ff, amz_eval_tt_iff_forall_eval_ff] at hamk,
          exact hamk (nth_le_mem_take_of_lt hi (lt_succ_self i)) },
        { use [Pos (g.nth i), mem_cons_of_mem _ (mem_singleton_self _)],
          rw [literal.eval, sinz_amo_tau, aite_neg (disj_right.mp hdis (nth_mem_stock g i)), nth_from_var_eq_nth_of_le],
          { exact halk },
          { simp only [length, succ_add_sub_one], exact le_of_lt_succ hi } } } },
    { unfold si_to_next_si at hc,
      by_cases hi' : i < ls.length,
      { simp [hi'] at hc, subst hc,
        rw eval_tt_iff_exists_literal_eval_tt,
        cases halk : (alk 1).eval τ ((lit₁ :: lit₂ :: ls).take (i + 1)),
        { use [Neg (g.nth i), mem_cons_self _ _],
          rw [literal.eval, sinz_amo_tau, aite_neg (disj_right.mp hdis (nth_mem_stock g i)), nth_from_var_eq_nth_of_le],
          { have hamk : !((alk 1).eval τ ((lit₁ :: lit₂ :: ls).take (i + 1))) = !ff, exact congr_arg bnot halk,
            rw [← amk_eval_eq_alk_succ_eval, bool.bnot_ff] at hamk,
            rw ← amk_eval_eq_alk_succ_eval, exact hamk },
          { simp only [length, succ_add_sub_one], exact le_of_lt_succ hi } },
        { use [Pos (g.nth (i + 1)), mem_cons_of_mem _ (mem_singleton_self _)],
          rw [literal.eval, sinz_amo_tau, aite_neg (disj_right.mp hdis (nth_mem_stock g (i + 1))), nth_from_var_eq_nth_of_le],
          { rw alk.eval_tt_of_sublist_of_eval_tt (take_sublist_of_le (le_succ (i + 1)) _),
            { exact halk },
            { exact _inst_1 } },
          { simp only [length, succ_add_sub_one, add_le_add_iff_right], exact le_of_lt hi' } } },
      { simp [hi'] at hc, contradiction } },
    { unfold si_to_next_xi at hc,
      cases i,
      { simp only [not_lt_zero', if_false, not_mem_nil] at hc, contradiction },
      { simp [-nth_le] at hc, subst hc,
        rw eval_tt_iff_exists_literal_eval_tt,
        cases halk : (alk 1).eval τ ((lit₁ :: lit₂ :: ls).take (i + 1)),
        { use [Neg (g.nth i), mem_cons_self _ _],
          rw [literal.eval, sinz_amo_tau],
          rw [aite_neg (disj_right.mp hdis (nth_mem_stock g i)), nth_from_var_eq_nth_of_le],
          { rw bnot_eq_true_eq_eq_ff, exact halk },
          { simp only [length, succ_add_sub_one], exact le_of_lt_succ (lt_of_succ_lt hi) } },
        { use [((lit₁ :: lit₂ :: ls).nth_le i.succ hi).flip, mem_cons_of_mem _ (mem_singleton_self _)],
          simp [-nth_le, eval_flip],
          rw [sinz_amo_tau, aite_pos_lit (mem_vars_of_mem (nth_le_mem (lit₁ :: lit₂ :: ls) _ hi))],
          have hi' : i.succ < (lit₁ :: lit₂ :: ls).length, exact hi,
          rw amo_eval_tt_iff_distinct_eval_ff_of_eval_tt at heval,
          rcases alo_eval_tt_iff_exists_eval_tt.mp halk with ⟨z, hmem, hevalz⟩,
          have := nth_le_mem_drop_of_ge hi' (le_refl i.succ),
          have := distinct_of_mem_take_of_mem_drop hmem this,
          exact heval this hevalz } } } }
end

theorem sinz_amo_mem_vars {l : list (literal V)} {g : gensym V} :
  ∀ ⦃v⦄, v ∈ (sinz_amo l g).1.vars → v ∈ (clause.vars l) ∨ (v ∈ (g.nfresh (length l - 1)).1) :=
begin
  -- TODO redo proof with si_to_si_mem theorems?
  induction l with lit₁ ls generalizing g,
  { simp [sinz_amo] },
  { cases ls with lit₂ ls,
    { simp [sinz_amo] },
    { intros v hv,
      rw sinz_amo at hv,
      unfold prod.fst at hv,
      simp [-map_with_index_cons] at hv,
      rcases hv with ⟨F, ⟨lit, idx, ⟨hlen, rfl⟩, rfl⟩, hf⟩,
      simp at hf,
      rcases hf with (hf | hf | hf),
      { unfold xi_to_si at hf,
        by_cases hidx : idx = ls.length + 1,
        { simp [hidx] at hf, contradiction },
        { have hlen' := lt_of_le_of_ne (le_of_lt_succ hlen) hidx,
          simp [hlen', flip_var_eq, var] at hf,
          rcases hf with (rfl | rfl),
          { exact or.inl (mem_vars_of_mem (nth_le_mem _ _ _)) },
          { exact or.inr (nth_mem_nfresh_of_lt _ hlen') } } },
      { unfold si_to_next_si at hf,
        by_cases hidx : idx ≥ ls.length,
        { simp [not_lt_of_ge hidx] at hf, contradiction },
        { have hlen' := lt_of_not_ge hidx,
          simp [hlen', var] at hf,
          right, simp only [length, succ_add_sub_one],
          rcases hf with (rfl | rfl),
          { exact nth_mem_nfresh_of_lt _ (lt_succ_of_lt hlen') },
          { exact nth_mem_nfresh_of_lt _ (succ_lt_succ_iff.mpr hlen') } } },
      { unfold si_to_next_xi at hf,
        cases idx,
        { simp at hf, contradiction },
        { simp [flip_var_eq, var] at hf,
          rcases hf with (rfl | rfl),
          { right, simp only [length, succ_add_sub_one],
            exact nth_mem_nfresh_of_lt _ (succ_lt_succ_iff.mp hlen) },
          { exact or.inl (mem_vars_of_mem (mem_cons_of_mem _ (nth_le_mem _ _ _))) } } } } }
end

theorem sinz_amo_is_wb : is_wb (sinz_amo : enc_fn V) :=
begin
  intros l g hdis,
  cases l with lit₁ ls,
  { simp [sinz_amo] },
  cases ls with lit₂ ls,
  { simp [sinz_amo] },
  { split,
    { rw sinz_amo,
      intros v hv,
      simp only [prod.snd] at hv,
      exact (nfresh_stock_subset _ _) hv },
    { intros v hv,
      apply (set.mem_union _ _ _).mpr,
      rcases sinz_amo_mem_vars hv with (hv | hv),
      { exact or.inl hv },
      { exact or.inr ⟨nfresh_mem_stock hv, nth_not_mem_nfresh_stock _ hv⟩ } } }
end

theorem signal_eval_tt_if_xi_eval_tt {i : nat} {hi : i < length l}
  (hi' : i < length l - 1) :
  (sinz_amo l g).1.eval τ = tt → (l.nth_le i hi).eval τ = tt → τ (g.nth i) = tt :=
begin
  cases l with lit₁ ls, { simp only [length, not_lt_zero'] at hi, contradiction },
  cases ls with lit₂ ls, { simp only [length_singleton, not_lt_zero'] at hi', contradiction },
  intros heval hlit,
  rw eval_tt_iff_forall_clause_eval_tt at heval,
  have := heval _ (xi_to_si_mem_sinz_amo g hi' hi),
  simp [eval_tt_iff_exists_literal_eval_tt, eval_flip, literal.eval, hlit] at this,
  exact this
end

theorem signal_eval_tt_of_prev_signal_eval_tt {i : nat} (hi : i < length l - 2) :
  (sinz_amo l g).1.eval τ = tt → 
  τ (g.nth i) = tt → ∀ ⦃j : nat⦄, (j > i ∧ j < length l - 1) → τ (g.nth j) = tt :=
begin
  cases l with lit₁ ls, { simp only [length, not_lt_zero'] at hi, contradiction },
  cases ls with lit₂ ls, { simp only [length_singleton, not_lt_zero'] at hi, contradiction },
  rintros heval hgnth j ⟨hij, hj⟩,
  rw eval_tt_iff_forall_clause_eval_tt at heval,
  induction j with j ih,
  { simp only [gt_iff_lt, not_lt_zero'] at hij, contradiction },
  { rcases (eq_or_lt_of_le (le_of_lt_succ hij)) with (rfl | hij'),
    { have := heval _ (si_to_next_si_mem g hi),
      simp [eval_tt_iff_exists_literal_eval_tt, literal.eval, hgnth] at this,
      exact this },
    { have ihred := ih hij' (lt_of_succ_lt hj),
      have hj' : j < (lit₁ :: lit₂ :: ls).length - 2,
      { simp at hj |-, exact succ_lt_succ_iff.mp hj },
      have := heval _ (si_to_next_si_mem g hj'),
      simp [eval_tt_iff_exists_literal_eval_tt, literal.eval, ihred] at this,
      exact this } }
end

theorem nth_eval_ff_of_signal_eval_tt {i : nat} (hi : i < length l - 1) :
  (sinz_amo l g).1.eval τ = tt → τ (g.nth i) = tt → 
  ∀ {j : nat} (hj : (j > i) ∧ (j < length l)), (l.nth_le j hj.2).eval τ = ff :=
begin
  cases l with lit₁ ls, { simp only [length, not_lt_zero'] at hi, contradiction },
  cases ls with lit₂ ls, { simp only [length_singleton, not_lt_zero'] at hi, contradiction },
  rintros heval hgnth j ⟨hij, hj⟩,
  cases j,
  { simp only [gt_iff_lt, not_lt_zero'] at hij, contradiction },
  { have hc := eval_tt_iff_forall_clause_eval_tt.mp heval _ (si_to_next_xi_mem g hj),
    rcases eq_or_lt_of_le (le_of_lt_succ hij) with (rfl | h),
    { simp [eval_flip, literal.eval, hgnth, -nth_le] at hc,
      exact hc },
    { simp [succ_lt_succ_iff ] at hj,
      have h' : i < (lit₁ :: lit₂ :: ls).length - 2,
      { exact lt_of_lt_of_le h (le_of_lt_succ hj) },
      have := signal_eval_tt_of_prev_signal_eval_tt h' heval hgnth,
      simp at this,
      simp [eval_flip, literal.eval, this h hj, -nth_le] at hc,
      exact hc } }
end

theorem sinz_amo_formula_encodes : is_correct (amk 1) (sinz_amo : enc_fn V) :=
begin
  intros l g hdis τ,
  cases l with lit₁ ls,
  { simp [sinz_amo] },
  { cases ls with lit₂ ls,
    { simp [sinz_amo], use τ },
    { split,
      { intro hamk,
        use [(sinz_amo_tau (lit₁ :: lit₂ :: ls) g τ), sinz_amo_eval_tt_under_sinz_amo_tau hdis τ hamk],
        intros v hv, rw [sinz_amo_tau, aite_pos hv] },
      { rintros ⟨σ, hs, hagree_on⟩,
        rw amo_eval_tt_iff_distinct_eval_ff_of_eval_tt,
        rintros lit₁ lit₂ ⟨i, j, hi, hj, hij, rfl, rfl⟩ hl₁,
        rw nth_eval_eq_of_agree_on hj hagree_on,
        have hi' := lt_of_lt_of_le hij (le_pred_of_lt hj),
        have hl₁' := nth_eval_eq_of_agree_on hi hagree_on,
        rw hl₁ at hl₁',
        have := signal_eval_tt_if_xi_eval_tt hi' hs hl₁'.symm,
        exact nth_eval_ff_of_signal_eval_tt hi' hs this ⟨hij, hj⟩ } } }
end

-- Alernative proof of reverse direction using the amk semantics directly
/-

theorem signal_semantics₁ : (sinz_amo l g).1.eval τ = tt → 
  ∀ ⦃i : nat⦄, i < length l - 1 → τ (g.nth i) = ff → (amk 0).eval τ (l.take (i + 1)) = tt :=
begin
  cases l with lit₁ ls, { simp },
  cases ls with lit₂ ls, { simp },
  intros heval i hi htau,
  rw eval_tt_iff_forall_clause_eval_tt at heval,
  induction i with i ih,
  { have : 0 < (lit₁ :: lit₂ :: ls).length, { simp },
    have := heval _ (xi_to_si_mem_sinz_amo g hi this),
    simp [literal.eval, eval_flip, htau] at this,
    simp [this] },
  { cases htau' : τ (g.nth i),
    { have hi' : i + 1 < (lit₁ :: lit₂ :: ls).length,
      { simp at hi |-, exact lt_of_succ_lt hi },
      cases hlit : ((lit₁ :: lit₂ :: ls).nth_le _ hi').eval τ,
      { rw [amk.eval_take_tail_neg hlit, take],
        simp at ih hi,
        exact ih (lt_of_succ_lt hi) htau' },
      { have := heval _ (xi_to_si_mem_sinz_amo g hi hi'),
        rw nth_le at hlit,
        simp [literal.eval, eval_flip, htau, hlit] at this,
        contradiction } },
    { have : i < (lit₁ :: lit₂ :: ls).length - 2,
      { simp at hi |-, exact succ_lt_succ_iff.mp hi },
      have := heval _ (si_to_next_si_mem g this),
      simp [literal.eval, htau, htau'] at this,
      contradiction } }
end

theorem signal_semantics₂ : (sinz_amo l g).1.eval τ = tt →
  ∀ ⦃i : nat⦄, i < length l - 1 → τ (g.nth i) = tt → (amk 1).eval τ (l.take (i + 1)) = tt :=
begin
  cases l with lit₁ ls, { simp },
  cases ls with lit₂ ls, { simp },
  intros heval i hi htau,
  have heval_copy := heval,
  rw eval_tt_iff_forall_clause_eval_tt at heval,
  induction i with i ih,
  { simp },
  { have hi' : i < (lit₁ :: lit₂ :: ls).length - 1,
    { simp at hi |-, exact lt_of_succ_lt hi },
    have hi'' : (i + 1) < (lit₁ :: lit₂ :: ls).length, 
    { simp at hi |-, exact lt_of_succ_lt hi },
    cases htau' : τ (g.nth i),
    { have := signal_semantics₁ heval_copy hi' htau',
      cases hlit : ((lit₁ :: lit₂ :: ls).nth_le _ hi'').eval τ,
      { rw amk.eval_take_tail_neg hlit,
        exact amk.eval_tt_of_le_of_eval_tt (zero_le 1) this },
      { rw amk.eval_take_tail_pos hlit,
        exact this } },
    { have := heval _ (si_to_next_xi_mem g hi''),
      simp [literal.eval, eval_flip, htau', -nth_le] at this,
      rw amk.eval_take_tail_neg this,
      exact ih hi' htau' } }
end

...
{ rintro ⟨σ, hs, hagree_on⟩,
  rw amk.eval_eq_of_agree_on 1 hagree_on,
  have hlen : length (lit₁ :: lit₂ :: ls) - 2 < length (lit₁ :: lit₂ :: ls) - 1, { simp },
  have hlen' : length (lit₁ :: lit₂ :: ls) - 1 < length (lit₁ :: lit₂ :: ls), { simp },
  have htake : (lit₁ :: lit₂ :: ls).take (length (lit₁ :: lit₂ :: ls)) = (lit₁ :: lit₂ :: ls),
  { simp only [take, take_length, eq_self_iff_true, and_self] },
  have hadd_sub : (lit₁ :: lit₂ :: ls).length = (lit₁ :: lit₂ :: ls).length - 1 + 1, { simp },
  cases hsig : σ (g.nth (length (lit₁ :: lit₂ :: ls) - 2)),
  { rw [← htake, hadd_sub],
    have hsigsem := signal_semantics₁ hs hlen hsig,
    cases hlit : ((lit₁ :: lit₂ :: ls).nth_le _ hlen').eval σ,
    { rw amk.eval_take_tail_neg hlit,
      exact amk.eval_tt_of_le_of_eval_tt (zero_le 1) hsigsem },
    { rw amk.eval_take_tail_pos hlit,
      exact hsigsem } },
  { rw [← htake, hadd_sub],
    have hsigsem := signal_semantics₂ hs hlen hsig,
    cases hlit : ((lit₁ :: lit₂ :: ls).nth_le _ hlen').eval σ,
    { rw amk.eval_take_tail_neg hlit,
      exact hsigsem },
    { have := eval_tt_iff_forall_clause_eval_tt.mp hs _ (si_to_next_xi_mem g hlen'),
      simp at hsig hlit,
      simp [literal.eval, eval_flip, hsig, hlit] at this,
      contradiction } }
-/

theorem sinz_amo_encodes_amo : encodes (amk 1) (sinz_amo : enc_fn V) :=
⟨sinz_amo_formula_encodes, sinz_amo_is_wb⟩ 

-- The version easier for theorem proving
def sinz_amo_rec : enc_fn V
| []                   g := ⟨[], g⟩
| [lit₁]               g := ⟨[], g⟩
| [lit₁, lit₂]         g := ⟨[[lit₁.flip, Pos g.fresh.1], [Neg g.fresh.1, lit₂.flip]], g.fresh.2⟩
| (lit₁ :: lit₂ :: ls) g :=
  ⟨[[lit₁.flip, Pos g.fresh.1], [Neg g.fresh.1, Pos g.fresh.2.fresh.1], [Neg g.fresh.1, lit₂.flip]] ++ 
   (sinz_amo_rec (lit₂ :: ls) g.fresh.2).1,
   (sinz_amo_rec (lit₂ :: ls) g.fresh.2).2⟩

-- A nicer looking and more efficient presentation of the Sinz encoding
def sinz_amo_rec' : enc_fn V
| []                   g := ⟨[], g⟩
| [lit₁]               g := ⟨[], g⟩
| [lit₁, lit₂]         g := 
    let ⟨y, g₁⟩ := g.fresh in
    ⟨[[lit₁.flip, Pos y], [Neg y, lit₂.flip]], g₁⟩
| (lit₁ :: lit₂ :: ls) g :=
    let ⟨y, g₁⟩ := g.fresh in
    let ⟨z, _⟩ := g₁.fresh in
    let ⟨F_rec, g₂⟩ := sinz_amo_rec' (lit₂ :: ls) g₁ in
    ⟨[[lit₁.flip, Pos y], [Neg y, Pos z], [Neg y, lit₂.flip]] ++ F_rec, g₂⟩

-- The two definitions of the Sinz encoding are equivalent on all inputs
theorem sinz_amo_rec_eq_sinz_amo_rec' : ∀ (l : list (literal V)) (g : gensym V),
  sinz_amo_rec l g = sinz_amo_rec' l g :=
begin
  intros l g,
  induction l with lit₁ ls ih generalizing g,
  { refl },
  { cases ls with lit₂ ls,
    { refl },
    { cases ls with lit₃ ls,
      { simp [sinz_amo_rec, sinz_amo_rec'], unfold fresh, refl },
      { rw [sinz_amo_rec, sinz_amo_rec'],
        rw [prod.ext_self g.fresh, sinz_amo_rec'._match_4,
            prod.ext_self g.fresh.2.fresh, sinz_amo_rec'._match_3,
            ← ih, prod.ext_self (sinz_amo_rec _ _)],
        rw sinz_amo_rec'._match_2 } } }
end

theorem sinz_amo_rec_is_wb : is_wb (sinz_amo_rec : enc_fn V) :=
begin
  intros l g hdis,
  induction l with lit₁ ls ih generalizing g,
  { simp [sinz_amo_rec] },
  { cases ls with lit₂ ls,
    { simp [sinz_amo_rec] },
    { cases ls with lit₃ ls,
      { simp [sinz_amo_rec, cnf.vars, var, flip_var_eq],
        split,
        { exact fresh_stock_subset g },
        { intros v hv,
          simp only [set.mem_insert_iff, set.mem_singleton_iff] at hv,
          rcases hv with (rfl | rfl | rfl),
          { apply set.mem_union_left, simp only [set.mem_insert_iff, set.mem_singleton, or_true] },
          { apply set.mem_union_left, simp only [set.mem_insert_iff, eq_self_iff_true, true_or] },
          { apply set.mem_union_right,
            exact ⟨fresh_mem_stock g, fresh_not_mem_fresh_stock g⟩ } } },
      { rw sinz_amo_rec,
        simp [cnf.vars, var, flip_var_eq],
        have ihred := ih (disj_fresh_cons hdis),
        split,
        { exact subset_trans ihred.1 (fresh_stock_subset g) },
        { intros v hv,
          simp only [set.mem_insert_iff, finset.mem_coe] at hv,
          rcases hv with (rfl | rfl | rfl | rfl | hv),
          { apply set.mem_union_left, simp only [set.mem_insert_iff, eq_self_iff_true, true_or] },
          { apply set.mem_union_right, split,
            { exact fresh_fresh_mem_stock g },
            { intro hcon,
              have : g.fresh.2.fresh.1 ∈ (sinz_amo_rec (lit₂ :: lit₃ :: ls) g.fresh.2).1.vars,
              { cases ls with lit₄ ls; { rw sinz_amo_rec, simp [cnf.vars, var] } },
              rcases (set.mem_union _ _ _).mp (ihred.2 this) with (hv | hv),
              { exact (disj_left.mp (disj_of_disj_cons hdis) hv) (fresh_fresh_mem_stock g) },
              { exact hv.2 hcon } } },
          { apply set.mem_union_right,
            exact ⟨fresh_mem_stock g, not_mem_subset (fresh_not_mem_fresh_stock g) ihred.1⟩ },
          { apply set.mem_union_left,
            simp only [set.mem_insert_iff, eq_self_iff_true, true_or, or_true] },
          { rcases (set.mem_union _ _ _).mp (ihred.2 hv) with (hv | hv),
            { apply set.mem_union_left,
              simp at hv,
              rcases hv with (rfl | rfl | hv),
              { simp only [set.mem_insert_iff, eq_self_iff_true, true_or, or_true] },
              { simp only [set.mem_insert_iff, eq_self_iff_true, true_or, or_true] },
              { simp only [hv, set.mem_insert_iff, finset.mem_coe, or_true] } },
            { apply set.mem_union_right,
              exact ⟨(fresh_stock_subset g) hv.1, hv.2⟩ } } } } } }
end

theorem sinz_amo_rec_amz {l} {g} (hdis : disj l g) : (amk 0).eval τ l = tt → 
  (sinz_amo_rec l g).1.eval (aite (clause.vars l) τ all_tt) = tt :=
begin
  induction l with lit₁ ls ih generalizing g,
  { simp [sinz_amo_rec] },
  { cases ls with lit₂ ls,
    { simp [sinz_amo_rec] },
    { intro hamk,
      have h₁ : lit₁ ∈ lit₁ :: lit₂ :: ls, { exact mem_cons_self _ _ },
      have h₂ : lit₂ ∈ lit₁ :: lit₂ :: ls, { exact mem_cons_of_mem _ (mem_cons_self _ _) },
      cases ls with lit₃ ls,
      { simp [sinz_amo_rec, eval_flip, literal.eval, -clause.vars_cons,
          aite_pos_lit (mem_vars_of_mem h₁),
          aite_pos_lit (mem_vars_of_mem h₂),
          (amz_eval_tt_iff_forall_eval_ff.mp hamk) h₁,
          (amz_eval_tt_iff_forall_eval_ff.mp hamk) h₂] },
      { rw sinz_amo_rec,
        simp [eval_flip, literal.eval, -clause.vars_cons,
          aite_pos_lit (mem_vars_of_mem h₁),
          aite_pos_lit (mem_vars_of_mem h₂),
          aite_neg (disj_right.mp hdis (fresh_mem_stock g)), 
          aite_neg (disj_right.mp hdis (fresh_fresh_mem_stock g)),
          (amz_eval_tt_iff_forall_eval_ff.mp hamk) h₁,
          (amz_eval_tt_iff_forall_eval_ff.mp hamk) h₂,
          all_tt_eval_tt],
        have ihred := ih (disj_fresh_cons hdis) (amz_of_amz_cons hamk),
        by_cases hlit₁ : lit₁.var ∈ clause.vars (lit₂ :: lit₃ :: ls),
        { rw vars_cons_of_mem hlit₁, exact ihred },
        { rw ← ihred,
          apply cnf.eval_eq_of_agree_on,
          intros v hv,
          rcases (set.mem_union _ _ _).mp 
            ((sinz_amo_rec_is_wb (disj_fresh_cons hdis)).2 hv) with (hv | hv),
          { rw [aite_pos hv, aite_pos (clause.mem_vars_cons_of_mem_vars _ hv)] },
          { rw [aite_neg (disj_right.mp (disj_fresh_cons hdis) hv.1),
                aite_neg (disj_right.mp (disj_fresh_of_disj hdis) hv.1)] } } } } }
end

theorem sinz_amo_rec_amo {l} {g} (hdis : disj l g) : 
  (sinz_amo_rec l g).1.eval τ = tt ∧ τ g.fresh.1 = tt → (amk 0).eval τ l.tail = tt :=
begin
  induction l with lit₁ ls ih generalizing g,
  { simp [sinz_amo_rec], },
  { cases ls with lit₂ ls,
    { simp [sinz_amo_rec] },
    { rintro ⟨heval, hfresh⟩,
      cases ls with lit₃ ls,
      { simp [sinz_amo_rec, hfresh, eval_flip, literal.eval] at heval,
        rw [tail, amk.eval_cons_neg heval, amk.eval_nil] },
      { rw sinz_amo_rec at heval,
        simp [hfresh, eval_flip, literal.eval] at heval,
        rcases heval with ⟨h₁, h₂, h₃⟩,
        rw [tail, amk.eval_cons_neg h₂],
        exact ih (disj_fresh_of_disj (disj_of_disj_cons hdis)) ⟨h₃, h₁⟩ } } }
end

theorem sinz_amo_rec_encodes : encodes (amk 1) (sinz_amo_rec : enc_fn V) :=
begin
  split,
  { intros l g hdis τ,
    induction l with lit₁ ls ih generalizing g,
    { simp [sinz_amo_rec] },
    { cases ls with lit₂ ls,
      { simp [sinz_amo_rec], use τ },
      { split,
        { intro hamk,
          have h₁ : lit₁ ∈ lit₁ :: lit₂ :: ls, { exact mem_cons_self _ _ },
          have h₂ : lit₂ ∈ lit₁ :: lit₂ :: ls, { exact mem_cons_of_mem _ (mem_cons_self _ _) },
          cases hlit₁ : lit₁.eval τ,
          { rw amk.eval_cons_neg hlit₁ at hamk,
            rcases (ih (disj_fresh_cons hdis)).mp hamk with ⟨σ, heval, hs⟩,
            have hnmem : g.fresh.1 ∉ (sinz_amo_rec (lit₂ :: ls) g.fresh.2).1.vars,
            { apply not_mem_form_of_is_wb sinz_amo_rec_is_wb (disj_fresh_cons hdis),
              intro hcon, rcases (set.mem_union _ _ _).mp hcon with (hv | hv),
              { exact (disj_right.mp (disj_of_disj_cons hdis) (fresh_mem_stock g)) hv },
              { exact (fresh_not_mem_fresh_stock g) hv } },
            rcases exists_agree_on_and_eq_of_not_mem σ ff hnmem with ⟨σ₂, hs₂, hfresh⟩,
            use aite (clause.vars (lit₁ :: lit₂ :: ls)) τ σ₂,
            split,
            { cases ls with lit₃ ls;
              simp [sinz_amo_rec, eval_flip, literal.eval, -clause.vars_cons,
                aite_pos_lit (mem_vars_of_mem h₁), hlit₁,
                aite_neg (disj_right.mp hdis (fresh_mem_stock g)), hfresh],
              have : agree_on (aite (clause.vars (lit₁ :: lit₂ :: lit₃ :: ls)) τ σ₂) σ₂ (sinz_amo_rec (lit₂ :: lit₃ :: ls) g.fresh.2).1.vars,
              { intros v hv,
                rcases mem_vars_or_stock_of_is_wb_of_mem sinz_amo_rec_is_wb (disj_fresh_cons hdis) hv with (h | h),
                { rw aite_pos (clause.mem_vars_cons_of_mem_vars _ h),
                  exact (hs _ h).symm ▸ (hs₂ _ hv) },
                { rw aite_neg (disj_right.mp (disj_fresh_of_disj hdis) h) } },
              rw [eval_eq_of_agree_on this, ← eval_eq_of_agree_on hs₂], exact heval },
            { intros v hv, rw aite_pos hv } },
          { rw amk.eval_cons_pos hlit₁ at hamk,
            use [aite (clause.vars (lit₁ :: lit₂ :: ls)) τ all_tt],
            split,
            { cases ls with lit₃ ls;
              simp [sinz_amo_rec, eval_flip, literal.eval, -clause.vars_cons,
                aite_pos_lit (mem_vars_of_mem h₁), hlit₁,
                aite_pos_lit (mem_vars_of_mem h₂),
                aite_neg (disj_right.mp hdis (fresh_mem_stock g)),
                aite_neg (disj_right.mp hdis (fresh_fresh_mem_stock g)), all_tt_eval_tt],
              { exact (amz_eval_tt_iff_forall_eval_ff.mp hamk) (mem_cons_self _ _) },
              { split,
                { exact (amz_eval_tt_iff_forall_eval_ff.mp hamk) (mem_cons_self _ _) },
                { rw [← sinz_amo_rec_amz (disj_fresh_of_disj (disj_of_disj_cons hdis)) hamk, cnf.eval_eq_of_agree_on],
                  intros v hv,
                  rcases mem_vars_or_stock_of_is_wb_of_mem sinz_amo_rec_is_wb (disj_fresh_cons hdis) hv with (h | h),
                  { rw [aite_pos h, aite_pos (clause.mem_vars_cons_of_mem_vars _ h)] },
                  { rw [aite_neg (disj_right.mp (disj_fresh_of_disj hdis) h),
                        aite_neg (disj_right.mp (disj_fresh_cons hdis) h)] } } } },
            { intros v hv, rw aite_pos hv } } },
        { rintros ⟨σ, heval, hs⟩,
          have hlit₁' := eval_eq_of_agree_on_of_var_mem hs (mem_vars_of_mem (mem_cons_self _ _)),
          cases hlit₁ : lit₁.eval σ,
          { rw hlit₁ at hlit₁',
            rw amk.eval_cons_neg hlit₁',
            cases ls with lit₃ ls,
            { simp [sinz_amo_rec, literal.eval, eval_flip, hlit₁] at heval,
              exact eval_singleton_pos 0 τ lit₂ },
            { rw sinz_amo_rec at heval,
              simp [literal.eval, eval_flip, hlit₁] at heval,
              exact (ih (disj_fresh_cons hdis)).mpr ⟨σ, heval.2.2, (agree_on_of_agree_on_vars_cons hs)⟩ } },
          { rw hlit₁ at hlit₁',
            rw amk.eval_cons_pos hlit₁',
            cases ls with lit₃ ls,
            { simp [sinz_amo_rec, literal.eval, eval_flip, hlit₁] at heval,
              rcases heval with ⟨he₁, (he₂ | he₂)⟩,
              { rw he₁ at he₂, contradiction },
              { rw ← (eval_eq_of_agree_on_of_var_mem hs 
                  (mem_vars_cons_of_mem_vars _ (mem_vars_of_mem (mem_cons_self _ _)))) at he₂,
                rw [amk.eval_cons_neg he₂ 0 [], amk.eval_nil 0 τ] } },
            { have heval_copy := heval,
              rw sinz_amo_rec at heval,
              simp [literal.eval, eval_flip, hlit₁] at heval,
              rw amk.eval_eq_of_agree_on 0 (agree_on_of_agree_on_vars_cons hs),
              exact sinz_amo_rec_amo hdis ⟨heval_copy, heval.1⟩ } } } } } },
  { exact sinz_amo_rec_is_wb }
end

end sinz_amo