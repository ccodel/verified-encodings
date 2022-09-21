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

-- A possible recursive definition. Proof was too challenging. Try again later?
/-
def sinz : Π (l : list (literal V)), Π (g : gensym V),
  (disjoint g.stock (clause.vars l)) → cnf V
| []               _ _            := []
| [l₁]             g hdis         := [] --[[l₁.flip, Pos (g.fresh.1)]] -- may be unneeded
| (l₁ :: l₂ :: ls) g hdis         := 
    [l₁.flip, Pos (g.fresh.1)] :: 
    [Neg g.fresh.1, Pos g.fresh.2.fresh.1] ::
    [Neg g.fresh.1, l₂.flip] ::
    (sinz (l₂ :: ls) g.fresh.2 (disjoint_fresh_of_disjoint hdis))
-/

def xi_to_si (g : gensym V) (n i : nat) (lit : literal V) : cnf V :=
  if (i < n - 1) then [[lit.flip, Pos (g.nth i)]] else []

def si_to_next_si (g : gensym V) (n i : nat) : cnf V :=
  if (i < n - 2) then [[Neg (g.nth i), Pos (g.nth (i + 1))]] else []

def si_to_next_xi (g : gensym V) (i : nat) (lit : literal V) : cnf V :=
  if (0 < i) then [[Neg (g.nth (i - 1)), lit.flip]] else []

def sinz_amo (l : list (literal V)) (g : gensym V) : cnf V :=
if hl : length l < 2 then [] else
  join (map_with_index (λ (idx : nat) (lit : literal V),
    xi_to_si g (length l) idx lit ++
    si_to_next_si g (length l) idx ++
    si_to_next_xi g idx lit) l)

theorem xi_to_si_mem {l : list (literal V)} (hl : length l ≥ 2) (g : gensym V) 
  {i : nat} (Hi' : i < length l - 1) (Hi : i < length l) :
  [(l.nth_le i Hi).flip, Pos (g.nth i)] ∈ sinz_amo l g :=
begin
  rw sinz_amo,
  simp [not_lt.mpr hl],
  use (xi_to_si g l.length i (l.nth_le i Hi) ++ si_to_next_si g l.length i ++ si_to_next_xi g i (l.nth_le i Hi)),
  split,
  { use [l.nth_le i Hi, i, Hi],
    simp only [eq_self_iff_true, append_assoc, and_self] },
  { simp [xi_to_si, Hi'] }
end

theorem si_to_next_si_mem {l : list (literal V)} (hl : length l ≥ 2) (g : gensym V)
  {i : nat} (Hi' : i < length l - 2) (Hi : i < length l) :
  [Neg (g.nth i), Pos (g.nth (i + 1))] ∈ sinz_amo l g :=
begin
  rw sinz_amo,
  simp [not_lt.mpr hl],
  use (xi_to_si g l.length i (l.nth_le i Hi) ++ si_to_next_si g l.length i ++ si_to_next_xi g i (l.nth_le i Hi)),
  split,
  { use [l.nth_le i Hi, i, Hi],
    simp only [eq_self_iff_true, append_assoc, and_self] },
  { simp [si_to_next_si, Hi'] }
end

theorem si_to_next_xi_mem {l : list (literal V)} (hl : length l ≥ 2) (g : gensym V)
  {i : nat} (Hi : 0 < i ∧ i < length l) :
  [Neg (g.nth (i - 1)), (l.nth_le i Hi.2).flip] ∈ sinz_amo l g :=
begin
  rw sinz_amo,
  simp [not_lt.mpr hl],
  use (xi_to_si g l.length i (l.nth_le i Hi.2) ++ si_to_next_si g l.length i ++ si_to_next_xi g i (l.nth_le i Hi.2)),
  split,
  { use [l.nth_le i Hi.2, i, Hi.2],
    simp only [eq_self_iff_true, append_assoc, and_self] },
  { simp [si_to_next_xi, Hi.1] }
end

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

def signal_truth (l : list (literal V)) (τ : assignment V) : nat → bool
| 0       := l.head.eval τ
| (i + 1) := if h : (i + 1) < length l then (l.nth_le (i + 1) h).eval τ || signal_truth i
             else ff 

def sinz_tau (l : list (literal V)) (g : gensym V) (τ : assignment V) : assignment V :=
  λ v, if v ∈ clause.vars l then τ v else
    signal_truth l τ (nth_from_var g v (length l))

theorem signal_semantics {g : gensym V} {l : list (literal V)} 
  (hdis : disjoint g.stock (clause.vars l)) {i : nat} :
  i < length l → ∀ {τ : assignment V},
  (signal_truth l τ i = tt ↔ alk.eval 1 τ (l.take (i + 1)) = tt) :=
begin
  intros hi τ,
  induction i with i ih,
  { simp [signal_truth, take_one_of_ne_nil (ne_nil_of_length_pos hi), 
    alk.eval, alk, bool_symm] },
  { simp [signal_truth, hi],
    split,
    { rintros (hs | hs),
      { rw eval_take_tail_pos hi hs,
        exact eval_zero _ _ },
      { have ihred := (ih (lt_of_succ_lt hi)).mp hs,
        have := take_sublist_of_le (le_succ (i + 1)) l,
        exact eval_tt_of_sublist_of_eval_tt this ihred } },
    { intro hl,
      cases h : (l.nth_le (i + 1) _).eval τ,
      { rw eval_take_tail_neg hi h at hl,
        exact or.inr ((ih (lt_of_succ_lt hi)).mpr hl) },
      { simp only [eq_self_iff_true, true_or] } } }
end

lemma minus_two {n m : nat} : n < m - 2 → n + 1 < m :=
begin
  intro h, cases m,
  { linarith },
  { cases m,
    { linarith },
    { simp only [succ_sub_succ_eq_sub, tsub_zero] at h,
      exact lt_succ_of_lt (succ_lt_succ_iff.mpr h) } }
end

theorem xts_eval_tt {g : gensym V} {l : list (literal V)}
  (hdis : disjoint g.stock (clause.vars l)) {i : nat} (Hi : i < length l) :
  ∀ (τ : assignment V),
  (xi_to_si g (length l) i (l.nth_le i Hi)).eval (sinz_tau l g τ) = tt :=
begin
  intro τ,
  rw eval_tt_iff_forall_clause_eval_tt,
  intros c hc,
  rw [xi_to_si] at hc,
  by_cases Hi₂ : (i = l.length - 1),
  { simp [Hi₂] at hc, contradiction },
  { simp [lt_of_le_of_ne (le_pred_of_lt Hi) Hi₂] at hc,
    subst hc,
    rw eval_tt_iff_exists_literal_eval_tt,
    cases hl : (l.nth_le i Hi).eval τ,
    { use (l.nth_le i Hi).flip,
      have hmem := mem_vars_of_mem (nth_le_mem l i Hi),
      cases l.nth_le i Hi;
      { rw var at hmem,
        rw literal.eval at hl,
        simp [eval_flip, literal.eval, hl, sinz_tau, hmem] } },
    { use Pos (g.nth i),
      simp [literal.eval, sinz_tau, forall_nth_not_mem_of_disjoint' hdis i,
        nth_from_var_eq_nth_of_le g (le_of_lt Hi)],
      cases i,
      { rw signal_truth, rw nth_le_zero at hl, exact hl },
      { simp [signal_truth, Hi], exact or.inl hl } } }
end

theorem stns_eval_tt {g : gensym V} {l : list (literal V)}
  (hdis : disjoint g.stock (clause.vars l)) :
  ∀ (i : nat) (τ : assignment V),
  (si_to_next_si g (length l) i).eval (sinz_tau l g τ) = tt :=
begin
  intros i τ,
  rw eval_tt_iff_forall_clause_eval_tt,
  intros c hc,
  rw si_to_next_si at hc,
  by_cases hi : (i < l.length - 2),
  { simp [hi] at hc,
    subst hc,
    rw eval_tt_iff_exists_literal_eval_tt,
    cases hs : (sinz_tau l g τ) (g.nth i),
    { use Neg (g.nth i),
      simp [literal.eval, hs] },
    { use Pos (g.nth (i + 1)),
      simp [literal.eval, sinz_tau, forall_nth_not_mem_of_disjoint' hdis (i + 1)],
      have : i + 1 < l.length, from minus_two hi,
      rw nth_from_var_eq_nth_of_le g (le_of_lt this),
      simp [signal_truth, this],
      simp [sinz_tau, forall_nth_not_mem_of_disjoint' hdis i,
        nth_from_var_eq_nth_of_le g (le_of_lt (lt_of_succ_lt this))] at hs,
      exact or.inr hs } },
  { simp [hi] at hc, contradiction }
end

theorem stnx_eval_tt {g : gensym V} {l : list (literal V)}
  (hdis : disjoint g.stock (clause.vars l)) {i : nat} (Hi : i < length l) :
  ∀ (τ : assignment V), amk.eval 1 τ (l.take (i + 1)) = tt →
  (si_to_next_xi g i (l.nth_le i Hi)).eval (sinz_tau l g τ) = tt :=
begin
  intros τ hamo,
  rw eval_tt_iff_forall_clause_eval_tt,
  intros c hc,
  rw si_to_next_xi at hc,
  cases i; simp at hc,
  { contradiction },
  { subst hc,
    rw eval_tt_iff_exists_literal_eval_tt,
    cases hs : (sinz_tau l g τ) (g.nth i),
    { use Neg (g.nth i),
      simp [hs, literal.eval] },
    { simp [sinz_tau, forall_nth_not_mem_of_disjoint' hdis i] at hs,
      rw nth_from_var_eq_nth_of_le g (le_of_lt (lt_of_succ_lt Hi)) at hs,
      cases ht : (l.nth_le _ Hi).eval (sinz_tau l g τ),
      { use (l.nth_le _ Hi).flip,
        simp [eval_flip, literal.eval, ht] },
      { have heqod : eqod (sinz_tau l g τ) τ (clause.vars l),
        { rw sinz_tau,
          intros v hv,
          simp [hv] },
        have := (signal_semantics hdis (lt_of_succ_lt Hi)).mp hs,
        have hmem := mem_vars_of_mem (nth_le_mem l _ Hi),
        rw eval_eq_of_eqod_of_var_mem heqod hmem at ht,
        rw eval_tail_pos ht at hamo,
        rw alk_of_amk_of_gt hamo nat.one_pos at this,
        contradiction } } }
end

-- Forward direction
theorem sinz_forward {τ : assignment V} {l : list (literal V)} {g : gensym V} 
  (hdis : disjoint g.stock (clause.vars l)) :
  amk.eval 1 τ l = tt → (sinz_amo l g).eval (sinz_tau l g τ) = tt :=
begin
  intro hamo,
  rw eval_tt_iff_forall_clause_eval_tt,
  intros c hc,
  by_cases hl : length l < 2,
  { simp [sinz_amo, hl] at hc, exfalso, exact hc },
  { simp [sinz_amo, hl] at hc,
    rcases hc with ⟨f, ⟨lit, i, ⟨Hi, rfl⟩, rfl⟩, hc⟩,
    simp at hc,
    rcases hc with (hc | hc | hc),
    { have := xts_eval_tt hdis Hi τ,
      exact eval_tt_iff_forall_clause_eval_tt.mp this _ hc },
    { have := stns_eval_tt hdis i τ,
      exact eval_tt_iff_forall_clause_eval_tt.mp this _ hc },
    { have := amk.eval_take hamo (i + 1),
      have := stnx_eval_tt hdis Hi τ this,
      rw si_to_next_xi at hc,
      by_cases hiz : (0 < i),
      { simp [hiz] at hc, subst hc,
        simp [si_to_next_xi, eval_tt_iff_forall_clause_eval_tt, hiz] at this,
        exact this },
      { simp [hiz] at hc, exfalso, exact hc } } } 
end

-- Reverse direction --

-- Proofs for necessary conditions for setting signal variables to true
theorem signal_nec2 {τ} {l : list (literal V)} (hl : length l ≥ 2) {g : gensym V} 
  {i : nat} (hi : i < length l - 2) :
  (sinz_amo l g).eval τ = tt →
  τ (g.nth i) = tt → ∀ {j : nat}, (j > i ∧ j < length l - 1) → τ (g.nth j) = tt :=
begin
  rintros hs hg j ⟨hij, hj⟩,
  induction j with j ih,
  { linarith },
  { by_cases hij' : i = j,
    { subst hij',
      have := si_to_next_si_mem hl g hi (lt_of_succ_lt (minus_two hi)),
      have := eval_tt_iff_forall_clause_eval_tt.mp hs _ this,
      simp [eval_tt_iff_exists_literal_eval_tt] at this,
      rcases this with ⟨lit, (rfl | rfl), hlit⟩,
      { simp [literal.eval, hg] at hlit, contradiction },
      { rw literal.eval at hlit, exact hlit } },
    { have := lt_of_le_of_ne (le_of_lt_succ hij) hij',
      have ihred := ih this (lt_of_succ_lt hj),
      have hjl : j < length l,
      { rcases exists_eq_add_of_le hl with ⟨k, hk⟩,
        rw add_comm at hk,
        simp [hk] at hj |-,
        exact lt_of_succ_lt (lt_succ_of_lt hj) },
      have : j < length l - 2,
      { rcases exists_eq_add_of_le hl with ⟨k, hk⟩,
        rw add_comm at hk,
        simp [hk] at hj |-,
        exact succ_lt_succ_iff.mp hj },
      have := si_to_next_si_mem hl g this hjl,
      have := eval_tt_iff_forall_clause_eval_tt.mp hs _ this,
      simp [eval_tt_iff_exists_literal_eval_tt] at this,
      rcases this with ⟨list, (rfl | rfl), hlit⟩,
      { simp [literal.eval, ihred] at hlit, contradiction },
      { rw literal.eval at hlit, exact hlit } } }
end

theorem signal_nec {τ} {l : list (literal V)} (hl : length l ≥ 2) {g : gensym V}
  {i : nat} (hi : i < length l - 1) :
  (sinz_amo l g).eval τ = tt → 
  alk.eval 1 τ (l.take (i + 1)) = tt → τ (g.nth i) = tt :=
begin
  intros hs hlk,
  induction i with i ih,
  { cases l with l ls,
    { rw length at hi, linarith },
    { rw length at hl,
      have : ls.length > 0, linarith,
      have : [l.flip, Pos (g.nth 0)] ∈ ite (0 < ls.length) [[l.flip, Pos (g.nth 0)]] [],
      { have : 0 < ls.length, exact this,
        simp [this] },
      simp [alk.eval, alk] at hlk,
      simp [sinz_amo, not_lt.mpr hl, eval_tt_iff_forall_clause_eval_tt, xi_to_si] at hs,
      have := hs _ (or.inl this),
      simp [eval_tt_iff_exists_literal_eval_tt] at this,
      rcases this with ⟨lit, (rfl | rfl), hlit⟩,
      { rw [eval_flip, ← hlk] at hlit, contradiction },
      { rw literal.eval at hlit, exact hlit } } },
  { have : i + 1 < length l, from lt_of_lt_pred hi,
    cases hx : literal.eval τ (l.nth_le _ this),
    { rw eval_take_tail_neg this hx at hlk,
      have ihred := ih (lt_of_succ_lt hi) hlk,
      have : i < l.length - 2,
      { rcases exists_eq_add_of_le hl with ⟨k, hk⟩,
        rw add_comm at hk,
        simp [hk] at hi |-,
        exact succ_lt_succ_iff.mp hi },
      apply signal_nec2 hl this hs ihred,
      split,
      { exact lt_succ_self i },
      { rcases exists_eq_add_of_le hl with ⟨k, hk⟩,
        rw add_comm at hk,
        simp [hk] at this |-,
        exact succ_lt_succ_iff.mpr this } },
    { have hmem := xi_to_si_mem hl g hi this,
      have := eval_tt_iff_forall_clause_eval_tt.mp hs _ hmem,
      simp [eval_tt_iff_exists_literal_eval_tt] at this,
      rcases this with ⟨list, (rfl | rfl), hlit⟩,
      { rw [eval_flip, hx] at hlit, contradiction },
      { rw literal.eval at hlit, exact hlit } } }
end

theorem signal_nec3 {τ} {l : list (literal V)} (hl : length l ≥ 2) {g : gensym V}
  {i : nat} (hi : i < length l) :
  (sinz_amo l g).eval τ = tt → τ (g.nth i) = tt → 
  ∀ {j : nat} (hj : (j > i ∧ j < length l)), (l.nth_le j hj.2).eval τ = ff :=
begin
  rintros hs hg j ⟨hij, hj⟩,
  have hs' := hs,
  rw eval_tt_iff_forall_clause_eval_tt at hs,
  have hc := hs _ (si_to_next_xi_mem hl g ⟨pos_of_gt hij, hj⟩),
  by_cases hj' : (j - 1) = i,
  { rw [hj', eval_tt_iff_exists_literal_eval_tt] at hc,
    simp at hc,
    rcases hc with ⟨lit, (rfl | rfl), he⟩,
    { simp [literal.eval, hg] at he, contradiction },
    { simp [eval_flip] at he, exact he } },
  { have hsub : j - 1 > i,
    { have := pos_of_gt hij,
      cases j,
      { linarith },
      { have : i ≤ j, exact lt_succ_iff.mp hij,
        simp at hj' |-,
        exact lt_of_le_of_ne this (ne.symm hj') } },
    have : j - 1 < length l - 1,
    { rcases exists_eq_add_of_le hl with ⟨k, hk⟩,
      rw add_comm at hk,
      simp [hk] at hj |-,
      cases j,
      { simp },
      { simp, exact succ_lt_succ_iff.mp hj } },
    have hi₂ : i < l.length - 2,
    { rcases exists_eq_add_of_le hl with ⟨k, hk⟩,
      rw add_comm at hk,
      simp [hk] at this |-,
      exact lt_of_lt_of_le hsub (le_of_lt_succ this) },
    have := signal_nec2 hl hi₂ hs' hg ⟨hsub, this⟩,
    simp [eval_tt_iff_exists_literal_eval_tt] at hc,
    rcases hc with ⟨lit, (rfl | rfl), he⟩,
    { simp [literal.eval, this] at he, contradiction },
    { simp [eval_flip] at he, exact he } }
end

theorem sinz_reverse {τ} {l : list (literal V)} {g : gensym V}
  (hdis : disjoint g.stock (clause.vars l)) :
  (sinz_amo l g).eval τ = tt → amk.eval 1 τ l = tt :=
begin
  intro hs,
  by_cases hl : length l ≥ 2,
  { rw amo_eval_tt_iff_distinct_eval_ff_of_eval_tt,
    rintros lit₁ lit₂ ⟨i, j, hi, hj, hij, rfl, rfl⟩ hl₁,
    have : i < length l - 1, from lt_of_lt_of_le hij (le_pred_of_lt hj),
    have := signal_nec hl this hs (amo_take_of_tt hi hl₁),
    exact signal_nec3 hl hi hs this ⟨hij, hj⟩ },
  { rw not_le at hl,
    exact eval_tt_of_ge_length (le_of_lt_succ hl) _ }
end

theorem sinz_amo_encodes_amo {l : list (literal V)} {g : gensym V} 
  (hdis : disjoint g.stock (clause.vars l)) : 
  encodes (amk 1) (sinz_amo l g) l :=
begin
  intro τ, split,
  { intro hamo,
    use sinz_tau l g τ,
    split,
    { exact sinz_forward hdis hamo },
    { intros v hv, simp [sinz_tau, hv] } },
  { rintros ⟨σ, hs, heqod⟩,
    rw [← amk.eval, eval_eq_amk_of_eqod 1 heqod],
    exact sinz_reverse hdis hs }
end

/-
theorem mem_sinz_vars_of_mem {l : list (literal V)} {g : gensym V} : 
  length l ≥ 2 → clause.vars l ⊆ cnf.vars (sinz_amo l g hdis) :=
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
-/

end sinz_amo