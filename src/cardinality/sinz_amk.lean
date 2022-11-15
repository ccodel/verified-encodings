/-
The Sinz at-most-one encoding.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import data.list.basic
import cnf.cnf
import cnf.gensym
import cnf.encoding
import cardinality.distinct
import cardinality.amk
import cardinality.alk

variables {V : Type*} [inhabited V] [decidable_eq V]

namespace sinz_amk

open list
open literal
open cnf
open clause
open assignment
open distinct
open prod
open gensym
open encoding
open amk
open alk
open nat

def S (g : gensym V) (l : list (literal V)) (r c : nat) : V := 
  g.nth ((r * length l) + c)

theorem S_not_mem_vars {g : gensym V} {l : list (literal V)} 
  (hdis : disjoint g.stock (clause.vars l)) : 
  ∀ (r c : nat), S g l r c ∉ clause.vars l :=
begin
  intros r c,
  rw S,
  have h₁ := set.disjoint_left.mp hdis,
  have h₂ := (nth_mem_stock g (r * length l + c)),
  exact h₁ h₂
end

def signal_row_prop (k : nat) (g : gensym V) (l : list (literal V)) (r c : nat) : cnf V :=
  ite (r < k + 1 ∧ c < length l - 1) 
  [[Neg (S g l r c), Pos (S g l r (c + 1))]] []

def first_prop (g : gensym V) (l : list (literal V)) (r c : nat) : cnf V :=
  if hidx : (r = 0 ∧ c < length l) then
    [[(l.nth_le c hidx.2).flip, Pos (S g l 0 c)]] 
  else []

def inc_prop (k : nat) (g : gensym V) (l : list (literal V)) (r c : nat) : cnf V :=
  if hidx : (r < k ∧ c < length l - 1 ∧ c + 1 < length l) then
    [[(l.nth_le (c + 1) hidx.2.2).flip, Neg (S g l r c), Pos (S g l (r + 1) (c + 1))]]
  else []

def sinz_amk (k : nat) (g : gensym V) (l : list (literal V)) : cnf V :=
if k ≤ 1 ∨ length l ≤ k then [] else
join ((range (k + 1)).map (λ i, join
    ((range (length l)).map (λ j,
      signal_row_prop k g l i j ++
      first_prop g l i j ++
      inc_prop k g l i j))
  )) ++ [[Neg (S g l k (length l - 1))]]

lemma helper {k c n : nat} : 1 < k → k < n → c < n - 1 → c < n :=
begin
  intros hk hn hc,
  rcases exists_eq_add_of_lt (lt_trans hk hn) with ⟨m, hm⟩,
  subst hm,
  simp at hc,
  exact lt_succ_of_lt hc
end

theorem signal_row_prop_mem {k r c : nat} {l : list (literal V)} 
  (hk : k > 1) (hl : length l > k) (g : gensym V) 
  (hr : r < k + 1) (hc : c < length l - 1) :
  [Neg (S g l r c), Pos (S g l r (c + 1))] ∈ sinz_amk k g l :=
begin
  rw sinz_amk,
  simp [not_le.mpr hl, not_le.mpr hk],
  use [r, hr, c, helper hk hl hc],
  left,
  rw signal_row_prop,
  simp [hr, hc]
end

theorem first_prop_mem {k c : nat} {l : list (literal V)}
  (hk : k > 1) (hl : length l > k) (g : gensym V)
  (hc : c < length l) :
  [(l.nth_le c hc).flip, Pos (S g l 0 c)] ∈ sinz_amk k g l :=
begin
  rw sinz_amk,
  simp [not_le.mpr hl, not_le.mpr hk],
  use 0,
  simp,
  use [c, hc],
  right, left,
  rw first_prop,
  simp [hc]
end

theorem inc_prop_mem {k r c : nat} {l : list (literal V)} 
  (hk : k > 1) (hl : length l > k) (g : gensym V) 
  (hr : r < k) (hc₁ : c < length l - 1) (hc₂ : c + 1 < length l) :
  [(l.nth_le (c + 1) hc₂).flip, Neg (S g l r c), Pos (S g l (r + 1) (c + 1))] ∈ sinz_amk k g l :=
begin
  rw sinz_amk,
  simp [not_le.mpr hk, not_le.mpr hl],
  use [r, lt_succ_of_lt hr, c, lt_of_succ_lt hc₂],
  right, right,
  rw inc_prop,
  simp [hr, hc₁, hc₂]
end

-- First arg is row, second is col in (k + 1) × |l| matrix
def signal_truth (l : list (literal V)) 
  (g : gensym V) (τ : assignment V) : nat → nat → bool
| 0       0       := l.head.eval τ 
| 0       (c + 1) := if h : (c + 1) < length l then 
                      (l.nth_le (c + 1) h).eval τ || signal_truth 0 c 
                     else ff
| (r + 1) 0       := ff
| (r + 1) (c + 1) := if h : (c + 1) < length l then
                      ((l.nth_le (c + 1) h).eval τ ∧ signal_truth r c) ||
                       signal_truth (r + 1) c
                     else ff

def rc_from_var (l : list (literal V)) (g : gensym V) (v : V) : nat → nat → (nat × nat)
| 0       0       := ⟨0, 0⟩
| 0       (c + 1) := if v = g.nth (c + 1) then ⟨0, c + 1⟩ else rc_from_var 0 c
| (r + 1) 0       := if v = g.nth ((r + 1) * length l) then ⟨r + 1, 0⟩ 
                     else rc_from_var r (length l - 1)
| (r + 1) (c + 1) := if v = g.nth ((r + 1) * length l + c + 1) then ⟨r + 1, c + 1⟩
                     else rc_from_var (r + 1) c

def sinz_tau (k : nat) (l : list (literal V))
  (g : gensym V) (τ : assignment V) : assignment V :=
  λ v, if v ∈ clause.vars l then τ v else
         signal_truth l g τ (rc_from_var l g v k (length l - 1)).1 (rc_from_var l g v k (length l - 1)).2

lemma help {a b c : nat} : b ≤ c → a + b ≤ a + c :=
begin
  exact (add_le_add_iff_left a).mpr
end

theorem rc_helper {r r' c c' : nat} (g : gensym V) {l : list (literal V)} :
  r ≤ r' → c < length l → c' < length l → 
  (r = r' → c ≤ c') → 
  rc_from_var l g (S g l r c) r' c' = ⟨r, c⟩ :=
begin
  intros hr hc hc' hreq,
  have hrc : (r * length l + c) ≤ (r' * length l + c'),
  { rcases eq_or_lt_of_le hr with ⟨rfl | hr⟩,
    { exact add_le_add_left (hreq h) _ },
    { rcases exists_eq_add_of_lt h with ⟨m, hm⟩,
      simp [hm, add_mul, add_assoc],
      rw [add_comm, add_assoc],
      exact le_add_right (le_of_lt hc) } },
  induction r' with r' ihr generalizing c',
  { simp at hr,
    subst hr,
    induction c' with c' ihc; simp at hrc,
    { subst hrc,
      simp [rc_from_var] },
    { rcases eq_or_lt_of_le hrc with (rfl | hrc),
      { simp [rc_from_var, S] },
      { simp at ihc,
        rw ← ihc (lt_of_succ_lt hc') (le_of_lt_succ hrc) (le_of_lt_succ hrc),
        have : c ≠ c' + 1, from ne_of_lt hrc,
        simp [rc_from_var, S, nth_ne_of_ne this] } } },
  { rcases eq_or_lt_of_le hr with (rfl | hr),
    { induction c' with c' ihc;
      simp at hrc,
      { simp [rc_from_var, hrc, S] },
      { have ihred := ihc (lt_of_succ_lt hc'),
        simp at ihred,
        rcases eq_or_lt_of_le hrc with (rfl | hrc),
        { simp [rc_from_var, S, add_assoc] },
        { rw ← ihred (le_of_lt_succ hrc),
          have : (r' + 1) * l.length + c ≠ (r' + 1) * l.length + c' + 1,
          { intro heq,
            rw add_assoc at heq,
            have := add_left_cancel heq,
            rw this at hrc,
            exact nat.lt_asymm hrc hrc },
          simp [rc_from_var, S, nth_ne_of_ne this], exact le_of_lt_succ hrc } } },
    { have hlen : length l - 1 < length l,
      { cases l with l₁ ls,
        { simp at hc', contradiction },
        { simp } },
      have : c ≤ length l - 1,
      { cases l with l₁ ls,
        { simp at hc, contradiction },
        { simp at hc |-, exact le_of_lt_succ hc } },
      have ihred := ihr (le_of_lt_succ hr) hlen (imp_intro this),
      induction c' with c' ihc,
      { have : r * l.length + c ≠ (r' + 1) * l.length,
        { rcases exists_eq_add_of_lt hr with ⟨m, hm⟩,
          intro heq,
          simp [← succ_eq_add_one, hm] at heq,
          rw [succ_mul, add_mul, add_assoc] at heq,
          have heqc := add_left_cancel_iff.mp heq,
          have : l.length ≤ m * l.length + l.length, from le_add_self,
          have := lt_of_lt_of_le hc this,
          exact absurd heqc (ne_of_lt this) },
        simp [rc_from_var, S, nth_ne_of_ne this],
        rw ← S,
        apply ihred,
        have h₁ : r * l.length ≤ r' * l.length,
        { exact nat.mul_le_mul_right _ (le_of_lt_succ hr) },
        have h₂ : c ≤ l.length - 1,
        { cases l with l₁ ls,
          { simp at hc, contradiction },
          { simp at hc, exact le_of_lt_succ hc } },
        exact add_le_add h₁ h₂, },
      { have : r * l.length + c ≤ (r' + 1) * l.length + c',
        { rw [add_mul, add_assoc],
          apply add_le_add,
          { exact nat.mul_le_mul_right _ (le_of_lt_succ hr) },
          { rw one_mul,
            exact le_add_right (le_of_lt hc) } },
        have himp : r = r' + 1 → c ≤ c',
        { rintro rfl,
          exact (add_le_add_iff_left ((r' + 1) * l.length)).mp this },
        rw ← ihc (lt_of_succ_lt hc') himp,
        have : r * l.length + c ≠ (r' + 1) * l.length + c' + 1,
        { exact ne_of_lt (lt_succ_of_le this) },
        simp [rc_from_var, S, nth_ne_of_ne this], exact this } } }
end

theorem rc_helper' {r r' c c' : nat} (g : gensym V) {l : list (literal V)} :
  r ≤ r' → c < length l → c' < length l → c ≤ c' →
  rc_from_var l g (S g l r c) r' c' = ⟨r, c⟩ :=
assume hr hc hc' hle, rc_helper g hr hc hc' (imp_intro hle)

-- Forward direction --
lemma sub_helper {n m : nat} : n < m → m - 1 < m :=
begin
  intro h,
  cases m,
  { simp at h, contradiction },
  { simp, exact lt_succ_self m }
end

theorem signal_semantics {k r c : nat} (hk : k > 1) {l : list (literal V)} {g : gensym V}
  (hdis : disjoint g.stock (clause.vars l))
  (hr : r < k + 1) (hc : c < length l) :
  ∀ {τ : assignment V}, 
  (signal_truth l g τ r c) = tt ↔ (alk.eval (r + 1) τ (l.take (c + 1))) = tt :=
begin
  intro τ,
  induction r with r ihr generalizing c,
  { induction c with c ihc,
    { simp [signal_truth, take_one_of_ne_nil (ne_nil_of_length_pos hc),
        alk.eval, alk, bool_symm] },
    { simp [signal_truth, hc],
      split,
      { rintros (hs | hs),
        { rw eval_take_tail_pos hc hs,
          exact eval_zero _ _ },
        { have ihred := (ihc (lt_of_succ_lt hc)).mp hs,
          have := take_sublist_of_le (le_succ (c + 1)) l,
          exact eval_tt_of_sublist_of_eval_tt this ihred } },
      { intro hl,
        cases h : (l.nth_le (c + 1) _).eval τ,
        { rw eval_take_tail_neg hc h at hl,
          exact or.inr ((ihc (lt_of_succ_lt hc)).mpr hl) },
        { simp only [eq_self_iff_true, true_or] } } } },
  {
    induction c with c ihc,
    { simp [signal_truth, take_one_of_ne_nil (ne_nil_of_length_pos hc),
        alk.eval, alk, bool_symm],
      cases h : literal.eval τ l.head; { simp } },
    {
      simp [signal_truth, hc],
      split,
      { rintros (⟨hs₁, hs₂⟩ | hs),
        { rw eval_take_tail_pos hc hs₁,
          exact (ihr (lt_of_succ_lt hr) (lt_of_succ_lt hc)).mp hs₂ },
        { have ihred := (ihc (lt_of_succ_lt hc)).mp hs,
          have : take (c + 1) l <+ take (c + 1 + 1) l,
          { exact take_sublist_of_le (le_succ (c + 1)) _ },
          exact eval_tt_of_sublist_of_eval_tt this ihred } },
      { intro hl,
        cases h : (l.nth_le (c + 1) _).eval τ,
        { rw eval_take_tail_neg hc h at hl,
          exact or.inr ((ihc (lt_of_succ_lt hc)).mpr hl) },
        { rw eval_take_tail_pos hc h at hl,
          exact or.inl ⟨rfl, (ihr (lt_of_succ_lt hr) (lt_of_succ_lt hc)).mpr hl⟩ } } } }
end

theorem sr_eval_tt_st {k r c : nat} (hk : k > 1) {l : list (literal V)} {g : gensym V}
  (hdis : disjoint g.stock (clause.vars l))
  (hr : r < k + 1) (hc : c < length l - 1) :
  ∀ (τ : assignment V), (signal_row_prop k g l r c).eval (sinz_tau k l g τ) = tt :=
begin
  intro τ,
  rw eval_tt_iff_forall_clause_eval_tt,
  intros cl hcl,
  simp [signal_row_prop, hr, hc] at hcl,
  subst hcl,
  rw eval_tt_iff_exists_literal_eval_tt,
  cases hs : (sinz_tau k l g τ) (S g l r c),
  { use Neg (S g l r c), simp [literal.eval, hs] },
  { use Pos (S g l r (c + 1)),
    have hc' : c + 1 < length l,
    { cases l with l₁ ls,
      { simp at hc, contradiction },
      { cases ls with l₂ ls,
        { simp at hc, contradiction },
        { simp at hc, simp [hc] } } },
    have hc'' : c < length l, from lt_of_succ_lt hc',
    have hc''' : c + 1 ≤ length l - 1,
    { cases l with l₁ ls,
      { simp at hc'', contradiction },
      { simp at hc' |-, exact succ_le_of_lt hc' } },
    simp [literal.eval, sinz_tau, S_not_mem_vars hdis,
      rc_helper g (le_of_lt_succ hr) hc' (sub_helper hc'') (imp_intro hc''')],
    simp [sinz_tau, S_not_mem_vars hdis] at hs,
    rw rc_helper g (le_of_lt_succ hr) hc'' (sub_helper hc'') 
      (imp_intro (le_of_succ_le hc''')) at hs,
    simp at hs,
    cases r; { simp [signal_truth, hc'], exact or.inr hs } }
end

theorem fp_eval_tt_st {k r c : nat} (hk : k > 1) {l : list (literal V)} {g : gensym V}
  (hdis : disjoint g.stock (clause.vars l))
  (hr : r < k + 1) (hc : c < length l) :
  ∀ (τ : assignment V), (first_prop g l r c).eval (sinz_tau k l g τ) = tt :=
begin
  intro τ,
  rw eval_tt_iff_forall_clause_eval_tt,
  intros cl hcl,
  cases r,
  { simp [first_prop, hc] at hcl,
    subst hcl,
    rw eval_tt_iff_exists_literal_eval_tt,
    cases hl : (l.nth_le c hc).eval τ,
    { use (l.nth_le c hc).flip,
      have hmem := mem_vars_of_mem (nth_le_mem l c hc),
      cases l.nth_le c hc;
      { rw var at hmem,
        rw literal.eval at hl,
        simp [eval_flip, hl, sinz_tau, literal.eval, hmem] } },
    { use Pos (S g l 0 c),
      simp [literal.eval, sinz_tau, S_not_mem_vars hdis],
      have : c ≤ length l - 1,
      { cases l with l₁ ls,
        { simp at hc, contradiction },
        { simp at hc |-, exact le_of_lt_succ hc } },
      rw rc_helper g (le_of_lt_succ hr) hc (sub_helper hc) (imp_intro this),
      cases c,
      { rw signal_truth,
        rw nth_le_zero at hl,
        exact hl },
      { rw signal_truth,
        simp [hc], exact or.inl hl } } },
  { simp [first_prop, hc] at hcl, contradiction }
end

theorem ip_eval_tt_st {k r c : nat} (hk : k > 1) {l : list (literal V)} {g : gensym V}
  (hdis : disjoint g.stock (clause.vars l))
  (hr : r < k) (hc : c < length l - 1) :
  ∀ (τ : assignment V), (inc_prop k g l r c).eval (sinz_tau k l g τ) = tt :=
begin
  intro τ,
  rw eval_tt_iff_forall_clause_eval_tt,
  intros cl hcl,
  rw inc_prop at hcl,
  have hc' : c + 1 < length l,
  { cases l with l₁ ls,
    { simp at hc, contradiction },
    { cases ls with l₂ ls,
      { simp at hc, contradiction },
      { simp at hc, simp [hc] } } },
  simp [hr, hc, hc'] at hcl,
  subst hcl,
  rw eval_tt_iff_exists_literal_eval_tt,
  cases hs₁ : (l.nth_le _ hc').eval (sinz_tau k l g τ),
  { use (l.nth_le _ hc').flip,
    simp [eval_flip, hs₁] },
  { cases hs₂ : (sinz_tau k l g τ) (S g l r c),
    { use Neg (S g l r c), simp [literal.eval, hs₂] },
    { use Pos (S g l (r + 1) (c + 1)),
      have hmem := mem_vars_of_mem (nth_le_mem l _ hc'),
      simp [literal.eval, hs₂],
      simp [sinz_tau, S_not_mem_vars hdis] at hs₂ |-,
      rw rc_helper g (le_of_lt hr) (lt_of_succ_lt hc') (sub_helper hc')
         (imp_intro (le_of_lt hc)) at hs₂,
      simp at hs₂,
      have : c + 1 ≤ length l - 1,
      { cases l with l₁ ls,
        { simp at hc', contradiction },
        { simp at hc |-, exact succ_le_of_lt hc } },
      rw rc_helper g (succ_le_of_lt hr) hc' (sub_helper hc') (imp_intro this),
      rw signal_truth,
      simp [hc'],
      cases l.nth_le _ hc';
      { rw var at hmem,
        simp [sinz_tau, literal.eval, hmem] at hs₁,
        simp [literal.eval],
        exact or.inl ⟨hs₁, hs₂⟩ } } }
end

theorem sinz_forward {k : nat} (hk : k > 1) {τ} {l : list (literal V)} {g : gensym V}
  (hdis : disjoint g.stock (clause.vars l)) :
  amk.eval k τ l = tt → (sinz_amk k g l).eval (sinz_tau k l g τ) = tt :=
begin
  intro hmk,
  rw eval_tt_iff_forall_clause_eval_tt,
  intros cl hcl,
  by_cases hl : length l > k,
  { simp [sinz_amk, not_le.mpr hk, not_le.mpr hl] at hcl,
    rcases hcl with (⟨r, hr, c, hc, hmem⟩ | rfl),
    { rcases hmem with (hmem | hmem | hmem),
      { by_cases hc' : c < length l - 1,
        { have := sr_eval_tt_st hk hdis hr hc' τ,
          exact eval_tt_iff_forall_clause_eval_tt.mp this _ hmem },
        { simp [signal_row_prop, hr, hc'] at hmem, contradiction } },
      { have := fp_eval_tt_st hk hdis hr hc τ,
        exact eval_tt_iff_forall_clause_eval_tt.mp this _ hmem },
      { by_cases hc' : c < length l - 1,
        { by_cases hr' : r < k,
          { have := ip_eval_tt_st hk hdis hr' hc' τ,
          exact eval_tt_iff_forall_clause_eval_tt.mp this _ hmem },
          { simp [inc_prop, hr'] at hmem, contradiction } },
        { simp [inc_prop, hc'] at hmem, contradiction } } },
    { have : length l - 1 < length l,
      { rcases exists_eq_add_of_lt (lt_trans hk hl) with ⟨m, hm⟩,
        simp [hm] },
      simp [eval_tt_iff_exists_literal_eval_tt, literal.eval,
        sinz_tau, S_not_mem_vars hdis],
      rw rc_helper g (le_refl k) this this (imp_intro (le_refl _)),
      rw amk_eval_eq_alk_succ_eval at hmk,
      simp at hmk,
      have hmt := mt (signal_semantics hk hdis (lt_succ_self k) this).mp,
      have : length l - 1 + 1 = length l,
      { rcases exists_eq_add_of_lt (lt_trans hk hl) with ⟨m, hm⟩,
        simp [hm] },
      simp [this] at hmt,
      exact hmt hmk } },
  { simp [sinz_amk, not_lt.mp hl] at hcl, contradiction }
end

-- Reverse direction --

theorem sr_eval_tt {τ} {k r c : nat} {g : gensym V} {l : list (literal V)}
  (hk : k > 1) (hl : length l > k)
  (hdis : disjoint g.stock (clause.vars l))
  (hr : r < k + 1) (hc : c < length l - 1) :
  (sinz_amk k g l).eval τ = tt →
  τ (S g l r c) = tt → ∀ {c₂ : nat}, (c₂ > c ∧ c₂ < length l) → τ (S g l r c₂) = tt :=
begin
  rintros hs ht c₂ ⟨hgt, hcl⟩,
  induction c₂ with c₂ ih,
  { linarith },
  { by_cases hcc : c = c₂,
    { subst hcc,
      have := signal_row_prop_mem hk hl g hr hc,
      have := eval_tt_iff_forall_clause_eval_tt.mp hs _ this,
      simp [eval_tt_iff_exists_literal_eval_tt] at this,
      rcases this with (hl | hl),
      { rw [literal.eval, ht] at hl, contradiction },
      { rw literal.eval at hl, exact hl } },
    { have := lt_of_le_of_ne (le_of_lt_succ hgt) hcc,
      have ihred := ih this (lt_of_succ_lt hcl),
      have : c₂ < l.length - 1,
      { rcases exists_eq_add_of_lt (lt_trans hk hl) with ⟨m, hm⟩,
        simp [hm] at hcl |-,
        exact succ_lt_succ_iff.mp hcl },
      have := signal_row_prop_mem hk hl g hr this,
      have := eval_tt_iff_forall_clause_eval_tt.mp hs _ this,
      simp [eval_tt_iff_exists_literal_eval_tt] at this,
      rcases this with (hl | hl),
      { simp [literal.eval, ihred] at hl, contradiction },
      { rw [literal.eval] at hl, exact hl } } }
end

theorem fp_eval_tt {τ} {k r c : nat} {g : gensym V} {l : list (literal V)}
  (hk : k > 1) (hl : length l > k)
  (hdis : disjoint g.stock (clause.vars l))
  (hr : r < k + 1) (hc : c < length l) :
  (sinz_amk k g l).eval τ = tt →
  alk.eval (r + 1) τ (l.take (c + 1)) = tt → τ (S g l r c) = tt :=
begin
  intros hs hlk,
  induction c with c ih generalizing r,
  { cases l with l ls,
    { rw length at hc, exact absurd hc (gt_irrefl _) },
    { simp [alk.eval, alk] at hlk,
      cases hlit : l.eval τ,
      { simp [hlit] at hlk, contradiction },
      { simp [hlit] at hlk,
        subst hlk,
        rw eval_tt_iff_forall_clause_eval_tt at hs,
        have := hs _ (first_prop_mem hk hl g hc),
        simp [eval_tt_iff_exists_literal_eval_tt] at this,
        rcases this with (hl | hl),
        { rw [eval_flip, hlit] at hl, contradiction },
        { rw literal.eval at hl, exact hl } } } },
  { have hc' : c < length l - 1,
    { rcases exists_eq_add_of_lt (lt_trans hk hl) with ⟨m, hm⟩,
      simp [hm] at hc |-,
      exact succ_lt_succ_iff.mp hc },
    cases hx : literal.eval τ (l.nth_le _ hc),
    { rw eval_take_tail_neg hc hx at hlk,
      have ihred := ih (lt_of_succ_lt hc) hr hlk,
      exact sr_eval_tt hk hl hdis hr hc' hs ihred ⟨lt_succ_self c, hc⟩ },
    { rw eval_take_tail_pos hc hx at hlk,
      rw eval_tt_iff_forall_clause_eval_tt at hs,
      cases r,
      { have := hs _ (first_prop_mem hk hl g hc),
        simp [eval_tt_iff_exists_literal_eval_tt] at this,
        rcases this with (hl | hl),
        { simp [eval_flip, hx] at hl, contradiction },
        { rw literal.eval at hl, exact hl } },
      { have ihred := ih (lt_of_succ_lt hc) (lt_of_succ_lt hr) hlk,
        have := hs _ (inc_prop_mem hk hl g (succ_lt_succ_iff.mp hr) hc' hc),
        simp [eval_tt_iff_exists_literal_eval_tt] at this,
        rcases this with (hl | hl | hl),
        { rw [eval_flip, hx] at hl, contradiction },
        { rw [literal.eval, ihred] at hl, contradiction },
        { rw literal.eval at hl, exact hl } } } }
end

theorem sinz_reverse {k : nat} (hk : k > 1) {τ} {l : list (literal V)} {g : gensym V}
  (hdis : disjoint g.stock (clause.vars l)) :
  (sinz_amk k g l).eval τ = tt → amk.eval k τ l = tt :=
begin
  intro hs,
  have hs_copy := hs,
  by_cases hl : length l > k,
  { simp [sinz_amk, not_le.mpr hk, not_le.mpr hl,   
      eval_tt_iff_forall_clause_eval_tt] at hs,
    have := hs _ (or.inr rfl),
    simp [eval_tt_iff_exists_literal_eval_tt, literal.eval] at this,
    have hl' : length l - 1 < length l,
    { rcases exists_eq_add_of_lt (lt_trans hk hl) with ⟨m, hm⟩,
      simp [hm] },
    have hl'' : length l - 1 + 1 = length l,
    { rcases exists_eq_add_of_lt (lt_trans hk hl) with ⟨m, hm⟩,
      simp [hm] },
    have hmt := mt (fp_eval_tt hk hl hdis (lt_succ_self k) hl' hs_copy),
    simp at hmt,
    have := hmt this,
    simp [hl''] at this,
    have hamkalk := amk_eval_eq_alk_succ_eval k τ l,
    rw [this, bool.bnot_ff] at hamkalk,
    exact hamkalk },
  { exact eval_tt_of_ge_length (not_lt.mp hl) _ }
end

theorem sinz_amk_encodes_amk {k : nat} (hk : k > 1) {l : list (literal V)} {g : gensym V}
  (hdis : disjoint g.stock (clause.vars l)) :
  encodes (amk k) (sinz_amk k g l) l :=
begin
  intro τ, split,
  { intro hmk,
    use sinz_tau k l g τ,
    split,
    { exact sinz_forward hk hdis hmk },
    { intros v hv, simp [sinz_tau, hv] } },
  { rintros ⟨σ, hs, heqod⟩,
    rw [← amk.eval, eval_eq_amk_of_eqod _ heqod],
    exact sinz_reverse hk hdis hs }
end

end sinz_amk