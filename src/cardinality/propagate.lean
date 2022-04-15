/-

Experiments with propagation structures.

Author: Cayden Codel
-/

import data.list.basic
import cnf.cnf
import cnf.gensym
import cnf.encoding
import cardinality.distinct
import cardinality.cardinality

variables {V : Type*} [inhabited V] [decidable_eq V]

namespace propagate

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

def signal_row_prop (g : gensym V) (l : list (literal V)) (r c : nat) : cnf V := 
  ite (c > 0) [[Neg (S g l r (c - 1)), Pos (S g l r c)]] []

def first_prop (g : gensym V) (l : list (literal V)) (r : nat) {c : nat} 
  (hc : c < length l) : cnf V :=
  ite (r = 0) [[(nth_le l c hc).flip, Pos (S g l 0 c)]] []

def inc_prop (g : gensym V) (l : list (literal V)) (r : nat) {c : nat} (hc : c < length l) : cnf V :=
  ite (c > 0 ∧ r > 0) [[
    (nth_le l c hc).flip, Neg (S g l (r - 1) (c - 1)), Pos (S g l r c)
  ]] []

def neg_unit (g : gensym V) (l : list (literal V)) (k r c : nat) : cnf V :=
  ite (r = k ∧ c = length l - 1) [[Neg (S g l r c)]] []

def prefix_true (t : nat) (l : list (literal V)) (τ : assignment V) : nat :=
  ((l.take t).map (literal.eval τ)).count tt

@[simp] theorem prefix_true_nil : 
  ∀ (t : nat) (τ : assignment V), prefix_true t [] τ = 0 :=
assume τ, by simp [prefix_true]

@[simp] theorem prefix_true_zero : 
  ∀ (l : list (literal V)) (τ : assignment V), prefix_true 0 l τ = 0 :=
assume l τ, by simp [prefix_true]

theorem prefix_true_cons_pos {lit : literal V} {τ : assignment V} :  
  lit.eval τ = tt → ∀ (t : nat) (l : list (literal V)), 
  prefix_true (t + 1) (lit :: l) τ = prefix_true t l τ + 1 :=
assume h, by simp [prefix_true, h]

theorem prefix_true_cons_neg {lit : literal V} {τ : assignment V} :
  lit.eval τ = ff → ∀ (t : nat) (l : list (literal V)),
  prefix_true (t + 1) (lit :: l) τ = prefix_true t l τ :=
assume h, by simp [prefix_true, h]

theorem prefix_true_tail_pos {t : nat} {l : list (literal V)} {τ : assignment V} 
  {ht : t < length l} : (l.nth_le t ht).eval τ = tt → 
  prefix_true (t + 1) l τ = prefix_true t l τ + 1 :=
begin
  induction t with t ih generalizing l,
  { rcases exists_cons_of_ne_nil (ne_nil_of_length_pos ht) with ⟨l₁, ls, rfl⟩,
    intro hl,
    rw [nth_le_zero, head] at hl,
    simp [prefix_true, hl] },
  { rcases exists_cons_of_ne_nil (ne_nil_of_length_pos (pos_of_gt ht)) with ⟨l₁, ls, rfl⟩,
    intro hl,
    rw nth_le at hl,
    cases h₁ : l₁.eval τ,
    { simp only [prefix_true_cons_neg h₁, ih hl] },
    { simp only [prefix_true_cons_pos h₁, ih hl] } }
end

theorem prefix_true_tail_neg {t : nat} {l : list (literal V)} {τ : assignment V}
  {ht : t < length l} : (l.nth_le t ht).eval τ = ff →
  prefix_true (t + 1) l τ = prefix_true t l τ :=
begin
  induction t with t ih generalizing l,
  { rcases exists_cons_of_ne_nil (ne_nil_of_length_pos ht) with ⟨l₁, ls, rfl⟩,
    intro hl,
    rw [nth_le_zero, head] at hl,
    simp [prefix_true, hl] },
  { rcases exists_cons_of_ne_nil (ne_nil_of_length_pos (pos_of_gt ht)) with ⟨l₁, ls, rfl⟩,
    intro hl,
    rw nth_le at hl,
    cases h₁ : l₁.eval τ,
    { simp only [prefix_true_cons_neg h₁, ih hl] },
    { simp only [prefix_true_cons_pos h₁, ih hl] } }
end

theorem prefix_true_le_of_lt {t₁ t₂ : nat} : t₁ < t₂ → 
  ∀ (l : list (literal V)) (τ : assignment V), 
  prefix_true t₁ l τ ≤ prefix_true t₂ l τ :=
begin
  intros ht l τ,
  induction t₂ with t₂ ih generalizing t₁ l,
  { linarith },
  { cases t₁,
    { rw prefix_true_zero, exact zero_le _ },
    { cases l with l₁ ls,
      { simp only [prefix_true_nil] },
      { have ihred := ih ls (lt_of_succ_lt_succ ht),
        cases hl₁ : (l₁.eval τ),
        { simp only [prefix_true_cons_neg hl₁, ihred] },
        { simp only [prefix_true_cons_pos hl₁, succ_le_succ_iff, ihred] } } } }
end

theorem prefix_true_le_iff_amk {k : nat} : ∀ (l : list (literal V)) (τ : assignment V),
  prefix_true (length l) l τ ≤ k ↔ amk.eval k τ l = tt :=
assume l τ, by simp [prefix_true, amk.eval, amk]

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

theorem rc_helper {k : nat} (g : gensym V) {l : list (literal V)} {r c : nat} :   
  --len = length l →
  --r < k + 1 → c < len → 
  --rc_from_var l g (S g l r c) k (len - 1) = ⟨r, c⟩ :=
  r < k + 1 → c < length l →
  rc_from_var l g (S g l r c) k (length l - 1) = ⟨r, c⟩ :=
begin
  sorry
  /-
  generalize hn : (k * len + (len - 1)) = n,
  induction n using nat.strong_induction_on with n ih generalizing len r c,
  have : 0 < length l := hl ▸ pos_of_gt hc,
  rcases exists_cons_of_ne_nil (ne_nil_of_length_pos this) with ⟨l₁, ls, rfl⟩,
  cases k,
  { cases ls with l₂ ls,
    { simp at hl hr,
      rw [hl, lt_one_iff] at hc,
      simp [rc_from_var, hl, hr, hc] },
    { rw length at hl,
      rw lt_one_iff at hr,
      simp [hl, hr, rc_from_var, S],
      by_cases hc₂ : c = ls.length + 1,
      { simp only [hc₂, eq_self_iff_true, if_true] },
      { simp [nth_ne_of_ne hc₂],
        simp at ih,
        have hn' : n - 1 < n, { simp [← hn, hl] },
        have ihred := ih _ hn',
      }
      simp [hl, hr, rc_from_var, S],
      simp at hn hr hc ih,
      simp [rc_from_var, hr, hc, S],
      { simp [hc₂] },
      { simp [nth_ne_of_ne hc₂],
        have hn' : n - 1 < n, { simp [← hn] },
        have hc' : c < (l₂ :: ls).length,
        { rw length, exact (ne.le_iff_lt hc₂).mp (le_of_lt_succ hc) },
        have hc₂' : (l₂ :: ls).length - 1 = n - 1,
        { rw [length, hn] },
        have ihred := ih _ hn' hr hc' hc₂',
      }

    }
  }
  -/
end

def sinz_assignment (k : nat) (l : list (literal V))
  (g : gensym V) (τ : assignment V) : assignment V :=
  λ v, if v ∈ clause.vars l then τ v else
         signal_truth l g τ (rc_from_var l g v k (length l - 1)).1 (rc_from_var l g v k (length l - 1)).2

theorem sa_helper {k : nat} {g : gensym V} {l : list (literal V)} {r c : nat} 
  (hdis : disjoint g.stock (clause.vars l)) :
  r < k + 1 → c < length l → ∀ (τ : assignment V),
  (sinz_assignment k l g τ) (S g l r c) = signal_truth l g τ r c :=
begin
  intros hr hc τ,
  simp [sinz_assignment, S_not_mem_vars hdis r c, rc_helper g hr hc]
end

theorem st_eqod {g : gensym V} {l : list (literal V)} {r c : nat} {τ σ : assignment V} :
  l ≠ [] → (τ≡clause.vars l≡σ) → signal_truth l g τ r c = signal_truth l g σ r c :=
begin
  sorry
  /-
  intros hl heqod,
  rcases exists_cons_of_ne_nil hl with ⟨l₁, ls, rfl⟩,
  induction r with r ih₁,
  { induction c with c ih₂,
    { have := mem_vars_of_mem (mem_cons_self l₁ ls),
      simp [signal_truth, eval_eq_of_eqod_of_var_mem heqod this] },
    { by_cases hc : c < ls.length,
      { have := mem_vars_of_mem (nth_le_mem ls c hc),
        have := (vars_subset_of_vars_cons l₁ ls) this,
        have := eval_eq_of_eqod_of_var_mem heqod this,
        simp [signal_truth, hc, ih₂],
        cases h₁ : literal.eval τ (ls.nth_le c hc),
        { cases h₂ : literal.eval σ (ls.nth_le c hc),
          { refl },
          { rw [h₁, h₂] at this, contradiction } },
        { cases h₂ : literal.eval σ (ls.nth_le c hc),
          { rw [h₁, h₂] at this, contradiction },
          { refl } } },
      { simp [signal_truth, hc] } } },
  {
    induction c with c ih₂,
    { simp [signal_truth] },
    { by_cases hc : c < ls.length,
      {
        simp [signal_truth, hc],
        have := mem_vars_of_mem (nth_le_mem ls c hc),
        have := (vars_subset_of_vars_cons l₁ ls) this,
        have := eval_eq_of_eqod_of_var_mem heqod this,
        cases r,
        { simp [signal_truth, hc] at ih₁,
          cases h₁ : literal.eval τ (ls.nth_le c hc),
          {
            cases h₂ : literal.eval σ (ls.nth_le c hc),
            { have : ff || signal_truth (l₁ :: ls) g τ 0 c = ff || signal_truth (l₁ :: ls) g σ 0 c,
              {
                rw ← h₁,
              }
            }
          }
        },
        cases h₁ : literal.eval τ (ls.nth_le c hc),
        {
          cases h₂ : literal.eval σ (ls.nth_le c hc),
          { cases r,
            {
            }
          }
        }
      }
    }
  }
  -/
end

theorem st_diag {g : gensym V} {l : list (literal V)} {r c : nat} :
  c < length l → c < r → ∀ (τ : assignment V),
  signal_truth l g τ r c = ff :=
begin
  intros hc hrc τ,
  generalize hn : r + c = n,
  induction n using nat.strong_induction_on with n ih generalizing r c,
  cases r,
  { linarith },
  { cases c,
    { refl },
    { simp [signal_truth, hc],
      split,
      { have hn_lt : n - 2 < n,
        { rw [hn.symm, succ_add, add_succ],
          simp, exact lt_trans (lt_succ_self (r + c)) (lt_succ_self _) },
        have hn' : r + c = n - 2,
        { rw [hn.symm, succ_add, add_succ], simp },
        have hc' := lt_of_succ_lt hc,
        have ihred := ih (n - 2) hn_lt hc' (lt_of_succ_lt_succ hrc) hn',
        exact or.inr ihred },
      { have hn_lt : n - 1 < n,
        { simp [hn.symm, lt_succ_self r] },
        have hn' : (r + 1) + c = n - 1,
        { simp [hn.symm, succ_add, add_succ] },
        have ihred := ih (n - 1) hn_lt (lt_of_succ_lt hc) (lt_of_succ_lt hrc) hn',
        exact ihred } } }
end

theorem st_cons_neg {g : gensym V} {l : list (literal V)} {r c : nat} 
  {τ : assignment V} {lit : literal V} (hdis : disjoint g.stock (clause.vars (lit :: l))) :
  c < length l → lit.eval τ = ff →
  signal_truth (lit :: l) g τ r (c + 1) = signal_truth l g τ r c  :=
begin
  intros hc heval,
  induction c with c ih generalizing r,
  { cases r,
    { simp [signal_truth, hc, nth_le_zero, heval] },
    { simp [signal_truth, hc, nth_le_zero],
      cases r,
      { simp [signal_truth, heval] },
      { simp [signal_truth] } } },
  { cases r,
    { simp [signal_truth, hc, ih (lt_of_succ_lt hc), lt_of_succ_lt hc],
      cases h : literal.eval τ (l.nth_le (c + 1) hc);
      { refl } },
    { simp [signal_truth, hc, ih (lt_of_succ_lt hc), lt_of_succ_lt hc],
      cases h : literal.eval τ (l.nth_le (c + 1) hc);
      { simp } } }
end


theorem st_cons_pos {g : gensym V} {l : list (literal V)} {r c : nat}
  {τ : assignment V} {lit : literal V} (hdis : disjoint g.stock (clause.vars (lit :: l))) :
  c < length l → lit.eval τ = tt →
  signal_truth (lit :: l) g τ (r + 1) (c + 1) = signal_truth l g τ r c :=
begin
  sorry
  /-
  intros hc heval,
  induction c with c ih generalizing r,
  { cases r; { simp [signal_truth, hc, nth_le_zero, heval] } },
  { cases r,
    { 
      simp [signal_truth, hc, ih (lt_of_succ_lt hc), lt_of_succ_lt hc],
      cases h : literal.eval τ (l.nth_le (c + 1) hc),
      { simp },
      {
        simp,
        right, left,
        induction c with c ih₂,
        { simp [signal_truth, heval] },
        { 
          simp [signal_truth, lt_of_succ_lt (lt_of_succ_lt hc)],
          have : c < l.length → ∀ {r : nat}, signal_truth (lit :: l) g τ (r + 1) (c + 1) = signal_truth l g τ r c,
          {

          },
          have ihred := ih₂ 
        }
      }
    }
  }
  -/
end

-- Changed format of proofs for signal row

theorem signal_row_prop_eval_tt {g : gensym V} {l : list (literal V)} {k r c : nat} 
  (hdis : disjoint g.stock (clause.vars l)) : 
  r < k + 1 → c < length l →
  ∀ (τ : assignment V), (signal_row_prop g l r c).eval (sinz_assignment k l g τ) = tt :=
begin
  intros hr hc τ,
  rw eval_tt_iff_forall_clause_eval_tt,
  intros cl hcl,
  cases c,
  { simp [signal_row_prop] at hcl, exfalso, exact hcl },
  { simp [signal_row_prop] at hcl,
    subst hcl,
    rw eval_tt_iff_exists_literal_eval_tt,
    cases h : (sinz_assignment k l g τ) (S g l r c),
    { use [(Neg (S g l r c))],
      simp [literal.eval, h] },
    { use [(Pos (S g l r (c + 1)))],
      simp [literal.eval],
      rw sa_helper hdis hr hc,
      rw sa_helper hdis hr (lt_of_succ_lt hc) at h,
      cases r;
      { simp [signal_truth, hc],
        exact or.inr h } } }
end

theorem signal_semantics {g : gensym V} {l : list (literal V)} {r c : nat} 
  (hdis : disjoint g.stock (clause.vars l)) :
  c < length l → ∀ (τ : assignment V),
  signal_truth l g τ r c = tt ↔ prefix_true (c + 1) l τ ≥ r + 1 :=
begin
  intros hc τ,
  generalize hn : r + c = n,
  induction n using nat.strong_induction_on with n ih generalizing r c l,
  rcases exists_cons_of_ne_nil (ne_nil_of_length_pos (pos_of_gt hc)) with ⟨l₁, ls, rfl⟩,
  have hdis' : disjoint g.stock (clause.vars ls),
  { have := vars_subset_of_subset (subset_cons l₁ ls),
    exact set.disjoint_of_subset_right this hdis },
  cases r,
  { cases c,
    { simp [signal_truth, prefix_true],
      exact ⟨λ h, h.symm, λ h, h.symm⟩ },
    { have hn_lt : n - 1 < n, { simp [← hn, lt_succ_self c] },
      have hn' : 0 + c = n - 1, { simp [← hn] },
      have hc' := lt_of_succ_lt_succ hc,
      have ihred := ih (n - 1) hn_lt hdis' hc' hn',
      cases hl₁ : l₁.eval τ,
      { rw [prefix_true_cons_neg hl₁, st_cons_neg hdis hc' hl₁],
        exact ihred },
      { split,
        { intro _,
          simp [prefix_true_cons_pos hl₁, succ_le_succ_iff] },
        { intro hp,
          simp [signal_truth, hc'],
          have ihred₂ := ih (n - 1) hn_lt hdis (lt_succ_of_lt hc') hn',
          right, apply ihred₂.mpr,
          simp [prefix_true_cons_pos hl₁, succ_le_succ_iff] } } } },
  { cases c,
    { split,
      { rw st_diag hc (zero_lt_succ r), intro h, contradiction },
      { cases hl₁ : l₁.eval τ,
        { intro hp,
          rw [prefix_true_cons_neg hl₁, prefix_true_zero] at hp,
          linarith },
        { intro hp,
          simp [prefix_true_cons_pos hl₁, prefix_true_zero, succ_le_succ_iff] at hp,
          exfalso, exact hp } } },
    { cases hl₁ : l₁.eval τ,
      { have hn_lt : n - 1 < n, { simp [← hn, lt_succ_self r] },
        have hn' : (r + 1) + c = n - 1, { simp [← hn, succ_add, add_succ] },
        have hc' := lt_of_succ_lt_succ hc,
        rw [prefix_true_cons_neg hl₁, st_cons_neg hdis hc' hl₁],
        exact ih (n - 1) hn_lt hdis' hc' hn' },
      { have hn_lt : n - 2 < n,
        { simp [← hn, succ_add, add_succ],
          exact lt_trans (lt_succ_self (r + c)) (lt_succ_self _) },
        have hn' : r + c = n - 2, { simp [← hn, succ_add, add_succ] },
        have hc' := lt_of_succ_lt_succ hc,
        rw [prefix_true_cons_pos hl₁, st_cons_pos hdis hc' hl₁],
        have := ih (n - 2) hn_lt hdis' hc' hn',
        split,
        { intro hs, exact succ_le_succ_iff.mpr (this.mp hs) },
        { intro hp, exact this.mpr (succ_le_succ_iff.mp hp) } } } }
end

theorem first_prop_eval_tt {g : gensym V} {l : list (literal V)} {k r c : nat} 
  (hdis : disjoint g.stock (clause.vars l)) (hr : r < k + 1) (hc : c < length l) :
  ∀ (τ : assignment V), (first_prop g l r hc).eval (sinz_assignment k l g τ) = tt :=
begin
  intro τ,
  rw eval_tt_iff_forall_clause_eval_tt,
  intros cl hcl,
  cases c,
  { cases r,
    { simp [first_prop] at hcl,
      subst hcl,
      rw eval_tt_iff_exists_literal_eval_tt,
      cases h : (l.nth_le 0 hc).eval τ,
      { use (l.nth_le 0 hc).flip,
        simp [eval_flip],
        have hmem := mem_vars_of_mem (nth_le_mem l 0 hc),
        cases (l.nth_le 0 hc);
        { rw var at hmem,
          simp [var, literal.eval] at h,
          simp [sinz_assignment, literal.eval, hmem, h] } },
      { use (Pos (S g l 0 0)),
        simp [literal.eval, sa_helper hdis hr hc, signal_truth, 
          ← nth_le_zero hc, h] } },
    { simp [first_prop] at hcl, exfalso, exact hcl } },
  { cases r,
    { simp [first_prop] at hcl,
      subst hcl,
      rw eval_tt_iff_exists_literal_eval_tt,
      cases h : (l.nth_le (c + 1) hc).eval τ,
      { use (l.nth_le (c + 1) hc).flip,
        simp [eval_flip],
        have hmem := mem_vars_of_mem (nth_le_mem l (c + 1) hc),
        cases (l.nth_le (c + 1) hc);
        { rw var at hmem,
          simp [var, literal.eval] at h,
          simp [sinz_assignment, literal.eval, hmem, h] } },
      { use (Pos (S g l 0 (c + 1))),
        simp [literal.eval, sa_helper hdis hr hc, signal_truth, hc],
        exact or.inl h } },
    { simp [first_prop] at hcl, exfalso, exact hcl } }
end

theorem inc_prop_eval_tt {g : gensym V} {l : list (literal V)} {k r c : nat} 
  (hdis : disjoint g.stock (clause.vars l)) (hr : r < k + 1) (hc : c < length l) :
  ∀ (τ : assignment V), (inc_prop g l r hc).eval (sinz_assignment k l g τ) = tt :=
begin
  intro τ,
  rw eval_tt_iff_forall_clause_eval_tt,
  intros cl hcl,
  cases c,
  { simp [inc_prop] at hcl, exfalso, exact hcl },
  { cases r,
    { simp [inc_prop] at hcl, exfalso, exact hcl },
    { simp [inc_prop] at hcl,
      subst hcl,
      rw eval_tt_iff_exists_literal_eval_tt,
      by_cases h : ((l.nth_le c.succ hc).eval τ = tt) ∧ 
                   ((signal_truth l g τ r c) = tt),
      { use (Pos (S g l (r + 1) (c + 1))),
        simp [literal.eval, sa_helper hdis hr hc, signal_truth, hc],
        exact or.inl h },
      { simp at h,
        have hmem := mem_vars_of_mem (nth_le_mem l (c + 1) hc),
        cases h₂ : ((l.nth_le c.succ hc).eval τ),
        { use (l.nth_le c.succ hc).flip,
          cases l.nth_le c.succ hc;
          { rw var at hmem,
            rw literal.eval at h₂,
            simp [eval_flip, literal.eval, sinz_assignment, hmem, h₂] } },
        { use (Neg (S g l r c)),
          simp [literal.eval, sa_helper hdis (lt_of_succ_lt hr) (lt_of_succ_lt hc)],
          exact h h₂ } } } }
end

#exit -- The lack of length proofs for first_prop etc. cause errors...

def sinz_amkv3 (k : nat) {g : gensym V} {l : list (literal V)}
  (hdis : disjoint g.stock (clause.vars l)) : cnf V :=
if l = [] then [] else
join ((range (k + 1)).map (λ i, join
    ((range (length l)).map (λ j,
      signal_row_prop g l i j ++
      first_prop g l i j ++
      inc_prop g l i j ++
      neg_unit g l k i j
    ))
  ))


theorem unit_mem (k : nat) {g : gensym V} {l : list (literal V)}
  (hdis : disjoint g.stock (clause.vars l)) : 
  l ≠ [] → [Neg (S g l k (length l - 1))] ∈ sinz_amkv3 k hdis :=
begin
  intro hl,
  rcases exists_cons_of_ne_nil hl with ⟨l₁, ls, rfl⟩,
  simp [sinz_amkv3],
  use [k, lt_succ_self k, ls.length, lt_succ_self ls.length],
  right, right, right,
  simp [neg_unit]
end

theorem exists_means_sa {k : nat} {g : gensym V} {l : list (literal V)}
  {hdis : disjoint g.stock (clause.vars l)} {τ : assignment V} :
  ((sinz_amkv3 k hdis).eval τ = tt) → 
  ((sinz_amkv3 k hdis).eval (sinz_assignment k l g τ) = tt ∧
  ((sinz_assignment k l g τ)≡(clause.vars l)≡τ)) :=
begin
  sorry
  /-
  intros τ ht,
  induction k with k ih,
  { cases l with l₁ ls,
  sorry
    { simp [sinz_amkv3] },
    { 
      split,
      {
        simp [sinz_amkv3, eval_tt_iff_forall_clause_eval_tt] at ht |-,
        intros cl c hc h,
        rcases h with (h | h | h | h),
        { 
        }

      }
    }
  },
  {
    sorry,
  }
  -/
end

theorem enc (k : nat) {g : gensym V} {l : list (literal V)}
  (hdis : disjoint g.stock (clause.vars l)) : 
  encodes (amk k) (sinz_amkv3 k hdis) l :=
begin
  intro τ,
  rw ← amk.eval,
  cases l with l₁ ls,
  { simp, use (sinz_assignment k [] g τ),
    simp [sinz_amkv3] },
  { split,
    { intro hamk,
      use (sinz_assignment k (l₁ :: ls) g τ),
      split,
      { rw sinz_amkv3,
        simp,
        rw eval_tt_iff_forall_clause_eval_tt,
        intros cl hcl,
        rcases exists_of_mem_join hcl with ⟨cl₂, hcl₂, hcc₃⟩,
        simp only [mem_map, mem_range] at hcl₂,
        rcases hcl₂ with ⟨r, hr, rfl⟩,
        simp at hcc₃,
        rcases hcc₃ with ⟨c, hc, h⟩,
        rcases h with (h | h | h | h),
        { have := signal_row_prop_eval_tt hdis hr hc τ,
          rw eval_tt_iff_forall_clause_eval_tt at this,
          exact this cl h },
        { have := first_prop_eval_tt hdis hr hc τ,
          rw eval_tt_iff_forall_clause_eval_tt at this,
          exact this cl h },
        { have := inc_prop_eval_tt hdis hr hc τ,
          rw eval_tt_iff_forall_clause_eval_tt at this,
          exact this cl h },
        { by_cases hrc : r = k ∧ c = length ls,
          { simp [neg_unit, hrc] at h,
            subst h,
            simp [clause.eval_singleton, literal.eval],
            rw hrc.1 at hr,
            rw hrc.2 at hc,
            rw sa_helper hdis hr hc τ,
            have := (prefix_true_le_iff_amk (l₁ :: ls) τ).mpr hamk,
            rw length at this,
            by_contradiction,
            rw [eq_tt_eq_not_eq_ff, signal_semantics hdis hc] at h,
            linarith },
          { simp [neg_unit, hrc] at h, exfalso, exact h } } },
      { rw sinz_assignment,
        intros v hv,
        simp [hv] } },
    { rintros ⟨σ, hs, heqod⟩,
      rcases exists_means_sa hs with ⟨hs₂, heqod₂⟩,
      simp [eval_tt_iff_forall_clause_eval_tt] at hs₂,
      have hlen : ls.length < length (l₁ :: ls), simp,
      have := unit_mem k hdis (cons_ne_nil l₁ ls),
      have hcon := hs₂ _ this,
      simp [clause.eval_singleton, literal.eval] at hcon,
      rw sa_helper hdis (lt_succ_self k) hlen at hcon,
      apply (prefix_true_le_iff_amk _ _).mp,
      by_contradiction,
      simp only [length, not_le] at h,
      rw ← succ_le_iff at h,
      have := (signal_semantics hdis hlen τ).mpr h,
      rw st_eqod heqod at this,
      rw this at hcon,
      contradiction } },
end

end propagate