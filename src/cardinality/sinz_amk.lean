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

open list nat prod
open literal clause cnf assignment distinct gensym encoding amk alk

variables (k : nat) {l : list (literal V)} {g : gensym V}
          {τ : assignment V} (hdis : disj l g)

def sig_var_matrix (V : Type*) := nat → nat → V  

def matrix (g : gensym V) (n : nat) : sig_var_matrix V :=
  λ row col, g.nth ((row * n) + col)

-- i runs from 0 to (length l - 1)
@[inline] def xi_to_si (S : sig_var_matrix V) (i : nat) (lit : literal V) : clause V :=
  [lit.flip, Pos (S 0 i)]

-- row runs from 0 to k, col runs from 0 to (length l - 2), with n = |l|
@[inline] def si_to_next_si (S : sig_var_matrix V) (n row col : nat) : cnf V :=
  if (col < n - 1) then [[Neg (S row col), Pos (S row (col + 1))]] else []

-- row runs from 0 to k - 1, col runs from 0 to (length l - 1), with n = |l|
@[inline] def ternary (S : sig_var_matrix V) (n row col : nat) (lit : literal V) : cnf V :=
  if (0 < col) then [[lit.flip, Neg (S row (col - 1)), Pos (S (row + 1) col)]] else []

def sinz_amk (k : nat) : enc_fn V
| []       g := ⟨[], g⟩
| l        g :=
  let n := length l in
  let S := matrix g n in
  ⟨(map_with_index (λ (idx : nat) (lit : literal V), xi_to_si S idx lit)) l ++

   join ((range (k + 1)).map (λ row,
     join ((range (n - 1)).map (λ col, si_to_next_si S n row col)))) ++

   join ((range k).map (λ row,
     join (map_with_index (λ (col : nat) (lit : literal V), ternary S n row col lit) l))) ++
  
   [[Neg (S k (n - 1))]],
   (g.nfresh ((k + 1) * length l)).2⟩

theorem sinz_amk_mem_vars :
  ∀ ⦃v⦄, v ∈ (sinz_amk k l g).1.vars → v ∈ (clause.vars l) ∨ (v ∈ (g.nfresh ((k + 1) * length l)).1) :=
begin
  cases l with lit₁ ls,
  { simp [sinz_amk] },
  { intros v hv,
    simp [sinz_amk, -length, -map_with_index_cons] at hv,
    rcases hv with (hmem | ⟨row, hrow, col, hcol, hmem⟩ | ⟨row, hrow, _, ⟨_, col, ⟨hcol, rfl⟩, rfl⟩, h⟩ | rfl),
    { rcases mem_vars_iff_exists_mem_clause_and_mem.mp hmem with ⟨c, hc, hv⟩,
      simp [-length, -map_with_index_cons] at hc,
      rcases hc with ⟨lit, i, ⟨hi, rfl⟩, rfl⟩,
      simp [xi_to_si, flip_var_eq, var] at hv,
      rcases hv with (rfl | rfl),
      { exact or.inl (mem_vars_of_mem (nth_le_mem _ _ hi)) },
      { right,
        unfold matrix,
        apply nth_mem_nfresh_of_lt,
        rw [zero_mul, zero_add, add_mul, one_mul, add_comm],
        exact lt_add_right _ _ _ hi } },
    { rcases mem_vars_iff_exists_mem_clause_and_mem.mp hmem with ⟨c, hc, hv⟩,
      simp at hcol,
      simp [si_to_next_si, hcol] at hc, subst hc,
      simp [flip_var_eq, var] at hv,
      right,
      rcases hv with (rfl | rfl);
      unfold matrix; apply nth_mem_nfresh_of_lt,
      { have h₁ : row * (ls.length + 1) + col < (row + 1) * (ls.length + 1),
        { rw [add_mul, one_mul], exact (add_lt_add_iff_left _).mpr (lt_succ_of_lt hcol) },
        exact lt_of_lt_of_le h₁ (nat.mul_le_mul_right _ (succ_le_of_lt hrow)) },
      { have h₁ : row * (ls.length + 1) + (col + 1) < (row + 1) * (ls.length + 1),
        { rw [add_mul, one_mul], exact (add_lt_add_iff_left _).mpr (succ_lt_succ hcol) },
        exact lt_of_lt_of_le h₁ (nat.mul_le_mul_right _ (succ_le_of_lt hrow)) } },
    { cases col,
      { simp [ternary] at h, contradiction },
      { simp [ternary, var, flip_var_eq, -length, -nth_le] at h,
        rcases h with (rfl | rfl | rfl),
        { exact or.inl (mem_vars_of_mem (nth_le_mem _ _ hcol)) },
        { right,
          rw length at hcol,
          unfold matrix,
          apply nth_mem_nfresh_of_lt,
          have h₁ : row * (ls.length + 1) + col < (row + 1) * (ls.length + 1),
          { rw [add_mul, one_mul], exact (add_lt_add_iff_left _).mpr (lt_of_succ_lt hcol) },
          exact lt_of_lt_of_le h₁ (nat.mul_le_mul_right _ (succ_le_of_lt (lt_succ_of_lt hrow))) },
        { right,
          simp [length, succ_eq_add_one] at hcol |-,
          unfold matrix,
          apply nth_mem_nfresh_of_lt,
          apply lt_of_lt_of_le (add_lt_add_left (succ_lt_succ hcol) _),
          have : (row + 1) * (ls.length + 1) + (ls.length + 1) = (row + 2) * (ls.length + 1),
          { simp [add_mul, two_mul, add_assoc] },
          rw this,
          exact nat.mul_le_mul_right _ (succ_le_succ (succ_le_of_lt hrow)) } } },
    { simp [var, matrix], right,
      apply nth_mem_nfresh_of_lt,
      simp [add_mul] } }
end

theorem matrix_not_mem_vars {g : gensym V} {l : list (literal V)} :
  disj l g → ∀ (r c : nat), (matrix g (length l) r c) ∉ clause.vars l :=
begin
  intros hdis r c,
  rw matrix,
  exact disj_right.mp hdis (nth_mem_stock _ _)
end
 
theorem xi_to_si_mem_sinz_amk (g : gensym V) {i : nat} (Hi : i < length l) :
  [(l.nth_le i Hi).flip, Pos (matrix g (length l) 0 i)] ∈ (sinz_amk k l g).1 :=
begin
  cases l with lit₁ ls, { simp at Hi, contradiction },
  rw sinz_amk,
  simp [xi_to_si, -map_with_index_cons],
  left,
  use [(lit₁ :: ls).nth_le i Hi, i, Hi],
  exact ⟨rfl, rfl⟩
end

theorem si_to_next_si_mem_sinz_amk (g : gensym V) {row col : nat} :
  row < (k + 1) → col < (length l) - 1 →  
  [Neg (matrix g (length l) row col), Pos (matrix g (length l) row (col + 1))] ∈ (sinz_amk k l g).1 :=
begin
  intros hrow hcol,
  cases l with lit₁ ls, { simp at hcol, contradiction },
  rw sinz_amk,
  simp [si_to_next_si, -map_with_index_cons],
  right, left,
  use [row, hrow, col, hcol],
  simp at hcol, simp [hcol]
end

theorem ternary_mem_sinz_amk (g : gensym V) {row col : nat} (hcol : col < length l) :
  row < k → 0 < col → 
  [(l.nth_le col hcol).flip, Neg (matrix g (length l) row (col - 1)), 
    Pos (matrix g (length l) (row + 1) col)] ∈ (sinz_amk k l g).1 :=
begin
  intros hr hc,
  cases l with lit₁ ls, { simp at hcol, contradiction },
  rw sinz_amk,
  simp [ternary, -map_with_index_cons],
  right, right,
  use [row, hr, [[((lit₁ :: ls).nth_le col hcol).flip, Neg (matrix g (ls.length + 1) row (col - 1)),
      Pos (matrix g (ls.length + 1) (row + 1) col )]]],
  split,
  { use [(lit₁ :: ls).nth_le col hcol, col, hcol], simp [hc] },
  { exact mem_singleton_self _ }
end

theorem neg_final_mem_sinz_amk (g : gensym V) (l : list (literal V)) :
  l ≠ [] → [Neg (matrix g (length l) k ((length l) - 1))] ∈ (sinz_amk k l g).1 :=
begin
  cases l with lit₁ ls,
  { intro hcon, contradiction },
  { intro hnil,
    rw sinz_amk,
    simp only [mem_append, mem_singleton, eq_self_iff_true, and_self, or_true] }
end

def row_and_col_from_var (S : sig_var_matrix V) (n : nat) (v : V) : nat → nat → (nat × nat)
| 0       0       := ⟨0, 0⟩
| 0       (c + 1) := if v = S 0 (c + 1) then ⟨0, c + 1⟩ else row_and_col_from_var 0 c
| (r + 1) 0       := if v = S (r + 1) 0 then ⟨r + 1, 0⟩ else row_and_col_from_var r (n - 1)
| (r + 1) (c + 1) := if v = S (r + 1) (c + 1) then ⟨r + 1, c + 1⟩ else row_and_col_from_var (r + 1) c 

def sinz_amk_tau (l : list (literal V)) (g : gensym V) (τ : assignment V) : assignment V :=
  aite (clause.vars l) τ 
    (λ v, let ⟨r, c⟩ := row_and_col_from_var (matrix g (length l)) (length l) v (k + 1) ((length l) - 1) in
       (alk (r + 1)).eval τ (l.take (c + 1)))

theorem hleper {a b c : nat} : a ≠ b → c + a ≠ c + b  :=
begin
  exact (add_ne_add_right c).mpr
end

theorem matrix_ne_of_ne_or_ne {g : gensym V} {n r₁ r₂ c₁ c₂ : nat} :
  c₁ < n → c₂ < n → r₁ ≠ r₂ ∨ c₁ ≠ c₂ → (matrix g n r₁ c₁) ≠ (matrix g n r₂ c₂) :=
begin
  rintros hc₁ hc₂ (h | h);
  unfold matrix; apply nth_ne_of_ne,
  { induction r₁ with r₁ ih generalizing r₂,
    { cases r₂,
      { exact absurd (eq.refl 0) h },
      { rw [zero_mul, zero_add],
        apply ne_of_lt,
        rw [succ_eq_add_one, add_mul, one_mul, add_comm (r₂ * n) n, add_assoc],
        exact lt_add_right _ _ _ hc₁ } },
    { cases r₂,
      { rw [zero_mul, zero_add],
        apply ne_of_gt,
        rw [succ_eq_add_one, add_mul, one_mul, add_comm (r₁ * n) n, add_assoc],
        exact lt_add_right _ _ _ hc₂ },
      { repeat { rw [succ_eq_add_one, add_mul, one_mul, add_comm _ n, add_assoc] },
        apply (add_ne_add_right n).mpr,
        exact ih ((add_ne_add_left 1).mp h) } } },
  { induction r₁ with r₁ ih generalizing r₂,
    { rw [zero_mul, zero_add],
      cases r₂,
      { rw [zero_mul, zero_add], exact h },
      { apply ne_of_lt,
        rw [succ_eq_add_one, add_mul, one_mul, add_comm (r₂ * n) n, add_assoc],
        exact lt_add_right _ _ _ hc₁ } },
    { cases r₂,
      { rw [zero_mul, zero_add],
        apply ne_of_gt,
        rw [succ_eq_add_one, add_mul, one_mul, add_comm (r₁ * n) n, add_assoc],
        exact lt_add_right _ _ _ hc₂ },
      { repeat { rw [succ_eq_add_one, add_mul, one_mul, add_comm _ n, add_assoc] },
        apply (add_ne_add_right n).mpr,
        exact ih } } }
end

theorem row_and_col_from_var_eq_row_and_col_of_lt (g : gensym V) {n row col r c : nat} :
  row ≤ r → col < n → c < n → (row = r → col ≤ c) → 
  row_and_col_from_var (matrix g n) n (matrix g n row col) r c = ⟨row, col⟩ :=
begin
  intros hrow hcol hc hcle,
  induction r with r ihr generalizing c,
  { simp at hrow, subst hrow, simp only [eq_self_iff_true, forall_true_left] at hcle,
    induction c with c ihc,
    { simp at hcle, subst hcle, rw row_and_col_from_var },
    { rcases eq_or_lt_of_le hcle with (rfl | h),
      { simp only [row_and_col_from_var, eq_self_iff_true, if_true] },
      { rw row_and_col_from_var,
        simp [matrix_ne_of_ne_or_ne (lt_trans h hc) hc (or.inr (ne_of_lt h))],
        exact ihc (lt_of_succ_lt hc) (le_of_lt_succ h) } } },
  { rcases eq_or_lt_of_le hrow with (rfl | hrow'),
    { induction c with c ihc,
      { simp at hcle, subst hcle,
        simp only [row_and_col_from_var, eq_self_iff_true, if_true] },
      { simp at hcle,
        rcases eq_or_lt_of_le hcle with (rfl | hclt),
        { simp only [row_and_col_from_var, eq_self_iff_true, if_true] },
        { rw row_and_col_from_var,
          simp [matrix_ne_of_ne_or_ne hcol hc (or.inr (ne_of_lt hclt))],
          exact ihc (lt_of_succ_lt hc) (λ _, le_of_lt_succ hclt) } } },
    { induction c with c ihc,
      { rw row_and_col_from_var,
        simp [matrix_ne_of_ne_or_ne hcol hc (or.inl (ne_of_lt hrow'))],
        apply ihr (le_of_lt_succ hrow'),
        { cases n,
          { exact absurd hc (nat.not_lt_zero 0) },
          { simp only [succ_sub_succ_eq_sub, tsub_zero], exact lt_succ_self n } },
        { cases n,
          { exact absurd hc (nat.not_lt_zero 0) },
          { intro _, simp only [succ_sub_succ_eq_sub, tsub_zero], exact le_of_lt_succ hcol } } },
      { rw row_and_col_from_var,
        simp [matrix_ne_of_ne_or_ne hcol hc (or.inl (ne_of_lt hrow'))],
        apply ihc (lt_of_succ_lt hc),
        intro hcon,
        exact absurd hcon (ne_of_lt hrow') } } }
end

theorem sinz_amk_eval_tt_under_sinz_amk_tau {k : nat} (hdis : disj l g) : ∀ (τ : assignment V),
  (amk k).eval τ l = tt → (sinz_amk k l g).1.eval (sinz_amk_tau k l g τ) = tt :=
begin
  intros τ heval,
  cases l with lit₁ ls,
  { simp [sinz_amk] },
  { rw sinz_amk,
    simp [-map_with_index_cons],
    split,
    { rw eval_tt_iff_forall_clause_eval_tt,
      intros c hc,
      simp [xi_to_si, -map_with_index_cons] at hc,
      rcases hc with ⟨_, i, ⟨hi, rfl⟩, rfl⟩,
      rw eval_tt_iff_exists_literal_eval_tt,
      cases hlit : ((lit₁ :: ls).nth_le i hi).eval τ,
      { use [((lit₁ :: ls).nth_le i hi).flip],
        split, { exact mem_cons_self _ _ },
        { simp only [eval_flip, bnot_eq_true_eq_eq_ff, sinz_amk_tau],
          rw aite_pos_lit (mem_vars_of_mem (nth_le_mem (lit₁ :: ls) i hi)),
          exact hlit } },
      { use [Pos (matrix g (ls.length + 1) 0 i)],
        simp [literal.eval],
        rw sinz_amk_tau,
        have := (matrix_not_mem_vars hdis 0 i),
        rw length at this |-,
        rw [aite_neg this, succ_sub_one],
        rw row_and_col_from_var_eq_row_and_col_of_lt g (zero_le (_ + 1)) hi (lt_succ_self _),
        { rw sinz_amk_tau._match_1,
          rw alo_eval_tt_iff_exists_eval_tt,
          use [((lit₁ :: ls).nth_le _ hi), nth_le_mem_take_of_lt hi (lt_succ_self _), hlit] },
        { exact (λ hcon, absurd hcon.symm (succ_ne_zero k)) } } },
    split,
    { rw eval_tt_iff_forall_clause_eval_tt,
      intros c hc,
      simp at hc,
      rcases hc with ⟨row, hrow, col, hcol, hc⟩,
      simp [si_to_next_si, hcol] at hc, subst hc,
      rw eval_tt_iff_exists_literal_eval_tt,
      cases halk : (alk (row + 1)).eval τ ((lit₁ :: ls).take (col + 1)),
      { use [Neg (matrix g (ls.length + 1) row col), mem_cons_self _ _],
        simp [literal.eval],
        rw sinz_amk_tau,
        have := (matrix_not_mem_vars hdis row col),
        rw length at this,
        rw aite_neg this, simp,
        rw row_and_col_from_var_eq_row_and_col_of_lt g (le_of_lt hrow) (lt_succ_of_lt hcol) (lt_succ_self _),
        { rw sinz_amk_tau._match_1, exact halk },
        { exact (λ hcon, absurd hcon (ne_of_lt hrow)) } },
      { use Pos (matrix g (ls.length + 1) row (col + 1)),
        simp [literal.eval],
        rw sinz_amk_tau,
        have := (matrix_not_mem_vars hdis row (col + 1)),
        rw length at this,
        rw aite_neg this, simp,
        rw row_and_col_from_var_eq_row_and_col_of_lt g (le_of_lt hrow) (succ_lt_succ hcol) (lt_succ_self _),
        { rw sinz_amk_tau._match_1,
          exact eval_take_succ_tt_of_eval_take_tt halk },
        { exact (λ _, succ_le_of_lt hcol) } } },
    split,
    { rw eval_tt_iff_forall_clause_eval_tt,
      intros c hc,
      simp [-map_with_index_cons] at hc,
      rcases hc with ⟨row, hrow, _, ⟨_, col, ⟨hcol, rfl⟩, rfl⟩, hc⟩,
      rw ternary at hc,
      cases col,
      { simp at hc, contradiction },
      { simp at hc, subst hc,
        rw eval_tt_iff_exists_literal_eval_tt,
        cases hlit : ((lit₁ :: ls).nth_le _ hcol).eval τ,
        { use [((lit₁ :: ls).nth_le _ hcol).flip, mem_cons_self _ _],
          simp [eval_flip, -nth_le],
          rw sinz_amk_tau,
          rw aite_pos_lit (mem_vars_of_mem (nth_le_mem (lit₁ :: ls) _ hcol)),
          exact hlit },
        { cases halk : (alk (row + 1)).eval τ ((lit₁ :: ls).take (col + 1)),
          { use [Neg (matrix g (ls.length + 1) row col)],
            simp [literal.eval],
            rw sinz_amk_tau,
            have := (matrix_not_mem_vars hdis row col),
            rw length at this,
            rw aite_neg this, simp,
            rw row_and_col_from_var_eq_row_and_col_of_lt g (le_of_lt (lt_succ_of_lt hrow)) (lt_of_succ_lt hcol) (lt_succ_self _),
            { rw sinz_amk_tau._match_1, exact halk },
            { rintro rfl, exact absurd (lt_of_succ_lt hrow) (not_lt.mpr (le_refl _)) } },
          { use [Pos (matrix g (ls.length + 1) (row + 1) (col + 1))],
            simp [literal.eval],
            rw sinz_amk_tau,
            have := (matrix_not_mem_vars hdis (row + 1) (col + 1)),
            rw length at this,
            rw aite_neg this, simp,
            rw row_and_col_from_var_eq_row_and_col_of_lt g 
              (succ_le_of_lt (lt_succ_of_lt hrow)) hcol (lt_succ_self _),
            { rw sinz_amk_tau._match_1, rw alk.eval_take_tail_pos hlit, exact halk },
            { exact (λ hcon, absurd hcon (ne_of_lt (succ_lt_succ hrow))) } } } } },
    { simp [literal.eval],
      rw sinz_amk_tau,
      have := (matrix_not_mem_vars hdis k ls.length),
      rw length at this,
      rw aite_neg this, simp,
      rw row_and_col_from_var_eq_row_and_col_of_lt g (le_succ k) (lt_succ_self _) (lt_succ_self _),
      { rw sinz_amk_tau._match_1,
        simp,
        rw [amk_eval_eq_alk_succ_eval, bnot_eq_true_eq_eq_ff] at heval, exact heval },
      { exact (λ _, le_refl _) } } }
end

-- TODO: verify if need hdis later...
theorem signal_semantics {k : nat} :
  (sinz_amk k l g).1.eval τ = tt → ∀ ⦃row col : nat⦄, row < k + 1 → col < length l → 
  τ (matrix g (length l) row col) = ff → (amk row).eval τ (l.take (col + 1)) = tt :=
begin
  intros heval row col hrow hcol htau,
  rw eval_tt_iff_forall_clause_eval_tt at heval,
  induction row with row ihr generalizing col,
  { induction col with col ihc,
    { have := heval _ (xi_to_si_mem_sinz_amk k g hcol),
      simp [eval_flip, literal.eval, htau] at this,
      cases l with lit₁ ls,
      { simp at hcol, contradiction },
      { rw nth_le at this,
        rw [take, take, amk.eval_cons_neg this, amk.eval_nil] } },
    { cases hlit : (l.nth_le _ hcol).eval τ,
      { cases htau' : τ (matrix g l.length 0 col),
        { rw amk.eval_take_tail_neg hlit,
          exact ihc (lt_of_succ_lt hcol) htau' },
        { cases l with lit₁ ls,
          { simp at hcol, contradiction },
          { simp at hcol,
            have : col < (lit₁ :: ls).length - 1,
            { simp only [length, add_succ_sub_one, add_zero], exact succ_lt_succ_iff.mp hcol },
            have := heval _ (si_to_next_si_mem_sinz_amk k g hrow this),
            rw length at htau htau',
            simp [literal.eval, htau', htau] at this, contradiction } } },
      { have := heval _ (xi_to_si_mem_sinz_amk k g hcol),
        simp [literal.eval, eval_flip, hlit, htau] at this, contradiction } } },
  { induction col with col ihc,
    { cases l with lit₁ ls; simp },
    { cases htau' : τ (matrix g l.length row col),
      { have := ihr (lt_of_succ_lt hrow) (lt_of_succ_lt hcol) htau',
        cases hlit : (l.nth_le _ hcol).eval τ,
        { rw amk.eval_take_tail_neg hlit,
          exact eval_tt_of_le_of_eval_tt (le_succ row) this },
        { rw amk.eval_take_tail_pos hlit,
          exact this } },
      { cases hlit : (l.nth_le _ hcol).eval τ,
        { cases htau'' : τ (matrix g l.length (row + 1) col),
          { rw amk.eval_take_tail_neg hlit,
            exact ihc (lt_of_succ_lt hcol) htau'' },
          { cases l with lit₁ ls,
            { simp at hcol, contradiction },
            { have : col < (lit₁ :: ls).length - 1,
              { simp only [length, add_succ_sub_one, add_zero], exact succ_lt_succ_iff.mp hcol },
              have := heval _ (si_to_next_si_mem_sinz_amk k g hrow this),
              rw length at htau htau'',
              simp [literal.eval, htau, htau''] at this, contradiction } } },
        { have := heval _ (ternary_mem_sinz_amk k g hcol (succ_lt_succ_iff.mp hrow) (ne_zero.pos (succ col))),
          simp [literal.eval, eval_flip, hlit, htau', htau] at this,
          contradiction } } } }
end

theorem sinz_amk_formula_encodes_amk : is_correct (amk k) (sinz_amk k : enc_fn V) :=
begin
  intros l g hdis τ,
  split,
  { intro hamk,
    use [sinz_amk_tau k l g τ, sinz_amk_eval_tt_under_sinz_amk_tau hdis τ hamk],
    intros v hv,
    rw [sinz_amk_tau, aite_pos hv] },
  { rintros ⟨σ, hs, hagree_on⟩,
    have hs_copy := hs,
    rw eval_tt_iff_forall_clause_eval_tt at hs,
    cases l with lit₁ ls,
    { simp },
    { have hfinal := hs _ (neg_final_mem_sinz_amk k g (lit₁ :: ls) (ne_nil_of_mem (mem_cons_self _ _))),
      simp [literal.eval] at hfinal,
      have : ls.length < (lit₁ :: ls).length,
      { rw length, exact lt_succ_self _ },
      have := signal_semantics hs_copy (lt_succ_self k) this hfinal,
      simp only [take, take_length] at this,
      rw amk.eval_eq_of_agree_on k hagree_on,
      exact this } }
end

theorem helper {a b : nat} : a * b + b = (a + 1) * b :=
begin
  exact (add_one_mul a b).symm,
end

theorem sinz_amk_is_wb : is_wb (sinz_amk k : enc_fn V) :=
begin
  intros l g hdis,
  cases l with lit₁ ls,
  { simp [sinz_amk] },
  { split,
    { simp [sinz_amk],
      exact nfresh_stock_subset g ((k + 1) * (length ls + 1)) },
    { intros v hv,
      rcases sinz_amk_mem_vars k hv with (h | h),
      { exact set.mem_union_left _ h },
      { apply set.mem_union_right,
        split,
        { exact nfresh_mem_stock h },
        { rw sinz_amk,
          unfold prod.snd,
          exact nth_not_mem_nfresh_stock h } } } }
end

theorem sinz_amk_encodes_amk : encodes (amk k) (sinz_amk k : enc_fn V) :=
⟨sinz_amk_formula_encodes_amk k, sinz_amk_is_wb k⟩

end sinz_amk