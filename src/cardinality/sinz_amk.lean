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
          {τ : assignment V} (hdis : disjoint g.stock (clause.vars l))

/-
-- TODO: last vs ilast vs last' vs nth
def sinz_amk_rec (k : nat) : encoding V
| []                   g := ⟨[], g⟩
| [lit₁]               g :=   -- x_n → s_{n, 1} and ¬ s_{n, k + 1}
    ⟨[[lit₁.flip, Pos (g.nfresh (k + 1)).1.head], 
      [Neg (g.nfresh (k + 1)).1.ilast]], (g.nfresh (k + 1)).2⟩ 
| (lit₁ :: lit₂ :: ls) g :=
    ⟨([[lit₁.flip, Pos (g.nfresh (k + 1)).1.head]] ++
      (zip_with (λ y z, [Neg y, Pos z]) (g.nfresh (k + 1)).1 ((g.nfresh (k + 1)).2.nfresh (k + 1)).1) ++
      (zip_with (λ y z, [lit₁.flip, Neg y, Pos z]) (g.nfresh (k + 1)).1.init ((g.nfresh (k + 1)).2.nfresh (k + 1)).1.tail) ++
      (sinz_amk_rec (lit₂ :: ls) (g.nfresh (k + 1)).2).1),
      (sinz_amk_rec (lit₂ :: ls) (g.nfresh (k + 1)).2).2⟩  

def sinz_amk_rec' (k : nat) : encoding V
| []                   g := ⟨[], g⟩
| [lit₁]               g :=   -- x_n → s_{n, 1} and ¬ s_{n, k + 1}
    let ⟨ys, g₁⟩ := g.nfresh (k + 1) in
    ⟨[[lit₁.flip, Pos ys.head], [Neg ys.ilast]], g₁⟩ 
| (lit₁ :: lit₂ :: ls) g :=
    let ⟨ys, g₁⟩ := g.nfresh (k + 1) in
    let ⟨zs, _⟩ := g₁.nfresh (k + 1) in  
    let signal_clauses := zip_with (λ y z, [Neg y, Pos z]) ys zs in
    let ternary_clauses := zip_with (λ y z, [lit₁.flip, Neg y, Pos z]) ys.init zs.tail in 
    let ⟨F_rec, g₂⟩ := sinz_amk_rec' (lit₂ :: ls) g₁ in
    ⟨([[lit₁.flip, Pos ys.head]] ++ signal_clauses ++ ternary_clauses) ++ F_rec, g₂⟩

theorem sinz_amk_rec_eq_sinz_amk_rec' (k : nat) : ∀ (l : list (literal V)) (g : gensym V),
  sinz_amk_rec k l g = sinz_amk_rec' k l g :=
begin
  intros l g,
  induction l with lit₁ ls ih generalizing g,
  { refl },
  { cases ls with lit₂ ls,
    { refl },
    { rw [sinz_amk_rec, sinz_amk_rec'],
      simp only,
      rw [prod.ext_self (g.nfresh (k + 1)), sinz_amk_rec'._match_4,
          prod.ext_self (sinz_amk_rec' k (lit₂ :: ls) (g.nfresh (k + 1)).2),
          prod.ext_self ((g.nfresh (k + 1)).2.nfresh (k + 1)),
          sinz_amk_rec'._match_3],
      simp only,
      rw [sinz_amk_rec'._match_2, ← ih] } }
end

theorem sinz_amk_rec_is_wb : is_wb (sinz_amk_rec k : encoding V) :=
begin
  intros l g hdis,
  induction l with lit₁ ls ih generalizing g,
  { simp [sinz_amk_rec] },
  { cases ls with lit₂ ls,
    { rw sinz_amk_rec, split,
      { unfold prod.snd, exact nfresh_stock_subset _ _ },
      { intros v hv,
        unfold prod.fst at hv,
        simp [flip_var_eq, var] at hv,
        rcases hv with (rfl | rfl | rfl),
        { apply set.mem_union_left,
          rw clause.vars_singleton,
          simp only [finset.coe_singleton, set.mem_singleton] },
        { sorry },
        { sorry } } },
    { sorry } }
end
-/

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

def sinz_amk (k : nat) : encoding V
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
  assignment.ite (clause.vars l) τ 
    (λ v, let ⟨r, c⟩ := row_and_col_from_var (matrix g (length l)) (length l) v (k + 1) ((length l) - 1) in
       (alk (r + 1)).eval τ (l.take (c + 1)))

/-
theorem rc_helper {r r' c c' : nat} (g : gensym V) {l : list (literal V)} :
  r ≤ r' → c < length l → c' < length l → 
  (r = r' → c ≤ c') → 
-/
theorem matrix_ne_of_ne_or_ne {g : gensym V} {n r₁ r₂ c₁ c₂ : nat} :
  c₁ < n → c₂ < n → r₁ ≠ r₂ ∨ c₁ ≠ c₂ → (matrix g n r₁ c₁) ≠ (matrix g n r₂ c₂) :=
begin
  rintros hc₁ hc₂ (h | h);
  unfold matrix; apply nth_ne_of_ne,
  { sorry },
  { sorry }
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
          rw ite_pos_lit (mem_vars_of_mem (nth_le_mem (lit₁ :: ls) i hi)),
          exact hlit } },
      { use [Pos (matrix g (ls.length + 1) 0 i)],
        simp [literal.eval],
        rw sinz_amk_tau,
        have := (matrix_not_mem_vars hdis 0 i),
        rw length at this |-,
        rw [ite_neg this, succ_sub_one],
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
        rw ite_neg this, simp,
        rw row_and_col_from_var_eq_row_and_col_of_lt g (le_of_lt hrow) (lt_succ_of_lt hcol) (lt_succ_self _),
        { rw sinz_amk_tau._match_1, exact halk },
        { exact (λ hcon, absurd hcon (ne_of_lt hrow)) } },
      { use Pos (matrix g (ls.length + 1) row (col + 1)),
        simp [literal.eval],
        rw sinz_amk_tau,
        have := (matrix_not_mem_vars hdis row (col + 1)),
        rw length at this,
        rw ite_neg this, simp,
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
          rw ite_pos_lit (mem_vars_of_mem (nth_le_mem (lit₁ :: ls) _ hcol)),
          exact hlit },
        { cases halk : (alk (row + 1)).eval τ ((lit₁ :: ls).take (col + 1)),
          { use [Neg (matrix g (ls.length + 1) row col)],
            simp [literal.eval],
            rw sinz_amk_tau,
            have := (matrix_not_mem_vars hdis row col),
            rw length at this,
            rw ite_neg this, simp,
            rw row_and_col_from_var_eq_row_and_col_of_lt g (le_of_lt (lt_succ_of_lt hrow)) (lt_of_succ_lt hcol) (lt_succ_self _),
            { rw sinz_amk_tau._match_1, exact halk },
            { rintro rfl, exact absurd (lt_of_succ_lt hrow) (not_lt.mpr (le_refl _)) } },
          { use [Pos (matrix g (ls.length + 1) (row + 1) (col + 1))],
            simp [literal.eval],
            rw sinz_amk_tau,
            have := (matrix_not_mem_vars hdis (row + 1) (col + 1)),
            rw length at this,
            rw ite_neg this, simp,
            rw row_and_col_from_var_eq_row_and_col_of_lt g 
              (succ_le_of_lt (lt_succ_of_lt hrow)) hcol (lt_succ_self _),
            { rw sinz_amk_tau._match_1, rw alk.eval_take_tail_pos hlit, exact halk },
            { exact (λ hcon, absurd hcon (ne_of_lt (succ_lt_succ hrow))) } } } } },
    { simp [literal.eval],
      rw sinz_amk_tau,
      have := (matrix_not_mem_vars hdis k ls.length),
      rw length at this,
      rw ite_neg this, simp,
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

theorem sinz_amk_formula_encodes_amk : encodes_base (amk k) (sinz_amk k : encoding V) :=
begin
  intros l g hdis τ,
  split,
  { intro hamk,
    use [sinz_amk_tau k l g τ, sinz_amk_eval_tt_under_sinz_amk_tau hdis τ hamk],
    intros v hv,
    rw [sinz_amk_tau, ite_pos hv] },
  { rintros ⟨σ, hs, heqod⟩,
    have hs_copy := hs,
    rw eval_tt_iff_forall_clause_eval_tt at hs,
    cases l with lit₁ ls,
    { simp },
    { have hfinal := hs _ (neg_final_mem_sinz_amk k g (lit₁ :: ls) (ne_nil_of_mem (mem_cons_self _ _))),
      simp [literal.eval] at hfinal,
      have : ls.length < (lit₁ :: ls).length,
      { rw length, exact lt_succ_self _ },
      have := signal_semantics hdis hs_copy (lt_succ_self k) this hfinal,
      simp only [take, take_length] at this,
      rw amk.eval_eq_of_eqod k heqod,
      exact this } }
end


theorem sinz_amk_is_wb : is_wb (sinz_amk k : encoding V) :=
begin
  sorry
end

theorem sinz_amk_encodes_amk : encodes (amk k) (sinz_amk k : encoding V) :=
⟨sinz_amk_formula_encodes_amk k, sinz_amk_is_wb k⟩

end sinz_amk