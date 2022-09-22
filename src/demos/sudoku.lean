/-

A demonstration of the at-most-one encodings for Sudoku

-/

import cnf.literal
import cnf.assignment
import cnf.cnf
import cnf.encoding

import cardinality.direct_amo
import cardinality.sinz_amo
import cardinality.distinct
import cardinality.alk
import cardinality.amk

import data.nat.basic
import data.list.basic
import data.list.range

open nat
open list
open function
open literal
open encoding
open clause cnf
open assignment
open alk amk distinct
open direct_amo
open sinz_amo

def square_var (row col num : nat) : nat := 
  (row * 81) + (col * 9) + num

def square_lit (row col num : nat) : literal nat := Pos (square_var row col num)

def grid_coords (gr gc : nat) : list (nat × nat) :=
  let row := gr * 3 in
  let col := gc * 3 in
  [(row, col), (row, col + 1), (row, col + 2),
   (row + 1, col), (row + 1, col + 1), (row + 1, col + 2),
   (row + 2, col), (row + 2, col + 1), (row + 2, col + 2)]

def square_lits (row col : nat) := (range 9).map (λ num, square_lit row col num)
def row_lits (row num : nat) := (range 9).map (λ col, square_lit row col num)
def col_lits (col num : nat) := (range 9).map (λ row, square_lit row col num)
--def grid_lits (gr gc num : nat) := (grid_coords gr gc).map
--  (λ coord, square_lit coord.1 coord.2 num)

def square_valid (τ : assignment nat) (row col : nat) :=
  (∀ {num num'}, num < 9 → num' < 9 → num ≠ num' → 
    τ (square_var row col num) = tt → τ (square_var row col num') = ff) ∧
  (∃ {num}, num < 9 ∧ τ (square_var row col num) = tt)

def row_valid (τ : assignment nat) (row num : nat) :=
  ∀ {col col'}, col < 9 → col' < 9 → col ≠ col' → 
    τ (square_var row col num) = tt → τ (square_var row col' num) = ff

def col_valid (τ : assignment nat) (col num : nat) :=
  ∀ {row row'}, row < 9 → row' < 9 → row ≠ row' → 
    τ (square_var row col num) = tt → τ (square_var row' col num) = ff

--def subgrid_valid (τ : assignment nat) (rs cs : nat) :=
--  ∀ {ro co ro' co'}, ro < 3 → co < 3 → ro' < 3 → co' < 3 → ro ≠ ro' ∨ co ≠ co' → 
--    square τ (rs + ro) (cs + co) ≠ square τ (rs + ro') (cs + co')

def is_valid_sudoku (τ : assignment nat) :=
  (∀ {row col}, row < 9 → col < 9 → square_valid τ row col) ∧ 
  (∀ {row num}, row < 9 → num < 9 → row_valid τ row num) ∧
  (∀ {col num}, col < 9 → num < 9 → col_valid τ col num)
  --subgrid_valid τ 0 0 ∧ subgrid_valid τ 3 0 ∧ subgrid_valid τ 6 0 ∧
  --subgrid_valid τ 0 3 ∧ subgrid_valid τ 3 3 ∧ subgrid_valid τ 6 3 ∧
  --subgrid_valid τ 0 6 ∧ subgrid_valid τ 3 6 ∧ subgrid_valid τ 6 6

--def sudoku_encoding (set_squares : list (nat × nat × nat)) : cnf nat :=
def sudoku_encoding : cnf nat :=
  -- Every square has at least one number
  join ((range 9).map (λ row, ((range 9).map (λ col, square_lits row col)))) ++
  -- Every square has at most one number
  join ((range 9).map (λ row, join ((range 9).map (λ col, direct_amo (square_lits row col))))) ++
  -- Every row has at most one instance of each number 1 - 9
  join ((range 9).map (λ row, join ((range 9).map (λ num, direct_amo (row_lits row num))))) ++
  -- Every col has at most one instance of each number 1 - 9
  join ((range 9).map (λ col, join ((range 9).map (λ num, direct_amo (col_lits col num))))) 

  -- Every subgrid has at most one instance of each number 1 - 9
  --join ((range 3).map (λ gr, join ((range 3).map (λ gc,
  --  join ((range 9).map (λ num, direct_amo (grid_lits gr gc num))))))) ++

  -- For each (row, col, num) that is provided, add a unit clause setting that number
  --set_squares.map (λ triple, [square_lit triple.1 triple.2.1 triple.2.2])

--#eval sudoku_encoding []
--#eval length (sudoku_encoding [])



lemma lemma1 (row col : nat) : length (square_lits row col) = 9 := rfl
lemma lemma2 (row col : nat) : length (square_lits row col) ≥ 2 := by simp [square_lits]

lemma lemma3' (r c : nat) {i} (Hi : i < length (square_lits r c)) :
  (square_lits r c).nth_le i Hi = Pos (square_var r c i) :=
by simp [square_lits, square_lit]

lemma lemma3 (τ : assignment nat) (r c : nat) {i} (Hi : i < length (square_lits r c)) : 
  ((square_lits r c).nth_le i Hi).eval τ = τ (square_var r c i) :=
by simp [lemma3' r c, literal.eval]

lemma lemma4 (row num : nat) : length (row_lits row num) = 9 := rfl
lemma lemma5 (row num : nat) : length (row_lits row num) ≥ 2 := by simp [row_lits]

lemma lemma6' (row num : nat) {i} (Hi : i < length (row_lits row num)) :
  (row_lits row num).nth_le i Hi = Pos (square_var row i num) :=
by simp [row_lits, square_lit]

lemma lemma6 (τ : assignment nat) (row num : nat) {i} (Hi : i < length (row_lits row num)) : 
  ((row_lits row num).nth_le i Hi).eval τ = τ (square_var row i num) :=
by simp [lemma6' row num, literal.eval]

lemma lemma7 (col num : nat) : length (col_lits col num) = 9 := rfl
lemma lemma8 (col num : nat) : length (col_lits col num) ≥ 2 := by simp [col_lits]

lemma lemma9' (col num : nat) {i} (Hi : i < length (col_lits col num)) :
  (col_lits col num).nth_le i Hi = Pos (square_var i col num) :=
by simp [col_lits, square_lit]

lemma lemma9 (τ : assignment nat) (col num : nat) {i} (Hi : i < length (col_lits col num)) :
  ((col_lits col num).nth_le i Hi).eval τ = τ (square_var i col num) :=
by simp [lemma9' col num, literal.eval]

lemma lemma10 : range 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] := rfl

lemma lemma11 (r c) {num : nat} (hnum : num < 9) : 
  (square_lits r c).nth_le num hnum = Pos (square_var r c num) :=
by simp [square_lits, square_lit]

lemma lemma12 (r num) {c : nat} (hc : c < 9) : 
  (row_lits r num).nth_le c hc = Pos (square_var r c num) :=
by simp [row_lits, square_lit]

lemma lemma13 (c num) {r : nat} (hr : r < 9) : 
  (col_lits c num).nth_le r hr = Pos (square_var r c num) :=
by simp [col_lits, square_lit]

lemma converter {τ : assignment nat} {r c : nat} (hr : r < 9) (hc : c < 9) : 
  (∃ (cl : clause nat), cl ∈ direct_amo (square_lits r c) ∧ cl.eval τ = ff) → 
  (∃ (cl : clause nat), (∃ (a : nat), a < 9 ∧ ∃ (b : nat), b < 9 ∧ cl ∈ direct_amo (square_lits a b)) ∧ cl.eval τ = ff) :=
by { rintros ⟨cl, hcl, heval⟩, use [cl, r, hr, c, hc, hcl, heval] }

lemma converter₂ {τ : assignment nat} {r c : nat} (hr : r < 9) (hc : c < 9) :
  (∃ (cl : clause nat), square_lits r c = cl ∧ cl.eval τ = ff) →
  (∃ (cl : clause ℕ), (∃ (a : ℕ), a < 9 ∧ ∃ (a_1 : ℕ), a_1 < 9 ∧ square_lits a a_1 = cl) ∧ cl.eval τ = ff) :=
by { rintros ⟨cl, hcl, heval⟩, use [cl, r, hr, c, hc, hcl, heval] }

lemma converter₃ {τ : assignment nat} {r num : nat} (hr : r < 9) (hnum : num < 9) : 
  (∃ (cl : clause nat), cl ∈ direct_amo (row_lits r num) ∧ cl.eval τ = ff) → 
  (∃ (cl : clause nat), (∃ (a : nat), a < 9 ∧ ∃ (b : nat), b < 9 ∧ cl ∈ direct_amo (row_lits a b)) ∧ cl.eval τ = ff) :=
by { rintros ⟨cl, hcl, heval⟩, use [cl, r, hr, num, hnum, hcl, heval] }

lemma converter₄ {τ : assignment nat} {c num : nat} (hc : c < 9) (hnum : num < 9) : 
  (∃ (cl : clause nat), cl ∈ direct_amo (col_lits c num) ∧ cl.eval τ = ff) → 
  (∃ (cl : clause nat), (∃ (a : nat), a < 9 ∧ ∃ (b : nat), b < 9 ∧ cl ∈ direct_amo (col_lits a b)) ∧ cl.eval τ = ff) :=
by { rintros ⟨cl, hcl, heval⟩, use [cl, c, hc, num, hnum, hcl, heval] }

theorem direct_amo_eq_amo {τ : assignment nat} {l : list (literal nat)} : 
  (direct_amo l).eval τ = amk.eval 1 τ l := sorry

theorem encodes_sudoku {τ : assignment nat} :
  is_valid_sudoku τ ↔ sudoku_encoding.eval τ = tt :=
begin
  split,
  { rintros ⟨hsq, hrow, hcol⟩,
    rw eval_tt_iff_forall_clause_eval_tt,
    intros cl hcl,
    simp [sudoku_encoding] at hcl,
    rcases hcl with (⟨r, hr, c, hc, h⟩ | ⟨r, hr, c, hc, h⟩ | 
      ⟨r, hr, num, hnum, h⟩ | ⟨c, hc, num, hnum, h⟩),
    { subst h,
      simp [square_lits, eval_tt_iff_exists_literal_eval_tt],
      rcases (hsq hr hc).2 with ⟨num, hlt, hnum⟩,
      use [num, hlt],
      simp [square_lit, literal.eval, hnum] },
    { rcases exists_double_flip_eq_of_mem (lemma2 r c) h with ⟨lit₁, lit₂, rfl⟩,
      rcases distinct_iff_mem.mpr h with ⟨i, j, hi, hj, hij, rfl, rfl⟩,
      rw eval_tt_iff_exists_literal_eval_tt,
      cases heval : ((square_lits r c).nth_le i hi).eval τ,
      { use ((square_lits r c).nth_le i hi).flip,
        simp [eval_flip, heval] },
      { use ((square_lits r c).nth_le j hj).flip,
        simp [eval_flip],
        simp [lemma3] at heval |-,
        rw lemma1 at hi hj,
        exact (hsq hr hc).1 hi hj (ne_of_lt hij) heval } },
    { rcases exists_double_flip_eq_of_mem (lemma5 r num) h with ⟨lit₁, lit₂, rfl⟩,
      rcases distinct_iff_mem.mpr h with ⟨i, j, hi, hj, hij, rfl, rfl⟩,
      rw eval_tt_iff_exists_literal_eval_tt,
      cases heval : ((row_lits r num).nth_le i hi).eval τ,
      { use ((row_lits r num).nth_le i hi).flip,
        simp [eval_flip, heval] },
      { use ((row_lits r num).nth_le j hj).flip,
        simp [eval_flip],
        simp [lemma6] at heval |-,
        rw lemma4 at hi hj,
        exact hrow hr hnum hi hj (ne_of_lt hij) heval } },
    { rcases exists_double_flip_eq_of_mem (lemma8 c num) h with ⟨lit₁, lit₂, rfl⟩,
      rcases distinct_iff_mem.mpr h with ⟨i, j, hi, hj, hij, rfl, rfl⟩,
      rw eval_tt_iff_exists_literal_eval_tt,
      cases heval : ((col_lits c num).nth_le i hi).eval τ,
      { use ((col_lits c num).nth_le i hi).flip,
        simp [eval_flip, heval] },
      { use ((col_lits c num).nth_le j hj).flip,
        simp [eval_flip],
        simp [lemma9] at heval |-,
        rw lemma7 at hi hj,
        exact hcol hc hnum hi hj (ne_of_lt hij) heval } } },
  { contrapose,
    intro his,
    rw [is_valid_sudoku] at his,
    simp only [not_and_distrib, not_forall] at his,
    simp only [sudoku_encoding, cnf.eval_append, append_assoc, band_eq_true_eq_eq_tt_and_eq_tt,  
      not_and_distrib, eq_ff_eq_not_eq_tt],
    rcases his with (⟨r, c, hr, hc, hsq⟩ | ⟨r, num, hr, hnum, hsq⟩ | 
      ⟨c, num, hc, hnum, hsq⟩),
    { rw [square_valid, not_and_distrib] at hsq,
      simp at hsq,
      rcases hsq with (⟨num, hnum, num', hnum', hne, hsq₁, hsq₂⟩ | hsq),
      { right, left,
        simp [eval_ff_iff_exists_clause_eval_ff],
        apply converter hr hc,
        have := eval_ff_iff_exists_clause_eval_ff.mp,
        simp only [exists_prop] at this,
        apply this,
        rw direct_amo_eq_amo,
        by_contradiction,
        simp at h,
        rw [amo_eval_tt_iff_distinct_eval_ff_of_eval_tt] at h,
        rcases ne.lt_or_lt hne with (hlt | hlt),
        { have : distinct (Pos (square_var r c num)) (Pos (square_var r c num')) (square_lits r c) :=  
            ⟨num, num', hnum, hnum', hlt, lemma11 r c hnum, lemma11 r c hnum'⟩,
          have := h this,
          simp [literal.eval] at this,
          rw this hsq₁ at hsq₂,
          contradiction },
        { have : distinct (Pos (square_var r c num')) (Pos (square_var r c num)) (square_lits r c) :=
            ⟨num', num, hnum', hnum, hlt, lemma11 r c hnum', lemma11 r c hnum⟩,
          have := h this,
          simp [literal.eval] at this,
          rw this hsq₂ at hsq₁,
          contradiction },
        exact classical.dec_eq ℕ,
        exact {default := r} },
      { left,
        simp [eval_ff_iff_exists_clause_eval_ff],
        apply converter₂ hr hc,
        simp [eval_ff_iff_forall_literal_eval_ff],
        intros l hl,
        simp [square_lits] at hl,
        rcases hl with ⟨num, hnum, rfl⟩,
        simp [literal.eval, square_lit],
        exact hsq _ hnum } },
    { right, right, left,
      simp [row_valid] at hsq,
      rcases hsq with ⟨c, hc, c', hc', hne, ht, ht'⟩,
      simp [eval_ff_iff_exists_clause_eval_ff],
      apply converter₃ hr hnum,
      have := eval_ff_iff_exists_clause_eval_ff.mp,
      simp only [exists_prop] at this,
      apply this,
      rw direct_amo_eq_amo,
      by_contradiction,
      simp at h,
      rw [amo_eval_tt_iff_distinct_eval_ff_of_eval_tt] at h,
      rcases ne.lt_or_lt hne with (hlt | hlt),
      { have : distinct (Pos (square_var r c num)) (Pos (square_var r c' num)) (row_lits r num) :=
          ⟨c, c', hc, hc', hlt, lemma12 r num hc, lemma12 r num hc'⟩,
        have := h this,
        simp [literal.eval] at this,
        rw this ht at ht',
        contradiction },
      { have : distinct (Pos (square_var r c' num)) (Pos (square_var r c num)) (row_lits r num) :=
          ⟨c', c, hc', hc, hlt, lemma12 r num hc', lemma12 r num hc⟩,
        have := h this,
        simp [literal.eval] at this,
        rw this ht' at ht,
        contradiction },
      exact classical.dec_eq ℕ,
      exact {default := r} },
    { right, right, right,
      simp [col_valid] at hsq,
      rcases hsq with ⟨r, hr, r', hr', hne, ht, ht'⟩,
      simp [eval_ff_iff_exists_clause_eval_ff],
      apply converter₄ hc hnum,
      have := eval_ff_iff_exists_clause_eval_ff.mp,
      simp only [exists_prop] at this,
      apply this,
      rw direct_amo_eq_amo,
      by_contradiction,
      simp at h,
      rw [amo_eval_tt_iff_distinct_eval_ff_of_eval_tt] at h,
      rcases ne.lt_or_lt hne with (hlt | hlt),
      { have : distinct (Pos (square_var r c num)) (Pos (square_var r' c num)) (col_lits c num) :=
          ⟨r, r', hr, hr', hlt, lemma13 c num hr, lemma13 c num hr'⟩,
        have := h this,
        simp [literal.eval] at this,
        rw this ht at ht',
        contradiction },
      { have : distinct (Pos (square_var r' c num)) (Pos (square_var r c num)) (col_lits c num) :=
          ⟨r', r, hr', hr, hlt, lemma13 c num hr', lemma13 c num hr⟩,
        have := h this,
        simp [literal.eval] at this,
        rw this ht' at ht,
        contradiction },
      exact classical.dec_eq ℕ,
      exact {default := r} } }
end