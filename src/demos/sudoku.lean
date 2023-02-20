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

open nat fin list function
open literal encoding constraint clause cnf assignment
open alk amk distinct
open direct_amo sinz_amo

--def sudoku_list (V : Type*) (n : nat) := Π (l : list (literal V)), l.length = n^6

variables {α V : Type*} [decidable_eq V] [inhabited V] {n : nat} (srow scol : fin n) (row col num : fin (n^2))

def grid_coords : list (fin (n^2) × fin (n^2)) :=
  join ((fin.range n).map (λ ro, (fin.range n).map (λ co, 
    (fin.square_add srow ro, fin.square_add scol co))))

def cell_idx : nat := (row.val * (n^4)) + (col.val * (n^2)) + num.val

theorem cell_idx_is_fin (n : nat) : ∀ (row col num : fin (n^2)),
  cell_idx row col num < n^6 :=
begin
  sorry
end

def is_cell_lit := λ idx, idx ∈ (fin.range (n^2)).map (λ num, cell_idx row col num)
def is_row_lit := λ idx, idx ∈ (fin.range (n^2)).map (λ col, cell_idx row col num)
def is_col_lit := λ idx, idx ∈ (fin.range (n^2)).map (λ row, cell_idx row col num)
def is_square_lit := λ idx, idx ∈ (grid_coords srow scol).map (λ ⟨row, col⟩, cell_idx row col num)

instance is_cell_lit_is_decidable : decidable_pred (is_cell_lit row col) :=
begin
  unfold is_cell_lit, intro idx, simp only,
  exact list.decidable_mem idx (map (cell_idx row col) (range (n^2)))
end

instance is_row_lit_is_decidable : decidable_pred (is_row_lit col num) :=
begin
  unfold is_row_lit, intro idx, simp only,
  exact list.decidable_mem idx (map (λ (col_1 : fin (n^2)), cell_idx col col_1 num) (range (n ^ 2)))
end

instance is_col_lit_is_decidable : decidable_pred (is_col_lit row num) :=
begin
  unfold is_col_lit, intro idx, simp only,
  exact list.decidable_mem idx (map (λ (row_1 : fin (n^2)), cell_idx row_1 row num) (range (n ^ 2)))
end

instance is_square_lit_is_decidable (srow scol : fin n) : decidable_pred (is_square_lit srow scol num) :=
begin
  unfold is_square_lit, intro idx, simp only,
  exact list.decidable_mem idx (map (is_square_lit._match_1 num) (grid_coords srow scol))
end

@[inline, reducible] def validity_base (p : nat → Prop) [decidable_pred p] : constraint :=
  (constraint.append (amk 1) (alk 1)) ∘ (filter_by_idx p)

@[inline, reducible] def weak_validity_base (p : nat → Prop) [decidable_pred p] := (amk 1) ∘ (filter_by_idx p)

def is_cell_valid := validity_base (is_cell_lit row col)
def is_row_valid' := validity_base (is_row_lit col num)
def is_col_valid' := validity_base (is_col_lit row num)
def is_square_valid' := validity_base (is_square_lit srow scol num)

def is_row_valid := weak_validity_base (is_row_lit col num)
def is_col_valid := weak_validity_base (is_col_lit row num)
def is_square_valid := weak_validity_base (is_square_lit srow scol num)

def is_valid_sudoku (n : nat) : constraint :=
let L := cp (n^2) (n^2) in
constraint.len_check (
  (fold (L.map (λ ⟨row, col⟩, is_cell_valid row col))) ++
  (fold (L.map (λ ⟨col, num⟩, is_row_valid col num))) ++
  (fold (L.map (λ ⟨row, num⟩, is_col_valid row num))) ++
  (fold ((list.zip (cp n n) (fin.range (n^2))).map (λ 
    ⟨⟨srow, scol⟩, num⟩, is_square_valid srow scol num))))
(λ len, len = n^6)

def is_valid_sudoku' (n : nat) : constraint :=
let L := cp (n^2) (n^2) in
constraint.len_check (
  (fold (L.map (λ ⟨row, col⟩, is_cell_valid row col))) ++
  (fold (L.map (λ ⟨col, num⟩, is_row_valid' col num))) ++
  (fold (L.map (λ ⟨row, num⟩, is_col_valid' row num))) ++
  (fold ((list.zip (cp n n) (fin.range (n^2))).map (λ 
    ⟨⟨srow, scol⟩, num⟩, is_square_valid' srow scol num))))
(λ len, len = n^6)

theorem is_valid_implies_is_valid (n : nat) : ∀ (l : list bool),
  is_valid_sudoku n l = is_valid_sudoku' n l :=
begin
  sorry
end

/-
def sq_lits  := (fin.range (n^2)).map (λ num, sql L hL row col num)

def Sq_lits : Π {α : Type*}, list α → list α := (λ {α : Type*} (l : list α), 
  if hl : length l = n^6 then sq_lits l hl row col else [])
-/

-- (univ: (fin 5 × fin 4))
--#eval fintype.elems (fin 5 × fin 3) -- {(0, 0), (0, 1), ...}

def alo_enc : enc_fn V := direct_alo
def amo_enc : enc_fn V := direct_amo

theorem amo_enc_is_correct : encodes (amk 1) (amo_enc : enc_fn V) :=
direct_amo_encodes_amo

theorem alo_enc_is_correct : encodes (alk 1) (alo_enc : enc_fn V) :=
direct_alo_encodes_alo

def sudoku_encoding (n : nat) : enc_fn V :=
let L : list (fin (n^2) × fin (n^2)) := cp (n^2) (n^2) in
encoding.len_check (
  (encoding.fold (L.map (λ ⟨row, col⟩,
    (encoding.append amo_enc alo_enc) ∘ (filter_by_idx (is_cell_lit row col))))) ++
  (fold (L.map (λ ⟨col, num⟩, 
    amo_enc ∘ (filter_by_idx (is_row_lit col num))))) ++
  (fold (L.map (λ ⟨row, num⟩, 
    amo_enc ∘ (filter_by_idx (is_col_lit row num))))) ++
  (fold ((list.zip (cp n n) (fin.range (n^2))).map (λ ⟨⟨srow, scol⟩, num⟩, 
    amo_enc ∘ (filter_by_idx (is_square_lit srow scol num))))))
(λ len, len = n^6)

/-
def l₀ : list (literal nat) := (fin.range (3^6)).map (λ n, Pos n)
def hl₀ : length l₀ = 3^6 := by dec_trivial
def g₀ : gensym nat := ⟨3^6, id, injective_id⟩

def l₁ : list (literal nat) := (fin.range (2^6)).map (λ n, Pos n)
def hl₁ : length l₁ = 2^6 := by dec_trivial
def g₁ : gensym nat := ⟨2^6, id, injective_id⟩

def enc_l₀ := (sudoku_encoding 3 l₀ g₀)
def enc_l₁ := (sudoku_encoding 2 l₁ g₁)
def enc_l₀' := (sudoku_encoding 3 [Pos 1] g₀)

#eval enc_l₀.1  -- Sudoku encoding for n = 3
#eval enc_l₀'.1 -- This is supposed to fail, since the list is too small
#eval enc_l₁.1  -- Sudoku encoding for n = 2
-/

theorem encodes_sudoku (n : nat) : encodes (is_valid_sudoku n) (sudoku_encoding n : enc_fn V) :=
begin
  apply check_encodes_of_encodes,
  repeat { apply encodes_append },
  { apply encodes_fold_fold,
    rintros ⟨fin₁, fin₂⟩ hfin,
    apply filter_by_idx_encodes_of_encodes,
    exact encodes_append amo_enc_is_correct alo_enc_is_correct },
  repeat { apply encodes_fold_fold,
           rintros ⟨fin₁, fin₂⟩ hfin,
           exact filter_by_idx_encodes_of_encodes _ amo_enc_is_correct },
  apply encodes_fold_fold,
  rintros ⟨⟨fin₁, fin₂⟩, fin₃⟩ hfins,
  exact filter_by_idx_encodes_of_encodes _ amo_enc_is_correct
end

theorem encodes_full_sudoku (n : nat) : encodes (is_valid_sudoku' n) (sudoku_encoding n : enc_fn V) :=
begin
  split,
  { intros l g hdis τ,
    unfold constraint.eval,
    rw ← is_valid_implies_is_valid,
    exact (encodes_sudoku n).1 hdis τ },
  { exact (encodes_sudoku n).2 }
end