/-
Defines a notion of getting two distinct indexes from a list.

Authors: Cayden Codel
Carnegie Mellon University
-/

import basic

import data.list.basic
import data.nat.basic
import tactic

namespace distinct

open list nat

def distinct {α : Type*} (a₁ a₂ : α) (l : list α) :=
  ∃ (i j : nat) (Hi : i < l.length) (Hj : j < l.length), 
  i < j ∧ l.nth_le i Hi = a₁ ∧ l.nth_le j Hj = a₂

theorem not_distinct_nil {α : Type*} (a₁ a₂ : α) : ¬distinct a₁ a₂ [] :=
begin
  rintro ⟨i, _, hi, _, _⟩,
  rw length at hi,
  linarith
end

theorem not_distinct_singleton {α : Type*} (a₁ a₂ a₃ : α) : ¬distinct a₁ a₂ [a₃] :=
begin
  rintro ⟨i, j, _, hj, hij, _⟩,
  have := gt_of_gt_of_ge hij (zero_le i),
  rw [length, length] at hj,
  linarith
end

theorem distinct_double {α : Type*} (a₁ a₂ : α) : distinct a₁ a₂ [a₁, a₂] :=
by { use [0, 1], simp }

theorem eq_of_distinct_double {α : Type*} {a₁ a₂ b₁ b₂ : α} :
  distinct a₁ a₂ [b₁, b₂] → a₁ = b₁ ∧ a₂ = b₂ :=
begin
  rintros ⟨i, j, hi, hj, hij, hil, hjl⟩,
  cases i,
  { rcases nth_le_of_ge hj (succ_le_iff.mpr hij) with ⟨h₁, h₂⟩,
    rw [hjl, nth_le, nth_le_singleton] at h₂,
    rw nth_le at hil,
    exact ⟨hil.symm, h₂⟩ },
  { simp [length] at hj,
    have : 1 ≤ i + 1, exact le_add_self,
    have := gt_of_gt_of_ge hij this,
    linarith }
end

theorem length_ge_two_of_distinct {α : Type*} {a₁ a₂ : α} {l : list α} :
  distinct a₁ a₂ l → length l ≥ 2 :=
begin
  rintros ⟨i, j, _, Hj, hij, _, _⟩,
  have : 1 ≤ j, exact succ_le_iff.mpr (pos_of_gt hij),
  have : 1 < length l, exact gt_of_gt_of_ge Hj this,
  exact succ_le_iff.mpr this
end

theorem exists_distinct_of_length_ge_two {α : Type*} {l : list α} :
  length l ≥ 2 → ∃ {a₁ a₂ : α}, distinct a₁ a₂ l :=
begin
  intro hl,
  rcases exists_cons_cons_of_length_ge_two hl with ⟨a₁, a₂, as, rfl⟩,
  use [a₁, a₂, 0, 1], simp
end

theorem distinct_cons_of_mem {α : Type*} (a₁ : α) {a₂ : α} {l : list α} :
  a₂ ∈ l → distinct a₁ a₂ (a₁ :: l) :=
begin
  intro h,
  rcases mem_iff_nth_le.mp h with ⟨n, hlen, hn⟩,
  have hi : 0 < length (a₁ :: l), simp,
  have hj : n + 1 < length (a₁ :: l), 
    by { rw [length, succ_lt_succ_iff], exact hlen },
  use [0, n + 1, hi, hj],
  simp [← hn],
  refl
end

theorem distinct_cons_of_distinct {α : Type*} {a₁ a₂ : α} {l : list α} (a : α) :
  distinct a₁ a₂ l → distinct a₁ a₂ (a :: l) :=
begin
  rintros ⟨i, j, hi, hj, hij, hil, hjl⟩,
  have hi₂ : i + 1 < (a :: l).length,
  { simp only [hi, length, add_lt_add_iff_right] },
  have hj₂ : j + 1 < (a :: l).length,
  { simp only [hj, length, add_lt_add_iff_right] },
  use [i + 1, j + 1, hi₂, hj₂, succ_lt_succ hij],
  rw [nth_le, nth_le],
  exact ⟨hil, hjl⟩
end

theorem distinct_of_distinct_cons_of_ne {α : Type*} {a₁ a₂ a : α} {l : list α} :
  distinct a₁ a₂ (a :: l) → a₁ ≠ a → distinct a₁ a₂ l :=
begin
  rintros ⟨i, j, hi, hj, hij, hil, hjl⟩ hne,
  cases i,
  { rw nth_le at hil, exact absurd hil.symm hne },
  { rw length at hi,
    have := succ_le_iff.mpr ((gt_of_gt_of_ge hij (zero_le i.succ))),
    rcases nth_le_of_ge hj this with ⟨hjm, hnth⟩,
    rw [← nat.sub_add_cancel this, length] at hj,
    rw ← nat.sub_add_cancel this at hij,
    use [i, j - 1, succ_lt_succ_iff.mp hi, succ_lt_succ_iff.mp hj,
      succ_lt_succ_iff.mp hij],
    rw [← hil, ← hjl, hnth, nth_le, nth_le],
    exact ⟨rfl, rfl⟩ }
end

theorem eq_or_distinct_of_distinct_cons {α : Type*} {a₁ a₂ a : α} {l : list α} :
  distinct a₁ a₂ (a :: l) → a₁ = a ∨ distinct a₁ a₂ l :=
begin
  intro hdis,
  by_cases h : (a₁ = a),
  { exact or.inl h },
  { exact or.inr (distinct_of_distinct_cons_of_ne hdis h) }
end

theorem mem_tail_of_distinct_cons {α : Type*} {a₁ a₂ a : α} {as : list α} :
  distinct a₁ a₂ (a :: as) → a₂ ∈ as :=
begin
  rintro ⟨i, j, Hi, Hj, hij, hil, hjl⟩,
  have := succ_le_iff.mpr ((gt_of_gt_of_ge hij (zero_le i))),
  rcases (nth_le_of_ge Hj this) with ⟨Hj₂, hnth⟩,
  rw hjl at hnth,
  rw [hnth, nth_le],
  exact nth_le_mem as _ _
end

theorem distinct_sublist {α : Type*} {a₁ a₂ : α} {l₁ l₂ : list α} :
  l₁ <+ l₂ → distinct a₁ a₂ l₁ → distinct a₁ a₂ l₂ :=
begin
  induction l₂ with a as ih generalizing l₁,
  { rw sublist_nil_iff_eq_nil, rintro rfl, exact id },
  { intros hl₁ hdis,
    cases hl₁,
    { exact distinct_cons_of_distinct a (ih hl₁_ᾰ hdis) },
    { by_cases ha : (a₁ = a),
      { have := (sublist.subset hl₁_ᾰ) (mem_tail_of_distinct_cons hdis),
        rcases mem_iff_nth_le.mp this with ⟨n, hn₁, hn₂⟩,
        have Hi : 0 < (a :: as).length, by dec_trivial,
        have Hj : n + 1 < (a :: as).length,
        { rw length, exact succ_lt_succ_iff.mpr hn₁ },
        use [0, n + 1, Hi, Hj],
        simp [ha],
        rw ← hn₂,
        refl },
      { have := distinct_of_distinct_cons_of_ne hdis ha,
        exact distinct_cons_of_distinct a (ih hl₁_ᾰ this) } } }
end

-- TODO way to do in a non-tactic way?
theorem mem_of_distinct_left {α : Type*} {a₁ a₂ : α} {l : list α} :
  distinct a₁ a₂ l → a₁ ∈ l :=
begin
  rintro ⟨i, _, hi, _, _, hil, _⟩,
  rw ← hil, exact nth_le_mem l _ _
end

-- TODO this too
theorem mem_of_distinct_right {α : Type*} {a₁ a₂ : α} {l : list α} :
  distinct a₁ a₂ l → a₂ ∈ l :=
begin
  rintro ⟨_, j, _, hj, _, _, hjl⟩,
  rw ← hjl, exact nth_le_mem l _ _
end

theorem countp_ge_two_of_distinct_of_pos {α : Type*} {a₁ a₂ : α}
  {p : α → Prop} [decidable_pred p] (h₁ : p a₁) (h₂ : p a₂) :
  ∀ {l : list α}, distinct a₁ a₂ l → countp p l ≥ 2
| [] hdis := absurd hdis (not_distinct_nil _ _)
| [a] hdis := absurd hdis (not_distinct_singleton _ _ _)
| (a :: b :: bs) hdis := begin
  have hmem := mem_tail_of_distinct_cons hdis,
  rcases hdis with ⟨i, j, hi, hj, hij, hil, hjl⟩,
  cases i,
  { rw nth_le at hil,
    rw [hil, countp_cons_of_pos p (b :: bs) h₁],
    apply succ_le_succ_iff.mpr,
    apply succ_le_iff.mpr,
    apply (countp_pos p).mpr,
    use [a₂, hmem, h₂] },
  { cases j,
    { linarith },
    { have : distinct a₁ a₂ (b :: bs),
      { rw [length, succ_lt_succ_iff] at hi hj,
        rw succ_lt_succ_iff at hij,
        rw nth_le at hil hjl,
        use [i, j, hi, hj, hij, hil, hjl] },
      have ih := countp_ge_two_of_distinct_of_pos this,
      exact le_trans ih (sublist.countp_le p (sublist_cons a (b :: bs))) } }
end

theorem distinct_of_mem_take_of_mem_drop {α : Type*} {a₁ a₂ : α} {l : list α} :
  ∀ {i : nat}, a₁ ∈ l.take i → a₂ ∈ l.drop i → distinct a₁ a₂ l :=
begin
  intros i htake hdrop,
  induction i with i ih generalizing l,
  { rw take at htake, exact absurd htake (not_mem_nil _) },
  { cases l with x xs,
    { rw take_nil at htake, exact absurd htake (not_mem_nil _) },
    { rw take at htake, rw drop at hdrop,
      rcases eq_or_mem_of_mem_cons htake with (rfl | h),
      { exact distinct_cons_of_mem a₁ (mem_of_mem_drop hdrop) },
      { exact distinct_cons_of_distinct _ (ih h hdrop) } } }
end


end distinct