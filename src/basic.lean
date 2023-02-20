/-
Some basic facts unrelated to clauses, etc.

Author: Cayden Codel, Marijn Heule, Jeremy Avigad
Carnegie Mellon University
-/

import data.bool.basic
import data.list.basic
import data.fin.basic
import data.list.indexes
import init.data.nat.lemmas
import data.finset.basic
import data.finset.fold
import init.function
import tactic

open list
open function
open nat

variables {α β γ : Type*}

/-! # Boolean logic -/

/- General -/

theorem ne_of_eq_ff_of_eq_tt {a b : bool} : a = ff → b = tt → a ≠ b :=
assume h₁ h₂, by { rw [h₁, h₂], intro h, contradiction }

theorem bool_symm : ∀ (a b : bool), a = b ↔ b = a :=
by simp only [bool.forall_bool, iff_self, and_self]

theorem prod.ext_self {α β : Type*} (p : α × β) : p = ⟨p.1, p.2⟩ :=
prod.ext rfl rfl

/- bxor -/

@[simp] theorem bxor_tt_left  : ∀ a, bxor tt a = !a := dec_trivial
@[simp] theorem bxor_tt_right : ∀ a, bxor a tt = !a := dec_trivial

theorem bxor_conjunctive (a b : bool) : bxor a b = (a || b) && (!a || !b) :=
by cases a; cases b; dec_trivial

theorem bxor_disjunctive (a b : bool) : bxor a b = (!a && b) || (a && !b) :=
by cases a; cases b; dec_trivial

/- cond -/

@[simp] theorem cond_tt_ff : ∀ a, cond a tt ff = a := dec_trivial
@[simp] theorem cond_ff_tt : ∀ a, cond a ff tt = !a := dec_trivial

theorem tt_of_cond_ne_second [decidable_eq α] {c d : α} {b : bool} :
  cond b c d ≠ d → b = tt :=
by { cases b, contradiction, tautology }

theorem ff_of_cond_ne_first [decidable_eq α] {c d : α} {b : bool} :
  cond b c d ≠ c → b = ff :=
by { cases b, tautology, contradiction }

theorem tt_of_ne_second_of_cond_eq [decidable_eq α] {c d e : α} {b : bool} :
  d ≠ e → cond b c d = e → b = tt :=
by { cases b, { intros, contradiction }, { tautology } }

theorem ff_of_ne_first_of_cond_eq [decidable_eq α] {c d e : α} {b : bool} :
  c ≠ e → cond b c d = e → b = ff :=
by { cases b, { tautology }, { intros, contradiction } }

theorem tt_of_ne_of_cond_eq_first [decidable_eq α] {c d : α} {b : bool} :
  c ≠ d → cond b c d = c → b = tt :=
by { cases b, { intros h₁ h₂, exact absurd h₂.symm h₁ }, { tautology } }

theorem ff_of_ne_of_cond_eq_second [decidable_eq α] {c d : α} {b : bool} :
  c ≠ d → cond b c d = d → b = ff :=
by { cases b, { tautology }, { intros, contradiction }}

/-! # Set -/

theorem not_mem_subset {a : α} {s₁ s₂ : set α} : a ∉ s₂ → s₁ ⊆ s₂ → a ∉ s₁ :=
begin
  intros ha hs,
  exact mt (@hs a) ha,
end

/-! # List operations -/

/- General results -/

theorem exists_append_singleton_of_ne_nil {l : list α} :
  l ≠ [] → ∃ L a, l = L ++ [a] :=
begin
  induction l with l₁ l ih,
  { contradiction },
  { intro h,
    cases l with l₂ l,
    { use [[], l₁], simp only [nil_append, eq_self_iff_true, and_self] },
    { rcases ih (cons_ne_nil l₂ l) with ⟨L, t, ht⟩,
      use [l₁ :: L, t], simp only [ht, cons_append, eq_self_iff_true, and_self] } }
end

-- TODO: do casewise with |, not in tactic
theorem exists_cons_cons_of_length_ge_two {l : list α} : 
  length l ≥ 2 → ∃ (a b : α) (L : list α), (a :: b :: L) = l :=
begin
  cases l with a as,
  { intro h, rw length at h, linarith },
  { cases as with b bs, 
    { intro h, rw [length, length] at h, linarith },
    { intro _,
      use [a, b, bs] } }
end

theorem exists_cons_cons_of_length_eq_two {l : list α} :
  length l = 2 → ∃ (a b : α), [a, b] = l :=
begin
  cases l with a as,
  { intro h, rw length at h, linarith },
  { cases as with b bs,
    { intro h, rw [length, length] at h, linarith },
    { cases bs with c cs,
      { simp },
      { intro h, rw [length, length, length] at h, linarith } } }
end

theorem nth_le_of_ge {α : Type*} {l : list α} {n c : nat} (Hn : n < length l) :
  n ≥ c → ∃ (Hn' : (n - c) + c < length l), 
  nth_le l n Hn = nth_le l ((n - c) + c) Hn' :=
begin
  intro hc,
  have := nat.sub_add_cancel hc,
  use this.symm ▸ Hn,
  simp [this]
end

theorem nth_le_mem_take_of_lt {α : Type*} [inhabited α] {l : list α} {i j : nat} (Hi : i < length l) :
  i < j → l.nth_le i Hi ∈ l.take j :=
begin
  induction l with a as ih generalizing i j,
  { simp at Hi, contradiction },
  { intro hlt,
    cases i,
    { cases j,
      { exact absurd hlt (nat.not_lt_zero 0) },
      { rw [nth_le_zero, head, take], exact mem_cons_self _ _ } },
    { cases j,
      { exact absurd hlt (nat.not_lt_zero i.succ) },
      { rw [nth_le, take],
        rw length at Hi,
        exact mem_cons_of_mem _ (ih (succ_lt_succ_iff.mp Hi) (succ_lt_succ_iff.mp hlt)) } } }
end

theorem nth_le_mem_drop_of_ge {α : Type*} [inhabited α] {l : list α} {i j : nat} (Hi : i < length l) :
  i ≥ j → l.nth_le i Hi ∈ l.drop j :=
begin
  induction l with a as ih generalizing i j,
  { simp at Hi, contradiction },
  { intro hge, 
    cases i,
    { cases j,
      { rw [nth_le, drop], exact mem_cons_self _ _ },
      { simp at hge, contradiction } },
    { cases j,
      { rw drop, exact nth_le_mem _ _ _ },
      { rw [nth_le, drop],
        rw length at Hi,
        exact ih (succ_lt_succ_iff.mp Hi) (succ_le_succ_iff.mp hge) } } }
end

theorem take_one_of_ne_nil {α : Type*} [inhabited α] {l : list α} : 
  l ≠ [] → l.take 1 = [l.head] :=
begin
  intro hl,
  rcases exists_cons_of_ne_nil hl with ⟨a, as, rfl⟩,
  simp [take, head]
end

@[simp] theorem mem_map_with_index {α β : Type*} {l : list α} {b : β} {f : nat → α → β} :
  b ∈ l.map_with_index f ↔ ∃ (a : α) (i : nat) (Hi : i < length l), a = l.nth_le i Hi ∧ f i a = b :=
begin
  induction l with a l ih generalizing f,
  { split, { rintro ⟨_⟩ }, { rintro ⟨a, _, ⟨_⟩, _⟩ } },
  { split,
    { intro hb,
      rcases eq_or_mem_of_mem_cons hb with (rfl | hw),
      { use [a, 0, dec_trivial],
        rw nth_le,
        exact ⟨rfl, rfl⟩ },
      { rw map_with_index_core_eq at hw,
        rcases ih.mp hw with ⟨a, i, Hi, ha, hf⟩,
        use [a, i + 1, succ_lt_succ_iff.mpr Hi],
        rw nth_le,
        subst ha,
        simp [hf], -- Investigate below later
        exact equiv.apply_swap_eq_self rfl Hi } },
    { rintros ⟨a, i, Hi, ha, hf⟩,
      cases i,
      { rw nth_le at ha,
        subst hf,
        rw [map_with_index, map_with_index_core, ha],
        exact mem_cons_self _ _ },
      { rw nth_le at ha,
        have := succ_lt_succ_iff.mp Hi,
        rw [map_with_index, map_with_index_core],
        apply (mem_cons_iff _ _ _).mpr,
        right,
        rw map_with_index_core_eq,
        apply ih.mpr,
        use [a, i, this, ha, hf] } } }
end

theorem take_sublist_of_le {α : Type*} {i j : nat} : i ≤ j → 
  ∀ (l : list α), l.take i <+ l.take j :=
begin
  intros hij l,
  induction l with a as ih generalizing i j,
  { rw [take_nil, take_nil] },
  { cases i,
    { rw take_zero,
      exact nil_sublist _ },
    { cases j,
      { exact absurd hij (not_le.mpr (succ_pos i)) },
      { rw [take, take],
        exact cons_sublist_cons_iff.mpr (ih (succ_le_succ_iff.mp hij)) } } }
end

theorem ne_tail_of_eq_head_of_ne [decidable_eq α] {a b : α} {l₁ l₂ : list α} :
  (a :: l₁) ≠ (b :: l₂) → a = b → l₁ ≠ l₂ :=
assume hne hab hl, absurd (congr (congr_arg cons hab) hl) hne

theorem length_lt_length_cons (a : α) (l : list α) :
  length l < length (a :: l) :=
by { rw length_cons, exact lt_add_one _ }

theorem strong_induction_on_lists [inhabited α] {p : list α → Prop} (l : list α)
  (h : ∀ l₁, (∀ l₂, length l₂ < length l₁ → p l₂) → p l₁) : p l :=
suffices ∀ (l₁ : list α) (l₂ : list α), length l₂ < length l₁ → p l₂,
  from this ((arbitrary α) :: l) l (length_lt_length_cons (arbitrary α) l),
begin
  intro l₁, induction l₁ with a as ih,
  { intros l₂ h₁, exact absurd h₁ (l₂.length).not_lt_zero },
  { intros m h₁,
    apply or.by_cases (decidable.lt_or_eq_of_le (nat.le_of_lt_succ h₁)),
    { intros, apply ih, assumption },
    { intro hlen, have := h m, rw hlen at this, exact this ih } }
end

theorem exists_append_of_gt_length {l : list α} {n : nat} : 
  length l > n → ∃ (l₁ l₂ : list α), l₁ ++ l₂ = l ∧ length l₁ = n :=
begin
  induction n with n ih,
  { intro h, use [nil, l, nil_append l, rfl] },
  { intro h,
    rcases ih (nat.lt_of_succ_lt h) with ⟨l₁, l₂, rfl, hl₁⟩,
    cases l₂ with l₂h hl₂t,
    { simp [hl₁] at h,
      exact absurd h (nat.not_succ_lt_self) },
    { use [l₁ ++ [l₂h], hl₂t],
      simp only [hl₁, eq_self_iff_true, length, singleton_append, 
        append_assoc, and_self, length_append] } }
end

theorem exists_append_mem_of_mem_of_ne {l : list α} {a b : α} :
  a ∈ l → b ∈ l → a ≠ b → ∃ (l₁ l₂), l₁ ++ l₂ = l ∧ 
  ((a ∈ l₁ ∧ b ∈ l₂) ∨ (a ∈ l₂ ∧ b ∈ l₁)) :=
begin
  induction l with x xs ih,
  { simp only [not_mem_nil, is_empty.forall_iff] },
  { intros ha hb hne,
    rcases eq_or_mem_of_mem_cons ha with (rfl | ha),
    { have := mem_of_ne_of_mem hne.symm hb,
      use [[a], xs],
      simp only [this, true_or, eq_self_iff_true, singleton_append, 
        and_self, mem_singleton] },
    { rcases eq_or_mem_of_mem_cons hb with (rfl | hb),
      { have := mem_of_ne_of_mem hne ha,
        use [[b], xs],
        simp only [this, hne, false_or, eq_self_iff_true, singleton_append, 
          and_self, mem_singleton, false_and] },
      { rcases ih ha hb hne with ⟨l₁, l₂, rfl, (⟨hl₁, hl₂⟩ | ⟨hl₁, hl₂⟩)⟩,
        { use [(x :: l₁), l₂],
          simp only [hl₁, hl₂, mem_cons_iff, cons_append, true_or, 
            eq_self_iff_true, or_true, and_self] },
        { use [(x :: l₁), l₂],
          simp only [hl₁, hl₂, mem_cons_iff, cons_append, eq_self_iff_true, 
            or_true, and_self] } } } }
end

theorem nth_le_sub_of_gt_zero {l : list α} {a : α} {n : nat} 
  (hn : n < length (a :: l)) (hnsub : (n - 1) < length l) :
  n > 0 → nth_le (a :: l) n hn = nth_le l (n - 1) hnsub :=
begin
  cases n,
  { intro h, exact absurd (ge_of_eq (refl 0)) (not_le.mpr h) },
  { intro _,
    rw nth_le,
    refl }
end

/- fold -/

theorem foldr_bor_tt (l : list α) (f : α → bool) : 
  foldr (λ x b, b || f x) tt l = tt :=
begin
  induction l with x xs ih,
  { rw foldr_nil },
  { rw [foldr_cons, ih, tt_bor] }
end

theorem foldr_band_ff (l : list α) (f : α → bool) :
  foldr (λ x b, b && f x) ff l = ff :=
begin
  induction l with x xs ih,
  { rw foldr_nil },
  { rw [foldr_cons, ih, ff_band] }
end

section map

variables {f : α → β} {a : α} {b : β} {l : list α}

theorem exists_of_map_singleton : map f l = [b] → ∃ a, [a] = l ∧ f a = b :=
begin
  cases l with x xs,
  { contradiction },
  { simp [map_cons],
    intros h₁ h₂,
    simp [h₁, h₂] }
end

theorem exists_cons_of_map_cons {bs : list β} :
  map f l = b :: bs → ∃ h L, l = h :: L ∧ f h = b ∧ map f L = bs :=
begin
  cases l with x xs,
  { contradiction },
  { rw map_cons,
    intro h,
    use [x, xs, ⟨refl _, (head_eq_of_cons_eq h), (tail_eq_of_cons_eq h)⟩] }
end

theorem exists_map_cons_of_map_cons {as : list α} : map f l = map f (a :: as) → 
  ∃ h L, l = h :: L ∧ f h = f a ∧ map f L = map f as :=
by { rw [map_cons], intro h, exact exists_cons_of_map_cons h }

theorem mem_map_append {l₁ l₂ : list α} {f : α → β} {b : β} :
  b ∈ map f (l₁ ++ l₂) → b ∈ map f l₁ ∨ b ∈ map f l₂ :=
by { rw [map_append, mem_append], exact id }

theorem mem_map_fst_of_mem {l : list (α × β)} {a : α} {b : β} :
  (a, b) ∈ l → a ∈ map prod.fst l :=
assume h, mem_map.mpr ⟨⟨a, b⟩, h, rfl⟩

theorem mem_map_snd_of_mem {l : list (α × β)} {a : α} {b : β} :
  (a, b) ∈ l → b ∈ map prod.snd l :=
assume h, mem_map.mpr ⟨⟨a, b⟩, h, rfl⟩

end map

/- filter -/

theorem length_filter {p : α → Prop} [decidable_pred p] {l : list α} : 
  length (filter p l) ≤ length l :=
begin
  induction l with x xs ih,
  { refl },
  { by_cases p x,
    { rw [filter_cons_of_pos _ h, length_cons, length_cons],
      exact nat.succ_le_succ_iff.mpr ih },
    { rw [filter_cons_of_neg _ h, length_cons],
      exact le_add_right ih } }
end

/-! # Naturals and successors of supremums -/

section nat

open nat

variables {f : α → nat} {l : list nat} {n m : nat}

/- General -/

theorem ne_succ_add (n m : nat) : n.succ + m ≠ n :=
begin
  rw [succ_eq_add_one, add_assoc, ← succ_eq_one_add],
  exact ne_of_gt (lt_add_of_pos_right n (succ_pos m))
end

theorem eq_succ_of_gt_of_le_succ {n m : nat} : m < n → n ≤ m + 1 → n = m + 1 :=
assume h₁ h₂, ge_antisymm (succ_le_iff.mpr h₁) h₂

theorem add_gt_one_of_gt_zero_of_gt_zero {n m : nat} : n > 0 → m > 0 → n + m > 1 :=
assume h₁ h₂, succ_le_iff.mp (add_le_add (succ_le_iff.mpr h₁) (succ_le_iff.mpr h₂))

theorem lt_min_left {a b c : nat} : a < min b c → a < b :=
assume hmin, lt_of_lt_of_le hmin (min_le_left b c)

theorem lt_min_right {a b c : nat} : a < min b c → a < c :=
assume hmin, lt_of_lt_of_le hmin (min_le_right b c)

section max_nat

def max_nat : list nat → nat
| []        := 0
| (n :: ns) := max n (max_nat ns)

theorem max_nat_eq_foldr_max (l) : max_nat l = foldr max 0 l :=
begin
  induction l with n ns ih,
  { refl },
  { unfold max_nat, rw [foldr_cons, ih] }
end

theorem le_max_nat_of_mem : n ∈ l → n ≤ max_nat l :=
begin
  induction l with m ms ih,
  { intro h, exact absurd h (not_mem_nil _) },
  { intros h,
    rcases eq_or_mem_of_mem_cons h with rfl | hms,
    { exact le_max_iff.mpr (or.inl (le_refl n)) },
    { exact le_max_iff.mpr (or.inr (ih hms)) } }
end

theorem not_mem_of_gt_max_nat : n > max_nat l → n ∉ l :=
by { contrapose, simp, exact le_max_nat_of_mem }

theorem exists_not_mem_of_bijective_of_gt_max_nat 
  (hf : bijective f) {l : list α} :
  n > max_nat (map f l) → ∃ a, f a = n ∧ a ∉ l :=
begin
  intros h,
  rcases (bijective_iff_exists_unique f).mp hf n with ⟨b, hb, _⟩,
  use b,
  split,
  { exact hb },
  { intro hbl,
    exact (not_mem_of_gt_max_nat h) (hb ▸ mem_map_of_mem f hbl) }
end

end max_nat

end nat

/-! # fin -/
namespace fin
open fin

theorem eq_or_exists_eq {n : ℕ} (i : fin (n + 1)) : i = n ∨ ∃ j : fin n, i = j :=
begin
  rcases eq_or_lt_of_le (le_of_lt_succ i.prop) with (h | h),
  { left,
    have : ↑n = ↑(i.val), { rw h },
    rw this,
    simp },
  { right, use ⟨i.val, h⟩, simp }
end

/-! # range -/

def range_core (n : nat) : list (fin (n + 1)) → Π (m : nat), m < n + 1 → list (fin (n + 1))
| l 0       hm := ⟨0, hm⟩ :: l
| l (m + 1) hm := range_core (⟨m + 1, hm⟩ :: l) m (lt_of_succ_lt hm)

def range : Π (n : nat), list (fin n)
| 0       := []
| (n + 1) := range_core n [] n (lt_succ_self n)

theorem mem_range_core {n m : nat} (hm : m < n + 1) : 
  ∀ (l : list (fin (n + 1))) (a : fin (n + 1)),
  a ∈ range_core n l m hm ↔ (a ∈ l ∨ a.val ≤ m) :=
begin
  intros l a,
  induction m with m ih generalizing l,
  { simp [range_core],
    split,
    { rintro (rfl | h),
      { exact or.inr rfl },
      { exact or.inl h } },
    { rintro (h | h),
      { exact or.inr h },
      { exact or.inl (ext h) } } },
  { split,
    { intro ha,
      unfold range_core at ha,
      rcases (ih (lt_of_succ_lt hm) _).mp ha with (h | h),
      { rcases eq_or_mem_of_mem_cons h with (rfl | hl),
        { right, refl },
        { exact or.inl hl } },
      { exact or.inr (le_succ_of_le h) } },
    { intro ha,
      unfold range_core,
      apply (ih (lt_of_succ_lt hm) _).mpr,
      rcases ha with (h | h),
      { exact or.inl (mem_cons_of_mem _ h) },
      { rcases eq_or_lt_of_le h with (h | h),
        { left,
          have : a = ⟨m + 1, hm⟩,
          { exact ext h },
          rw this,
          exact mem_cons_self _ l },
        { exact or.inr (le_of_lt_succ h) } } } }
end

theorem mem_range (n : nat) : ∀ (a : fin n), a ∈ range n :=
begin
  intro a,
  induction n with n ih,
  { exact elim0 a },
  { apply (mem_range_core (lt_succ_self n) [] a).mpr,
    exact or.inr (le_of_lt_succ a.prop) }
end

/-! # Cartesian product -/

def cp (n m : nat) : list (fin n × fin m) :=
  join ((range n).map (λ a, (range m).map (λ b, ⟨a, b⟩)))

theorem mem_cp (n m : nat) : ∀ (a : fin n) (b : fin m), (a, b) ∈ cp n m :=
begin
  intros a b,
  simp only [cp, mem_join, mem_map, exists_exists_and_eq_and, prod.mk.inj_iff, exists_eq_right_right],
  exact ⟨mem_range n a, mem_range m b⟩
end

def square : Π {n : nat}, fin n → fin (n^2)
| 0       i := elim0 i
| (n + 1) i := ⟨i.val * (n + 1), (pow_two (n + 1)).symm ▸ (mul_lt_mul_right (zero_lt_succ n)).mpr i.prop⟩

theorem nat.mul_pred_eq_square_sub (n : nat) : n * (n - 1) = n^2 - n :=
by rw [pow_two, nat.mul_sub_left_distrib, mul_one]

theorem nat.le_square_sub_of_lt {a b : nat} : a < b → a * b ≤ b^2 - b :=
begin
  intro h,
  cases b,
  { exact absurd h (nat.not_lt_zero a) },
  { rw ← nat.mul_pred_eq_square_sub,
    simp,
    rw mul_comm b.succ b,
    exact (mul_le_mul_right (pos_of_gt h)).mpr (le_of_lt_succ h) }
end

theorem nat.sub_add_lt_of_lt_of_lt {a b c : nat} : a < b → b < c → c - b + a < c :=
assume ha hb, lt_of_lt_of_le (add_lt_add_left ha (c - b)) (le_of_eq (nat.sub_add_cancel (le_of_lt hb)))

theorem nat.lt_square_of_gt_one {a : nat} : 1 < a → a < a^2 :=
begin
  intro h,
  rw pow_two,
  exact lt_mul_self h
end

theorem nat.sub_add_lt_square_of_lt {a b : nat} : a < b → b^2 - b + a < b^2 :=
begin
  intro h,
  cases b,
  { exact absurd h (nat.not_lt_zero a) },
  { cases b,
    { simp at h, subst h, simp },
    { have : 1 < b.succ.succ, dec_trivial,
      exact nat.sub_add_lt_of_lt_of_lt h (nat.lt_square_of_gt_one this) } }
end

theorem nat.mul_add_lt_square_of_lt_of_lt {a b c : nat} : a < c → b < c → (a * c) + b < c^2 :=
assume h₁ h₂, lt_of_le_of_lt (add_le_add_right (nat.le_square_sub_of_lt h₁) b) 
  (nat.sub_add_lt_square_of_lt h₂)

def square_add : Π {n : nat}, fin n → fin n → fin (n^2)
| 0       i j := fin.elim0 i
| (n + 1) i j := ⟨i.val * (n + 1) + j.val, nat.mul_add_lt_square_of_lt_of_lt i.prop j.prop⟩

end fin

namespace finset
open finset

variables [decidable_eq α] 

theorem subset_union_of_subset_left {s₁ s₂ : finset α} (s₃ : finset α) :
  s₁ ⊆ s₂ → s₁ ⊆ s₂ ∪ s₃ :=
λ h, subset.trans h (subset_union_left s₂ s₃)

theorem subset_union_of_subset_right {s₁ s₃ : finset α} (s₂ : finset α) :
  s₁ ⊆ s₃ → s₁ ⊆ s₂ ∪ s₃ :=
λ h, subset.trans h (subset_union_right s₂ s₃)

end finset

namespace list

/-! # idx_filter -/

/- Better version with fin, but tough to prove theorems about
def filter_by_idx (l : list α) (p : fin (length l) → Prop) [decidable_pred p] : list α :=
  map prod.snd (filter (p ∘ prod.fst) (zip (fin.range (length l)) l))
-/

-- Version with nat. Still hard to prove things
--def filter_by_idx (p : nat → Prop) [decidable_pred p] (l : list α) : list α :=
--  map prod.snd (filter (p ∘ prod.fst) (zip (range (length l)) l))

section filter_by_idx

variables (p : nat → Prop) [decidable_pred p] (a : α) (l : list α)

def filter_by_idx_core : nat → list α → list α
| n []        := []
| n (a :: as) := if p n then a :: (filter_by_idx_core (n + 1) as) 
                 else filter_by_idx_core (n + 1) as

def filter_by_idx : list α := filter_by_idx_core p 0 l

@[simp] theorem filter_by_idx_core_nil (n : nat) : filter_by_idx_core p n ([] : list α) = [] := rfl
@[simp] theorem filter_by_idx_nil : filter_by_idx p ([] : list α) = [] := rfl

@[simp] theorem filter_by_idx_core_singleton (n : nat) : 
  filter_by_idx_core p n [a] = if p n then [a] else [] := rfl

@[simp] theorem filter_by_idx_singleton : filter_by_idx p [a] = if p 0 then [a] else [] := rfl

theorem filter_by_idx_core_add (n c : nat) :
  filter_by_idx_core (p ∘ (λ x, x + c)) n l = filter_by_idx_core p (n + c) l :=
begin
  induction l with a as ih generalizing n c,
  { refl },
  { unfold filter_by_idx_core,
    by_cases hp : p (n + c);
    { simp [hp],
      rw [add_assoc n c 1, add_comm c 1, ← add_assoc n 1 c],
      exact ih (n + 1) c } }
end

@[simp] theorem filter_by_idx_cons (p : nat → Prop) [decidable_pred p] (a : α) (l : list α) :
  filter_by_idx p (a :: l) = if p 0 then a :: filter_by_idx (p ∘ succ) l else filter_by_idx (p ∘ succ) l :=
begin
  unfold filter_by_idx,
  rw filter_by_idx_core,
  by_cases hp : p 0;
  { simp [hp], exact (filter_by_idx_core_add p l 0 1).symm }
end

theorem map_filter_by_idx (f : β → α) (l : list β) (p : nat → Prop) [decidable_pred p] :
  filter_by_idx p (map f l) = map f (filter_by_idx p l) :=
begin
  unfreezingI { induction l with b bs ih generalizing p,
  { refl },
  { by_cases hp : p 0;
    { simp [hp], apply ih (p ∘ succ) } } }
end

theorem filter_by_idx_sublist : filter_by_idx p l <+ l :=
begin
  unfreezingI { induction l with a as ih generalizing p,
  { refl },
  { by_cases hp : p 0; simp [hp],
    { apply sublist.cons_cons a, exact ih _ },
    { apply sublist.cons, exact ih _ } } }
end

theorem filter_by_idx_subset : filter_by_idx p l ⊆ l :=
sublist.subset (filter_by_idx_sublist _ _)

end filter_by_idx

end list