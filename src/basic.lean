/-
Some basic facts unrelated to clauses, etc.

Author: Cayden Codel, Marijn Heule, Jeremy Avigad
Carnegie Mellon University
-/

import data.bool.basic
import data.list.basic
import init.data.nat.lemmas
import data.finset.basic
import data.finset.fold
import init.function

open list
open function

universes u v
variables {α : Type u} {β : Type v}

/-! # Boolean logic -/

/- General -/

theorem ne_of_eq_ff_of_eq_tt {a b : bool} : a = ff → b = tt → a ≠ b :=
assume h₁ h₂, by { rw [h₁, h₂], intro h, contradiction }

/- bxor -/

notation a ` ⊕ ` b := bxor a b

@[simp] theorem bxor_tt_left  : ∀ a, tt ⊕ a = !a := dec_trivial
@[simp] theorem bxor_tt_right : ∀ a, a ⊕ tt = !a := dec_trivial

theorem bxor_conjunctive (a b : bool) : a ⊕ b = (a || b) && (!a || !b) :=
by cases a; cases b; dec_trivial

theorem bxor_disjunctive (a b : bool) : a ⊕ b = (!a && b) || (a && !b) :=
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

/-! # List operations -/

/- General results -/

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