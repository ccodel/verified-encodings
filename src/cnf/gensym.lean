/-
Following the tradition of other programming languages,
gensym.lean contains the definition of an object to generate
fresh variable names for CNF encodings. Also included in this
file are the proofs of the freshness of variable generation.

Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
-/

import cnf.cnf
import data.list.basic
import data.nat.basic
import data.set.basic

open nat
open function
open prod
open list

variables {α : Type*}-- [decidable_eq α] [inhabited α]

/- Essentially, a gensym object only tracks a position along the natural number
   line. When provided with an injective function from the naturals to the
   boolean variable type, the gensym will provably generate fresh variables,
   with respect to those variables already generated.
-/
structure gensym (α : Type*) :=
(offset : nat)
(f : nat → α)
(f_inj : injective f)

namespace gensym

variables {f : nat → α} (hf : injective f) {a : α} (g : gensym α)

/-! # Gensym creation -/

/- Initial gensym that starts at 0 -/
def init : gensym α := { offset := 0, f := f, f_inj := hf }

/- We can create a gensym that doesn't ever generate variables in a list
   when we provide a bijection between α and the naturals. Simply start the
   gensym's offset at one more than the maximum element in the list. -/
def seed (fi : α → nat) (fi_inj : injective fi) 
  (rinv : right_inverse f fi) : list α → gensym α
| [] := init hf
| l  := { offset := 1 + max_nat (map fi l), f := f, f_inj := hf }

/-! # fresh -/

-- Note: the operation below acts like a state monad
-- Future work on this file could convert gensym into a monad

/- Generates a new variable and returns an updated gensym -/
def fresh : (α × gensym α) :=
⟨g.f (g.offset), ⟨g.offset + 1, g.f, g.f_inj⟩⟩

@[simp] theorem fresh_offset :
  (fresh g).2.offset = g.offset + 1 := rfl

@[simp] theorem fresh_f : (fresh g).2.f = g.f := rfl

theorem fresh_var : (fresh g).1 = g.f g.offset := rfl

theorem fresh_f_injective : injective (fresh g).2.f :=
(fresh g).2.f_inj

/-! # nfresh -/

/- Generates a list of n new variables and returns the gensym at the end -/
def nfresh : gensym α → nat → (list α × gensym α)
| g 0       := ⟨[], g⟩
| g (n + 1) := let ⟨a, g₂⟩ := fresh g in
               prod.map (λ l, a :: l) id (nfresh g₂ n)

@[simp] theorem nfresh_zero : nfresh g 0 = ⟨[], g⟩ := rfl

@[simp] theorem nfresh_one : (nfresh g 1).2 = (fresh g).2 := rfl

@[simp] theorem nfresh_offset (n : nat) :
  (nfresh g n).2.offset = g.offset + n :=
begin
  induction n with n ih generalizing g,
  { refl },
  { simp [nfresh, fresh, ih, nat.add_succ, nat.succ_add] }
end

@[simp] theorem nfresh_f (n : nat) : (nfresh g n).2.f = g.f :=
begin
  induction n with n ih generalizing g,
  { refl },
  { simp only [nfresh, fresh, ih, id.def, prod_map] }
end

theorem nfresh_f_injective (n : nat) : 
  injective (nfresh g n).2.f := (nfresh g n).2.f_inj

theorem nfresh_one_eq_fresh : 
  nfresh g 1 = prod.map (λ a, [a]) id (fresh g) :=
by simp only [fresh, nfresh, map_mk, eq_self_iff_true]

theorem nfresh_succ_eq_nfresh_fresh (n : nat) :
  nfresh g (n + 1) = ⟨(fresh g).1 :: (nfresh (fresh g).2 n).1, 
                      (fresh (nfresh g n).2).2⟩ :=
begin
  induction n with n ih generalizing g,
  { refl },
  { simp [nfresh, fresh, ih, nat.add_succ, nat.succ_add] }
end

theorem nfresh_succ_gensym_eq_fresh_nfresh_gensym (n : nat) :
  (nfresh g (n + 1)).2 = (fresh (nfresh g n).2).2 :=
by simp only [nfresh_succ_eq_nfresh_fresh]

theorem nfresh_succ_gensym_eq_nfresh_fresh_gensym (n : nat) :
  (nfresh g (n + 1)).2 = (nfresh (fresh g).2 n).2 :=
by simp [nfresh_succ_eq_nfresh_fresh, nfresh, fresh]

--theorem nfresh_succ_eq_fresh_nfresh (n : nat) :
--  nfresh g (n + 1) = ⟨(nfresh g n).1 ++ [(nfresh g n).2.fresh.1], (nfresh g n).2.fresh.2⟩ :=

/- nfresh can be split across two sets of calls -/
-- TODO later include both list and gensym objets in theorem
theorem nfresh_concat {n m₁ m₂ : nat} :
  n = m₁ + m₂ → (nfresh g n).2 = (nfresh (nfresh g m₁).2 m₂).2 :=
begin
  induction n with n ih generalizing m₁ m₂,
  { intro h,
    rw [nat.eq_zero_of_add_eq_zero_left h.symm,
      nat.eq_zero_of_add_eq_zero_right h.symm],
    refl },
  { cases m₂,
    { rw add_zero, rintro rfl, refl },
    { simp only [succ_eq_add_one, ← add_assoc],
      intro h,
      simp only [ih (nat.succ.inj h),
        nfresh_succ_gensym_eq_fresh_nfresh_gensym] } }
end

theorem length_list_nfresh (n : nat) : 
  length (nfresh g n).1 = n :=
begin
  induction n with n ih generalizing g,
  { refl },
  { simp only [nfresh_succ_eq_nfresh_fresh, ih, length_cons] }
end

/-! # stock -/

/- Any gensym has a set of values it can produce
   A variable is in the stock if offset could reach it. -/
def stock : set α := { a | ∃ (n : nat), g.f (g.offset + n) = a }

-- TODO this can be cleaned up - right induction proof?
@[simp] theorem mem_stock {g : gensym α} : 
  a ∈ g.stock ↔ a = g.fresh.1 ∨ a ∈ stock g.fresh.2 :=
begin
  split,
  { unfold stock,
    rw set.mem_set_of_eq,
    rintros ⟨n, hn⟩,
    induction n with n ih generalizing g,
    { rw add_zero at hn,
      exact or.inl hn.symm },
    { right,
      rw set.mem_set_of_eq,
      have : g.fresh.2.f (g.fresh.2.offset + n) = a,
      { rw [fresh_f, fresh_offset, add_assoc, ← succ_eq_one_add],
        exact hn },
      rcases ih this with (hm | hm),
      { simp [fresh] at hm,
        use 0,
        rw [fresh_f, fresh_offset, add_zero],
        exact hm.symm },
      { rw set.mem_set_of_eq at hm,
        rcases hm with ⟨m, hm⟩,
        use m + 1,
        simp at hm,
        simp,
        rw add_comm m 1,
        rw ← add_assoc _ 1 m,
        exact hm } } },
  { rintros (ha | ha),
    { unfold stock, rw set.mem_set_of_eq,
      simp [fresh] at ha,
      use 0, simp [ha] },
    { unfold stock at ha, rw set.mem_set_of_eq at ha,
      rcases ha with ⟨n, hn⟩,
      unfold stock, rw set.mem_set_of_eq,
      use n + 1,
      simp at hn,
      rw [add_comm n 1, ← add_assoc _ 1 n],
      exact hn } }
end

theorem fresh_mem_stock : g.fresh.1 ∈ g.stock :=
mem_stock.mpr (or.inl (refl g.fresh.1))

theorem fresh_fresh_mem_stock : g.fresh.2.fresh.1 ∈ g.stock :=
mem_stock.mpr (or.inr (fresh_mem_stock g.fresh.2))

theorem mem_stock_of_mem_fresh_stock {g : gensym α} : 
  a ∈ g.fresh.2.stock → a ∈ g.stock :=
assume h, mem_stock.mpr (or.inr h)

theorem fresh_stock_subset : g.fresh.2.stock ⊆ g.stock :=
begin
  intros a ha,
  unfold stock at ha, rw set.mem_set_of_eq at ha,
  rcases ha with ⟨n, hn⟩,
  simp only [fresh_f, fresh_offset, add_assoc] at hn,
  unfold stock, rw set.mem_set_of_eq,
  use [1 + n, hn]
end

theorem fresh_not_mem_fresh_stock : g.fresh.1 ∉ g.fresh.2.stock :=
begin
  intro h,
  rcases mem_stock.mp h with hf | hf,
  { simp only [fresh] at hf,
    exact absurd (g.3.eq_iff.mp hf).symm (nat.succ_ne_self g.offset) },
  { unfold stock at hf,
    rw set.mem_set_of_eq at hf,
    rcases hf with ⟨n, hn⟩,
    simp [fresh] at hn,
    rw [add_assoc, ← succ_eq_add_one] at hn,
    exact absurd (g.3.eq_iff.mp hn) (ne_succ_add _ _) }
end

-- TODO can make one line
theorem fresh_stock_ssubset : stock g.fresh.2 ⊂ g.stock :=
begin
  apply (set.ssubset_iff_of_subset (fresh_stock_subset g)).mpr,
  use [g.fresh.1, fresh_mem_stock g, fresh_not_mem_fresh_stock g]
end

theorem nfresh_mem_stock {g : gensym α} {n : nat} : ∀ ⦃v⦄, v ∈ (g.nfresh n).1 → v ∈ g.stock :=
begin
  induction n with n ih generalizing g,
  { intros v hv, simp [nfresh] at hv, contradiction },
  { intros v hv,
    rw [nfresh_succ_eq_nfresh_fresh, mem_cons_iff] at hv,
    rcases hv with (rfl | hv),
    { exact fresh_mem_stock g },
    { exact fresh_stock_subset _ (ih hv) } }
end

theorem nfresh_stock_subset : ∀ (n : nat), (g.nfresh n).2.stock ⊆ g.stock :=
begin
  intro n,
  induction n with n ih,
  { rw nfresh_zero },
  { rw nfresh_succ_eq_nfresh_fresh,
    exact subset_trans (fresh_stock_subset _) ih }
end

-- # nth

def nth (g : gensym α) (n : nat) : α := g.f (n + g.offset)

theorem nth_ne_of_ne {i j : nat} : i ≠ j → ∀ (g : gensym α), nth g i ≠ nth g j :=
assume hne g, g.f_inj.ne_iff.mpr ((add_ne_add_left g.offset).mpr hne)

theorem eq_of_nth_eq {i j : nat} {g : gensym α} : nth g i = nth g j → i = j :=
assume h, (add_left_inj g.offset).mp (g.f_inj.eq_iff.mp h)

theorem nth_zero_eq_fresh : ∀ (g : gensym α), g.nth 0 = g.fresh.1 :=
by { intro g, rw [nth, fresh, zero_add] }

theorem nth_mem_stock : ∀ (g : gensym α) (n : nat), g.nth n ∈ g.stock :=
begin
  intros g n,
  rw [nth, stock],
  simp, use n, rw add_comm,
end

theorem nth_not_mem_nfresh_stock {g : gensym α} {i : nat} : ∀ ⦃a : α⦄, 
  a ∈ (g.nfresh i).1 → a ∉ (g.nfresh i).2.stock :=
begin
  induction i with i ih generalizing g;
  intros a ha,
  { simp at ha, contradiction },
  { rw nfresh_succ_eq_nfresh_fresh at ha,
    unfold prod.fst at ha,
    rcases eq_or_mem_of_mem_cons ha with (rfl | hmem),
    { rw nfresh_succ_eq_nfresh_fresh,
      apply not_mem_subset (fresh_not_mem_fresh_stock g),
      unfold prod.snd,
      rw ← nfresh_succ_gensym_eq_fresh_nfresh_gensym g,
      rw nfresh_succ_gensym_eq_nfresh_fresh_gensym g,
      exact nfresh_stock_subset _ _ },
    { exact ih hmem } }
end

theorem nth_mem_nfresh_of_lt {i j : nat} : i < j → g.nth i ∈ (g.nfresh j).1 :=
begin
  induction j with j ih generalizing i g,
  { simp },
  { intro hlt,
    rw nfresh_succ_eq_nfresh_fresh,
    unfold prod.fst,
    cases i,
    { unfold fresh,
      unfold nth,
      rw [zero_add],
      exact mem_cons_self _ _ },
    { have : g.nth i.succ = g.fresh.2.nth i,
      { simp [nth, fresh, add_comm, add_assoc, succ_eq_add_one] },
      rw this,
      exact mem_cons_of_mem _ (ih _ (succ_lt_succ_iff.mp hlt)) } }
end

-- Disjointness
theorem forall_nth_not_mem_of_disjoint {g : gensym α} {l : set α} :
  disjoint g.stock l → ∀ (n : nat), g.nth n ∉ l :=
λ h n, set.disjoint_left.mp h (nth_mem_stock g n)

-- Coercion is silly
theorem forall_nth_not_mem_of_disjoint' {g : gensym α} {l : finset α} :
  disjoint g.stock l → ∀ (n : nat), g.nth n ∉ l :=
forall_nth_not_mem_of_disjoint

end gensym