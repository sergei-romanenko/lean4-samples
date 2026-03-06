/-
  Based on

    James Brotherston. Sequent Calculus Proof Systems for Inductive Definitions.
    PhD thesis, University of Edinburgh, 2006.
    https://era.ed.ac.uk/items/f3318657-8d5e-42e4-810b-9eba4235a450
 -/

import Batteries
import Aesop

-- Mathematical induction.
-- Augustus de Morgan (1838).

def indNat  {p : Nat -> Prop}
      (p0 : p 0)
      (step : (m : Nat) -> p m -> p (m + 1)) :
      (n : Nat) -> p n
  | 0 => p0
  | k + 1 =>
      step k (indNat p0 step k)

def indNat_by  {p : Nat -> Prop}
      (p0 : p 0)
      (step : (m : Nat) -> p m -> p (m + 1)) :
      (n : Nat) -> p n := by
  intro n
  induction n with
  | zero => exact p0
  | succ n ih =>
      apply step; exact ih

-- Infinite descent.
-- Pierre de Fermat (1659)

def descNat  {p : Nat -> Prop}
      (np0 : p 0 -> False)
      (down : (m : Nat) -> p (m + 1) -> p m) :
      (n : Nat) -> p n -> False
  | 0, p0 => np0 p0
  | k + 1, pn =>
      descNat np0 down k (down k pn)

def descNat_by  {p : Nat -> Prop}
      (np0 : p 0 -> False)
      (down : (m : Nat) -> p (m + 1) -> p m) :
      (n : Nat) -> p n -> False := by
  intro n pn
  induction n with
  | zero => exact np0 pn
  | succ n ih => exact ih (down n pn)
  done

namespace plus_lz_1

def plus_lz : (n : Nat) -> 0 + n = n :=
  indNat
    (rfl : 0 + 0 = 0)
    (fun _ => congrArg (· + 1) : (m : Nat) -> 0 + m = m -> 0 + (m + 1) = m + 1)

end plus_lz_1

namespace plus_lz_2

def plus_lz : (n : Nat) -> 0 + n = n := fun
  | 0 =>
      show 0 + 0 = 0 from
      rfl
  | k + 1 =>
      show 0 + (k + 1) = k + 1 from
      show (0 + k) + 1 = k + 1 from
        congrArg (· + 1) $
      show 0 + k = k from
        plus_lz k

end plus_lz_2

namespace plus_lz_3

def plus_lz : (n : Nat) -> 0 + n = n := fun
  | 0 => by
      have : 0 + 0 = 0 := rfl
      exact this
  | k + 1 => by
      have : 0 + k = k             := plus_lz k
      have : (0 + k) + 1 = k + 1   := congrArg (· + 1) this
      have : 0 + (k + 1) = k + 1   := this
      exact this

end plus_lz_3

namespace plus_lz_4

def plus_lz : (n : Nat) -> 0 + n = n
  | 0 =>
      calc 0 + 0 = 0   := rfl
  | k + 1 =>
      calc 0 + (k + 1)
      _ = (0 + k) + 1  := rfl
      _ = k + 1        := congrArg (· + 1) (plus_lz k)

end plus_lz_4

namespace neq_n_succ_n_1

def neq_n_sn : (n : Nat) -> n = n + 1 -> False :=
  descNat
    (fun h : 0 = 0 + 1 => nomatch h)
    (fun _ => congrArg Nat.pred :
      (m : Nat) -> m + 1 = m + 1 + 1 -> m = m + 1)

end neq_n_succ_n_1

namespace neq_n_succ_n_2

def neq_n_sn : (n : Nat) -> n = n + 1 -> False
  | 0, h =>
      nomatch (h : 0 = 0 + 1)
  | k + 1, h =>
      show False from
        neq_n_sn k $
      show k  = k + 1 from
        congrArg Nat.pred $
      show k + 1 = k + 1 + 1 from
        h

end neq_n_succ_n_2

namespace neq_n_succ_n_3

def neq_n_sn : (n : Nat) -> n = n + 1 -> False
  | 0, h => by
      cases h
  | k + 1, h => by
      have : k = k + 1 := congrArg Nat.pred h
      show False
      apply neq_n_sn k this

end neq_n_succ_n_3

--
-- Even & Odd
--

mutual

  @[aesop safe [constructors, cases]]
  inductive Even : Nat -> Prop where
    | ev0 : Even 0
    | ev1 {n} : Odd n -> Even (n + 1)

  @[aesop safe [constructors, cases]]
  inductive Odd : Nat -> Prop where
    | odd {n} : Even n -> Odd (n + 1)

end

open Even Odd

def odd_1 : Odd 1 := by
  -- aesop
  apply odd
  apply ev0

def even_2 : Even 2 := by
  -- aesop
  apply ev1
  apply odd
  apply ev0

-- Inversion.

-- @[aesop unsafe [apply]]
def odd_z : Odd 0 -> False := by
  intro h; cases h

-- @[aesop unsafe [apply]]
def even_s {n : Nat} : Even (n + 1) -> Odd n
  | ev1 odd_n => odd_n

-- @[aesop unsafe [apply]]
def odd_s {n : Nat} : Odd (n + 1) -> Even n
  | odd even_n => even_n

def not_odd_0 (h : Odd 0) : False := by
  -- aesop
  obtain @⟨n, a⟩ := h

def not_even_1 (h : Even 1) : False := by
  -- aesop
  rcases h with ⟨⟩ | @⟨n, a⟩
  obtain @⟨n, a_1⟩ := a

def not_odd_2 (h : Odd 2) : False := by
  -- aesop
  obtain @⟨n, a⟩ := h
  simp_all only [Nat.zero_add]
  rcases a with ⟨⟩ | @⟨n, a_1⟩
  obtain @⟨n, a⟩ := a_1


-- "Ordinary" induction.
-- (n : Nat) -> Even (n + n)

namespace Even_dbl_1

def even_dbl : (n : Nat) -> Even (n + n)
  | 0 =>
      show Even (0 + 0) from
      show Even 0 from
        ev0
  | k + 1 =>
      show Even ((k + 1) + (k + 1)) from
      show Even (((k + 1) + k) + 1) from
        Eq.subst (motive := Even ∘ .succ) (Eq.symm $ Nat.succ_add k k) $
      show Even ((k + k) + 2) from
        (ev1 ∘ odd) $
      show Even (k + k) from
        even_dbl k

end Even_dbl_1

namespace Even_dbl_2

def even_dbl : (n : Nat) -> Even (n + n)
  | 0 =>
      ev0 |>
      Eq.subst rfl
  | k + 1 =>
      even_dbl k |>
      (ev1 ∘ odd) |>
      Eq.subst (motive := Even ∘ .succ) (Eq.symm $ Nat.succ_add k k)

end Even_dbl_2

namespace Even_dbl_3

def even_dbl : (n : Nat) -> Even (n + n)
  | 0 =>
      have : Even 0 := ev0
      have : Even (0 + 0) := this
      this
  | k + 1 =>
      have : Even (k + k) := even_dbl k
      have : Even ((k + k) + 2) := (ev1 ∘ odd) this
      have : Even (((k + 1) + k) + 1) :=
        Eq.subst (motive := Even ∘ .succ) (Eq.symm $ Nat.succ_add k k) this
      have : Even ((k + 1) + (k + 1)) := this
      this

end Even_dbl_3

namespace Even_dbl_4

def even_dbl : (n : Nat) -> Even (n + n)
  | 0 => by
      simp; exact ev0
  | k + 1 => by
      show Even ((k + 1) + (k + 1))
      show Even (((k + 1) + k) + 1)
      rw [Nat.succ_add]
      show Even ((k + k) + 2)
      apply ev1 ∘ odd
      show Even (k + k)
      apply even_dbl k

end Even_dbl_4

namespace Even_dbl_5

def even_dbl (n : Nat) : Even (n + n) := by
  induction n with
  | zero =>
      -- aesop
      rw [Nat.add_zero]
      exact ev0
  | succ k h =>
      rw [Nat.succ_add]
      -- aesop
      apply ev1
      apply odd
      exact h

end Even_dbl_5

-- "Infinite descent" in style of Fermat.
-- (n : Nat) -> Odd (n + n) -> False

namespace Odd_dbl_1

def not_odd_dbl : (n : Nat) -> Odd (n + n) -> False
  | 0, h => by
      cases h
  | k + 1, h =>  not_odd_dbl k $
      show Odd (k + k) from
        even_s $
      show Even ((k + k) + 1) from
        odd_s $
      show Odd ((k + k) + 2) from
      show Odd ((k + (k + 1)) + 1) from
        Eq.subst (motive := Odd ∘ .succ) (Nat.succ_add k k) $
      show Odd ((k + 1) + (k + 1)) from h


end Odd_dbl_1

namespace Odd_dbl_2

def not_odd_dbl : (n : Nat) -> Odd (n + n) -> False
  | 0, h =>
      have : Odd (0 + 0) := h
      have : Odd 0 := this
      nomatch this
  | k + 1, h =>
      have : Odd ((k + 1) + (k + 1)) := h
      have : Odd (((k + 1) + k) + 1) := this
      have : Odd ((k + k) + 2) :=
         Eq.subst (motive := Odd ∘ .succ) (Nat.succ_add k k) this
      have : Odd (k + k) := (even_s ∘ odd_s) this
      show False from not_odd_dbl k this

end Odd_dbl_2

namespace Odd_dbl_3

def not_odd_dbl : (n : Nat) -> Odd (n + n) -> False
  | 0, h => nomatch (h : Odd (0 + 0))
  | k + 1, h =>
      h |>
      Eq.subst (motive := Odd ∘ .succ) (Nat.succ_add k k) |>
      (even_s ∘ odd_s) |>
      not_odd_dbl k

end Odd_dbl_3

namespace Odd_dbl_4

def not_odd_dbl : (n : Nat) -> Odd (n + n) -> False
  | 0, h => by
      nomatch (h : Odd (0 + 0))
  | .succ k, h => by
      apply not_odd_dbl k
      apply even_s
      apply odd_s
      show Odd ((k + k).succ.succ)
      rw [<- Nat.add_succ k k, <- Nat.succ_add]
      exact h

end Odd_dbl_4

namespace Odd_dbl_5

def not_odd_dbl (n : Nat) (h : Odd (n + n)) : False := by
  induction n with
  | zero => nomatch (h : Odd (0 + 0))
  | succ k ih =>
      apply ih
      apply even_s
      apply odd_s
      show Odd ((k + k).succ.succ)
      rw [<- Nat.add_succ k k, <- Nat.succ_add]
      exact h

end Odd_dbl_5

-- (n : Nat) -> Even n ∨ Odd n

namespace EvenOrOdd_1

def  even'odd : (n : Nat) -> Even n ∨ Odd n
  | .zero => Or.inl ev0
  | .succ 0 => Or.inr $ odd ev0
  | .succ (.succ k) =>
      match even'odd k with
      | .inl even_k => Or.inl $ ev1 (odd even_k)
      | .inr odd_k  => Or.inr $ odd (ev1 odd_k)

end EvenOrOdd_1

namespace EvenOrOdd_2

def  even'odd : (n : Nat) -> Even n ∨ Odd n
  | .zero => Or.inl ev0
  | .succ 0 => Or.inr $ odd ev0
  | .succ (.succ k) =>
      Or.elim (even'odd k) (Or.inl ∘ ev1 ∘ odd) (Or.inr ∘ odd ∘ ev1)

end EvenOrOdd_2

namespace EvenOrOdd_3

def even'odd : (n : Nat) -> Even n ∨ Odd n
  | .zero => Or.inl ev0
  | .succ k =>
      Or.elim (even'odd k) (Or.inr ∘ odd) (Or.inl ∘ ev1)

end EvenOrOdd_3

namespace EvenOrOdd_4

def even'odd : (n : Nat) -> Even n ∨ Odd n
  | .zero => Or.inl ev0
  | .succ k => by
      apply Or.elim (even'odd k)
      · intro even_k
        apply Or.inr
        exact odd even_k
      · intro odd_k
        apply Or.inl
        exact ev1 odd_k

end EvenOrOdd_4

namespace EvenOrOdd_5

def even'odd : (n : Nat) -> Even n ∨ Odd n :=
  indNat (Or.inl ev0)
    (fun _ h => Or.elim h (Or.inr ∘ odd) (Or.inl ∘ ev1))

end EvenOrOdd_5

-- "Infinite descent" in style of Fermat.
-- (m : Nat) -> (Even m ∧ Odd m) -> False

namespace Even_Odd_1

def not_even_odd : (m : Nat) -> (Even m ∧ Odd m) -> False := fun
  | .zero, h =>
      nomatch (h.right : Odd 0)
  | .succ k, h =>
      not_even_odd k $ ⟨odd_s h.right, even_s h.left⟩

end Even_Odd_1

namespace Even_Odd_2

def not_even_odd : (m : Nat) -> Even m -> Odd m -> False
  | .zero, _, odd_0 =>
      nomatch odd_0
  | .succ k, even_sk, odd_sk =>
       not_even_odd k (odd_s odd_sk) (even_s even_sk)

end Even_Odd_2
