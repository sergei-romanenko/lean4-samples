import Batteries
import Aesop

import Sqrt2Irr.Coquand.Misc

mutual

  @[aesop unsafe [constructors, cases]]
  inductive Even : Nat -> Prop where
    | even0  : Even 0
    | even1 : {n : Nat} -> Odd n -> Even (n + 1)

  @[aesop unsafe [constructors, cases]]
  inductive Odd : Nat -> Prop where
    | odd1 : {n : Nat} -> Even n -> Odd (n + 1)

end
open Even Odd

def even'odd : (n : Nat) -> Even n ∨ Odd n
  | 0 =>
      Or.inl even0
  | k + 1 =>
      Or.elim (even'odd k) (Or.inr ∘  odd1) (Or.inl ∘ even1)

def even_mul_2 : (n : Nat) -> Even (2 * n)
  | 0 => even0
  | 1 => even1 (odd1 even0)
  | k + 2 => even_mul_2 k |> calc
        Even (2 * k)
    _ ⇒ Even (2 * k + 2)        := even1 ∘ odd1
    _ = Even (2 * (k + 1))      := rfl
    _ ⇒ Even (2 * (k + 1) + 2)  := even1 ∘ odd1
    _ = Even (2 * (k + 2))      := rfl

def even_dbl : (n : Nat) -> Even (n + n)
  | 0 => even0
  | 1 => even1 (odd1 even0)
  | k + 2 => even_dbl k |> calc
          Even (k + k)
      _ ⇒ Even ((k + k) + 2) := even1 ∘ odd1
      _ = Even ((k + (k + 1)) + 1) := rfl
      _ = Even ((k + 1) + (k + 1)) := congrArg Even (Eq.symm $ Nat.succ_add k (k + 1))
      _ ⇒ Even (((k + 1) + (k + 1)) + 2) := even1 ∘ odd1
      _ = Even (((k + 1) + (k + 2)) + 1) := rfl
      _ = Even ((k + 2) + (k + 2)) := congrArg Even (Eq.symm $ Nat.succ_add (k + 1) (k + 2))

def even_even_add (m : Nat) : (n : Nat) -> Even n -> Even (m + n) -> Even m
  | 0, even0 => calc
          Even (m + 0)
      _ = Even m := rfl
      _ ⇒ Even m := id
  | n + 2, even1 (odd1 even_n) => calc
          Even (m + (n + 2))
      _ = Even ((m + n) + 2)  := rfl
      _ ⇒ Odd ((m + n) + 1)   := fun | even1 h => h
      _ ⇒ Even (m + n)        := fun | odd1 h => h
      _ ⇒ Even m              := even_even_add m n even_n

def odd_even_mul (m : Nat) : (n : Nat) -> Odd n -> Even (m * n) -> Even m
  | 1, odd1 even0 => calc
          Even (m * 1)
      _ = Even m      := congrArg Even (Nat.mul_one m)
      _ ⇒ Even m      := id
  | n + 2, odd1 (even1 odd_n) => calc
          Even (m * (n + 2))
      _ = Even (((m * n) + m) + m)  := by rfl
      _ = Even ((m * n) + (m + m))  := congrArg Even (Nat.add_assoc (m * n) m m)
      _ ⇒ Even (m * n)              := even_even_add (m * n) (m + m) (even_dbl m)
      _ ⇒ Even m                    := odd_even_mul m n odd_n

-- 2 divides n

def D2 (n : Nat) : Prop :=
  ∃ x, 2 * x = n

def even_d2 : (n : Nat) -> Even n -> D2 n
  | 0, even0 =>
      ⟨0, (rfl : 2 * 0 = 0)⟩
  | n + 2, even1 (odd1 even_n) => by
      have ⟨x, eq_2x_n⟩ : ∃ x, 2 * x = n := even_d2 n even_n
      suffices 2 * (x + 1) = n + 2 from ⟨x + 1, this⟩
      calc
          2 * (x + 1)
      _ = 2 * x + 2 := rfl
      _ = n + 2 := (congrArg (· + 2) eq_2x_n)

def d2_even (n : Nat) : (d2_n : D2 n) -> Even n
  | ⟨x, eq_2x_n⟩ => even_mul_2 x |> calc
        Even (2 * x)
    _ = Even n := congrArg Even eq_2x_n
    _ ⇒ Even n := id

def even_mult_even'even (m n : Nat) (even_mn : Even (m * n)) : Even m ∨ Even n
  :=
  match even'odd n with
  | .inl even_n => Or.inr $ even_n
  | .inr odd_n  => Or.inl $ odd_even_mul m n odd_n even_mn

def d2mn_d2m'd2n (m n : Nat) : D2 (m * n) -> D2 m ∨ D2 n
  := calc
        D2 (m * n)
    _ ⇒ Even (m * n)      := d2_even (m * n)
    _ ⇒ (Even m ∨ Even n) := even_mult_even'even m n
    _ ⇒ (D2 m ∨ D2 n)     := (Or.elim · (Or.inl ∘ even_d2 m) (Or.inr ∘ even_d2 n))
