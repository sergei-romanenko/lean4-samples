-- Induction
import Batteries

-- Induction by data

theorem ind_nat {P : Nat -> Prop}
    (h0 : P 0) (ih : (n : Nat) -> P n → P (n + 1)) : (n : Nat) -> P n
  | 0 =>
      show P 0 from h0
  | n' + 1 =>
      show P (n' + 1) from
      have hpn : P n' := ind_nat h0 ih n'
      ih n' hpn

theorem ind_nat_by {P : Nat -> Prop}
    (h0 : P 0) (ih : (n : Nat) -> P n → P (n + 1)) : (n : Nat) -> P n := by
  intro n
  induction n with
  | zero =>
      show P 0
      exact h0
  | succ n' h =>
      show P (n' + 1)
      exact ih n' h

-- Induction by derivation

namespace IndEven

inductive Even : Nat -> Prop where
  | even0 : Even 0
  | even2 : {k : Nat} -> Even k -> Even (k + 2)

open Even

def ev0 : Even 0 := even0
def ev2 : Even 2 := even2 even0
def ev4 : Even 4 := even2 (even2 even0)

theorem even2_inv (n : Nat) : Even (n + 2) -> Even n
  | even2 ev_n => ev_n

theorem even_mod2eq0 (n : Nat) : Even n -> n % 2 = 0
  | @even0 => show 0 % 2 = 0 from rfl
  | @even2 k ev_k => by
      show (k + 2) % 2 = 0
      simp
      show k % 2 = 0
      have : Even k -> k % 2 = 0 := even_mod2eq0 k
      exact this ev_k

theorem even_mod2eq0' (n : Nat) : Even n -> n % 2 = 0 := by
  intro ev_n
  induction ev_n with
  | @even0 => show 0 % 2 = 0; rfl
  | @even2 k ev_k ih =>
      show (k + 2) % 2 = 0
      simp
      show k % 2 = 0
      exact ih

def ev2n : (n : Nat) → Even (n + n)
  | .zero => even0
  | .succ n =>
      have ev2n_n : Even (n + n) := ev2n n
      have eq : (n.succ + n.succ = (n + n).succ.succ) := by
        calc n.succ + n.succ
        _ = (n.succ + n).succ
          := by rfl
        _ = (n + n).succ.succ
          := by rw [Nat.succ_add]
      Eq.subst (Eq.symm eq) (even2 ev2n_n)

def impl (p q : Prop) : Prop :=
  p -> q

def ev2n_chain : (n : Nat) -> Even (n + n) := fun
  | .zero =>
      have : Even .zero := even0
      show Even (.zero + .zero) from this
  | .succ n =>
      have : Even (n + n) :=
        ev2n_chain n
      have : Even ((n + n).succ.succ) :=
        even2 this
      have : Even ((n.succ + n).succ) :=
        Eq.subst (by rw [Nat.succ_add]) this
      show Even (n.succ + n.succ) from
        this

instance impTrans : Trans impl impl impl where
  trans pq qr := fun p => qr (pq p)

infixr:20 " ~~> " => impl

example {p q r} (h1 : p -> q) (h2 : q -> r) : p -> r :=
  calc p
  _ ~~> r := by
    intro hp
    exact h2 (h1 hp)

def ev2n_calc : (n : Nat) -> Even (n + n)
  | 0 => even0
  | n + 1 => ev2n_calc n |>
      calc Even (n + n)
      _ ~~> Even ((n + n).succ.succ)
        := even2
      _ ~~> Even ((n.succ + n).succ)
        := Eq.subst (by rw [Nat.succ_add])
      _ ~~> Even (n.succ + n.succ)
        := id

end IndEven

namespace IndEvenOdd

mutual

  inductive Even : Nat -> Prop where
    | even0 : Even 0
    | even1 {k} : Odd k -> Even (k + 1)

  inductive Odd : Nat -> Prop where
    | odd1 {k} : Even k -> Odd (k + 1)

end

open Even Odd

def odd_1 : Odd 1 :=
  have : Even 0 := even0
  have : Odd 1 := odd1 this
  this

def even_2 : Even 2 := -- even1 (odd1 even0)
  have : Even 0 := even0
  have : Odd 1 := odd1 this
  have : Even 2 := even1 this
  this

-- Uninhabited...

def not_odd_Z (h : Odd 0) : False := by
  cases h

def not_odd_Z' (h : Odd 0) : False :=
  nomatch h

-- Inversion.

def even_pred {n} : Even (n + 1) -> Odd n
  | even1 odd_n => odd_n

def odd_pred {n} : Odd (n + 1) -> Even n
  | odd1 even_n => even_n

mutual

  def even_even {m n} : Even m -> Even n -> Even (m + n)
    | em, @even0 => em
    | em, @even1 n' on' => by
        show Even (m + (n' + 1))
        apply even1
        show Odd (m + n')
        apply even_odd em on'

  def even_odd {m n} : Even m -> Odd n -> Odd (m + n)
    | em, @odd1 n' en' => by
        show Odd (m + (n' + 1))
        apply odd1
        show Even (m + n')
        apply even_even em en'

end

end IndEvenOdd
