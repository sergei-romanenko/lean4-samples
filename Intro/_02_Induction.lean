-- Induction

-- Induction by data

theorem ind_nat {P : Nat -> Prop}
    (h0 : P 0) (ih : (n : Nat) -> P n → P (n + 1)) : (n : Nat) -> P n
  | 0 =>
      show P 0 from h0
  | n + 1 =>
      show P (n + 1) from
      have hpn : P n := ind_nat h0 ih n
      ih n hpn

-- Induction by derivation

inductive Even : Nat -> Prop where
  | even0 : Even 0
  | even2 : {k : Nat} -> Even k -> Even (k + 2)

open Even

def ev0 : Even 0 := even0
def ev2 : Even 2 := even2 even0
def ev4 : Even 4 := even2 (even2 even0)

theorem even2_inv (n : Nat) : Even (n + 2) -> Even n
  | even2 even_n => even_n

theorem even_mod2eq0 (n : Nat) : Even n -> n % 2 = 0
  | @even0 => show 0 % 2 = 0 from rfl
  | @even2 k even_k => by
      show (k + 2) % 2 = 0
      simp
      show k % 2 = 0
      exact even_mod2eq0 k even_k

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
