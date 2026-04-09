/-
  This has been produced by rewriting the Coq code by
  Pierre Corbineau in
    http://www-verimag.imag.fr/~corbinea/ftp/programs/sqrt2.v

  There is no m and n such that
    n ≠ 0 and m² ≡ 2 * n²
  Hence, sqrt 2 is irrational.
-/

import Batteries
import Aesop

-- Reasoning by implication

def «⇒» (p q : Prop) : Prop :=
  p -> q

instance impTrans : Trans «⇒» «⇒» «⇒» where
  trans pq qr := qr ∘ pq

infixr:20 " ⇒ " => «⇒»

-- Lemmas

@[simp]
def dbl (n : Nat) := n + n

@[simp]
def sq (n : Nat) := n * n

@[simp]
def div2 (n : Nat) := Nat.div n 2

@[simp]
theorem dbl_succ (n : Nat) : dbl (n + 1) = dbl n + 2 := by
  simp only [dbl]
  omega

@[simp]
theorem div2_2 (n : Nat) : div2 (n + 2) = div2 n + 1 := by
  apply Nat.add_div_right
  omega

@[simp]
theorem div2_dbl (n : Nat) : div2 (dbl n) = n := by
  induction n with
  | zero =>
      show div2 (dbl 0) / 2 = 0
      rfl
  | succ k ih =>
      calc
        div2 (dbl (k + 1))
    _ = div2 ((dbl k) + 2)  := congrArg div2 (dbl_succ k)
    _ = div2 (dbl k) + 1    := div2_2 (dbl k)
    _ = k + 1                  := congrArg Nat.succ ih

@[simp]
theorem div2_le (n : Nat) (nn0 : n ≠ 0) : div2 n < n := by
  apply Nat.div_lt_self
  · omega
  · omega

theorem dbl_inj {n m : Nat} (h : dbl n = dbl m) : n = m := by
  calc
      n
  _ = div2 (dbl n) := Eq.symm (div2_dbl n)
  _ = div2 (dbl m) := congrArg div2 h
  _ = m               := div2_dbl m

example (n m : Nat) : dbl n = dbl m -> n = m := calc
      dbl n = dbl m
  _ ⇒ div2 (dbl n) = div2 (dbl m) := congrArg div2
  _ ⇒ n = div2 (dbl m) :=
      Eq.subst (motive := (· = div2 (dbl m))) (div2_dbl n)
  _ ⇒ n = m :=
      Eq.subst (motive := (n = ·)) (div2_dbl m)

example (n m : Nat) (h : dbl n = dbl m) : n = m :=
  have : div2 (dbl n) = div2 (dbl m) :=
    congrArg div2 h
  have : n = div2 (dbl m) :=
    Eq.subst (motive := (· = div2 (dbl m))) (div2_dbl n) this
  show n = m from
    Eq.subst (motive := (n = ·)) (div2_dbl m) this

@[simp]
theorem dbl_mult_l (n m : Nat) : dbl (n * m) = n * dbl m := calc
      dbl (n * m)
  _ = n * m + n * m := rfl
  _ = n * (m + m) := by rw [Nat.left_distrib]
  _ = n * dbl m := rfl

@[simp]
theorem dbl_mult_r (n m : Nat) : dbl (n * m) = dbl n * m := calc
    dbl (n * m)
  _ = n * m + n * m := rfl
  _ = (n + n) * m := by rw [Nat.right_distrib]
  _ = dbl n * m := rfl

mutual

  @[aesop unsafe [constructors]]
  inductive Even : Nat -> Prop where
    | even0  : Even 0
    | even1 {n} : Odd n -> Even (n + 1)

  @[aesop unsafe [constructors]]
  inductive Odd : Nat -> Prop where
    | odd1 {n} : Even n -> Odd (n + 1)

end
open Even Odd

@[simp]
theorem even_or_odd : (n : Nat) -> Even n ∨ Odd n
  | 0 =>
      show Even 0 ∨ Odd 0 from
      Or.inl even0
  | k + 1 =>
      show Even (k + 1) ∨ Odd (k + 1) from
      match even_or_odd k with
      | .inl even_k => Or.inr $ odd1 even_k
      | .inr odd_k => Or.inl $ even1 odd_k

@[simp]
theorem not_odd_0 (odd_0 : Odd 0) : False := by
  nomatch odd_0

@[simp]
theorem not_even_and_odd : (n : Nat) -> Even n -> Odd n -> False
  | 0, even_0, odd_0 => not_odd_0 odd_0
  | k + 1, even_k1, odd_k1 => by
      cases odd_k1
      cases even_k1
      rename_i even_k odd_k
      apply not_even_and_odd k even_k odd_k

@[simp]
theorem even_dbl : (n : Nat) -> Even (dbl n)
  | 0 =>
      show Even (dbl 0) from
      even0
  | 1 =>
      show Even (dbl 1) from
      even1 $ odd1 even0
  | k + 2 => even_dbl k |> calc
          Even (dbl k)
      _ ⇒ Even (dbl k + 2) := even1 ∘ odd1
      _ = Even (dbl (k + 1)) := congrArg Even (Eq.symm $ dbl_succ k)
      _ ⇒ Even (dbl (k + 1) + 2) := even1 ∘ odd1
      _ = Even (dbl (k + 2)) := congrArg Even (Eq.symm $ dbl_succ (k + 1))

@[simp]
theorem dbl_div2 {n} : Even n -> dbl (div2 n) = n
  | .even0 =>
      show dbl (div2 0) = 0 from
      rfl
  | .even1 (.odd1 (n := k) even_k) =>
      show dbl (div2 (k + 2)) = k + 2 from
      calc
          dbl (div2 (k + 2))
      _ = dbl (div2 k + 1)     := congrArg dbl (div2_2 k)
      _ = dbl (div2 k) + 2     := dbl_succ (div2 k)
      _ = k + 2                   := congrArg (· + 2) (dbl_div2 even_k)

mutual

@[simp]
theorem even_even_add {m n} (even_m : Even m) (even_mn : Even (m + n)) : Even n :=
  match n with
  | 0 => even0
  | _ + 1 =>
      match even_mn with
      | even1 odd_mn' =>
          even1 (even_odd_odd even_m odd_mn')

theorem even_odd_odd {m n} (even_m : Even m) (odd_mn : Odd (m + n)) : Odd n :=
  match n with
  | 0 => by
      simp at odd_mn; exfalso
      exact not_even_and_odd m even_m odd_mn
  | _ + 1 =>
      match odd_mn with
      | .odd1 even_mn' => odd1 (even_even_add even_m even_mn')

end

@[simp]
theorem odd_even_mult {m n} : Odd m -> Even (m * n) -> Even n
  | .odd1 even0 => calc
        Even ((0 + 1) * n)
    _ ⇒ Even n                   := Eq.subst (by simp)
  | .odd1 (.even1 (n := m) odd_m) => calc
        Even ((m + 1 + 1) * n)
    _ ⇒ Even ((n + n) + m * n)   := Eq.subst (by grind)
    _ ⇒ Even (m * n)             := even_even_add (even_dbl n)
    _ ⇒ Even n                   := odd_even_mult odd_m

@[simp]
theorem even_sq_is_even {n} (even_sq : Even (sq n)) : Even n := by
  cases even_or_odd n with
  | inl even_n =>
      exact even_n
  | inr odd_n =>
      exact odd_even_mult odd_n even_sq

@[simp]
theorem sq_0 {n} (nn0 : sq n = 0) : n = 0 :=
  match n with
  | 0 => rfl
  | n' + 1 => by nomatch nn0

@[simp]
theorem dbl2_sq_div2_sq (n : Nat) (even_n : Even n) : dbl (dbl (sq (div2 n))) = sq n
  := calc
      dbl (dbl (sq (div2 n)))
  _ = dbl (dbl (div2 n * div2 n))
        := rfl
  _ = dbl (div2 n * dbl (div2 n))
        := congrArg dbl (dbl_mult_l (div2 n) (div2 n))
  _ = dbl (div2 n) * dbl (div2 n)
        := dbl_mult_r (div2 n) (dbl (div2 n))
  _ = sq n
        := congrArg₂ (· * ·) (dbl_div2 even_n) (dbl_div2 even_n)

--
-- The most sophisticated part:
--   m² = 2 * p² ⇒ p = 0.
-- The proof is by reducing the problem to a "smaller" one:
--   (m/2)² = 2 * (p/2)² ⇒ p/2 = 0
--

@[simp]
theorem descent (m p : Nat) (mm2pp : sq m = dbl (sq p)) : p = 0 :=
  if m0 : m = 0 then
    Eq.symm mm2pp |> calc
        dbl (sq p) = sq m
    _ ⇒ dbl (sq p) = 0      := by subst m0; simp; exact id
    _ ⇒ dbl (sq p) = dbl 0  := by simp; exact id
    _ ⇒ sq p = 0            := dbl_inj
    _ ⇒ p = 0               := sq_0
  else
    let n := div2 m
    let q := div2 p

    have even_m : Even m :=
      have : Even (dbl (sq p)) := even_dbl (sq p)
      this |> calc
          Even (dbl (sq p))
      _ = Even (sq m)
            := congrArg Even (Eq.symm mm2pp)
      _ ⇒ Even m
            := even_sq_is_even

    have : dbl (dbl (sq n)) = sq m :=
      dbl2_sq_div2_sq m even_m

    have dbl2_sq_n : dbl (dbl (sq n)) = dbl (sq p) := calc
        dbl (dbl (sq n))
      _= sq m         := this
      _= dbl (sq p)   := mm2pp

  have : dbl (sq n) = sq p :=
    dbl_inj dbl2_sq_n

    have even_p : Even p :=
      even_dbl (sq n) |> calc
          Even (dbl (sq n))
      _ = Even (sq p)      :=  congrArg Even this
      _ ⇒ Even p           :=  even_sq_is_even

    have dbl2_sq_n_dbl3_sq_q : dbl (dbl (sq n)) = dbl (dbl (dbl (sq q))) := calc
          dbl (dbl (sq n))
      _ = dbl (sq p)
            := dbl2_sq_n
      _ = dbl (dbl (dbl (sq q)))
            := congrArg dbl (Eq.symm $ dbl2_sq_div2_sq p even_p)

    have ih : sq n = dbl (sq q) :=
      dbl_inj (dbl_inj dbl2_sq_n_dbl3_sq_q)

    have q0 : q = 0 :=
      have : div2 m < m := div2_le m m0
      descent n q ih

    have p0 : p = 0 := calc
          p
      _ = dbl (div2 p) := Eq.symm $ dbl_div2 even_p
      _ = dbl q        := rfl
      _ = dbl 0        := congrArg dbl q0
      _ = 0            := rfl

    p0

--  There is no m and n such that
--    n ≢ 0 and m^2 ≡ 2*n^2
--  Hence, sqrt 2 is irrational.

theorem irrational_sqrt2 (m n : Nat) (nn0 : n ≠ 0) : ¬ sq m = dbl (sq n) :=
  fun h : sq m = dbl (sq n) =>
  have n0 : n = 0 := descent m n h
  show False from
  nn0 n0
