import Batteries

namespace NoConfusion

example (x y : Nat) (h : x.succ = y.succ) : x = y :=
  Nat.noConfusion h id

example (x y : Nat) (h : x.succ = y.succ) : x = y :=
  Nat.succ.noConfusion (x = y) x y h id

example (x y : Nat) (h : x.succ = y.succ) : x = y := by
  injection h

example (x : Nat) (h : x.succ = .zero) : False :=
  Nat.noConfusion h

example (x : Nat) (h : x.succ = .zero) : False :=
  have : Nat.noConfusionType False (Nat.succ x) Nat.zero := Nat.noConfusion h
  this

example (x : Nat) (h : x.succ = .zero) : False :=
  by cases h


def DecidableEqBool : DecidableEq Bool := by
  intro a b
  match a, b with
    | false, false => exact isTrue rfl
    | false, true => exact isFalse (Bool.noConfusion)
    | true , false => exact isFalse (by intro h; cases h)
    | true , true => exact isTrue rfl

end NoConfusion

--
-- Injectivity of `dbl`.
--

def dbl : Nat -> Nat
  | .zero => .zero
  | .succ n => (dbl n).succ.succ

-- "Correctness"

def dbl_correct : (n : Nat) -> dbl n = n + n
  | .zero => rfl
  | .succ n =>
      calc dbl n.succ
      _ = (dbl n).succ.succ  := rfl
      _ = (n + n).succ.succ  := by rw [dbl_correct]
      _ = (n.succ + n).succ  := by rw [Nat.succ_add]
      _ = n.succ + n.succ    := rfl

-- Now let us prove this:

def dbl_injective : (m n : Nat) -> dbl m = dbl n -> m = n := fun
  | .zero, .zero, h =>
      show dbl Nat.zero = dbl Nat.zero from rfl
  | .zero, .succ n, h =>
      by cases h
  | .succ m, .zero, h =>
      by cases h
  | .succ m, .succ n, h =>
      have : dbl m.succ = dbl n.succ
        := h
      have : (dbl m).succ.succ = (dbl n).succ.succ
        := this
      have : (dbl m).succ = (dbl n).succ
        := by injection this
      have : dbl m = dbl n
        := by injection this
      have : m = n
        := dbl_injective m n this
      show m.succ = n.succ
        from by rw [this]
