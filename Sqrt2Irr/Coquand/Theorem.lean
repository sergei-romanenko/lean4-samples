--
-- Sqrt2Irr.Coquand.Theorem
--

/-
The original proof was written by Thierry Coquand.
http://www.cs.ru.nl/~freek/comparison/comparison.pdf
-/

import Batteries
import Aesop

import Sqrt2Irr.Coquand.Cancellative

def Multiple {α} [CAMonoid α] (p x y : α) : Prop :=
  p <.> x = y

def Divides {α} [CAMonoid α] (x y : α) : Prop :=
  ∃ z, x <.> z = y

def Prime {α : Type} [CAMonoid α] (p : α) : Prop :=
  (x y : α) -> Divides p (x <.> y) ->
  (Divides p x) ∨ (Divides p y)

def NotSquare {α : Type} [CAMonoid α] (p : α) : Prop :=
  (x y : α) -> p <.> (x <.> x) ≠ y <.> y

theorem p_sq {α : Type} [CAMonoid α](p x : α)
      (prime_p : Prime p) (p_xx : Divides p (x <.> x)) : Divides p x
  := by
  cases prime_p x x p_xx with
  | inl p_x => exact p_x
  | inr p_x => exact p_x

section
open CAMonoid

def down {α : Type} [CAMonoid α]
  (p : α) (prime_p : Prime p) (x y : α) (p_xx_yy : p <.> (x <.> x) = y <.> y) :
    (∃ z, p <.> z = y ∧ p <.> (z <.> z) = x <.> x)
  := by
  have ⟨w, pw__y⟩: Divides p y := (p_sq p y prime_p ⟨x <.> x, p_xx_yy⟩)
  exists w
  show p <.> w = y ∧ p <.> (w <.> w) = x <.> x
  apply And.intro pw__y
  apply op_left_cancel p (p <.> (w <.> w)) (x <.> x)
  calc
        p <.> (p <.> (w <.> w))
    _ = p <.> ((p <.> w) <.> w)   := congrArg (p <.> ·) (op_assoc p w w)
    _ = p <.> (w <.> (p <.> w))   := congrArg (p <.> ·) (op_comm (p <.> w) w)
    _ = (p <.> w) <.> (p <.> w)   := op_assoc p w (p <.> w)
    _ = y <.> y                   := congrArg₂ (· <.> ·) pw__y pw__y
    _ = p <.> (x <.> x)           := Eq.symm p_xx_yy

end

-- ======
-- The main theorem which is originally proved by Thierry Coquand:
-- any prime cannot be α square of rational in cancellative
-- abelian monoid.
-- ======

theorem descent {α : Type} [CAMonoid α]
    (p : α) (prime_p : Prime p)
    (x u : α) (pxx__uu : p <.> (x <.> x) = (u <.> u)) :
    Acc (Multiple p) u -> False
  := by
  intro acc
  induction acc generalizing x with
  | intro u h ih =>
      have ⟨y, py__u, pyy_xx⟩ := down p prime_p x u pxx__uu
      have ⟨w, pw__x, pww__yy⟩ := down p prime_p y x pyy_xx
      exact ih y py__u w pww__yy

theorem main_theorem {α : Type} [CAMonoid α]
      (p : α) (prime_p : Prime p) (wfmp : WellFounded (Multiple p)) : NotSquare p
  := by
  simp [NotSquare]
  intro x u pxx_uu
  apply descent p prime_p x u pxx_uu (WellFounded.apply wfmp u)
