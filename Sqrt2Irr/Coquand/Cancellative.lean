--
-- Sqrt2Irr.Coquand.Cancellative
--

/-
The original proof is written by Thierry Coquand.
http://www.cs.ru.nl/~freek/comparison/comparison.pdf
-/

--
-- Cancellative Abelian Monoid
--

class CAMonoid (α : Type) where

  op : α -> α -> α
  neutral : α

  op_assoc : (l c r : α) ->
    op l (op c r) = op (op l c) r

  op_comm : (l r : α) ->
    op l r = op r l

  neutral_op : (x : α) ->
    op neutral x = x

  op_left_cancel : (z x y : α) ->
    op z x = op z y -> x = y

infix:70 " <.> " => CAMonoid.op
