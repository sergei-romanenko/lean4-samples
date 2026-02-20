--
-- MOESI
--

import Batteries

abbrev State := Nat × Nat × Nat × Nat × Nat

inductive Reachable : State -> Prop where
  | start {i} : Reachable (i, 0, 0, 0, 0)
  | t1 {i m s e o'} : Reachable (i + 1, m, s, e, o') ->
      Reachable (i, 0, (s + e) + 1, 0, m + o')
  | t2 {i m s e o'} : Reachable (i, m, s, e + 1, o') ->
      Reachable (i, m + 1, s, e, o')
  | t3 {i m s e o'} : Reachable (i, m, s + 1, e, o') ->
      Reachable (i + m + s + e + o', 0, 0, 1, 0)
  | t4 {i m s e o'} : Reachable (i + 1, m, s, e, o') ->
      Reachable (i + m + s + e + o', 0, 0, 1, 0)

inductive Unsafe : State -> Prop where
  | u1  {i m s e o'} : Unsafe (i, m + 1, s + 1, e, o')
  | u2  {i m s e o'} : Unsafe (i, m + 1, s, e + 1, o')
  | u3  {i m s e o'} : Unsafe (i, m + 1, s, e, o' + 1)
  | u4  {i m s e o'} : Unsafe (i, m + 2, s, e, o')
  | u5  {i m s e o'} : Unsafe (i, m, s, e + 2, o')

inductive Config : State -> Prop where
  | c1 : Config (_, 0, 0, 1, 0)
  | c2 : Config (_, 1, 0, 0, 0)
  | c3 : Config (_, 0, _, 0, _)

open Reachable Unsafe Config

--
-- A proof of `valid` that mimics a proof by supercompilation.
--

-- Any reachable state is covered by a configuration

theorem inclusion {s : State} (r : Reachable s) : Config s := by
  induction r with
  | start  | t1 _ _ => exact c3
  | t3 _ _ | t4 _ _ => exact c1
  | t2 _ ih =>
      cases ih; simp; exact c2

-- Any state, that is covered by a configuration, is not unsafe.

theorem safety {s : State} (c : Config s) (u : Unsafe s) : False := by
  cases c <;> cases u

-- Any reachable state is not unsafe.

theorem valid : {s : State} -> Reachable s -> Unsafe s -> False :=
  safety ∘ inclusion

--
-- A direct proof, which is mysterious...
--

/-
-- This is in Idris 2:

valid': (r : Reachable s) -> (u : Unsafe s) -> Void
valid' (t2 (t2 r)) u1 = valid' r u5
valid' (t2 r) u2 = valid' r u5
valid' (t2 (t2 r)) u3 = valid' r u5
valid' (t2 r) u4 = valid' r u2
valid' (t2 r) u5 = valid' r u5
 -/

theorem valid'{s : State} (r : Reachable s) (u : Unsafe s) : False := by
  induction r with
  | t2 r' h' =>
      apply h'
      cases r' with
      | t2 _ => cases u <;> exact u2
      | _ => cases u
  | _ => cases u
