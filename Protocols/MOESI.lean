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

def inclusion: {s : State} -> Reachable s -> Config s := by
  intro s r
  induction r with
  | start => exact c3
  | t1 _ _ => exact c3
  | t2 r' ih =>
      cases ih with
      | c1 => simp; exact c2
  | t3 _ _ => exact c1
  | t4 _ _ => exact c1
  done

-- Any state, that is covered by a configuration, is not unsafe.

def safety: {s : State} -> Config s -> Unsafe s -> False := by
  intro s c u
  cases c with
  | c1 => cases u
  | c2 => cases u
  | c3 => cases u
  done

-- Any reachable state is not unsafe.

def valid : {s : State} -> Reachable s -> Unsafe s -> False :=
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

/-
-- Lean 4: "fail to show termination for valid'".

def valid': {s : State} -> (r : Reachable s) -> (u : Unsafe s) -> False := by
  intro s r u
  cases u with
  | u1 =>
      cases r with
      | t2 r' =>
          cases r' with
          | t2 r'' => exact valid' r'' u5
  | u2 =>
      cases r with
      | t2 r' => exact valid' r' u5
  | u3 =>
      cases r with
      | t2 r' =>
          cases r' with
          | t2 r'' =>
              exact valid' r'' u5
  | u4 =>
      cases r with
      | t2 r' => exact (valid' r' u2)
  | u5 =>
      cases r with
      | t2 r' => exact (valid r' u5)
  -/
