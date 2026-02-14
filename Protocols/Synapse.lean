--
-- Synapse
--

import Batteries

abbrev State := Nat × Nat × Nat

inductive Reachable : State -> Prop where
  | start {i} : Reachable (i, 0, 0)
  | t1 {i d v} : Reachable (i + 1, d, v) -> Reachable (i + d, 0, v + 1)
  | t2 {i d v} : Reachable (i, d, v + 1) -> Reachable (i + d + v, 1, 0)
  | t3 {i d v} : Reachable (i + 1, d, v) -> Reachable (i + d + v, 1, 0)

inductive Unsafe : State -> Prop where
  | u1 {i d v} : Unsafe (i, d + 1, v + 1)
  | u2 {i d v} : Unsafe (i, d + 2, v)

inductive Config : State -> Prop where
  | c1 {i} : Config (i, 0 + 1, 0)
  | c2 {i v} : Config (i, 0, v)

open Reachable Unsafe Config

--
-- A proof of `valid` that mimics a proof by supercompilation.
--

-- Any reachable state is covered by a configuration

def inclusion: {s : State} -> Reachable s -> Config s := by
  intro s r
  cases r with
  | start => exact c2
  | t1 _ => exact c2
  | t2 _ => exact c1
  | t3 _ => exact c1


-- Any state, that is covered by a configuration, is not unsafe.

def safety : {s : State} -> Config s -> Unsafe s -> False := by
  intro s c u
  cases c with
  | c1 => cases u
  | c2 => cases u

-- Any reachable state is not unsafe.

def valid : {s : State} -> Reachable s -> Unsafe s -> False :=
  safety ∘ inclusion

--
-- A direct proof, which is mysterious...
--

def valid' : {s : State} -> Reachable s -> Unsafe s -> False := by
  intro s r u
  induction r with
  | start => cases u
  | t1 _ _ => cases u
  | t2 _ _ => cases u
  | t3 _ _ => cases u
