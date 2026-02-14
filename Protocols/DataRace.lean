--
-- Data Race
--

import Batteries

abbrev State := Nat × Nat × Nat

inductive Reachable : State -> Prop where
  | start {out} : Reachable (out, 0, 0)
  | t1 {out} : Reachable (out + 1, 0, 0) -> Reachable (out, 1, 0)
  | t2 {out scs} : Reachable (out + 1, 0, scs)  -> Reachable (out, 0, scs + 1)
  | t3 {out cs scs} : Reachable (out, cs + 1, scs) -> Reachable (out + 1, cs, scs)
  | t4 {out cs scs} : Reachable (out, cs, scs + 1) -> Reachable (out + 1, cs, scs)

inductive Unsafe : State -> Prop where
  | u1 {out cs scs} : Unsafe (out, cs + 1, scs + 1)

inductive Config : State -> Prop where
  | c1 {out scs} : Config (out, 0, scs)
  | c2 {out} : Config (out, 1, 0)

open Reachable Unsafe Config

--
-- A proof of `valid` that mimics a proof by supercompilation.
--

-- Any reachable state is covered by a configuration

def inclusion: {s : State} -> Reachable s -> Config s := by
  intro s r
  induction r with
  | start => exact c1
  | t1 _ ih => exact c2
  | t2 _ ih => exact c1
  | t3 _ ih =>
      cases ih with
      | c2 => exact c1
  | t4 _ ih =>
      cases ih with
      | c1 => exact c1

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
  | t3 _ ih =>
      cases u with
      | u1 => exact (ih u1)
  | t4 r' ih =>
      cases u with
      | u1 => exact (ih u1)
