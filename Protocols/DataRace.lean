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

theorem inclusion {s : State} (r : Reachable s) : Config s := by
  induction r with
  | start | t2 _ _ => exact c1
  | t1 _ _ => exact c2
  | t3 _ ih | t4 _ ih =>
      cases ih; exact c1

-- Any state, that is covered by a configuration, is not unsafe.

theorem safety {s : State} (c : Config s) (u : Unsafe s) : False := by
  cases c <;> cases u

-- Any reachable state is not unsafe.

theorem valid {s : State} : Reachable s -> Unsafe s -> False :=
  safety ∘ inclusion

--
-- A direct proof, which is mysterious...
--

theorem valid' : {s : State} -> Reachable s -> Unsafe s -> False := by
  intro s r u
  induction r with
  | t3 _ ih | t4 _ ih =>
      cases u; exact (ih u1)
  | _ => cases u
