--
-- Data Race
--

import Batteries
import Aesop

abbrev State := Nat × Nat × Nat

inductive Reachable : State -> Type where
  | start {out} : Reachable (out, 0, 0)
  | t1 {out} : Reachable (out + 1, 0, 0) -> Reachable (out, 1, 0)
  | t2 {out scs} : Reachable (out + 1, 0, scs)  -> Reachable (out, 0, scs + 1)
  | t3 {out cs scs} : Reachable (out, cs + 1, scs) -> Reachable (out + 1, cs, scs)
  | t4 {out cs scs} : Reachable (out, cs, scs + 1) -> Reachable (out + 1, cs, scs)

@[simp]
def szReachable {s : State} : Reachable s -> Nat := fun
  | .start => 0
  | .t1 r => szReachable r + 1
  | .t2 r => szReachable r + 1
  | .t3 r => szReachable r + 1
  | .t4 r => szReachable r + 1

@[simp]
instance instSzReachable {s} : SizeOf (Reachable s) where
  sizeOf := szReachable

@[aesop unsafe [cases]]
inductive Unsafe : State -> Prop where
  | u1 {out cs scs} : Unsafe (out, cs + 1, scs + 1)

@[aesop unsafe [constructors, cases]]
inductive Config : State -> Prop where
  | c1 {out scs} : Config (out, 0, scs)
  | c2 {out} : Config (out, 1, 0)

open Reachable Unsafe Config

--
-- A proof of `valid` that mimics a proof by supercompilation.
--

-- Any reachable state is covered by a configuration

theorem inclusion {s : State} (r : Reachable s) : Config s := by
  induction r <;>
  -- first | constructor | rename_i r' h'; cases h'; constructor
  aesop

-- Any state, that is covered by a configuration, is not unsafe.

theorem safety {s : State} (c : Config s) (u : Unsafe s) : False := by
  -- cases c <;> cases u
  aesop

-- Any reachable state is not unsafe.

theorem valid {s : State} : Reachable s -> Unsafe s -> False :=
  safety ∘ inclusion

--
-- A direct proof, which is mysterious...
--

theorem valid' {s : State} (r : Reachable s) (u : Unsafe s) : False := by
  induction r <;> cases u <;>
    · rename_i r' h'; apply h'; constructor

theorem valid'' {s : State} (r : Reachable s) (u : Unsafe s) : False :=
  match r with
  | start => nomatch u
  | t1 _ => nomatch u
  | t2 _ => nomatch u
  | t3 r' =>
      match u with
      | u1 => valid'' r' u1
  | t4 r' =>
      match u with
      | .u1 => valid'' r' u1
-- termination_by sizeOf r
-- decreasing_by
--   · simp
--   · simp
