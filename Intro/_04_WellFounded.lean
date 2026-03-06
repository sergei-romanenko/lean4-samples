---
--- WellFounded
---

import Batteries

-- The termination checker of Idris is basicly the same as that of Foetus:
--
--   Andreas Abel. 1998. foetus -- Termination Checker for Simple
--   Functional Programs. Programming Lab Report.
--   http://www2.tcs.ifi.lmu.de/~abel/foetus/

-- The termination checker of Agda inspects the parameters of recursive call.
-- In the third line, (x′ < succ x′ & y = y).

def add₁ : (x y : Nat) -> Nat
  | x, .zero => x
  | x, .succ y' => .succ (add₁ x y')

def add₂ : (x y : Nat) -> Nat
  | x, 0 => x
  | x, y' + 1 => (add₂ x y') + 1

example : add₁ 2 3 = 5 := rfl

-- The dependency relation is defined as follows:
--
--  * Constructor elimination: if cons is a constructor,
--      x < cons a1 ... an x b1 ... ε
--  * Application: if y < x then
--       y a1 ... an < x

-- Idris can find termination orders across mutually recursive functions.
-- Idris can find lexicographic termination orders.

-- There is a lexicographic order on parameters with respect
-- to the dependency order:
--   (x , y) << (x’, y’) ⇔ (x < x’ or (x ≤ x’ & y < y’))

def ack : Nat -> Nat -> Nat
  | 0, _ => 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)

--
-- But in some cases all the above is not sufficient.
--

-- Division by 2, rounded downwards.

def div2 : Nat -> Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => div2 n + 1

@[simp] theorem div2.r1 : div2 0 = 0 := rfl
@[simp] theorem div2.r2 : div2 1 = 0 := rfl
@[simp] theorem div2.r3 : div2 (n + 2) = div2 n + 1 := rfl

@[simp]
def div2le (n : Nat) : div2 n ≤ n := by
  cases n with
  | zero => simp [div2]
  | succ n' =>
      cases n' with
      | zero => simp [div2]
      | succ n'' =>
          simp
          have : div2 n'' ≤ n'' := div2le n''
          omega

@[simp]
def div2lt (n : Nat) : div2 n < n + 1 := by
  exact Nat.lt_succ_of_le (div2le n)

def log2a : (n : Nat) -> Nat
  | 0 => 0
  | 1 => 0
  | n' + 2 =>
      log2a (div2 n' + 1) + 1

#guard [0, 1, 2, 3, 4].map log2a == [0, 0, 1, 1, 2]
example : [0, 1, 2, 3, 4].map log2a = [0, 0, 1, 1, 2] :=
  by simp [log2a]

--
-- Using the accessibility of all Nat's.
--

-- inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop where
--   | intro (x : α) (h : (y : α) → r y x → Acc r y) : Acc r x

-- inductive WellFounded {α : Sort u} (r : α → α → Prop) : Prop where
--   | intro (h : ∀ a, Acc r a) : WellFounded r

def log2w' : (n : Nat) -> (acc : Acc Nat.lt n) -> Nat := fun
  | .zero, acc => .zero
  | .succ .zero, acc => .zero
  | .succ (.succ n), (Acc.intro _ rec) =>
      have : div2 n ≤ n := div2le n
      have lt : div2 n + 1 < n + 2 := by omega
      .succ (log2w' (.succ (div2 n)) (rec _ lt))

def log2w (n : Nat) : Nat :=
  have : Acc Nat.lt n := Nat.lt_wfRel.wf.apply n
  log2w' n (Nat.lt_wfRel.wf.apply n)

#guard [0, 1, 2, 3, 4].map log2w  = [0, 0, 1, 1, 2]

-- Now let us try to define a well-founded relation...

-- def Subrelation {α : Sort u} (q r : α → α → Prop) :=
--   ∀ {x y}, q x y → r x y

/-
namespace Div2LtRel

-- @[simp]
def Div2LtRel (x y : Nat) : Prop := x = div2 y ∧ x < y

theorem SrDiv2 : Subrelation Div2LtRel Nat.lt := by
  simp [Subrelation, Div2LtRel]

instance instWFDiv2LtRel : WellFoundedRelation Nat where
  rel := Div2LtRel
  wf := Subrelation.wf SrDiv2 Nat.lt_wfRel.wf

def log2wf : (n : Nat) -> Nat
  | 0 => 0
  | 1 => 0
  | n' + 2 =>
      log2wf (div2 n' + 1) + 1
termination_by n => n
decreasing_by simp [Div2LtRel]

end Div2LtRel
 -/

--
-- Sized
--

inductive Bin : Type where
  | ε : Bin
  | b0 : Bin -> Bin
  | b1 : Bin -> Bin

open Bin

-- Here b0 x < b0 (b1 x) .

-- Alas! This is OK in Agda and Lean 4, but doesn't work in Idris. :-(

def foo1 : Bin -> Nat
  | ε => 0
  | b0 ε => 0
  | b0 (b0 x) => foo1 (b0 x) + 1
  | b0 (b1 x) => foo1 (b0 x) + 1
  | b1 x      => foo1 x + 1

-- This is OK neither in Agda nor in Idris.
-- Here b1 x < b0 (b0 x) doesn't hold!

-- But Lean 4 is able to prove termination!

def foo2 : (n : Bin) -> Nat
  | ε => 0
  | b0 ε => 0
  | b0 (b0 x) => foo2 (b1 x) + 1
  | b0 (b1 x) => foo2 (b0 x) + 1
  | b1 x      => foo2 x + 1

def foo2' (n : Bin) : Nat :=
  match n with
    | ε => 0
    | b0 ε => 0
    | b0 (b0 x) => foo2' (b1 x) + 1
    | b0 (b1 x) => foo2' (b0 x) + 1
    | b1 x      => foo2' x + 1
termination_by n
decreasing_by
  · show sizeOf x.b1 < sizeOf x.b0.b0; simp
  · show sizeOf x.b0 < sizeOf x.b1.b0; simp
  · show sizeOf x < sizeOf x.b1; simp

def sizeOfBin : Bin -> Nat
  | .ε => 0
  | .b0 n => sizeOfBin n + 1
  | .b1 n => sizeOfBin n + 1

instance : SizeOf Bin where
  sizeOf := sizeOfBin

#guard sizeOf ε == 0
#guard sizeOf ε.b0 == 1
#guard sizeOf ε.b0.b1 == 2

def foo3 (n : Bin) : Nat :=
  match n with
    | ε => 0
    | b0 ε => 0
    | b0 (b0 x) =>
        -- have : sizeOf x.b1 < sizeOf x.b0.b0 := by
        --   simp [sizeOf, sizeOfBin]
        foo3 (b1 x) + 1
    | b0 (b1 x) => foo3 (b0 x) + 1
    | b1 x      => foo3 x + 1
termination_by n
decreasing_by all_goals simp [sizeOf, sizeOfBin]

-- But we can "ornament" Bin with its size.
-- Then the termination checker sees the decreasing size and is happy.

inductive SBin : (k : Nat) -> Type where
  | sbε : SBin 0
  | sb0 {k} : SBin k -> SBin (k + 1)
  | sb1 {k} : SBin k -> SBin (k + 1)
open SBin

def foo_s {k} : SBin k -> Nat
  | sbε => 0
  | sb0 sbε => 0
  | sb0 (sb0 x) => foo_s (sb0 x) + 1
  | sb0 (sb1 x) => foo_s (sb0 x) + 1
  | sb1 x => foo_s x + 1
termination_by k
decreasing_by all_goals simp

-- We can separate the computational part from the proofs
-- related to ensuring the termination. See the papers:
--
-- Ana Bove. 2001. Simple general recursion in type theory.
-- Nordic J. of Computing 8, 1 (March 2001), 22-42.
--
-- Ana Bove and Venanzio Capretta. 2005.
-- Modelling general recursion in type theory.
-- Mathematical. Structures in Comp. Sci. 15, 4 (August 2005), 671-708.
-- DOI=10.1017/S0960129505004822 http://dx.doi.org/10.1017/S0960129505004822

inductive Log2b : Nat -> Type where
  | l0 : Log2b 0
  | l1 : Log2b 1
  | l2 {n} : Log2b (div2 n + 1) -> Log2b (n + 2)
open Log2b

def sizeOfLog2b {n} : Log2b n -> Nat
  | l0 => 0
  | l1 => 1
  | l2 h => sizeOfLog2b h + 1

/-
def sizeOfLog2b {n} : Log2b n -> Nat := by
  intro h
  cases n with
  | zero => exact 0
  | succ n' =>
      cases n' with
      | zero => exact 1
      | succ n'' =>
          have h2 : Log2b (div2 n'' + 1) := by
            cases h with
            | l2 h'' => exact h''
          exact sizeOfLog2b h2
termination_by n
decreasing_by
  have : div2 n'' ≤ n'' := div2le n''
  omega
 -/

instance {n} : SizeOf (Log2b n) where
  sizeOf := sizeOfLog2b

def log2b' : (n : Nat) -> (acc : Log2b n) -> Nat := fun
  | .(0), l0  => 0
  | .(1), l1  => 0
  | .(k + 2), l2 (n := k) acc  =>
      (log2b' (div2 k + 1) acc) + 1

def Log2b_3 : Log2b 3 := l2 l1

#guard log2b' 3 Log2b_3 == 1

example : log2b' 3 Log2b_3 == 1 := rfl

-- For all `n`, `Log2b n`!

def all_log2b : (n : Nat) -> Log2b n
  | 0 => l0
  | 1 => l1
  | n + 2 =>
      have : div2 n + 1 < n + 2 := by
        have : div2 n ≤ n := div2le n
        omega
      (all_log2b (div2 n + 1)).l2

def log2b (n : Nat) : Nat :=
  log2b' n (all_log2b n)

#guard [0, 1, 2, 3, 4].map log2b  == [0, 0, 1, 1, 2]

example : [0, 1, 2, 3, 4].map log2b  = [0, 0, 1, 1, 2] := by
  simp [log2b, log2b', all_log2b]

--
-- Transfinite addition of ordinal numbers
--

inductive OrdNat : Type where
  | oz  : OrdNat
  | os  : (n : OrdNat) -> OrdNat
  | lim : (f : Nat -> OrdNat) -> OrdNat
open OrdNat

-- Here we use the application rule:
--  y < x ⇒ y a1 ... an < x

def addOrd : (n m : OrdNat) -> OrdNat
  | n, oz => n
  | n, os m => os (addOrd n m)
  | n, lim f => lim fun u => addOrd n (f u)

def lim0 : OrdNat := lim (fun _ => oz)
def lim1 := lim (fun _ => lim fun _ => oz.os)

example : addOrd lim0 oz = lim (fun _ => oz) := by
  rfl

example (n : OrdNat) : addOrd n lim0 = lim (fun _ => n) := by
  rfl

namespace AddOrd1

def addOrd : OrdNat -> OrdNat -> OrdNat := by
  intro n m
  cases m with
  | oz => exact n
  | os m => exact os (addOrd n m)
  | lim f =>
      apply lim
      intro u
      apply addOrd
      · exact n
      · exact f u

end AddOrd1

def OrdNat.ofNat : Nat -> OrdNat
  | 0 => oz
  | n + 1 => os (OrdNat.ofNat n)

instance (n : Nat) : OfNat OrdNat n where
  ofNat := OrdNat.ofNat n

example : addOrd 1 2 = 3 :=
  rfl

@[simp]
theorem addOrd_nz {n} : addOrd n oz = n := by
  rfl

@[simp]
theorem addOrd_ns {n m} : addOrd n (os m) = os (addOrd n m) := by
  rfl

@[simp]
theorem addOrd_nl {n f} : addOrd n (lim f) = lim (fun u => addOrd n (f u)) := by
  rfl

def branch : OrdNat := lim (fun u => ofNat u)

example : addOrd branch branch =
            (lim fun u => addOrd (lim ofNat) (ofNat u)) := by
  simp [branch]

-- In transfinite arithmetic, specifically for ordinal numbers
-- like ω, addition and multiplication are not commutative!

@[simp]
theorem addOrd_zn {n} : addOrd oz n = n := by
  induction n with
  | oz =>
      show addOrd oz oz = oz
      simp
  | os n' ih =>
      show addOrd oz (os n') = os n'
      -- ih : addOrd oz n' = n'
      simp [ih]
  | lim f ih =>
      show addOrd oz (lim f) = lim f
      simp
      show (fun u => addOrd oz (f u)) = f
      apply funext
      show ∀ (x : Nat), addOrd oz (f x) = f x
      -- ih : ∀ (a : Nat), addOrd oz (f a) = f a
      exact ih

/-
theorem addOrd_sm {n m} : addOrd (os n) m = os (addOrd n m) := by
  induction m generalizing n with
  | oz => rfl
  | os n' ih =>
      -- simp [ih]
      rw [addOrd_ns, addOrd_ns, ih]
  | lim f ih =>
      rw [addOrd_nl, addOrd_nl]
      show (lim fun u => addOrd n.os (f u)) = (lim fun u => addOrd n (f u)).os
      conv =>
        lhs
        congr
        intro u
        rw [ih]
      show (lim fun u => (addOrd n (f u)).os) = (lim fun u => addOrd n (f u)).os
      sorry
 -/
