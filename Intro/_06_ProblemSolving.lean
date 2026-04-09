--
-- Problem Solving
--

import Batteries
import Aesop

-- x = 2 + 1

example : ∃ x, x = 2 + 1 := by
  simp_all only [Nat.reduceAdd, exists_eq]

example : {x // x = 2 + 1 } := by
  aesop

example : {x // x = 2 + 1} := by
  simp_all only [Nat.reduceAdd]
  apply Subtype.mk
  · rfl

def «x=2+1» : {x : Nat // x = 2 + 1} := by
  exact ⟨3, rfl⟩

#guard «x=2+1».val == 3

-- x = m + n

def «?=m+n» (m n : Nat) : {x // x = m + n} := by
  exact ⟨m + n, rfl⟩

#guard («?=m+n» 2 3).val == 5

-- 2 + x = 3

def «2+x=3» : {x // 2 + x = 3} := by
  show { x // 2 + x = 3 }
  simp +arith
  show { x // x = 1 }
  exact ⟨1, rfl⟩

#guard «2+x=3».val == 1

-- x + 2 = 3

def «x+2=3» : {x // x + 2 = 3} := by
  show { x // x + 2 = 3 }
  simp
  show { x // x = 1 }
  exact ⟨1, rfl⟩

-- ∃ x, x + m = n

def «∃?+m=n» (m n : Nat) (le : m ≤ n) : ∃ x, x + m = n := by
  induction le
  · exact ⟨0, Nat.zero_add m⟩
  · rename_i m' le' ih
    simp_all only [Nat.le_eq, Nat.succ_eq_add_one]
    obtain ⟨w, h⟩ := ih
    subst h
    simp_all only [Nat.le_add_left]
    apply Exists.intro (w + 1)
    simp +arith

-- x + m = n

def «?+m=n» (m n : Nat) (le : m ≤ n) : {x // x + m = n} :=
  match m, n with
  | 0, n =>
      ⟨n, rfl⟩
  | m' + 1, 0 =>
      nomatch le
  | m' + 1, n' + 1 => --by
      have xp : {x' // x' + m' = n'} :=
        «?+m=n» m' n' (Nat.le_of_succ_le_succ le)
      ⟨xp.val, congrArg Nat.succ xp.property⟩

#guard («?+m=n» 1 3 (by simp only [Nat.reduceLeDiff])).val == 2


example : ∃ x, x ≤ 1 := by
  exact ⟨0, Nat.zero_le 1⟩

def «x≤1» : {x // x ≤ 1} :=
  ⟨0, Nat.zero_le 1⟩

#guard «x≤1».val == 0

/-
x≤1×y≤1 : ∃ λ x → ∃ λ y → x ≢ y × x ≤ 1 × y ≤ 1
x≤1×y≤1 = zero , suc zero , (λ ()) , z≤n , s≤s z≤n
 -/

example : ∃ x y, (x ≠ y ∧ x ≤ 1 ∧ y ≤ 1) := by
  refine Exists.intro ?_ ?_
  · exact 0
  · refine Exists.intro ?_ ?_
    · exact 1
    · show 0 ≠ 1 ∧ 0 ≤ 1 ∧ 1 ≤ 1
      omega

namespace Pratt5
  /-
  My Favorite Logic Puzzles
  by John P. Pratt

  http://www.johnpratt.com/items/puzzles/logic_puzzles.html

  When asked her 3 children's ages, Mrs. Muddled said that Alice is the youngest
  unless Bill is, and that if Carl isn't the youngest then Alice is the oldest.
  Who is the oldest and who is the youngest?
  -/

inductive Child : Type where
  | Alice : Child
  | Bill  : Child
  | Carl  : Child
deriving Repr, BEq

open Child

axiom youngest : Child → Prop
axiom oldest   : Child → Prop

axiom superlative1 : (a b : _) -> a ≠ b -> youngest a → ¬ youngest b
axiom superlative2 : (a b : _) -> a ≠ b -> oldest a → ¬ oldest b

axiom antonym1 : (a : _) -> oldest a -> ¬ youngest a
axiom antonym2 : (a : _) -> youngest a -> ¬ oldest a

axiom given1 : ¬ youngest Alice → youngest Bill
axiom given2 : ¬ youngest Carl  → oldest Alice

example : {a : Child // oldest a} := by
  refine ⟨?_, ?_⟩
  · exact Alice
  · show oldest Alice
    apply given2
    show ¬youngest Carl
    intro z
    show False
    refine superlative1 Bill Carl ?_ ?_ ?_
    · show Bill ≠ Carl
      exact Child.noConfusion
    · show youngest Bill
      apply given1
      refine superlative1 Carl Alice ?_ ?_
      · show Carl ≠ Alice
        exact Child.noConfusion
      · exact z
    · exact z

def «∃-oldest» : {a : Child // oldest a} :=
  have : oldest Alice :=
    given2 (fun z : youngest Carl => superlative1
      Bill Carl Child.noConfusion
        (given1 (superlative1 Carl Alice Child.noConfusion z)) z)
  ⟨Alice, this⟩

#guard «∃-oldest».val == Alice

def  «∃-youngest» : {a : Child // youngest a} :=
  have : youngest Bill :=
    given1 (antonym1 Alice «∃-oldest».property)
  ⟨Bill, this⟩

#guard «∃-youngest».val == Bill

def problem : {ab : Child × Child // oldest ab.fst ∧ youngest ab.snd} :=
  ⟨(Alice, Bill), ⟨ «∃-oldest».property, «∃-youngest».property ⟩⟩

end Pratt5
