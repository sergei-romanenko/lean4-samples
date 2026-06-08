import Batteries
import Aesop

@[aesop unsafe]
inductive EvenP : (n : Nat) -> Prop where
  | z : EvenP 0
  | s {n} : EvenP n -> EvenP (n + 1)

example : EvenP 2
:= by
  -- aesop
  apply EvenP.s
  apply EvenP.s
  apply EvenP.z

def task1P : {n // n > 3 ∧ EvenP n}
:= by
  simp_all only [gt_iff_lt]
  apply Subtype.mk
  · apply And.intro
    on_goal 2 => {
      apply EvenP.s
      · apply EvenP.s
        · apply EvenP.s
          · apply EvenP.s
            · apply EvenP.z
    }
    · simp_all only [Nat.zero_add, Nat.reduceAdd, Nat.lt_add_one]
  done

#guard task1P.val == 4

@[aesop unsafe]
inductive EvenT : (n : Nat) -> Type where
  | z : EvenT 0
  | s {n} : EvenT n -> EvenT (n + 1)
deriving BEq

def example1T : EvenT 2
:= by
  -- aesop
  apply EvenT.s
  apply EvenT.s
  apply EvenT.z

#guard example1T == EvenT.s (EvenT.s (EvenT.z))

/-
inductive SortedBinTree : (min max : Nat) -> Type where
  | leaf : (x : Nat) -> SortedBinTree x x
  | node {lmin lmax rmin rmax} :
      (left : SortedBinTree lmin lmax) ->
      (right : SortedBinTree rmin rmax) ->
      (lmax < rmin) -> SortedBinTree lmin rmax
 -/

namespace BT1

@[aesop unsafe [constructors cases]]
inductive BT : Type where
  | leaf : (x : Nat) -> BT
  | node : (left right : BT) -> BT

@[aesop unsafe [constructors cases]]
inductive IsSBT : (min max : Nat) -> (t : BT) -> Prop where
  | leaf : (x : Nat) -> IsSBT x x (.leaf x)
  | node {lmin lmax rmin rmax} {t1 t2} :
      (lmax < rmin) ->
      (l : IsSBT lmin lmax t1) ->
      (r : IsSBT rmin rmax t2) ->
      IsSBT lmin rmax (.node t1 t2)

def t_3_5 : BT := .node (.node (.leaf 3) (.leaf 4)) (.leaf 5)

def isSBT_t_3_5 : IsSBT 3 5 t_3_5
:= by
  apply @IsSBT.node 3 4 5 5
  · exact Nat.lt_add_one 4
  · apply @IsSBT.node 3 3 4 4
    · exact Nat.lt_add_one 3
    · exact IsSBT.leaf 3
    · exact IsSBT.leaf 4
  · apply @IsSBT.leaf 5

def task_3_5 : {t // IsSBT 3 5 t}
:= ⟨t_3_5, isSBT_t_3_5⟩

end BT1

namespace BT2

@[aesop unsafe [constructors cases]]
inductive BT : Type where
  | leaf : BT
  | node : (x : Nat) -> (t1 t2 : BT) -> BT

@[aesop unsafe [constructors cases]]
inductive BTLt (u : Nat) : (t : BT) -> Prop where
  | leaf : BTLt u .leaf
  | node {t1 t2} : (x : Nat) -> x < u ->
      BTLt u t1 -> BTLt u t2 -> BTLt u (.node x t1 t2)

@[aesop unsafe [constructors cases]]
inductive BTGt (u : Nat) : (t : BT) -> Prop where
  | leaf : BTGt u .leaf
  | node {t1 t2} : (x : Nat) -> x > u ->
      BTGt u t1 -> BTGt u t2 -> BTGt u (.node x t1 t2)

inductive IsSBT : (t : BT) -> Prop where
  | leaf : IsSBT .leaf
  | node {t1 t2} : (x : Nat) -> BTLt x t1 -> BTGt x t2 ->
      IsSBT t1 -> IsSBT t2 -> IsSBT (.node x t1 t2)

def t_3_5 : BT := .node 4 (.node 3 .leaf .leaf) (.node 5 .leaf .leaf)

theorem isSBT_t_3_5 : IsSBT t_3_5
:= by
  apply IsSBT.node 4
  · apply BTLt.node 3
    · simp only [Nat.lt_add_one]
    · exact BTLt.leaf
    · exact BTLt.leaf
  · apply BTGt.node 5
    · simp only [gt_iff_lt, Nat.lt_add_one]
    · exact BTGt.leaf
    · exact BTGt.leaf
  · apply IsSBT.node 3
    · exact BTLt.leaf
    · exact BTGt.leaf
    · exact IsSBT.leaf
    · exact IsSBT.leaf
  · apply IsSBT.node 5
    · exact BTLt.leaf
    · exact BTGt.leaf
    · exact IsSBT.leaf
    · exact IsSBT.leaf

def task_3_5 : {t // IsSBT t}
:= ⟨t_3_5, isSBT_t_3_5⟩

end BT2
