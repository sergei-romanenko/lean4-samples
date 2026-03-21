import Batteries
import Aesop

inductive N where
  | zero : N
  | succ (n : N) : N

open N

def N.ofNat : Nat -> N
  | 0 => zero
  | n + 1 => succ (N.ofNat n)

instance (n : Nat) : OfNat N n where
  ofNat := N.ofNat n

example : (3 : N) = zero.succ.succ.succ
  := rfl

def add_acc : N -> N -> N := fun
  | m, zero => m
  | m, succ n => add_acc m.succ n

@[simp]
theorem acc_add_zero (m : N) : add_acc m zero = m
  := rfl

@[simp]
theorem acc_add_succ (m n : N) : add_acc m n.succ = add_acc m.succ n
  := rfl

/-
theorem acc_succ_add₀ (m n : N) : add_acc m.succ n = (add_acc m n).succ := by
  induction n with
  | zero =>
      -- simp
      show add_acc m.succ zero = (add_acc m zero).succ
      rewrite [acc_add_zero, acc_add_zero]
      show m.succ = m.succ
      rfl
  | succ n' ih =>
      -- simp [ih]
      show add_acc m.succ n'.succ = (add_acc m n'.succ).succ
      rewrite [acc_add_succ, acc_add_succ]
      show add_acc m.succ.succ n' = (add_acc m.succ n').succ
      -- ih : add_acc m.succ n' = (add_acc m n').succ
      -- ih is not general enough!
      sorry
 -/

@[simp]
theorem acc_succ_add (m n : N) : add_acc m.succ n = (add_acc m n).succ := by
  induction n generalizing m with
  | zero =>
      -- simp
      show add_acc m.succ zero = (add_acc m zero).succ
      rewrite [acc_add_zero, acc_add_zero]
      show m.succ = m.succ
      rfl
  | succ n' ih =>
      -- simp [ih]
      show add_acc m.succ n'.succ = (add_acc m n'.succ).succ
      rewrite [acc_add_succ, acc_add_succ]
      show add_acc m.succ.succ n' = (add_acc m.succ n').succ
      -- ih : ∀ (m : Nat), add_acc m.succ n' = (add_acc m n').succ
      exact ih m.succ

theorem acc_succ_add₂ (m n : N) : add_acc m.succ n = (add_acc m n).succ := by
  induction n generalizing m <;> aesop

theorem acc_zero_add (n : N) : add_acc zero n = n := by
  induction n with
  | zero =>
      -- simp
      show add_acc zero zero = zero
      rewrite [acc_add_zero]
      show zero = zero
      rfl
  | succ n' ih =>
      -- simp [ih]
      show add_acc zero n'.succ = n'.succ
      show add_acc zero.succ n' = n'.succ
      rewrite [acc_succ_add]
      show (add_acc zero n').succ = n'.succ
      rewrite [ih]
      show n'.succ = n'.succ
      rfl

theorem acc_zero_add₁ (n : N) : add_acc zero n = n := by
  induction n <;> aesop

example (m n : Nat) : m + n = n + m := by
    induction m with
    | zero =>
        show 0 + n = n + 0
        rw [Nat.zero_add, Nat.add_zero]
    | succ m' ih =>
        show (m' + 1) + n = n + (m' + 1)
        rw [Nat.succ_add, Nat.add_succ, ih]

example (m n : Nat) : m + n = n + m := by
  induction m with
  | zero =>
      show 0 + n = n + 0
      rw [Nat.zero_add, Nat.add_zero]
  | succ m' ihm =>
      show m' + 1 + n = n + (m' + 1)
      induction n with
      | zero =>
          show m' + 1 + 0 = 0 + (m' + 1)
          rw [Nat.add_zero, Nat.zero_add]
      | succ n' ihn =>
          show (m' + 1) + (n' + 1) = (n' + 1) + (m' + 1)
          rw [Nat.succ_add, ihm, Nat.add_succ, Nat.add_zero, Nat.add_succ]

example {α} (xs : List α) : xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons h xs' ih =>
      apply congrArg (h :: ·)
      exact ih

def plus: Nat → Nat → Nat
  | n, Nat.zero => n
  | n, Nat.succ k' => plus (Nat.succ n) k'

example (n k : Nat) : plus n k = n + k := by
  induction k generalizing n with
  | zero => rfl
  | succ k' ih =>
      rw [plus, ih n.succ, Nat.succ_add, Nat.add_succ]

def rev {α} : List α -> List α := fun
  | [] => []
  | x :: xs => rev xs ++ [x]

@[simp]
def rev_nil {α} : @rev α [] = [] := rfl

@[simp]
def rev_cons {α} {x : α} {xs} : rev (x :: xs) = rev xs ++ [x] := rfl

@[simp]
def rev_append {α} (xs ys : List α) : rev (xs ++ ys) = rev ys ++ rev xs := by
  cases xs with
  | nil =>
      show rev ([] ++ ys) = rev ys ++ rev []
      rw [List.nil_append, rev_nil, List.append_nil]
  | cons x xs =>
      show rev (x :: xs ++ ys) = rev ys ++ rev (x :: xs)
      rw [List.cons_append, rev_cons, rev]
      show rev (xs ++ ys) ++ [x] = rev ys ++ (rev xs ++ [x])
      rw [rev_append]
      show rev ys ++ rev xs ++ [x] = rev ys ++ (rev xs ++ [x])
      rw [List.append_assoc]

example {α} (xs ys : List α) : rev (xs ++ ys) = rev ys ++ rev xs := by
  induction xs with
  | nil =>
      -- aesop
      simp_all only [List.nil_append, rev_nil, List.append_nil]
  | cons x xs ih =>
      -- aesop
      simp_all only [List.cons_append, rev_cons, List.append_assoc]

example {α} (xs ys : List α) : rev (xs ++ ys) = rev ys ++ rev xs := by
  induction xs <;> aesop

def rev_rev {α} : (xs : List α) -> rev (rev xs) = xs
  | [] =>
      show rev (rev []) = [] from
      rfl
  | x :: xs => by
      show rev (rev (x :: xs)) = x :: xs
      simp only [rev_cons, rev_append, rev_nil, List.nil_append, List.cons_append]
      show x :: rev (rev xs) = x :: xs
      have : rev (rev xs) = xs := rev_rev xs
      rw [this]

example {α} (xs : List α) : rev (rev xs) = xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      simp
      exact ih

example {α} (xs : List α) : rev (rev xs) = xs := by
  induction xs <;> aesop

def rev_acc {α}  (acc xs : List α) : List α :=
    match xs with
    | [] => acc
    | x :: xs => rev_acc (x :: acc) xs

@[simp]
def rev_acc_nil {α} (acc : List α) : rev_acc acc [] = acc := rfl

@[simp]
def rev_acc_cons {α} (x : α) (acc xs : List α) :
      rev_acc acc (x :: xs) = rev_acc (x :: acc) xs  := rfl

theorem rev_app_acc' {α} (acc xs : List α) : rev xs ++ acc = rev_acc acc xs := by
  cases xs with
  | nil =>
      show rev [] ++ acc = rev_acc acc []
      rw [rev_nil, List.nil_append, rev_acc_nil]
  | cons x xs' =>
      show rev (x :: xs') ++ acc = rev_acc acc (x :: xs')
      rw [rev_cons, List.append_assoc, List.cons_append, List.nil_append, rev_acc_cons]
      show rev xs' ++ x :: acc = rev_acc (x :: acc) xs'
      rw [rev_app_acc']

theorem rev_app_acc'' {α} (acc xs : List α) : rev xs ++ acc = rev_acc acc xs :=
  match xs with
  | [] => calc
          rev [] ++ acc
      _ = acc              := rfl
      _ = rev_acc acc []   := rfl
  | x :: xs' => calc
        rev (x :: xs') ++ acc
    _ = rev xs' ++ [x] ++ acc := rfl
    _ = rev xs' ++ (x :: acc)  := by
          rw [List.append_assoc, List.cons_append, List.nil_append]
    _ = rev_acc (x :: acc) xs' := rev_app_acc'' (x :: acc) xs'
    _ = rev_acc acc (x :: xs') := rfl

example {α} (acc xs : List α) : rev xs ++ acc = rev_acc acc xs := by
  fun_induction rev generalizing acc
  · show [] ++ acc = rev_acc acc []
    rw [List.nil_append, rev_acc_nil]
  · rename_i x xs' ih
    rw [rev_acc_cons, List.append_assoc, ih, List.cons_append, List.nil_append]

theorem rev_rev_acc {α} (xs : List α) :
    rev xs = rev_acc [] xs := by
  suffices (acc : _) -> rev xs ++ acc = rev_acc acc xs by
    have : rev xs ++ [] = rev_acc [] xs := this []
    rw [List.append_nil] at this
    exact this
  intro acc
  induction xs generalizing acc with
  | nil =>
      rw [rev_nil, List.nil_append, rev_acc_nil]
  | cons x xs' ih =>
      show rev (x :: xs') ++ acc = rev_acc acc (x :: xs')
      rw [rev_cons, List.append_assoc, List.cons_append, List.nil_append, rev_acc_cons]
      show rev xs' ++ x :: acc = rev_acc (x :: acc) xs'
      exact ih (x :: acc)
