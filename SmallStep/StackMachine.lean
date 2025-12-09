--
-- Small-step operational semantics
-- making use of dependent types
--

/-
This (slightly modified) code is from

  Proof by Smugness
  by Conor on August 7, 2007.
  http://fplab.bitbucket.org/posts/2007-08-07-proof-by-smugness.html
-/

--
-- A Toy Language
--

inductive Tm where
  | val (n : Nat) : Tm
  | add (t1 t2 : Tm) : Tm

def tm123 := Tm.add (Tm.val 1) (Tm.add (Tm.val 2) (Tm.val 3))

def tm123' : Tm := .add (.val 1) (.add (.val 2) (.val 3))

#check tm123
#eval tm123

-- Big-step evaluator

def eval : Tm -> Nat
  | .val n => n
  | .add t1 t2 => eval t1 + eval t2

#check eval tm123
#eval eval tm123

--
-- Virtual machine
--

-- Program

-- The idea is to index code by initial and final stack depth
-- in order to ensure stack safety.

inductive Code : Nat -> Nat -> Type where
  | seq  : {i j k : Nat} -> (c1 : Code i j) -> (c2 : Code j k) -> Code i k
  | push : {i : Nat} -> (n : Nat) -> Code i (i + 1)
  | add  : {i : Nat} -> Code (i + 2) (i + 1)

def code123 : Code 0 1 :=
  Code.seq (Code.push 1) (Code.seq (Code.push 2) (Code.seq (Code.push 3) (
  Code.seq (Code.add) (Code.add))))

def code123' : Code 0 1 :=
  .seq (.push 1) $
  .seq (.push 2) $
  .seq (.push 3) $
  .seq (.add) $
  .add

def code123'' : Code 0 1 :=
  (Code.push 1).seq
  ((Code.push 2).seq
  ((Code.push 3).seq
  (Code.add.seq Code.add)))

infixr:40 " ;; " => Code.seq

def code123''' : Code 0 1 :=
  .push 1 ;; .push 2 ;; .push 3 ;; .add ;; .add

-- State

inductive Stack : Nat -> Type where
  | nil : Stack 0
  | cons : {k : Nat} -> (hd : Nat) -> (tl : Stack k) -> Stack (k + 1)

#check Stack 10

def st123 : Stack 3 :=
  Stack.cons 1 (Stack.cons 2 (Stack.cons 3 Stack.nil))

def st123' : Stack 3 :=
  .cons 1 (.cons 2 (.cons 3 .nil))

infixr:67 " ::: " => Stack.cons

def st123'' : Stack 3 :=
  1 ::: 2 ::: 3 ::: .nil

#check List

-- Interpreter

def exec {i j : Nat} : (c : Code i j) -> (s : Stack i) -> Stack j
  | c1 ;; c2, s => exec c2 (exec c1 s)
  | .push n, s => n ::: s
  | .add, n2 ::: (n1 ::: s) => (n1 + n2) ::: s

#check exec
#eval exec code123 Stack.nil

-- Compiler

def compile {i : Nat} : (t : Tm) -> Code i (i + 1)
  | .val n => .push n
  | .add t1 t2 => (compile t1 ;; compile t2) ;; .add

#check (compile tm123 : Code 0 1)
#eval (compile tm123 : Code 0 1)


-- `seq` is associative with respect to `exec`.

def seq_assoc {i0 i1 i2 i3 : Nat} {c1 : Code i0 i1} {c2 : Code i1 i2} {c3 : Code i2 i3} {s} :
    exec ((c1 ;; c2) ;; c3) s = exec (c1 ;; (c2 ;; c3)) s :=
  calc exec ((c1 ;; c2) ;; c3) s
  _ = exec c3 (exec (c1 ;; c2) s)
      := by rfl
  _ = exec c3 (exec c2 (exec c1 s))
      := by rfl
  _ = exec (c2 ;; c3) (exec c1 s)
      := by rfl
  _ = exec (c1 ;; (c2 ;; c3)) s
      := by rfl

-- Here is another proof, which is shorter, but is more mysterious.

def seq_assoc' :
    exec ((c1 ;; c2) ;; c3) s = exec (c1 ;; (c2 ;; c3)) s :=
  .refl (exec c3 (exec c2 (exec c1 s)))

-- `compile` is correct with respect to `exec`.

def correct {i} (t : Tm) (s : Stack i) :
    exec (compile t) s = eval t ::: s :=
  match t with
  | .val n =>
      calc exec (compile (.val n)) s
      _ = exec (.push n) s
          := by rw [compile]
      _ = n ::: s
          := by rw [exec]
      _ = eval (.val n) ::: s
          := by rw [eval]
  | .add t1 t2 =>
      calc exec (compile (t1.add t2)) s
      _ = exec ((compile t1 ;; compile t2) ;; .add) s
          := by rw [compile]
      _ = exec .add (exec (compile t1 ;; compile t2) s)
          := by rw [exec]
      _ = exec .add (exec (compile t2) (exec (compile t1) s))
          := by rw [exec]
      _ = exec .add (eval t2 ::: exec (compile t1) s)
          := by rw [correct]
      _ = exec .add (eval t2 ::: eval t1 ::: s)
          := by rw [correct]
      _ = (eval t1 + eval t2) ::: s
          := by rw [exec]
      _ = eval (t1.add t2) ::: s
          := by rw [eval]


-- Here is another proof, which is shorter, but is more mysterious.

def correct' {i} (t : Tm) (s : Stack i) :
    exec (compile t) s = eval t ::: s :=
  match t with
  | .val n =>
      show exec (compile (.val n)) s = eval (.val n) ::: s from
        rfl
  | .add t1 t2 =>
      show (exec (compile (.add t1 t2)) s = eval (.add t1 t2) ::: s) from
        by simp [eval, compile, exec, correct']

/-

In Lean 4, extracting a program from a proof leverages proof erasure,
where proofs (in Prop) and types are automatically discarded during
compilation, leaving only computational content as an executable program.
This works because Lean treats proofs as irrelevant: a function returning
{x : A // P x} pairs a computed x with a proof of P x, but the proof
vanishes at compile time, yielding a plain A-returning function.

 -/

--
-- A compiler that is correct "by construction".
--

def ex_code {i} (t : Tm) :
    {c : Code i (i + 1) // (s : Stack i) -> exec c s = eval t ::: s} :=
  match t with
  | .val n =>
      ⟨.push n, fun s =>
        calc exec (.push n) s
        _ = n ::: s
            := by rw [exec]
        _ = eval (.val n) ::: s
            := by rw [eval]
       ⟩
  | .add t1 t2 =>
      let ⟨c1, p1⟩ := ex_code (i := i) t1
      let ⟨c2, p2⟩ := ex_code (i := i + 1) t2
      ⟨(c1 ;; c2) ;; .add, fun s =>
        calc exec ((c1 ;; c2) ;; .add) s
        _ = exec .add (exec (c1 ;; c2) s)
            := by rw [exec]
        _ = (exec .add (exec c2 (exec c1 s)))
            := by rw [exec]
        _ =(exec .add (exec c2 (eval t1 ::: s)))
            := by rw [p1]
        _ =(exec .add (eval t2 ::: eval t1 ::: s))
            := by rw [p2]
        _ = (eval t1 + eval t2) ::: s
            := by rw [exec]
        _ = eval (.add t1 t2) ::: s
            := by rw [eval]
      ⟩

--
-- `ex_code` produces the same code as `compile`.
--

def correct'' {i : Nat} : (t : Tm) ->
    (ex_code (i := i) t).val = compile (i := i) t
  | .val n =>
      calc (ex_code (.val n)).val = compile (.val n)
        := rfl
  | .add t1 t2 =>
      let ⟨c1, eq1⟩ := ex_code (i := i) t1
      let ⟨c2, eq2⟩ := ex_code (i := i + 1) t1
      calc (ex_code (.add t1 t2)).val
      _ = (((ex_code t1).val ;; (ex_code t2).val) ;; Code.add)
        := by rw [ex_code];
      _ = ((compile t1 ;; compile t2) ;; Code.add)
        := by rw [correct'', correct'']
      _ = compile (.add t1 t2)
        := by rw [<- compile]

--
-- Compiling to a list of instructions
--

-- Instructions

inductive Inst : (i j : Nat) -> Type where
  | push : {i : Nat} -> (n : Nat) -> Inst i (i + 1)
  | add  : {i : Nat} -> Inst (i + 2) (i + 1)

-- Programs

inductive Prog : (i j : Nat) -> Type where
  | nil  : {i : Nat} -> Prog i i
  | cons : {i j k : Nat} -> (c : Inst i j) -> (p : Prog j k) -> Prog i k

infixr:40 " # " => Prog.cons

def prog123''' : Prog 0 1 :=
  .push 1 # .push 2 # .push 3 # .add # .add # .nil

-- Interpreter

def p_exec {i j} : (p : Prog i j) -> (s : Stack i) -> Stack j
  | .nil, s => s
  | (.push n # p), s =>
      p_exec p (n ::: s)
  | (.add # p), (n2 ::: n1 ::: s) =>
      p_exec p ((n1 + n2) ::: s)

-- Compiler

def p_compile {i j} : (t : Tm) -> (p : Prog (i + 1) j) -> Prog i j
  | .val n, p => .push n # p
  | .add t1 t2, p =>
      p_compile t1 (p_compile t2 (.add # p))

-- Code -> Prog

def flatten {i j k} : (c : Code i j) -> (p : Prog j k) -> Prog i k
  | (c1 ;; c2), p => flatten c1 (flatten c2 p)
  | (.push n), p => .push n # p
  | .add, p => .add # p

-- `flatten` is correct.

def flatten_correct' {i j k} : (c : Code i j) -> (p : Prog j k) -> (s : Stack i) ->
    p_exec p (exec c s) = p_exec (flatten c p) s
  | c1 ;; c2, p, s =>
      calc p_exec p (exec (c1 ;; c2) s)
      _ = p_exec p (exec c2 (exec c1 s))
        := by rw [exec]
      _ = p_exec (flatten c2 p) (exec c1 s)
        := by rw [flatten_correct']
      _ = p_exec (flatten c1 (flatten c2 p)) s
        := by rw [flatten_correct']
      _ = p_exec (flatten (c1 ;; c2) p) s
        := by rw [<- flatten]
  | .push n, p, s =>
      calc p_exec p (exec (.push n) s)
      _ = p_exec (flatten (.push n) p) s
        := .refl (p_exec p (n ::: s))
  | .add, p, n2 ::: n1 ::: s =>
      calc p_exec p (exec .add (n2 ::: n1 ::: s))
      _ = p_exec (flatten .add p) (n2 ::: n1 ::: s)
        := .refl (p_exec p ((n1 + n2) ::: s))

def flatten_correct {i j} (c : Code i j) (s : Stack i) :
    exec c s = p_exec (flatten c .nil) s :=
  flatten_correct' c .nil s

-- compile ~ p_compile

def compile_p_compile {i j} : (t : Tm) -> (p : Prog (i + 1) j) ->
    flatten (compile t) p = p_compile t p
  | .val n, p =>
    calc flatten (compile (.val n)) p
    _ = p_compile (.val n) p
      := .refl (.push n # p)
  | .add t1 t2, p =>
    calc flatten (compile (.add t1 t2)) p
    _ = flatten (compile t1) (flatten (compile t2) (.add # p))
      := by rw [compile, flatten, flatten, flatten]
    _ = (p_compile t1 (flatten (compile t2) (.add # p)))
      := by rw [compile_p_compile]
    _ = (p_compile t1 (p_compile t2 (.add # p)))
      := by rw [compile_p_compile]
    _ = p_compile (.add t1 t2) p
      := by rw [<- p_compile]
