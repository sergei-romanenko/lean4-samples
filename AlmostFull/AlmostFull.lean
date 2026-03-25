/-
  Title:      AlmostFull.lean
  Author:     Sergei Romanenko, KIAM Moscow

  This Agda version is based on

  Vytiniotis, Dimitrios; Coquand, Thierry; Wahlstedt, David.
  Stop when you are almost-full.
  Adventures in constructive termination.
  Beringer, Lennart (ed.) et al., Interactive theorem proving.
  Third international conference, ITP 2012,
  Princeton, NJ, USA, August 13‒15, 2012. Proceedings.
  Berlin: Springer (ISBN 978-3-642-32346-1/pbk).
  Lecture Notes in Computer Science 7406, 250-265 (2012).

  http://research.microsoft.com/en-us/people/dimitris/af-itp.pdf
  http://research.microsoft.com/en-us/people/dimitris/af-itp2012.tgz
  http://research.microsoft.com/en-us/people/dimitris/afchalmers.pptx
-/

import Batteries
import Aesop

--
--  Basic setup, inductive trees, and almost-full relations
--

@[aesop unsafe [constructors, cases]]
inductive AlmostFull {X : Type} : (X -> X -> Prop) -> Type where
  | now : {R : X -> X -> Prop} ->
     (n : ∀ x y, R x y) -> AlmostFull R
  | later : {R : X -> X -> Prop} ->
     (l : ∀ u, AlmostFull (fun x y => R x y ∨ R u x)) -> AlmostFull R
open AlmostFull

-- AlmostFull A -> AlmostFull B

def af_strengthen
   {X : Type} {A B : X -> X -> Prop} (p : AlmostFull A)
    (a2b : ∀ x y, A x y -> B x y) : AlmostFull B
  :=
  match p with
  | now ha =>
      now fun x y => a2b x y (ha x y)
  | later h =>
      later $
      fun u =>
      af_strengthen (h u) (
        fun x y => fun
        | .inl axy => Or.inl (a2b x y axy)
        | .inr azx => Or.inr (a2b u x azx))

--
-- AlmostFull implies that every infinite chain has two related elements
--

theorem sec_binary_infinite_chain
    {X : Type} {R : X -> X -> Prop} (p : AlmostFull R) (f : Nat -> X) (k : Nat) :
    ∃ m n, k ≤ m ∧ m < n ∧ R (f m) (f n)
  := by
  induction p generalizing k with
  | @now R' rxy =>
      show ∃ m n, k ≤ m ∧ m < n ∧ R' (f m) (f n)
      exists k, k + 1
      simp only [Nat.le_refl, Nat.lt_add_one, true_and]
      exact rxy (f k) (f (k + 1))
  | @later R' p' ih =>
      show ∃ m n, k ≤ m ∧ m < n ∧ R' (f m) (f n)
      specialize ih (f k) (k + 1)
      simp_all only [exists_and_left]
      obtain ⟨m, lekm, x, ltmx, r'r'⟩ := ih
      cases r'r' with
      | inl h1 =>
          exists m
          have : k ≤ m := by omega
          simp [this]
          exists x
      | inr h2 =>
          exists k
          simp
          exists m

theorem af_inf_chain {X : Type} {R : X -> X -> Prop} (p : AlmostFull R)
    (f : Nat -> X):  ∃ m n, m < n ∧ R (f m) (f n)
  := by
  have : ∃ m n, 0 ≤ m ∧ m < n ∧ R (f m) (f n) := by
    apply sec_binary_infinite_chain p f 0
  show ∃ m n, m < n ∧ R (f m) (f n)
  simp at this
  exact this

--
-- From a decidable Well-founded relation to an AlmostFull
--

-- Generalization to an arbitrary decidable well-founded relation

def af_iter {X : Type} {R : X -> X -> Prop}
    (decR : DecidableRel R) (z : X) (accX : Acc R z) :
    AlmostFull (fun x y => ¬ R x z ∨ ¬ R y x)
  := by
  induction accX
  rename_i x h ih
  apply later
  intro u
  match decR u x with
  | .isFalse nrux =>
      apply now
      --aesop
      intro x' y'
      show (¬R x' x ∨ ¬R y' x') ∨ (¬R u x ∨ ¬R x' u)
      exact (Or.inr ∘ Or.inl) nrux
  | .isTrue rux =>
      have af_R' := ih u rux
      apply af_strengthen af_R'
      --aesop
      intro x' y'
      show ¬R x' u ∨ ¬R y' x' -> (¬R x' x ∨ ¬R y' x') ∨ (¬R u x ∨ ¬R x' u)
      exact (Or.elim · (Or.inr ∘ Or.inr) (Or.inl ∘ Or.inr))

-- WellFounded R -> AlmostFull

def af_from_wf {X : Type} {R : X -> X -> Prop}
        (w : WellFounded R) (d : DecidableRel R) : AlmostFull (fun x y => ¬ R y x)
    :=
    later fun u =>
    have af_a := af_iter d u (WellFounded.apply w u)
    have ab := fun _ _ => (Or.elim · Or.inr Or.inl)
    af_strengthen af_a ab

--
-- From an AlmostFull relation to a Well-Founded one
--

@[aesop unsafe [constructors, cases]]
inductive ReflTransGen (r : α -> α -> Prop) (a : α) : α -> Prop
  | refl : ReflTransGen r a a
  | tail {b} : Relation.TransGen r a b -> ReflTransGen r a b

local add_aesop_rules unsafe [Relation.TransGen]

@[simp]
theorem rtt_t_tt {X} {T : X -> X -> Prop} {x y u : X}
      (rttxu : ReflTransGen T x u) (tuy: T u y) : Relation.TransGen T x y
  :=
  match rttxu with
  | .refl => Relation.TransGen.single tuy
  | .tail ttxu => Relation.TransGen.tail ttxu tuy

@[simp]
theorem rtt_t_rtt {X} {T : X -> X -> Prop} {x y u : X}
      (rttxu : ReflTransGen T x u) (tuy: T u y) : ReflTransGen T x y
  :=
  ReflTransGen.tail $
  match rttxu with
  | .refl => Relation.TransGen.single tuy
  | .tail ttxu => Relation.TransGen.tail ttxu tuy

@[simp]
theorem acc_from_af
      {X : Type}
      {R : X -> X -> Prop} (p : AlmostFull R) (T : X -> X -> Prop) (x : X)
      (h : ∀ z y, (ReflTransGen T y x ->
                Relation.TransGen T z y -> R y z -> False)) : Acc T x
  := by
  induction p generalizing x with
  | @now R' n =>
      apply Acc.intro
      intro z tzx
      apply False.elim
      apply h z x ReflTransGen.refl (Relation.TransGen.single tzx) (n x z)
  | @later R' l l_ih =>
      apply Acc.intro
      intro z tzx
      apply l_ih x z
      intro u y rttyz ttuy rr
      simp_all
      cases rr with
      | inl ryu =>
          have rttyx : ReflTransGen T y x := rtt_t_rtt rttyz tzx
          apply h u y rttyx ttuy ryu
      | inr rxy =>
          have rttyx: Relation.TransGen T y x := rtt_t_tt rttyz tzx
          exact h y x ReflTransGen.refl rttyx rxy

theorem wf_from_af (X : Type) (R : X -> X -> Prop) (p : AlmostFull R)
      (T : X -> X -> Prop)
      (h : ∀ x y, Relation.TransGen T x y -> R y x -> False)
        : WellFounded T
  := by
  apply WellFounded.intro
  intro y
  apply acc_from_af p T
  intro x z rttzy ttxz
  exact h x z ttxz

--
-- A reassuring lemma
--

def Transitive  {X : Type} (R : X -> X -> Prop) :=
  ∀ {a b c : X},  R a b -> R b c -> R a c

theorem wf_from_wqo (X : Type) (R : X -> X -> Prop)
      (tr : Transitive R) (p : AlmostFull R) :
      WellFounded (fun x y => R x y ∧ ¬ R y x)
  := by

  let P := fun x y => R x y ∧ ¬ R y x

  let rec get_r {x y} : Relation.TransGen P x y -> R x y
    | .single pxy => pxy.left
    | .tail (b := z) h pzy =>
        have rxz : R x z := get_r h
        have rzy : R z y := pzy.left
        tr rxz rzy

  let rec get_false {x y} : Relation.TransGen P x y -> R y x -> False
    | .single pxy, ryx =>
        have nryx : ¬R y x := pxy.right
        nryx ryx
    | .tail (b := z) tpxz pzy, ryx =>
        have ⟨rzy, nryz⟩ := pzy
        have rxz : R x z := get_r tpxz
        have rzx : R z x := tr rzy ryx
        get_false tpxz rzx

  apply wf_from_af X R p P
  apply get_false


--
-- Well-founded trees
--

inductive WFT (X  :  Type) : Type where
  | zt  : WFT X
  | sup : (g : X -> WFT X) -> WFT X
open WFT

-- SecureBy

def SecureBy {X : Type} (R : X -> X -> Prop) (p : WFT X) : Prop :=
 match p with
  | zt => ∀ x y, R x y
  | sup p =>
      ∀ u, SecureBy (fun x y => R x y ∨ R u x) (p u)

@[simp]
theorem rw_zt (X : Type) (A : X -> X -> Prop) :
    SecureBy A zt = ∀ x y, A x y
  := rfl

@[simp]
theorem rw_sup (X : Type) (A : X -> X -> Prop) (f : X -> WFT X) :
    SecureBy A (sup f) =
    ∀ u, SecureBy (fun x y => A x y ∨ A u x) (f u)
  := by rfl

-- AlmostFullT

@[simp]
def AlmostFullT {X : Type} (R : X -> X -> Prop) :=
  {p // SecureBy R p}

-- AlmostFullT R : AlmostFull R

def aft_to_af' {X : Type} {R : X -> X -> Prop} :
      (p : WFT X) -> (s : SecureBy R p) -> AlmostFull R
  | zt, s =>
      AlmostFull.now s
  | sup g, s =>
      AlmostFull.later
      fun u => aft_to_af' (g u) (s u)

def aft_to_af {X : Type} {R : X -> X -> Prop}
      (p : AlmostFullT R) : AlmostFull R
  := aft_to_af' p.val p.property

-- AlmostFull R -> AlmostFullT R

def af_to_aft {X : Type} {R : X -> X -> Prop} : AlmostFull R -> AlmostFullT R
  | now n => ⟨zt, n⟩
  | later l =>
      have step := fun u => af_to_aft (l u)
      ⟨ sup fun u => (step u).val, fun u => (step u).property ⟩

-- AlmostFull R -> WFT X

def wft_from_af {X : Type} {R : X -> X -> Prop} :
      AlmostFull R -> WFT X
  | now _ => zt
  | later l => sup (fun u => wft_from_af (l u))

-- AlmostFull R -> SecureBy R

def af_to_sec {X : Type} {R : X -> X -> Prop} :
      (p : AlmostFull R) -> SecureBy R (wft_from_af p)
  | now n => n
  | later l => fun u => af_to_sec (l u)

-- SecureBy A -> SecureBy B

def sec_strengthen {X : Type} {A B : X -> X -> Prop}
  (t : WFT X) (sa : SecureBy A t) (ab: ∀ x y, A x y → B x y) :
      SecureBy B t :=
  match t with
  | zt => fun x y => ab x y (sa x y)
  | sup g =>
      fun u =>
      show SecureBy (fun x y => B x y ∨ B u x) (g u) from
      sec_strengthen (g u) (sa u) (fun x y =>
        show A x y ∨ A u x → B x y ∨ B u x from
        (Or.elim · (Or.inl ∘ ab x y) (Or.inr ∘ ab u x)))
