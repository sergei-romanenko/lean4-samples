/-
    Title:      Berghofer.HigmanT2
    Author:     Sergei Romanenko, KIAM Moscow

    This version is produced by rewriting the proof presented in

      S. Berghofer. A constructive proof of Higman's lemma in Isabelle.
      In Types for Proofs and Programs, TYPES'04. LNCS, 3085: 66-82.
      Springer Verlag, 2004.

    from Isabelle to Lean 4.
-/

import Batteries
import Aesop

-- Words are modelled as lists of letters from
-- the two letter alphabet.

inductive Letter : Type where
  | l0 : Letter
  | l1 : Letter
deriving BEq

open Letter

abbrev Word := List Letter

-- The embedding relation on words is defined inductively.
-- Intuitively, a word `v` can be embedded into a word `w`,
-- if we can obtain `v` by deleting letters from `w`.
-- For example,
--   l1 :: l0 :: l1 :: [] ⊴ l0 :: l1 :: l0 :: l0 :: l1 :: []

@[aesop unsafe [constructors, cases]]
inductive «<<» : (v w : Word) -> Prop where
  | empty : «<<» [] []
  | drop {v w a}  : «<<» v w -> «<<» v (a :: w)
  | keep {v w a}  : «<<» v w -> «<<» (a :: v) (a :: w)
open «<<»

infix:50 " << " => «<<»

example : l1 :: l0 :: l1 :: [] << l0 :: l1 :: l0 :: l0 :: l1 :: [] :=
  -- aesop
  drop $ keep $ drop $ keep $ keep empty

-- [] is embeddable in any word.

@[simp]
theorem emb_empty : (w : Word) -> [] << w
  | [] => empty
  | _ :: ws => drop $ emb_empty ws

example : (w : Word) -> [] << w := by
  intro w; induction w <;> aesop

-- We represent a finite sequence w_0, w_1, ... , w_n as
--   w_n :: ... :: w_1 :: w_0 :: []

abbrev WSeq := List Word

-- In order to formalize the notion of a good sequence,
-- we define an auxiliary relation *<<.
--   ws *<< v
-- means that ws contains a word w, such that w << v .

@[aesop unsafe [constructors, cases]]
inductive «*<<» : (ws : WSeq) -> (v : Word) -> Prop where
  | eHere  {w ws v} : w << v -> «*<<» (w :: ws) v
  | eThere {w ws v} : «*<<» ws v -> «*<<» (w :: ws) v
open «*<<»

infix:50 " *<< " => «*<<»

-- A list of words is good if its tail is either good
-- or contains a word which can be embedded into the word
-- occurring at the head position of the list.

@[aesop unsafe [constructors, cases]]
inductive Good : (ws : WSeq) -> Prop where
  | here  {w ws} : ws *<< w -> Good (w :: ws)
  | there {w ws} : Good ws -> Good (w :: ws)
open Good

-- In order to express the fact that every infinite sequence is good,
-- we define a predicate Bar.
--
-- Intuitively, Bar ws means that either
-- (1) the list of words ws is already good, or
-- (2) successively adding words will turn it into a good list.

@[aesop unsafe [constructors, cases]]
inductive Bar : WSeq -> Prop where
  | now   {ws} : Good ws -> Bar ws
  | later {ws} : ((w : Word) -> Bar (w :: ws)) -> Bar ws
open Bar

-- Consequently,
--   Bar []
-- means that every infinite sequence must be good,
-- since by successively adding words to the empty list, we must
-- eventually arrive at a list which is good.

-- (Note that the above definition of Bar is closely related to
-- Brouwer’s more general principle of bar induction.)

-- The following function adds a letter to each word in a word list.

def «::*» : (a : Letter) -> (ws : WSeq) -> WSeq
  | _, [] => []
  | a, (w :: ws) => (a :: w) :: («::*» a ws)

infix:67 " ::* " => «::*»

@[simp]
theorem «::*-[]» {a} : a ::* [] = [] :=rfl

@[simp]
theorem «::*-::» {a w ws} : a ::* (w :: ws) = (a :: w) :: («::*» a ws) :=rfl


namespace Berghofer's_T

  -- This is the relation `T`, used in the original Berghofer's proof.

  -- `T a vs ws` means that vs is obtained from ws by
  -- (1) first copying the prefix of words starting with the letter b,
  --     where Not(a = b), and
  -- (2) then appending the tails of words starting with a.

inductive T : (a : Letter) -> (vs ws : WSeq) -> Prop where
  | tInit {a b w ws} : Not (a = b) ->
            T a (w ::(b ::* ws)) ((a :: w) :: (b ::* ws))
  | tKeep {a vs ws w} : T a vs ws ->
            T a (w :: vs) ((a :: w) :: ws)
  | tDrop {a b vs ws w} : Not (a = b) ->
            T a vs ws -> T a vs ((b :: w) :: ws)

end Berghofer's_T

-- In Berghofer's proof `T` is always used as a comination
--   `T a xs zs -> T b ys zs -> ...`
-- So, we can simplify the proof by directly defining a relation T2, such that
-- `T2 xs ys zs` is equivalent to `(T a xs zs, T a xs zs)`.

@[aesop unsafe [constructors, cases]]
inductive T2 : (zs xs ys : WSeq) -> Prop where
  | init0 {w ys} : T2 (w :: (l1 ::* ys)) ys ((l0 :: w) :: (l1 ::* ys))
  | init1 {w xs} : T2 xs (w :: (l0 ::* xs)) ((l1 :: w) :: (l0 ::* xs))
  | step0 {w xs ys zs} : T2 xs ys zs -> T2 (w :: xs) ys ((l0 :: w) :: zs)
  | step1 {w xs ys zs} : T2 xs ys zs -> T2 xs (w :: ys) ((l1 :: w) :: zs)
open T2

--
-- The proof of Higman’s lemma is divided into several parts, namely
-- prop1, prop2 and prop3.
-- From the computational point of view, these theorems can be thought of
-- as functions transforming trees.

--
-- prop1 : Sequences “ending” with empty word (trivial)
-- A sequence ending with the empty word satisfies predicate Bar,
-- since it can trivially be extended to a good sequence
-- by appending any word.
--

@[simp]
theorem bar_w_empty (ws : WSeq) : Bar ([] :: ws) :=
  later $
  show (w : Word) -> Bar (w :: [] :: ws) from
  fun w =>
  have : [] << w := emb_empty w
  have : [] :: ws *<< w := eHere this
  have : Good (w :: [] :: ws) :=  here this
  have : Bar (w :: [] :: ws) := now this
  this

example (ws : WSeq) : Bar ([] :: ws) :=
  later (emb_empty · |> eHere |> here |> now)

example (ws : WSeq) : Bar ([] :: ws) :=
  by aesop

-- Lemmas. w *<< v ... -> (a :: w) *<< v ...

example {ws v a} : ws *<< v -> ws *<< a :: v
  := by intro h; induction h <;> aesop

@[simp]
theorem s_emb_drop {ws v a} : ws *<< v -> ws *<< a :: v
  | eHere w_emb_v => eHere (drop w_emb_v)
  | eThere ws_s_emb_v => eThere (s_emb_drop ws_s_emb_v)

example {ws v a} : ws *<< v -> (a ::* ws) *<< a :: v
  := by intro h; induction h <;> aesop

@[simp]
theorem s_emb_keep {ws v a} : ws *<< v -> (a ::* ws) *<< a :: v
  | eHere w_emb_v => eHere (keep w_emb_v)
  | eThere ws_s_emb_v => eThere (s_emb_keep ws_s_emb_v)

example {xs ys zs w} : T2 xs ys zs -> xs *<< w -> zs *<< l0 :: w
  := by intro ht hw; induction ht <;> (try simp_all) <;> cases hw <;> aesop

@[simp]
theorem t2_semb_drop0 {xs ys zs w} : T2 xs ys zs -> xs *<< w -> zs *<< l0 :: w
  | init0 => fun
    | eHere emb_w => eHere (keep emb_w)
    | eThere semb_w => eThere (s_emb_drop semb_w)
  | init1 => fun
      semb_w => eThere (s_emb_keep semb_w)
  | step0 t2 => fun
    | eHere emb_w => eHere (keep emb_w)
    | eThere semb_w => eThere (t2_semb_drop0 t2 semb_w)
  | step1 t2 => fun
    | semb_w => eThere (t2_semb_drop0 t2 semb_w)

example {xs ys zs w} : T2 xs ys zs -> ys *<< w -> zs *<< l1 :: w
  := by intro ht hw; induction ht <;> (try simp_all) <;> cases hw <;> aesop

@[simp]
theorem t2_semb_drop1 {xs ys zs w} : T2 xs ys zs -> ys *<< w -> zs *<< l1 :: w
  | init0 => fun
    | semb_w => eThere (s_emb_keep semb_w)
  | init1 => fun
    | eHere emb_w => eHere (keep emb_w)
    | eThere semb_w => eThere (s_emb_drop semb_w)
  | step0 t2 => fun
    | semb_w => eThere (t2_semb_drop1 t2 semb_w)
  | step1 t2 => fun
    | eHere emb_w => eHere (keep emb_w)
    | eThere emb_w => eThere (t2_semb_drop1 t2 emb_w)

-- Lemmas. Good ... -> Good ...

example {ws a} : Good ws -> Good (a ::* ws)
  := by intro gx; induction gx <;> aesop

@[simp]
theorem good_drop {ws a} : Good ws -> Good (a ::* ws)
  | here ws_s_emb_w =>
      here (s_emb_keep ws_s_emb_w)
  | there good_ws =>
      there (good_drop good_ws)

-- set_option trace.aesop true

example {xs ys zs} : T2 xs ys zs -> Good xs -> Good zs := by
  intro t gx; induction t <;> cases gx <;>
  first | aesop | apply here; expose_names; exact t2_semb_drop0 h h_1

theorem good_t0 {xs ys zs} : T2 xs ys zs -> Good xs -> Good zs
  | init0 => fun
    | here semb_w => here (s_emb_drop semb_w)
    | there good_l1ys => there good_l1ys
  | init1 => fun
    | gx => there (good_drop gx)
  | step0 t2 => fun
    | here semb_w => here (t2_semb_drop0 t2 semb_w)
    | there gx => there (good_t0 t2 gx)
  | step1 t2 => fun
    | gx => there (good_t0 t2 gx)

example {xs ys zs} : T2 xs ys zs -> Good ys -> Good zs := by
  intro t gy; induction t <;> cases gy <;>
  first | aesop | apply here; expose_names; exact t2_semb_drop1 h h_1

theorem good_t1 {xs ys zs} : T2 xs ys zs -> Good ys -> Good zs
  | init0 => fun
    | gy => there (good_drop gy)
  | init1 => fun
    | here semb_w => here (s_emb_drop semb_w)
    | there good_l0xs => there good_l0xs
  | step0 t2 => fun
    | gy => there (good_t1 t2 gy)
  | step1 t2 => fun
    | here semb_w => here (t2_semb_drop1 t2 semb_w)
    | there gy => there (good_t1 t2 gy)

--
-- prop2 : Interleaving two trees
--
-- Proof idea: Induction on Bar xs and Bar ys,
-- then case distinction on the first letter of the first word following zs.

-- This is not accepted by Lean 4 (due to termination problems)...

/-
theorem tt_bb {xs ys zs} (bxs : Bar xs) (bys : Bar ys) (t : T2 xs ys zs) : Bar zs :=
  match bxs, bys with
  | now nx, _ => now (good_t0 t nx)
  | later lx, now ny => now (good_t1 t ny)
  | later lx, later ly => later $
      show (w : Word) -> Bar (w :: zs) from
      fun
      | [] => bar_w_empty zs
      | l0 :: w =>
          @tt_bb (w :: xs) ys ((l0 :: w) :: zs)
            (lx w) (later ly) (step0 t)
      | l1 :: w =>
          @tt_bb xs (w :: ys) ((l1 :: w) :: zs)
            (later lx) (ly w) (step1 t)
 -/

-- This is OK. Explicit recursion has been replaced with `induction`.

theorem tt_bb {xs ys zs} (bxs : Bar xs) (bys : Bar ys) (t : T2 xs ys zs) : Bar zs := by
  induction bxs generalizing ys zs bys with
  | now nx => exact now $ good_t0 t nx
  | @later xs' lx hx =>
      induction bys generalizing xs zs with
      | now ny => exact now (good_t1 t ny)
      | @later ys' ly hy =>
          apply later
          show (v : Word) -> Bar (v :: zs)
          intro v
          match v with
          | [] => exact bar_w_empty zs
          | l0 :: w =>
              show Bar ((l0 :: w) :: zs)
              apply hx w (ys := ys') (later ly) (step0 t)
          | l1 :: w =>
              show Bar ((l1 :: w) :: zs)
              apply hy w (xs := xs') (step1 t)

--
-- prop3 : Lifting to longer words
--
-- Proof idea: Induction on Bar ws, then induction on first word following ws
--

theorem bar_lift (c ws : _) (b : Bar ws) : Bar (c ::* ws) := by
  induction b with
  | @now ws n => exact now $ good_drop n
  | @later ws' l ihl =>
      show Bar (c ::* ws')
      apply later; intro v
      induction v with
      | nil => exact bar_w_empty (c ::* ws')
      | cons c' w ih =>
          match c' with
          | l0 =>
              match c with
              | l0 => exact ihl w
              | l1 =>
                  show Bar ((l0 :: w) :: (l1 ::* ws'))
                  exact tt_bb ih (later l) init0
          | l1 =>
              match c with
              | l0 =>
                  show Bar ((l1 :: w) :: l0 ::* ws')
                  exact tt_bb (later l) ih init1
              | l1 => exact ihl w

--
-- higman: Main theorem
--

theorem later_empty :  (w : Word) -> Bar (w :: [])
  | [] => bar_w_empty []
  | c :: w =>
      bar_lift c (w :: []) (later_empty w)

theorem bar_empty : Bar [] :=
  later later_empty

theorem bar_ne (w ws : _) : Bar ws -> Bar (w :: ws)
  | now n => now (there n)
  | later l => l w

theorem higman : (ws : WSeq) -> Bar ws
  | [] => bar_empty
  | (w :: ws) => bar_ne w ws (higman ws)

--
-- good-prefix-lemma
--

inductive IsPrefix (f : Nat -> Word) : WSeq -> Prop where
  | pz : IsPrefix f []
  | ps {xs} : IsPrefix f xs -> IsPrefix f (f xs.length :: xs)
open IsPrefix

theorem goodPrefix' (f : Nat -> Word)
    {ws} (p : IsPrefix f ws) (b : Bar ws) :
    (∃ xs', IsPrefix f xs' ∧ Good xs') := by
  match b with
  | @now ws' n =>
      exact ⟨ws', p, n⟩
  | @later ws' l =>
      exact goodPrefix' f (ps p) (l (f ws'.length))

-- Finding good prefixes of infinite sequences

theorem goodPrefix (f : Nat -> Word) :
      (∃ xs, IsPrefix f xs ∧ Good xs) :=
  goodPrefix' f pz bar_empty
