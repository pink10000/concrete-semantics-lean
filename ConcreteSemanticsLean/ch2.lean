import ConcreteSemanticsLean.cslib
import Init.Prelude
import Mathlib.Tactic.Linarith

-- 2.1, p15
#eval 1 + (2: Nat) -- 3
#eval 1 + (2: Int) -- 3
#eval 1 - (2: Nat) -- 0
#eval 1 - (2: Int) -- -1

-- 2.2, p15

-- 2.3, p15
def count [DecidableEq X] (elm : X) (l : mylist X) : Nat :=
  match l with
  | [] => 0
  | a :: l' => if elm = a then 1 + count elm l' else count elm l'

#eval count 1 (1 :: 2 :: 1 :: []) -- 2
#eval count 3 (1 :: 2 :: 1 :: []) -- 0
#eval count type1.A type1_list -- 1

-- someone should try to find  way to remove the need for DecidableEq
theorem count_x_le_len [DecidableEq X] : ∀ (elm : X) (l : mylist X), count elm l ≤ len l := by
  intros elm l
  induction l
  case nil =>
    simp [count, len]
  case cons head tl ih =>
    simp [count, len]  -- Simplify count and len for the cons case
    by_cases h : elm = head
    -- Case when elm = hd
    . simp [h]; rw [← h]; exact ih
   -- Case when elm ≠ hd
    . simp [h]; linarith


-- 2.4, p15
def snoc: mylist X -> X -> mylist X
  | mylist.nil, b => b :: mylist.nil
  | a :: l, b => a :: (snoc l b)

#eval snoc (1::2::3::mylist.nil) 1 -- correctly appends to end

def rev': mylist X -> mylist X
  | mylist.nil => mylist.nil
  | a :: l => snoc (rev' l) a

#eval rev' (1::2::3::mylist.nil) -- correctly reverses

-- [1] need to show reversing a right-append (snoc) on list l is left-appending elem with list l reversed
theorem rev_snoc_is_left_app_rev: ∀ (l: mylist X) (elem: X), rev' (snoc l elem) = elem :: rev' l := by
  intro l elem
  induction l
  case nil => rfl
  case cons elem l' ih => simp [rev']; rw [ih]; simp [snoc]

theorem rev_involutive: ∀ l: mylist X, rev' (rev' l) = l := by
  intro l
  induction l
  case nil => rfl
  case cons a l' ih =>
    simp [rev'] -- [1] wants rev' (snoc (rev' l') a) = mylist.cons a l'
    rw [rev_snoc_is_left_app_rev, ih]

-- 2.5, p15

-- 2.6, p19

def contents {X} (t : tree X) : (mylist X) :=
  match t with
  | tree.tip => mylist.nil
  | tree.node l val r =>
    match (l, r) with
    | (tree.tip, tree.tip)  => val :: mylist.nil
    | (tree.tip, _)         => val :: contents r
    | (_, tree.tip)         => val :: contents l
    | (_, _)                => val :: (contents l ++ contents r)
/-
   2
  / \
 1   3
-/
def exampleTree : tree Nat :=
  tree.node
    (tree.node tree.tip 1 tree.tip)
    2
    (tree.node tree.tip 3 tree.tip)
#eval contents exampleTree -- [1, 2, 3]

/-
      4
    /   \
   2     6
  / \   / \
 1  3  5  7
-/
def lvl2tree : tree Nat :=
  tree.node
    (tree.node (tree.node tree.tip 1 tree.tip) 2 (tree.node tree.tip 3 tree.tip))
    4
    (tree.node (tree.node tree.tip 5 tree.tip) 6 (tree.node tree.tip 7 tree.tip))

#eval contents lvl2tree -- [1, 2, 3, 4, 5, 6, 7]

def sum_tree (t : tree Nat) : Nat := sum (contents t) -- defined this way because it's how it's defined...?
theorem sum_tree_is_sum_list : ∀ t: tree Nat, sum_tree t = sum (contents t) := by intro t; rfl


-- 2.7, p19

-- 2.8, p19

-- 2.9, p21

/--
reverses list `l` and appends it to `acc`
tail-recursive = can be compiled to a loop

Looks like we already defined a `reverse`, but for the
purposes of this problem, we'll use this instead.
--/
def itrev {X} (l : mylist X) (acc : mylist X) : mylist X :=
  match l with
  | mylist.nil => acc
  | a :: l' => itrev l' (a :: acc)

lemma itrev_rev_prepend : ∀ (a b : mylist X), itrev a b = (rev' a) ++ b := by
  intro a b
  induction a
  case nil => simp [itrev, rev', concat]
  case cons x l ih =>
    simp [itrev, rev', concat]
    sorry -- i think rev' and snoc can be better defined

lemma itrev_rev_empty : ∀ (l acc : mylist X), itrev l [] = rev' l := by
  intro l h
  induction l
  case nil => simp [itrev, rev']
  case cons a l ih =>
    simp [itrev, rev', snoc]
    sorry



-- 2.10, p25

-- 2.11, p25
