import ConcreteSemanticsLean.cslib
import Init.Prelude
import Mathlib.Tactic.Linarith

-- 2.1, p15
#eval 1 + (2: Nat) -- 3
#eval 1 + (2: Int) -- 3
#eval 1 - (2: Nat) -- 0
#eval 1 - (2: Int) -- -1

-- 2.2, p15
def double : Nat → Nat
  | 0     => 0
  | (n+1) => double n + 2

theorem add_zero_right : ∀ (n : Nat), add n 0 = n := by
  intro n
  induction n
  case zero => rfl
  case succ n ih =>
    simp [add]; apply ih

theorem add_one : ∀ (m : Nat), add m 1 = m + 1 := by
  intro m
  induction m
  case zero => rfl
  case succ m ih =>
    simp [add]; rw [ih]

theorem add_succ : ∀ (n : Nat), add m (n + 1) = (add m n) + 1 := by
  intro n
  induction n
  case zero => simp [add]; rw [add_zero_right]; rw [add_one]
  case succ n ih =>
    -- have e : (1 : Nat) + 1 = 2 := rfl
    simp_all; rw [← ih]; sorry


theorem add_is_comm : ∀ (m n : Nat), add m n = add n m := by
  intro m n
  induction m generalizing n
  case zero => rw [add_zero_right]; rfl
  case succ m ih =>
    simp [add]; rw [ih]; sorry

theorem add_is_assoc : ∀ (m n k : Nat), add m (add n k) = add (add m n) k := by
  intros m n k
  induction k
  case zero =>
    rw [add_zero_right, add_zero_right]
  case succ k ih =>
   sorry

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
-- append
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

lemma snoc_append (l : mylist X) (x : X) (b : mylist X) : ((snoc l x) ++ b) = l ++ (x :: b) := by
  induction l
  case nil => simp [snoc, concat]
  case cons h t ih => simp [snoc, concat]; rw [ih]

lemma itrev_rev_prepend : ∀ (a b : mylist X), itrev a b = (rev' a) ++ b := by
  intro a b
  induction a generalizing b
  case nil => simp [itrev, concat]
  case cons x l ih => simp [itrev, rev']; rw [snoc_append, ih (x :: b)]

lemma itrev_rev_empty : ∀ (l : mylist X), itrev l [] = rev' l := by
  intro l; rw [itrev_rev_prepend l [], concat_empty]

def itadd (a b : Nat) : Nat := match a with | 0 => b | Nat.succ a' => itadd a' (Nat.succ b)
lemma itadd_eq_add : ∀ (a b : Nat), itadd a b = a + b := by
  intro a b
  induction a generalizing b
  case zero => simp [itadd]
  case succ n ih => simp [itadd]; rw [ih (b + 1)]; linarith


-- 2.10, p25

-- 2.11, p25
