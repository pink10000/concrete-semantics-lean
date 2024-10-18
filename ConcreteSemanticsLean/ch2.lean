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

-- 2.7, p19
def pre_order: tree X -> List X -- using real List, not mylist
  | tree.tip => List.nil
  | tree.node l val r => [val] ++ pre_order l ++ pre_order r

def post_order: tree X -> List X -- using real List, not mylist
  | tree.tip => List.nil
  | tree.node l val r => post_order l ++ post_order r ++ [val]

def ex_2_7_tree := tree.node (tree.node tree.tip 2 tree.tip) 1 (tree.node tree.tip 3 tree.tip)
--   1
--  / \
-- 2   3

#eval pre_order ex_2_7_tree -- [1, 2, 3]
#eval post_order ex_2_7_tree -- [2, 3, 1]

theorem pre_order_mirror_is_rev_post_order: ∀ (t: tree X), pre_order (mirror t) = List.reverse (post_order t) := by
  intro t
  induction t
  case tip => rfl
  case node l val r lih rih => simp [mirror, pre_order, post_order]; rw [lih, rih]

-- 2.8, p19

-- 2.9, p21

-- 2.10, p25
-- binary tree skeleton
inductive tree0 where
  | tip -- null, not a leaf
  | node (l: tree0) (r: tree0) -- inner nodes and leaves
deriving Repr

def nodes: tree0 -> Nat
  | tree0.tip => 0
  | tree0.node l r => 1 + nodes l + nodes r

def ex_tree0_3 := tree0.node (tree0.node tree0.tip tree0.tip) (tree0.node tree0.tip tree0.tip)
--   o
--  / \
-- o   o
def ex_tree0_2 := tree0.node (tree0.node tree0.tip tree0.tip) tree0.tip
--   o
--  /
-- o
#eval nodes ex_tree0_3 -- 3

-- creates a new tree E from tree `t` with
-- recurrence |E[n]| = 1 + 2|E[n-1]| = 2^n - 1 + 2^n * (nodes t)
def explode: Nat -> tree0 -> tree0
  | 0, t => t
  | Nat.succ n, t => explode n (tree0.node t t)

#eval nodes (explode 2 ex_tree0_2) -- 11 nodes
#eval explode 1 ex_tree0_2
--      o
--    /   \
--   o     o
--  /     /
-- o     o

example: ex_tree0_2.node ex_tree0_2 = explode 1 ex_tree0_2 := rfl -- lhs is weird lean syntax that creates a new tree with l = r = the 1 given tree
example: (explode 2 tree0.tip) = ex_tree0_3 := rfl


theorem explode_step_equiv: ∀ (n: Nat) (t: tree0), explode (n+1) t = (explode n t).node (explode n t) := by
  intros n t
  induction n
  case zero => simp [explode]
  case succ n' ih => simp [explode]; sorry

example: k - 1 = k + -1 := by
rw [sub_eq_add_neg]

example: 1 + (2 - 1) = 2 := by
  linarith
  -- rw [<- add_comm_sub] -- doesn't work

example: 2 - 1 + 1 = 2 := by
  linarith
  -- rw [sub_add_cancel] -- neither work
  -- rw [sub_add_comm]

theorem explode_recurrence: ∀ (n: Nat) (t: tree0), nodes (explode n t) = 2^n - 1 + 2^n * (nodes t) := by
  intros n t
  induction n
  case zero => simp [explode]
  case succ n' ih =>
    rw [explode_step_equiv]
    simp [nodes, ih]
    rw [<- add_assoc (1) (2 ^ n' - 1) (2 ^ n' * nodes t)]
    rw [add_comm (2 ^ n' - 1) (2 ^ n' * nodes t)]
    rw [add_assoc (1 + (2 ^ n' - 1)) (2 ^ n' * nodes t)]
    rw [<- add_assoc (2 ^ n' * nodes t) (2 ^ n' * nodes t)]
    rw [<- two_mul, <- mul_assoc, <- mul_comm (2 ^ n') (2), <- pow_succ]
    rw [add_comm (2 ^ (n' + 1) * nodes t)]
    rw [<- add_assoc]
    rw [add_comm 1]
    have cancel: 2 ^ n' - 1 + 1 = 2 ^ n' := by
      -- apply [sub_add_cancel (2 ^ n') (1) (1)] -- why doesn't it work
      sorry
    rw [cancel]
    have assoc: 2 ^ n' + (2 ^ n' - 1) = (2 ^ n' + 2 ^ n') - 1 := by
      sorry
    rw [assoc]
    rw [<- two_mul, <- mul_comm (2 ^ n') (2), <- pow_succ]


-- 2.11, p25
