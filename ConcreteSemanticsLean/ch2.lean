import ConcreteSemanticsLean.cslib
import Init.Prelude
import Mathlib.Tactic.Linarith

-- 2.1
#eval 1 + (2: Nat) -- 3
#eval 1 + (2: Int) -- 3
#eval 1 - (2: Nat) -- 0
#eval 1 - (2: Int) -- -1
-- 2.2

-- 2.3
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


-- 2.4
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

-- 2.5

-- 2.6

-- 2.7

-- 2.8

-- 2.9

-- 2.10

-- 2.11
