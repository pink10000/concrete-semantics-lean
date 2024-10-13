import ConcreteSemanticsLean.cslib
import Init.Prelude
import Mathlib.Tactic.Linarith

-- 2.1

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

-- 2.5

-- 2.6

-- 2.7

-- 2.8

-- 2.9

-- 2.10

-- 2.11
