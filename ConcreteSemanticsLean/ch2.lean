import ConcreteSemanticsLean.cslib
import Init.Prelude

-- 2.1

-- 2.2

-- 2.3
def count [DecidableEq X] (elm : X) (l : mylist X) (occ : Nat) : Nat :=
  match l with
  | [] => occ
  | a :: l' => if elm = a then count elm l' (occ + 1) else count elm l' occ

#eval count 1 (1 :: 2 :: 1 :: []) 0 -- 2
#eval count 3 (1 :: 2 :: 1 :: []) 0 -- 0
#eval count type1.A type1_list 0 -- 1

-- someone should try to find  way to remove the need for DecidableEq
theorem count_x_le_len [DecidableEq X] : ∀ (elm : X) (l : mylist X), count elm l 0 ≤ len l := by
  intros elm l
  induction l
  . simp [count, len]
  . simp [count, len]
    sorry





-- 2.4

-- 2.5

-- 2.6

-- 2.7

-- 2.8

-- 2.9

-- 2.10

-- 2.11
