-- Holds definitions of CS terms in lean
-- nat, bool are already included in Init

def sample := "sample"

section cslib

inductive mylist (X : Type) where
| nil
| cons (a : X) (l : mylist X)
deriving Repr

set_option quotPrecheck false in
notation x " :: " l => (mylist.cons x l)
notation "[]" => mylist.nil

#check mylist.cons 1 mylist.nil
def append (l : mylist X) (a : X) : (mylist X) := a :: l

#eval append [] 1
#check append (1 :: []) 2

def reverse (l : mylist X) (acc : mylist X) : (mylist X) :=
  match l with
  | mylist.nil => acc
  | a :: l' => reverse l' (a :: acc)

#check reverse [] []
#eval reverse (1 :: []) []
#eval reverse (2 :: 1 :: []) []

example : reverse (1 :: 2 :: 3 :: []) [] = 3 :: 2 :: 1 :: [] := by rfl

def len (l : mylist X) : Nat :=
  match l with
  | mylist.nil => 0
  | _ :: l' => 1 + len l'

#eval len (1 :: 2 :: 3 :: []) -- 3
#eval len ([] : mylist Nat) -- 0
-- note, lean doesn't know what type [] is since we've told it to be implicit

inductive type1 where
| A
| B
| C
deriving Repr, DecidableEq -- this is kinda insane that you need this
-- lean straight up has no idea if the inductive types can be equal to itself or not
-- adding DecidableEq tells lean "hey, you can check if these are equal or not"

def type1_list := (type1.A :: type1.B :: type1.C :: [])

-- exercises 2.6-2.7 use this binary tree
inductive tree (X: Type) where
| tip
| node (left: tree X) (node_val: X) (right: tree X)

def mirror: tree X -> tree X
  | tree.tip => tree.tip
  | tree.node l val r => tree.node (mirror r) val (mirror l)

theorem mirror_involutive: ∀ (t: tree X), mirror (mirror t) = t := by
  intros t
  induction t
  case tip => rfl
  case node l val r lih rih =>
    simp [mirror]
    rw [lih, rih]
    simp -- basically `apply And.intro; rfl; rfl`

end cslib
