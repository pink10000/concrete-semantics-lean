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

  #check 1 :: mylist.nil

end cslib
