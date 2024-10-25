import ConcreteSemanticsLean.cslib
import Init.Prelude
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Basic

section ch2_1 -- 2.1, p15
  #eval 1 + (2: Nat) -- 3
  #eval 1 + (2: Int) -- 3
  #eval 1 - (2: Nat) -- 0
  #eval 1 - (2: Int) -- -1
end ch2_1

section ch2_2 -- 2.2, p15
  def double : Nat → Nat
    | 0     => 0
    | (n+1) => double n + 2

  lemma add_zero_right : ∀ (n : Nat), add n 0 = n := by
    intro n
    induction n
    case zero => rfl
    case succ n ih => simp [add]; apply ih

  theorem add_zero_left : ∀ (n : Nat), add 0 n = n := by intro n; induction n <;> rfl

  lemma add_one : ∀ (m : Nat), add m 1 = m + 1 := by
    intro m
    induction m
    case zero => rfl
    case succ m ih => simp [add]; rw [ih]

  theorem add_is_comm : ∀ (m n : Nat), add m n = add n m := by
    intro m n
    induction m generalizing n
    case zero => rw [add_zero_right]; rfl
    case succ m ih =>
      simp [add]; rw [ih]
      induction n
      case zero => rw [add_zero_left]; rfl
      case succ n ih => simp [add]; rw [ih]

  theorem add_is_assoc : ∀ (m n k : Nat), add m (add n k) = add (add m n) k := by
    intros m n k
    induction m generalizing n k
    case zero => rfl
    case succ m ihm => simp [add]; rw [ihm]
end ch2_2

section ch2_3 -- 2.3, p15
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

end ch2_3

section ch2_4 -- 2.4, p15
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
end ch2_4

section ch2_5 -- 2.5, p15
def sum_upto : Nat -> Nat
  | 0 => 0
  | Nat.succ n => Nat.succ (sum_upto n) + n

#eval sum_upto 4 = (4 * 5)/2
#eval sum_upto 10 = (10 * 11)/2

theorem sum_upto_eq : ∀ (n : Nat), sum_upto n = n * (n+1) / 2 := by
  intro n
  induction n
  case zero => rfl
  case succ n ih =>
    simp [sum_upto]; rw [ih];
    rw [mul_add, add_assoc, add_comm (n + 1) 1]
    simp [div_eq_mul_inv]; ring
    calc 1 + n + (n + n ^ 2) / 2
      _ = 2 * (1 + n) / 2 + (n + n^2) / 2 := by
        rw [add_right_cancel_iff]; ring_nf; simp; linarith
      _ = (2 * (1 + n) + n + n^2) / 2 := by
        sorry






end ch2_5

section ch2_6 -- 2.6, p19
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

  def sum_tree (t : tree Nat) : Nat := sum (contents t)
  theorem sum_tree_is_sum_list : ∀ t: tree Nat, sum_tree t = sum (contents t) := by intro t; rfl
end ch2_6

section ch2_7 -- 2.7, p19
  def pre_order: tree X -> mylist X
    | tree.tip => []
    | tree.node l val r => (val :: []) ++ pre_order l ++ pre_order r

  def post_order: tree X -> mylist X
    | tree.tip => []
    | tree.node l val r => post_order l ++ post_order r ++ (val :: [])

  def ex_2_7_tree := tree.node (tree.node tree.tip 2 tree.tip) 1 (tree.node tree.tip 3 tree.tip)
  --   1
  --  / \
  -- 2   3

  #eval pre_order ex_2_7_tree -- [1, 2, 3]
  #eval post_order ex_2_7_tree -- [2, 3, 1]

  lemma reverse_concat : ∀ (l1 l2 : mylist X), reverse (l1 ++ l2) = reverse l2 ++ reverse l1 := by
    intro l1 l2
    induction l1 generalizing l2
    case nil => simp [reverse, concat, concat_empty]
    case cons a l1 ih =>
      simp [reverse, concat]
      rw [ih, append_is_concat, append_is_concat, concat_assoc];

  theorem pre_order_mirror_is_rev_post_order: ∀ (t: tree X), pre_order (mirror t) = reverse (post_order t) := by
    intro t
    induction t
    case tip => rfl
    case node l val r lih rih =>
      simp [mirror, pre_order, post_order, reverse]; rw [lih, rih]
      rw [reverse_concat, reverse_concat]; rfl
end ch2_7

section ch2_8 -- 2.8, p19
end ch2_8

section ch2_9 -- 2.9, p21
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
end ch2_9

section ch2_10 -- 2.10, p25
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
  #eval nodes ex_tree0_2 -- 2

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
  #eval nodes (explode 1 ex_tree0_2) -- 5
  #check ex_tree0_2.node ex_tree0_2

  -- lhs is weird lean syntax that creates a new tree with l = r = the 1 given tree
  example : ex_tree0_2.node ex_tree0_2 = explode 1 ex_tree0_2 := by rfl
  example : (explode 2 tree0.tip) = ex_tree0_3 := by rfl

  theorem explode_double_step :
    ∀ (t : tree0), explode 2 t = (explode 1 t).node (explode 1 t) := by intros t; simp [explode]
  theorem explode_triple_step :
    ∀ (t : tree0), explode 3 t = (explode 2 t).node (explode 2 t) := by intros t; simp [explode]
  theorem explode_quadruple_step :
    ∀ (t : tree0), explode 4 t = (explode 3 t).node (explode 3 t) := by intros t; simp [explode]

  theorem explode_step_equiv :
    ∀ (n : Nat) (t : tree0), explode (n + 1) t = (explode n t).node (explode n t) := by
    intros n t
    induction n
    case zero => simp [explode]
    case succ n' ih =>
      simp [explode]; sorry


  theorem explode_recurrence :
    ∀ (n : Nat) (t : tree0), nodes (explode n t) = 2^n - 1 + 2^n * (nodes t) := by
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
      have cancel : 2 ^ n' - 1 + 1 = 2 ^ n' := by
        rw [Nat.sub_add_cancel]; apply Nat.pow_pos; linarith
      rw [cancel]
      have assoc : 2 ^ n' + (2 ^ n' - 1) = (2 ^ n' + 2 ^ n') - 1 := by
        rw [Nat.add_sub_assoc]; linarith
      rw [assoc]
      rw [<- two_mul, <- mul_comm (2 ^ n') (2), <- pow_succ]

end ch2_10

section ch2_11 -- 2.11, p25
end ch2_11
