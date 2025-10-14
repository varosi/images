import «Myproj»

inductive AssetType where
| common
| preferred

inductive Ticker (α : AssetType) where
| MkTicker : String -> Ticker α
deriving Repr

#check AssetType.common

def xxx (z : USize) :=
  let x := z
  x

def func1 : Ticker AssetType.common := Ticker.MkTicker "test"

inductive Weekday where
  | sunday    : Weekday
  | monday    : Weekday

structure Point where
  x : Float
  y : Float
deriving Repr

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }
def zeroX (p : Point) : Point :=
  { x := 0, y := p.y }

def Weekday.next (d : Weekday) : Weekday :=
  match d with
    | sunday    => monday
    | monday    => sunday

def natOrStringThree (b : Bool) : if b then Nat else String :=
  match b with
  | true => (3 : Nat)
  | false => "three"

#eval 2+2
#eval println! "something"

#eval (5 : Fin 8)

def lean : String := "Test"

#eval "str".append "ttt"

def NonTail.sum : List Nat → Nat
| [] => 0
| x :: xs => x + sum xs

def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs

def Tail.sum (xs : List Nat) : Nat :=
  Tail.sumHelper 0 xs

theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc]
    rw [Nat.add_comm y n]
    exact ih (n + y)

theorem non_tail_sum_eq_tail_sum1 : NonTail.sum = Tail.sum := by
  funext xs
  simp [Tail.sum]
  rw [←Nat.zero_add (NonTail.sum xs)]
  exact non_tail_sum_eq_helper_accum xs 0

theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  simp [Tail.sum]
  rw [←Nat.zero_add (NonTail.sum xs)]
  exact non_tail_sum_eq_helper_accum xs 0

-- Sections
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end useful

def sum (xs : Array Nat) : IO Nat := do
  let mut s := 0
  for x in xs do
    IO.println s!"x: {x}"
    s := s + x
  return s

#eval sum #[1, 2, 3]

inductive Color where
  | red
  | green
  | blue

structure ColorPoint (α : Type) extends PPoint α where
  color : Color

class Add' (a : Type) where
  add : a -> a -> a

#check @Add'.add

instance : Add' Nat where
  add := Nat.add


-- PLAY with ARRAYS and Fin --------------------------------------------
#check #[1,2,3]

def f (a : Array Nat) (i : Fin a.size) : Nat :=
  a[i] + a[i]

def xxx := #[1,2,3,4,5]
def f' (a : Array Nat) (i : Nat) (h : i < a.size) : Nat :=
  a[i] + a[i]

#eval (5 : Fin 1)

def findHelper (arr : Array α) (p : α → Bool) (i : Nat) : Option (Fin arr.size × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (⟨i, h⟩, x)
    else findHelper arr p (i + 1)
  else none
termination_by findHelper arr p i => arr.size - i

#eval dbgTraceIfShared "test" #[1,2]

def Array.find (arr : Array α) (p : α → Bool) : Option (Fin arr.size × α) :=
  findHelper arr p 0

def Fin.next? (x: Fin n) : Option (Fin n) :=
  let y := (val x) + 1
  if h : y < n then some ⟨y, h⟩
  else none

theorem test1 : (3 : Fin 8).next? = some 4 := by simp_arith
theorem test2 : (7 : Fin 8).next? = none := by simp_arith

theorem onePlusOneIsTwo : 2 < 5 :=
  open Nat.le in
  step (step refl)

def xxxx := f' xxx 2

inductive IsThree : Nat → Prop where
  | isThree : IsThree 3

theorem three_is_three : IsThree 3 := by
  constructor

inductive IsFive : Nat → Prop where
  | isFive : IsFive 5

theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  cases three with
  | isThree => constructor

theorem four_is_not_three : ¬ IsThree 4 := by
  simp [Not]
  intro h
  cases h

theorem four_le_seven : 4 ≤ 7 :=
  open Nat.le in
  step (step (step refl))

theorem four_lt_seven : 4 < 7 :=
  open Nat.le in
  step (step refl)

#check Nat.le.step


-- PROVE merge sort and termination -----------------------------------------
def merge [Ord α] (xs : List α) (ys : List α) : List α :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x'::xs', y'::ys' =>
    match Ord.compare x' y' with
    | .lt | .eq => x' :: merge xs' (y' :: ys')
    | .gt => y' :: merge (x'::xs') ys'
termination_by merge xs ys => (xs, ys)

def splitList (lst : List α) : (List α × List α) :=
  match lst with
  | [] => ([], [])
  | x :: xs =>
    let (a, b) := splitList xs
    (x :: b, a)

theorem splitList_shorter_le (lst : List α) :
  (splitList lst).fst.length ≤ lst.length ∧
    (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
    cases ih
    constructor
    case left => apply Nat.succ_le_succ; assumption
    case right => apply Nat.le_succ_of_le; assumption

theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  match lst with
  | x :: y :: xs =>
    simp_arith [splitList]
    apply splitList_shorter_le

theorem splitList_shorter_fst (lst : List α) (h : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length :=
  splitList_shorter lst h |>.left

theorem splitList_shorter_snd (lst : List α) (h : lst.length ≥ 2) :
    (splitList lst).snd.length < lst.length :=
  splitList_shorter lst h |>.right

def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : xs.length ≥ 2 := by
      apply Nat.ge_of_not_lt
      assumption
    have : halves.fst.length < xs.length := by
      apply splitList_shorter_fst
      assumption
    have : halves.snd.length < xs.length := by
      apply splitList_shorter_snd
      assumption
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by mergeSort xs => xs.length

#eval mergeSort ["soapstone", "geode", "mica", "limestone"]

-- Prove Insertion sort in-place ----------------------
def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    have : i' < arr.size := by
      simp [Nat.lt_of_succ_lt, *]
    match Ord.compare arr[i'] arr[i] with
    | .lt | .eq => arr
    | .gt =>
      insertSorted (arr.swap ⟨i', by assumption⟩ i) ⟨i', by simp [*]⟩

theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → arr.size = len →
    (insertSorted arr ⟨i, isLt⟩).size = len := by
  skip

def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
      sorry
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by insertionSortLoop arr i => arr.size - i

-------------------------------------------------------

def div (n k : Nat) (ok : k > 0) : Nat :=
  if n < k then
    0
  else
    have : 0 < n := by
      cases n with
      | zero => sorry
      | succ n' => simp_arith
    have : n - k < n := by
      apply Nat.sub_lt <;> assumption
    1 + div (n - k) k ok
termination_by div n k ok => n

theorem exam1 : ∀ n : Nat, 0 < (n + 1) := by
  intro n
  induction n <;> simp_arith

theorem exam2 : ∀ n : Nat, 0 ≤ n := by
  intro n
  induction n <;> simp

theorem exam3a : ∀ k : Nat, 1 - (k + 1) = 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k' =>
    rw [Nat.add_one]
    rw [Nat.succ_sub_succ]
    simp

theorem exam3b : ∀ n' k : Nat, Nat.succ n' + 1 - (k + 1) = Nat.succ n' - k := by
  skip

theorem exam3 : ∀ n k : Nat, (n+1)-(k+1) = n-k := by
  intro n k
  induction n with
  | zero =>
    simp
    apply exam3a
  | succ n' => apply exam3b

theorem exam3c : ∀ n : Nat, n - n = 0 := by
  intro n
  induction n <;> simp
