def hello := "world"

namespace numerals

inductive nat : Type where 
  | zero : nat
  | succ : nat → nat

def add (a : nat) (b : nat) : nat := match b with
  | nat.succ x => nat.succ (add a x)
  | nat.zero => a

/- def pred (a : nat) : nat := match a with -/
/-     | nat.succ x => x -/
/-     | nat.zero => nat.zero -/

-- Let's prove a+0 = a (right identity)
theorem right_identity : ∀ x, add x nat.zero = x := by
  intro x
  unfold add
  rfl

theorem left_identity: ∀ x, add nat.zero x = x := by
  intro x
  induction x with
  | zero => unfold add; simp
  | succ z ih =>
    unfold add
    simp
    apply ih

/- constant and: Prop -> Prop -> Prop -/

/- theorem s_injectivity: ∀ x y, nat.succ x = nat.succ y → x = y := by -/
/-   intro x y h -/
/-   induction -/

-- Let's prove commutativity

end numerals

#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
/- #check Implies -- Prop → Prop → Prop -/

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
/- #check Implies (And p q) (And q p)  -- Prop -/

def double (x : Nat) : Nat := x + x
#check double 4
#eval double 4
#eval 4 + 4
def myadd := fun (x: Nat) => x + x
#eval myadd 4

def foo := let a := Nat; fun x : a => x + 2

variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)
def doTwice := h (h x)
def doThrice := h (h (h x))

#print compose
#print doTwice
#print doThrice
#check List.cons
def foo2 := List.cons 1 [2, 3, 4]
#print foo2

#check @List.cons

section
  universe u
  def Lst (α : Type u) : Type u := List α

  def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
  def Lst.nil {α : Type u} : Lst α := List.nil
  def Lst.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

  #check Lst.cons 0 Lst.nil

  def as : Lst Nat := Lst.nil
  def bs : Lst Nat := Lst.cons 5 Lst.nil
end

section
  universe u
  def ident {α : Type u} (x : α) := x

  #check ident         -- ?m → ?m
  #check ident 1       -- Nat
  #check ident "hello" -- String
  #check @ident        -- {α : Type u_1} → α → α
  #check @ident Nat 2
  #check @ident Int 2
end

#check List.nil               -- List ?m
