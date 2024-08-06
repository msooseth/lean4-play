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

/- theorem s_injectivity: ∀ x y, nat.succ x = nat.succ y → x = y := by -/
/-   intro x y h -/
/-   induction -/

-- Let's prove commutativity



end numerals
