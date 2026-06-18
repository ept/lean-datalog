/-!
A small grab-bag of theorems exercising the constructs the extractor must encode:
foralls, lambdas, applications, universe polymorphism, literals, and
dependencies on other (user-defined) declarations.
-/

namespace Examples

theorem add_comm_nat (a b : Nat) : a + b = b + a := Nat.add_comm a b

theorem id_eq {α : Type} (x : α) : id x = x := rfl

-- universe polymorphic statement
theorem const_app {α : Sort u} {β : Sort v} (a : α) (b : β) :
    (fun _ => a) b = a := rfl

-- a literal in the statement
theorem two_plus_two : (2 : Nat) + 2 = 4 := rfl

-- a user-defined definition that a theorem depends on
def double (n : Nat) : Nat := n + n

theorem double_eq (n : Nat) : double n = 2 * n := by
  simp [double, Nat.two_mul]

-- depends on a user-defined inductive
inductive Tree where
  | leaf : Tree
  | node : Tree → Tree → Tree

def Tree.size : Tree → Nat
  | .leaf => 1
  | .node l r => l.size + r.size

theorem size_pos (t : Tree) : 0 < t.size := by
  induction t with
  | leaf => decide
  | node l r ihl _ => simp [Tree.size]; omega

end Examples
