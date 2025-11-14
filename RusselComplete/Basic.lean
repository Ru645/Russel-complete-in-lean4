namespace RusselComplete

inductive MyProp where
 | T : MyProp
 | F : MyProp
 deriving Repr

open MyProp

def my_or (a b : MyProp) : MyProp :=
  match a with
  | T => T
  | F => b

-- 这样是可以的
#eval (my_or T F)
-- 这样怎么搞? 不会
/-
instance : Or MyProp where
  or := my_or
#eval (T ∨ F)
-/

-- 为什么这样子可以?
namespace MyNat

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
  deriving Repr

def my_add (m n : MyNat) : MyNat :=
  match n with
  | MyNat.zero   => m
  | MyNat.succ n => MyNat.succ (my_add m n)

open MyNat

instance : Add MyNat where
  add := my_add

theorem add_zero (m : MyNat) : m + zero = m := rfl
theorem add_succ (m n : MyNat) : m + succ n = succ (m + n) := rfl
#eval (succ (succ zero)) + (succ zero)

end MyNat

end RusselComplete
