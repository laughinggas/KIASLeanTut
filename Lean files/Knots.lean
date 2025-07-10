import Mathlib

/- We attempt to define links, and hence knots in terms of tangles. A tangle is a building block of a knot. The fundamental pure tangles we define are the over crossing, under crossing, cap, cup, empty, identity (single strand), and a horizontal composition of these. We then use this to also define braids. Your task is to understand this construction, prove intermediate lemmas, and define the trefoil knot in this framework. The construction uses inductive operators. -/

namespace Knots

/-- The 5 fundamental tangles with horizontal composition. -/
-- The fundamental pure tangles are "constructors", and help with inductively building tangles.
inductive Tangle.Pure : ℕ → ℕ → Type*
| over : Pure 2 2
| under : Pure 2 2
| cap : Pure 0 2
| cup : Pure 2 0
| nil : Pure 0 0
| id' : Pure 1 1
| tensor {a b c d : ℕ} : Pure a b → Pure c d → Pure (a + c) (b + d)

namespace Tangle.Pure

/-- The identity braid on n strands. -/
-- We use induction on the natural number `n` to define this
def id : (n : ℕ) → Pure n n
| 0 => nil
| n + 1 => (id n).tensor id'

-- Don't worry about this definition, it is used to make sure that we don't need to keep used to identify `Pure n m` with `Pure m m` if `n = m`.
def eqToTangle {n m : ℕ} : n = m → Pure n m | rfl => id _

-- #check Pure

/-- The condition for a pure tangle to be a braid. -/
def isBraid {n m : ℕ} : Pure n m → Prop
| Pure.over => True
| under => True
| cap => False
| cup => False
| nil => True
| id' => True
| tensor p q => isBraid p ∧ isBraid q

lemma id_isBraid : ∀ {n : ℕ}, isBraid (id n)
-- Prove this using induction on `n`. You can use the tactic `trivial`. Note that you can inductively call the lemma in the successor case.
| 0 => by sorry
| _ + 1 => by sorry

-- What is this lemma saying?
lemma isBraid.eq {n m : ℕ} : {t : Pure n m} → t.isBraid → n = m
| Pure.over, _ => sorry
| under, _ => sorry
| nil, _ => sorry
| id', _ => sorry
| tensor p q, h => by 
  -- If you have `h : a ∧ b`, you can extract `a` by using `h.1` and `b` by using `h.2`.
  sorry

end Tangle.Pure

/-- A tangle is either a pure tangle or the vertical composition of tangles. -/
inductive Tangle : ℕ → ℕ → Type*
| pure {a b : ℕ} : Tangle.Pure a b → Tangle a b
| sum {a b c : ℕ} : Tangle a b → Tangle b c → Tangle a c

namespace Tangle

-- Instead of writing sum, we can use the notation `//`
infixr:min " // " => sum

/-- Don't worry about this, makes sure that `n=m` does not cause complications. -/
def eqToTangle {n m : ℕ} : n = m → Tangle n m := fun h => pure (.eqToTangle h)

-- We are tagging this lemma with `simp`, when you call `simp`, it will consider this lemma.
@[simp] lemma eqToTangle_rfl {n : ℕ} : eqToTangle (Eq.refl n) = pure (.id n) := rfl

/-- The condition for a tangle to be a braid. -/
def isBraid {n m : ℕ} : Tangle n m → Prop
| pure t => t.isBraid
| sum t u => isBraid t ∧ isBraid u

lemma isBraid.eq {n m : ℕ} : (t : Tangle n m) → t.isBraid → n = m
-- Use induction!
| pure p, h => by sorry
| sum t u, h => by sorry

/-- The height of a tangle is the number of pure tangles in the stack. -/
@[simp] def height : {n m : ℕ} → Tangle n m → ℕ
| _, _, pure _ => 1
| _, _, sum t u => height t + height u + 1

/-- Horizontal composition of tangles. -/
def hcomp {a b c d : ℕ} : Tangle a b → Tangle c d → Tangle (a + c) (b + d)
| pure p, pure q => pure (p.tensor q)
| pure p, sum t u => sum (hcomp (pure p) t) (hcomp (pure (Pure.id _)) u)
| sum t u, pure q => sum (hcomp t (pure q)) (hcomp u (pure (Pure.id _)))
| sum t u, sum t' u' => sum (hcomp t t') (hcomp u u')
termination_by x y => height x + height y

-- Use the notation `||` for horizontal composition of tangles.
infixr:20 " || " => hcomp

/-- A planar diagram corresponding to a link is a (0, 0)-tangle. -/
abbrev Link : Type* := Tangle 0 0

/-- The trivial link/knot. -/
def Unknot : Link := pure .cap // pure .cup

def stackedCap : (n : ℕ) → Tangle 0 (2 * n)
| 0 => pure Pure.nil
| n + 1 =>
    pure .cap //
    pure (.id 1) || stackedCap n || pure (.id 1) //
    eqToTangle (by omega)

-- define stackedCup
-- define the Trefoil knot
-- can you define isotopy?

end Tangle

end Knots