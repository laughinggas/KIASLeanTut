import Mathlib

/- We attempt to define the Collatz function f: if n is odd, f(n) is 3n+1, and n/2 otherwise. We use the fact that every odd natural can be written as `n=2^k*m - 1`. Under the Collatz steps, we attempt to prove that this goes to `3^k*m - 1` -/

namespace Collatz

variable (n : ℕ) [NeZero n]

def k : ℕ := padicValInt 2 (n + 1)

def m : ℕ := (n + 1) / (k n)

def kResult : ℕ := 3 ^ (k n) * (m n) - 1

-- can you define k' to be the first odd integer to appear after 3^k*m - 1?

lemma OddEq (h : Odd n) : n = 2 ^ (k n) * (m n) - 1 := sorry

def ColStep : ℕ := if Odd n then (3 * n + 1) / 2 else n / 2

lemma ColStep_iter (h : Odd n) : (ColStep^[k n]) n = (kResult n) := by 
  -- Try to guess lemma names, or use LeanSearch and mathlib search
  sorry

-- can you write (and prove) the lemma that states that ColStep iterated (k + k') times gives an odd number? what is its value?

end Collatz
