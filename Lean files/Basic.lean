import Mathlib

/- In this file, we shall discuss the basics of Lean 4.
  This is a very quick crash course. To know more, please read: 
  · Mathematics in Lean (https://leanprover-community.github.io/mathematics_in_lean/) 
  · Theorem Proving in Lean (https://leanprover.github.io/theorem_proving_in_lean4/#) 
  · Glimpses of Lean (https://github.com/PatrickMassot/GlimpseOfLean?tab=readme-ov-file). 
  
  Don't be scared of errors, it gets better with time. If you need help, you can always ask me. Help is more swiftly and widely available on the Zulip server : https://leanprover.zulipchat.com/. 

  You can search for lemmas existing in `mathlib` here: https://leanprover-community.github.io/mathlib4_docs/ . Other AI-based search options include LeanSearch(https://leansearch.net/), Loogle (https://loogle.lean-lang.org/) and Moogle (https://www.moogle.ai/?ref=taaft).
  
  Happy Leaning! :) -/

-- First, press Alt and Z to make sure everything fits on your screen.

-- Let us start with understanding what types are.
-- Every element in Lean has a unique `Type`.
-- Let us check the inherent `Type` of `0`.
-- Remove the `--` in the beginning of the next line to uncomment it.
#check 0

-- This tells us that Lean automatically takes `0` to have type `Nat`.
-- A Type is similar to a set. It is not the same, because an element can belong to multiple sets,
-- but every element has a unique `Type`. Let us check the type of the integer `1`
#check (1 : Int)
-- To read more about this, hover on the brackets in the above line.

-- Now, uncomment the following two lines :
-- #check (-1 + 1 : Nat)
-- #eval -1 + 1
-- The first line gives an error because Lean cannot find
-- negation defined on the naturals, and so this is NOT identified as `0 : Nat`.
-- What is its type?
-- PS : You can hover on/click on elements in the InfoView, it is interactive!
-- Is this the same type as (0 : Nat)?

-- How do we relate the two? Hover over both sides of the equation below
#check (1 : Nat) = (1 : Int)
-- The RHS has type `Int`. Lean has automatically taken the RHS to be an element of type `Int`.
-- It has used a function `ofNat : Nat → Int`, to convert the LHS into the type of the RHS.
-- Such functions are called coercions.

-- Notice also that the type of this equality is `Prop`.
-- This is a special kind of type for propositions, equalities, inequalities etc.
-- The next line is another example, which I call P :
#check ∀ x, x = 0
-- Note that, if I supply a proof hP of this proposition, then hP has type P.
-- Can you construct some elements which have type `Prop`? Here is another example.
#check ∃ n : ℕ, n = 1

-- We can now try to prove the following.
-- Since both are the same, the proof is just reflexivity
-- The yellow line is a warning that there is a sorry somewhere in the proof. This is telling Lean: Ignore the proof for now, assume I know it. `by` indicates the start of a proof. Look over into the window on the right after clicking on `sorry`, you will see a goal preceded by `⊢`. All hypotheses and variables appear above this.
-- Replace `sorry` with `rfl`, you will notice the yellow line disappears.
example : ((1 : ℕ) : ℤ) = (1 : ℤ) := by sorry
-- Hover on `rfl` to see what it does
-- Congrats on your first Lean proof! :)

-- Let us now understand functions.
def fn1 (x : ℕ) : ℕ := x + (4 - 1)
#print fn1
#eval fn1 0
-- This defines `fn1`, which is given an input of `x` which has type `Nat`,
-- and gives as output a term of type `Nat`, which is defined to be `x + 3`.

-- If we remove the type of the output, Lean is able to infer it since it knows the type of `x` :
def fn2 (x : ℕ) := x + 3
#print fn2
#eval fn2 2

-- Another way to make the same definition is :
def fn3 := λ (x : ℕ) => x + 3
#print fn3
#eval fn3 4

-- Let us now turn to theorem proofs. We use tactics to prove theorems.
-- Let us try to prove that the functions we defined above are indeed the same.
lemma fn1_eq_fn3 (x : ℕ) : fn1 x = fn3 x := by sorry
-- The name of the lemma is `fn1_eq_fn2`. The statement we want to prove is put after `:`.
-- We assume `x` to be an explicit hypothesis, enclosed in round brackets.
-- Can you prove this? Once proved, you will see `No goals` in the RHS window.

lemma eqs : fn1 = fn2 := by sorry

--lets try some more examples
lemma hs : 1200000 = (500000 : ℤ) + 700000 := by sorry
#print hs

-- What does the theorem below say?
theorem t1 {p q : Prop} : p → q → p := by
-- We need some way to extract variables of type `p` and `q`. Recall that these are proofs of `p` and `q`.
-- This is done by the tactic `intro`. `intro x` will call the extracted variable `x`. 

-- `apply h` applies a lemma `h` which is present in the local or global context, while asking for proofs of any given hypotheses.

-- Try to complete the proof. Notice that each line of code that you write changes the InfoView.
  sorry

-- Try to solve this using both methods mentioned above
theorem t2 {p q r : Prop} (h₁ : q → r) (h₂ : p → q) : p → r := by sorry

theorem t3 {p : ℕ → Prop} {q r : Prop} (h₁ : q → r) (h₂ : p 0 → q) (h₃ : ∀ x, p x) : p 0 ∧ r := by 
  -- We will need `p 0`. The tactic `have` allows you add a hypothesis (to be proved) to the local context. What is the statement saying?
  have h0 : p 0 := h₃ 0
  -- You need to prove two things here: `p 0` and `r`. One way to separate this into goals is to use the `refine` tactic, which makes a new goal for every provided placeholder.
  refine' ⟨_, _⟩
  -- Now try to prove the goals!
  · sorry
  · sorry

/-- Consider the “barber paradox,” that is, the claim that in a certain town there is a (male) barber that shaves all and only the men who do not shave themselves. Prove that this is a contradiction. -/
theorem barbers_paradox {men : Type} {barber : men} (shaves : men → men → Prop) (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by 
  -- Try to prove this using what you learned above. 
  -- You can also use the tactic `simp`, which searches through some lemmas in `mathlib` and tries to simplify the expression.
  -- `simp` applies to the goal; `simp [h]` uses the lemma `h` as well; `simp at h` applies `simp` to the hypothesis `h`. If you want to see what lemmas `simp` uses, you can put `simp?`.
  sorry

example {K : Type*} [hK: Field K] : Ring K := by 
  -- here, we are using Lean's typeclass inference system. It "understands" that if `K` is a field (as given in []), then it is a ring.
  -- All we need to do is refer to the typeclass inference system. The easiest way to do it is to replace `sorry` with `infer_instance`.
  sorry

-- How about this? If you hover on `→+*`, you will see that we are asking for a ring homomorphim between 2 fields, implying that Lean knows these are rings.
example {K : Type*} [Field K] : K →+* K := by 
  -- use `RingHom.id` to solve this. Note that only the explicit hypothesis is provided, that is, the ones in the () brackets. If you don't wish to provide any hypothesis, you may use a placeholder instead.
  sorry

example {K : Type*} [Field K] (k : K) : k + 0 = k := by 
  -- What I want to do is use the lemma `add_zero` to solve this. You can use `#check` to see what `add_zero` does. 
  -- Try to solve the goal using the tactic `rw`. Given a statement `h : a = b` or `h : a ↔ b`, `rw [h]` replaces `a` in the goal with `b`, while `rw [← h]` replaces `b` in the goal with `a`.
  -- You can also use `rw` on local hypothesis `h'` by doing `rw [h] at h'`.
  sorry

example {a b c : ℤ} (h1 : 7 * a = 5 * b^2 + 30) (h2 : 2 * b^2 = 3 * a - 4) : a = -40 := by
-- There are in built tactics such as `linarith` and `linear_combination` which help with linear equations. Here are two different solutions.
--  linarith
--  apply add_right_cancel (b := 2 * a + b + 3)
  sorry

/-- The square root of 2 is irrational. -/
example : Irrational (Real.sqrt 2) := by
-- Try to solve this using the lemmas: `irrational_iff_ne_rational`, `eq_div_iff`, `mul_pow`, `padicValInt.mul`, `padicValInt.self`, `Nat.not_odd_iff_even`. If you have a different proof in mind, you can ask LeanSearch for help with the right lemma names in `mathlib`.
-- The tactic `norm_num` helps deal with coercions, `by_cases` splits the goal into cases.
-- Note that, for a proposition `p`, `¬p` is the same as `p → False`.
-- You can focus on a goal by using `·`.
-- We start by assuming a contradiction
  by_contra h
  sorry

-- Here's another way to prove the above: try using `apply?`. This searches for existing lemmas in the library that could solve this. This does exist in the library, but for the sake of knowledge, I would suggest trying to prove it yourself!

-- You have reached the end of this file, congrats! You can try the other 2 files now.