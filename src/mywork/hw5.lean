/-
qbu8hp  Vlad Tarashansky
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)
  (p : α → Prop)
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value ... 
-- your completed English rendition here:   ... to a β value and every α value with property p implies that 
the β value it maps to has property q,
then if there exists an object of type α with property p there will exist an object of type β with property q. 
-/


-- Give your formal proof here
begin
  assume mapfunc existsa,
  cases mapfunc with func imp,
  cases existsa with a propA,
  apply exists.intro,
  apply imp a,
  apply propA,

end
/-
Informal proof: To proof the proposition above first you assume you have a function, mapfunc, that maps every α
value to a β value that for all α values with property p its mapped β value has property q. Then you assume
there exists an α that has property p. From these assumptions we do a case study on both assumptions. This returns
the function we name func, α→β, the implication we call imp, ∀ (a : α), p a → q (func a), an α value, a, with 
property p that we call propA. What we have left to prove is that there exists a β with property q. First,
 we apply exists.intro. Then we apply our implication imp, ∀ (a : α), p a → q (func a), passing in the parameter 
of our nonspecific α value, a, then pass in our property p of a, propA to return a mapped β value with property q.

-/

/- 
PART II: BASIC SET THEORY

stay tuned!
-/
