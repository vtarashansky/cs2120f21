import ..instructor.lectures.lecture_23
import tactic.ring
namespace relation


--qbu8hp Vlad Tarashansky


-- PRELIMINARY SETUP

/-
Preliminary set up. For the rest of this file,
we specify an arbitrary binary relation, r, on
an arbitrary type, β, as a two-place predicate, 
with infix notation x ≺ y for (r x y). One can
pronounce these expressions in English as "x is
related to y".
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺` : 50 := r  


/-
The default Lean libraries are missing definitions
for the assympetric property of relations and for
the notion of a powerset. We define these terms for
use in the rest of this file.
-/
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x
def powerset (s : set β) := { s' | s' ⊆ s}


-- PROBLEMS

/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
  unfold asymmetric reflexive,
  assume ex assym,
  assume refl,
  cases ex with b pf,
  have rbb:= refl b,
  have nrbb:= assym rbb,
  contradiction,
end
/-  ENGLISH : If we have a non empty set of type beta and a relation on two betas is asymmetric then it is not reflexive
It suffices to prove that if the relation is also reflexive we get a cotradiction. So if the relation is reflexive 
we can get a proof of any element, b, of type beta is relatd to itself, r b b. Then beccause the relation is asymmetric r b b→ ¬ r b b. 
With these proofs that b is related to itself and b is not related to itself we arrive at a contradiction. -/

/-answer : If the type β is uninhabited then it is asymmetric and reflexive because there are no cases of either predicate.
Universal quantification over an empty set is true. -/

/-
#2. Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. See the question at
the very bottom of the page here:
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html

Is the conjecture actually logically valid? If not, what condition 
needs to be added to make it so? Try prove this/his version of the
conjecture, as articulated slightly differently below. If you get
stuck, then you need to figure out an additional condition that needs 
to be added as a premise to make the proposition true. In that case,
add the premise and then show that the updated conjecture is true.
-/
example : (∃ (b : β), true)→  transitive r → reflexive r → ¬ asymmetric r :=
begin
   unfold transitive reflexive asymmetric,
  assume  ex tran refl,
  assume asymm,
  cases ex with b pf,
  have bb:= refl b,
  have as:= asymm bb,
  contradiction,
end





/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof of, this proposition.
-/
example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
  assume s s1 s2,
  assume s1s s2s,
  assume s1s2 s2s1,
  apply set.ext,
  assume x,
  apply iff.intro,
    assume xs1,
    apply s1s2 xs1,
    assume xs2,
    apply s2s1 xs2,
  
end
/-ENGLISH: To prove that subset 1,s1, equals subset 2,s2, given that they are both in a powerset of the same set
and that they are subsets of each other you must prove that for all values of a type that value exists in both set 1 and set 2. 
Because set 1 is a subset of set 2 then any value in set 1 is in set 2 and because set 2 is a subset of set 1 then any value in set 1 is in set 2. 
So set 1 and set 2 contain the same values and are therefore equal.-/





/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/
def divides (m n : ℕ) := ∃ k, n = k * m


/- 
#4: Formally and informally state and prove each of the following
propositions. Remember that the ring tactic is useful for producing
proofs of simple algebraic equalities involving + and *. You can use
the phrase, "by basic algebra" when translating the use of this tactic
into English. (Or if you wanted to be truly Hobbit-like you could say 
"by the ring axioms!")
-/

-- A: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
begin
  assume n,
  unfold divides,
  apply exists.intro n,
  ring,
end
/-To prove that 1 divides n you must prove that there exists a value, k, for which n = k*1. 
If you use n as that value then you must prove that n = n*1. This can be proved by using basic algebra.-/

-- B. For any n, n divides n
example : ∀ n, divides n n :=
begin
  assume n,
  unfold divides,
  apply exists.intro 1,
  ring,
end

/-To prove that n divides n you must prove that there exists a value, k, for which n = k*n. 
If you use 1 as that value then you must prove that n = 1*n. This can be proved by using basic algebra.-/




-- #C. prove that divides is reflexive 
example : reflexive divides :=
begin
  unfold reflexive,
  assume n,
  unfold divides,
  apply exists.intro 1,
  ring,
end 
/-To prove that divides is reflexive it suffices to prove that for all values, n, n divides n.To prove that 
n divides n you must prove that there exists a value, k, for which n = k*n. 
If you use 1 as that value then you must prove that n = 1*n. This can be proved by using basic algebra.-/



-- #D. prove that divides is transitive
example : transitive divides :=
begin
  unfold transitive divides,
  assume x y z xdivy ydivz,
  
 -- apply exists.intro 1,
  cases xdivy with m1 xdy,
  cases ydivz with m2 ydz,
  apply exists.intro (m1*m2),
  rw ydz,
  rw xdy,
  ring,
end 

/-To prove that divides is transitive you  must prove, given three values, x y z, and given that
 x divides y and y divides z, that x divides z. To do this you do a case analysis on proofs of 
 x divides y and y divides z. Then to prove that x divides z you must prove there exists a value, k, for which
 z = k * x. That value of k will be that multiliers value in the proofs of x divides y and y divides z. Lets call those multipliers m1 and m2,respectively.
 If we use m1*m2 as our k value then it suffices to prove that z = m1*m2*x. Rewriting this equation using y divides x and x divides x then using basic algebra proves it.-/

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

-- it is not symmetric because 6/3 = 2 but 3/6 does 
--not yield a natural number. So 3 divides 6 but 6 does not divide 3. 
--There is no k of type Nat that satisfies 3= k*6.

/- 
#F. Prove that divides is antisymmetric. 
-/


example : anti_symmetric divides := 
begin   
  
  unfold anti_symmetric divides,
  assume x y  xdy ydx,
  
  cases xdy with q xdy,
  cases ydx with w ydx,
  rw ydx,
  have cmon: w=1:=sorry,
  rw cmon,
  ring,


end


/- #4
Prove the following propositions. Remember that
throughout this file, each definition implicitly
includes β as a type and r as an arbitrary binary 
relation on β. In addition to formal proofs, give
an English language proof of the last of the three
problems.
-/

-- A
example : asymmetric r → irreflexive r :=
begin
  unfold asymmetric irreflexive,
  assume assym,
  assume x,
  assume xx,
  have nxx:= assym xx,
  contradiction,
end

-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive transitive asymmetric,
  assume irr trans,
  assume x y rxy,
  have nyy:= irr y,
  apply not.intro,
  assume ryx,
  have yy:= trans ryx rxy,
  contradiction,
end

-- C----------------------------------------------------------------
example :  transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive symmetric irreflexive,
  assume  trans nsym,
  assume irr,
  
      --try to prove if transitive must be symm
  --apply nsym,
  --assume x y xy,
      --can get proof of ¬ r x x   and  ¬ r y y
      --Transitive does not imply symmetric  Dead End

  --nothing else to try here
  sorry
end

--attempt with elements
example : (∃ (x y z: β), true)→ transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive symmetric irreflexive,
  assume  e trans nsym,
  assume irr,
  cases e with x e,
  cases e with y e,
  cases e with z pf,
  --cant do much unless you add a symmetric relation into the assumptions. But this invalidates everything.
sorry
end


end relation
