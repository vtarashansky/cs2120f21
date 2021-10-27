import data.set

/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/
example: ∀ {α : Type}(L : set α), L ∩ L = L:=
begin
  assume α L,
  apply set.ext,
  assume a,
  apply iff.intro,
  assume ainLIL,
  cases ainLIL,
  exact ainLIL_left,


  assume ainl,
  apply and.intro ainl ainl,
  
  
end


/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/
example: ∀ {α:Type}(A B : set α), A ∪ B = B ∪ A:=
begin
  assume α A B,
  apply set.ext,
  assume x,
  apply iff.intro,
repeat{
  assume xinaub,
  cases xinaub,
  apply or.intro_right, exact xinaub,
  apply or.intro_left, exact xinaub,
}
end


        --ENGLISH 
        /- The union operator on sets is commutative. If we have two sets, 
        A and B, of a type A∪B = B∪A. This is proved by bi impllication.
        If A∪B then there is a value, x, that is in both sets. This means
        we can create a new conjunction  B∪A because x is in both B and A. 
        This works vice versa proving the bi-implication -/

/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/
example: ∀ {α:Type}( A B C: set α), A⊆A ∧ (A⊆B→ B⊆C → A⊆C):=
begin
  assume α A B C,
  apply and.intro,
  assume x,
  assume xina,exact xina,

  assume asubb,
  assume bsubc,
  assume x,
  assume xina,
  have xinb :=asubb xina,
  apply bsubc xinb,

end
/-
    Subset is reflexive that means that any set is a subset of itself.
    This is proved by assuming that we have a set, A, with any value, x,
    if x is in A then it is in the subset of A, and therefore if it is in A ,
    A can be a subset of A. 


    Subset is transitive. we prove this by having three sets, A, B, and C.
    If A is a subset of B and B is a subset of C then we must prove that A is a subset of C.
    If A is a subset of B and A contains a nonspecific value, x, then x is also in B. 
    Then B is a subset of C and B contains x so C must also contain x. So A is a subset of C because any x in A is also in C.
-/


/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/
--union associative
example: ∀{α :Type } (A B C : set α ), (A∪B)∪ C = A∪(B∪C):=
begin 
  assume α A B C,
  apply set.ext,
  assume x,
  apply iff.intro,
  assume left,
  cases left,
  cases left,
  apply or.intro_left, exact left,

  apply or.intro_right,apply or.intro_left, exact left,

  apply or.intro_right, apply or.intro_right,exact left,


  assume right,
  cases right,
  apply or.intro_left, apply or.intro_left, exact right,

  cases right,
  apply or.intro_left,apply or.intro_right,exact right,

  apply or.intro_right, exact right
end

--ENGLISH
/- Union is assiociative. We can prove this by assuming we have three 
sets, A,B, and C, and by proving (A∪B)∪ C = A∪(B∪C). To prove this biimplication
in the forwards direction we assume the left side. From this we can say that only values
that are in sets A or B will then be applied to the union operator with C and that values 
that are in A or B or C will be in the set (A∪B)∪ C. So it suffices to say
that these values are in B∪C and A∪(B∪C). This works in reverse. Union is assiociative because or is associative. 
-/


--intersect associative
example: ∀{α :Type } (A B C : set α ), (A∩ B)∩ C = A∩(B∩C):=
begin 
  assume α A B C,
  apply set.ext,
  assume x,apply iff.intro,

  assume left,
  cases left with aib c,
  cases aib with a b,

  apply and.intro a _, apply and.intro b c,

  assume right,
  cases right with a bic,
  cases bic with b c,
  apply and.intro _ c, apply and.intro a b,
end

--ENGLISH
/-
  Intersect is associative. We can prove this by assuming we have three sets, A, B, and C,
  and then proving (A∩ B)∩ C = A∩(B∩C). To prove this bi-implication in the forwards direction
  we assume the left side and from that we can say that a nonspecific value, x, is in A and B and C using basic and elimmination rules.
  Then we can construct the right side also using and intro rules. This works in both directions. 
  Intersect is associative because and is associative.
-/
/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state and prove both formally and 
informally that ∩ is left-distributive over ∩.
-/
example: ∀{α :Type } (A B C: set α ),A ∩(B ∩ C) = (A ∩ B) ∩ (A ∩ C) :=
begin
  assume α A B C,
  apply set.ext,
  assume x,
  apply iff.intro,
  assume left,
  cases left with a bic,
  cases bic with b c,
  apply and.intro,
  apply and.intro a b, apply and.intro a c,

  assume left,
  cases left with ab ac,
  cases ab with a b,
  cases ac with a c,
  apply and.intro a,
  exact and.intro b c,
end
/-
  To prove that ∩ is left-distributive over itself it suffices to prove that given three sets, A B C,
  that A ∩(B ∩ C) = (A ∩ B) ∩ (A ∩ C). To prove this bi-implication in the forward direction we
  assume that for all values, x, which are in A ∩(B ∩ C) we can get proofs that x∈A, x∈B, and x∈C.
  Using these proofs we can construct (A ∩ B) ∩ (A ∩ C) by constructing (A ∩ B) because x is in both A and B,
  then construct (A ∩ C) because x is in A and C, and finally construct (A ∩ B) ∩ (A ∩ C) because x is in (A ∩ B) and (A ∩ C).


  To prove in the reverse direction we assume the premise, (A ∩ B) ∩ (A ∩ C), and break that down into 
  proofs again that x ∈ all three sets, A B C, using and elimination rules. Then construct A ∩(B ∩ C) using 
  and intro rules and the three proofs x∈A, x∈B, and x∈C. QED.
-/





/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/
example: ∀{α :Type } (A B C: set α ),A ∪(B ∩ C) = (A ∪ B) ∩ (A ∪ C):=
begin 
  assume α A B C,
  apply set.ext,
  assume x, apply iff.intro,
  assume left,
  cases left with a bic,

  apply and.intro,
  repeat{apply or.intro_left, exact a},

  cases bic with b c,
  apply and.intro,
  apply or.intro_right,exact b,
  apply or.intro_right, exact c,
  --reverse

  assume left,
  cases left with aub auc,
  cases aub with a b,
  cases auc with a c,
  apply or.intro_left, exact a,
  apply or.intro_left, exact a,
  cases auc with a c,
  apply or.intro_left, exact a,
  apply or.intro_right, exact and.intro b c,
end

/-
  To prove that ∪ is left distributive over ∩ it suffices to prove assuming we have three sets, A B C, 
  that A ∪(B ∩ C) = (A ∪ B) ∩ (A ∪ C). To prove this in the forward direction we get proofs that 
  for all values, x, that are in the A ∪(B ∩ C) that those values are in A or in B and C. This gives us two cases
  the values are in B and C or in A. So if the values are in A we can construct the conclusion because
  it says the values must be in A or B and in A or C so values being in A satisfies both sides of the conjunction. 
  In the case that the values are in B and C then it proves the coonlusion because x∈ B satisfies the left side of the
  conjunction and x∈C satisfies the right side of the conjunction. 

  To prove in the reverse direction we assume for all values, x, x∈ (A ∪ B) ∩ (A ∪ C).
  From this we get four cases. These cases are: x∈A, x∈A ∧ x∈B, x∈A ∧ x∈C, x∈B ∧ x∈C. 
  The first,second,and third cases proves the left side of the disjunction in the conclusion.
  The fourth case proves the right side of the disjunction in the conclusion becuase x∈B ∧ x∈C means x∈B∩C.  
-/

