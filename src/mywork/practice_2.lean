/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro
--Using introduction rule for true shows true is true.

--example : false :=     -- trick question? why?
  --Because false cannot be proved true. By definition false 
  --has no proofs

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward 
    assume porp,
    apply or.elim porp,
      assume p,exact p,
      assume p,exact p,
  --backwards
  assume p,
  exact or.intro_left P p,
end
/-
To prove that P or P is true if and only if P is true
-/


example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume p,
  apply iff.intro _ _,
    assume pp,
    apply and.elim_left pp,

    assume p,
    exact and.intro p p,

end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
    assume pq,
    apply or.elim pq,
      assume p, 
      apply or.intro_right,exact p,
      
      assume q,
      apply or.intro_left, exact q,
    ------do it
    assume qp,
    apply or.elim qp,
      assume q,
      apply or.intro_right, exact q,

      assume p,
      apply or.intro_left, exact p,
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --Left
    assume pq,
    apply and.intro(and.elim_right pq) (and.elim_left pq),
  --right
    assume qp,
    apply and.intro(and.elim_right qp) (and.elim_left qp),

end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
  assume pqorr,
  have p: P:= and.elim_left pqorr,
  have qr: Q ∨ R:= and.elim_right pqorr,
  apply or.elim qr,
    assume q,
    apply or.intro_left, apply and.intro p q,

    assume r,
    apply or.intro_right, apply and.intro p r,

--backwards
  assume right,
  apply or.elim right,
  assume pq,
    apply and.intro _ _,
      apply and.elim_left pq,
      
      apply or.intro_left, apply and.elim_right pq,
  assume pr,
    apply and.intro _ _,
      apply and.elim_left pr,

      apply or.intro_right, apply and.elim_right pr,  
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro,
  --forwards
  assume left,
  apply or.elim left,
    --leftside of or
      assume p,
      apply and.intro _ _, 
        apply or.intro_left, apply p,
        apply or.intro_left, apply p,
    --right side of or
      assume qr,
      have q:Q:= and.elim_left qr,
      have r:R:= and.elim_right qr,
      apply and.intro _ _,
        apply or.intro_right, exact q,
        apply or.intro_right, exact r,
  --backwards
  assume right,
  have porq: P∨Q:= and.elim_left right,
  have porr: P ∨ R:= and.elim_right right,
  ---IDK
  cases porq,
  apply or.intro_left,exact porq,
  cases porr,
  apply or.intro_left,exact porr,
  apply or.intro_right, apply and.intro porq porr,
  



end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q, 
  apply iff.intro,
  assume left,
  apply and.elim_left left,
  --backwards
  assume p,
  apply and.intro _ _,
  exact p,
  apply or.intro_left, exact p,
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  assume left,
  apply or.elim left,
    assume p,exact p,
    
    assume pq,
    apply and.elim_left pq,
  --backwards
  assume p,
  apply or.intro_left,
  apply p,
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro,
  assume portrue,
  apply or.elim portrue,
    assume p, apply true.intro,

    assume tr, exact true.intro,
  
  assume tr, 
  apply or.intro_right,
    apply tr,

end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro,
  assume lft,
  cases lft,
    apply lft,
  cases lft,

  assume p,
  apply or.intro_left, exact p,
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro,
    assume ptrue,
    apply and.elim_left ptrue,

    assume p,
    apply and.intro p true.intro,
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro,
  assume left,
  cases left,
  exact left_right,

  assume f,
  exact false.elim f,
end


