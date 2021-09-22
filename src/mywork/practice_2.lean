/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro
--Using introduction rule for true shows true is true.

--example : false :=   -- trick question? why?
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
Proof: We assume that P is an arbitrary but specific proposition. Then we apply introduction rule for iff.
We prove iff in the forwards direction by applying the elimination rule for or. We prove it in the backwards
direction by using introduction rule for or. QED.
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

/-
Proof: We assume P is an arbitrary but specific proposition. Then we apply introduction rule for iff. 
We prove implication in the forwards direction using intro rule of →  and elimination rule of ∧ .
Then we prove it in the backwards direction using the introduction rule for → and ∧ . QED.
-/

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
    ------reverse
    assume qp,
    apply or.elim qp,
      assume q,
      apply or.intro_right, exact q,

      assume p,
      apply or.intro_left, exact p,
end
/-
Proof: We assume P and Q are propositions. Then we apply introduction rule for iff. 
We prove iff in the forwards direction using the intro of → and eliminaton and introduction rules for ∨ . 
We prove iff in the backwards direction by applying the intro of → and elimination and introduction rules for ∨ . QED. 
-/
example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forwards
    assume pq,
    apply and.intro(and.elim_right pq) (and.elim_left pq),
  --backwards
    assume qp,
    apply and.intro(and.elim_right qp) (and.elim_left qp),
end
/-
Proof: We assume P and Q are propositions then apply intro for ↔. 
Then we prove ↔ in the forwards direction using intro for → and intro and elim for ∧ . 
We prove ↔ in the backwards direction using intro for → and intro and elim for ∧. QED. 
-/
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
/-
Proof: We assume P Q and R are propositions then apply intro for ↔ . 
To prove ↔ in the forward direcction we let p be a proof of P and qr be a proof of Q∨R using elim for ∧.
Then using the elim rule for ∨ on qr, the intro for →, the intro rules for ∧ and ∨ along with p we provvee ↔ in the forwards direction. 


-/

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
/-
  Proof: We assume P Q and R are propositions. Then
  apply introduction rule for ↔. TO prove the forwards direction
  You first use the introduction rule for → then apply elimination rule for ∨. Then using intro rule for ∧ and ∨ prove that P → (P ∨ Q) ∧ (P ∨ R).
  To prove Q ∧ R → (P ∨ Q) ∧ (P ∨ R) you use elimination rule for ∧ and intro rules for ∧ and ∨. 

  To prove iff in the backwards direction first use intro for → .
  Then use case studies on both or statements in your assumption in conjunction with introduction rule for ∨ to complete the proof.
-/
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
/-
Proof: We assume P and Q are propositions then apply the intro rule for ↔. 
To prove the forwards direction you intro for → and elimination rule for ∧. 
To prove the backwards direction you first use intro rule for → ,
then build the and statement using ∧'s intro rule along with our assumption of P and introduction rule for ∨.
-/

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
/-
  Proof: To prove P ∨ (P ∧ Q) ↔ P we first assume P Q are arbitrary but specific propositions.
  The we apply introduction rule for iff. To prove the forwards direction, P ∨ P ∧ Q → P,
  you apply intro for →. You assume P ∨ (P ∧ Q), then apply elimination rule for or on that assumption. You prove P → P by using → introduction rule.
  Then prove that P∧Q → P using ∧'s elimination rule.

  To prove iff's reverse direction, P → P ∨ P ∧ Q, We assume p as a proof of P. Then using introduction rule for ∨ and our proof p to complete our proof.
-/
example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro,
  assume portrue,
  exact true.intro,
  
  assume tr, 
  apply or.intro_right,
    apply tr,

end
/-
Proof: To prove P ∨ true ↔ true we first assume P is a proposition.
Then we apply intro rule for iff. Then we use intro rule → and assume P∨true.
We prove true using intro rule for true. 
To prove the reverse direction you assume true using → intro and then use ∨ intro rule to prove P∨true.QED
-/

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
/-
Proof: To prove P ∨ false ↔ P we first assume P is a proposition.
Then we apply intro rule for iff. to prove the forwards dirrection we assume 
P∨false. Using case studies we show that P→P and that false→P has no possible cases.
To prove the reverse direcction we assume P and using introduction rule for ∨ to prove P∨false.QED. 
-/
example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro,
    assume ptrue,
    apply and.elim_left ptrue,

    assume p,
    apply and.intro p true.intro,
end
/- 
Proof. To prove P ∧ true ↔ P we first assume P is a proposition.
Then we apply intro rule for ↔. To prove the forwards direction we assume P∧true
and use elimination rule for ∧ to prove P. To prove the reverse direction
we assume P and prove P∧true using intro rule for ∧, our assumption p, and intro rule for true.QED
-/
example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro,
  assume lft,
  apply and.elim_right lft,

  assume f,
  exact false.elim f,
end
/-
Proof: To prove P ∧ false ↔ false we have to show that both sides are always false, so we show the contradictions.
We assume P is a proposition and then apply intro rule for ↔. To proof the forwards direction
we assume P∧false using the intro for → and prove false→false using elimination rule for and. 
To prove the reverse direction we assume the premise, false, and use the elimination rule for false.
-/

