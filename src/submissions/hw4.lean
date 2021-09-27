-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  have pp:= em P,
  have qq:= em Q,
  apply iff.intro,
    assume npandq,
    cases pp,
    cases qq,
    apply false.elim,
    have pq:= and.intro pp qq,
    apply npandq pq,

    apply or.intro_right, exact qq,
    
    apply or.intro_left, exact pp,

    --reverse
    assume h,
    assume pq,
    have p:= and.elim_left pq,
    have q:= and.elim_right pq,
    cases h,
    contradiction,
    contradiction,
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume h,
  have pp:= classical.em P,
  have qq:= classical.em Q,
  cases pp,
  cases qq,
  
  apply false.elim,
  apply h,
  apply or.intro_left, exact pp,

  apply false.elim,
  apply h,
  apply or.intro_left,exact pp,

  cases qq,

  apply false.elim,
  apply h,
  apply or.intro_right, exact qq,

  apply and.intro pp qq,



end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro,
  assume h,
  cases h,
  apply or.intro_left, exact h,

  apply or.intro_right, exact and.elim_right h,

  --reverse
  assume h,
  cases h,
  apply or.intro_left, exact h,
  have pp:= em P,
  cases pp,
  apply or.intro_left, exact pp,

  apply or.intro_right, apply and.intro pp h,
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro,
  assume h,
  have l:= and.elim_left h,
  have r:= and.elim_right h,
  cases l,
    apply or.intro_left, exact l,
  cases r,
     apply or.intro_left, exact r,

    apply or.intro_right, exact and.intro l r,
  --reverse
  assume h,
  cases h,
    apply and.intro,
      apply or.intro_left, exact h,
      apply or.intro_left, exact h,
    have q:= and.elim_left h,
    have r:= and.elim_right h,
    apply and.intro,
      apply or.intro_right, exact q,
      apply or.intro_right, exact r,

end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro,
  assume l,
  have porq:= and.elim_left l,
  have rors:= and.elim_right l,
  cases porq,
  cases rors,

    apply or.intro_left, exact and.intro porq rors,

    apply or.intro_right,
    apply or.intro_left, exact and.intro porq rors,

  cases rors,

    apply or.intro_right,
    apply or.intro_right,
    apply or.intro_left,  exact and.intro porq rors,

    apply or.intro_right,
    apply or.intro_right,
    apply or.intro_right, exact and.intro porq rors,

    --reverse
    assume h,
    cases h,
    have p:= and.elim_left h,
    have r:= and.elim_right h,
    apply and.intro _ _,
       apply or.intro_left, exact p,
       apply or.intro_left, exact r,

    cases h,
    have p:= and.elim_left h,
    have s:= and.elim_right h,
    apply and.intro _ _,
       apply or.intro_left, exact p,
       apply or.intro_right, exact s,
    
    cases h,
    have q:= and.elim_left h,
    have r:= and.elim_right h,
    apply and.intro _ _,
       apply or.intro_right, exact q,
       apply or.intro_left, exact r,
    
    have q:= and.elim_left h,
    have s:= and.elim_right h,
    apply and.intro _ _,
       apply or.intro_right, exact q,
       apply or.intro_right, exact s,

end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ∃ (n:ℕ),n≠0:=
begin
  apply exists.intro 2,
  assume p:2=0,
  have pp: 2=2:= eq.refl 2,
  contradiction,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q ,
  apply iff.intro,
  have pp:= em P,
  assume h,
  cases pp,
    apply or.intro_right, apply h pp,

    apply or.intro_left, exact pp,
  --reverse
  assume h,
  assume p,
  have pp:= em P,
  cases pp,
  cases h,
    contradiction,
    exact h,

    contradiction,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume h,
  assume nq,
  have pp:= em P,
  cases pp,
    have q:= h pp,
    contradiction,

    exact pp,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P H hyp h,
  have pp:= em P,
  cases pp,
    exact pp,

  have nh:= hyp pp,
  contradiction,
end

