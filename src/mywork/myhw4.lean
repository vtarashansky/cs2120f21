--1
example: 0 ≠ 1 :=
begin
  assume h,
  cases h,
end


--2
example : 0 ≠ 0 → 2 = 3:=
begin
  assume h,
  apply false.elim,
  apply h,
  apply eq.refl,
end 


--3
example: ∀ (P:Prop), P → ¬¬P:=
begin
  assume P p,
  assume np,
  contradiction,
end 

--We might need classical (vs constructive) reasoning
#check classical.em 
open classical
#check em

--4 
theorem neq_elim: ∀ (P : Prop), ¬¬P → P:=
begin
  assume P nnp,
  have pornp:= em P,
  apply or.elim pornp,
    assume p,
    exact p,
  
    assume np, 
    contradiction,
end