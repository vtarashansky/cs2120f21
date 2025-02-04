def pythag_triple (a b c: ℕ ): Prop := a*a + b*b = c*c



example : ∃ ( a b c : ℕ ), pythag_triple a b c:=
begin
  apply exists.intro 3, 
  apply exists.intro 4,
  apply exists.intro 5,
  unfold pythag_triple,
  apply eq.refl,
end
axioms
  (Person : Type)
  (Nice : Person → Prop)
  (Likes : Person → Person → Prop)

-- example : 
--   (∃ (p1 : Person), ∀ (p2 : Person), Loves p2 p1) → 
--   (∀ (p1 : Person), ∃ (p2 : Person), Loves p1 p2) :=
-- begin
--   assume h,
--   cases h with w pf,
--   assume pppp,
--   apply exists.intro w,
--   apply pf pppp,

-- end
axiom Loves : Person → Person → Prop
example:
  (∃ (p1 : Person), ∀ (p2 : Person), Loves p2 p1) → (∀ (p1 : Person), ∃ (p2 : Person), Loves p1 p2):=
begin
  assume h,
  cases h with w pf,
  assume pppp,
  apply exists.intro w,
  apply pf pppp,

end

