def pythag_triple (a b c: ℕ ): Prop := a*a + b*b = c*c



example : ∃ ( a b c : ℕ ), pythag_triple a b c:=
begin
  apply exists.intro 3, 
  apply exists.intro 4,
  apply exists.intro 5,
  unfold pythag_triple,
  apply eq.refl,
end
