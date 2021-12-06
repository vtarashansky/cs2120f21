import algebra.algebra.basic tactic.ring





-- --Number 1
-- ∀ n, P(n)
-- by proving two lemmas
-- P(0), and ∀ n', P(n') → P(n'+1)

--Number 2
---prove 0^2+1^2 +...n^2 = (1/6)n(1+n)(1+2n)

/- To prove that for all n 0^2 + 1^2 + ...+ n^2 = (1/6) * n *(1+n)*(1+2*n)
first we rewrite it to be 6*( 0^2 + 1^2 + ...+ n^2) = n *(1+n)*(1+2*n).
Then we prove it using induction. To prove the base case, n=0, it suffices to prove
6*0 = 0*(1+0)*(1+2*0). This is proved using basic algebra. To prove the case of n+1 it suffices to
prove that 6*(0^2 + 1^2 + ...+ (n+1)^2) = (n+1) *(1+(n+1))*(1+2*(n+1))
The left side can be rewritten as 6(0^2 + 1^2 +...n^2) + 6(n+1)^2. 
We need to prove that for all n, if n has the property then n+1 has the propert we are trying to prove. 
So we have assumed that 6(0^2 + 1^2 +...n^2) = n *(1+n)*(1+2*n). Using this assumption
we can rewrite our goal to be n *(1+n)*(1+2*n) + 6(n+1)^2 = (n+1) *(1+(n+1))*(1+2*(n+1)).
Now, using basic algebra, the equation is satisfied.
-/



--Test Out


--Number 1
-- prove 0^2+1^2 +...n^2 = (1/6)n(1+n)(1+2n)

--Made my own exponent 
def expo:ℕ →ℕ →ℕ 
|(n)(0)  := 1
|(n)(x+1) := n* expo n x

def nToTwo: ℕ →  ℕ
|(0) := 0
|(n+1) := nToTwo(n) + expo (n+1) (2) 


example: ∀(n:ℕ ),6*nToTwo n = n * (n + 1) *(1+(2*n)):= 
begin
  assume n,
  induction n with n,
  unfold nToTwo,
  exact rfl,
  simp[nToTwo],
  rw mul_add,
  unfold expo,
  rw n_ih,
  rw nat.succ_eq_add_one,
  ring,
end

--Number 2

--10
example: ∀ (n:ℕ), 1*n=n:=
begin
  assume n,
  induction n with n n_ih,
  apply rfl,
  rw nat.succ_eq_add_one,
  rw mul_add,
  ring,
end
--11
example:∀( m n k:ℕ), m*(n+k) = m*n+m*k:=
begin
  assume m n k,
  rw mul_add, -- this is a rule in 17.4
  -- induction n,
  -- rw mul_add,
  -- rw nat.succ_eq_add_one,
  -- rw mul_add,
end

--12
example:∀( m n k:ℕ), m*(n*k) = (m*n)*k:=
begin
  assume a b c,
  --ring, done
  induction c,
  simp,
  rw nat.succ_eq_add_one,
  rw mul_assoc,
end
--13
example:∀( a b:ℕ), a*b =b*a :=
begin
  assume a b,
  induction a,
  simp,
  rw nat.succ_eq_add_one,
  ring,
end


--Extra credit
--#5

def F: ℕ→ℤ  
|(0)  := 0
|(1) := 1
|(n+2):= F(n)+F(n+1)

--Cassini
def expoNOne:ℕ → ℤ 
|(0)  := 1
|(n+1) := (-[1+0]) * expoNOne n

-- #reduce  

example:∀(n:ℕ ),F(n+2)*(F(n+1)+F(n)) - F(n+2)*F(n) = expoNOne(n):=
begin
  assume n,
  induction n with n n_ih,
  unfold F,
  unfold expoNOne,
  ring,
  --  rw nat.succ_eq_add_one,
  simp[F],
  rw nat.succ_eq_add_one,
  rw add_comm,
  rw mul_add,
  rw mul_add,
  rw mul_comm,
  rw add_comm,
  rw mul_add,
  
  
  
  
  
  

end