-- ∀(n:ℕ),2^0 + 2^1 + ... 2^n = 2^(n+1) -1
import algebra.algebra.basic tactic.ring
def expo2:ℕ →ℕ 
|(0)  := 1
|(x+1) := 2* expo2 x

def P: ℕ → ℕ 
| 0:= 1
| (n+1) :=  P n + expo2 n 


example: ∀(n:ℕ ),1+ P n  = expo2 n+1 :=
begin
  assume n,
  induction n with n n_ih,
  unfold P,
  unfold expo2,

  simp[P],
  --rw expo,
  rw add_comm,
  rw nat.succ_eq_add_one,
  unfold expo2,
  rw add_assoc,
  rw add_comm,
  rw add_assoc,
  rw add_comm,
  rw n_ih,
  
  


  
  



 end