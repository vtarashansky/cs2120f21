-- ∀(n:ℕ),2^0 + 2^1 + ... 2^n = 2^(n+1) -1

def pp : nat → nat 
| (0) := 1
| (n'+1) :=   (pp n') +  (n'.succ) 