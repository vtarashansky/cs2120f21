import algebra.algebra.basic tactic.ring 

namespace hidden

inductive nat : Type 
|zero : nat
|succ (n' : nat) : nat

def z:= nat.zero
#check z 
#reduce z 

def o:= nat.succ(z)
def t:= nat.succ(o)

#check t 
#reduce t

def f : nat :=
begin
 exact nat.succ(nat.succ t)
end


def inc' : nat → nat:=
begin
  assume n,
  exact nat.succ n
end

def inc: nat→nat
|n:= nat.succ n 


def dec:nat→nat
|(nat.zero):= nat.zero 
|(nat.succ n') := n'

def add: nat→nat→nat
|(nat.zero)(m):= m 
|(nat.succ n')(m):= /-answer for n'-/ nat.succ (add n' m)

def mul:nat→nat→nat
|(nat.zero)(m) := nat.zero 
|(nat.succ n')(m) :=  add (m) (mul n' m)/-(mul n' m)-/

def expo:nat→nat→nat
|(m)(nat.zero):= nat.zero.succ
|(m)(nat.succ n') := mul (m) (expo m n')

#reduce expo t f


def sum_to: nat→nat
|(nat.zero):= nat.zero
|(nat.succ n'):= add(sum_to n')(inc n')


theorem foo: ∀ (n:nat), P n:=

end hidden

def P : nat → Prop 
|n:= hidden.sum_to n = n*(n+1)
