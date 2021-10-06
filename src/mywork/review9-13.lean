



namespace implies

axioms ( P Q : Prop)

def if_P_is_true_then_so_is_Q: Prop:= P → Q

--assume P is true
--assume we have a proof of P(p)
axiom p:P

axiom pq: P → Q
-- assume that we have a proof, pq, of P → Q

--intro for implies: assume premise, show conclusion
--elimination rule for implies: 

#check pq

/-
Suppose P and Q are propositionns and you 
know that P → Q and that P are both True
Show that Q is true

Proof: apply the truth of P → Q to the 
truth of P to derive the truth of Q

Proof: by the  elimination rule for → with
pq applied to p

proof: by "modus ponnens". QED
-/
end implies
namespace all
/-
FORALL
-/

axioms
  (T:Type)
  (P:T→ Prop)
  (t:T)
  (pf:∀ (x:T), P x)
  --Does t have property P?    
   --Yes bc all x of type T have P x so t must have P x
  --

  example: P t:= pf t

  #check pf t
  
end all
example : ∀ (P Q : Prop) (p2q : P → Q) (q: Q), P :=
begin
  assume P Q,
  assume p2q,
  appl imply
end