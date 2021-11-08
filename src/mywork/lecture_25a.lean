import .lecture_24

/-
BASIC SETUP
-/
namespace relations
section relation

/-
Define relation, r, as two-place predicate on 
a type, β, with notation, x ≺ y, for (r x y). 
-/
variables {α β γ : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  

/-
ORDERING RELATIONS ON A TYPE, β 
-/


/-
Define relation, r, as two-place predicate on 
a type, β, with notation, x ≺ y, for (r x y). 
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  

-- special relations on an arbitrary type, α 
def empty_relation := λ a₁ a₂ : α, false
def full_relation := λ a₁ a₂ : α, true
def id_relation :=  λ a₁ a₂ : α, a₁ = a₂ 

-- Analog of the subset relation but now on binary relations
-- Note: subrelation is a binary relation on binary relations
def subrelation (q r : β → β → Prop) := ∀ ⦃x y⦄, q x y → r x y

/-
Additional properties of relations
-/

def strongly_connected := ∀ x y, x ≺ y ∨ y ≺ x
def total := @strongly_connected β 
/-
Note: we will use "total" later to refer to a different
property of relations that also satisfy the constraints
needed to be "functions."  To avoid ambiguity we will
prefer the term, "strongly_connected," over "total."
-/

def anti_reflexive := ∀ x, ¬ x ≺ x
def irreflexive := anti_reflexive r -- sometimes used
def anti_symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x

def strict_ordering :=  asymmetric r ∧ transitive r


def ordering :=         reflexive r ∧ transitive r ∧ anti_symmetric r


def partial_order :=    reflexive r ∧ transitive r ∧ anti_symmetric r ∧ ¬strongly_connected r


def total_order :=      reflexive r ∧ transitive r ∧ anti_symmetric r ∧ strongly_connected r

def well_ordering := total_order r ∧ (

    ∀(s:set β),
    ∃(b:β),
      (∀ (b':β), b' ∈ s → b < b') 
      

)

end relation
end relations
