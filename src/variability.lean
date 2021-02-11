import data.set
import data.finset

import .SPL

open SPL

namespace variability

--constants {Feature : Type} 
--constants [t : fintype Feature] 
--constants [d : decidable_eq Feature]
--constants {L : SPL}
--parameters (L : SPL Feature)
 
constants {L : SPL}

section var 

inductive PC : Type
| All
| None
| Atom : Feature → PC 
| Not  : PC → PC
| And  : PC → PC → PC
| Or   : PC → PC → PC 
 
section PCSemantics

open PC

--def allProducts := allConfigs Feature L
#check @SPL 
def semantics : PC → finset Config
| All           := L.allConfigs
| None          := ∅
| (Atom f)      := L.allConfigs.filter (λ p, f ∈ p)
| (Not pc)      := L.allConfigs.filter (λ p, p ∈ (semantics pc))
| (And pc₁ pc₂) := (semantics pc₁) ∩ (semantics pc₂)
| (Or  pc₁ pc₂) := (semantics pc₁) ∪ (semantics pc₂)

end PCSemantics


structure Var (α : Type) := (v : α) (pc : PC)

structure Lifted (α : Type) := 
    (s : list (Var α))
    (disjoint : ∀ p q : Var α, p ∈ s ∧ q ∈ s ∧ p ≠ q → (semantics (PC.And p.pc q.pc)) = ∅)
    (complete : semantics(list.foldr (PC.Or) (PC.None) (list.map (Var.pc) s)) = allProducts)

/-
def set' (α : Type v) : Type v := α → PC

end var

@[class]
structure has_index (α : Type) {β : Type} :=
(index_ : α → PC → β )

def index (s : set' α) (pc : PC) : set α := (and pc) ∘ s

instance : has_index (set' α) := --(set β):= 
⟨variability.index⟩ 

protected def mem (x : Var α) (s : set' α) : Prop := 
    x.2 → (s x.1)

instance : has_mem (Var α) (set' α) := ⟨variability.mem⟩

protected def subset (s₁ s₂ : set' α) : Prop :=
    ∀ a, a ∈ s₁ → a ∈ s₂

instance : has_subset (set' α) := ⟨ variability.subset ⟩

protected def sub {α : Type u} (s₁ s₂ : set' α) : set' α :=
    λ (a : α), s₁ a ∧ ¬ (s₂ a)

instance : has_sub (set' α) := ⟨ variability.sub ⟩

protected def union (s₁ s₂ : set' α) : set' α :=
    λ x, (s₁ x) ∨ (s₂ x)

instance : has_union (set' α) :=
⟨variability.union⟩

def image (f : α → β) (s : set' α) : set' β :=
λ x, (∀ y, f y = x ∧ s y)  

infix `|`:90 := index

variables (f  : set  α → set  β) (g  : set  β  → set  γ)
variables (f' : set' α → set' β) (g' : set' β  → set' γ)
theorem fun_comp_correct :
    (∀ a ρ, (f (a | ρ) = (f' a) | ρ)) →
    (∀ b ρ, (g (b | ρ) = (g' b) | ρ)) →
    (∀ a ρ, (g ∘ f) (a | ρ) = ((g' ∘ f') a) | ρ) 
    :=
begin
intros h₁ h₂ a ρ, simp, 
rw h₁, rw← h₂ 
end
-/

end var

notation `⟦` p `⟧` := (semantics p)
postfix `↑`:(max+1) := Lifted

end variability
