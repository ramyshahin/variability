import data.finset
import data.set

namespace liftedSet

universes u v 

variables {α β γ : Type}

def PC := Prop
structure Var (α : Type) := 
    (v : α) (pc : PC) 

def set' (α : Type) [fintype α] [decidable_eq α]: Type := α → PC

@[class]
structure has_index (α : Type) {β : Type} :=
(index_ : α → PC → β )

def index {α:Type} [fintype α] [decidable_eq α]
    (s : set' α) (pc : PC) : set α := (and pc) ∘ s

protected def mem {α:Type} [fintype α] [decidable_eq α] 
    (x : Var α) (s : set' α) : Prop := x.2 → (s x.1)

instance {α:Type} [fintype α] [decidable_eq α]: 
    has_mem (Var α) (set' α) := ⟨liftedSet.mem⟩

protected def subset {α:Type} [fintype α] [decidable_eq α]
    (s₁ s₂ : set' α) : Prop := ∀ a, a ∈ s₁ → a ∈ s₂

instance {α:Type} [fintype α] [decidable_eq α]: 
    has_subset (set' α) := ⟨ liftedSet.subset ⟩

protected def sub {α : Type} [fintype α] [decidable_eq α] 
    (s₁ s₂ : set' α) : set' α := λ (a : α), s₁ a ∧ ¬ (s₂ a)

instance {α:Type} [fintype α] [decidable_eq α]: 
    has_sub (set' α) := ⟨ liftedSet.sub ⟩

protected def union {α:Type} [fintype α] [decidable_eq α]
    (s₁ s₂ : set' α) : set' α := λ x, (s₁ x) ∨ (s₂ x)

instance {α:Type} [fintype α] [decidable_eq α]: 
    has_union (set' α) := ⟨liftedSet.union⟩

protected def diff {α:Type} [fintype α] [decidable_eq α] 
    (s₁ s₂ : set' α) : set' α := λ x, (s₁ x) ∧ ¬(s₂ x)

instance {α: Type } [fintype α] [decidable_eq α]: 
    has_sdiff (set' α) := ⟨liftedSet.diff⟩

def image_ {α:Type} {β:Type} [fintype α] [decidable_eq α]
    (f : α → β) (s : set' α) : set (β × PC) :=
        {y: β×PC | ∃ x, (y.1 = f x) ∧ (s x = y.2)}

--finset.filter 
 
--def image {α:Type} {β:Type} (f : α → β) (s : set' α) : set' β :=
--{(y,pc) | ∃ x, x ∈ α ∧ (y = f x) ∧ (s y = pc)}  
--λ x, (∀ y, f y = x ∧ s y)  

infix `|`:90 := index

variables [fintype α] [decidable_eq α] [fintype β] [decidable_eq β] [fintype γ] [decidable_eq γ]
    (f₁  : set  α → set  β) (f₂  : set  β  → set  γ)
    (f₁' : set' α → set' β) (f₂' : set' β  → set' γ)
    
theorem fun_comp_correct :
    (∀ a ρ, (f₁ (a | ρ) = (f₁' a) | ρ)) →
    (∀ b ρ, (f₂ (b | ρ) = (f₂' b) | ρ)) →
    (∀ a ρ, (f₂ ∘ f₁) (a | ρ) = ((f₂' ∘ f₁') a) | ρ) :=
begin
intros h₁ h₂ a ρ, simp, 
rw h₁, rw← h₂ 
end

end liftedSet