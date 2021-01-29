import data.set

namespace variability

universes u v 

variables {α β γ : Type}

def PC := Prop

structure Var (α : Type u) := 
    (v : α) (pc : PC) 

def set' (α : Type v) : Type v := α → PC

@[class]
structure has_index (α : Type) {β : Type} :=
(index_ : α → PC → β )

def index (s : set' α) (pc : PC) : set α := (and pc) ∘ s

instance : has_index (set' β) := --(set β):= 
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

variables (f₁  : set  α → set  β) (f₂  : set  β  → set  γ)
variables (f₁' : set' α → set' β) (f₂' : set' β  → set' γ)
theorem fun_comp_correct :
    (∀ a ρ, (f₁ (a | ρ) = (f₁' a) | ρ)) →
    (∀ b ρ, (f₂ (b | ρ) = (f₂' b) | ρ)) →
    (∀ a ρ, (f₂ ∘ f₁) (a | ρ) = ((f₂' ∘ f₁') a) | ρ) :=
begin
intros h₁ h₂ a ρ, simp, 
rw h₁, rw← h₂ 
end

end variability
