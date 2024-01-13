import data.finset
import data.set

namespace liftedSet

universes u v 

variables {α β γ : Type}

def PC := Prop
structure Var (α : Type) := 
    (v : α) (pc : PC) 

def set' (α : Type) /-[fintype α] [decidable_eq α]-/: Type := α → PC

@[class]
structure has_index (α : Type) {β : Type} :=
(index_ : α → PC → β )

--def to_finset {α: Type} [f: fintype α] (s: set α): finset α :=
--set.finite.to_finset --to_finset 
--set.finite.coe_to_finset (set.finite.of_fintype s)
    --set.univ_finite_iff_nonempty_fintype f f.elems ∩ s 
    --@set.to_finset α s (set.finite.fintype (@set.fintype α f)) -- ↥s)

#print finset.finite_to_set
#print fintype.of_finset
#print finset.fintype_coe_sort
#print set.finite.coe_sort_to_finset
#print finset.finite_to_set_to_finset

--@[simp]
--noncomputable
--def to_finite {α: Type} [f: fintype α] (s: set α) : finset α :=
    --set.finite.coe_to_finset 
--    (set.finite.of_fintype s).to_finset

--noncomputable
def index {α:Type} --[f: fintype α] [decidable_eq α]
    (s : set' α) (pc : PC) : set α := ((and pc) ∘ s)
        --@set.to_finset α ((and pc) ∘ s) (fintype.of_finset f) --(@finset.fintype α f)

--protected def mem {α:Type} [fintype α] [decidable_eq α] 
--    (x : Var α) (s : set' α) : Prop := x.2 → (s x.1)

--instance {α:Type} [fintype α] [decidable_eq α]: 
--    has_mem (Var α) (set' α) := ⟨liftedSet.mem⟩

--@[simp]
instance liftedSet_has_mem {α:Type}: --[fintype α] [decidable_eq α]: 
    has_mem α (set' α) := ⟨λx s, s x⟩

protected def subset {α:Type} --[fintype α] [decidable_eq α]
    (s₁ s₂ : set' α) : Prop := ∀ a, a ∈ s₁ → a ∈ s₂

instance {α:Type}:-- [fintype α] [decidable_eq α]: 
    has_subset (set' α) := ⟨ liftedSet.subset ⟩

protected def sub {α : Type}-- [fintype α] [decidable_eq α] 
    (s₁ s₂ : set' α) : set' α := λ (a : α), s₁ a ∧ ¬ (s₂ a)

instance {α:Type}:-- [fintype α] [decidable_eq α]: 
    has_sub (set' α) := ⟨ liftedSet.sub ⟩

protected def union {α:Type}-- [fintype α] [decidable_eq α]
    (s₁ s₂ : set' α) : set' α := λ x, (s₁ x) ∨ (s₂ x)

instance {α:Type}:-- [fintype α] [decidable_eq α]: 
    has_union (set' α) := ⟨liftedSet.union⟩

protected def diff {α:Type}-- [fintype α] [decidable_eq α] 
    (s₁ s₂ : set' α) : set' α := λ x, (s₁ x) ∧ ¬(s₂ x)

instance {α: Type }:-- [fintype α] [decidable_eq α]: 
    has_sdiff (set' α) := ⟨liftedSet.diff⟩

infix `|`:90 := index

--def image_ {α:Type} {β:Type} --[fintype α] [decidable_eq α]
--    (f : α → β) (s : set' α) : set (β × PC) :=
--        {y: β×PC | ∃ x, (y.1 = f x) ∧ (s x = y.2)}

--finset.filter 
 
#print set.image
#print finset.subtype.fintype

instance or_is_commutative: is_commutative PC or := ⟨ λ a b, propext (or_comm a b) ⟩
instance or_is_associative: is_associative PC or := ⟨ λ a b _, propext (or_assoc a b) ⟩

def image {α:Type} [fintype α] {β:Type} 
(f : α → β) (s : set' α) : set' β :=
λ x, let r := {z | f(z) = x} in 
    finset.fold or true s (set.finite.to_finset (set.finite.of_fintype r))   

lemma index_image {α: Type} [fintype α] {β: Type} (f: α→β) (s: set' α) (pc: PC):
    (image f s) | pc = set.image f (s|pc) :=
begin 
    --rw set.image, 
    rw image, unfold set.finite.to_finset, rw index, rw function.comp, rw set_of, apply funext, intros, 
    simp, split, 
    {intros h, apply and.elim h, intros h₁ h₂, let y:α,   } 
end

lemma index_union {α: Type} (x: α) (pc: PC) (s₁ s₂: set' α): 
    (x ∈ s₁|pc ∨ x ∈ s₂|pc) = (x ∈ (s₁ ∪ s₂)|pc) :=
begin
    intros, repeat {rw index}, repeat {rw function.comp}, 
    repeat {rw set.mem_def}, simp, rw← and_or_distrib_left, refl 
end

lemma index_mem {α: Type} (x:α) (pc: PC) (s: set' α):
    (x ∈ s|pc) = ((x ∈ s) ∧ pc) :=
begin
    unfold index, unfold function.comp, unfold has_mem.mem,
    unfold set.mem, rw and_comm
end

-- filter
def filter {α: Type} (p: α → Prop) (s: set' α): 
    set' α := λx, p x ∧ s x

/-
theorem filter_correct {α:Type} [fintype α] [decidable_eq α] (p: α → Prop) (s: set' α) (pc: PC) [decidable_pred p]:
    filter p s | pc = finset.filter p (s | pc) :=
begin
    unfold index, repeat {unfold function.comp}, unfold filter,
    simp, rw finset.finite_to_set_to_finset, rw set.to_finset, 
end 
-/

variables --[fintype α] [decidable_eq α] [fintype β] [decidable_eq β] [fintype γ] [decidable_eq γ]
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