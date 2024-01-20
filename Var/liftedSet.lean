--import data.finset
--import data.set
import Mathlib.Init.Set
import Mathlib.Data.Set.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Fintype.Basic

import Var.SPL

namespace liftedSet

--universes u v

opaque α: Type
opaque β: Type
opaque γ : Type

structure Var (α : Type) :=
    (v : α) (pc : PC)

def set' (α : Type) /-[fintype α] [decidable_eq α]-/: Type := α → SPL.PC

@[class]
structure has_index (α : Type) {β : Type} :=
(index_ : α → PC → β )

--def to_finset {α: Type} [f: fintype α] (s: set α): finset α :=
--set.finite.to_finset --to_finset
--set.finite.coe_to_finset (set.finite.of_fintype s)
    --set.univ_finite_iff_nonempty_fintype f f.elems ∩ s
    --@set.to_finset α s (set.finite.fintype (@set.fintype α f)) -- ↥s)

--#print finset.finite_to_set
--#print fintype.of_finset
--#print finset.fintype_coe_sort
--#print set.finite.coe_sort_to_finset
--#print finset.finite_to_set_to_finset

--@[simp]
--noncomputable
--def to_finite {α: Type} [f: fintype α] (s: set α) : finset α :=
    --set.finite.coe_to_finset
--    (set.finite.of_fintype s).to_finset

--noncomputable
def index {α:Type} --[f: fintype α] [decidable_eq α]
    (s : set' α) (pc : SPL.PC) : Set α := --((And pc) ∘ s)
        λx ↦ if (⦃SPL.PC.And pc (s x)⦄ == ∅)
             then False
             else True
        --@set.to_finset α ((and pc) ∘ s) (fintype.of_finset f) --(@finset.fintype α f)

--protected def mem {α:Type} [fintype α] [decidable_eq α]
--    (x : Var α) (s : set' α) : Prop := x.2 → (s x.1)

--instance {α:Type} [fintype α] [decidable_eq α]:
--    has_mem (Var α) (set' α) := ⟨liftedSet.mem⟩

--@[simp]
--instance liftedSet_has_mem {α:Type}: --[fintype α] [decidable_eq α]:
--    Membership α (set' α) := ⟨λx s ↦⦃s x⦄ ≠ ∅⟩

def mem {α:Type} (x:α) (s: set' α) : SPL.PC := s x

protected def subset {α:Type} --[fintype α] [decidable_eq α]
    (s₁ s₂ : set' α) : Prop := ∀ a, a ∈ s₁ → a ∈ s₂

instance {α:Type}:-- [fintype α] [decidable_eq α]:
    HasSubset (set' α) := ⟨ liftedSet.subset ⟩

protected def union {α:Type}-- [fintype α] [decidable_eq α]
    (s₁ s₂ : set' α) : set' α := λ x ↦ (s₁ x) ∨ (s₂ x)

instance unionSet' {α:Type}:-- [fintype α] [decidable_eq α]:
    Union (set' α) := ⟨liftedSet.union⟩

protected def diff {α:Type}-- [fintype α] [decidable_eq α]
    (s₁ s₂ : set' α) : set' α := λ x ↦ (s₁ x) ∧ ¬(s₂ x)

instance {α: Type }:-- [fintype α] [decidable_eq α]:
    SDiff (set' α) := ⟨liftedSet.diff⟩

infix:90 "|" => index

--def image_ {α:Type} {β:Type} --[fintype α] [decidable_eq α]
--    (f : α → β) (s : set' α) : set (β × PC) :=
--        {y: β×PC | ∃ x, (y.1 = f x) ∧ (s x = y.2)}

--finset.filter

--#print set.image
--#print finset.subtype.fintype
instance or_is_commutative: IsCommutative PC Or where
  comm := λ _ _ ↦ propext or_comm
instance or_is_associative: IsAssociative PC Or where
  assoc := λ _ _ _ ↦ propext or_assoc

def image {α:Type} [Fintype α] {β:Type} --[Fintype β] --[DecidableEq β]
(f : α → β) (s : set' α) : set' β :=
--Finset.image f s _ _
λ x ↦ let r := {z // f z = x}
      --let fin : Fintype r := Subtype.fintype (λz ↦ f z = x)
      let es := Fintype.elems
      --let fin : Fintype r := Set.Finite.toFinset_setOf r
      Finset.fold Or True s es --(Set.Finite.ofFinset r))

/-
theorem index_image {α: Type} [Fintype α] {β: Type} (f: α→β) (s: set' α) (pc: PC):
    (image f s) | pc = Set.image f (s|pc) :=
by
    rw [Set.image]
    unfold image
    simp
    --rw [image]
    --unfold set.finite.to_finset
    rw [index]
    rw [Function.comp]
    --rw set_of
    apply funext
    rw [setOf]
    intros x
    simp
    apply Iff.intro
    {
        intros h
        apply And.elim h
        intros h₁ h₂
        let y:α,   }
-/

lemma index_union {α: Type} (x: α) (pc: PC) (s₁ s₂: set' α):
    (x ∈ s₁|pc ∨ x ∈ s₂|pc) = (x ∈ (s₁ ∪ s₂)|pc) :=
by
    intros
    repeat rw [index]
    repeat rw [Function.comp]
    repeat rw [Set.mem_def]
    simp [unionSet', liftedSet.union, and_or_left]

lemma index_mem {α: Type} (x:α) (pc: PC) (s: set' α):
    (x ∈ s|pc) = ((x ∈ s) ∧ pc) :=
by
    --rw[Set.instMembershipSet, Set.Mem]
    unfold index
    unfold Function.comp
    rw [Membership] --has_mem.mem
    rw [liftedSet_has_mem] --, Set.Mem]
    --rw and_comm


-- filter
def filter {α: Type} (p: α → Prop) (s: set' α):
    set' α := λx, p x ∧ s x

/-
theorem filter_correct {α:Type} [fintype α] [decidable_eq α] (p: α → Prop) (s: set' α) (pc: PC) [decidable_pred p]:
    filter p s | pc = finset.filter p (s | pc) :=
by
    unfold index, repeat {unfold function.comp}, unfold filter,
    simp, rw finset.finite_to_set_to_finset, rw set.to_finset,

-/

variables --[fintype α] [decidable_eq α] [fintype β] [decidable_eq β] [fintype γ] [decidable_eq γ]
    (f₁  : set  α → set  β) (f₂  : set  β  → set  γ)
    (f₁' : set' α → set' β) (f₂' : set' β  → set' γ)

theorem fun_comp_correct :
    (∀ a ρ, (f₁ (a | ρ) = (f₁' a) | ρ)) →
    (∀ b ρ, (f₂ (b | ρ) = (f₂' b) | ρ)) →
    (∀ a ρ, (f₂ ∘ f₁) (a | ρ) = ((f₂' ∘ f₁') a) | ρ) :=
by
intros h₁ h₂ a ρ, simp,
rw h₁, rw← h₂


 liftedSet
