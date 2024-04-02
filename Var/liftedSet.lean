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

opaque F: Type
opaque α: Type
opaque β: Type
opaque γ: Type

--structure Var (α : Type) :=
--    (v : α) (pc : PC)

abbrev vset (F: Type) (α : Type) := Set (α × @SPL.Config F) -- → Prop

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

@[simp]
def vset.index {F α : Type} (s: vset F α) (ρ: @SPL.Config F) : Set α :=
    λ x ↦ s (x, ρ)

--noncomputable
instance vset.Variational {F α : Type} : @SPL.Variational F (Set α) (vset F α) :=
    ⟨ vset.index ⟩

--protected def mem {α:Type} [fintype α] [decidable_eq α]
--    (x : Var α) (s : set' α) : Prop := x.2 → (s x.1)

--instance {α:Type} [fintype α] [decidable_eq α]:
--    has_mem (Var α) (set' α) := ⟨liftedSet.mem⟩

instance vset.Inhabited {F α: Type}: Inhabited (vset F α) :=
⟨λ (_, ρ) ↦ ρ = ∅⟩

--instance liftedSet_has_mem {F α:Type} : --[fintype α] [decidable_eq α]:
--    Membership α (vset F α) := ⟨λx s ↦ ∃ ρ, s (x, ρ) ⟩

instance liftedSet_has_mem2 {F α:Type} : --[fintype α] [decidable_eq α]:
    Membership (α × (@SPL.Config F)) (vset F α) :=
    inferInstance

--instance vset.decidableMem {F α: Type} (x: α) (s: vset F α): Decidable (x ∈ s) :=
--    inferInstance

-- def mem {α:Type} (x:α) (s: vset α) : @SPL.PC F := s x

--protected def subset {F α:Type} --[fintype α] [decidable_eq α]
--    (s₁ s₂ : vset F α) : Prop := ∀ a, a ∈ s₁ → a ∈ s₂

--instance {F α:Type} :-- [fintype α] [decidable_eq α]:
--    HasSubset (vset F α) := ⟨ liftedSet.subset ⟩
--@[simp]
--protected def union (F α:Type) -- [fintype α] [decidable_eq α]
 --   (s₁ s₂ : vset F α) : vset F α := λ (x, ρ) ↦ s₁ (x, ρ) ∨ s₂ (x, ρ)

--instance vsetUnion (F α:Type):-- [fintype α] [decidable_eq α]:
--    Union (vset F α) := ⟨liftedSet.union F α⟩

--protected def inter {F α: Type} [Fintype α] [DecidableEq α]
--    (s₁ s₂ : vset F α) : vset F α := λ (x, ρ) ↦ s₁ (x, ρ) ∧ s₂ (x, ρ)

--instance interSet' {F α: Type} [Fintype α] [DecidableEq α]:
--    Inter (vset F α) := ⟨liftedSet.inter⟩

--protected def diff {α:Type} [Fintype α] [DecidableEq α]-- [fintype α] [decidable_eq α]
--    (s₁ s₂ : vset F α) : vset F α := λ (x, ρ) ↦ s₁ (x, ρ) ∧ ¬ s₂ (x, ρ)

--instance {α: Type } [Fintype α] [DecidableEq α]:-- [fintype α] [decidable_eq α]:
--    SDiff (vset F α) := ⟨liftedSet.diff⟩

--def image_ {α:Type} {β:Type} --[fintype α] [decidable_eq α]
--    (f : α → β) (s : set' α) : set (β × PC) :=
--        {y: β×PC | ∃ x, (y.1 = f x) ∧ (s x = y.2)}

--finset.filter

--#print set.image
--#print finset.subtype.fintype
/-
instance or_is_commutative: IsCommutative (SPL.PC F) SPL.PC.Or where
  comm := λ _ _ ↦ propext or_comm
instance or_is_associative: IsAssociative PC Or where
  assoc := λ _ _ _ ↦ propext or_assoc
-/
/-
def image {α:Type} [Fintype α] {β:Type} --[Fintype β] --[DecidableEq β]
(f : α → β) (s : vset α) : vset β :=
--Finset.image f s _ _
λ x ↦ let r := {z // f z = x}
      --let fin : Fintype r := Subtype.fintype (λz ↦ f z = x)
      let es := Fintype.elems
      --let fin : Fintype r := Set.Finite.toFinset_setOf r
      Finset.fold Or True s es --(Set.Finite.ofFinset r))
-/
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
/-
lemma index_union {α: Type} (x: α) (pc: @SPL.PC F) (s₁ s₂: vset α):
    (x ∈ s₁|pc ∨ x ∈ s₂|pc) = (x ∈ (s₁ ∪ s₂)|pc) :=
by
    simp [index]
    repeat rw [Function.comp]
    repeat rw [Set.mem_def]
    simp [unionSet', liftedSet.union, and_or_left]
-/

lemma index_mem {F α: Type} (x:α) (ρ: @SPL.Config F) (s: vset F α):
    (x ∈ ((s|ρ) : Set α)) = ((x, ρ) ∈ s) :=
by
    simp [vset.Variational, Set.mem_def]

-- filter
--def filter {α: Type} (p: α → Prop) [Fintype α] [DecidableEq α] [DecidablePred p] (s: vset F α): vset F α :=
--    λx ↦ if p x then s x else SPL.PC.None

/-
theorem filter_correct {α:Type} [fintype α] [decidable_eq α] (p: α → Prop) (s: set' α) (pc: PC) [decidable_pred p]:
    filter p s | pc = finset.filter p (s | pc) :=
by
    unfold index, repeat {unfold function.comp}, unfold filter,
    simp, rw finset.finite_to_set_to_finset, rw set.to_finset,

-/

opaque f₁  : Set  α → Set β
opaque f₂  : Set  β  → Set γ
opaque f₁' : vset F α → vset F β
opaque f₂' : vset F β  → vset F γ

theorem fun_comp_correct:
    (∀ a (ρ: @SPL.Config F), (f₁ (a | ρ) = (f₁' a) | ρ)) →
    (∀ b (ρ: @SPL.Config F), (f₂ (b | ρ) = (f₂' b) | ρ)) →
    (∀ a (ρ: @SPL.Config F), (f₂ ∘ f₁) (a | ρ) = ((f₂' ∘ f₁') a) | ρ) :=
by
    intros h₁ h₂ a ρ
    simp
    rw [h₁]
    rw [←h₂]

lemma index_union {α F: Type} (s₁ s₂ : vset F α) (ρ : @SPL.Config F):
    ((s₁ | ρ) ∪ (s₂ | ρ)) = (((s₁ ∪ s₂) | ρ): Set α) :=
by
    --simp [vsetUnion, vset.index]
    simp [Set.union_def]
    simp [index_mem]
    simp [vset.Variational]
    unfold vset.index
    simp [vset.index, Set.union, Set.union_def, Set.mem_def, setOf]

end liftedSet
