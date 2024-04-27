import Mathlib.Init.Set
import Mathlib.Data.Set.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Fintype.Basic

import Var.SPL

namespace liftedSet

opaque F: Type
opaque α: Type
opaque β: Type
opaque γ: Type

abbrev vset (F: Type) (α : Type) := Set (α × @SPL.Config F)

@[simp]
def vset.index {F α : Type} (s: vset F α) (ρ: @SPL.Config F) : Set α :=
    λ x ↦ s (x, ρ)

instance vset.Variational {F α : Type} : @SPL.Variational F (Set α) (vset F α) :=
    ⟨ vset.index ⟩

instance vset.Inhabited {F α: Type}: Inhabited (vset F α) :=
⟨λ (_, ρ) ↦ ρ = ∅⟩

instance liftedSet_has_mem2 {F α:Type} :
    Membership (α × (@SPL.Config F)) (vset F α) :=
    inferInstance

lemma index_mem {F α: Type} (x:α) (ρ: @SPL.Config F) (s: vset F α):
    (x ∈ ((s|ρ) : Set α)) = ((x, ρ) ∈ s) :=
by
    simp [vset.Variational, Set.mem_def]

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
    simp [Set.union_def]
    simp [index_mem]
    simp [vset.Variational]
    unfold vset.index
    simp [vset.index, Set.union, Set.union_def, Set.mem_def, setOf]

end liftedSet
