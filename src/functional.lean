-- functional.lean
-- variability-aware functional programming
--import .variability
import data.fintype
import data.finset

namespace functional

variables {α β : Type}

section func

inductive PC (Feature : Type) : Type
| All  : PC 
| None : PC
| Atom : Feature → PC 
| Not  : PC → PC
| And  : PC → PC → PC
| Or   : PC → PC → PC 
 
def Config (Feature : Type) [fintype Feature] : finset Feature := 
    fintype.elems Feature

def allConfigs (Feature : Type) [fintype Feature] 
    := (Config Feature).powerset

--def allProducts := allConfigs Feature L

open PC

def semantics {Feature : Type} [fintype Feature] [decidable_eq Feature]
    : PC Feature → finset (finset Feature)
| (All Feature) := allConfigs Feature
| (None Feature):= ∅
| (Atom f)      := (allConfigs Feature).filter (λ p, f ∈ p)
| (Not pc)      := (allConfigs Feature).filter (λ p, p ∈ (semantics pc))
| (And pc₁ pc₂) := (semantics pc₁) ∩ (semantics pc₂)
| (Or  pc₁ pc₂) := (semantics pc₁) ∪ (semantics pc₂)

structure Var {Feature: Type} [fintype Feature] (α : Type) := 
    (v : α) (pc : PC Feature)

structure Lifted {Feature: Type} [fintype Feature] [decidable_eq Feature] (α : Type) := 
    (s : list (Var α))
    (disjoint : ∀ p q : Var α, p ∈ s ∧ q ∈ s ∧ p ≠ q → (semantics (And p.pc q.pc)) = ∅)
    (complete : semantics(list.foldr Or (None Feature) (list.map (Var.pc) s)) = allConfigs Feature)

notation `⟦` p `⟧` := (semantics p)
postfix `↑`:(max+1) := Lifted

def apply_inner {Feature : Type} [t: fintype Feature] [d: decidable_eq Feature] 
    (f : @Var Feature t (α → β)) (u : α↑) : list (@Var Feature t β) :=
    let sat := list.filter (λ(v : Var α), ⟦And f.pc v.pc⟧ ≠ ∅) u.s in
    list.map (λ(v':Var α), Var.mk (f.v v'.v) (And f.pc  v'.pc)) sat

def apply {Feature : Type} [t: fintype Feature] [d: decidable_eq Feature] 
    (f : @Lifted Feature t d (α → β)) (v : @Lifted Feature t d α) : @Lifted Feature t d β :=
    ⟨list.foldr list.append [] (list.map (λ x, apply_inner x v) f.s),
    _,
    _⟩

end func

end functional