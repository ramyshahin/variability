-- SPL.lean
-- Software Product Line variability
--import data.fintype
import data.finset

namespace SPL

-- Features and Configurations
section 
parameters (Feature : Type) [fintype Feature] [decidable_eq Feature]

@[reducible]
def Config : Type := finset Feature  

@[reducible]
def ConfigSpace : Type := finset (finset Feature) 

end -- Features and Configurations section

-- Presence Conditions (PCs)
section 
parameters {Feature : Type} [fintype Feature] [decidable_eq Feature]

@[reducible]
def allConfigs : ConfigSpace Feature := finset.univ

inductive PC : Type
| All  : PC 
| None : PC
| Atom : Feature → PC 
| Not  : PC → PC
| And  : PC → PC → PC
| Or   : PC → PC → PC

open PC list

def semantics : PC → ConfigSpace Feature
| (All)         := allConfigs
| (None)        := ∅
| (Atom f)      := allConfigs.filter (λ p, f ∈ p)
| (Not pc)      := allConfigs.filter (λ p, p ∈ (semantics pc))
| (And pc₁ pc₂) := (semantics pc₁) ∩ (semantics pc₂)
| (Or  pc₁ pc₂) := (semantics pc₁) ∪ (semantics pc₂)

end -- section PCs

notation `⟦` p `⟧` := (semantics p)

end SPL