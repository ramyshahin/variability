import Var.SPL

open SPL

namespace Test0

inductive Feats
| FA
| FB
| FC
deriving Repr, DecidableEq

--open Feats
--def lFeats : List Feats := [FA, FB, FC]

/-
instance Feats_Finite: Fintype Feats := Fintype.ofList lFeats
  (by
    intro x
    apply @Feats.casesOn (λ x ↦ x ∈ lFeats)
    repeat simp [lFeats]
  )


instance featSet: FeatureSet Feats where
  fin_Features := inferInstance
  decEq_Features :=inferInstance
-/

def s : SPL Feats := SPL.mk

def pc0 := PC.Atom Feats.FA
def pc1: PC Feats := Feats.FB
def pc2 := pc0 &&& pc1
def pc3:PC Feats := Feats.FB ||| Feats.FC
def pc4 := ~~~pc0

#eval pc0 = pc2

def cp := singletonCP.split pc0
#eval pc2

-- lifted values
def l0 := Variational.mk cp (λ _ ↦  8)

def ρ₀ : @Config Feats := {Feats.FA}
def ρ₁ : @Config Feats := {Feats.FA, Feats.FB}

def x := cp⟦ρ₀⟧
def y := cp⟦ρ₁⟧

#print Quotient.eq

#eval x = y
end Test0
