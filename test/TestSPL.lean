import Var.SPL

open SPL

namespace Test0

inductive Feats
| FA
| FB
| FC
deriving DecidableEq, Repr--, FeatureSet

open Feats
def lFeats : List Feats := [FA, FB, FC]

instance Feats_Finite: Fintype Feats := Fintype.ofList lFeats
  (by
    intro x
    apply @Feats.casesOn (λ x ↦ x ∈ lFeats)
    repeat simp [lFeats]
  )

instance featSet: FeatureSet Feats where
  fin_Features := inferInstance
  decEq_Features :=inferInstance

def s : SPL Feats := SPL.mk

open Feats

def pc0 := PC.Atom FA
def pc1 := FB
def pc2 := pc0 &&& pc1
def pc3:PC Feats := FB ||| FC
def pc4 := ~~~pc0

def cp := split pc0
-- lifted values
def l0 := Lifted.mk cp (7 ::ᵥ 9 ::ᵥ Vector.nil)

end Test0
