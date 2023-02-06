-- variability_test.lean
-- testing the variability module
import data.set tactic data.setoid.partition  data.finset
import .variability

open variability

def FA: Feature := @fin.mk n 0 (begin rw n, simp end)
def FB: Feature := @fin.mk n 1 (begin rw n, simp end)
def FC: Feature := @fin.mk n 2 (begin rw n, simp end)

def pc₁ : PC := (FeatureExpr.Atom FA)
def pc₂ : PC := FeatureExpr.Not pc₁
def pc₃ := (FeatureExpr.Atom FB)
def pc₄ := FeatureExpr.And pc₁ pc₃
def pc₅ := FeatureExpr.Or pc₁ pc₂

def s₁ := ⦃pc₁⦄
def s₂ := ⦃pc₂⦄

#eval s₁
#eval s₂

open setoid

#eval ⦃pc₄⦄
#eval ⦃pc₅⦄

#eval (checkDisj (list.map semantics [pc₁, pc₂]))
#eval (checkTotal (list.map semantics [pc₁, pc₂]))
def p₁ : ConfigPartition := {ConfigPartition . pcs := [pc₁, pc₂]}

#eval (checkDisj (list.map semantics [pc₁, pc₃]))
#eval (checkTotal [pc₁, pc₃])


-- should fail
--def p₁ : ConfigPartition := {ConfigPartition . pcs := [pc₁, pc₃]}

def v₁ : Var := Var.mk [(7,pc₁), (3,pc₂)]
#eval v₁

#eval index {Feat_B} v₁
#eval index {Feat_C} v₁
#eval index {Feat_A} v₁

-- should fail
--def v₂ : Var := Var.mk [(7,pc₁), (3,pc₃)]

#eval p₁
#eval (to_bool (is_eqv p₁ {Feat_B} {Feat_C}))
#eval (is_eqv p₁ {Feat_B} {Feat_A})