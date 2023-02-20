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
#eval (checkTotal (list.map semantics [pc₁, pc₃]))


-- should fail
--def p₁ : ConfigPartition := {ConfigPartition . pcs := [pc₁, pc₃]}


def v₁ : Var := Var.mk p₁ [7, 3]
#eval v₁

#eval index {FB} v₁
#eval index {FC} v₁
#eval index {FA} v₁

-- should fail
--def v₂ : Var := Var.mk {ConfigPartition . pcs := [pc₁, pc₃]} [7, 3]

#eval p₁
#eval (to_bool (is_eqv p₁ {FB} {FC}))
#eval (is_eqv p₁ {FB} {FA})