-- variability_test.lean
-- testing the variability module
import data.set tactic data.setoid.partition  data.finset
import .variability

open variability

-- the auto-derive works only when data.set and tactic are imported
@[derive [fintype, decidable_eq]] inductive Features 
| Feat_A
| Feat_B
| Feat_C

open Features
instance : has_to_string Features :=
⟨λ f, match f with
      | Feat_A := "Feat_A"
      | Feat_B := "Feat_B"
      | Feat_C := "Feat_C"
      end⟩

instance : has_repr Features := ⟨to_string⟩

def T : Type := finset Features
def x : T := {Feat_A}

def p : SPL := ⟨Features⟩

def pc₁ : PC := FeatureExpr.Atom Features.Feat_A
def pc₂ : PC := FeatureExpr.Not pc₁
def pc₃ := FeatureExpr.Atom Feat_B
def pc₄ := FeatureExpr.And pc₁ pc₃
def pc₅ := FeatureExpr.Or pc₁ pc₂

def s₁ := semantics pc₁
def s₂ := semantics pc₂


#eval s₁
#eval s₂

open setoid

#eval (semantics pc₄)
#eval (semantics pc₅)

#eval (checkDisj (list.map semantics [pc₁, pc₂]))
#eval (checkTotal [pc₁, pc₂])
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