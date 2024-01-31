-- SPL.lean
-- Software Product Line variability
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset
namespace SPL

class FeatureSet (α: Type) where
    fin_Features: Fintype α
    decEq_Features: DecidableEq α

structure SPL (α: Type) [FeatureSet α] where

section

variable{F: Type} [FeatureSet F]
instance Features_finite: Fintype F := FeatureSet.fin_Features
instance Features_decEq:  DecidableEq F := FeatureSet.decEq_Features
variable (s: SPL F)

-- a configuration is a set of features
@[reducible]
def Config: Type :=
    Finset F

instance Config.Fintype : Fintype (@Config F) :=
    inferInstance

instance Config.DecidableEq: DecidableEq (@Config F) :=
    Finset.decidableEq

inductive PC {α:Type}: Type
| All  : PC
| None : PC
| Atom : α → @PC α
| Not  : PC → PC
| And  : PC → PC → PC
| Or   : PC → PC → PC

instance FeatureSet.toPC {F:Type} [FeatureSet F]: Coe F (@PC F) :=
    Coe.mk PC.Atom

instance {F: Type} : AndOp (@PC F) := AndOp.mk PC.And
instance {F: Type} : OrOp (@PC F) := OrOp.mk PC.Or
instance {F: Type} : Complement (@PC F) := Complement.mk PC.Not

--
-- set membership is decidable only on finite sets of types with
-- decidable equality, so we need ConfigSpace to be a Finset
-- instead of a Set
--
@[reducible]
def ConfigSpace :=
    Finset (@Config F)

instance ConfigSpace.Fintype: Fintype (@ConfigSpace F) :=
    Finset.fintype

instance ConfigSpace.Membership: Membership (@Config F) (@ConfigSpace F) :=
    inferInstance

@[reducible]
def allConfigs: @ConfigSpace F := Finset.univ

end

section

variable {F: Type} [FeatureSet F]
variable {s: SPL F}
variable (α: Type)

def semantics {F: Type} [FeatureSet F]: @PC F → @ConfigSpace F
| PC.All         => allConfigs
| PC.None        => ∅
| PC.Atom f      => Finset.filter (λc: Config ↦ f ∈ c) allConfigs
| PC.Not pc      => (semantics pc)ᶜ
| PC.And pc₁ pc₂ => (semantics pc₁) ∩ (semantics pc₂)
| PC.Or  pc₁ pc₂ => (semantics pc₁) ∪ (semantics pc₂)

notation "⦃" p "⦄" => semantics p

structure Var (α: Type) {F: Type} [fs: FeatureSet F] :=
    v   : α
    pc  : @PC F

open List

def disjointPCs (α: Type) {F: Type} [fs: FeatureSet F] (ss : List (@Var α F fs)) : Prop :=
    ∀ (c : @Config F) (x₁ x₂ : Var α),
        x₁ ∈ ss → x₂ ∈ ss →
        c ∈ ⦃x₁.pc⦄ → c ∈ ⦃x₂.pc⦄ → x₁ = x₂

def completePCs (α: Type) {F: Type} [fs: FeatureSet F] (ss : List (@Var α F fs)) : Prop :=
    ∀ (c : @Config F), ∃ (v : (Var α)), v ∈ ss ∧ c ∈ ⦃v.pc⦄

structure Lifted (α : Type) {F: Type} [fs: FeatureSet F] :=
    (s    : List (@Var α F fs))
    (disj : disjointPCs α s)
    (comp : completePCs α s)

postfix:50 "↑" => Lifted

-- List_find -- helper for index
lemma List_find {α : Type} (q : α → Prop) [DecidablePred q] :
    ∀ (l : List α), (∃ y, y ∈ l ∧ q y) → (List.find? q l).isSome :=
by
    intros l h₁
    induction l with
    -- base case
    | nil =>
        apply Exists.elim h₁
        intros a h₂
        apply And.left at h₂
        let _ := Iff.mp (List.mem_nil_iff a) h₂
        contradiction
    -- induction
    | cons x xs ih =>
        rw [List.find?]
        cases Classical.em (q x) with
        | inl hpos => simp [hpos]
        | inr hneg =>
            simp [hneg]
            apply ih
            simp at h₁
            apply Or.elim h₁
            {
                intro contra
                contradiction
            }
            {
                intro h
                exact h
            }

def index' {α: Type} [fs: FeatureSet F] (v : @Lifted α F fs) (ρ : @Config F) : @Var α F fs :=
    let pred := λ (u: Var α) ↦ ρ ∈ semantics (u.pc)
    let r    := List.find? pred v.s
    if  h : r.isSome
    then Option.get r h
    else let vs := (v.comp ρ)
         let res := (List_find pred v.s vs)
         False.elim (h res)

def index {α: Type} [fs: FeatureSet F] (v : @Lifted α F fs) (ρ : @Config F) : α :=
    (index' v ρ).v

-- this holds even if we have duplicate atoms within a lifted value
-- for example: [(7,pc₁), (5,pc₂), (7,pc₃)]. Here configurations
-- included within pc₁ and pc₃ are considered equivalent.
instance Config.Setoid {α: Type} [fs: FeatureSet F] (v: @Lifted α F fs): Setoid (@Config F) := {
    r := λ c₁ c₂: @Config F ↦ index v c₁ = index v c₂
    iseqv := {
    refl  :=
      by
        intro x
        rfl
    symm  :=
      by
        intro x y h
        rw [h]
    trans :=
      by
        intros x y z h₀ h₁
        rw[h₀,←h₁]
  }
}

def ConfigPartition {α:Type} [fs: FeatureSet F] (v: @Lifted α F fs) : Type := Quotient (Config.Setoid v)

end -- section

end SPL
