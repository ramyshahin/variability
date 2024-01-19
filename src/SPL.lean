-- SPL.lean
-- Software Product Line variability
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset
namespace SPL

opaque FEAT_COUNT: ℕ
def Feature : Type := Fin FEAT_COUNT
instance Feature_finite : Fintype Feature := Fin.fintype FEAT_COUNT
instance Feature_decidableEq : DecidableEq Feature := instDecidableEqFin FEAT_COUNT

-- a configuration is a set of features
@[reducible]
def Config : Type := Finset Feature
instance Config.Fintype : Fintype Config := Finset.fintype
instance Config.Membership : Membership Feature Config := Finset.instMembershipFinset
-- Presence Conditions (PCs)

inductive PC : Type
| All  : PC
| None : PC
| Atom : Feature → PC
| Not  : PC → PC
| And  : PC → PC → PC
| Or   : PC → PC → PC

--
-- set membership is decidable only on finite sets of types with
-- decidable equality, so we need ConfigSpace to be a Finset
-- instead of a Set
--
@[reducible]
def ConfigSpace: Type := Finset Config

instance ConfigSpace.Fintype : Fintype ConfigSpace := Finset.fintype

@[reducible]
def allConfigs : ConfigSpace := Finset.univ

def semantics : PC → ConfigSpace
| PC.All         => allConfigs
| PC.None        => ∅
| PC.Atom f      => Set.toFinset {c: Config | f ∈ c}
| PC.Not pc      => Set.toFinset (semantics pc)ᶜ
| PC.And pc₁ pc₂ => (semantics pc₁) ∩ (semantics pc₂)
| PC.Or  pc₁ pc₂ => (semantics pc₁) ∪ (semantics pc₂)

notation "⦃" p "⦄" => semantics p

-- Var and Lifted
--section
--parameters {Feature : Type} [fintype Feature] [decidable_eq Feature]

structure Var (α : Type) := (v : α) (pc : PC)

open List

def disjointPCs {α : Type} (s : List (Var α)) : Prop :=
    ∀ (c : Config) (x₁ x₂ : Var α),
        x₁ ∈ s → x₂ ∈ s →
        c ∈ ⦃x₁.pc⦄ → c ∈ ⦃x₂.pc⦄ → x₁ = x₂

def completePCs {α : Type} (s : List (Var α)) : Prop :=
    ∀ (c : Config), ∃ (v : (Var α)), v ∈ s ∧ c ∈ ⦃v.pc⦄

structure Lifted (α : Type) :=
    (s    : List (Var α))
    (disj : disjointPCs s)
    (comp : completePCs s)

postfix:50 "↑" => Lifted
#print Decidable.predToBool
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

def index' {α: Type} (v : α↑) (ρ : Config) : Var α :=
    let pred := λ (u: Var α) ↦ ρ ∈ semantics (u.pc)
    let r    := List.find? pred v.s
    if  h : r.isSome
    then Option.get r h
    else let vs := (v.comp ρ)
         let res := (List_find pred v.s vs)
         False.elim (h res)


def index {α: Type} (v : α↑) (ρ : Config) : α :=
    (index' v ρ).v

-- this holds even if we have duplicate atoms within a lifted value
-- for example: [(7,pc₁), (5,pc₂), (7,pc₃)]. Here configurations
-- included within pc₁ and pc₃ are considered equivalent.
instance Config.Setoid {α: Type} (v: α↑): Setoid Config := {
    r := λ c₁ c₂: Config ↦ index v c₁ = index v c₂
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

def ConfigPartition {α:Type} (v:α↑) : Type := Quotient (Config.Setoid v)

end SPL
