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

instance Lifted.Setoid: Setoid (Lifted α) := {
    r := λ v₁ v₂: Lifted α ↦
}


-- indexing
def index'' (v : Lifted α) (ρ : Config) : Option (Var α) :=
    List.find? (λ (u: Var α) ↦ ρ ∈ ⦃u.pc⦄) v.s

def configRel (v : Lifted α) (c₁ c₂ : Config) : Prop :=
    index'' v c₁ = index'' v c₂

lemma configRelReflexive (v : α↑) : ∀ (ρ : Config), configRel v ρ ρ :=
begin intros ρ, unfold configRel end

lemma configRelSymmetric (v: α↑) :
    ∀ (c₁ c₂ : Config Feature), configRel v c₁ c₂ → configRel v c₂ c₁ :=
begin
    intros c₁ c₂, unfold configRel, intros h, rw h
end

lemma configRelTransitive (v: α↑) :
    ∀ (c₁ c₂ c₃: Config Feature),
        configRel v c₁ c₂ → configRel v c₂ c₃ → configRel v c₁ c₃ :=
begin
    intros c₁ c₂ c₃, unfold configRel, intros h₁ h₂, rw h₁, rw← h₂
end

theorem configRel_equiv (α : Type) (v : Lifted α) : @equivalence (Config Feature) (configRel v) :=
mk_equivalence (configRel v) (configRelReflexive v) (configRelSymmetric v) (configRelTransitive v)

instance lifted_setoid (α : Type) (v : α↑): setoid (Config Feature) :=
setoid.mk (configRel v) (configRel_equiv α v)

#print lifted_setoid

lemma index_unique (v : Lifted α) (x : Var α) (ρ : Config Feature)
    : x ∈ v.s → ρ ∈ semantics (x.pc) → (index'' v ρ) = some x :=
begin
    intros h1 h2,
    unfold index'',
    --generalize_hyp h3 : (hd :: tl) = xs,
    induction h3 : v.s generalizing x,
    -- base case
    rw h3 at h1, simp at h1, contradiction,
    -- induction
    unfold List.find, split_ifs,
    apply v.disj, rw h3, simp,
    exact h1,
    exact h,
    exact h2,
    apply ih,

    --simp, split_ifs,
    {rw option.get_of_mem, simp, }
end

end -- indexing section

end SPL
