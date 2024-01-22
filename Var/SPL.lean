-- SPL.lean
-- Software Product Line variability
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset
namespace SPL

--opaque FEAT_COUNT: ℕ
--def Feature : Type := Fin FEAT_COUNT
--instance Feature_finite : Fintype Feature := Fin.fintype FEAT_COUNT
--instance Feature_decidableEq : DecidableEq Feature := instDecidableEqFin FEAT_COUNT

structure SPL where
    Features: Type
    fin_Features: Fintype Features
    decEq_Features: DecidableEq Features

--set_option trace.Meta.synthInstance true

section

--variable (Features: Type) [fin: Fintype Features]
--variable [@DecidableEq Features]

variable (s: SPL)
instance Features_finite: Fintype s.Features := s.fin_Features
instance Features_decEq:  DecidableEq s.Features := s.decEq_Features

-- a configuration is a set of features
@[reducible]
def Config: Type :=
    Finset s.Features


instance Config.DecidableEq: DecidableEq (Config s) := Finset.decidableEq

--variable {F: Type} [Fintype F] [DecidableEq F]

--instance Config.Fintype {s: SPL F} [DecidableEq (Config s)] : Fintype (Config s) := _

--instance Config.Membership  {s: SPL Features} : Membership s.Features (Config s) :=
--    Finset.instMembershipFinset
-- Presence Conditions (PCs)

inductive PC : Type
| All  : PC
| None : PC
| Atom : s.Features → PC
| Not  : PC → PC
| And  : PC → PC → PC
| Or   : PC → PC → PC

--
-- set membership is decidable only on finite sets of types with
-- decidable equality, so we need ConfigSpace to be a Finset
-- instead of a Set
--
@[reducible]
def ConfigSpace :=
    Finset (Config s)

instance ConfigSpace.Fintype: Fintype (ConfigSpace Features) :=
    Finset.fintype

instance ConfigSpace.Membership: Membership (Config s) (ConfigSpace s) :=
    inferInstance -- Finset.instMembershipFinset

--instance Config.DecidableMem {s: SPL Features} : DecidablePred (λ c:Config s ↦ x ∈ c):=
--    Set.decidableMemOfFintype (λy: s.Features ↦ y ∈ c) x

@[reducible]
def allConfigs: ConfigSpace s := Finset.univ

end

section

variable {s: SPL}
variable (α: Type)

def semantics: PC s → ConfigSpace s
| PC.All         => allConfigs s
| PC.None        => ∅
| PC.Atom f      => Finset.filter (λc: Config s ↦ f ∈ c) (allConfigs s) --Fintype.subtype Set.toFinset {c: Config s | f ∈ c}
| PC.Not pc      => (semantics pc)ᶜ
| PC.And pc₁ pc₂ => (semantics pc₁) ∩ (semantics pc₂)
| PC.Or  pc₁ pc₂ => (semantics pc₁) ∪ (semantics pc₂)

notation "⦃" p "⦄" => semantics p

--end

--section

--variable {Features: Type} [Fintype Features] [DecidableEq Features]
--variable {α: Type}
--variable (s: SPL Features)

-- Var and Lifted
--section
--parameters {Feature : Type} [fintype Feature] [decidable_eq Feature]

structure Var  :=
    v   : α
    pc  : PC s

open List

def disjointPCs {s: SPL} (ss : List (@Var s α)) : Prop :=
    ∀ (c : Config s) (x₁ x₂ : Var α),
        x₁ ∈ ss → x₂ ∈ ss →
        c ∈ ⦃x₁.pc⦄ → c ∈ ⦃x₂.pc⦄ → x₁ = x₂

def completePCs (ss : List (@Var s α)) : Prop :=
    ∀ (c : Config s), ∃ (v : (Var α)), v ∈ ss ∧ c ∈ ⦃v.pc⦄

structure Lifted (α : Type) :=
    (s    : List (@Var s α))
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

def index' {α: Type} (v : @Lifted s α) (ρ : Config s) : @Var s α :=
    let pred := λ (u: Var α) ↦ ρ ∈ semantics (u.pc)
    let r    := List.find? pred v.s
    if  h : r.isSome
    then Option.get r h
    else let vs := (v.comp ρ)
         let res := (List_find pred v.s vs)
         False.elim (h res)

def index {α: Type} (v : @Lifted s α) (ρ : Config s) : α :=
    (index' v ρ).v

-- this holds even if we have duplicate atoms within a lifted value
-- for example: [(7,pc₁), (5,pc₂), (7,pc₃)]. Here configurations
-- included within pc₁ and pc₃ are considered equivalent.
instance Config.Setoid {α: Type} (v: @Lifted s α): Setoid (Config s) := {
    r := λ c₁ c₂: Config s ↦ index v c₁ = index v c₂
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

def ConfigPartition {α:Type} (v: @Lifted s α) : Type := Quotient (Config.Setoid v)

end

end SPL
