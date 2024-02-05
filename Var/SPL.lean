-- SPL.lean
-- Software Product Line variability
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Vector.Mem

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

inductive PC (α:Type): Type
| All  : PC α
| None : PC α
| Atom : α → PC α
| Not  : PC α → PC α
| And  : PC α → PC α → PC α
| Or   : PC α → PC α → PC α

instance FeatureSet.toPC {F:Type}: Coe F (PC F) :=
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

def disjointPCs {F: Type} [FeatureSet F] (pcs : List (PC F)) : Prop :=
    ∀ (c : @Config F) (pc₁ pc₂ : PC F),
        pc₁ ∈ pcs → pc₂ ∈ pcs →
        c ∈ ⦃pc₁⦄ → c ∈ ⦃pc₂⦄ → pc₁ = pc₂

def completePCs {F: Type} [FeatureSet F] (pcs : List (PC F)) : Prop :=
    ∀ (c : @Config F), ∃ (pc : PC F), pc ∈ pcs ∧ c ∈ ⦃pc⦄

structure ConfigPartition {n: ℕ} [fs: FeatureSet F] :=
    pcs: Vector (PC F) n
    disjoint: disjointPCs (Vector.toList pcs)
    complete: completePCs (Vector.toList pcs)

def index {n: ℕ} [fs: FeatureSet F] (p : @ConfigPartition F n fs) (ρ : @Config F) : {x:ℕ // x < n} :=
    let i := List.findIdx (λ (x: PC F) ↦ ρ ∈ semantics x) p.pcs.toList
    let p: i < n :=
    by
        rw[←(Vector.length_val p.pcs)]
        apply List.findIdx_lt_length_of_exists
        simp
        apply p.complete
    ⟨i, p⟩

-- this holds even if we have duplicate atoms within a lifted value
-- for example: [(7,pc₁), (5,pc₂), (7,pc₃)]. Here configurations
-- included within pc₁ and pc₃ are considered equivalent.
instance Config.Setoid {n:ℕ} [fs: FeatureSet F] (p: @ConfigPartition F n fs): Setoid (@Config F) := {
    r := λ c₁ c₂: @Config F ↦ index p c₁ = index p c₂
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

def ConfigQuotient {α:Type} [fs: FeatureSet F] (p: @ConfigPartition F n fs) : Type := Quotient (Config.Setoid p)

def split (pc: PC F) [fs: FeatureSet F] : @ConfigPartition F 2 fs :=
    ConfigPartition.mk
         (pc ::ᵥ ~~~pc ::ᵥ Vector.nil)
         (by
            simp[disjointPCs]
            intros c pc₁ pc₂ h₁ h₂ h₃ h₄
            apply Or.elim h₁
            (
                intros h₅
                apply Or.elim h₂
                (
                    intros h₆
                    simp[h₅, h₆]
                )
                intros h₆
                rw[h₆] at h₄
                rw[h₅] at h₃
                simp[Complement.complement, semantics] at h₄
                contradiction
            )
            (
                intros h₅
                apply Or.elim h₂
                (
                    intros h₆
                    rw[h₆] at h₄
                    rw[h₅] at h₃
                    simp[Complement.complement, semantics] at h₃
                    contradiction
                )
                (
                    intros h₆
                    rw[h₅,h₆]
                )
            )
         )
         (by
            simp[completePCs, Complement.complement, semantics]
            intros c
            apply Classical.em (c ∈ ⦃pc⦄)
         )

structure Lifted (α : Type) {n: ℕ} {F: Type} [fs: FeatureSet F] :=
    configs: @ConfigPartition F n fs
    vals   : Vector α n

postfix:50 "↑" => Lifted

end -- section

end SPL
