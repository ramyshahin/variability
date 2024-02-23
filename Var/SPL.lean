-- SPL.lean
-- Software Product Line variability
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Vector.Mem

namespace SPL

structure SPL (α: Type) where

section

variable{F: Type}
--instance Features_finite: Fintype F := FeatureSet.fin_Features
--instance Features_decEq:  DecidableEq F := FeatureSet.decEq_Features
variable (s: SPL F)

-- a configuration is a set of features
@[reducible]
def Config: Type := Set F
    --Finset F

instance Config.Membership: Membership F (@Config F) :=
    inferInstance

--instance Config.Fintype : Fintype (@Config F) :=
--    inferInstance

--instance Config.DecidableEq: DecidableEq (@Config F) :=
--    Finset.decidableEq

inductive PC (α:Type): Type
| All  : PC α
| None : PC α
| Atom : α → PC α
| Not  : PC α → PC α
| And  : PC α → PC α → PC α
| Or   : PC α → PC α → PC α
deriving Repr, DecidableEq

instance PC.Repr {F: Type} [Repr F]: Repr (PC F) :=
⟨ λ pc n ↦ match pc, n with
           | All, _ => "All"
           | None, _ => "None"
           | Atom a, _ => repr a
           | Not p, _ => "~~~" ++ repr p
           | And p₁ p₂, _ => "(" ++ repr p₁ ++ " &&& " ++ repr p₂ ++ ")"
           | Or p₁ p₂, _  => "(" ++ repr p₁ ++ " ||| " ++ repr p₂ ++ ")"
⟩

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
def ConfigSpace := Set (@Config F)
    --Finset (@Config F)

--instance ConfigSpace.Fintype: Fintype (@ConfigSpace F) :=
--    Finset.fintype

instance ConfigSpace.Membership: Membership (@Config F) (@ConfigSpace F) :=
    inferInstance

@[reducible]
def allConfigs: @ConfigSpace F := Set.univ --Finset.univ

end

section

--variable {F: Type} [FeatureSet F]
--variable {s: SPL F}
--variable (α: Type)

def semantics {F: Type} /-[FeatureSet F]-/: @PC F → @ConfigSpace F
| PC.All         => allConfigs
| PC.None        => ∅
| PC.Atom f      => {ρ:@Config F | f ∈ ρ} --Finset.filter (λc: Config ↦ f ∈ c) allConfigs
| PC.Not pc      => (semantics pc)ᶜ
| PC.And pc₁ pc₂ => (semantics pc₁) ∩ (semantics pc₂)
| PC.Or  pc₁ pc₂ => (semantics pc₁) ∪ (semantics pc₂)

notation "⦃" p "⦄" => semantics p

--structure Var (α: Type) {F: Type} [fs: FeatureSet F] :=
--    v   : α
--    pc  : @PC F

def disjointPCs {F: Type} /-[FeatureSet F]-/ (pcs: Set (PC F)) : Prop :=
--| nil : disjointPCs [] --F fs []
--| singleton x: disjointPCs [x]
--| cons x xs : (xs.all (λx' ↦ ⦃x⦄ ∩ ⦃x'⦄ == ∅)) → disjointPCs xs → disjointPCs (x :: xs)
    ∀ (c : @Config F) (pc₁ pc₂ : pcs),
        c ∈ ⦃pc₁.val⦄ → c ∈ ⦃pc₂.val⦄ → pc₁ = pc₂

def completePCs {F: Type} /-[FeatureSet F]-/ (pcs : Set (PC F)) : Prop :=
    ∀ (c : @Config F), ∃ (pc : pcs), c ∈ ⦃pc.val⦄

structure ConfigPartition {F: Type} := --[fs: FeatureSet F] :=
    pcs: Set (PC F)
    disjoint: @disjointPCs F pcs
    complete: @completePCs F pcs

--instance {F: Type} (cp: @ConfigPartition F): DecidableEq cp.pcs :=
--    Finset.decidableEq
/-
def index {n: ℕ} [fs: FeatureSet F] (p : @ConfigPartition F n fs) (ρ : @Config F) : PC F :=
    let i := List.findIdx (λ (x: PC F) ↦ ρ ∈ semantics x) p.pcs.toList
    let pr: i < n :=
    by
        rw[←(Vector.length_val p.pcs)]
        apply List.findIdx_lt_length_of_exists
        simp
        apply p.complete
    p.pcs.get ⟨i, pr⟩
-/
-- this holds even if we have duplicate atoms within a lifted value
-- for example: [(7,pc₁), (5,pc₂), (7,pc₃)]. Here configurations
-- included within pc₁ and pc₃ are considered equivalent.
instance Config.Setoid {F: Type}/-[fs: FeatureSet F]-/ (p: @ConfigPartition F): Setoid (@Config F) := {
    r := λ (ρ₁ ρ₂: @Config F) ↦ ∃!pc: p.pcs, ρ₁ ∈ ⦃pc.val⦄ ∧ ρ₂ ∈ ⦃pc.val⦄
    iseqv := {
        refl  := by
            intros x
            apply Exists.elim (p.complete x)
            intros a h
            apply Exists.intro a
            simp
            apply And.intro
                ( h )
                ( by
                    intros pc h₁ h₂
                    apply (p.disjoint x { val := pc, property := h₁ } a)
                    simp
                    exact h₂
                    exact h )
        symm  := by
            intro x y h
            apply Exists.elim h
            intros a h₁
            simp at h₁
            apply Exists.intro a
            simp
            apply And.intro
                ( by simp [h₁.left] )
                ( by
                    intros a' h₂ h₃ h₄
                    apply h₁.right
                    exact h₄
                    exact h₃
                )
        trans := by
            intros x y z h₀ h₁
            apply Exists.elim h₀
            intros a h₂
            simp at h₂
            apply Exists.intro a
            simp
            apply Exists.elim h₁
            intros b h₃
            simp at h₃
            have h₄: a = b := p.disjoint y a b h₂.left.right h₃.left.left
            rw [←h₄] at h₃
            apply And.intro
                (And.intro h₂.left.left h₃.left.right)
                ( by
                    intros d e h₅ _
                    have h₇ := p.disjoint x a ⟨d, e⟩ h₂.left.left h₅
                    rw[h₇]
                )
  }
}

def ConfigQuotient /-[fs: FeatureSet F]-/ (p: @ConfigPartition F) : Type := Quotient (Config.Setoid p)

def ConfigQuotient.mk {F: Type} (p: @ConfigPartition F) (ρ: @Config F) : ConfigQuotient p :=
    @Quotient.mk' _ (Config.Setoid p) ρ

notation p "⟦ " c "⟧ " => ConfigQuotient.mk p c

def singletonCP {F: Type} :=
    @ConfigPartition.mk F
        {PC.All} --::ᵥ Vector.nil)
        (by simp[disjointPCs])
        (by simp[completePCs, semantics])

def Set.split (α: Type) (s: Set α) (f: α → (α × α)) : Set α :=
Set.image (Prod.fst ∘ f) s ∪ Set.image (Prod.snd ∘ f) s


--| 0, .nil, _ => .nil
--| Nat.succ k, v, f => let p:= f v.head; p.fst ::ᵥ p.snd ::ᵥ (split k v.tail f)
lemma splitDisjoint {F: Type} {p: @ConfigPartition F} (pc: PC F):
    disjointPCs (Set.split (PC F) p.pcs (λ p ↦ (pc &&& p, ~~~pc &&& p))) :=
by
    simp[disjointPCs, Set.split]
    intros c a h₀ b h₁ h₂ h₃
    apply Or.elim h₀
    {
        intros h₄
        apply Exists.elim h₄
        intros x h₅
        simp [←h₅.right, semantics] at h₂
        apply Or.elim h₁
        {
            intros h₆
            apply Exists.elim h₆
            intros y h₇
            simp[←h₇.right, semantics] at h₃
            have h₈ := p.disjoint c ⟨x, h₅.left⟩ ⟨y, h₇.left⟩ h₂.right h₃.right
            simp at h₈
            simp[←h₅.right, ←h₇.right, h₈]
        }
        {
            intros h₆
            apply Exists.elim h₆
            intros y h₇
            simp[←h₇.right, semantics] at h₃
            apply Not.elim h₃.left h₂.left
        }
    }
    {
        intros h₄
        apply Exists.elim h₄
        intros x h₅
        simp [←h₅.right, semantics] at h₂
        apply Or.elim h₁
        {
            intros h₆
            apply Exists.elim h₆
            intros y h₇
            simp[←h₇.right, semantics] at h₃
            apply Not.elim h₂.left h₃.left
        }
        {
            intros h₆
            apply Exists.elim h₆
            intros y h₇
            simp[←h₇.right, semantics] at h₃
            have h₈ := p.disjoint c ⟨x, h₅.left⟩ ⟨y, h₇.left⟩ h₂.right h₃.right
            simp at h₈
            simp[←h₅.right, ←h₇.right, h₈]
        }
    }

lemma splitComplete {F: Type} {p: @ConfigPartition F} (splitter: PC F): completePCs (Set.split (PC F) p.pcs (λ p ↦ (splitter &&& p, ~~~splitter &&& p))) :=
by
    simp[Set.split, completePCs]
    intros c
    apply Exists.elim (p.complete c)
    intros x h₀
    apply Or.elim (Classical.em (c ∈ ⦃splitter &&& x.val⦄))
    (
        intros h₁
        apply Exists.intro (splitter &&& x)
        apply And.intro
        (
            apply Or.intro_left
            apply Exists.intro ↑x
            simp
            exact h₁
        )
    )
    (
        intro h₁
        simp[semantics] at h₁
        apply Exists.intro (~~~splitter &&& x)
        simp[semantics]
        apply And.intro
        (
            apply Or.intro_right
            apply Exists.intro ↑x
            apply And.intro
            (
                simp
                simp
                apply And.intro
                (
                    apply Classical.byContradiction
                    intros h₂
                    simp at h₂
                    apply h₁ h₂
                    exact h₀
                    exact h₀
                )
            )
        )
    )

def ConfigPartition.split {F: Type} {p: @ConfigPartition F} (pc: PC F) : @ConfigPartition F :=
    ConfigPartition.mk
         (Set.split (PC F) p.pcs (λp ↦ ⟨pc &&& p, ~~~pc &&& p⟩))
         (splitDisjoint pc)
         (splitComplete pc)

structure Variational (α : Type) {F: Type} :=
    configs: @ConfigPartition F
    vals   : ConfigQuotient configs → α

postfix:50 "↑" => Variational

def index {α F: Type} (l:@Variational α F) (ρ:@Config F) := @ConfigQuotient.mk F l.configs ρ

notation l "[ " x "] " => index l x

end -- section

end SPL
