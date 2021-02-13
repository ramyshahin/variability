-- functional.lean
-- variability-aware functional programming
--import .variability
import data.fintype
import data.finset
import tactic.basic

namespace functional

variables {α β : Type}

section func

inductive PC {Feature : Type} : Type
| All  : PC 
| None : PC
| Atom : Feature → PC 
| Not  : PC → PC
| And  : PC → PC → PC
| Or   : PC → PC → PC 
 
def Config (Feature : Type) [fintype Feature] : finset Feature := 
    fintype.elems Feature

def allConfigs (Feature : Type) [fintype Feature] 
    := (Config Feature).powerset

--def allProducts := allConfigs Feature L

open PC

--@[simp]
def semantics {Feature : Type} [fintype Feature] [decidable_eq Feature]
    : PC → finset (finset Feature)
| (All) := allConfigs Feature
| (None):= ∅
| (Atom f)      := (allConfigs Feature).filter (λ p, f ∈ p)
| (Not pc)      := (allConfigs Feature).filter (λ p, p ∈ (semantics pc))
| (And pc₁ pc₂) := (semantics pc₁) ∩ (semantics pc₂)
| (Or  pc₁ pc₂) := (semantics pc₁) ∪ (semantics pc₂)

structure Var {Feature: Type} [fintype Feature] (α : Type) := 
    (v : α) (pc : @PC Feature)

--@[simp]
def disjoint {Feature : Type} [fintype Feature] [decidable_eq Feature]
    (pc₁ : @PC Feature) (pc₂ : PC) : Prop :=
    semantics (And pc₁ pc₂) = ∅ 

lemma conj_preserves_disjoint {Feature : Type} [fintype Feature] [decidable_eq Feature] :
    ∀ (pc₁ : @PC Feature) (pc₂ : PC) (c : PC), disjoint pc₁ pc₂ → disjoint (And c pc₁) (And c pc₂) :=
    begin 
        --simp,   -- ∀ (pc₁ pc₂ c : PC), semantics (And pc₁ pc₂) = ∅ → 
                -- semantics (And (And c pc₁) (And c pc₂)) = ∅ 
        intros, -- semantics (And (And c pc₁) (And c pc₂)) = ∅
        unfold disjoint, unfold disjoint at a,
        unfold semantics, -- semantics c ∩ semantics pc₁ ∩ (semantics c ∩ semantics pc₂) = ∅
        unfold semantics at a, -- a : semantics pc₁ ∩ semantics pc₂ = ∅ 
        simp, 
        rw← finset.inter_assoc,
        rw a, -- ∅ ∩ semantics c = ∅ 
        apply finset.empty_inter
    end

--@[simp]
def disjointList {Feature : Type} [t : fintype Feature] [decidable_eq Feature] {α : Type}
    (vs : list (@Var Feature t α)) : Prop :=
    ∀ (x y : Var α) , x ∈ vs → y ∈ vs → x.pc ≠ y.pc → disjoint x.pc y.pc

def cover {Feature : Type} [t : fintype Feature] [d : decidable_eq Feature] {α : Type}
    (v : list (@Var Feature t α)) := 
    semantics(list.foldr Or None (list.map (Var.pc) v))

structure Lifted {Feature: Type} [fintype Feature] [decidable_eq Feature] (α : Type) := 
    (s : list (Var α))
    (disj : disjointList s)
    (comp : cover s = allConfigs Feature)

notation `⟦` p `⟧` := (semantics p)
postfix `↑`:(max+1) := Lifted

--@[simp]
def apply_single {Feature : Type} [t: fintype Feature] [d: decidable_eq Feature] 
    (f : @Var Feature t (α → β)) (u : α↑) : list (@Var Feature t β) :=
    let sat := list.filter (λ(v : Var α), ⟦And f.pc v.pc⟧ ≠ ∅) u.s in
    list.map (λ(v':Var α), Var.mk (f.v v'.v) (And f.pc  v'.pc)) sat
 
lemma apply_single_disj {Feature : Type} [t: fintype Feature] [d: decidable_eq Feature] {α β : Type} : 
    ∀ (f : @Var Feature t (α → β)) (u : @Lifted Feature t d α), disjointList (apply_single f u) :=
begin
    unfold apply_single, simp,
    intros, unfold disjointList, simp, intros, 
    rw[←a_2,←a_5], simp, apply conj_preserves_disjoint,
    apply u.disj, apply a, apply a_3,
    rw [←a_2, ←a_5] at a_6, simp at a_6, apply a_6
end

section 
open classical

lemma apply_single_cover {Feature : Type} [t : fintype Feature] [d: decidable_eq Feature] {α β : Type} :
    ∀ (f : @Var Feature t (α → β)) (u : @Lifted Feature t d α),
    cover (apply_single f u) = ⟦f.pc⟧ ∩ cover u.s :=
begin
    intros, unfold apply_single, 
    induction u.s,
    -- base case
    simp, unfold cover, simp, unfold semantics, simp, 
    -- induction
    simp, unfold list.filter,  
    --unfold cover, simp,
    -- we need excluded middle.. this will be a classical proof
    cases decidable.em (semantics (PC.And (f.pc) (hd.pc)) = ∅) with hEmpty hNEmpty, 
    {
        rw← hEmpty, simp, rw hEmpty, simp at ih, rw ih, unfold cover, simp,
        unfold semantics, rw finset.inter_distrib_left, unfold semantics at hEmpty, 
        rw hEmpty, rw finset.empty_union   
    },
    {
        rw (if_pos hNEmpty), simp at ih, simp, unfold cover, simp, unfold cover at ih, 
        unfold semantics, unfold semantics at ih, simp at ih, simp, rw ih,
        rw finset.inter_distrib_left, simp     
    }
    
end -- section
#print 

lemma apply_single_append {Feature : Type} [t : fintype Feature] [d: decidable_eq Feature] {α β : Type} :
    ∀ (f₁ f₂ : @Var Feature t (α → β)) (u : @Lifted Feature t d α),
    disjoint f₁.pc f₂.pc → disjointList (apply_single f₁ u) → disjointList (apply_single f₂ u) →
    disjointList (list.append (apply_single f₁ u) (apply_single f₂ u)) :=
begin
    intros f₁ f₂ u,
    generalize : (apply_single f₁ u) = l₁,
    intros h₁ h₂ h₃,  
    induction l₁,
    -- base case
    simp, apply h₃, 
    -- induction
    simp, unfold disjointList at h₂, 
end

@[simp]
def apply_inner {Feature : Type} [t: fintype Feature] [d: decidable_eq Feature] 
    (f : @Lifted Feature t d (α → β)) (v : @Lifted Feature t d α) : list (@Var Feature t β) :=
    list.foldr list.append [] (list.map (λ x, apply_single x v) f.s

lemma apply_inner_disjoint {Feature : Type} [t: fintype Feature] [d: decidable_eq Feature] {α β : Type} : 
    ∀ (f : @Lifted Feature t d (α → β)) (v : @Lifted Feature t d α),
    disjointList(apply_inner f v) :=
begin
    unfold apply_inner, intros, induction f.s, 
    -- base case
    unfold disjointList, simp,
    -- induction step  
    unfold list.map, unfold list.foldr, 
    unfold disjointList, intros, 
end


def apply {Feature : Type} [t: fintype Feature] [d: decidable_eq Feature] 
    (f : @Lifted Feature t d (α → β)) (v : @Lifted Feature t d α) : @Lifted Feature t d β :=
    ⟨apply_inner f v,
    begin 
        intros, simp, intros, 
    end,
    _⟩

end func

end functional