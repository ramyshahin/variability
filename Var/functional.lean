-- functional.lean
-- variability-aware functional programming
import .variability
--import data.fintype
--import data.finset
--import tactic.basic
--import order.boolean_algebra
--import order.bounded_lattice

namespace functional

variables {α β : Type}

section func 

--instance fin_fin_power {α : Type} [t : fintype α]: fintype (finset (finset α)) :=
--{ elems := finset.powerset (finset.univ.powerset) ,
--  complete :=
--  begin 
--    intros, apply finset.subset_univ, apply finset.mem_univ
--  end}

--def allProducts := allConfigs Feature L

open variability 

open variability.PC

--@[simp]
def disjoint {Feature : Type} [fintype Feature] [decidable_eq Feature]
    (pc₁ pc₂: @PC Feature) : Prop := ⟦And pc₁ pc₂⟧ = ∅ 

lemma conj_preserves_disjoint {Feature : Type} [fintype Feature] [decidable_eq Feature] :
    ∀ (pc₁ : @PC Feature) (pc₂ : PC) (c : PC), disjoint pc₁ pc₂ → disjoint (And c pc₁) (And c pc₂) :=
    begin 
        --simp,   -- ∀ (pc₁ pc₂ c : PC), semantics (And pc₁ pc₂) = ∅ → 
                -- semantics (And (And c pc₁) (And c pc₂)) = ∅ 
        intros pc₁ pc₂ c h, -- semantics (And (And c pc₁) (And c pc₂)) = ∅
        unfold disjoint, unfold disjoint at h,
        unfold semantics, -- semantics c ∩ semantics pc₁ ∩ (semantics c ∩ semantics pc₂) = ∅
        unfold semantics at h, -- a : semantics pc₁ ∩ semantics pc₂ = ∅ 
        simp, 
        rw finset.inter_comm _ (semantics pc₂),
        rw← finset.inter_assoc (semantics pc₁),
        rw h, 
        rw finset.empty_inter, simp 
    end

--@[simp]
def disjointList {Feature : Type} [t : fintype Feature] [decidable_eq Feature]
    (vs : list (@PC Feature)) : Prop :=
    ∀ (x y : PC) , x ∈ vs → y ∈ vs → x ≠ y → disjoint x y

def cover {Feature : Type} [t : fintype Feature] [d : decidable_eq Feature]
    (v : list (@PC Feature)) := 
    semantics(list.foldr Or None v)

/-
lemma disj_cover {Feature : Type} [t : fintype Feature] [d : decidable_eq Feature] :
    ∀ (l₁ l₂ : list (@PC Feature)) (x y : PC), 
        x ∈ l₁ → y ∈ l₂ → cover l₁ ∩ cover l₂ = ∅ → disjoint x y :=
begin
    intros l₁ l₂ x y h₁ h₂ h₃, unfold disjoint, unfold semantics,
    induction l₁,
    simp at h₁, by_contradiction, exact h₁,
    apply l₁_ih, simp at h₁,  
end -/

structure PCPartition {Feature: Type} [t : fintype Feature] [decidable_eq Feature] :=
    (pcs  : list (@PC Feature))
    (disj : disjointList pcs)
    (comp : cover pcs = allConfigs)

def getPC {Feature: Type} [t : fintype Feature] [d: decidable_eq Feature]
    (c : @Config Feature t) : (list (@PC Feature)) → @PC Feature
| [] := None
| (x :: xs) := ite (c ∈ ⟦x⟧) x (getPC xs)

def pRel {Feature: Type} [t : fintype Feature] [d: decidable_eq Feature] (p : @PCPartition Feature t d)
    (c₁ : @Config Feature t) (c₂ : @Config Feature t) : Prop :=
getPC c₁ p.pcs = getPC c₂ p.pcs

lemma pRelReflexive {Feature: Type} [t : fintype Feature] [d: decidable_eq Feature] (p : @PCPartition Feature t d) :
    ∀ (c : Config), pRel p c c :=
begin
    intros c, unfold pRel 
end

lemma pRelSymmetric {Feature: Type} [t : fintype Feature] [d: decidable_eq Feature] (p : @PCPartition Feature t d) :
    symmetric (pRel p) :=
begin
    unfold symmetric, intros c₁ c₂ h, unfold pRel, unfold pRel at h, rw h 
end

lemma pRelTransitive {Feature: Type} [t : fintype Feature] [d: decidable_eq Feature] (p : @PCPartition Feature t d) :
    ∀ (c₁ c₂ c₃: Config), pRel p c₁ c₂ → pRel p c₂ c₃ → pRel p c₁ c₃  :=
begin
    intros c₁ c₂ c₃ h₁ h₂, unfold pRel, unfold pRel at h₁, unfold pRel at h₂,
    rw h₁, rw← h₂
end
 
lemma pRelEquiv {Feature: Type} [t : fintype Feature] [d: decidable_eq Feature] (p : @PCPartition Feature t d) :
    equivalence (pRel p) :=
⟨pRelReflexive p, ⟨pRelSymmetric p, pRelTransitive p⟩⟩

structure Lifted {Feature: Type} [t : fintype Feature] [decidable_eq Feature] (α : Type) := 
    (s : list (@Var Feature t α))
    (nonEmpty : ¬s.empty)
    (disj : disjointList s)
    (comp : cover s = allConfigs)

postfix `↑`:(max+1) := Lifted


--lemma exists_config {Feature: Type} [t : fintype Feature] [d : decidable_eq Feature] (α : Type) :
--    ∀ (x : @Lifted Feature t d α) (c : @Config Feature t), ∃ (v : @Var Feature t α), v ∈ x.s → c ∈ ⟦v.pc⟧ :=
--begin
--    intros, 
--end

def index' {Feature: Type} [t : fintype Feature] [decidable_eq Feature] {α : Type}
    (x : α↑) (c : Config) : list (@Var Feature t α) :=
let xs := list.filter (λ (y : @Var Feature t α), c ∈ ⟦y.pc⟧) x.s in xs 

#print equivalence
lemma unique_index' {Feature: Type} [t : fintype Feature] [decidable_eq Feature] {α : Type} :
    ∀ (x : α↑) (c : @Config Feature t), list.length (index' x c) = 1 :=
begin
    --intros x c, 
    unfold index', simp, intros x c, 
    -- base case
    simp, apply x.nonEmpty,   
end

--@[simp]
def apply_single {Feature : Type} [t: fintype Feature] [d: decidable_eq Feature] {α β : Type}
    (f : @Var Feature t (α → β)) (u : α↑) : list (@Var Feature t β) :=
    let sat := list.filter (λ(v : Var), ⟦And f.pc v.pc⟧ ≠ ∅) u.s in
    list.map (λ(v':Var), Var.mk (f.v v'.v) (And f.pc  v'.pc)) sat
 
lemma apply_single_disj {Feature : Type} [t: fintype Feature] [d: decidable_eq Feature] {α β : Type} : 
    ∀ (f : @Var Feature t (α → β)) (u : @Lifted Feature t d α), disjointList (apply_single f u) :=
begin
    unfold apply_single, simp,
    intros f u, unfold disjointList, simp, intros x y x₁ h₁ h₂ h₃ x₂ h₄ h₅ h₆ h₇, 
    rw[←h₃,←h₆], simp, apply conj_preserves_disjoint,
    apply u.disj, exact h₁, exact h₄,
    rw [←h₃, ←h₆] at h₇, simp at h₇, apply h₇
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
        unfold semantics, unfold semantics at ih, simp at ih, rw ih,
        rw finset.inter_distrib_left     
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

lemma disjoint_append {Feature : Type} [t: fintype Feature] [d: decidable_eq Feature] {α β : Type} :
    ∀ (l₁ l₂ : list (@Var Feature t Feature)), cover l₁ ∩ cover l₂ = ∅ → disjointList l₁ → disjointList l₂ → disjointList (l₁ ++ l₂) :=
begin
    intros l₁ l₂ h₁ h₂ h₃,
    unfold disjointList, intros x y h₄ h₅ h₆,
    simp at h₄, simp at h₅, 
    apply or.elim h₄,
    -- assume x ∈ l₁
    intro h₇, apply or.elim h₅, 
    -- and assume y ∈ l₁
    intro h₈, unfold disjointList at h₂,
    apply h₂, exact h₇, exact h₈, exact h₆, 
    -- now assume y ∈ l₂
    intro h₈, 
    -- base case
    simp, exact h₃,
    -- induction
    simp, unfold disjointList, intros x y h₄ h₅ h₆,
    simp at h₄, apply or.elim h₄,
    -- case 1
    intro h₇, 
end

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

lemma cover_append {Feature : Type} [t: fintype Feature] [d: decidable_eq Feature] {α : Type} : 
    ∀ (l₁ l₂ : list (@Var Feature t α)),
    cover (list.append l₁ l₂) = cover l₁ ∪ cover l₂ :=
begin
    intros, induction l₁,
    -- base case
    simp, unfold cover, simp, unfold semantics, simp,
    -- induction
    unfold cover, simp, unfold semantics, unfold cover at l₁_ih, simp at l₁_ih, 
    rw l₁_ih, rw← finset.union_assoc, cc 
end
--#print finset.has_lift.lift
#check finset.inter_univ

lemma interAll {α : Type} {c: finset α} [d: decidable_eq α] [t: fintype α]:
    (c ∩ finset.univ) = c := 
begin
    intros, --lift finset.univ to (set α) using finset.lift,
    --finish[set.inter_eq_self_of_subset_left],
    apply finset.inter_univ
end 
 
lemma apply_inner_complete {Feature : Type} [t: fintype Feature] [d: decidable_eq Feature] {α β : Type} : 
    ∀ (f : @Lifted Feature t d (α → β)) (v : @Lifted Feature t d α),
    cover (apply_inner f v) = cover f.s :=
begin
    intros, unfold apply_inner, induction f.s,
    -- base case
    simp, refl,
    -- induction,
    simp, rw cover_append, simp at ih, rw ih, rw apply_single_cover, rw v.comp,
    simp, unfold cover, simp, unfold semantics   
end

def apply {Feature : Type} [t: fintype Feature] [d: decidable_eq Feature] 
    (f : @Lifted Feature t d (α → β)) (v : @Lifted Feature t d α) : @Lifted Feature t d β :=
    ⟨apply_inner f v,
     _,
     apply_inner_complete⟩

end func

end functional