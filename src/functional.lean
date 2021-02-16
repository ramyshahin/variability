-- functional.lean
-- variability-aware functional programming
--import .variability
--import data.fintype
import data.finset
import tactic.basic
import order.boolean_algebra
import order.bounded_lattice

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
 
@[simp]
def Config {Feature : Type} [fintype Feature] : finset Feature := 
    finset.univ 

--instance fin_fin_power {α : Type} [t : fintype α]: fintype (finset (finset α)) :=
--{ elems := finset.powerset (finset.univ.powerset) ,
--  complete :=
--  begin 
--    intros, apply finset.subset_univ, apply finset.mem_univ
--  end}

@[simp]
def allConfigs {Feature : Type} [t1 : fintype Feature] : finset (finset Feature)
    := finset.univ 

--def allProducts := allConfigs Feature L

open PC

--@[simp]
def semantics {Feature : Type} [fintype Feature] [decidable_eq Feature]
    : PC → finset (finset Feature)
| (All) := allConfigs
| (None):= ∅
| (Atom f)      := allConfigs.filter (λ p, f ∈ p)
| (Not pc)      := allConfigs.filter (λ p, p ∈ (semantics pc))
| (And pc₁ pc₂) := (semantics pc₁) ∩ (semantics pc₂)
| (Or  pc₁ pc₂) := (semantics pc₁) ∪ (semantics pc₂)

structure Var {Feature: Type} [fintype Feature] {α : Type} := 
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
def disjointList {Feature : Type} [t : fintype Feature] [decidable_eq Feature] {α : Type}
    (vs : list (@Var Feature t α)) : Prop :=
    ∀ (x y : Var) , x ∈ vs → y ∈ vs → x.pc ≠ y.pc → disjoint x.pc y.pc

def cover {Feature : Type} [t : fintype Feature] [d : decidable_eq Feature] {α : Type}
    (v : list (@Var Feature t α)) := 
    semantics(list.foldr Or None (list.map (Var.pc) v))

structure Lifted {Feature: Type} [t : fintype Feature] [decidable_eq Feature] (α : Type) := 
    (s : list (@Var Feature t α))
    (disj : disjointList s)
    (comp : cover s = allConfigs)

notation `⟦` p `⟧` := (semantics p)
postfix `↑`:(max+1) := Lifted

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