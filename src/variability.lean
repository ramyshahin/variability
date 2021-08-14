import data.finset
import data.setoid.partition

namespace variability

section 

parameters {Features : Type} [decidable_eq Features] [fintype Features]
variables  {α :Type}

@[reducible]
def Config : Type := finset Features

@[simp]
def allConfigs : finset Config := finset.univ

inductive PC : Type
| All  : PC 
| None : PC
| Atom : Features → PC 
| Not  : PC → PC
| And  : PC → PC → PC
| Or   : PC → PC → PC

open PC list 

def semantics : PC → finset Config
| (All)         := allConfigs
| (None)        := ∅
| (Atom f)      := allConfigs.filter (λ p, f ∈ p)
| (Not pc)      := allConfigs.filter (λ p, p ∈ (semantics pc))
| (And pc₁ pc₂) := (semantics pc₁) ∩ (semantics pc₂)
| (Or  pc₁ pc₂) := (semantics pc₁) ∪ (semantics pc₂)

local notation `⟦` p `⟧` := semantics p
#print finset.map
-- configuration partition
structure ConfigPartition := 
 (pcs: finset PC) (p: setoid.indexed_partition semantics)

-- annotated value (AVal)
structure AVal := (v : α) (pc : PC)

/-
def cover {Feature : Type} [t : fintype Feature] [d : decidable_eq Feature] {α : Type}
    (v : list (@Var Feature t α)) : finset Config := 
    semantics(foldr Or None (map Var.pc v))

inductive disjointVars {Feature : Type} [t : fintype Feature] [d : decidable_eq Feature] {α : Type} : (list (@Var Feature t α)) → Prop
| nil_disjoint : disjointVars [] 
| cons_disjoint : ∀ (x : @Var Feature t α) (xs: list (@Var Feature t α)), ⟦x.pc⟧ ∩ cover xs = ∅ → disjointVars (x :: xs)
-/

def disjointPCs {α : Type} (s: list (@AVal α)) : Prop := 
    ∀ (c : Config) (pc₁ pc₂ : PC), pc₁ ∈ map (AVal.pc) s → pc₂ ∈ map (AVal.pc) s → 
                                   c ∈ semantics pc₁ → c ∈ semantics pc₂ → pc₁ = pc₂

def completePCs {α : Type} (s: list (@AVal α)) : Prop :=
    ∀ (c : Config), ∃ (v : AVal), v ∈ s ∧ c ∈ semantics v.pc

structure Var {α : Type} :=
    (s    : list (@AVal α))
    (disj : disjointPCs s) 
    (comp : completePCs s)

--postfix `↑`:(max+1) := Var

section 

open classical

lemma list_find {α : Type} (q : α → Prop) [decidable_pred q] : ∀ (l : list α), 
                            (∃ y, y ∈ l ∧ q y) → (list.find q l).is_some := 
begin
    intros l h₁, --apply exists.elim h₁, intros a h₂, 
    induction l,
    -- base case
    apply exists.elim h₁, intros a h₂, apply and.elim h₂, intros h₃ h₄, simp, 
    apply not_mem_nil a h₃,
    -- induction
    unfold find, cases decidable.em (q l_hd) with hpos hneg,
    { rw if_pos hpos, simp },
    { rw if_neg hneg, apply exists.elim h₁, intros a h₂, apply l_ih, apply exists.intro a,
      simp at h₂, rw and.comm at h₂, rw and_or_distrib_left at h₂, apply or.elim h₂, 
      {intro h₃, apply and.elim h₃, intros h₄ h₅, rw← h₅ at hneg, contradiction},
      {intro h₃, rw and.comm, exact h₃}
    } 
end

end --section

def index {α : Type} (v : Var) (ρ : Config) : α :=
let pred := λ (u : @AVal α) , ρ ∈ semantics u.pc,
    r    := find pred v.s in 
if  h : r.is_some 
then (option.get h).v
else false.elim 
begin 
    apply h, apply (list_find pred v.s (v.comp ρ))
end
 
lemma index_unique {α : Type} (l1 : @Var α) (x : @AVal α) (ρ : Config)  
    : x ∈ l.s → ρ ∈ semantics x.pc → (index l ρ) = x.v :=
begin
    intros h1 h2, 
    unfold index, simp, split_ifs, 
    {rw option.get_of_mem, simp,  }
end
#print list.find_mem 

infix `|` := index

/-
def PCPartition {Feature: Type} [t : fintype Feature] [d: decidable_eq Feature] {α : Type} 
    (v : @Lifted Feature t d α) : list (@PC Feature) := 
    map (Var.pc) v.s
-/

def apply' {Feature : Type} [t: fintype Feature] [d: decidable_eq Feature] {α β : Type}
    (f : @Lifted Feature t d (α → β)) (v : @Lifted Feature t d α) : list (@Var Feature t β) :=
    let pairs := f.s.product v.s,
        satPairs := filter (λ (p : ((@Var Feature t (α → β)) × Var α)) , ⟦p.1.pc⟧ ∩ ⟦p.2.pc⟧ ≠ ∅) pairs
    in  map (λ (p : (Var (α → β) × Var α)), Var.mk (p.1.v p.2.v) (And p.1.pc p.2.pc)) satPairs

lemma apply'_disjoint {Feature : Type} [t: fintype Feature] [d: decidable_eq Feature] {α β : Type} :
    ∀ (f : @Lifted Feature t d (α → β)) (v : @Lifted Feature t d α), disjointPCs (apply' f v) := 
begin
    intros f v, unfold apply', simp, unfold disjointPCs, intros c pc₁ pc₂ h1 h2 h3 h4,
    simp at h1, simp at h2, apply exists.elim h1, intros, apply exists.elim ᾰ, intros,
    apply and.elim ᾰ_1, intros, apply and.elim ᾰ_2, intros, apply and.elim ᾰ_4, intros, 
    apply exists.elim h2, intros, apply exists.elim ᾰ_8, intros,
    apply and.elim ᾰ_9, intros, apply and.elim ᾰ_10, intros, apply and.elim ᾰ_12, intros,
    rw← ᾰ_3 at h3, unfold semantics at h3, simp at h3, 
    rw← ᾰ_11 at h4, unfold semantics at h4, simp at h4, 
    rw← ᾰ_3, rw← ᾰ_11, have : a.pc = a_2.pc, 
    apply f.disj, simp, existsi a, split, apply ᾰ_6, refl,
    simp, existsi a_2, split, apply ᾰ_14, refl,
    apply h3.left, apply h4.left,
    rw this, have : a_1.pc = a_3.pc,
    apply v.disj, simp, existsi a_1, split, apply ᾰ_7, refl, 
    simp, existsi a_3, split, apply ᾰ_15, refl,   
    apply exists.elim h1, intros a h5, apply exists.elim h5,
    intros a_1 h6, apply and.elim h6, intros h7 h8, apply h3.right, apply h4.right,
    rw this
end

lemma apply'_complete {Feature : Type} [t: fintype Feature] [d: decidable_eq Feature] {α β : Type} :
    ∀ (f : @Lifted Feature t d (α → β)) (v : @Lifted Feature t d α), completePCs (apply' f v) := 
begin
    intros f v, unfold apply', simp, unfold completePCs, intros, simp, 
    have : ∃ (v₁ : Var (α → β)), v₁ ∈ f.s ∧ c ∈ ⟦v₁.pc⟧, apply f.comp, apply exists.elim this, intros, 
    have : ∃ (v₂ : Var α), v₂ ∈ v.s ∧ c ∈ ⟦v₂.pc⟧, apply v.comp, apply exists.elim this, intros,
    existsi (Var.mk (a.v a_1.v) (a.pc.And a_1.pc)), simp, split, 
    existsi a, existsi a_1, split, split, split, exact ᾰ.left, exact ᾰ_1.left,  
    apply finset.ne_empty_of_mem, simp, split, apply ᾰ.right, apply ᾰ_1.right,
    simp, unfold semantics, simp, split, apply ᾰ.right, apply ᾰ_1.right
end

def apply {Feature : Type} [t: fintype Feature] [d: decidable_eq Feature] {α β : Type}
    (f : @Lifted Feature t d (α → β)) (v : @Lifted Feature t d α) : @Lifted Feature t d β :=
⟨apply' f v, apply'_disjoint f v, apply'_complete f v⟩

theorem apply_correct {Feature : Type} [t: fintype Feature] [d: decidable_eq Feature] (α β : Type) :
    ∀ (f : @Lifted Feature t d (α → β)) (v : @Lifted Feature t d α) (ρ : @Config Feature t),
    index (apply f v) ρ = (index f ρ) (index v ρ) :=
begin
    intros f v ρ, 
end

end section

end variability
