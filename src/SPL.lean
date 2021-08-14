-- SPL.lean
-- Software Product Line variability
--import data.fintype
import data.finset

namespace SPL

-- Features and Configurations
section 
parameters (Feature : Type) [fintype Feature] [decidable_eq Feature]

@[reducible]
def Config : Type := finset Feature   

end -- Features and Configurations section

-- Presence Conditions (PCs)
section 
parameters (Feature : Type) [fintype Feature] [decidable_eq Feature]

inductive PC : Type
| All  : PC 
| None : PC
| Atom : Feature → PC 
| Not  : PC → PC
| And  : PC → PC → PC
| Or   : PC → PC → PC

end

section
parameters {Feature : Type} [fintype Feature] [decidable_eq Feature]

@[reducible]
def ConfigSpace : Type := finset (Config Feature)

@[reducible]
def allConfigs : ConfigSpace := finset.univ

open PC list

def semantics : PC Feature → ConfigSpace
| (All)         := allConfigs
| (None)        := ∅
| (Atom f)      := allConfigs.filter (λ p, f ∈ p)
| (Not pc)      := allConfigs.filter (λ p, p ∈ (semantics pc))
| (And pc₁ pc₂) := (semantics pc₁) ∩ (semantics pc₂)
| (Or  pc₁ pc₂) := (semantics pc₁) ∪ (semantics pc₂)

end -- section PCs

notation `⟦` p `⟧` := (semantics p)

-- Var and Lifted
section
parameters {Feature : Type} [fintype Feature] [decidable_eq Feature]   

structure Var (α : Type) := (v : α) (pc : PC Feature)

open list 

def disjointPCs {α : Type} (s : list (Var α)) : Prop := 
    ∀ (c : Config Feature) (x₁ x₂ : Var α), 
        x₁ ∈ s → x₂ ∈ s → 
        c ∈ ⟦x₁.pc⟧ → c ∈ ⟦x₂.pc⟧ → x₁ = x₂

def completePCs {α : Type} (s : list (Var α)) : Prop :=
    ∀ (c : Config Feature), ∃ (v : (Var α)), v ∈ s ∧ c ∈ ⟦v.pc⟧

structure Lifted (α : Type) :=
    (s    : list (Var α))
    (disj : disjointPCs s) 
    (comp : completePCs s)

end -- section Var and Lifted

postfix `↑`:(max+1) := Lifted

-- list_find -- helper for index
section 

open classical

lemma list_find {α : Type} (q : α → Prop) [decidable_pred q] : 
    ∀ (l : list α), (∃ y, y ∈ l ∧ q y) → (list.find q l).is_some := 
begin
    intros l h₁, 
    induction l,
    -- base case
    apply exists.elim h₁, intros a h₂, apply and.elim h₂, intros h₃ h₄, simp, 
    apply list.not_mem_nil a h₃,
    -- induction
    unfold list.find, cases decidable.em (q l_hd) with hpos hneg,
    { rw if_pos hpos, simp },
    { rw if_neg hneg, apply exists.elim h₁, intros a h₂, apply l_ih, apply exists.intro a,
      simp at h₂, rw and.comm at h₂, rw and_or_distrib_left at h₂, apply or.elim h₂, 
      {intro h₃, apply and.elim h₃, intros h₄ h₅, rw← h₅ at hneg, contradiction},
      {intro h₃, rw and.comm, exact h₃}
    } 
end

end --section list_find

-- indexing
section 
variables {Feature: Type} [fintype Feature] [decidable_eq Feature] {α : Type}

def index'' (v : Lifted α) (ρ : Config Feature) : option (Var α) :=
    list.find (λ (u: @Var Feature _inst_1 _inst_2 α), ρ ∈ ⟦u.pc⟧) v.s

def configRel (v : Lifted α) (c₁ c₂ : Config Feature) : Prop :=
    index'' v c₁ = index'' v c₂

lemma configRelReflexive (v : α↑) : ∀ (ρ : Config Feature), configRel v ρ ρ :=
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

def index' --[t : fintype Feature] [d : decidable_eq Feature] 
    (v : Lifted α) (ρ : Config Feature) : Var α :=
    let pred := λ (u: @Var Feature _inst_1 _inst_2 α), ρ ∈ semantics (u.pc),
        r    := list.find pred v.s in 
    if  h : r.is_some 
    then option.get h
    else false.elim 
        begin 
            apply h, apply (list_find pred v.s (v.comp ρ))
        end

def index (v : Lifted α) (ρ : Config Feature) : α :=
    (index' v ρ).v

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
    unfold list.find, split_ifs, 
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