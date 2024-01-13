import data.finset data.set tactic
import data.setoid.partition
import data.finset
import data.fin

namespace variability

def n := 3 

@[simp, reducible]
def Feature := fin n

@[derive decidable_eq]
inductive FeatureExpr
| All  : FeatureExpr 
| None : FeatureExpr
| Atom : Feature → FeatureExpr 
| Not  : FeatureExpr → FeatureExpr
| And  : FeatureExpr → FeatureExpr → FeatureExpr
| Or   : FeatureExpr → FeatureExpr → FeatureExpr

open FeatureExpr
def featExpr_to_string  : FeatureExpr → string
| All       := "Universe"
| None      := "∅"
| (Atom f)  := to_string f --Feature Feature_has_to_string f
| (Not p)   := "¬" ++ featExpr_to_string p
| (And p q) := (featExpr_to_string p) ++ " ∧ " ++ (featExpr_to_string q)
| (Or p q)  := (featExpr_to_string p) ++ " ∨ " ++ (featExpr_to_string q)
      
instance: has_to_string FeatureExpr := ⟨featExpr_to_string⟩

instance [has_to_string Feature] : has_repr FeatureExpr := ⟨to_string⟩

--#print has_lift_t 
@[reducible, simp] --, derive (has_lift (finset Feature) (set Feature))] 
def Config: Type := finset Feature

@[reducible, simp]
def ConfigSpace :Type := finset Config

open FeatureExpr
def semantics: FeatureExpr → ConfigSpace
| (All)         := finset.univ
| (None)        := ∅
| (Atom f)      := finset.filter (λx, f ∈ x) finset.univ
| (Not pc)      := finset.univ \ (semantics pc)
| (And pc₁ pc₂) := (semantics pc₁) ∩ (semantics pc₂)
| (Or  pc₁ pc₂) := (semantics pc₁) ∪ (semantics pc₂)

notation `⦃` p `⦄` := semantics p

instance : has_equiv FeatureExpr :=
⟨λ x y, eq ⦃x⦄ ⦃y⦄⟩

def PC := FeatureExpr

instance: has_to_string PC := ⟨featExpr_to_string⟩

structure SPL :=
(Features: Type)
(Φ: FeatureExpr)

open list

--def PCond := @PC F d ft

-- decision procedure for list disjointness
@[simp]
def checkDisj {β : Type} [decidable_eq β]: list (finset β) → bool
| ([]) := true
| (x :: xs) := band (checkDisj xs) (∀ y ∈ xs, x ∩ y = ∅)

@[simp]
def checkTotal (cs : list ConfigSpace) : bool :=
    foldl (∪) ∅ cs = finset.univ

--def C := @Config F d ft
def l {C : Type} := @lift_t (finset C) (set C)

--def m (p : @PC F d ft) : set (@Config F d ft) := ↑(semantics p)

--@[derive [decidable_eq]]  

@[reducible]
lemma hl1: has_lift_t (finset Config) (set Config) := ⟨λ x, ↑x⟩

--⟨λ x, let y := finset.image ((λy, ↑y) : finset Feature → set Feature) x in y⟩ --{z:α | z ∈ y}}⟩
@[reducible]
lemma hl2: has_lift_t (finset (finset Config)) (set (set Config)) := 
    ⟨λ x, (finset.image (λ(y: finset Config), @lift_t (finset Config) (set Config) hl1 y) x)⟩ 

structure ConfigPartition :=
(pcs : list PC)
(cs  : list (finset Config) := (list.map semantics pcs))
(inv: checkDisj(cs) ∧ checkTotal(cs) . tactic.exact_dec_trivial)
--(inv : ∀ (c: Config), ∃! b ∈ cs, c ∈ b . tactic.exact_dec_trivial)

--lemma partition_inv : 
--    ∀ (cs : list (finset Conf)), checkDisj cs ∧ checkTotal cs ↔ ∀ (c: @ConfigSpace F d ft), ∃! b ∈ cs, c ∈ b :=
--begin
--    intros, split, induction cs,
      -- base case
--      intros H c, simp at H, simp,
--end

--(disj: checkDisj (list.map semantics (pcs)) . tactic.exact_dec_trivial) --disjPCs pcs)
--(total : checkTotal pcs . tactic.exact_dec_trivial)

--def partition_to_setoid (cp : ConfigPartition) : setoid Config :=
--setoid.mk_classes (↑cp.cs) (cp.inv)

structure Var (α : Type) :=
(p      : ConfigPartition)
(elems  : list α)
(inv    : elems.length = p.pcs.length . tactic.exact_dec_trivial)

--open list
-- configuration partition: ConfigPartition
--def ConfigPartition := indexed_partition (λ pc, {x | x ∈ ⦃pc⦄}) 

inductive disjPCs : list PC → Prop
| disjPCs_nil : disjPCs []
| disjPCs_cons {x : PC} {xs : list PC} : disjPCs xs → (∀ y, y ∈ xs → ⦃x⦄ ∩ ⦃y⦄ = ∅) → disjPCs (x :: xs)

instance: has_to_string ConfigPartition :=
    ⟨λ p, list.to_string p.pcs⟩

instance: has_repr ConfigPartition := ⟨to_string⟩

def is_eqv (p : ConfigPartition) (ρ₁ ρ₂ : Config) : bool :=
let idx := λ ρ, list.find (λ x, ρ ∈ ⦃x⦄) p.pcs
in  idx ρ₁ = idx ρ₂

local infix `~` := is_eqv
/-
lemma checkDisj_correct :
    ∀ (pcs : list PC), disjPCs pcs ↔ (checkDisj (map semantics pcs) = tt) :=
begin
    intros, split, 
    -- → 
    intro h, induction h,
      -- base case
      simp,
      -- induction
      simp, split,
        -- lhs
        apply h_ih, 
        -- rhs
        apply h_ᾰ_1, 
    -- ←
    intro h, induction pcs,
      -- base case
      apply disjPCs.disjPCs_nil,
      -- induction
      apply disjPCs.disjPCs_cons,
        apply pcs_ih, unfold map at h, simp at h, apply h.left,
        intros y h₂, simp at h, apply h.right, apply h₂
end
-/

section LiftedVals
/-
parameter {α :Type}

-- annotated value
def annVal := (α × PC)

-- lifted value
structure Var := 
    (elems: list annVal)
    (disj: checkDisj (map semantics (map prod.snd elems)) . tactic.exact_dec_trivial)
    (total : checkTotal (map prod.snd elems) . tactic.exact_dec_trivial)

instance {α : Type} [has_to_string (α × PC)]: has_to_string (@Var α) :=
    ⟨λ v, list.to_string v.elems⟩

instance {α : Type} [has_to_string (α × PC)]: has_repr (@Var α) := ⟨to_string⟩

local postfix `↑`:(max+1) := Var
-/
end LiftedVals 

def index' {α:Type} (ρ : Config) : list (α × PC) → option α
| [] := none
| (x :: xs) := if ρ ∈ ⦃x.2⦄ then some x.1 else index' xs 

def index {α:Type} (ρ : Config) (v : @Var α) : option α := 
    index' ρ (list.zip v.elems v.p.pcs)

infix `|` := index

/-
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


 
lemma index_unique {α : Type} (l1 : @Var α) (x : @AVal α) (ρ : Config)  
    : x ∈ l.s → ρ ∈ semantics x.pc → (index l ρ) = x.v :=
begin
    intros h1 h2, 
    unfold index, simp, split_ifs, 
    {rw option.get_of_mem, simp,  }
end
#print list.find_mem 

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
-/
end variability
