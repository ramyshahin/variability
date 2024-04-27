/-
import data.fintype
import data.finset
import data.set

namespace datalog

section datalog

parameters {const : Type} [fintype const] [decidable_eq const]
parameters {var   : Type} [fintype var] [decidable_eq var]
parameters {sym   : Type} [fintype sym] [decidable_eq sym]

structure predicate : Type := (s : sym) (arity : ℕ)

inductive term : Type
| C : const → term
| V : var   → term

structure fact : Type := (p : predicate) (cs : vector const p.arity)
structure atom : Type := (p : predicate) (ts : vector term  p.arity)

open list
open term
open finset

def vars (a : atom) : finset var :=
    foldr (λ (t: term) (s : finset var),
            match t with
            | V v := insert v s
            | _   := s
            end) finset.empty a.ts.to_list

structure rule : Type := (head : atom) (body: list atom)
    (i : (foldr (λ (a:atom) (s:finset var), s ∪ (vars a)) finset.empty body) ⊂ vars head)

def IDB : Type := list rule
def EDB : Type := list fact

structure Program : Type := (idb : IDB) (edb : EDB)

-- semantics

def interp := finset fact
def subst  := var → option const

def extend_subst (s : subst) (v : var) (c : const) : subst :=
    λ x, if     x= v
         then   some c
         else   s x

def matchTerm (c : const) (σ : subst) : term → option subst
| (term.C v)  := if v = c then some σ else none
| (term.V v)  := match σ v with
                 | (some x) := if c = x then some σ else none
                 | _        := some (extend_subst σ v c)
                 end

open list
open prod

def matchAtom (a : atom) (f : fact) (σ : subst) : option subst :=
    if (a.p.s = f.p.s)
    then foldl  (λ σ' p, σ' >>= λ σ'', matchTerm (snd p) σ'' (fst p))
                (some σ)
                (zip a.ts.to_list f.cs.to_list)
    else none

-- tests
section testMatchTerm

def s₀  : subst := λ_, none
parameters c₀ c₁ c₂ : const
parameters v₀ v₁ v₂ : var

def t₀  : term  := term.C c₁
def t₁  : term  := term.V v₀
def t₂  : term  := term.C c₀

def eval : option subst → var → option const
| (some s) v := s v
| none _     := none

def s₁ := matchTerm c₀ s₀ t₀
def r₁ := eval s₁ v₀

#print r₁

def s₂ := matchTerm c₀ s₀ t₁
def r₂ := eval s₂ v₀

#eval r₂

def s₃ := matchTerm c₀ s₀ t₂
def r₃ := eval s₃ v₀

#eval r₃

end testMatchTerm

end datalog

end datalog
-/
