import data.fintype

namespace datalog

constants α β γ: ℕ

--constant symtype  : fin α
--constant constype : fin β
--constant vartype  : fin γ

--set_option class.instance_max_depth 1000

--set_option trace.class_instances true

structure sym   : Type := (S : fin 10) (arity : ℕ) -- TODO
structure const : Type := (C : fin 10) -- TODO
structure var   : Type := (V : fin 10) -- TODO 

--def var := vartype

inductive term
| tconst : const → term
| tvar   : var   → term

structure fact : Type := (s : sym) (cs : vector sym s.arity)
structure atom : Type := (s : sym) (ts : vector term s.arity)
structure rule {n : ℕ} : Type := (head : atom) (body: vector atom n)

-- semantics
def interp := finset fact
def subst  := var → option const

def extend_subst (s : subst) (v : var) (c : const) : subst :=
    λ x, if     x.V = v.V
         then   some c
         else   s x

def matchTerm (c : const) (σ : subst) : term → option subst
| (term.tconst v)  := if v.C = c.C then some σ else none
| (term.tvar v)    := match σ v with
                      | (some x) := if c.C = x.C then some σ else none
                      | _        := some (extend_subst σ v c)
                      end


end datalog