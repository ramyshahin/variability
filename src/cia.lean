-- CIA: Change Impact Assessment
import data.set 
import data.finset

open set

namespace CIA

constant SysElCount: ℕ
constant GSNElCount: ℕ

@[derive fintype, derive decidable_eq]
def SysEl: Type := fin SysElCount

@[derive fintype]
def SySEls := set SysEl 

@[derive fintype, derive decidable_eq]
def GSNEl: Type := fin GSNElCount

@[derive fintype]
def GSNEls := set GSNEl

--section

@[derive decidable_eq]
inductive Annotation : Type
| Reuse
| Recheck
| Revise
 
--variables (SysEl : Type) [finSysEl: fintype SysEl] [deqSysEl: decidable_eq SysEl]
--variables (GSNEl : Type) [finGSNEl: fintype GSNEl] [deqGSNEl: decidable_eq GSNEl]

@[reducible]
def Sys : Type := set SysEl --finset SysEl

--@[reducible, simp]
--instance SysEl_has_union: has_union (finset SysEl) := @finset.has_union SysEl deqSysEl

@[reducible]
def GSN : Type := set GSNEl --finset GSNEl

@[reducible]
def TraceRel : Type := set (SysEl × GSNEl) --finset (SysEl × GSNEl)

variable sliceSys   (s : Sys)  (es : set SysEl) : Sys
variable sliceGSN_V (ac : GSN) (es : set GSNEl) : GSN
variable sliceGSN_R (ac : GSN) (es : set GSNEl) : GSN

structure Delta :=
(add : set SysEl) (delete : set SysEl) (modify : set SysEl)

def allElements (d: Delta) : set SysEl :=
     (d.add ∪ d.delete ∪ d.modify)

def restrict (t : TraceRel) (d : Delta) : TraceRel := 
    {x:(SysEl × GSNEl) | x ∈ t ∧ x.1 ∈ allElements d }
    
def trace (t : TraceRel) (es : set SysEl) : set GSNEl :=
    set.image (λx:(SysEl × GSNEl), x.2) 
        {e: (SysEl × GSNEl) | e ∈ t ∧ e.1 ∈ es }
        --(set.filter (λ e:(SysEl × GSNEl), e.1 ∈ es) t)

/-
def createAnnotation'   (recheck:   set GSNEl)
                        (revise:    set GSNEl) 
                        (el:        GSNEl) 
                        : Annotation :=
if 
    --Annotation 
    (el ∈ recheck) then
    --(set.decidable_mem el recheck) 
    (λ_, Annotation.Recheck) else
    (λ_, @dite 
        Annotation
        (el ∈ revise) 
        (set.decidable_mem_of_fintype revise el)
        (λ_,  Annotation.Revise) 
        (λ_, Annotation.Reuse)) .

def createAnnotation    (g : GSN) 
                        (recheck : set GSNEl)
                        (revise : set GSNEl) 
                        : set (GSNEl × Annotation) :=
    set.image (λx, (x, createAnnotation' recheck revise x)) g
-/

def createAnnotation    (g : GSN) 
                        (recheck : set GSNEl)
                        (revise : set GSNEl)
                    : set (GSNEl × Annotation) :=
    let ch := image (λ e, (e, Annotation.Recheck)) recheck,
        rv := image (λ e, (e, Annotation.Revise)) revise,
        ru := image (λ e, (e, Annotation.Reuse)) 
                    (g \ (recheck ∪ revise))
    in  ch ∪ rv ∪ ru

open Delta

def GSN_IA  (S  : Sys)
            (S' : Sys)
            (A  : GSN)
            (R  : TraceRel)
            (D  : Delta)
            : set (GSNEl × Annotation) :=
    let R'          := restrict R D,
        C1dm        := sliceSys S (D.delete ∪ D.modify),
        C1am        := sliceSys S' (D.add ∪ D.modify),
        C2Recheck   := (trace R C1dm) ∪ (trace R' C1am),
        C2Revise    := trace R (D.delete),
        C3Recheck1  := sliceGSN_V A C2Revise,
        C3Recheck2  := sliceGSN_R A (C2Recheck ∪ C3Recheck1)
    in  createAnnotation A C3Recheck2 C2Revise

end CIA

