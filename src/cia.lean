-- CIA: Change Impact Assessment
import data.set 
import data.finset

open set

namespace CIA

constant SysElCount: ℕ
constant GSNElCount: ℕ
def SysEl: Type := fin SysElCount
def GSNEl: Type := fin GSNElCount

--section

@[derive decidable_eq]
inductive Annotation : Type
| Reuse
| Recheck
| Revise
 
--variables (SysEl : Type) [finSysEl: fintype SysEl] [deqSysEl: decidable_eq SysEl]
--variables (GSNEl : Type) [finGSNEl: fintype GSNEl] [deqGSNEl: decidable_eq GSNEl]

@[reducible]
def Sys : Type := finset SysEl

--@[reducible, simp]
--instance SysEl_has_union: has_union (finset SysEl) := @finset.has_union SysEl deqSysEl

@[reducible]
def GSN : Type := finset GSNEl

@[reducible]
def TraceRel : Type := finset (SysEl × GSNEl)

variable sliceSys   (s : Sys)  (es : finset SysEl) : Sys
variable sliceGSN_V (ac : GSN) (es : finset GSNEl) : GSN
variable sliceGSN_R (ac : GSN) (es : finset GSNEl) : GSN

structure Delta :=
(add : finset SysEl) (delete : finset SysEl) (modify : finset SysEl)

def allElements (d: Delta) : finset SysEl :=
     (d.add ∪ d.delete ∪ d.modify)

def restrict (t : TraceRel) (d : Delta) : TraceRel :=
    finset.filter (λx, x.1 ∈ allElements d) t
    
def trace (t : TraceRel) (es : finset SysEl) : finset GSNEl :=
    finset.image (λx:(SysEl × GSNEl), x.2) 
        (finset.filter (λ e:(SysEl × GSNEl), e.1 ∈ es) t)

def createAnnotation'   (recheck : finset GSNEl)
                        (revise : finset GSNEl) 
                        (el: GSNEl) 
                        : Annotation :=
@dite 
    Annotation 
    (el ∈ recheck) 
    (finset.decidable_mem el recheck) 
    (λ_, Annotation.Recheck)
    (λ_, @dite 
        Annotation
        (el ∈ revise) 
        (finset.decidable_mem el revise)
        (λ_,  Annotation.Revise) 
        (λ_, Annotation.Reuse))

def createAnnotation    (g : GSN) 
                        (recheck : finset GSNEl)
                        (revise : finset GSNEl) 
                        : finset (GSNEl × Annotation) :=
    finset.image (λx, (x, createAnnotation' recheck revise x)) g

open Delta

def GSN_IA  (S  : Sys)
            (S' : Sys)
            (A  : GSN)
            (R  : TraceRel)
            (D  : Delta)
            : finset (GSNEl × Annotation) :=
    let R'          := restrict R D,
        C1dm        := sliceSys S (D.delete ∪ D.modify),
        C1am        := sliceSys S' (D.add ∪ D.modify),
        C2Recheck   := (trace R C1dm) ∪ (trace R' C1am),
        C2Revise    := trace R (D.delete),
        C3Recheck1  := sliceGSN_V A C2Revise,
        C3Recheck2  := sliceGSN_R A (C2Recheck ∪ C3Recheck1)
    in  createAnnotation A C3Recheck2 C2Revise
    
end CIA

