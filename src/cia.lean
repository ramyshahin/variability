-- CIA: Change Impact Assessment
import data.set 

open set

namespace CIA

inductive Annotation : Type
| Reuse
| Recheck
| Revise

constant SysEl : Type
constant GSNEl : Type

def Sys : Type := set SysEl

def GSN : Type := set GSNEl

@[reducible]
def TraceRel : Type := set (SysEl × GSNEl)

constant sliceSys   (s : Sys)  (es : set SysEl) : Sys
constant sliceGSN_V (ac : GSN) (es : set GSNEl) : GSN
constant sliceGSN_R (ac : GSN) (es : set GSNEl) : GSN

structure Delta :=
(add : set SysEl) (delete : set SysEl) (modify : set SysEl)

open has_union

def restrict (t : TraceRel) (d : Delta) : TraceRel :=
    λ x, x.1 ∈ (d.add ∪ d.delete ∪ d.modify) ∧ x ∈ t

def trace (t : TraceRel) (es : set SysEl) : set GSNEl :=
    λ e, ∃ s ∈ es, (s,e) ∈ t 

def createAnnotation    (g : GSN) 
                        (recheck : set GSNEl)
                        (revise : set GSNEl)
                    : set (GSNEl × Annotation) :=
    let ch := image (λ e, (e, Annotation.Recheck)) recheck,
        rv := image (λ e, (e, Annotation.Revise)) revise,
        ru := image (λ e, (e, Annotation.Reuse)) 
                    (g - (recheck ∪ revise))
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
