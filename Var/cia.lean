-- CIA: Change Impact Assessment on safety cases
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset

namespace CIA

--opaque SysElCount: ℕ
--opaque GSNElCount: ℕ

opaque SysEl: Type

--def SysEl: Type := Fin SysElCount

def SySEls := Set SysEl

opaque GSNEl: Type

--def GSNEl: Type := Fin GSNElCount

def GSNEls := Set GSNEl

inductive Annotation : Type
| Reuse
| Recheck
| Revise

@[reducible]
def Sys : Type := Set SysEl

@[reducible]
def GSN : Type := Set GSNEl

@[reducible]
def TraceRel : Type := Set (SysEl × GSNEl)

opaque sliceSys   (s : Sys)  (es : Set SysEl) : Sys
opaque sliceGSN_V (ac : GSN) (es : Set GSNEl) : GSN
opaque sliceGSN_R (ac : GSN) (es : Set GSNEl) : GSN

structure Delta :=
(add : Set SysEl) (delete : Set SysEl) (modify : Set SysEl)

def allElements (d: Delta) : Set SysEl :=
     (d.add ∪ d.delete ∪ d.modify)

def restrict (t : TraceRel) (d : Delta) : TraceRel :=
    {x:(SysEl × GSNEl) | x ∈ t ∧ x.1 ∈ allElements d }

def trace (t : TraceRel) (es : Set SysEl) : Set GSNEl :=
    Set.image (λx:(SysEl × GSNEl) ↦ x.2) {e: (SysEl × GSNEl) | e ∈ t ∧ e.1 ∈ es }

def createAnnotation    (g : GSN)
                        (recheck : Set GSNEl)
                        (revise : Set GSNEl)
: Set (GSNEl × Annotation) :=
    let ch := Set.image (λ e ↦ (e, Annotation.Recheck)) recheck
    let rv := Set.image (λ e ↦ (e, Annotation.Revise)) revise
    let ru := Set.image (λ e ↦ (e, Annotation.Reuse))
                        (g \ (recheck ∪ revise))
    ch ∪ rv ∪ ru

open Delta

def GSN_IA  (S  : Sys)
            (S' : Sys)
            (A  : GSN)
            (R  : TraceRel)
            (D  : Delta)
: Set (GSNEl × Annotation) :=
    let R'          := restrict R D
    let C1dm        := sliceSys S (D.delete ∪ D.modify)
    let C1am        := sliceSys S' (D.add ∪ D.modify)
    let C2Recheck   := (trace R C1dm) ∪ (trace R' C1am)
    let C2Revise    := trace R (D.delete)
    let C3Recheck1  := sliceGSN_V A C2Revise
    let C3Recheck2  := sliceGSN_R A (C2Recheck ∪ C3Recheck1)
    createAnnotation A C3Recheck2 C2Revise

end CIA
