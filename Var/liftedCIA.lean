-- liftedCIA: Variability-aware Change Impact Assessment
import Var.cia
import Var.liftedSet
import Var.SPL

open CIA
open liftedSet
open SPL

namespace liftedCIA

opaque F: Type

abbrev Annotation' := @Var Annotation F
abbrev SysEl' := @Var SysEl F
abbrev GSNEl' := @Var GSNEl F

abbrev Sys' : Type := vset F SysEl
abbrev GSN' : Type := vset F GSNEl

abbrev TraceRel' := vset F (SysEl × GSNEl)

opaque sliceSys': Sys' → (@vset F SysEl) → Sys'
opaque sliceGSN_V': GSN' → (@vset F GSNEl) → GSN'
opaque sliceGSN_R': GSN' →  @vset F GSNEl → GSN'

axiom sliceSys_correct:
∀ (s : Sys')  (es : @vset F SysEl) (ρ : @Config F),
    ((sliceSys' s es) | ρ) = (sliceSys (s | ρ) (es | ρ))

axiom sliceGSNV_correct :
∀ (ac : GSN')  (es : vset F GSNEl) (ρ : @Config F),
    ((sliceGSN_V' ac es) | ρ) = sliceGSN_V (ac | ρ) (es | ρ)

axiom sliceGSNR_correct :
∀ (ac : GSN')  (es : vset F GSNEl) (ρ : @Config F),
    ((sliceGSN_R' ac es) | ρ) = sliceGSN_R (ac | ρ) (es | ρ)

structure Delta' :=
(add : vset F SysEl) (delete : vset F SysEl) (modify : vset F SysEl)

def indexDelta (d : Delta') (ρ : @Config F) : Delta :=
    let a := d.add | ρ
    let l := d.delete | ρ
    let m := d.modify | ρ
    Delta.mk a l m

instance Delta_Variational : Variational F Delta Delta' :=
⟨ indexDelta ⟩

@[simp]
def allElements' (d: Delta') : vset F SysEl :=
     (d.add ∪ d.delete ∪ d.modify)

def restrict' (t: TraceRel') (d : Delta') : TraceRel' :=
    {x | x ∈ t ∧ ((x.1.1, x.2) ∈ allElements' d)}

theorem restrict_correct: ∀ (ρ : @Config F) (t : TraceRel') (d : Delta'),
    ((restrict' t d) | ρ) = restrict (t | ρ) (d | ρ) :=
by
    intros ρ t d
    simp [restrict']
    simp [←Set.setOf_or, Variational.index]
    unfold vset.index
    simp [setOf, ←(and_or_left)]
    simp [restrict, indexDelta, allElements, ←Set.setOf_or, index_mem, setOf]
    apply funext
    intros x
    simp [Set.mem_def]

def trace' (t : TraceRel') (es : vset F SysEl) : vset F GSNEl :=
    Set.image (λx:((SysEl × GSNEl) × Config F) ↦ (x.1.2, x.2)) {e | e ∈ t ∧ (e.1.1, e.2) ∈ es}

theorem trace_correct : ∀ (t : TraceRel') (es : vset F SysEl) (ρ : Config F),
    ((trace' t es) | ρ) = trace (t | ρ) (es | ρ) :=
by
    intros t es ρ
    simp [trace', Variational.index]
    unfold vset.index
    simp [trace, setOf]
    apply funext
    intros x
    simp[Set.image, setOf, Set.mem_def]

def createAnnotation'   (g : GSN')
                        (recheck : vset F GSNEl)
                        (revise : vset F GSNEl)
                    : vset F (GSNEl × Annotation) :=
    let ch := Set.image (λ e ↦ ((e.1, Annotation.Recheck), e.2)) recheck
    let rv := Set.image (λ e ↦ ((e.1, Annotation.Revise), e.2)) revise
    let n  := Set.image (λ e ↦ ((e.1, Annotation.Reuse), e.2)) (g \ (recheck ∪ revise))
    ch ∪ rv ∪ n

theorem createAnnotation_correct:
    ∀ (g : GSN') (recheck : vset F GSNEl) (revise : vset F GSNEl) (ρ : Config F),
    ((createAnnotation' g recheck revise) | ρ) =
    createAnnotation (g | ρ) (recheck | ρ) (revise | ρ) :=
by
    intros g recheck revise ρ
    simp [createAnnotation', Set.image]
    simp [←Set.setOf_or, Variational.index]
    unfold vset.index
    simp [createAnnotation, Set.image, ←Set.setOf_or, setOf]
    apply funext
    intros x
    simp[Set.mem_def, Set.union_def, setOf]

open Delta'

def GSN_IA' (S S' : Sys')
            (A  : GSN')
            (R  : TraceRel')
            (D  : Delta')
            : vset F (GSNEl × Annotation) :=
    let R'          := restrict' R D
    let C1dm        := sliceSys' S (D.delete ∪ D.modify)
    let C1am        := sliceSys' S' (D.add ∪ D.modify)
    let C2Recheck   := (trace' R C1dm) ∪ (trace' R' C1am)
    let C2Revise    := trace' R D.delete
    let C3Recheck1  := sliceGSN_V' A C2Revise
    let C3Recheck2  := sliceGSN_R' A (C2Recheck ∪ C3Recheck1)
    createAnnotation' A C3Recheck2 C2Revise

theorem GSN_IA'_correct :
    ∀ (S S' : Sys') (A  : GSN') (R  : TraceRel') (D : Delta') (ρ : Config F),
    ((GSN_IA' S S' A R D) | ρ) = GSN_IA  (S | ρ) (S' | ρ) (A | ρ) (R | ρ) (D | ρ)
    :=
by
    intros S S' A R D ρ
    simp [GSN_IA', GSN_IA]
    simp [←restrict_correct]
    simp [Delta_Variational, indexDelta, index_union, ←sliceSys_correct]
    simp [←trace_correct]
    simp [←sliceGSNV_correct, index_union]
    simp [←sliceGSNR_correct, ←createAnnotation_correct]

end liftedCIA
