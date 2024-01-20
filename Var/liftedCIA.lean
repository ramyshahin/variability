-- liftedCIA: Variability-aware Change Impact Assessment
import .cia
import .liftedSet

open CIA
open liftedSet 

namespace liftedCIA

def Annotation' := Var Annotation
def SysEl' := Var SysEl
def GSNEl' := Var GSNEl

def Sys' : Type := set' SysEl
def GSN' : Type := set' GSNEl

@[derive has_mem (SysEl × GSNEl)]
def TraceRel' := set' (SysEl × GSNEl)

--instance: has_mem (SysEl × GSNEl ) TraceRel' := liftedSet.liftedSet_has_mem

def indexTraceRel (t: TraceRel') (pc : PC) : set (SysEl × GSNEl) := 
    index t pc

instance TraceRel_has_index : has_index TraceRel' :=
⟨ indexTraceRel ⟩

variable sliceSys   (s : Sys)  (es : set SysEl) : Sys
variable sliceGSN_V (ac : GSN) (es : set GSNEl) : GSN
variable sliceGSN_R (ac : GSN) (es : set GSNEl) : GSN

constant sliceSys'   (s : Sys')  (es : set' SysEl) : Sys'
constant sliceGSN_V' (ac : GSN') (es : set' GSNEl) : GSN'
constant sliceGSN_R' (ac : GSN') (es : set' GSNEl) : GSN'

axiom sliceSys_correct : ∀ (s : Sys')  (es : set' SysEl) (pc : PC),
index (sliceSys' s es) pc = (sliceSys (index s pc) (index es pc))

axiom sliceGSNV_correct : ∀ (ac : GSN')  (es : set' GSNEl) (pc : PC),
index (sliceGSN_V' ac es) pc = sliceGSN_V (index ac pc) (index es pc)

axiom sliceGSNR_correct : ∀ (ac : GSN')  (es : set' GSNEl) (pc : PC),
index (sliceGSN_R' ac es) pc = sliceGSN_R (index ac pc) (index es pc)

structure Delta' :=
(add : set' SysEl) (delete : set' SysEl) (modify : set' SysEl)

def indexDelta (d : Delta') (pc : PC) :=
    let a := index d.add pc,
        l := index d.delete pc,
        m := index d.modify pc
    in  Delta.mk a l m

instance Delta_has_index : has_index Delta' :=
⟨ indexDelta ⟩

def restrict' (t : TraceRel') (d : Delta') : TraceRel' :=
    let relevant := d.add ∪ d.delete ∪ d.modify
    in  {x | x ∈ t ∧ x.1 ∈ relevant} 

theorem restrict_correct : ∀ (pc : PC) (t : TraceRel') (d : Delta'), 
    index (restrict' t d) pc = restrict (index t pc) (indexDelta d pc)
    :=
begin
    intros, rw restrict', rw indexDelta, simp, rw restrict, rw allElements, simp,
    apply funext, intros, repeat {rw set_of}, repeat {rw index_union},
    repeat {rw index_mem}, rw index, repeat {rw function.comp}, simp,
    rw and_comm _ pc, rw and_comm _ pc, rw and_assoc, rw← and_assoc (x ∈ t), 
    rw← and_assoc _ (x ∈ t ∧ pc), rw and_comm _ (x ∈ t ∧ pc), simp, rw and_comm _ pc,
    rw← and_assoc 
end

def trace' (t : TraceRel') (es : set' SysEl) : set' GSNEl :=
    λ (g:GSNEl), ∃ (s : SysEl) , es s ∧ t ⟨s , g⟩

theorem trace_correct : ∀ (t : TraceRel') (es : set' SysEl) (pc : PC),
    index (trace' t es) pc = trace (index t pc) (index es pc)
    :=
begin
    intros, rw trace', rw index, rw function.comp, rw CIA.trace, simp, unfold set.image,
    rw set_of,  simp, apply funext, intros, simp, split,
    { intros h, apply exists.elim h.2, intros a g, existsi a, repeat {rw index_mem}, split,
      split, exact g.2, exact h.1, split, exact g.1, exact h.1},
    { intros h, apply exists.elim h, intros a g, repeat {rw index_mem at g}, split,
      exact g.1.2, existsi a, split, exact g.2.1, exact g.1.1}
end

def createAnnotation'   (g : GSN') 
                        (recheck : set' GSNEl)
                        (revise : set' GSNEl)
                    : set' (GSNEl × Annotation) :=
    let ch := image (λ e, (e, Annotation.Recheck)) recheck,
        rv := image (λ e, (e, Annotation.Revise)) revise,
        n  := image (λ e, (e, Annotation.Reuse)) (g - (recheck ∪ revise))
    in  ch ∪ rv ∪ n

theorem createAnnotation_correct:
    ∀ (g : GSN') (recheck : set' GSNEl) (revise : set' GSNEl) (pc : PC),
    index (createAnnotation' g recheck revise) pc =
    createAnnotation (index g pc) (index recheck pc) (index revise pc)
    :=  
begin
    intros, unfold createAnnotation', repeat {rw image},
    simp, unfold createAnnotation, repeat {rw set.image}, simp,
    rw index, repeat {rw function.comp}, repeat {rw set_of}, apply funext, intros, simp, split,
    { intros h, rw set'.union, }
    rw set.union,
    rw exists.intro,  
    rw index, rw function.comp, unfold has_sub.sub,
    repeat {rw set.union_def}, 
    repeat {unfold has_sub.sub}, repeat{rw set.mem_def},
    rw createAnnotation, rw createAnnotation', simp, 
    repeat {rw image},  dsimp, unfold has_sdiff.sdiff, 
    rw set.diff, simp, funext, simp, rw and_or_distrib_right,
    repeat {rw image}, repeat {rw set.union_def}, simp, 
    repeat {rw set.union_def}, dsimp, 
    repeat {rw set.mem_def}, 
end

open Delta'

def GSN_IA' (S S' : Sys')
            (A  : GSN')
            (R  : TraceRel')
            (D  : Delta')
            : set' (GSNEl × Annotation) :=
    let R'          := restrict' R D,
        C1dm        := sliceSys' S (D.delete ∪ D.modify),
        C1am        := sliceSys' S' (D.add ∪ D.modify),
        C2Recheck   := (trace' R C1dm) ∪ (trace' R' C1am),
        C2Revise    := trace' R D.delete,
        C3Recheck1  := sliceGSN_V' A C2Revise,
        C3Recheck2  := sliceGSN_R' A (C2Recheck ∪ C3Recheck1)
    in  createAnnotation' A C3Recheck2 C2Revise

universe u
variables {α β γ : Type}

open set

lemma index_union : ∀ {α : Type _} (s₁ s₂ : set' α) (pc : PC),
(index (s₁ ∪ s₂) pc) = (index s₁ pc) ∪ (index s₂ pc) :=
begin
    intros, unfold has_union.union, unfold liftedSet.union, unfold set.union, 
    unfold has_mem.mem, unfold set.mem, 
    rw index, rw index, rw index,
    rw function.comp, rw function.comp, rw function.comp, simp,  
    apply funext, intro, 
    rw and_or_distrib_left, refl
end 

theorem GSN_IA'_correct : 
    ∀ (S S' : Sys') (A  : GSN') (R  : TraceRel') (D : Delta') (pc : PC),
    (GSN_IA' S S' A R D) | pc = GSN_IA  (S | pc) (S' | pc) (A | pc) (R | pc) (indexDelta D pc) 
    :=
begin
    intros, rw GSN_IA', rw GSN_IA, simp, 
    rw← restrict_correct, rw indexDelta, simp,
    rw ←index_union, rw ←index_union, rw← sliceSys_correct, 
    rw← trace_correct, rw← trace_correct, rw← sliceSys_correct,
    rw← trace_correct, rw← sliceGSNV_correct, rw ←index_union,
    rw ←index_union, rw← sliceGSNR_correct, rw← createAnnotation_correct
end

end liftedCIA
