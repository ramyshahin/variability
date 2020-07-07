-- liftedCIA: Variability-aware Change Impact Assessment
import .cia
import .variability

open CIA
open variability 

namespace liftedCIA

def Annotation' := Var Annotation
def SysEl' := Var SysEl
def GSNEl' := Var GSNEl

def Sys' : Type := set' SysEl
def GSN' : Type := set' GSNEl

def TraceRel' := set' (SysEl × GSNEl)

open variability.has_index

def indexTraceRel (t: TraceRel') (pc : PC) : set (SysEl × GSNEl) := 
    index t pc

instance TraceRel_has_index : has_index TraceRel' :=
⟨ indexTraceRel ⟩

constant sliceSys'   (s : Sys')  (es : set' SysEl) : Sys'
constant sliceGSN_V' (ac : GSN') (es : set' GSNEl) : GSN'
constant sliceGSN_R' (ac : GSN') (es : set' GSNEl) : GSN'

axiom sliceSys_correct : ∀ (s : Sys')  (es : set' SysEl) (pc : PC),
index (sliceSys' s es) pc = sliceSys (index s pc) (index es pc)

axiom sliceGSNV_correct : ∀ (ac : GSN')  (es : set' GSNEl) (pc : PC),
index (sliceGSN_V' ac es) pc = sliceGSN_V (index ac pc) (index es pc)

axiom sliceGSNR_correct : ∀ (ac : GSN')  (es : set' GSNEl) (pc : PC),
index (sliceGSN_R' ac es) pc = sliceGSN_R (index ac pc) (index es pc)

structure Delta' :=
mk :: (add : set' SysEl) (delete : set' SysEl) (modify : set' SysEl)

open variability.has_index

def indexDelta (d : Delta') (pc : PC) :=
    let a := index d.add pc,
        l := index d.delete pc,
        m := index d.modify pc
    in  Delta.mk a l m

instance Delta_has_index : has_index Delta' :=
⟨ indexDelta ⟩

def restrict' (t : TraceRel') (d : Delta') : TraceRel' :=
    let relevant := d.add ∪ d.delete ∪ d.modify
    in  λ x, t x ∧ relevant x.1 

theorem restrict_correct : ∀ (pc : PC) (t : TraceRel') (d : Delta'), 
    index (restrict' t d) pc = restrict (index t pc) (indexDelta d pc)
    :=
begin
    intros, 
    rw restrict, rw indexDelta, simp,
    repeat {rw index}, repeat {rw function.comp},
    unfold has_mem.mem, unfold set.mem,
    apply funext, intros, 
    repeat {rw ←and_or_distrib_left}, rw ←and_assoc, rw ←and_comm pc,
    rw ←and_assoc, rw and_self pc, rw and_assoc, rw ←and.rotate,
    rw restrict', simp, rw ←and_assoc, rw and_comm pc,
    unfold has_union.union, repeat {rw variability.union}, simp, 
    rw and_assoc 
end

def trace' (t : TraceRel') (es : set' SysEl) : set' GSNEl :=
    λ (g:GSNEl), ∃ (s : SysEl) , es s ∧ t ⟨s , g⟩

theorem trace_correct : ∀ (t : TraceRel') (es : set' SysEl) (pc : PC),
    index (trace' t es) pc = trace (index t pc) (index es pc)
    :=
begin
    intros, repeat {rw index}, repeat {rw function.comp},
    rw trace', rw CIA.trace, simp, funext, simp, 
    unfold has_mem.mem, rw ←exists_and_distrib_left, split,
        intro h, cases h with x h₁, existsi x, repeat {rw set.mem}, 
            rw and.left_comm, rw and.assoc, rw ←and.assoc, rw and_self, 
            apply h₁,
        intro h, cases h with x h₁, existsi x, repeat {rw set.mem at h₁},
            rw and.left_comm at h₁, rw and.assoc at h₁, rw ←and.assoc at h₁,
            rw and_self at h₁, exact h₁ 
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
    intros, repeat {rw index}, repeat {rw function.comp},
    rw createAnnotation, rw createAnnotation', simp, 
    repeat {rw image}, repeat {rw set.union_def}, simp, unfold has_sdiff.sdiff, 
    rw set.diff, simp, funext, simp,
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

theorem fun_comp_correct : 
    ∀ (f₁  : set  α → set  β) (f₂  : set  β  → set  γ)
      (f₁' : set' α → set' β) (f₂' : set' β  → set' γ),
    (∀ (a : set' α) (pc : PC), f₁ (index a pc) = index (f₁' a) pc) →
    (∀ (b : set' β) (pc : PC), f₂ (index b pc) = index (f₂' b) pc) →
     ∀ (a : set' α) (b : set' β) (pc : PC), f₂ (f₁ (index a pc)) = 
        index (f₂' (f₁' a)) pc :=
begin
intros f₁ f₂ f₃ f₄ h₁ h₂ a h₃ pc, rw h₁, rw← h₂
end

open set
open variability
open variability.has_index

lemma index_union : ∀ {α : Type _} (s₁ s₂ : set' α) (pc : PC),
(index (s₁ ∪ s₂) pc) = (index s₁ pc) ∪ (index s₂ pc) :=
begin
    intros, unfold has_union.union, unfold variability.union, unfold set.union, 
    unfold has_mem.mem, unfold set.mem, 
    rw index, rw index, rw index,
    rw function.comp, rw function.comp, rw function.comp, simp,  
    apply funext, intro, 
    rw and_or_distrib_left, refl
end 

theorem GSN_IA'_correct : 
    ∀   (S S' : Sys') (A  : GSN') (R  : TraceRel') 
        (D  : Delta') (pc : PC),
    index (GSN_IA' S S' A R D) pc =
    GSN_IA  (index S pc) (index S' pc) (index A pc) 
            (index R pc) (indexDelta D pc) 
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
