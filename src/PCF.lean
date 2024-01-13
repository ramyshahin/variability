import data.finset
import tactic.induction

namespace PCF

-- vname: variable name
def vname := string

@[derive [decidable_eq]]
inductive τ 
| Nat : τ
| Bool : τ
| Arrow : τ → τ → τ

def to_string_τ : τ → string
| τ.Nat           := "ℕ"
| τ.Bool          := "Bool"
| (τ.Arrow t₀ t₁) := (to_string_τ t₀) ++ " → " ++ (to_string_τ t₁)

instance : has_to_string τ := ⟨to_string_τ⟩
instance : has_repr τ := ⟨to_string_τ⟩

inductive expr
| Zero : expr
| succ : expr → expr
--| pred : expr → expr
| True : expr
| False : expr
| zero : expr → expr
| Var : vname → expr
| ITE : expr → expr → expr → expr
| LAM : vname → τ → expr → expr
| APP : expr → expr → expr
| FIX : vname → τ → expr → expr

-- fv: free variables in expressions
def fv : expr → finset vname
| expr.Zero         := ∅ 
| (expr.succ e)     := fv e
--| (expr.pred e)     := fv e
| expr.True         := ∅ 
| expr.False        := ∅
| (expr.zero e)     := fv e
| (expr.Var v)      := {v}
| (expr.ITE c t e)  := (fv c) ∪ (fv t) ∪ (fv e)
| (expr.LAM v t b)  := (fv b) \ {v}
| (expr.APP e₀ e₁)  := (fv e₀) ∪ (fv e₁)
| (expr.FIX v t b)  := (fv b) \ {v} 

-- substitution
def sub (s: expr) (v: vname) : expr → expr
| expr.Zero         := expr.Zero
| (expr.succ e')    := expr.succ (sub e')
--| (expr.pred e')    := expr.pred (sub e')
| expr.True         := expr.True
| expr.False        := expr.True
| (expr.zero e')    := expr.zero (sub e')
| (expr.Var v')     := if v = v' then s else expr.Var v'
| (expr.ITE c t e') := expr.ITE (sub c) (sub t) (sub e')
| (expr.LAM v' t b) := if v = v' then expr.LAM v' t b else expr.LAM v' t (sub b)
| (expr.APP e₀ e₁)  := expr.APP (sub e₀) (sub e₁)
| (expr.FIX v' t b) := if v = v' then expr.FIX v' t b else expr.FIX v' t (sub b)

-- type environment
def env : Type := vname → option τ
def emptyEnv : env := λ x, none
def addType (Γ: env) (v: vname) (t: τ) : env := 
λ x, if (x = v) then (some t) else (Γ x)

-- typing function
def typing : env → expr → option τ
| _ expr.Zero         := τ.Nat
| Γ (expr.succ e)     := if typing Γ e = some τ.Nat then some τ.Nat else none 
--| Γ (expr.pred e)     := if typing Γ e = some τ.Nat then some τ.Nat else none
| _ expr.True         := τ.Bool
| _ expr.False        := τ.Bool
| Γ (expr.zero e)     := if typing Γ e = some τ.Nat then some τ.Bool else none
| Γ (expr.Var v)      := Γ v
| Γ (expr.ITE c t e)  := if (typing Γ c = some τ.Bool) && (typing Γ t = typing Γ e) then typing Γ t else none
| Γ (expr.LAM v t b)  := let tb := (typing (addType Γ v t)) b in
                         match tb with
                         | none     := none
                         | some t'  := τ.Arrow t t'
                         end
| Γ (expr.APP e₀ e₁)  := let t₀ := typing Γ e₀,
                             t₁ := typing Γ e₁ in
                         match t₀, t₁ with
                         | some (τ.Arrow t' t''), some t''' := if (t' = t''') then (some t'') else none
                         | _, _ := none
                         end
| Γ (expr.FIX v t b)  := let tb := (typing (addType Γ v t)) b in
                         match tb with
                         | some t' := if t = t' then some t else none
                         | _ := none
                         end

namespace operational
-- call-by-value operational semantics of PCF

-- values (normal forms)
inductive val : expr → Prop
| zero : val expr.Zero
| true : val expr.True
| false : val expr.False
| succ {e} (h: val e) : val (expr.succ e)
--| pred {e} (h: val e) : val (expr.pred e)
| lam {v} {t} {e} : val (expr.LAM v t e)

inductive big_step : expr → expr → Prop
-- reduction rules
--| v {e} (h: val e) : big_step e e
| succ {e e'} (h: big_step e e'): big_step (expr.succ e) (expr.succ e')
--| pred_z: big_step (expr.pred expr.Zero) expr.Zero
--| pred {e e'} (h: big_step e e') : big_step (expr.pred e) e'
| zero_t {e} (h: big_step e expr.Zero) : big_step (expr.zero e) (expr.True)
| zero_f {e e'} (h: big_step e (expr.succ e')) : big_step (expr.zero e) (expr.False)
--| if_ {c t f c'} (hc: big_step c c'): big_step (expr.ITE c t f) (expr.ITE c' t f)
| if_t {c t t' e} (hc: big_step c expr.True) (ht : big_step t t'): big_step (expr.ITE c t e) t'
| if_f {c t e e'} (hc: big_step c expr.False) (ht : big_step e e'): big_step (expr.ITE c t e) e'
| app_1 {e₀ e₀' e₁} (h: big_step e₀ e₀'): big_step (expr.APP e₀ e₁) (expr.APP e₀' e₁)
| app_2 {e₀ e₁ e₁'} (h₀: val e₀) (h₁: big_step e₁ e₁'): big_step (expr.APP e₀ e₁) (expr.APP e₀ e₁')
| app_lam {x t e e₀} (h₀: val e₀): big_step (expr.APP (expr.LAM x t e) e₀) (sub e₀ x e)
| fix {x t b} : big_step (expr.FIX x t b) (sub (expr.FIX x t b) x b)

infix ` ⟹ ` : 110 := big_step

theorem big_step_deterministic {e₀ e₁ e₂} 
  (h₀: e₀ ⟹ e₁) (h₁: e₀ ⟹ e₂) : 
  e₁ = e₂ :=
begin
  induction' h₀, 
    case succ {
      cases h₁, 
      simp, 
      apply ih, 
      assumption },
    case zero_t {
      cases h₁, 
      refl,
      have h₂ := ih h₁_h, cases h₂},
    case zero_f: e₃ e₄ {
      cases h₁,
      have h₂ := ih h₁_h, cases h₂,
      refl },
    case if_t: e₃ e₄ e₅ e₆ h₂ h₃ h₄ h₅ {
      apply h₅, cases h₁, assumption,
      have h₇ := h₄ h₁_hc, cases h₇ },
    case if_f: e₃ e₄ e₅ e₆ h₂ h₃ h₄ h₅ {
      apply h₅, cases h₁,
      have h₇ := h₄ h₁_hc, cases h₇,
      assumption },
    case app_1 : e₃ e₄ e₅ {
      cases h₁,
        simp, apply ih, assumption,
        rw (@ih e₃), simp, assumption,
    },
    -- easy cases
    repeat {cases h₁, refl},
    -- succ 
    rw ih e₁, 
    cases h₁, rw h₀_ih, refl,
    -- true
    cases h₁, refl,
end

end operational

namespace denotational
-- denotational semantics of PCF
def bot {α : Type} : Type := false → α --:= λf, by contradiction

def lifted_T (α : Type) := (@bot α) ⊕ α

def denoteT : τ → Type
| τ.Nat := lifted_T ℕ
| τ.Bool := lifted_T bool
| (τ.Arrow t₀ t₁) := (denoteT t₀) → (denoteT t₁)

end denotational

end PCF