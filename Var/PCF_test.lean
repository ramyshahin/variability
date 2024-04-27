/-
import PCF

open PCF

-- example 5.3.2 from Prof. Marcelo Fiore's lecture notes on
-- Denotational Semantics
def F := expr.Var "F"
def G := expr.Var "G"
def x := expr.Var "x"
def y := expr.Var "y"
def h := expr.Var "h"

def Γ₀ := emptyEnv
def Γ₁ := addType Γ₀ "F" (τ.Arrow τ.Nat τ.Nat)
def Γ₂ := addType Γ₁ "G" (τ.Arrow τ.Nat
                          (τ.Arrow τ.Nat
                          (τ.Arrow τ.Nat τ.Nat)))

def H :=
  expr.FIX (expr.LAM "h" (τ.Arrow τ.Nat (τ.Arrow τ.Nat τ.Nat))
            (expr.LAM "x" τ.Nat
             (expr.LAM "y" τ.Nat
              (expr.ITE (expr.zero y)
                        (expr.APP F x)
                        (expr.APP (expr.APP (expr.APP G x)
                                            (expr.pred y))
                                  (expr.APP (expr.APP h x)
                                            (expr.pred y))
                        )
              )
             )
            )
           )

#check H
#eval typing Γ₂ H

-- example 5.6.1 (p. 45)
def V :=
  expr.LAM "x" τ.Nat
    (expr.APP (expr.LAM "y" τ.Nat (expr.Var "y"))
      expr.Zero)

#check V
#eval typing Γ₀ V

def V' := expr.LAM "x" τ.Nat (expr.Zero)
#check V'
#eval typing Γ₀ V'
-/
