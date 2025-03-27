module Transformation.Transformation {n} where

open import Data.Nat 
open import Data.Product 
open import Data.Vec.Base

open import Transformation.ActiveSet {n}
open import Transformation.AST {n}

-- Expression transformation.
transExp : ASTExpS → 𝒜 → ASTExp
transExp (IntVal n) _ = INTVAL n
transExp (Var v) A = VAR (v , lookup A v)
transExp (Add exp₁ exp₂) A = ADD (transExp exp₁ A) (transExp exp₂ A)

-- Program transformation from bracketed to non-bracketed statements, following the rules from Figure 4.
transStm : ASTStmS → 𝒜 → ASTStm × 𝒜
transStm Skip A = SKIP , A
transStm (v := e) A = ASSIGN (v , lookup A v) (transExp e A) , A
transStm ⟦ v := e ⟧ A = 
   let newIndex = suc (lookup A v) 
    in ASSIGN (v , newIndex) (transExp e A) , A [ v ]≔ newIndex
transStm (Seq s₁ s₂) A = 
   let tS₁ , A₁ = transStm s₁ A
       tS₂ , A₂ = transStm s₂ A₁
    in SEQ tS₁ tS₂ , A₂
transStm (If cond sT sF) A =
   let tCond = transExp cond A
       tST , A₁ = transStm sT A
       tSF , A₂ = transStm sF A
       A₃ = merge𝒜 A₁ A₂
       trueBranch = SEQ tST (A₃ :=𝒜 A₁)
       falseBranch = SEQ tSF (A₃ :=𝒜 A₂)
    in IF tCond trueBranch falseBranch , A₃
transStm (While cond s) A =
   let _ , A₁ = transStm s A
       A₂ = merge𝒜 A A₁
       tCond = transExp cond A₂
       tS , A₃ = transStm s A₂
    in SEQ (A₂ :=𝒜 A) (WHILE tCond (SEQ tS (A₂ :=𝒜 A₃))) , A₂

-- Transformation of a bracketed program to its non-bracketed version.
transformProgram : ASTStmS → ASTStm × 𝒜
transformProgram stm = transStm stm (replicate n zero)