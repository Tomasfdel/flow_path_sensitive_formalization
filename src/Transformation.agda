module Transformation {n} where

open import Data.Nat 
open import Data.Product 
open import Data.Vec.Base


open import ActiveSet {n}
open import AST {n}

-- Expressions transformation.
transExp : ASTExpS → 𝒜 → ASTExp
transExp (IntVal n) _ = INTVAL n
transExp (Var v) active = VAR (v , lookup active v)
transExp (Add e1 e2) active = ADD (transExp e1 active) (transExp e2 active)

-- Program transformation from bracketed to non-bracketed statements,
-- following rules from figure 4 of the paper.
transStm : ASTStmS → 𝒜 → ASTStm × 𝒜
transStm Skip active = (SKIP , active)
transStm (v := e) active = (ASSIGN (v , lookup active v) (transExp e active) , active)
transStm ⟦ v := e ⟧ active = 
   let newIndex = suc (lookup active v) 
   in (ASSIGN (v , newIndex) (transExp e active) , (active [ v ]≔ newIndex) )
transStm (Seq s1 s2) active = 
   let (tS1 , active1) = transStm s1 active
       (tS2 , active2) = transStm s2 active1
   in (SEQ tS1 tS2 , active2)
transStm (If0 cond sT sF) active =
   let tCond = transExp cond active
       (tST , active1) = transStm sT active
       (tSF , active2) = transStm sF active
       active3 = merge𝒜 active1 active2
       trueBranch = SEQ tST (active3 :=𝒜 active1)
       falseBranch = SEQ tSF (active3 :=𝒜 active2)
   in (IF0 tCond trueBranch falseBranch , active3)
transStm (While cond s) active =
   let (_ , active1) = transStm s active
       active2 = merge𝒜 active active1
       (tS , active3) = transStm s active2
       tCond = transExp cond active2
   in (SEQ (active2 :=𝒜 active) 
                          (WHILE tCond 
                                 (SEQ tS (active2 :=𝒜 active3))) , active2)

transformProgram : ASTStmS → ASTStm × 𝒜
transformProgram stm = transStm stm (replicate n zero)