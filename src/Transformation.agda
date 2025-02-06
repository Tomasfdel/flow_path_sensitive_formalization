module Transformation {n} where

open import Agda.Builtin.Nat
open import Data.Bool.Base
open import Data.Fin 
open import Data.Nat 
open import Data.Product 
open import Data.Vec.Base

open import AST {n}

-- Active Sets.
-- Using a vector to represent a Fin n → ℕ .
𝒜 : Set _
𝒜 = Vec ℕ n

-- Active sets merge function from Figure 5 of the paper.
merge𝒜 : {m : ℕ} → Vec ℕ m → Vec ℕ m → Vec ℕ m
merge𝒜 [] [] = []
merge𝒜 (h1 ∷ t1) (h2 ∷ t2) =
   (if h1 == h2 then h1 else (suc (h1 ⊔ h2))) ∷ (merge𝒜 t1 t2)

-- Returns a sequence of two statements, unless one of them is a 
-- SKIP, in which case the other is returned.
simplifiedSeq : ASTStm → ASTStm → ASTStm
simplifiedSeq SKIP s = s
simplifiedSeq s SKIP = s
simplifiedSeq s1 s2  = SEQ s1 s2

assignActiveSetAux : {m : ℕ} → Vec (Fin n) m → Vec ℕ m → Vec ℕ m → ASTStm
assignActiveSetAux _ [] [] = SKIP
assignActiveSetAux (hInd ∷ tInd) (h1 ∷ t1) (h2 ∷ t2) = 
   let assignment = ASSIGN (hInd , h1) (VAR (hInd , h2)) 
       assignRest = assignActiveSetAux tInd t1 t2
   in if h1 == h2 then assignRest else (simplifiedSeq assignment assignRest)

-- := definition for active sets from Figure 4 of the paper.
_:=𝒜_ : 𝒜 → 𝒜 → ASTStm
_:=𝒜_ = assignActiveSetAux (allFin n)

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
       trueBranch = simplifiedSeq tST (active3 :=𝒜 active1)
       falseBranch = simplifiedSeq tSF (active3 :=𝒜 active2)
   in (IF0 tCond trueBranch falseBranch , active3)
transStm (While cond s) active =
   let (_ , active1) = transStm s active
       active2 = merge𝒜 active active1
       (tS , active3) = transStm s active2
       tCond = transExp cond active2
   in (simplifiedSeq (active2 :=𝒜 active) 
                          (WHILE tCond 
                                 (simplifiedSeq tS (active2 :=𝒜 active3))) , active2)
