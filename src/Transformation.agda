module Transformation {n} where

-- TODO: Cuando termine de implementar todo, ver si sigo necesitando todos estos imports.
open import Data.Bool.Base
open import Data.Nat 
open import Agda.Builtin.Nat
open import Data.Fin 
open import Data.Vec
open import Data.Vec.Base
open import Data.Product 

-- | AST for expressions and statements

-- Expressions for language without brackets
data ASTExpS : Set where
   IntVal : ℕ → ASTExpS 
   Var    : Fin n → ASTExpS
   Add    : ASTExpS  → ASTExpS  → ASTExpS
   
-- Statements with brackets
data ASTStmS : Set where
   ⟦_:=_⟧ : Fin n → ASTExpS  → ASTStmS
   _:=_   : Fin n → ASTExpS  → ASTStmS
   If0    : ASTExpS → ASTStmS → ASTStmS  → ASTStmS 
   While  : ASTExpS → ASTStmS → ASTStmS 
   Seq    : ASTStmS → ASTStmS → ASTStmS 
   Skip   : ASTStmS 

-- Expressions for language without brackets
data ASTExp : Set where
   INTVAL : ℕ → ASTExp 
   VAR    : Fin n × ℕ → ASTExp
   ADD    : ASTExp  → ASTExp  → ASTExp 

-- Statements without brackets
data ASTStm : Set where
   ASSIGN : Fin n × ℕ → ASTExp  → ASTStm     
   IF0    : ASTExp → ASTStm → ASTStm  → ASTStm 
   WHILE  : ASTExp → ASTStm → ASTStm 
   SEQ    : ASTStm → ASTStm → ASTStm 
   SKIP   : ASTStm 

-- Active Sets
-- Using a vector to represent a Fin n → ℕ 
𝒜 : Set _
𝒜 = Vec ℕ n

mergeActiveSets : {m : ℕ} → Vec ℕ m → Vec ℕ m → Vec ℕ m
mergeActiveSets [] [] = []
mergeActiveSets (h1 ∷ t1) (h2 ∷ t2) =
   (if h1 == h2 then h1 else (suc (h1 ⊔ h2))) ∷ (mergeActiveSets t1 t2)

-- TODO: Esta definición es una asquerosidad, ver cómo puedo hacerla mejor.
-- TODO: Ceci recomienda que vea qué onda with. Volver a revisar cómo funciona.
assignActiveSetAux : {m : ℕ} → Vec (Fin n) m → Vec ℕ m → Vec ℕ m → ASTStm
assignActiveSetAux _ [] [] = SKIP
assignActiveSetAux (i1 ∷ iR) (h1 ∷ t1) (h2 ∷ t2) = 
   let assignment = ASSIGN (i1 , h1) (VAR (i1 , h2)) 
       assignRest = assignActiveSetAux iR t1 t2
   in if h1 == h2 then assignRest else (SEQ assignment assignRest)

assignActiveSet : 𝒜 → 𝒜 → ASTStm
assignActiveSet = assignActiveSetAux (allFin n)

-- Auxiliary functions for sequences using assignActiveSet.
-- TODO: Preguntarle a Ceci si esto es necesario.
seqWithoutLeftSkip : ASTStm → ASTStm → ASTStm
seqWithoutLeftSkip SKIP s = s
seqWithoutLeftSkip s1 s2  = SEQ s1 s2

seqWithoutRightSkip : ASTStm → ASTStm → ASTStm
seqWithoutRightSkip s SKIP = s
seqWithoutRightSkip s1 s2  = SEQ s1 s2

-- Expressions transformation
transExp : ASTExpS → 𝒜 → ASTExp
transExp (IntVal n) _ = INTVAL n
transExp (Var v) active = VAR (v , lookup active v)
transExp (Add e1 e2) active = ADD (transExp e1 active) (transExp e2 active)

-- Transformation
-- TODO: Releer esta implementación para asegurarme que sigue la especificación del paper.
trans : ASTStmS → 𝒜 → ASTStm × 𝒜
trans Skip active = (SKIP , active)
trans (v := e) active = (ASSIGN (v , lookup active v) (transExp e active) , active)
trans ⟦ v := e ⟧ active = 
   let newIndex = suc (lookup active v) 
   in (ASSIGN (v , newIndex) (transExp e active) , (active [ v ]≔ newIndex) )
trans (Seq s1 s2) active = 
   let (tS1 , active1) = trans s1 active
       (tS2 , active2) = trans s2 active1
   in (SEQ tS1 tS2 , active2)
trans (If0 cond sT sF) active =
   let tCond = transExp cond active
       (tST , active1) = trans sT active
       (tSF , active2) = trans sF active
       active3 = mergeActiveSets active1 active2
       trueBranch = seqWithoutRightSkip tST (assignActiveSet active3 active1)
       flaseBranch = seqWithoutRightSkip tSF (assignActiveSet active3 active2)
   in (IF0 tCond trueBranch flaseBranch , active3)
trans (While cond s) active =
   let (_ , active1) = trans s active
       active2 = mergeActiveSets active active1
       (tS , active3) = trans s active2
       tCond = transExp cond active2
   in (seqWithoutLeftSkip (assignActiveSet active2 active) 
                          (WHILE tCond 
                                 (seqWithoutRightSkip tS (assignActiveSet active2 active3))) , active2)

-- TODO: Ver qué onda el argumento del módulo que definió Ceci acá.

-- Correctness of the transformation
-- TODO: Ver si vamos a implementar esta parte o si hay alguna otra propiedad que tenga sentido formalizar. 
-- Lo dejaría para el final ya que hay dar la semántica