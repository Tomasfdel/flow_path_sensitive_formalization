module Transformation {n} where

open import Data.Nat 
open import Data.Fin 
open import Data.Vec
open import Data.Product 

-- | AST for expressions and statements

-- Expressions
data ASTExp : Set where
   INTVAL : ℕ → ASTExp 
   VAR    : Fin n → ASTExp
   ADD    : ASTExp  → ASTExp  → ASTExp 
   
-- Statements with brackets
data ASTStmS : Set where
   ⟦_:=_⟧ : Fin n → ASTExp  → ASTStmS
   _:=_   : Fin n → ASTExp  → ASTStmS
   If0    : ASTExp → ASTStmS → ASTStmS  → ASTStmS 
   While  : ASTExp → ASTStmS → ASTStmS 
   Seq    : ASTStmS → ASTStmS → ASTStmS 
   Skip   : ASTStmS 

-- Statements without brackets
data ASTStm : Set where
   ASSIGN : Fin n × ℕ → ASTExp  → ASTStm     
   IF0    : ASTExp → ASTStm → ASTStm  → ASTStm 
   WHILE  : ASTExp → ASTStm → ASTStm 
   SEQ    : ASTStm → ASTStm → ASTStm 
   SKIP   : ASTStm 

-- Active Sets
𝒜 : Set _
𝒜 = Vec ℕ n  -- es lo mismo que Fin n → ℕ 

-- Transformation
trans : ASTStmS × 𝒜  → ASTStm × 𝒜 -- ver si el último producto no es dependiente, en cuyo caso sería Σ 𝒜 ASTStm
trans t = {!!} 

-- TODO: La definición de esta función va a ser más a lo Haskell. Nada raro de Agda dando vueltas.

-- TODO: Ver qué onda el argumento del módulo que definió Ceci acá.


-- Correctness of the transformation

-- Lo dejaría para el final ya que hay dar la semántica
-- TODO: Ver si vamos a implementar esta parte o si hay alguna otra propiedad que tenga sentido formalizar.

