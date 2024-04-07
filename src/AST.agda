module AST {n} where

open import Data.Fin 
open import Data.Nat 
open import Data.Product

-- | AST for expressions and statements.

-- Expressions for language with brackets.
data ASTExpS : Set where
   IntVal : ℕ → ASTExpS 
   Var    : Fin n → ASTExpS
   Add    : ASTExpS → ASTExpS → ASTExpS
   
-- Statements with brackets.
data ASTStmS : Set where
   ⟦_:=_⟧ : Fin n → ASTExpS → ASTStmS
   _:=_   : Fin n → ASTExpS → ASTStmS
   If0    : ASTExpS → ASTStmS → ASTStmS → ASTStmS 
   While  : ASTExpS → ASTStmS → ASTStmS 
   Seq    : ASTStmS → ASTStmS → ASTStmS 
   Skip   : ASTStmS 

-- Expressions for language without brackets.
data ASTExp : Set where
   INTVAL : ℕ → ASTExp 
   VAR    : Fin n × ℕ → ASTExp
   ADD    : ASTExp → ASTExp → ASTExp 

-- Statements without brackets.
data ASTStm : Set where
   ASSIGN : Fin n × ℕ → ASTExp → ASTStm
   IF0    : ASTExp → ASTStm → ASTStm → ASTStm 
   WHILE  : ASTExp → ASTStm → ASTStm 
   SEQ    : ASTStm → ASTStm → ASTStm 
   SKIP   : ASTStm 

-- Statements without brackets and with assignment identifiers.
data ASTStmId : Set where
   ASSIGN : Fin n × ℕ → ℕ → ASTExp → ASTStmId
   IF0    : ASTExp → ASTStmId → ASTStmId → ASTStmId 
   WHILE  : ASTExp → ASTStmId → ASTStmId 
   SEQ    : ASTStmId → ASTStmId → ASTStmId 
   SKIP   : ASTStmId 
