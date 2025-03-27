module Transformation.AST {n} where

open import Agda.Builtin.Nat 
open import Data.Bool.Base
open import Data.Fin
open import Data.Nat

open import Transformation.VariableSet {n}

-- Expressions for language with brackets.
data ASTExpS : Set where
   IntVal : ℕ → ASTExpS 
   Var    : Fin n → ASTExpS
   Add    : ASTExpS → ASTExpS → ASTExpS
   
-- Statements with brackets.
data ASTStmS : Set where
   ⟦_:=_⟧ : Fin n → ASTExpS → ASTStmS
   _:=_   : Fin n → ASTExpS → ASTStmS
   If    : ASTExpS → ASTStmS → ASTStmS → ASTStmS 
   While  : ASTExpS → ASTStmS → ASTStmS 
   Seq    : ASTStmS → ASTStmS → ASTStmS 
   Skip   : ASTStmS 

-- Expressions for language without brackets.
data ASTExp : Set where
   INTVAL : ℕ → ASTExp 
   VAR    : TransVariable → ASTExp
   ADD    : ASTExp → ASTExp → ASTExp 

-- Equality test for expressions.
_==ₑ_ : ASTExp → ASTExp → Bool
(INTVAL n₁) ==ₑ (INTVAL n₂) = n₁ == n₂
(VAR v₁) ==ₑ (VAR v₂) = v₁ ==ᵥ v₂
(ADD exp₁ exp₂) ==ₑ (ADD exp₃ exp₄) = (exp₁ ==ₑ exp₃) ∧ (exp₂ ==ₑ exp₄)
_ ==ₑ _ = false

-- Set of free variables of an expression.
expressionVariables : ASTExp → VariableSet
expressionVariables (INTVAL _) = emptyᵥₛ
expressionVariables (VAR v) = singletonᵥₛ v
expressionVariables (ADD exp₁ exp₂) = 
    (expressionVariables exp₁) unionᵥₛ (expressionVariables exp₂)

-- Statements without brackets.
data ASTStm : Set where
   ASSIGN : TransVariable → ASTExp → ASTStm
   IF     : ASTExp → ASTStm → ASTStm → ASTStm 
   WHILE  : ASTExp → ASTStm → ASTStm 
   SEQ    : ASTStm → ASTStm → ASTStm 
   SKIP   : ASTStm 

-- Statements without brackets and with assignment identifiers.
-- A program is parameterized by the total number of assignment statements it has.
data ASTStmId (t : ℕ) : Set where
   ASSIGN : TransVariable → Fin t → ASTExp → ASTStmId t
   IF     : ASTExp → ASTStmId t → ASTStmId t → ASTStmId t
   WHILE  : ASTExp → ASTStmId t → ASTStmId t
   SEQ    : ASTStmId t → ASTStmId t → ASTStmId t
   SKIP   : ASTStmId t
