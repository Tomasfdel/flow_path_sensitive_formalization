module AST {n} where

open import Agda.Builtin.Nat 
open import Data.Bool.Base
open import Data.Fin
open import Data.Nat

open import VariableSet {n}

-- AST for expressions and statements.

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
   VAR    : TransVariable → ASTExp
   ADD    : ASTExp → ASTExp → ASTExp 

-- Equality test for expressions.
_==ₑ_ : ASTExp → ASTExp → Bool
(INTVAL v1) ==ₑ (INTVAL v2) = v1 == v2
(VAR v1) ==ₑ (VAR v2) = v1 ==ᵥ v2
(ADD exp1 exp2) ==ₑ (ADD exp3 exp4) = (exp1 ==ₑ exp3) ∧ (exp2 ==ₑ exp4)
_ ==ₑ _ = false

-- Set of free variables of an expression.
expressionVariables : ASTExp → VariableSet
expressionVariables (INTVAL _) = emptyᵥₛ
expressionVariables (VAR variableName) = singletonᵥₛ variableName
expressionVariables (ADD expression1 expression2) = 
    (expressionVariables expression1) unionᵥₛ (expressionVariables expression2)

-- Statements without brackets.
data ASTStm : Set where
   ASSIGN : TransVariable → ASTExp → ASTStm
   IF0    : ASTExp → ASTStm → ASTStm → ASTStm 
   WHILE  : ASTExp → ASTStm → ASTStm 
   SEQ    : ASTStm → ASTStm → ASTStm 
   SKIP   : ASTStm 

-- Statements without brackets and with assignment identifiers.
-- A program is parameterized by the total number of assignment statements it has.
data ASTStmId {t : ℕ} : Set where
   ASSIGN : TransVariable → Fin t → ASTExp → ASTStmId {t}
   IF0    : ASTExp → ASTStmId {t} → ASTStmId {t} → ASTStmId {t}
   WHILE  : ASTExp → ASTStmId {t} → ASTStmId {t}
   SEQ    : ASTStmId {t} → ASTStmId {t} → ASTStmId {t}
   SKIP   : ASTStmId {t}
