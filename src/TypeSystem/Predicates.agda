module TypeSystem.Predicates {n} where

open import Data.Bool.Base
open import Data.List.Base
  hiding (replicate)
open import Data.Nat
open import Data.Product
open import Data.Vec.Base 

open import Transformation.AST {n}
open import Transformation.VariableSet {n}

data Predicate : Set where
    True : Predicate
    ExpZero : ASTExp → Predicate
    ExpNonZero : ASTExp → Predicate
    And : Predicate → Predicate → Predicate

simplifyAnd : Predicate → Predicate → Predicate
simplifyAnd True pred = pred
simplifyAnd pred True = pred
simplifyAnd pred₁ pred₂ = And pred₁ pred₂

-- Removes all parts of a predicate that contain a given variable.
removeVarFromPred : Predicate → TransVariable → Predicate
removeVarFromPred True _ = True
removeVarFromPred pred@(ExpZero exp) v = if v elemᵥₛ (expressionVariables exp) then True else pred
removeVarFromPred pred@(ExpNonZero exp) v = if v elemᵥₛ (expressionVariables exp) then True else pred
removeVarFromPred (And pred₁ pred₂) v = simplifyAnd (removeVarFromPred pred₁ v) (removeVarFromPred pred₂ v)

-- Equality test for predicates.
_==ₚ_ : Predicate → Predicate → Bool
True ==ₚ True = true
ExpZero exp₁ ==ₚ ExpZero exp₂ = exp₁ ==ₑ exp₂
ExpNonZero exp₁ ==ₚ ExpNonZero exp₂ = exp₁ ==ₑ exp₂
And pred₁ pred₂ ==ₚ And pred₃ pred₄ = (pred₁ ==ₚ pred₃) ∧ (pred₂ ==ₚ pred₄)
_ ==ₚ _ = false

-- Checks if a base predicate is part of another predicate.
containsPred : Predicate → Predicate → Bool
containsPred pred (And pred₁ pred₂) = (containsPred pred pred₁) ∨ (containsPred pred pred₂)
containsPred pred₁ pred₂ = pred₁ ==ₚ pred₂

-- Finds all base predicates that are part of both the given predicates and return a conjunction of them.
intersectPred : Predicate → Predicate → Predicate
intersectPred (And pred₁ pred₂) pred = simplifyAnd (intersectPred pred₁ pred) (intersectPred pred₂ pred)
intersectPred pred₁ pred₂ = if containsPred pred₁ pred₂ then pred₁ else True

-- Iterates through the given program statement and determines a predicate that should always be true after its execution.
-- For that, it takes a predicate previous to the execution of the statement and uses that to determine predicates of the
-- intermediate steps of the execution doing a shallow branch analysis on IF and WHILE statements.
-- Additionally, when the function finds an assignment statement, it stores the predicate that was true before its execution
-- in the n-th index of a vector, where n is the index number of the assignment. 
populatePredicates : {t : ℕ} → ASTStmId t → Predicate → Vec Predicate t → Predicate × (Vec Predicate t)
populatePredicates SKIP pred predicates = pred , predicates
populatePredicates (ASSIGN v id _) pred predicates = removeVarFromPred pred v , predicates [ id ]≔ pred
populatePredicates (SEQ s₁ s₂) pred predicates = 
  let pred' , predicates' = populatePredicates s₁ pred predicates
   in populatePredicates s₂ pred' predicates'
populatePredicates (IF cond sT sF) pred predicates = 
  let predT , predicatesT = populatePredicates sT (simplifyAnd pred (ExpNonZero cond)) predicates
      predF , predicatesF = populatePredicates sF (simplifyAnd pred (ExpZero cond)) predicatesT
   in intersectPred predT predF , predicatesF
populatePredicates (WHILE cond s) pred predicates = 
  let pred' , predicates' = populatePredicates s (simplifyAnd pred (ExpNonZero cond)) predicates
      finalPred = intersectPred pred pred'
   in simplifyAnd finalPred (ExpZero cond) , predicates'

-- Given a program statement, returns a vector of predicates so that the element in its n-th
-- position is a predicate that is always true before the execution of the n-th assignment 
-- of the program. 
generatePredicates : {t : ℕ} → ASTStmId t → Vec Predicate t
generatePredicates {t} statement = proj₂ (populatePredicates statement True (replicate t True))