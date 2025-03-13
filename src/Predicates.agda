module Predicates {n} where

open import Data.Bool.Base
open import Data.Fin 
open import Data.List.Base
open import Data.Nat
open import Data.Product
open import Data.Vec.Base 

open import AST {n}
open import VariableSet {n}

data Predicate : Set where
    True : Predicate
    ExpZero : ASTExp → Predicate
    ExpNonZero : ASTExp → Predicate
    And : Predicate → Predicate → Predicate

simplifyAnd : Predicate → Predicate → Predicate
simplifyAnd True pred = pred
simplifyAnd pred True = pred
simplifyAnd pred1 pred2 = And pred1 pred2

removePredicatesWithVariable : Predicate → Fin n × ℕ → Predicate
removePredicatesWithVariable True _ = True
removePredicatesWithVariable predicate@(ExpZero expression) variableName = 
    if variableName elemᵥₛ (expressionVariables expression) then True else predicate
removePredicatesWithVariable predicate@(ExpNonZero expression) variableName = 
    if variableName elemᵥₛ (expressionVariables expression) then True else predicate
removePredicatesWithVariable (And predicate1 predicate2) variableName = 
    simplifyAnd (removePredicatesWithVariable predicate1 variableName) (removePredicatesWithVariable predicate2 variableName)

_==ₚ_ : Predicate → Predicate → Bool
True ==ₚ True = true
(ExpZero exp1) ==ₚ (ExpZero exp2) = exp1 ==ₑ exp2
(ExpNonZero exp1) ==ₚ (ExpNonZero exp2) = exp1 ==ₑ exp2
(And pred1 pred2) ==ₚ (And pred3 pred4) = (pred1 ==ₚ pred3) ∧ (pred2 ==ₚ pred4)
_ ==ₚ _ = false

containsPredicate : Predicate → Predicate → Bool
containsPredicate pred (And pred1 pred2) = 
    (containsPredicate pred pred1) ∨ (containsPredicate pred pred2)
containsPredicate pred1 pred2 = pred1 ==ₚ pred2

intersectPredicates : Predicate → Predicate → Predicate
intersectPredicates (And pred1 pred2) pred = 
    simplifyAnd (intersectPredicates pred1 pred) (intersectPredicates pred2 pred)
intersectPredicates pred1 pred2 = 
    if containsPredicate pred1 pred2 then pred1 else True

-- Iterates through the given program statement and determines a predicate that should always be true after its execution.
-- For that, it takes a predicate previous to the execution of the statement and uses that to determine predicates of the
-- intermediate steps of the execution doing a shallow branch analysis on IF and WHILE statements.
-- Additionally, when the function finds an assignment statement, it stores the predicate that was true before its execution
-- in the n-th index of a vector, where n is the index number of the assignment. 
populatePredicateVector : {t : ℕ} → ASTStmId {t} → Predicate → Vec Predicate t → Predicate × (Vec Predicate t)
populatePredicateVector (ASSIGN variableName assignId _) predicate predicateVector = 
    let newPredicate = removePredicatesWithVariable predicate variableName
        newPredicateVector = predicateVector [ assignId ]≔ predicate
     in newPredicate , newPredicateVector
populatePredicateVector (IF0 condition statementT statementF) predicate predicateVector = 
    let predicateT , predicateVectorT = populatePredicateVector statementT (simplifyAnd predicate (ExpNonZero condition)) predicateVector
        predicateF , predicateVectorF = populatePredicateVector statementF (simplifyAnd predicate (ExpZero condition)) predicateVectorT
     in intersectPredicates predicateT predicateF , predicateVectorF
populatePredicateVector (WHILE condition statement) predicate predicateVector = 
    let predicate2 , predicateVector2 = populatePredicateVector statement (simplifyAnd predicate (ExpNonZero condition)) predicateVector
        finalPredicate = intersectPredicates predicate predicate2
     in (simplifyAnd finalPredicate (ExpZero condition)) , predicateVector2
populatePredicateVector (SEQ statement1 statement2) predicate predicateVector = 
    let predicate2 , predicateVector2 = populatePredicateVector statement1 predicate predicateVector
     in populatePredicateVector statement2 predicate2 predicateVector2
populatePredicateVector SKIP predicate predicateVector =
    predicate , predicateVector

-- Given a program statement, returns a vector of predicates so that the element in its n-th
-- position is a predicate that is always true before the execution of the n-th assignment 
-- of the program. 
generatePredicates : {t : ℕ} → ASTStmId {t} → Vec Predicate t
generatePredicates {t} statement =
    proj₂ (populatePredicateVector statement True (Data.Vec.Base.replicate t True))