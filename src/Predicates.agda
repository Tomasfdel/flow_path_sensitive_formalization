module Predicates {n} where

open import Data.Bool.Base
open import Data.Fin 
open import Data.List.Base
open import Data.Nat
open import Data.Product
open import Data.Vec.Base 

open import AST {n}
open import NonRepeatingCollection

data Predicate : Set where
    True : Predicate
    ExpZero : ASTExp → Predicate
    ExpNonZero : ASTExp → Predicate
    And : Predicate → Predicate → Predicate

simplifyAnd : Predicate → Predicate → Predicate
simplifyAnd True pred = pred
simplifyAnd pred True = pred
simplifyAnd pred1 pred2 = And pred1 pred2

-- TODO: Move somewhere else.
-- TODO: Replace NonRepeatingCollection (Fin n × ℕ) by the VariableSet type.
expressionVariables : ASTExp → NonRepeatingCollection (Fin n × ℕ)
expressionVariables (INTVAL _) = listToNRC []
expressionVariables (VAR variableName) = listToNRC (variableName ∷ [])
expressionVariables (ADD expression1 expression2) = 
    unionNRC (expressionVariables expression1) (expressionVariables expression2)

removePredicatesWithVariable : Predicate → Fin n × ℕ → Predicate
removePredicatesWithVariable True _ = True
removePredicatesWithVariable predicate@(ExpZero expression) variableName = 
    if hasElemNRC variableName (expressionVariables expression) then True else predicate
removePredicatesWithVariable predicate@(ExpNonZero expression) variableName = 
    if hasElemNRC variableName (expressionVariables expression) then True else predicate
removePredicatesWithVariable (And predicate1 predicate2) variableName = 
    simplifyAnd (removePredicatesWithVariable predicate1 variableName) (removePredicatesWithVariable predicate2 variableName)

populatePredicateVector : {m : ℕ} → ASTStmId → Predicate → Vec Predicate m → Predicate × (Vec Predicate m)
-- TODO: newPredicateVector should equal (predicateVector [ assignId ]≔ predicate) but for that I 
-- need to see how to make it so that assignId is of type (Fin m) instead of ℕ.
populatePredicateVector (ASSIGN variableName assignId _) predicate predicateVector = 
    let newPredicate = removePredicatesWithVariable predicate variableName
        newPredicateVector = predicateVector
     in newPredicate , newPredicateVector
-- TODO: This is not entirely correct in the case that the original predicate can become
-- false in both the conditional branches, so I have to check that every condition in the predicate
-- is still present in both the resulting predicates from the conditional branches.
populatePredicateVector (IF0 condition statementT statementF) predicate predicateVector = 
    let _ , predicateVectorT = populatePredicateVector statementT (simplifyAnd predicate (ExpNonZero condition)) predicateVector
        _ , predicateVectorF = populatePredicateVector statementF (simplifyAnd predicate (ExpZero condition)) predicateVectorT
     in predicate , predicateVectorF
-- TODO: Here I also may need to remove some clauses from the predicate after the while since, similarly
-- to the IF0 case, some parts of the condition may become invalidated. However, I should always remove
-- that part from the predicate after the while since I cannot know statically whether the body will
-- execute or not, so to be safe those conditions need to be removed always. If a variable is not affected
-- by the while body and is part of a condition, that should be safe to keep as long as no affected variable is involved
-- in the condition.
populatePredicateVector (WHILE condition statement) predicate predicateVector = 
    let _ , predicateVector2 = populatePredicateVector statement (simplifyAnd predicate (ExpNonZero condition)) predicateVector
     in (simplifyAnd predicate (ExpZero condition)) , predicateVector2
populatePredicateVector (SEQ statement1 statement2) predicate predicateVector = 
    let predicate2 , predicateVector2 = populatePredicateVector statement1 predicate predicateVector
     in populatePredicateVector statement2 predicate2 predicateVector2
populatePredicateVector SKIP predicate predicateVector =
    predicate , predicateVector

generatePredicates : {m : ℕ} → ASTStmId → Vec Predicate m
generatePredicates statement =
    proj₂ (populatePredicateVector statement True (Data.Vec.Base.replicate True))