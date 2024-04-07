module AssignmentId {n} where

open import Data.Nat 
open import Data.Product
open import Function.Base

open import AST {n}

identifyAssignmentsAux : ASTStm → ℕ → ASTStmId × ℕ
identifyAssignmentsAux (ASSIGN (var , index) exp) id = (ASSIGN (var , index) id exp , suc id)   
identifyAssignmentsAux (IF0 cond sT sF) id = 
   let sTId , id1 = identifyAssignmentsAux sT id
       sFId , id2 = identifyAssignmentsAux sF id1
   in IF0 cond sTId sFId , id2
identifyAssignmentsAux (WHILE cond s) id =
   let sId , id1 = identifyAssignmentsAux s id
   in WHILE cond sId , id1
identifyAssignmentsAux (SEQ s1 s2) id =
   let s1Id , id1 = identifyAssignmentsAux s1 id
       s2Id , id2 = identifyAssignmentsAux s2 id1
   in SEQ s1Id s2Id , id2     
identifyAssignmentsAux SKIP id = SKIP , id

-- Returns the given program with each assignment having a unique (integer) identifier
-- and the total number of assignments in it.
identifyAssignments : ASTStm → ASTStmId × ℕ
identifyAssignments ast = identifyAssignmentsAux ast zero 

-- TODO: Revisar si esta implementación es demasiado fea o me termina complicando a la larga.
-- Meter una segunda transformación no me gusta para nada, pero es lo que se me ocurrió.
-- Otra alternativa sería hacer algo como que las operaciones que requieren los identificadores 
-- los infieran de alguna forma, pero creo que eso es peor todavía.
