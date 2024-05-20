module AssignmentId {n} where

open import Data.Fin
  hiding (_≤_ ; _+_ ; _<_)
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality 

open import AST {n}

assignCount : ASTStm → ℕ
assignCount (ASSIGN _ _) = 1
assignCount (IF0 _ sT sF) = assignCount sT + assignCount sF
assignCount (WHILE _ s) = assignCount s
assignCount (SEQ s1 s2) = assignCount s1 + assignCount s2
assignCount SKIP = 0

-- Auxiliary function to identifyAssignments. Given a statement s, an integer id and another integer t,
-- which is the total number of assignments in the program being analysed, this function recursively
-- traverses s assigning indices of type Fin t to each assignment statement it finds, starting from id
-- and increasing it by 1 each time.  
identifyAssignmentsAux : {t : ℕ} → (s : ASTStm) → (id : ℕ) → id + assignCount s ≤ t → ASTStmId {t}
identifyAssignmentsAux {t} s@(ASSIGN x exp) id id+1≤t = 
   let 1+id≤t : assignCount s + id ≤ t
       1+id≤t = subst (λ x → x ≤ t) (+-comm id (assignCount s)) id+1≤t
   in ASSIGN x (fromℕ< {id} 1+id≤t) exp

identifyAssignmentsAux {t} s@(IF0 cond sT sF) id id+aCIf≤t =
   let id+aCIf=id+aCST+aCSF : id + assignCount s ≡ id + (assignCount sT + assignCount sF) 
       id+aCIf=id+aCST+aCSF = cong (λ y → id + y) refl

       id+aCST+aCSF-assoc : (id + assignCount sT) + assignCount sF ≡ id + (assignCount sT + assignCount sF)
       id+aCST+aCSF-assoc = +-assoc id (assignCount sT) (assignCount sF) 

       id+aCST+aCSF≤t : (id + assignCount sT) + assignCount sF ≤ t
       id+aCST+aCSF≤t = subst (λ x → x ≤ t) (trans id+aCIf=id+aCST+aCSF (sym id+aCST+aCSF-assoc)) id+aCIf≤t
       
       id+aCST≤t : id + assignCount sT ≤ t
       id+aCST≤t = m+n≤o⇒m≤o (id + assignCount sT) id+aCST+aCSF≤t
       
       sTId = identifyAssignmentsAux sT id id+aCST≤t
       sFId = identifyAssignmentsAux sF (id + assignCount sT) id+aCST+aCSF≤t
   in IF0 cond sTId sFId 

identifyAssignmentsAux (WHILE cond s) id id+aCS≤t =
   WHILE cond (identifyAssignmentsAux s id id+aCS≤t)

identifyAssignmentsAux {t} s@(SEQ s1 s2) id id+aCSeq≤t =
   let id+aCSeq=id+aCS1+aCS2 : id + assignCount s ≡ id + (assignCount s1 + assignCount s2) 
       id+aCSeq=id+aCS1+aCS2 = cong (λ y → id + y) refl

       id+aCS1+aCS2-assoc : (id + assignCount s1) + assignCount s2 ≡ id + (assignCount s1 + assignCount s2)
       id+aCS1+aCS2-assoc = +-assoc id (assignCount s1) (assignCount s2)

       id+aCS1+aCS2≤t : (id + assignCount s1) + assignCount s2 ≤ t
       id+aCS1+aCS2≤t = subst (λ x → x ≤ t) (trans id+aCSeq=id+aCS1+aCS2 (sym id+aCS1+aCS2-assoc)) id+aCSeq≤t
       
       id+aCS1≤t : id + assignCount s1 ≤ t
       id+aCS1≤t = m+n≤o⇒m≤o (id + assignCount s1) id+aCS1+aCS2≤t
       
       s1Id = identifyAssignmentsAux s1 id id+aCS1≤t
       s2Id = identifyAssignmentsAux s2 (id + assignCount s1) id+aCS1+aCS2≤t
    in SEQ s1Id s2Id 

identifyAssignmentsAux SKIP _ _ = SKIP 

-- Returns the given program with each assignment having a unique (integer) identifier.
identifyAssignments : (s : ASTStm) → ASTStmId {1 + assignCount s}
identifyAssignments ast = identifyAssignmentsAux ast zero (n≤1+n (assignCount ast))
