module TypeSystem.AssignmentId {n} where

open import Data.Fin
  hiding (_≤_ ; _+_ ; _<_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality 

open import Transformation.AST {n}

-- Counts the number of assignments in a program statement.
assignCount : ASTStm → ℕ
assignCount SKIP = 0
assignCount (ASSIGN _ _) = 1
assignCount (SEQ s₁ s₂) = assignCount s₁ + assignCount s₂
assignCount (IF _ sT sF) = assignCount sT + assignCount sF
assignCount (WHILE _ s) = assignCount s

mutual
  -- Function used to cover the IF and SEQ cases of idAssignAux, which are analogous since
  -- both involve identifying all assignments in one statement and then in the other.
  idStmSeq : {t : ℕ} {s : ASTStm} → (s₁ : ASTStm) → (s₂ : ASTStm) → (id : ℕ) → 
             assignCount s ≡ assignCount s₁ + assignCount s₂ → id + assignCount s ≤ t → 
             ASTStmId t × ASTStmId t
  idStmSeq {t} {s} s₁ s₂ id aCs=aCs₁+aCs₂ id+aCs≤t =
    let id+aCs=id+aCs₁+aCs₂ : id + assignCount s ≡ id + (assignCount s₁ + assignCount s₂) 
        id+aCs=id+aCs₁+aCs₂ = cong (λ y → id + y) aCs=aCs₁+aCs₂
        id+aCs₁+aCs₂-assoc : (id + assignCount s₁) + assignCount s₂ ≡ id + (assignCount s₁ + assignCount s₂)
        id+aCs₁+aCs₂-assoc = +-assoc id (assignCount s₁) (assignCount s₂)
        id+aCs₁+aCs₂≤t : (id + assignCount s₁) + assignCount s₂ ≤ t
        id+aCs₁+aCs₂≤t = subst (λ x → x ≤ t) (trans id+aCs=id+aCs₁+aCs₂ (sym id+aCs₁+aCs₂-assoc)) id+aCs≤t
        id+aCs₁≤t : id + assignCount s₁ ≤ t
        id+aCs₁≤t = m+n≤o⇒m≤o (id + assignCount s₁) id+aCs₁+aCs₂≤t
        s₁Id = idAssignAux s₁ id id+aCs₁≤t
        s₂Id = idAssignAux s₂ (id + assignCount s₁) id+aCs₁+aCs₂≤t
     in s₁Id , s₂Id 
  
  -- Auxiliary function to identifyAssignments. Given a statement s, an integer id and another integer t,
  -- which is the total number of assignments in the program being analysed, this function recursively
  -- traverses s assigning indices of type Fin t to each assignment statement it finds, starting from id
  -- and increasing it by 1 each time.  
  idAssignAux : {t : ℕ} → (s : ASTStm) → (id : ℕ) → id + assignCount s ≤ t → ASTStmId t
  idAssignAux SKIP _ _ = SKIP 
  idAssignAux {t} s@(ASSIGN v exp) id id+1≤t = 
    let 1+id≤t : assignCount s + id ≤ t
        1+id≤t = subst (λ x → x ≤ t) (+-comm id (assignCount s)) id+1≤t
    in ASSIGN v (fromℕ< 1+id≤t) exp
  idAssignAux {t} s@(SEQ s₁ s₂) id id+aCs≤t =
    let s₁Id , s₂Id = idStmSeq {t} {s} s₁ s₂ id refl id+aCs≤t
     in SEQ s₁Id s₂Id   
  idAssignAux {t} s@(IF cond sT sF) id id+aCs≤t =
    let sTId , sFId = idStmSeq {t} {s} sT sF id refl id+aCs≤t
    in IF cond sTId sFId 
  idAssignAux (WHILE cond s) id id+aCs≤t =
    WHILE cond (idAssignAux s id id+aCs≤t)

-- Returns the given program with each assignment having a unique (integer) identifier.
identifyAssignments : (s : ASTStm) → ASTStmId (assignCount s)
identifyAssignments s = idAssignAux s zero (≤-reflexive refl)
