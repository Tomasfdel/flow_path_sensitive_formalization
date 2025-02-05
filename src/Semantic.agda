module Semantic {n} where

--open import Agda.Builtin.Nat
open import Data.Bool.Base
open import Data.Fin
  hiding (_+_)
open import Data.List
  hiding (lookup ; [_])
open import Data.Nat 
open import Data.Product 
open import Data.Vec.Base
open import Relation.Binary.PropositionalEquality 
  hiding ([_])

open import AST {n}
open import Transformation {n}


-- BRACKETED LANGUAGE SEMANTICS
-- State of the memory at a certain program point for the bracketed program.
Memory : Set _
Memory = Vec ℕ n

-- Update the value of a variable in memory.
infixl 6 _[_↦_]
_[_↦_] : Memory → Fin n → ℕ → Memory
m [ name ↦ v ] = m [ name ]≔ v

-- Semantic evaluation of expressions.
-- TODO(minor): Add the rest of the arythmetic operations besides ADD to the ASTExp type.
⟦_⟧ : ASTExpS → Memory → ℕ
⟦ IntVal n ⟧ m = n
⟦ Var name ⟧ m = lookup m name
⟦ Add exp exp' ⟧ m = ⟦ exp ⟧ m + ⟦ exp' ⟧ m
  
-- Big step semantics of statements.
infixl 5 ⟨_,_⟩⇓_
data ⟨_,_⟩⇓_ : ASTStmS → Memory → Memory → Set where
  Skip : {m : Memory} → ⟨ Skip , m ⟩⇓ m
  Seq : {m m' m'' : Memory}{s₁ s₂ : ASTStmS}
    → ⟨ s₁ , m ⟩⇓ m'  
    → ⟨ s₂ , m' ⟩⇓ m'' 
    → ⟨ Seq s₁ s₂ , m ⟩⇓ m'' 
  Assign : {m : Memory} {x : Fin n} {e : ASTExpS} 
    → ⟨ x := e , m ⟩⇓ m [ x  ↦ ⟦ e ⟧ m ]
  -- TODO(minor): How do I set the precedence for this to work properly using '⟦x := e⟧' instead of '⟦_:=_ x e⟧'  
  AssignBr : {m : Memory} {x : Fin n} {e : ASTExpS} 
    → ⟨ ⟦_:=_⟧ x e , m ⟩⇓ m [ x  ↦ ⟦ e ⟧ m ]
  IfT : {m m' : Memory} {e : ASTExpS} {s₁ s₂ : ASTStmS}
    → ⟦ e ⟧ m ≢  0 
    → ⟨ s₁ , m ⟩⇓ m' 
    → ⟨ If0 e s₁ s₂ , m ⟩⇓ m'  
  IfF : {m m' : Memory} {e : ASTExpS} {s₁ s₂ : ASTStmS}
    → ⟦ e ⟧ m ≡ 0 
    → ⟨ s₂ , m ⟩⇓ m' 
    → ⟨ If0 e s₁ s₂ , m ⟩⇓ m'  
  WhileT : {m m' m'' : Memory} {e : ASTExpS} {s : ASTStmS}
    → ⟦ e ⟧ m ≢  0 
    → ⟨ s , m ⟩⇓ m'  
    → ⟨ While e s , m' ⟩⇓ m'' 
    → ⟨ While e s , m ⟩⇓ m''
  WhileF : {m : Memory} {e : ASTExpS} {s : ASTStmS}
    → ⟦ e ⟧ m ≡ 0 
    → ⟨ While e s , m ⟩⇓ m


-- TRANSFORMED LANGUAGE SEMANTICS
-- State of the memory at a certain program point for the transformed program.
Memoryₜ : Set _
Memoryₜ = Vec (List ℕ) n

-- TODO(minor): Dirty list lookup and update implementations, there's probably a cleaner way of doing this.
lookupOrDefault : ℕ → List ℕ → ℕ
lookupOrDefault _ [] = 0
lookupOrDefault 0 (x ∷ xs) = x
lookupOrDefault (suc n) (x ∷ xs) = lookupOrDefault n xs

safeListUpdate : List ℕ → ℕ → ℕ → List ℕ
safeListUpdate [] _ _ = []
safeListUpdate (x ∷ xs) 0 v = v ∷ xs
safeListUpdate (x ∷ xs) (suc n) v = x ∷ (safeListUpdate xs n v)

-- Update the value of a variable in memory of the transformed program.
infixl 6 _[_↦_]ₜ
_[_↦_]ₜ : Memoryₜ → Fin n × ℕ → ℕ → Memoryₜ
m [ (name , index) ↦ v ]ₜ = 
  m [ name ]≔ (safeListUpdate (lookup m name) index v)

-- Semantic evaluation of tranformed expressions.
-- TODO(minor): Add the rest of the arythmetic operations besides ADD to the ASTExp type.
⟦_⟧ₜ : ASTExp → Memoryₜ → ℕ
⟦ INTVAL n ⟧ₜ m = n
⟦ VAR (name , index) ⟧ₜ m = lookupOrDefault index (lookup m name)       
⟦ ADD exp exp' ⟧ₜ m = ⟦ exp ⟧ₜ m + ⟦ exp' ⟧ₜ m
  
-- Big step semantics of transformed statements.
infixl 5 ⟨_,_⟩⇓ₜ_
data ⟨_,_⟩⇓ₜ_ : ASTStm → Memoryₜ → Memoryₜ → Set where
  Skipₜ : {m : Memoryₜ} → ⟨ SKIP , m ⟩⇓ₜ m
  Seqₜ : {m m' m'' : Memoryₜ} {s₁ s₂ : ASTStm}
    → ⟨ s₁ , m ⟩⇓ₜ m'  
    → ⟨ s₂ , m' ⟩⇓ₜ m'' 
    → ⟨ SEQ s₁ s₂ , m ⟩⇓ₜ m'' 
  Assignₜ : {m : Memoryₜ} {x : Fin n × ℕ} {e : ASTExp} 
    → ⟨ ASSIGN x e , m ⟩⇓ₜ m [ x  ↦ ⟦ e ⟧ₜ m ]ₜ
  IfTₜ : {m m' : Memoryₜ} {e : ASTExp} {s₁ s₂ : ASTStm}
    → ⟦ e ⟧ₜ m ≢  0 
    → ⟨ s₁ , m ⟩⇓ₜ m' 
    → ⟨ IF0 e s₁ s₂ , m ⟩⇓ₜ m'  
  IfFₜ : {m m' : Memoryₜ} {e : ASTExp} {s₁ s₂ : ASTStm}
    → ⟦ e ⟧ₜ m ≡ 0 
    → ⟨ s₂ , m ⟩⇓ₜ m' 
    → ⟨ IF0 e s₁ s₂ , m ⟩⇓ₜ m'  
  WhileTₜ : {m m' m'' : Memoryₜ} {e : ASTExp} {s : ASTStm}
    → ⟦ e ⟧ₜ m ≢  0 
    → ⟨ s , m ⟩⇓ₜ m'  
    → ⟨ WHILE e s , m' ⟩⇓ₜ m'' 
    → ⟨ WHILE e s , m ⟩⇓ₜ m''
  WhileFₜ : {m : Memoryₜ} {e : ASTExp} {s : ASTStm}
    → ⟦ e ⟧ₜ m ≡ 0 
    → ⟨ WHILE e s , m ⟩⇓ₜ m
