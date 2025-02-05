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

-- Representation of the state of the memory at a certain program point.
Memory : Set _
Memory = Vec (List ℕ) n

-- TODO(minor): Dirty list lookup and update implementations, there's probably a cleaner way of doing this.
lookupOrDefault : ℕ → List ℕ → ℕ
lookupOrDefault _ [] = 0
lookupOrDefault 0 (x ∷ xs) = x
lookupOrDefault (suc n) (x ∷ xs) = lookupOrDefault n xs

safeListUpdate : List ℕ → ℕ → ℕ → List ℕ
safeListUpdate [] _ _ = []
safeListUpdate (x ∷ xs) 0 v = v ∷ xs
safeListUpdate (x ∷ xs) (suc n) v = x ∷ (safeListUpdate xs n v)

-- Update the value of a variable in memory.
infixl 6 _[_↦_]
_[_↦_] : Memory → Fin n × ℕ → ℕ → Memory
m [ (name , index) ↦ v ] = 
  m [ name ]≔ (safeListUpdate (lookup m name) index v)

-- Semantic evaluation of expressions.
-- TODO(minor): Add the rest of the arythmetic operations besides ADD to the ASTExp type.
⟦_⟧ : ASTExp → Memory → ℕ
⟦_⟧ (INTVAL n) m = n
⟦_⟧ (VAR (name , index)) m = lookupOrDefault index (lookup m name)       
⟦_⟧ (ADD exp exp') m = ⟦ exp ⟧ m + ⟦ exp' ⟧ m
  
-- TODO(major): Implement the semantics for the ASTStmS type, since I'll probably need this for the correctness proof.
-- Big step semantics of statements.
infixl 5 ⟨_,_⟩⇓ₜ_
data ⟨_,_⟩⇓ₜ_ : ASTStm → Memory → Memory → Set where
  Skip : {m : Memory} → ⟨ SKIP , m ⟩⇓ₜ m
  Seq : {m m' m'' : Memory}{s₁ s₂ : ASTStm}
    → ⟨ s₁ , m ⟩⇓ₜ m'  
    → ⟨ s₂ , m' ⟩⇓ₜ m'' 
    → ⟨ SEQ s₁ s₂ , m ⟩⇓ₜ m'' 
  Assign : {m : Memory} {x : Fin n × ℕ} {e : ASTExp} 
    → ⟨ ASSIGN x e , m ⟩⇓ₜ m [ x  ↦ ⟦ e ⟧ m ]
  If0T : {m m' : Memory} {e : ASTExp} {s₁ s₂ : ASTStm}
    → ⟦ e ⟧ m ≢  0 
    → ⟨ s₁ , m ⟩⇓ₜ m' 
    → ⟨ IF0 e s₁ s₂ , m ⟩⇓ₜ m'  
  If0F : {m m' : Memory} {e : ASTExp} {s₁ s₂ : ASTStm}
    → ⟦ e ⟧ m ≡ 0 
    → ⟨ s₂ , m ⟩⇓ₜ m' 
    → ⟨ IF0 e s₁ s₂ , m ⟩⇓ₜ m'  
  WhileT : {m m' m'' : Memory} {e : ASTExp} {s : ASTStm}
    → ⟦ e ⟧ m ≢  0 
    → ⟨ s , m ⟩⇓ₜ m'  
    → ⟨ WHILE e s , m' ⟩⇓ₜ m'' 
    → ⟨ WHILE e s , m ⟩⇓ₜ m''
  WhileF : {m : Memory} {e : ASTExp} {s : ASTStm}
    → ⟦ e ⟧ m ≡ 0 
    → ⟨ WHILE e s , m ⟩⇓ₜ m
