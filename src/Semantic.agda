module Semantic {n} where

open import Data.Empty
open import Data.Fin
  hiding (_+_)
open import Data.List
  hiding (lookup ; [_])
open import Data.Nat 
  hiding (_≟_)
open import Data.Product 
open import Data.Vec.Base
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality 

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
  IfT : {m m' : Memory} {e : ASTExpS} {v : ℕ} {s₁ s₂ : ASTStmS}
    → ⟦ e ⟧ m ≡ v
    → v ≢  0 
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
  IfTₜ : {m m' : Memoryₜ} {e : ASTExp} {v : ℕ} {s₁ s₂ : ASTStm}
    → ⟦ e ⟧ₜ m ≡ v
    → v ≢  0 
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


-- CORRECTNESS PROOF

lookupₜ : Memoryₜ  → 𝒜 → Fin n → ℕ
lookupₜ mₜ active x = lookupOrDefault (lookup active x) (lookup mₜ x)

-- Equality between a memory and the projection of a transformed memory on an active set.
_==ₘ_-_ : Memory → Memoryₜ → 𝒜 → Set
m ==ₘ mₜ - active = ∀ x → lookup m x ≡ lookupₜ mₜ active x

-- Semantic equality of expression and its transformed counterpart.
-- TODO(major): This only returns the first half of the thesis from the Lemma 3. I'll need to define the second half at some point.
expEquality : {e : ASTExpS} {m : Memory} {mₜ : Memoryₜ} {v v' : ℕ} {active : 𝒜}
  → m ==ₘ mₜ - active
  → ⟦ e ⟧ m ≡ v 
  → ⟦ transExp e active ⟧ₜ mₜ ≡ v' 
  → v ≡ v' 
expEquality {IntVal n} {m} {mₜ} {.(⟦ IntVal n ⟧ m)} {.(⟦ transExp (IntVal n) a ⟧ₜ mₜ)} {a} _ refl refl = refl
expEquality {Var x} {m} {mₜ} {.(⟦ Var x ⟧ m)} {.(⟦ transExp (Var x) a ⟧ₜ mₜ)} {a} m=mt refl refl = m=mt x
expEquality {Add e1 e2} {m} {mₜ} {.(⟦ Add e1 e2 ⟧ m)} {.(⟦ transExp (Add e1 e2) a ⟧ₜ mₜ)} {a} m=mt refl refl = 
  let expEq1 = expEquality {e1} {m} {mₜ} {⟦ e1 ⟧ m} {⟦ transExp e1 a ⟧ₜ mₜ} {a} m=mt refl refl
      expEq2 = expEquality {e2} {m} {mₜ} {⟦ e2 ⟧ m} {⟦ transExp e2 a ⟧ₜ mₜ} {a} m=mt refl refl
   in cong₂ _+_ expEq1 expEq2

-- TODO(minor): I should clean up these properties and probably move them to another file. 
-- Γ[x↦st] x = st
lookupx∘changex : 
  {m v : ℕ} (index : Fin m) (vector : Vec ℕ m) 
  → lookup (vector [ index ]≔ v) index ≡ v
lookupx∘changex zero (head ∷ tail) = refl
lookupx∘changex (suc x) (head ∷ tail) = lookupx∘changex x tail 

-- x ≠ y ⇒ Γ[x↦st] y = Γ y
lookupy∘changex : 
  {m v : ℕ} (i1 i2 : Fin m) (vector : Vec ℕ m)
  → i2 ≢  i1
  → lookup (vector [ i1 ]≔ v) i2 ≡ lookup vector i2
lookupy∘changex zero zero vector i2!=i1 = ⊥-elim (i2!=i1 refl)
lookupy∘changex zero (suc x) (head ∷ tail) i2!=i1 = refl
lookupy∘changex (suc x) zero (head ∷ tail) i2!=i1 = refl
lookupy∘changex (suc x) (suc y) (head ∷ tail) i2!=i1 = lookupy∘changex x y tail (i2!=i1 ∘ cong suc)  

-- TODO(minor): I'll probably have to update the other function definitions to cover all cases with this property,
--  but at least it works for now.
listLookupx∘listUpdatex : 
  {v : ℕ} (a : ℕ) (list : List ℕ) 
  → lookupOrDefault a (safeListUpdate list a v) ≡ v
listLookupx∘listUpdatex a [] = {!   !}
listLookupx∘listUpdatex 0 (head ∷ tail) = refl
listLookupx∘listUpdatex (suc n) (head ∷ tail) = listLookupx∘listUpdatex n tail

lookupₜx∘changeₜx : 
  {m v activeVar : ℕ} (index : Fin m) (vector : Vec (List ℕ) m) 
  → lookupOrDefault activeVar (lookup (vector [ index ]≔ (safeListUpdate (lookup vector index) activeVar v)) index) ≡ v
lookupₜx∘changeₜx {_} {_} {activeVar} zero (head ∷ tail) = listLookupx∘listUpdatex activeVar head
lookupₜx∘changeₜx (suc x) (head ∷ tail) = lookupₜx∘changeₜx x tail 

lookupₜy∘changeₜx : 
  {m v activeVar activeVar2 : ℕ} (i1 i2 : Fin m) (vector : Vec (List ℕ) m) 
  → i2 ≢  i1
  → lookupOrDefault activeVar (lookup (vector [ i1 ]≔ (safeListUpdate (lookup vector i1) activeVar2 v)) i2) ≡ lookupOrDefault activeVar (lookup vector i2)
lookupₜy∘changeₜx zero zero vector i2!=i1 = ⊥-elim (i2!=i1 refl)
lookupₜy∘changeₜx zero (suc x) (head ∷ tail) i2!=i1 = refl
lookupₜy∘changeₜx (suc x) zero (head ∷ tail) i2!=i1 = refl
lookupₜy∘changeₜx (suc x) (suc y) (head ∷ tail) i2!=i1 = lookupₜy∘changeₜx x y tail (i2!=i1 ∘ cong suc)  


-- Correctness of the program transformation.
-- TODO(major): Implement.
correctness : {s : ASTStmS} {m m' : Memory} {mₜ mₜ' : Memoryₜ} {active : 𝒜}
  → ⟨ s , m ⟩⇓ m'
  → ⟨ proj₁ (transStm s active) , mₜ ⟩⇓ₜ mₜ'
  → m ==ₘ mₜ - active
  → m' ==ₘ mₜ' - (proj₂ (transStm s active))

correctness {x := e} {m} {.(m [ x ↦ ⟦ e ⟧ m ])} {mₜ} {.(mₜ [ x , lookup a x ↦ ⟦ transExp e a ⟧ₜ mₜ ]ₜ)} {a} 
  Assign
  Assignₜ 
  -- TODO(minor): Rewrite this using a let and type explanations for the difficult terms like I did in AssignmentId.
  meq varName with varName ≟ x
...              | yes vN=x = trans 
                                -- lookup (m [ x ]≔ ⟦ e ⟧ m) varName === v'
                                (trans 
                                  -- lookup (m [ x ]≔ ⟦ e ⟧ m) varName === v
                                  (trans 
                                  -- lookup (m [ x ]≔ ⟦ e ⟧ m) varName === lookup (m [ varName ]≔ ⟦ e ⟧ m) varName
                                    (sym (cong (λ y → lookup (m [ y ]≔ ⟦ e ⟧ m) varName) vN=x))
                                  -- lookup (m [ varName ]≔ v) varName ≡ v
                                    (lookupx∘changex varName m)
                                  )
                                  -- v === v'
                                  (expEquality {e} {m} {mₜ} meq refl refl)
                                ) 
                                -- v' === lookup (mₜ [ x , lookup a x ↦ ⟦ transExp e a ⟧ₜ mₜ) varName
                                (trans 
                                  -- v' === lookupOrDefault activeVar (lookup (mₜ [ varName ]≔ (safeListUpdate (lookup mₜ varName) activeVar v)) varName)
                                  (sym (lookupₜx∘changeₜx varName mₜ))
                                  -- lookupOrDefault activeVar (lookup (mₜ [ varName ]≔ (safeListUpdate (lookup mₜ varName) activeVar v)) varName)
                                  -- ===
                                  -- lookupOrDefault activeVar (lookup (mₜ [ x ]≔ (safeListUpdate (lookup mₜ x) (lookup a x) v)) varName)
                                  (cong (λ y → lookupOrDefault (lookup a varName) (lookup (mₜ [ y ]≔ safeListUpdate (lookup mₜ y) (lookup a y) (⟦ transExp e a ⟧ₜ mₜ)) varName)) vN=x)
                                )
...              | no vN!=x = trans 
                                (trans 
                                  (lookupy∘changex x varName m vN!=x)
                                  (meq varName)
                                ) 
                                (sym (lookupₜy∘changeₜx x varName mₜ vN!=x))

correctness {⟦ x := e ⟧} {m} {.(m [ x ↦ ⟦ e ⟧ m ])} {mₜ} {.(mₜ [ x , suc (lookup a x) ↦ ⟦ transExp e a ⟧ₜ mₜ ]ₜ)} {a} 
  AssignBr 
  Assignₜ 
  meq varName with varName ≟ x
...              | yes vN=x = {!   !}
...              | no vN!=x = {!   !}

correctness {If0 cond sT sF} {m} {m'} {mₜ} {mₜ'} {a} 
  (IfT {.m} {.m'} {.cond} {v} {.sT} {.sF} em=v v<>0 d) 
  (IfTₜ {.mₜ} {.mₜ'} {.(transExp cond a)} {s₁} {s₂} em'=v' v'<>0 d') 
  meq = {! !}

correctness {If0 cond sT sF} {m} {m'} {mₜ} {mₜ'} {a} 
  (IfT {.m} {.m'} {.cond} {v} {_} {_} em=v v<>0 d) 
  (IfFₜ em'=0 d') 
  meq = 
    let em=em' = expEquality {cond} {m} {mₜ} {v} {0} {a} meq em=v em'=0
     in ⊥-elim (v<>0 em=em')

correctness {If0 cond sT sF} {m} {m'} {mₜ} {mₜ'} {a} 
  (IfF em=0 d) 
  (IfTₜ {.mₜ} {.mₜ'} {_} {v} {_} {_} em'=v v<>0 d') 
  meq = 
    let em=em' = expEquality {cond} {m} {mₜ} {0} {v} {a} meq em=0 em'=v
     in ⊥-elim (v<>0 (sym em=em'))

correctness {If0 x s s₁} {m} {m'} {mₜ} {mₜ'} {a} (IfF x₁ d) (IfFₜ x₂ d') meq = {!   !}

correctness {While x s} {m} {m'} {mₜ} {mₜ'} {a} (WhileT x₁ d d₁) d' meq = {!  !}

correctness {While x s} {m} {.m} {mₜ} {mₜ'} {a} (WhileF x₁) d' meq = {!  !}

correctness {Seq s s₁} {m} {m'} {mₜ} {mₜ'} {a} 
  (Seq {m = .m} {m' = m2} {m'' = .m'} d d₁) 
  (Seqₜ {m = .mₜ} {m' = mt2} {m'' = .mₜ'} d' d'') 
  meq = 
    let h1 = correctness {s} {m} {m2} {mₜ} {mt2} d d' meq
     in correctness d₁ d'' h1

correctness {Skip} {m} {.m} {mₜ} {.mₜ} {a} Skip Skipₜ meq = meq
