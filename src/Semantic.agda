module Semantic {n} where

open import Data.Empty
open import Data.Fin
  hiding (_+_ ; pred)
  renaming (_≟_ to _≟f_)
open import Data.Fin.Properties
  hiding (≤∧≢⇒<)
open import Data.List
  hiding (lookup ; [_])
open import Data.Nat 
  renaming (_≟_ to _≟ₙ_ ; _<_ to _<ₙ_ ; _≤_ to _≤ₙ_ )
open import Data.Nat.Properties
  hiding (<⇒≢ )
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
  WhileT : {m m' m'' : Memory} {e : ASTExpS} {v : ℕ} {s : ASTStmS}
    → ⟦ e ⟧ m ≡ v
    → v ≢  0 
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
  WhileTₜ : {m m' m'' : Memoryₜ} {e : ASTExp} {v : ℕ} {s : ASTStm}
    → ⟦ e ⟧ₜ m ≡ v
    → v ≢  0  
    → ⟨ s , m ⟩⇓ₜ m'  
    → ⟨ WHILE e s , m' ⟩⇓ₜ m'' 
    → ⟨ WHILE e s , m ⟩⇓ₜ m''
  WhileFₜ : {m : Memoryₜ} {e : ASTExp} {s : ASTStm}
    → ⟦ e ⟧ₜ m ≡ 0 
    → ⟨ WHILE e s , m ⟩⇓ₜ m


-- CORRECTNESS PROOF PRELIMINARIES

lookupₜ : Memoryₜ  → 𝒜 → Fin n → ℕ
lookupₜ mₜ active x = lookupOrDefault (lookup active x) (lookup mₜ x)

-- Equality between a memory and the projection of a transformed memory on an active set.
_==ₘ_-_ : Memory → Memoryₜ → 𝒜 → Set
m ==ₘ mₜ - active = ∀ x → lookup m x ≡ lookupₜ mₜ active x

-- Equality between two memory projections on active sets.
_-_==ₘₜ_-_ : Memoryₜ → 𝒜 → Memoryₜ → 𝒜 → Set
m1ₜ - a1 ==ₘₜ m2ₜ - a2 = ∀ x → lookupₜ m1ₜ a1 x ≡ lookupₜ m2ₜ a2 x

-- Transitive property between ==ₘ and ==ₘₜ .
==ₘ-trans : {m : Memory} {mₜ mₜ' : Memoryₜ} {a a' : 𝒜}
  → m ==ₘ mₜ - a
  → mₜ - a ==ₘₜ mₜ' - a'
  → m ==ₘ mₜ' - a'
==ₘ-trans meq meq2 var = trans (meq var) (meq2 var)   

-- Semantic equality of expression and its transformed counterpart.
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
  {A : Set} {m : ℕ} {v : A} (index : Fin m) (vector : Vec A m) 
  → lookup (vector [ index ]≔ v) index ≡ v
lookupx∘changex zero (head ∷ tail) = refl
lookupx∘changex (suc x) (head ∷ tail) = lookupx∘changex x tail 

-- x ≠ y ⇒ Γ[x↦st] y = Γ y
lookupy∘changex : 
  {A : Set} {m : ℕ} {v : A} (i1 i2 : Fin m) (vector : Vec A m)
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

𝒜memEqPostVar : {currVar n' : ℕ} {varName : Fin n} {cV<n : currVar <ₙ n} {n=sn' : n ≡ suc n'} {a a' : 𝒜} {mₜ mₜ' : Memoryₜ}
  → ⟨ assignActiveSetAux currVar cV<n a a' n=sn' , mₜ ⟩⇓ₜ mₜ'
  → currVar <ₙ toℕ varName
  → lookup mₜ varName ≡ lookup mₜ' varName

𝒜memEqPostVar {zero} {_} {varName} {z<n} {_} {a} {a'} {_} {_} _ _ with lookup a (fromℕ< z<n) ≟ₙ lookup a' (fromℕ< z<n)
𝒜memEqPostVar {zero} {_} {varName} {_} {_} {a} {a'} {mₜ} {.mₜ} Skipₜ _        | yes _ = refl
𝒜memEqPostVar {zero} {_} {varName} {z<n} {_} {a} {a'} {mₜ} {mₜ'} Assignₜ z<vN | no _ =
  let -- toℕ (fromℕ< z<n) ≡ 0
      toNz=0 = toℕ-fromℕ< z<n
      -- toℕ (fromℕ< z<n) <ₙ toℕ varName
      toNz<toNvN = subst (\x → x <ₙ toℕ varName) (sym toNz=0) z<vN
      -- (fromℕ< z<n) < varName
      z<vN = toℕ-cancel-< toNz<toNvN
      -- vN ≢  (fromℕ< z<n)
      vN<>z = ≢-sym (<⇒≢  z<vN)
   in sym (lookupy∘changex (fromℕ< z<n) varName mₜ vN<>z)

𝒜memEqPostVar currVar@{suc currVar'} {_} {varName} {cV<n} {_} {a} {a'} {_} {_} _ _ with lookup a (fromℕ< cV<n) ≟ₙ lookup a' (fromℕ< cV<n)
𝒜memEqPostVar currVar@{suc currVar'} {_} {varName} {_} {_} {a} {a'} {_} {_} (Seqₜ Skipₜ d) cV<vN        | yes _ = 
  𝒜memEqPostVar d (<-pred (m<n⇒m<1+n cV<vN))
𝒜memEqPostVar currVar@{suc currVar'} {_} {varName} {cV<n} {_} {a} {a'} {mₜ} {mₜ'} (Seqₜ Assignₜ d) cV<vN | no _ = 
  let -- toℕ (fromℕ< cV<n) ≡ currVar
      toNcV=cV = toℕ-fromℕ< cV<n
      -- toℕ (fromℕ< cV<n) <ₙ toℕ varName
      toNcV<toNvN = subst (\x → x <ₙ toℕ varName) (sym toNcV=cV) cV<vN
      -- (fromℕ< cV<n) < varName
      fNcV<vN = toℕ-cancel-< toNcV<toNvN
      -- varName ≢  (fromℕ< cV<n)
      vN<>fNcV = ≢-sym (<⇒≢  fNcV<vN)
      -- lookup mₜ varName ≡ lookup mₜ1 varName
      lmtvN=lmt1vN = sym (lookupy∘changex (fromℕ< cV<n) varName mₜ vN<>fNcV)
      -- lookup mₜ1 varName ≡ lookup mₜ' varName
      lmt1vN=lmt'vN = 𝒜memEqPostVar d (<-pred (m<n⇒m<1+n cV<vN))
   in trans lmtvN=lmt1vN lmt1vN=lmt'vN  

𝒜memEqPreVar : {currVar n' : ℕ} {varName : Fin n} {cV<n : currVar <ₙ n} {n=sn' : n ≡ suc n'} {a a' : 𝒜} {mₜ mₜ' : Memoryₜ}
  → ⟨ assignActiveSetAux currVar cV<n a a' n=sn' , mₜ ⟩⇓ₜ mₜ'
  → toℕ varName ≤ₙ currVar
  → lookupₜ mₜ a' varName ≡ lookupₜ mₜ' a varName

𝒜memEqPreVar {zero} {_} {zero} {_} {_} {a} {a'} {_} {_} _ _ with lookup a zero ≟ₙ lookup a' zero
𝒜memEqPreVar {zero} {_} {zero} {_} {_} {_} {_} {mₜ} {.mₜ} Skipₜ _   | yes laz=la'z = 
  cong (\x → lookupOrDefault x (lookup mₜ zero)) (sym laz=la'z)
𝒜memEqPreVar {zero} {_} {zero} {_} {_} {a} {a'} {mₜ} {_} Assignₜ _ | no _ = 
  sym (lookupₜx∘changeₜx {n} {_} {lookup a zero} zero mₜ)

𝒜memEqPreVar currVar@{suc currVar'} {_} {varName} {cV<n} {_} {a} {a'} {_} {_} _ _ with toℕ varName ≟ₙ currVar | lookup a (fromℕ< cV<n) ≟ₙ lookup a' (fromℕ< cV<n)
𝒜memEqPreVar currVar@{suc currVar'} {_} {varName} {cV<n} {_} {a} {a'} {_} {_} (Seqₜ Skipₜ d) _                     | yes vN=cV | yes lacV=la'cV = 
  let lmtvN=lmt'vN = 𝒜memEqPostVar d (subst (\x → currVar' <ₙ x) (sym vN=cV) (n<1+n currVar'))
      -- varName ≡ fromℕ< cV<n
      vN=cV = toℕ-injective (trans vN=cV (sym (toℕ-fromℕ< cV<n)))
      lavN=la'vN = subst (\x → lookup a x ≡ lookup a' x) (sym vN=cV) lacV=la'cV
   in cong₂ (\x y → lookupOrDefault x y) (sym lavN=la'vN) lmtvN=lmt'vN
𝒜memEqPreVar currVar@{suc currVar'} {_} {varName} {cV<n} {_} {a} {a'} {mₜ} {mₜ'} (Seqₜ {.mₜ} {mₜ1} {.mₜ'} Assignₜ d) _ | yes vN=cV | no _ = 
  let finCurrVar = fromℕ< cV<n
      -- lookup mt1 varName = lookup mt' varName
      lmt1vN=lmt'vN = 𝒜memEqPostVar d (subst (\x → currVar' <ₙ x) (sym vN=cV) (n<1+n currVar'))
      -- lookupOrDefault (lookup a finCurrVar) (lookup mt1 finCurrVar) == lookupOrDefault (lookup a' finCurrVar) (lookup mt finCurrVar)
      lamt1cV=la'mtcV = lookupₜx∘changeₜx {n} {_} {lookup a finCurrVar} finCurrVar mₜ
      -- fromℕ< cV<n ≡ varName
      cV=vN = sym (toℕ-injective (trans vN=cV (sym (toℕ-fromℕ< cV<n))))
      -- lookupOrDefault (lookup a varName) (lookup mt1 varName) == lookupOrDefault (lookup a' varName) (lookup mt varName)
      lamt1vN=la'mtvN = subst (\x → lookupₜ mₜ a' x ≡ lookupₜ mₜ1 a x) cV=vN (sym lamt1cV=la'mtcV)
   in subst (\x → lookupₜ mₜ a' varName ≡ lookupOrDefault (lookup a varName) x) lmt1vN=lmt'vN lamt1vN=la'mtvN
𝒜memEqPreVar currVar@{suc currVar'} {_} {varName} {_} {_} {a} {a'} {_} {_} (Seqₜ Skipₜ d) vN≤cV                     | no vN<>cV | yes _ = 
  𝒜memEqPreVar d (m<1+n⇒m≤n (≤∧≢⇒< vN≤cV vN<>cV))
𝒜memEqPreVar currVar@{suc currVar'} {_} {varName} {cV<n} {_} {a} {a'} {mₜ} {mₜ'} (Seqₜ Assignₜ d) vN≤cV               | no vN<>cV | no _ =
  let -- varName <> fromℕ< cV<n
      vN<>fromN<cV = (\vN=fromN<cV → vN<>cV (subst (\x → toℕ x ≡ currVar) (sym vN=fromN<cV) (toℕ-fromℕ< cV<n))) 
      -- lookupₜ mₜ1 a' varName ≡ lookupₜ mₜ a' varName
      lmt1a'vN=lmta'vN = lookupₜy∘changeₜx (fromℕ< cV<n) varName mₜ vN<>fromN<cV
      -- lookupₜ mₜ1 a' varName ≡ lookupₜ mₜ' a varName
      lmt1a'vN=lmt'avN = 𝒜memEqPreVar d (m<1+n⇒m≤n (≤∧≢⇒< vN≤cV vN<>cV))
   in trans (sym lmt1a'vN=lmta'vN) lmt1a'vN=lmt'avN

-- Memory equality after executing an active set assignment.
:=𝒜-memEq : {a a' : 𝒜} {mₜ mₜ' : Memoryₜ} 
  → ⟨ a' :=𝒜 a , mₜ ⟩⇓ₜ mₜ'
  → mₜ - a ==ₘₜ mₜ' - a'
:=𝒜-memEq {a} {a'} {mₜ} {mₜ'} d varName with n ≟ₙ zero 
...                                        | no n<>0 = let n' , n=sn' = 0<n=>n=sn' (n≢0⇒n>0 n<>0)
                                                        in 𝒜memEqPreVar d (subst (\x → toℕ varName ≤ₙ x) (cong pred n=sn') (toℕ≤pred[n] varName))
:=𝒜-memEq {[]} {[]} {mₜ} {.mₜ} Skipₜ varName | yes _ = refl


-- CORRECTNESS PROOF

-- Correctness of the program transformation for the While case.
whileCorrectness : {e : ASTExpS} {s : ASTStmS} {e' : ASTExp} {s' : ASTStm} {m m' : Memory} {mₜ mₜ' : Memoryₜ} {A A₁ A₂ : 𝒜}
  → ⟨ While e s , m ⟩⇓ m'
  → ⟨ WHILE e' s' , mₜ ⟩⇓ₜ mₜ' 
  → e' ≡ transExp e A₁
  → s' ≡ SEQ (proj₁ (transStm s A₁)) (A₁ :=𝒜 A₂)
  → A₁ ≡ merge𝒜 A (proj₂ (transStm s A))
  → A₂ ≡ proj₂ (transStm s A₁)
  → m ==ₘ mₜ - A₁
  → m' ==ₘ mₜ' - A₁

-- Correctness of the program transformation.
correctness : {s : ASTStmS} {m m' : Memory} {mₜ mₜ' : Memoryₜ} {active : 𝒜}
  → ⟨ s , m ⟩⇓ m'
  → ⟨ proj₁ (transStm s active) , mₜ ⟩⇓ₜ mₜ'
  → m ==ₘ mₜ - active
  → m' ==ₘ mₜ' - (proj₂ (transStm s active))

-- TODO(minor): Rewrite this using a let and type explanations for the difficult terms like I did in AssignmentId.
correctness {x := e} {m} {.(m [ x ↦ ⟦ e ⟧ m ])} {mₜ} {.(mₜ [ x , lookup a x ↦ ⟦ transExp e a ⟧ₜ mₜ ]ₜ)} {a} 
  Assign
  Assignₜ 
  meq varName with varName ≟f x
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
                                  (cong (λ y → lookupOrDefault (lookup a varName) (lookup (mₜ [ y , lookup a y ↦ ⟦ transExp e a ⟧ₜ mₜ ]ₜ) varName)) vN=x)
                                )
...              | no vN!=x = trans 
                                (trans 
                                  (lookupy∘changex x varName m vN!=x)
                                  (meq varName)
                                ) 
                                (sym (lookupₜy∘changeₜx x varName mₜ vN!=x))

-- TODO(minor): Same as above, rewrite this using a let and type explanations.
correctness {⟦ x := e ⟧} {m} {.(m [ x ↦ ⟦ e ⟧ m ])} {mₜ} {mₜ'} {a} 
  AssignBr 
  Assignₜ 
  meq varName with varName ≟f x
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
                                -- v' ≡ lookupₜ mₜ' a' varName
                                (sym (trans
                                  -- lookupOrDefault (lookup (a [ x ]≔ suc (lookup a x)) varName) (lookup (mₜ [ x ]≔ (safeListUpdate (lookup mₜ x) (suc (lookup a x)) v')) varName)
                                  -- ===
                                  -- lookupOrDefault (suc (lookup a x)) (safeListUpdate (lookup mₜ x) (suc (lookup a x)) v')
                                  (trans
                                    -- lookupOrDefault (lookup (a [ x ]≔ suc (lookup a x)) varName) (lookup (mₜ [ x , suc (lookup a x) ↦ v' ]ₜ) varName)
                                    -- ===
                                    -- lookupOrDefault (lookup (a [ x ]≔ suc (lookup a x)) x) (safeListUpdate (lookup mₜ x) (suc (lookup a x)) v')
                                    (trans 
                                      (cong (λ y → lookupOrDefault (lookup (a [ x ]≔ suc (lookup a x)) y) (lookup (mₜ [ x ]≔ (safeListUpdate (lookup mₜ x) (suc (lookup a x)) (⟦ transExp e a ⟧ₜ mₜ))) y)) vN=x)
                                      (cong (λ y → lookupOrDefault (lookup (a [ x ]≔ suc (lookup a x)) x) y) (lookupx∘changex x mₜ))
                                    )
                                    -- lookupOrDefault (lookup (a [ x ]≔ suc (lookup a x)) x) (safeListUpdate (lookup mₜ x) (suc (lookup a x)) v')
                                    -- ===
                                    -- lookupOrDefault (suc (lookup a x)) (safeListUpdate (lookup mₜ x) (suc (lookup a x)) v')
                                    (cong (λ y → lookupOrDefault y (safeListUpdate (lookup mₜ x) (suc (lookup a x)) (⟦ transExp e a ⟧ₜ mₜ))) (lookupx∘changex x a))
                                  )
                                  -- lookupOrDefault (suc (lookup a x)) (safeListUpdate (lookup mₜ x) (suc (lookup a x)) v') ≡ v'
                                  (listLookupx∘listUpdatex (suc (lookup a x)) (lookup mₜ x))
                                ))
...              | no vN!=x = trans 
                                -- lookup m' varName ≡ lookupₜ mₜ active varName
                                (trans 
                                  -- lookup m' varName ≡ lookup m varName
                                  (lookupy∘changex x varName m vN!=x)
                                  -- lookup m varName ≡ lookupₜ mₜ active varName
                                  (meq varName)
                                )
                                -- lookupₜ mₜ active varName ≡ lookupₜ mₜ' active' varName
                                (trans
                                  -- lookupₜ mₜ a varName ≡ lookupₜ mₜ' a varName
                                  (sym (lookupₜy∘changeₜx x varName mₜ vN!=x))
                                  -- lookupₜ mₜ' a varName ≡ lookupₜ mₜ' a' varName
                                  (cong (λ y → lookupOrDefault y (lookup mₜ' varName)) (sym (lookupy∘changex x varName a vN!=x)))  
                                )

-- TODO(minor): I tried to replace some of the values in the long expression of IfTₜ but apparently if I use a dot I need
-- to use the full expression, and if I don't use it I cannot have functions as part of the pattern. Is there a nicer way of writing that expression?
correctness {If0 cond sT sF} {m} {m'} {mₜ} {mₜ'} {a} 
  (IfT {.m} {.m'} {.cond} {v} {.sT} {.sF} em=v v<>0 d) 
  (IfTₜ {.mₜ} {.mₜ'} {.(transExp cond a)} {v'} {.(SEQ (proj₁ (transStm sT a)) (merge𝒜 (proj₂ (transStm sT a)) (proj₂ (transStm sF a)) :=𝒜 proj₂ (transStm sT a)))} {sF'} em'=v' v'<>0 (Seqₜ {m1} {m2} {m3} d' d''))
  meq = 
    let aT = proj₂ (transStm sT a)
        aF = proj₂ (transStm sF a)
        a' = merge𝒜 aT aF
        m1=mt1a' = correctness {sT} {m} {m'} {mₜ} {m2} {a} d d' meq
        mt1a'=mt2a'' = :=𝒜-memEq {aT} {a'} d''
      in ==ₘ-trans {m'} {m2} {mₜ'} {aT} {a'} m1=mt1a' mt1a'=mt2a''

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

correctness {If0 cond sT sF} {m} {m'} {mₜ} {mₜ'} {a}
  (IfF {.m} {.m'} {.cond} {.sT} {.sF} em=0 d) 
  (IfFₜ {.mₜ} {.mₜ'} {.(transExp cond a)} {sT'} {.(SEQ (proj₁ (transStm sF a)) (merge𝒜 (proj₂ (transStm sT a)) (proj₂ (transStm sF a)) :=𝒜 proj₂ (transStm sF a)))} em'=0 (Seqₜ {m1} {m2} {m3} d' d''))
  meq = 
    let aT = proj₂ (transStm sT a)
        aF = proj₂ (transStm sF a)
        a' = merge𝒜 aT aF
        m1=mt1a' = correctness {sF} {m} {m'} {mₜ} {m2} {a} d d' meq
        mt1a'=mt2a'' = :=𝒜-memEq {aF} {a'} d''
      in ==ₘ-trans {m'} {m2} {mₜ'} {aF} {a'} m1=mt1a' mt1a'=mt2a''

correctness {While cond s} {m} {m'} {mₜ} {mₜ'} {active} d (Seqₜ {.mₜ} {mₜ1} {.mₜ'} dₜ dₜ') meq = 
  let A₁ = merge𝒜 active (proj₂ (transStm s active))
      mtA=mt1A1 = :=𝒜-memEq {active} {A₁} {mₜ} {mₜ1} dₜ
   in whileCorrectness d dₜ' refl refl refl refl (==ₘ-trans {m} {mₜ} {mₜ1} {active} {A₁} meq mtA=mt1A1)

correctness {Seq s s₁} {m} {m'} {mₜ} {mₜ'} {a} 
  (Seq {m = .m} {m' = m2} {m'' = .m'} d d₁) 
  (Seqₜ {m = .mₜ} {m' = mt2} {m'' = .mₜ'} d' d'') 
  meq = 
    let h1 = correctness {s} {m} {m2} {mₜ} {mt2} d d' meq
     in correctness d₁ d'' h1

correctness {Skip} {m} {.m} {mₜ} {.mₜ} {a} Skip Skipₜ meq = meq

-- whileCorrectness : {e : ASTExpS} {s : ASTStmS} {e' : ASTExp} {s' : ASTStm} {m m' : Memory} {mₜ mₜ' : Memoryₜ} {A A₁ A₂ : 𝒜}
--   → ⟨ While e s , m ⟩⇓ m'
--   → ⟨ WHILE e' s' , mₜ ⟩⇓ₜ mₜ' 
--   → e' ≡ transExp e A₁
--   → s' ≡ SEQ (proj₁ (transStm s A₁)) (A₁ :=𝒜 A₂)
--   → A₁ ≡ merge𝒜 A (proj₂ (transStm s A))
--   → A₂ ≡ proj₂ (transStm s A₁)
--   → m ==ₘ mₜ - A₁
--   → m' ==ₘ mₜ' - A₁

whileCorrectness {e} {s} {e'} {s'} {m} {m'} {mₜ} {mₜ'} {A} {A₁} {A₂} 
  (WhileF em=0) 
  (WhileFₜ em'=0) 
  refl refl refl refl
  meq = meq

whileCorrectness {e} {s} {e'} {s'} {m} {m'} {mₜ} {mₜ'} {A} {A₁} {A₂} 
  (WhileF em=0) 
  (WhileTₜ {_} {_} {_} {_} {v} {_} em'=v v<>0 _ _)
  refl refl refl refl
  meq = 
    let em=em' = expEquality {e} {m} {_} {0} {v} {_} meq em=0 em'=v
     in ⊥-elim (v<>0 (sym em=em'))

whileCorrectness {e} {s} {e'} {s'} {m} {m'} {mₜ} {mₜ'} {A} {A₁} {A₂} 
  (WhileT {.m} {_} {_} {.e} {v} {_} em=v v<>0 _ _) 
  (WhileFₜ em'=0) 
  refl refl refl refl
  meq = 
    let em=em' = expEquality {e} {m} {_} {v} {0} {_} meq em=v em'=0
     in ⊥-elim (v<>0 em=em')

whileCorrectness {e} {s} {e'} {s'} {m} {m'} {mₜ} {mₜ'} {A} {A₁} {A₂} 
  (WhileT {.m} {m1} {.m'} {.e} {_} {.s} _ _ d d') 
  (WhileTₜ {.mₜ} {mₜ2} {.mₜ'} {cond'} {_} {s'} _ _ (Seqₜ {.mₜ} {mₜ1} {.mₜ2} dₜ' dₜ'') dₜ''')
  refl refl refl refl
  meq = 
        -- m1 ==ₘ mₜ1 - A2
    let h = correctness {s} {m} {m1} {mₜ} {mₜ1} {A₁} d dₜ' meq
        -- mt1 - A2 ==ₘₜ mt2 - A1
        mt1A2=mt2A1 = :=𝒜-memEq {A₂} {A₁} {mₜ1} {mₜ2} dₜ''
        -- m' ==ₘ mₜ' - A1
     in whileCorrectness d' dₜ''' refl refl refl refl (==ₘ-trans {m1} {mₜ1} {mₜ2} {A₂} {A₁} h mt1A2=mt2A1)