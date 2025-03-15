module ActiveSet {n} where

open import Agda.Builtin.Nat
open import Data.Bool.Base
open import Data.Fin 
  hiding (_≟_ ; _+_)
open import Data.Nat 
  renaming (_<_ to _<ₙ_)
open import Data.Nat.Properties
open import Data.Product 
open import Data.Vec.Base
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality 

open import AST {n}

-- Active Sets.
-- Using a vector to represent a Fin n → ℕ mapping.
𝒜 : Set _
𝒜 = Vec ℕ n

𝒜varCount : {m : ℕ} → Vec ℕ m → ℕ
𝒜varCount [] = 0
𝒜varCount (h1 ∷ t1) = suc h1 + 𝒜varCount t1

-- Active sets merge function from Figure 5 of the paper.
merge𝒜 : {m : ℕ} → Vec ℕ m → Vec ℕ m → Vec ℕ m
merge𝒜 [] [] = []
merge𝒜 (h1 ∷ t1) (h2 ∷ t2) =
   (if h1 == h2 then h1 else (suc (h1 ⊔ h2))) ∷ (merge𝒜 t1 t2)

activeSetVarAssignment : Fin n → 𝒜 → 𝒜 → ASTStm
activeSetVarAssignment hInd a a' with lookup a hInd ≟ lookup a' hInd 
...                             | yes _ = SKIP
...                             | no _  = ASSIGN (hInd , (lookup a hInd)) (VAR (hInd , (lookup a' hInd)))

assignActiveSetAux : {n' : ℕ} (m : ℕ) → m <ₙ n → 𝒜 → 𝒜 → n ≡ (suc n') → ASTStm
assignActiveSetAux zero z<n a a' n=sn' = activeSetVarAssignment (fromℕ< z<n) a a'
assignActiveSetAux (suc m) sm<n a a' n=sn' = 
   let m<sn' = m<n⇒m<1+n (<-pred (subst (\x → suc m <ₙ x) n=sn' sm<n))
       m<n = (subst (\x → m <ₙ x) (sym n=sn') m<sn')
    in SEQ (activeSetVarAssignment (fromℕ< sm<n) a a') 
           (assignActiveSetAux m m<n a a' n=sn')

0<n=>n=sn' : {m : ℕ} → zero <ₙ m → Σ[ m' ∈ ℕ ] (m ≡ suc m')
0<n=>n=sn' (s≤s {zero} {n'} z≤n) = n' , refl

-- := definition for active sets from Figure 4 of the paper.
_:=𝒜_ : 𝒜 → 𝒜 → ASTStm
a :=𝒜 a' with n ≟ zero 
...    | no n<>0 = let n' , n=sn' = 0<n=>n=sn' (n≢0⇒n>0 n<>0)
                    in assignActiveSetAux {n'} n' (subst (\x → n' <ₙ x) (sym n=sn') (n<1+n n')) a a' n=sn'
...    | yes _ = SKIP
